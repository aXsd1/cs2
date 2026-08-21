#![cfg_attr(not(debug_assertions), windows_subsystem = "windows")]

mod updater;

use std::path::PathBuf;
use std::sync::mpsc::{self, Receiver, Sender};
use std::thread;
use std::time::{Duration, Instant};

use eframe::egui::{self, Color32, FontId, Pos2, Rect, Rounding, Stroke, Vec2};
use updater::{AutoUpdater, LauncherConfig, UpdaterEvent};

#[allow(dead_code)]
enum AppState {
    Checking,
    Verifying,
    Downloading {
        current_file: String,
        file_index: usize,
        total_files: usize,
    },
    UpToDate {
        version: String,
    },
    Launching {
        executable: String,
    },
    Success,
    Error(String),
}

struct LauncherApp {
    state: AppState,
    status_text: String,
    sub_status: String,
    target_progress: f32,
    animated_progress: f32,
    shimmer_offset: f32,
    is_indeterminate: bool,
    config: LauncherConfig,
    event_rx: Option<Receiver<UpdaterEvent>>,
    success_time: Option<Instant>,
    last_frame: Instant,
    icon_texture: Option<egui::TextureHandle>,
}

impl LauncherApp {
    fn new(cc: &eframe::CreationContext<'_>, config: LauncherConfig) -> Self {
        // Modern dark theme styling
        let mut visuals = egui::Visuals::dark();
        visuals.panel_fill = Color32::from_rgb(14, 17, 24);
        visuals.window_fill = Color32::from_rgb(14, 17, 24);
        visuals.window_stroke = Stroke::new(1.0, Color32::from_rgb(34, 40, 58));
        cc.egui_ctx.set_visuals(visuals);

        // Load icon texture
        let icon_texture = image::load_from_memory(include_bytes!("../app-icon.ico"))
            .ok()
            .map(|img| {
                let rgba = img.to_rgba8();
                let size = [rgba.width() as usize, rgba.height() as usize];
                let color_image = egui::ColorImage::from_rgba_unmultiplied(size, rgba.as_raw());
                cc.egui_ctx.load_texture("app_icon", color_image, egui::TextureOptions::LINEAR)
            });

        let mut app = Self {
            state: AppState::Checking,
            status_text: "Checking for updates...".to_string(),
            sub_status: "Connecting securely to update server".to_string(),
            target_progress: 0.0,
            animated_progress: 0.0,
            shimmer_offset: 0.0,
            is_indeterminate: true,
            config,
            event_rx: None,
            success_time: None,
            last_frame: Instant::now(),
            icon_texture,
        };

        app.start_updater_thread();
        app
    }

    fn start_updater_thread(&mut self) {
        let (tx, rx): (Sender<UpdaterEvent>, Receiver<UpdaterEvent>) = mpsc::channel();
        self.event_rx = Some(rx);
        self.state = AppState::Checking;
        self.status_text = "Checking for updates...".to_string();
        self.sub_status = "Connecting securely to update server".to_string();
        self.target_progress = 0.0;
        self.animated_progress = 0.0;
        self.is_indeterminate = true;
        self.success_time = None;

        let config_clone = self.config.clone();
        thread::spawn(move || {
            let updater = AutoUpdater::new(config_clone);
            let tx_clone = tx.clone();
            if let Err(err_msg) = updater.run_with_events(move |evt| {
                let _ = tx_clone.send(evt);
            }) {
                let _ = tx.send(UpdaterEvent::Error(err_msg));
            }
        });
    }

    fn process_events(&mut self) {
        if let Some(ref rx) = self.event_rx {
            while let Ok(event) = rx.try_recv() {
                match event {
                    UpdaterEvent::CheckingVersions => {
                        self.state = AppState::Checking;
                        self.status_text = "Checking for updates...".to_string();
                        self.sub_status = "Verifying remote package manifest".to_string();
                        self.is_indeterminate = true;
                    }
                    UpdaterEvent::VerifyingSignature => {
                        self.state = AppState::Verifying;
                        self.status_text = "Verifying signature...".to_string();
                        self.sub_status = "Validating Ed25519 cryptographic security key".to_string();
                        self.is_indeterminate = true;
                    }
                    UpdaterEvent::UpToDate { version } => {
                        self.state = AppState::UpToDate { version: version.clone() };
                        self.status_text = format!("Up to Date (v{})", version);
                        self.sub_status = "All files verified, launching client...".to_string();
                        self.is_indeterminate = false;
                        self.target_progress = 1.0;
                    }
                    UpdaterEvent::UpdateFound { version, total_files } => {
                        self.state = AppState::Downloading {
                            current_file: String::new(),
                            file_index: 0,
                            total_files,
                        };
                        self.status_text = format!("Update Found (v{})", version);
                        self.sub_status = format!("{} file(s) required. Starting download...", total_files);
                        self.is_indeterminate = false;
                        self.target_progress = 0.0;
                        self.animated_progress = 0.0;
                    }
                    UpdaterEvent::DownloadingFile {
                        path,
                        file_index,
                        total_files,
                        overall_progress,
                    } => {
                        self.state = AppState::Downloading {
                            current_file: path.clone(),
                            file_index,
                            total_files,
                        };
                        self.status_text = format!("Downloading files... ({}/{})", file_index, total_files);
                        self.sub_status = format!("Downloading: {}", path);
                        self.is_indeterminate = false;
                        self.target_progress = overall_progress;
                    }
                    UpdaterEvent::FileCompleted {
                        path,
                        file_index,
                        total_files,
                        overall_progress,
                    } => {
                        self.status_text = format!("Verified: {} ({}/{})", path, file_index, total_files);
                        self.target_progress = overall_progress;
                    }
                    UpdaterEvent::Launching { executable } => {
                        self.state = AppState::Launching { executable: executable.clone() };
                        self.status_text = "Launching application...".to_string();
                        self.sub_status = format!("Starting target: {}", executable);
                        self.is_indeterminate = false;
                        self.target_progress = 1.0;
                    }
                    UpdaterEvent::Success => {
                        self.state = AppState::Success;
                        self.status_text = "Ready & Launched!".to_string();
                        self.sub_status = "Client initialized successfully. Enjoy the game!".to_string();
                        self.is_indeterminate = false;
                        self.target_progress = 1.0;
                        self.success_time = Some(Instant::now());
                    }
                    UpdaterEvent::Error(err_msg) => {
                        self.state = AppState::Error(err_msg.clone());
                        self.status_text = "Update Error".to_string();
                        self.sub_status = err_msg;
                        self.is_indeterminate = false;
                    }
                }
            }
        }
    }
}

impl eframe::App for LauncherApp {
    fn update(&mut self, ctx: &egui::Context, _frame: &mut eframe::Frame) {
        let now = Instant::now();
        let dt = (now - self.last_frame).as_secs_f32().clamp(0.0, 0.1);
        self.last_frame = now;

        self.process_events();

        // Smooth lerp progress bar interpolation
        if self.is_indeterminate {
            self.shimmer_offset += dt * 1.5;
            if self.shimmer_offset > 2.0 {
                self.shimmer_offset -= 2.0;
            }
        } else {
            let lerp_factor = (dt * 8.0).clamp(0.0, 1.0);
            self.animated_progress += (self.target_progress - self.animated_progress) * lerp_factor;
        }

        // Close launcher after 1.8 seconds upon success
        if let Some(success_start) = self.success_time {
            if success_start.elapsed() >= Duration::from_millis(1800) {
                ctx.send_viewport_cmd(egui::ViewportCommand::Close);
            }
        }

        // Continuous smooth repaint (60/144 FPS)
        ctx.request_repaint();

        let window_rect = ctx.screen_rect();
        let painter = ctx.layer_painter(egui::LayerId::background());

        // Background panel with soft rounded border
        painter.rect_filled(
            window_rect,
            Rounding::same(12.0),
            Color32::from_rgb(14, 17, 24),
        );
        painter.rect_stroke(
            window_rect,
            Rounding::same(12.0),
            Stroke::new(1.2, Color32::from_rgb(34, 42, 62)),
        );

        // Top accent glow line
        let glow_rect = Rect::from_min_size(
            Pos2::new(window_rect.min.x + 20.0, window_rect.min.y),
            Vec2::new(window_rect.width() - 40.0, 2.0),
        );
        painter.rect_filled(
            glow_rect,
            Rounding::same(1.0),
            Color32::from_rgb(99, 102, 241),
        );

        egui::CentralPanel::default()
            .frame(egui::Frame::none().inner_margin(egui::Margin::symmetric(22.0, 18.0)))
            .show(ctx, |ui| {
                // 1. Header Bar: Logo, Title & Window Controls (Draggable)
                ui.horizontal(|ui| {
                    // Logo Icon
                    if let Some(ref texture) = self.icon_texture {
                        let (icon_rect, _) = ui.allocate_exact_size(Vec2::new(26.0, 26.0), egui::Sense::hover());
                        ui.painter().rect_filled(
                            icon_rect,
                            Rounding::same(6.0),
                            Color32::from_rgb(22, 27, 40),
                        );
                        ui.painter().image(
                            texture.id(),
                            icon_rect.shrink(2.0),
                            Rect::from_min_max(Pos2::new(0.0, 0.0), Pos2::new(1.0, 1.0)),
                            Color32::WHITE,
                        );
                    } else {
                        let (logo_rect, _) = ui.allocate_exact_size(Vec2::new(26.0, 26.0), egui::Sense::hover());
                        ui.painter().rect_filled(
                            logo_rect,
                            Rounding::same(6.0),
                            Color32::from_rgb(26, 31, 48),
                        );
                        ui.painter().text(
                            logo_rect.center(),
                            egui::Align2::CENTER_CENTER,
                            "◆",
                            FontId::proportional(14.0),
                            Color32::from_rgb(129, 140, 248),
                        );
                    }

                    ui.add_space(8.0);

                    // Titles
                    ui.vertical(|ui| {
                        ui.horizontal(|ui| {
                            ui.label(
                                egui::RichText::new("YEAGETH")
                                    .font(FontId::proportional(14.0))
                                    .strong()
                                    .color(Color32::WHITE),
                            );
                            ui.label(
                                egui::RichText::new("STREAM LOADER")
                                    .font(FontId::proportional(10.0))
                                    .color(Color32::from_rgb(148, 163, 184)),
                            );
                        });
                    });

                    // Draggable empty space
                    let drag_space = ui.available_size_before_wrap() - Vec2::new(56.0, 0.0);
                    let (_drag_rect, drag_resp) = ui.allocate_exact_size(drag_space, egui::Sense::drag());
                    if drag_resp.dragged() {
                        ctx.send_viewport_cmd(egui::ViewportCommand::StartDrag);
                    }

                    // Window Action Buttons
                    ui.with_layout(egui::Layout::right_to_left(egui::Align::Center), |ui| {
                        // Close Button
                        let close_btn = ui.add(
                            egui::Button::new(
                                egui::RichText::new("✕")
                                    .font(FontId::proportional(12.0))
                                    .color(Color32::from_rgb(156, 163, 175)),
                            )
                            .frame(false)
                            .min_size(Vec2::new(24.0, 24.0)),
                        );
                        if close_btn.hovered() {
                            ui.output_mut(|o| o.cursor_icon = egui::CursorIcon::PointingHand);
                        }
                        if close_btn.clicked() {
                            ctx.send_viewport_cmd(egui::ViewportCommand::Close);
                        }

                        // Minimize Button
                        let min_btn = ui.add(
                            egui::Button::new(
                                egui::RichText::new("—")
                                    .font(FontId::proportional(11.0))
                                    .color(Color32::from_rgb(156, 163, 175)),
                            )
                            .frame(false)
                            .min_size(Vec2::new(24.0, 24.0)),
                        );
                        if min_btn.clicked() {
                            ctx.send_viewport_cmd(egui::ViewportCommand::Minimized(true));
                        }
                    });
                });

                ui.add_space(20.0);

                // 2. Status Card Area
                let card_bg = Color32::from_rgb(18, 22, 32);
                let card_border = Color32::from_rgb(29, 36, 54);

                egui::Frame::none()
                    .fill(card_bg)
                    .stroke(Stroke::new(1.0, card_border))
                    .rounding(Rounding::same(10.0))
                    .inner_margin(egui::Margin::symmetric(16.0, 14.0))
                    .show(ui, |ui| {
                        // Status Title & Status Dot
                        ui.horizontal(|ui| {
                            let (dot_color, dot_char) = match &self.state {
                                AppState::Checking | AppState::Verifying => (Color32::from_rgb(99, 102, 241), "●"),
                                AppState::Downloading { .. } => (Color32::from_rgb(56, 189, 248), "▼"),
                                AppState::UpToDate { .. } | AppState::Success | AppState::Launching { .. } => (Color32::from_rgb(52, 211, 153), "✔"),
                                AppState::Error(_) => (Color32::from_rgb(248, 113, 113), "✖"),
                            };

                            ui.label(
                                egui::RichText::new(dot_char)
                                    .font(FontId::proportional(12.0))
                                    .color(dot_color),
                            );

                            ui.add_space(4.0);

                            ui.label(
                                egui::RichText::new(&self.status_text)
                                    .font(FontId::proportional(14.0))
                                    .strong()
                                    .color(Color32::WHITE),
                            );

                            // Download Percentage
                            if let AppState::Downloading { .. } = &self.state {
                                ui.with_layout(egui::Layout::right_to_left(egui::Align::Center), |ui| {
                                    ui.label(
                                        egui::RichText::new(format!("{:.0}%", self.animated_progress * 100.0))
                                            .font(FontId::proportional(13.0))
                                            .color(Color32::from_rgb(56, 189, 248))
                                            .strong(),
                                    );
                                });
                            }
                        });

                        ui.add_space(10.0);

                        // 3. Modern Custom Progress Bar
                        let bar_height = 8.0;
                        let (bar_rect, _) = ui.allocate_exact_size(
                            Vec2::new(ui.available_width(), bar_height),
                            egui::Sense::hover(),
                        );

                        // Progress Bar Trough
                        ui.painter().rect_filled(
                            bar_rect,
                            Rounding::same(4.0),
                            Color32::from_rgb(26, 32, 48),
                        );

                        if self.is_indeterminate {
                            // Indeterminate Shimmer/Wave Animation
                            let wave_width = bar_rect.width() * 0.35;
                            let wave_start_x = bar_rect.min.x + (self.shimmer_offset - 0.35) * (bar_rect.width() + wave_width);
                            let visible_min_x = wave_start_x.max(bar_rect.min.x);
                            let visible_max_x = (wave_start_x + wave_width).min(bar_rect.max.x);

                            if visible_max_x > visible_min_x {
                                let wave_rect = Rect::from_min_max(
                                    Pos2::new(visible_min_x, bar_rect.min.y),
                                    Pos2::new(visible_max_x, bar_rect.max.y),
                                );
                                ui.painter().rect_filled(
                                    wave_rect,
                                    Rounding::same(4.0),
                                    Color32::from_rgb(99, 102, 241),
                                );
                            }
                        } else {
                            // Determinate Filling Progress Bar
                            let current_fill_width = (bar_rect.width() * self.animated_progress.clamp(0.0, 1.0)).max(0.0);
                            if current_fill_width > 0.0 {
                                let fill_rect = Rect::from_min_size(
                                    bar_rect.min,
                                    Vec2::new(current_fill_width, bar_height),
                                );

                                let fill_color = match &self.state {
                                    AppState::Success | AppState::UpToDate { .. } | AppState::Launching { .. } => {
                                        Color32::from_rgb(52, 211, 153) // Green
                                    }
                                    AppState::Error(_) => Color32::from_rgb(248, 113, 113), // Red
                                    _ => Color32::from_rgb(56, 189, 248), // Cyan / Indigo
                                };

                                ui.painter().rect_filled(
                                    fill_rect,
                                    Rounding::same(4.0),
                                    fill_color,
                                );
                            }
                        }

                        ui.add_space(8.0);

                        // Subtitle Details
                        ui.horizontal(|ui| {
                            let sub_color = match &self.state {
                                AppState::Error(_) => Color32::from_rgb(248, 113, 113),
                                _ => Color32::from_rgb(148, 163, 184),
                            };

                            ui.label(
                                egui::RichText::new(&self.sub_status)
                                    .font(FontId::proportional(11.0))
                                    .color(sub_color),
                            );
                        });
                    });

                // Error Retry Button
                if let AppState::Error(_) = &self.state {
                    ui.add_space(8.0);
                    ui.horizontal(|ui| {
                        ui.with_layout(egui::Layout::right_to_left(egui::Align::Center), |ui| {
                            let retry_btn = ui.add(
                                egui::Button::new(
                                    egui::RichText::new("🔄 Retry")
                                        .font(FontId::proportional(12.0))
                                        .color(Color32::WHITE),
                                )
                                .fill(Color32::from_rgb(79, 70, 229))
                                .rounding(Rounding::same(6.0)),
                            );

                            if retry_btn.clicked() {
                                self.start_updater_thread();
                            }
                        });
                    });
                }

                // 4. Footer Bar
                ui.with_layout(egui::Layout::bottom_up(egui::Align::Min), |ui| {
                    ui.horizontal(|ui| {
                        ui.label(
                            egui::RichText::new("v1.0.0 • Secured by Ed25519")
                                .font(FontId::proportional(10.0))
                                .color(Color32::from_rgb(71, 85, 105)),
                        );

                        ui.with_layout(egui::Layout::right_to_left(egui::Align::Center), |ui| {
                            ui.horizontal(|ui| {
                                ui.label(
                                    egui::RichText::new("●")
                                        .font(FontId::proportional(8.0))
                                        .color(Color32::from_rgb(52, 211, 153)),
                                );
                                ui.label(
                                    egui::RichText::new("CS2 Server Connected")
                                        .font(FontId::proportional(10.0))
                                        .color(Color32::from_rgb(100, 116, 139)),
                                );
                            });
                        });
                    });
                });
            });
    }
}

fn load_window_icon() -> Option<egui::IconData> {
    if let Ok(img) = image::load_from_memory(include_bytes!("../app-icon.ico")) {
        let rgba = img.to_rgba8();
        let (width, height) = rgba.dimensions();
        Some(egui::IconData {
            rgba: rgba.into_raw(),
            width,
            height,
        })
    } else {
        None
    }
}

fn main() -> Result<(), eframe::Error> {
    let config = LauncherConfig {
        base_url: "https://yeageth.com/stream_files/csesp".to_string(),
        install_dir: PathBuf::from("./app"),
        manifest_file: "manifest.json".to_string(),
        signature_file: Some("manifest.json.sig".to_string()),
        public_key_hex: Some("6ceb4af58d0ab8b1dbfba8ddf7fe97361a8760bbcca91ef09e2c3a7c6e748df6".to_string()),
        auto_launch: true,
        ..Default::default()
    };

    let mut viewport = egui::ViewportBuilder::default()
        .with_inner_size([460.0, 220.0])
        .with_min_inner_size([460.0, 220.0])
        .with_max_inner_size([460.0, 220.0])
        .with_resizable(false)
        .with_decorations(false)
        .with_transparent(true)
        .with_title("Yeageth Stream Loader");

    if let Some(icon) = load_window_icon() {
        viewport = viewport.with_icon(icon);
    }

    let options = eframe::NativeOptions {
        viewport,
        centered: true,
        ..Default::default()
    };

    eframe::run_native(
        "Yeageth Stream Loader",
        options,
        Box::new(|cc| Ok(Box::new(LauncherApp::new(cc, config)))),
    )
}