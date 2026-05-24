use std::time::Instant;
use cs2::{
    CS2Model,
    ClassNameCache,
    LocalCameraControllerTarget,
    PlayerPawnState,
    StateCS2Memory,
    StateEntityList,
    StateLocalPlayerController,
    StatePawnInfo,
    StatePawnModelInfo,
    CEntityIdentityEx,
};
use utils_state::StateRegistry;
use overlay::UnicodeTextRenderer;

use super::Enhancement;
use crate::{
    settings::AppSettings,
    view::ViewController,
};

use windows::Win32::{
    Foundation::{HWND, RECT, POINT},
    UI::WindowsAndMessaging::{FindWindowExA, GetWindowThreadProcessId, GetWindowRect},
    Graphics::Gdi::{
        GetDC, ReleaseDC, CreateCompatibleDC, DeleteDC, CreateCompatibleBitmap,
        SelectObject, BitBlt, GetDIBits, DeleteObject, ClientToScreen,
        SRCCOPY, BITMAPINFO, BITMAPINFOHEADER, BI_RGB, DIB_RGB_COLORS, HGDIOBJ, RGBQUAD,
    },
};

pub struct DataCollector {
    last_capture: Option<Instant>,
}

impl DataCollector {
    pub fn new() -> Self {
        Self {
            last_capture: None,
        }
    }
}

fn find_cs2_window(process_id: u32) -> Option<HWND> {
    let mut current_hwnd = HWND::default();
    for _ in 0..10000 {
        current_hwnd = unsafe { FindWindowExA(None, current_hwnd, None, None) };
        if current_hwnd.0 == 0 {
            break;
        }

        let mut window_process_id = 0;
        let success = unsafe {
            GetWindowThreadProcessId(current_hwnd, Some(&mut window_process_id)) != 0
        };
        if !success || window_process_id != process_id {
            continue;
        }

        let mut window_rect = RECT::default();
        let success = unsafe { GetWindowRect(current_hwnd, &mut window_rect).is_ok() };
        if !success {
            continue;
        }

        if window_rect.left == 0
            && window_rect.bottom == 0
            && window_rect.right == 0
            && window_rect.top == 0
        {
            continue;
        }

        return Some(current_hwnd);
    }
    None
}

unsafe fn capture_screenshot(rect: RECT) -> Option<Vec<u8>> {
    let width = rect.right - rect.left;
    let height = rect.bottom - rect.top;

    let hscreen_dc = GetDC(HWND(0));
    if hscreen_dc.0 == 0 {
        return None;
    }

    let hmem_dc = CreateCompatibleDC(hscreen_dc);
    if hmem_dc.0 == 0 {
        ReleaseDC(HWND(0), hscreen_dc);
        return None;
    }

    let hbitmap = CreateCompatibleBitmap(hscreen_dc, width, height);
    if hbitmap.0 == 0 {
        DeleteDC(hmem_dc);
        ReleaseDC(HWND(0), hscreen_dc);
        return None;
    }

    let hold_obj = SelectObject(hmem_dc, HGDIOBJ(hbitmap.0));

    let bitblt_ok = BitBlt(
        hmem_dc,
        0,
        0,
        width,
        height,
        hscreen_dc,
        rect.left,
        rect.top,
        SRCCOPY,
    );

    let mut success = false;
    let mut bgra_data = vec![0u8; (width * height * 4) as usize];

    if bitblt_ok.is_ok() {
        let mut bmi = BITMAPINFO {
            bmiHeader: BITMAPINFOHEADER {
                biSize: std::mem::size_of::<BITMAPINFOHEADER>() as u32,
                biWidth: width,
                biHeight: -height,
                biPlanes: 1,
                biBitCount: 32,
                biCompression: BI_RGB.0 as u32,
                biSizeImage: 0,
                biXPelsPerMeter: 0,
                biYPelsPerMeter: 0,
                biClrUsed: 0,
                biClrImportant: 0,
            },
            bmiColors: [RGBQUAD::default(); 1],
        };

        let lines = GetDIBits(
            hmem_dc,
            hbitmap,
            0,
            height as u32,
            Some(bgra_data.as_mut_ptr() as *mut _),
            &mut bmi,
            DIB_RGB_COLORS,
        );

        if lines > 0 {
            success = true;
        }
    }

    SelectObject(hmem_dc, hold_obj);
    DeleteObject(hbitmap);
    DeleteDC(hmem_dc);
    ReleaseDC(HWND(0), hscreen_dc);

    if success {
        Some(bgra_data)
    } else {
        None
    }
}

fn save_bmp(path: &std::path::Path, width: i32, height: i32, bgra_data: &[u8]) -> std::io::Result<()> {
    use std::fs::File;
    use std::io::Write;

    let mut file = File::create(path)?;
    let file_size = 54 + bgra_data.len() as u32;

    file.write_all(b"BM")?;
    file.write_all(&file_size.to_le_bytes())?;
    file.write_all(&0u16.to_le_bytes())?;
    file.write_all(&0u16.to_le_bytes())?;
    file.write_all(&54u32.to_le_bytes())?;

    file.write_all(&40u32.to_le_bytes())?;
    file.write_all(&width.to_le_bytes())?;
    file.write_all(&(-height).to_le_bytes())?;
    file.write_all(&1u16.to_le_bytes())?;
    file.write_all(&32u16.to_le_bytes())?;
    file.write_all(&0u32.to_le_bytes())?;
    file.write_all(&(bgra_data.len() as u32).to_le_bytes())?;
    file.write_all(&0i32.to_le_bytes())?;
    file.write_all(&0i32.to_le_bytes())?;
    file.write_all(&0u32.to_le_bytes())?;
    file.write_all(&0u32.to_le_bytes())?;

    file.write_all(bgra_data)?;
    Ok(())
}

impl Enhancement for DataCollector {
    fn update(&mut self, ctx: &crate::UpdateContext) -> anyhow::Result<()> {
        let settings = ctx.states.resolve::<AppSettings>(())?;
        if !settings.collect_data {
            return Ok(());
        }

        let cooldown = std::time::Duration::from_secs(settings.collect_data_time as u64);
        if let Some(last) = self.last_capture {
            if last.elapsed() < cooldown {
                return Ok(());
            }
        }

        let view = ctx.states.resolve::<ViewController>(())?;
        let screen_width = view.screen_bounds.x;
        let screen_height = view.screen_bounds.y;

        if screen_width <= 0.0 || screen_height <= 0.0 {
            return Ok(());
        }

        let cx = screen_width / 2.0;
        let cy = screen_height / 2.0;

        let crop_x0 = cx - 208.0;
        let crop_y0 = cy - 208.0;
        let crop_x1 = cx + 208.0;
        let crop_y1 = cy + 208.0;

        let entities = ctx.states.resolve::<StateEntityList>(())?;
        let class_name_cache = ctx.states.resolve::<ClassNameCache>(())?;
        let memory = ctx.states.resolve::<StateCS2Memory>(())?;
        let local_player_controller = ctx.states.resolve::<StateLocalPlayerController>(())?;
        let Some(local_player_controller) = local_player_controller
            .instance
            .value_reference(memory.view_arc())
        else {
            return Ok(());
        };

        let local_team_id = local_player_controller.m_iPendingTeamNum()?;

        let view_target = ctx.states.resolve::<LocalCameraControllerTarget>(())?;
        let view_target_entity_id = match &view_target.target_entity_id {
            Some(value) => *value,
            None => return Ok(()),
        };

        let mut players_in_crop = Vec::new();

        for entity_identity in entities.entities() {
            if entity_identity.handle::<()>()?.get_entity_index() == view_target_entity_id {
                continue;
            }

            let entity_class = class_name_cache.lookup(&entity_identity.entity_class_info()?)?;
            if !entity_class
                .map(|name| *name == "C_CSPlayerPawn")
                .unwrap_or(false)
            {
                continue;
            }

            let pawn_state = ctx
                .states
                .resolve::<PlayerPawnState>(entity_identity.handle()?)?;
            if *pawn_state != PlayerPawnState::Alive {
                continue;
            }

            let pawn_info = ctx
                .states
                .resolve::<StatePawnInfo>(entity_identity.handle()?)?;

            if pawn_info.player_health <= 0 || pawn_info.player_name.is_none() {
                continue;
            }

            // Only capture enemy players
            if pawn_info.team_id == local_team_id {
                continue;
            }

            let pawn_model = ctx
                .states
                .resolve::<StatePawnModelInfo>(entity_identity.handle()?)?;

            let entry_model = ctx.states.resolve::<CS2Model>(pawn_model.model_address)?;
            let player_2d_box = view.calculate_box_2d(
                &(entry_model.vhull_min + pawn_info.position),
                &(entry_model.vhull_max + pawn_info.position),
            );

            if let Some((vmin, vmax)) = player_2d_box {
                let left = f32::max(vmin.x, crop_x0);
                let right = f32::min(vmax.x, crop_x1);
                let top = f32::max(vmin.y, crop_y0);
                let bottom = f32::min(vmax.y, crop_y1);

                if left < right && top < bottom {
                    let rx = left - crop_x0;
                    let ry = top - crop_y0;
                    let rw = right - left;
                    let rh = bottom - top;

                    players_in_crop.push((
                        rx.round() as i32,
                        ry.round() as i32,
                        rw.round() as i32,
                        rh.round() as i32,
                    ));
                }
            }
        }

        if !players_in_crop.is_empty() {
            if let Some(hwnd) = find_cs2_window(ctx.cs2.process_id() as u32) {
                let mut center = POINT {
                    x: (screen_width / 2.0) as i32,
                    y: (screen_height / 2.0) as i32,
                };
                unsafe {
                    ClientToScreen(hwnd, &mut center);
                }

                let capture_rect = RECT {
                    left: center.x - 208,
                    top: center.y - 208,
                    right: center.x + 208,
                    bottom: center.y + 208,
                };

                if let Some(pixels) = unsafe { capture_screenshot(capture_rect) } {
                    let timestamp = chrono::Local::now().timestamp_millis();
                    let mut coord_parts = Vec::new();
                    for (x, y, w, h) in &players_in_crop {
                        coord_parts.push(format!("{},{},{},{}", x, y, w, h));
                    }
                    let filename = format!("{}_{}.bmp", coord_parts.join("_"), timestamp);

                    self.last_capture = Some(Instant::now());
                    std::thread::spawn(move || {
                        let _ = std::fs::create_dir_all("Data");
                        let path = std::path::Path::new("Data").join(&filename);
                        if let Err(e) = save_bmp(&path, 416, 416, &pixels) {
                            log::error!("Failed to save data collection screenshot: {:?}", e);
                        } else {
                            log::info!("Saved data collection screenshot: {}", filename);
                        }
                    });
                }
            }
        }

        Ok(())
    }

    fn render(
        &self,
        _states: &StateRegistry,
        _ui: &imgui::Ui,
        _unicode_text: &UnicodeTextRenderer,
    ) -> anyhow::Result<()> {
        Ok(())
    }
}
