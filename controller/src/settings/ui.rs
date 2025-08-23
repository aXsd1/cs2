use std::{
    borrow::Cow,
    collections::{
        btree_map::Entry,
        HashMap,
    },
    fs::File,
    io::{
        BufReader,
        Write,
    },
    path::PathBuf,
    sync::{
        atomic::Ordering,
        Arc,
        Mutex,
    },
    thread,
    time::Instant,
};

use anyhow::Context;
use chrono::{
    Datelike,
    Utc};
use chrono_tz::Tz;
use cs2::{
    StateBuildInfo,
    StateCurrentMap,
};
use imgui::{
    Condition,
    ImColor32,
    SelectableFlags,
    StyleColor,
    StyleVar,
    TableColumnFlags,
    TableColumnSetup,
    TableFlags,
    TreeNodeFlags,
};
use obfstr::obfstr;
use overlay::UnicodeTextRenderer;
use serde::Deserialize;
use utils_state::StateRegistry;

use super::{
    Color,
    EspColor,
    EspColorType,
    EspConfig,
    EspSelector,
    GrenadeSettings,
    GrenadeSortOrder,
    GrenadeSpotInfo,
    GrenadeType,
    KeyToggleMode,
};
use crate::{
    enhancements::StateGrenadeHelperPlayerLocation,
    settings::{
        AppSettings,
        EspBoxType,
        EspHeadDot,
        EspHealthBar,
        EspPlayerSettings,
        EspTracePosition,
    },
    utils::{
        ImGuiKey,
        ImguiComboEnum,
    },
    Application,
};

enum EspPlayerActiveHeader {
    Features,
    Style,
}

#[derive(Debug, PartialEq, Eq, Clone)]
enum GrenadeSettingsTarget {
    General,
    MapType(String),
    Map {
        map_name: String,
        display_name: String,
    },
}



// Add these with your other enums
enum UiState {
    Login,
    LoggedIn,
}

// Login işleminin durumunu yönetir
enum LoginStatus {
    Idle,
    InProgress,
    Failed(String),
}

// Login ekranı için gerekli tüm verileri tutar
struct LoginState {
    username: String,
    password: String,
    status: LoginStatus,
    result_handle: Arc<Mutex<Option<Result<String, String>>>>,
}

// Sunucudan gelen JSON yanıtları için struct'lar
#[derive(Deserialize)]
struct VersionsResponse {
    versions: Versions,
}
#[derive(Deserialize)]
struct Versions {
    timezone: String,
    csesp: String,
}

#[derive(Deserialize)]
    struct ServerResponse {
        resultCode: String,
    }

impl GrenadeSettingsTarget {
    pub fn ui_token(&self) -> Cow<'static, str> {
        match self {
            Self::General => "_settings".into(),
            Self::MapType(value) => format!("map_type_{}", value).into(),
            Self::Map { map_name: name, .. } => format!("map_{}", name).into(),
        }
    }

    pub fn ident_level(&self) -> usize {
        match self {
            Self::General => 0,
            Self::MapType(_) => 0,
            Self::Map { .. } => 1,
        }
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
enum GrenadeHelperTransferDirection {
    Export,
    Import,
}

enum GrenadeHelperTransferState {
    /// Currently no transfer in progress
    Idle,
    /// A new transfer should be initiated.
    Pending {
        direction: GrenadeHelperTransferDirection,
    },
    /// A transfer has been initiated.
    /// This might be either an export or import.
    Active {
        direction: GrenadeHelperTransferDirection,
    },
    /// The current transfer failed.
    Failed {
        direction: GrenadeHelperTransferDirection,
        message: String,
    },
    /// The source file has been loaded.
    /// Prompting the user, if he wants to replace or add the new items.
    ImportPending {
        elements: HashMap<String, Vec<GrenadeSpotInfo>>,
    },
    ImportSuccess {
        count: usize,
        replacing: bool,
    },
    ExportSuccess {
        target_path: PathBuf,
    },
}

pub struct SettingsUI {
    ui_state: UiState,
    login_state: LoginState,

    discord_link_copied: Option<Instant>,

    esp_selected_target: EspSelector,
    esp_pending_target: Option<EspSelector>,
    esp_player_active_header: EspPlayerActiveHeader,

    grenade_helper_target: GrenadeSettingsTarget,
    grenade_helper_selected_id: usize,
    grenade_helper_skip_confirmation_dialog: bool,
    grenade_helper_new_item: Option<GrenadeSpotInfo>,
    grenade_helper_transfer_state: Arc<Mutex<GrenadeHelperTransferState>>,

    grenade_helper_pending_target: Option<GrenadeSettingsTarget>,
    grenade_helper_pending_selected_id: Option<usize>,
}

// =================================================================
// YARDIMCI FONKSİYONLAR (HWID & LOGIN MANTIĞI)
// =================================================================

/// Sadece Windows üzerinde derlenir ve klasör sahibinin SID'sini HWID olarak alır.
#[cfg(windows)]
fn get_hwid() -> Result<String, String> {
    use std::{ffi::c_void, ptr};
    use windows_sys::Win32::{
        Foundation::{LocalFree, PSID},
        Security::GetFileSecurityW,
        Security::GetSecurityDescriptorOwner,
        Security::OWNER_SECURITY_INFORMATION,
        Security::Authorization::ConvertSidToStringSidW, // 🔧 Doğru modül!
    };
    use widestring::U16CStr; // 🔧 U16Str değil, U16CStr

    unsafe {
        let path: Vec<u16> = ".".encode_utf16().chain(std::iter::once(0)).collect();
        let mut bytes_needed = 0;

        GetFileSecurityW(
            path.as_ptr(),
            OWNER_SECURITY_INFORMATION,
            ptr::null_mut(),
            0,
            &mut bytes_needed,
        );

        if bytes_needed == 0 {
            return Err("HWID Error: Could not get required buffer size.".to_string());
        }

        let layout = std::alloc::Layout::from_size_align(bytes_needed as usize, 1).unwrap();
        let p_security_descriptor = std::alloc::alloc(layout) as *mut c_void;

        if GetFileSecurityW(
            path.as_ptr(),
            OWNER_SECURITY_INFORMATION,
            p_security_descriptor,
            bytes_needed,
            &mut bytes_needed,
        ) == 0
        {
            std::alloc::dealloc(p_security_descriptor as *mut u8, layout);
            return Err("HWID Error: GetFileSecurityW failed.".to_string());
        }

        let mut p_sid_owner: PSID = ptr::null_mut();
        let mut p_defaulted: i32 = 0;
        if GetSecurityDescriptorOwner(
            p_security_descriptor,
            &mut p_sid_owner,
            &mut p_defaulted,
        ) == 0
        {
            std::alloc::dealloc(p_security_descriptor as *mut u8, layout);
            return Err("HWID Error: GetSecurityDescriptorOwner failed.".to_string());
        }

        let mut sid_string_ptr: *mut u16 = ptr::null_mut();
        if ConvertSidToStringSidW(p_sid_owner, &mut sid_string_ptr) == 0 {
            std::alloc::dealloc(p_security_descriptor as *mut u8, layout);
            return Err("HWID Error: ConvertSidToStringSidW failed.".to_string());
        }

        // 🔧 DÜZELTME: U16CStr::from_ptr_str kullanılıyor
        let sid_string = U16CStr::from_ptr_str(sid_string_ptr)
            .to_string_lossy();

        LocalFree(sid_string_ptr as *mut c_void);
        std::alloc::dealloc(p_security_descriptor as *mut u8, layout);

        Ok(sid_string)
    }
}


/// Windows dışı platformlar için yedek HWID fonksiyonu.
#[cfg(not(windows))]
fn get_hwid() -> Result<String, String> {
    Ok("non-windows-hwid".to_string())
}


/// Tüm karmaşık login mantığını yürüten ana fonksiyon.
fn perform_full_login_check(username: &str, password: &str) -> Result<String, String> {

    const PROGRAM_CSESP_VERSION: &str = "1";

    let client = reqwest::blocking::Client::new();

    // =================================================================
    // ADIM 2: SUNUCUDAN BİLGİLERİ AL
    // =================================================================
    let version_info: VersionsResponse = client.get("https://yeageth.com/versions.php")
        .send().map_err(|e| format!("Network Error: {}", e))?
        .json().map_err(|e| format!("Data Error: {}", e))?;
    
    // Sunucudan gelen versiyon bilgilerini kontrol et
    if version_info.versions.csesp != PROGRAM_CSESP_VERSION {
        // Eğer versiyonlar uyuşmuyorsa, işlemi hemen bitir ve hata döndür.
        return Err("Uygulama sürümü güncel değil. Lütfen güncelleyin.".to_string());
    }

    // =================================================================
    // ADIM 4: YEREL DOĞRULAMA KODUNU HESAPLA
    // =================================================================
    let timezone: Tz = version_info.versions.timezone.parse()
        .map_err(|_| "Invalid timezone from server".to_string())?;

    let now = Utc::now().with_timezone(&timezone);
    let local_code: String = (now.year() as u32 * 365 + now.month() * 30 + now.day())
        .saturating_mul(1344)
        .to_string()
        .chars()
        .map(|c| if c.to_digit(10).unwrap_or(0) % 2 == 0 { '0' } else { '1' })
        .collect();

    // =================================================================
    // ADIM 5: DİĞER KONTROLLER (HWID VE LOGIN)
    // =================================================================
    let hwid = get_hwid()?;

    let params = [("username", username), ("password", password), ("hwid", &hwid),];

    let response = client
        .post("https://yeageth.com/usercheck_csesp.php")
        .form(&params)
        .send()
        .map_err(|e| format!("Login request failed: {}", e))?;

    if !response.status().is_success() {
        return Err(format!("Server returned error: {}", response.status()));
    }

    let data: String = response
        .text()
        .map_err(|_| "Invalid response from server".to_string())?;

    // JSON parse et
    let parsed: ServerResponse =
        serde_json::from_str(&data).map_err(|e| format!("Failed to parse JSON: {}", e))?;

    // Karşılaştırma
    if parsed.resultCode == local_code {
        Ok("Login Successful!".to_string())
    } else {
        Err(match parsed.resultCode.as_str() {
            "1" => "Subscription ended".to_string(),
            "2" => "You don't have access to this product".to_string(),
            "3" => "HWID didn't match".to_string(),
            "4" => "User not found".to_string(),
            "5" => "Wrong password".to_string(),
            _   => "Login failed: Unknown error".to_string(),
        })
    }
}

const VERSION: &str = env!("CARGO_PKG_VERSION");
impl SettingsUI {
    pub fn new() -> Self {
        Self {
            ui_state: UiState::Login,
            login_state: LoginState {
                username: String::with_capacity(64),
                password: String::with_capacity(64),
                status: LoginStatus::Idle,
                result_handle: Arc::new(Mutex::new(None)),
            },
            
            discord_link_copied: None,

            esp_selected_target: EspSelector::None,
            esp_pending_target: None,
            esp_player_active_header: EspPlayerActiveHeader::Features,

            grenade_helper_target: GrenadeSettingsTarget::General,
            grenade_helper_selected_id: 0,
            grenade_helper_new_item: None,
            grenade_helper_skip_confirmation_dialog: false,
            grenade_helper_transfer_state: Arc::new(Mutex::new(GrenadeHelperTransferState::Idle)),

            grenade_helper_pending_target: None,
            grenade_helper_pending_selected_id: None,
        }
    }

    pub fn render(
        &mut self,
        app: &Application,
        ui: &imgui::Ui,
        unicode_text: &UnicodeTextRenderer,
    ) {
        match self.ui_state {
            UiState::Login => self.render_login_screen(app, ui),
            UiState::LoggedIn => self.render_main_ui(app, ui, unicode_text),
        }
    }

    /// Login ekranını çizen fonksiyon.
    fn render_login_screen(&mut self, app: &Application, ui: &imgui::Ui) {
        let display_size = ui.io().display_size;
        let window_size = [400.0, 220.0];
        let window_pos = [(display_size[0] - window_size[0]) * 0.5, (display_size[1] - window_size[1]) * 0.5];

        ui.window(obfstr!("Login"))
            .position(window_pos, Condition::Always)
            .size(window_size, Condition::Always)
            .resizable(false).collapsible(false).title_bar(true)
            .build(|| {
                ui.text_wrapped("Please log in to continue.");
                ui.separator();
                ui.dummy([0.0, 10.0]);

                let is_in_progress = matches!(self.login_state.status, LoginStatus::InProgress);
                let _disable = ui.begin_disabled(is_in_progress);

                ui.set_next_item_width(-1.0); // Tam genişlik
                ui.input_text(obfstr!("Username"), &mut self.login_state.username).build();

                ui.set_next_item_width(-1.0); // Tam genişlik
                ui.input_text(obfstr!("Password"), &mut self.login_state.password).password(true).build();

                ui.dummy([0.0, 10.0]);

                if ui.button_with_size(obfstr!("Login"), [-1.0, 30.0]) {
                    self.login_state.status = LoginStatus::InProgress;
                    let username = self.login_state.username.clone();
                    let password = self.login_state.password.clone();
                    let result_handle = self.login_state.result_handle.clone();

                    // Arka planda login işlemini yürüt
                    thread::spawn(move || {
                        let outcome = perform_full_login_check(&username, &password);
                        *result_handle.lock().unwrap() = Some(outcome);
                    });
                }
                
                drop(_disable);

                // Arka plandan gelen sonucu kontrol et
                if let Ok(mut result_lock) = self.login_state.result_handle.try_lock() {
                    if let Some(result) = result_lock.take() {
                        match result {
                            Ok(_) => {
                                self.ui_state = UiState::LoggedIn;
                                let mut username_state = app.username_state.lock().unwrap();
                                *username_state = Some(self.login_state.username.clone());
                            },
                            Err(e) => self.login_state.status = LoginStatus::Failed(e),
                        }
                    }
                }
                
                // Durum mesajlarını göster
                match &self.login_state.status {
                    LoginStatus::InProgress => ui.text_colored([1.0, 0.76, 0.03, 1.0], "Logging in..."),
                    LoginStatus::Failed(message) => ui.text_colored([1.0, 0.0, 0.0, 1.0], message),
                    LoginStatus::Idle => {},
                }
            });
    }


    pub fn render_main_ui(
        &mut self,
        app: &Application,
        ui: &imgui::Ui,
        _unicode_text: &UnicodeTextRenderer,
    ) {
        let display_size = ui.io().display_size;
        let window_size = [400.0, 120.0];
        let window_pos = [(display_size[0] - window_size[0]) * 0.5, (display_size[1] - window_size[1]) * 0.5];

        ui.window("Welcome")
            .position(window_pos, Condition::Always)
            .size(window_size, Condition::FirstUseEver)
            .resizable(false)
            .collapsible(false)
            .build(|| {
                ui.dummy([0.0, 10.0]);

                let welcome_text = format!("Welcome, {}!", self.login_state.username);

                let text_width = ui.calc_text_size(&welcome_text)[0];
                let window_width = ui.window_size()[0];
                let new_cursor_x = (window_width - text_width) * 0.5;

                // Mevcut Y pozisyonunu al
                let current_cursor_y = ui.cursor_pos()[1];

                // Yeni X ve mevcut Y ile tam cursor pozisyonunu ayarla
                ui.set_cursor_pos([new_cursor_x, current_cursor_y]);

                ui.text(welcome_text);
            });
    }

    fn render_esp_target(
        &mut self,
        settings: &mut AppSettings,
        ui: &imgui::Ui,
        target: &EspSelector,
    ) {
        let config_key = target.config_key();
        let target_enabled = settings
            .esp_settings_enabled
            .get(&config_key)
            .cloned()
            .unwrap_or_default();

        let parent_enabled = target_enabled || {
            let mut current = target.parent();
            while let Some(parent) = current.take() {
                let enabled = settings
                    .esp_settings_enabled
                    .get(&parent.config_key())
                    .cloned()
                    .unwrap_or_default();

                if enabled {
                    current = Some(parent);
                    break;
                }

                current = parent.parent();
            }

            current.is_some()
        };

        {
            let pos_begin = ui.cursor_screen_pos();
            let clicked = ui
                .selectable_config(format!(
                    "{} ##{}",
                    target.config_display(),
                    target.config_key()
                ))
                .selected(target == &self.esp_selected_target)
                .flags(SelectableFlags::SPAN_ALL_COLUMNS)
                .build();

            let indicator_color = if target_enabled {
                ImColor32::from_rgb(0x4C, 0xAF, 0x50)
            } else if parent_enabled {
                ImColor32::from_rgb(0xFF, 0xC1, 0x07)
            } else {
                ImColor32::from_rgb(0xF4, 0x43, 0x36)
            };
            let pos_end = ui.cursor_screen_pos();
            let indicator_radius = ui.current_font_size() * 0.25;

            ui.get_window_draw_list()
                .add_circle(
                    [
                        pos_begin[0] - indicator_radius - 5.0,
                        pos_begin[1] + (pos_end[1] - pos_begin[1]) / 2.0 - indicator_radius / 2.0,
                    ],
                    indicator_radius,
                    indicator_color,
                )
                .filled(true)
                .build();

            if clicked {
                self.esp_pending_target = Some(target.clone());
            }
        }

        let children = target.children();
        if children.len() > 0 {
            ui.indent();
            for child in children.iter() {
                self.render_esp_target(settings, ui, child);
            }
            ui.unindent();
        }
    }

    fn render_esp_settings_player(
        &mut self,
        settings: &mut AppSettings,
        ui: &imgui::Ui,
        target: EspSelector,
    ) {
        let config_key = target.config_key();
        let config_enabled = settings
            .esp_settings_enabled
            .get(&config_key)
            .cloned()
            .unwrap_or_default();

        let config = match settings.esp_settings.entry(config_key.clone()) {
            Entry::Occupied(entry) => {
                let value = entry.into_mut();
                if let EspConfig::Player(value) = value {
                    value
                } else {
                    log::warn!("Detected invalid player config for {}", config_key);
                    *value = EspConfig::Player(EspPlayerSettings::new(&target));
                    if let EspConfig::Player(value) = value {
                        value
                    } else {
                        unreachable!()
                    }
                }
            }
            Entry::Vacant(entry) => {
                if let EspConfig::Player(value) =
                    entry.insert(EspConfig::Player(EspPlayerSettings::new(&target)))
                {
                    value
                } else {
                    unreachable!()
                }
            }
        };
        let _ui_enable_token = ui.begin_enabled(config_enabled);

        let content_height =
            ui.content_region_avail()[1] - ui.text_line_height_with_spacing() * 2.0 - 16.0;
        unsafe {
            imgui::sys::igSetNextItemOpen(
                matches!(
                    self.esp_player_active_header,
                    EspPlayerActiveHeader::Features
                ),
                0,
            );
        };
        if ui.collapsing_header("Features", TreeNodeFlags::empty()) {
            self.esp_player_active_header = EspPlayerActiveHeader::Features;
            if let Some(_token) = {
                ui.child_window("features")
                    .size([0.0, content_height])
                    .begin()
            } {
                ui.indent_by(5.0);
                ui.dummy([0.0, 5.0]);

                const COMBO_WIDTH: f32 = 150.0;
                {
                    const ESP_BOX_TYPES: [(EspBoxType, &'static str); 3] = [
                        (EspBoxType::None, "Off"),
                        (EspBoxType::Box2D, "2D"),
                        (EspBoxType::Box3D, "3D"),
                    ];

                    ui.set_next_item_width(COMBO_WIDTH);
                    ui.combo_enum(obfstr!("player box"), &ESP_BOX_TYPES, &mut config.box_type);
                }

                {
                    #[derive(Debug, Clone, Copy, PartialEq, PartialOrd)]
                    enum PlayerSkeletonType {
                        None,
                        Skeleton,
                    }

                    const PLAYER_SKELETON_TYPES: [(PlayerSkeletonType, &'static str); 2] = [
                        (PlayerSkeletonType::None, "Off"),
                        (PlayerSkeletonType::Skeleton, "On"),
                    ];

                    let mut skeleton_type = if config.skeleton {
                        PlayerSkeletonType::Skeleton
                    } else {
                        PlayerSkeletonType::None
                    };

                    ui.set_next_item_width(COMBO_WIDTH);
                    let value_changed = ui.combo_enum(
                        obfstr!("player skeleton"),
                        &PLAYER_SKELETON_TYPES,
                        &mut skeleton_type,
                    );

                    if value_changed {
                        config.skeleton = matches!(skeleton_type, PlayerSkeletonType::Skeleton);
                    }
                }

                {
                    const HEAD_DOT_TYPES: [(EspHeadDot, &'static str); 3] = [
                        (EspHeadDot::None, "Off"),
                        (EspHeadDot::Filled, "Filled"),
                        (EspHeadDot::NotFilled, "Outlined"),
                    ];

                    ui.set_next_item_width(COMBO_WIDTH);
                    ui.combo_enum(obfstr!("head dot"), &HEAD_DOT_TYPES, &mut config.head_dot);
                }

                {
                    const TRACER_LINE_TYPES: [(EspTracePosition, &'static str); 7] = [
                        (EspTracePosition::None, "Off"),
                        (EspTracePosition::TopLeft, "Top left"),
                        (EspTracePosition::TopCenter, "Top center"),
                        (EspTracePosition::TopRight, "Top right"),
                        (EspTracePosition::BottomLeft, "Bottom left"),
                        (EspTracePosition::BottomCenter, "Bottom center"),
                        (EspTracePosition::BottomRight, "Bottom right"),
                    ];

                    ui.set_next_item_width(COMBO_WIDTH);
                    ui.combo_enum(
                        obfstr!("tracer lines"),
                        &TRACER_LINE_TYPES,
                        &mut config.tracer_lines,
                    );
                }

                {
                    const HEALTH_BAR_TYPES: [(EspHealthBar, &'static str); 5] = [
                        (EspHealthBar::None, "Off"),
                        (EspHealthBar::Top, "Top"),
                        (EspHealthBar::Left, "Left"),
                        (EspHealthBar::Bottom, "Bottom"),
                        (EspHealthBar::Right, "Right"),
                    ];

                    ui.set_next_item_width(COMBO_WIDTH);
                    ui.combo_enum(
                        obfstr!("player health bar"),
                        &HEALTH_BAR_TYPES,
                        &mut config.health_bar,
                    );
                }
                ui.dummy([0.0, 10.0]);

                ui.text("Player Info");
                ui.checkbox(obfstr!("Name"), &mut config.info_name);
                ui.checkbox(obfstr!("Weapon"), &mut config.info_weapon);
                ui.checkbox(obfstr!("Distance"), &mut config.info_distance);
                ui.checkbox(obfstr!("Health"), &mut config.info_hp_text);
                ui.checkbox(obfstr!("Kit"), &mut config.info_flag_kit);
                ui.checkbox(obfstr!("Flashed"), &mut config.info_flag_flashed);
                ui.checkbox(obfstr!("Near only"), &mut config.near_players);
                if config.near_players {
                    ui.same_line();
                    ui.slider_config("Max distance", 0.0, 50.0)
                        .build(&mut config.near_players_distance);
                }
            }
        }

        unsafe {
            imgui::sys::igSetNextItemOpen(
                matches!(self.esp_player_active_header, EspPlayerActiveHeader::Style),
                0,
            );
        };
        if ui.collapsing_header("Style & Colors", TreeNodeFlags::empty()) {
            self.esp_player_active_header = EspPlayerActiveHeader::Style;
            if let Some(_token) = {
                ui.child_window("styles")
                    .size([0.0, content_height])
                    .begin()
            } {
                ui.indent_by(5.0);
                ui.dummy([0.0, 5.0]);

                if let Some(_token) = {
                    let mut column_type = TableColumnSetup::new("Type");
                    column_type.init_width_or_weight = 130.0;
                    column_type.flags = TableColumnFlags::WIDTH_FIXED;

                    let mut column_value = TableColumnSetup::new("Value");
                    column_value.init_width_or_weight = 160.0;
                    column_value.flags = TableColumnFlags::WIDTH_FIXED;

                    ui.begin_table_header_with_flags(
                        "styles_table",
                        [TableColumnSetup::new("Name"), column_type, column_value],
                        TableFlags::ROW_BG
                            | TableFlags::BORDERS
                            | TableFlags::SIZING_STRETCH_PROP
                            | TableFlags::SCROLL_Y,
                    )
                } {
                    ui.table_next_row();
                    Self::render_esp_settings_player_style_color(
                        ui,
                        obfstr!("ESP box color"),
                        &mut config.box_color,
                    );

                    ui.table_next_row();
                    Self::render_esp_settings_player_style_width(
                        ui,
                        obfstr!("ESP box width"),
                        1.0,
                        10.0,
                        &mut config.box_width,
                    );

                    ui.table_next_row();
                    Self::render_esp_settings_player_style_color(
                        ui,
                        obfstr!("Player skeleton color"),
                        &mut config.skeleton_color,
                    );

                    ui.table_next_row();
                    Self::render_esp_settings_player_style_width(
                        ui,
                        obfstr!("Player skeleton width"),
                        1.0,
                        10.0,
                        &mut config.skeleton_width,
                    );

                    ui.table_next_row();
                    Self::render_esp_settings_player_style_color(
                        ui,
                        obfstr!("Head dot color"),
                        &mut config.head_dot_color,
                    );

                    ui.table_next_row();
                    Self::render_esp_settings_player_style_width(
                        ui,
                        obfstr!("Head dot thickness"),
                        1.0,
                        5.0,
                        &mut config.head_dot_thickness,
                    );

                    ui.table_next_row();
                    Self::render_esp_settings_player_style_width(
                        ui,
                        obfstr!("Head dot radius"),
                        0.0,
                        10.0,
                        &mut config.head_dot_base_radius,
                    );

                    ui.table_next_row();
                    Self::render_esp_settings_player_style_width(
                        ui,
                        obfstr!("Head dot z offset"),
                        0.0,
                        10.0,
                        &mut config.head_dot_z,
                    );

                    ui.table_next_row();
                    Self::render_esp_settings_player_style_width(
                        ui,
                        obfstr!("Health bar width"),
                        5.0,
                        30.0,
                        &mut config.health_bar_width,
                    );

                    ui.table_next_row();
                    Self::render_esp_settings_player_style_color(
                        ui,
                        obfstr!("Tracer line color"),
                        &mut config.tracer_lines_color,
                    );

                    ui.table_next_row();
                    Self::render_esp_settings_player_style_width(
                        ui,
                        obfstr!("Tracer line width"),
                        1.0,
                        10.0,
                        &mut config.tracer_lines_width,
                    );

                    ui.table_next_row();
                    Self::render_esp_settings_player_style_color(
                        ui,
                        obfstr!("Color info name"),
                        &mut config.info_name_color,
                    );

                    ui.table_next_row();
                    Self::render_esp_settings_player_style_color(
                        ui,
                        obfstr!("Color info distance"),
                        &mut config.info_distance_color,
                    );

                    ui.table_next_row();
                    Self::render_esp_settings_player_style_color(
                        ui,
                        obfstr!("Color info weapon"),
                        &mut config.info_weapon_color,
                    );

                    ui.table_next_row();
                    Self::render_esp_settings_player_style_color(
                        ui,
                        obfstr!("Color info health"),
                        &mut config.info_hp_text_color,
                    );

                    ui.table_next_row();
                    Self::render_esp_settings_player_style_color(
                        ui,
                        obfstr!("Color info player flags"),
                        &mut config.info_flags_color,
                    );
                }
            }
        }

        drop(_ui_enable_token);
    }

    fn render_esp_settings_player_style_width(
        ui: &imgui::Ui,
        label: &str,
        min: f32,
        max: f32,
        value: &mut f32,
    ) -> bool {
        ui.table_next_column();
        ui.text(label);

        ui.table_next_column();
        ui.text(&format!("{:.2} - {:.2}", min, max));

        ui.table_next_column();
        if {
            ui.input_float(&format!("##{}_style_width", ui.table_row_index()), value)
                .build()
        } {
            *value = value.clamp(min, max);
            true
        } else {
            false
        }
    }

    fn render_esp_settings_player_style_color(ui: &imgui::Ui, label: &str, color: &mut EspColor) {
        ui.table_next_column();
        ui.text(label);

        ui.table_next_column();
        {
            let mut color_type = EspColorType::from_esp_color(color);
            ui.set_next_item_width(ui.content_region_avail()[0]);
            let color_type_changed = ui.combo_enum(
                &format!("##{}_color_type", ui.table_row_index()),
                &[
                    (EspColorType::Static, "Static"),
                    (EspColorType::HealthBased, "Health based"),
                    (EspColorType::HealthBasedRainbow, "Rainbow"),
                    (EspColorType::DistanceBased, "Distance"),
                ],
                &mut color_type,
            );

            if color_type_changed {
                *color = match color_type {
                    EspColorType::Static => EspColor::Static {
                        value: Color::from_f32([1.0, 1.0, 1.0, 1.0]),
                    },
                    EspColorType::HealthBased => EspColor::HealthBased {
                        max: Color::from_f32([0.0, 1.0, 0.0, 1.0]),
                        mid: Color::from_f32([1.0, 1.0, 0.0, 1.0]),
                        min: Color::from_f32([1.0, 0.0, 0.0, 1.0]),
                    },
                    EspColorType::HealthBasedRainbow => EspColor::HealthBasedRainbow { alpha: 1.0 },
                    EspColorType::DistanceBased => EspColor::DistanceBased {
                        near: Color::from_f32([1.0, 0.0, 0.0, 1.0]),
                        mid: Color::from_f32([1.0, 1.0, 0.0, 1.0]),
                        far: Color::from_f32([0.0, 1.0, 0.0, 1.0]),
                    },
                }
            }
        }

        ui.table_next_column();
        {
            match color {
                EspColor::HealthBasedRainbow { alpha } => {
                    ui.text("Alpha:");
                    ui.same_line();
                    ui.set_next_item_width(100.0);
                    ui.slider_config(
                        &format!("##{}_rainbow_alpha", ui.table_row_index()),
                        0.1,
                        1.0,
                    )
                    .display_format("%.2f")
                    .build(alpha);
                }
                EspColor::Static { value } => {
                    let mut color_value = value.as_f32();

                    if {
                        ui.color_edit4_config(
                            &format!("##{}_static_value", ui.table_row_index()),
                            &mut color_value,
                        )
                        .alpha_bar(true)
                        .inputs(false)
                        .label(false)
                        .build()
                    } {
                        *value = Color::from_f32(color_value);
                    }
                }
                EspColor::HealthBased { max, mid, min } => {
                    let mut max_value = max.as_f32();
                    if {
                        ui.color_edit4_config(
                            &format!("##{}_health_max", ui.table_row_index()),
                            &mut max_value,
                        )
                        .alpha_bar(true)
                        .inputs(false)
                        .label(false)
                        .build()
                    } {
                        *max = Color::from_f32(max_value);
                    }
                    ui.same_line();
                    ui.text(" => ");
                    ui.same_line();

                    let mut mid_value = mid.as_f32();
                    if {
                        ui.color_edit4_config(
                            &format!("##{}_health_mid", ui.table_row_index()),
                            &mut mid_value,
                        )
                        .alpha_bar(true)
                        .inputs(false)
                        .label(false)
                        .build()
                    } {
                        *mid = Color::from_f32(mid_value);
                    }
                    ui.same_line();
                    ui.text(" => ");
                    ui.same_line();

                    let mut min_value = min.as_f32();
                    if {
                        ui.color_edit4_config(
                            &format!("##{}_health_min", ui.table_row_index()),
                            &mut min_value,
                        )
                        .alpha_bar(true)
                        .inputs(false)
                        .label(false)
                        .build()
                    } {
                        *min = Color::from_f32(min_value);
                    }
                }
                EspColor::DistanceBased { near, mid, far } => {
                    let mut near_color = near.as_f32();
                    if ui
                        .color_edit4_config(
                            &format!("##{}_near", ui.table_row_index()),
                            &mut near_color,
                        )
                        .alpha_bar(true)
                        .inputs(false)
                        .label(false)
                        .build()
                    {
                        *near = Color::from_f32(near_color);
                    }

                    ui.same_line();
                    ui.text(" => ");
                    ui.same_line();
                    let mut mid_color = mid.as_f32();
                    if ui
                        .color_edit4_config(
                            &format!("##{}_mid", ui.table_row_index()),
                            &mut mid_color,
                        )
                        .alpha_bar(true)
                        .inputs(false)
                        .label(false)
                        .build()
                    {
                        *mid = Color::from_f32(mid_color);
                    }

                    ui.same_line();
                    ui.text(" => ");
                    ui.same_line();
                    let mut far_color = far.as_f32();
                    if ui
                        .color_edit4_config(
                            &format!("##{}_far", ui.table_row_index()),
                            &mut far_color,
                        )
                        .alpha_bar(true)
                        .inputs(false)
                        .label(false)
                        .build()
                    {
                        *far = Color::from_f32(far_color);
                    }
                }
            }
        }
    }

    fn render_esp_settings_chicken(
        &mut self,
        _settings: &mut AppSettings,
        ui: &imgui::Ui,
        _target: EspSelector,
    ) {
        ui.text("Chicken!");
    }

    fn render_esp_settings_weapon(
        &mut self,
        _settings: &mut AppSettings,
        ui: &imgui::Ui,
        _target: EspSelector,
    ) {
        ui.text("Weapon!");
    }

    fn render_esp_settings(&mut self, settings: &mut AppSettings, ui: &imgui::Ui) {
        if let Some(target) = self.esp_pending_target.take() {
            self.esp_selected_target = target;
        }

        /* the left tree */
        let content_region = ui.content_region_avail();
        let original_style = ui.clone_style();
        let tree_width = (content_region[0] * 0.25).max(150.0);
        let content_width = (content_region[0] - tree_width - 5.0).max(300.0);

        ui.text("ESP Target");
        ui.same_line_with_pos(
            original_style.window_padding[0] * 2.0 + tree_width + original_style.window_border_size,
        );
        if !matches!(self.esp_selected_target, EspSelector::None) {
            let target_key = self.esp_selected_target.config_key();
            let target_enabled = settings
                .esp_settings_enabled
                .entry(target_key.to_string())
                .or_insert(false);

            ui.checkbox(self.esp_selected_target.config_title(), target_enabled);

            let reset_text = "Reset config";
            let reset_text_width = ui.calc_text_size(&reset_text)[0];

            let total_width = ui.content_region_avail()[0] + 2.0;
            ui.same_line_with_pos(total_width - reset_text_width);

            let _enabled = ui.begin_enabled(*target_enabled);
            if ui.button(reset_text) {
                /* just removing the key will work as a default config will be emplaced later */
                settings.esp_settings.remove(&target_key);
            }
        } else {
            ui.text("Target Configuration");
        };

        //ui.dummy([0.0, 10.0]);

        if let (Some(_token), _padding) = {
            let padding = ui.push_style_var(StyleVar::WindowPadding([
                0.0,
                original_style.window_padding[1],
            ]));
            let window = ui
                .child_window("ESP Target")
                .size([tree_width, 0.0])
                .border(true)
                .draw_background(true)
                .scroll_bar(true)
                .begin();

            (window, padding)
        } {
            ui.indent_by(
                original_style.window_padding[0] +
                    /* for the indicator */
                    ui.current_font_size() * 0.5 + 4.0,
            );

            self.render_esp_target(settings, ui, &EspSelector::Player);
            // self.render_esp_target(settings, ui, &EspSelector::Chicken);
            // self.render_esp_target(settings, ui, &EspSelector::Weapon)
        }
        ui.same_line();
        if let Some(_token) = {
            ui.child_window("Content")
                .size([content_width, 0.0])
                .scroll_bar(true)
                .begin()
        } {
            match &self.esp_selected_target {
                EspSelector::None => {}
                EspSelector::Player
                | EspSelector::PlayerTeam { .. }
                | EspSelector::PlayerTeamVisibility { .. } => {
                    self.render_esp_settings_player(settings, ui, self.esp_selected_target.clone())
                }
                EspSelector::Chicken => {
                    self.render_esp_settings_chicken(settings, ui, self.esp_selected_target.clone())
                }
                EspSelector::Weapon
                | EspSelector::WeaponGroup { .. }
                | EspSelector::WeaponSingle { .. } => {
                    self.render_esp_settings_weapon(settings, ui, self.esp_selected_target.clone())
                }
            }
        }
    }

    fn render_grenade_target(
        &mut self,
        settings: &mut GrenadeSettings,
        ui: &imgui::Ui,
        target: &GrenadeSettingsTarget,
    ) {
        let ident = ui.clone_style().indent_spacing * target.ident_level() as f32;
        if ident > 0.0 {
            ui.indent_by(ident);
        }

        let item_text = match target {
            GrenadeSettingsTarget::General => "Settings".to_string(),
            GrenadeSettingsTarget::MapType(value) => value.clone(),
            GrenadeSettingsTarget::Map {
                map_name,
                display_name,
            } => {
                let location_count = settings.map_spots.get(map_name).map(Vec::len).unwrap_or(0);
                format!(
                    "{} ({}) ##{}",
                    display_name,
                    location_count,
                    target.ui_token()
                )
            }
        };

        let clicked = ui
            .selectable_config(item_text)
            .selected(target == &self.grenade_helper_target)
            .flags(SelectableFlags::SPAN_ALL_COLUMNS)
            .build();

        if clicked && !matches!(target, GrenadeSettingsTarget::MapType(_)) {
            self.grenade_helper_pending_target = Some(target.clone());
        }

        if ident > 0.0 {
            ui.unindent_by(ident);
        }
    }

    fn render_grenade_helper(
        &mut self,
        states: &StateRegistry,
        settings: &mut GrenadeSettings,
        ui: &imgui::Ui,
        unicode_text: &UnicodeTextRenderer,
    ) {
        if let Some(target) = self.grenade_helper_pending_target.take() {
            self.grenade_helper_target = target;
            self.grenade_helper_selected_id = 0;
            self.grenade_helper_new_item = None;
        }

        if let Some(target) = self.grenade_helper_pending_selected_id.take() {
            self.grenade_helper_selected_id = target;
            self.grenade_helper_new_item = None;
        }

        /* the left tree */
        let content_region = ui.content_region_avail();
        let original_style = ui.clone_style();
        let tree_width = (content_region[0] * 0.25).max(150.0);
        let content_width = content_region[0] - tree_width - 5.0;

        ui.text("Grenade Helper");

        ui.same_line_with_pos(
            original_style.window_padding[0] * 2.0 + tree_width + original_style.window_border_size,
        );
        ui.text("");

        {
            let text_import = "Import";
            let text_import_width = ui.calc_text_size(&text_import)[0];

            let text_export = "Export";
            let text_export_width = ui.calc_text_size(&text_export)[0];

            let total_width = ui.content_region_avail()[0] + 2.0;

            let mut grenade_helper_transfer_state =
                self.grenade_helper_transfer_state.lock().unwrap();
            let _buttons_disabled = ui.begin_disabled(!matches!(
                &*grenade_helper_transfer_state,
                GrenadeHelperTransferState::Idle
            ));
            ui.same_line_with_pos(
                total_width
                    - text_export_width
                    - original_style.frame_padding[0] * 2.0
                    - text_import_width
                    - original_style.frame_padding[0] * 2.0,
            );
            if ui.button(text_export) {
                *grenade_helper_transfer_state = GrenadeHelperTransferState::Pending {
                    direction: GrenadeHelperTransferDirection::Export,
                };
            }

            ui.same_line_with_pos(total_width - text_import_width);
            if ui.button(text_import) {
                *grenade_helper_transfer_state = GrenadeHelperTransferState::Pending {
                    direction: GrenadeHelperTransferDirection::Import,
                };
            }
        }

        //ui.dummy([0.0, 10.0]);

        if let (Some(_token), _padding) = {
            let padding = ui.push_style_var(StyleVar::WindowPadding([
                0.0,
                original_style.window_padding[1],
            ]));
            let window = ui
                .child_window("Helper Target")
                .size([tree_width, 0.0])
                .border(true)
                .draw_background(true)
                .scroll_bar(true)
                .begin();

            (window, padding)
        } {
            ui.indent_by(original_style.window_padding[0] + 4.0);

            for target in [
                GrenadeSettingsTarget::General,
                GrenadeSettingsTarget::MapType("Competitive Maps".to_owned()),
                GrenadeSettingsTarget::Map {
                    map_name: "de_ancient".to_owned(),
                    display_name: "Ancient".to_owned(),
                },
                GrenadeSettingsTarget::Map {
                    map_name: "de_anubis".to_owned(),
                    display_name: "Anubis".to_owned(),
                },
                GrenadeSettingsTarget::Map {
                    map_name: "de_dust2".to_owned(),
                    display_name: "Dust 2".to_owned(),
                },
                GrenadeSettingsTarget::Map {
                    map_name: "de_inferno".to_owned(),
                    display_name: "Inferno".to_owned(),
                },
                GrenadeSettingsTarget::Map {
                    map_name: "de_mills".to_owned(),
                    display_name: "Mills".to_owned(),
                },
                GrenadeSettingsTarget::Map {
                    map_name: "de_mirage".to_owned(),
                    display_name: "Mirage".to_owned(),
                },
                GrenadeSettingsTarget::Map {
                    map_name: "de_nuke".to_owned(),
                    display_name: "Nuke".to_owned(),
                },
                GrenadeSettingsTarget::Map {
                    map_name: "cs_office".to_owned(),
                    display_name: "Office".to_owned(),
                },
                GrenadeSettingsTarget::Map {
                    map_name: "de_overpass".to_owned(),
                    display_name: "Overpass".to_owned(),
                },
                GrenadeSettingsTarget::Map {
                    map_name: "de_thera".to_owned(),
                    display_name: "Thera".to_owned(),
                },
                GrenadeSettingsTarget::Map {
                    map_name: "de_vertigo".to_owned(),
                    display_name: "Vertigo".to_owned(),
                },
            ] {
                self.render_grenade_target(settings, ui, &target);
            }
        }
        ui.same_line();
        if let Some(_token) = {
            ui.child_window("Content")
                .size([content_width, 0.0])
                .scroll_bar(true)
                .begin()
        } {
            match &self.grenade_helper_target {
                GrenadeSettingsTarget::General => {
                    self.render_grenade_helper_target_settings(states, settings, ui);
                }
                GrenadeSettingsTarget::MapType(_) => { /* Nothing to render */ }
                GrenadeSettingsTarget::Map { map_name, .. } => {
                    self.render_grenade_helper_target_map(
                        states,
                        settings,
                        ui,
                        &map_name.clone(),
                        unicode_text,
                    );
                }
            }
        }
    }

    fn render_grenade_helper_target_map(
        &mut self,
        states: &StateRegistry,
        settings: &mut GrenadeSettings,
        ui: &imgui::Ui,
        map_name: &str,
        unicode_text: &UnicodeTextRenderer,
    ) {
        /* the left tree */
        let content_region = ui.content_region_avail();
        let original_style = ui.clone_style();
        let tree_width = (content_region[0] * 0.25).max(150.0);
        let content_width = content_region[0] - tree_width - original_style.item_spacing[0];

        /* The list itself */
        {
            ui.text("Available spots");
            let text_width = ui.calc_text_size("Available spots")[0];
            let button_width = tree_width - text_width - original_style.item_spacing[0];

            ui.same_line();

            ui.set_next_item_width(button_width);
            ui.combo_enum(
                "##sort_type",
                &[
                    (GrenadeSortOrder::Alphabetical, "A-z"),
                    (GrenadeSortOrder::AlphabeticalReverse, "Z-a"),
                ],
                &mut settings.ui_sort_order,
            );

            if let (Some(_token), _padding) = {
                let padding = ui.push_style_var(StyleVar::WindowPadding([
                    0.0,
                    original_style.window_padding[1],
                ]));
                let window = ui
                    .child_window("Map Target")
                    .size([
                        tree_width,
                        content_region[1]
                            - ui.text_line_height_with_spacing() * 2.0
                            - original_style.frame_padding[1] * 4.0,
                    ])
                    .border(true)
                    .draw_background(true)
                    .scroll_bar(true)
                    .begin();

                (window, padding)
            } {
                ui.indent_by(original_style.window_padding[0]);

                if let Some(grenades) = settings.map_spots.get(map_name) {
                    let mut sorted_grenades = grenades.iter().collect::<Vec<_>>();
                    settings.ui_sort_order.sort(&mut sorted_grenades);

                    for grenade in sorted_grenades.iter() {
                        let grenade_types = grenade
                            .grenade_types
                            .iter()
                            .map(GrenadeType::display_name)
                            .collect::<Vec<_>>()
                            .join(", ");

                        let clicked = ui
                            .selectable_config(format!(
                                "{} ({}) ##{}",
                                grenade.name, grenade_types, grenade.id
                            ))
                            .selected(grenade.id == self.grenade_helper_selected_id)
                            .flags(SelectableFlags::SPAN_ALL_COLUMNS)
                            .build();
                        unicode_text.register_unicode_text(&grenade.name);

                        if clicked {
                            self.grenade_helper_pending_selected_id = Some(grenade.id);
                        }
                    }
                }
            }

            /* Add / delete buttons */
            {
                let mut delete_current_grenade = false;
                let current_grenade_position = settings
                    .map_spots
                    .get(map_name)
                    .map(|spots| {
                        spots
                            .iter()
                            .position(|spot| spot.id == self.grenade_helper_selected_id)
                    })
                    .flatten();

                let button_width = (tree_width - original_style.item_spacing[0]) / 2.0;
                ui.set_cursor_pos([
                    0.0,
                    content_region[1]
                        - ui.text_line_height()
                        - original_style.frame_padding[1] * 2.0,
                ]);
                if ui.button_with_size("New", [button_width, 0.0]) {
                    self.grenade_helper_new_item = Some(Default::default());
                    self.grenade_helper_selected_id = 0;
                }

                let _button_disabled = ui.begin_disabled(current_grenade_position.is_none());
                ui.same_line();
                if ui.button_with_size("Delete", [button_width, 0.0]) {
                    if self.grenade_helper_skip_confirmation_dialog {
                        delete_current_grenade = true;
                    } else {
                        ui.open_popup("Delete item? ##delete_grenade_helper_spot");
                    }
                }

                if let Some(_token) = ui
                    .modal_popup_config("Delete item? ##delete_grenade_helper_spot")
                    .resizable(false)
                    .movable(false)
                    .always_auto_resize(true)
                    .begin_popup()
                {
                    ui.text("Are you sure you want to delete this item?");
                    ui.spacing();
                    ui.separator();
                    ui.spacing();
                    ui.checkbox(
                        "do not ask again",
                        &mut self.grenade_helper_skip_confirmation_dialog,
                    );

                    let button_width =
                        (ui.content_region_avail()[0] - original_style.item_spacing[0]) / 2.0;
                    if ui.button_with_size("Yes", [button_width, 0.0]) {
                        ui.close_current_popup();
                        delete_current_grenade = true;
                    }

                    ui.same_line();
                    if ui.button_with_size("No", [button_width, 0.0]) {
                        ui.close_current_popup();
                    }
                }

                if delete_current_grenade {
                    if let Some(grenades) = settings.map_spots.get_mut(map_name) {
                        grenades.remove(current_grenade_position.unwrap());
                    }
                }
            }
        }

        /* grenade info */
        ui.set_cursor_pos([tree_width + original_style.item_spacing[0], 0.0]);
        if let Some(_token) = {
            ui.child_window("Content")
                .size([content_width, 0.0])
                .scroll_bar(true)
                .begin()
        } {
            if let Some(current_grenade) = {
                settings
                    .map_spots
                    .get_mut(map_name)
                    .map(|spots| {
                        spots
                            .iter_mut()
                            .find(|spot| spot.id == self.grenade_helper_selected_id)
                    })
                    .flatten()
                    .or(self.grenade_helper_new_item.as_mut())
            } {
                let mut assign_current_position = false;
                let _full_width = ui.push_item_width(-1.0);

                if current_grenade.id > 0 {
                    ui.text("Grenade Info");
                } else {
                    ui.text("Add a new grenade spot");
                }

                ui.text("Name");
                ui.input_text("##grenade_helper_spot_name", &mut current_grenade.name)
                    .build();
                unicode_text.register_unicode_text(&current_grenade.name);

                ui.text("Description");
                ui.input_text_multiline(
                    "##grenade_helper_spot_description",
                    &mut current_grenade.description,
                    [0.0, 100.0],
                )
                .build();
                unicode_text.register_unicode_text(&current_grenade.description);

                ui.text("Eye position");
                ui.input_float3(
                    "##grenade_helper_spot_eye_position",
                    &mut current_grenade.eye_position,
                )
                .display_format("%.3f")
                .build();

                ui.text("Pitch/Yaw");
                ui.input_float2(
                    "##grenade_helper_spot_ptch_yaw",
                    &mut current_grenade.eye_direction,
                )
                .display_format("%.3f")
                .build();

                let current_map = states
                    .get::<StateCurrentMap>(())
                    .map(|value| value.current_map.clone())
                    .flatten();

                let current_player_position = states
                    .resolve::<StateGrenadeHelperPlayerLocation>(())
                    .map(|value| {
                        if let StateGrenadeHelperPlayerLocation::Valid {
                            eye_position,
                            eye_direction,
                        } = *value
                        {
                            Some((eye_position, eye_direction))
                        } else {
                            None
                        }
                    });

                {
                    let button_enabled =
                        current_player_position.as_ref().unwrap_or(&None).is_some();
                    let _enabled_token = ui.begin_enabled(button_enabled);
                    if ui.button("Use current") {
                        if current_map
                            .as_ref()
                            .map(|current_map| current_map == map_name)
                            .unwrap_or(false)
                        {
                            assign_current_position = true;
                        } else {
                            /* Map differs */
                            ui.open_popup(
                                "Are you sure?##grenade_helper_use_current_map_different",
                            );
                        }
                    }

                    if ui.is_item_hovered() {
                        match &current_player_position {
                            Ok(Some(_)) => {
                                ui.tooltip_text("Copy your current location and direction")
                            }
                            Ok(None) => ui.tooltip_text("You don't have a valid player position"),
                            Err(err) => ui.tooltip_text(format!("Error: {:#}", err)),
                        }
                    }
                }

                if let Some(_token) = ui
                    .modal_popup_config("Are you sure?##grenade_helper_use_current_map_different")
                    .resizable(false)
                    .always_auto_resize(true)
                    .begin_popup()
                {
                    ui.text("The current map does not match the selected map.");
                    ui.text(format!("Selected map: {}", map_name));
                    ui.text(format!(
                        "Current map: {}",
                        current_map
                            .as_ref()
                            .map(String::as_str)
                            .unwrap_or("unknown")
                    ));
                    ui.new_line();
                    ui.text("Do you want to copy the location anyways?");

                    ui.spacing();
                    ui.separator();
                    ui.spacing();

                    let button_width =
                        (ui.content_region_avail()[0] - original_style.item_spacing[0]) / 2.0;
                    if ui.button_with_size("Yes", [button_width, 0.0]) {
                        ui.close_current_popup();
                        assign_current_position = true;
                    }

                    ui.same_line();
                    if ui.button_with_size("No", [button_width, 0.0]) {
                        ui.close_current_popup();
                    }
                }

                if assign_current_position {
                    if let Some((eye_position, eye_direction)) =
                        current_player_position.ok().flatten()
                    {
                        current_grenade.eye_position = eye_position.as_slice().try_into().unwrap();
                        current_grenade.eye_direction =
                            eye_direction.as_slice().try_into().unwrap();
                    }
                }

                for grenade_type in [
                    GrenadeType::Smoke,
                    GrenadeType::Flashbang,
                    GrenadeType::Explosive,
                    GrenadeType::Molotov,
                ] {
                    let current_position = current_grenade
                        .grenade_types
                        .iter()
                        .position(|value| *value == grenade_type);

                    let mut enabled = current_position.is_some();
                    if ui.checkbox(grenade_type.display_name(), &mut enabled) {
                        if let Some(current_position) = current_position {
                            current_grenade.grenade_types.remove(current_position);
                        } else {
                            current_grenade.grenade_types.push(grenade_type);
                        }
                    }
                }

                if current_grenade.id == 0 {
                    let region_avail = ui.content_region_max();
                    ui.set_cursor_pos([region_avail[0] - 100.0, ui.cursor_pos()[1]]);
                    if ui.button_with_size("Create", [100.0, 0.0]) {
                        if let Some(mut grenade) = self.grenade_helper_new_item.take() {
                            let grenades =
                                settings.map_spots.entry(map_name.to_string()).or_default();

                            grenade.id = GrenadeSpotInfo::new_id();
                            self.grenade_helper_pending_selected_id = Some(grenade.id);

                            grenades.push(grenade);
                        }
                    }
                }
            } else {
                let text = "Please select an item";
                let text_bounds = ui.calc_text_size(text);
                let region_avail = ui.content_region_avail();

                ui.set_cursor_pos([
                    (region_avail[0] - text_bounds[0]) / 2.0,
                    (region_avail[1] - text_bounds[1]) / 2.0,
                ]);

                ui.text_colored(
                    ui.style_color(StyleColor::TextDisabled),
                    "Please select a grenade",
                );
            }
        }
    }

    fn render_grenade_helper_target_settings(
        &mut self,
        _states: &StateRegistry,
        settings: &mut GrenadeSettings,
        ui: &imgui::Ui,
    ) {
        fn render_color(ui: &imgui::Ui, label: &str, value: &mut Color) {
            let mut color_value = value.as_f32();

            if {
                ui.color_edit4_config(label, &mut color_value)
                    .alpha_bar(true)
                    .inputs(false)
                    .label(true)
                    .build()
            } {
                *value = Color::from_f32(color_value);
            }
        }

        ui.text("UI Settings");
        ui.spacing();

        ui.input_float("Circle distance", &mut settings.circle_distance)
            .build();
        ui.input_float("Circle radius", &mut settings.circle_radius)
            .build();
        ui.input_scalar("Circle segments", &mut settings.circle_segments)
            .build();

        ui.input_float("Angle threshold yar", &mut settings.angle_threshold_yaw)
            .build();
        ui.input_float("Angle threshold pitch", &mut settings.angle_threshold_pitch)
            .build();

        render_color(ui, "Color position", &mut settings.color_position);
        render_color(
            ui,
            "Color position (active)",
            &mut settings.color_position_active,
        );
        render_color(ui, "Color angle", &mut settings.color_angle);
        render_color(
            ui,
            "Color angle  (active)",
            &mut settings.color_angle_active,
        );

        ui.checkbox(
            obfstr!("ViewBox Background"),
            &mut settings.grenade_background,
        );
    }

    fn render_grenade_helper_transfer(&mut self, settings: &mut GrenadeSettings, ui: &imgui::Ui) {
        let mut transfer_state = self.grenade_helper_transfer_state.lock().unwrap();
        match &*transfer_state {
            GrenadeHelperTransferState::Idle => return,

            GrenadeHelperTransferState::Pending { direction } => {
                let executor: Box<
                    dyn FnOnce() -> anyhow::Result<GrenadeHelperTransferState> + Send,
                > = match direction {
                    GrenadeHelperTransferDirection::Export => {
                        let items = settings.map_spots.clone();
                        Box::new(move || {
                            // GrenadeHelperTransferState
                            let Some(target_path) = rfd::FileDialog::new()
                                .add_filter("Grenade Spots", &["vgs"])
                                .save_file()
                            else {
                                return Ok(GrenadeHelperTransferState::Idle);
                            };

                            let items = serde_json::to_string(&items)?;
                            let mut output = File::options()
                                .create(true)
                                .truncate(true)
                                .write(true)
                                .open(&target_path)
                                .context("open destination")?;
                            output.write_all(items.as_bytes()).context("write")?;

                            Ok(GrenadeHelperTransferState::ExportSuccess { target_path })
                        })
                    }
                    GrenadeHelperTransferDirection::Import => {
                        Box::new(move || {
                            // GrenadeHelperTransferState
                            let Some(target_path) = rfd::FileDialog::new()
                                .add_filter("Grenade Spots", &["vgs"])
                                .pick_file()
                            else {
                                return Ok(GrenadeHelperTransferState::Idle);
                            };

                            let input = File::options()
                                .read(true)
                                .open(target_path)
                                .context("open file")?;

                            let elements = serde_json::from_reader(&mut BufReader::new(input))
                                .context("parse file")?;

                            Ok(GrenadeHelperTransferState::ImportPending { elements })
                        })
                    }
                };

                thread::spawn({
                    let direction = direction.clone();
                    let grenade_helper_transfer_state = self.grenade_helper_transfer_state.clone();
                    move || {
                        let result = executor();
                        let mut transfer_state = grenade_helper_transfer_state.lock().unwrap();
                        match result {
                            Ok(new_state) => {
                                *transfer_state = new_state;
                            }
                            Err(err) => {
                                *transfer_state = GrenadeHelperTransferState::Failed {
                                    direction,
                                    message: format!("{:#}", err),
                                };
                            }
                        }
                    }
                });
                *transfer_state = GrenadeHelperTransferState::Active {
                    direction: direction.clone(),
                };
            }
            GrenadeHelperTransferState::Active { .. } => {
                /* Just waiting for the file picker to finish. */
            }

            GrenadeHelperTransferState::ImportPending { elements } => {
                let mut popup_open = true;
                if let Some(_popup) = ui
                    .modal_popup_config("Data Import")
                    .always_auto_resize(true)
                    .opened(&mut popup_open)
                    .begin_popup()
                {
                    let total_count = elements.values().map(|spots| spots.len()).sum::<usize>();

                    ui.text(format!(
                        "The following locations have been loaded ({})",
                        total_count
                    ));
                    for (map_name, spots) in elements.iter() {
                        ui.text(format!("- {} ({} spots)", map_name, spots.len()));
                    }

                    ui.new_line();
                    ui.text("Would you like to replace the current configuration?");

                    ui.spacing();
                    ui.separator();
                    ui.spacing();

                    let button_width =
                        (ui.content_region_avail()[0] - ui.clone_style().item_spacing[0]) / 2.0;

                    if ui.button_with_size("Cancel", [button_width, 0.0]) {
                        *transfer_state = GrenadeHelperTransferState::Idle;
                        return;
                    }

                    ui.same_line();
                    if ui.button_with_size("Yes", [button_width, 0.0]) {
                        settings.map_spots = elements.clone();
                        *transfer_state = GrenadeHelperTransferState::ImportSuccess {
                            count: total_count,
                            replacing: false,
                        };
                    }
                } else {
                    ui.open_popup("Data Import");
                }
            }

            GrenadeHelperTransferState::Failed { direction, message } => {
                let mut popup_open = true;
                let popup_name = format!(
                    "{} failed",
                    match direction {
                        GrenadeHelperTransferDirection::Export => "Export",
                        GrenadeHelperTransferDirection::Import => "Import",
                    }
                );
                if let Some(_popup) = ui
                    .modal_popup_config(&popup_name)
                    .opened(&mut popup_open)
                    .always_auto_resize(true)
                    .begin_popup()
                {
                    ui.text("A fatal error occurred:");
                    ui.spacing();

                    ui.text(message);

                    ui.spacing();
                    ui.separator();
                    ui.spacing();
                    if ui.button_with_size("Close", [100.0, 0.0]) {
                        popup_open = false;
                    }
                } else {
                    ui.open_popup(&popup_name);
                }

                if !popup_open {
                    *transfer_state = GrenadeHelperTransferState::Idle;
                }
            }
            GrenadeHelperTransferState::ExportSuccess { target_path } => {
                let mut popup_open = true;
                if let Some(_popup) = ui
                    .modal_popup_config("Export successfull")
                    .opened(&mut popup_open)
                    .always_auto_resize(true)
                    .begin_popup()
                {
                    ui.text("All grenade helper spots have been exported to");
                    ui.text(format!("{}", target_path.display()));

                    ui.spacing();
                    ui.separator();
                    ui.spacing();
                    if ui.button_with_size("Close", [100.0, 0.0]) {
                        popup_open = false;
                    }
                } else {
                    ui.open_popup("Export successfull");
                }

                if !popup_open {
                    *transfer_state = GrenadeHelperTransferState::Idle;
                }
            }
            GrenadeHelperTransferState::ImportSuccess { count, .. } => {
                let mut popup_open = true;
                if let Some(_popup) = ui
                    .modal_popup_config("Import successful")
                    .opened(&mut popup_open)
                    .always_auto_resize(true)
                    .begin_popup()
                {
                    ui.text(format!("{} grenade helper spots have been imported", count));

                    ui.spacing();
                    ui.separator();
                    ui.spacing();
                    if ui.button_with_size("Close", [100.0, 0.0]) {
                        popup_open = false;
                    }
                } else {
                    ui.open_popup("Import successfull");
                }

                if !popup_open {
                    *transfer_state = GrenadeHelperTransferState::Idle;
                }
            }
        }
    }
}
