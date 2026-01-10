use std::path::PathBuf;
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};
use std::fs;

use anyhow::Context;
use cs2::{
    CEntityIdentityEx, CS2Model, ClassNameCache, PlayerPawnState,
    StateCS2Memory, StateEntityList, StateLocalPlayerController,
    StatePawnInfo, StatePawnModelInfo,
};
use cs2_schema_generated::cs2::client::CEntityInstance;
use overlay::UnicodeTextRenderer;

use super::Enhancement;
use crate::{
    settings::AppSettings,
    view::ViewController,
};

use windows::Win32::Graphics::Gdi::{
    BitBlt, CreateCompatibleBitmap, CreateCompatibleDC, DeleteDC, DeleteObject,
    GetDC, GetDIBits, ReleaseDC, SelectObject, ClientToScreen, BITMAPINFO, BITMAPINFOHEADER,
    BI_RGB, DIB_RGB_COLORS, SRCCOPY,
};
use windows::Win32::Foundation::{HWND, POINT, RECT};
use windows::Win32::UI::WindowsAndMessaging::{
    FindWindowExA, GetWindowThreadProcessId, GetClientRect,
};

const CAPTURE_SIZE: i32 = 600;
const CAPTURE_COOLDOWN_MS: u64 = 1000; // 1 second cooldown between captures

pub struct DataCollector {
    local_team_id: u8,
    last_capture_time: Instant,
    output_dir: PathBuf,
}

unsafe impl Send for DataCollector {}
unsafe impl Sync for DataCollector {}

impl DataCollector {
    pub fn new() -> Self {
        // Create output directory
        let output_dir = PathBuf::from("collected_img");
        if !output_dir.exists() {
            let _ = fs::create_dir_all(&output_dir);
        }
        
        Self {
            local_team_id: 0,
            last_capture_time: Instant::now() - Duration::from_secs(10), // Allow immediate first capture
            output_dir,
        }
    }

    /// Find the CS2 window position on screen by process ID
    fn find_window_position(&self, process_id: u32) -> Option<(i32, i32)> {
        unsafe {
            let mut current_hwnd = HWND::default();
            
            // Iterate through all windows to find the one belonging to CS2
            loop {
                current_hwnd = FindWindowExA(None, current_hwnd, None, None);
                if current_hwnd.0 == 0 {
                    break;
                }

                let mut window_process_id = 0u32;
                let result = GetWindowThreadProcessId(current_hwnd, Some(&mut window_process_id));
                if result == 0 || window_process_id != process_id {
                    continue;
                }

                // Found a window belonging to CS2, get its client rect
                let mut rect = RECT::default();
                if GetClientRect(current_hwnd, &mut rect).is_err() {
                    continue;
                }

                // Skip windows with zero size
                if rect.right == 0 || rect.bottom == 0 {
                    continue;
                }

                // Convert client coordinates to screen coordinates
                let mut point = POINT { x: 0, y: 0 };
                if ClientToScreen(current_hwnd, &mut point).as_bool() {
                    return Some((point.x, point.y));
                }
            }
            
            None
        }
    }

    fn capture_screen_region(&self, x: i32, y: i32, width: i32, height: i32) -> Option<Vec<u8>> {
        unsafe {
            let hdc_screen = GetDC(HWND::default());
            if hdc_screen.is_invalid() {
                return None;
            }

            let hdc_mem = CreateCompatibleDC(hdc_screen);
            if hdc_mem.is_invalid() {
                ReleaseDC(HWND::default(), hdc_screen);
                return None;
            }

            let hbm = CreateCompatibleBitmap(hdc_screen, width, height);
            if hbm.is_invalid() {
                let _ = DeleteDC(hdc_mem);
                ReleaseDC(HWND::default(), hdc_screen);
                return None;
            }

            let old_obj = SelectObject(hdc_mem, hbm);
            
            // Copy screen content to our bitmap
            let result = BitBlt(hdc_mem, 0, 0, width, height, hdc_screen, x, y, SRCCOPY);
            if result.is_err() {
                SelectObject(hdc_mem, old_obj);
                let _ = DeleteObject(hbm);
                let _ = DeleteDC(hdc_mem);
                ReleaseDC(HWND::default(), hdc_screen);
                return None;
            }

            // Prepare to get the bitmap bits
            let mut bmi = BITMAPINFO {
                bmiHeader: BITMAPINFOHEADER {
                    biSize: std::mem::size_of::<BITMAPINFOHEADER>() as u32,
                    biWidth: width,
                    biHeight: -height, // Negative for top-down DIB
                    biPlanes: 1,
                    biBitCount: 24,
                    biCompression: BI_RGB.0,
                    biSizeImage: 0,
                    biXPelsPerMeter: 0,
                    biYPelsPerMeter: 0,
                    biClrUsed: 0,
                    biClrImportant: 0,
                },
                bmiColors: [Default::default()],
            };

            // Calculate row stride (must be DWORD aligned)
            let row_stride = ((width * 3 + 3) & !3) as usize;
            let buffer_size = row_stride * height as usize;
            let mut buffer: Vec<u8> = vec![0; buffer_size];

            let lines = GetDIBits(
                hdc_mem,
                hbm,
                0,
                height as u32,
                Some(buffer.as_mut_ptr() as *mut _),
                &mut bmi,
                DIB_RGB_COLORS,
            );

            SelectObject(hdc_mem, old_obj);
            let _ = DeleteObject(hbm);
            let _ = DeleteDC(hdc_mem);
            ReleaseDC(HWND::default(), hdc_screen);

            if lines == 0 {
                return None;
            }

            // Convert BGR to RGB
            let mut rgb_buffer = Vec::with_capacity((width * height * 3) as usize);
            for row in 0..height as usize {
                let row_start = row * row_stride;
                for col in 0..width as usize {
                    let pixel_start = row_start + col * 3;
                    rgb_buffer.push(buffer[pixel_start + 2]); // R
                    rgb_buffer.push(buffer[pixel_start + 1]); // G
                    rgb_buffer.push(buffer[pixel_start]);     // B
                }
            }

            Some(rgb_buffer)
        }
    }

    fn save_screenshot(
        &self,
        pixels: Vec<u8>,
        width: u32,
        height: u32,
        enemy_boxes: &Vec<(i32, i32, i32, i32)>,
    ) -> anyhow::Result<()> {
        let timestamp = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap_or_default()
            .as_millis();

        // Build filename with all enemy coordinates
        // Format: {timestamp}_{count}_{minx1}_{miny1}_{maxx1}_{maxy1}_{minx2}_{miny2}_{maxx2}_{maxy2}...png
        let mut filename = format!("{}_{}", timestamp, enemy_boxes.len());
        for (min_x, min_y, max_x, max_y) in enemy_boxes {
            filename.push_str(&format!("_{}_{}_{}_{}" , min_x, min_y, max_x, max_y));
        }
        filename.push_str(".png");

        let path = self.output_dir.join(&filename);

        let img = image::RgbImage::from_raw(width, height, pixels)
            .context("Failed to create image from raw pixels")?;
        
        img.save(&path)
            .context("Failed to save PNG image")?;

        println!("[DataCollector] Saved: {} ({} enemies)", filename, enemy_boxes.len());
        Ok(())
    }
}

impl Enhancement for DataCollector {
    fn update(&mut self, ctx: &crate::UpdateContext) -> anyhow::Result<()> {
        // Check cooldown
        if self.last_capture_time.elapsed() < Duration::from_millis(CAPTURE_COOLDOWN_MS) {
            return Ok(());
        }

        let memory = ctx.states.resolve::<StateCS2Memory>(())?;
        let view = ctx.states.resolve::<ViewController>(())?;
        let entities = ctx.states.resolve::<StateEntityList>(())?;
        let class_name_cache = ctx.states.resolve::<ClassNameCache>(())?;
        
        let local_controller = ctx.states.resolve::<StateLocalPlayerController>(())?;
        
        let local_controller_ref = match local_controller.instance.value_reference(memory.view_arc()) {
            Some(lc) => lc,
            None => return Ok(()),
        };
        
        self.local_team_id = local_controller_ref.m_iPendingTeamNum()?;

        let local_player_index = local_controller_ref
            .m_pEntity()?
            .value_reference(memory.view_arc())
            .context("m_pEntity nullptr")?
            .handle::<()>()?
            .get_entity_index();

        let screen_center_x = view.screen_bounds.x / 2.0;
        let screen_center_y = view.screen_bounds.y / 2.0;
        let half_size = (CAPTURE_SIZE / 2) as f32;

        // Capture box bounds on screen
        let capture_left = screen_center_x - half_size;
        let capture_top = screen_center_y - half_size;
        let capture_right = screen_center_x + half_size;
        let capture_bottom = screen_center_y + half_size;

        // Collect all enemies within the capture area
        let mut enemy_boxes: Vec<(i32, i32, i32, i32)> = Vec::new();

        for entity_identity in entities.entities() {
            let entity_class = class_name_cache.lookup(&entity_identity.entity_class_info()?)?;
            if !entity_class.map(|name| *name == "C_CSPlayerPawn").unwrap_or(false) {
                continue;
            }

            let pawn_state = ctx.states.resolve::<PlayerPawnState>(entity_identity.handle()?)?;
            if *pawn_state != PlayerPawnState::Alive {
                continue;
            }

            let pawn_info = ctx.states.resolve::<StatePawnInfo>(entity_identity.handle()?)?;
            
            // Skip teammates
            if pawn_info.team_id == self.local_team_id {
                continue;
            }

            // Skip dead players
            if pawn_info.player_health <= 0 {
                continue;
            }

            // Check if spotted by local player (like aimbot does)
            if (pawn_info.spotted_by_mask & (1 << (local_player_index - 1))) == 0 {
                continue;
            }

            // Get 2D bounding box (like ESP does)
            let pawn_model = ctx.states.resolve::<StatePawnModelInfo>(entity_identity.handle()?)?;
            let entry_model = ctx.states.resolve::<CS2Model>(pawn_model.model_address)?;

            let player_2d_box = view.calculate_box_2d(
                &(entry_model.vhull_min + pawn_info.position),
                &(entry_model.vhull_max + pawn_info.position),
            );

            if let Some((vmin, vmax)) = player_2d_box {
                // Check if the enemy box intersects with the capture area
                if vmax.x < capture_left || vmin.x > capture_right ||
                   vmax.y < capture_top || vmin.y > capture_bottom {
                    // Enemy is outside capture area, skip
                    continue;
                }

                // Convert screen coordinates to local coordinates within 600x600 capture area
                let local_min_x = ((vmin.x - capture_left).max(0.0) as i32).min(CAPTURE_SIZE);
                let local_min_y = ((vmin.y - capture_top).max(0.0) as i32).min(CAPTURE_SIZE);
                let local_max_x = ((vmax.x - capture_left).max(0.0) as i32).min(CAPTURE_SIZE);
                let local_max_y = ((vmax.y - capture_top).max(0.0) as i32).min(CAPTURE_SIZE);

                enemy_boxes.push((local_min_x, local_min_y, local_max_x, local_max_y));
            }
        }

        // Only capture and save if there are enemies in the capture area
        if !enemy_boxes.is_empty() {
            // Get CS2 window position on screen
            let process_id = ctx.cs2.process_id() as u32;
            let (window_x, window_y) = self.find_window_position(process_id).unwrap_or((0, 0));
            
            // Screen capture coordinates = window position + local capture position
            let screen_capture_x = window_x + capture_left as i32;
            let screen_capture_y = window_y + capture_top as i32;
            
            println!("[DataCollector] DEBUG: screen_bounds=({}, {}), center=({}, {})", 
                view.screen_bounds.x, view.screen_bounds.y, screen_center_x, screen_center_y);
            println!("[DataCollector] DEBUG: window_pos=({}, {}), capture_local=({}, {}), capture_screen=({}, {})",
                window_x, window_y, capture_left as i32, capture_top as i32, screen_capture_x, screen_capture_y);
            
            if let Some(pixels) = self.capture_screen_region(
                screen_capture_x,
                screen_capture_y,
                CAPTURE_SIZE,
                CAPTURE_SIZE,
            ) {
                if let Err(e) = self.save_screenshot(
                    pixels,
                    CAPTURE_SIZE as u32,
                    CAPTURE_SIZE as u32,
                    &enemy_boxes,
                ) {
                    eprintln!("[DataCollector] Failed to save screenshot: {}", e);
                }

                // Update last capture time
                self.last_capture_time = Instant::now();
            }
        }

        Ok(())
    }

    fn render(
        &self,
        _states: &utils_state::StateRegistry,
        _ui: &imgui::Ui,
        _unicode_text: &UnicodeTextRenderer,
    ) -> anyhow::Result<()> {
        // No rendering needed
        Ok(())
    }
}
