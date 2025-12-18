use std::time::{Duration, Instant};
use anyhow::Context;
use imgui::{ImColor32, Ui};

use cs2::{StateCS2Memory, StateLocalPlayerController};

use cs2_schema_generated::cs2::client::{
    CCSPlayerController, 
    CCSPlayerController_ActionTrackingServices
};

use super::Enhancement;
use crate::settings::{AppSettings, HitMarkerType};
use crate::utils::audio;

// Hitmarker verisi
struct HitLog {
    damage: i32,
    is_headshot: bool,
    spawn_time: Instant,
    position_offset: f32,
}

pub struct HitmarkerPlugin {
    logs: Vec<HitLog>,
    prev_damage: i32,
    prev_headshots: i32,
}

impl HitmarkerPlugin {
    pub fn new() -> Self {
        Self {
            logs: Vec::new(),
            prev_damage: 0,
            prev_headshots: 0,
        }
    }
}

impl Enhancement for HitmarkerPlugin {
    fn update(&mut self, ctx: &crate::UpdateContext) -> anyhow::Result<()> {
        let settings = ctx.states.resolve::<AppSettings>(())?;

        // Eğer hitmarker kapalıysa işlem yapma
        if !settings.hitmarker_enabled {
            return Ok(());
        }

        let memory = ctx.states.resolve::<StateCS2Memory>(())?;
        let local_controller_state = ctx.states.resolve::<StateLocalPlayerController>(())?;

        let local_controller = match local_controller_state.instance.value_reference(memory.view_arc()) {
            Some(c) => c,
            None => return Ok(()),
        };

        let tracking_services_ptr = local_controller.m_pActionTrackingServices()?;
        if tracking_services_ptr.is_null() {
            return Ok(());
        }

        let tracking_services = match tracking_services_ptr.value_reference(memory.view_arc()) {
            Some(s) => s,
            None => return Ok(()),
        };

        let current_damage = tracking_services.m_flTotalRoundDamageDealt()? as i32;
        let current_headshots = tracking_services.m_iNumRoundKillsHeadshots()?;

        // --- İLK BAŞLATMA KONTROLÜ ---
        // Eğer hileyi oyun ortasında açtıysan ve zaten hasarın varsa,
        // eski hasarı (0) yeni hasara (örneğin 300) eşitleyip sesi çalmamalıyız.
        if self.prev_damage == 0 && current_damage > 0 {
            self.prev_damage = current_damage;
            self.prev_headshots = current_headshots;
            return Ok(());
        }

        // Round sıfırlandıysa
        if current_damage < self.prev_damage {
            self.prev_damage = current_damage;
            self.prev_headshots = current_headshots;
            return Ok(());
        }

        // --- VURUŞ ALGILAMA ---
        if current_damage > self.prev_damage {
            let damage_diff = current_damage - self.prev_damage;
            let is_hs = current_headshots > self.prev_headshots;

            // KONSOLA YAZDIR: Vuruş algılandı mı?
            //println!(">> VURUS ALGILANDI! Hasar: {}, HS: {}", damage_diff, is_hs);

            self.logs.push(HitLog {
                damage: damage_diff,
                is_headshot: is_hs,
                spawn_time: Instant::now(),
                position_offset: (current_damage % 20 - 10) as f32 * 2.0, 
            });

            if settings.hitmarker_type != HitMarkerType::Off {
                //println!(">> Ses çalınıyor: {:?}", settings.hitmarker_type); // Ses tipi ne?
                match settings.hitmarker_type {
                    HitMarkerType::Rust => {
                        audio::play_sound_from_bytes(include_bytes!("../../resources/rust.wav"));
                    }
                    HitMarkerType::Pat => {
                        audio::play_sound_from_bytes(include_bytes!("../../resources/pat.wav"));
                    }
                    HitMarkerType::Serdar => {
                        audio::play_sound_from_bytes(include_bytes!("../../resources/serdar.wav"));
                    }
                    HitMarkerType::Off => {} 
                }
            }
        }

        self.prev_damage = current_damage;
        self.prev_headshots = current_headshots;
        self.logs.retain(|log| log.spawn_time.elapsed() < Duration::from_millis(1000));

        Ok(())
    }

    fn render(
        &self,
        _states: &utils_state::StateRegistry,
        ui: &Ui,
        _unicode_text: &overlay::UnicodeTextRenderer,
    ) -> anyhow::Result<()> {
        let draw_list = ui.get_background_draw_list();
        let [w, h] = ui.io().display_size;
        let window_center = [w / 2.0, h / 2.0];
        
        for log in &self.logs {
            let elapsed = log.spawn_time.elapsed().as_secs_f32();
            let life_percent = elapsed / 1.0; 

            // Animasyon Hesaplamaları
            let fade_alpha = (1.0 - life_percent).clamp(0.0, 1.0);
            let move_up = life_percent * 50.0;

            let color = if log.is_headshot {
                ImColor32::from_rgba(255, 50, 50, (fade_alpha * 255.0) as u8)
            } else {
                ImColor32::from_rgba(255, 255, 255, (fade_alpha * 255.0) as u8)
            };

            let text = if log.is_headshot {
                format!("HEADSHOT ({})", log.damage)
            } else {
                format!("-{}", log.damage)
            };

            let pos_x = window_center[0] + log.position_offset;
            let pos_y = window_center[1] + 20.0 - move_up;

            draw_list.add_text([pos_x, pos_y], color, &text);
        }
        
        Ok(())
    }
}