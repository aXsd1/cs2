use std::time::Instant;
use anyhow::Context;
use cs2::{
    // CEntityIdentityEx trait'ini ekledik (entity_class_info ve handle için gerekli)
    CEntityIdentityEx, 
    CS2Model, ClassNameCache, MouseState, PlayerPawnState,
    StateCS2Memory, StateEntityList, StateLocalPlayerController,
    StatePawnInfo, StatePawnModelInfo,
};
use overlay::UnicodeTextRenderer;
use nalgebra::Vector2;
use cs2_schema_generated::cs2::client::CEntityInstance;

use super::Enhancement;
use crate::{
    settings::AppSettings,
    view::ViewController,
};

pub struct HumanAimbot {
    start_time: Instant,
    local_team_id: u8,
}

impl HumanAimbot {
    pub fn new() -> Self {
        Self {
            start_time: Instant::now(),
            local_team_id: 0,
        }
    }

    fn calculate_curved_move(&self, diff_x: f32, diff_y: f32, speed: f32, intensity: f32) -> (i32, i32) {
        let time_factor = self.start_time.elapsed().as_secs_f32() * 3.0;
        let curve_direction = time_factor.sin();
        
        let offset_x = -diff_y * intensity * curve_direction;
        let offset_y = diff_x * intensity * curve_direction;
        
        let target_dx = diff_x + offset_x;
        let target_dy = diff_y + offset_y;

        let smooth_factor = if speed > 85.0 { 85.0 } else { speed };
        let divisor = 100.0 - smooth_factor;
        
        let raw_move_x = target_dx / divisor;
        let raw_move_y = target_dy / divisor;

        // X ekseni
        let move_x = if raw_move_x.abs() < 1.0 && raw_move_x.abs() > 0.05 {
            if raw_move_x > 0.0 { 1 } else { -1 }
        } else {
            raw_move_x.round() as i32
        };

        // Y ekseni
        let move_y = if raw_move_y.abs() < 1.0 && raw_move_y.abs() > 0.05 {
            if raw_move_y > 0.0 { 1 } else { -1 }
        } else {
            raw_move_y.round() as i32
        };

        (move_x, move_y)
    }
}

impl Enhancement for HumanAimbot {
    fn update(&mut self, ctx: &crate::UpdateContext) -> anyhow::Result<()> {
        let settings = ctx.states.resolve::<AppSettings>(())?;

        if !settings.aim_bot_enabled {
            return Ok(());
        }

        let is_key_down = if let Some(key) = &settings.aim_bot_key {
            ctx.input.is_key_down(key.0)
        } else {
            false
        };

        if !is_key_down {
            self.start_time = Instant::now();
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

        let screen_center = Vector2::new(view.screen_bounds.x / 2.0, view.screen_bounds.y / 2.0);
        
        let mut best_target_pos: Option<Vector2<f32>> = None;
        let mut min_dist = settings.aim_bot_fov;

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
            
            if pawn_info.team_id == self.local_team_id {
                continue;
            }

            if pawn_info.player_health <= 0 {
                continue;
            }

            if (pawn_info.spotted_by_mask & (1 << (local_player_index - 1))) == 0 {
                 continue;
            }

            let pawn_model = ctx.states.resolve::<StatePawnModelInfo>(entity_identity.handle()?)?;
            let entry_model = ctx.states.resolve::<CS2Model>(pawn_model.model_address)?;

            if let Some(head_bone_index) = entry_model.bones.iter().position(|bone| bone.name == "head_0") {
                 if let Some(head_state) = pawn_model.bone_states.get(head_bone_index) {
                    if let Some(screen_pos_mint) = view.world_to_screen(&head_state.position, true) {
                        let screen_pos = Vector2::new(screen_pos_mint.x, screen_pos_mint.y);
                        let dist = (screen_pos - screen_center).norm();

                        if dist < min_dist {
                            min_dist = dist;
                            best_target_pos = Some(screen_pos);
                        }
                    }
                 }
            }
        }

        if let Some(target_pos) = best_target_pos {
            let diff_x = target_pos.x - screen_center.x;
            let diff_y = target_pos.y - screen_center.y;

            let (move_x, move_y) = self.calculate_curved_move(
                diff_x, 
                diff_y, 
                settings.aim_bot_smooth, 
                settings.aim_bot_curve
            );

            if move_x != 0 || move_y != 0 {
                ctx.cs2.send_mouse_state(&[MouseState {
                    last_x: move_x,
                    last_y: move_y, 
                    ..Default::default()
                }])?;
            }
        }

        Ok(())
    }

    fn render(
        &self,
        states: &utils_state::StateRegistry,
        ui: &imgui::Ui,
        _unicode_text: &UnicodeTextRenderer,
    ) -> anyhow::Result<()> {
        let settings = states.resolve::<AppSettings>(())?;

        // Aimbot aktifse VE fov çizimi aktifse
        if settings.aim_bot_enabled && settings.aim_bot_draw_fov {
            let draw_list = ui.get_background_draw_list();
            let display_size = ui.io().display_size;
            let center = [display_size[0] / 2.0, display_size[1] / 2.0];

            // Çemberi çiz (Renk: Beyaz [1.0, 1.0, 1.0, 1.0])
            draw_list
                .add_circle(center, settings.aim_bot_fov, [1.0, 1.0, 1.0, 1.0])
                .build();
        }

        Ok(())
    }
}