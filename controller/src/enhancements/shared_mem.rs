use anyhow::Context;
use cs2::{
    CEntityIdentityEx,
    LocalCameraControllerTarget,
    StateCS2Memory,
    StateEntityList,
};
use cs2_schema_generated::cs2::client::{
    C_CSPlayerPawn,
    C_EconEntity,
};
use overlay::UnicodeTextRenderer;
use utils_state::StateRegistry;
use shared_memory::*;
use std::sync::Mutex;

use super::Enhancement;

pub struct SharedMemoryWriter {
    shmem: Mutex<Shmem>,
}

impl SharedMemoryWriter {
    pub fn new() -> Self {
        // Paylaşılan belleği oluştur veya varsa bağlan
        let shmem = match ShmemConf::new().size(4096).os_id("yeageth_weapon_data").create() {
            Ok(m) => m,
            Err(ShmemError::LinkExists) => ShmemConf::new().os_id("yeageth_weapon_data").open().expect("Failed to open shared memory"),
            Err(e) => panic!("Shared memory error: {}", e),
        };

        Self {
            shmem: Mutex::new(shmem),
        }
    }
}

impl Enhancement for SharedMemoryWriter {
    fn update(&mut self, _ctx: &crate::UpdateContext) -> anyhow::Result<()> {
        Ok(())
    }

    fn render(
        &self,
        states: &StateRegistry,
        _ui: &imgui::Ui,
        _unicode_text: &UnicodeTextRenderer,
    ) -> anyhow::Result<()> {
        let memory = states.resolve::<StateCS2Memory>(())?;
        let entities = states.resolve::<StateEntityList>(())?;
        let view_target = states.resolve::<LocalCameraControllerTarget>(())?;

        // Eğer hedef yoksa varsayılan olarak 0 yazıyoruz
        let weapon_id_to_write: u32 = if let Some(target_entity_id) = view_target.target_entity_id {
            let weapon_id = (|| -> anyhow::Result<u16> {
                let player_pawn = entities
                    .identity_from_index(target_entity_id)
                    .context("missing entity identity")?
                    .entity_ptr::<dyn C_CSPlayerPawn>()?
                    .value_reference(memory.view_arc())
                    .context("player pawn nullptr")?;

                let weapon = player_pawn
                    .m_pClippingWeapon()?
                    .value_reference(memory.view_arc())
                    .context("weapon nullptr")?;

                let weapon_id = weapon
                    .cast::<dyn C_EconEntity>()
                    .m_AttributeManager()?
                    .m_Item()?
                    .m_iItemDefinitionIndex()?;

                Ok(weapon_id)
            })();

            weapon_id.unwrap_or(0) as u32
        } else {
            0
        };

        // Paylaşılan belleğe yaz
        if let Ok(shmem) = self.shmem.lock() {
            let shmem_ptr = shmem.as_ptr();
            unsafe {
                // İlk 4 byte'a weapon_id yazıyoruz
                let src_ptr = &weapon_id_to_write as *const u32 as *const u8;
                std::ptr::copy_nonoverlapping(src_ptr, shmem_ptr, 4);
            }
        }

        Ok(())
    }

    fn render_debug_window(
        &mut self,
        _states: &StateRegistry,
        _ui: &imgui::Ui,
        _unicode_text: &UnicodeTextRenderer,
    ) -> anyhow::Result<()> {
        Ok(())
    }
}