use anyhow::Context;
use cs2::{
    LocalCameraControllerTarget,
    StateCS2Memory,
    StateEntityList,
    WeaponId,
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
    // Shmem thread-safe olmadığı için Mutex içine alıyoruz veya
    // sadece render döngüsünde (single thread) kullanıldığından emin oluyoruz.
    shmem: Mutex<Shmem>,
}

impl SharedMemoryWriter {
    pub fn new() -> anyhow::Result<Self> {
        // Paylaşılan belleği oluştur veya varsa bağlan
        let shmem = match ShmemConf::new().size(4096).os_id("yeageth_weapon_data").create() {
            Ok(m) => m,
            Err(ShmemError::LinkExists) => ShmemConf::new().os_id("yeageth_weapon_data").open()?,
            Err(e) => return Err(anyhow::anyhow!("Shared memory error: {}", e)),
        };

        Ok(Self {
            shmem: Mutex::new(shmem),
        })
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
        // O anki oyuncuyu (veya izleneni) bulmak için view_target kullanıyoruz
        let view_target = states.resolve::<LocalCameraControllerTarget>(())?;

        // Eğer hedef yoksa varsayılan olarak 0 veya -1 yazabiliriz
        let weapon_id_to_write: u32 = if let Some(target_entity_id) = view_target.target_entity_id {
            if let Some(player_pawn) = entities.identity_from_index(target_entity_id) {
                 if let Ok(pawn_ptr) = player_pawn.entity_ptr::<dyn C_CSPlayerPawn>() {
                     if let Ok(pawn_ref) = pawn_ptr.value_reference(memory.view_arc()) {
                         // Silahı al
                         if let Ok(weapon_handle) = pawn_ref.m_pClippingWeapon() {
                             if let Some(weapon_ref) = weapon_handle.value_reference(memory.view_arc()) {
                                 // Weapon ID'yi oku
                                 let id_result = weapon_ref
                                     .cast::<dyn C_EconEntity>()
                                     .m_AttributeManager()
                                     .and_then(|m| m.m_Item())
                                     .and_then(|i| i.m_iItemDefinitionIndex());
                                 
                                 match id_result {
                                     Ok(id) => id as u32,
                                     Err(_) => 0,
                                 }
                             } else { 0 }
                         } else { 0 }
                     } else { 0 }
                 } else { 0 }
            } else { 0 }
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