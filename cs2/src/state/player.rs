use std::{
    ffi::CStr,
    ops::Deref,
};

use anyhow::{
    Context,
    Result,
};
use cs2_schema_cutl::EntityHandle;
use cs2_schema_generated::cs2::client::{
    CCSPlayer_ItemServices,
    CCSPlayer_WeaponServices,
    CGameSceneNode,
    CPlayer_WeaponServices,
    CSkeletonInstance,
    C_BaseEntity,
    C_BasePlayerPawn,
    C_BasePlayerWeapon,
    C_CSPlayerPawn,
    C_CSPlayerPawnBase,
    C_EconEntity,
};
use utils_state::{
    State,
    StateCacheType,
    StateRegistry,
};

use crate::{
    schema::{
        CBoneStateData,
        CModelStateEx,
    },
    CS2Model,
    StateCS2Memory,
    StateEntityList,
    WeaponId,
};

#[derive(Debug, Clone)]
pub struct StatePawnInfo {
    pub controller_entity_id: Option<u32>,
    pub pawn_entity_id: u32,
    pub team_id: u8,

    pub player_health: i32,
    pub player_has_defuser: bool,
    pub player_has_bomb: bool,
    pub player_name: Option<String>,
    pub weapon: WeaponId,
    pub weapon_current_ammo: i32,
    pub weapon_reserve_ammo: i32,
    pub player_flashtime: f32,

    pub player_has_flash: u32,
    pub player_has_smoke: bool,
    pub player_has_hegrenade: bool,
    pub player_has_molotov: bool,
    pub player_has_incendiary: bool,
    pub player_has_decoy: bool,

    pub position: nalgebra::Vector3<f32>,
    pub rotation: f32,
}

impl State for StatePawnInfo {
    type Parameter = EntityHandle<dyn C_CSPlayerPawn>;

    fn create(states: &StateRegistry, handle: Self::Parameter) -> anyhow::Result<Self> {
        let memory = states.resolve::<StateCS2Memory>(())?;
        let entities = states.resolve::<StateEntityList>(())?;
        let Some(player_pawn) = entities.entity_from_handle(&handle) else {
            anyhow::bail!("entity does not exists")
        };
        let player_pawn = player_pawn
            .value_copy(memory.view())?
            .context("player pawn nullptr")?;

        let player_health = player_pawn.m_iHealth()?;

        let controller_handle = player_pawn.m_hController()?;
        let current_controller = entities.entity_from_handle(&controller_handle);

        let player_team = player_pawn.m_iTeamNum()?;
        let player_name = if let Some(identity) = &current_controller {
            let player_controller = identity
                .value_reference(memory.view_arc())
                .context("nullptr")?;
            Some(
                CStr::from_bytes_until_nul(&player_controller.m_iszPlayerName()?)
                    .context("player name missing nul terminator")?
                    .to_string_lossy()
                    .to_string(),
            )
        } else {
            None
        };

        let player_has_defuser = player_pawn
            .m_pItemServices()?
            .value_reference(memory.view_arc())
            .context("m_pItemServices nullptr")?
            .cast::<dyn CCSPlayer_ItemServices>()
            .m_bHasDefuser()?;

        let weapon_services = player_pawn
            .m_pWeaponServices()?
            .value_reference(memory.view_arc())
            .context("m_pWeaponServices nullptr")?
            .cast::<dyn CCSPlayer_WeaponServices>();

        let ammo = weapon_services.m_iAmmo()?;

        let mut player_has_flash = 0;
        let mut player_has_smoke = false;
        let mut player_has_hegrenade = false;
        let mut player_has_molotov = false;
        let mut player_has_incendiary = false;
        let mut player_has_decoy = false;

        let grenade_slots = [
            (15, &mut player_has_smoke),
            (13, &mut player_has_hegrenade),
            (17, &mut player_has_decoy),
        ];

        if let Some(count) = ammo.get(14) {
            player_has_flash = *count as u32;
        }

        for (index, flag) in grenade_slots {
            if let Some(count) = ammo.get(index) {
                *flag = *count > 0;
            }
        }

        if let Some(count) = ammo.get(16) {
            if *count > 0 {
                match player_team {
                    2 => player_has_molotov = true,    // Terrorist
                    3 => player_has_incendiary = true, // Counter-Terrorist
                    _ => {}                            // Unknown team
                }
            }
        }

        /* Will be an instance of CSkeletonInstance */
        let game_screen_node = player_pawn
            .m_pGameSceneNode()?
            .value_reference(memory.view_arc())
            .context("game screen node nullptr")?
            .cast::<dyn CSkeletonInstance>()
            .copy()?;

        let position =
            nalgebra::Vector3::<f32>::from_column_slice(&game_screen_node.m_vecAbsOrigin()?);

        let weapon_ref = player_pawn
            .m_pClippingWeapon()?
            .value_reference(memory.view_arc());
        let weapon_type = if let Some(weapon) = &weapon_ref {
            weapon
                .cast::<dyn C_EconEntity>()
                .m_AttributeManager()?
                .m_Item()?
                .m_iItemDefinitionIndex()?
        } else {
            WeaponId::Knife.id()
        };

        let (weapon_current_ammo, weapon_reserve_ammo) = if let Some(weapon) = weapon_ref.as_ref() {
            let weapon = weapon.cast::<dyn C_BasePlayerWeapon>();
            (weapon.m_iClip1()?, weapon.m_pReserveAmmo()?[0])
        } else {
            (-1, 0)
        };

        let player_flashtime = player_pawn.m_flFlashBangTime()?;

        // Use cached bomb carrier state instead of iterating through all entities
        let player_has_bomb = if let Ok(bomb_carrier) = states.resolve::<super::BombCarrierInfo>(())
        {
            bomb_carrier.carrier_entity_id == Some(handle.get_entity_index())
        } else {
            false
        };

        Ok(Self {
            controller_entity_id: if controller_handle.is_valid() {
                Some(controller_handle.get_entity_index())
            } else {
                None
            },
            pawn_entity_id: handle.get_entity_index(),

            team_id: player_team,

            player_name,
            player_has_defuser,
            player_has_bomb,
            player_health,
            weapon: WeaponId::from_id(weapon_type).unwrap_or(WeaponId::Unknown),
            weapon_current_ammo,
            weapon_reserve_ammo,
            player_flashtime,

            player_has_flash,
            player_has_smoke,
            player_has_hegrenade,
            player_has_molotov,
            player_has_incendiary,
            player_has_decoy,

            position,
            rotation: player_pawn.m_angEyeAngles()?[1],
        })
    }

    fn cache_type() -> StateCacheType {
        StateCacheType::Volatile
    }
}

#[derive(Debug, Clone)]
pub struct BoneStateData {
    pub position: nalgebra::Vector3<f32>,
}

impl TryFrom<&dyn CBoneStateData> for BoneStateData {
    type Error = anyhow::Error;

    fn try_from(value: &dyn CBoneStateData) -> Result<Self, Self::Error> {
        Ok(Self {
            position: nalgebra::Vector3::from_row_slice(&value.position()?),
        })
    }
}

#[derive(Debug, Clone)]
pub struct StatePawnModelInfo {
    pub model_address: u64,
    pub bone_states: Vec<BoneStateData>,
}

impl State for StatePawnModelInfo {
    type Parameter = EntityHandle<dyn C_CSPlayerPawn>;

    fn create(states: &StateRegistry, handle: Self::Parameter) -> anyhow::Result<Self> {
        let memory = states.resolve::<StateCS2Memory>(())?;
        let entities = states.resolve::<StateEntityList>(())?;
        let Some(player_pawn) = entities.entity_from_handle(&handle) else {
            anyhow::bail!("entity does not exists")
        };
        let player_pawn = player_pawn
            .value_copy(memory.view())?
            .context("player pawn nullptr")?;

        let game_screen_node = player_pawn
            .m_pGameSceneNode()?
            .value_reference(memory.view_arc())
            .context("game screen node nullptr")?
            .cast::<dyn CSkeletonInstance>()
            .copy()?;

        let model_address = game_screen_node
            .m_modelState()?
            .m_hModel()?
            .read_value(memory.view())?
            .context("m_hModel nullptr")?
            .address;

        let model = states.resolve::<CS2Model>(model_address)?;
        let bone_states = game_screen_node
            .m_modelState()?
            .bone_state_data()?
            .elements_copy(memory.view(), 0..model.bones.len())?
            .into_iter()
            .map(|bone| bone.deref().try_into())
            .collect::<Result<Vec<_>>>()?;

        Ok(Self {
            bone_states,
            model_address,
        })
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum PlayerPawnState {
    Alive,
    Dead,
}

impl State for PlayerPawnState {
    type Parameter = EntityHandle<dyn C_CSPlayerPawn>;

    fn create(
        states: &utils_state::StateRegistry,
        handle: Self::Parameter,
    ) -> anyhow::Result<Self> {
        let memory = states.resolve::<StateCS2Memory>(())?;
        let entities = states.resolve::<StateEntityList>(())?;

        let player_pawn = match entities.entity_from_handle::<dyn C_CSPlayerPawn>(&handle) {
            Some(identity) => identity
                .value_reference(memory.view_arc())
                .context("entity nullptr")?,
            None => return Ok(Self::Dead),
        };

        let player_health = player_pawn.m_iHealth()?;
        if player_health <= 0 {
            return Ok(Self::Dead);
        }

        /* Will be an instance of CSkeletonInstance */
        let game_screen_node = player_pawn
            .m_pGameSceneNode()?
            .value_reference(memory.view_arc())
            .context("m_pGameSceneNode nullptr")?
            .cast::<dyn CSkeletonInstance>();
        if game_screen_node.m_bDormant()? {
            return Ok(Self::Dead);
        }

        Ok(Self::Alive)
    }

    fn cache_type() -> StateCacheType {
        StateCacheType::Volatile
    }
}
