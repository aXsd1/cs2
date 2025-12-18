use windows::Win32::Media::Audio::{PlaySoundA, SND_MEMORY, SND_ASYNC};
use windows::core::PCSTR;

pub fn play_sound_from_bytes(data: &'static [u8]) {
    //println!("[Audio] Ses çalma fonksiyonu tetiklendi. Veri boyutu: {} bytes", data.len());
    unsafe {
        let _ = PlaySoundA(
            PCSTR::from_raw(data.as_ptr()),
            None,
            SND_MEMORY | SND_ASYNC
        );
    }
}