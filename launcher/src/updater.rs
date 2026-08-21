use std::fs::{self, File};
use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Duration;
use ed25519_dalek::{Signature, Verifier, VerifyingKey};
use serde::Deserialize;
use sha2::{Digest, Sha256};

#[derive(Debug, Deserialize, Clone)]
pub struct ManifestFile {
    pub path: String,
    pub sha256: String,
    #[serde(default)]
    pub size: u64,
}

#[derive(Debug, Deserialize, Clone)]
pub struct Manifest {
    pub version: String,
    pub target_executable: String,
    pub files: Vec<ManifestFile>,
}

#[derive(Clone, Debug)]
pub struct LauncherConfig {
    pub base_url: String,
    pub install_dir: PathBuf,
    pub manifest_file: String,
    pub signature_file: Option<String>,
    pub public_key_hex: Option<String>,
    pub auto_launch: bool,
}

impl Default for LauncherConfig {
    fn default() -> Self {
        Self {
            base_url: String::new(),
            install_dir: PathBuf::from("./app"),
            manifest_file: "manifest.json".to_string(),
            signature_file: Some("manifest.json.sig".to_string()),
            public_key_hex: None,
            auto_launch: true,
        }
    }
}

#[derive(Clone, Debug)]
pub enum UpdaterEvent {
    CheckingVersions,
    VerifyingSignature,
    UpToDate { version: String },
    UpdateFound { version: String, total_files: usize },
    DownloadingFile {
        path: String,
        file_index: usize,
        total_files: usize,
        overall_progress: f32,
    },
    FileCompleted {
        path: String,
        file_index: usize,
        total_files: usize,
        overall_progress: f32,
    },
    Launching { executable: String },
    Success,
    Error(String),
}

pub struct AutoUpdater {
    config: LauncherConfig,
    client: reqwest::blocking::Client,
}

impl AutoUpdater {
    pub fn new(config: LauncherConfig) -> Self {
        let client = reqwest::blocking::Client::builder()
            .timeout(Duration::from_secs(45))
            .build()
            .unwrap_or_default();

        Self { config, client }
    }

    /// Calculate SHA-256 (Streaming)
    fn compute_sha256(path: &Path) -> Result<String, Box<dyn std::error::Error>> {
        let mut file = File::open(path)?;
        let mut hasher = Sha256::new();
        let mut buffer = [0u8; 16384];
        loop {
            let bytes_read = file.read(&mut buffer)?;
            if bytes_read == 0 {
                break;
            }
            hasher.update(&buffer[..bytes_read]);
        }
        Ok(hex::encode(hasher.finalize()))
    }

    /// Run the update routine with event callbacks
    pub fn run_with_events<F>(&self, mut on_event: F) -> Result<(), String>
    where
        F: FnMut(UpdaterEvent),
    {
        fs::create_dir_all(&self.config.install_dir)
            .map_err(|e| format!("Failed to create destination folder: {}", e))?;

        // 1. Check version and manifest
        on_event(UpdaterEvent::CheckingVersions);
        std::thread::sleep(Duration::from_millis(600));

        let manifest_url = format!("{}/{}", self.config.base_url.trim_end_matches('/'), self.config.manifest_file);
        let manifest_resp = self.client.get(&manifest_url).send()
            .map_err(|e| format!("Could not connect to update server: {}", e))?;
        
        if !manifest_resp.status().is_success() {
            return Err(format!("Failed to download manifest (HTTP {}): {}", manifest_resp.status(), manifest_url));
        }
        let manifest_bytes = manifest_resp.bytes()
            .map_err(|e| format!("Failed to read manifest data: {}", e))?;

        // 2. Verify Ed25519 signature
        if let (Some(sig_name), Some(pk_hex)) = (&self.config.signature_file, &self.config.public_key_hex) {
            on_event(UpdaterEvent::VerifyingSignature);
            std::thread::sleep(Duration::from_millis(400));

            let sig_url = format!("{}/{}", self.config.base_url.trim_end_matches('/'), sig_name);
            let sig_resp = self.client.get(&sig_url).send()
                .map_err(|e| format!("Failed to fetch signature file: {}", e))?;
            
            if !sig_resp.status().is_success() {
                return Err(format!("Signature download failed (HTTP {}): {}", sig_resp.status(), sig_url));
            }
            let sig_bytes = sig_resp.bytes()
                .map_err(|e| format!("Failed to read signature bytes: {}", e))?;

            let pk_raw = hex::decode(pk_hex)
                .map_err(|e| format!("Invalid Public Key hex string: {}", e))?;
            let pk_arr: [u8; 32] = pk_raw.as_slice().try_into()
                .map_err(|_| "Invalid Ed25519 Public Key length (expected 32 bytes)".to_string())?;
            let verifying_key = VerifyingKey::from_bytes(&pk_arr)
                .map_err(|e| format!("Failed to initialize public key: {}", e))?;

            let signature = Signature::from_slice(sig_bytes.as_ref())
                .map_err(|e| format!("Invalid signature format: {:?}", e))?;

            verifying_key.verify(&manifest_bytes, &signature)
                .map_err(|e| format!("Security Alert: Invalid package signature! The update may be altered or forged: {:?}", e))?;
        }

        let manifest: Manifest = serde_json::from_slice(&manifest_bytes)
            .map_err(|e| format!("Failed to parse manifest JSON: {}", e))?;

        // 3. Compare local files against manifest
        let mut files_to_download: Vec<&ManifestFile> = Vec::new();
        for item in &manifest.files {
            let local_path = self.config.install_dir.join(&item.path);
            let needs_download = if local_path.exists() {
                match Self::compute_sha256(&local_path) {
                    Ok(hash) => hash.to_lowercase() != item.sha256.to_lowercase(),
                    Err(_) => true,
                }
            } else {
                true
            };

            if needs_download {
                files_to_download.push(item);
            }
        }

        // 4. Download updates if necessary
        if !files_to_download.is_empty() {
            on_event(UpdaterEvent::UpdateFound {
                version: manifest.version.clone(),
                total_files: files_to_download.len(),
            });
            std::thread::sleep(Duration::from_millis(500));

            let total_files_count = files_to_download.len();
            for (idx, item) in files_to_download.iter().enumerate() {
                let local_path = self.config.install_dir.join(&item.path);
                if let Some(parent) = local_path.parent() {
                    fs::create_dir_all(parent)
                        .map_err(|e| format!("Failed to create folder {}: {}", parent.display(), e))?;
                }

                let file_url = format!("{}/{}", self.config.base_url.trim_end_matches('/'), item.path);
                
                let base_progress = idx as f32 / total_files_count as f32;
                on_event(UpdaterEvent::DownloadingFile {
                    path: item.path.clone(),
                    file_index: idx + 1,
                    total_files: total_files_count,
                    overall_progress: base_progress,
                });

                let mut response = self.client.get(&file_url).send()
                    .map_err(|e| format!("Failed to download file ({}): {}", item.path, e))?;

                if !response.status().is_success() {
                    return Err(format!("Server returned HTTP {} for {}", response.status(), file_url));
                }

                let total_size = response.content_length().unwrap_or(item.size);
                let mut buffer = [0u8; 16384];
                let mut downloaded_bytes: u64 = 0;
                let mut file_content = Vec::with_capacity(if total_size > 0 { total_size as usize } else { 32768 });

                loop {
                    let n = response.read(&mut buffer)
                        .map_err(|e| format!("Error while reading file stream {}: {}", item.path, e))?;
                    if n == 0 {
                        break;
                    }
                    file_content.extend_from_slice(&buffer[..n]);
                    downloaded_bytes += n as u64;

                    let file_ratio = if total_size > 0 {
                        (downloaded_bytes as f32 / total_size as f32).clamp(0.0, 1.0)
                    } else {
                        0.5
                    };

                    let current_overall = (idx as f32 + file_ratio) / total_files_count as f32;
                    on_event(UpdaterEvent::DownloadingFile {
                        path: item.path.clone(),
                        file_index: idx + 1,
                        total_files: total_files_count,
                        overall_progress: current_overall,
                    });
                }

                // SHA-256 Hash Verification
                let mut hasher = Sha256::new();
                hasher.update(&file_content);
                let downloaded_hash = hex::encode(hasher.finalize());

                if downloaded_hash.to_lowercase() != item.sha256.to_lowercase() {
                    return Err(format!(
                        "File checksum mismatch: {}\nExpected: {}\nDownloaded: {}",
                        item.path, item.sha256, downloaded_hash
                    ));
                }

                let mut file = File::create(&local_path)
                    .map_err(|e| format!("Failed to create file {}: {}", local_path.display(), e))?;
                file.write_all(&file_content)
                    .map_err(|e| format!("Failed to write file content {}: {}", local_path.display(), e))?;

                let finished_overall = (idx + 1) as f32 / total_files_count as f32;
                on_event(UpdaterEvent::FileCompleted {
                    path: item.path.clone(),
                    file_index: idx + 1,
                    total_files: total_files_count,
                    overall_progress: finished_overall,
                });
            }
        } else {
            on_event(UpdaterEvent::UpToDate {
                version: manifest.version.clone(),
            });
            std::thread::sleep(Duration::from_millis(600));
        }

        // 5. Launch Target
        if self.config.auto_launch {
            let exe_path = self.config.install_dir.join(&manifest.target_executable);
            on_event(UpdaterEvent::Launching {
                executable: manifest.target_executable.clone(),
            });
            std::thread::sleep(Duration::from_millis(500));

            if !exe_path.exists() {
                return Err(format!("Target executable was not found: {:?}", exe_path));
            }

            Command::new(&exe_path)
                .current_dir(&self.config.install_dir)
                .spawn()
                .map_err(|e| format!("Failed to spawn executable: {}", e))?;
        }

        on_event(UpdaterEvent::Success);
        Ok(())
    }
}
