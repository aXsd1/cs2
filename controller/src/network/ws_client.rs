use std::sync::{Arc, Mutex};
use std::time::Duration;
use tokio::sync::mpsc;
use tokio::time::sleep;
use tokio_tungstenite::{connect_async, tungstenite::protocol::Message};
use futures_util::{StreamExt, SinkExt};
use serde::{Deserialize, Serialize};
use url::Url;
use log::{info, error, warn, debug};
use crate::settings::AppSettings;

#[derive(Debug)]
pub enum WsCommand {
    Login {
        username: String,
        password: String,
        hwid: String,
    }
}

#[derive(Serialize)]
#[serde(tag = "type")]
enum ClientMessage {
    #[serde(rename = "auth")]
    Auth {
        username: String,
        password: String,
        hwid: String,
    },
    #[serde(rename = "pong")]
    Pong,
}

#[derive(Deserialize, Debug)]
#[serde(tag = "type", rename_all = "snake_case")]
enum ServerMessage {
    AuthSuccess {
        sys: Option<String>,
        #[serde(rename = "resultCode")]
        result_code: Option<String>,
    },
    AuthFailed {
        error: Option<String>,
        #[serde(rename = "resultCode")]
        result_code: Option<String>,
    },
    Error {
        message: String,
        code: Option<i32>,
    },
    ConfigUpdate {
        config: String,
    },
    Ping,
}

pub async fn run_ws_client(
    mut cmd_rx: mpsc::Receiver<WsCommand>,
    settings_tx: std::sync::mpsc::Sender<AppSettings>,
    auth_status: Arc<Mutex<Option<Result<String, String>>>>,
) {
    let url = Url::parse("wss://yeageth.com/ws").expect("Invalid WebSocket URL");
    
    // Retry strategy
    let mut backoff = Duration::from_secs(1);
    let max_backoff = Duration::from_secs(60);

    let mut stored_credentials: Option<(String, String, String)> = None;

    loop {
        // Wait for credentials if we don't have them
        if stored_credentials.is_none() {
            match cmd_rx.recv().await {
                Some(WsCommand::Login { username, password, hwid }) => {
                    stored_credentials = Some((username, password, hwid));
                    // Reset backoff on new login attempt
                    backoff = Duration::from_secs(1);
                }
                None => {
                    info!("WebSocket client stopping: command channel closed");
                    return;
                }
            }
        }

        info!("Connecting to WebSocket at {}...", url);
        match connect_async(url.clone()).await {
            Ok((ws_stream, _)) => {
                info!("WebSocket connected");
                backoff = Duration::from_secs(1); // Reset backoff on success

                let (mut write, mut read) = ws_stream.split();

                // Send Auth immediately
                if let Some((user, pass, hwid)) = &stored_credentials {
                    let auth_msg = ClientMessage::Auth {
                        username: user.clone(),
                        password: pass.clone(),
                        hwid: hwid.clone(),
                    };
                    let json = serde_json::to_string(&auth_msg).unwrap();
                    if let Err(e) = write.send(Message::Text(json)).await {
                        error!("Failed to send auth: {}", e);
                    } else {
                        info!("Auth sent for user: {}", user);
                    }
                }

                // Inner loop handling messages
                loop {
                    tokio::select! {
                        // Receive messages from Server
                        msg = read.next() => {
                            match msg {
                                Some(Ok(Message::Text(text))) => {
                                    // Parse JSON
                                    match serde_json::from_str::<ServerMessage>(&text) {
                                        Ok(parsed) => {
                                            match parsed {
                                                ServerMessage::AuthSuccess { sys: _, result_code: _ } => {
                                                    info!("Auth Success received from server");
                                                    // Update UI status
                                                    if let Ok(mut lock) = auth_status.lock() {
                                                        *lock = Some(Ok("Login Successful!".to_string()));
                                                    }
                                                }
                                                ServerMessage::AuthFailed { error, result_code: _ } => {
                                                    let err_msg = error.unwrap_or_else(|| "Authentication failed".to_string());
                                                    warn!("Auth Failed: {}", err_msg);
                                                    if let Ok(mut lock) = auth_status.lock() {
                                                        *lock = Some(Err(err_msg));
                                                    }
                                                }
                                                ServerMessage::Error { message, code: _ } => {
                                                    error!("Server Error: {}", message);
                                                    // Optionally update UI for general errors too if relevant
                                                }
                                                ServerMessage::ConfigUpdate { config } => {
                                                    info!("Received Config Update");
                                                    match serde_yaml::from_str::<AppSettings>(&config) {
                                                        Ok(new_settings) => {
                                                            if let Err(e) = settings_tx.send(new_settings) {
                                                                error!("Failed to send settings to main thread: {}", e);
                                                            } else {
                                                                debug!("Settings updated sent to main thread");
                                                            }
                                                        }
                                                        Err(e) => {
                                                            error!("Failed to parse ConfigUpdate YAML: {}", e);
                                                        }
                                                    }
                                                }
                                                ServerMessage::Ping => {
                                                    debug!("Received Ping, sending Pong");
                                                    let pong = ClientMessage::Pong;
                                                    let json = serde_json::to_string(&pong).unwrap();
                                                    if let Err(e) = write.send(Message::Text(json)).await {
                                                        error!("Failed to send Pong: {}", e);
                                                    }
                                                }
                                            }
                                        }
                                        Err(e) => {
                                            // Maybe it's not one of our known messages, log it
                                            debug!("Unknown or malformed message: {} ({})", text, e);
                                        }
                                    }
                                }
                                Some(Ok(Message::Close(_))) => {
                                    warn!("Server closed connection");
                                    break; // Break inner loop, trigger reconnect
                                }
                                Some(Err(e)) => {
                                    error!("WebSocket error: {}", e);
                                    break;
                                }
                                None => {
                                    warn!("WebSocket stream ended");
                                    break;
                                }
                                _ => {}
                            }
                        }
                        // Receive commands from UI (e.g. re-login)
                        cmd = cmd_rx.recv() => {
                            match cmd {
                                Some(WsCommand::Login { username, password, hwid }) => {
                                    info!("New login command received while connected");
                                    stored_credentials = Some((username.clone(), password.clone(), hwid.clone()));
                                    
                                    // Send new auth on existing connection
                                    let auth_msg = ClientMessage::Auth {
                                        username,
                                        password,
                                        hwid
                                    };
                                    let json = serde_json::to_string(&auth_msg).unwrap();
                                    if let Err(e) = write.send(Message::Text(json)).await {
                                        error!("Failed to send re-auth: {}", e);
                                        break; // Reconnect
                                    }
                                }
                                None => {
                                    info!("Command channel closed");
                                    return; // App exit
                                }
                            }
                        }
                    }
                }
            }
            Err(e) => {
                error!("Connection failed: {}", e);
            }
        }

        // Backoff delay
        info!("Reconnecting in {:?}...", backoff);
        sleep(backoff).await;
        backoff = std::cmp::min(backoff * 2, max_backoff);
    }
}
