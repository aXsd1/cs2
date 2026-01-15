use std::sync::{Arc, Mutex};
use std::time::Duration;

use anyhow::Context;
use futures_util::{SinkExt, StreamExt};
use log::{debug, error, info, warn};
use radar_shared::{
    protocol::{
        C2SMessage, ClientEvent, HandshakeProtocolV2, S2CMessage, RADAR_PROTOCOL_VERSION,
    },
    RadarState,
};
use tokio::{
    sync::mpsc::{self, Receiver, Sender},
    time::{self, Interval},
};
use tokio_tungstenite::{connect_async, tungstenite::protocol::Message};
use url::Url;

const RADAR_SERVER_URL: &str = "wss://yeageth.com/radar/publish";

/// Commands that can be sent to the radar publisher
#[derive(Debug)]
pub enum RadarCommand {
    /// Start publishing radar data
    Start,
    /// Stop publishing radar data
    Stop,
    /// Update radar state to be published
    UpdateState(RadarState),
}

/// Radar session information shared with the UI
#[derive(Debug, Clone, Default)]
pub struct RadarSessionInfo {
    pub session_id: Option<String>,
    pub connected: bool,
    pub viewer_count: usize,
    pub error: Option<String>,
}

/// Creates a WebSocket connection to the radar server and performs handshake
async fn create_radar_ws_connection(
    url: &Url,
) -> anyhow::Result<(
    Sender<C2SMessage>,
    Receiver<ClientEvent<S2CMessage>>,
)> {
    info!("Connecting to radar server at {}...", url);
    
    let (ws_stream, _) = connect_async(url)
        .await
        .context("Failed to connect to radar server")?;
    
    let (mut write, mut read) = ws_stream.split();
    
    // Send handshake
    let handshake = HandshakeProtocolV2::RequestInitialize {
        client_version: RADAR_PROTOCOL_VERSION,
    };
    write
        .send(Message::Text(serde_json::to_string(&handshake)?))
        .await?;
    
    // Receive handshake response
    let response = read
        .next()
        .await
        .context("EOF while waiting for handshake response")??;
    
    let response: HandshakeProtocolV2 = serde_json::from_slice(&response.into_data())?;
    match response {
        HandshakeProtocolV2::ResponseSuccess { server_version } => {
            info!("Radar server handshake successful, server version: {}", server_version);
        }
        HandshakeProtocolV2::ResponseGenericFailure { message } => {
            anyhow::bail!("Radar handshake failure: {}", message);
        }
        HandshakeProtocolV2::ResponseIncompatible { supported_versions } => {
            anyhow::bail!(
                "Radar server protocol incompatible (supported: {:?})",
                supported_versions
            );
        }
        _ => anyhow::bail!("Invalid radar server handshake response"),
    }
    
    // Create channels for message passing
    let (tx_to_server, mut rx_from_channel) = mpsc::channel::<C2SMessage>(16);
    let (tx_to_channel, rx_from_server) = mpsc::channel::<ClientEvent<S2CMessage>>(16);
    
    // Spawn sender task
    let tx_to_channel_clone = tx_to_channel.clone();
    tokio::spawn(async move {
        while let Some(message) = rx_from_channel.recv().await {
            let json = match serde_json::to_string(&message) {
                Ok(json) => json,
                Err(e) => {
                    let _ = tx_to_channel_clone
                        .send(ClientEvent::SendError(e.into()))
                        .await;
                    break;
                }
            };
            
            if let Err(e) = write.send(Message::Text(json)).await {
                let _ = tx_to_channel_clone
                    .send(ClientEvent::SendError(e.into()))
                    .await;
                break;
            }
        }
    });
    
    // Spawn receiver task
    tokio::spawn(async move {
        loop {
            let message = tokio::select! {
                _ = tx_to_channel.closed() => break,
                msg = read.next() => msg,
            };
            
            match message {
                Some(Ok(Message::Text(text))) => {
                    match serde_json::from_str::<S2CMessage>(&text) {
                        Ok(msg) => {
                            if tx_to_channel.send(ClientEvent::RecvMessage(msg)).await.is_err() {
                                break;
                            }
                        }
                        Err(e) => {
                            let _ = tx_to_channel.send(ClientEvent::RecvError(e.into())).await;
                            break;
                        }
                    }
                }
                Some(Ok(Message::Close(_))) => break,
                Some(Err(e)) => {
                    let _ = tx_to_channel.send(ClientEvent::RecvError(e.into())).await;
                    break;
                }
                None => break,
                _ => {}
            }
        }
    });
    
    Ok((tx_to_server, rx_from_server))
}

/// Main radar publisher task that runs in the background
pub async fn run_radar_publisher(
    mut cmd_rx: Receiver<RadarCommand>,
    session_info: Arc<Mutex<RadarSessionInfo>>,
) {
    let url = match Url::parse(RADAR_SERVER_URL) {
        Ok(url) => url,
        Err(e) => {
            error!("Invalid radar server URL: {}", e);
            return;
        }
    };
    
    let mut backoff = Duration::from_secs(1);
    let max_backoff = Duration::from_secs(30);
    let mut enabled = true; // Default enabled
    let mut current_state: Option<RadarState> = None;
    let mut session_auth_token: Option<String> = None;
    
    loop {
        if !enabled {
            // Wait for start command
            match cmd_rx.recv().await {
                Some(RadarCommand::Start) => {
                    enabled = true;
                    backoff = Duration::from_secs(1);
                }
                Some(RadarCommand::UpdateState(state)) => {
                    current_state = Some(state);
                }
                Some(RadarCommand::Stop) => continue,
                None => return,
            }
        }
        
        // Try to connect
        let connection = create_radar_ws_connection(&url).await;
        let (tx, mut rx) = match connection {
            Ok(conn) => {
                backoff = Duration::from_secs(1);
                conn
            }
            Err(e) => {
                error!("Radar connection failed: {}", e);
                
                if let Ok(mut info) = session_info.lock() {
                    info.connected = false;
                    info.error = Some(format!("Connection failed: {}", e));
                }
                
                tokio::time::sleep(backoff).await;
                backoff = (backoff * 2).min(max_backoff);
                continue;
            }
        };
        
        info!("Radar WebSocket connected");
        
        // Initialize publish session
        let init_result = tx
            .send(C2SMessage::InitializePublish {
                session_auth_token: session_auth_token.clone(),
            })
            .await;
        
        if let Err(e) = init_result {
            error!("Failed to send InitializePublish: {}", e);
            continue;
        }
        
        // Wait for session response
        let session_response = tokio::select! {
            msg = rx.recv() => msg,
            _ = time::sleep(Duration::from_secs(5)) => {
                error!("Radar session init timeout");
                continue;
            }
        };
        
        let (session_id, auth_token) = match session_response {
            Some(ClientEvent::RecvMessage(S2CMessage::ResponseInitializePublish {
                session_id,
                session_auth_token: token,
            })) => {
                info!("Radar session created: {}", session_id);
                (session_id, token)
            }
            Some(ClientEvent::RecvMessage(S2CMessage::ResponseError { error })) => {
                error!("Radar session error: {}", error);
                if let Ok(mut info) = session_info.lock() {
                    info.error = Some(error);
                }
                continue;
            }
            Some(ClientEvent::RecvMessage(S2CMessage::ResponseSessionInvalidId {})) => {
                warn!("Previous session expired, creating new session");
                session_auth_token = None;
                continue;
            }
            other => {
                error!("Unexpected session response received");
                continue;
            }
        };
        
        // Store auth token for reconnection
        session_auth_token = Some(auth_token);
        
        // Update session info
        if let Ok(mut info) = session_info.lock() {
            info.session_id = Some(session_id.clone());
            info.connected = true;
            info.error = None;
        }
        
        // Create state publish interval
        let mut publish_interval = time::interval(Duration::from_millis(50));
        
        // Main message loop
        loop {
            tokio::select! {
                // Handle commands
                cmd = cmd_rx.recv() => {
                    match cmd {
                        Some(RadarCommand::Stop) => {
                            enabled = false;
                            let _ = tx.send(C2SMessage::Disconnect {
                                reason: "User disabled radar".to_string(),
                            }).await;
                            
                            if let Ok(mut info) = session_info.lock() {
                                info.connected = false;
                                info.session_id = None;
                            }
                            break;
                        }
                        Some(RadarCommand::Start) => {}
                        Some(RadarCommand::UpdateState(state)) => {
                            current_state = Some(state);
                        }
                        None => return,
                    }
                }
                
                // Handle incoming messages
                msg = rx.recv() => {
                    match msg {
                        Some(ClientEvent::RecvMessage(S2CMessage::NotifyViewCount { viewers })) => {
                            debug!("Radar viewer count: {}", viewers);
                            if let Ok(mut info) = session_info.lock() {
                                info.viewer_count = viewers;
                            }
                        }
                        Some(ClientEvent::RecvMessage(S2CMessage::NotifySessionClosed {})) => {
                            warn!("Radar session closed by server");
                            session_auth_token = None;
                            break;
                        }
                        Some(ClientEvent::RecvError(e)) => {
                            error!("Radar recv error: {}", e);
                            break;
                        }
                        Some(ClientEvent::SendError(e)) => {
                            error!("Radar send error: {}", e);
                            break;
                        }
                        None => {
                            warn!("Radar connection closed");
                            break;
                        }
                        _ => {}
                    }
                }
                
                // Publish radar state periodically
                _ = publish_interval.tick() => {
                    if let Some(state) = current_state.take() {
                        if tx.send(C2SMessage::NotifyRadarState { state }).await.is_err() {
                            break;
                        }
                    }
                }
            }
        }
        
        // Connection lost, update status
        if let Ok(mut info) = session_info.lock() {
            info.connected = false;
        }
        
        if enabled {
            info!("Radar reconnecting in {:?}...", backoff);
            tokio::time::sleep(backoff).await;
            backoff = (backoff * 2).min(max_backoff);
        }
    }
}
