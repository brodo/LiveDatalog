//! Connects Zed to the language listener of a running `LiveDatalogServer`.
//!
//! The listener speaks the Language Server Protocol over TCP and Zed launches
//! language servers over stdio, so the command Zed runs is a bridge from one
//! to the other: `nc HOST PORT` unless the user configures their own.

use zed_extension_api::{self as zed, serde_json, settings::LspSettings, LanguageServerId, Result};

const DEFAULT_HOST: &str = "127.0.0.1";
const DEFAULT_PORT: u64 = 7071;

/// Bridges tried in order when the user names none.
const BRIDGES: &[&str] = &["nc", "ncat"];

struct LiveDatalogExtension;

impl zed::Extension for LiveDatalogExtension {
    fn new() -> Self {
        Self
    }

    fn language_server_command(
        &mut self,
        language_server_id: &LanguageServerId,
        worktree: &zed::Worktree,
    ) -> Result<zed::Command> {
        let settings = LspSettings::for_worktree(language_server_id.as_ref(), worktree)?;

        // A configured binary replaces the bridge entirely.
        if let Some(binary) = settings.binary.as_ref() {
            if let Some(path) = binary.path.clone() {
                return Ok(zed::Command {
                    command: path,
                    args: binary.arguments.clone().unwrap_or_default(),
                    env: binary
                        .env
                        .clone()
                        .map(|env| env.into_iter().collect())
                        .unwrap_or_default(),
                });
            }
        }

        let (host, port) = address(settings.settings.as_ref())?;
        let bridge = BRIDGES
            .iter()
            .find_map(|name| worktree.which(name))
            .ok_or_else(|| {
                format!(
                    "LiveDatalog needs `nc` or `ncat` on PATH to reach the language listener \
                     at {host}:{port}; install one, or set `lsp.{language_server_id}.binary` \
                     to another stdio-to-TCP bridge"
                )
            })?;
        Ok(zed::Command {
            command: bridge,
            args: vec![host, port.to_string()],
            env: Default::default(),
        })
    }
}

/// Reads `host` and `port` from `lsp.livedatalog.settings`, which default to
/// the development server's own defaults.
fn address(settings: Option<&serde_json::Value>) -> Result<(String, u64)> {
    let host = match settings.and_then(|s| s.get("host")) {
        None => DEFAULT_HOST.to_string(),
        Some(value) => value
            .as_str()
            .filter(|host| !host.is_empty())
            .ok_or("`lsp.livedatalog.settings.host` must be a non-empty string")?
            .to_string(),
    };
    let port = match settings.and_then(|s| s.get("port")) {
        None => DEFAULT_PORT,
        Some(value) => value
            .as_u64()
            .filter(|port| (1..=u64::from(u16::MAX)).contains(port))
            .ok_or("`lsp.livedatalog.settings.port` must be a port number")?,
    };
    Ok((host, port))
}

zed::register_extension!(LiveDatalogExtension);

#[cfg(test)]
mod tests {
    use super::*;
    use zed::serde_json::json;

    #[test]
    fn defaults_to_the_servers_defaults() {
        assert_eq!(address(None).unwrap(), ("127.0.0.1".into(), 7071));
        assert_eq!(
            address(Some(&json!({}))).unwrap(),
            ("127.0.0.1".into(), 7071)
        );
    }

    #[test]
    fn reads_host_and_port() {
        let settings = json!({ "host": "::1", "port": 9001 });
        assert_eq!(address(Some(&settings)).unwrap(), ("::1".into(), 9001));
    }

    #[test]
    fn rejects_bad_values() {
        assert!(address(Some(&json!({ "port": 0 }))).is_err());
        assert!(address(Some(&json!({ "port": 70000 }))).is_err());
        assert!(address(Some(&json!({ "port": "7071" }))).is_err());
        assert!(address(Some(&json!({ "host": "" }))).is_err());
    }
}
