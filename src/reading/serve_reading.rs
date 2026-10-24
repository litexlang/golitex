use crate::prelude::*;
use std::fs::{self, File};
use std::io::{Read, Write};
use std::net::{TcpListener, TcpStream};
use std::path::{Component, Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

use super::export_reading::{
    reading_html, APP_JS, KATEX_CSS, KATEX_JS, KATEX_LICENSE, READER_CSS, READER_JS,
};
use super::helper::{object, text};
use super::partition_reading::ReadingSite;
use super::upload_cache::{UploadBuild, UploadCache};

const MAX_REQUEST: usize = 16 * 1024 * 1024;
const MAX_SOURCE: usize = 8 * 1024 * 1024;
const MAX_OUTPUT: u64 = 128 * 1024 * 1024;
static NEXT_UPLOAD: AtomicU64 = AtomicU64::new(0);

pub fn serve_reading(
    document: JsonValue,
    port: u16,
    open_browser: bool,
    strict: bool,
) -> RuntimeResult<()> {
    let listener = TcpListener::bind(("127.0.0.1", port))
        .map_err(|error| io_error(Path::new("<reading-server>"), error))?;
    let address = listener
        .local_addr()
        .map_err(|error| io_error(Path::new("<reading-server>"), error))?;
    let origin = format!("http://{address}");
    let site = ReadingSite::new(&document);
    let html = Arc::new(reading_html(&site.manifest, true));
    let full_url = site
        .manifest
        .as_object()
        .unwrap()
        .get("full_document_url")
        .unwrap()
        .as_str()
        .unwrap()
        .to_string();
    let mut files = site.files;
    let json = Arc::new(files.remove(&full_url).unwrap());
    let mut files = files
        .into_iter()
        .map(|(path, data)| (path, Arc::new(data)))
        .collect::<std::collections::BTreeMap<_, _>>();
    files.insert(full_url, Arc::clone(&json));
    let parts = Arc::new(files);
    let cache = Arc::new(UploadCache::new());
    eprintln!("Litex Reading: {origin}/");
    eprintln!("Press Ctrl-C to stop the local reader.");
    if open_browser {
        if let Err(error) = launch_browser(&format!("{origin}/")) {
            eprintln!("Could not open a browser ({error}); open {origin}/ manually.");
        }
    }
    for incoming in listener.incoming() {
        let stream = incoming.map_err(|error| io_error(Path::new("<reading-server>"), error))?;
        let html = Arc::clone(&html);
        let json = Arc::clone(&json);
        let parts = Arc::clone(&parts);
        let cache = Arc::clone(&cache);
        let origin = origin.clone();
        std::thread::spawn(move || {
            if let Err(error) =
                handle_connection(stream, &html, &json, &parts, &origin, strict, &cache)
            {
                eprintln!("reading request: {error}");
            }
        });
    }
    Ok(())
}

fn handle_connection(
    mut stream: TcpStream,
    html: &str,
    json: &str,
    parts: &std::collections::BTreeMap<String, Arc<String>>,
    origin: &str,
    strict: bool,
    cache: &UploadCache,
) -> std::io::Result<()> {
    stream.set_read_timeout(Some(Duration::from_secs(10)))?;
    stream.set_write_timeout(Some(Duration::from_secs(30)))?;
    let mut bytes = Vec::new();
    let header_end = loop {
        if let Some(index) = bytes.windows(4).position(|part| part == b"\r\n\r\n") {
            break index + 4;
        }
        if bytes.len() >= 16 * 1024 {
            return response(&mut stream, 431, "text/plain", "Request headers too large");
        }
        let mut chunk = [0; 4096];
        let count = stream.read(&mut chunk)?;
        if count == 0 {
            return Ok(());
        }
        bytes.extend_from_slice(&chunk[..count]);
    };
    let header = match std::str::from_utf8(&bytes[..header_end]) {
        Ok(header) => header.to_string(),
        Err(_) => return response(&mut stream, 400, "text/plain", "Invalid request header"),
    };
    if header_end > 16 * 1024 {
        return response(&mut stream, 431, "text/plain", "Request headers too large");
    }
    let mut lines = header.split("\r\n");
    let mut request = lines.next().unwrap_or("").split_whitespace();
    let method = request.next().unwrap_or("");
    let path = request.next().unwrap_or("").split('?').next().unwrap_or("");
    let mut length = None;
    let mut request_origin = None;
    let mut content_type = "";
    let mut host = "";
    for line in lines.filter(|line| !line.is_empty()) {
        let Some((name, value)) = line.split_once(':') else {
            return response(&mut stream, 400, "text/plain", "Invalid header");
        };
        match name.to_ascii_lowercase().as_str() {
            "content-length" => {
                if length.is_some() {
                    return response(&mut stream, 400, "text/plain", "Duplicate content length");
                }
                length = value.trim().parse::<usize>().ok();
                if length.is_none() {
                    return response(&mut stream, 400, "text/plain", "Invalid content length");
                }
            }
            "transfer-encoding" => {
                return response(
                    &mut stream,
                    400,
                    "text/plain",
                    "Transfer encoding is not supported",
                )
            }
            "origin" => request_origin = Some(value.trim()),
            "content-type" => content_type = value.trim(),
            "host" => host = value.trim(),
            _ => {}
        }
    }
    if host != origin.trim_start_matches("http://") {
        return response(
            &mut stream,
            403,
            "application/json",
            &error_json("Unexpected local server host"),
        );
    }
    if method == "GET" {
        if let Some(part) = parts.get(path.trim_start_matches('/')) {
            return response(&mut stream, 200, "application/json; charset=utf-8", part);
        }
        return match path {
            "/" | "/index.html" => response(&mut stream, 200, "text/html; charset=utf-8", html),
            "/reader.js" => response(
                &mut stream,
                200,
                "text/javascript; charset=utf-8",
                READER_JS,
            ),
            "/reader.css" => response(&mut stream, 200, "text/css; charset=utf-8", READER_CSS),
            "/katex.min.js" => {
                response(&mut stream, 200, "text/javascript; charset=utf-8", KATEX_JS)
            }
            "/katex.min.css" => response(&mut stream, 200, "text/css; charset=utf-8", KATEX_CSS),
            "/katex.LICENSE" => {
                response(&mut stream, 200, "text/plain; charset=utf-8", KATEX_LICENSE)
            }
            "/app.js" => response(&mut stream, 200, "text/javascript; charset=utf-8", APP_JS),
            "/reading.json" => response(&mut stream, 200, "application/json; charset=utf-8", json),
            _ => response(&mut stream, 404, "text/plain", "Not found"),
        };
    }
    if method != "POST" || path != "/api/reading/build" {
        return response(
            &mut stream,
            405,
            "application/json",
            &error_json("Unsupported reading request"),
        );
    }
    if request_origin.is_some_and(|request_origin| request_origin != origin) {
        return response(
            &mut stream,
            403,
            "application/json",
            &error_json("Cross-origin builds are not allowed"),
        );
    }
    if content_type.split(';').next() != Some("application/json") {
        return response(
            &mut stream,
            415,
            "application/json",
            &error_json("Use application/json"),
        );
    }
    let Some(length) = length else {
        return response(
            &mut stream,
            411,
            "application/json",
            &error_json("Content length is required"),
        );
    };
    if length > MAX_REQUEST {
        return response(
            &mut stream,
            413,
            "application/json",
            &error_json("Reading upload exceeds 16 MiB"),
        );
    }
    let already = bytes.len() - header_end;
    if already < length {
        Read::take(&mut stream, (length - already) as u64).read_to_end(&mut bytes)?;
    }
    if bytes.len() < header_end + length {
        return response(
            &mut stream,
            400,
            "application/json",
            &error_json("Incomplete request body"),
        );
    }
    let result = std::str::from_utf8(&bytes[header_end..header_end + length])
        .map_err(|_| "Reading input must be UTF-8".to_string())
        .and_then(|body| build_upload(body, strict, cache));
    match result {
        Ok(build) => {
            write!(stream, "HTTP/1.1 200 OK\r\nContent-Type: application/json; charset=utf-8\r\nContent-Length: {}\r\nCache-Control: no-store\r\nX-Litex-Reading-Cache: {}\r\nConnection: close\r\n\r\n", build.json.len(), build.cache_status)?;
            stream.write_all(build.json.as_bytes())
        }
        Err(error) => response(
            &mut stream,
            400,
            "application/json; charset=utf-8",
            &error_json(&error),
        ),
    }
}

fn build_upload(body: &str, strict: bool, cache: &UploadCache) -> Result<UploadBuild, String> {
    check_json_depth(body)?;
    let request = JsonValue::parse(body).map_err(|error| error.to_string())?;
    let fields = request.as_object().map_err(|error| error.to_string())?;
    let files = fields
        .get("files")
        .ok_or("Missing files")?
        .as_array()
        .map_err(|error| error.to_string())?;
    if files.is_empty() || files.len() > 512 {
        return Err("Provide between 1 and 512 source/config files".into());
    }
    let workspace = UploadWorkspace::new().map_err(|error| error.to_string())?;
    let input_root = workspace.path.join("input");
    fs::create_dir(&input_root).map_err(|error| error.to_string())?;
    let input_root = input_root
        .canonicalize()
        .map_err(|error| error.to_string())?;
    let mut names = std::collections::BTreeSet::new();
    let mut configs = Vec::new();
    let mut sources = Vec::new();
    let mut total = 0;
    for file in files {
        let file = file.as_object().map_err(|error| error.to_string())?;
        let name = file
            .get("path")
            .ok_or("Missing file path")?
            .as_str()
            .map_err(|error| error.to_string())?;
        let path = safe_upload_path(name)?;
        if !names.insert(path.clone()) {
            return Err(format!("Duplicate upload path: {name}"));
        }
        let content = file
            .get("content")
            .ok_or("Missing file content")?
            .as_str()
            .map_err(|error| error.to_string())?;
        total += content.len();
        if total > MAX_SOURCE {
            return Err("Source/config input exceeds 8 MiB".into());
        }
        let destination = input_root.join(&path);
        if path.file_name().is_some_and(|name| name == "litex.config") {
            configs.push(destination.clone());
        } else if path.extension().is_some_and(|extension| extension == "lit") {
            sources.push(destination.clone());
        } else if path
            .file_name()
            .is_some_and(|name| name == "reading-titles.json")
        {
            // Optional source presentation metadata; not a runnable input.
        } else {
            return Err(format!(
                "Only .lit, litex.config and reading-titles.json files are accepted: {name}"
            ));
        }
        if let Some(parent) = destination.parent() {
            fs::create_dir_all(parent).map_err(|error| error.to_string())?;
        }
        fs::write(destination, content).map_err(|error| error.to_string())?;
    }
    let closed_project = validate_upload_configs(&input_root, &configs)?;
    configs.sort_by_key(|path| (path.components().count(), path.clone()));
    let (mode, entry) = if let Some(entry) = fields.get("entry") {
        let entry = entry.as_object().map_err(|error| error.to_string())?;
        let kind = entry
            .get("kind")
            .ok_or("Missing entry kind")?
            .as_str()
            .map_err(|error| error.to_string())?;
        let name = entry
            .get("path")
            .ok_or("Missing entry path")?
            .as_str()
            .map_err(|error| error.to_string())?;
        let path = if kind == "project" && name == "." {
            input_root.clone()
        } else {
            input_root.join(safe_upload_path(name)?)
        };
        match kind {
            "file"
                if path.is_file()
                    && path.extension().is_some_and(|extension| extension == "lit") =>
            {
                ("-f", path)
            }
            "project" if path.join("litex.config").is_file() => ("-r", path),
            _ => {
                return Err(
                    "Entry must identify an uploaded .lit file or a project with litex.config"
                        .into(),
                )
            }
        }
    } else if let Some(config) = configs.first() {
        if configs
            .get(1)
            .is_some_and(|next| next.components().count() == config.components().count())
        {
            return Err("Several project roots were uploaded; select an explicit entry".into());
        }
        ("-r", config.parent().unwrap().to_path_buf())
    } else if sources.len() == 1 {
        ("-f", sources.remove(0))
    } else {
        return Err(
            "Multiple .lit files need litex.config to establish their execution order".into(),
        );
    };
    let language = fields
        .get("language")
        .map(|value| value.as_str().map_err(|error| error.to_string()))
        .transpose()?
        .unwrap_or("en");
    OutputLanguage::parse_token(language).map_err(|error| error.to_string())?;
    let requested_strict = match fields.get("strict") {
        Some(JsonValue::Bool(value)) => *value,
        None => false,
        Some(_) => return Err("strict must be a boolean".into()),
    };
    let stdout_path = workspace.path.join("output.json");
    let stderr_path = workspace.path.join("error.txt");
    let executable = std::env::current_exe().map_err(|error| error.to_string())?;
    let engine_id = if closed_project {
        super::helper::executable_digest()
    } else {
        None
    };
    let cache_key = engine_id.as_ref().map(|id| format!("{strict}:{id}:{body}"));
    if let Some(json) = cache_key.as_ref().and_then(|key| cache.get(key)) {
        return Ok(UploadBuild::new(json, "hit"));
    }
    let mut command = Command::new(executable);
    command
        .args(["-reading", "-json", mode])
        .arg(entry)
        .args(["-lang", language]);
    if strict || requested_strict {
        command.arg("-strict");
    }
    let mut child = command
        .stdin(Stdio::null())
        .stdout(File::create(&stdout_path).map_err(|error| error.to_string())?)
        .stderr(File::create(&stderr_path).map_err(|error| error.to_string())?)
        .spawn()
        .map_err(|error| error.to_string())?;
    let started = Instant::now();
    let status = loop {
        if let Some(status) = child.try_wait().map_err(|error| error.to_string())? {
            break status;
        }
        if started.elapsed() > Duration::from_secs(120)
            || fs::metadata(&stdout_path)
                .map(|meta| meta.len() > MAX_OUTPUT)
                .unwrap_or(false)
        {
            let _ = child.kill();
            let _ = child.wait();
            return Err("Reading build exceeded its 120-second or 128-MiB output limit".into());
        }
        std::thread::sleep(Duration::from_millis(30));
    };
    if !matches!(status.code(), Some(0 | 1)) {
        let message = fs::read_to_string(stderr_path).unwrap_or_default();
        return Err(format!("Reading process stopped: {status}. {message}"));
    }
    let json = fs::read_to_string(&stdout_path).map_err(|error| error.to_string())?;
    if json.is_empty() || json.len() as u64 > MAX_OUTPUT {
        return Err("Reading process produced no usable bundle".into());
    }
    if let Some(key) = cache_key.as_ref() {
        if status.success() {
            let document = JsonValue::parse(&json).map_err(|error| error.to_string())?;
            let actual_engine = document
                .as_object()
                .ok()
                .and_then(|fields| fields.get("engine"))
                .and_then(|engine| engine.as_object().ok())
                .and_then(|fields| fields.get("executable_id"))
                .and_then(|id| id.as_str().ok());
            if actual_engine == engine_id.as_deref() {
                let json = Arc::new(json);
                cache.insert(key.clone(), Arc::clone(&json));
                return Ok(UploadBuild::new(json, "miss"));
            }
        }
    }
    Ok(UploadBuild::new(
        Arc::new(json),
        if cache_key.is_some() {
            "miss"
        } else {
            "bypass"
        },
    ))
}

pub(super) fn safe_upload_path(name: &str) -> Result<PathBuf, String> {
    let path = PathBuf::from(name);
    if name.is_empty()
        || name.contains('\\')
        || path.is_absolute()
        || path
            .components()
            .any(|part| !matches!(part, Component::Normal(_)))
    {
        return Err(format!(
            "Upload paths must be relative project paths: {name}"
        ));
    }
    Ok(path)
}

fn validate_upload_configs(root: &Path, configs: &[PathBuf]) -> Result<bool, String> {
    let std_root = crate::run_module::resolve_std_root(Some(root));
    let allowed_std = normalize_path(&std_root);
    let mut closed_project = true;
    for config in configs {
        let config = crate::run_module::load_config(config.parent().unwrap(), &std_root)
            .map_err(|error| error.to_string())?;
        for export in &config.exports {
            if !normalize_path(&export.path).starts_with(root) {
                return Err("Uploaded exports must stay inside the uploaded project".into());
            }
        }
        for import in &config.imports {
            let path = normalize_path(&import.path);
            closed_project &= path.starts_with(root);
            if !path.starts_with(root) && !path.starts_with(&allowed_std) {
                return Err("Upload all project dependencies; imports may only use uploaded files or the configured std library".into());
            }
        }
    }
    Ok(closed_project)
}

fn normalize_path(path: &Path) -> PathBuf {
    if let Ok(path) = path.canonicalize() {
        return path;
    }
    let mut result = PathBuf::new();
    for part in path.components() {
        match part {
            Component::ParentDir => {
                result.pop();
            }
            Component::CurDir => {}
            _ => result.push(part.as_os_str()),
        }
    }
    result
}

fn check_json_depth(body: &str) -> Result<(), String> {
    let mut depth = 0usize;
    let mut quoted = false;
    let mut escaped = false;
    for byte in body.bytes() {
        if quoted {
            if escaped {
                escaped = false;
            } else if byte == b'\\' {
                escaped = true;
            } else if byte == b'"' {
                quoted = false;
            }
        } else {
            match byte {
                b'"' => quoted = true,
                b'[' | b'{' => {
                    depth += 1;
                    if depth > 64 {
                        return Err("Upload JSON is nested too deeply".into());
                    }
                }
                b']' | b'}' => depth = depth.saturating_sub(1),
                _ => {}
            }
        }
    }
    Ok(())
}

fn response(
    stream: &mut TcpStream,
    status: u16,
    content_type: &str,
    body: &str,
) -> std::io::Result<()> {
    let reason = match status {
        200 => "OK",
        400 => "Bad Request",
        403 => "Forbidden",
        404 => "Not Found",
        405 => "Method Not Allowed",
        411 => "Length Required",
        413 => "Payload Too Large",
        415 => "Unsupported Media Type",
        _ => "Request Rejected",
    };
    write!(stream, "HTTP/1.1 {status} {reason}\r\nContent-Type: {content_type}\r\nContent-Length: {}\r\nConnection: close\r\nCache-Control: no-store\r\nX-Content-Type-Options: nosniff\r\n\r\n", body.len())?;
    stream.write_all(body.as_bytes())
}

fn error_json(message: &str) -> String {
    object(vec![("error", text(message))]).stringify()
}

fn launch_browser(url: &str) -> std::io::Result<()> {
    #[cfg(target_os = "macos")]
    let mut command = Command::new("open");
    #[cfg(target_os = "windows")]
    let mut command = {
        let mut command = Command::new("cmd");
        command.args(["/C", "start", ""]);
        command
    };
    #[cfg(not(any(target_os = "macos", target_os = "windows")))]
    let mut command = Command::new("xdg-open");
    let status = command
        .arg(url)
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status()?;
    if status.success() {
        Ok(())
    } else {
        Err(std::io::Error::other(format!(
            "browser launcher exited {status}"
        )))
    }
}

fn io_error(path: &Path, error: std::io::Error) -> RuntimeError {
    RuntimeError::Io {
        path: path.into(),
        message: error.to_string(),
    }
}

struct UploadWorkspace {
    path: PathBuf,
}

impl UploadWorkspace {
    fn new() -> std::io::Result<Self> {
        let stamp = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap_or_default()
            .as_nanos();
        let serial = NEXT_UPLOAD.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "litex-reading-{}-{stamp}-{serial}",
            std::process::id()
        ));
        fs::create_dir(&path)?;
        Ok(Self { path })
    }
}

impl Drop for UploadWorkspace {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}
