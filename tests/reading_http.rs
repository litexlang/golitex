//! Real loopback service + child verifier acceptance. No mock proof bundles.
use litex::knowledge_base::JsonValue;
use std::io::{BufRead, BufReader, Read, Write};
use std::net::TcpStream;
use std::process::{Child, ChildStderr, Command, Stdio};
use std::time::Duration;

struct LocalReader {
    child: Child,
    authority: String,
    stderr: BufReader<ChildStderr>,
}

impl LocalReader {
    fn start(strict: bool) -> Self {
        let mut command = Command::new(env!("CARGO_BIN_EXE_litex"));
        command.args([
            "-reading",
            "-no-browser",
            "-lang",
            "en",
            "-e",
            "have preview_value R\n0 <= preview_value ^ 2\n",
        ]);
        if strict {
            command.arg("-strict");
        }
        let mut child = command
            .stdin(Stdio::null())
            .stdout(Stdio::null())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();
        let stderr = BufReader::new(child.stderr.take().unwrap());
        let mut server = Self {
            child,
            authority: String::new(),
            stderr,
        };
        let mut line = String::new();
        server.stderr.read_line(&mut line).unwrap();
        server.authority = line
            .trim()
            .strip_prefix("Litex Reading: http://")
            .expect(&line)
            .trim_end_matches('/')
            .into();
        assert!(server.authority.starts_with("127.0.0.1:"));
        server
    }

    fn request(&self, method: &str, path: &str, headers: &str, body: &str) -> (u16, String) {
        let (status, body, _) = self.request_details(method, path, headers, body);
        (status, body)
    }

    fn request_details(
        &self,
        method: &str,
        path: &str,
        headers: &str,
        body: &str,
    ) -> (u16, String, String) {
        let mut stream = TcpStream::connect(&self.authority).unwrap();
        stream
            .set_read_timeout(Some(Duration::from_secs(30)))
            .unwrap();
        write!(
            stream,
            "{method} {path} HTTP/1.1\r\nHost: {}\r\n{headers}Connection: close\r\n\r\n{body}",
            self.authority
        )
        .unwrap();
        let mut response = String::new();
        stream.read_to_string(&mut response).unwrap();
        let (header, body) = response.split_once("\r\n\r\n").expect(&response);
        let status = header.split_whitespace().nth(1).unwrap().parse().unwrap();
        (status, body.into(), header.into())
    }

    fn build(&self, body: &str) -> (u16, String) {
        self.request(
            "POST",
            "/api/reading/build",
            &format!(
                "Content-Type: application/json\r\nContent-Length: {}\r\nOrigin: http://{}\r\n",
                body.len(),
                self.authority
            ),
            body,
        )
    }
}

#[test]
fn upload_cache_reuses_complete_evidence_and_invalidates_changed_requests() {
    let server = LocalReader::start(false);
    let request = body(vec![("chapter.lit", "0 = 0\n")], None);
    let build = |request: &str| {
        server.request_details(
            "POST",
            "/api/reading/build",
            &format!(
                "Content-Type: application/json\r\nContent-Length: {}\r\n",
                request.len()
            ),
            request,
        )
    };
    let first = build(&request);
    assert_eq!(first.0, 200);
    assert!(first.2.contains("X-Litex-Reading-Cache: miss"));
    let repeated = build(&request);
    assert!(repeated.2.contains("X-Litex-Reading-Cache: hit"));
    assert_eq!(
        repeated.1, first.1,
        "a cache hit preserves the complete evidence verbatim"
    );
    for changed in [
        request.replace("0 = 0", "1 = 1"),
        request.replace("\"zh\"", "\"en\""),
        format!("{{\"strict\":true,{}", &request[1..]),
        request.replace("chapter.lit", "renamed.lit"),
    ] {
        let response = build(&changed);
        assert_eq!(response.0, 200, "{}", response.1);
        assert!(response.2.contains("X-Litex-Reading-Cache: miss"));
        let document = JsonValue::parse(&response.1).unwrap();
        assert_ne!(
            document.field("bundle_id"),
            JsonValue::parse(&first.1).unwrap().field("bundle_id")
        );
    }
    let broken = body(vec![("broken.lit", "missing_reading_value = 0\n")], None);
    for _ in 0..2 {
        let response = build(&broken);
        assert!(response.2.contains("X-Litex-Reading-Cache: miss"));
        assert_eq!(
            JsonValue::parse(&response.1)
                .unwrap()
                .field("run_result")
                .as_str()
                .unwrap(),
            "failure"
        );
    }
}

impl Drop for LocalReader {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

fn body(files: Vec<(&str, &str)>, entry: Option<(&str, &str)>) -> String {
    let files = files
        .into_iter()
        .map(|(path, content)| {
            JsonValue::object_from(vec![
                ("path".into(), JsonValue::String(path.into())),
                ("content".into(), JsonValue::String(content.into())),
            ])
        })
        .collect();
    let mut fields = vec![
        ("files".into(), JsonValue::Array(files)),
        ("language".into(), JsonValue::String("zh".into())),
    ];
    if let Some((kind, path)) = entry {
        fields.push((
            "entry".into(),
            JsonValue::object_from(vec![
                ("kind".into(), JsonValue::String(kind.into())),
                ("path".into(), JsonValue::String(path.into())),
            ]),
        ));
    }
    JsonValue::object_from(fields).stringify()
}

trait Fields {
    fn field(&self, name: &str) -> &JsonValue;
}
impl Fields for JsonValue {
    fn field(&self, name: &str) -> &JsonValue {
        self.as_object().unwrap().get(name).unwrap()
    }
}

#[test]
fn real_upload_preview_project_and_failure_boundaries() {
    let server = LocalReader::start(false);
    let (status, html) = server.request("GET", "/", "", "");
    assert_eq!(status, 200);
    assert!(html.contains("litex-reading-page"));
    assert!(html.contains("data-live=\"true\""));
    assert!(html.contains("katex.min.js") && html.contains("katex.min.css"));
    for (path, marker, mime) in [
        ("/katex.min.js", "KaTeX", "text/javascript"),
        ("/katex.min.css", "data:font/woff2;base64,", "text/css"),
        (
            "/katex.LICENSE",
            "Permission is hereby granted",
            "text/plain",
        ),
    ] {
        let (status, asset, headers) = server.request_details("GET", path, "", "");
        assert_eq!(status, 200);
        assert!(asset.contains(marker) && headers.contains(mime));
    }
    let (status, manifest) = server.request("GET", "/reading.manifest.json", "", "");
    assert_eq!(status, 200);
    let manifest = JsonValue::parse(&manifest).unwrap();
    assert_eq!(manifest.field("kind").as_str().unwrap(), "reading_manifest");
    let (status, full) = server.request(
        "GET",
        &format!("/{}", manifest.field("full_document_url").as_str().unwrap()),
        "",
        "",
    );
    assert_eq!(status, 200);
    let full = JsonValue::parse(&full).unwrap();
    assert_eq!(manifest.field("bundle_id"), full.field("bundle_id"));
    for source in manifest.field("sources").as_array().unwrap() {
        let (status, chunk) = server.request(
            "GET",
            &format!("/{}", source.field("chunk_url").as_str().unwrap()),
            "",
            "",
        );
        assert_eq!(status, 200);
        let chunk = JsonValue::parse(&chunk).unwrap();
        assert_eq!(chunk.field("manifest_id"), manifest.field("manifest_id"));
        assert_eq!(chunk.field("source_id"), source.field("id"));
    }
    let response = server.build(&body(
        vec![(
            "chapter.lit",
            include_str!("../examples/reading/linked_facts.lit"),
        )],
        None,
    ));
    assert_eq!(response.0, 200, "{}", response.1);
    let bundle = JsonValue::parse(&response.1).unwrap();
    assert_eq!(bundle.field("kind").as_str().unwrap(), "reading");
    assert_eq!(bundle.field("run_result").as_str().unwrap(), "success");
    assert_eq!(bundle.field("statements").as_array().unwrap().len(), 3);

    let response = server.build(&body(
        vec![(
            "inferred.lit",
            include_str!("../examples/reading/inferred_facts.lit"),
        )],
        None,
    ));
    assert_eq!(response.0, 200, "{}", response.1);
    let bundle = JsonValue::parse(&response.1).unwrap();
    assert_eq!(bundle.field("run_result").as_str().unwrap(), "success");
    assert!(!bundle.field("inferences").as_array().unwrap().is_empty());
    let statements = bundle.field("statements").as_array().unwrap();
    let inferred = statements[3].field("inferred_fact_ids").as_array().unwrap();
    let later_cites = statements[4].field("cited_fact_ids").as_array().unwrap();
    assert!(
        inferred.iter().any(|id| later_cites.contains(id)),
        "the real upload must retain the later citation to its inferred fact"
    );

    let response = server.build(&body(
        vec![
            (
                "litex.config",
                "[import]\nValues=\"./library\"\n[export]\nmain=\"./main.lit\"\n",
            ),
            ("library/litex.config", "[export]\nbase=\"./base.lit\"\n"),
            (
                "library/base.lit",
                include_str!("../examples/module_manager/identifier_resolution/library/base.lit"),
            ),
            ("main.lit", "Values::base::k = 2\n"),
        ],
        Some(("project", ".")),
    ));
    assert_eq!(response.0, 200, "{}", response.1);
    let bundle = JsonValue::parse(&response.1).unwrap();
    assert_eq!(
        bundle.field("run_result").as_str().unwrap(),
        "success",
        "{}",
        response.1
    );
    let sources = bundle.field("sources").as_array().unwrap();
    assert_eq!(sources.len(), 2);
    let main = sources
        .iter()
        .find(|source| source.field("path").as_str().unwrap() == "main.lit")
        .unwrap();
    assert_eq!(bundle.field("entry_source_id"), main.field("id"));
    assert_eq!(sources[0].field("role").as_str().unwrap(), "dependency");
    assert!(
        !response.1.contains("/litex-reading-"),
        "temporary absolute paths must not be published"
    );

    let response = server.build(&body(vec![("broken.lit", "Missing::base::k = 2\n")], None));
    assert_eq!(response.0, 200);
    let bundle = JsonValue::parse(&response.1).unwrap();
    assert_eq!(bundle.field("run_result").as_str().unwrap(), "failure");
    assert!(!bundle.field("diagnostics").as_array().unwrap().is_empty());

    for files in [
        vec![("../outside.lit", "0=0")],
        vec![("/outside.lit", "0=0")],
        vec![("a\\outside.lit", "0=0")],
        vec![("same.lit", "0=0"), ("same.lit", "0=0")],
        vec![("litex.config", "[export]\nmain=\"../outside.lit\"\n")],
        vec![("one.lit", "0=0"), ("two.lit", "0=0")],
    ] {
        let response = server.build(&body(files, None));
        assert_eq!(response.0, 400, "{}", response.1);
    }
    let response = server.build(&body(
        vec![("litex.config", "[export]\n")],
        Some(("file", "litex.config")),
    ));
    assert_eq!(response.0, 400);
    let response = server.build(&format!(
        "{{\"files\":{}0{}}}",
        "[".repeat(65),
        "]".repeat(65)
    ));
    assert_eq!(response.0, 400);
    assert!(response.1.contains("nested too deeply"));

    assert_eq!(server.request("POST", "/api/reading/build", "Content-Type: application/json\r\nContent-Length: 2\r\nOrigin: https://example.com\r\n", "{}").0, 403);
    assert_eq!(
        server
            .request(
                "POST",
                "/api/reading/build",
                "Content-Type: application/json\r\nContent-Length: 2\r\nContent-Length: 2\r\n",
                "{}"
            )
            .0,
        400
    );
    assert_eq!(
        server
            .request(
                "POST",
                "/api/reading/build",
                "Content-Type: text/plain\r\nContent-Length: 2\r\n",
                "{}"
            )
            .0,
        415
    );
    assert_eq!(
        server
            .request(
                "POST",
                "/api/reading/build",
                "Content-Type: application/json\r\nContent-Length: 16777217\r\n",
                ""
            )
            .0,
        413
    );
    assert_eq!(server.request("GET", "/unknown", "", "").0, 404);
}

#[test]
fn server_strict_policy_cannot_be_weakened_by_an_upload() {
    let server = LocalReader::start(true);
    let response = server.build(&body(vec![("assumption.lit", "trust 7 = 7\n")], None));
    assert_eq!(response.0, 200);
    let bundle = JsonValue::parse(&response.1).unwrap();
    assert_eq!(bundle.field("run_result").as_str().unwrap(), "failure");
    assert!(matches!(
        bundle.field("execution_policy").field("strict"),
        JsonValue::Bool(true)
    ));
}
