use anyhow::{Context, Result};
use base64::{engine::general_purpose::STANDARD, Engine as _};
use jsvm_lift::{
    capture_import::{import_capture_project, CaptureImportOptions},
    project_deob::{materialize_project_deobfuscation, ProjectDeobOptions},
    source_graph::build_source_graph,
    source_materialize::materialize_capture_source,
    wasm_js_boundary::correlate_project,
    wasm_materialize::materialize_wasm,
};
use serde_json::{json, Value};
use std::{collections::BTreeSet, fs, path::Path};

const HOST_EFFECT_WASM_HEX: &str = concat!(
    "0061736d010000000131096000016f60026f7f017f60016f016f60016f017f60036f7f7f016f60036f7f7f006000017f60017f017f60037f7f7f0002f7010803776267115f5f7762696e6467656e5f6d656d6f72790000037762671b5f5f7762675f67726f775f343364333639303838613337303639340001037762671d5f5f7762675f6275666665725f36303963633365656535316564313538000203776267215f5f7762675f627974654c656e6774685f656135326163336465383832623438330003037762671a5f5f7762675f6e65775f37653037396661323565313335656231000403776267205f5f7762675f67657455696e7433325f39633363633866646537393139656434000103776267145f5f7762675f7369676e616c5f66697874757265000504686f737405616c6c6f63000603060506070708060404016f00100707010372756e000c0a8502050e01017f100722001000260020000b1802016f017f2000250010022101100722022001260020020b3003027f016f017f100810092201250010032102200125004100200210042103100722042003260020042500200010050b0c00200025002001200210060b9c0101027f010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101011008220025004101100141107421012000200141d01b100b200141d01b72100a1a200020014184bb03100b20014184bb0372100a0b008402046e616d650180010c00066d656d6f7279010467726f770206627566666572030b627974655f6c656e6774680408766965775f6e657705076765745f753332060d6f70617175655f7369676e616c0705616c6c6f63080b6d656d6f72795f736c6f74090b6275666665725f736c6f740a0a6d656d6f72795f6765740b0b686f73745f656666656374027a0508010004736c6f740903000b6d656d6f72795f736c6f7401066275666665720204736c6f740a0500066f6666736574010b6275666665725f736c6f7402066c656e6774680304766965770409766965775f736c6f740b030004736c6f7401046261736502066f66667365740c020004736c6f74010462617365"
);

const COPIED_WASM_HEX: &str = concat!(
    "0061736d01000000011f066000016f60016f016f60036f6f7f006000017f60017f017f60026f7f017f022e0303776267115f5f7762696e6467656e5f",
    "6d656d6f72790000037762670463746f720001037762670373657400020304030304050404016f00040503010001071102066d656d6f727902000463",
    "6f707900050aad01030e01017f410222001000260020000b040020000b960101017f0101010101010101010101010101010101010101010101010101",
    "010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101",
    "0101010101010101012001417c712102410020002600410110031004250010012600410125004100250020024102761002200228020020022802046a",
    "0b0061046e616d65012e0500066d656d6f7279010463746f720203736574030b6d656d6f72795f736c6f74040b6275666665725f736c6f74022a0303",
    "010004736c6f7404010004736c6f7405030006736f757263650104626173650207616c69676e6564",
);

const FRESH_WASM_HEX: &str = concat!(
    "0061736d0100000001270860016f017f6000016f60016f016f60036f6f7f006000006000017f60017f017f60026f7f017f02610503776267066c656e",
    "677468000003776267115f5f7762696e6467656e5f6d656d6f72790001037762670463746f72000203776267037365740003037762671f5f5f776269",
    "6e6467656e5f696e69745f65787465726e7265665f7461626c65000403060505060606070404016f00080503010001073a04135f5f7762696e646765",
    "6e5f6578706f72745f300100066d656d6f72790200105f5f7762696e6467656e5f7374617274000404636f707900090ace01050e01017f4102220010",
    "01260020000b040020000b08002000250010000b0a00410028020020006a0ba30101017f010101010101010101010101010101010101010101010101",
    "010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101",
    "0101010101010101010101014100200026004101100510062500100226002001047f4104054100100741027410080b21024101250041002500200241",
    "02761003200228020020022802046a0b0b0a010041000b0408000000009701046e616d6501530900066c656e67746801066d656d6f7279020463746f",
    "72030373657404057374617274050b6d656d6f72795f736c6f74060b6275666665725f736c6f74070d6c656e6774685f68656c7065720805616c6c6f",
    "63023b0505010004736c6f7406010004736c6f7407010004736c6f7408010005627974657309030006736f7572636501077573655f616c7402046261",
    "7365",
);

const CLEANUP_WASM_HEX: &str = concat!(
    "0061736d01000000012b0960016f017f6000016f60016f016f60036f6f7f006000006000017f60017f017f60017f0060026f7f017f026e0603776267",
    "066c656e677468000003776267115f5f7762696e6467656e5f6d656d6f7279000103776267066275666665720002037762670463746f720002037762",
    "67037365740003037762671f5f5f7762696e6467656e5f696e69745f65787465726e7265665f7461626c650004030807050506060607080404016f00",
    "0805030100010606017f0141080b073a04135f5f7762696e6467656e5f6578706f72745f300100066d656d6f72790200105f5f7762696e6467656e5f",
    "7374617274000504636f7079000c0a9d02070f01017f2300220041016a240020000b0e01017f100622001001260020000b1802016f017f2000250010",
    "022101100622022001260020020b08002000250010000b0a00410028020020006a0b100020004102744180086a41003602000bbd0103037f016f017f",
    "010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101",
    "010101010101010101010101010101010101010101010101010101010101010101010101410020002600100722021008220325001003210510062204",
    "200526002003100b2001047f41040541001009410274100a0b21062004250041002500200641027610042004100b2002100b20062802002006280204",
    "6a0b0b0a010041000b0408000000009a02046e616d6501700c00066c656e67746801066d656d6f72790206627566666572030463746f720403736574",
    "05057374617274060a736c6f745f616c6c6f63070b6d656d6f72795f736c6f74080b6275666665725f736c6f74090d6c656e6774685f68656c706572",
    "0a05616c6c6f630b07636c65616e75700292010706010004736c6f7407010004736c6f740803000b6d656d6f72795f736c6f74010576616c75650204",
    "736c6f7409010004736c6f740a01000562797465730b010004736c6f740c070006736f7572636501077573655f616c74020b6d656d6f72795f736c6f",
    "74030b6275666665725f736c6f74040d72656365697665725f736c6f7405087265636569766572060462617365070c0100096e6578745f736c6f74",
);

const CLEANUP_OVERLAP_WASM_HEX: &str = concat!(
    "0061736d01000000012b0960016f017f6000016f60016f016f60036f6f7f006000006000017f60017f017f60017f0060026f7f017f026e0603776267",
    "066c656e677468000003776267115f5f7762696e6467656e5f6d656d6f7279000103776267066275666665720002037762670463746f720002037762",
    "67037365740003037762671f5f5f7762696e6467656e5f696e69745f65787465726e7265665f7461626c650004030807050506060607080404016f00",
    "0805030100010606017f0141080b073a04135f5f7762696e6467656e5f6578706f72745f300100066d656d6f72790200105f5f7762696e6467656e5f",
    "7374617274000504636f7079000c0a9902070f01017f2300220041016a240020000b0e01017f100622001001260020000b1802016f017f2000250010",
    "022101100622022001260020020b08002000250010000b0a00410028020020006a0b0c0020001a411041003602000bbd0103037f016f017f01010101",
    "010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101",
    "010101010101010101010101010101010101010101010101010101010101010141002000260010072202100822032500100321051006220420052600",
    "2003100b2001047f41040541001009410274100a0b21062004250041002500200641027610042004100b2002100b200628020020062802046a0b0b0a",
    "010041000b0408000000009a02046e616d6501700c00066c656e67746801066d656d6f72790206627566666572030463746f72040373657405057374",
    "617274060a736c6f745f616c6c6f63070b6d656d6f72795f736c6f74080b6275666665725f736c6f74090d6c656e6774685f68656c7065720a05616c",
    "6c6f630b07636c65616e75700292010706010004736c6f7407010004736c6f740803000b6d656d6f72795f736c6f74010576616c75650204736c6f74",
    "09010004736c6f740a01000562797465730b010004736c6f740c070006736f7572636501077573655f616c74020b6d656d6f72795f736c6f74030b62",
    "75666665725f736c6f74040d72656365697665725f736c6f7405087265636569766572060462617365070c0100096e6578745f736c6f74",
);

fn decode_hex(hex: &str) -> Result<Vec<u8>> {
    anyhow::ensure!(hex.len() % 2 == 0, "odd-length hex fixture");
    (0..hex.len())
        .step_by(2)
        .map(|index| {
            u8::from_str_radix(&hex[index..index + 2], 16)
                .with_context(|| format!("invalid hex at byte {}", index / 2))
        })
        .collect()
}

fn har_entry(url: &str, mime: &str, text: &str, encoding: Option<&str>) -> Value {
    let mut content = json!({"size": text.len(), "mimeType": mime, "text": text});
    if let Some(encoding) = encoding {
        content["encoding"] = encoding.into();
    }
    json!({
        "pageref": "page_1",
        "startedDateTime": "2026-10-11T00:00:00.000Z",
        "time": 1,
        "request": {"method": "GET", "url": url, "httpVersion": "HTTP/2", "headers": [], "queryString": [], "cookies": [], "headersSize": -1, "bodySize": 0},
        "response": {"status": 200, "statusText": "OK", "httpVersion": "HTTP/2", "headers": [{"name": "content-type", "value": mime}], "cookies": [], "content": content, "redirectURL": "", "headersSize": -1, "bodySize": text.len()},
        "cache": {},
        "timings": {"send": 0, "wait": 1, "receive": 0},
    })
}

fn write_har(path: &Path, title: &str, entries: Vec<Value>) -> Result<()> {
    fs::write(
        path,
        serde_json::to_vec(&json!({
            "log": {
                "version": "1.2",
                "creator": {"name": title, "version": "1"},
                "pages": [{"startedDateTime": "2026-10-11T00:00:00.000Z", "id": "page_1", "title": title, "pageTimings": {}}],
                "entries": entries,
            }
        }))?,
    )?;
    Ok(())
}

fn write_inline_wasm_har(path: &Path, title: &str, source: &str) -> Result<()> {
    write_har(
        path,
        title,
        vec![
            har_entry(
                "https://fixture.invalid/index.html",
                "text/html",
                "<!doctype html><script src=\"https://fixture.invalid/carrier.js\"></script>",
                None,
            ),
            har_entry(
                "https://fixture.invalid/carrier.js",
                "application/javascript",
                source,
                None,
            ),
        ],
    )
}

fn run_wasm_boundary_pipeline(input: &Path, project: &Path) -> Result<Value> {
    import_capture_project(&CaptureImportOptions {
        input: input.to_owned(),
        output: project.to_owned(),
        assets_dir: None,
        overwrite: false,
    })?;
    materialize_capture_source(project, Some(1))?;
    materialize_wasm(project, None)?;
    materialize_project_deobfuscation(
        project,
        &ProjectDeobOptions {
            jobs: Some(1),
            max_iterations: 16,
        },
    )?;
    correlate_project(project)?;
    read_json(&project.join("analysis/wasm-js-boundary.json"))
}

fn read_json(path: &Path) -> Result<Value> {
    serde_json::from_slice(&fs::read(path).with_context(|| format!("reading {}", path.display()))?)
        .with_context(|| format!("parsing {}", path.display()))
}

fn copied_input_js(wasm: &[u8], fresh: bool) -> String {
    let encoded = STANDARD.encode(wasm);
    let mut imports = String::from(
        "var host = window;\nvar exportsBinding;\nfunction init(instance) { exportsBinding = instance.exports;",
    );
    if fresh {
        imports.push_str(" exportsBinding.__wbindgen_start();");
    }
    imports.push_str(" return exportsBinding; }\nfunction tQ() { var imports = {wbg: {}};\n");
    if fresh {
        imports.push_str("imports.wbg.length = function(value) { return value.length; };\n");
    }
    imports.push_str(
        "imports.wbg.__wbindgen_memory = function() { return exportsBinding.memory; };\n\
         imports.wbg.ctor = function(value) { return new host.Uint32Array(value); };\n\
         imports.wbg.set = function(receiver, source, offset) { receiver.set(source, offset >>> 0); };\n",
    );
    if fresh {
        imports.push_str(
            "imports.wbg.__wbindgen_init_externref_table = function() { var table, base; table = exportsBinding.__wbindgen_export_0; base = table.grow(4); table.set(0, void 0); table.set(base + 0, void 0); table.set(base + 1, null); table.set(base + 2, true); table.set(base + 3, false); };\n",
        );
    }
    imports.push_str(&format!(
        "return imports; }}\nfunction bA(A) {{ if (Uint8Array.fromBase64) return [Uint8Array.fromBase64(A).buffer, false]; for (var Q = atob(A), g = new Uint8Array(Q.length), E = 0; E < Q.length; E++) g[E] = Q.charCodeAt(E); return [g.buffer, false]; }}\nconst embedded = \"{encoded}\";\nvar bytes = bA(embedded)[0], imports = tQ();\nvar module = new host.WebAssembly.Module(bytes);\nvar instance = new host.WebAssembly.Instance(module, imports);\ninit(instance);\nvar input = new host.Uint32Array([11, 22]);\ninstance.exports.copy(input, 0);\n"
    ));
    imports
}

fn cleanup_input_js(wasm: &[u8]) -> String {
    let encoded = STANDARD.encode(wasm);
    format!(
        "var host = window;\nvar exportsBinding;\nfunction init(instance) {{ exportsBinding = instance.exports; exportsBinding.__wbindgen_start(); return exportsBinding; }}\nfunction tQ() {{ var imports = {{wbg: {{}}}}; imports.wbg.length = function(value) {{ return value.length; }}; imports.wbg.__wbindgen_memory = function() {{ return exportsBinding.memory; }}; imports.wbg.buffer = function(value) {{ return value.buffer; }}; imports.wbg.ctor = function(value) {{ return new host.Uint32Array(value); }}; imports.wbg.set = function(receiver, source, offset) {{ receiver.set(source, offset >>> 0); }}; imports.wbg.__wbindgen_init_externref_table = function() {{ var table, base; table = exportsBinding.__wbindgen_export_0; base = table.grow(4); table.set(0, void 0); table.set(base + 0, void 0); table.set(base + 1, null); table.set(base + 2, true); table.set(base + 3, false); }}; return imports; }}\nfunction bA(A) {{ if (Uint8Array.fromBase64) return [Uint8Array.fromBase64(A).buffer, false]; for (var Q = atob(A), g = new Uint8Array(Q.length), E = 0; E < Q.length; E++) g[E] = Q.charCodeAt(E); return [g.buffer, false]; }}\nconst embedded = \"{encoded}\";\nvar bytes = bA(embedded)[0], imports = tQ();\nvar module = new host.WebAssembly.Module(bytes);\nvar instance = new host.WebAssembly.Instance(module, imports);\ninit(instance);\nvar input = new host.Uint32Array([11, 22]);\ninstance.exports.copy(input, 0);\n"
    )
}

fn only_copied_input(boundary: &Value) -> Result<&Value> {
    let rows = boundary["copied_input_rows"]
        .as_array()
        .context("copied_input_rows missing")?;
    anyhow::ensure!(rows.len() == 1, "expected one copied-input row");
    Ok(&rows[0])
}

#[test]
fn wasm_capture_deduplicates_origins_and_correlates_host_effects() -> Result<()> {
    let workspace = tempfile::tempdir()?;
    let har = workspace.path().join("fixture.har");
    let project = workspace.path().join("project");
    let wasm = decode_hex(HOST_EFFECT_WASM_HEX)?;
    let wasm_b64 = STANDARD.encode(&wasm);
    let js = format!(
        "var host = window;\nvar imports = {{wbg: {{}}}};\nimports.wbg.__wbg_signal_fixture = function(memory, base, offset) {{ var view = new host.DataView(memory.buffer), address = base + offset; offset === 56708 || view.setUint32(address, 1, false); }};\nfunction bA(A) {{ if (Uint8Array.fromBase64) return [Uint8Array.fromBase64(A).buffer, false]; for (var Q = atob(A), g = new Uint8Array(Q.length), E = 0; E < Q.length; E++) g[E] = Q.charCodeAt(E); return [g.buffer, false]; }}\nconst embedded = \"{wasm_b64}\";\nvar bytes = bA(embedded)[0];\nhost.WebAssembly.instantiate(bytes, imports);\n"
    );
    let split = wasm.len() / 2;
    let split_js = format!(
        "function loadSplit() {{ const left = atob(\"{}\"); const right = atob(\"{}\"); const output = new Uint8Array({}); function copy(chunk, offset) {{ for (let i = 0; i < chunk.length; i++) output[offset + i] = chunk.charCodeAt(i); }} copy(left, 0); copy(right, {}); return new WebAssembly.Module(output); }}\n",
        STANDARD.encode(&wasm[..split]),
        STANDARD.encode(&wasm[split..]),
        wasm.len(),
        split,
    );
    write_har(
        &har,
        "wasm capture regression",
        vec![
            har_entry(
                "https://fixture.invalid/index.html",
                "text/html",
                "<!doctype html><script src=\"https://fixture.invalid/fixture.js\"></script>",
                None,
            ),
            har_entry(
                "https://fixture.invalid/fixture.js",
                "application/javascript",
                &js,
                None,
            ),
            har_entry(
                "https://fixture.invalid/split.js",
                "application/javascript",
                &split_js,
                None,
            ),
            har_entry(
                "https://fixture.invalid/module.wasm",
                "application/wasm",
                &wasm_b64,
                Some("base64"),
            ),
        ],
    )?;
    let boundary = run_wasm_boundary_pipeline(&har, &project)?;

    let manifest = read_json(&project.join("capture-manifest.json"))?;
    let wasm_resource = manifest["resources"]
        .as_array()
        .context("resources missing")?
        .iter()
        .find(|row| row["kind"] == "wasm")
        .context("WASM resource missing")?;
    let wasm_path = project.join(
        wasm_resource["output_path"]
            .as_str()
            .context("WASM output missing")?,
    );
    assert_eq!(fs::read(wasm_path)?, wasm);

    let index = read_json(&project.join("analysis/wasm/index.json"))?;
    assert_eq!(index["summary"]["modules"], 1);
    assert_eq!(index["summary"]["direct_resources"], 1);
    assert_eq!(index["summary"]["inline_extracted"], 1);
    assert_eq!(index["summary"]["origins"], 3);
    let module = &index["modules"][0];
    let recovery_kinds = module["origins"]
        .as_array()
        .context("origins missing")?
        .iter()
        .filter_map(|origin| origin["recovery_kind"].as_str())
        .collect::<BTreeSet<_>>();
    assert_eq!(
        recovery_kinds,
        BTreeSet::from([
            "proven_static_byte_assembly",
            "validated_static_wasm_carrier"
        ])
    );

    assert_eq!(boundary["summary"]["host_effect_pairs"], 2);
    assert_eq!(boundary["summary"]["proven_js_set_u32_shapes"], 1);
    assert_eq!(
        boundary["summary"]["proven_js_import_object_instantiation_sites"],
        2
    );
    assert_eq!(
        boundary["summary"]["proven_host_import_binding_identities"],
        2
    );
    let rows = boundary["host_effect_rows"]
        .as_array()
        .context("host rows missing")?;
    let row_3536 = rows
        .iter()
        .find(|row| row["offset"] == 3536)
        .context("3536 row missing")?;
    let row_56708 = rows
        .iter()
        .find(|row| row["offset"] == 56708)
        .context("56708 row missing")?;
    assert_eq!(row_3536["js_set_u32_shape_proven"], true);
    assert_eq!(row_56708["js_set_u32_shape_proven"], false);
    assert!(rows.iter().all(
        |row| row["js_import_object_instantiation_site_proven"] == true
            && row["import_binding_identity_proven"] == true
    ));

    build_source_graph(&project)?;
    let graph = read_json(&project.join("analysis/source-graph.json"))?;
    let wasm_node = graph["nodes"]
        .as_array()
        .context("graph nodes missing")?
        .iter()
        .find(|node| node["type"] == "wasm_module")
        .context("WASM graph node missing")?;
    let edge_kinds = graph["edges"]
        .as_array()
        .context("graph edges missing")?
        .iter()
        .filter(|edge| edge["to"] == wasm_node["id"])
        .filter_map(|edge| edge["kind"].as_str())
        .collect::<BTreeSet<_>>();
    assert_eq!(
        edge_kinds,
        BTreeSet::from(["wasm_inline_base64", "wasm_resource", "wasm_static_bytes"])
    );
    Ok(())
}

#[test]
fn copied_input_boundary_preserves_exact_cross_language_proofs() -> Result<()> {
    let workspace = tempfile::tempdir()?;

    let copied_wasm = decode_hex(COPIED_WASM_HEX)?;
    let copied_har = workspace.path().join("copied.har");
    let copied_project = workspace.path().join("copied-project");
    write_inline_wasm_har(
        &copied_har,
        "copied input",
        &copied_input_js(&copied_wasm, false),
    )?;
    let copied = run_wasm_boundary_pipeline(&copied_har, &copied_project)?;
    assert_eq!(copied["summary"]["copied_input_candidates"], 1);
    assert_eq!(copied["summary"]["proven_js_typed_array_copy_semantics"], 1);
    assert_eq!(
        copied["summary"]["proven_copied_input_binding_identities"],
        1
    );
    assert_eq!(copied["summary"]["proven_module_memory_identities"], 1);
    assert_eq!(copied["summary"]["proven_destination_base_alignments"], 1);
    assert_eq!(
        copied["summary"]["proven_source_word_return_dependencies"],
        1
    );
    let row = only_copied_input(&copied)?;
    assert_eq!(row["destination_base_alignment_basis"], "static_ssa");
    assert_eq!(row["destination_byte_integrity_proven"], true);
    assert_eq!(row["destination_load_interpretation_proven"], true);
    assert_eq!(row["source_word_semantic_overlay_proven"], true);
    assert_eq!(row["runtime_dependency_graph_proven"], true);
    assert_eq!(row["source_word_return_dependencies_proven"], true);
    assert_eq!(row["source_uint32_array_length_lower_bound"], 2);
    let returns = row["source_word_returns"]
        .as_array()
        .context("source-word returns missing")?;
    anyhow::ensure!(returns.len() == 1, "expected one source-word return");
    let expression = returns[0]["source_word_expression"]
        .as_str()
        .context("source-word expression missing")?;
    assert!(expression.contains("source_u32(arg0, 0)"));
    assert!(expression.contains("source_u32(arg0, 1)"));

    let fresh_wasm = decode_hex(FRESH_WASM_HEX)?;
    let fresh_har = workspace.path().join("fresh.har");
    let fresh_project = workspace.path().join("fresh-project");
    write_inline_wasm_har(
        &fresh_har,
        "fresh alignment",
        &copied_input_js(&fresh_wasm, true),
    )?;
    let fresh = run_wasm_boundary_pipeline(&fresh_har, &fresh_project)?;
    let fresh_row = only_copied_input(&fresh)?;
    assert_eq!(fresh_row["static_destination_base_alignment_proven"], false);
    assert_eq!(fresh_row["destination_base_alignment_proven"], true);
    assert_eq!(
        fresh_row["destination_base_alignment_basis"],
        "fresh_exact_evaluation"
    );
    assert_eq!(fresh_row["destination_byte_integrity_proven"], true);
    assert_eq!(fresh_row["source_word_return_dependencies_proven"], true);
    let fresh_proof = &fresh_row["fresh_destination_base_alignment_proof"];
    assert_eq!(fresh_proof["source_uint32_array_length"], 2);
    assert_eq!(fresh_proof["allocator_byte_count"], 8);
    assert_eq!(fresh_proof["evaluated_destination_base"], 16);
    assert_eq!(
        fresh_proof["evaluated_destination_base_trailing_zero_bits"],
        4
    );
    assert_eq!(fresh_proof["fresh_evaluation"]["outcome"], "returned");

    for (name, hex, expect_disjoint) in [
        ("cleanup", CLEANUP_WASM_HEX, true),
        ("cleanup-overlap", CLEANUP_OVERLAP_WASM_HEX, false),
    ] {
        let wasm = decode_hex(hex)?;
        let har = workspace.path().join(format!("{name}.har"));
        let project = workspace.path().join(format!("{name}-project"));
        write_inline_wasm_har(&har, name, &cleanup_input_js(&wasm))?;
        let boundary = run_wasm_boundary_pipeline(&har, &project)?;
        let row = only_copied_input(&boundary)?;
        assert_eq!(row["destination_base_alignment_proven"], true);
        if expect_disjoint {
            assert_eq!(row["destination_byte_integrity_proven"], true);
            assert_eq!(row["destination_load_interpretation_proven"], true);
            assert_eq!(row["source_word_return_dependencies_proven"], true);
            let proof = &row["fresh_cleanup_disjointness_proof"];
            assert_eq!(proof["protected_memory"], 0);
            assert_eq!(proof["protected_range_start"], 16);
            assert_eq!(proof["protected_range_end"], 24);
            assert_eq!(proof["post_copy_accesses_disjoint_from_copied_range"], true);
        } else {
            assert!(row["fresh_cleanup_disjointness_proof"].is_null());
            assert_eq!(row["destination_byte_integrity_proven"], false);
            assert_eq!(row["destination_load_interpretation_proven"], false);
            assert_eq!(row["source_word_semantic_overlay_proven"], false);
            assert_eq!(row["source_word_return_dependencies_proven"], false);
            assert_eq!(row["source_word_returns"], json!([]));
        }
    }
    Ok(())
}
