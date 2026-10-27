#!/usr/bin/env python3
"""Verify the example and build the offline explainer and editable SVG figures."""

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile
from xml.etree import ElementTree as ET

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
TEAL = "#007C91"
ORANGE = "#C66B32"
INK = "#20272B"
GREY = "#68747B"
SVG = "http://www.w3.org/2000/svg"
ET.register_namespace("", SVG)

LABELS = {
    "en": {
        "title": "Proof as a search over mathematical knowledge",
        "a": "Mathematical context", "asub": "A goal and the knowledge available to it",
        "b": "Staged verification", "bsub": "Non-equality atomic search, after dispatch",
        "c": "Composed proof evidence", "csub": "The selected rule and its checked premise",
        "goal": "Goal", "established": "Established knowledge", "scope": "Current visible scope Γ",
        "from": "from: have x R", "real-number": "x is a real number", "definitions": "definitions and equalities",
        "memberships": "memberships and object properties", "sources": "fact identities and source references",
        "read": "Read visible facts; keep their sources.", "reuse": "Reuse checked knowledge in later statements.",
        "shape": "Classify the fact", "wd": "Check well-definedness", "wdsub": "objects · signature · domains",
        "truth": "Truth search: try allowed routes in order", "direct": "Direct evidence",
        "known": "Known facts / special properties", "builtin": "Builtin rule", "strategy": "Strategy",
        "definition": "Definition", "forall": "Known forall", "rewrite": "Rewrite (final fallback)",
        "miss": "No proof found", "misssub": "all allowed routes miss", "proof": "Return proof evidence",
        "square": "Even real powers are nonnegative", "real": "Required premise", "add": "Real addition is closed",
        "lookup": "Context citation", "calculate": "Exact calculation", "and": "AND: both premises are required",
        "permission": "Premises inherit restricted search permissions.",
        "accepted": "Verified fact", "store": "Store", "infer": "Direct inference, once", "updated": "Updated context",
        "request": "required condition", "evidence": "returned evidence", "rule": "mathematical rule",
        "boundary": "Search order and proof-dependency depth are separate dimensions.",
    },
    "zh": {
        "title": "证明：在数学知识中搜索证据",
        "a": "数学上下文", "asub": "待验证的目标，以及当前可用的知识",
        "b": "分层验证", "bsub": "逻辑形状分派后的非等式原子事实搜索",
        "c": "组合证明证据", "csub": "选中的规则，以及已检查的规则前提",
        "goal": "目标", "established": "已建立的数学知识", "scope": "当前可见作用域 Γ",
        "from": "来源：have x R", "real-number": "x 是一个实数", "definitions": "定义与等式关系",
        "memberships": "成员关系与对象属性", "sources": "事实标识与来源引用",
        "read": "读取可见事实，保留其来源。", "reuse": "已验证知识可以用于后续陈述。",
        "shape": "识别事实形状", "wd": "检查良定义性", "wdsub": "对象 · 谓词签名 · 适用域",
        "truth": "证明搜索：按顺序尝试允许的入口", "direct": "直接证据 Direct",
        "known": "已知事实匹配 / 对象属性", "builtin": "内置规则 Builtin rule", "strategy": "策略 Strategy",
        "definition": "定义 Definition", "forall": "已知全称事实", "rewrite": "改写：最后尝试",
        "miss": "未找到证明", "misssub": "允许的入口均未命中", "proof": "返回证明证据",
        "square": "实数的偶次幂非负", "real": "需要检查的前提", "add": "实数加法封闭",
        "lookup": "引用上下文", "calculate": "精确计算", "and": "AND：两个前提都必须成立",
        "permission": "前提检查继承受限的搜索权限。",
        "accepted": "已验证事实", "store": "存储", "infer": "直接推导一次", "updated": "更新上下文",
        "request": "需要的条件", "evidence": "返回的证据", "rule": "数学规则",
        "boundary": "搜索入口的顺序与证明依赖的深度，是两个维度。",
    },
}

STYLE = f"""
.proof-figure {{ font-family: Arial, Helvetica, 'PingFang SC', 'Microsoft YaHei', sans-serif; background: #fff; }}
.proof-figure text {{ fill: {INK}; font-size: 15px; font-weight: 400; }}
.proof-figure .small {{ font-size: 13px; fill: {GREY}; }}
.proof-figure .heading {{ font-size: 16px; font-weight: 600; }}
.proof-figure .panel-letter {{ font-size: 18.5px; font-weight: 700; }}
.proof-figure .math {{ font-size: 16.2px; }}
.proof-figure .code {{ font-family: 'Courier New', monospace; font-size: 13px; }}
.proof-figure .shape {{ stroke: #A9B4B9; stroke-width: 1; fill: #fff; }}
.proof-figure .fact .shape {{ fill: #F0F7F8; stroke: #8BB9C0; }}
.proof-figure .rule .shape {{ fill: #FCF4ED; stroke: #D7A581; }}
.proof-figure .selected-rule .shape {{ stroke: {ORANGE}; stroke-width: 1.7; }}
.proof-figure .edge {{ fill: none; stroke: #8B969C; stroke-width: 1; }}
.proof-figure .request {{ stroke-dasharray: 3.5 3.5; }}
.proof-figure .evidence {{ stroke: {TEAL}; stroke-width: 1.3; }}
.proof-figure .selected-edge {{ stroke: {ORANGE}; stroke-width: 1.5; }}
.proof-figure .guide {{ fill: none; stroke: #CBD2D5; stroke-width: .8; }}
"""


def element(parent, tag, **attrs):
    return ET.SubElement(parent, f"{{{SVG}}}{tag}", {key.replace("_", "-"): str(value) for key, value in attrs.items()})


def text(parent, value, x, y, cls="", anchor="middle"):
    node = element(parent, "text", x=x, y=y, text_anchor=anchor, dominant_baseline="middle", **{"class": cls})
    node.text = value
    return node


def path(parent, d, cls="edge", marker=None):
    attrs = {"d": d, "class": cls}
    if marker:
        attrs["marker-end"] = f"url(#{marker})"
    return element(parent, "path", **attrs)


def node(parent, key, label, x, y, width, kind="", shape="rect", step="", sub=None):
    group = element(parent, "g", data_node=key, data_steps=step, **{"class": f"node {kind}".strip()})
    element(group, "title").text = label
    left, right = x - width / 2, x + width / 2
    if shape == "rule":
        element(group, "polygon", points=f"{left},{y} {left+12},{y-21} {right-12},{y-21} {right},{y} {right-12},{y+21} {left+12},{y+21}", **{"class": "shape"})
    elif shape == "db":
        path(group, f"M {left} {y-15} C {left} {y-34}, {right} {y-34}, {right} {y-15} V {y+14} C {right} {y+33}, {left} {y+33}, {left} {y+14} Z", "shape")
        path(group, f"M {left} {y-15} C {left} {y+3}, {right} {y+3}, {right} {y-15}", "guide")
        text(group, label, x, y + 8)
        return group
    else:
        element(group, "rect", x=left, y=y-23, width=width, height=46, rx=2, **{"class": "shape"})
    text(group, label, x, y-7 if sub else y, "math" if key in {"goal", "result", "real", "x", "one"} else "")
    if sub:
        text(group, sub, x, y+11, "small")
    return group


def marker_defs(svg, prefix):
    defs = element(svg, "defs")
    for name, color in [("grey", "#8B969C"), ("teal", TEAL), ("orange", ORANGE)]:
        marker = element(defs, "marker", id=f"{prefix}-{name}", viewBox="0 0 8 8", refX=7, refY=4, markerWidth=5, markerHeight=5, orient="auto")
        element(marker, "path", d="M 1 1 L 7 4 L 1 7", fill="none", stroke=color, stroke_width=1.2)


def panel_header(parent, letter, title, subtitle):
    text(parent, letter, 0, 26, "panel-letter", "start")
    text(parent, title, 28, 26, "heading", "start")
    text(parent, subtitle, 0, 57, "small", "start")


def panel_a(parent, labels, prefix):
    panel_header(parent, "a", labels["a"], labels["asub"])
    text(parent, labels["goal"], 188, 88, "small")
    node(parent, "goal", "0 ≤ (x + 1)²", 188, 127, 314, "fact", step="0")
    text(parent, "0 <= (x + 1)^2", 188, 175, "code")
    text(parent, labels["established"], 188, 240, "heading")
    group = element(parent, "g", data_node="context", data_steps="0 4 5", **{"class": "node fact"})
    path(group, "M 28 294 C 28 260, 348 260, 348 294 V 490 C 348 524, 28 524, 28 490 Z", "shape")
    path(group, "M 28 294 C 28 328, 348 328, 348 294", "guide")
    text(group, labels["scope"], 188, 294)
    fact = element(parent, "g", data_node="context-fact", data_steps="0 4", **{"class": "node fact"})
    element(fact, "rect", x=48, y=333, width=280, height=67, rx=0, **{"class": "shape"})
    text(fact, "x ∈ ℝ", 188, 347, "math")
    text(fact, labels["from"], 188, 368, "code")
    text(fact, labels["real-number"], 188, 389, "small")
    text(group, labels["definitions"], 188, 426)
    text(group, labels["memberships"], 188, 457)
    text(group, labels["sources"], 188, 488)
    text(parent, labels["read"], 188, 564, "small")
    text(parent, labels["reuse"], 188, 591, "small")
    path(parent, "M 188 654 H 355 V 529 H 188 V 519", "edge evidence", f"{prefix}-teal")


def panel_b(parent, labels, prefix):
    panel_header(parent, "b", labels["b"], labels["bsub"])
    node(parent, "shape", labels["shape"], 171, 107, 280, step="0")
    path(parent, "M 171 131 V 148", marker=f"{prefix}-grey")
    node(parent, "wd", labels["wd"], 171, 174, 280, step="1", sub=labels["wdsub"])
    path(parent, "M 171 198 V 220", marker=f"{prefix}-grey")
    text(parent, labels["truth"], 171, 242, "small")
    stages = ["direct", "known", "builtin", "strategy", "definition", "forall", "rewrite"]
    for i, key in enumerate(stages):
        y = 282 + i * 40
        group = element(parent, "g", data_node=key, data_steps="2" if key == "builtin" else "", **{"class": "node rule selected-rule" if key == "builtin" else "node"})
        element(group, "rect", x=31, y=y-16, width=280, height=32, rx=0, **{"class": "shape"})
        text(group, labels[key], 171, y)
        if i < len(stages)-1:
            path(parent, f"M 171 {y+16} V {y+23}", marker=f"{prefix}-grey")
        cls, color = ("edge selected-edge", "orange") if key == "builtin" else ("guide", "grey")
        path(parent, f"M 311 {y} H 352", cls, f"{prefix}-{color}")
    path(parent, "M 352 282 V 626 H 314", "edge evidence", f"{prefix}-teal")
    path(parent, "M 352 362 V 626 H 314", "edge selected-edge", f"{prefix}-orange")
    path(parent, "M 171 539 V 557", marker=f"{prefix}-grey")
    text(parent, labels["miss"], 171, 572)
    text(parent, labels["misssub"], 171, 590, "small")
    node(parent, "proof", labels["proof"], 171, 626, 280, "fact", step="5")
    text(parent, labels["permission"], 171, 664, "small")


def proof_edge(parent, x1, y1, x2, y2, prefix):
    middle = (y1 + y2) / 2
    path(parent, f"M {x1-5} {y1} C {x1-5} {middle}, {x2-5} {middle}, {x2-5} {y2}", "edge request", f"{prefix}-grey")
    path(parent, f"M {x2+5} {y2} C {x2+5} {middle}, {x1+5} {middle}, {x1+5} {y1}", "edge evidence", f"{prefix}-teal")


def panel_c(parent, labels, prefix):
    panel_header(parent, "c", labels["c"], labels["csub"])
    edges = [(188,130,188,169), (188,211,188,251), (188,297,188,337),
             (188,379,88,428), (188,379,288,428), (88,475,88,524), (288,475,288,524)]
    for edge in edges:
        proof_edge(parent, *edge, prefix)
    node(parent, "result", "0 ≤ (x + 1)²", 188, 107, 244, "fact", step="5")
    node(parent, "square", labels["square"], 188, 190, 340, "rule", "rule", "2 5")
    node(parent, "real", "x + 1 ∈ ℝ", 188, 274, 270, "fact", step="2 3 5")
    node(parent, "add", labels["add"], 188, 358, 294, "rule", "rule", "3 5")
    node(parent, "x", "x ∈ ℝ", 88, 451, 156, "fact", step="3 4 5")
    node(parent, "one", "1 ∈ ℝ", 288, 451, 156, "fact", step="3 4 5")
    node(parent, "lookup", labels["lookup"], 88, 549, 158, "fact", "db", "4")
    node(parent, "calculation", labels["calculate"], 288, 549, 158, step="4")
    text(parent, labels["and"], 188, 611, "small")
    text(parent, "Builtin rule → Direct → context / calculation" if labels is LABELS["en"] else "内置规则 → Direct 结构检查 → 上下文 / 计算", 188, 643, "small")


def footer(parent, labels, prefix, vertical=False):
    if vertical:
        for i, key in enumerate(["accepted", "store", "infer", "updated"]):
            y = 30+i*65
            node(parent, "commit", labels[key], 188, y, 280, "fact" if key in {"updated", "accepted"} else "", step="5")
            if i < 3:
                path(parent, f"M 188 {y+24} V {y+40}", "edge evidence", f"{prefix}-teal")
        return
    path(parent, "M 0 0 H 1152", "guide")
    for key, x in [("updated", 140), ("infer", 430), ("store", 710), ("accepted", 996)]:
        node(parent, "commit", labels[key], x, 39, 218, "fact" if key in {"updated", "accepted"} else "", step="5")
    for right, left in [(887,819), (601,539), (321,249)]:
        path(parent, f"M {right} 39 H {left}", "edge evidence", f"{prefix}-teal")
    path(parent, "M 60 91 H 104", "edge request", f"{prefix}-grey")
    text(parent, labels["request"], 113, 91, "small", "start")
    path(parent, "M 380 91 H 424", "edge evidence", f"{prefix}-teal")
    text(parent, labels["evidence"], 433, 91, "small", "start")
    element(parent, "polygon", points="716,91 724,84 732,91 724,98", fill="#FCF4ED", stroke=ORANGE, stroke_width=1)
    text(parent, labels["rule"], 741, 91, "small", "start")


def make_svg(lang, panel=None):
    labels = LABELS[lang]
    width, height = (376, 684) if panel in ("a", "b", "c") else (1152, 108) if panel == "footer" else (376, 260) if panel == "footer-mobile" else (1200, 824)
    prefix = f"ps-{lang}-{panel or 'figure'}"
    attrs = {"viewBox": f"0 0 {width} {height}", "class": "proof-figure", "role": "img", "aria-labelledby": prefix+"-title"}
    if panel is None:
        attrs.update(width="183mm", height="125.66mm")
    svg = ET.Element(f"{{{SVG}}}svg", attrs)
    element(svg, "title", id=prefix+"-title").text = labels["title"]
    element(svg, "desc").text = "A verified example connects scoped context, ordered verification and the composition of rule evidence. The diagram is a curated teaching projection, not a log of failed search candidates."
    element(svg, "style").text = STYLE
    marker_defs(svg, prefix)
    element(svg, "rect", x=0, y=0, width=width, height=height, fill="#FFFFFF")
    functions = {"a": panel_a, "b": panel_b, "c": panel_c, "footer": footer,
                 "footer-mobile": lambda parent, labels, prefix: footer(parent, labels, prefix, vertical=True)}
    if panel:
        functions[panel](svg, labels, prefix)
    else:
        for key, x in [("a",24),("b",412),("c",800)]:
            group = element(svg, "g", transform=f"translate({x} 0)")
            functions[key](group, labels, prefix)
        group = element(svg, "g", transform="translate(24 706)")
        footer(group, labels, prefix)
        path(svg, "M 164 722 V 688 H 212 V 654", "edge evidence")
    return ET.tostring(svg, encoding="unicode")


def checked_evidence(binary, evidence_dir):
    commands = {
        "normal": [str(binary), "-lang", "en", "-strict", "-f", str(HERE / "demo.lit")],
        "reading": [str(binary), "-reading", "-json", "-lang", "en", "-strict", "-f", str(HERE / "demo.lit")],
    }
    results = {}
    for kind, command in commands.items():
        result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True, timeout=60)
        (evidence_dir / f"{kind}.json").write_text(result.stdout)
        data = json.loads(result.stdout)
        if result.returncode or data.get("run_result") != "success":
            raise ValueError(f"{kind} gate failed: {result.stderr} {result.stdout[:1500]}")
        results[kind] = data
    normal, reading = results["normal"], results["reading"]
    if normal.get("session_terminated") or normal.get("termination") is not None:
        raise ValueError("Tracer did not finish normally")
    if reading["trust_summary"]["user_assumptions"] or reading["trust_summary"]["axioms"]:
        raise ValueError("The figure example must remain strict")
    nodes = {entry["id"]: entry["node"] for entry in reading["evidence_nodes"]}
    deref = lambda value: nodes[value["evidence_id"]]
    powers = [node for node in nodes.values() if node["type"] == "EvenPowNonnegativeBuiltinRuleProof"]
    if len(powers) != 1:
        raise ValueError("Expected one selected even-power rule")
    base = deref(powers[0]["fields"]["base_in_real_proof"])
    while base["type"] != "VerifyAtomicExceptEqualityFactSuccess":
        base = deref(base["fields"]["0"])
    searched = deref(base["fields"]["searched_proof"])
    if searched["variant"] != "ByStructuralMembership":
        raise ValueError("The displayed real-base premise no longer uses structural membership")
    structure = deref(searched["fields"]["0"])
    addition = deref(structure["fields"]["reason"])
    if addition["variant"] != "Add":
        raise ValueError("Expected structural addition")
    reasons = [deref(deref(addition["fields"][key])["fields"]["reason"]) for key in ("left", "right")]
    if [reason["variant"] for reason in reasons] != ["Known", "Closed"]:
        raise ValueError("Expected a known left operand and closed right operand")
    citation = deref(reasons[0]["fields"]["0"])["fields"]["cite_fact_id"]["fact_id"]
    declared = reading["statements"][0]["produced_fact_ids"]
    target = reading["statements"][1]
    if citation not in declared or citation not in target["cited_fact_ids"]:
        raise ValueError("The premise must cite the actual have declaration")
    return {
        "engine": reading["engine"], "run_result": "success", "strict": True,
        "example_sha256": hashlib.sha256((HERE / "demo.lit").read_bytes()).hexdigest(),
        "source": "demo.lit", "target": target["text"], "context_fact_id": citation,
        "rule_ids": target["rule_ids"],
        "selected_premise": {"search": "ByStructuralMembership", "constructor": "Add", "left": "Known", "right": "Closed"},
        "boundary": "Curated successful proof projection; pipeline routes are source-audited, not a failed-candidate timeline.",
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binary", type=Path, default=ROOT / "target/release/litex")
    parser.add_argument("--evidence-dir", type=Path)
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix="litex-proof-figure-") as temporary:
        evidence_dir = args.evidence_dir.resolve() if args.evidence_dir else Path(temporary)
        evidence_dir.mkdir(parents=True, exist_ok=True)
        acceptance = checked_evidence(args.binary.resolve(), evidence_dir)
    figures = {}
    for lang in LABELS:
        suffix = "" if lang == "en" else ".zh"
        (HERE / f"proof-search{suffix}.svg").write_text(make_svg(lang) + "\n")
        figures[lang] = '<div class="figure-panels">' + "".join(f'<div class="figure-panel">{make_svg(lang, panel)}</div>' for panel in "abc") + '</div>' + f'<div class="figure-footer">{make_svg(lang, "footer")}</div><div class="figure-footer-mobile">{make_svg(lang, "footer-mobile")}</div>'
    template = (HERE / "index.template.html").read_text()
    for lang, markup in figures.items():
        template = template.replace(f"<!-- FIGURE_{lang.upper()} -->", markup)
    template = template.replace("<!-- EVIDENCE -->", json.dumps(acceptance, ensure_ascii=False).replace("<", "\\u003c"))
    (HERE / "index.html").write_text(template)
    acceptance["assets"] = {name: hashlib.sha256((HERE / name).read_bytes()).hexdigest() for name in ["proof-search.svg", "proof-search.zh.svg", "index.html", "viewer.js", "style.css", "build.py", "index.template.html", "export.cjs", "README.md"]}
    (HERE / "acceptance.json").write_text(json.dumps(acceptance, ensure_ascii=False, indent=2) + "\n")
    print("Verified demo; generated English/Chinese SVG and offline interactive figure.")


if __name__ == "__main__":
    main()
