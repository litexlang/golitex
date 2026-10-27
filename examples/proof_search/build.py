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
        "title": "Definitions build context; proofs use it",
        "part-definition": "I  Definitions: build context", "part-proof": "II  Proofs: use established context",
        "a": "Introduce a real object", "asub": "The declaration itself is checked",
        "b": "Search for a proof", "bsub": "Check a new fact in the established context",
        "c": "Composed proof evidence", "csub": "The selected rule and its checked premise",
        "goal": "Goal", "established": "Established knowledge", "scope": "Current visible scope Γ",
        "from": "from: have x R", "real-number": "x is a real number", "definitions": "definitions and equalities",
        "carrier": "Check the carrier R", "carrier-sub": "R is well-defined",
        "nonempty": "Check that R is nonempty", "nonempty-sub": "StandardSetNonempty builtin",
        "register": "Register x and its declaration", "register-sub": "record the membership x ∈ ℝ",
        "context-record": "declaration · membership · source",
        "definition-note": "Declaration checks can invoke proof rules.",
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
        "title": "定义建立上下文，证明使用上下文",
        "part-definition": "I  定义：建立数学上下文", "part-proof": "II  证明：使用已有数学上下文",
        "a": "引入一个实数对象", "asub": "声明本身也要经过检查",
        "b": "搜索事实的证明", "bsub": "在已建立的上下文中验证新事实",
        "c": "组合证明证据", "csub": "选中的规则，以及已检查的规则前提",
        "goal": "目标", "established": "已建立的数学知识", "scope": "当前可见作用域 Γ",
        "from": "来源：have x R", "real-number": "x 是一个实数", "definitions": "定义与等式关系",
        "carrier": "检查集合 R", "carrier-sub": "R 是合法的集合对象",
        "nonempty": "检查 R 非空", "nonempty-sub": "内置规则 StandardSetNonempty",
        "register": "登记名称 x 与它的声明", "register-sub": "记录成员关系 x ∈ ℝ",
        "context-record": "声明 · 成员关系 · 来源",
        "definition-note": "定义/声明的检查，也会使用证明规则。",
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
    cls = "code" if key == "declaration" else "math" if key in {"goal", "result", "real", "x", "one"} else ""
    text(group, label, x, y-7 if sub else y, cls)
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
    node(parent, "declaration", "have x R", 188, 108, 314, "fact", step="0")
    text(parent, labels["real-number"], 188, 148, "small")
    node(parent, "carrier", labels["carrier"], 188, 205, 314, step="1", sub=labels["carrier-sub"])
    node(parent, "nonempty", labels["nonempty"], 188, 285, 314, "rule", step="1", sub=labels["nonempty-sub"])
    node(parent, "register", labels["register"], 188, 365, 314, step="2", sub=labels["register-sub"])
    for start, end in [(158,180),(229,260),(309,340),(389,421)]:
        path(parent, f"M 188 {start} V {end}", marker=f"{prefix}-grey")
    group = element(parent, "g", data_node="context", data_steps="2 7 8", **{"class": "node fact"})
    path(group, "M 28 450 C 28 423, 348 423, 348 450 V 596 C 348 623, 28 623, 28 596 Z", "shape")
    path(group, "M 28 450 C 28 477, 348 477, 348 450", "guide")
    text(group, labels["scope"], 188, 450)
    fact = element(parent, "g", data_node="context-fact", data_steps="2 7", **{"class": "node fact"})
    element(fact, "rect", x=48, y=480, width=280, height=85, rx=0, **{"class": "shape"})
    text(fact, "x ∈ ℝ", 188, 499, "math")
    text(fact, labels["from"], 188, 522, "code")
    text(fact, labels["real-number"], 188, 546, "small")
    text(group, labels["context-record"], 188, 588, "small")
    text(parent, labels["definition-note"], 188, 665, "small")
    path(parent, "M 355 654 V 624 H 188 V 620", "edge evidence", f"{prefix}-teal")


def panel_b(parent, labels, prefix):
    panel_header(parent, "b", labels["b"], labels["bsub"])
    node(parent, "goal", "0 ≤ (x + 1)²", 171, 107, 280, step="3", sub=labels["shape"])
    path(parent, "M 171 131 V 148", marker=f"{prefix}-grey")
    node(parent, "wd", labels["wd"], 171, 174, 280, step="4", sub=labels["wdsub"])
    path(parent, "M 171 198 V 220", marker=f"{prefix}-grey")
    text(parent, labels["truth"], 171, 242, "small")
    stages = ["direct", "known", "builtin", "strategy", "definition", "forall", "rewrite"]
    for i, key in enumerate(stages):
        y = 282 + i * 40
        group = element(parent, "g", data_node=key, data_steps="5" if key == "builtin" else "", **{"class": "node rule selected-rule" if key == "builtin" else "node"})
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
    node(parent, "proof", labels["proof"], 171, 626, 280, "fact", step="8")
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
    node(parent, "result", "0 ≤ (x + 1)²", 188, 107, 244, "fact", step="8")
    node(parent, "square", labels["square"], 188, 190, 340, "rule", "rule", "5 8")
    node(parent, "real", "x + 1 ∈ ℝ", 188, 274, 270, "fact", step="5 6 8")
    node(parent, "add", labels["add"], 188, 358, 294, "rule", "rule", "6 8")
    node(parent, "x", "x ∈ ℝ", 88, 451, 156, "fact", step="6 7 8")
    node(parent, "one", "1 ∈ ℝ", 288, 451, 156, "fact", step="6 7 8")
    node(parent, "lookup", labels["lookup"], 88, 549, 158, "fact", "db", "7")
    node(parent, "calculation", labels["calculate"], 288, 549, 158, step="7")
    text(parent, labels["and"], 188, 611, "small")
    text(parent, "Builtin rule → Direct → context / calculation" if labels is LABELS["en"] else "内置规则 → Direct 结构检查 → 上下文 / 计算", 188, 643, "small")


def footer(parent, labels, prefix, vertical=False):
    if vertical:
        for i, key in enumerate(["accepted", "store", "infer", "updated"]):
            y = 30+i*65
            node(parent, "commit", labels[key], 188, y, 280, "fact" if key in {"updated", "accepted"} else "", step="8")
            if i < 3:
                path(parent, f"M 188 {y+24} V {y+40}", "edge evidence", f"{prefix}-teal")
        return
    path(parent, "M 0 0 H 1152", "guide")
    for key, x in [("updated", 140), ("infer", 430), ("store", 710), ("accepted", 996)]:
        node(parent, "commit", labels[key], x, 39, 218, "fact" if key in {"updated", "accepted"} else "", step="8")
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
    width, height = (376, 684) if panel in ("a", "b", "c") else (1152, 108) if panel == "footer" else (376, 260) if panel == "footer-mobile" else (1200, 898)
    prefix = f"ps-{lang}-{panel or 'figure'}"
    attrs = {"viewBox": f"0 0 {width} {height}", "class": "proof-figure", "role": "img", "aria-labelledby": prefix+"-title"}
    if panel is None:
        attrs.update(width="183mm", height="136.95mm")
    svg = ET.Element(f"{{{SVG}}}svg", attrs)
    element(svg, "title", id=prefix+"-title").text = labels["title"]
    element(svg, "desc").text = "Part I checks an object declaration and extends the mathematical context. Part II uses that context to verify a fact and compose its proof evidence. This is a curated teaching projection."
    element(svg, "style").text = STYLE
    marker_defs(svg, prefix)
    element(svg, "rect", x=0, y=0, width=width, height=height, fill="#FFFFFF")
    functions = {"a": panel_a, "b": panel_b, "c": panel_c, "footer": footer,
                 "footer-mobile": lambda parent, labels, prefix: footer(parent, labels, prefix, vertical=True)}
    if panel:
        functions[panel](svg, labels, prefix)
    else:
        text(svg, labels["part-definition"], 24, 27, "heading", "start")
        text(svg, labels["part-proof"], 412, 27, "heading", "start")
        path(svg, "M 24 51 H 392 M 412 51 H 1176", "guide")
        path(svg, "M 400 74 V 758", "guide")
        for key, x in [("a",24),("b",412),("c",800)]:
            group = element(svg, "g", transform=f"translate({x} 74)")
            functions[key](group, labels, prefix)
        group = element(svg, "g", transform="translate(24 780)")
        footer(group, labels, prefix)
        path(svg, "M 164 796 V 762 H 379 V 728", "edge evidence")
    return ET.tostring(svg, encoding="unicode")


def proof_guide(lang, citation):
    rows = {
        "en": [
            ("0 ≤ (x + 1)²", "Read the goal: zero on the left, a power on the right."),
            ("x + 1  ·  (x + 1)²", "Check object formation, predicate signature and domains first."),
            ("u ∈ ℝ  ⇒  0 ≤ u²", "Match u = x + 1 and the even exponent 2; require x + 1 ∈ ℝ."),
            ("x ∈ ℝ  AND  1 ∈ ℝ", "Direct addition structure reduces the real-base condition to both operands."),
            ("have x R  ·  1 ∈ ℝ", f"Cite {citation} for x; check the numeral 1 by exact closed calculation."),
            ("↑  0 ≤ (x + 1)²", "Both leaves succeed; combine their evidence back up the dependency tree."),
        ],
        "zh": [
            ("0 ≤ (x + 1)²", "从目标读取结构：左边是 0，右边是一个幂。"),
            ("x + 1  ·  (x + 1)²", "先检查对象、谓词签名和适用域。"),
            ("u ∈ ℝ  ⇒  0 ≤ u²", "匹配 u = x + 1、偶数指数 2；接着要求 x + 1 ∈ ℝ。"),
            ("x ∈ ℝ  AND  1 ∈ ℝ", "Direct 沿加法结构向下分解，两个操作数都要是实数。"),
            ("have x R  ·  1 ∈ ℝ", f"x 的成员关系引用 {citation}；数值 1 的成员关系由精确闭式计算确认。"),
            ("↑  0 ≤ (x + 1)²", "两条叶子都找到依据后，证据沿依赖树向上组合。"),
        ],
    }
    title = "How is this proof found?" if lang == "en" else "这个证明是怎么找到的？"
    subtitle = "Follow the goal down to smaller requirements" if lang == "en" else "从目标开始，向下找到更小的条件"
    replay = "Demonstrate from the goal" if lang == "en" else "从目标开始演示"
    parts = []
    for index, (formula, detail) in enumerate(rows[lang], start=3):
        # All text comes from maintained literals or the checked numeric citation.
        parts.append(
            f'<li><button type="button" data-route-step="{index}">'
            f'<span class="route-label"><span class="route-number">{index+1:02}</span><strong class="route-title"></strong></span>'
            f'<span class="route-formula">{formula}</span><span class="route-detail">{detail}</span>'
            '</button></li>'
        )
    return (
        f'<section class="proof-route-guide"><h3>{title}</h3><p class="route-subtitle">{subtitle}</p>'
        f'<button class="proof-replay" type="button">{replay} ↓</button>'
        '<ol class="proof-route">' + ''.join(parts) + '</ol></section>'
    )


def interactive_tree(lang):
    svg = ET.fromstring(make_svg(lang, "c"))
    svg.find(f"{{{SVG}}}text[@class='heading']").set("data-tree-title", "")
    svg.find(f"{{{SVG}}}text[@class='small']").set("data-tree-subtitle", "")
    edges = [child for child in svg if child.get("class", "").startswith("edge ")]
    for edge, stage in zip(edges, [stage for stage in [5, 5, 6, 6, 6, 7, 7] for _ in range(2)], strict=True):
        edge.set("data-edge-step", str(stage))
    return ET.tostring(svg, encoding="unicode")


def make_discovery_svg(lang, citation):
    """A standalone diagram of the checked dependency, without browser execution."""
    labels = {
        "en": [
            "Find the requirements downward; compose the evidence upward",
            "Example: have x R, then check 0 ≤ (x + 1)². Formation and domain checks precede truth search.",
            "1  Start with the goal", "2  Match the real even-power rule",
            "u = x + 1; the exponent 2 is even", "3  Ask for the rule's premise",
            "4  Follow the addition structure", "Both smaller memberships are required",
            "5a  Cite established context", f"have x R → x ∈ ℝ  ·  {citation}",
            "5b  Exact closed calculation", "The literal 1 belongs to ℝ",
            "AND: both leaves must succeed", "↑  Combine the leaf evidence back up",
            "x ∈ ℝ and 1 ∈ ℝ  ⇒  x + 1 ∈ ℝ  ⇒  0 ≤ (x + 1)²",
            "Selected route: EvenPowNonnegative → Direct / Add → Known + Closed.",
            "A curated successful dependency, not a log of every attempted search candidate.",
        ],
        "zh": [
            "向下找齐条件，再把证据向上组合",
            "例子：have x R，然后检查 0 ≤ (x + 1)²；对象与适用域先经过检查，再找真值证据。",
            "1  从待证目标出发", "2  匹配实数偶次幂非负规则",
            "u = x + 1；指数 2 是偶数", "3  提出规则需要的子目标",
            "4  沿加法结构继续向下分解", "两个操作数的实数成员关系都需要依据",
            "5a  引用已经建立的上下文", f"have x R → x ∈ ℝ  ·  {citation}",
            "5b  执行精确的闭式计算", "字面量 1 属于实数集 ℝ",
            "AND：两条叶子都必须成功", "↑  把叶子证据沿原路向上组合",
            "x ∈ ℝ 且 1 ∈ ℝ  ⇒  x + 1 ∈ ℝ  ⇒  0 ≤ (x + 1)²",
            "实际选中路径：EvenPowNonnegative → Direct / Add → Known + Closed。",
            "图中展开一条已验证的成功依赖，不是全部搜索候选的尝试日志。",
        ],
    }[lang]
    s = ET.Element(f"{{{SVG}}}svg", {"viewBox":"0 0 1200 950", "width":"183mm", "height":"144.875mm", "class":"proof-figure", "role":"img"})
    element(s, "title").text = labels[0]
    element(s, "style").text = STYLE + '.proof-figure .discovery-title{font-size:26px;font-weight:500}.proof-figure .discovery-math{font-size:23px}.proof-figure .discovery-note{font-size:15px;fill:#68747B}'
    element(s, "rect", width=1200, height=950, fill="white")
    marker_defs(s, f"discovery-{lang}")
    text(s, labels[0], 36, 38, "discovery-title", "start")
    text(s, labels[1], 36, 81, "discovery-note", "start")

    def card(x, y, w, h, kind, lines):
        g = element(s, "g", **{"class":kind})
        element(g, "rect", x=x, y=y, width=w, height=h, rx=3, **{"class":"shape"})
        for label, dy, cls in lines:
            text(g, label, x+w/2, y+dy, cls)

    card(300, 116, 600, 76, "fact", [(labels[2],20,"heading"),("0 ≤ (x + 1)²",51,"discovery-math")])
    card(250, 233, 700, 95, "rule", [(labels[3],21,"heading"),("u ∈ ℝ  ⇒  0 ≤ u²",51,"discovery-math"),(labels[4],78,"discovery-note")])
    card(300, 369, 600, 76, "fact", [(labels[5],20,"heading"),("x + 1 ∈ ℝ",51,"discovery-math")])
    card(250, 486, 700, 80, "rule", [(labels[6],24,"heading"),(labels[7],57,"discovery-note")])
    for start,end in [(192,233),(328,369),(445,486)]:
        path(s, f"M 600 {start+4} V {end-8}", "edge request", f"discovery-{lang}-grey")
    for x in [320,880]:
        path(s,f"M 600 570 V 593 H {x} V 620", "edge request", f"discovery-{lang}-grey")
    card(70, 628, 500, 106, "fact", [(labels[8],22,"heading"),("x ∈ ℝ",52,"discovery-math"),(labels[9],83,"discovery-note")])
    card(630, 628, 500, 106, "fact", [(labels[10],22,"heading"),("1 ∈ ℝ",52,"discovery-math"),(labels[11],83,"discovery-note")])
    text(s, labels[12], 600, 765, "discovery-note")
    card(70, 803, 1060, 94, "fact", [(labels[13],24,"heading"),(labels[14],60,"discovery-math")])
    text(s, labels[15], 36, 922, "small", "start")
    text(s, labels[16], 36, 943, "small", "start")
    return ET.tostring(s, encoding="unicode")


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
    declaration = reading["statements"][0]
    declared = declaration["produced_fact_ids"]
    target = reading["statements"][1]
    if citation not in declared or citation not in target["cited_fact_ids"]:
        raise ValueError("The premise must cite the actual have declaration")
    have_results = [node for node in nodes.values() if node["type"] == "ExecHaveObjInNonemptySetStmtSuccessResult"]
    if len(have_results) != 1 or len(have_results[0]["fields"]["groups"]) != 1:
        raise ValueError("Expected the actual successful single-group have declaration")
    group = deref(have_results[0]["fields"]["groups"][0])
    carrier = deref(group["fields"]["param_type_well_defined"])
    nonempty = deref(group["fields"]["nonempty_check"])
    defined = deref(group["fields"]["defined_params"])
    rule = "builtin.IsNonemptySetFactSearchProofByBuiltinRule::StandardSetNonempty"
    if carrier["variant"] != "Obj" or nonempty["variant"] != "Obj" or rule not in declaration["rule_ids"]:
        raise ValueError("Declaration must retain carrier WD and the checked nonempty-real-set rule")
    if citation not in [item["fact_id"] for item in defined["fields"]["stored_fact_ids"]]:
        raise ValueError("Declaration storage must own the membership used by the proof")
    if not declaration["statement_kind"].startswith("Definition.DefineObj.") or not declaration["declaration_symbol_ids"]:
        raise ValueError("Expected an object-definition declaration and a resolved symbol")
    return {
        "engine": reading["engine"], "run_result": "success", "strict": True,
        "example_sha256": hashlib.sha256((HERE / "demo.lit").read_bytes()).hexdigest(),
        "source": "demo.lit", "target": target["text"], "context_fact_id": citation,
        "rule_ids": target["rule_ids"],
        "selected_premise": {"search": "ByStructuralMembership", "constructor": "Add", "left": "Known", "right": "Closed"},
        "declaration": {"statement_kind": declaration["statement_kind"], "symbol_ids": declaration["declaration_symbol_ids"],
                        "carrier_well_defined": True, "nonempty_rule_ids": [rule], "stored_membership_id": citation},
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
        (HERE / f"proof-discovery{suffix}.svg").write_text(make_discovery_svg(lang, acceptance["context_fact_id"]) + "\n")
        pipeline_title = "Verification pipeline reference" if lang == "en" else "查看验证管线的入口顺序"
        figures[lang] = (
            '<div class="figure-phases">'
            f'<section class="definition-phase" data-phase="definition"><h2 class="phase-heading">{LABELS[lang]["part-definition"]}</h2>'
            f'<div class="figure-panel">{make_svg(lang, "a")}</div></section>'
            f'<section class="proof-phase" data-phase="proof"><h2 class="phase-heading">{LABELS[lang]["part-proof"]}</h2>'
            '<div class="proof-panels">' + proof_guide(lang, acceptance["context_fact_id"])
            + f'<div class="figure-panel proof-tree">{interactive_tree(lang)}</div></div>'
            + f'<details class="pipeline-reference"><summary>{pipeline_title}</summary><div class="figure-panel">{make_svg(lang, "b")}</div></details></section></div>'
            + f'<div class="figure-footer">{make_svg(lang, "footer")}</div><div class="figure-footer-mobile">{make_svg(lang, "footer-mobile")}</div>'
        )
    template = (HERE / "index.template.html").read_text()
    for lang, markup in figures.items():
        template = template.replace(f"<!-- FIGURE_{lang.upper()} -->", markup)
    template = template.replace("<!-- EVIDENCE -->", json.dumps(acceptance, ensure_ascii=False).replace("<", "\\u003c"))
    (HERE / "index.html").write_text(template)
    acceptance["assets"] = {name: hashlib.sha256((HERE / name).read_bytes()).hexdigest() for name in ["proof-search.svg", "proof-search.zh.svg", "proof-discovery.svg", "proof-discovery.zh.svg", "index.html", "viewer.js", "style.css", "build.py", "index.template.html", "export.cjs", "README.md"]}
    (HERE / "acceptance.json").write_text(json.dumps(acceptance, ensure_ascii=False, indent=2) + "\n")
    print("Verified declaration and proof; generated English/Chinese two-part figures.")


if __name__ == "__main__":
    main()
