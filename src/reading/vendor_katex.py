#!/usr/bin/env python3
"""Bundle the pinned installed KaTeX package with offline WOFF2 fonts."""
import base64
import json
from pathlib import Path
import re
import shutil
import sys

package = Path(sys.argv[1])
version = json.loads((package / "package.json").read_text())["version"]
if version != "0.16.21":
    raise SystemExit(f"Expected KaTeX 0.16.21, got {version}; review an upgrade separately.")
target = Path(__file__).resolve().parent / "web" / "vendor" / "katex"
target.mkdir(parents=True, exist_ok=True)

def embed(match):
    name = re.search(r"url\(fonts/([^()]+\.woff2)\)", match[1])
    if not name:
        raise ValueError("Expected a WOFF2 font source")
    data = base64.b64encode((package / "dist/fonts" / name[1]).read_bytes()).decode()
    return f'src:url("data:font/woff2;base64,{data}") format("woff2")'

css = (package / "dist/katex.min.css").read_text()
css, count = re.subn(r"src:([^}]+)", embed, css)
assert count > 0 and "url(fonts/" not in css
(target / "katex.min.css").write_text(css)
shutil.copyfile(package / "dist/katex.min.js", target / "katex.min.js")
shutil.copyfile(package / "LICENSE", target / "LICENSE")
print(f"Bundled KaTeX {version}, {count} embedded WOFF2 fonts")
