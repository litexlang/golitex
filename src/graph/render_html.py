#!/usr/bin/env python3
"""Embed an emitted mathematical graph in the shipped standalone viewer."""
import json
from pathlib import Path
import sys


def main():
    if len(sys.argv) != 3:
        raise SystemExit('usage: python3 src/graph/render_html.py graph.json graph.html')
    source, destination = map(Path, sys.argv[1:])
    graph = json.loads(source.read_text())
    if graph.get('kind') != 'math_graph' or graph.get('schema_version') != 1:
        raise SystemExit('expected a math_graph schema_version 1 document')
    root = Path(__file__).resolve().parents[2]
    viewer = (root / 'docs/assets/math_graph_viewer.html').read_text()
    # JSON is data, never executable source; prevent closing the script element.
    encoded = json.dumps(graph, ensure_ascii=False).replace('<', '\\u003c').replace('>', '\\u003e').replace('&', '\\u0026')
    viewer = viewer.replace('<script id="initial-data" type="application/json">null</script>',
                            '<script id="initial-data" type="application/json">' + encoded + '</script>')
    destination.write_text(viewer)


if __name__ == '__main__':
    main()
