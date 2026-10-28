#!/usr/bin/env python3
"""Check generated gallery links, localized sources and shared asset identity."""
import argparse
import hashlib
import json
import mmap
from html.parser import HTMLParser
from pathlib import Path
from urllib.parse import urlsplit, parse_qs

ROOT = Path(__file__).resolve().parents[4]


class Page(HTMLParser):
    def __init__(self, path):
        super().__init__()
        self.assets, self.alternates, self.groups = [], {}, []
        self.capture, self.data = False, []
        # Proof JSON can exceed 300 MB in a standalone book. Inspect the actual
        # navigation markup without making HTMLParser buffer that script body.
        with path.open('rb') as stream, mmap.mmap(stream.fileno(), 0, access=mmap.ACCESS_READ) as data:
            head_end = data.find(b'</head>')
            assert 0 <= head_end < 65536, (path, 'unexpected export head')
            self.feed(data[:head_end + 7].decode('utf-8'))
            position = data.find(b'id="reading-example-groups"')
            if position >= 0:
                start = data.rfind(b'<script', 0, position)
                end = data.find(b'</script>', position)
                assert start >= 0 and end >= position, path
                self.feed(data[start:end + 9].decode('utf-8'))
        self.close()

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        if tag == 'script' and attrs.get('id') == 'reading-example-groups':
            self.capture, self.data = True, []
        if tag == 'script' and attrs.get('src'):
            self.assets.append(attrs['src'])
        if tag == 'link' and attrs.get('rel') == 'stylesheet':
            self.assets.append(attrs['href'])
        if tag == 'link' and attrs.get('rel') == 'alternate':
            self.alternates[attrs['hreflang']] = attrs['href']

    def handle_data(self, text):
        if self.capture:
            self.data.append(text)

    def handle_endtag(self, tag):
        if tag == 'script' and self.capture:
            self.groups = json.loads(''.join(self.data))
            self.capture = False


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('site', type=Path)
    args = parser.parse_args()
    site = args.site.resolve()
    assets = {name: (ROOT / 'src/reading/web' / name).read_bytes()
              for name in ('reader.js', 'reader.css', 'app.js')}
    pages = list(site.rglob('index.html')) + list(site.rglob('standalone.html'))
    links = 0
    for path in pages:
        page = Page(path)
        seen = set()
        for asset in page.assets:
            url = urlsplit(asset)
            if url.path not in assets:
                continue
            seen.add(url.path)
            assert (path.parent / url.path).read_bytes() == assets[url.path], (path, url.path)
            assert parse_qs(url.query).get('v') == [hashlib.sha256(assets[url.path]).hexdigest()[:12]], (path, asset)
        assert seen == set(assets), (path, seen)
        for group in page.groups:
            for entry in group.get('items', []):
                for locale in ('zh', 'en'):
                    href = entry.get('hrefs', {}).get(locale) or entry.get('href')
                    assert href and not urlsplit(href).scheme, (path, href)
                    target = (path.parent / href).resolve()
                    assert target.is_relative_to(site) and (target / 'index.html').is_file(), (path, href)
                    links += 1
        for locale, href in page.alternates.items():
            assert locale in ('zh', 'en')
            target = (path.parent / href).resolve()
            assert target.is_relative_to(site) and target.is_file(), (path, href)
    catalogue = json.loads((ROOT / 'examples/reading/lessons/catalogue.json').read_text())['lessons']
    for item in catalogue:
        for locale in ('zh', 'en'):
            directory = site / 'lessons' / locale / item['id']
            bundle = json.loads((directory / 'reading.json').read_text())
            assert bundle['run_result'] == item['expected']
            assert len(bundle['sources']) == 1
            assert bundle['sources'][0]['content'] == (ROOT / 'examples/reading/lessons' / item['litex_code'][locale]).read_text()
            assert bundle['sources'][0]['titles'] == item['titles']
            for name in ('index.html', 'standalone.html'):
                page = Page(directory / name)
                assert set(page.alternates) == {'zh', 'en'}
                assert page.groups[0]['titles']['en'] == 'Start reading'
    print(json.dumps({'passed': True, 'pages': len(pages), 'menu_links': links,
                      'localized_lessons': len(catalogue) * 2,
                      'shared_assets_identical': True}, indent=2))


if __name__ == '__main__':
    main()
