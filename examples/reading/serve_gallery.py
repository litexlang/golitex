#!/usr/bin/env python3
"""Serve a local reading gallery with the native Litex checking endpoint."""
import argparse
import json
from functools import partial
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer
from urllib.error import HTTPError, URLError
from urllib.parse import urlparse
from urllib.request import Request, urlopen


class GalleryHandler(SimpleHTTPRequestHandler):
    def do_GET(self):
        # HTML gets an opt-in same-origin checking endpoint. Exports stay static.
        if urlparse(self.path).path.endswith(('/', '.html')):
            path = self.translate_path(self.path)
            from pathlib import Path
            page = Path(path)
            if page.is_dir():
                page = page / 'index.html'
            if page.is_file():
                content = page.read_text().replace('</body>', '<script type="application/json" id="reading-build-endpoint">/api/reading/build</script></body>')
                data = content.encode()
                self.send_response(200)
                self.send_header('Content-Type', 'text/html; charset=utf-8')
                self.send_header('Content-Length', str(len(data)))
                self.send_header('Cache-Control', 'no-store')
                self.end_headers()
                self.wfile.write(data)
                return
        super().do_GET()

    def do_POST(self):
        origin = f'http://127.0.0.1:{self.server.server_port}'
        if self.path != '/api/reading/build' or self.headers.get('Origin') not in (None, origin):
            self.send_error(403)
            return
        if self.headers.get('Host') != f'127.0.0.1:{self.server.server_port}':
            self.send_error(403)
            return
        try:
            size = int(self.headers.get('Content-Length', '0'))
            if not 0 < size <= 16 * 1024 * 1024:
                raise ValueError('Request exceeds 16 MiB or has no content')
            if self.headers.get_content_type() != 'application/json':
                raise ValueError('Expected application/json')
            body = self.rfile.read(size)
            request = Request(self.server.build_origin + '/api/reading/build', body,
                              {'Content-Type': 'application/json', 'Origin': self.server.build_origin})
            with urlopen(request, timeout=310) as response:
                self.send_response(response.status)
                self.send_header('Content-Type', 'application/json')
                self.end_headers()
                while chunk := response.read(1024 * 1024):
                    self.wfile.write(chunk)
        except HTTPError as error:
            self.send_response(error.code)
            self.send_header('Content-Type', 'application/json')
            self.end_headers()
            self.wfile.write(error.read())
        except (ValueError, URLError, TimeoutError) as error:
            self.send_response(502)
            self.send_header('Content-Type', 'application/json')
            self.end_headers()
            self.wfile.write(json.dumps({'error': str(error)}).encode())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('directory')
    parser.add_argument('--port', type=int, default=49187)
    parser.add_argument('--build-origin', default='http://127.0.0.1:49186')
    args = parser.parse_args()
    upstream = urlparse(args.build_origin)
    if upstream.scheme != 'http' or upstream.hostname != '127.0.0.1' or upstream.path not in ('', '/'):
        parser.error('--build-origin must be a loopback Litex reading server')
    server = ThreadingHTTPServer(('127.0.0.1', args.port), partial(GalleryHandler, directory=args.directory))
    server.build_origin = args.build_origin.rstrip('/')
    print(f'Editable reading gallery: http://127.0.0.1:{args.port}/', flush=True)
    server.serve_forever()


if __name__ == '__main__':
    main()
