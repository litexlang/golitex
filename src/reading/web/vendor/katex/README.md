# KaTeX 0.16.21

Vendored from the installed `katex` npm package in the sibling litex-webpage
checkout. Upstream: https://github.com/KaTeX/KaTeX. See LICENSE for the MIT
license covering the library and bundled fonts.

The minified JavaScript is unchanged. CSS font sources are replaced with
embedded WOFF2 data URLs so preview, static export and offline reading need
no CDN, font routes or installed Node runtime.

Regenerate from an installed package of the pinned version:

```sh
python3 src/reading/vendor_katex.py /path/to/node_modules/katex
```

Review version changes explicitly; the bundler rejects other versions.
