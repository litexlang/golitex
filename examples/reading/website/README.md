# Embed the reading viewer in a website

The example uses a real static export twice: a shared component and an iframe.
The host buttons select actual statement/fact IDs in both readers. No proof
relationships are reconstructed by the website.

From the golitex root, prepare an isolated example site:

```sh
mkdir -p tmp/reading-website
cp examples/reading/website/index.html examples/reading/website/main.js tmp/reading-website/
target/release/litex -reading -strict -lang zh \
  -f examples/reading/inferred_facts.lit -export tmp/reading-website/book
python3 -m http.server 49182 --bind 127.0.0.1 --directory tmp/reading-website
```

Open `http://127.0.0.1:49182/`. “查看后文陈述” selects the later statement,
whose grounds include a grey inferred fact. “查看推导事实” selects that exact
fact and shows the source seed and inference evidence. The displayed status
reports actual component/iframe navigation callbacks.
“查看有定义依据” selects an actual registered object by its exported WD ID,
including its scope, creator and retained formation evidence.

The host reads `reading.manifest.json` and opens the shared component with
`LitexReading.open`; chapter proofs load on demand. It waits for the iframe's
actual `litex-reading:ready` event and checks its `bundle_id`. Selections carry
the same ID, so replacing the iframe document disables stale host controls.
To try chapter navigation/search, export `-r examples/reading/book` instead
of the single-file input above.

For a real website, publish `book/` with the site. Copy only the integration
you need from `main.js`. The host does not need Node or Litex to browse
prebuilt evidence. Rechecking edited Litex needs a backend running the
reading exporter; see the [integration guide](../../../docs/reading.md).
