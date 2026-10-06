# Qualified struct views

Run `target/release/litex -strict -f examples/module_manager/qualified_struct_views/main.lit`
or use `-r examples/module_manager/qualified_struct_views`.

The root imports two different modules exporting `Pair`, and first exports its
own natural-valued `Pair`. The main file uses full import paths, a current-export
path, the single-export `Lib:::Tagged` spelling, generic parameters, a function
return carrier and a nested field type. The original two-line parser failure
is preserved as comments. Active assertions retain the full definition owner.

`cargo test --release qualified_struct_view_tests` executes the configured
files through the actual launcher. It rejects fractional tuples for the natural
and integer owners, incorrect field values, unknown fields, wrong generic
arity/domain, unknown module/export/struct names, malformed paths and flattened
references to an import with more than one export. No trust or new identity
representation is used. Nested field membership checks declared types; opening
struct laws and proving nested field values are separate proof operations.

For example, after the declared Lib import has loaded:

```litex
have item &Lib::facts::Pair = (1/2, 3/2)
item(1) = 1/2
item.first = 1/2
```

The new representation stores `item.first=item(1)`. The explicit coordinate
equality lets the original field assertion use ordinary equality transitivity.
The unmodified field-only block currently misses at `search_proof`; its receipt
is retained in the tuple/cart implementation journal. The added steps do not
change the struct owner, field order, carrier or original goals.
