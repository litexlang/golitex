# Legacy std archive

The modules in `modules/` are historical experiment material, not a Litex
standard library and not a supported import surface.

- Rebuild a fact only when a current source needs it.
- Put the rebuilt fact in that source's local cite package first.
- Consider a shared package only after the fact is fully checkable and used by
  at least three independent sources.
