# Litex Lean library

This Lake package owns the shared target ABI used by Litex-to-Lean output.

- `Litex.Core` defines the universal `Litex.Object` ABI and its small semantic
  boundary.
- `Litex.BuiltinRules` proves concrete verifier rules once and re-exports the
  core by importing it.

Generated files import only `Litex.BuiltinRules`. A generated ABI-version
check fails if the file is compiled against an incompatible shared library.

Add this package as a Lake dependency before compiling generated output. The
package currently targets Lean and Mathlib `v4.28.0`.
