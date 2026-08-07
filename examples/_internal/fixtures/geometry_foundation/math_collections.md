# Mathematical Collections

This fixture models only two real constants, `a = 1` and `b = 2`, in separate
exported files. Their separation is intentional: it checks that arithmetic can
consume fully qualified numeric values from more than one export of the same
imported module.

The ideal interface is the implemented pair of ordinary checked object
definitions:

```litex
have a R = 1
have b R = 2
```

There are no outstanding existence, uniqueness, well-definedness, or proof
holes. The fixture is not intended to grow into a geometry library.
