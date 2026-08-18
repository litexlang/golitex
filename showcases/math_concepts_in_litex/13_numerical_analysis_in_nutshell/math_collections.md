# Concept Inventory

| Concept | Litex form | Why it is here |
| --- | --- | --- |
| residual | `have fn` | measures equation error |
| Newton update | guarded `have fn` | exposes division by a nonzero iterate |
| concrete iterates | three checked equalities | shows executable exact arithmetic |
| scaled residual identity | `thm` | flagship mechanism stated through the residual interface |
| residual decrease | checked inequalities | connects the identity to visible numerical progress |

The first version stops before floating-point error, stopping criteria,
interpolation, quadrature, numerical ODEs, and matrix algorithms.
