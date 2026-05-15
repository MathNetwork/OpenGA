import OpenGALib.Algebraic
import OpenGALib.Tensor
import OpenGALib.MetricGeometry
import OpenGALib.Riemannian
import OpenGALib.Bridges
import OpenGALib.Comparison
import OpenGALib.GeometricMeasureTheory

/-!
# OpenGALib — Open Geometric Analysis Library

A Lean 4 library of algebraic, tensor, Riemannian-geometry, and
geometric-measure-theory primitives. Layered:

```
Algebraic ← Tensor ← Riemannian ← GeometricMeasureTheory
```

Each sub-namespace is built on Mathlib. Application papers consume this lib
as a separate sub-project (`require OpenGALib from ".."`).

## Sub-namespaces

* `Algebraic`               — field-generic computable algebraic core
                              (bilinear forms + concrete instances) plus
                              `Algebraic/Auxiliary/` combinatorial helpers
                              (Fin / Perm / Kronecker / Shuffle theory)
                              consumed by `Tensor/Alternating`.
* `Tensor`                  — vector-bundle tensor algebra: continuous
                              multilinear / alternating maps, tensor
                              products, differential forms. Independent
                              of metric.
* `Riemannian`              — Levi-Civita connection, Riemann / Ricci /
                              scalar curvature, second fundamental form,
                              manifold gradient, Hessian / Laplacian
                              operators, `(r,s)`-tensor bundle types.
* `GeometricMeasureTheory`  — finite-perimeter, varifolds, stationary,
                              tangent cones, rectifiability, isoperimetric.

## Sorry status

Per `docs/SORRY_CATALOG.md`. The Riemannian package carries zero existence
axioms; ported content carries 5 PRE-PAPER sorrys total (2 in
`Algebraic/Auxiliary/Fin`, 3 in `Algebraic/Auxiliary/ShuffleDeriv`),
all inherited from the external lib.
-/
