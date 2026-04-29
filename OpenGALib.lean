import Algebraic
import Riemannian
import GeometricMeasureTheory
import MinMax
import Regularity

/-!
# OpenGALib — Open Geometric Analysis Library

A Lean 4 library of algebraic-geometry, Riemannian-geometry,
geometric-measure-theory, min-max, and regularity primitives. Layered:

```
Algebraic ← Riemannian ← GeometricMeasureTheory ← {MinMax, Regularity}
```

Each sub-namespace is built on Mathlib and intended as a future
Mathlib-upstream candidate. Application papers (e.g., AltRegularity)
consume this lib as a separate sub-project.

## Sub-namespaces

* `Algebraic`               — field-generic computable algebraic core
                              (bilinear forms + concrete instances)
* `Riemannian`              — Levi-Civita, Riemann/Ricci/scalar curvature,
                              second fundamental form, manifold gradient
* `GeometricMeasureTheory`  — finite-perimeter, varifolds, stationary,
                              tangent cones, rectifiability, isoperimetric
* `MinMax`                  — sweepout-based min-max
* `Regularity`              — Wickramasekera 𝒮_α + smooth regularity
-/
