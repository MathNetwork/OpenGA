import OpenGALib.Algebraic
import OpenGALib.Riemannian
import OpenGALib.GeometricMeasureTheory
import OpenGALib.Regularity

/-!
# OpenGALib — Open Geometric Analysis Library

A Lean 4 library of algebraic-geometry, Riemannian-geometry,
geometric-measure-theory, and regularity primitives. Layered:

```
Algebraic ← Riemannian ← GeometricMeasureTheory ← Regularity
```

Each sub-namespace is built on Mathlib and intended as a future
Mathlib-upstream candidate. Application papers consume this lib as a
separate sub-project.

## Sub-namespaces

* `Algebraic`               — field-generic computable algebraic core
                              (bilinear forms + concrete instances)
* `Riemannian`              — Levi-Civita, Riemann/Ricci/scalar curvature,
                              second fundamental form, manifold gradient
* `GeometricMeasureTheory`  — finite-perimeter, varifolds, stationary,
                              tangent cones, rectifiability, isoperimetric
* `Regularity`              — Wickramasekera 𝒮_α + smooth regularity
-/
