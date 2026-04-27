/-!
# OpenGALib — Open Geometric Analysis Library

A Lean 4 library of Riemannian-geometry, geometric-measure-theory,
min-max, and regularity primitives. Layered:
Riemannian ← GeometricMeasureTheory ← {MinMax, Regularity}

Each sub-namespace is built on Mathlib and intended as a future
Mathlib-upstream candidate. Application papers (e.g., AltRegularity)
consume this lib as a separate sub-project.

## Sub-namespaces

* `Riemannian`              — Levi-Civita, Riemann/Ricci/scalar curvature,
                              second fundamental form, manifold gradient
* `GeometricMeasureTheory`  — finite-perimeter, varifolds, stationary,
                              tangent cones, rectifiability, isoperimetric
* `MinMax`                  — sweepout-based min-max (CLS22-style)
* `Regularity`              — Wickramasekera 𝒮_α + smooth regularity
-/

import Riemannian
import GeometricMeasureTheory
import MinMax
import Regularity
