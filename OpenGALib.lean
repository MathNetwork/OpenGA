import OpenGALib.Algebraic
import OpenGALib.Tensor
import OpenGALib.Riemannian
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

## Phase status

* **Phase A (port)** — complete. ~10 000 lines of tensor / shuffle /
  differential-form / operator content ported from external reference
  (qinz1yang/differential-geometry). See `docs/EXTERNAL_INTEGRATION_PLAN.md`.
* **Phase B (audit)** — complete. Findings in `docs/AUDIT_PHASE_B.md`. Net:
  ported content is self-contained, currently isolated from lib core; bridges
  to Curvature / Hessian-symmetry / manifold-DifferentialForm are tier-3
  Phase C work, consumer-driven.
* **Phase C (consolidation)** — in progress. Tier 1 (documentation / facade)
  current; tier 2 (naming / `@[simp]` audit) deferred; tier 3 (substantive
  bridges) consumer-driven.

## Sorry status

Per `docs/SORRY_CATALOG.md`. The Riemannian package carries zero existence
axioms; ported content carries 5 PRE-PAPER sorrys total (2 in
`Algebraic/Auxiliary/Fin`, 3 in `Algebraic/Auxiliary/ShuffleDeriv`),
all inherited from the external lib.
-/
