import Riemannian.Connection
import Riemannian.Curvature
import Riemannian.SecondFundamentalForm
import Riemannian.Gradient
import Riemannian.InnerProductBridge

/-!
# Riemannian

Riemannian-geometry primitives layered above Mathlib's covariant-derivative
infrastructure: Levi-Civita connection, Riemann/Ricci/scalar curvature,
codim-1 second fundamental form + mean curvature, manifold gradient via
Riesz duality.

This package is independent of paper-domain concerns and is a future
spin-out candidate as a standalone Lean lib (Mathlib upstream / community
use).

## Layering

```
Mathlib                      ← upstream
       ↑
Riemannian                   ← THIS package
       ↑
GeometricMeasureTheory       ← consumer (Variation/, Stable.lean)
       ↑
MinMax / Regularity          ← consumers
       ↑
AltRegularity                ← consumer
```

## Files

  * `Connection.lean` — Levi-Civita (existence axiom + Classical.choice)
  * `Curvature.lean`  — Riemann tensor, Ricci, scalar curvature
  * `SecondFundamentalForm.lean` — codim-1 scalar form, |A|², mean curvature
  * `Gradient.lean`   — manifold gradient, gradient norm squared
-/
