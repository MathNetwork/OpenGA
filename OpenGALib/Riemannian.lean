import OpenGALib.Riemannian.Manifold.BumpFunction
import OpenGALib.Riemannian.Connection.LeviCivita
import OpenGALib.Riemannian.Curvature.RiemannCurvature
import OpenGALib.Util.Notation
import OpenGALib.Util.Tactic
import OpenGALib.Riemannian.Operators.Gradient
import OpenGALib.Riemannian.Metric.RiemannianMetric
import OpenGALib.Riemannian.Operators.ConnectionLaplacian
import OpenGALib.Riemannian.Operators.Hessian
import OpenGALib.Riemannian.Operators.Laplacian
import OpenGALib.Riemannian.Operators.SecondFundamentalForm
import OpenGALib.Riemannian.TensorBundle.BundleSectionContinuity
import OpenGALib.Riemannian.Util.ChartJacobianSmooth
import OpenGALib.Riemannian.Util.ChartJacobianSmoothness
import OpenGALib.Riemannian.Util.CovDerivBridges
import OpenGALib.Riemannian.Util.DivergenceSimp
import OpenGALib.Riemannian.Util.MetricInnerSmoothness
import OpenGALib.Riemannian.TensorBundle.Defs
import OpenGALib.Riemannian.TangentBundle.TangentSmooth
import OpenGALib.Riemannian.Instances.EuclideanSpace

/-!
# Riemannian

Riemannian-geometry primitives layered above Mathlib's covariant-derivative
infrastructure: framework-owned `RiemannianMetric` typeclass, Levi-Civita
connection (Koszul + Riesz construction), Riemann / Ricci / scalar curvature,
codim-1 second fundamental form + mean curvature, manifold gradient via
Riesz duality, and bump-function infrastructure.

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
```

## Status

Pre-`v0.1.0`, experimental. Zero existence axioms: all 9 primitives
(Riemann curvature, Ricci, scalar curvature, second fundamental form
+ sq norm, mean curvature, manifold gradient + sq norm, Levi-Civita
connection) are real Lean definitions. Remaining PRE-PAPER property-
level sorrys are tracked in `docs/SORRY_CATALOG.md` with repair plans.
-/
