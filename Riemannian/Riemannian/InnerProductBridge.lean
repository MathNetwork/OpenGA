import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Topology.VectorBundle.Riemannian
import Mathlib.Analysis.InnerProductSpace.Defs

/-!
# Riemannian.InnerProductBridge

Framework self-build bridge: provides `NormedAddCommGroup` and
`InnerProductSpace ℝ` typeclass instances on `TangentSpace I x` from
the `RiemannianBundle (fun x ↦ TangentSpace I x)` data.

## Why this file exists

Mathlib's `Topology/VectorBundle/Riemannian.lean` (lines 431, 453)
provides scoped instances accomplishing the same goal — but they
target the general bundle pattern `E : B → Type*` and rely on
higher-order unification with the literal `fun x ↦ TangentSpace I x`
to fire. Empirically (Phase 1.6 Spike 5) this unification fails in
the framework's smooth-manifold cascade, leaving
`InnerProductSpace ℝ (TangentSpace I x)` unsynthesized.

This file replicates the scoped-instance bodies as **non-scoped
explicit instances**, using the `RiemannianBundle.g` accessor
directly. The instances use `letI` and `InnerProductSpace.Core`
machinery from Mathlib (`RiemannianMetric.toCore`,
`InnerProductSpace.ofCoreOfTopology`) — same construction Mathlib
uses internally, just made explicit at our cascade.

**Used by**: downstream `Riemannian/Gradient.lean` for Riesz duality;
unblocks `manifoldGradient`, `secondFundamentalFormScalar`,
`secondFundamentalFormSqNorm`, `meanCurvature`, `scalarCurvature`
real defs.
-/

open Bundle
open scoped Manifold

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- **NormedAddCommGroup bridge**: `TangentSpace I x` inherits a
`NormedAddCommGroup ℝ` instance from the
`RiemannianBundle (fun x ↦ TangentSpace I x)` data, via Mathlib's
`InnerProductSpace.Core.toNormedAddCommGroupOfTopology`.

Mirror of Mathlib's scoped instance in
`Topology/VectorBundle/Riemannian.lean` line ~431, made explicit
to bypass higher-order unification on
`fun x ↦ TangentSpace I x`. -/
noncomputable instance instNormedAddCommGroupTangentSpace
    [h : RiemannianBundle (fun x : M => TangentSpace I x)] (x : M) :
    NormedAddCommGroup (TangentSpace I x) :=
  (h.g.toCore x).toNormedAddCommGroupOfTopology
    (h.g.continuousAt x) (h.g.isVonNBounded x)

/-- **InnerProductSpace bridge**: `TangentSpace I x` inherits an
`InnerProductSpace ℝ` instance from the same bundle data.

Mirror of Mathlib's scoped instance line ~453. -/
noncomputable instance instInnerProductSpaceTangentSpace
    [h : RiemannianBundle (fun x : M => TangentSpace I x)] (x : M) :
    InnerProductSpace ℝ (TangentSpace I x) :=
  InnerProductSpace.ofCoreOfTopology (h.g.toCore x)
    (h.g.continuousAt x) (h.g.isVonNBounded x)

/-- **FiniteDimensional bridge**: `TangentSpace I x` inherits the
finite-dimensional structure from the model space `E`. The
`unfold TangentSpace; infer_instance` proof leverages the def-equality
`TangentSpace I x = E`. -/
instance instFiniteDimensionalTangentSpace
    [FiniteDimensional ℝ E] (x : M) :
    FiniteDimensional ℝ (TangentSpace I x) := by
  unfold TangentSpace; infer_instance

/-- **CompleteSpace bridge**: with `NormedAddCommGroup (TangentSpace I x)`
provided by `instNormedAddCommGroupTangentSpace` and
`FiniteDimensional ℝ (TangentSpace I x)` provided by
`instFiniteDimensionalTangentSpace`, `CompleteSpace` follows from
Mathlib's `FiniteDimensional.complete` for normed ℝ-spaces. -/
instance instCompleteSpaceTangentSpace
    [h : RiemannianBundle (fun x : M => TangentSpace I x)]
    [FiniteDimensional ℝ E] (x : M) :
    CompleteSpace (TangentSpace I x) :=
  FiniteDimensional.complete ℝ (TangentSpace I x)

end Riemannian
