import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Riemannian.Metric.Basic
import Riemannian.TangentBundle.Smoothness
import Riemannian.TangentBundle.SmoothSection

/-!
# `metricInner` smoothness helper

Framework analog of Mathlib's `MDifferentiableAt.inner_bundle`, using the
framework-owned `metricInner` instead of `[IsContMDiffRiemannianBundle]`.
Used by `koszul_smul_right` / `koszul_add_right` to derive scalar
smoothness of $\langle Y, Z \rangle_g$ from bundle-section smoothness of
$Y, Z$.

Proof: chart-bridge via the trivialization
`e := trivializationAt E (TangentSpace I) x`, using the round-trip
identity `e.symmL ℝ y (e.continuousLinearMapAt ℝ y v) = v` on
`e.baseSet`. The `e.symmL` smoothness step delegates to
`TangentBundle.symmLFlat_mdifferentiableAt`
(`Riemannian/TangentBundle/Smoothness.lean`), which exposes a flat-typed
`M → (E →L[ℝ] E)` API hiding the `TangentSpace I y = E` def-eq bridge
internally — no `cast` or `h_TS_E_eq` parameter surfaces in this file. -/

open scoped ContDiff Manifold Topology

namespace OpenGALib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [g : RiemannianMetric I M]

/-- **Smoothness of the metric inner product** as a scalar function of
the basepoint, given smooth bundle sections.

For smooth tangent vector fields $Y, Z$ at $x$, the scalar function
$y \mapsto \langle Y(y), Z(y)\rangle_g$ is $C^\infty$ at $x$.

Hypotheses are taken as `TangentSmoothAt` predicates (Phase A.0
abstraction layer for Riemannian smoothness). -/
theorem MDifferentiableAt.metricInner_smoothAt
    {Y Z : Π y : M, TangentSpace I y} {x : M}
    (hY : TangentSmoothAt Y x) (hZ : TangentSmoothAt Z x) :
    MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => metricInner y (Y y) (Z y)) x := by
  set e := trivializationAt E (TangentSpace I) x with he_def
  have hY' : MDifferentiableAt I 𝓘(ℝ, E) (fun y => (e ⟨y, Y y⟩).2) x :=
    hY.coordSmoothAt
  have hZ' : MDifferentiableAt I 𝓘(ℝ, E) (fun y => (e ⟨y, Z y⟩).2) x :=
    hZ.coordSmoothAt
  have hg : MDifferentiableAt I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) g.metricTensor x :=
    (g.smoothMetric x).mdifferentiableAt (by decide)
  have h_symmL : MDifferentiableAt I 𝓘(ℝ, E →L[ℝ] E)
      (fun y : M => TangentBundle.symmLFlat (I := I) (M := M) x y) x :=
    TangentBundle.symmLFlat_mdifferentiableAt x
  have h_compY : MDifferentiableAt I 𝓘(ℝ, E)
      (fun y => TangentBundle.symmLFlat (I := I) (M := M) x y ((e ⟨y, Y y⟩).2)) x :=
    h_symmL.clm_apply hY'
  have h_compZ : MDifferentiableAt I 𝓘(ℝ, E)
      (fun y => TangentBundle.symmLFlat (I := I) (M := M) x y ((e ⟨y, Z y⟩).2)) x :=
    h_symmL.clm_apply hZ'
  have h_smooth : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y => g.metricTensor y
        (TangentBundle.symmLFlat (I := I) (M := M) x y ((e ⟨y, Y y⟩).2))
        (TangentBundle.symmLFlat (I := I) (M := M) x y ((e ⟨y, Z y⟩).2))) x :=
    (hg.clm_apply h_compY).clm_apply h_compZ
  apply h_smooth.congr_of_eventuallyEq
  have h_baseSet_e : e.baseSet ∈ 𝓝 x :=
    e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' x)
  filter_upwards [h_baseSet_e] with y hy
  set_option backward.isDefEq.respectTransparency false in
  have hY_inv :
      TangentBundle.symmLFlat (I := I) (M := M) x y ((e ⟨y, Y y⟩).2) = (Y y : E) := by
    show e.symmL ℝ y (e ⟨y, Y y⟩).2 = (Y y : E)
    have h_round := Bundle.Trivialization.symmL_continuousLinearMapAt
      (R := ℝ) (e := e) hy (Y y)
    have h_eq : (e ⟨y, Y y⟩).2 = e.continuousLinearMapAt ℝ y (Y y) := by
      have := Bundle.Trivialization.coe_linearMapAt_of_mem (R := ℝ) e hy
      exact (congrFun this (Y y)).symm
    rw [h_eq]
    exact h_round
  set_option backward.isDefEq.respectTransparency false in
  have hZ_inv :
      TangentBundle.symmLFlat (I := I) (M := M) x y ((e ⟨y, Z y⟩).2) = (Z y : E) := by
    show e.symmL ℝ y (e ⟨y, Z y⟩).2 = (Z y : E)
    have h_round := Bundle.Trivialization.symmL_continuousLinearMapAt
      (R := ℝ) (e := e) hy (Z y)
    have h_eq : (e ⟨y, Z y⟩).2 = e.continuousLinearMapAt ℝ y (Z y) := by
      have := Bundle.Trivialization.coe_linearMapAt_of_mem (R := ℝ) e hy
      exact (congrFun this (Z y)).symm
    rw [h_eq]
    exact h_round
  show metricInner y (Y y) (Z y) =
      g.metricTensor y
        (TangentBundle.symmLFlat (I := I) (M := M) x y ((e ⟨y, Y y⟩).2))
        (TangentBundle.symmLFlat (I := I) (M := M) x y ((e ⟨y, Z y⟩).2))
  rw [hY_inv, hZ_inv]
  rfl

end OpenGALib
