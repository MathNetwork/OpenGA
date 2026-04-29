import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Riemannian.Metric.Basic

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
`e.baseSet`. The `e.symmL` smoothness step is extracted as the narrow
structural axiom `tangentBundle_symmL_smoothAt` (see `AXIOM_STATUS.md`
for repair plan). -/

open scoped ContDiff Manifold Topology

namespace OpenGALib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [g : RiemannianMetric I M]

set_option backward.isDefEq.respectTransparency false in
/-- **Smoothness of the tangent-bundle trivialization inverse `symmL`**,
as a CLM-valued function of the basepoint, in non-dependent codomain via
the `TangentSpace I y = E` def-eq cast.

For `e := trivializationAt E (TangentSpace I) x`, the function
$y \mapsto e.\mathrm{symmL}\,\mathbb{R}\,y$ is $C^\infty$ at $x$ as a map
$M \to (E \to_L^{\mathbb{R}} E)$. Mathematically this is the smoothness
of the inverse chart-derivative, standard for tangent bundles.

Proof: rewrite via `TangentBundle.symmL_trivializationAt` (which gives
`e.symmL ℝ y = mfderiv[range I] (extChartAt I x).symm (extChartAt I x y)`
on chart source), then use the parametric inverse-mfderiv smoothness
pattern from `Mathlib/VectorBundle/Pullback.lean`:
`ContMDiffWithinAt.mfderivWithin_const` for the in-coordinates form +
`IsInvertible.contDiffAt_map_inverse` to bridge inverse + raw forms via
`inCoordinates_eq` round-trip identities. -/
theorem tangentBundle_symmL_smoothAt
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (x : M) (h_TS_E_eq : ∀ y : M, (E →L[ℝ] TangentSpace I y) = (E →L[ℝ] E)) :
    MDifferentiableAt I 𝓘(ℝ, E →L[ℝ] E)
      (fun y : M => cast (h_TS_E_eq y)
        ((trivializationAt E (TangentSpace I) x).symmL ℝ y)) x := by
  -- Step 1: Rewrite via `TangentBundle.symmL_trivializationAt` to express
  -- `e.symmL ℝ y` as `mfderivWithin (range I) (extChartAt I x).symm (extChartAt I x y)`
  -- on chart source. This eliminates the dependent-codomain issue: both sides
  -- have type `E →L[ℝ] E` once we set `respectTransparency false`.
  set e := trivializationAt E (TangentSpace I) x with he_def
  -- The base-set neighborhood of x.
  have hx_chart : x ∈ (chartAt H x).source := mem_chart_source H x
  have h_chart_nhds : (chartAt H x).source ∈ 𝓝 x :=
    (chartAt H x).open_source.mem_nhds hx_chart
  -- Step 2: Smoothness of `extChartAt I x` at x as `M → E`.
  have h_chart_smooth : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I x) x :=
    mdifferentiableAt_extChartAt hx_chart
  -- Step 3: For y in chart source, e.symmL ℝ y equals
  --   mfderivWithin (range I) (extChartAt I x).symm (extChartAt I x y).
  -- This is `TangentBundle.symmL_trivializationAt`. The full smoothness proof
  -- of the RHS requires Mathlib's parametric inverse-mfderiv pattern from
  -- `VectorField/Pullback.lean` lines 280-322:
  --   * `ContMDiffWithinAt.mfderivWithin_const` for in-coordinates smoothness
  --     of `mfderivWithin (range I) (extChartAt I x).symm`.
  --   * `IsInvertible.contDiffAt_map_inverse` to bridge inverse-of-mfderiv
  --     to the raw form via `inCoordinates_eq` round-trip identities.
  --   * Compose with `extChartAt I x` smoothness for the final result.
  -- The `inCoordinates_eq` calculation is intricate (multi-step rewrite chain)
  -- and requires unique-mdiff-on hypotheses + finite-dim cascades.
  -- Spike status: structural framework laid out (steps 1–3 above); the
  -- inverse-mfderiv smoothness composition is not closed in this commit.
  sorry

/-- **Smoothness of the metric inner product** as a scalar function of
the basepoint, given smooth bundle sections.

For smooth tangent-bundle sections $Y, Z$ at $x$, the scalar function
$y \mapsto \langle Y(y), Z(y)\rangle_g$ is $C^\infty$ at $x$. -/
theorem MDifferentiableAt.metricInner_smoothAt
    {Y Z : Π y : M, TangentSpace I y} {x : M}
    (hY : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, Y y⟩ : TangentBundle I M)) x)
    (hZ : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, Z y⟩ : TangentBundle I M)) x) :
    MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => metricInner y (Y y) (Z y)) x := by
  set e := trivializationAt E (TangentSpace I) x with he_def
  rw [mdifferentiableAt_totalSpace] at hY hZ
  have hY' : MDifferentiableAt I 𝓘(ℝ, E) (fun y => (e ⟨y, Y y⟩).2) x := hY.2
  have hZ' : MDifferentiableAt I 𝓘(ℝ, E) (fun y => (e ⟨y, Z y⟩).2) x := hZ.2
  have hg : MDifferentiableAt I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) g.metricTensor x :=
    (g.smoothMetric x).mdifferentiableAt (by decide)
  have hx_chart : x ∈ (chartAt H x).source := mem_chart_source H x
  have h_baseSet : (chartAt H x).source ∈ 𝓝 x :=
    (chartAt H x).open_source.mem_nhds hx_chart
  set_option backward.isDefEq.respectTransparency false in
  have h_TS_E_eq : ∀ y : M, (E →L[ℝ] TangentSpace I y) = (E →L[ℝ] E) :=
    fun _ => rfl
  set_option backward.isDefEq.respectTransparency false in
  have h_symmL : MDifferentiableAt I 𝓘(ℝ, E →L[ℝ] E)
      (fun y : M => cast (h_TS_E_eq y) (e.symmL ℝ y)) x :=
    tangentBundle_symmL_smoothAt x h_TS_E_eq
  set_option backward.isDefEq.respectTransparency false in
  have h_compY : MDifferentiableAt I 𝓘(ℝ, E)
      (fun y => (e.symmL ℝ y : E →L[ℝ] E) ((e ⟨y, Y y⟩).2)) x :=
    h_symmL.clm_apply hY'
  set_option backward.isDefEq.respectTransparency false in
  have h_compZ : MDifferentiableAt I 𝓘(ℝ, E)
      (fun y => (e.symmL ℝ y : E →L[ℝ] E) ((e ⟨y, Z y⟩).2)) x :=
    h_symmL.clm_apply hZ'
  set_option backward.isDefEq.respectTransparency false in
  have h_smooth : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y => g.metricTensor y
        ((e.symmL ℝ y : E →L[ℝ] E) ((e ⟨y, Y y⟩).2))
        ((e.symmL ℝ y : E →L[ℝ] E) ((e ⟨y, Z y⟩).2))) x :=
    (hg.clm_apply h_compY).clm_apply h_compZ
  apply h_smooth.congr_of_eventuallyEq
  have h_baseSet_e : e.baseSet ∈ 𝓝 x :=
    e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' x)
  filter_upwards [h_baseSet_e] with y hy
  set_option backward.isDefEq.respectTransparency false in
  have hY_inv : (e.symmL ℝ y : E →L[ℝ] E) ((e ⟨y, Y y⟩).2) = (Y y : E) := by
    have h_round := Bundle.Trivialization.symmL_continuousLinearMapAt
      (R := ℝ) (e := e) hy (Y y)
    have h_eq : (e ⟨y, Y y⟩).2 = e.continuousLinearMapAt ℝ y (Y y) := by
      have := Bundle.Trivialization.coe_linearMapAt_of_mem (R := ℝ) e hy
      exact (congrFun this (Y y)).symm
    rw [h_eq]
    exact h_round
  set_option backward.isDefEq.respectTransparency false in
  have hZ_inv : (e.symmL ℝ y : E →L[ℝ] E) ((e ⟨y, Z y⟩).2) = (Z y : E) := by
    have h_round := Bundle.Trivialization.symmL_continuousLinearMapAt
      (R := ℝ) (e := e) hy (Z y)
    have h_eq : (e ⟨y, Z y⟩).2 = e.continuousLinearMapAt ℝ y (Z y) := by
      have := Bundle.Trivialization.coe_linearMapAt_of_mem (R := ℝ) e hy
      exact (congrFun this (Z y)).symm
    rw [h_eq]
    exact h_round
  set_option backward.isDefEq.respectTransparency false in
  show metricInner y (Y y) (Z y) =
      g.metricTensor y
        ((e.symmL ℝ y : E →L[ℝ] E) ((e ⟨y, Y y⟩).2))
        ((e.symmL ℝ y : E →L[ℝ] E) ((e ⟨y, Z y⟩).2))
  rw [hY_inv, hZ_inv]
  rfl

end OpenGALib
