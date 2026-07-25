import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.SlotFreeCurvatureOperatorField
import DifferentialGeometry.Geometry.Metric.InverseMetricField
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.PosDefPerturbation
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.HomTensorRSRiemannian


noncomputable section

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.Analysis.Sobolev.TensorHilbert

open DifferentialGeometry
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure
open TensorMultilinear (contMDiffAt_section_apply contMDiff_section_apply)

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma dualToCotangent_add {x : M}
    (α β : Module.Dual ℝ (TangentSpace I x)) :
    dualToCotangent (I := I) (x := x) (α + β)
      = dualToCotangent (I := I) (x := x) α + dualToCotangent (I := I) (x := x) β := by
  apply cotangentToDualLinear_injective (I := I) (x := x)
  rw [map_add, cotangentToDualLinear_apply, cotangentToDualLinear_apply,
    cotangentToDualLinear_apply, cotangentToDual_dualToCotangent,
    cotangentToDual_dualToCotangent, cotangentToDual_dualToCotangent]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma dualToCotangent_smul {x : M} (c : ℝ)
    (α : Module.Dual ℝ (TangentSpace I x)) :
    dualToCotangent (I := I) (x := x) (c • α)
      = c • dualToCotangent (I := I) (x := x) α := by
  apply cotangentToDualLinear_injective (I := I) (x := x)
  rw [map_smul, cotangentToDualLinear_apply, cotangentToDualLinear_apply,
    cotangentToDual_dualToCotangent, cotangentToDual_dualToCotangent]

def g0FlatCLM (g₀ : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →L[ℝ] Tensor0SSpace 1 I x :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => dualToCotangent (I := I) (x := x) (g₀.inner x v).toLinearMap
      map_add' := fun v v' => by
        have h : ((g₀.inner x (v + v')).toLinearMap : Module.Dual ℝ (TangentSpace I x))
            = (g₀.inner x v).toLinearMap + (g₀.inner x v').toLinearMap := by
          ext w; simp [map_add]
        rw [h, dualToCotangent_add]
      map_smul' := fun c v => by
        have h : ((g₀.inner x (c • v)).toLinearMap : Module.Dual ℝ (TangentSpace I x))
            = c • (g₀.inner x v).toLinearMap := by
          ext w; simp [map_smul]
        rw [h, dualToCotangent_smul]; rfl }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma g0FlatCLM_apply (g₀ : SmoothRiemannianMetric I M) (x : M) (v : TangentSpace I x) :
    g0FlatCLM (I := I) g₀ x v = dualToCotangent (I := I) (x := x) (g₀.inner x v).toLinearMap := by
  rw [g0FlatCLM, LinearMap.coe_toContinuousLinearMap']; rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma inverseMetricSharpFib_g0FlatCLM_eq_metricSharp (g₀ g' : SmoothRiemannianMetric I M) (x : M)
    (v : TangentSpace I x) :
    inverseMetricSharpFib (I := I) g' x (g0FlatCLM (I := I) g₀ x v) =
      DifferentialGeometry.Integral.DivergenceTheorem.metricSharp
        (I := I) g' x (g₀.inner x v).toLinearMap := by
  rw [inverseMetricSharpFib_apply, g0FlatCLM_apply]
  rw [show cotangentToDualLinear (I := I) (dualToCotangent (I := I) (g₀.inner x v).toLinearMap)
        = (g₀.inner x v).toLinearMap from by
    rw [cotangentToDualLinear_apply, cotangentToDual_dualToCotangent]]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma cotangentToDual_g0FlatCLM (g₀ : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    cotangentToDual (I := I) (x := x) (g0FlatCLM (I := I) g₀ x v) w = g₀.inner x v w := by
  rw [g0FlatCLM_apply, cotangentToDual_dualToCotangent]; rfl

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma metricInner_injective (g₀ : SmoothRiemannianMetric I M) (x : M) :
    Function.Injective
      (fun u : TangentSpace I x => (g₀.inner x u : TangentSpace I x →L[ℝ] ℝ)) := by
  intro a b hab
  have hval : ∀ w, g₀.inner x a w = g₀.inner x b w := fun w => by
    have := congrArg (fun (φ : TangentSpace I x →L[ℝ] ℝ) => φ w) hab
    simpa using this
  by_contra hne
  have hsub : a - b ≠ 0 := sub_ne_zero.mpr hne
  have hpos := g₀.pos x (a - b) hsub
  have hzero : g₀.inner x (a - b) (a - b) = 0 := by
    have hsymm₁ : g₀.inner x (a - b) (a - b) = g₀.inner x (a - b) a - g₀.inner x (a - b) b := by
      rw [← map_sub]
    rw [hsymm₁]
    rw [g₀.symm x (a - b) a, g₀.symm x (a - b) b]
    have e1 : g₀.inner x a (a - b) = g₀.inner x b (a - b) := hval (a - b)
    rw [e1]; ring
  exact absurd hzero (ne_of_gt hpos)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma inverseMetricSharpFib_g0FlatCLM (g₀ : SmoothRiemannianMetric I M) (x : M)
    (v : TangentSpace I x) :
    inverseMetricSharpFib (I := I) g₀ x (g0FlatCLM (I := I) g₀ x v) = v := by
  have hkey : (g₀.inner x (inverseMetricSharpFib (I := I) g₀ x (g0FlatCLM (I := I) g₀ x v)) :
        TangentSpace I x →L[ℝ] ℝ) = g₀.inner x v := by
    ext w
    rw [inverseMetricSharpFib_inner, cotangentToDualLinear_apply, cotangentToDual_g0FlatCLM]
  exact metricInner_injective (I := I) g₀ x hkey

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma g0FlatCLM_inverseMetricSharpFib
    (g₀ : SmoothRiemannianMetric I M) (x : M) (θ : Tensor0SSpace 1 I x) :
    g0FlatCLM (I := I) g₀ x (inverseMetricSharpFib (I := I) g₀ x θ) = θ := by
  apply cotangentToDualLinear_injective (I := I) (x := x)
  rw [cotangentToDualLinear_apply, cotangentToDualLinear_apply]
  ext w
  rw [cotangentToDual_g0FlatCLM (I := I) g₀ x
    (inverseMetricSharpFib (I := I) g₀ x θ) w]
  rw [inverseMetricSharpFib_inner (I := I) g₀ x θ w]
  rw [cotangentToDualLinear_apply]

def metricComparisonDiffEndo (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x :=
  (inverseMetricSharpFib (I := I) g₁ x).comp (g0FlatCLM (I := I) g₀ x)
    - ContinuousLinearMap.id ℝ (TangentSpace I x)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma gInvDiffRaisedEndo_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (v : TangentSpace I x) :
    metricComparisonDiffEndo (I := I) g₀ g₁ x v =
      inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x v) - v := by
  rw [metricComparisonDiffEndo]
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma gInvDiffRaisedEndo_self (g₀ : SmoothRiemannianMetric I M) (x : M)
    (v : TangentSpace I x) :
    metricComparisonDiffEndo (I := I) g₀ g₀ x v = 0 := by
  rw [gInvDiffRaisedEndo_apply, inverseMetricSharpFib_g0FlatCLM, sub_self]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma gInvDiffRaisedEndo_eq_sharp_sub (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (v : TangentSpace I x) :
    metricComparisonDiffEndo (I := I) g₀ g₁ x v =
      inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x v)
        - inverseMetricSharpFib (I := I) g₀ x (g0FlatCLM (I := I) g₀ x v) := by
  rw [gInvDiffRaisedEndo_apply, inverseMetricSharpFib_g0FlatCLM]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma inner_g1_gInvDiffRaisedEndo (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    g₁.inner x (metricComparisonDiffEndo (I := I) g₀ g₁ x v) w =
      g₀.inner x v w - g₁.inner x v w := by
  rw [gInvDiffRaisedEndo_apply, map_sub, ContinuousLinearMap.sub_apply]
  rw [inverseMetricSharpFib_inner, cotangentToDualLinear_apply, cotangentToDual_g0FlatCLM]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [FiniteDimensional ℝ E] in
private lemma g1_self_lower_bound
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + h y v w)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) g₀ h δ)
    (x : M) (u : TangentSpace I x) :
    (1 - δ) * g₀.inner x u u ≤ g₁.inner x u u := by
  have hlb := perturbedInner_self_lower_bound (I := I) (M := M) g₀ h hδ x u
  rw [perturbedInner_apply] at hlb
  rw [htie x u u]
  exact hlb

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma sqrt_inner_gInvDiffRaisedEndo_le
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + h y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ) (hδ : metricCauchySchwarzBound (I := I) g₀ h δ)
    (x : M) (v : TangentSpace I x) :
    Real.sqrt (g₀.inner x (metricComparisonDiffEndo (I := I) g₀ g₁ x v)
        (metricComparisonDiffEndo (I := I) g₀ g₁ x v))
      ≤ (δ / (1 - δ)) * Real.sqrt (g₀.inner x v v) := by
  set Dv : TangentSpace I x := metricComparisonDiffEndo (I := I) g₀ g₁ x v with hDv
  set N : ℝ := Real.sqrt (g₀.inner x Dv Dv) with hN
  set Nv : ℝ := Real.sqrt (g₀.inner x v v) with hNv
  have hcoeff : 0 < 1 - δ := by linarith
  have hg0Dv_nn : 0 ≤ g₀.inner x Dv Dv := metric_inner_self_nonneg (I := I) (M := M) g₀ x Dv
  have hg0v_nn : 0 ≤ g₀.inner x v v := metric_inner_self_nonneg (I := I) (M := M) g₀ x v
  have hN_nn : 0 ≤ N := Real.sqrt_nonneg _
  have hNv_nn : 0 ≤ Nv := Real.sqrt_nonneg _
  have hN_sq : N * N = g₀.inner x Dv Dv := by
    rw [hN, ← Real.sqrt_mul hg0Dv_nn, Real.sqrt_mul_self hg0Dv_nn]

  have hg1Dv : g₁.inner x Dv Dv = -(h x v Dv) := by
    have hp := inner_g1_gInvDiffRaisedEndo (I := I) g₀ g₁ x v Dv
    rw [hDv] at hp ⊢
    rw [hp, htie x v Dv]; ring

  have hgate := hδ x v Dv
  have habs : |h x v Dv| ≤ δ * Nv * N := by
    rw [hNv, hN]; exact hgate
  have hg1Dv_le : g₁.inner x Dv Dv ≤ δ * Nv * N := by
    rw [hg1Dv]
    calc -(h x v Dv) ≤ |h x v Dv| := neg_le_abs _
      _ ≤ δ * Nv * N := habs

  have hlow := g1_self_lower_bound (I := I) g₀ g₁ h htie hδ x Dv

  have hkey : (1 - δ) * (N * N) ≤ δ * Nv * N := by
    rw [hN_sq]; exact le_trans hlow hg1Dv_le

  rcases eq_or_lt_of_le hN_nn with hN0 | hNpos
  · rw [← hN0]
    exact mul_nonneg (div_nonneg hδ_nn hcoeff.le) hNv_nn
  · have hNN : (1 - δ) * N ≤ δ * Nv := by
      have h1 : (1 - δ) * N * N ≤ δ * Nv * N := by nlinarith [hkey]
      exact le_of_mul_le_mul_right h1 hNpos
    rw [div_mul_eq_mul_div, le_div_iff₀ hcoeff]
    rw [mul_comm N (1 - δ)]; exact hNN

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma g0_cross_inverseMetricSharp_eq_g1
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (a b : TangentSpace I x) :
    g₀.inner x (inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x a)) b
      = g₁.inner x (inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x b))
            (inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x a)) := by
  rw [g₀.symm x _ b, ← cotangentToDual_g0FlatCLM (I := I) g₀ x b
    (inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x a)),
    inverseMetricSharpFib_inner, cotangentToDualLinear_apply]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem gInvDiffRaisedEndo_g0_self_adjoint (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    g₀.inner x (metricComparisonDiffEndo (I := I) g₀ g₁ x v) w
      = g₀.inner x v (metricComparisonDiffEndo (I := I) g₀ g₁ x w) := by
  rw [gInvDiffRaisedEndo_apply, gInvDiffRaisedEndo_apply, map_sub, map_sub,
    ContinuousLinearMap.sub_apply]
  have hcross :
      g₀.inner x (inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x v)) w
        = g₀.inner x v (inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x w)) := by
    rw [g0_cross_inverseMetricSharp_eq_g1 (I := I) g₀ g₁ x v w]
    rw [g₀.symm x v _, g0_cross_inverseMetricSharp_eq_g1 (I := I) g₀ g₁ x w v]
    exact g₁.symm x _ _
  rw [hcross]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem abs_sum_g0_inner_gInvDiffRaisedEndo_le
    {n : ℕ} (g₀ g₁ : SmoothRiemannianMetric I M)
    (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + h y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ) (hδ : metricCauchySchwarzBound (I := I) g₀ h δ)
    (x : M) (u v : Fin n → TangentSpace I x) :
    |∑ a, g₀.inner x (metricComparisonDiffEndo (I := I) g₀ g₁ x (u a)) (v a)|
      ≤ (δ / (1 - δ)) * Real.sqrt (∑ a, g₀.inner x (u a) (u a))
          * Real.sqrt (∑ a, g₀.inner x (v a) (v a)) := by
  classical
  set Λ : TangentSpace I x →L[ℝ] TangentSpace I x := metricComparisonDiffEndo (I := I) g₀ g₁ x with hΛ
  set κ : ℝ := δ / (1 - δ) with hκ_def
  have hκ : 0 ≤ κ := div_nonneg hδ_nn (by linarith)
  have hper : ∀ a, Real.sqrt (g₀.inner x (Λ (u a)) (Λ (u a)))
      ≤ κ * Real.sqrt (g₀.inner x (u a) (u a)) := by
    intro a
    have hsqrt := sqrt_inner_gInvDiffRaisedEndo_le (I := I) g₀ g₁ h htie hδ_lt hδ_nn hδ x (u a)
    rw [← hΛ, ← hκ_def] at hsqrt
    exact hsqrt
  set αu : Fin n → ℝ := fun a => Real.sqrt (g₀.inner x (u a) (u a)) with hαu
  set βv : Fin n → ℝ := fun a => Real.sqrt (g₀.inner x (v a) (v a)) with hβv
  have hαu_nn : ∀ a, 0 ≤ αu a := fun a => Real.sqrt_nonneg _
  have hβv_nn : ∀ a, 0 ≤ βv a := fun a => Real.sqrt_nonneg _
  have hterm : ∀ a, |g₀.inner x (Λ (u a)) (v a)| ≤ κ * αu a * βv a := by
    intro a
    have hCS := abs_metric_inner_le_sqrt_metric_quadratic (I := I) (M := M) g₀ x (Λ (u a)) (v a)
    have h1 : Real.sqrt (g₀.inner x (Λ (u a)) (Λ (u a))) * βv a ≤ (κ * αu a) * βv a :=
      mul_le_mul_of_nonneg_right (hper a) (hβv_nn a)
    calc |g₀.inner x (Λ (u a)) (v a)|
        ≤ Real.sqrt (g₀.inner x (Λ (u a)) (Λ (u a))) * βv a := hCS
      _ ≤ (κ * αu a) * βv a := h1
      _ = κ * αu a * βv a := by ring
  have hsum1 : |∑ a, g₀.inner x (Λ (u a)) (v a)| ≤ ∑ a, κ * αu a * βv a := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    exact Finset.sum_le_sum (fun a _ => hterm a)
  have hCSsum : (∑ a, αu a * βv a)
      ≤ Real.sqrt (∑ a, αu a ^ 2) * Real.sqrt (∑ a, βv a ^ 2) := by
    have hsq := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ αu βv
    have hL_nn : 0 ≤ ∑ a, αu a * βv a :=
      Finset.sum_nonneg (fun a _ => mul_nonneg (hαu_nn a) (hβv_nn a))
    have hA_nn : 0 ≤ ∑ a, αu a ^ 2 := Finset.sum_nonneg (fun a _ => sq_nonneg _)
    calc ∑ a, αu a * βv a
        = Real.sqrt ((∑ a, αu a * βv a) ^ 2) := (Real.sqrt_sq hL_nn).symm
      _ ≤ Real.sqrt ((∑ a, αu a ^ 2) * (∑ a, βv a ^ 2)) := Real.sqrt_le_sqrt hsq
      _ = Real.sqrt (∑ a, αu a ^ 2) * Real.sqrt (∑ a, βv a ^ 2) := Real.sqrt_mul hA_nn _
  have hαsq : (∑ a, αu a ^ 2) = ∑ a, g₀.inner x (u a) (u a) := by
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [hαu]; exact Real.sq_sqrt (metric_inner_self_nonneg (I := I) (M := M) g₀ x (u a))
  have hβsq : (∑ a, βv a ^ 2) = ∑ a, g₀.inner x (v a) (v a) := by
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [hβv]; exact Real.sq_sqrt (metric_inner_self_nonneg (I := I) (M := M) g₀ x (v a))
  calc |∑ a, g₀.inner x (Λ (u a)) (v a)|
      ≤ ∑ a, κ * αu a * βv a := hsum1
    _ = κ * ∑ a, αu a * βv a := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun a _ => by ring)
    _ ≤ κ * (Real.sqrt (∑ a, αu a ^ 2) * Real.sqrt (∑ a, βv a ^ 2)) :=
        mul_le_mul_of_nonneg_left hCSsum hκ
    _ = κ * Real.sqrt (∑ a, g₀.inner x (u a) (u a)) * Real.sqrt (∑ a, g₀.inner x (v a) (v a)) := by
        rw [hαsq, hβsq]; ring

omit [CompactSpace M] in

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem metricFlat_chartComponent_contMDiffOn (g₀ : SmoothRiemannianMetric I M)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (γ : M) (j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M => (g₀.inner b (Y b)).toLinearMap (chartBasisVecFiber (I := I) γ j b))
      (chartAt H γ).source := by
  have h_total : ContMDiffOn I (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun b : M => (⟨b, g₀.inner b (Y b) (chartBasisVecFiber (I := I) γ j b)⟩ :
        TotalSpace ℝ (Bundle.Trivial M ℝ)))
      (trivializationAt E (TangentSpace I) γ).baseSet :=
    ContMDiffOn.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ) (b := id)
      g₀.contMDiff.contMDiffOn Y.contMDiff.contMDiffOn
      (chartBasisVec_contMDiffOn (I := I) γ j)
  have hbase_eq :
      (trivializationAt E (TangentSpace I) γ).baseSet = (chartAt H γ).source :=
    trivializationAt_baseSet_eq_chartAt_source (I := I) γ
  rw [hbase_eq] at h_total
  intro b hb
  have hpb := h_total b hb
  rw [Bundle.contMDiffWithinAt_totalSpace] at hpb
  exact hpb.2

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma gInvDiffRaisedEndo_eq_metricSharp_flatDiff (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (v : TangentSpace I x) :
    metricComparisonDiffEndo (I := I) g₀ g₁ x v =
      DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I) g₁ x
        ((g₀.inner x v).toLinearMap - (g₁.inner x v).toLinearMap) := by
  rw [gInvDiffRaisedEndo_apply, inverseMetricSharpFib_g0FlatCLM_eq_metricSharp]

  have hv : DifferentialGeometry.Integral.DivergenceTheorem.metricSharp
      (I := I) g₁ x (g₁.inner x v).toLinearMap = v := by
    rw [← inverseMetricSharpFib_g0FlatCLM_eq_metricSharp (I := I) g₁ g₁ x v]
    exact inverseMetricSharpFib_g0FlatCLM (I := I) g₁ x v

  have hsharp_sub : DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I) g₁ x
        ((g₀.inner x v).toLinearMap - (g₁.inner x v).toLinearMap)
      = DifferentialGeometry.Integral.DivergenceTheorem.metricSharp
          (I := I) g₁ x (g₀.inner x v).toLinearMap
        - DifferentialGeometry.Integral.DivergenceTheorem.metricSharp
          (I := I) g₁ x (g₁.inner x v).toLinearMap := by
    rw [DifferentialGeometry.Integral.DivergenceTheorem.metricSharp_def,
      DifferentialGeometry.Integral.DivergenceTheorem.metricSharp_def,
      DifferentialGeometry.Integral.DivergenceTheorem.metricSharp_def, map_sub]
  rw [hsharp_sub, hv]

omit [CompactSpace M] in

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem metricFlatDiff_chartComponent_contMDiffOn (g₀ g₁ : SmoothRiemannianMetric I M)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (γ : M) (j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M => ((g₀.inner b (Y b)).toLinearMap - (g₁.inner b (Y b)).toLinearMap)
        (chartBasisVecFiber (I := I) γ j b))
      (chartAt H γ).source := by
  have h0 := metricFlat_chartComponent_contMDiffOn (I := I) g₀ Y γ j
  have h1 := metricFlat_chartComponent_contMDiffOn (I := I) g₁ Y γ j
  refine (h0.sub h1).congr ?_
  intro b hb
  rw [LinearMap.sub_apply]

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem gInvDiffRaisedEndo_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z) x
        (metricComparisonDiffEndo (I := I) g₀ g₁ x)) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := E) (V₁ := fun z : M => TangentSpace I z)
    (F₂ := E) (V₂ := fun z : M => TangentSpace I z)
    (φ := fun x => metricComparisonDiffEndo (I := I) g₀ g₁ x)
  intro Y
  have hsharpY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E
        (E := fun z : M => TangentSpace I z) b
        (DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I) g₁ b
          ((g₀.inner b (Y b)).toLinearMap - (g₁.inner b (Y b)).toLinearMap))) := by
    apply metricSharp_contMDiff_total (I := I) g₁
    intro γ j
    exact metricFlatDiff_chartComponent_contMDiffOn (I := I) g₀ g₁ Y γ j
  refine hsharpY.congr (fun x => ?_)
  rw [gInvDiffRaisedEndo_eq_metricSharp_flatDiff (I := I) g₀ g₁ x (Y x)]

set_option backward.isDefEq.respectTransparency false in

def metricComparisonDiffSlotEndo (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  slotInsertEndoFib (I := I) (M := M) 2 0 x (metricComparisonDiffEndo (I := I) g₀ g₁ x)

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem gInvDiffSlotEndo_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (metricComparisonDiffSlotEndo (I := I) g₀ g₁ x))) :=
  slotInsertEndoFib_contMDiff (I := I) (M := M) g₀ 2 0
    (fun x : M => metricComparisonDiffEndo (I := I) g₀ g₁ x)
    (gInvDiffRaisedEndo_contMDiff (I := I) g₀ g₁)

set_option backward.isDefEq.respectTransparency false in

def metricComparisonDiffFibreEndo (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    TensorRSSpace 0 2 I x →L[ℝ] TensorRSSpace 0 2 I x :=
  haveI : FiniteDimensional ℝ (TensorRSSpace 0 2 I x) :=
    inferInstanceAs (FiniteDimensional ℝ (Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x))
  haveI : T2Space (TensorRSSpace 0 2 I x) :=
    inferInstanceAs (T2Space (Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x))
  LinearMap.toContinuousLinearMap
    { toFun := fun v => (metricComparisonDiffSlotEndo (I := I) g₀ g₁ x).comp
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from v)
      map_add' := fun v v' => by
        rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from v + v') =
            (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from v) +
              (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from v') from rfl,
          ContinuousLinearMap.comp_add]
      map_smul' := fun c v => by
        rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from c • v) =
            c • (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from v) from rfl,
          ContinuousLinearMap.comp_smul]
        rfl }

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma gInvDiffFibreEndo_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (v : TensorRSSpace 0 2 I x) :
    metricComparisonDiffFibreEndo (I := I) g₀ g₁ x v =
      (metricComparisonDiffSlotEndo (I := I) g₀ g₁ x).comp
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from v) := by
  haveI : FiniteDimensional ℝ (TensorRSSpace 0 2 I x) :=
    inferInstanceAs (FiniteDimensional ℝ (Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x))
  haveI : T2Space (TensorRSSpace 0 2 I x) :=
    inferInstanceAs (T2Space (Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x))
  rw [metricComparisonDiffFibreEndo, LinearMap.coe_toContinuousLinearMap']
  rfl

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem gInvDiffFibreEndo_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 2 ℝ E →L[ℝ] TensorRSModel 0 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 0 2 ℝ E →L[ℝ] TensorRSModel 0 2 ℝ E)
        (E := fun z : M => TensorRSSpace 0 2 I z →L[ℝ] TensorRSSpace 0 2 I z) x
        (metricComparisonDiffFibreEndo (I := I) g₀ g₁ x)) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := TensorRSModel 0 2 ℝ E) (V₁ := fun z : M => TensorRSSpace 0 2 I z)
    (F₂ := TensorRSModel 0 2 ℝ E) (V₂ := fun z : M => TensorRSSpace 0 2 I z)
    (φ := fun x => metricComparisonDiffFibreEndo (I := I) g₀ g₁ x)
  intro Z
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SModel 0 ℝ E) (V₁ := fun z : M => Tensor0SSpace 0 I z)
    (F₂ := Tensor0SModel 2 ℝ E) (V₂ := fun z : M => Tensor0SSpace 2 I z)
    (φ := fun x => (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
      metricComparisonDiffFibreEndo (I := I) g₀ g₁ x (Z x)))
  intro ζ
  have hZinner : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from Z x) (ζ x))) :=
    ContMDiff.clm_bundle_apply (b := id) Z.contMDiff ζ.contMDiff
  have happ : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) x
        (metricComparisonDiffSlotEndo (I := I) g₀ g₁ x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from Z x) (ζ x)))) := by
    have hslot : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E →L[ℝ] Tensor0SModel 2 ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E →L[ℝ] Tensor0SModel 2 ℝ E)
          (E := fun z : M => Tensor0SSpace 2 I z →L[ℝ] Tensor0SSpace 2 I z) x
          (metricComparisonDiffSlotEndo (I := I) g₀ g₁ x)) :=
      gInvDiffSlotEndo_contMDiff (I := I) g₀ g₁
    exact ContMDiff.clm_bundle_apply (b := id) hslot hZinner
  refine happ.congr ?_
  intro x
  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
        metricComparisonDiffFibreEndo (I := I) g₀ g₁ x (Z x)) (ζ x) =
      metricComparisonDiffSlotEndo (I := I) g₀ g₁ x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from Z x) (ζ x)) from by
    rw [gInvDiffFibreEndo_apply, ContinuousLinearMap.comp_apply]]


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma exists_orthonormalFrame_fiberNormSq_rank22_repr (g₀ : SmoothRiemannianMetric I M) (x : M) :
    ∃ (n : ℕ) (e : Fin n → TangentSpace I x),
      n = Module.finrank ℝ (TangentSpace I x) ∧
      (∀ i j : Fin n, g₀.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0) ∧
      (∀ u : TangentSpace I x,
        ∑ b : Fin n, (g₀.inner x u (e b)) ^ 2 = g₀.inner x u u) ∧
      (∀ S : TensorRSSpace 2 2 I x,
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x S =
          ∑ K : Fin 2 → Fin n, ∑ J : Fin 2 → Fin n,
            fiberNormSqSummand (I := I) (M := M) g₀ x 2 2 S n e K J) := by
  classical
  let cd : InnerProductSpace.Core ℝ (TangentSpace I x) := g₀.toRiemannianMetric.toCore x
  have hc : ContinuousAt (fun v : TangentSpace I x => cd.inner v v) 0 :=
    g₀.toRiemannianMetric.continuousAt x
  have hbnd : Bornology.IsVonNBounded ℝ {v : TangentSpace I x |
      RCLike.re (cd.inner v v) < 1} :=
    g₀.toRiemannianMetric.isVonNBounded x
  letI nag : NormedAddCommGroup (TangentSpace I x) :=
    cd.toNormedAddCommGroupOfTopology hc hbnd
  letI ips : InnerProductSpace ℝ (TangentSpace I x) :=
    InnerProductSpace.ofCoreOfTopology cd hc hbnd
  set n : ℕ := Module.finrank ℝ (TangentSpace I x) with hn_def
  set eob : OrthonormalBasis (Fin n) ℝ (TangentSpace I x) := stdOrthonormalBasis ℝ _ with heob_def
  have hinner_eq : ∀ u v : TangentSpace I x, (inner ℝ u v : ℝ) = g₀.inner x u v :=
    fun u v => rfl
  refine ⟨n, fun i => eob i, rfl, ?_, ?_, ?_⟩
  · intro i j
    have horth : Orthonormal ℝ (fun i : Fin n => eob i) := eob.orthonormal
    have hite := (orthonormal_iff_ite (𝕜 := ℝ) (E := TangentSpace I x)).mp horth i j
    rw [← hinner_eq (eob i) (eob j)]; exact hite
  · intro u
    have hpar := eob.sum_inner_mul_inner u u
    rw [← hinner_eq u u, ← hpar]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [← hinner_eq u (eob b), sq, real_inner_comm (eob b) u]
  · intro S; rfl


private lemma slotInsert_sqsum_kroneckerDelta_eq_dim_mul_sqsum (n : ℕ) (f : Fin n → Fin n → ℝ) :
    (∑ K : Fin 2 → Fin n, ∑ J : Fin 2 → Fin n,
      (f (J 0) (K 0) * (if K 1 = J 1 then (1 : ℝ) else 0)) ^ 2)
      = (n : ℝ) * ∑ J : Fin 2 → Fin n, (f (J 0) (J 1)) ^ 2 := by
  classical
  have key : ∀ g : (Fin 2 → Fin n) → ℝ,
      (∑ p : Fin 2 → Fin n, g p) = ∑ a : Fin n, ∑ b : Fin n, g ![a, b] := by
    intro g
    rw [← (finTwoArrowEquiv (Fin n)).symm.sum_comp g, Fintype.sum_prod_type]; rfl
  have hL : (∑ K : Fin 2 → Fin n, ∑ J : Fin 2 → Fin n,
      (f (J 0) (K 0) * (if K 1 = J 1 then (1 : ℝ) else 0)) ^ 2)
      = ∑ k0 : Fin n, ∑ k1 : Fin n, ∑ j0 : Fin n, ∑ j1 : Fin n,
          (f j0 k0 * (if k1 = j1 then (1 : ℝ) else 0)) ^ 2 := by
    rw [key]
    refine Finset.sum_congr rfl (fun k0 _ => Finset.sum_congr rfl (fun k1 _ => ?_))
    rw [key]; rfl
  have hR : ((n : ℝ) * ∑ J : Fin 2 → Fin n, (f (J 0) (J 1)) ^ 2)
      = (n : ℝ) * ∑ j0 : Fin n, ∑ j1 : Fin n, (f j0 j1) ^ 2 := by
    rw [key]; rfl
  rw [hL, hR]
  have hcollapse : ∀ (a : ℝ) (k1 j1 : Fin n),
      (a * (if k1 = j1 then (1 : ℝ) else 0)) ^ 2 = a ^ 2 * (if k1 = j1 then (1 : ℝ) else 0) := by
    intro a k1 j1; by_cases h : k1 = j1 <;> simp [h]
  have step1 : ∑ k0 : Fin n, ∑ k1 : Fin n, ∑ j0 : Fin n, ∑ j1 : Fin n,
          (f j0 k0 * (if k1 = j1 then (1 : ℝ) else 0)) ^ 2
        = ∑ k0 : Fin n, ∑ j0 : Fin n, ∑ j1 : Fin n, (f j0 k0) ^ 2 := by
    refine Finset.sum_congr rfl (fun k0 _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j0 _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j1 _ => ?_)
    rw [Finset.sum_congr rfl (fun k1 _ => hcollapse (f j0 k0) k1 j1),
      ← Finset.mul_sum, Finset.sum_ite_eq' Finset.univ j1 (fun _ => (1 : ℝ))]
    simp
  rw [step1]
  have step2 : ∀ k0 j0 : Fin n, (∑ _j1 : Fin n, (f j0 k0) ^ 2) = (n : ℝ) * (f j0 k0) ^ 2 := by
    intro k0 j0; rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring
  rw [Finset.sum_congr rfl (fun k0 _ => Finset.sum_congr rfl (fun j0 _ => step2 k0 j0))]
  rw [Finset.mul_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j0 _ => ?_)
  rw [Finset.mul_sum]


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma slotEndo_fiberComponent_endo_eq (g₀ : SmoothRiemannianMetric I M) (x : M)
    (Λ : TangentSpace I x →L[ℝ] TangentSpace I x)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ i j : Fin n, g₀.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (K J : Fin 2 → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g₀ x 2 2
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) 2 0 x Λ)) n e K J =
      g₀.inner x (Λ (e (J 0))) (e (K 0)) * (if K 1 = J 1 then (1 : ℝ) else 0) := by
  have hcomp : fiberNormSqComponent (I := I) (M := M) g₀ x 2 2
      (show TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) 2 0 x Λ)) n e K J =
      Tensor0SSpace.toModel
        ((slotInsertEndoFib (I := I) (M := M) 2 0 x Λ) (coframeS (I := I) (M := M) g₀ x 2 e K))
        (fun k => e (J k)) := by
    unfold fiberNormSqComponent coframeS; rfl
  rw [hcomp, slotInsertEndoFib_apply_eval]
  rw [show (coframeS (I := I) (M := M) g₀ x 2 e K).toModel
        (Function.update (fun k => e (J k)) 0 (Λ (e (J 0))))
      = coframeS (I := I) (M := M) g₀ x 2 e K
        (Function.update (fun k => e (J k)) 0 (Λ (e (J 0)))) from rfl]
  rw [coframeS_apply, Fin.prod_univ_two, Function.update_self,
    Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0)]
  rw [g₀.symm x (e (K 0)) (Λ (e (J 0))), horth (K 1) (J 1)]


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma riemannianFiberNormSq_slotInsert_eq_dim_mul (g₀ : SmoothRiemannianMetric I M) (x : M)
    (Λ : TangentSpace I x →L[ℝ] TangentSpace I x) :
    ∃ (n : ℕ) (e : Fin n → TangentSpace I x),
      n = Module.finrank ℝ E ∧
      (∀ i j : Fin n, g₀.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0) ∧
      (∀ u : TangentSpace I x,
        ∑ b : Fin n, (g₀.inner x u (e b)) ^ 2 = g₀.inner x u u) ∧
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
          (show TensorRSSpace 2 2 I x from
            TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) 2 0 x Λ))
        = (n : ℝ) * ∑ J : Fin 2 → Fin n, (g₀.inner x (Λ (e (J 0))) (e (J 1))) ^ 2 := by
  obtain ⟨n, e, hn, horth, hpar, hrepr22⟩ := exists_orthonormalFrame_fiberNormSq_rank22_repr (I := I) g₀ x
  have hnE : n = Module.finrank ℝ E := by
    rw [hn]; rfl
  refine ⟨n, e, hnE, horth, hpar, ?_⟩
  have h22 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
      (show TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) 2 0 x Λ))
      = ∑ K : Fin 2 → Fin n, ∑ J : Fin 2 → Fin n,
          (fiberNormSqComponent (I := I) (M := M) g₀ x 2 2
            (show TensorRSSpace 2 2 I x from
              TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) 2 0 x Λ)) n e K J) ^ 2 :=
    riemannianFiberNormSq_eq_sum_componentRS_sq (I := I) (M := M) g₀ x 2 2 e hrepr22 _
  rw [h22]
  have h22' : (∑ K : Fin 2 → Fin n, ∑ J : Fin 2 → Fin n,
          (fiberNormSqComponent (I := I) (M := M) g₀ x 2 2
            (show TensorRSSpace 2 2 I x from
              TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) 2 0 x Λ)) n e K J) ^ 2)
      = ∑ K : Fin 2 → Fin n, ∑ J : Fin 2 → Fin n,
          (g₀.inner x (Λ (e (J 0))) (e (K 0)) *
            (if K 1 = J 1 then (1 : ℝ) else 0)) ^ 2 := by
    refine Finset.sum_congr rfl (fun K _ => Finset.sum_congr rfl (fun J _ => ?_))
    rw [slotEndo_fiberComponent_endo_eq (I := I) g₀ x Λ e horth K J]
  rw [h22',
    slotInsert_sqsum_kroneckerDelta_eq_dim_mul_sqsum n (fun a b => g₀.inner x (Λ (e a)) (e b))]


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem riemannianFiberNormSq_gInvDiffSlotEndo_le
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + h y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ) (hδ : metricCauchySchwarzBound (I := I) g₀ h δ)
    (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (metricComparisonDiffSlotEndo (I := I) g₀ g₁ x))
      ≤ ((Module.finrank ℝ E : ℝ) * (δ / (1 - δ))) ^ 2 := by
  classical
  set Λ : TangentSpace I x →L[ℝ] TangentSpace I x := metricComparisonDiffEndo (I := I) g₀ g₁ x with hΛ

  obtain ⟨n, e, hn, horth, hpar, heq⟩ :=
    riemannianFiberNormSq_slotInsert_eq_dim_mul (I := I) g₀ x Λ
  have hnE : (n : ℝ) = (Module.finrank ℝ E : ℝ) := by rw [hn]
  rw [show metricComparisonDiffSlotEndo (I := I) g₀ g₁ x = slotInsertEndoFib (I := I) (M := M) 2 0 x Λ from rfl, heq]
  set r : ℝ := δ / (1 - δ) with hr
  have hr_nn : 0 ≤ r := div_nonneg hδ_nn (by linarith)

  have hper : ∀ i : Fin n, g₀.inner x (Λ (e i)) (Λ (e i)) ≤ r ^ 2 := by
    intro i
    have hsqrt := sqrt_inner_gInvDiffRaisedEndo_le (I := I) g₀ g₁ h htie hδ_lt hδ_nn hδ x (e i)
    rw [← hΛ] at hsqrt
    have he1 : g₀.inner x (e i) (e i) = 1 := by rw [horth i i]; simp
    rw [he1, Real.sqrt_one, mul_one] at hsqrt
    have hLnn : 0 ≤ g₀.inner x (Λ (e i)) (Λ (e i)) :=
      metric_inner_self_nonneg (I := I) (M := M) g₀ x (Λ (e i))
    have hsq := Real.sq_sqrt hLnn
    nlinarith [Real.sqrt_nonneg (g₀.inner x (Λ (e i)) (Λ (e i))), hsqrt, hsq, hr_nn]

  have hJsplit : (∑ J : Fin 2 → Fin n, (g₀.inner x (Λ (e (J 0))) (e (J 1))) ^ 2)
      = ∑ a : Fin n, ∑ b : Fin n, (g₀.inner x (Λ (e a)) (e b)) ^ 2 := by
    rw [← (finTwoArrowEquiv (Fin n)).symm.sum_comp
      (fun J : Fin 2 → Fin n => (g₀.inner x (Λ (e (J 0))) (e (J 1))) ^ 2)]
    rw [Fintype.sum_prod_type]; rfl

  have hParseval : (∑ a : Fin n, ∑ b : Fin n, (g₀.inner x (Λ (e a)) (e b)) ^ 2)
      = ∑ a : Fin n, g₀.inner x (Λ (e a)) (Λ (e a)) :=
    Finset.sum_congr rfl (fun a _ => hpar (Λ (e a)))

  have hsum_le : (∑ a : Fin n, g₀.inner x (Λ (e a)) (Λ (e a))) ≤ (n : ℝ) * r ^ 2 := by
    calc (∑ a : Fin n, g₀.inner x (Λ (e a)) (Λ (e a)))
        ≤ ∑ _a : Fin n, r ^ 2 := Finset.sum_le_sum (fun a _ => hper a)
      _ = (n : ℝ) * r ^ 2 := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring

  rw [hJsplit, hParseval]
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  calc (n : ℝ) * (∑ a : Fin n, g₀.inner x (Λ (e a)) (Λ (e a)))
      ≤ (n : ℝ) * ((n : ℝ) * r ^ 2) := mul_le_mul_of_nonneg_left hsum_le hn_nn
    _ = ((Module.finrank ℝ E : ℝ) * r) ^ 2 := by rw [← hnE]; ring


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem exists_gInvDiffFibreEndo_neumannFibreBound
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ Cnorm : ℝ, 0 ≤ Cnorm ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ),
        (∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + h y v w) →
        ∀ {δ : ℝ}, δ < 1 / 2 → 0 ≤ δ → metricCauchySchwarzBound (I := I) g₀ h δ →
        ∀ (x : M) (v : TensorRSSpace 0 2 I x),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
              (metricComparisonDiffFibreEndo (I := I) g₀ g₁ x v) ≤
            (Cnorm * δ) ^ 2 *
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x v := by
  refine ⟨2 * (Module.finrank ℝ E : ℝ), by positivity, ?_⟩
  intro g₁ h htie δ hδ_half hδ_nn hδ x v
  have hδ_lt1 : δ < 1 := by linarith

  rw [gInvDiffFibreEndo_apply]

  have hcomp := riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ 0 2 2 x
    (show TensorRSSpace 2 2 I x from TensorRSSpace.ofCLM (metricComparisonDiffSlotEndo (I := I) g₀ g₁ x))
    (show TensorRSSpace 0 2 I x from v)
  have hslotcomp :
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          (show TensorRSSpace 2 2 I x from
            TensorRSSpace.ofCLM (metricComparisonDiffSlotEndo (I := I) g₀ g₁ x))).comp
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
            (show TensorRSSpace 0 2 I x from v)) =
        (metricComparisonDiffSlotEndo (I := I) g₀ g₁ x).comp
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from v) := by
    rfl
  rw [hslotcomp] at hcomp

  have hslot_le := riemannianFiberNormSq_gInvDiffSlotEndo_le (I := I) g₀ g₁ h htie hδ_lt1 hδ_nn hδ x
  have hv_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x v :=
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 2 x v

  have hcoeff : 0 < 1 - δ := by linarith
  have hslot_le' : riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (metricComparisonDiffSlotEndo (I := I) g₀ g₁ x))
      ≤ ((2 * (Module.finrank ℝ E : ℝ)) * δ) ^ 2 := by
    refine hslot_le.trans ?_

    have hdimnn : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
    have hbase_nn : 0 ≤ (Module.finrank ℝ E : ℝ) * (δ / (1 - δ)) :=
      mul_nonneg hdimnn (div_nonneg hδ_nn hcoeff.le)
    have hratio : δ / (1 - δ) ≤ 2 * δ := by
      rw [div_le_iff₀ hcoeff]
      nlinarith [hδ_half, hδ_nn]
    have hbase_le : (Module.finrank ℝ E : ℝ) * (δ / (1 - δ))
        ≤ (2 * (Module.finrank ℝ E : ℝ)) * δ := by
      calc (Module.finrank ℝ E : ℝ) * (δ / (1 - δ))
          ≤ (Module.finrank ℝ E : ℝ) * (2 * δ) :=
            mul_le_mul_of_nonneg_left hratio hdimnn
        _ = (2 * (Module.finrank ℝ E : ℝ)) * δ := by ring
    exact pow_le_pow_left₀ hbase_nn hbase_le 2
  calc riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
          ((metricComparisonDiffSlotEndo (I := I) g₀ g₁ x).comp
            (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from v))
      ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
            (show TensorRSSpace 2 2 I x from
              TensorRSSpace.ofCLM (metricComparisonDiffSlotEndo (I := I) g₀ g₁ x)) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x v := hcomp
    _ ≤ ((2 * (Module.finrank ℝ E : ℝ)) * δ) ^ 2 *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x v :=
        mul_le_mul_of_nonneg_right hslot_le' hv_nn

def metricComparisonEndo (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x :=
  (inverseMetricSharpFib (I := I) g₁ x).comp (g0FlatCLM (I := I) g₀ x)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma gInvRaisedEndo_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (v : TangentSpace I x) :
    metricComparisonEndo (I := I) g₀ g₁ x v =
      inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x v) := by
  rw [metricComparisonEndo, ContinuousLinearMap.comp_apply]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma gInvRaisedEndo_eq_diff_add_id (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (v : TangentSpace I x) :
    metricComparisonEndo (I := I) g₀ g₁ x v = metricComparisonDiffEndo (I := I) g₀ g₁ x v + v := by
  rw [gInvRaisedEndo_apply, gInvDiffRaisedEndo_apply, sub_add_cancel]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem sqrt_inner_gInvRaisedEndo_le
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + h y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ) (hδ : metricCauchySchwarzBound (I := I) g₀ h δ)
    (x : M) (v : TangentSpace I x) :
    Real.sqrt (g₀.inner x (metricComparisonEndo (I := I) g₀ g₁ x v)
        (metricComparisonEndo (I := I) g₀ g₁ x v))
      ≤ (1 / (1 - δ)) * Real.sqrt (g₀.inner x v v) := by
  have hcoeff : 0 < 1 - δ := by linarith
  rw [gInvRaisedEndo_eq_diff_add_id]
  set Dv : TangentSpace I x := metricComparisonDiffEndo (I := I) g₀ g₁ x v with hDv
  set Nv : ℝ := Real.sqrt (g₀.inner x v v) with hNv
  have hNv_nn : 0 ≤ Nv := Real.sqrt_nonneg _
  have haa_nn : 0 ≤ g₀.inner x Dv Dv := metric_inner_self_nonneg (I := I) (M := M) g₀ x Dv
  have hbb_nn : 0 ≤ g₀.inner x v v := metric_inner_self_nonneg (I := I) (M := M) g₀ x v
  have hsum_nn : 0 ≤ g₀.inner x (Dv + v) (Dv + v) :=
    metric_inner_self_nonneg (I := I) (M := M) g₀ x (Dv + v)
  have hND_nn : 0 ≤ Real.sqrt (g₀.inner x Dv Dv) := Real.sqrt_nonneg _
  have hND_sq : (Real.sqrt (g₀.inner x Dv Dv)) ^ 2 = g₀.inner x Dv Dv :=
    Real.sq_sqrt haa_nn
  have hNv_sq : Nv ^ 2 = g₀.inner x v v := by rw [hNv, Real.sq_sqrt hbb_nn]
  have hcross : g₀.inner x Dv v ≤ Real.sqrt (g₀.inner x Dv Dv) * Nv := by
    have habs := abs_metric_inner_le_sqrt_metric_quadratic (I := I) (M := M) g₀ x Dv v
    rw [← hNv] at habs
    exact le_trans (le_abs_self _) habs
  have hexpand : g₀.inner x (Dv + v) (Dv + v) =
      g₀.inner x Dv Dv + 2 * g₀.inner x Dv v + g₀.inner x v v := by
    have h1 : g₀.inner x (Dv + v) (Dv + v)
        = g₀.inner x Dv (Dv + v) + g₀.inner x v (Dv + v) := by
      rw [map_add (g₀.inner x), ContinuousLinearMap.add_apply]
    have h2 : g₀.inner x Dv (Dv + v) = g₀.inner x Dv Dv + g₀.inner x Dv v :=
      map_add (g₀.inner x Dv) Dv v
    have h3 : g₀.inner x v (Dv + v) = g₀.inner x v Dv + g₀.inner x v v :=
      map_add (g₀.inner x v) Dv v
    have h4 : g₀.inner x v Dv = g₀.inner x Dv v := g₀.symm x v Dv
    rw [h1, h2, h3, h4]; ring
  have htri : Real.sqrt (g₀.inner x (Dv + v) (Dv + v)) ≤
      Real.sqrt (g₀.inner x Dv Dv) + Nv := by
    have hsum_pos_nn : 0 ≤ Real.sqrt (g₀.inner x Dv Dv) + Nv := add_nonneg hND_nn hNv_nn
    have hle_sq : g₀.inner x (Dv + v) (Dv + v) ≤ (Real.sqrt (g₀.inner x Dv Dv) + Nv) ^ 2 := by
      rw [hexpand]
      have hexp2 : (Real.sqrt (g₀.inner x Dv Dv) + Nv) ^ 2 =
          (Real.sqrt (g₀.inner x Dv Dv)) ^ 2 + 2 * (Real.sqrt (g₀.inner x Dv Dv) * Nv) + Nv ^ 2 := by
        ring
      rw [hexp2, hND_sq, hNv_sq]
      nlinarith [hcross]
    calc Real.sqrt (g₀.inner x (Dv + v) (Dv + v))
        ≤ Real.sqrt ((Real.sqrt (g₀.inner x Dv Dv) + Nv) ^ 2) := Real.sqrt_le_sqrt hle_sq
      _ = Real.sqrt (g₀.inner x Dv Dv) + Nv := by rw [Real.sqrt_sq hsum_pos_nn]
  have hdiff := sqrt_inner_gInvDiffRaisedEndo_le (I := I) g₀ g₁ h htie hδ_lt hδ_nn hδ x v
  rw [← hDv, ← hNv] at hdiff
  calc Real.sqrt (g₀.inner x (Dv + v) (Dv + v))
      ≤ Real.sqrt (g₀.inner x Dv Dv) + Nv := htri
    _ ≤ (δ / (1 - δ)) * Nv + Nv := by linarith [hdiff]
    _ = (1 / (1 - δ)) * Nv := by
        have hne : (1 - δ) ≠ 0 := ne_of_gt hcoeff
        field_simp
        ring

set_option backward.isDefEq.respectTransparency false in

def gInvSlotEndo (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  slotInsertEndoFib (I := I) (M := M) 2 0 x (metricComparisonEndo (I := I) g₀ g₁ x)

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem gInvSlotEndo_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (gInvSlotEndo (I := I) g₀ g₁ x))) := by
  apply slotInsertEndoFib_contMDiff (I := I) (M := M) g₀ 2 0
    (fun x : M => metricComparisonEndo (I := I) g₀ g₁ x)
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := E) (V₁ := fun z : M => TangentSpace I z)
    (F₂ := E) (V₂ := fun z : M => TangentSpace I z)
    (φ := fun x => metricComparisonEndo (I := I) g₀ g₁ x)
  intro Y
  have hsharpY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E
        (E := fun z : M => TangentSpace I z) b
        (DifferentialGeometry.Integral.DivergenceTheorem.metricSharp
          (I := I) g₁ b (g₀.inner b (Y b)).toLinearMap)) := by
    apply metricSharp_contMDiff_total (I := I) g₁
    intro γ j
    exact metricFlat_chartComponent_contMDiffOn (I := I) g₀ Y γ j
  refine hsharpY.congr (fun x => ?_)
  rw [gInvRaisedEndo_apply, inverseMetricSharpFib_g0FlatCLM_eq_metricSharp]


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem riemannianFiberNormSq_gInvSlotEndo_le
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + h y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ) (hδ : metricCauchySchwarzBound (I := I) g₀ h δ)
    (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (gInvSlotEndo (I := I) g₀ g₁ x))
      ≤ ((Module.finrank ℝ E : ℝ) * (1 / (1 - δ))) ^ 2 := by
  classical
  set Λ : TangentSpace I x →L[ℝ] TangentSpace I x := metricComparisonEndo (I := I) g₀ g₁ x with hΛ
  obtain ⟨n, e, hn, horth, hpar, heq⟩ :=
    riemannianFiberNormSq_slotInsert_eq_dim_mul (I := I) g₀ x Λ
  have hnE : (n : ℝ) = (Module.finrank ℝ E : ℝ) := by rw [hn]
  rw [show gInvSlotEndo (I := I) g₀ g₁ x = slotInsertEndoFib (I := I) (M := M) 2 0 x Λ from rfl, heq]
  set r : ℝ := 1 / (1 - δ) with hr
  have hcoeff : 0 < 1 - δ := by linarith
  have hr_nn : 0 ≤ r := by rw [hr]; positivity
  have hper : ∀ i : Fin n, g₀.inner x (Λ (e i)) (Λ (e i)) ≤ r ^ 2 := by
    intro i
    have hsqrt := sqrt_inner_gInvRaisedEndo_le (I := I) g₀ g₁ h htie hδ_lt hδ_nn hδ x (e i)
    rw [← hΛ] at hsqrt
    have he1 : g₀.inner x (e i) (e i) = 1 := by rw [horth i i]; simp
    rw [he1, Real.sqrt_one, mul_one] at hsqrt
    have hLnn : 0 ≤ g₀.inner x (Λ (e i)) (Λ (e i)) :=
      metric_inner_self_nonneg (I := I) (M := M) g₀ x (Λ (e i))
    have hsq := Real.sq_sqrt hLnn
    nlinarith [Real.sqrt_nonneg (g₀.inner x (Λ (e i)) (Λ (e i))), hsqrt, hsq, hr_nn]
  have hJsplit : (∑ J : Fin 2 → Fin n, (g₀.inner x (Λ (e (J 0))) (e (J 1))) ^ 2)
      = ∑ a : Fin n, ∑ b : Fin n, (g₀.inner x (Λ (e a)) (e b)) ^ 2 := by
    rw [← (finTwoArrowEquiv (Fin n)).symm.sum_comp
      (fun J : Fin 2 → Fin n => (g₀.inner x (Λ (e (J 0))) (e (J 1))) ^ 2)]
    rw [Fintype.sum_prod_type]; rfl
  have hParseval : (∑ a : Fin n, ∑ b : Fin n, (g₀.inner x (Λ (e a)) (e b)) ^ 2)
      = ∑ a : Fin n, g₀.inner x (Λ (e a)) (Λ (e a)) :=
    Finset.sum_congr rfl (fun a _ => hpar (Λ (e a)))
  have hsum_le : (∑ a : Fin n, g₀.inner x (Λ (e a)) (Λ (e a))) ≤ (n : ℝ) * r ^ 2 := by
    calc (∑ a : Fin n, g₀.inner x (Λ (e a)) (Λ (e a)))
        ≤ ∑ _a : Fin n, r ^ 2 := Finset.sum_le_sum (fun a _ => hper a)
      _ = (n : ℝ) * r ^ 2 := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring
  rw [hJsplit, hParseval]
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  calc (n : ℝ) * (∑ a : Fin n, g₀.inner x (Λ (e a)) (Λ (e a)))
      ≤ (n : ℝ) * ((n : ℝ) * r ^ 2) := mul_le_mul_of_nonneg_left hsum_le hn_nn
    _ = ((Module.finrank ℝ E : ℝ) * r) ^ 2 := by rw [← hnE]; ring
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma inner_sharp_mixed (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) (v : TangentSpace I x) :
    g₀.inner x (inverseMetricSharpFib (I := I) g₁ x om) v =
      cotangentToDual (I := I) (x := x) om (metricComparisonEndo (I := I) g₀ g₁ x v) := by
  rw [show cotangentToDual (I := I) (x := x) om (metricComparisonEndo (I := I) g₀ g₁ x v) =
      cotangentToDualLinear (I := I) (x := x) om
        (metricComparisonEndo (I := I) g₀ g₁ x v) from rfl]
  rw [← inverseMetricSharpFib_inner (I := I) g₁ x om
    (metricComparisonEndo (I := I) g₀ g₁ x v)]
  rw [g₁.symm x (inverseMetricSharpFib (I := I) g₁ x om)
    (metricComparisonEndo (I := I) g₀ g₁ x v)]
  rw [gInvRaisedEndo_apply]
  rw [inverseMetricSharpFib_inner (I := I) g₁ x
    (g0FlatCLM (I := I) g₀ x v) (inverseMetricSharpFib (I := I) g₁ x om)]
  rw [cotangentToDualLinear_apply, cotangentToDual_g0FlatCLM]
  rw [g₀.symm x v (inverseMetricSharpFib (I := I) g₁ x om)]


end DifferentialGeometry.Analysis.Sobolev.TensorHilbert

end
