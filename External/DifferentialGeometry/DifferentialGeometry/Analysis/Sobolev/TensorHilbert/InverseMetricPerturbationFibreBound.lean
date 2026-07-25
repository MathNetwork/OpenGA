import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CometricInverseDifferenceMultiplier


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

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [FiniteDimensional ℝ E] in
private lemma sqrt_g0_inner_add_le
    (g₀ : SmoothRiemannianMetric I M) (x : M) (a b : TangentSpace I x) :
    Real.sqrt (g₀.inner x (a + b) (a + b)) ≤
      Real.sqrt (g₀.inner x a a) + Real.sqrt (g₀.inner x b b) := by
  set na := Real.sqrt (g₀.inner x a a) with hna
  set nb := Real.sqrt (g₀.inner x b b) with hnb
  have haa_nn : 0 ≤ g₀.inner x a a := metric_inner_self_nonneg (I := I) (M := M) g₀ x a
  have hbb_nn : 0 ≤ g₀.inner x b b := metric_inner_self_nonneg (I := I) (M := M) g₀ x b
  have hsum_nn : 0 ≤ g₀.inner x (a + b) (a + b) :=
    metric_inner_self_nonneg (I := I) (M := M) g₀ x (a + b)
  have hna_nn : 0 ≤ na := Real.sqrt_nonneg _
  have hnb_nn : 0 ≤ nb := Real.sqrt_nonneg _
  have hna_sq : na ^ 2 = g₀.inner x a a := by rw [hna, Real.sq_sqrt haa_nn]
  have hnb_sq : nb ^ 2 = g₀.inner x b b := by rw [hnb, Real.sq_sqrt hbb_nn]
  have hcross : g₀.inner x a b ≤ na * nb := by
    have habs := abs_metric_inner_le_sqrt_metric_quadratic (I := I) (M := M) g₀ x a b
    rw [← hna, ← hnb] at habs
    exact le_trans (le_abs_self _) habs
  have hexpand : g₀.inner x (a + b) (a + b) =
      g₀.inner x a a + 2 * g₀.inner x a b + g₀.inner x b b := by
    have h1 : g₀.inner x (a + b) (a + b)
        = g₀.inner x a (a + b) + g₀.inner x b (a + b) := by
      rw [map_add (g₀.inner x), ContinuousLinearMap.add_apply]
    have h2 : g₀.inner x a (a + b) = g₀.inner x a a + g₀.inner x a b :=
      map_add (g₀.inner x a) a b
    have h3 : g₀.inner x b (a + b) = g₀.inner x b a + g₀.inner x b b :=
      map_add (g₀.inner x b) a b
    have h4 : g₀.inner x b a = g₀.inner x a b := g₀.symm x b a
    rw [h1, h2, h3, h4]; ring
  have hle_sq : g₀.inner x (a + b) (a + b) ≤ (na + nb) ^ 2 := by
    rw [hexpand]
    have : (na + nb) ^ 2 = na ^ 2 + 2 * (na * nb) + nb ^ 2 := by ring
    rw [this, hna_sq, hnb_sq]
    nlinarith [hcross]
  have hsum_pos_nn : 0 ≤ na + nb := add_nonneg hna_nn hnb_nn
  calc Real.sqrt (g₀.inner x (a + b) (a + b))
      ≤ Real.sqrt ((na + nb) ^ 2) := Real.sqrt_le_sqrt hle_sq
    _ = na + nb := by rw [Real.sqrt_sq hsum_pos_nn]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem norm_inverseMetricSharpFib_g0Flat_le
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + h y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ) (hδ : metricCauchySchwarzBound (I := I) g₀ h δ)
    (x : M) (v : TangentSpace I x) :
    Real.sqrt (g₀.inner x
        (inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x v))
        (inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x v)))
      ≤ (1 / (1 - δ)) * Real.sqrt (g₀.inner x v v) := by
  have hcoeff : 0 < 1 - δ := by linarith
  have hsplit :
      inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x v)
        = metricComparisonDiffEndo (I := I) g₀ g₁ x v + v := by
    rw [gInvDiffRaisedEndo_apply, sub_add_cancel]
  rw [hsplit]
  set Dv : TangentSpace I x := metricComparisonDiffEndo (I := I) g₀ g₁ x v with hDv
  have htri := sqrt_g0_inner_add_le (I := I) (M := M) g₀ x Dv v
  have hdiff := sqrt_inner_gInvDiffRaisedEndo_le (I := I) g₀ g₁ h htie hδ_lt hδ_nn hδ x v
  rw [← hDv] at hdiff
  set Nv : ℝ := Real.sqrt (g₀.inner x v v) with hNv
  have hNv_nn : 0 ≤ Nv := Real.sqrt_nonneg _
  calc Real.sqrt (g₀.inner x (Dv + v) (Dv + v))
      ≤ Real.sqrt (g₀.inner x Dv Dv) + Nv := htri
    _ ≤ (δ / (1 - δ)) * Nv + Nv := by linarith [hdiff]
    _ = (1 / (1 - δ)) * Nv := by
        have hne : (1 - δ) ≠ 0 := ne_of_gt hcoeff
        field_simp
        ring

end DifferentialGeometry.Analysis.Sobolev.TensorHilbert

end
