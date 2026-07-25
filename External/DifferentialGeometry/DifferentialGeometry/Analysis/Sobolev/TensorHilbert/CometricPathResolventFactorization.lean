import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CometricInverseDifferenceMultiplier

noncomputable section

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.Analysis.Sobolev.TensorHilbert

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Analysis.Laplacian

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem sqrt_inner_gInvDiffRaisedEndo_sub_le
    (g₀ ga gb : SmoothRiemannianMetric I M)
    (ha hb : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie_a : ∀ (y : M) (v w : TangentSpace I y),
      ga.inner y v w = g₀.inner y v w + ha y v w)
    (htie_b : ∀ (y : M) (v w : TangentSpace I y),
      gb.inner y v w = g₀.inner y v w + hb y v w)
    {δa δb δab : ℝ} (hδa_lt : δa < 1) (hδa : metricCauchySchwarzBound (I := I) g₀ ha δa)
    (hδb_lt : δb < 1) (hδb_nn : 0 ≤ δb) (hδb : metricCauchySchwarzBound (I := I) g₀ hb δb)
    (hδab_nn : 0 ≤ δab)
    (hδab : metricCauchySchwarzBound (I := I) g₀ (fun y => ha y - hb y) δab)
    (x : M) (v : TangentSpace I x) :
    Real.sqrt (g₀.inner x
        (metricComparisonDiffEndo (I := I) g₀ ga x v - metricComparisonDiffEndo (I := I) g₀ gb x v)
        (metricComparisonDiffEndo (I := I) g₀ ga x v - metricComparisonDiffEndo (I := I) g₀ gb x v)) ≤
      (δab / ((1 - δa) * (1 - δb))) * Real.sqrt (g₀.inner x v v) := by
  classical
  have hcoeff_a : 0 < 1 - δa := by linarith
  have hcoeff_b : 0 < 1 - δb := by linarith
  set Da : TangentSpace I x := metricComparisonDiffEndo (I := I) g₀ ga x v with hDa
  set Db : TangentSpace I x := metricComparisonDiffEndo (I := I) g₀ gb x v with hDb
  set z : TangentSpace I x := Da - Db with hz
  set N : ℝ := Real.sqrt (g₀.inner x z z) with hN
  set Nv : ℝ := Real.sqrt (g₀.inner x v v) with hNv
  have hg0z_nn : 0 ≤ g₀.inner x z z := metric_inner_self_nonneg (I := I) (M := M) g₀ x z
  have hg0v_nn : 0 ≤ g₀.inner x v v := metric_inner_self_nonneg (I := I) (M := M) g₀ x v
  have hN_nn : 0 ≤ N := Real.sqrt_nonneg _
  have hNv_nn : 0 ≤ Nv := Real.sqrt_nonneg _
  have hN_sq : N * N = g₀.inner x z z := by
    rw [hN, ← Real.sqrt_mul hg0z_nn, Real.sqrt_mul_self hg0z_nn]
  have h_ga_Da : ∀ w : TangentSpace I x, ga.inner x Da w = -(ha x v w) := by
    intro w
    rw [hDa, inner_g1_gInvDiffRaisedEndo (I := I) g₀ ga x v w, htie_a x v w]
    ring
  have h_gb_Db : ∀ w : TangentSpace I x, gb.inner x Db w = -(hb x v w) := by
    intro w
    rw [hDb, inner_g1_gInvDiffRaisedEndo (I := I) g₀ gb x v w, htie_b x v w]
    ring
  have h_g0_Db : ∀ w : TangentSpace I x,
      g₀.inner x Db w = -(hb x v w) - hb x Db w := by
    intro w
    have h1 := h_gb_Db w
    rw [htie_b x Db w] at h1
    linarith
  have h_ga_Db : ∀ w : TangentSpace I x,
      ga.inner x Db w = -(hb x v w) - hb x Db w + ha x Db w := by
    intro w
    rw [htie_a x Db w, h_g0_Db w]
  have h_ga_zz : ga.inner x z z =
      -((ha x (Db + v) z - hb x (Db + v) z)) := by
    have hsub : ga.inner x z z = ga.inner x Da z - ga.inner x Db z := by
      rw [hz]
      rw [map_sub (ga.inner x) Da Db, ContinuousLinearMap.sub_apply]
    rw [hsub, h_ga_Da z, h_ga_Db z]
    have hha : ha x (Db + v) z = ha x Db z + ha x v z := by
      rw [map_add (ha x) Db v, ContinuousLinearMap.add_apply]
    have hhb : hb x (Db + v) z = hb x Db z + hb x v z := by
      rw [map_add (hb x) Db v, ContinuousLinearMap.add_apply]
    rw [hha, hhb]
    ring
  have hraised : Db + v = metricComparisonEndo (I := I) g₀ gb x v := by
    rw [hDb, gInvRaisedEndo_eq_diff_add_id (I := I) g₀ gb x v]
  have hbound_rb : Real.sqrt (g₀.inner x (Db + v) (Db + v)) ≤ (1 / (1 - δb)) * Nv := by
    rw [hraised, hNv]
    exact sqrt_inner_gInvRaisedEndo_le (I := I) g₀ gb hb htie_b hδb_lt hδb_nn hδb x v
  have habs : |ha x (Db + v) z - hb x (Db + v) z| ≤
      δab * Real.sqrt (g₀.inner x (Db + v) (Db + v)) * N := by
    have h := hδab x (Db + v) z
    have happ : (fun y => ha y - hb y) x (Db + v) z =
        ha x (Db + v) z - hb x (Db + v) z := by
      rw [show (fun y => ha y - hb y) x = ha x - hb x from rfl,
        ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply]
    rw [happ] at h
    rw [hN]
    exact h
  have h_ga_zz_le : ga.inner x z z ≤ δab * ((1 / (1 - δb)) * Nv) * N := by
    calc ga.inner x z z = -((ha x (Db + v) z - hb x (Db + v) z)) := h_ga_zz
      _ ≤ |ha x (Db + v) z - hb x (Db + v) z| := neg_le_abs _
      _ ≤ δab * Real.sqrt (g₀.inner x (Db + v) (Db + v)) * N := habs
      _ ≤ δab * ((1 / (1 - δb)) * Nv) * N := by
          refine mul_le_mul_of_nonneg_right ?_ hN_nn
          exact mul_le_mul_of_nonneg_left hbound_rb hδab_nn
  have hlow : (1 - δa) * g₀.inner x z z ≤ ga.inner x z z := by
    have h := perturbedInner_self_lower_bound (I := I) (M := M) g₀ ha hδa x z
    rw [perturbedInner_apply] at h
    rw [htie_a x z z]
    exact h
  have hkey : (1 - δa) * (N * N) ≤ δab * ((1 / (1 - δb)) * Nv) * N := by
    rw [hN_sq]
    exact le_trans hlow h_ga_zz_le
  rcases eq_or_lt_of_le hN_nn with hN0 | hNpos
  · rw [← hN0]
    have : 0 ≤ δab / ((1 - δa) * (1 - δb)) := by positivity
    exact mul_nonneg this hNv_nn
  · have hNN : (1 - δa) * N ≤ δab * ((1 / (1 - δb)) * Nv) := by
      have h1 : (1 - δa) * N * N ≤ δab * ((1 / (1 - δb)) * Nv) * N := by
        nlinarith [hkey]
      exact le_of_mul_le_mul_right h1 hNpos
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0:ℝ) < (1 - δa) * (1 - δb))]
    have hexpand : N * ((1 - δa) * (1 - δb)) = ((1 - δa) * N) * (1 - δb) := by ring
    rw [hexpand]
    calc ((1 - δa) * N) * (1 - δb) ≤ (δab * ((1 / (1 - δb)) * Nv)) * (1 - δb) :=
          mul_le_mul_of_nonneg_right hNN hcoeff_b.le
      _ = δab * Nv := by field_simp

end DifferentialGeometry.Analysis.Sobolev.TensorHilbert

end
