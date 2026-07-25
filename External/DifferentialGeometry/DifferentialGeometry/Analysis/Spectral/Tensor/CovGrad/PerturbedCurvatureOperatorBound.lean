import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifference
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceJetTower
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.RicciTraceCarrier
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.UniformRiemannOperatorNormBound
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ConnectionDifferenceCurvature
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.PerturbedRiemannOpDifferenceBound
import DifferentialGeometry.Geometry.Curvature.Bochner.OrthonormalFrameTrace
import DifferentialGeometry.Geometry.Connection.ChartFrame.RicciIdentitySmoothFrame
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.PerturbedInnerUpperBound
import DifferentialGeometry.Geometry.Metric.MetricBounds


noncomputable section

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Geometry
namespace Curvature

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem gZeroInner_self_le_of_g1_self_le
    (g₀ g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    {δ : ℝ}
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
    (htie : ∀ (x : M) (v w : TangentSpace I x),
      g₁.inner x v w = g₀.inner x v w +
        ccTensorBilinSymm (I := I) g₀ P x v w)
    (x : M) (v : TangentSpace I x) {c : ℝ} (hc : g₁.inner x v v ≤ c) :
    (1 - δ) * g₀.inner x v v ≤ c := by
  have hlb := perturbedInner_self_lower_bound (I := I) (M := M) g₀
    (ccTensorBilinSymm (I := I) g₀ P) hδ x v
  rw [perturbedInner_apply] at hlb
  rw [← htie x v v] at hlb
  linarith

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem gZeroInner_self_le_neumann_of_g1_unit
    (g₀ g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
    (htie : ∀ (x : M) (v w : TangentSpace I x),
      g₁.inner x v w = g₀.inner x v w +
        ccTensorBilinSymm (I := I) g₀ P x v w)
    (x : M) (v : TangentSpace I x) (hunit : g₁.inner x v v = 1) :
    g₀.inner x v v ≤ (1 - δ)⁻¹ := by
  have hcoeff : 0 < 1 - δ := by linarith
  have hkey := gZeroInner_self_le_of_g1_self_le (I := I) (M := M) g₀ g₁ P hδ htie x v
    (le_of_eq hunit)
  rw [show (1 - δ)⁻¹ = 1 / (1 - δ) from (one_div _).symm, le_div_iff₀ hcoeff]
  linarith

private lemma inv_le_inv_of_le_of_pos {a b : ℝ} (hb : 0 < b) (hab : b ≤ a) :
    a⁻¹ ≤ b⁻¹ := by
  have ha : 0 < a := lt_of_lt_of_le hb hab
  rw [inv_le_inv₀ ha hb]; exact hab

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
omit [FiniteDimensional ℝ E] in
private lemma gNorm_triangle
    (g : SmoothRiemannianMetric I M) (x : M) (a b : TangentSpace I x) :
    Real.sqrt (g.inner x (a + b) (a + b)) ≤
      Real.sqrt (g.inner x a a) + Real.sqrt (g.inner x b b) := by
  have haa : 0 ≤ g.inner x a a := metric_inner_self_nonneg (I := I) (M := M) g x a
  have hbb : 0 ≤ g.inner x b b := metric_inner_self_nonneg (I := I) (M := M) g x b
  have hcs : g.inner x a b ≤ Real.sqrt (g.inner x a a) * Real.sqrt (g.inner x b b) := by
    refine le_trans (le_abs_self _) ?_
    exact abs_metric_inner_le_sqrt_metric_quadratic (I := I) (M := M) g x a b
  have hexpand : g.inner x (a + b) (a + b) =
      g.inner x a a + 2 * g.inner x a b + g.inner x b b := by
    have h1 : g.inner x (a + b) (a + b) =
        g.inner x a (a + b) + g.inner x b (a + b) := by
      rw [map_add (g.inner x), ContinuousLinearMap.add_apply]
    have h2 : g.inner x a (a + b) = g.inner x a a + g.inner x a b :=
      map_add (g.inner x a) a b
    have h3 : g.inner x b (a + b) = g.inner x b a + g.inner x b b :=
      map_add (g.inner x b) a b
    have h4 : g.inner x b a = g.inner x a b := g.symm x b a
    rw [h1, h2, h3, h4]; ring
  have hsum_nn : 0 ≤ Real.sqrt (g.inner x a a) + Real.sqrt (g.inner x b b) :=
    add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  rw [show Real.sqrt (g.inner x a a) + Real.sqrt (g.inner x b b) =
      Real.sqrt ((Real.sqrt (g.inner x a a) + Real.sqrt (g.inner x b b)) ^ 2) from
    (Real.sqrt_sq hsum_nn).symm]
  refine Real.sqrt_le_sqrt ?_
  rw [hexpand]
  have hsq : (Real.sqrt (g.inner x a a) + Real.sqrt (g.inner x b b)) ^ 2 =
      g.inner x a a + 2 * (Real.sqrt (g.inner x a a) * Real.sqrt (g.inner x b b)) +
        g.inner x b b := by
    rw [add_sq, Real.sq_sqrt haa, Real.sq_sqrt hbb]; ring
  rw [hsq]
  linarith [hcs]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
omit [FiniteDimensional ℝ E] in
private lemma gNorm_sq_sub_eq_self_le
    (g : SmoothRiemannianMetric I M) (x : M) (a b : TangentSpace I x)
    {Ka Cb : ℝ} (hKa : 0 ≤ Ka) (hCb : 0 ≤ Cb) {p : ℝ} (hp : 0 ≤ p)
    (ha : g.inner x a a ≤ Ka ^ 2 * p) (hb : g.inner x b b ≤ Cb ^ 2 * p) :
    g.inner x (a + b) (a + b) ≤ (Ka + Cb) ^ 2 * p := by
  have hsqrtp : 0 ≤ Real.sqrt p := Real.sqrt_nonneg _
  have ha' : Real.sqrt (g.inner x a a) ≤ Ka * Real.sqrt p := by
    have : Real.sqrt (g.inner x a a) ≤ Real.sqrt (Ka ^ 2 * p) := Real.sqrt_le_sqrt ha
    rwa [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hKa] at this
  have hb' : Real.sqrt (g.inner x b b) ≤ Cb * Real.sqrt p := by
    have : Real.sqrt (g.inner x b b) ≤ Real.sqrt (Cb ^ 2 * p) := Real.sqrt_le_sqrt hb
    rwa [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hCb] at this
  have htri := gNorm_triangle (I := I) (M := M) g x a b
  have hsum_le : Real.sqrt (g.inner x (a + b) (a + b)) ≤ (Ka + Cb) * Real.sqrt p := by
    calc Real.sqrt (g.inner x (a + b) (a + b))
        ≤ Real.sqrt (g.inner x a a) + Real.sqrt (g.inner x b b) := htri
      _ ≤ Ka * Real.sqrt p + Cb * Real.sqrt p := add_le_add ha' hb'
      _ = (Ka + Cb) * Real.sqrt p := by ring
  have hab_nn : 0 ≤ g.inner x (a + b) (a + b) :=
    metric_inner_self_nonneg (I := I) (M := M) g x (a + b)
  have hrhs_nn : 0 ≤ (Ka + Cb) * Real.sqrt p :=
    mul_nonneg (add_nonneg hKa hCb) hsqrtp
  have hsq : g.inner x (a + b) (a + b) ≤ ((Ka + Cb) * Real.sqrt p) ^ 2 := by
    have hmul := mul_le_mul hsum_le hsum_le (Real.sqrt_nonneg _) hrhs_nn
    rw [Real.mul_self_sqrt hab_nn] at hmul
    rw [sq]; exact hmul
  calc g.inner x (a + b) (a + b) ≤ ((Ka + Cb) * Real.sqrt p) ^ 2 := hsq
    _ = (Ka + Cb) ^ 2 * (Real.sqrt p ^ 2) := by ring
    _ = (Ka + Cb) ^ 2 * p := by rw [Real.sq_sqrt hp]

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
theorem exists_riemannOp_LeviCivita_perturbed_gQuadratic_le_of_jetEnvelope
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) (B : ℝ)
    (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ max δ₀ 0)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_htie : ∀ (x : M) (v w : TangentSpace I x),
          g₁.inner x v w = g₀.inner x v w +
            ccTensorBilinSymm (I := I) g₀ P x v w)
        (x : M),
        (∑ j ∈ Finset.range 3,
            (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
              Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
            ‖(iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x‖)) ≤ B →
          ∀ v w u : TangentSpace I x,
            g₀.inner x (riemannOp (cov := LeviCivita (I := I) g₁) x v w u)
                (riemannOp (cov := LeviCivita (I := I) g₁) x v w u) ≤
              C ^ 2 * g₀.inner x v v * g₀.inner x w w * g₀.inner x u u := by
  classical
  obtain ⟨Kbase, hKbase_nn, hKbase⟩ :=
    exists_uniform_riemannOp_LeviCivita_gNorm_bound (I := I) (M := M) g₀
  obtain ⟨CD, hCD_nn, hCD⟩ :=
    exists_riemannOp_LeviCivita_difference_gQuadratic_le_of_jetEnvelope
      (I := I) (M := M) g₀ hδ₀ B hB
  refine ⟨Real.sqrt Kbase + CD, add_nonneg (Real.sqrt_nonneg _) hCD_nn, ?_⟩
  intro g₁ P δ hδ_le hδ htie x henv v w u
  set R0 : TangentSpace I x := riemannOp (cov := LeviCivita (I := I) g₀) x v w u with hR0
  set R1 : TangentSpace I x := riemannOp (cov := LeviCivita (I := I) g₁) x v w u with hR1
  set p : ℝ := g₀.inner x v v * g₀.inner x w w * g₀.inner x u u with hp_def
  have hp_nn : 0 ≤ p := by
    rw [hp_def]
    exact mul_nonneg (mul_nonneg (metric_inner_self_nonneg (I := I) (M := M) g₀ x v)
      (metric_inner_self_nonneg (I := I) (M := M) g₀ x w))
      (metric_inner_self_nonneg (I := I) (M := M) g₀ x u)
  have hbase : g₀.inner x R0 R0 ≤ Real.sqrt Kbase ^ 2 * p := by
    rw [Real.sq_sqrt hKbase_nn, hp_def]
    have h := hKbase x v w u
    rw [← hR0] at h
    calc g₀.inner x R0 R0 ≤ Kbase * g₀.inner x v v * g₀.inner x w w * g₀.inner x u u := h
      _ = Kbase * (g₀.inner x v v * g₀.inner x w w * g₀.inner x u u) := by ring
  have hdiff : g₀.inner x (R1 - R0) (R1 - R0) ≤ CD ^ 2 * p := by
    have h := hCD g₁ P hδ_le hδ htie x henv v w u
    rw [← hR0, ← hR1] at h
    calc g₀.inner x (R1 - R0) (R1 - R0)
        ≤ CD ^ 2 * g₀.inner x v v * g₀.inner x w w * g₀.inner x u u := h
      _ = CD ^ 2 * p := by rw [hp_def]; ring
  have hsplit : R1 = R0 + (R1 - R0) := by abel
  have hkey := gNorm_sq_sub_eq_self_le (I := I) (M := M) g₀ x R0 (R1 - R0)
    (Real.sqrt_nonneg Kbase) hCD_nn hp_nn hbase hdiff
  rw [← hsplit] at hkey
  calc g₀.inner x R1 R1 ≤ (Real.sqrt Kbase + CD) ^ 2 * p := hkey
    _ = (Real.sqrt Kbase + CD) ^ 2 * g₀.inner x v v * g₀.inner x w w * g₀.inner x u u := by
        rw [hp_def]; ring

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
theorem exists_ricEndoRaisedFib_perturbed_gQuadratic_le_of_jetEnvelope
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) (B : ℝ)
    (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ max δ₀ 0)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_htie : ∀ (x : M) (v w : TangentSpace I x),
          g₁.inner x v w = g₀.inner x v w +
            ccTensorBilinSymm (I := I) g₀ P x v w)
        (x : M),
        (∑ j ∈ Finset.range 3,
            (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
              Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
            ‖(iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x‖)) ≤ B →
          ∀ v : TangentSpace I x,
            g₀.inner x (ricEndoRaisedFib (I := I) g₁ x v)
                (ricEndoRaisedFib (I := I) g₁ x v) ≤ C ^ 2 * g₀.inner x v v := by
  classical
  set m : ℝ := max δ₀ 0 with hm_def
  have hm0 : 0 ≤ m := le_max_right _ _
  have hm1 : m < 1 := max_lt hδ₀ (by norm_num)
  have hmpos : 0 < 1 - m := by linarith
  have hm_inv_nn : (0 : ℝ) ≤ (1 - m)⁻¹ := inv_nonneg.mpr (le_of_lt hmpos)
  set N : ℝ := (Module.finrank ℝ E : ℝ) with hN_def
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  obtain ⟨C1, hC1_nn, hC1⟩ :=
    exists_riemannOp_LeviCivita_perturbed_gQuadratic_le_of_jetEnvelope
      (I := I) (M := M) g₀ hδ₀ B hB
  refine ⟨(1 - m)⁻¹ * (N * (C1 * Real.sqrt ((1 + m) * (1 - m)⁻¹))),
      by positivity, ?_⟩
  intro g₁ P δ hδ_le hδ htie x henv v
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hm1
  have hδpos : 0 < 1 - δ := by linarith
  set Λ : TangentSpace I x := ricEndoRaisedFib (I := I) g₁ x v with hΛ
  set Bf : Fin (Module.finrank ℝ E) → TangentSpace I x :=
    fun i => smoothOrthoFrame (I := I) g₁ x i x with hBf
  have hBorth : ∀ i j : Fin (Module.finrank ℝ E),
      g₁.inner x (Bf i) (Bf j) = if i = j then (1 : ℝ) else 0 := by
    intro i j; exact smoothOrthoFrame_orthonormal_at_center (I := I) g₁ x i j
  have hg1δ : ∀ a : TangentSpace I x, g₁.inner x a a ≤ (1 + δ) * g₀.inner x a a := by
    intro a
    have h := gInner_self_le_of_gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ P) hδ x a
    rw [← htie x a a] at h; exact h
  have hg0v_nn : 0 ≤ g₀.inner x v v := metric_inner_self_nonneg (I := I) (M := M) g₀ x v
  have hg0Λ_nn : 0 ≤ g₀.inner x Λ Λ := metric_inner_self_nonneg (I := I) (M := M) g₀ x Λ
  have hframe_g0 : ∀ i : Fin (Module.finrank ℝ E),
      g₀.inner x (Bf i) (Bf i) ≤ (1 - δ)⁻¹ := by
    intro i
    refine gZeroInner_self_le_neumann_of_g1_unit (I := I) (M := M) g₀ g₁ P hδ_lt hδ htie x _ ?_
    rw [hBf]
    rw [show g₁.inner x (smoothOrthoFrame (I := I) g₁ x i x)
          (smoothOrthoFrame (I := I) g₁ x i x) = if i = i then (1 : ℝ) else 0 from
      smoothOrthoFrame_orthonormal_at_center (I := I) g₁ x i i]
    simp
  set Kc : ℝ := C1 * Real.sqrt ((1 + m) * (1 - m)⁻¹) with hKc
  have hKc_nn : 0 ≤ Kc := mul_nonneg hC1_nn (Real.sqrt_nonneg _)
  have hterm : ∀ i : Fin (Module.finrank ℝ E),
      |g₁.inner x (riemannOp (cov := LeviCivita (I := I) g₁) x (Bf i) v Λ) (Bf i)| ≤
        Kc * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x Λ Λ) := by
    intro i
    set R : TangentSpace I x :=
      riemannOp (cov := LeviCivita (I := I) g₁) x (Bf i) v Λ with hR
    have hCS := abs_metric_inner_le_sqrt_metric_quadratic (I := I) (M := M) g₁ x R (Bf i)
    have hBii : g₁.inner x (Bf i) (Bf i) = 1 := by rw [hBorth i i]; simp
    rw [hBii, Real.sqrt_one, mul_one] at hCS
    have hg0RR : g₀.inner x R R ≤ C1 ^ 2 * (1 - δ)⁻¹ * g₀.inner x v v * g₀.inner x Λ Λ := by
      have hR2 := hC1 g₁ P hδ_le hδ htie x henv (Bf i) v Λ
      rw [← hR] at hR2
      have hfi := hframe_g0 i
      have hC1sq_nn : 0 ≤ C1 ^ 2 := sq_nonneg _
      calc g₀.inner x R R
          ≤ C1 ^ 2 * g₀.inner x (Bf i) (Bf i) * g₀.inner x v v * g₀.inner x Λ Λ := hR2
        _ ≤ C1 ^ 2 * (1 - δ)⁻¹ * g₀.inner x v v * g₀.inner x Λ Λ := by
            gcongr
    have hg1RR : g₁.inner x R R ≤
        (1 + m) * (C1 ^ 2 * (1 - δ)⁻¹ * g₀.inner x v v * g₀.inner x Λ Λ) := by
      have h := hg1δ R
      have hg0RR_nn : 0 ≤ g₀.inner x R R := metric_inner_self_nonneg (I := I) (M := M) g₀ x R
      have hδm : (1 + δ) ≤ (1 + m) := by linarith
      calc g₁.inner x R R ≤ (1 + δ) * g₀.inner x R R := h
        _ ≤ (1 + m) * g₀.inner x R R := mul_le_mul_of_nonneg_right hδm hg0RR_nn
        _ ≤ (1 + m) * (C1 ^ 2 * (1 - δ)⁻¹ * g₀.inner x v v * g₀.inner x Λ Λ) :=
            mul_le_mul_of_nonneg_left hg0RR (by linarith)
    have hbnd : (1 + m) * (C1 ^ 2 * (1 - δ)⁻¹ * g₀.inner x v v * g₀.inner x Λ Λ) ≤
        Kc ^ 2 * g₀.inner x v v * g₀.inner x Λ Λ := by
      have hinv_le : (1 - δ)⁻¹ ≤ (1 - m)⁻¹ :=
        inv_le_inv_of_le_of_pos hmpos (by linarith)
      have hKcsq : Kc ^ 2 = C1 ^ 2 * ((1 + m) * (1 - m)⁻¹) := by
        rw [hKc, mul_pow, Real.sq_sqrt (by positivity)]
      rw [hKcsq]
      have hprod_nn : 0 ≤ g₀.inner x v v * g₀.inner x Λ Λ := mul_nonneg hg0v_nn hg0Λ_nn
      have hstep : (1 + m) * (C1 ^ 2 * (1 - δ)⁻¹) ≤
          C1 ^ 2 * ((1 + m) * (1 - m)⁻¹) := by
        have : (1 + m) * (C1 ^ 2 * (1 - δ)⁻¹) =
            C1 ^ 2 * ((1 + m) * (1 - δ)⁻¹) := by ring
        rw [this]
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        exact mul_le_mul_of_nonneg_left hinv_le (by linarith)
      calc (1 + m) * (C1 ^ 2 * (1 - δ)⁻¹ * g₀.inner x v v * g₀.inner x Λ Λ)
          = ((1 + m) * (C1 ^ 2 * (1 - δ)⁻¹)) * (g₀.inner x v v * g₀.inner x Λ Λ) := by ring
        _ ≤ (C1 ^ 2 * ((1 + m) * (1 - m)⁻¹)) * (g₀.inner x v v * g₀.inner x Λ Λ) :=
            mul_le_mul_of_nonneg_right hstep hprod_nn
        _ = C1 ^ 2 * ((1 + m) * (1 - m)⁻¹) * g₀.inner x v v * g₀.inner x Λ Λ := by ring
    have hg1RR' : g₁.inner x R R ≤ Kc ^ 2 * g₀.inner x v v * g₀.inner x Λ Λ :=
      le_trans hg1RR hbnd
    have hsqrtRR : Real.sqrt (g₁.inner x R R) ≤
        Kc * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x Λ Λ) := by
      have hrhs_eq : Kc ^ 2 * g₀.inner x v v * g₀.inner x Λ Λ =
          (Kc * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x Λ Λ)) ^ 2 := by
        have e1 : Real.sqrt (g₀.inner x v v) ^ 2 = g₀.inner x v v := Real.sq_sqrt hg0v_nn
        have e2 : Real.sqrt (g₀.inner x Λ Λ) ^ 2 = g₀.inner x Λ Λ := Real.sq_sqrt hg0Λ_nn
        calc Kc ^ 2 * g₀.inner x v v * g₀.inner x Λ Λ
            = Kc ^ 2 * Real.sqrt (g₀.inner x v v) ^ 2 *
                Real.sqrt (g₀.inner x Λ Λ) ^ 2 := by rw [e1, e2]
          _ = (Kc * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x Λ Λ)) ^ 2 := by ring
      rw [hrhs_eq] at hg1RR'
      have hrhs_nn : 0 ≤ Kc * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x Λ Λ) :=
        mul_nonneg (mul_nonneg hKc_nn (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
      have := Real.sqrt_le_sqrt hg1RR'
      rwa [Real.sqrt_sq hrhs_nn] at this
    exact le_trans hCS hsqrtRR
  have htrace : g₁.inner x Λ Λ =
      ∑ i : Fin (Module.finrank ℝ E),
        g₁.inner x (riemannOp (cov := LeviCivita (I := I) g₁) x (Bf i) v Λ) (Bf i) := by
    have hric := inner_ricEndoRaisedFib (I := I) g₁ x v Λ
    rw [hΛ] at hric ⊢
    rw [hric]
    exact ricciTensor_eq_orthonormal_trace (I := I) g₁ x v Λ Bf hBorth
  have hg1ΛΛ_le : g₁.inner x Λ Λ ≤
      N * (Kc * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x Λ Λ)) := by
    rw [htrace]
    calc ∑ i : Fin (Module.finrank ℝ E),
          g₁.inner x (riemannOp (cov := LeviCivita (I := I) g₁) x (Bf i) v Λ) (Bf i)
        ≤ ∑ i : Fin (Module.finrank ℝ E),
            Kc * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x Λ Λ) := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          exact le_trans (le_abs_self _) (hterm i)
      _ = N * (Kc * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x Λ Λ)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hN_def]
  have hg0lower : (1 - δ) * g₀.inner x Λ Λ ≤ g₁.inner x Λ Λ := by
    have h := gZeroInner_self_le_of_g1_self_le (I := I) (M := M) g₀ g₁ P hδ htie x Λ
      (c := g₁.inner x Λ Λ) (le_refl _)
    exact h
  set S : ℝ := Real.sqrt (g₀.inner x Λ Λ) with hS
  have hS_nn : 0 ≤ S := Real.sqrt_nonneg _
  have hS_sq : S ^ 2 = g₀.inner x Λ Λ := Real.sq_sqrt hg0Λ_nn
  have hcombined : (1 - δ) * S ^ 2 ≤
      N * (Kc * Real.sqrt (g₀.inner x v v) * S) := by
    rw [hS_sq]
    exact le_trans hg0lower hg1ΛΛ_le
  have hSbound : (1 - δ) * S ≤ N * (Kc * Real.sqrt (g₀.inner x v v)) := by
    rcases eq_or_lt_of_le hS_nn with hS0 | hSpos
    · rw [← hS0, mul_zero]
      positivity
    · have hSpos' : 0 < S := hSpos
      have hdiv : (1 - δ) * S * S ≤ N * (Kc * Real.sqrt (g₀.inner x v v)) * S := by
        have : (1 - δ) * S ^ 2 = (1 - δ) * S * S := by ring
        rw [this] at hcombined
        calc (1 - δ) * S * S ≤ N * (Kc * Real.sqrt (g₀.inner x v v) * S) := hcombined
          _ = N * (Kc * Real.sqrt (g₀.inner x v v)) * S := by ring
      exact le_of_mul_le_mul_right hdiv hSpos'
  have hS_final : S ≤ (1 - δ)⁻¹ * (N * (Kc * Real.sqrt (g₀.inner x v v))) := by
    rw [show (1 - δ)⁻¹ * (N * (Kc * Real.sqrt (g₀.inner x v v))) =
        ((1 - δ) * S * (1 - δ)⁻¹ + ((1 - δ)⁻¹ * (N * (Kc * Real.sqrt (g₀.inner x v v)))
          - (1 - δ) * S * (1 - δ)⁻¹)) from by ring]
    have hmono : (1 - δ) * S ≤ N * (Kc * Real.sqrt (g₀.inner x v v)) := hSbound
    have hkey : S = (1 - δ) * S * (1 - δ)⁻¹ := by
      field_simp
    nlinarith [mul_le_mul_of_nonneg_right hmono hm_inv_nn, hkey, hmpos, hδpos,
      inv_pos.mpr hδpos]
  have hSle_m : S ≤ (1 - m)⁻¹ * (N * Kc) * Real.sqrt (g₀.inner x v v) := by
    have hinv_le : (1 - δ)⁻¹ ≤ (1 - m)⁻¹ := inv_le_inv_of_le_of_pos hmpos (by linarith)
    have hrhs_nn : 0 ≤ N * (Kc * Real.sqrt (g₀.inner x v v)) :=
      mul_nonneg hN0 (mul_nonneg hKc_nn (Real.sqrt_nonneg _))
    calc S ≤ (1 - δ)⁻¹ * (N * (Kc * Real.sqrt (g₀.inner x v v))) := hS_final
      _ ≤ (1 - m)⁻¹ * (N * (Kc * Real.sqrt (g₀.inner x v v))) :=
          mul_le_mul_of_nonneg_right hinv_le hrhs_nn
      _ = (1 - m)⁻¹ * (N * Kc) * Real.sqrt (g₀.inner x v v) := by ring
  set Cfin : ℝ := (1 - m)⁻¹ * (N * Kc) with hCfin
  have hCfin_nn : 0 ≤ Cfin := by
    rw [hCfin]; exact mul_nonneg hm_inv_nn (mul_nonneg hN0 hKc_nn)
  have hCfin_eq : Cfin = (1 - m)⁻¹ * (N * (C1 * Real.sqrt ((1 + m) * (1 - m)⁻¹))) := by
    rw [hCfin, hKc]
  have hSv : S ≤ Cfin * Real.sqrt (g₀.inner x v v) := by
    rw [hCfin]; exact hSle_m
  have hRHS_nn : 0 ≤ Cfin * Real.sqrt (g₀.inner x v v) :=
    mul_nonneg hCfin_nn (Real.sqrt_nonneg _)
  have hgoal : g₀.inner x Λ Λ ≤ Cfin ^ 2 * g₀.inner x v v := by
    have hSsq : g₀.inner x Λ Λ ≤ (Cfin * Real.sqrt (g₀.inner x v v)) ^ 2 := by
      rw [← hS_sq]
      have hmul := mul_le_mul hSv hSv hS_nn hRHS_nn
      rw [← sq, ← sq] at hmul
      exact hmul
    calc g₀.inner x Λ Λ ≤ (Cfin * Real.sqrt (g₀.inner x v v)) ^ 2 := hSsq
      _ = Cfin ^ 2 * (Real.sqrt (g₀.inner x v v)) ^ 2 := by ring
      _ = Cfin ^ 2 * g₀.inner x v v := by rw [Real.sq_sqrt hg0v_nn]
  rw [hCfin_eq] at hgoal
  exact hgoal

end Curvature
end Geometry
end DifferentialGeometry

end
