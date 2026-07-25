import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceJetTower
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceFibreBound


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma coframeS_one_eq_g0FlatCLM (g₀ : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (K : Fin 1 → Fin n) :
    coframeS (I := I) (M := M) g₀ x 1 e K = g0FlatCLM (I := I) g₀ x (e (K 0)) := by
  apply cotangentToDualLinear_injective (I := I) (x := x)
  apply LinearMap.ext
  intro w
  rw [cotangentToDualLinear_apply, cotangentToDualLinear_apply, cotangentToDual_apply,
    cotangentToDual_apply]
  rw [show coframeS (I := I) (M := M) g₀ x 1 e K (fun _ : Fin 1 => w) =
      ∏ k : Fin 1, g₀.inner x (e (K k)) w from coframeS_apply (I := I) (M := M) g₀ x 1 e K _]
  rw [Fin.prod_univ_one]
  rw [g0FlatCLM_apply, dualToCotangent_apply]
  rfl

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma fiberNormSqComponent_sharpFlatEndoCc
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) {n : ℕ}
    (e : Fin n → TangentSpace I x)
    (K : Fin 1 → Fin n) (J : Fin 1 → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g₀ x 1 1
        ((sharpFlatEndoCc (I := I) g₀ g₁).toSection x) n e K J =
      g₀.inner x
        (inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x (e (K 0)))) (e (J 0)) := by
  rw [show fiberNormSqComponent (I := I) (M := M) g₀ x 1 1
        ((sharpFlatEndoCc (I := I) g₀ g₁).toSection x) n e K J =
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
          (sharpFlatEndoCc (I := I) g₀ g₁).toSection x)
        (coframeS (I := I) (M := M) g₀ x 1 e K))
        (fun k => e (J k)) from rfl]
  rw [coframeS_one_eq_g0FlatCLM (I := I) (M := M) g₀ x e K]
  rw [sharpFlatEndoCc_toSection]
  rw [show (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        TensorRSSpace.ofCLM
          ((g0FlatCLM (I := I) g₀ x).comp (inverseMetricSharpFib (I := I) g₁ x)))
        (g0FlatCLM (I := I) g₀ x (e (K 0))) =
      g0FlatCLM (I := I) g₀ x
        (inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x (e (K 0)))) from rfl]
  rw [show (g0FlatCLM (I := I) g₀ x
        (inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x (e (K 0)))))
        (fun k => e (J k)) =
      cotangentToDual (I := I) (x := x)
        (g0FlatCLM (I := I) g₀ x
          (inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x (e (K 0)))))
        (e (J 0)) from by
    rw [cotangentToDual_apply]
    rfl]
  rw [cotangentToDual_g0FlatCLM (I := I) g₀ x
    (inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x (e (K 0)))) (e (J 0))]

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem riemannianFiberNormSq_sharpFlatEndoCc_le_of_lt_one
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (_hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1)
    (g₁ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2)
    (h : ∀ y v w, g₁.inner y v w =
      g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
    {δ : ℝ} (hδ : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
    (hbound : metricCauchySchwarzBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x
        ((sharpFlatEndoCc (I := I) g₀ g₁).toSection x) ≤
      ((Module.finrank ℝ E : ℝ)) ^ 2 * (1 / (1 - δ₀)) ^ 2 := by
  classical
  have hceil0 : 0 < 1 - δ₀ := by linarith
  have hcoeff : 0 < 1 - δ := by linarith
  obtain ⟨n, e, bse, hn, hbse, horth, hpars, hrepr_v, hsum⟩ :=
    tangent_orthonormalBasis_witness (I := I) (M := M) g₀ x
  have hnE : n = Module.finrank ℝ E := by rw [hn]; rfl
  have hg₁ : ∀ (b : M) (u₁ u₂ : TangentSpace I b),
      g₁.inner b u₁ u₂ = g₀.inner b u₁ u₂ + ccTensorBilinSymm (I := I) g₀ T b u₁ u₂ :=
    fun b u₁ u₂ => h b u₁ u₂
  rw [riemannianFiberNormSq_eq_sum_componentSq_of_basis (I := I) (M := M) g₀ 1 1 x
    ((sharpFlatEndoCc (I := I) g₀ g₁).toSection x) e bse hnE hbse horth]
  have hinv_le : 1 / (1 - δ) ≤ 1 / (1 - δ₀) := by
    rw [div_le_div_iff₀ hcoeff hceil0]; linarith
  have hinv₀_nn : 0 ≤ 1 / (1 - δ₀) := by positivity
  have heach : ∀ (K J : Fin 1 → Fin n),
      (fiberNormSqComponent (I := I) (M := M) g₀ x 1 1
        ((sharpFlatEndoCc (I := I) g₀ g₁).toSection x) n e K J) ^ 2 ≤
        (1 / (1 - δ₀)) ^ 2 := by
    intro K J
    rw [fiberNormSqComponent_sharpFlatEndoCc (I := I) (M := M) g₀ g₁ x e K J]
    set u : TangentSpace I x :=
      inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x (e (K 0))) with hu_def
    have hcs := metric_inner_cauchy_schwarz_sq (I := I) (M := M) g₀ x u (e (J 0))
    have hJJ : g₀.inner x (e (J 0)) (e (J 0)) = 1 := by rw [horth (J 0) (J 0)]; simp
    rw [hJJ, mul_one] at hcs
    have hsfib := norm_inverseMetricSharpFib_g0Flat_le
      (I := I) (M := M) g₀ g₁ (ccTensorBilinSymm (I := I) g₀ T) hg₁
      (by linarith : δ < 1) hδ0 hbound x (e (K 0))
    have hKK : g₀.inner x (e (K 0)) (e (K 0)) = 1 := by rw [horth (K 0) (K 0)]; simp
    rw [hKK, Real.sqrt_one, mul_one] at hsfib
    rw [← hu_def] at hsfib
    have huu_nn : 0 ≤ g₀.inner x u u := metric_inner_self_nonneg (I := I) (M := M) g₀ x u
    have hsqrt_eq : Real.sqrt (g₀.inner x u u) ^ 2 = g₀.inner x u u :=
      Real.sq_sqrt huu_nn
    have hsqrt_nn : 0 ≤ Real.sqrt (g₀.inner x u u) := Real.sqrt_nonneg _
    have huu_le : g₀.inner x u u ≤ (1 / (1 - δ₀)) ^ 2 := by
      rw [← hsqrt_eq]
      have hsfib' : Real.sqrt (g₀.inner x u u) ≤ 1 / (1 - δ₀) := le_trans hsfib hinv_le
      have := mul_self_le_mul_self hsqrt_nn hsfib'
      nlinarith [this, hsfib', hinv₀_nn]
    calc (g₀.inner x u (e (J 0))) ^ 2
        ≤ g₀.inner x u u := hcs
      _ ≤ (1 / (1 - δ₀)) ^ 2 := huu_le
  calc ∑ K : Fin 1 → Fin n, ∑ J : Fin 1 → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g₀ x 1 1
          ((sharpFlatEndoCc (I := I) g₀ g₁).toSection x) n e K J) ^ 2
      ≤ ∑ K : Fin 1 → Fin n, ∑ J : Fin 1 → Fin n, (1 / (1 - δ₀)) ^ 2 :=
        Finset.sum_le_sum (fun K _ => Finset.sum_le_sum (fun J _ => heach K J))
    _ = (Fintype.card (Fin 1 → Fin n) : ℝ) * (Fintype.card (Fin 1 → Fin n) : ℝ) *
        (1 / (1 - δ₀)) ^ 2 := by
        rw [Finset.sum_const, Finset.sum_const]
        simp only [Finset.card_univ, nsmul_eq_mul]
        ring
    _ = ((Module.finrank ℝ E : ℝ)) ^ 2 * (1 / (1 - δ₀)) ^ 2 := by
        simp only [Fintype.card_fun, Fintype.card_fin, pow_one]
        rw [← hnE]
        ring

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma g0_inner_sharpFlatRaiseEndo_eq_g1
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) (v w : TangentSpace I x) :
    g₀.inner x (sharpFlatRaiseEndo (I := I) g₀ g₁ x v) w = g₁.inner x v w := by
  rw [sharpFlatRaiseEndo_apply]
  rw [inverseMetricSharpFib_inner (I := I) g₀ x (g0FlatCLM (I := I) g₁ x v) w]
  rw [cotangentToDualLinear_apply]
  rw [cotangentToDual_g0FlatCLM (I := I) g₁ x v w]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma g1_self_upper_bound
    (g₀ g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (h : ∀ y v w, g₁.inner y v w =
      g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
    {δ : ℝ} (hbound : metricCauchySchwarzBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (x : M) (v : TangentSpace I x) :
    g₁.inner x v v ≤ (1 + δ) * g₀.inner x v v := by
  have hgate := hbound x v v
  have hnn : 0 ≤ g₀.inner x v v := metric_inner_self_nonneg (I := I) (M := M) g₀ x v
  have hsq : Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x v v) = g₀.inner x v v := by
    rw [← Real.sqrt_mul hnn, Real.sqrt_mul_self hnn]
  have habs : |ccTensorBilinSymm (I := I) g₀ T x v v| ≤ δ * g₀.inner x v v := by
    calc |ccTensorBilinSymm (I := I) g₀ T x v v|
        ≤ δ * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x v v) := hgate
      _ = δ * (Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x v v)) := by ring
      _ = δ * g₀.inner x v v := by rw [hsq]
  have hle : ccTensorBilinSymm (I := I) g₀ T x v v ≤ δ * g₀.inner x v v :=
    le_trans (le_abs_self _) habs
  rw [h x v v]
  nlinarith [hle]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem sqrt_inner_sharpFlatRaiseEndo_le
    (g₀ g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (h : ∀ y v w, g₁.inner y v w =
      g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
    {δ : ℝ} (hδ_nn : 0 ≤ δ)
    (hbound : metricCauchySchwarzBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (x : M) (v : TangentSpace I x) :
    Real.sqrt (g₀.inner x (sharpFlatRaiseEndo (I := I) g₀ g₁ x v)
        (sharpFlatRaiseEndo (I := I) g₀ g₁ x v))
      ≤ (1 + δ) * Real.sqrt (g₀.inner x v v) := by
  set p : TangentSpace I x := sharpFlatRaiseEndo (I := I) g₀ g₁ x v with hp_def
  set Np : ℝ := Real.sqrt (g₀.inner x p p) with hNp_def
  set Nv : ℝ := Real.sqrt (g₀.inner x v v) with hNv_def
  have hNp_nn : 0 ≤ Np := Real.sqrt_nonneg _
  have hNv_nn : 0 ≤ Nv := Real.sqrt_nonneg _
  have hpp_nn : 0 ≤ g₀.inner x p p := metric_inner_self_nonneg (I := I) (M := M) g₀ x p
  have hvv_nn : 0 ≤ g₀.inner x v v := metric_inner_self_nonneg (I := I) (M := M) g₀ x v
  have hNp_sq : Np * Np = g₀.inner x p p := by
    rw [hNp_def, ← Real.sqrt_mul hpp_nn, Real.sqrt_mul_self hpp_nn]
  have h1delta_nn : 0 ≤ 1 + δ := by linarith
  have hpp_eq : g₀.inner x p p = g₁.inner x v p := by
    rw [hp_def]
    rw [g0_inner_sharpFlatRaiseEndo_eq_g1 (I := I) g₀ g₁ x v p]
  have hg1cs : g₁.inner x v p ≤
      Real.sqrt (g₁.inner x v v) * Real.sqrt (g₁.inner x p p) := by
    have habs := abs_metric_inner_le_sqrt_metric_quadratic (I := I) (M := M) g₁ x v p
    exact le_trans (le_abs_self _) habs
  have hg1vv := g1_self_upper_bound (I := I) g₀ g₁ T h hbound x v
  have hg1pp := g1_self_upper_bound (I := I) g₀ g₁ T h hbound x p
  have hg1vv_nn : 0 ≤ g₁.inner x v v := metric_inner_self_nonneg (I := I) (M := M) g₁ x v
  have hg1pp_nn : 0 ≤ g₁.inner x p p := metric_inner_self_nonneg (I := I) (M := M) g₁ x p
  have hsqrt_g1vv : Real.sqrt (g₁.inner x v v) ≤ Real.sqrt ((1 + δ) * g₀.inner x v v) :=
    Real.sqrt_le_sqrt hg1vv
  have hsqrt_g1pp : Real.sqrt (g₁.inner x p p) ≤ Real.sqrt ((1 + δ) * g₀.inner x p p) :=
    Real.sqrt_le_sqrt hg1pp
  have hsplit_vv : Real.sqrt ((1 + δ) * g₀.inner x v v) =
      Real.sqrt (1 + δ) * Nv := by
    rw [Real.sqrt_mul h1delta_nn, hNv_def]
  have hsplit_pp : Real.sqrt ((1 + δ) * g₀.inner x p p) =
      Real.sqrt (1 + δ) * Np := by
    rw [Real.sqrt_mul h1delta_nn, hNp_def]
  have hroot_sq : Real.sqrt (1 + δ) * Real.sqrt (1 + δ) = 1 + δ := by
    rw [← Real.sqrt_mul h1delta_nn, Real.sqrt_mul_self h1delta_nn]
  have hroot_nn : 0 ≤ Real.sqrt (1 + δ) := Real.sqrt_nonneg _
  have hchain : g₀.inner x p p ≤ (1 + δ) * Nv * Np := by
    calc g₀.inner x p p = g₁.inner x v p := hpp_eq
      _ ≤ Real.sqrt (g₁.inner x v v) * Real.sqrt (g₁.inner x p p) := hg1cs
      _ ≤ (Real.sqrt (1 + δ) * Nv) * (Real.sqrt (1 + δ) * Np) := by
          rw [← hsplit_vv, ← hsplit_pp]
          exact mul_le_mul hsqrt_g1vv hsqrt_g1pp (Real.sqrt_nonneg _)
            (le_trans (Real.sqrt_nonneg _) hsqrt_g1vv)
      _ = (1 + δ) * Nv * Np := by
          rw [show (Real.sqrt (1 + δ) * Nv) * (Real.sqrt (1 + δ) * Np)
              = (Real.sqrt (1 + δ) * Real.sqrt (1 + δ)) * (Nv * Np) from by ring]
          rw [hroot_sq]; ring
  rw [← hNp_sq] at hchain
  rcases eq_or_lt_of_le hNp_nn with hNp0 | hNppos
  · rw [← hNp0]
    exact mul_nonneg h1delta_nn hNv_nn
  · have h2 : Np * Np ≤ ((1 + δ) * Nv) * Np := by nlinarith [hchain]
    exact le_of_mul_le_mul_right h2 hNppos

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma fiberNormSqComponent_raisedKoszul
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) {n : ℕ}
    (e : Fin n → TangentSpace I x)
    (K : Fin 1 → Fin n) (J : Fin 2 → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g₀ x 1 2
        ((raisedKoszul (I := I) g₀ g₁).toSection x) n e K J =
      g₀.inner x (e (K 0))
        (sharpFlatRaiseEndo (I := I) g₀ g₁ x
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (e (J 0)) (e (J 1)))) := by
  rw [show fiberNormSqComponent (I := I) (M := M) g₀ x 1 2
        ((raisedKoszul (I := I) g₀ g₁).toSection x) n e K J =
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
          (raisedKoszul (I := I) g₀ g₁).toSection x)
        (coframeS (I := I) (M := M) g₀ x 1 e K))
        (fun k => e (J k)) from rfl]
  rw [coframeS_one_eq_g0FlatCLM (I := I) (M := M) g₀ x e K]
  rw [raisedKoszul_toSection]
  rw [show (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        raisedKoszulFib (I := I) g₀ g₁ x) (g0FlatCLM (I := I) g₀ x (e (K 0)))
      = raisedKoszulPairing (I := I) g₀ g₁ x (g0FlatCLM (I := I) g₀ x (e (K 0))) from rfl]
  rw [show (raisedKoszulPairing (I := I) g₀ g₁ x (g0FlatCLM (I := I) g₀ x (e (K 0))))
        (fun k => e (J k))
      = (g0FlatCLM (I := I) g₀ x (e (K 0)))
          (fun _ : Fin 1 => raisedKoszulVec (I := I) g₀ g₁ x (e (J 0)) (e (J 1))) from rfl]
  rw [raisedKoszulVec_apply]
  rw [sharpFlatRaiseEndo_apply]
  rw [show (g0FlatCLM (I := I) g₀ x (e (K 0)))
        (fun _ : Fin 1 => inverseMetricSharpFib (I := I) g₀ x
          (g0FlatCLM (I := I) g₁ x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (e (J 0)) (e (J 1))))) =
      cotangentToDual (I := I) (x := x) (g0FlatCLM (I := I) g₀ x (e (K 0)))
        (inverseMetricSharpFib (I := I) g₀ x
          (g0FlatCLM (I := I) g₁ x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (e (J 0)) (e (J 1)))))
      from (cotangentToDual_apply (I := I) (x := x) _ _).symm]
  rw [cotangentToDual_g0FlatCLM (I := I) g₀ x (e (K 0))]

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
omit [NeZero (Module.finrank ℝ E)] in
theorem riemannianFiberNormSq_raisedKoszul_le_of_lt_one
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g₁ : SmoothRiemannianMetric I M)
      (T : SmoothCcTensor g₀ 0 2)
      (_h : ∀ y v w, g₁.inner y v w =
        g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
      {δ : ℝ} (_hδ : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
      (_hbound : metricCauchySchwarzBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
      (x : M),
      letI : Bundle.RiemannianBundle
          (fun y : M => Tensor0SBundle.TensorRSSpace 0 3 I y) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x
          ((raisedKoszul (I := I) g₀ g₁).toSection x) ≤
        C ^ 2 * ‖((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x :
            Tensor0SBundle.TensorRSSpace 0 3 I x)‖ ^ 2 := by
  classical
  letI instTens : Bundle.RiemannianBundle
      (fun y : M => Tensor0SBundle.TensorRSSpace 0 3 I y) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
  obtain ⟨C₀, hC₀0, hpw⟩ :=
    connDiff_gFibreNorm_le_iteratedCovGrad_of_lt_one (I := I) (M := M) g₀ hδ₀0 hδ₀
  refine ⟨Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 3) * ((1 + δ₀) * C₀), by positivity, ?_⟩
  intro g₁ T h δ hδ hδ0 hbound x
  obtain ⟨n, e, bse, hn, hbse, horth, hpars, hrepr_v, hsum⟩ :=
    tangent_orthonormalBasis_witness (I := I) (M := M) g₀ x
  have hnE : n = Module.finrank ℝ E := by rw [hn]; rfl
  set G : ℝ := ‖((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x :
      Tensor0SBundle.TensorRSSpace 0 3 I x)‖ with hG_def
  have hG_nn : 0 ≤ G := norm_nonneg _
  have hδ_lt1 : δ < 1 := by linarith
  rw [riemannianFiberNormSq_eq_sum_componentSq_of_basis (I := I) (M := M) g₀ 1 2 x
    ((raisedKoszul (I := I) g₀ g₁).toSection x) e bse hnE hbse horth]
  have heach : ∀ (K : Fin 1 → Fin n) (J : Fin 2 → Fin n),
      (fiberNormSqComponent (I := I) (M := M) g₀ x 1 2
        ((raisedKoszul (I := I) g₀ g₁).toSection x) n e K J) ^ 2 ≤
        ((1 + δ₀) * C₀) ^ 2 * G ^ 2 := by
    intro K J
    rw [fiberNormSqComponent_raisedKoszul (I := I) (M := M) g₀ g₁ x e K J]
    set d : TangentSpace I x :=
      PDE.DeTurck.connDiff (I := I) g₁ g₀ x (e (J 0)) (e (J 1)) with hd_def
    set u : TangentSpace I x := sharpFlatRaiseEndo (I := I) g₀ g₁ x d with hu_def
    have hcs := metric_inner_cauchy_schwarz_sq (I := I) (M := M) g₀ x (e (K 0)) u
    have hKK : g₀.inner x (e (K 0)) (e (K 0)) = 1 := by rw [horth (K 0) (K 0)]; simp
    rw [hKK, one_mul] at hcs
    have hrev := sqrt_inner_sharpFlatRaiseEndo_le (I := I) g₀ g₁ T h hδ0 hbound x d
    rw [← hu_def] at hrev
    have hconn := hpw g₁ T h hδ hδ0 hbound x (e (J 0)) (e (J 1))
    have hJ0 : g₀.inner x (e (J 0)) (e (J 0)) = 1 := by rw [horth (J 0) (J 0)]; simp
    have hJ1 : g₀.inner x (e (J 1)) (e (J 1)) = 1 := by rw [horth (J 1) (J 1)]; simp
    rw [hJ0, hJ1, Real.sqrt_one, mul_one, mul_one, ← hG_def, ← hd_def] at hconn
    have hd_sqrt_nn : 0 ≤ Real.sqrt (g₀.inner x d d) := Real.sqrt_nonneg _
    have h1delta_nn : 0 ≤ 1 + δ := by linarith
    have hconn' : (1 + δ) * Real.sqrt (g₀.inner x d d) ≤ (1 + δ₀) * (C₀ * G) := by
      have hstep1 : (1 + δ) * Real.sqrt (g₀.inner x d d) ≤ (1 + δ) * (C₀ * G) :=
        mul_le_mul_of_nonneg_left hconn h1delta_nn
      have hstep2 : (1 + δ) * (C₀ * G) ≤ (1 + δ₀) * (C₀ * G) :=
        mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hC₀0 hG_nn)
      exact le_trans hstep1 hstep2
    have hu_sqrt_le : Real.sqrt (g₀.inner x u u) ≤ (1 + δ₀) * (C₀ * G) :=
      le_trans hrev hconn'
    have huu_nn : 0 ≤ g₀.inner x u u := metric_inner_self_nonneg (I := I) (M := M) g₀ x u
    have hsqrt_eq : Real.sqrt (g₀.inner x u u) ^ 2 = g₀.inner x u u := Real.sq_sqrt huu_nn
    have hsqrt_nn : 0 ≤ Real.sqrt (g₀.inner x u u) := Real.sqrt_nonneg _
    have hrhs_nn : 0 ≤ (1 + δ₀) * (C₀ * G) := by positivity
    have huu_le : g₀.inner x u u ≤ ((1 + δ₀) * C₀ * G) ^ 2 := by
      rw [← hsqrt_eq]
      have := mul_self_le_mul_self hsqrt_nn hu_sqrt_le
      nlinarith [this, hu_sqrt_le, hrhs_nn]
    calc (g₀.inner x (e (K 0)) u) ^ 2
        ≤ g₀.inner x u u := hcs
      _ ≤ ((1 + δ₀) * C₀ * G) ^ 2 := huu_le
      _ = ((1 + δ₀) * C₀) ^ 2 * G ^ 2 := by ring
  calc ∑ K : Fin 1 → Fin n, ∑ J : Fin 2 → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g₀ x 1 2
          ((raisedKoszul (I := I) g₀ g₁).toSection x) n e K J) ^ 2
      ≤ ∑ K : Fin 1 → Fin n, ∑ J : Fin 2 → Fin n, ((1 + δ₀) * C₀) ^ 2 * G ^ 2 :=
        Finset.sum_le_sum (fun K _ => Finset.sum_le_sum (fun J _ => heach K J))
    _ = (Fintype.card (Fin 1 → Fin n) : ℝ) * (Fintype.card (Fin 2 → Fin n) : ℝ) *
        (((1 + δ₀) * C₀) ^ 2 * G ^ 2) := by
        rw [Finset.sum_const, Finset.sum_const]
        simp only [Finset.card_univ, nsmul_eq_mul]
        ring
    _ = (Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 3) * ((1 + δ₀) * C₀)) ^ 2 * G ^ 2 := by
        have hcard : (Fintype.card (Fin 1 → Fin n) : ℝ) * (Fintype.card (Fin 2 → Fin n) : ℝ)
            = (n : ℝ) ^ 3 := by
          rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
            Fintype.card_fin]
          push_cast
          ring
        rw [hcard, ← hnE]
        have hsq : Real.sqrt ((n : ℝ) ^ 3) ^ 2 = (n : ℝ) ^ 3 :=
          Real.sq_sqrt (by positivity)
        rw [show (Real.sqrt ((n : ℝ) ^ 3) * ((1 + δ₀) * C₀)) ^ 2 * G ^ 2
            = Real.sqrt ((n : ℝ) ^ 3) ^ 2 * (((1 + δ₀) * C₀) ^ 2 * G ^ 2) from by ring]
        rw [hsq]

omit [NeZero (Module.finrank ℝ E)] in
private lemma fiberNormSqComponent_covGrad_raisedKoszul
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) {n : ℕ}
    (e : Fin n → TangentSpace I x)
    (K : Fin 1 → Fin n) (J : Fin 3 → Fin n)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hXx : X x = e (J 0)) (hYx : Y x = e (J 1)) (hZx : Z x = e (J 2)) :
    fiberNormSqComponent (I := I) (M := M) g₀ x 1 3
        ((covGrad (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁)).toSection x) n e K J =
      g₀.inner x (e (K 0))
        (covDerivRaisedKoszulVec (I := I) g₀ g₁ X Y Z x) := by
  classical
  obtain ⟨om, hom⟩ := ContMDiffSection.exists_eq_at (I := I)
    (F := Tensor0SModel 1 ℝ E) (V := fun y : M => Tensor0SSpace 1 I y)
    (n := (⊤ : ℕ∞)) x (coframeS (I := I) (M := M) g₀ x 1 e K)
  have homx : om x = coframeS (I := I) (M := M) g₀ x 1 e K := hom
  have hcomp : fiberNormSqComponent (I := I) (M := M) g₀ x 1 3
        ((covGrad (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁)).toSection x) n e K J =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
          (covGrad (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁)).toSection x)
          (om x))
        (Fin.cons (X x) (Fin.cons (Y x) ![Z x])) := by
    rw [show fiberNormSqComponent (I := I) (M := M) g₀ x 1 3
          ((covGrad (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁)).toSection x) n e K J =
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
            (covGrad (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁)).toSection x)
          (coframeS (I := I) (M := M) g₀ x 1 e K))
          (fun k => e (J k)) from rfl]
    rw [← homx]
    rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
          (covGrad (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁)).toSection x)
          (om x))
          (fun k => e (J k)) =
        Tensor0SSpace.toModel
          ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
            (covGrad (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁)).toSection x)
            (om x))
          (fun k => (show E from e (J k))) from rfl]
    congr 1
    funext k
    refine Fin.cases ?_ (fun i => ?_) k
    · rw [Fin.cons_zero]; exact hXx.symm
    · refine Fin.cases ?_ (fun j => ?_) i
      · rw [Fin.cons_succ, Fin.cons_zero]; exact hYx.symm
      · refine Fin.cases ?_ (fun j' => ?_) j
        · rw [Fin.cons_succ, Fin.cons_succ]
          rw [show (![Z x] : Fin 1 → TangentSpace I x) 0 = Z x from rfl]
          exact hZx.symm
        · exact j'.elim0
  rw [hcomp]
  rw [raisedKoszul_covGrad_eq_covDerivRaisedKoszulVec (I := I) g₀ g₁ om X Y Z x]
  rw [homx, coframeS_one_eq_g0FlatCLM (I := I) (M := M) g₀ x e K]
  rw [show (g0FlatCLM (I := I) g₀ x (e (K 0)))
        (fun _ : Fin 1 => covDerivRaisedKoszulVec (I := I) g₀ g₁ X Y Z x) =
      cotangentToDual (I := I) (x := x) (g0FlatCLM (I := I) g₀ x (e (K 0)))
        (covDerivRaisedKoszulVec (I := I) g₀ g₁ X Y Z x) from
    (cotangentToDual_apply (I := I) (x := x) _ _).symm]
  rw [cotangentToDual_g0FlatCLM (I := I) g₀ x (e (K 0))]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
omit [FiniteDimensional ℝ E] in
private lemma sqrt_g0_inner_add_le_arm
    (g₀ : SmoothRiemannianMetric I M) (x : M) (a b : TangentSpace I x) :
    Real.sqrt (g₀.inner x (a + b) (a + b)) ≤
      Real.sqrt (g₀.inner x a a) + Real.sqrt (g₀.inner x b b) := by
  set na := Real.sqrt (g₀.inner x a a) with hna
  set nb := Real.sqrt (g₀.inner x b b) with hnb
  have haa_nn : 0 ≤ g₀.inner x a a := metric_inner_self_nonneg (I := I) (M := M) g₀ x a
  have hbb_nn : 0 ≤ g₀.inner x b b := metric_inner_self_nonneg (I := I) (M := M) g₀ x b
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
    have hsq : (na + nb) ^ 2 = na ^ 2 + 2 * (na * nb) + nb ^ 2 := by ring
    rw [hsq, hna_sq, hnb_sq]
    nlinarith [hcross]
  have hsum_pos_nn : 0 ≤ na + nb := add_nonneg hna_nn hnb_nn
  calc Real.sqrt (g₀.inner x (a + b) (a + b))
      ≤ Real.sqrt ((na + nb) ^ 2) := Real.sqrt_le_sqrt hle_sq
    _ = na + nb := by rw [Real.sqrt_sq hsum_pos_nn]

def sharpFlatRaiseEndoField (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x) where
  toFun := fun x : M => sharpFlatRaiseEndo (I := I) g₀ g₁ x
  contMDiff_toFun := sharpFlatRaiseEndo_contMDiff (I := I) g₀ g₁

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [SigmaCompactSpace M] in
@[simp] lemma sharpFlatRaiseEndoField_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (sharpFlatRaiseEndoField (I := I) (M := M) g₀ g₁ x) =
      sharpFlatRaiseEndo (I := I) g₀ g₁ x := rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
omit [SigmaCompactSpace M] in
private lemma covDerivRaisedKoszulVec_eq_endoCov_add_sharpFlat
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    covDerivRaisedKoszulVec (I := I) g₀ g₁ X Y Z x =
      ((endoCovariantDerivative (I := I) (M := M) g₀)
          (sharpFlatRaiseEndoField (I := I) (M := M) g₀ g₁) x (X x))
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Y x) (Z x))
      + sharpFlatRaiseEndo (I := I) g₀ g₁ x
          (covDerivConnDiff (I := I) g₀ g₁ (fun b => X b) (fun b => Z b) (fun b => Y b) x) := by
  classical
  set S : Π b : M, TangentSpace I b →L[ℝ] TangentSpace I b :=
    fun b => sharpFlatRaiseEndo (I := I) g₀ g₁ b with hS_def
  have hDsm : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ b (Y b) (Z b))) :=
    PDE.DeTurck.connDiff_contMDiff (I := I) g₁ g₀ Y.contMDiff Z.contMDiff
  set Dsec : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨fun b : M => PDE.DeTurck.connDiff (I := I) g₁ g₀ b (Y b) (Z b), hDsm⟩ with hDsec_def
  have hDsecx : Dsec x = PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Y x) (Z x) := rfl
  have hLeib := endoCovariantDerivative_apply (I := I) (M := M) g₀
    (sharpFlatRaiseEndoField (I := I) (M := M) g₀ g₁) Dsec x (X x)
  have hΛapp : (fun y : M => (sharpFlatRaiseEndoField (I := I) (M := M) g₀ g₁ y) (Dsec y)) =
      (fun y : M => raisedKoszulVec (I := I) g₀ g₁ y (Y y) (Z y)) := by
    funext y
    rw [sharpFlatRaiseEndoField_apply, hDsec_def]
    change sharpFlatRaiseEndo (I := I) g₀ g₁ y
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ y (Y y) (Z y)) = _
    rw [raisedKoszulVec]
  rw [hΛapp] at hLeib
  rw [sharpFlatRaiseEndoField_apply, hDsecx] at hLeib
  rw [covDerivRaisedKoszulVec]
  have hgrad_eq : (LeviCivita (I := I) g₀).toFun
        (fun b => raisedKoszulVec (I := I) g₀ g₁ b (Y b) (Z b)) x (X x) =
      ((endoCovariantDerivative (I := I) (M := M) g₀)
          (sharpFlatRaiseEndoField (I := I) (M := M) g₀ g₁) x (X x))
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Y x) (Z x))
      + sharpFlatRaiseEndo (I := I) g₀ g₁ x
          ((LeviCivita (I := I) g₀).toFun (fun b => Dsec b) x (X x)) := by
    have h : ((endoCovariantDerivative (I := I) (M := M) g₀)
          (sharpFlatRaiseEndoField (I := I) (M := M) g₀ g₁) x (X x))
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Y x) (Z x)) =
        (LeviCivita (I := I) g₀).toFun
            (fun b => raisedKoszulVec (I := I) g₀ g₁ b (Y b) (Z b)) x (X x) -
          sharpFlatRaiseEndo (I := I) g₀ g₁ x
            ((LeviCivita (I := I) g₀).toFun (fun b => Dsec b) x (X x)) := hLeib
    rw [h]; abel
  rw [hgrad_eq]
  set ET : TangentSpace I x :=
    ((endoCovariantDerivative (I := I) (M := M) g₀)
        (sharpFlatRaiseEndoField (I := I) (M := M) g₀ g₁) x (X x))
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Y x) (Z x)) with hET_def
  set gradY : TangentSpace I x :=
    (LeviCivita (I := I) g₀).toFun (fun b => Y b) x (X x) with hgradY_def
  set gradZ : TangentSpace I x :=
    (LeviCivita (I := I) g₀).toFun (fun b => Z b) x (X x) with hgradZ_def
  set gradD : TangentSpace I x :=
    (LeviCivita (I := I) g₀).toFun (fun b => Dsec b) x (X x) with hgradD_def
  have hrkY : raisedKoszulVec (I := I) g₀ g₁ x gradY (Z x) =
      sharpFlatRaiseEndo (I := I) g₀ g₁ x
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x gradY (Z x)) := by
    rw [raisedKoszulVec]
  have hrkZ : raisedKoszulVec (I := I) g₀ g₁ x (Y x) gradZ =
      sharpFlatRaiseEndo (I := I) g₀ g₁ x
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Y x) gradZ) := by
    rw [raisedKoszulVec]
  rw [hrkY, hrkZ]
  have hcollapse :
      ET + sharpFlatRaiseEndo (I := I) g₀ g₁ x gradD
        - sharpFlatRaiseEndo (I := I) g₀ g₁ x
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x gradY (Z x))
        - sharpFlatRaiseEndo (I := I) g₀ g₁ x
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Y x) gradZ) =
      ET + sharpFlatRaiseEndo (I := I) g₀ g₁ x
          (gradD - PDE.DeTurck.connDiff (I := I) g₁ g₀ x gradY (Z x)
            - PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Y x) gradZ) := by
    rw [map_sub, map_sub]; abel
  rw [hcollapse]
  congr 1
  rw [covDerivConnDiff, covDerivDiff]
  have hdiffSec_x : diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁)
        (fun b => Z b) (fun b => Y b) = fun b => Dsec b := by
    funext b
    rw [diffSec]
    rfl
  rw [hdiffSec_x, ← hgradD_def]
  have hcovApplyZ : covApply (LeviCivita (I := I) g₀) (fun b => X b) (fun b => Z b) x = gradZ := by
    rw [covApply_apply, hgradZ_def]
  have hcovApplyY : covApply (LeviCivita (I := I) g₀) (fun b => X b) (fun b => Y b) x = gradY := by
    rw [covApply_apply, hgradY_def]
  rw [hcovApplyZ, hcovApplyY]
  rw [show CovariantDerivative.difference (LeviCivita (I := I) g₁) (LeviCivita (I := I) g₀) x
        (Y x) gradZ = PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Y x) gradZ from rfl]
  rw [show CovariantDerivative.difference (LeviCivita (I := I) g₁) (LeviCivita (I := I) g₀) x
        gradY (Z x) = PDE.DeTurck.connDiff (I := I) g₁ g₀ x gradY (Z x) from rfl]
  abel

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem cotangent_g0FlatY_mdiffAtCotangent_g1
    (g₁ : SmoothRiemannianMetric I M)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    MDiffAtCotangent (I := I)
      (fun b : M => cotangentToCLM (I := I) (g0FlatCLM (I := I) g₁ b (Y b))) x := by
  have heq : (fun b : M => cotangentToCLM (I := I) (g0FlatCLM (I := I) g₁ b (Y b))) =
      metricFlat (I := I) g₁ (fun b : M => Y b) := by
    funext b
    apply ContinuousLinearMap.ext
    intro w
    rw [metricFlat_apply]
    change cotangentToDual (I := I) (g0FlatCLM (I := I) g₁ b (Y b)) w = _
    exact cotangentToDual_g0FlatCLM (I := I) g₁ b (Y b) w
  rw [heq]
  exact metricFlat_mdiff (I := I) g₁ (Y.contMDiff.mdifferentiableAt (by norm_num))

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
omit [SigmaCompactSpace M] in
private theorem endoCov_sharpFlatRaiseField_apply
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (v : TangentSpace I x) :
    ((endoCovariantDerivative (I := I) (M := M) g₀)
        (sharpFlatRaiseEndoField (I := I) (M := M) g₀ g₁) x v) (Y x) =
      inverseMetricSharpFib (I := I) g₀ x
          (dualToCotangent (I := I)
            ((cotangentCov (LeviCivita (I := I) g₀)).toFun
              (fun b : M => cotangentToCLM (I := I) (g0FlatCLM (I := I) g₁ b (Y b))) x v))
        - inverseMetricSharpFib (I := I) g₀ x
            (g0FlatCLM (I := I) g₁ x ((LeviCivita (I := I) g₀).toFun (fun y : M => Y y) x v)) := by
  classical
  set β : Π b : M, Tensor0SSpace 1 I b := fun b : M => g0FlatCLM (I := I) g₁ b (Y b) with hβdef
  set gradY : TangentSpace I x := (LeviCivita (I := I) g₀).toFun (fun y : M => Y y) x v with hgradY
  have hΛval : ∀ y : M, (sharpFlatRaiseEndoField (I := I) (M := M) g₀ g₁ y) (Y y) =
      (inverseMetricSharpFib (I := I) g₀ y) (β y) := by
    intro y
    rw [hβdef, sharpFlatRaiseEndoField_apply]
    exact sharpFlatRaiseEndo_apply (I := I) g₀ g₁ y (Y y)
  have hβ₀ : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y
        ((inverseMetricSharpFib (I := I) g₀ y) (β y))) x := by
    have hcong : (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y
        ((inverseMetricSharpFib (I := I) g₀ y) (β y))) =
        (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y
          ((sharpFlatRaiseEndoField (I := I) (M := M) g₀ g₁ y) (Y y))) := by
      funext y; rw [hΛval y]
    rw [hcong]
    exact (endoApplySection_contMDiff (I := I) (M := M)
      (sharpFlatRaiseEndoField (I := I) (M := M) g₀ g₁) Y x).mdifferentiableAt (by norm_num)
  have hLeibniz := endoCovariantDerivative_apply (I := I) (M := M) g₀
    (sharpFlatRaiseEndoField (I := I) (M := M) g₀ g₁) Y x v
  rw [hLeibniz]
  have hsplit : (LeviCivita (I := I) g₀)
        (fun y : M => (sharpFlatRaiseEndoField (I := I) (M := M) g₀ g₁ y) (Y y)) x v =
      inverseMetricSharpFib (I := I) g₀ x
        (dualToCotangent (I := I)
          ((cotangentCov (LeviCivita (I := I) g₀)).toFun
            (fun b : M => cotangentToCLM (I := I) (β b)) x v)) := by
    have hfun : (fun y : M => (sharpFlatRaiseEndoField (I := I) (M := M) g₀ g₁ y) (Y y)) =
        (fun b : M => (inverseMetricSharpFib (I := I) g₀ b) (β b)) := by
      funext y; rw [hΛval y]
    have hB := inverseMetricSharpField_covGrad_eq_zero (I := I) g₀ β hβ₀ v
    have hop : (LeviCivita (I := I) g₀).toFun
          (fun y : M => (sharpFlatRaiseEndoField (I := I) (M := M) g₀ g₁ y) (Y y)) x =
        (LeviCivita (I := I) g₀).toFun
          (fun b : M => (inverseMetricSharpFib (I := I) g₀ b) (β b)) x := by
      rw [hfun]
    have hopv := congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x => L v) hop
    simp only at hopv
    rw [show (LeviCivita (I := I) g₀)
          (fun y : M => (sharpFlatRaiseEndoField (I := I) (M := M) g₀ g₁ y) (Y y)) x v =
        (LeviCivita (I := I) g₀).toFun
          (fun y : M => (sharpFlatRaiseEndoField (I := I) (M := M) g₀ g₁ y) (Y y)) x v from rfl]
    rw [hopv, hB]
  rw [hsplit]
  have hΛx : (sharpFlatRaiseEndoField (I := I) (M := M) g₀ g₁ x) gradY =
      inverseMetricSharpFib (I := I) g₀ x (g0FlatCLM (I := I) g₁ x gradY) := by
    rw [sharpFlatRaiseEndoField_apply]
    exact sharpFlatRaiseEndo_apply (I := I) g₀ g₁ x gradY
  rw [show (LeviCivita (I := I) g₀) (fun y => Y y) x v = gradY from rfl, hΛx]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
omit [SigmaCompactSpace M] in
private theorem g0_inner_endoCov_sharpFlatRaise_eq
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (v z : TangentSpace I x) :
    g₀.inner x
        (((endoCovariantDerivative (I := I) (M := M) g₀)
          (sharpFlatRaiseEndoField (I := I) (M := M) g₀ g₁) x v) (Y x)) z =
      g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Y x) v) z
        + g₁.inner x (Y x) (PDE.DeTurck.connDiff (I := I) g₁ g₀ x z v) := by
  classical
  rw [endoCov_sharpFlatRaiseField_apply (I := I) (M := M) g₀ g₁ Y x v]
  set θ : Π b : M, TangentSpace I b →L[ℝ] ℝ :=
    fun b : M => cotangentToCLM (I := I) (g0FlatCLM (I := I) g₁ b (Y b)) with hθdef
  set gradY₀ : TangentSpace I x := (LeviCivita (I := I) g₀).toFun (fun y : M => Y y) x v with hgY0
  have hA : g₀.inner x
      (inverseMetricSharpFib (I := I) g₀ x
        (dualToCotangent (I := I) ((cotangentCov (LeviCivita (I := I) g₀)).toFun θ x v))) z =
      ((cotangentCov (LeviCivita (I := I) g₀)).toFun θ x v) z := by
    rw [inverseMetricSharpFib_inner (I := I) g₀ x _ z, cotangentToDualLinear_apply,
      cotangentToDual_dualToCotangent]
    rfl
  have hBb : g₀.inner x
      (inverseMetricSharpFib (I := I) g₀ x (g0FlatCLM (I := I) g₁ x gradY₀)) z =
      g₁.inner x gradY₀ z := by
    rw [inverseMetricSharpFib_inner (I := I) g₀ x _ z, cotangentToDualLinear_apply,
      cotangentToDual_g0FlatCLM (I := I) g₁ x gradY₀ z]
  rw [map_sub, ContinuousLinearMap.sub_apply, hA, hBb]
  have hθmd : MDiffAtCotangent (I := I) θ x := cotangent_g0FlatY_mdiffAtCotangent_g1 (I := I) g₁ Y x
  have hsplit := cotangentCov_leviCivita_connDiff (I := I) g₀ g₁ hθmd v z
  have hflatθ : θ = metricFlat (I := I) g₁ (fun b => Y b) := by
    funext b
    apply ContinuousLinearMap.ext
    intro w
    rw [hθdef, metricFlat_apply]
    change cotangentToDual (I := I) (g0FlatCLM (I := I) g₁ b (Y b)) w = _
    exact cotangentToDual_g0FlatCLM (I := I) g₁ b (Y b) w
  have hdual := cotangentCov_metricDuality (I := I) g₁
    (X := fun b => Y b) (Y.contMDiff.mdifferentiableAt (by norm_num)) v z
  rw [← hflatθ] at hdual
  set gradY₁ : TangentSpace I x := (LeviCivita (I := I) g₁).toFun (fun b => Y b) x v with hgY1
  have hθval : θ x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x z v) =
      g₁.inner x (Y x) (PDE.DeTurck.connDiff (I := I) g₁ g₀ x z v) := by
    rw [hθdef]
    change cotangentToDual (I := I) (g0FlatCLM (I := I) g₁ x (Y x))
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x z v) = _
    rw [cotangentToDual_g0FlatCLM (I := I) g₁ x (Y x) (PDE.DeTurck.connDiff (I := I) g₁ g₀ x z v)]
  have hcg0 : ((cotangentCov (LeviCivita (I := I) g₀)).toFun θ x v) z =
      g₁.inner x gradY₁ z + g₁.inner x (Y x) (PDE.DeTurck.connDiff (I := I) g₁ g₀ x z v) := by
    have hstep : ((cotangentCov (LeviCivita (I := I) g₀)).toFun θ x v) z =
        ((cotangentCov (LeviCivita (I := I) g₁)).toFun θ x v) z
          + θ x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x z v) := by linarith [hsplit]
    rw [hstep, hdual, hθval]
  rw [hcg0]
  have hconnY : PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Y x) v = gradY₁ - gradY₀ := by
    have hca := PDE.DeTurck.connDiff_apply (I := I) g₁ g₀ (σ := fun b => Y b)
      (Y.contMDiff.mdifferentiableAt (by norm_num)) v
    rw [hgY1, hgY0]
    exact hca
  rw [hconnY, map_sub, ContinuousLinearMap.sub_apply]
  ring

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma sqrt_g1_le_sqrt_g0_of_realize
    (g₀ g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (h : ∀ y v w, g₁.inner y v w =
      g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
    {δ : ℝ}
    (hbound : metricCauchySchwarzBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (x : M) (a : TangentSpace I x) :
    Real.sqrt (g₁.inner x a a) ≤ Real.sqrt (1 + δ) * Real.sqrt (g₀.inner x a a) := by
  have hub := g1_self_upper_bound (I := I) g₀ g₁ T h hbound x a
  have hnn : 0 ≤ g₀.inner x a a := metric_inner_self_nonneg (I := I) (M := M) g₀ x a
  have hg1nn : 0 ≤ g₁.inner x a a := metric_inner_self_nonneg (I := I) (M := M) g₁ x a
  rcases le_or_gt (1 + δ) 0 with hd | hd
  · have hle0 : g₁.inner x a a ≤ 0 := le_trans hub (mul_nonpos_of_nonpos_of_nonneg hd hnn)
    have hg1z : g₁.inner x a a = 0 := le_antisymm hle0 hg1nn
    rw [hg1z, Real.sqrt_zero]
    positivity
  · calc Real.sqrt (g₁.inner x a a)
        ≤ Real.sqrt ((1 + δ) * g₀.inner x a a) := Real.sqrt_le_sqrt hub
      _ = Real.sqrt (1 + δ) * Real.sqrt (g₀.inner x a a) := by
          rw [Real.sqrt_mul (le_of_lt hd)]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma sqrt_self_of_inner_le
    (g₀ : SmoothRiemannianMetric I M) (x : M) (u : TangentSpace I x) (K : ℝ) (hK : 0 ≤ K)
    (hbd : ∀ z : TangentSpace I x, g₀.inner x u z ≤ K * Real.sqrt (g₀.inner x z z)) :
    Real.sqrt (g₀.inner x u u) ≤ K := by
  have huu_nn : 0 ≤ g₀.inner x u u := metric_inner_self_nonneg (I := I) (M := M) g₀ x u
  have hself := hbd u
  set Nu : ℝ := Real.sqrt (g₀.inner x u u) with hNu
  have hNu_nn : 0 ≤ Nu := Real.sqrt_nonneg _
  have hNu_sq : Nu * Nu = g₀.inner x u u := by
    rw [hNu, ← Real.sqrt_mul huu_nn, Real.sqrt_mul_self huu_nn]
  rcases eq_or_lt_of_le hNu_nn with h0 | hpos
  · rw [← h0]; exact hK
  · have hle : Nu * Nu ≤ K * Nu := by rw [hNu_sq, hNu]; exact hself
    exact le_of_mul_le_mul_right hle hpos

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
omit [NeZero (Module.finrank ℝ E)] in
private lemma sqrt_inner_endoCov_sharpFlatRaiseEndo_apply_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g₁ : SmoothRiemannianMetric I M)
      (T : SmoothCcTensor g₀ 0 2)
      (_h : ∀ y v w, g₁.inner y v w =
        g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
      {δ : ℝ} (_hδ : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
      (_hbound : metricCauchySchwarzBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
      (x : M) (v w : TangentSpace I x),
      letI : Bundle.RiemannianBundle
          (fun y : M => Tensor0SBundle.TensorRSSpace 0 3 I y) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
      Real.sqrt (g₀.inner x
          (((endoCovariantDerivative (I := I) (M := M) g₀)
            (sharpFlatRaiseEndoField (I := I) (M := M) g₀ g₁) x v) w)
          (((endoCovariantDerivative (I := I) (M := M) g₀)
            (sharpFlatRaiseEndoField (I := I) (M := M) g₀ g₁) x v) w)) ≤
        C * ‖((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x :
            Tensor0SBundle.TensorRSSpace 0 3 I x)‖ *
          Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) := by
  classical
  letI instTens : Bundle.RiemannianBundle
      (fun y : M => Tensor0SBundle.TensorRSSpace 0 3 I y) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
  obtain ⟨C₀, hC₀0, hpw⟩ :=
    connDiff_gFibreNorm_le_iteratedCovGrad_of_lt_one (I := I) (M := M) g₀ hδ₀0 hδ₀
  refine ⟨2 * (1 + δ₀) * C₀, by positivity, ?_⟩
  intro g₁ T h δ hδ hδ0 hbound x v w
  obtain ⟨Y, hYx⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
    (F := E) (V := (TangentSpace I : M → Type _)) x w
  set G : ℝ := ‖((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x :
      Tensor0SBundle.TensorRSSpace 0 3 I x)‖ with hG_def
  have hG_nn : 0 ≤ G := norm_nonneg _
  set Nv : ℝ := Real.sqrt (g₀.inner x v v) with hNv_def
  set Nw : ℝ := Real.sqrt (g₀.inner x w w) with hNw_def
  have hNv_nn : 0 ≤ Nv := Real.sqrt_nonneg _
  have hNw_nn : 0 ≤ Nw := Real.sqrt_nonneg _
  set u : TangentSpace I x :=
    ((endoCovariantDerivative (I := I) (M := M) g₀)
      (sharpFlatRaiseEndoField (I := I) (M := M) g₀ g₁) x v) w with hu_def
  have hbd : ∀ z : TangentSpace I x,
      g₀.inner x u z ≤ (2 * (1 + δ₀) * C₀ * G * Nv * Nw) * Real.sqrt (g₀.inner x z z) := by
    intro z
    set Nz : ℝ := Real.sqrt (g₀.inner x z z) with hNz_def
    have hNz_nn : 0 ≤ Nz := Real.sqrt_nonneg _
    have hform := g0_inner_endoCov_sharpFlatRaise_eq (I := I) (M := M) g₀ g₁ Y x v z
    rw [hYx] at hform
    rw [← hu_def] at hform
    rw [hform]
    set cw : TangentSpace I x := PDE.DeTurck.connDiff (I := I) g₁ g₀ x w v with hcw_def
    set cz : TangentSpace I x := PDE.DeTurck.connDiff (I := I) g₁ g₀ x z v with hcz_def
    have hcs1 : g₁.inner x cw z ≤
        Real.sqrt (g₁.inner x cw cw) * Real.sqrt (g₁.inner x z z) := by
      have habs := abs_metric_inner_le_sqrt_metric_quadratic (I := I) (M := M) g₁ x cw z
      exact le_trans (le_abs_self _) habs
    have hcs2 : g₁.inner x w cz ≤
        Real.sqrt (g₁.inner x w w) * Real.sqrt (g₁.inner x cz cz) := by
      have habs := abs_metric_inner_le_sqrt_metric_quadratic (I := I) (M := M) g₁ x w cz
      exact le_trans (le_abs_self _) habs
    have h1d_nn : 0 ≤ Real.sqrt (1 + δ) := Real.sqrt_nonneg _
    have hconn_w := hpw g₁ T h hδ hδ0 hbound x w v
    rw [← hG_def, ← hNv_def, ← hNw_def, ← hcw_def] at hconn_w
    have hcw_g0 : Real.sqrt (g₀.inner x cw cw) ≤ C₀ * G * Nw * Nv := hconn_w
    have hcw_g1 : Real.sqrt (g₁.inner x cw cw) ≤ Real.sqrt (1 + δ) * (C₀ * G * Nw * Nv) := by
      refine le_trans (sqrt_g1_le_sqrt_g0_of_realize (I := I) g₀ g₁ T h hbound x cw) ?_
      exact mul_le_mul_of_nonneg_left hcw_g0 h1d_nn
    have hz_g1 : Real.sqrt (g₁.inner x z z) ≤ Real.sqrt (1 + δ) * Nz := by
      rw [hNz_def]; exact sqrt_g1_le_sqrt_g0_of_realize (I := I) g₀ g₁ T h hbound x z
    have hw_g1 : Real.sqrt (g₁.inner x w w) ≤ Real.sqrt (1 + δ) * Nw := by
      rw [hNw_def]; exact sqrt_g1_le_sqrt_g0_of_realize (I := I) g₀ g₁ T h hbound x w
    have hconn_z := hpw g₁ T h hδ hδ0 hbound x z v
    rw [← hG_def, ← hNv_def, ← hNz_def, ← hcz_def] at hconn_z
    have hcz_g0 : Real.sqrt (g₀.inner x cz cz) ≤ C₀ * G * Nz * Nv := hconn_z
    have hcz_g1 : Real.sqrt (g₁.inner x cz cz) ≤ Real.sqrt (1 + δ) * (C₀ * G * Nz * Nv) := by
      refine le_trans (sqrt_g1_le_sqrt_g0_of_realize (I := I) g₀ g₁ T h hbound x cz) ?_
      exact mul_le_mul_of_nonneg_left hcz_g0 h1d_nn
    have hd_nn : 0 ≤ (1:ℝ) + δ := by linarith
    have hroot_sq : Real.sqrt (1 + δ) * Real.sqrt (1 + δ) = 1 + δ := by
      rw [← Real.sqrt_mul hd_nn, Real.sqrt_mul_self hd_nn]
    have hCGnn : 0 ≤ C₀ * G * Nw * Nv := by positivity
    have hCGnn' : 0 ≤ C₀ * G * Nz * Nv := by positivity
    have hterm1 : g₁.inner x cw z ≤ (1 + δ) * (C₀ * G * Nw * Nv) * Nz := by
      calc g₁.inner x cw z
          ≤ Real.sqrt (g₁.inner x cw cw) * Real.sqrt (g₁.inner x z z) := hcs1
        _ ≤ (Real.sqrt (1 + δ) * (C₀ * G * Nw * Nv)) * (Real.sqrt (1 + δ) * Nz) := by
            refine mul_le_mul hcw_g1 hz_g1 (Real.sqrt_nonneg _) ?_
            positivity
        _ = (1 + δ) * (C₀ * G * Nw * Nv) * Nz := by
            rw [show (Real.sqrt (1 + δ) * (C₀ * G * Nw * Nv)) * (Real.sqrt (1 + δ) * Nz)
                = (Real.sqrt (1 + δ) * Real.sqrt (1 + δ)) * ((C₀ * G * Nw * Nv) * Nz) from by ring,
              hroot_sq]; ring
    have hterm2 : g₁.inner x w cz ≤ (1 + δ) * (C₀ * G * Nz * Nv) * Nw := by
      calc g₁.inner x w cz
          ≤ Real.sqrt (g₁.inner x w w) * Real.sqrt (g₁.inner x cz cz) := hcs2
        _ ≤ (Real.sqrt (1 + δ) * Nw) * (Real.sqrt (1 + δ) * (C₀ * G * Nz * Nv)) := by
            refine mul_le_mul hw_g1 hcz_g1 (Real.sqrt_nonneg _) ?_
            positivity
        _ = (1 + δ) * (C₀ * G * Nz * Nv) * Nw := by
            rw [show (Real.sqrt (1 + δ) * Nw) * (Real.sqrt (1 + δ) * (C₀ * G * Nz * Nv))
                = (Real.sqrt (1 + δ) * Real.sqrt (1 + δ)) * (Nw * (C₀ * G * Nz * Nv)) from by ring,
              hroot_sq]; ring
    have hsum : g₁.inner x cw z + g₁.inner x w cz ≤
        (2 * (1 + δ₀) * C₀ * G * Nv * Nw) * Nz := by
      have hδle : (1:ℝ) + δ ≤ 1 + δ₀ := by linarith
      have e1 : (1 + δ) * (C₀ * G * Nw * Nv) * Nz ≤ (1 + δ₀) * (C₀ * G * Nw * Nv) * Nz := by
        apply mul_le_mul_of_nonneg_right _ hNz_nn
        apply mul_le_mul_of_nonneg_right hδle hCGnn
      have e2 : (1 + δ) * (C₀ * G * Nz * Nv) * Nw ≤ (1 + δ₀) * (C₀ * G * Nz * Nv) * Nw := by
        apply mul_le_mul_of_nonneg_right _ hNw_nn
        apply mul_le_mul_of_nonneg_right hδle hCGnn'
      calc g₁.inner x cw z + g₁.inner x w cz
          ≤ (1 + δ₀) * (C₀ * G * Nw * Nv) * Nz + (1 + δ₀) * (C₀ * G * Nz * Nv) * Nw :=
            add_le_add (le_trans hterm1 e1) (le_trans hterm2 e2)
        _ = (2 * (1 + δ₀) * C₀ * G * Nv * Nw) * Nz := by ring
    rw [hcw_def, hcz_def] at hsum
    exact hsum
  have hK_nn : 0 ≤ 2 * (1 + δ₀) * C₀ * G * Nv * Nw := by positivity
  have hres := sqrt_self_of_inner_le (I := I) g₀ x u (2 * (1 + δ₀) * C₀ * G * Nv * Nw) hK_nn hbd
  rw [hu_def] at hres
  rw [hG_def, hNv_def, hNw_def] at hres
  exact hres

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
omit [NeZero (Module.finrank ℝ E)] in
private lemma abs_unitModel4_iteratedCovGrad_symmS_le
    (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2) (x : M)
    (a b c d : TangentSpace I x) :
    letI : Bundle.RiemannianBundle
        (fun y : M => Tensor0SBundle.TensorRSSpace 0 4 I y) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 4
    |unitModel (I := I) (M := M) g₀ 4
        (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) g₀ T)) x ![a, b, c, d]| ≤
      ‖((iteratedCovGrad (I := I) g₀ 0 2 2 T).toSection x :
          Tensor0SBundle.TensorRSSpace 0 4 I x)‖ *
        Real.sqrt (g₀.inner x a a) * Real.sqrt (g₀.inner x b b) *
          Real.sqrt (g₀.inner x c c) * Real.sqrt (g₀.inner x d d) := by
  letI instTens : Bundle.RiemannianBundle
      (fun y : M => Tensor0SBundle.TensorRSSpace 0 4 I y) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 4
  set W : Tensor0SBundle.TensorRSSpace 0 4 I x :=
    (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) g₀ T)).toSection x with hW_def
  have hunit : unitModel (I := I) (M := M) g₀ 4
        (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) g₀ T)) x ![a, b, c, d] =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from W)
          (unitZeroSec (I := I) (M := M) x))
        (Fin.cons a (Fin.cons b (Fin.cons c ![d]))) := by
    rw [unitModel]
    rfl
  rw [hunit]
  have hprim := abs_tensor04_unit_eval_le_fibreNorm_mul_sqrt (I := I) (M := M) g₀ x W a b c d
  refine le_trans hprim ?_
  have hnorm_le := norm_iteratedCovGrad_two_symmS_le (I := I) (M := M) g₀ T x
  rw [← hW_def] at hnorm_le
  have hsqrt_nn : 0 ≤ Real.sqrt (g₀.inner x a a) * Real.sqrt (g₀.inner x b b) *
      Real.sqrt (g₀.inner x c c) * Real.sqrt (g₀.inner x d d) := by positivity
  calc ‖(W : Tensor0SBundle.TensorRSSpace 0 4 I x)‖ *
        Real.sqrt (g₀.inner x a a) * Real.sqrt (g₀.inner x b b) *
          Real.sqrt (g₀.inner x c c) * Real.sqrt (g₀.inner x d d)
      = ‖(W : Tensor0SBundle.TensorRSSpace 0 4 I x)‖ *
          (Real.sqrt (g₀.inner x a a) * Real.sqrt (g₀.inner x b b) *
            Real.sqrt (g₀.inner x c c) * Real.sqrt (g₀.inner x d d)) := by ring
    _ ≤ ‖((iteratedCovGrad (I := I) g₀ 0 2 2 T).toSection x :
            Tensor0SBundle.TensorRSSpace 0 4 I x)‖ *
          (Real.sqrt (g₀.inner x a a) * Real.sqrt (g₀.inner x b b) *
            Real.sqrt (g₀.inner x c c) * Real.sqrt (g₀.inner x d d)) :=
        mul_le_mul_of_nonneg_right hnorm_le hsqrt_nn
    _ = ‖((iteratedCovGrad (I := I) g₀ 0 2 2 T).toSection x :
            Tensor0SBundle.TensorRSSpace 0 4 I x)‖ *
          Real.sqrt (g₀.inner x a a) * Real.sqrt (g₀.inner x b b) *
            Real.sqrt (g₀.inner x c c) * Real.sqrt (g₀.inner x d d) := by ring

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma sqrt_g0_self_of_g1_inner_le
    (g₀ g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (h : ∀ y v w, g₁.inner y v w =
      g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hbound : metricCauchySchwarzBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (x : M) (u : TangentSpace I x) (K : ℝ) (hK : 0 ≤ K)
    (hbd : ∀ z : TangentSpace I x, g₁.inner x u z ≤ K * Real.sqrt (g₀.inner x z z)) :
    Real.sqrt (g₀.inner x u u) ≤ (1 / (1 - δ)) * K := by
  have hcoeff : 0 < 1 - δ := by linarith
  set Nu : ℝ := Real.sqrt (g₀.inner x u u) with hNu_def
  have hNu_nn : 0 ≤ Nu := Real.sqrt_nonneg _
  have hbd0 : ∀ z : TangentSpace I x,
      g₀.inner x u z ≤ (K + δ * Nu) * Real.sqrt (g₀.inner x z z) := by
    intro z
    set Nz : ℝ := Real.sqrt (g₀.inner x z z) with hNz_def
    have hNz_nn : 0 ≤ Nz := Real.sqrt_nonneg _
    have hg1 := hbd z
    rw [← hNz_def] at hg1
    have hcc : g₀.inner x u z = g₁.inner x u z - ccTensorBilinSymm (I := I) g₀ T x u z := by
      rw [h x u z]; ring
    have hgate := hbound x u z
    have habs : |ccTensorBilinSymm (I := I) g₀ T x u z| ≤ δ * Nu * Nz := by
      rw [hNu_def, hNz_def]; exact hgate
    have hcc_le : - ccTensorBilinSymm (I := I) g₀ T x u z ≤ δ * Nu * Nz := by
      have := (abs_le.mp habs).1
      linarith
    rw [hcc]
    calc g₁.inner x u z - ccTensorBilinSymm (I := I) g₀ T x u z
        ≤ K * Nz + δ * Nu * Nz := by linarith [hg1, hcc_le]
      _ = (K + δ * Nu) * Nz := by ring
  have hKstep : 0 ≤ K + δ * Nu := by positivity
  have hbd' := sqrt_self_of_inner_le (I := I) g₀ x u (K + δ * Nu) hKstep hbd0
  rw [← hNu_def] at hbd'
  have hfinal : (1 - δ) * Nu ≤ K := by nlinarith [hbd', hNu_nn, hδ0]
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hcoeff]
  nlinarith [hfinal]

private lemma weighted_sum_le_of_sq_and_linear_bounds
    (G1 G2 Q NX NY NZ Nζ C₀ δ δ₀ R : ℝ)
    (_hG1_nn : 0 ≤ G1) (_hG2_nn : 0 ≤ G2) (hQ_nn : 0 ≤ Q)
    (hNX_nn : 0 ≤ NX) (hNY_nn : 0 ≤ NY) (hNZ_nn : 0 ≤ NZ) (hNζ_nn : 0 ≤ Nζ)
    (_hC₀0 : 0 ≤ C₀) (hR1_nn : 0 ≤ 1 + R)
    (hG1sq_le : G1 ^ 2 ≤ (1 + R) * Q) (hG2_le : G2 ≤ (1 + R) * Q)
    (hδ_le : (1 : ℝ) + δ ≤ 1 + δ₀) (hδ_nn : 0 ≤ 1 + δ) :
    (3 / 2 : ℝ) * G2 * NX * NY * NZ * Nζ +
        2 * (1 + δ) * C₀ ^ 2 * G1 ^ 2 * NX * NY * NZ * Nζ ≤
      ((3 / 2) + 2 * (1 + δ₀) * C₀ ^ 2) * (1 + R) * Q * NX * NY * NZ * Nζ := by
  have hP_nn : 0 ≤ NX * NY * NZ * Nζ := by positivity
  have hRQ_nn : 0 ≤ (1 + R) * Q := mul_nonneg hR1_nn hQ_nn
  have hA : (3 / 2 : ℝ) * G2 * NX * NY * NZ * Nζ ≤
      (3 / 2 : ℝ) * ((1 + R) * Q) * (NX * NY * NZ * Nζ) := by
    have hstep : (3 / 2 : ℝ) * G2 ≤ (3 / 2 : ℝ) * ((1 + R) * Q) :=
      mul_le_mul_of_nonneg_left hG2_le (by norm_num)
    calc (3 / 2 : ℝ) * G2 * NX * NY * NZ * Nζ
        = ((3 / 2 : ℝ) * G2) * (NX * NY * NZ * Nζ) := by ring
      _ ≤ ((3 / 2 : ℝ) * ((1 + R) * Q)) * (NX * NY * NZ * Nζ) :=
          mul_le_mul_of_nonneg_right hstep hP_nn
      _ = (3 / 2 : ℝ) * ((1 + R) * Q) * (NX * NY * NZ * Nζ) := by ring
  have hcoeff_le : 2 * (1 + δ) * C₀ ^ 2 ≤ 2 * (1 + δ₀) * C₀ ^ 2 := by
    have : (1 + δ) * C₀ ^ 2 ≤ (1 + δ₀) * C₀ ^ 2 :=
      mul_le_mul_of_nonneg_right hδ_le (sq_nonneg _)
    linarith
  have hcoeff_nn : (0 : ℝ) ≤ 2 * (1 + δ) * C₀ ^ 2 := by positivity
  have hB : 2 * (1 + δ) * C₀ ^ 2 * G1 ^ 2 * NX * NY * NZ * Nζ ≤
      2 * (1 + δ₀) * C₀ ^ 2 * ((1 + R) * Q) * (NX * NY * NZ * Nζ) := by
    have hstep : 2 * (1 + δ) * C₀ ^ 2 * G1 ^ 2 ≤ 2 * (1 + δ₀) * C₀ ^ 2 * ((1 + R) * Q) := by
      calc 2 * (1 + δ) * C₀ ^ 2 * G1 ^ 2
          ≤ 2 * (1 + δ) * C₀ ^ 2 * ((1 + R) * Q) :=
            mul_le_mul_of_nonneg_left hG1sq_le hcoeff_nn
        _ ≤ 2 * (1 + δ₀) * C₀ ^ 2 * ((1 + R) * Q) :=
            mul_le_mul_of_nonneg_right hcoeff_le hRQ_nn
    calc 2 * (1 + δ) * C₀ ^ 2 * G1 ^ 2 * NX * NY * NZ * Nζ
        = (2 * (1 + δ) * C₀ ^ 2 * G1 ^ 2) * (NX * NY * NZ * Nζ) := by ring
      _ ≤ (2 * (1 + δ₀) * C₀ ^ 2 * ((1 + R) * Q)) * (NX * NY * NZ * Nζ) :=
          mul_le_mul_of_nonneg_right hstep hP_nn
      _ = 2 * (1 + δ₀) * C₀ ^ 2 * ((1 + R) * Q) * (NX * NY * NZ * Nζ) := by ring
  calc (3 / 2 : ℝ) * G2 * NX * NY * NZ * Nζ +
        2 * (1 + δ) * C₀ ^ 2 * G1 ^ 2 * NX * NY * NZ * Nζ
      ≤ (3 / 2 : ℝ) * ((1 + R) * Q) * (NX * NY * NZ * Nζ) +
          2 * (1 + δ₀) * C₀ ^ 2 * ((1 + R) * Q) * (NX * NY * NZ * Nζ) := add_le_add hA hB
    _ = ((3 / 2) + 2 * (1 + δ₀) * C₀ ^ 2) * (1 + R) * Q * NX * NY * NZ * Nζ := by ring

set_option maxHeartbeats 12800000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
omit [NeZero (Module.finrank ℝ E)] in
private lemma g1_inner_covDerivConnDiff_le_pointwise
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1)
    (C₀ : ℝ) (hC₀0 : 0 ≤ C₀)
    (hconn : ∀ (g₁ : SmoothRiemannianMetric I M)
      (T : SmoothCcTensor g₀ 0 2)
      (_h : ∀ y v w, g₁.inner y v w =
        g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
      {δ : ℝ} (_hδ : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
      (_hbound : metricCauchySchwarzBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
      (x : M) (v w : TangentSpace I x),
      letI : Bundle.RiemannianBundle
          (fun y : M => Tensor0SBundle.TensorRSSpace 0 3 I y) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
      Real.sqrt (g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x v w)
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x v w)) ≤
        C₀ * ‖((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x :
            Tensor0SBundle.TensorRSSpace 0 3 I x)‖ *
          Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w))
    (g₁ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2)
    (h : ∀ y v w, g₁.inner y v w =
      g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
    {δ : ℝ} (hδ : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
    (hbound : metricCauchySchwarzBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (x : M)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {R : ℝ} (hR0 : 0 ≤ R)
    (hjet :
      letI : Bundle.RiemannianBundle
          (fun y : M => Tensor0SBundle.TensorRSSpace 0 3 I y) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
      ‖((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x :
          Tensor0SBundle.TensorRSSpace 0 3 I x)‖ ≤ R)
    (ζ : TangentSpace I x) :
    letI : Bundle.RiemannianBundle
        (fun y : M => Tensor0SBundle.TensorRSSpace 0 3 I y) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
    letI : Bundle.RiemannianBundle
        (fun y : M => Tensor0SBundle.TensorRSSpace 0 4 I y) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 4
    g₁.inner x
        (covDerivConnDiff (I := I) g₀ g₁ (fun b => X b) (fun b => Z b) (fun b => Y b) x) ζ ≤
      (((3 / 2) + 2 * (1 + δ₀) * C₀ ^ 2) *
          (1 + R) *
          Real.sqrt (‖((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x :
                Tensor0SBundle.TensorRSSpace 0 3 I x)‖ ^ 2 +
              ‖((iteratedCovGrad (I := I) g₀ 0 2 2 T).toSection x :
                Tensor0SBundle.TensorRSSpace 0 4 I x)‖ ^ 2) *
          Real.sqrt (g₀.inner x (X x) (X x)) * Real.sqrt (g₀.inner x (Y x) (Y x)) *
          Real.sqrt (g₀.inner x (Z x) (Z x))) * Real.sqrt (g₀.inner x ζ ζ) := by
  classical
  letI inst3 : Bundle.RiemannianBundle
      (fun y : M => Tensor0SBundle.TensorRSSpace 0 3 I y) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
  letI inst4 : Bundle.RiemannianBundle
      (fun y : M => Tensor0SBundle.TensorRSSpace 0 4 I y) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 4
  have hg₁ : ∀ (b : M) (u w : TangentSpace I b),
      g₁.inner b u w = g₀.inner b u w + ccTensorBilinSymm (I := I) g₀ T b u w :=
    fun b u w => h b u w
  have hδ_lt1 : δ < 1 := by linarith
  set G1 : ℝ := ‖((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x :
      Tensor0SBundle.TensorRSSpace 0 3 I x)‖ with hG1_def
  set G2 : ℝ := ‖((iteratedCovGrad (I := I) g₀ 0 2 2 T).toSection x :
      Tensor0SBundle.TensorRSSpace 0 4 I x)‖ with hG2_def
  have hG1_nn : 0 ≤ G1 := norm_nonneg _
  have hG2_nn : 0 ≤ G2 := norm_nonneg _
  set Q : ℝ := Real.sqrt (G1 ^ 2 + G2 ^ 2) with hQ_def
  have hQ_nn : 0 ≤ Q := Real.sqrt_nonneg _
  have hG1_le_Q : G1 ≤ Q := by
    have hle : G1 ^ 2 ≤ G1 ^ 2 + G2 ^ 2 := by nlinarith [sq_nonneg G2]
    have h1 : Real.sqrt (G1 ^ 2) ≤ Q := by rw [hQ_def]; exact Real.sqrt_le_sqrt hle
    rwa [Real.sqrt_sq hG1_nn] at h1
  have hG2_le_Q : G2 ≤ Q := by
    have hle : G2 ^ 2 ≤ G1 ^ 2 + G2 ^ 2 := by nlinarith [sq_nonneg G1]
    have h1 : Real.sqrt (G2 ^ 2) ≤ Q := by rw [hQ_def]; exact Real.sqrt_le_sqrt hle
    rwa [Real.sqrt_sq hG2_nn] at h1
  have hjet' : G1 ≤ R := hjet
  have hR1_nn : 0 ≤ 1 + R := by linarith
  set NX : ℝ := Real.sqrt (g₀.inner x (X x) (X x)) with hNX_def
  set NY : ℝ := Real.sqrt (g₀.inner x (Y x) (Y x)) with hNY_def
  set NZ : ℝ := Real.sqrt (g₀.inner x (Z x) (Z x)) with hNZ_def
  have hNX_nn : 0 ≤ NX := Real.sqrt_nonneg _
  have hNY_nn : 0 ≤ NY := Real.sqrt_nonneg _
  have hNZ_nn : 0 ≤ NZ := Real.sqrt_nonneg _
  set D : TangentSpace I x :=
    covDerivConnDiff (I := I) g₀ g₁ (fun b => X b) (fun b => Z b) (fun b => Y b) x with hD_def
  set Kc : ℝ := ((3 / 2) + 2 * (1 + δ₀) * C₀ ^ 2) * (1 + R) * Q * NX * NY * NZ with hKc_def
  have h1δ_nn : 0 ≤ 1 + δ := by linarith
  have hroot1δ_nn : 0 ≤ Real.sqrt (1 + δ) := Real.sqrt_nonneg _
  have hroot1δ_sq : Real.sqrt (1 + δ) * Real.sqrt (1 + δ) = 1 + δ := by
    rw [← Real.sqrt_mul h1δ_nn, Real.sqrt_mul_self h1δ_nn]
  change g₁.inner x D ζ ≤ Kc * Real.sqrt (g₀.inner x ζ ζ)
  set Nζ : ℝ := Real.sqrt (g₀.inner x ζ ζ) with hNζ_def
  have hNζ_nn : 0 ≤ Nζ := Real.sqrt_nonneg _
  have hident := covDerivConnDiff_g1inner_eq_half_secondCovGrad_sub_connDiffSq
    (I := I) (M := M) g₀ g₁ T hg₁ X Y Z x ζ
  rw [← hD_def] at hident
  set ζf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) x ζ, smoothExtensionTangent_contMDiff (I := I) x ζ⟩
    with hζf_def
  have hζfx : ζf x = ζ := smoothExtensionTangent_eq (I := I) x ζ
  have hR41 := abs_unitModel4_iteratedCovGrad_symmS_le (I := I) (M := M) g₀ T x
    (X x) (Z x) (Y x) ζ
  have hR42 := abs_unitModel4_iteratedCovGrad_symmS_le (I := I) (M := M) g₀ T x
    (X x) (Y x) (Z x) ζ
  have hR43 := abs_unitModel4_iteratedCovGrad_symmS_le (I := I) (M := M) g₀ T x
    (X x) ζ (Z x) (Y x)
  rw [← hG2_def, ← hNX_def, ← hNY_def, ← hNZ_def, ← hNζ_def] at hR41 hR42 hR43
  set R41 : ℝ := unitModel (I := I) (M := M) g₀ 4
    (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) g₀ T)) x ![X x, Z x, Y x, ζ] with hR41_def
  set R42 : ℝ := unitModel (I := I) (M := M) g₀ 4
    (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) g₀ T)) x ![X x, Y x, Z x, ζ] with hR42_def
  set R43 : ℝ := unitModel (I := I) (M := M) g₀ 4
    (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) g₀ T)) x ![X x, ζ, Z x, Y x] with hR43_def
  set cYZ : TangentSpace I x := PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Y x) (Z x) with hcYZ_def
  have hT2eq : inverseMetricSharpFib (I := I) g₁ x
        (koszulCovGradCovec (I := I) (M := M) g₀ g₁ X ζf x) =
      PDE.DeTurck.connDiff (I := I) g₁ g₀ x ζ (X x) := by
    have := connDiff_eq_appCc_invGram_covGrad (I := I) (M := M) g₀ g₁ X ζf x
    rw [hζfx] at this
    exact this.symm
  have hT5eq : inverseMetricSharpFib (I := I) g₁ x
        (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y x) = cYZ := by
    have := connDiff_eq_appCc_invGram_covGrad (I := I) (M := M) g₀ g₁ Z Y x
    rw [hcYZ_def]; exact this.symm
  rw [show (koszulCovGradCovec (I := I) (M := M) g₀ g₁ X
        ⟨smoothExtensionTangent (I := I) x ζ,
          smoothExtensionTangent_contMDiff (I := I) x ζ⟩ x) =
      koszulCovGradCovec (I := I) (M := M) g₀ g₁ X ζf x from rfl] at hident
  rw [hT2eq, hT5eq] at hident
  set cζX : TangentSpace I x := PDE.DeTurck.connDiff (I := I) g₁ g₀ x ζ (X x) with hcζX_def
  set cWX : TangentSpace I x := PDE.DeTurck.connDiff (I := I) g₁ g₀ x cYZ (X x) with hcWX_def
  have hcYZ_g0 : Real.sqrt (g₀.inner x cYZ cYZ) ≤ C₀ * G1 * NY * NZ := by
    have := hconn g₁ T h hδ hδ0 hbound x (Y x) (Z x)
    rw [← hG1_def, ← hNY_def, ← hNZ_def, ← hcYZ_def] at this
    exact this
  have hcζX_g0 : Real.sqrt (g₀.inner x cζX cζX) ≤ C₀ * G1 * Nζ * NX := by
    have := hconn g₁ T h hδ hδ0 hbound x ζ (X x)
    rw [← hG1_def, ← hNζ_def, ← hNX_def, ← hcζX_def] at this
    exact this
  have hcYZ_g0_nn : 0 ≤ Real.sqrt (g₀.inner x cYZ cYZ) := Real.sqrt_nonneg _
  have hcWX_g0 : Real.sqrt (g₀.inner x cWX cWX) ≤ C₀ * G1 * (C₀ * G1 * NY * NZ) * NX := by
    have hraw := hconn g₁ T h hδ hδ0 hbound x cYZ (X x)
    rw [← hG1_def, ← hNX_def, ← hcWX_def] at hraw
    refine le_trans hraw ?_
    have hstep : C₀ * G1 * Real.sqrt (g₀.inner x cYZ cYZ) * NX ≤
        C₀ * G1 * (C₀ * G1 * NY * NZ) * NX := by
      apply mul_le_mul_of_nonneg_right _ hNX_nn
      apply mul_le_mul_of_nonneg_left hcYZ_g0 (by positivity)
    exact hstep
  have hcYZ_g1 : Real.sqrt (g₁.inner x cYZ cYZ) ≤ Real.sqrt (1 + δ) * (C₀ * G1 * NY * NZ) := by
    refine le_trans (sqrt_g1_le_sqrt_g0_of_realize (I := I) g₀ g₁ T h hbound x cYZ) ?_
    exact mul_le_mul_of_nonneg_left hcYZ_g0 hroot1δ_nn
  have hcζX_g1 : Real.sqrt (g₁.inner x cζX cζX) ≤ Real.sqrt (1 + δ) * (C₀ * G1 * Nζ * NX) := by
    refine le_trans (sqrt_g1_le_sqrt_g0_of_realize (I := I) g₀ g₁ T h hbound x cζX) ?_
    exact mul_le_mul_of_nonneg_left hcζX_g0 hroot1δ_nn
  have hcWX_g1 : Real.sqrt (g₁.inner x cWX cWX) ≤
      Real.sqrt (1 + δ) * (C₀ * G1 * (C₀ * G1 * NY * NZ) * NX) := by
    refine le_trans (sqrt_g1_le_sqrt_g0_of_realize (I := I) g₀ g₁ T h hbound x cWX) ?_
    exact mul_le_mul_of_nonneg_left hcWX_g0 hroot1δ_nn
  have hζ_g1 : Real.sqrt (g₁.inner x ζ ζ) ≤ Real.sqrt (1 + δ) * Nζ := by
    rw [hNζ_def]; exact sqrt_g1_le_sqrt_g0_of_realize (I := I) g₀ g₁ T h hbound x ζ
  have hT2 : |g₁.inner x cYZ cζX| ≤ (1 + δ) * C₀ ^ 2 * G1 ^ 2 * NX * NY * NZ * Nζ := by
    have hcs : |g₁.inner x cYZ cζX| ≤
        Real.sqrt (g₁.inner x cYZ cYZ) * Real.sqrt (g₁.inner x cζX cζX) :=
      abs_metric_inner_le_sqrt_metric_quadratic (I := I) (M := M) g₁ x cYZ cζX
    calc |g₁.inner x cYZ cζX|
        ≤ Real.sqrt (g₁.inner x cYZ cYZ) * Real.sqrt (g₁.inner x cζX cζX) := hcs
      _ ≤ (Real.sqrt (1 + δ) * (C₀ * G1 * NY * NZ)) *
            (Real.sqrt (1 + δ) * (C₀ * G1 * Nζ * NX)) := by
          refine mul_le_mul hcYZ_g1 hcζX_g1 (Real.sqrt_nonneg _)
            (mul_nonneg hroot1δ_nn (by positivity))
      _ = (1 + δ) * C₀ ^ 2 * G1 ^ 2 * NX * NY * NZ * Nζ := by
          rw [show (Real.sqrt (1 + δ) * (C₀ * G1 * NY * NZ)) *
                (Real.sqrt (1 + δ) * (C₀ * G1 * Nζ * NX)) =
              (Real.sqrt (1 + δ) * Real.sqrt (1 + δ)) *
                ((C₀ * G1 * NY * NZ) * (C₀ * G1 * Nζ * NX)) from by ring, hroot1δ_sq]
          ring
  have hT5 : |g₁.inner x cWX ζ| ≤ (1 + δ) * C₀ ^ 2 * G1 ^ 2 * NX * NY * NZ * Nζ := by
    have hcs : |g₁.inner x cWX ζ| ≤
        Real.sqrt (g₁.inner x cWX cWX) * Real.sqrt (g₁.inner x ζ ζ) :=
      abs_metric_inner_le_sqrt_metric_quadratic (I := I) (M := M) g₁ x cWX ζ
    calc |g₁.inner x cWX ζ|
        ≤ Real.sqrt (g₁.inner x cWX cWX) * Real.sqrt (g₁.inner x ζ ζ) := hcs
      _ ≤ (Real.sqrt (1 + δ) * (C₀ * G1 * (C₀ * G1 * NY * NZ) * NX)) *
            (Real.sqrt (1 + δ) * Nζ) := by
          refine mul_le_mul hcWX_g1 hζ_g1 (Real.sqrt_nonneg _)
            (mul_nonneg hroot1δ_nn (by positivity))
      _ = (1 + δ) * C₀ ^ 2 * G1 ^ 2 * NX * NY * NZ * Nζ := by
          rw [show (Real.sqrt (1 + δ) * (C₀ * G1 * (C₀ * G1 * NY * NZ) * NX)) *
                (Real.sqrt (1 + δ) * Nζ) =
              (Real.sqrt (1 + δ) * Real.sqrt (1 + δ)) *
                ((C₀ * G1 * (C₀ * G1 * NY * NZ) * NX) * Nζ) from by ring, hroot1δ_sq]
          ring
  have e1 : R41 ≤ G2 * NX * NY * NZ * Nζ := by
    refine le_trans (le_abs_self _) (le_trans hR41 (le_of_eq ?_)); ring
  have e2 : R42 ≤ G2 * NX * NY * NZ * Nζ := by
    refine le_trans (le_abs_self _) (le_trans hR42 (le_of_eq ?_)); ring
  have e3 : - R43 ≤ G2 * NX * NY * NZ * Nζ := by
    have hle := (abs_le.mp hR43).1
    nlinarith [hle]
  have hcombine : g₁.inner x D ζ ≤
      (3 / 2 : ℝ) * G2 * NX * NY * NZ * Nζ +
        2 * (1 + δ) * C₀ ^ 2 * G1 ^ 2 * NX * NY * NZ * Nζ := by
    rw [hident]
    have hrank4 : (1 / 2 : ℝ) * (R41 + R42 - R43) ≤
        (3 / 2 : ℝ) * (G2 * NX * NY * NZ * Nζ) := by
      linarith [e1, e2, e3]
    have hT2le : - g₁.inner x cYZ cζX ≤ (1 + δ) * C₀ ^ 2 * G1 ^ 2 * NX * NY * NZ * Nζ := by
      have := neg_le_of_abs_le hT2
      linarith [this]
    have hT5le : - g₁.inner x cWX ζ ≤ (1 + δ) * C₀ ^ 2 * G1 ^ 2 * NX * NY * NZ * Nζ := by
      have := neg_le_of_abs_le hT5
      linarith [this]
    nlinarith [hrank4, hT2le, hT5le]
  have hG1sq_le : G1 ^ 2 ≤ (1 + R) * Q := by
    have hG1_le_R1 : G1 ≤ 1 + R := le_trans hjet' (by linarith)
    have hmul : G1 * G1 ≤ (1 + R) * Q := mul_le_mul hG1_le_R1 hG1_le_Q hG1_nn hR1_nn
    calc G1 ^ 2 = G1 * G1 := by ring
      _ ≤ (1 + R) * Q := hmul
  have hG2_le_R1Q : G2 ≤ (1 + R) * Q := by
    refine le_trans hG2_le_Q ?_
    have hQ1 : Q = 1 * Q := (one_mul Q).symm
    calc Q = 1 * Q := hQ1
      _ ≤ (1 + R) * Q := mul_le_mul_of_nonneg_right (by linarith) hQ_nn
  have hδ_le_δ₀ : (1 : ℝ) + δ ≤ 1 + δ₀ := by linarith
  have hfinal : (3 / 2 : ℝ) * G2 * NX * NY * NZ * Nζ +
        2 * (1 + δ) * C₀ ^ 2 * G1 ^ 2 * NX * NY * NZ * Nζ ≤ Kc * Nζ := by
    rw [hKc_def]
    have hscalar := weighted_sum_le_of_sq_and_linear_bounds G1 G2 Q NX NY NZ Nζ C₀ δ δ₀ R
      hG1_nn hG2_nn hQ_nn hNX_nn hNY_nn hNZ_nn hNζ_nn hC₀0 hR1_nn
      hG1sq_le hG2_le_R1Q hδ_le_δ₀ h1δ_nn
    calc (3 / 2 : ℝ) * G2 * NX * NY * NZ * Nζ +
          2 * (1 + δ) * C₀ ^ 2 * G1 ^ 2 * NX * NY * NZ * Nζ
        ≤ ((3 / 2) + 2 * (1 + δ₀) * C₀ ^ 2) * (1 + R) * Q * NX * NY * NZ * Nζ := hscalar
      _ = ((3 / 2) + 2 * (1 + δ₀) * C₀ ^ 2) * (1 + R) * Q * NX * NY * NZ * Nζ := by ring
  exact le_trans hcombine hfinal

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
omit [NeZero (Module.finrank ℝ E)] in
private lemma sqrt_inner_covDerivConnDiff_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g₁ : SmoothRiemannianMetric I M)
      (T : SmoothCcTensor g₀ 0 2)
      (_h : ∀ y v w, g₁.inner y v w =
        g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
      {δ : ℝ} (_hδ : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
      (_hbound : metricCauchySchwarzBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
      (x : M)
      (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
      {R : ℝ} (_hR0 : 0 ≤ R)
      (_hjet :
        letI : Bundle.RiemannianBundle
            (fun y : M => Tensor0SBundle.TensorRSSpace 0 3 I y) :=
          Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
        ‖((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x :
            Tensor0SBundle.TensorRSSpace 0 3 I x)‖ ≤ R),
      letI : Bundle.RiemannianBundle
          (fun y : M => Tensor0SBundle.TensorRSSpace 0 3 I y) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
      letI : Bundle.RiemannianBundle
          (fun y : M => Tensor0SBundle.TensorRSSpace 0 4 I y) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 4
      Real.sqrt (g₀.inner x
          (covDerivConnDiff (I := I) g₀ g₁ (fun b => X b) (fun b => Z b) (fun b => Y b) x)
          (covDerivConnDiff (I := I) g₀ g₁ (fun b => X b) (fun b => Z b) (fun b => Y b) x)) ≤
        C * (1 + R) *
          Real.sqrt (‖((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x :
                Tensor0SBundle.TensorRSSpace 0 3 I x)‖ ^ 2 +
              ‖((iteratedCovGrad (I := I) g₀ 0 2 2 T).toSection x :
                Tensor0SBundle.TensorRSSpace 0 4 I x)‖ ^ 2) *
          Real.sqrt (g₀.inner x (X x) (X x)) * Real.sqrt (g₀.inner x (Y x) (Y x)) *
          Real.sqrt (g₀.inner x (Z x) (Z x)) := by
  classical
  letI inst3 : Bundle.RiemannianBundle
      (fun y : M => Tensor0SBundle.TensorRSSpace 0 3 I y) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
  letI inst4 : Bundle.RiemannianBundle
      (fun y : M => Tensor0SBundle.TensorRSSpace 0 4 I y) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 4
  obtain ⟨C₀, hC₀0, hconn⟩ :=
    connDiff_gFibreNorm_le_iteratedCovGrad_of_lt_one (I := I) (M := M) g₀ hδ₀0 hδ₀
  have hceil00 : 0 < 1 - δ₀ := by linarith
  have hCpos : 0 ≤ (1 / (1 - δ₀)) * ((3 / 2) + 2 * (1 + δ₀) * C₀ ^ 2) := by
    have h1 : 0 ≤ 1 / (1 - δ₀) := one_div_nonneg.mpr (le_of_lt hceil00)
    have h2 : 0 ≤ (3 / 2 : ℝ) + 2 * (1 + δ₀) * C₀ ^ 2 := by positivity
    exact mul_nonneg h1 h2
  refine ⟨(1 / (1 - δ₀)) * ((3 / 2) + 2 * (1 + δ₀) * C₀ ^ 2), hCpos, ?_⟩
  intro g₁ T h δ hδ hδ0 hbound x X Y Z R hR0 hjet
  have hceil0 : 0 < 1 - δ₀ := by linarith
  have hδ_lt1 : δ < 1 := by linarith
  have hcoeff : 0 < 1 - δ := by linarith
  set Q : ℝ := Real.sqrt (‖((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x :
        Tensor0SBundle.TensorRSSpace 0 3 I x)‖ ^ 2 +
      ‖((iteratedCovGrad (I := I) g₀ 0 2 2 T).toSection x :
        Tensor0SBundle.TensorRSSpace 0 4 I x)‖ ^ 2) with hQ_def
  set NX : ℝ := Real.sqrt (g₀.inner x (X x) (X x)) with hNX_def
  set NY : ℝ := Real.sqrt (g₀.inner x (Y x) (Y x)) with hNY_def
  set NZ : ℝ := Real.sqrt (g₀.inner x (Z x) (Z x)) with hNZ_def
  set D : TangentSpace I x :=
    covDerivConnDiff (I := I) g₀ g₁ (fun b => X b) (fun b => Z b) (fun b => Y b) x with hD_def
  set Kc : ℝ := ((3 / 2) + 2 * (1 + δ₀) * C₀ ^ 2) * (1 + R) * Q * NX * NY * NZ with hKc_def
  have hQ_nn : 0 ≤ Q := by rw [hQ_def]; exact Real.sqrt_nonneg _
  have hNX_nn : 0 ≤ NX := by rw [hNX_def]; exact Real.sqrt_nonneg _
  have hNY_nn : 0 ≤ NY := by rw [hNY_def]; exact Real.sqrt_nonneg _
  have hNZ_nn : 0 ≤ NZ := by rw [hNZ_def]; exact Real.sqrt_nonneg _
  have hKc_nn : 0 ≤ Kc := by
    rw [hKc_def]
    have hcoeff_nn : 0 ≤ (3 / 2 : ℝ) + 2 * (1 + δ₀) * C₀ ^ 2 := by positivity
    have hR1_nn : 0 ≤ 1 + R := by linarith
    have := mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      (mul_nonneg hcoeff_nn hR1_nn) hQ_nn) hNX_nn) hNY_nn) hNZ_nn
    exact this
  have hbd : ∀ ζ : TangentSpace I x, g₁.inner x D ζ ≤ Kc * Real.sqrt (g₀.inner x ζ ζ) := by
    intro ζ
    have hpw := g1_inner_covDerivConnDiff_le_pointwise (I := I) (M := M) g₀ hδ₀ C₀ hC₀0 hconn
      g₁ T h hδ hδ0 hbound x X Y Z hR0 hjet ζ
    rw [← hD_def, ← hQ_def, ← hNX_def, ← hNY_def, ← hNZ_def, ← hKc_def] at hpw
    exact hpw
  have hsqrt := sqrt_g0_self_of_g1_inner_le (I := I) g₀ g₁ T h hδ0 hδ_lt1 hbound x D Kc hKc_nn hbd
  refine le_trans hsqrt ?_
  have hconv : (1 / (1 - δ)) ≤ (1 / (1 - δ₀)) := by
    rw [div_le_div_iff₀ hcoeff hceil0]; linarith
  calc (1 / (1 - δ)) * Kc
      ≤ (1 / (1 - δ₀)) * Kc := mul_le_mul_of_nonneg_right hconv hKc_nn
    _ = (1 / (1 - δ₀)) * ((3 / 2) + 2 * (1 + δ₀) * C₀ ^ 2) * (1 + R) * Q * NX * NY * NZ := by
        rw [hKc_def]; ring

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
omit [NeZero (Module.finrank ℝ E)] in
private lemma sqrt_inner_covDerivRaisedKoszulVec_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ Carm : ℝ, 0 ≤ Carm ∧ ∀ (g₁ : SmoothRiemannianMetric I M)
      (T : SmoothCcTensor g₀ 0 2)
      (_h : ∀ y v w, g₁.inner y v w =
        g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
      {δ : ℝ} (_hδ : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
      (_hbound : metricCauchySchwarzBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
      (x : M)
      (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
      (_hX : g₀.inner x (X x) (X x) = 1) (_hY : g₀.inner x (Y x) (Y x) = 1)
      (_hZ : g₀.inner x (Z x) (Z x) = 1)
      {R : ℝ} (_hR0 : 0 ≤ R)
      (_hjet :
        letI : Bundle.RiemannianBundle
            (fun y : M => Tensor0SBundle.TensorRSSpace 0 3 I y) :=
          Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
        ‖((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x :
            Tensor0SBundle.TensorRSSpace 0 3 I x)‖ ≤ R),
      letI : Bundle.RiemannianBundle
          (fun y : M => Tensor0SBundle.TensorRSSpace 0 3 I y) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
      letI : Bundle.RiemannianBundle
          (fun y : M => Tensor0SBundle.TensorRSSpace 0 4 I y) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 4
      Real.sqrt (g₀.inner x
          (covDerivRaisedKoszulVec (I := I) g₀ g₁ X Y Z x)
          (covDerivRaisedKoszulVec (I := I) g₀ g₁ X Y Z x)) ≤
        Carm * (1 + R) *
          Real.sqrt (‖((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x :
                Tensor0SBundle.TensorRSSpace 0 3 I x)‖ ^ 2 +
              ‖((iteratedCovGrad (I := I) g₀ 0 2 2 T).toSection x :
                Tensor0SBundle.TensorRSSpace 0 4 I x)‖ ^ 2) := by
  classical
  letI inst3 : Bundle.RiemannianBundle
      (fun y : M => Tensor0SBundle.TensorRSSpace 0 3 I y) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
  letI inst4 : Bundle.RiemannianBundle
      (fun y : M => Tensor0SBundle.TensorRSSpace 0 4 I y) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 4
  obtain ⟨Cendo, hCendo0, hendo⟩ :=
    sqrt_inner_endoCov_sharpFlatRaiseEndo_apply_le (I := I) (M := M) g₀ hδ₀0 hδ₀
  obtain ⟨Cconn, hCconn0, hconn⟩ :=
    connDiff_gFibreNorm_le_iteratedCovGrad_of_lt_one (I := I) (M := M) g₀ hδ₀0 hδ₀
  obtain ⟨Ccdc, hCcdc0, hcdc⟩ :=
    sqrt_inner_covDerivConnDiff_le (I := I) (M := M) g₀ hδ₀0 hδ₀
  refine ⟨Cendo * Cconn + (1 + δ₀) * Ccdc, by positivity, ?_⟩
  intro g₁ T h δ hδ hδ0 hbound x X Y Z hX hY hZ R hR0 hjet
  set G1 : ℝ := ‖((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x :
      Tensor0SBundle.TensorRSSpace 0 3 I x)‖ with hG1_def
  set G2 : ℝ := ‖((iteratedCovGrad (I := I) g₀ 0 2 2 T).toSection x :
      Tensor0SBundle.TensorRSSpace 0 4 I x)‖ with hG2_def
  have hG1_nn : 0 ≤ G1 := norm_nonneg _
  have hG2_nn : 0 ≤ G2 := norm_nonneg _
  set Q : ℝ := Real.sqrt (G1 ^ 2 + G2 ^ 2) with hQ_def
  have hQ_nn : 0 ≤ Q := Real.sqrt_nonneg _
  have hG1_le_Q : G1 ≤ Q := by
    rw [hQ_def]
    have : G1 = Real.sqrt (G1 ^ 2) := by rw [Real.sqrt_sq hG1_nn]
    rw [this]
    exact Real.sqrt_le_sqrt (by nlinarith [hG2_nn])
  have hjet' : G1 ≤ R := hjet
  have hR1_nn : 0 ≤ 1 + R := by linarith
  set A : TangentSpace I x :=
    ((endoCovariantDerivative (I := I) (M := M) g₀)
        (sharpFlatRaiseEndoField (I := I) (M := M) g₀ g₁) x (X x))
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Y x) (Z x)) with hA_def
  set B : TangentSpace I x :=
    sharpFlatRaiseEndo (I := I) g₀ g₁ x
      (covDerivConnDiff (I := I) g₀ g₁ (fun b => X b) (fun b => Z b) (fun b => Y b) x)
    with hB_def
  have hsplit : covDerivRaisedKoszulVec (I := I) g₀ g₁ X Y Z x = A + B := by
    rw [hA_def, hB_def]
    exact covDerivRaisedKoszulVec_eq_endoCov_add_sharpFlat (I := I) (M := M) g₀ g₁ X Y Z x
  set NA : ℝ := Real.sqrt (g₀.inner x A A) with hNA_def
  have hNA_le : NA ≤ Cendo * Cconn * G1 ^ 2 := by
    have hAbound := hendo g₁ T h hδ hδ0 hbound x (X x)
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Y x) (Z x))
    rw [← hA_def, ← hG1_def] at hAbound
    rw [hX, Real.sqrt_one, mul_one] at hAbound
    have hcn := hconn g₁ T h hδ hδ0 hbound x (Y x) (Z x)
    rw [← hG1_def, hY, hZ, Real.sqrt_one, mul_one, mul_one] at hcn
    have hcd_nn : 0 ≤ Real.sqrt (g₀.inner x
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Y x) (Z x))
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Y x) (Z x))) := Real.sqrt_nonneg _
    rw [hNA_def]
    calc Real.sqrt (g₀.inner x A A)
        ≤ Cendo * G1 * Real.sqrt (g₀.inner x
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Y x) (Z x))
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Y x) (Z x))) := hAbound
      _ ≤ Cendo * G1 * (Cconn * G1) := by
          refine mul_le_mul_of_nonneg_left hcn (mul_nonneg hCendo0 hG1_nn)
      _ = Cendo * Cconn * G1 ^ 2 := by ring
  set NB : ℝ := Real.sqrt (g₀.inner x B B) with hNB_def
  have hNB_le : NB ≤ (1 + δ₀) * Ccdc * ((1 + R) * Q) := by
    set D : TangentSpace I x :=
      covDerivConnDiff (I := I) g₀ g₁ (fun b => X b) (fun b => Z b) (fun b => Y b) x with hD_def
    have hBeq : B = sharpFlatRaiseEndo (I := I) g₀ g₁ x D := by rw [hB_def, hD_def]
    have hneumann := sqrt_inner_sharpFlatRaiseEndo_le (I := I) g₀ g₁ T h hδ0 hbound x D
    rw [← hBeq] at hneumann
    have hDbound := hcdc g₁ T h hδ hδ0 hbound x X Y Z hR0 hjet
    rw [← hD_def, ← hG1_def, ← hG2_def, ← hQ_def, hX, hY, hZ, Real.sqrt_one,
      mul_one, mul_one, mul_one] at hDbound
    have hD_sqrt_nn : 0 ≤ Real.sqrt (g₀.inner x D D) := Real.sqrt_nonneg _
    have h1delta_nn : 0 ≤ 1 + δ := by linarith
    have hR1Q_nn : 0 ≤ (1 + R) * Q := mul_nonneg hR1_nn hQ_nn
    rw [hNB_def]
    calc Real.sqrt (g₀.inner x B B)
        ≤ (1 + δ) * Real.sqrt (g₀.inner x D D) := hneumann
      _ ≤ (1 + δ) * (Ccdc * ((1 + R) * Q)) := by
          refine mul_le_mul_of_nonneg_left ?_ h1delta_nn
          calc Real.sqrt (g₀.inner x D D)
              ≤ Ccdc * (1 + R) * Q := hDbound
            _ = Ccdc * ((1 + R) * Q) := by ring
      _ ≤ (1 + δ₀) * (Ccdc * ((1 + R) * Q)) := by
          refine mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hCcdc0 hR1Q_nn)
      _ = (1 + δ₀) * Ccdc * ((1 + R) * Q) := by ring
  have htri : Real.sqrt (g₀.inner x (A + B) (A + B)) ≤ NA + NB := by
    rw [hNA_def, hNB_def]
    exact sqrt_g0_inner_add_le_arm (I := I) (M := M) g₀ x A B
  rw [hsplit]
  refine htri.trans ?_
  have hδ₀1_nn : 0 ≤ 1 + δ₀ := by linarith
  have hG1sq_le : G1 ^ 2 ≤ (1 + R) * Q := by
    have hG1_le_R1Q : G1 ≤ (1 + R) := le_trans hjet' (by linarith)
    have : G1 * G1 ≤ (1 + R) * Q := by
      refine mul_le_mul hG1_le_R1Q ?_ hG1_nn hR1_nn
      exact hG1_le_Q
    nlinarith [this]
  calc NA + NB
      ≤ Cendo * Cconn * G1 ^ 2 + (1 + δ₀) * Ccdc * ((1 + R) * Q) := add_le_add hNA_le hNB_le
    _ ≤ Cendo * Cconn * ((1 + R) * Q) + (1 + δ₀) * Ccdc * ((1 + R) * Q) := by
        refine add_le_add ?_ (le_refl _)
        exact mul_le_mul_of_nonneg_left hG1sq_le (by positivity)
    _ = (Cendo * Cconn + (1 + δ₀) * Ccdc) * (1 + R) * Q := by ring

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
omit [NeZero (Module.finrank ℝ E)] in
theorem riemannianFiberNormSq_iteratedCovGrad_one_raisedKoszul_le_of_lt_one
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g₁ : SmoothRiemannianMetric I M)
      (T : SmoothCcTensor g₀ 0 2)
      (_h : ∀ y v w, g₁.inner y v w =
        g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
      {δ : ℝ} (_hδ : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
      (_hbound : metricCauchySchwarzBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
      (x : M) {R : ℝ} (_hR0 : 0 ≤ R)
      (_hjet :
        letI : Bundle.RiemannianBundle
            (fun y : M => Tensor0SBundle.TensorRSSpace 0 3 I y) :=
          Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
        ‖((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x :
            Tensor0SBundle.TensorRSSpace 0 3 I x)‖ ≤ R),
      letI : Bundle.RiemannianBundle
          (fun y : M => Tensor0SBundle.TensorRSSpace 0 3 I y) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
      letI : Bundle.RiemannianBundle
          (fun y : M => Tensor0SBundle.TensorRSSpace 0 4 I y) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 4
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + 1) x
          ((iteratedCovGrad (I := I) g₀ 1 2 1 (raisedKoszul (I := I) g₀ g₁)).toSection x) ≤
        C ^ 2 * (1 + R) ^ 2 *
          (‖((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x :
                Tensor0SBundle.TensorRSSpace 0 3 I x)‖ ^ 2 +
            ‖((iteratedCovGrad (I := I) g₀ 0 2 2 T).toSection x :
              Tensor0SBundle.TensorRSSpace 0 4 I x)‖ ^ 2) := by
  classical
  letI inst3 : Bundle.RiemannianBundle
      (fun y : M => Tensor0SBundle.TensorRSSpace 0 3 I y) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
  letI inst4 : Bundle.RiemannianBundle
      (fun y : M => Tensor0SBundle.TensorRSSpace 0 4 I y) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 4
  obtain ⟨Carm, hCarm0, harm⟩ :=
    sqrt_inner_covDerivRaisedKoszulVec_le (I := I) (M := M) g₀ hδ₀0 hδ₀
  refine ⟨Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 4) * Carm, by positivity, ?_⟩
  intro g₁ T h δ hδ hδ0 hbound x R hR0 hjet
  obtain ⟨n, e, bse, hn, hbse, horth, hpars, hrepr_v, hsum⟩ :=
    tangent_orthonormalBasis_witness (I := I) (M := M) g₀ x
  have hnE : n = Module.finrank ℝ E := by rw [hn]; rfl
  set G1 : ℝ := ‖((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x :
      Tensor0SBundle.TensorRSSpace 0 3 I x)‖ with hG1_def
  set G2 : ℝ := ‖((iteratedCovGrad (I := I) g₀ 0 2 2 T).toSection x :
      Tensor0SBundle.TensorRSSpace 0 4 I x)‖ with hG2_def
  have hG1_nn : 0 ≤ G1 := norm_nonneg _
  have hG2_nn : 0 ≤ G2 := norm_nonneg _
  have hjet' : G1 ≤ R := hjet
  have hQ_nn : (0 : ℝ) ≤ G1 ^ 2 + G2 ^ 2 := by positivity
  have hiter1 : iteratedCovGrad (I := I) g₀ 1 2 1 (raisedKoszul (I := I) g₀ g₁) =
      covGrad (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁) := by
    rw [iteratedCovGrad_succ, iteratedCovGrad_zero]
  rw [hiter1]
  rw [riemannianFiberNormSq_eq_sum_componentSq_of_basis (I := I) (M := M) g₀ 1 3 x
    ((covGrad (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁)).toSection x)
    e bse hnE hbse horth]
  have hR1_nn : 0 ≤ 1 + R := by linarith
  have heach : ∀ (K : Fin 1 → Fin n) (J : Fin 3 → Fin n),
      (fiberNormSqComponent (I := I) (M := M) g₀ x 1 3
        ((covGrad (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁)).toSection x) n e K J) ^ 2 ≤
        (Carm * (1 + R)) ^ 2 * (G1 ^ 2 + G2 ^ 2) := by
    intro K J
    obtain ⟨X, hXx⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
      (F := E) (V := (TangentSpace I : M → Type _)) x (e (J 0))
    obtain ⟨Y, hYx⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
      (F := E) (V := (TangentSpace I : M → Type _)) x (e (J 1))
    obtain ⟨Z, hZx⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
      (F := E) (V := (TangentSpace I : M → Type _)) x (e (J 2))
    rw [fiberNormSqComponent_covGrad_raisedKoszul (I := I) (M := M) g₀ g₁ x e K J X Y Z hXx hYx hZx]
    set u : TangentSpace I x := covDerivRaisedKoszulVec (I := I) g₀ g₁ X Y Z x with hu_def
    have hcs := metric_inner_cauchy_schwarz_sq (I := I) (M := M) g₀ x (e (K 0)) u
    have hKK : g₀.inner x (e (K 0)) (e (K 0)) = 1 := by rw [horth (K 0) (K 0)]; simp
    rw [hKK, one_mul] at hcs
    have hXX : g₀.inner x (X x) (X x) = 1 := by rw [hXx, horth (J 0) (J 0)]; simp
    have hYY : g₀.inner x (Y x) (Y x) = 1 := by rw [hYx, horth (J 1) (J 1)]; simp
    have hZZ : g₀.inner x (Z x) (Z x) = 1 := by rw [hZx, horth (J 2) (J 2)]; simp
    have hroot := harm g₁ T h hδ hδ0 hbound x X Y Z hXX hYY hZZ hR0 hjet
    rw [← hu_def, ← hG1_def, ← hG2_def] at hroot
    have huu_nn : 0 ≤ g₀.inner x u u := metric_inner_self_nonneg (I := I) (M := M) g₀ x u
    have hsqrt_eq : Real.sqrt (g₀.inner x u u) ^ 2 = g₀.inner x u u := Real.sq_sqrt huu_nn
    have hsqrt_nn : 0 ≤ Real.sqrt (g₀.inner x u u) := Real.sqrt_nonneg _
    have hrhs_nn : 0 ≤ Carm * (1 + R) * Real.sqrt (G1 ^ 2 + G2 ^ 2) :=
      mul_nonneg (mul_nonneg hCarm0 hR1_nn) (Real.sqrt_nonneg _)
    have hsqrtQ_sq : Real.sqrt (G1 ^ 2 + G2 ^ 2) ^ 2 = G1 ^ 2 + G2 ^ 2 :=
      Real.sq_sqrt hQ_nn
    have huu_le : g₀.inner x u u ≤ (Carm * (1 + R)) ^ 2 * (G1 ^ 2 + G2 ^ 2) := by
      rw [← hsqrt_eq]
      have hmul := mul_self_le_mul_self hsqrt_nn hroot
      have hexpand : (Carm * (1 + R) * Real.sqrt (G1 ^ 2 + G2 ^ 2)) *
          (Carm * (1 + R) * Real.sqrt (G1 ^ 2 + G2 ^ 2)) =
          (Carm * (1 + R)) ^ 2 * (G1 ^ 2 + G2 ^ 2) := by
        rw [show (Carm * (1 + R) * Real.sqrt (G1 ^ 2 + G2 ^ 2)) *
              (Carm * (1 + R) * Real.sqrt (G1 ^ 2 + G2 ^ 2)) =
            (Carm * (1 + R)) ^ 2 *
              (Real.sqrt (G1 ^ 2 + G2 ^ 2) * Real.sqrt (G1 ^ 2 + G2 ^ 2)) from by ring]
        rw [show Real.sqrt (G1 ^ 2 + G2 ^ 2) * Real.sqrt (G1 ^ 2 + G2 ^ 2) =
            Real.sqrt (G1 ^ 2 + G2 ^ 2) ^ 2 from by ring, hsqrtQ_sq]
      rw [hexpand] at hmul
      nlinarith [hmul, hsqrt_nn, hroot]
    calc (g₀.inner x (e (K 0)) u) ^ 2
        ≤ g₀.inner x u u := hcs
      _ ≤ (Carm * (1 + R)) ^ 2 * (G1 ^ 2 + G2 ^ 2) := huu_le
  calc ∑ K : Fin 1 → Fin n, ∑ J : Fin 3 → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g₀ x 1 3
          ((covGrad (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁)).toSection x) n e K J) ^ 2
      ≤ ∑ K : Fin 1 → Fin n, ∑ J : Fin 3 → Fin n,
          (Carm * (1 + R)) ^ 2 * (G1 ^ 2 + G2 ^ 2) :=
        Finset.sum_le_sum (fun K _ => Finset.sum_le_sum (fun J _ => heach K J))
    _ = (Fintype.card (Fin 1 → Fin n) : ℝ) * (Fintype.card (Fin 3 → Fin n) : ℝ) *
        ((Carm * (1 + R)) ^ 2 * (G1 ^ 2 + G2 ^ 2)) := by
        rw [Finset.sum_const, Finset.sum_const]
        simp only [Finset.card_univ, nsmul_eq_mul]
        ring
    _ = (Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 4) * Carm) ^ 2 * (1 + R) ^ 2 *
          (G1 ^ 2 + G2 ^ 2) := by
        have hcard : (Fintype.card (Fin 1 → Fin n) : ℝ) * (Fintype.card (Fin 3 → Fin n) : ℝ)
            = (n : ℝ) ^ 4 := by
          rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
            Fintype.card_fin]
          push_cast
          ring
        rw [hcard, ← hnE]
        have hsq : Real.sqrt ((n : ℝ) ^ 4) ^ 2 = (n : ℝ) ^ 4 :=
          Real.sq_sqrt (by positivity)
        rw [show (Real.sqrt ((n : ℝ) ^ 4) * Carm) ^ 2 * (1 + R) ^ 2 * (G1 ^ 2 + G2 ^ 2)
            = Real.sqrt ((n : ℝ) ^ 4) ^ 2 *
                ((Carm * (1 + R)) ^ 2 * (G1 ^ 2 + G2 ^ 2)) from by ring]
        rw [hsq]

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma fiberNormSqComponent_flatArmCc
    (g₀ g₁ : SmoothRiemannianMetric I M) (kind : Bool) (x : M) {n : ℕ}
    (e : Fin n → TangentSpace I x)
    (K : Fin 1 → Fin n) (J : Fin 2 → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g₀ x 1 2
        ((flatArmCc (I := I) g₀ g₁ kind).toSection x) n e K J =
      g₀.inner x
        (flatArmVec (I := I) g₀ g₁ kind x (g0FlatCLM (I := I) g₀ x (e (K 0))) (e (J 0)))
        (e (J 1)) := by
  rw [show fiberNormSqComponent (I := I) (M := M) g₀ x 1 2
        ((flatArmCc (I := I) g₀ g₁ kind).toSection x) n e K J =
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
          (flatArmCc (I := I) g₀ g₁ kind).toSection x)
        (coframeS (I := I) (M := M) g₀ x 1 e K))
        (fun k => e (J k)) from rfl]
  rw [coframeS_one_eq_g0FlatCLM (I := I) (M := M) g₀ x e K]
  rw [flatArmCc_toSection]
  rw [show (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        flatArmFib (I := I) g₀ g₁ kind x) (g0FlatCLM (I := I) g₀ x (e (K 0)))
      = flatArmPairing (I := I) g₀ g₁ kind x (g0FlatCLM (I := I) g₀ x (e (K 0))) from rfl]
  rw [show (flatArmPairing (I := I) g₀ g₁ kind x (g0FlatCLM (I := I) g₀ x (e (K 0))))
        (fun k => e (J k))
      = g₀.inner x
          (flatArmVec (I := I) g₀ g₁ kind x (g0FlatCLM (I := I) g₀ x (e (K 0))) (e (J 0)))
          (e (J 1)) from flatArmPairing_apply (I := I) g₀ g₁ kind x _ _]

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
omit [NeZero (Module.finrank ℝ E)] in
private lemma sqrt_inner_flatArmVec_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ Carm : ℝ, 0 ≤ Carm ∧ ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
      (_h : ∀ y v w, g₁.inner y v w =
        g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
      {δ : ℝ} (_hδ : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
      (_hbound : metricCauchySchwarzBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
      (kind : Bool) (x : M) (v0 w : TangentSpace I x)
      (_hw : g₀.inner x w w = 1),
      letI : Bundle.RiemannianBundle
          (fun y : M => Tensor0SBundle.TensorRSSpace 0 3 I y) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
      Real.sqrt (g₀.inner x
          (flatArmVec (I := I) g₀ g₁ kind x (g0FlatCLM (I := I) g₀ x w) v0)
          (flatArmVec (I := I) g₀ g₁ kind x (g0FlatCLM (I := I) g₀ x w) v0)) ≤
        Carm *
          ‖((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x :
              Tensor0SBundle.TensorRSSpace 0 3 I x)‖ *
          Real.sqrt (g₀.inner x v0 v0) := by
  classical
  letI instTens : Bundle.RiemannianBundle
      (fun y : M => Tensor0SBundle.TensorRSSpace 0 3 I y) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
  obtain ⟨C₀, hC₀0, hpw⟩ :=
    connDiff_gFibreNorm_le_iteratedCovGrad_of_lt_one (I := I) (M := M) g₀ hδ₀0 hδ₀
  refine ⟨(1 / (1 - δ₀)) ^ 2 * C₀, by positivity, ?_⟩
  intro g₁ T h δ hδ hδ0 hbound kind x v0 w hw
  have hg₁ : ∀ (b : M) (u₁ u₂ : TangentSpace I b),
      g₁.inner b u₁ u₂ = g₀.inner b u₁ u₂ + ccTensorBilinSymm (I := I) g₀ T b u₁ u₂ :=
    fun b u₁ u₂ => h b u₁ u₂
  have hceil0 : 0 < 1 - δ₀ := by linarith
  set G : ℝ := ‖((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x :
      Tensor0SBundle.TensorRSSpace 0 3 I x)‖ with hG_def
  have hG_nn : 0 ≤ G := norm_nonneg _
  set Nv0 : ℝ := Real.sqrt (g₀.inner x v0 v0) with hNv0_def
  have hNv0_nn : 0 ≤ Nv0 := Real.sqrt_nonneg _
  set s : TangentSpace I x :=
    inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x w) with hs_def
  have hs_sqrt : Real.sqrt (g₀.inner x s s) ≤ (1 / (1 - δ₀)) := by
    have hsfib := norm_inverseMetricSharpFib_g0Flat_le
      (I := I) g₀ g₁ (ccTensorBilinSymm (I := I) g₀ T) hg₁
      (by linarith : δ < 1) hδ0 hbound x w
    rw [hw, Real.sqrt_one, mul_one] at hsfib
    rw [← hs_def] at hsfib
    have hinv_le : 1 / (1 - δ) ≤ 1 / (1 - δ₀) := by
      have hcoeff : 0 < 1 - δ := by linarith
      rw [div_le_div_iff₀ hcoeff hceil0]; linarith
    exact le_trans hsfib hinv_le
  have hge1 : (1 : ℝ) ≤ 1 / (1 - δ₀) := by
    rw [le_div_iff₀ hceil0]; linarith
  have hbound_target : Real.sqrt (g₀.inner x
      (flatArmVec (I := I) g₀ g₁ kind x (g0FlatCLM (I := I) g₀ x w) v0)
      (flatArmVec (I := I) g₀ g₁ kind x (g0FlatCLM (I := I) g₀ x w) v0)) ≤
      C₀ * G * (1 / (1 - δ₀)) ^ 2 * Nv0 := by
    cases kind with
    | true =>
        have hval : flatArmVec (I := I) g₀ g₁ true x (g0FlatCLM (I := I) g₀ x w) v0 =
            - PDE.DeTurck.connDiff (I := I) g₁ g₀ x s v0 := by
          rw [flatArmVec, if_pos rfl, hs_def]
        rw [hval]
        rw [show g₀.inner x (- PDE.DeTurck.connDiff (I := I) g₁ g₀ x s v0)
              (- PDE.DeTurck.connDiff (I := I) g₁ g₀ x s v0) =
            g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x s v0)
              (PDE.DeTurck.connDiff (I := I) g₁ g₀ x s v0) from by
          simp only [map_neg, ContinuousLinearMap.neg_apply, neg_neg]]
        have hconn := hpw g₁ T h hδ hδ0 hbound x s v0
        rw [← hG_def, ← hNv0_def] at hconn
        refine hconn.trans ?_
        have hss_sqrt_le : Real.sqrt (g₀.inner x s s) ≤ (1 / (1 - δ₀)) ^ 2 := by
          have hsq_ge : 1 / (1 - δ₀) ≤ (1 / (1 - δ₀)) ^ 2 := by nlinarith [hge1]
          exact le_trans hs_sqrt hsq_ge
        have hC₀G_nn : 0 ≤ C₀ * G := mul_nonneg hC₀0 hG_nn
        calc C₀ * G * Real.sqrt (g₀.inner x s s) * Nv0
            ≤ C₀ * G * ((1 / (1 - δ₀)) ^ 2) * Nv0 := by
              refine mul_le_mul_of_nonneg_right ?_ hNv0_nn
              exact mul_le_mul_of_nonneg_left hss_sqrt_le hC₀G_nn
    | false =>
        set Dfun : TangentSpace I x →L[ℝ] ℝ :=
          (-(cotangentToCLM (I := I) (g0FlatCLM (I := I) g₀ x w)).comp
              ((PDE.DeTurck.connDiff (I := I) g₁ g₀ x).flip v0)) with hDfun_def
        have hval : flatArmVec (I := I) g₀ g₁ false x (g0FlatCLM (I := I) g₀ x w) v0 =
            inverseMetricSharpFib (I := I) g₁ x (dualToCotangent (I := I) Dfun.toLinearMap) := by
          rw [flatArmVec, if_neg (by decide : ¬ (false = true)), hDfun_def]
        rw [hval]
        set p : TangentSpace I x :=
          inverseMetricSharpFib (I := I) g₀ x (dualToCotangent (I := I) Dfun.toLinearMap)
          with hp_def
        set q : TangentSpace I x :=
          inverseMetricSharpFib (I := I) g₁ x (dualToCotangent (I := I) Dfun.toLinearMap)
          with hq_def
        have hqeq : q = inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x p) := by
          rw [hq_def]
          congr 1
          exact (g0FlatCLM_inverseMetricSharpFib (I := I) g₀ x
            (dualToCotangent (I := I) Dfun.toLinearMap)).symm
        set Np : ℝ := Real.sqrt (g₀.inner x p p) with hNpdef
        have hNp_nn : 0 ≤ Np := Real.sqrt_nonneg _
        have hpp_nn : 0 ≤ g₀.inner x p p := metric_inner_self_nonneg (I := I) (M := M) g₀ x p
        have hNp_sq : Np ^ 2 = g₀.inner x p p := Real.sq_sqrt hpp_nn
        have hDval : ∀ z : TangentSpace I x, Dfun z =
            - g₀.inner x w (PDE.DeTurck.connDiff (I := I) g₁ g₀ x z v0) := by
          intro z
          rw [hDfun_def, ContinuousLinearMap.neg_apply, ContinuousLinearMap.comp_apply,
            ContinuousLinearMap.flip_apply]
          change - cotangentToDual (I := I) (g0FlatCLM (I := I) g₀ x w)
              (PDE.DeTurck.connDiff (I := I) g₁ g₀ x z v0) = _
          rw [cotangentToDual_g0FlatCLM]
        have hpz : ∀ z : TangentSpace I x, g₀.inner x p z = Dfun z := by
          intro z
          rw [hp_def, inverseMetricSharpFib_inner (I := I) g₀ x
            (dualToCotangent (I := I) Dfun.toLinearMap) z]
          rw [cotangentToDualLinear_apply, cotangentToDual_dualToCotangent]
          rfl
        have hpp_val : g₀.inner x p p =
            - g₀.inner x w (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p v0) := by
          rw [hpz p, hDval p]
        have hconn_p := hpw g₁ T h hδ hδ0 hbound x p v0
        rw [← hG_def, ← hNpdef, ← hNv0_def] at hconn_p
        have hcs := abs_metric_inner_le_sqrt_metric_quadratic (I := I) (M := M) g₀ x w
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p v0)
        rw [hw, Real.sqrt_one, one_mul] at hcs
        have hKnn : 0 ≤ C₀ * G * Nv0 :=
          mul_nonneg (mul_nonneg hC₀0 hG_nn) hNv0_nn
        have hNp_le : Np ≤ C₀ * G * (1 / (1 - δ₀)) * Nv0 := by
          have hpp_le : g₀.inner x p p ≤
              Real.sqrt (g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p v0)
                (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p v0)) := by
            rw [hpp_val]
            calc - g₀.inner x w (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p v0)
                ≤ |g₀.inner x w (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p v0)| := neg_le_abs _
              _ ≤ Real.sqrt (g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p v0)
                  (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p v0)) := hcs
          have hconnG : Real.sqrt (g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p v0)
                (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p v0)) ≤ C₀ * G * Np * Nv0 := hconn_p
          have hpp_le2 : g₀.inner x p p ≤ (C₀ * G * Nv0) * Np := by
            refine hpp_le.trans (hconnG.trans ?_)
            nlinarith [hNp_nn, hKnn]
          have hNp_le0 : Np ≤ C₀ * G * Nv0 := by
            nlinarith [hNp_sq, hNp_nn, hpp_le2, hKnn]
          have hstep : C₀ * G * Nv0 ≤ C₀ * G * (1 / (1 - δ₀)) * Nv0 := by
            nlinarith [mul_le_mul_of_nonneg_left hge1 (mul_nonneg hC₀0 hG_nn), hNv0_nn, hKnn]
          exact hNp_le0.trans hstep
        have hsharp := norm_inverseMetricSharpFib_g0Flat_le (I := I) g₀ g₁
          (ccTensorBilinSymm (I := I) g₀ T) hg₁
          (by linarith : δ < 1) hδ0 hbound x p
        rw [← hNpdef] at hsharp
        rw [hqeq]
        refine hsharp.trans ?_
        have hinv_le : 1 / (1 - δ) ≤ 1 / (1 - δ₀) := by
          have hcoeff : 0 < 1 - δ := by linarith
          rw [div_le_div_iff₀ hcoeff hceil0]; linarith
        have hstep : (1 / (1 - δ)) * Np ≤ (1 / (1 - δ₀)) * Np :=
          mul_le_mul_of_nonneg_right hinv_le hNp_nn
        refine hstep.trans ?_
        have hinv₀_nn : 0 ≤ 1 / (1 - δ₀) := by positivity
        calc (1 / (1 - δ₀)) * Np
            ≤ (1 / (1 - δ₀)) * (C₀ * G * (1 / (1 - δ₀)) * Nv0) :=
              mul_le_mul_of_nonneg_left hNp_le hinv₀_nn
          _ = C₀ * G * (1 / (1 - δ₀)) ^ 2 * Nv0 := by ring
  refine hbound_target.trans ?_
  rw [hG_def, hNv0_def]
  apply le_of_eq; ring

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
omit [NeZero (Module.finrank ℝ E)] in
theorem riemannianFiberNormSq_flatArmCc_le_of_lt_one
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) (kind : Bool) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g₁ : SmoothRiemannianMetric I M)
      (T : SmoothCcTensor g₀ 0 2)
      (_h : ∀ y v w, g₁.inner y v w =
        g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
      {δ : ℝ} (_hδ : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
      (_hbound : metricCauchySchwarzBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
      (x : M),
      letI : Bundle.RiemannianBundle
          (fun y : M => Tensor0SBundle.TensorRSSpace 0 3 I y) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x
          ((flatArmCc (I := I) g₀ g₁ kind).toSection x) ≤
        C ^ 2 * ‖((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x :
            Tensor0SBundle.TensorRSSpace 0 3 I x)‖ ^ 2 := by
  classical
  letI instTens : Bundle.RiemannianBundle
      (fun y : M => Tensor0SBundle.TensorRSSpace 0 3 I y) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
  obtain ⟨Carm, hCarm0, harm⟩ :=
    sqrt_inner_flatArmVec_le (I := I) (M := M) g₀ hδ₀0 hδ₀
  refine ⟨Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 3) * Carm, by positivity, ?_⟩
  intro g₁ T h δ hδ hδ0 hbound x
  obtain ⟨n, e, bse, hn, hbse, horth, hpars, hrepr_v, hsum⟩ :=
    tangent_orthonormalBasis_witness (I := I) (M := M) g₀ x
  have hnE : n = Module.finrank ℝ E := by rw [hn]; rfl
  set G : ℝ := ‖((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x :
      Tensor0SBundle.TensorRSSpace 0 3 I x)‖ with hG_def
  have hG_nn : 0 ≤ G := norm_nonneg _
  rw [riemannianFiberNormSq_eq_sum_componentSq_of_basis (I := I) (M := M) g₀ 1 2 x
    ((flatArmCc (I := I) g₀ g₁ kind).toSection x) e bse hnE hbse horth]
  have heach : ∀ (K : Fin 1 → Fin n) (J : Fin 2 → Fin n),
      (fiberNormSqComponent (I := I) (M := M) g₀ x 1 2
        ((flatArmCc (I := I) g₀ g₁ kind).toSection x) n e K J) ^ 2 ≤
        Carm ^ 2 * G ^ 2 := by
    intro K J
    rw [fiberNormSqComponent_flatArmCc (I := I) g₀ g₁ kind x e K J]
    set u : TangentSpace I x :=
      flatArmVec (I := I) g₀ g₁ kind x (g0FlatCLM (I := I) g₀ x (e (K 0))) (e (J 0))
      with hu_def
    have hcs := metric_inner_cauchy_schwarz_sq (I := I) (M := M) g₀ x u (e (J 1))
    have hJ1 : g₀.inner x (e (J 1)) (e (J 1)) = 1 := by rw [horth (J 1) (J 1)]; simp
    rw [hJ1, mul_one] at hcs
    have hKK : g₀.inner x (e (K 0)) (e (K 0)) = 1 := by rw [horth (K 0) (K 0)]; simp
    have hJ0 : g₀.inner x (e (J 0)) (e (J 0)) = 1 := by rw [horth (J 0) (J 0)]; simp
    have hroot := harm g₁ T h hδ hδ0 hbound kind x (e (J 0)) (e (K 0)) hKK
    rw [← hu_def, hJ0, Real.sqrt_one, mul_one, ← hG_def] at hroot
    have huu_nn : 0 ≤ g₀.inner x u u := metric_inner_self_nonneg (I := I) (M := M) g₀ x u
    have hsqrt_eq : Real.sqrt (g₀.inner x u u) ^ 2 = g₀.inner x u u := Real.sq_sqrt huu_nn
    have hsqrt_nn : 0 ≤ Real.sqrt (g₀.inner x u u) := Real.sqrt_nonneg _
    have hrhs_nn : 0 ≤ Carm * G := mul_nonneg hCarm0 hG_nn
    have huu_le : g₀.inner x u u ≤ (Carm * G) ^ 2 := by
      rw [← hsqrt_eq]
      have := mul_self_le_mul_self hsqrt_nn hroot
      nlinarith [this, hroot, hrhs_nn]
    calc (g₀.inner x u (e (J 1))) ^ 2
        ≤ g₀.inner x u u := hcs
      _ ≤ (Carm * G) ^ 2 := huu_le
      _ = Carm ^ 2 * G ^ 2 := by ring
  calc ∑ K : Fin 1 → Fin n, ∑ J : Fin 2 → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g₀ x 1 2
          ((flatArmCc (I := I) g₀ g₁ kind).toSection x) n e K J) ^ 2
      ≤ ∑ K : Fin 1 → Fin n, ∑ J : Fin 2 → Fin n, Carm ^ 2 * G ^ 2 :=
        Finset.sum_le_sum (fun K _ => Finset.sum_le_sum (fun J _ => heach K J))
    _ = (Fintype.card (Fin 1 → Fin n) : ℝ) * (Fintype.card (Fin 2 → Fin n) : ℝ) *
        (Carm ^ 2 * G ^ 2) := by
        rw [Finset.sum_const, Finset.sum_const]
        simp only [Finset.card_univ, nsmul_eq_mul]
        ring
    _ = (Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 3) * Carm) ^ 2 * G ^ 2 := by
        have hcard : (Fintype.card (Fin 1 → Fin n) : ℝ) * (Fintype.card (Fin 2 → Fin n) : ℝ)
            = (n : ℝ) ^ 3 := by
          rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
            Fintype.card_fin]
          push_cast
          ring
        rw [hcard, ← hnE]
        have hsq : Real.sqrt ((n : ℝ) ^ 3) ^ 2 = (n : ℝ) ^ 3 :=
          Real.sq_sqrt (by positivity)
        rw [show (Real.sqrt ((n : ℝ) ^ 3) * Carm) ^ 2 * G ^ 2
            = Real.sqrt ((n : ℝ) ^ 3) ^ 2 * (Carm ^ 2 * G ^ 2) from by ring]
        rw [hsq]

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
omit [NeZero (Module.finrank ℝ E)] in
theorem riemannianFiberNormSq_iteratedCovGrad_one_sharpFlatEndoCc_le_of_lt_one
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g₁ : SmoothRiemannianMetric I M)
      (T : SmoothCcTensor g₀ 0 2)
      (_h : ∀ y v w, g₁.inner y v w =
        g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
      {δ : ℝ} (_hδ : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
      (_hbound : metricCauchySchwarzBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
      (x : M),
      letI : Bundle.RiemannianBundle
          (fun y : M => Tensor0SBundle.TensorRSSpace 0 3 I y) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + 1) x
          ((iteratedCovGrad (I := I) g₀ 1 1 1 (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x) ≤
        C ^ 2 * ‖((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x :
            Tensor0SBundle.TensorRSSpace 0 3 I x)‖ ^ 2 := by
  classical
  letI instTens : Bundle.RiemannianBundle
      (fun y : M => Tensor0SBundle.TensorRSSpace 0 3 I y) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
  obtain ⟨Ctrue, hCtrue0, harmTrue⟩ :=
    riemannianFiberNormSq_flatArmCc_le_of_lt_one (I := I) (M := M) g₀ hδ₀0 hδ₀ true
  obtain ⟨Cfalse, hCfalse0, harmFalse⟩ :=
    riemannianFiberNormSq_flatArmCc_le_of_lt_one (I := I) (M := M) g₀ hδ₀0 hδ₀ false
  refine ⟨Real.sqrt (2 * Ctrue ^ 2 + 2 * Cfalse ^ 2), by positivity, ?_⟩
  intro g₁ T h δ hδ hδ0 hbound x
  set G : ℝ := ‖((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x :
      Tensor0SBundle.TensorRSSpace 0 3 I x)‖ with hG_def
  have hG_nn : 0 ≤ G := norm_nonneg _
  have harms := riemannianFiberNormSq_iteratedCovGrad_sharpFlatEndoCc_succ_le_arms (I := I) (M := M) g₀ g₁ 0 x
  rw [iteratedCovGrad_zero, iteratedCovGrad_zero] at harms
  have hbtrue := harmTrue g₁ T h hδ hδ0 hbound x
  have hbfalse := harmFalse g₁ T h hδ hδ0 hbound x
  rw [← hG_def] at hbtrue hbfalse
  refine harms.trans ?_
  have hcombine : 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 ((1 + 1) + 0) x
        ((flatArmCc (I := I) g₀ g₁ true).toSection x) +
      2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 ((1 + 1) + 0) x
        ((flatArmCc (I := I) g₀ g₁ false).toSection x) ≤
      2 * (Ctrue ^ 2 * G ^ 2) + 2 * (Cfalse ^ 2 * G ^ 2) := by
    have hbtrue' : riemannianFiberNormSq (I := I) (M := M) g₀ 1 ((1 + 1) + 0) x
        ((flatArmCc (I := I) g₀ g₁ true).toSection x) ≤ Ctrue ^ 2 * G ^ 2 := hbtrue
    have hbfalse' : riemannianFiberNormSq (I := I) (M := M) g₀ 1 ((1 + 1) + 0) x
        ((flatArmCc (I := I) g₀ g₁ false).toSection x) ≤ Cfalse ^ 2 * G ^ 2 := hbfalse
    linarith [hbtrue', hbfalse']
  refine hcombine.trans ?_
  have hCsq : Real.sqrt (2 * Ctrue ^ 2 + 2 * Cfalse ^ 2) ^ 2 = 2 * Ctrue ^ 2 + 2 * Cfalse ^ 2 :=
    Real.sq_sqrt (by positivity)
  rw [hCsq]
  ring_nf
  rfl

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
