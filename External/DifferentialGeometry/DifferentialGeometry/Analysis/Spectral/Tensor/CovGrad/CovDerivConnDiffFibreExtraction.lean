import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceFibreBound
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CometricInverseDifferenceMultiplier

noncomputable section

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Geometry
namespace Curvature

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.Analysis.Laplacian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma coframe_arity_one_eq_metric_flat_apply
    (g₀ : SmoothRiemannianMetric I M) (x : M)
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

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem abs_tensor_one_three_flat_eval_le_fibreNorm_mul_sqrt
    (g₀ : SmoothRiemannianMetric I M) (x : M)
    (W : TensorRSSpace 1 3 I x) (d a b c : TangentSpace I x) :
    letI : Bundle.RiemannianBundle
        (fun y : M => Tensor0SBundle.TensorRSSpace 1 3 I y) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 1 3
    |Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from W)
          (g0FlatCLM (I := I) g₀ x d))
        (Fin.cons a (Fin.cons b ![c]))| ≤
      ‖(W : Tensor0SBundle.TensorRSSpace 1 3 I x)‖ *
        Real.sqrt (g₀.inner x d d) *
        Real.sqrt (g₀.inner x a a) * Real.sqrt (g₀.inner x b b) *
          Real.sqrt (g₀.inner x c c) := by
  classical
  letI instTens : Bundle.RiemannianBundle
      (fun y : M => Tensor0SBundle.TensorRSSpace 1 3 I y) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 1 3
  obtain ⟨n, e, bse, hn, hbse, horth, hpars, hrepr, _hsum⟩ :=
    tangent_orthonormalBasis_witness (I := I) (M := M) g₀ x
  have hnE : n = Module.finrank ℝ E := by rw [hn]; rfl
  set vec : Fin 3 → TangentSpace I x := ![a, b, c] with hvec_def
  set coef : (Fin 1 → Fin n) × (Fin 3 → Fin n) → ℝ :=
    fun p => g₀.inner x (e (p.1 0)) d * ∏ i : Fin 3, g₀.inner x (e (p.2 i)) (vec i) with hcoef_def
  set comp : (Fin 1 → Fin n) × (Fin 3 → Fin n) → ℝ :=
    fun p => fiberNormSqComponent (I := I) (M := M) g₀ x 1 3 W n e p.1 p.2 with hcomp_def
  have hcompval : ∀ (K : Fin 1 → Fin n) (J : Fin 3 → Fin n),
      fiberNormSqComponent (I := I) (M := M) g₀ x 1 3 W n e K J =
        Tensor0SSpace.toModel
          ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from W)
            (g0FlatCLM (I := I) g₀ x (e (K 0))))
          (fun i : Fin 3 => e (J i)) := by
    intro K J
    rw [show fiberNormSqComponent (I := I) (M := M) g₀ x 1 3 W n e K J =
        Tensor0SSpace.toModel
          ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from W)
            (coframeS (I := I) (M := M) g₀ x 1 e K))
          (fun i : Fin 3 => e (J i)) from rfl]
    rw [coframe_arity_one_eq_metric_flat_apply (I := I) (M := M) g₀ x e K]
  have hWd : (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from W)
        (g0FlatCLM (I := I) g₀ x d) =
      ∑ k : Fin n, g₀.inner x (e k) d •
        (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from W)
          (g0FlatCLM (I := I) g₀ x (e k)) := by
    have hflat : g0FlatCLM (I := I) g₀ x d =
        ∑ k : Fin n, g₀.inner x (e k) d • g0FlatCLM (I := I) g₀ x (e k) := by
      conv_lhs => rw [hrepr d]
      rw [map_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [map_smul]
    rw [hflat, map_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [map_smul]
  have hexp : ∀ i : Fin 3, vec i = ∑ j : Fin n, g₀.inner x (e j) (vec i) • e j :=
    fun i => hrepr (vec i)
  have hvalue : Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from W)
          (g0FlatCLM (I := I) g₀ x d))
        (Fin.cons a (Fin.cons b ![c])) =
      ∑ p : (Fin 1 → Fin n) × (Fin 3 → Fin n), coef p * comp p := by
    change Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from W)
          (g0FlatCLM (I := I) g₀ x d)) vec =
        ∑ p : (Fin 1 → Fin n) × (Fin 3 → Fin n), coef p * comp p
    rw [hWd]
    rw [show Tensor0SSpace.toModel
          (∑ k : Fin n, g₀.inner x (e k) d •
            (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from W)
              (g0FlatCLM (I := I) g₀ x (e k))) =
        ∑ k : Fin n, g₀.inner x (e k) d •
          Tensor0SSpace.toModel
            ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from W)
              (g0FlatCLM (I := I) g₀ x (e k))) from by
      rw [← Tensor0SSpace.toModelL_apply, map_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [map_smul, Tensor0SSpace.toModelL_apply]]
    rw [ContinuousMultilinearMap.sum_apply]
    have hterm : ∀ k : Fin n,
        (g₀.inner x (e k) d •
          Tensor0SSpace.toModel
            ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from W)
              (g0FlatCLM (I := I) g₀ x (e k)))) vec =
        ∑ J : Fin 3 → Fin n,
          (g₀.inner x (e k) d * ∏ i : Fin 3, g₀.inner x (e (J i)) (vec i)) *
            fiberNormSqComponent (I := I) (M := M) g₀ x 1 3 W n e (fun _ => k) J := by
      intro k
      rw [ContinuousMultilinearMap.smul_apply]
      set B3 : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ :=
        Tensor0SSpace.toModel
          ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from W)
            (g0FlatCLM (I := I) g₀ x (e k))) with hB3_def
      set coefJ : (Fin 3 → Fin n) → ℝ :=
        fun J => ∏ i : Fin 3, g₀.inner x (e (J i)) (vec i) with hcoefJ_def
      set compJ : (Fin 3 → Fin n) → ℝ :=
        fun J => B3 (fun i : Fin 3 => (show E from e (J i))) with hcompJ_def
      have hexp' : ∀ i : Fin 3, (show E from vec i) =
          ∑ j : Fin n, g₀.inner x (e j) (vec i) • (show E from e j) :=
        fun i => hexp i
      have hB3val : B3 vec = ∑ J : Fin 3 → Fin n, coefJ J * compJ J := by
        have hrw : B3 vec = B3 (fun i : Fin 3 =>
            ∑ j : Fin n, g₀.inner x (e j) (vec i) • (show E from e j)) := by
          congr 1
          funext i
          exact hexp' i
        rw [hrw, ContinuousMultilinearMap.map_sum]
        refine Finset.sum_congr rfl (fun J _ => ?_)
        rw [hcoefJ_def, hcompJ_def]
        rw [ContinuousMultilinearMap.map_smul_univ, smul_eq_mul]
      rw [hB3val, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun J _ => ?_)
      rw [hcompJ_def, hcompval (fun _ => k) J, ← hB3_def, hcoefJ_def]
      ring
    rw [Finset.sum_congr rfl (fun k _ => hterm k)]
    rw [show (∑ k : Fin n, ∑ J : Fin 3 → Fin n,
          (g₀.inner x (e k) d * ∏ i : Fin 3, g₀.inner x (e (J i)) (vec i)) *
            fiberNormSqComponent (I := I) (M := M) g₀ x 1 3 W n e (fun _ => k) J) =
        ∑ K : Fin 1 → Fin n, ∑ J : Fin 3 → Fin n,
          (g₀.inner x (e (K 0)) d * ∏ i : Fin 3, g₀.inner x (e (J i)) (vec i)) *
            fiberNormSqComponent (I := I) (M := M) g₀ x 1 3 W n e K J from by
      refine (Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin n)).symm _ _ (fun k => ?_))
      refine Finset.sum_congr rfl (fun J _ => ?_)
      have hKeq : (Equiv.funUnique (Fin 1) (Fin n)).symm k = (fun _ : Fin 1 => k) := rfl
      rw [hKeq]]
    rw [← Fintype.sum_prod_type']
  rw [hvalue]
  have hCS : (∑ p : (Fin 1 → Fin n) × (Fin 3 → Fin n), coef p * comp p) ^ 2 ≤
      (∑ p : (Fin 1 → Fin n) × (Fin 3 → Fin n), coef p ^ 2) *
        ∑ p : (Fin 1 → Fin n) × (Fin 3 → Fin n), comp p ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ coef comp
  have hdd_nn : 0 ≤ g₀.inner x d d := metric_inner_self_nonneg (I := I) (M := M) g₀ x d
  have haa_nn : 0 ≤ g₀.inner x a a := metric_inner_self_nonneg (I := I) (M := M) g₀ x a
  have hbb_nn : 0 ≤ g₀.inner x b b := metric_inner_self_nonneg (I := I) (M := M) g₀ x b
  have hcc_nn : 0 ≤ g₀.inner x c c := metric_inner_self_nonneg (I := I) (M := M) g₀ x c
  have hcoefsq : (∑ p : (Fin 1 → Fin n) × (Fin 3 → Fin n), coef p ^ 2) =
      g₀.inner x d d * (g₀.inner x a a * g₀.inner x b b * g₀.inner x c c) := by
    have hpow : ∀ p : (Fin 1 → Fin n) × (Fin 3 → Fin n), coef p ^ 2 =
        g₀.inner x (e (p.1 0)) d ^ 2 *
          ∏ i : Fin 3, g₀.inner x (e (p.2 i)) (vec i) ^ 2 := by
      intro p
      rw [hcoef_def, mul_pow, ← Finset.prod_pow]
    rw [Finset.sum_congr rfl (fun p _ => hpow p)]
    rw [Fintype.sum_prod_type]
    rw [show (∑ K : Fin 1 → Fin n, ∑ J : Fin 3 → Fin n,
          g₀.inner x (e (K 0)) d ^ 2 * ∏ i : Fin 3, g₀.inner x (e (J i)) (vec i) ^ 2) =
        (∑ K : Fin 1 → Fin n, g₀.inner x (e (K 0)) d ^ 2) *
          ∑ J : Fin 3 → Fin n, ∏ i : Fin 3, g₀.inner x (e (J i)) (vec i) ^ 2 from by
      rw [Finset.sum_mul_sum]]
    have hKsum : (∑ K : Fin 1 → Fin n, g₀.inner x (e (K 0)) d ^ 2) = g₀.inner x d d := by
      rw [← hpars d]
      rw [show (∑ K : Fin 1 → Fin n, g₀.inner x (e (K 0)) d ^ 2) =
          ∑ k : Fin n, g₀.inner x (e k) d ^ 2 from by
        rw [← Equiv.sum_comp (Equiv.funUnique (Fin 1) (Fin n))
          (fun k : Fin n => g₀.inner x (e k) d ^ 2)]
        rfl]
    have hJsum : (∑ J : Fin 3 → Fin n, ∏ i : Fin 3, g₀.inner x (e (J i)) (vec i) ^ 2) =
        g₀.inner x a a * g₀.inner x b b * g₀.inner x c c := by
      rw [show (∑ J : Fin 3 → Fin n, ∏ i : Fin 3, g₀.inner x (e (J i)) (vec i) ^ 2) =
          ∑ J ∈ Fintype.piFinset (fun _ : Fin 3 => (Finset.univ : Finset (Fin n))),
            ∏ i : Fin 3, g₀.inner x (e (J i)) (vec i) ^ 2 from by
        rw [Fintype.piFinset_univ]]
      rw [← Finset.prod_univ_sum (fun _ : Fin 3 => (Finset.univ : Finset (Fin n)))
        (fun i j => g₀.inner x (e j) (vec i) ^ 2)]
      rw [Fin.prod_univ_three]
      rw [hpars (vec 0), hpars (vec 1), hpars (vec 2)]
      have h0 : vec 0 = a := rfl
      have h1 : vec 1 = b := rfl
      have h2 : vec 2 = c := rfl
      rw [h0, h1, h2]
    rw [hKsum, hJsum]
  have hcompsq : (∑ p : (Fin 1 → Fin n) × (Fin 3 → Fin n), comp p ^ 2) =
      ‖(W : Tensor0SBundle.TensorRSSpace 1 3 I x)‖ ^ 2 := by
    rw [← riemannianFiberNormSq_eq_bundle_norm_sq' (I := I) (M := M) g₀ 1 3 x W]
    rw [riemannianFiberNormSq_eq_sum_componentSq_of_basis (I := I) (M := M) g₀ 1 3 x W e bse hnE hbse horth]
    rw [Fintype.sum_prod_type]
  have hnorm_nn : 0 ≤ ‖(W : Tensor0SBundle.TensorRSSpace 1 3 I x)‖ := norm_nonneg _
  have habs_sq : (∑ p : (Fin 1 → Fin n) × (Fin 3 → Fin n), coef p * comp p) ^ 2 ≤
      ‖(W : Tensor0SBundle.TensorRSSpace 1 3 I x)‖ ^ 2 *
        (g₀.inner x d d * (g₀.inner x a a * g₀.inner x b b * g₀.inner x c c)) := by
    calc (∑ p : (Fin 1 → Fin n) × (Fin 3 → Fin n), coef p * comp p) ^ 2
        ≤ (∑ p : (Fin 1 → Fin n) × (Fin 3 → Fin n), coef p ^ 2) *
            ∑ p : (Fin 1 → Fin n) × (Fin 3 → Fin n), comp p ^ 2 := hCS
      _ = (g₀.inner x d d * (g₀.inner x a a * g₀.inner x b b * g₀.inner x c c)) *
            ‖(W : Tensor0SBundle.TensorRSSpace 1 3 I x)‖ ^ 2 := by
            rw [hcoefsq, hcompsq]
      _ = ‖(W : Tensor0SBundle.TensorRSSpace 1 3 I x)‖ ^ 2 *
            (g₀.inner x d d * (g₀.inner x a a * g₀.inner x b b * g₀.inner x c c)) := by ring
  rw [← Real.sqrt_sq (abs_nonneg (∑ p : (Fin 1 → Fin n) × (Fin 3 → Fin n), coef p * comp p)),
    sq_abs]
  rw [show ‖(W : Tensor0SBundle.TensorRSSpace 1 3 I x)‖ *
        Real.sqrt (g₀.inner x d d) *
        Real.sqrt (g₀.inner x a a) * Real.sqrt (g₀.inner x b b) *
          Real.sqrt (g₀.inner x c c) =
      Real.sqrt (‖(W : Tensor0SBundle.TensorRSSpace 1 3 I x)‖ ^ 2 *
        (g₀.inner x d d * (g₀.inner x a a * g₀.inner x b b * g₀.inner x c c))) from ?_]
  · exact Real.sqrt_le_sqrt habs_sq
  · rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hnorm_nn]
    rw [Real.sqrt_mul hdd_nn, Real.sqrt_mul (mul_nonneg haa_nn hbb_nn), Real.sqrt_mul haa_nn]
    ring

end Curvature
end Geometry
end DifferentialGeometry

end
