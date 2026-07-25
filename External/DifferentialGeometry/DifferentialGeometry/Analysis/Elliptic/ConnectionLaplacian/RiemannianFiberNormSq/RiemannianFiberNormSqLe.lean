import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.Defs
import DifferentialGeometry.Geometry.Metric.MetricBounds
import DifferentialGeometry.Tensor.RSTensor.TensorRSSpaceOperatorNorm
import Mathlib.Analysis.Normed.Module.Multilinear.Basic


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

open Bundle Set IsManifold ContinuousLinearMap Function
open scoped Manifold Topology Bundle ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Laplacian
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [InnerProductSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

noncomputable def orthoBasisSumNormSq
    (g : SmoothRiemannianMetric I M) (b : M) : ℝ := by
  classical
  let cd : InnerProductSpace.Core ℝ (TangentSpace I b) := g.toRiemannianMetric.toCore b
  have hc : ContinuousAt (fun v : TangentSpace I b => cd.inner v v) 0 :=
    g.toRiemannianMetric.continuousAt b
  have hb : Bornology.IsVonNBounded ℝ {v : TangentSpace I b |
      RCLike.re (cd.inner v v) < 1} :=
    g.toRiemannianMetric.isVonNBounded b
  letI : NormedAddCommGroup (TangentSpace I b) :=
    cd.toNormedAddCommGroupOfTopology hc hb
  letI : InnerProductSpace ℝ (TangentSpace I b) :=
    InnerProductSpace.ofCoreOfTopology cd hc hb
  let n : ℕ := Module.finrank ℝ (TangentSpace I b)
  let e : OrthonormalBasis (Fin n) ℝ (TangentSpace I b) := stdOrthonormalBasis ℝ _
  exact ∑ i : Fin n, ‖e i‖ ^ 2

omit [InnerProductSpace ℝ E] in
lemma orthoBasisSumNormSq_nonneg
    (g : SmoothRiemannianMetric I M) (b : M) :
    0 ≤ orthoBasisSumNormSq (I := I) (M := M) g b := by
  unfold orthoBasisSumNormSq
  exact Finset.sum_nonneg (fun i _ => sq_nonneg _)

noncomputable def pointwiseBoundScalar
    (g : SmoothRiemannianMetric I M) (b : M) : ℝ :=
  1 + metricInnerOpNorm (I := I) (M := M) g b +
    orthoBasisSumNormSq (I := I) (M := M) g b

omit [InnerProductSpace ℝ E] in
lemma pointwiseBoundScalar_nonneg
    (g : SmoothRiemannianMetric I M) (b : M) :
    0 ≤ pointwiseBoundScalar (I := I) (M := M) g b := by
  unfold pointwiseBoundScalar
  have h2 : 0 ≤ metricInnerOpNorm (I := I) (M := M) g b := norm_nonneg _
  have h3 := orthoBasisSumNormSq_nonneg (I := I) (M := M) g b
  linarith

omit [InnerProductSpace ℝ E] in
lemma pointwiseBoundScalar_one_le
    (g : SmoothRiemannianMetric I M) (b : M) :
    1 ≤ pointwiseBoundScalar (I := I) (M := M) g b := by
  unfold pointwiseBoundScalar
  have h2 : 0 ≤ metricInnerOpNorm (I := I) (M := M) g b := norm_nonneg _
  have h3 := orthoBasisSumNormSq_nonneg (I := I) (M := M) g b
  linarith

omit [InnerProductSpace ℝ E] in
lemma metricInnerOpNorm_le_pointwiseBoundScalar
    (g : SmoothRiemannianMetric I M) (b : M) :
    metricInnerOpNorm (I := I) (M := M) g b ≤
      pointwiseBoundScalar (I := I) (M := M) g b := by
  unfold pointwiseBoundScalar
  have h3 := orthoBasisSumNormSq_nonneg (I := I) (M := M) g b
  linarith

omit [InnerProductSpace ℝ E] in
lemma orthoBasisSumNormSq_le_pointwiseBoundScalar
    (g : SmoothRiemannianMetric I M) (b : M) :
    orthoBasisSumNormSq (I := I) (M := M) g b ≤
      pointwiseBoundScalar (I := I) (M := M) g b := by
  unfold pointwiseBoundScalar
  have h2 : 0 ≤ metricInnerOpNorm (I := I) (M := M) g b := norm_nonneg _
  linarith

omit [Module.Finite ℝ E] [InnerProductSpace ℝ E] in
private lemma metric_inner_apply_opNorm_le
    (g : SmoothRiemannianMetric I M) (b : M) (v : TangentSpace I b) :
    ‖g.inner b v‖ ≤ metricInnerOpNorm (I := I) (M := M) g b * ‖v‖ := by
  unfold metricInnerOpNorm
  exact (g.inner b).le_opNorm v

omit [Module.Finite ℝ E] [InnerProductSpace ℝ E] in
private lemma omegaK_opNorm_le
    (g : SmoothRiemannianMetric I M) (b : M) (r : ℕ) (n : ℕ)
    (e : Fin n → TangentSpace I b) (K : Fin r → Fin n) :
    ‖((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin r) ℝ).compContinuousLinearMap
        (fun k => g.inner b (e (K k))) :
        ContinuousMultilinearMap ℝ (fun _ : Fin r => TangentSpace I b) ℝ)‖ ≤
      metricInnerOpNorm (I := I) (M := M) g b ^ r *
        ∏ k : Fin r, ‖e (K k)‖ := by
  have hbase :=
    (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin r) ℝ).norm_compContinuousLinearMap_le
      (fun k => g.inner b (e (K k)))
  have hmkPi : ‖ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin r) ℝ‖ = 1 :=
    ContinuousMultilinearMap.norm_mkPiAlgebra (𝕜 := ℝ) (ι := Fin r) (A := ℝ)
  rw [hmkPi, one_mul] at hbase
  refine hbase.trans ?_
  have hfactor : ∀ k : Fin r,
      ‖g.inner b (e (K k))‖ ≤ metricInnerOpNorm (I := I) (M := M) g b * ‖e (K k)‖ :=
    fun k => metric_inner_apply_opNorm_le (I := I) (M := M) g b (e (K k))
  have hprod_le :
      ∏ k : Fin r, ‖g.inner b (e (K k))‖ ≤
        ∏ k : Fin r, (metricInnerOpNorm (I := I) (M := M) g b * ‖e (K k)‖) := by
    refine Finset.prod_le_prod ?_ ?_
    · intro k _; exact norm_nonneg _
    · intro k _; exact hfactor k
  have hprod_eq :
      ∏ k : Fin r, (metricInnerOpNorm (I := I) (M := M) g b * ‖e (K k)‖) =
        metricInnerOpNorm (I := I) (M := M) g b ^ r *
          ∏ k : Fin r, ‖e (K k)‖ := by
    rw [Finset.prod_mul_distrib]; simp [Finset.prod_const, Finset.card_univ]
  exact hprod_le.trans (le_of_eq hprod_eq)

omit [InnerProductSpace ℝ E] in
lemma fiberNormSqSummand_le_pointwise_bound
    (g : SmoothRiemannianMetric I M) (b : M) (r s : ℕ)
    (T : TensorRSSpace r s I b)
    (n : ℕ) (e : Fin n → TangentSpace I b)
    (K : Fin r → Fin n) (J : Fin s → Fin n) :
    fiberNormSqSummand (I := I) (M := M) g b r s T n e K J ≤
      ‖T‖ ^ 2 *
        (metricInnerOpNorm (I := I) (M := M) g b ^ (2 * r) *
          ((∏ k : Fin r, ‖e (K k)‖ ^ 2) *
            ∏ k : Fin s, ‖e (J k)‖ ^ 2)) := by
  classical
  set omegaK : Tensor0SSpace r I b :=
    ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin r) ℝ).compContinuousLinearMap
      (fun k => g.inner b (e (K k)))) with homega_def
  set TomegaK : Tensor0SSpace s I b :=
    (T : Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b) omegaK with hTomega_def
  set val : ℝ := TomegaK (fun k => e (J k)) with hval_def
  have h_eval : |val| ≤ ‖TomegaK‖ * ∏ k : Fin s, ‖e (J k)‖ := by
    have h := (TomegaK :
        ContinuousMultilinearMap ℝ (fun _ : Fin s => TangentSpace I b) ℝ).le_opNorm
        (fun k => e (J k))
    have hnorm_eq : ‖TomegaK (fun k => e (J k))‖ = |TomegaK (fun k => e (J k))| := rfl
    rw [hnorm_eq] at h
    exact h
  have h_T_apply : ‖TomegaK‖ ≤ ‖T‖ * ‖omegaK‖ := by
    have := tensorRSSpace_norm_apply_le (𝕜 := ℝ) (E := E) (I := I) (M := M)
      (r := r) (s := s) (b := b) T omegaK
    simpa [hTomega_def] using this
  have h_omega_le : ‖omegaK‖ ≤ metricInnerOpNorm (I := I) (M := M) g b ^ r *
      ∏ k : Fin r, ‖e (K k)‖ := by
    simpa [homega_def] using
      omegaK_opNorm_le (I := I) (M := M) g b r n e K
  have hT_nn : 0 ≤ ‖T‖ := norm_nonneg _
  have h_inner_pow_nn : 0 ≤ metricInnerOpNorm (I := I) (M := M) g b ^ r :=
    pow_nonneg (norm_nonneg _) r
  have h_prod_K_nn : 0 ≤ ∏ k : Fin r, ‖e (K k)‖ :=
    Finset.prod_nonneg (fun _ _ => norm_nonneg _)
  have h_prod_J_nn : 0 ≤ ∏ k : Fin s, ‖e (J k)‖ :=
    Finset.prod_nonneg (fun _ _ => norm_nonneg _)
  have h_T_omega_le : ‖TomegaK‖ ≤ ‖T‖ *
      (metricInnerOpNorm (I := I) (M := M) g b ^ r * ∏ k : Fin r, ‖e (K k)‖) :=
    h_T_apply.trans (mul_le_mul_of_nonneg_left h_omega_le hT_nn)
  have h_val_abs : |val| ≤
      ‖T‖ *
        (metricInnerOpNorm (I := I) (M := M) g b ^ r * ∏ k : Fin r, ‖e (K k)‖) *
        ∏ k : Fin s, ‖e (J k)‖ :=
    h_eval.trans (mul_le_mul_of_nonneg_right h_T_omega_le h_prod_J_nn)
  have h_val_nn : 0 ≤ |val| := abs_nonneg _
  have h_sq : val ^ 2 ≤
      (‖T‖ *
          (metricInnerOpNorm (I := I) (M := M) g b ^ r * ∏ k : Fin r, ‖e (K k)‖) *
          ∏ k : Fin s, ‖e (J k)‖) ^ 2 := by
    have h_abs_sq : (|val|) ^ 2 = val ^ 2 := sq_abs val
    have h_sq' : (|val|) ^ 2 ≤
        (‖T‖ *
            (metricInnerOpNorm (I := I) (M := M) g b ^ r * ∏ k : Fin r, ‖e (K k)‖) *
            ∏ k : Fin s, ‖e (J k)‖) ^ 2 :=
      pow_le_pow_left₀ h_val_nn h_val_abs 2
    rwa [h_abs_sq] at h_sq'
  have hRHS_alg :
      (‖T‖ *
          (metricInnerOpNorm (I := I) (M := M) g b ^ r * ∏ k : Fin r, ‖e (K k)‖) *
          ∏ k : Fin s, ‖e (J k)‖) ^ 2 =
        ‖T‖ ^ 2 *
          (metricInnerOpNorm (I := I) (M := M) g b ^ (2 * r) *
            ((∏ k : Fin r, ‖e (K k)‖ ^ 2) *
              ∏ k : Fin s, ‖e (J k)‖ ^ 2)) := by
    have hprodK_sq :
        (∏ k : Fin r, ‖e (K k)‖) ^ 2 = ∏ k : Fin r, ‖e (K k)‖ ^ 2 := by
      rw [← Finset.prod_pow]
    have hprodJ_sq :
        (∏ k : Fin s, ‖e (J k)‖) ^ 2 = ∏ k : Fin s, ‖e (J k)‖ ^ 2 := by
      rw [← Finset.prod_pow]
    have hpow2r :
        (metricInnerOpNorm (I := I) (M := M) g b ^ r) ^ 2 =
          metricInnerOpNorm (I := I) (M := M) g b ^ (2 * r) := by
      rw [← pow_mul, mul_comm]
    have h_expand :
        (‖T‖ *
            (metricInnerOpNorm (I := I) (M := M) g b ^ r * ∏ k : Fin r, ‖e (K k)‖) *
            ∏ k : Fin s, ‖e (J k)‖) ^ 2 =
          ‖T‖ ^ 2 *
            ((metricInnerOpNorm (I := I) (M := M) g b ^ r) ^ 2 *
              ((∏ k : Fin r, ‖e (K k)‖) ^ 2) *
              (∏ k : Fin s, ‖e (J k)‖) ^ 2) := by ring
    rw [h_expand, hpow2r, hprodK_sq, hprodJ_sq]; ring
  have h_target_eq : fiberNormSqSummand (I := I) (M := M) g b r s T n e K J = val ^ 2 := by
    unfold fiberNormSqSummand
    simp [hval_def, hTomega_def, homega_def]
  rw [h_target_eq]
  exact h_sq.trans (le_of_eq hRHS_alg)

noncomputable def ambientFrameNormSq
    (b : M) (n : ℕ) (e : Fin n → TangentSpace I b) : ℝ :=
  ∑ i : Fin n, ‖e i‖ ^ 2

omit [Module.Finite ℝ E] [InnerProductSpace ℝ E] [IsManifold I ∞ M] in
lemma ambientFrameNormSq_nonneg
    (b : M) (n : ℕ) (e : Fin n → TangentSpace I b) :
    0 ≤ ambientFrameNormSq (I := I) (M := M) b n e :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

omit [Module.Finite ℝ E] [InnerProductSpace ℝ E] [IsManifold I ∞ M] in
private lemma sum_prod_norm_sq_eq_pow
    {b : M} (n : ℕ) (e : Fin n → TangentSpace I b) (r : ℕ) :
    (∑ K : Fin r → Fin n, ∏ k : Fin r, ‖e (K k)‖ ^ 2) =
      (∑ i : Fin n, ‖e i‖ ^ 2) ^ r := by
  classical
  rw [Fintype.sum_pow (f := fun (i : Fin n) => ‖e i‖ ^ 2) r]

omit [InnerProductSpace ℝ E] in
lemma riemannianFiberNormSq_sum_le_pointwise
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M)
    (T : TensorRSSpace r s I b)
    (n : ℕ) (e : Fin n → TangentSpace I b) :
    (∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
        fiberNormSqSummand (I := I) (M := M) g b r s T n e K J) ≤
      ‖T‖ ^ 2 *
        (metricInnerOpNorm (I := I) (M := M) g b ^ (2 * r) *
          ambientFrameNormSq (I := I) (M := M) b n e ^ (r + s)) := by
  classical
  have hbound : ∀ K J,
      fiberNormSqSummand (I := I) (M := M) g b r s T n e K J ≤
        ‖T‖ ^ 2 *
          (metricInnerOpNorm (I := I) (M := M) g b ^ (2 * r) *
            ((∏ k : Fin r, ‖e (K k)‖ ^ 2) *
              ∏ k : Fin s, ‖e (J k)‖ ^ 2)) :=
    fun K J => fiberNormSqSummand_le_pointwise_bound
      (I := I) (M := M) g b r s T n e K J
  have h_sum_bound :
      (∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
          fiberNormSqSummand (I := I) (M := M) g b r s T n e K J) ≤
        ∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
          ‖T‖ ^ 2 *
            (metricInnerOpNorm (I := I) (M := M) g b ^ (2 * r) *
              ((∏ k : Fin r, ‖e (K k)‖ ^ 2) *
                ∏ k : Fin s, ‖e (J k)‖ ^ 2)) := by
    refine Finset.sum_le_sum (fun K _ => ?_)
    exact Finset.sum_le_sum (fun J _ => hbound K J)
  refine h_sum_bound.trans ?_
  have hfactor :
      (∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
          ‖T‖ ^ 2 *
            (metricInnerOpNorm (I := I) (M := M) g b ^ (2 * r) *
              ((∏ k : Fin r, ‖e (K k)‖ ^ 2) *
                ∏ k : Fin s, ‖e (J k)‖ ^ 2))) =
        ‖T‖ ^ 2 *
          (metricInnerOpNorm (I := I) (M := M) g b ^ (2 * r) *
            ((∑ K : Fin r → Fin n, ∏ k : Fin r, ‖e (K k)‖ ^ 2) *
              ∑ J : Fin s → Fin n, ∏ k : Fin s, ‖e (J k)‖ ^ 2)) := by
    have step1 :
        (∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
            ‖T‖ ^ 2 *
              (metricInnerOpNorm (I := I) (M := M) g b ^ (2 * r) *
                ((∏ k : Fin r, ‖e (K k)‖ ^ 2) *
                  ∏ k : Fin s, ‖e (J k)‖ ^ 2))) =
          ‖T‖ ^ 2 *
            ∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
              (metricInnerOpNorm (I := I) (M := M) g b ^ (2 * r) *
                ((∏ k : Fin r, ‖e (K k)‖ ^ 2) *
                  ∏ k : Fin s, ‖e (J k)‖ ^ 2)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun K _ => ?_)
      rw [Finset.mul_sum]
    rw [step1]
    refine congrArg (HMul.hMul _) ?_
    have step2 :
        (∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
            metricInnerOpNorm (I := I) (M := M) g b ^ (2 * r) *
              ((∏ k : Fin r, ‖e (K k)‖ ^ 2) *
                ∏ k : Fin s, ‖e (J k)‖ ^ 2)) =
          metricInnerOpNorm (I := I) (M := M) g b ^ (2 * r) *
            ∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
              ((∏ k : Fin r, ‖e (K k)‖ ^ 2) *
                ∏ k : Fin s, ‖e (J k)‖ ^ 2) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun K _ => ?_)
      rw [Finset.mul_sum]
    rw [step2]
    refine congrArg (HMul.hMul _) ?_
    rw [Finset.sum_mul_sum]
  rw [hfactor]
  rw [sum_prod_norm_sq_eq_pow (b := b) n e r,
      sum_prod_norm_sq_eq_pow (b := b) n e s]
  unfold ambientFrameNormSq
  rw [pow_add]

omit [InnerProductSpace ℝ E] in
lemma riemannianFiberNormSq_eq_sum_witness
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M)
    (T : TensorRSSpace r s I b) :
    ∃ (n : ℕ) (e : Fin n → TangentSpace I b),
      n = Module.finrank ℝ (TangentSpace I b) ∧
      riemannianFiberNormSq (I := I) (M := M) g r s b T =
        ∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
          fiberNormSqSummand (I := I) (M := M) g b r s T n e K J := by
  classical
  let cd : InnerProductSpace.Core ℝ (TangentSpace I b) := g.toRiemannianMetric.toCore b
  have hc : ContinuousAt (fun v : TangentSpace I b => cd.inner v v) 0 :=
    g.toRiemannianMetric.continuousAt b
  have hb : Bornology.IsVonNBounded ℝ {v : TangentSpace I b |
      RCLike.re (cd.inner v v) < 1} :=
    g.toRiemannianMetric.isVonNBounded b
  letI : NormedAddCommGroup (TangentSpace I b) :=
    cd.toNormedAddCommGroupOfTopology hc hb
  letI : InnerProductSpace ℝ (TangentSpace I b) :=
    InnerProductSpace.ofCoreOfTopology cd hc hb
  let n : ℕ := Module.finrank ℝ (TangentSpace I b)
  let e : OrthonormalBasis (Fin n) ℝ (TangentSpace I b) := stdOrthonormalBasis ℝ _
  refine ⟨n, fun i => e i, rfl, ?_⟩
  rfl

omit [InnerProductSpace ℝ E] in
lemma riemannianFiberNormSq_le_pointwise_witness
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M)
    (T : TensorRSSpace r s I b) :
    ∃ (Ab : ℝ), 0 ≤ Ab ∧
      riemannianFiberNormSq (I := I) (M := M) g r s b T ≤
        ‖T‖ ^ 2 *
          (metricInnerOpNorm (I := I) (M := M) g b ^ (2 * r) *
            Ab ^ (r + s)) := by
  obtain ⟨n, e, _hn, h_eq⟩ :=
    riemannianFiberNormSq_eq_sum_witness (I := I) (M := M) g r s b T
  refine ⟨ambientFrameNormSq (I := I) (M := M) b n e,
    ambientFrameNormSq_nonneg (I := I) (M := M) b n e, ?_⟩
  rw [h_eq]
  exact riemannianFiberNormSq_sum_le_pointwise (I := I) (M := M) g r s b T n e

end Connection
end Integral
end DifferentialGeometry

end
