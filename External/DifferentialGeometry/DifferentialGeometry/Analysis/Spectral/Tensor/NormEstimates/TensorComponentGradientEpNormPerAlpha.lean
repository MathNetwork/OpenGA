import DifferentialGeometry.Analysis.Spectral.Tensor.NormEstimates.GradNormChartBoundPouWeighted
import DifferentialGeometry.Analysis.Spectral.Tensor.NormEstimates.TensorComponentGradientL2Atoms
import DifferentialGeometry.Analysis.Spectral.Tensor.TrivProj.ChartTwistIdentity
import DifferentialGeometry.Analysis.Spectral.Tensor.UniformChartBounds.TensorChartTwistUniformBound
import DifferentialGeometry.Analysis.Spectral.Tensor.NormEstimates.GradNormChartBound
import DifferentialGeometry.Geometry.Metric.MetricBounds

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 2400000
set_option maxHeartbeats 2400000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

lemma sqrt_add_le_sqrt_add_sqrt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  have h_sum_nn : 0 ≤ a + b := add_nonneg ha hb
  have h_sa_nn : 0 ≤ Real.sqrt a := Real.sqrt_nonneg _
  have h_sb_nn : 0 ≤ Real.sqrt b := Real.sqrt_nonneg _
  have h_sum_sq_nn : 0 ≤ Real.sqrt a + Real.sqrt b := add_nonneg h_sa_nn h_sb_nn
  have h_lhs_sq : Real.sqrt (a + b) ^ 2 = a + b := Real.sq_sqrt h_sum_nn
  have h_rhs_sq : (Real.sqrt a + Real.sqrt b) ^ 2 =
      a + b + 2 * (Real.sqrt a * Real.sqrt b) := by
    rw [add_pow_two, Real.sq_sqrt ha, Real.sq_sqrt hb]; ring
  have h_cross_nn : 0 ≤ 2 * (Real.sqrt a * Real.sqrt b) := by positivity
  have h_sq_le : Real.sqrt (a + b) ^ 2 ≤ (Real.sqrt a + Real.sqrt b) ^ 2 := by
    rw [h_lhs_sq, h_rhs_sq]; linarith
  exact (abs_le_of_sq_le_sq' h_sq_le h_sum_sq_nn).2

lemma sqrt_add3_le_sum {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    Real.sqrt (a + b + c) ≤ Real.sqrt a + Real.sqrt b + Real.sqrt c := by
  have h_ab_nn : 0 ≤ a + b := add_nonneg ha hb
  have h_step1 : Real.sqrt (a + b + c) ≤ Real.sqrt (a + b) + Real.sqrt c :=
    sqrt_add_le_sqrt_add_sqrt h_ab_nn hc
  have h_step2 : Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b :=
    sqrt_add_le_sqrt_add_sqrt ha hb
  linarith

lemma coe_nnnorm_eq_ofReal_norm {X : Type*} [SeminormedAddCommGroup X]
    (x : X) :
    (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖x‖ := by
  rw [show ((‖x‖₊ : ℝ≥0∞)) = ‖x‖ₑ from (enorm_eq_nnnorm x).symm,
    ← ofReal_norm_eq_enorm x]

lemma sum_norm_sq_le_card_mul_sum_norm_sq
    {ι : Type*} {X : Type*} [SeminormedAddCommGroup X]
    (s : Finset ι) (x : ι → X) :
    ‖∑ i ∈ s, x i‖ ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖x i‖ ^ 2 := by
  classical
  have h_tri : ‖∑ i ∈ s, x i‖ ≤ ∑ i ∈ s, ‖x i‖ := norm_sum_le _ _
  have h_lhs_nn : 0 ≤ ‖∑ i ∈ s, x i‖ := norm_nonneg _
  have h_rhs_nn : 0 ≤ ∑ i ∈ s, ‖x i‖ :=
    Finset.sum_nonneg (fun i _ => norm_nonneg _)
  have h_sq_tri : ‖∑ i ∈ s, x i‖ ^ 2 ≤ (∑ i ∈ s, ‖x i‖) ^ 2 := by
    have := mul_self_le_mul_self h_lhs_nn h_tri
    rw [← sq, ← sq] at this
    exact this
  have h_pmi : (∑ i ∈ s, ‖x i‖) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖x i‖ ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  exact h_sq_tri.trans h_pmi

lemma norm_sq_neg_sum_add_sum_le_two_mul
    {r' s' : ℕ} {X : Type*} [SeminormedAddCommGroup X]
    (x : Fin r' → X) (y : Fin s' → X) :
    ‖- (∑ i : Fin r', x i) + (∑ l : Fin s', y l)‖ ^ 2 ≤
      2 * (‖∑ i : Fin r', x i‖ ^ 2 + ‖∑ l : Fin s', y l‖ ^ 2) := by
  classical
  set u : X := ∑ i : Fin r', x i with hu_def
  set v : X := ∑ l : Fin s', y l with hv_def
  have h_tri : ‖- u + v‖ ≤ ‖u‖ + ‖v‖ := by
    calc ‖- u + v‖ ≤ ‖- u‖ + ‖v‖ := norm_add_le _ _
      _ = ‖u‖ + ‖v‖ := by rw [norm_neg]
  have h_lhs_nn : 0 ≤ ‖- u + v‖ := norm_nonneg _
  have h_rhs_nn : 0 ≤ ‖u‖ + ‖v‖ := by positivity
  have h_sq : ‖- u + v‖ ^ 2 ≤ (‖u‖ + ‖v‖) ^ 2 := by
    have := mul_self_le_mul_self h_lhs_nn h_tri
    rw [← sq, ← sq] at this
    exact this
  have h_abc : (‖u‖ + ‖v‖) ^ 2 ≤ 2 * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
    have h_id : (‖u‖ + ‖v‖) ^ 2 + (‖u‖ - ‖v‖) ^ 2 = 2 * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
      ring
    have h_diff_nn : 0 ≤ (‖u‖ - ‖v‖) ^ 2 := sq_nonneg _
    linarith
  exact h_sq.trans h_abc

lemma sqrt_sum_le_sum_sqrt_fin {n : ℕ} (a : Fin n → ℝ)
    (ha : ∀ k, 0 ≤ a k) :
    Real.sqrt (∑ k : Fin n, a k) ≤ ∑ k : Fin n, Real.sqrt (a k) := by
  classical
  suffices h : ∀ (s : Finset (Fin n)),
      Real.sqrt (∑ k ∈ s, a k) ≤ ∑ k ∈ s, Real.sqrt (a k) by
    simpa using h Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert k₀ s' hk_notin ih =>
      rw [Finset.sum_insert hk_notin, Finset.sum_insert hk_notin]
      have h_a_nn : 0 ≤ a k₀ := ha k₀
      have h_sum_nn : 0 ≤ ∑ k ∈ s', a k :=
        Finset.sum_nonneg (fun k _ => ha k)
      have h_sqrt_add :=
        sqrt_add_le_sqrt_add_sqrt h_a_nn h_sum_nn
      have h_sqrt_ind : Real.sqrt (∑ k ∈ s', a k) ≤ ∑ k ∈ s', Real.sqrt (a k) := ih
      linarith

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace
  Bundle.continuousMultilinearMap.instNormedAddCommGroup
  Bundle.continuousMultilinearMap.instNormedSpace in
omit [CompleteSpace E] in
private theorem tchr_model_triv_sum_le_const_mul_tensorInnerPointwise_on_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : SmoothCcTensor g r s) {b : M},
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        (∑ k : Fin (Module.finrank ℝ E),
            ‖(trivializationAt (TensorRSModel r s ℝ E)
                (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
              (- (∑ i : Fin r,
                  chartTensorRSInputSlotCorrection (I := I) r s g α
                    (fun b' => T.toSection b')
                    (chartBasisVecFiber (I := I) α k) b i)
                + (∑ l : Fin s,
                    chartTensorRSOutputSlotCorrection (I := I) r s g α
                      (fun b' => T.toSection b')
                      (chartBasisVecFiber (I := I) α k) b l))‖ ^ 2) ≤
          C * tensorInnerPointwise (I := I) (M := M) g r s b (T.toFun b) (T.toFun b) := by
  classical
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
  set n : ℕ := Module.finrank ℝ E with hn_def
  obtain ⟨M_F_in, hM_F_in_nn, hM_F_in_le⟩ :=
    chartTensorRSInputSlotCorrection_riemannian_norm_le_on_pouTsupport_local
      (I := I) (M := M) g r s α
  obtain ⟨M_F_out, hM_F_out_nn, hM_F_out_le⟩ :=
    chartTensorRSOutputSlotCorrection_riemannian_norm_le_on_pouTsupport_local
      (I := I) (M := M) g r s α
  set M_F : ℝ := max M_F_in M_F_out with hM_F_def
  have hM_F_nn : 0 ≤ M_F := le_max_of_le_left hM_F_in_nn
  have hK_cpt : IsCompact (tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) :=
    pouTsupport_isCompact (I := I) (M := M) α
  have hK_sub : tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ⊆ (chartAt H α).source :=
    fun x hx => chartAtlasPOU_isSubordinate (I := I) (M := M) α hx
  obtain ⟨Cto, hCto_pos, hCto_bound⟩ :=
    tensorRSChartFiberToModel_opNorm_isBounded_on_compact_unconditional
      (I := I) (M := M) g r s α hK_cpt hK_sub
  have hCto_nn : 0 ≤ Cto := le_of_lt hCto_pos
  refine ⟨Cto ^ 2 * (2 * ((r : ℝ) + (s : ℝ))) * (n : ℝ) *
      ((r : ℝ) + (s : ℝ)) * M_F ^ 2, by positivity, ?_⟩
  intro T b hb
  have h_sec_iso : ‖T.toSection b‖ ^ 2 =
      tensorInnerPointwise (I := I) (M := M) g r s b (T.toFun b) (T.toFun b) := by
    have h_inner : (⟪T.toSection b, T.toSection b⟫_ℝ : ℝ) =
        tensorInnerPointwise (I := I) (M := M) g r s b (T.toFun b) (T.toFun b) := by
      change DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM
          (I := I) (M := M) g r s b (T.toSection b) (T.toSection b) = _
      rw [DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM_apply]
      rfl
    rw [← h_inner, real_inner_self_eq_norm_sq]
  have h_per_k : ∀ k : Fin n,
      ‖(trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
        (- (∑ i : Fin r,
            chartTensorRSInputSlotCorrection (I := I) r s g α
              (fun b' => T.toSection b')
              (chartBasisVecFiber (I := I) α k) b i)
          + (∑ l : Fin s,
              chartTensorRSOutputSlotCorrection (I := I) r s g α
                (fun b' => T.toSection b')
                (chartBasisVecFiber (I := I) α k) b l))‖ ^ 2 ≤
        Cto ^ 2 * (2 * ((r : ℝ) + (s : ℝ))) * ((r : ℝ) + (s : ℝ)) *
          M_F ^ 2 * ‖T.toSection b‖ ^ 2 := by
    intro k
    set a : Fin r → TensorRSSpace r s I b := fun i =>
      chartTensorRSInputSlotCorrection (I := I) r s g α
        (fun b' => T.toSection b') (chartBasisVecFiber (I := I) α k) b i with ha_def
    set c : Fin s → TensorRSSpace r s I b := fun l =>
      chartTensorRSOutputSlotCorrection (I := I) r s g α
        (fun b' => T.toSection b') (chartBasisVecFiber (I := I) α k) b l with hc_def
    set X : TensorRSSpace r s I b := - (∑ i : Fin r, a i) + (∑ l : Fin s, c l)
      with hX_def
    have h_to : ‖(trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b X‖ ≤
        Cto * ‖X‖ := hCto_bound b hb X
    have h_sq := mul_self_le_mul_self (norm_nonneg _) h_to
    have h_model_le : ‖(trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b X‖ ^ 2 ≤
        Cto ^ 2 * ‖X‖ ^ 2 := by nlinarith [h_sq, sq_nonneg Cto, norm_nonneg X]
    have h_X_sq_split : ‖X‖ ^ 2 ≤
        2 * (‖∑ i : Fin r, a i‖ ^ 2 + ‖∑ l : Fin s, c l‖ ^ 2) :=
      norm_sq_neg_sum_add_sum_le_two_mul (r' := r) (s' := s) a c
    have h_sum_a_sq : ‖∑ i : Fin r, a i‖ ^ 2 ≤
        (r : ℝ) * ∑ i : Fin r, ‖a i‖ ^ 2 := by
      have h := sum_norm_sq_le_card_mul_sum_norm_sq
        (s := (Finset.univ : Finset (Fin r))) a
      rwa [Finset.card_univ, Fintype.card_fin] at h
    have h_sum_c_sq : ‖∑ l : Fin s, c l‖ ^ 2 ≤
        (s : ℝ) * ∑ l : Fin s, ‖c l‖ ^ 2 := by
      have h := sum_norm_sq_le_card_mul_sum_norm_sq
        (s := (Finset.univ : Finset (Fin s))) c
      rwa [Finset.card_univ, Fintype.card_fin] at h
    have h_a_each : ∀ i : Fin r, ‖a i‖ ^ 2 ≤ M_F ^ 2 * ‖T.toSection b‖ ^ 2 := by
      intro i
      have h0 : ‖a i‖ ≤ M_F_in * ‖T.toSection b‖ :=
        hM_F_in_le (fun b' => T.toSection b') (b := b) hb k i
      have h_bnd : ‖a i‖ ≤ M_F * ‖T.toSection b‖ :=
        h0.trans (mul_le_mul_of_nonneg_right (le_max_left M_F_in M_F_out)
          (norm_nonneg (T.toSection b)))
      have hsq := mul_self_le_mul_self (norm_nonneg (a i)) h_bnd
      nlinarith [hsq, sq_nonneg M_F, norm_nonneg (T.toSection b)]
    have h_c_each : ∀ l : Fin s, ‖c l‖ ^ 2 ≤ M_F ^ 2 * ‖T.toSection b‖ ^ 2 := by
      intro l
      have h0 : ‖c l‖ ≤ M_F_out * ‖T.toSection b‖ :=
        hM_F_out_le (fun b' => T.toSection b') (b := b) hb k l
      have h_bnd : ‖c l‖ ≤ M_F * ‖T.toSection b‖ :=
        h0.trans (mul_le_mul_of_nonneg_right (le_max_right M_F_in M_F_out)
          (norm_nonneg (T.toSection b)))
      have hsq := mul_self_le_mul_self (norm_nonneg (c l)) h_bnd
      nlinarith [hsq, sq_nonneg M_F, norm_nonneg (T.toSection b)]
    have h_sum_a_M : ∑ i : Fin r, ‖a i‖ ^ 2 ≤
        (r : ℝ) * (M_F ^ 2 * ‖T.toSection b‖ ^ 2) := by
      have h_le := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin r)))
        (fun i _ => h_a_each i)
      rwa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h_le
    have h_sum_c_M : ∑ l : Fin s, ‖c l‖ ^ 2 ≤
        (s : ℝ) * (M_F ^ 2 * ‖T.toSection b‖ ^ 2) := by
      have h_le := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin s)))
        (fun l _ => h_c_each l)
      rwa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h_le
    have h_a_sum_nn : 0 ≤ ∑ i : Fin r, ‖a i‖ ^ 2 :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have h_c_sum_nn : 0 ≤ ∑ l : Fin s, ‖c l‖ ^ 2 :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have h_secsq_nn : 0 ≤ ‖T.toSection b‖ ^ 2 := sq_nonneg _
    have h_MF_sq_nn : 0 ≤ M_F ^ 2 := sq_nonneg _
    have h_r_le : (r : ℝ) ≤ (r : ℝ) + (s : ℝ) := by
      have : (0 : ℝ) ≤ (s : ℝ) := by positivity
      linarith
    have h_s_le : (s : ℝ) ≤ (r : ℝ) + (s : ℝ) := by
      have : (0 : ℝ) ≤ (r : ℝ) := by positivity
      linarith
    have h_X_sq_bound : ‖X‖ ^ 2 ≤
        2 * ((r : ℝ) + (s : ℝ)) * (((r : ℝ) + (s : ℝ)) * M_F ^ 2 *
          ‖T.toSection b‖ ^ 2) := by
      have h_sum_le : (∑ i : Fin r, ‖a i‖ ^ 2) + (∑ l : Fin s, ‖c l‖ ^ 2) ≤
          ((r : ℝ) + (s : ℝ)) * M_F ^ 2 * ‖T.toSection b‖ ^ 2 := by
        have hab := add_le_add h_sum_a_M h_sum_c_M
        have hr := mul_le_mul_of_nonneg_right h_r_le (mul_nonneg h_MF_sq_nn h_secsq_nn)
        have hs := mul_le_mul_of_nonneg_right h_s_le (mul_nonneg h_MF_sq_nn h_secsq_nn)
        nlinarith [hab, hr, hs]
      nlinarith [h_X_sq_split, h_sum_le, h_a_sum_nn, h_c_sum_nn,
        mul_nonneg h_MF_sq_nn h_secsq_nn]
    have h_Cto_sq_nn : 0 ≤ Cto ^ 2 := sq_nonneg _
    calc ‖(trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b X‖ ^ 2
        ≤ Cto ^ 2 * ‖X‖ ^ 2 := h_model_le
      _ ≤ Cto ^ 2 * (2 * ((r : ℝ) + (s : ℝ)) *
            (((r : ℝ) + (s : ℝ)) * M_F ^ 2 * ‖T.toSection b‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left h_X_sq_bound h_Cto_sq_nn
      _ = Cto ^ 2 * (2 * ((r : ℝ) + (s : ℝ))) * ((r : ℝ) + (s : ℝ)) *
            M_F ^ 2 * ‖T.toSection b‖ ^ 2 := by ring
  calc (∑ k : Fin n,
          ‖(trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
            (- (∑ i : Fin r,
                chartTensorRSInputSlotCorrection (I := I) r s g α
                  (fun b' => T.toSection b')
                  (chartBasisVecFiber (I := I) α k) b i)
              + (∑ l : Fin s,
                  chartTensorRSOutputSlotCorrection (I := I) r s g α
                    (fun b' => T.toSection b')
                    (chartBasisVecFiber (I := I) α k) b l))‖ ^ 2)
      ≤ ∑ _k : Fin n,
          (Cto ^ 2 * (2 * ((r : ℝ) + (s : ℝ))) * ((r : ℝ) + (s : ℝ)) *
            M_F ^ 2 * ‖T.toSection b‖ ^ 2) :=
        Finset.sum_le_sum (fun k _ => h_per_k k)
    _ = Cto ^ 2 * (2 * ((r : ℝ) + (s : ℝ))) * (n : ℝ) * ((r : ℝ) + (s : ℝ)) *
          M_F ^ 2 * ‖T.toSection b‖ ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
    _ = Cto ^ 2 * (2 * ((r : ℝ) + (s : ℝ))) * (n : ℝ) * ((r : ℝ) + (s : ℝ)) *
          M_F ^ 2 *
          tensorInnerPointwise (I := I) (M := M) g r s b (T.toFun b) (T.toFun b) := by
        rw [h_sec_iso]

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace
  Bundle.continuousMultilinearMap.instNormedAddCommGroup
  Bundle.continuousMultilinearMap.instNormedSpace in

omit [CompleteSpace E] in
theorem exists_eLpNorm_sqrt_g_inner_gradFun_tensorChartComponentScalar_le_const_mul_h1Norm
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensorH1 g r s)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        eLpNorm (fun b : M => Real.sqrt
            (g.inner b
              (gradFun (I := I) g
                (tensorChartComponentScalar (I := I) (M := M)
                  g r s S.toCcTensor α Idx Jdx) b)
              (gradFun (I := I) g
                (tensorChartComponentScalar (I := I) (M := M)
                  g r s S.toCcTensor α Idx Jdx) b))) 2
            (riemannianVolumeMeasure (I := I) (M := M) g) ≤
          ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞) := by
  classical
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
  obtain ⟨A, B, hA_nn, hB_nn, h_G1⟩ :=
    g_inner_gradFun_le_pou_weighted_atoms_on_pouTsupport_h1
      (I := I) (M := M) g r s α
  obtain ⟨C₂, hC₂_nn, h_G2⟩ :=
    exists_eLpNorm_sq_pou_mul_sum_triv_chart_cov_le_const_mul_h1NormSq
      (I := I) (M := M) g r s α
  obtain ⟨C₄, hC₄_nn, h_G4⟩ :=
    exists_integral_indicator_tsupp_raw_sq_le_const_mul_h1NormSq
      (I := I) (M := M) g r s α
  obtain ⟨Cchr, hCchr_nn, h_Tchr_TIP⟩ :=
    tchr_model_triv_sum_le_const_mul_tensorInnerPointwise_on_pouTsupport
      (I := I) (M := M) g r s α
  set C₃ : ℝ := B * Cchr with hC₃_def
  have hC₃_nn : 0 ≤ C₃ := by rw [hC₃_def]; positivity
  set C_sq : ℝ := A * C₄ ^ 2 + B * C₂ ^ 2 + C₃ with hC_sq_def
  have hC_sq_nn : 0 ≤ C_sq := by rw [hC_sq_def]; positivity
  set C : ℝ := Real.sqrt C_sq with hC_def
  have hC_nn : 0 ≤ C := Real.sqrt_nonneg _
  refine ⟨C, hC_nn, ?_⟩
  intro S Idx Jdx
  set μ : MeasureTheory.Measure M := riemannianVolumeMeasure (I := I) (M := M) g
    with hμ_def
  set u : M → ℝ := tensorChartComponentScalar (I := I) (M := M)
      g r s S.toCcTensor α Idx Jdx with hu_def
  set ρ : M → ℝ := fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x with hρ_def
  set Tinner : M → ℝ := fun b : M =>
      g.inner b (gradFun (I := I) g u b) (gradFun (I := I) g u b)
    with hTinner_def
  set TinnerSqrt : M → ℝ := fun b : M => Real.sqrt (Tinner b) with hTinnerSqrt_def
  have hTinner_nn : ∀ b, 0 ≤ Tinner b := fun b => by
    rw [hTinner_def]
    exact DifferentialGeometry.Analysis.Laplacian.metric_inner_self_nonneg
      (I := I) (M := M) g b _
  change eLpNorm TinnerSqrt 2 μ ≤ ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞)
  set rawZ : M → ℝ := fun b : M =>
      scalarOnE (I := I) α
        (tensorChartComponentRaw (I := I) (M := M)
          g r s S.toCcTensor α Idx Jdx) (extChartAt I α b) with hrawZ_def
  set rawInd : M → ℝ := fun b : M =>
      (tsupport ρ).indicator rawZ b with hrawInd_def
  set Tcov : M → ℝ := fun b : M => ∑ k : Fin (Module.finrank ℝ E),
      ‖(trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
        (chartTensorRSCovariantDerivative (I := I) r s g α
          (fun b' => S.toCcTensor.toSection b')
          (chartBasisVecFiber (I := I) α k) b)‖ ^ 2
    with hTcov_def
  set Tchr : M → ℝ := fun b : M => ∑ k : Fin (Module.finrank ℝ E),
      ‖(trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
        (- (∑ i : Fin r,
            chartTensorRSInputSlotCorrection (I := I) r s g α
              (fun b' => S.toCcTensor.toSection b')
              (chartBasisVecFiber (I := I) α k) b i)
          + (∑ l : Fin s,
              chartTensorRSOutputSlotCorrection (I := I) r s g α
                (fun b' => S.toCcTensor.toSection b')
                (chartBasisVecFiber (I := I) α k) b l))‖ ^ 2
    with hTchr_def
  have hρ_nn : ∀ b, 0 ≤ ρ b := fun b => by
    rw [hρ_def]; exact (chartAtlasPOU I M).nonneg α b
  have hTcov_nn : ∀ b, 0 ≤ Tcov b := fun b => by
    rw [hTcov_def]; exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hTchr_nn : ∀ b, 0 ≤ Tchr b := fun b => by
    rw [hTchr_def]; exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have h_ptbound : ∀ b : M, Tinner b ≤
      A * (rawInd b) ^ 2 + B * (ρ b) ^ 2 * Tcov b + B * (ρ b) ^ 2 * Tchr b := by
    intro b
    by_cases hb : b ∈ tsupport ρ
    · have h_G1_b := h_G1 S Idx Jdx b hb
      have h_G1' : Tinner b ≤
          A * rawZ b ^ 2 + B * (ρ b) ^ 2 * (Tcov b + Tchr b) := h_G1_b
      have h_rawInd_eq : rawInd b = rawZ b := by
        change (tsupport ρ).indicator rawZ b = rawZ b
        exact Set.indicator_of_mem hb _
      calc Tinner b
          ≤ A * rawZ b ^ 2 + B * (ρ b) ^ 2 * (Tcov b + Tchr b) := h_G1'
        _ = A * rawInd b ^ 2 + B * (ρ b) ^ 2 * Tcov b + B * (ρ b) ^ 2 * Tchr b := by
            rw [h_rawInd_eq]; ring
    · have h_sqrt_zero :
          Real.sqrt (g.inner b
            (gradFun (I := I) g
              (tensorChartComponentScalar (I := I) (M := M)
                g r s S.toCcTensor α Idx Jdx) b)
            (gradFun (I := I) g
              (tensorChartComponentScalar (I := I) (M := M)
                g r s S.toCcTensor α Idx Jdx) b)) = 0 :=
        sqrt_g_inner_gradFun_tensorChartComponentScalar_eq_zero_outside_pouTsupport
          (I := I) (M := M) g r s S.toCcTensor α Idx Jdx hb
      have h_Tinner_zero : Tinner b = 0 := by
        rw [hTinner_def, hu_def]
        have h_nn := hTinner_nn b
        rw [hTinner_def, hu_def] at h_nn
        exact (Real.sqrt_eq_zero h_nn).mp h_sqrt_zero
      rw [h_Tinner_zero]
      have h_rawInd_zero : rawInd b = 0 := by
        change (tsupport ρ).indicator rawZ b = 0
        exact Set.indicator_of_notMem hb _
      have h_ρ_zero : ρ b = 0 := by
        by_contra hne; exact hb (subset_tsupport _ hne)
      rw [h_rawInd_zero, h_ρ_zero]; simp
  have h_TinnerSqrt_sq : ∀ b, (TinnerSqrt b) ^ 2 = Tinner b := fun b => by
    rw [hTinnerSqrt_def, Real.sq_sqrt (hTinner_nn b)]
  have h_pt_enn : ∀ b, (‖TinnerSqrt b‖ₑ : ℝ≥0∞) ^ 2 ≤
      ENNReal.ofReal (A * (rawInd b) ^ 2) +
        ENNReal.ofReal (B * (ρ b) ^ 2 * Tcov b) +
        ENNReal.ofReal (B * (ρ b) ^ 2 * Tchr b) := by
    intro b
    have h_lhs : (‖TinnerSqrt b‖ₑ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (Tinner b) := by
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _),
        sq_abs, h_TinnerSqrt_sq]
    rw [h_lhs]
    have h_t1_nn : 0 ≤ A * (rawInd b) ^ 2 := mul_nonneg hA_nn (sq_nonneg _)
    have h_t2_nn : 0 ≤ B * (ρ b) ^ 2 * Tcov b :=
      mul_nonneg (mul_nonneg hB_nn (sq_nonneg _)) (hTcov_nn b)
    have h_t3_nn : 0 ≤ B * (ρ b) ^ 2 * Tchr b :=
      mul_nonneg (mul_nonneg hB_nn (sq_nonneg _)) (hTchr_nn b)
    have h_add :
        ENNReal.ofReal (A * (rawInd b) ^ 2 + B * (ρ b) ^ 2 * Tcov b +
            B * (ρ b) ^ 2 * Tchr b) =
          ENNReal.ofReal (A * (rawInd b) ^ 2) +
            ENNReal.ofReal (B * (ρ b) ^ 2 * Tcov b) +
            ENNReal.ofReal (B * (ρ b) ^ 2 * Tchr b) := by
      rw [ENNReal.ofReal_add (add_nonneg h_t1_nn h_t2_nn) h_t3_nn,
          ENNReal.ofReal_add h_t1_nn h_t2_nn]
    rw [← h_add]
    exact ENNReal.ofReal_le_ofReal (h_ptbound b)
  have h_sq_to_lint : (eLpNorm TinnerSqrt 2 μ) ^ 2 =
      ∫⁻ b, (‖TinnerSqrt b‖ₑ : ℝ≥0∞) ^ 2 ∂μ :=
    sq_eLpNorm_two_eq_lintegral_enorm_sq μ TinnerSqrt
  have h_sq_bound : (eLpNorm TinnerSqrt 2 μ) ^ 2 ≤
      ENNReal.ofReal (C_sq * ‖S‖ ^ 2) := by
    rw [h_sq_to_lint]
    set f1 : M → ℝ≥0∞ := fun b => ENNReal.ofReal (A * (rawInd b) ^ 2) with hf1_def
    set f2 : M → ℝ≥0∞ :=
      fun b => ENNReal.ofReal (B * (ρ b) ^ 2 * Tcov b) with hf2_def
    set f3 : M → ℝ≥0∞ :=
      fun b => ENNReal.ofReal (B * (ρ b) ^ 2 * Tchr b) with hf3_def
    have h_lint_mono :
        ∫⁻ b, (‖TinnerSqrt b‖ₑ : ℝ≥0∞) ^ 2 ∂μ ≤ ∫⁻ b, f1 b + f2 b + f3 b ∂μ := by
      refine lintegral_mono_ae ?_
      filter_upwards with b using h_pt_enn b
    refine h_lint_mono.trans ?_
    have h_atom3 :
        AEStronglyMeasurable
          (fun b : M =>
            (tsupport (fun x : M =>
                ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)).indicator
              (fun b' : M => |scalarOnE (I := I) α
                (tensorChartComponentRaw (I := I) (M := M)
                  g r s S.toCcTensor α Idx Jdx)
                (extChartAt I α b')|) b)
          μ :=
      aestronglyMeasurable_indicator_tsupp_abs_raw
        (I := I) (M := M) g r s α S Idx Jdx
    have h_rawInd_sq_eq :
        ∀ b, (rawInd b) ^ 2 =
          ((tsupport (fun x : M =>
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)).indicator
            (fun b' : M => |scalarOnE (I := I) α
              (tensorChartComponentRaw (I := I) (M := M)
                g r s S.toCcTensor α Idx Jdx)
              (extChartAt I α b')|) b) ^ 2 := by
      intro b
      by_cases hb : b ∈ tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)
      · have h1 : rawInd b = rawZ b := by
          change (tsupport _).indicator rawZ b = rawZ b
          exact Set.indicator_of_mem hb _
        have h2 :
            (tsupport (fun x : M =>
                ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)).indicator
              (fun b' : M => |scalarOnE (I := I) α
                (tensorChartComponentRaw (I := I) (M := M)
                  g r s S.toCcTensor α Idx Jdx)
                (extChartAt I α b')|) b = |rawZ b| :=
          Set.indicator_of_mem hb _
        rw [h1, h2, sq_abs]
      · have h1 : rawInd b = 0 := by
          change (tsupport _).indicator rawZ b = 0
          exact Set.indicator_of_notMem hb _
        have h2 :
            (tsupport (fun x : M =>
                ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)).indicator
              (fun b' : M => |scalarOnE (I := I) α
                (tensorChartComponentRaw (I := I) (M := M)
                  g r s S.toCcTensor α Idx Jdx)
                (extChartAt I α b')|) b = 0 :=
          Set.indicator_of_notMem hb _
        rw [h1, h2]
    have h_f1_ae_str : AEStronglyMeasurable f1 μ := by
      have h_sq : AEStronglyMeasurable (fun b : M => (rawInd b) ^ 2) μ := by
        have : (fun b : M => (rawInd b) ^ 2) =
            (fun b : M =>
              ((tsupport (fun x : M =>
                  ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)).indicator
                (fun b' : M => |scalarOnE (I := I) α
                  (tensorChartComponentRaw (I := I) (M := M)
                    g r s S.toCcTensor α Idx Jdx)
                  (extChartAt I α b')|) b) ^ 2) := by
          funext b; exact h_rawInd_sq_eq b
        rw [this]
        exact (continuous_pow 2).comp_aestronglyMeasurable h_atom3
      have h_A_sq : AEStronglyMeasurable (fun b : M => A * (rawInd b) ^ 2) μ :=
        h_sq.const_mul A
      exact (ENNReal.continuous_ofReal.comp_aestronglyMeasurable h_A_sq :
        AEStronglyMeasurable (fun b : M => ENNReal.ofReal (A * (rawInd b) ^ 2)) μ)
    have h_f1_aemeas : AEMeasurable f1 μ := h_f1_ae_str.aemeasurable
    have h_atom1 :
        AEStronglyMeasurable
          (fun b : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
              Real.sqrt
                (∑ k : Fin (Module.finrank ℝ E),
                  ‖(trivializationAt (TensorRSModel r s ℝ E)
                      (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt
                        ℝ b
                    (chartTensorRSCovariantDerivative (I := I) r s g α
                      (fun b' => S.toCcTensor.toSection b')
                      (chartBasisVecFiber (I := I) α k) b)‖ ^ 2))
          μ :=
      aestronglyMeasurable_pou_mul_sqrt_sum_triv_chart_cov
        (I := I) (M := M) g r s α S
    have h_rho_Tcov_sq_eq : ∀ b,
        (ρ b) ^ 2 * Tcov b =
          (((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
            Real.sqrt
              (∑ k : Fin (Module.finrank ℝ E),
                ‖(trivializationAt (TensorRSModel r s ℝ E)
                    (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt
                      ℝ b
                  (chartTensorRSCovariantDerivative (I := I) r s g α
                    (fun b' => S.toCcTensor.toSection b')
                    (chartBasisVecFiber (I := I) α k) b)‖ ^ 2)) ^ 2 := by
      intro b
      have h_sum_eq :
          (∑ k : Fin (Module.finrank ℝ E),
              ‖(trivializationAt (TensorRSModel r s ℝ E)
                  (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt
                    ℝ b
                (chartTensorRSCovariantDerivative (I := I) r s g α
                  (fun b' => S.toCcTensor.toSection b')
                  (chartBasisVecFiber (I := I) α k) b)‖ ^ 2) = Tcov b := by
        rw [hTcov_def]
      have h_eq_inside :
          Real.sqrt
              (∑ k : Fin (Module.finrank ℝ E),
                ‖(trivializationAt (TensorRSModel r s ℝ E)
                    (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt
                      ℝ b
                  (chartTensorRSCovariantDerivative (I := I) r s g α
                    (fun b' => S.toCcTensor.toSection b')
                    (chartBasisVecFiber (I := I) α k) b)‖ ^ 2) =
            Real.sqrt (Tcov b) := by
        rw [h_sum_eq]
      rw [hρ_def, h_eq_inside, mul_pow,
        show Real.sqrt (Tcov b) ^ 2 = Tcov b from Real.sq_sqrt (hTcov_nn b)]
    have h_f2_ae_str : AEStronglyMeasurable f2 μ := by
      have h_sq : AEStronglyMeasurable (fun b : M => (ρ b) ^ 2 * Tcov b) μ := by
        have hfun_eq :
            (fun b : M => (ρ b) ^ 2 * Tcov b) =
              (fun b : M =>
                (((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
                  Real.sqrt
                    (∑ k : Fin (Module.finrank ℝ E),
                      ‖(trivializationAt (TensorRSModel r s ℝ E)
                          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt
                            ℝ b
                        (chartTensorRSCovariantDerivative (I := I) r s g α
                          (fun b' => S.toCcTensor.toSection b')
                          (chartBasisVecFiber (I := I) α k) b)‖ ^ 2)) ^ 2) := by
          funext b; exact h_rho_Tcov_sq_eq b
        rw [hfun_eq]
        exact (continuous_pow 2).comp_aestronglyMeasurable h_atom1
      have h_B_sq : AEStronglyMeasurable
          (fun b : M => B * ((ρ b) ^ 2 * Tcov b)) μ := h_sq.const_mul B
      have hrearr : (fun b : M => B * ((ρ b) ^ 2 * Tcov b)) =
          (fun b : M => B * (ρ b) ^ 2 * Tcov b) := by
        funext b; ring
      rw [hrearr] at h_B_sq
      exact ENNReal.continuous_ofReal.comp_aestronglyMeasurable h_B_sq
    have h_f2_aemeas : AEMeasurable f2 μ := h_f2_ae_str.aemeasurable
    have h_split12 :
        ∫⁻ b, f1 b + f2 b + f3 b ∂μ =
          ∫⁻ b, f1 b ∂μ + ∫⁻ b, f2 b + f3 b ∂μ := by
      have hg_eq :
          (fun b : M => f1 b + f2 b + f3 b) =
            (fun b : M => f1 b + (f2 b + f3 b)) := by
        funext b; rw [add_assoc]
      rw [show (∫⁻ b, f1 b + f2 b + f3 b ∂μ) =
          ∫⁻ b, f1 b + (f2 b + f3 b) ∂μ from by rw [hg_eq]]
      exact lintegral_add_left' h_f1_aemeas _
    have h_split23 :
        ∫⁻ b, f2 b + f3 b ∂μ = ∫⁻ b, f2 b ∂μ + ∫⁻ b, f3 b ∂μ :=
      lintegral_add_left' h_f2_aemeas _
    rw [h_split12, h_split23]
    have h_G4_S : eLpNorm rawInd 2 μ ≤ ENNReal.ofReal C₄ * (‖S‖₊ : ℝ≥0∞) := by
      have := h_G4 S Idx Jdx
      have h_fun_eq :
          (fun b : M =>
            (tsupport (fun x : M =>
                ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)).indicator
              (fun b' : M =>
                scalarOnE (I := I) α
                  (tensorChartComponentRaw (I := I) (M := M)
                    g r s S.toCcTensor α Idx Jdx)
                  (extChartAt I α b')) b) = rawInd := by
        funext b; rfl
      rw [h_fun_eq] at this
      exact this
    have h_f1_int : ∫⁻ b, f1 b ∂μ ≤ ENNReal.ofReal (A * C₄ ^ 2 * ‖S‖ ^ 2) := by
      have h_f1_eq :
          ∀ b, f1 b = ENNReal.ofReal A * (‖rawInd b‖ₑ : ℝ≥0∞) ^ 2 := by
        intro b
        have h_enn_sq : (‖rawInd b‖ₑ : ℝ≥0∞) ^ 2 =
            ENNReal.ofReal ((rawInd b) ^ 2) := by
          rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
        change ENNReal.ofReal (A * (rawInd b) ^ 2) =
          ENNReal.ofReal A * (‖rawInd b‖ₑ : ℝ≥0∞) ^ 2
        rw [h_enn_sq, ENNReal.ofReal_mul hA_nn]
      have h_int_eq :
          ∫⁻ b, f1 b ∂μ =
            ENNReal.ofReal A * ∫⁻ b, (‖rawInd b‖ₑ : ℝ≥0∞) ^ 2 ∂μ := by
        rw [show (∫⁻ b, f1 b ∂μ) =
            ∫⁻ b, ENNReal.ofReal A * (‖rawInd b‖ₑ : ℝ≥0∞) ^ 2 ∂μ from by
          refine lintegral_congr ?_; intro b; exact h_f1_eq b]
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      have h_G4_sq : (eLpNorm rawInd 2 μ) ^ 2 ≤
          ENNReal.ofReal (C₄ ^ 2 * ‖S‖ ^ 2) := by
        have h_pow_mono := pow_le_pow_left' h_G4_S 2
        have h_pow_rhs :
            (ENNReal.ofReal C₄ * (‖S‖₊ : ℝ≥0∞)) ^ 2 =
              ENNReal.ofReal (C₄ ^ 2 * ‖S‖ ^ 2) := by
          rw [mul_pow, ← ENNReal.ofReal_pow hC₄_nn,
            show ((‖S‖₊ : ℝ≥0∞)) ^ 2 = ENNReal.ofReal (‖S‖ ^ 2) from by
              rw [show ((‖S‖₊ : ℝ≥0∞)) = ENNReal.ofReal ‖S‖ from
                  coe_nnnorm_eq_ofReal_norm S,
                ← ENNReal.ofReal_pow (norm_nonneg _)],
            ← ENNReal.ofReal_mul (by positivity)]
        rw [h_pow_rhs] at h_pow_mono
        exact h_pow_mono
      have h_G4_sq_lint :
          ∫⁻ b, (‖rawInd b‖ₑ : ℝ≥0∞) ^ 2 ∂μ ≤
            ENNReal.ofReal (C₄ ^ 2 * ‖S‖ ^ 2) := by
        rw [← sq_eLpNorm_two_eq_lintegral_enorm_sq μ rawInd]; exact h_G4_sq
      calc ∫⁻ b, f1 b ∂μ
          = ENNReal.ofReal A * ∫⁻ b, (‖rawInd b‖ₑ : ℝ≥0∞) ^ 2 ∂μ := h_int_eq
        _ ≤ ENNReal.ofReal A * ENNReal.ofReal (C₄ ^ 2 * ‖S‖ ^ 2) :=
            mul_le_mul_of_nonneg_left h_G4_sq_lint (zero_le _)
        _ = ENNReal.ofReal (A * (C₄ ^ 2 * ‖S‖ ^ 2)) :=
            (ENNReal.ofReal_mul hA_nn).symm
        _ = ENNReal.ofReal (A * C₄ ^ 2 * ‖S‖ ^ 2) := by congr 1; ring
    have h_G2_S := h_G2 S
    have h_f2_int : ∫⁻ b, f2 b ∂μ ≤ ENNReal.ofReal (B * C₂ ^ 2 * ‖S‖ ^ 2) := by
      set h2 : M → ℝ := fun b : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
          Real.sqrt
            (∑ k : Fin (Module.finrank ℝ E),
              ‖(trivializationAt (TensorRSModel r s ℝ E)
                  (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt
                    ℝ b
                (chartTensorRSCovariantDerivative (I := I) r s g α
                  (fun b' => S.toCcTensor.toSection b')
                  (chartBasisVecFiber (I := I) α k) b)‖ ^ 2)
        with hh2_def
      have h_f2_eq :
          ∀ b, f2 b = ENNReal.ofReal B * (‖h2 b‖ₑ : ℝ≥0∞) ^ 2 := by
        intro b
        have h_rho_Tcov : (ρ b) ^ 2 * Tcov b = (h2 b) ^ 2 := h_rho_Tcov_sq_eq b
        have h_enn_sq : (‖h2 b‖ₑ : ℝ≥0∞) ^ 2 =
            ENNReal.ofReal ((h2 b) ^ 2) := by
          rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
        change ENNReal.ofReal (B * (ρ b) ^ 2 * Tcov b) =
          ENNReal.ofReal B * (‖h2 b‖ₑ : ℝ≥0∞) ^ 2
        rw [h_enn_sq, show B * (ρ b) ^ 2 * Tcov b = B * ((ρ b) ^ 2 * Tcov b)
          from by ring, h_rho_Tcov, ENNReal.ofReal_mul hB_nn]
      have h_int_eq :
          ∫⁻ b, f2 b ∂μ =
            ENNReal.ofReal B * ∫⁻ b, (‖h2 b‖ₑ : ℝ≥0∞) ^ 2 ∂μ := by
        rw [show (∫⁻ b, f2 b ∂μ) =
            ∫⁻ b, ENNReal.ofReal B * (‖h2 b‖ₑ : ℝ≥0∞) ^ 2 ∂μ from by
          refine lintegral_congr ?_; intro b; exact h_f2_eq b]
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      have h_G2_sq : (eLpNorm h2 2 μ) ^ 2 ≤
          ENNReal.ofReal (C₂ ^ 2 * ‖S‖ ^ 2) := by
        have h_pow_mono := pow_le_pow_left' h_G2_S 2
        have h_pow_rhs :
            (ENNReal.ofReal C₂ * (‖S‖₊ : ℝ≥0∞)) ^ 2 =
              ENNReal.ofReal (C₂ ^ 2 * ‖S‖ ^ 2) := by
          rw [mul_pow, ← ENNReal.ofReal_pow hC₂_nn,
            show ((‖S‖₊ : ℝ≥0∞)) ^ 2 = ENNReal.ofReal (‖S‖ ^ 2) from by
              rw [show ((‖S‖₊ : ℝ≥0∞)) = ENNReal.ofReal ‖S‖ from
                  coe_nnnorm_eq_ofReal_norm S,
                ← ENNReal.ofReal_pow (norm_nonneg _)],
            ← ENNReal.ofReal_mul (by positivity)]
        rw [h_pow_rhs] at h_pow_mono
        exact h_pow_mono
      have h_G2_sq_lint :
          ∫⁻ b, (‖h2 b‖ₑ : ℝ≥0∞) ^ 2 ∂μ ≤
            ENNReal.ofReal (C₂ ^ 2 * ‖S‖ ^ 2) := by
        rw [← sq_eLpNorm_two_eq_lintegral_enorm_sq μ h2]; exact h_G2_sq
      calc ∫⁻ b, f2 b ∂μ
          = ENNReal.ofReal B * ∫⁻ b, (‖h2 b‖ₑ : ℝ≥0∞) ^ 2 ∂μ := h_int_eq
        _ ≤ ENNReal.ofReal B * ENNReal.ofReal (C₂ ^ 2 * ‖S‖ ^ 2) :=
            mul_le_mul_of_nonneg_left h_G2_sq_lint (zero_le _)
        _ = ENNReal.ofReal (B * (C₂ ^ 2 * ‖S‖ ^ 2)) :=
            (ENNReal.ofReal_mul hB_nn).symm
        _ = ENNReal.ofReal (B * C₂ ^ 2 * ‖S‖ ^ 2) := by congr 1; ring
    have h_f3_int : ∫⁻ b, f3 b ∂μ ≤ ENNReal.ofReal (C₃ * ‖S‖ ^ 2) := by
      set TIP : M → ℝ := fun b : M =>
        tensorInnerPointwise (I := I) (M := M) g r s b
          (S.toCcTensor.toFun b) (S.toCcTensor.toFun b) with hTIP_def
      have hTIP_nn : ∀ b, 0 ≤ TIP b := fun b =>
        tensorInnerPointwise_nonneg (I := I) (M := M) g r s b _
      have h_pt_f3 : ∀ b, B * (ρ b) ^ 2 * Tchr b ≤ C₃ * TIP b := by
        intro b
        by_cases hb : b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)
        · have h_rho_le_one : ρ b ≤ 1 := by
            rw [hρ_def]; exact (chartAtlasPOU I M).le_one α b
          have h_rho_nn_b : 0 ≤ ρ b := hρ_nn b
          have h_rho_sq_le_one : (ρ b) ^ 2 ≤ 1 := by
            rw [sq]
            calc ρ b * ρ b ≤ 1 * 1 :=
                  mul_le_mul h_rho_le_one h_rho_le_one h_rho_nn_b zero_le_one
              _ = 1 := by ring
          have h_Tchr_TIP_b : Tchr b ≤ Cchr * TIP b := by
            rw [hTchr_def, hTIP_def]; exact h_Tchr_TIP S.toCcTensor hb
          have h_Tchr_nn_b : 0 ≤ Tchr b := hTchr_nn b
          have h_B_rho_sq_le : B * (ρ b) ^ 2 ≤ B := by
            have : B * (ρ b) ^ 2 ≤ B * 1 :=
              mul_le_mul_of_nonneg_left h_rho_sq_le_one hB_nn
            linarith
          calc B * (ρ b) ^ 2 * Tchr b
              ≤ B * Tchr b := mul_le_mul_of_nonneg_right h_B_rho_sq_le h_Tchr_nn_b
            _ ≤ B * (Cchr * TIP b) := mul_le_mul_of_nonneg_left h_Tchr_TIP_b hB_nn
            _ = C₃ * TIP b := by rw [hC₃_def]; ring
        · have h_ρ_zero : ρ b = 0 := by
            by_contra hne; exact hb (subset_tsupport _ hne)
          have hRHS_nn : 0 ≤ C₃ * TIP b := mul_nonneg hC₃_nn (hTIP_nn b)
          rw [h_ρ_zero]; simpa using hRHS_nn
      have h_pt_enn3 : ∀ b, f3 b ≤ ENNReal.ofReal (C₃ * TIP b) := by
        intro b
        rw [hf3_def]
        exact ENNReal.ofReal_le_ofReal (h_pt_f3 b)
      have h_mono : ∫⁻ b, f3 b ∂μ ≤ ∫⁻ b, ENNReal.ofReal (C₃ * TIP b) ∂μ :=
        lintegral_mono h_pt_enn3
      have h_TIP_int : Integrable TIP μ := by
        rw [hμ_def, hTIP_def]
        exact SmoothCcTensor.integrable_inner_cross (I := I) (M := M)
          S.toCcTensor S.toCcTensor
      have h_CTIP_int : Integrable (fun b => C₃ * TIP b) μ := h_TIP_int.const_mul C₃
      have h_CTIP_ae_nn : 0 ≤ᵐ[μ] (fun b => C₃ * TIP b) :=
        Filter.Eventually.of_forall (fun b => mul_nonneg hC₃_nn (hTIP_nn b))
      have h_lint_to_int :
          ∫⁻ b, ENNReal.ofReal (C₃ * TIP b) ∂μ =
            ENNReal.ofReal (∫ b, C₃ * TIP b ∂μ) :=
        (MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_CTIP_int h_CTIP_ae_nn).symm
      have h_int_TIP_le : ∫ b, TIP b ∂μ ≤ ‖S‖ ^ 2 := by
        have h_l2_eq : ∫ b, TIP b ∂μ = ‖S.toCcTensor‖ ^ 2 := by
          rw [hTIP_def, hμ_def]
          have h_eq : ∫ b,
              tensorInnerPointwise (I := I) (M := M) g r s b
                (S.toCcTensor.toFun b) (S.toCcTensor.toFun b)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
            tensorL2Inner (I := I) (M := M) g r s
              S.toCcTensor.toFun S.toCcTensor.toFun := rfl
          rw [h_eq, ← SmoothCcTensor.norm_sq_eq_inner_self
            (I := I) (M := M) S.toCcTensor]
        rw [h_l2_eq]
        exact SmoothCcTensorH1.l2NormSq_le_h1NormSq S
      have h_int_CTIP_le : ∫ b, C₃ * TIP b ∂μ ≤ C₃ * ‖S‖ ^ 2 := by
        rw [integral_const_mul]
        exact mul_le_mul_of_nonneg_left h_int_TIP_le hC₃_nn
      calc ∫⁻ b, f3 b ∂μ
          ≤ ∫⁻ b, ENNReal.ofReal (C₃ * TIP b) ∂μ := h_mono
        _ = ENNReal.ofReal (∫ b, C₃ * TIP b ∂μ) := h_lint_to_int
        _ ≤ ENNReal.ofReal (C₃ * ‖S‖ ^ 2) :=
            ENNReal.ofReal_le_ofReal h_int_CTIP_le
    have h_sum_le :
        ∫⁻ b, f1 b ∂μ + (∫⁻ b, f2 b ∂μ + ∫⁻ b, f3 b ∂μ) ≤
          ENNReal.ofReal (A * C₄ ^ 2 * ‖S‖ ^ 2) +
            (ENNReal.ofReal (B * C₂ ^ 2 * ‖S‖ ^ 2) +
              ENNReal.ofReal (C₃ * ‖S‖ ^ 2)) :=
      add_le_add h_f1_int (add_le_add h_f2_int h_f3_int)
    refine h_sum_le.trans ?_
    have hA_sq_nn : 0 ≤ A * C₄ ^ 2 * ‖S‖ ^ 2 :=
      mul_nonneg (mul_nonneg hA_nn (sq_nonneg _)) (sq_nonneg _)
    have hB_sq_nn : 0 ≤ B * C₂ ^ 2 * ‖S‖ ^ 2 :=
      mul_nonneg (mul_nonneg hB_nn (sq_nonneg _)) (sq_nonneg _)
    have hC3_sq_nn : 0 ≤ C₃ * ‖S‖ ^ 2 := mul_nonneg hC₃_nn (sq_nonneg _)
    rw [← ENNReal.ofReal_add hB_sq_nn hC3_sq_nn,
      ← ENNReal.ofReal_add hA_sq_nn (add_nonneg hB_sq_nn hC3_sq_nn)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hC_sq_def]; exact le_of_eq (by ring)
  have h_eLpNorm_le := eLpNorm_two_le_ofReal_sqrt
    (μ := μ) (f := TinnerSqrt) (mul_nonneg hC_sq_nn (sq_nonneg _)) h_sq_bound
  refine h_eLpNorm_le.trans ?_
  have hS_nn : 0 ≤ ‖S‖ := norm_nonneg _
  have h_sqrt_fact : Real.sqrt (C_sq * ‖S‖ ^ 2) = C * ‖S‖ := by
    rw [hC_def, Real.sqrt_mul hC_sq_nn,
      show ‖S‖ ^ 2 = ‖S‖ * ‖S‖ from by ring, Real.sqrt_mul_self hS_nn]
  rw [h_sqrt_fact, ENNReal.ofReal_mul hC_nn,
    show ENNReal.ofReal ‖S‖ = (‖S‖₊ : ℝ≥0∞) from
      (coe_nnnorm_eq_ofReal_norm S).symm]

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
