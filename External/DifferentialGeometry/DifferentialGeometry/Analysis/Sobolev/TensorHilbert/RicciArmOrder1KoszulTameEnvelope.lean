import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RemainderCoeffPerOrderJetEnvelopes
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTower
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqSmoothCcUniformBound
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciLinearizationArmFields

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Tensor0SBundle ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Integral.Connection

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (ricciArmOrder1KoszulCoeff raisedKoszul)
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
theorem cometricCastG0_perOrder_l2_tameEnvelope_generic
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ l, 0 ≤ K l) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (l : ℕ),
          ‖iteratedCovGrad (I := I) g₀ 3 1 l (cometricDoubleTraceCastG0 (I := I) g₀ g₁)‖ ^ 2 ≤
            K l * (1 + ∑ j ∈ Finset.range (l + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  set Φ : SmoothCcTensor g₀ 3 1 := cometricDoubleTraceField (I := I) g₀ 1 with hΦ_def
  obtain ⟨C_base, hC_base_nn, hC_base⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_slotInsertEndoCc_zero_gInvDiffRaisedEndoField_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨K_t, hK_t_nn, hK_t⟩ :=
    antidiagonalTupleGrid_integral_ballUniform_tameWindow (I := I) (M := M) g₀ a ha_super hR
  have hSΦ_ex : ∀ i : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + i) x
        ((iteratedCovGrad (I := I) g₀ 3 1 i Φ).toSection x) ≤ K :=
    fun i => exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 3 (1 + i)
      (iteratedCovGrad (I := I) g₀ 3 1 i Φ)
  choose SΦ hSΦ_nn hSΦ using hSΦ_ex
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  set KW : ℕ → ℝ := fun q => fr ^ 2 * C_base q * K_t q with hKW_def
  have hKW_nn : ∀ q, 0 ≤ KW q := by
    intro q
    simp only [hKW_def]
    exact mul_nonneg (mul_nonneg (by positivity) (hC_base_nn q)) (hK_t_nn q)
  set KD : ℕ → ℝ := fun l => diagonalGridGrowthFactor (E := E) l *
    (∑ i' ∈ Finset.range (l + 1), SΦ i') * (∑ q ∈ Finset.range (l + 1), KW q) with hKD_def
  have hKD_nn : ∀ l, 0 ≤ KD l := by
    intro l
    simp only [hKD_def]
    exact mul_nonneg (mul_nonneg (appCcGdiag_nonneg _)
      (Finset.sum_nonneg (fun i' _ => hSΦ_nn i'))) (Finset.sum_nonneg (fun q _ => hKW_nn q))
  set aL : ℕ → ℝ := fun l => ‖iteratedCovGrad (I := I) g₀ 3 1 l Φ‖ ^ 2 with haL_def
  have haL_nn : ∀ l, 0 ≤ aL l := by
    intro l; simp only [haL_def]; positivity
  refine ⟨fun l => 2 * aL l + 2 * KD l,
    fun l => by linarith [haL_nn l, hKD_nn l], ?_⟩
  intro g₁ P δ hδ_le hδ htie hPball l
  have hwin_nn : 0 ≤ ∑ j ∈ Finset.range (l + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  by_cases hMne : Nonempty M
  · obtain ⟨x₀⟩ := hMne
    have hδ0 : 0 ≤ δ := by
      obtain ⟨v, hv⟩ : ∃ v : TangentSpace I x₀, v ≠ 0 := by
        haveI : Nontrivial (TangentSpace I x₀) := by
          have hfr' : 0 < Module.finrank ℝ (TangentSpace I x₀) := by
            have heq : Module.finrank ℝ (TangentSpace I x₀) = Module.finrank ℝ E := rfl
            rw [heq]; exact Nat.pos_of_ne_zero (NeZero.ne _)
          exact Module.nontrivial_of_finrank_pos hfr'
        exact exists_ne 0
      have hpos : 0 < g₀.inner x₀ v v := g₀.pos x₀ v hv
      have hbound := hδ x₀ v v
      have hsqrt_pos : 0 < Real.sqrt (g₀.inner x₀ v v) := Real.sqrt_pos.mpr hpos
      have habs_nn : 0 ≤ |ccTensorBilinSymm (I := I) g₀ P x₀ v v| := abs_nonneg _
      by_contra hδc
      have hδc' : δ < 0 := lt_of_not_ge hδc
      have hrhs_neg : δ * Real.sqrt (g₀.inner x₀ v v) * Real.sqrt (g₀.inner x₀ v v) < 0 := by
        have h1 : δ * Real.sqrt (g₀.inner x₀ v v) < 0 := mul_neg_of_neg_of_pos hδc' hsqrt_pos
        exact mul_neg_of_neg_of_pos h1 hsqrt_pos
      linarith [le_trans habs_nn hbound]
    set W : SmoothCcTensor g₀ 3 3 :=
      endoSlotZeroCcTensor (I := I) (M := M) g₀ 2 (gInvDiffRaisedEndoField (I := I) g₀ g₁)
      with hW_def
    have hid : cometricDoubleTraceCastG0 (I := I) g₀ g₁ =
        Φ + ccOperatorFieldComp (I := I) (M := M) g₀ 3 3 1 Φ W := by
      have h := cometricCastG0_eq_doubleTrace_add_appCcRS (I := I) g₀ g₁
      rw [← hΦ_def, ← hW_def] at h
      exact h
    have hstep2 : ∀ q : ℕ,
        ‖iteratedCovGrad (I := I) g₀ 3 3 q W‖ ^ 2 ≤
          KW q * (1 + ∑ j ∈ Finset.range (q + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
      intro q
      obtain ⟨hgi, hgb⟩ := hK_t P hPball q
      have hpt : ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + q) x
              ((iteratedCovGrad (I := I) g₀ 3 3 q W).toSection x) ≤
            fr ^ 2 * C_base q *
              (∑ n ∈ Finset.range (q + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n q,
                ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) := by
        intro x
        have h1 := rfns_iteratedCovGrad_slotInsertEndoCc_le_endo (I := I) g₀ 2
          (gInvDiffRaisedEndoField (I := I) g₀ g₁) q x
        rw [← hW_def, ← hfr_def] at h1
        have h2 := hC_base g₁ P htie hδ_le hδ0 hδ q x
        calc riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + q) x
              ((iteratedCovGrad (I := I) g₀ 3 3 q W).toSection x)
            ≤ fr ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + q) x
                ((iteratedCovGrad (I := I) g₀ 1 1 q
                  (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
                    (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x) := h1
          _ ≤ fr ^ 2 * (C_base q *
                (∑ n ∈ Finset.range (q + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n q,
                  ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))) :=
              mul_le_mul_of_nonneg_left h2 (sq_nonneg fr)
          _ = fr ^ 2 * C_base q *
                (∑ n ∈ Finset.range (q + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n q,
                  ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) := by ring
      have hint : MeasureTheory.Integrable
          (fun x => fr ^ 2 * C_base q *
            (∑ n ∈ Finset.range (q + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n q,
              ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)))
          (riemannianVolumeMeasure (I := I) (M := M) g₀) := hgi.const_mul _
      have hkey := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 3 (3 + q)
        (iteratedCovGrad (I := I) g₀ 3 3 q W) _ hint hpt
      refine le_trans hkey ?_
      rw [MeasureTheory.integral_const_mul]
      calc fr ^ 2 * C_base q *
              (∫ x, ∑ n ∈ Finset.range (q + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n q,
                ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
                ∂(riemannianVolumeMeasure (I := I) (M := M) g₀))
          ≤ fr ^ 2 * C_base q * (K_t q * (1 + ∑ j ∈ Finset.range (q + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)) :=
            mul_le_mul_of_nonneg_left hgb
              (mul_nonneg (by positivity) (hC_base_nn q))
        _ = KW q * (1 + ∑ j ∈ Finset.range (q + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
            simp only [hKW_def]; ring
    have hstep3 :
        ‖iteratedCovGrad (I := I) g₀ 3 1 l (ccOperatorFieldComp (I := I) (M := M) g₀ 3 3 1 Φ W)‖ ^ 2 ≤
          KD l * (1 + ∑ j ∈ Finset.range (l + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
      have hpt : ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + l) x
              ((iteratedCovGrad (I := I) g₀ 3 1 l
                (ccOperatorFieldComp (I := I) (M := M) g₀ 3 3 1 Φ W)).toSection x) ≤
            (diagonalGridGrowthFactor (E := E) l * (∑ i' ∈ Finset.range (l + 1), SΦ i')) *
              (∑ q ∈ Finset.range (l + 1),
                riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + q) x
                  ((iteratedCovGrad (I := I) g₀ 3 3 q W).toSection x)) := by
        intro x
        refine le_trans (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le
          (I := I) (M := M) g₀ l 3 3 1 Φ W x) ?_
        rw [mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg _)
        rw [Finset.sum_mul]
        refine Finset.sum_le_sum (fun i' _ => ?_)
        refine mul_le_mul (hSΦ i' x) ?_
          (Finset.sum_nonneg (fun q _ => riemannianFiberNormSq_nonneg _ _ _ _ _)) (hSΦ_nn i')
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_
          (fun q _ _ => riemannianFiberNormSq_nonneg _ _ _ _ _)
        intro q hq
        rw [Finset.mem_range] at hq ⊢
        omega
      have hint : MeasureTheory.Integrable
          (fun x => (diagonalGridGrowthFactor (E := E) l * (∑ i' ∈ Finset.range (l + 1), SΦ i')) *
            (∑ q ∈ Finset.range (l + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + q) x
                ((iteratedCovGrad (I := I) g₀ 3 3 q W).toSection x)))
          (riemannianVolumeMeasure (I := I) (M := M) g₀) := by
        apply MeasureTheory.Integrable.const_mul
        apply MeasureTheory.integrable_finset_sum
        intro q _
        exact integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 3 (3 + q)
          (iteratedCovGrad (I := I) g₀ 3 3 q W)
      have hkey := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 3 (1 + l)
        (iteratedCovGrad (I := I) g₀ 3 1 l (ccOperatorFieldComp (I := I) (M := M) g₀ 3 3 1 Φ W)) _ hint hpt
      refine le_trans hkey ?_
      rw [MeasureTheory.integral_const_mul,
        MeasureTheory.integral_finset_sum _ (fun q _ =>
          integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 3 (3 + q)
            (iteratedCovGrad (I := I) g₀ 3 3 q W))]
      have hconv : ∀ q ∈ Finset.range (l + 1),
          (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + q) x
              ((iteratedCovGrad (I := I) g₀ 3 3 q W).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) =
          ‖iteratedCovGrad (I := I) g₀ 3 3 q W‖ ^ 2 := by
        intro q _
        rw [SmoothCcTensor.norm_def,
          tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g₀ 3 (3 + q)
            (iteratedCovGrad (I := I) g₀ 3 3 q W)]
      rw [Finset.sum_congr rfl hconv]
      have hWsum : ∑ q ∈ Finset.range (l + 1), ‖iteratedCovGrad (I := I) g₀ 3 3 q W‖ ^ 2 ≤
          (∑ q ∈ Finset.range (l + 1), KW q) *
            (1 + ∑ j ∈ Finset.range (l + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
        rw [Finset.sum_mul]
        refine Finset.sum_le_sum (fun q hq => ?_)
        refine le_trans (hstep2 q) ?_
        refine mul_le_mul_of_nonneg_left ?_ (hKW_nn q)
        have hsub : ∑ j ∈ Finset.range (q + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 ≤
            ∑ j ∈ Finset.range (l + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 := by
          refine Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.range_mono ?_) (fun j _ _ => sq_nonneg _)
          rw [Finset.mem_range] at hq
          omega
        linarith
      calc (diagonalGridGrowthFactor (E := E) l * (∑ i' ∈ Finset.range (l + 1), SΦ i')) *
              (∑ q ∈ Finset.range (l + 1), ‖iteratedCovGrad (I := I) g₀ 3 3 q W‖ ^ 2)
          ≤ (diagonalGridGrowthFactor (E := E) l * (∑ i' ∈ Finset.range (l + 1), SΦ i')) *
              ((∑ q ∈ Finset.range (l + 1), KW q) *
                (1 + ∑ j ∈ Finset.range (l + 1),
                  ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)) :=
            mul_le_mul_of_nonneg_left hWsum
              (mul_nonneg (appCcGdiag_nonneg _) (Finset.sum_nonneg (fun i' _ => hSΦ_nn i')))
        _ = KD l * (1 + ∑ j ∈ Finset.range (l + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
            simp only [hKD_def]; ring
    rw [hid, iteratedCovGrad_add (I := I) g₀ 3 1 l Φ (ccOperatorFieldComp (I := I) (M := M) g₀ 3 3 1 Φ W)]
    have haLl : ‖iteratedCovGrad (I := I) g₀ 3 1 l Φ‖ ^ 2 ≤
        aL l * (1 + ∑ j ∈ Finset.range (l + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
      have h1 : aL l = ‖iteratedCovGrad (I := I) g₀ 3 1 l Φ‖ ^ 2 := by simp only [haL_def]
      nlinarith [haL_nn l, hwin_nn]
    have hsq := pow_le_pow_left₀ (norm_nonneg (iteratedCovGrad (I := I) g₀ 3 1 l Φ +
        iteratedCovGrad (I := I) g₀ 3 1 l (ccOperatorFieldComp (I := I) (M := M) g₀ 3 3 1 Φ W)))
      (norm_add_le (iteratedCovGrad (I := I) g₀ 3 1 l Φ)
        (iteratedCovGrad (I := I) g₀ 3 1 l (ccOperatorFieldComp (I := I) (M := M) g₀ 3 3 1 Φ W))) 2
    nlinarith [hsq, hstep3, haLl,
      sq_nonneg (‖iteratedCovGrad (I := I) g₀ 3 1 l Φ‖ -
        ‖iteratedCovGrad (I := I) g₀ 3 1 l (ccOperatorFieldComp (I := I) (M := M) g₀ 3 3 1 Φ W)‖)]
  · haveI hem : IsEmpty M := not_nonempty_iff.mp hMne
    have hz : ‖iteratedCovGrad (I := I) g₀ 3 1 l (cometricDoubleTraceCastG0 (I := I) g₀ g₁)‖ = 0 := by
      rw [SmoothCcTensor.norm_def, tensorL2Norm_def, tensorL2Inner,
        MeasureTheory.integral_of_isEmpty, Real.sqrt_zero]
    rw [hz]
    have hnn : 0 ≤ 2 * aL l + 2 * KD l := by linarith [haL_nn l, hKD_nn l]
    nlinarith [hwin_nn, hnn]

theorem ricciArmOrder1KoszulCoeff_perOrder_l2_tameEnvelope_generic
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ),
          ‖iteratedCovGrad (I := I) g₀ 3 2 i
              (ricciArmOrder1KoszulCoeff (I := I) (M := M) g₀ g₁)‖ ^ 2 ≤
            K i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  obtain ⟨ΛA, FΦ, hΛA, hFΦ_nn, hΦfeed⟩ :=
    raisedKoszul_order0sup_jetL2_ballUniform_generic (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨ΛB, FW, hΛB, hFW_nn, hWfeed⟩ :=
    cometricDoubleTraceField_order0sup_jetL2_ballUniform_generic
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨KC, hKC_nn, hKC⟩ :=
    cometricCastG0_perOrder_l2_tameEnvelope_generic (I := I) (M := M) g₀ a ha_super hR hδ₀
  refine ⟨fun i => diagonalGridGrowthFactor (E := E) i *
      (exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le
        (I := I) (M := M) g₀ 1 3 2 1 i).choose *
      (ΛB ^ 2 * 10 + ΛA ^ 2 * ∑ l ∈ Finset.range (i + 1), KC l),
    fun i => by
      refine mul_nonneg (mul_nonneg (appCcGdiag_nonneg (E := E) i)
        (exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le
          (I := I) (M := M) g₀ 1 3 2 1 i).choose_spec.1) (add_nonneg ?_ ?_)
      · exact mul_nonneg (sq_nonneg _) (by norm_num)
      · exact mul_nonneg (sq_nonneg _)
          (Finset.sum_nonneg (fun l _ => hKC_nn l)), ?_⟩
  intro g₁ P δ hδ_le hδ htie hPball i
  obtain ⟨hΦsup, hΦsum⟩ := hΦfeed g₁ P hδ_le hδ htie hPball
  obtain ⟨hWsup, hWsum⟩ := hWfeed g₁ P hδ_le hδ htie hPball
  obtain ⟨hgrid_int, hgrid_bound⟩ :=
    (exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le
      (I := I) (M := M) g₀ 1 3 2 1 i).choose_spec.2
      (raisedKoszul (I := I) g₀ g₁) (cometricDoubleTraceCastG0 (I := I) g₀ g₁) ΛA ΛB hΛA hΛB hΦsup hWsup
  rw [ricciArmOrder1KoszulCoeff_eq_raisedKoszul_contract_cometricDoubleTraceCastG0 (I := I) (M := M) g₀ g₁]
  have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 3 (2 + i)
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (ccOperatorFieldComp (I := I) (M := M) g₀ 3 1 2 (raisedKoszul (I := I) g₀ g₁)
        (cometricDoubleTraceCastG0 (I := I) g₀ g₁)))
    (fun x => diagonalGridGrowthFactor (E := E) i *
      ∑ n ∈ Finset.range (i + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
            ((iteratedCovGrad (I := I) g₀ 1 2 n (raisedKoszul (I := I) g₀ g₁)).toSection x)
          * ∑ l ∈ Finset.range (i + 1 - n),
              riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + l) x
                ((iteratedCovGrad (I := I) g₀ 3 1 l (cometricDoubleTraceCastG0 (I := I) g₀ g₁)).toSection x))
    (hgrid_int.const_mul (diagonalGridGrowthFactor (E := E) i))
    (fun x => riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le (I := I) (M := M) g₀
      i 3 1 2 (raisedKoszul (I := I) g₀ g₁) (cometricDoubleTraceCastG0 (I := I) g₀ g₁) x)
  refine le_trans key ?_
  rw [MeasureTheory.integral_const_mul]
  have hAnn : (0 : ℝ) ≤ diagonalGridGrowthFactor (E := E) i := appCcGdiag_nonneg (E := E) i
  have hCnn : (0 : ℝ) ≤ (exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le
      (I := I) (M := M) g₀ 1 3 2 1 i).choose :=
    (exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le
      (I := I) (M := M) g₀ 1 3 2 1 i).choose_spec.1
  have hwin2_nn : 0 ≤ ∑ j ∈ Finset.range (i + 2),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hSa : ∑ n ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 1 2 n (raisedKoszul (I := I) g₀ g₁)‖ ^ 2 ≤
      10 * (1 + ∑ j ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
    have h1 : ∑ n ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 1 2 n (raisedKoszul (I := I) g₀ g₁)‖ ^ 2 ≤
        ∑ n ∈ Finset.range (i + 1),
          10 * ‖iteratedCovGrad (I := I) g₀ 0 2 (n + 1) P‖ ^ 2 :=
      Finset.sum_le_sum (fun n _ =>
        raisedKoszul_perOrder_l2_le_iteratedCovGrad_succ (I := I) (M := M) g₀ g₁ P htie n)
    have h2 : ∑ n ∈ Finset.range (i + 1),
          10 * ‖iteratedCovGrad (I := I) g₀ 0 2 (n + 1) P‖ ^ 2 =
        10 * ∑ n ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 (n + 1) P‖ ^ 2 := by
      rw [Finset.mul_sum]
    have h3 := Finset.sum_range_succ'
      (fun j => ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) (i + 1)
    have h4 : ∑ n ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 (n + 1) P‖ ^ 2 ≤
        ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 := by
      rw [h3]
      have := sq_nonneg ‖iteratedCovGrad (I := I) g₀ 0 2 0 P‖
      linarith
    calc ∑ n ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 1 2 n (raisedKoszul (I := I) g₀ g₁)‖ ^ 2
        ≤ 10 * ∑ n ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 (n + 1) P‖ ^ 2 := by rw [← h2]; exact h1
      _ ≤ 10 * ∑ j ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 := by linarith
      _ ≤ 10 * (1 + ∑ j ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by linarith
  have hSc : ∑ l ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 3 1 l (cometricDoubleTraceCastG0 (I := I) g₀ g₁)‖ ^ 2 ≤
      (∑ l ∈ Finset.range (i + 1), KC l) *
        (1 + ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun l hl => ?_)
    refine le_trans (hKC g₁ P hδ_le hδ htie hPball l) ?_
    refine mul_le_mul_of_nonneg_left ?_ (hKC_nn l)
    have hsub : ∑ j ∈ Finset.range (l + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 ≤
        ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 := by
      refine Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono ?_) (fun j _ _ => sq_nonneg _)
      rw [Finset.mem_range] at hl
      omega
    linarith
  calc diagonalGridGrowthFactor (E := E) i * ∫ x,
          (∑ n ∈ Finset.range (i + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
                ((iteratedCovGrad (I := I) g₀ 1 2 n (raisedKoszul (I := I) g₀ g₁)).toSection x)
              * ∑ l ∈ Finset.range (i + 1 - n),
                  riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + l) x
                    ((iteratedCovGrad (I := I) g₀ 3 1 l
                      (cometricDoubleTraceCastG0 (I := I) g₀ g₁)).toSection x))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)
      ≤ diagonalGridGrowthFactor (E := E) i *
          ((exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le
            (I := I) (M := M) g₀ 1 3 2 1 i).choose *
            (ΛB ^ 2 * ∑ n ∈ Finset.range (i + 1),
                ‖iteratedCovGrad (I := I) g₀ 1 2 n (raisedKoszul (I := I) g₀ g₁)‖ ^ 2
              + ΛA ^ 2 * ∑ l ∈ Finset.range (i + 1),
                ‖iteratedCovGrad (I := I) g₀ 3 1 l (cometricDoubleTraceCastG0 (I := I) g₀ g₁)‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hgrid_bound hAnn
    _ ≤ diagonalGridGrowthFactor (E := E) i *
          ((exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le
            (I := I) (M := M) g₀ 1 3 2 1 i).choose *
            ((ΛB ^ 2 * 10 + ΛA ^ 2 * ∑ l ∈ Finset.range (i + 1), KC l) *
              (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hCnn) hAnn
        have h1 := mul_le_mul_of_nonneg_left hSa (sq_nonneg ΛB)
        have h2 := mul_le_mul_of_nonneg_left hSc (sq_nonneg ΛA)
        nlinarith [h1, h2]
    _ = diagonalGridGrowthFactor (E := E) i *
          (exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le
            (I := I) (M := M) g₀ 1 3 2 1 i).choose *
          (ΛB ^ 2 * 10 + ΛA ^ 2 * ∑ l ∈ Finset.range (i + 1), KC l) *
          (1 + ∑ j ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
        ring

end DifferentialGeometry.Integral.Connection

end
