import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RemainderCoeffPerOrderJetEnvelopes
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTower
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciThreeArmAppCc

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Tensor0SBundle ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Integral.Connection

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (ricciArmOrder1KoszulCoeff raisedKoszul)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
private lemma arm1NormSq_eq_integral (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (C : SmoothCcTensor g r s) :
    ‖C‖ ^ 2 = ∫ x, riemannianFiberNormSq (I := I) (M := M) g r s x (C.toSection x)
      ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  rw [SmoothCcTensor.norm_def (I := I) (M := M) C,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g r s C]

private lemma riemannianFiberNormSq_iteratedCovGrad_cometricCastG0_gridWindow_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Kw : ℕ → ℝ, (∀ l, 0 ≤ Kw l) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        (l : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + l) x
            ((iteratedCovGrad (I := I) g₀ 3 1 l (cometricDoubleTraceCastG0 (I := I) g₀ g₁)).toSection x) ≤
          Kw l * Combinatorics.boundedFactorGridWindow
            (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
              ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) l (l + 1) := by
  classical
  set Φ : SmoothCcTensor g₀ 3 1 :=
    DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.cometricDoubleTraceField
      (I := I) g₀ 1 with hΦ_def
  have hSΦ_ex : ∀ i : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + i) x
        ((iteratedCovGrad (I := I) g₀ 3 1 i Φ).toSection x) ≤ K :=
    fun i => exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 3 (1 + i)
      (iteratedCovGrad (I := I) g₀ 3 1 i Φ)
  choose SΦ hSΦ_nn hSΦ using hSΦ_ex
  obtain ⟨C, hC_nn, hC⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_slotInsertEndoCc_zero_gInvDiffRaisedEndoField_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  refine ⟨fun l => 2 * SΦ l +
      2 * (diagonalGridGrowthFactor (E := E) l * (∑ i' ∈ Finset.range (l + 1), SΦ i') *
        (fr ^ 2 * ∑ q ∈ Finset.range (l + 1), C q)), ?_, ?_⟩
  · intro l
    have h1 : 0 ≤ SΦ l := hSΦ_nn l
    have h2 : 0 ≤ ∑ i' ∈ Finset.range (l + 1), SΦ i' := Finset.sum_nonneg (fun i' _ => hSΦ_nn i')
    have h3 : 0 ≤ ∑ q ∈ Finset.range (l + 1), C q := Finset.sum_nonneg (fun q _ => hC_nn q)
    have h4 : 0 ≤ diagonalGridGrowthFactor (E := E) l := appCcGdiag_nonneg (E := E) l
    positivity
  · intro g₁ P δ hδ_le hδ0 hδ htie l x
    set W : SmoothCcTensor g₀ 3 3 :=
      endoSlotZeroCcTensor (I := I) (M := M) g₀ 2 (gInvDiffRaisedEndoField (I := I) g₀ g₁)
      with hW_def
    set bP : ℕ → ℝ := fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
      ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x) with hbP_def
    have hbP_nn : ∀ j, 0 ≤ bP j :=
      fun j => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j) x _
    set BFGW : ℝ := Combinatorics.boundedFactorGridWindow bP l (l + 1) with hBFGW_def
    have hBFGW_one : (1 : ℝ) ≤ BFGW :=
      Combinatorics.one_le_boundedFactorGridWindow bP hbP_nn (by omega)
    have hBFGW_nn : 0 ≤ BFGW := le_trans zero_le_one hBFGW_one
    have hWq : ∀ q : ℕ, q ≤ l →
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + q) x
          ((iteratedCovGrad (I := I) g₀ 3 3 q W).toSection x) ≤
          fr ^ 2 * C q * Combinatorics.boundedFactorGrid bP l q := by
      intro q hq
      have h1 := rfns_iteratedCovGrad_slotInsertEndoCc_le_endo (I := I) g₀ 2
        (gInvDiffRaisedEndoField (I := I) g₀ g₁) q x
      rw [← hW_def, ← hfr_def] at h1
      have h2 := hC g₁ P htie hδ_le hδ0 hδ q x
      have hgrideq : (∑ n ∈ Finset.range (q + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n q,
            ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) =
          Combinatorics.antidiagonalTupleGrid bP q := rfl
      rw [hgrideq, Combinatorics.antidiagonalTupleGrid_eq_boundedFactorGrid bP hq] at h2
      calc riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + q) x
            ((iteratedCovGrad (I := I) g₀ 3 3 q W).toSection x)
          ≤ fr ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + q) x
              ((iteratedCovGrad (I := I) g₀ 1 1 q
                (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
                  (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x) := h1
        _ ≤ fr ^ 2 * (C q * Combinatorics.boundedFactorGrid bP l q) :=
            mul_le_mul_of_nonneg_left h2 (sq_nonneg fr)
        _ = fr ^ 2 * C q * Combinatorics.boundedFactorGrid bP l q := by ring
    have hid : cometricDoubleTraceCastG0 (I := I) g₀ g₁ = Φ + ccOperatorFieldComp (I := I) (M := M) g₀ 3 3 1 Φ W := by
      rw [hΦ_def, hW_def]
      exact cometricCastG0_eq_doubleTrace_add_appCcRS (I := I) g₀ g₁
    rw [hid, iteratedCovGrad_add (I := I) g₀ 3 1 l Φ (ccOperatorFieldComp (I := I) (M := M) g₀ 3 3 1 Φ W)]
    rw [show ((iteratedCovGrad (I := I) g₀ 3 1 l Φ +
          iteratedCovGrad (I := I) g₀ 3 1 l (ccOperatorFieldComp (I := I) (M := M) g₀ 3 3 1 Φ W)).toSection x) =
        (iteratedCovGrad (I := I) g₀ 3 1 l Φ).toSection x +
          (iteratedCovGrad (I := I) g₀ 3 1 l (ccOperatorFieldComp (I := I) (M := M) g₀ 3 3 1 Φ W)).toSection x
        from by rw [SmoothCcTensor.toSection_add]; rfl]
    refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 3 (1 + l) x _ _) ?_
    have hA : riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + l) x
        ((iteratedCovGrad (I := I) g₀ 3 1 l Φ).toSection x) ≤ SΦ l := hSΦ l x
    have hB : riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + l) x
        ((iteratedCovGrad (I := I) g₀ 3 1 l (ccOperatorFieldComp (I := I) (M := M) g₀ 3 3 1 Φ W)).toSection x) ≤
        (diagonalGridGrowthFactor (E := E) l * (∑ i' ∈ Finset.range (l + 1), SΦ i') *
          (fr ^ 2 * ∑ q ∈ Finset.range (l + 1), C q)) * BFGW := by
      refine le_trans (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le
        (I := I) (M := M) g₀ l 3 3 1 Φ W x) ?_
      rw [mul_assoc, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg (E := E) l)
      have hqsum : ∀ i', (∑ q ∈ Finset.range (l + 1 - i'),
            riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + q) x
              ((iteratedCovGrad (I := I) g₀ 3 3 q W).toSection x)) ≤
          (fr ^ 2 * ∑ q ∈ Finset.range (l + 1), C q) * BFGW := by
        intro i'
        calc (∑ q ∈ Finset.range (l + 1 - i'),
              riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + q) x
                ((iteratedCovGrad (I := I) g₀ 3 3 q W).toSection x))
            ≤ ∑ q ∈ Finset.range (l + 1),
                riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + q) x
                  ((iteratedCovGrad (I := I) g₀ 3 3 q W).toSection x) := by
              refine Finset.sum_le_sum_of_subset_of_nonneg
                (Finset.range_mono (by omega)) ?_
              exact fun q _ _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 3 (3 + q) x _
          _ ≤ ∑ q ∈ Finset.range (l + 1),
                fr ^ 2 * C q * Combinatorics.boundedFactorGrid bP l q := by
              refine Finset.sum_le_sum (fun q hq => ?_)
              exact hWq q (by rw [Finset.mem_range] at hq; omega)
          _ ≤ ∑ q ∈ Finset.range (l + 1), fr ^ 2 * C q * BFGW := by
              refine Finset.sum_le_sum (fun q hq => ?_)
              refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (sq_nonneg fr) (hC_nn q))
              exact Combinatorics.boundedFactorGrid_le_boundedFactorGridWindow bP hbP_nn
                (by rw [Finset.mem_range] at hq; omega)
          _ = (fr ^ 2 * ∑ q ∈ Finset.range (l + 1), C q) * BFGW := by
              rw [Finset.mul_sum, Finset.sum_mul]
      calc (∑ i' ∈ Finset.range (l + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + i') x
              ((iteratedCovGrad (I := I) g₀ 3 1 i' Φ).toSection x) *
              ∑ q ∈ Finset.range (l + 1 - i'),
                riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + q) x
                  ((iteratedCovGrad (I := I) g₀ 3 3 q W).toSection x))
          ≤ ∑ i' ∈ Finset.range (l + 1),
              SΦ i' * ((fr ^ 2 * ∑ q ∈ Finset.range (l + 1), C q) * BFGW) := by
            refine Finset.sum_le_sum (fun i' _ => ?_)
            refine mul_le_mul (hSΦ i' x) (hqsum i')
              (Finset.sum_nonneg (fun q _ =>
                riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 3 (3 + q) x _))
              (hSΦ_nn i')
        _ = (∑ i' ∈ Finset.range (l + 1), SΦ i') *
              ((fr ^ 2 * ∑ q ∈ Finset.range (l + 1), C q) * BFGW) := by
            rw [Finset.sum_mul]
    have hKw_pos_part : 0 ≤ diagonalGridGrowthFactor (E := E) l * (∑ i' ∈ Finset.range (l + 1), SΦ i') *
        (fr ^ 2 * ∑ q ∈ Finset.range (l + 1), C q) := by
      have h2 : 0 ≤ ∑ i' ∈ Finset.range (l + 1), SΦ i' :=
        Finset.sum_nonneg (fun i' _ => hSΦ_nn i')
      have h3 : 0 ≤ ∑ q ∈ Finset.range (l + 1), C q := Finset.sum_nonneg (fun q _ => hC_nn q)
      have h4 : 0 ≤ diagonalGridGrowthFactor (E := E) l := appCcGdiag_nonneg (E := E) l
      positivity
    have hSΦl_le : SΦ l ≤ SΦ l * BFGW := le_mul_of_one_le_right (hSΦ_nn l) hBFGW_one
    calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + l) x
            ((iteratedCovGrad (I := I) g₀ 3 1 l Φ).toSection x) +
          2 * riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + l) x
            ((iteratedCovGrad (I := I) g₀ 3 1 l
              (ccOperatorFieldComp (I := I) (M := M) g₀ 3 3 1 Φ W)).toSection x)
        ≤ 2 * SΦ l +
            2 * ((diagonalGridGrowthFactor (E := E) l * (∑ i' ∈ Finset.range (l + 1), SΦ i') *
              (fr ^ 2 * ∑ q ∈ Finset.range (l + 1), C q)) * BFGW) :=
          add_le_add (by linarith [hA]) (by linarith [hB])
      _ ≤ 2 * (SΦ l * BFGW) +
            2 * ((diagonalGridGrowthFactor (E := E) l * (∑ i' ∈ Finset.range (l + 1), SΦ i') *
              (fr ^ 2 * ∑ q ∈ Finset.range (l + 1), C q)) * BFGW) := by
          have := hSΦl_le; linarith
      _ = (2 * SΦ l +
            2 * (diagonalGridGrowthFactor (E := E) l * (∑ i' ∈ Finset.range (l + 1), SΦ i') *
              (fr ^ 2 * ∑ q ∈ Finset.range (l + 1), C q))) * BFGW := by ring

private lemma riemannianFiberNormSq_appCcRS_coeffLower_general_le (g : SmoothRiemannianMetric I M)
    (p a b : ℕ) (Φ : SmoothCcTensor g a b) (W : SmoothCcTensor g p a) (i : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g p (b + i) x
        ((∑ k ∈ Finset.range i,
          ccOperatorFieldComp (I := I) (M := M) g p (a + (k + 1)) (b + i)
            (appCcLeibnizPsi (I := I) (M := M) g a b Φ i (k + 1))
            (iteratedCovGrad (I := I) g p a (k + 1) W)).toSection x) ≤
      (i : ℝ) * diagonalGridGrowthFactor (E := E) i *
        ∑ k ∈ Finset.range i,
          riemannianFiberNormSq (I := I) (M := M) g a (b + (i - (k + 1))) x
              ((iteratedCovGrad (I := I) g a b (i - (k + 1)) Φ).toSection x) *
            riemannianFiberNormSq (I := I) (M := M) g p (a + (k + 1)) x
              ((iteratedCovGrad (I := I) g p a (k + 1) W).toSection x) := by
  rw [SmoothCcTensor.toSection_sum_apply]
  refine le_trans (riemannianFiberNormSq_sum_le_card_mul (I := I) (M := M) g p (b + i) x
    (Finset.range i) (fun k =>
      (ccOperatorFieldComp (I := I) (M := M) g p (a + (k + 1)) (b + i)
        (appCcLeibnizPsi (I := I) (M := M) g a b Φ i (k + 1))
        (iteratedCovGrad (I := I) g p a (k + 1) W)).toSection x)) ?_
  rw [Finset.card_range, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg i)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun k hk => ?_)
  have hk_le : k + 1 ≤ i := by simp only [Finset.mem_range] at hk; omega
  rw [appCcRS_toSection (I := I) (M := M) g p (a + (k + 1)) (b + i)
    (appCcLeibnizPsi (I := I) (M := M) g a b Φ i (k + 1))
    (iteratedCovGrad (I := I) g p a (k + 1) W) x]
  refine le_trans (riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g p (a + (k + 1))
    (b + i) x _ _) ?_
  rw [← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_
    (riemannianFiberNormSq_nonneg (I := I) (M := M) g p (a + (k + 1)) x _)
  exact rfns_iteratedCovGrad_appCcLeibnizPsi_window_le (I := I) (M := M) g a b Φ i (k + 1) 0 hk_le x

theorem ricciArmOrder1KoszulCoeff_topSeparatedResidual_jetL2_flat_leak_allOrders
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧ ∃ Kleak : ℝ, 0 ≤ Kleak ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ),
          ‖iteratedCovGrad (I := I) g₀ 3 2 i
                (ricciArmOrder1KoszulCoeff (I := I) (M := M) g₀ g₁) -
              ccOperatorFieldComp (I := I) (M := M) g₀ 3 1 (2 + i)
                (iteratedCovGrad (I := I) g₀ 1 2 i (raisedKoszul (I := I) g₀ g₁))
                (cometricDoubleTraceCastG0 (I := I) g₀ g₁)‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) +
              Kleak * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 1) P‖ ^ 2 := by
  classical
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  obtain ⟨Kw, hKw_nn, hKwbound⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_cometricCastG0_gridWindow_le (I := I) (M := M) g₀ hδ₀
  obtain ⟨Kflat, hKflat_nn, hKflat⟩ :=
    boundedFactorGridWindow_integral_ballUniform_flat_allOrders (I := I) (M := M) g₀ a ha_super hR
  refine ⟨fun i => (i : ℝ) * diagonalGridGrowthFactor (E := E) i *
      (∑ k ∈ Finset.range i, 10 * Kw (k + 1)) * Kflat (i - 1), ?_, 0, le_refl 0, ?_⟩
  · intro i
    have h1 : 0 ≤ ∑ k ∈ Finset.range i, 10 * Kw (k + 1) :=
      Finset.sum_nonneg (fun k _ => by have := hKw_nn (k + 1); linarith)
    have h2 : 0 ≤ diagonalGridGrowthFactor (E := E) i := appCcGdiag_nonneg (E := E) i
    have h3 : 0 ≤ Kflat (i - 1) := hKflat_nn (i - 1)
    positivity
  · intro g₁ P δ hδ_le hδ htie hPball i
    have hdiff : iteratedCovGrad (I := I) g₀ 3 2 i (ricciArmOrder1KoszulCoeff (I := I) (M := M) g₀ g₁) -
          ccOperatorFieldComp (I := I) (M := M) g₀ 3 1 (2 + i)
            (iteratedCovGrad (I := I) g₀ 1 2 i (raisedKoszul (I := I) g₀ g₁))
            (cometricDoubleTraceCastG0 (I := I) g₀ g₁) =
          ∑ k ∈ Finset.range i,
            ccOperatorFieldComp (I := I) (M := M) g₀ 3 (1 + (k + 1)) (2 + i)
              (appCcLeibnizPsi (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁) i (k + 1))
              (iteratedCovGrad (I := I) g₀ 3 1 (k + 1) (cometricDoubleTraceCastG0 (I := I) g₀ g₁)) := by
      have hsum : iteratedCovGrad (I := I) g₀ 3 2 i
            (ricciArmOrder1KoszulCoeff (I := I) (M := M) g₀ g₁) =
          (∑ k ∈ Finset.range i,
            ccOperatorFieldComp (I := I) (M := M) g₀ 3 (1 + (k + 1)) (2 + i)
              (appCcLeibnizPsi (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁) i (k + 1))
              (iteratedCovGrad (I := I) g₀ 3 1 (k + 1) (cometricDoubleTraceCastG0 (I := I) g₀ g₁))) +
            ccOperatorFieldComp (I := I) (M := M) g₀ 3 1 (2 + i)
              (iteratedCovGrad (I := I) g₀ 1 2 i (raisedKoszul (I := I) g₀ g₁))
              (cometricDoubleTraceCastG0 (I := I) g₀ g₁) := by
        rw [ricciArmOrder1KoszulCoeff_eq_raisedKoszul_contract_cometricDoubleTraceCastG0 (I := I) g₀ g₁,
          iteratedCovGrad_appCcRS_eq (I := I) (M := M) g₀ 3 1 2 (raisedKoszul (I := I) g₀ g₁)
            (cometricDoubleTraceCastG0 (I := I) g₀ g₁) i,
          Finset.sum_range_succ' (fun k =>
            ccOperatorFieldComp (I := I) (M := M) g₀ 3 (1 + k) (2 + i)
              (appCcLeibnizPsi (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁) i k)
              (iteratedCovGrad (I := I) g₀ 3 1 k (cometricDoubleTraceCastG0 (I := I) g₀ g₁))) i]
        congr 1
        rw [appCcLeibnizPsi_zero_right_eq (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁) i,
          iteratedCovGrad_zero (I := I) g₀ 3 1 (cometricDoubleTraceCastG0 (I := I) g₀ g₁)]
      rw [hsum]; abel
    rw [hdiff]
    by_cases hMne : Nonempty M
    · obtain ⟨x₀⟩ := hMne
      have hδ0 : 0 ≤ δ := by
        obtain ⟨v, hv⟩ : ∃ v : TangentSpace I x₀, v ≠ 0 := by
          haveI : Nontrivial (TangentSpace I x₀) := by
            have hfr : 0 < Module.finrank ℝ (TangentSpace I x₀) := by
              have heq : Module.finrank ℝ (TangentSpace I x₀) = Module.finrank ℝ E := rfl
              rw [heq]; exact Nat.pos_of_ne_zero (NeZero.ne _)
            exact Module.nontrivial_of_finrank_pos hfr
          exact exists_ne 0
        have hpos : 0 < g₀.inner x₀ v v := g₀.pos x₀ v hv
        have hbound := hδ x₀ v v
        have hsqrt_pos : 0 < Real.sqrt (g₀.inner x₀ v v) := Real.sqrt_pos.mpr hpos
        have habs_nn : 0 ≤ |ccTensorBilinSymm (I := I) g₀ P x₀ v v| := abs_nonneg _
        by_contra hδc
        have hδc' : δ < 0 := lt_of_not_ge hδc
        have hrhs_neg : δ * Real.sqrt (g₀.inner x₀ v v) * Real.sqrt (g₀.inner x₀ v v) < 0 := by
          have h1 : δ * Real.sqrt (g₀.inner x₀ v v) < 0 :=
            mul_neg_of_neg_of_pos hδc' hsqrt_pos
          exact mul_neg_of_neg_of_pos h1 hsqrt_pos
        linarith [le_trans habs_nn hbound]
      set C : ℝ := (i : ℝ) * diagonalGridGrowthFactor (E := E) i * (∑ k ∈ Finset.range i, 10 * Kw (k + 1))
        with hC_def
      have hC_nn : 0 ≤ C := by
        rw [hC_def]
        have h1 : 0 ≤ ∑ k ∈ Finset.range i, 10 * Kw (k + 1) :=
          Finset.sum_nonneg (fun k _ => by have := hKw_nn (k + 1); linarith)
        have h2 : 0 ≤ diagonalGridGrowthFactor (E := E) i := appCcGdiag_nonneg (E := E) i
        positivity
      have hpt : ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 3 (2 + i) x
              ((∑ k ∈ Finset.range i,
                ccOperatorFieldComp (I := I) (M := M) g₀ 3 (1 + (k + 1)) (2 + i)
                  (appCcLeibnizPsi (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁) i (k + 1))
                  (iteratedCovGrad (I := I) g₀ 3 1 (k + 1)
                    (cometricDoubleTraceCastG0 (I := I) g₀ g₁))).toSection x) ≤
            C * Combinatorics.boundedFactorGridWindow
              (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) i (i + 2) := by
        intro x
        set bP : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) with hbP_def
        have hbP_nn : ∀ l, 0 ≤ bP l :=
          fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
        refine le_trans (riemannianFiberNormSq_appCcRS_coeffLower_general_le (I := I) (M := M) g₀ 3 1 2
          (raisedKoszul (I := I) g₀ g₁) (cometricDoubleTraceCastG0 (I := I) g₀ g₁) i x) ?_
        have hsumcell : (∑ k ∈ Finset.range i,
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + (i - (k + 1))) x
                  ((iteratedCovGrad (I := I) g₀ 1 2 (i - (k + 1))
                    (raisedKoszul (I := I) g₀ g₁)).toSection x) *
                riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + (k + 1)) x
                  ((iteratedCovGrad (I := I) g₀ 3 1 (k + 1)
                    (cometricDoubleTraceCastG0 (I := I) g₀ g₁)).toSection x)) ≤
            (∑ k ∈ Finset.range i, 10 * Kw (k + 1)) *
              Combinatorics.boundedFactorGridWindow bP i (i + 2) := by
          rw [Finset.sum_mul]
          refine Finset.sum_le_sum (fun k hk => ?_)
          have hk1 : k + 1 ≤ i := by simp only [Finset.mem_range] at hk; omega
          have hRK := rfns_iteratedCovGrad_raisedKoszul_pointwise_le (I := I) (M := M) g₀ g₁ P htie
            (i - (k + 1)) x
          rw [show (i - (k + 1)) + 1 = i - k from by omega] at hRK
          have hCG := hKwbound g₁ P hδ_le hδ0 hδ htie (k + 1) x
          have hcomb : bP (i - k) *
              Combinatorics.boundedFactorGridWindow bP (k + 1) (k + 2) ≤
              Combinatorics.boundedFactorGridWindow bP i (i + 2) := by
            calc bP (i - k) * Combinatorics.boundedFactorGridWindow bP (k + 1) (k + 2)
                ≤ bP (i - k) * Combinatorics.boundedFactorGridWindow bP i (k + 2) := by
                  refine mul_le_mul_of_nonneg_left ?_ (hbP_nn (i - k))
                  exact Combinatorics.boundedFactorGridWindow_mono bP hbP_nn
                    (by omega : k + 1 ≤ i) (le_refl (k + 2))
              _ ≤ Combinatorics.boundedFactorGridWindow bP i ((k + 2) + (i - k)) :=
                  Combinatorics.single_factor_mul_boundedFactorGridWindow_le bP hbP_nn
                    (by omega : 1 ≤ i - k) (by omega : i - k ≤ i)
              _ = Combinatorics.boundedFactorGridWindow bP i (i + 2) := by
                  congr 1; omega
          calc riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + (i - (k + 1))) x
                  ((iteratedCovGrad (I := I) g₀ 1 2 (i - (k + 1))
                    (raisedKoszul (I := I) g₀ g₁)).toSection x) *
                riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + (k + 1)) x
                  ((iteratedCovGrad (I := I) g₀ 3 1 (k + 1)
                    (cometricDoubleTraceCastG0 (I := I) g₀ g₁)).toSection x)
              ≤ (10 * bP (i - k)) *
                  (Kw (k + 1) * Combinatorics.boundedFactorGridWindow bP (k + 1) (k + 2)) := by
                refine mul_le_mul hRK hCG
                  (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 3 (1 + (k + 1)) x _) ?_
                have := hbP_nn (i - k); positivity
            _ = 10 * Kw (k + 1) *
                  (bP (i - k) * Combinatorics.boundedFactorGridWindow bP (k + 1) (k + 2)) := by ring
            _ ≤ 10 * Kw (k + 1) * Combinatorics.boundedFactorGridWindow bP i (i + 2) := by
                refine mul_le_mul_of_nonneg_left hcomb ?_
                have := hKw_nn (k + 1); positivity
        calc (i : ℝ) * diagonalGridGrowthFactor (E := E) i *
              ∑ k ∈ Finset.range i,
                riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + (i - (k + 1))) x
                    ((iteratedCovGrad (I := I) g₀ 1 2 (i - (k + 1))
                      (raisedKoszul (I := I) g₀ g₁)).toSection x) *
                  riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + (k + 1)) x
                    ((iteratedCovGrad (I := I) g₀ 3 1 (k + 1)
                      (cometricDoubleTraceCastG0 (I := I) g₀ g₁)).toSection x)
            ≤ (i : ℝ) * diagonalGridGrowthFactor (E := E) i *
                ((∑ k ∈ Finset.range i, 10 * Kw (k + 1)) *
                  Combinatorics.boundedFactorGridWindow bP i (i + 2)) := by
              refine mul_le_mul_of_nonneg_left hsumcell ?_
              have h2 : 0 ≤ diagonalGridGrowthFactor (E := E) i := appCcGdiag_nonneg (E := E) i
              positivity
          _ = C * Combinatorics.boundedFactorGridWindow bP i (i + 2) := by rw [hC_def]; ring
      rcases i with _ | j
      · simp only [Finset.range_zero, Finset.sum_empty, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
          not_false_eq_true, zero_pow]
        have h1 : 0 ≤ ∑ k ∈ Finset.range 0, 10 * Kw (k + 1) :=
          Finset.sum_nonneg (fun k _ => by have := hKw_nn (k + 1); linarith)
        have h2 : 0 ≤ diagonalGridGrowthFactor (E := E) 0 := appCcGdiag_nonneg (E := E) 0
        have h3 : 0 ≤ Kflat (0 - 1) := hKflat_nn (0 - 1)
        have hsumnn : 0 ≤ ∑ j ∈ Finset.range 1, ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 :=
          Finset.sum_nonneg (fun j _ => sq_nonneg _)
        positivity
      · obtain ⟨hgrid_int, hgrid_bound⟩ := hKflat P hPball j
        have hint : MeasureTheory.Integrable
            (fun x => C * Combinatorics.boundedFactorGridWindow
              (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (j + 1) (j + 3))
            (riemannianVolumeMeasure (I := I) (M := M) g₀) := hgrid_int.const_mul C
        have hkey := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M)
          g₀ 3 (2 + (j + 1))
          (∑ k ∈ Finset.range (j + 1),
            ccOperatorFieldComp (I := I) (M := M) g₀ 3 (1 + (k + 1)) (2 + (j + 1))
              (appCcLeibnizPsi (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁) (j + 1) (k + 1))
              (iteratedCovGrad (I := I) g₀ 3 1 (k + 1) (cometricDoubleTraceCastG0 (I := I) g₀ g₁)))
          _ hint hpt
        refine le_trans hkey ?_
        rw [MeasureTheory.integral_const_mul]
        have hbb : C * ∫ x, Combinatorics.boundedFactorGridWindow
                (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (j + 1) (j + 3)
                ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)
            ≤ C * (Kflat j * (1 + ∑ jj ∈ Finset.range (j + 1 + 1),
                ‖iteratedCovGrad (I := I) g₀ 0 2 jj P‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left hgrid_bound hC_nn
        refine le_trans hbb (le_of_eq ?_)
        rw [hC_def]
        simp only [Nat.add_sub_cancel]
        push_cast
        ring
    · haveI : IsEmpty M := not_nonempty_iff.mp hMne
      have hz : ‖∑ k ∈ Finset.range i,
            ccOperatorFieldComp (I := I) (M := M) g₀ 3 (1 + (k + 1)) (2 + i)
              (appCcLeibnizPsi (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁) i (k + 1))
              (iteratedCovGrad (I := I) g₀ 3 1 (k + 1) (cometricDoubleTraceCastG0 (I := I) g₀ g₁))‖ = 0 := by
        rw [SmoothCcTensor.norm_def, tensorL2Norm_def, tensorL2Inner,
          MeasureTheory.integral_of_isEmpty, Real.sqrt_zero]
      rw [hz, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
      have h1 : 0 ≤ ∑ k ∈ Finset.range i, 10 * Kw (k + 1) :=
        Finset.sum_nonneg (fun k _ => by have := hKw_nn (k + 1); linarith)
      have h2 : 0 ≤ diagonalGridGrowthFactor (E := E) i := appCcGdiag_nonneg (E := E) i
      have h3 : 0 ≤ Kflat (i - 1) := hKflat_nn (i - 1)
      have hsumnn : 0 ≤ ∑ j ∈ Finset.range (i + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 :=
        Finset.sum_nonneg (fun j _ => sq_nonneg _)
      positivity

theorem ricciArmOrder1KoszulCoeff_perOrder_l2_topSeparated_generic_allOrders
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧ ∃ Kleak : ℝ, 0 ≤ Kleak ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ),
          ∃ Hd : SmoothCcTensor g₀ 3 (2 + i),
            (∀ x : M,
              riemannianFiberNormSq (I := I) (M := M) g₀ 3 (2 + i) x (Hd.toSection x) ≤
                Ktop * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 1)) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (i + 1) P).toSection x)) ∧
            ‖Hd‖ ^ 2 ≤ Ktop * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 1) P‖ ^ 2 ∧
            ‖iteratedCovGrad (I := I) g₀ 3 2 i
                (ricciArmOrder1KoszulCoeff (I := I) (M := M) g₀ g₁) - Hd‖ ^ 2 ≤
              Kc i * (1 + ∑ j ∈ Finset.range (i + 1),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) +
                Kleak * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 1) P‖ ^ 2 := by
  classical
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  obtain ⟨ΛB, _, hΛB_nn, _, hBfeed⟩ :=
    cometricDoubleTraceField_order0sup_jetL2_ballUniform_generic
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨Kc, hKc_nn, Kleak, hKleak_nn, hleaf⟩ :=
    ricciArmOrder1KoszulCoeff_topSeparatedResidual_jetL2_flat_leak_allOrders
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  refine ⟨10 * ΛB ^ 2, by positivity, Kc, hKc_nn, Kleak, hKleak_nn, ?_⟩
  intro g₁ P δ hδ_le hδ htie hPball i
  obtain ⟨hBsup, _⟩ := hBfeed g₁ P hδ_le hδ htie hPball
  have hheadpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 3 (2 + i) x
          ((ccOperatorFieldComp (I := I) (M := M) g₀ 3 1 (2 + i)
            (iteratedCovGrad (I := I) g₀ 1 2 i (raisedKoszul (I := I) g₀ g₁))
            (cometricDoubleTraceCastG0 (I := I) g₀ g₁)).toSection x) ≤
        10 * ΛB ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 1)) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (i + 1) P).toSection x) := by
    intro x
    rw [appCcRS_toSection (I := I) (M := M) g₀ 3 1 (2 + i)
      (iteratedCovGrad (I := I) g₀ 1 2 i (raisedKoszul (I := I) g₀ g₁))
      (cometricDoubleTraceCastG0 (I := I) g₀ g₁) x]
    refine le_trans (riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ 3 1
      (2 + i) x _ _) ?_
    have h1 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 2 i (raisedKoszul (I := I) g₀ g₁)).toSection x) ≤
        10 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 1)) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (i + 1) P).toSection x) :=
      rfns_iteratedCovGrad_raisedKoszul_pointwise_le (I := I) (M := M) g₀ g₁ P htie i x
    have h2 : riemannianFiberNormSq (I := I) (M := M) g₀ 3 1 x
        ((cometricDoubleTraceCastG0 (I := I) g₀ g₁).toSection x) ≤ ΛB ^ 2 := hBsup x
    calc riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 1 2 i (raisedKoszul (I := I) g₀ g₁)).toSection x) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 1 x
          ((cometricDoubleTraceCastG0 (I := I) g₀ g₁).toSection x)
        ≤ (10 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 1)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 1) P).toSection x)) * ΛB ^ 2 := by
          refine mul_le_mul h1 h2
            (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 3 1 x _) ?_
          have := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + (i + 1)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 1) P).toSection x)
          positivity
      _ = 10 * ΛB ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 1)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 1) P).toSection x) := by ring
  refine ⟨ccOperatorFieldComp (I := I) (M := M) g₀ 3 1 (2 + i)
      (iteratedCovGrad (I := I) g₀ 1 2 i (raisedKoszul (I := I) g₀ g₁))
      (cometricDoubleTraceCastG0 (I := I) g₀ g₁), hheadpt, ?_, ?_⟩
  · have hF_int : MeasureTheory.Integrable
        (fun x => 10 * ΛB ^ 2 *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 1)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 1) P).toSection x))
        (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
      (integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 0 (2 + (i + 1))
        (iteratedCovGrad (I := I) g₀ 0 2 (i + 1) P)).const_mul _
    have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M)
      g₀ 3 (2 + i)
      (ccOperatorFieldComp (I := I) (M := M) g₀ 3 1 (2 + i)
        (iteratedCovGrad (I := I) g₀ 1 2 i (raisedKoszul (I := I) g₀ g₁))
        (cometricDoubleTraceCastG0 (I := I) g₀ g₁))
      _ hF_int hheadpt
    refine le_trans key ?_
    rw [MeasureTheory.integral_const_mul]
    rw [← arm1NormSq_eq_integral (I := I) (M := M) g₀ 0 (2 + (i + 1))
      (iteratedCovGrad (I := I) g₀ 0 2 (i + 1) P)]
  · exact hleaf g₁ P hδ_le hδ htie hPball i

end DifferentialGeometry.Integral.Connection

end
