import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciArmResidualCoefficientFields
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldInputSlotSymmetrization
import DifferentialGeometry.Analysis.Sobolev.BoundedFactorProductGrid
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricArmCoeffJetTower
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.FlatArmCoeffConnectionDifferenceBridge
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RicciArmResidualFieldGridWindowGInvQuadResidual
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RicciArmResidualFieldGridWindowBgRefoldConversion


noncomputable section

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle MeasureTheory
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

section NormedScalarHelpers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem iteratedCovGrad_smul_real (g : SmoothRiemannianMetric I M) (r s j : ℕ) (c : ℝ)
    (w : SmoothCcTensor g r s) :
    iteratedCovGrad (I := I) g r s j (c • w) = c • iteratedCovGrad (I := I) g r s j w := by
  induction j with
  | zero => simp only [iteratedCovGrad_zero]
  | succ j ih => rw [iteratedCovGrad_succ, iteratedCovGrad_succ, ih,
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad_smul]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma riemannianFiberNormSq_smul_value (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (x : M) (c : ℝ) (v : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (c • v) =
      c ^ 2 * riemannianFiberNormSq (I := I) (M := M) g r s x v := by
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (c • v),
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x v]
  rw [TensorRSSpace.toModel_smul, tensorInnerPointwise_smul_left,
    tensorInnerPointwise_smul_right]
  ring

end NormedScalarHelpers


theorem riemannianFiberNormSq_iteratedCovGrad_ricciArmOrder0BgRCommCoeffFieldDifference_boundedFactorGridWindow_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₁
                - ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₀)).toSection x) ≤
          C i * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3) := by
  classical
  obtain ⟨C2, hC2_nn, hC2⟩ :=
    exists_rfns_icg_mvDoubleTraceField_window (I := I) (M := M) g₀ 2 hδ₀
  set KD : ℕ → ℝ := fun u =>
    (exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 4 (2 + u)
      (iteratedCovGrad (I := I) g₀ 4 2 u (cometricDoubleTraceField (I := I) g₀ 2))).choose
    with hKD_def
  have hKD_nn : ∀ u, 0 ≤ KD u := fun u =>
    (exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 4 (2 + u)
      (iteratedCovGrad (I := I) g₀ 4 2 u
        (cometricDoubleTraceField (I := I) g₀ 2))).choose_spec.1
  have hKD : ∀ u (y : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + u) y
          ((iteratedCovGrad (I := I) g₀ 4 2 u
            (cometricDoubleTraceField (I := I) g₀ 2)).toSection y) ≤ KD u := fun u =>
    (exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 4 (2 + u)
      (iteratedCovGrad (I := I) g₀ 4 2 u
        (cometricDoubleTraceField (I := I) g₀ 2))).choose_spec.2
  set KW : ℕ → ℝ := fun w =>
    (exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 2 (4 + w)
      (iteratedCovGrad (I := I) g₀ 2 4 w (riemannCometricDoubleTraceFold (I := I) (M := M) g₀))).choose
    with hKW_def
  have hKW_nn : ∀ w, 0 ≤ KW w := fun w =>
    (exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 2 (4 + w)
      (iteratedCovGrad (I := I) g₀ 2 4 w
        (riemannCometricDoubleTraceFold (I := I) (M := M) g₀))).choose_spec.1
  have hKW : ∀ w (y : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + w) y
          ((iteratedCovGrad (I := I) g₀ 2 4 w
            (riemannCometricDoubleTraceFold (I := I) (M := M) g₀)).toSection y) ≤ KW w := fun w =>
    (exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 2 (4 + w)
      (iteratedCovGrad (I := I) g₀ 2 4 w
        (riemannCometricDoubleTraceFold (I := I) (M := M) g₀))).choose_spec.2
  refine ⟨fun i => diagonalGridGrowthFactor (E := E) i *
      ∑ u ∈ Finset.range (i + 1), (2 * C2 u + 2 * KD u) *
        ∑ w ∈ Finset.range (i + 1 - u), KW w,
    fun i => mul_nonneg (appCcGdiag_nonneg (E := E) i)
      (Finset.sum_nonneg fun u _ => mul_nonneg
        (by have := hC2_nn u; have := hKD_nn u; linarith)
        (Finset.sum_nonneg fun w _ => hKW_nn w)), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hbound i x
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) with hb_def
  have hb_nn : ∀ l, 0 ≤ b l :=
    fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  have hdiff : ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₁
      - ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₀ =
      ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 2
        (secondMetricCometricDoubleTraceField (I := I) (M := M) g₀ g₁ 2 - cometricDoubleTraceField (I := I) g₀ 2)
        (riemannCometricDoubleTraceFold (I := I) (M := M) g₀) := by
    rw [appCcRS_sub_left (I := I) (M := M) g₀ 2 4 2
      (secondMetricCometricDoubleTraceField (I := I) (M := M) g₀ g₁ 2) (cometricDoubleTraceField (I := I) g₀ 2)
      (riemannCometricDoubleTraceFold (I := I) (M := M) g₀)]
    rw [← bgRCommCoeffField_eq_refold (I := I) (M := M) g₀ g₁]
    rw [← mvDoubleTraceField_self_eq (I := I) (M := M) g₀ 2]
    rw [← bgRCommCoeffField_eq_refold (I := I) (M := M) g₀ g₀]
  rw [hdiff]
  refine le_trans (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le (I := I)
    (M := M) g₀ i 2 4 2
    (secondMetricCometricDoubleTraceField (I := I) (M := M) g₀ g₁ 2 - cometricDoubleTraceField (I := I) g₀ 2)
    (riemannCometricDoubleTraceFold (I := I) (M := M) g₀) x) ?_
  have hW_nn : 0 ≤ Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) :=
    Combinatorics.boundedFactorGridWindow_nonneg b hb_nn _ _
  have hAd : ∀ u : ℕ, u ≤ i →
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + u) x
          ((iteratedCovGrad (I := I) g₀ 4 2 u
            (secondMetricCometricDoubleTraceField (I := I) (M := M) g₀ g₁ 2
              - cometricDoubleTraceField (I := I) g₀ 2)).toSection x) ≤
        (2 * C2 u + 2 * KD u) * Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) := by
    intro u hu
    have hsec : (iteratedCovGrad (I := I) g₀ 4 2 u
        (secondMetricCometricDoubleTraceField (I := I) (M := M) g₀ g₁ 2
          - cometricDoubleTraceField (I := I) g₀ 2)).toSection x =
        (iteratedCovGrad (I := I) g₀ 4 2 u
          (secondMetricCometricDoubleTraceField (I := I) (M := M) g₀ g₁ 2)).toSection x -
        (iteratedCovGrad (I := I) g₀ 4 2 u
          (cometricDoubleTraceField (I := I) g₀ 2)).toSection x := by
      rw [sub_eq_add_neg (secondMetricCometricDoubleTraceField (I := I) (M := M) g₀ g₁ 2)
        (cometricDoubleTraceField (I := I) g₀ 2)]
      rw [iteratedCovGrad_add (I := I) g₀ 4 2 u _ _,
        iteratedCovGrad_neg (I := I) g₀ 4 2 u _, SmoothCcTensor.toSection_add]
      rw [show (((iteratedCovGrad (I := I) g₀ 4 2 u
            (secondMetricCometricDoubleTraceField (I := I) (M := M) g₀ g₁ 2)).toSection +
          (-(iteratedCovGrad (I := I) g₀ 4 2 u
            (cometricDoubleTraceField (I := I) g₀ 2))).toSection) x) =
          (iteratedCovGrad (I := I) g₀ 4 2 u
            (secondMetricCometricDoubleTraceField (I := I) (M := M) g₀ g₁ 2)).toSection x +
          (-(iteratedCovGrad (I := I) g₀ 4 2 u
            (cometricDoubleTraceField (I := I) g₀ 2))).toSection x from rfl]
      rw [show ((-(iteratedCovGrad (I := I) g₀ 4 2 u
          (cometricDoubleTraceField (I := I) g₀ 2))).toSection x) =
          -((iteratedCovGrad (I := I) g₀ 4 2 u
            (cometricDoubleTraceField (I := I) g₀ 2)).toSection x) from by
        rw [SmoothCcTensor.toSection_neg]; rfl]
      rw [← sub_eq_add_neg]
    rw [hsec]
    refine le_trans (riemannianFiberNormSq_sub_le_pt (I := I) (M := M) g₀ 4 (2 + u) x _ _) ?_
    have h1 : riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + u) x
        ((iteratedCovGrad (I := I) g₀ 4 2 u
          (secondMetricCometricDoubleTraceField (I := I) (M := M) g₀ g₁ 2)).toSection x) ≤
        C2 u * Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) := by
      refine le_trans (hC2 g₁ P htie hδ_le hδ0 hbound u (i + 1) (by omega) x) ?_
      refine mul_le_mul_of_nonneg_left ?_ (hC2_nn u)
      exact Combinatorics.boundedFactorGridWindow_mono b hb_nn (le_refl _) (by omega)
    have h2 : riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + u) x
        ((iteratedCovGrad (I := I) g₀ 4 2 u
          (cometricDoubleTraceField (I := I) g₀ 2)).toSection x) ≤
        KD u * Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) := by
      calc riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + u) x
            ((iteratedCovGrad (I := I) g₀ 4 2 u
              (cometricDoubleTraceField (I := I) g₀ 2)).toSection x)
          ≤ KD u := hKD u x
        _ = KD u * 1 := by ring
        _ ≤ KD u * Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) := by
            refine mul_le_mul_of_nonneg_left ?_ (hKD_nn u)
            exact Combinatorics.one_le_boundedFactorGridWindow b hb_nn (by omega)
    calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + u) x
          ((iteratedCovGrad (I := I) g₀ 4 2 u
            (secondMetricCometricDoubleTraceField (I := I) (M := M) g₀ g₁ 2)).toSection x) +
        2 * riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + u) x
          ((iteratedCovGrad (I := I) g₀ 4 2 u
            (cometricDoubleTraceField (I := I) g₀ 2)).toSection x)
        ≤ 2 * (C2 u * Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3)) +
            2 * (KD u * Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3)) := by
          linarith [h1, h2]
      _ = (2 * C2 u + 2 * KD u) * Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) := by
          ring
  calc diagonalGridGrowthFactor (E := E) i *
        ∑ u ∈ Finset.range (i + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + u) x
              ((iteratedCovGrad (I := I) g₀ 4 2 u
                (secondMetricCometricDoubleTraceField (I := I) (M := M) g₀ g₁ 2
                  - cometricDoubleTraceField (I := I) g₀ 2)).toSection x) *
            ∑ w ∈ Finset.range (i + 1 - u),
              riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + w) x
                ((iteratedCovGrad (I := I) g₀ 2 4 w
                  (riemannCometricDoubleTraceFold (I := I) (M := M) g₀)).toSection x)
      ≤ diagonalGridGrowthFactor (E := E) i *
          ∑ u ∈ Finset.range (i + 1),
            ((2 * C2 u + 2 * KD u) *
              Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3)) *
            ∑ w ∈ Finset.range (i + 1 - u), KW w := by
        refine mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun u hu => ?_) (appCcGdiag_nonneg (E := E) i)
        rw [Finset.mem_range] at hu
        refine mul_le_mul (hAd u (by omega)) (Finset.sum_le_sum fun w _ => hKW w x)
          (Finset.sum_nonneg fun w _ =>
            riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (4 + w) x _)
          (mul_nonneg (by have := hC2_nn u; have := hKD_nn u; linarith) hW_nn)
    _ = (diagonalGridGrowthFactor (E := E) i *
          ∑ u ∈ Finset.range (i + 1), (2 * C2 u + 2 * KD u) *
            ∑ w ∈ Finset.range (i + 1 - u), KW w) *
          Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) := by
        have hstep : ∀ u : ℕ, ((2 * C2 u + 2 * KD u) *
            Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3)) *
            (∑ w ∈ Finset.range (i + 1 - u), KW w) =
            ((2 * C2 u + 2 * KD u) * ∑ w ∈ Finset.range (i + 1 - u), KW w) *
              Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) := by
          intro u
          ring
        rw [Finset.sum_congr rfl fun u _ => hstep u, ← Finset.sum_mul]
        ring


theorem rfns_iteratedCovGrad_ricciArmSharpGradKoszulResidualFieldMetricDifference_boundedFactorGridWindow_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀ g₁
                (metricDifferenceCcTensor (I := I) (M := M) g₀ g₁))).toSection x) ≤
          C i * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3) := by
  classical
  obtain ⟨CPT, hCPT_nn, hCPT⟩ :=
    exists_rfns_icg_mvPairTraceOp_window (I := I) (M := M) g₀ hδ₀
  obtain ⟨CW1, hCW1_nn, hCW1⟩ :=
    exists_riemannianFiberNormSq_iteratedCovGrad_koszulConnDiffFoldWeightGeneral_boundedFactorGridWindow_le (I := I) (M := M) g₀ tauM1 hδ₀
  obtain ⟨CW2, hCW2_nn, hCW2⟩ :=
    exists_riemannianFiberNormSq_iteratedCovGrad_koszulConnDiffFoldWeightGeneral_boundedFactorGridWindow_le (I := I) (M := M) g₀ tauM2 hδ₀
  obtain ⟨CW3, hCW3_nn, hCW3⟩ :=
    exists_riemannianFiberNormSq_iteratedCovGrad_koszulConnDiffFoldWeightGeneral_boundedFactorGridWindow_le (I := I) (M := M) g₀ tauM3 hδ₀
  obtain ⟨CW4, hCW4_nn, hCW4⟩ :=
    exists_riemannianFiberNormSq_iteratedCovGrad_koszulConnDiffFoldWeightGeneral_boundedFactorGridWindow_le (I := I) (M := M) g₀ tauM4 hδ₀
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : 0 ≤ fr := Nat.cast_nonneg _
  set CX : ℕ → ℝ := fun w =>
    fr ^ 2 * (4 * CW1 w + 4 * CW2 w + 4 * CW3 w + 4 * CW4 w) with hCX_def
  have hCX_nn : ∀ w, 0 ≤ CX w := fun w => by
    have h1 := hCW1_nn w
    have h2 := hCW2_nn w
    have h3 := hCW3_nn w
    have h4 := hCW4_nn w
    have h5 : (0 : ℝ) ≤ fr ^ 2 := by positivity
    simp only [hCX_def]
    nlinarith
  refine ⟨fun i => 4 * (diagonalGridGrowthFactor (E := E) i *
      ∑ u ∈ Finset.range (i + 1), CPT u *
        ∑ w ∈ Finset.range (i + 1 - u),
          CX w * Combinatorics.windowPairCellCount (u + 1) (w + 3)),
    fun i => by
      refine mul_nonneg (by norm_num)
        (mul_nonneg (appCcGdiag_nonneg (E := E) i)
          (Finset.sum_nonneg fun u _ => mul_nonneg (hCPT_nn u)
            (Finset.sum_nonneg fun w _ => mul_nonneg (hCX_nn w)
              (Combinatorics.windowPairCellCount_nonneg _ _)))), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hbound i x
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) with hb_def
  have hb_nn : ∀ l, 0 ≤ b l :=
    fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  rw [metricDifferenceCcTensor_eq_symmS (I := I) (M := M) g₀ g₁ P htie]
  rw [sharpGradKoszulResidualField_eq_refold (I := I) (M := M) g₀ g₁ P htie]
  have hsm : (iteratedCovGrad (I := I) g₀ 2 2 i
      ((2 : ℝ) •
        ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 (secondMetricPairTraceOp (I := I) (M := M) g₀ g₁)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 ricciFoldRemainderSlotPerm
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              ((koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM1 P +
                  koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM2 P) -
                (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM3 P +
                  koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM4 P)))))).toSection x =
      (2 : ℝ) • ((iteratedCovGrad (I := I) g₀ 2 2 i
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 (secondMetricPairTraceOp (I := I) (M := M) g₀ g₁)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 ricciFoldRemainderSlotPerm
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              ((koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM1 P +
                  koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM2 P) -
                (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM3 P +
                  koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM4 P)))))).toSection x) := by
    rw [iteratedCovGrad_smul_real (I := I) g₀ 2 2 i (2 : ℝ) _,
      SmoothCcTensor.toSection_smul]
    rfl
  rw [hsm, riemannianFiberNormSq_smul_value (I := I) (M := M) g₀ 2 (2 + i) x (2 : ℝ) _,
    show ((2 : ℝ)) ^ 2 = 4 from by norm_num]
  have hPT : ∀ u : ℕ, u ≤ i →
      riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + u) x
          ((iteratedCovGrad (I := I) g₀ 6 2 u
            (secondMetricPairTraceOp (I := I) (M := M) g₀ g₁)).toSection x) ≤
        CPT u * Combinatorics.boundedFactorGridWindow b (i + 1) (u + 1) :=
    fun u hu => hCPT g₁ P htie hδ_le hδ0 hbound u (i + 1) (by omega) x
  have hWX : ∀ w : ℕ, w ≤ i →
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + w) x
          ((iteratedCovGrad (I := I) g₀ 2 6 w
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 ricciFoldRemainderSlotPerm
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                ((koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM1 P +
                    koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM2 P) -
                  (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM3 P +
                    koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM4 P))))).toSection x) ≤
        CX w * Combinatorics.boundedFactorGridWindow b (i + 1) (w + 3) := by
    intro w hw
    rw [riemannianFiberNormSq_iteratedCovGrad_rsDomDomCongrSection_eq (I := I) (M := M) g₀ 2 6 ricciFoldRemainderSlotPerm _ w x]
    rw [show slotExtendIter (I := I) (M := M) g₀ 0 4 2
        ((koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM1 P +
            koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM2 P) -
          (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM3 P +
            koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM4 P)) =
        slotExtend (I := I) (M := M) g₀ 1 5 (slotExtend (I := I) (M := M) g₀ 0 4
          ((koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM1 P +
              koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM2 P) -
            (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM3 P +
              koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM4 P))) from rfl]
    refine le_trans (rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 1 5
      (slotExtend (I := I) (M := M) g₀ 0 4
        ((koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM1 P +
            koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM2 P) -
          (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM3 P +
            koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM4 P))) w x) ?_
    refine le_trans (mul_le_mul_of_nonneg_left
      (rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 0 4
        ((koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM1 P +
            koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM2 P) -
          (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM3 P +
            koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM4 P)) w x) hfr_nn) ?_
    have hsub : (iteratedCovGrad (I := I) g₀ 0 4 w
        ((koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM1 P +
            koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM2 P) -
          (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM3 P +
            koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM4 P))).toSection x =
        (iteratedCovGrad (I := I) g₀ 0 4 w
          (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM1 P +
            koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM2 P)).toSection x -
        (iteratedCovGrad (I := I) g₀ 0 4 w
          (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM3 P +
            koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM4 P)).toSection x := by
      rw [sub_eq_add_neg (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM1 P +
          koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM2 P)
        (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM3 P +
          koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM4 P)]
      rw [iteratedCovGrad_add (I := I) g₀ 0 4 w _ _,
        iteratedCovGrad_neg (I := I) g₀ 0 4 w _, SmoothCcTensor.toSection_add]
      rw [show (((iteratedCovGrad (I := I) g₀ 0 4 w
            (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM1 P +
              koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM2 P)).toSection +
          (-(iteratedCovGrad (I := I) g₀ 0 4 w
            (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM3 P +
              koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM4 P))).toSection) x) =
          (iteratedCovGrad (I := I) g₀ 0 4 w
            (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM1 P +
              koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM2 P)).toSection x +
          (-(iteratedCovGrad (I := I) g₀ 0 4 w
            (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM3 P +
              koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM4 P))).toSection x from rfl]
      rw [show ((-(iteratedCovGrad (I := I) g₀ 0 4 w
          (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM3 P +
            koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM4 P))).toSection x) =
          -((iteratedCovGrad (I := I) g₀ 0 4 w
            (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM3 P +
              koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM4 P)).toSection x) from by
        rw [SmoothCcTensor.toSection_neg]; rfl]
      rw [← sub_eq_add_neg]
    have h12 : (iteratedCovGrad (I := I) g₀ 0 4 w
        (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM1 P +
          koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM2 P)).toSection x =
        (iteratedCovGrad (I := I) g₀ 0 4 w
          (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM1 P)).toSection x +
        (iteratedCovGrad (I := I) g₀ 0 4 w
          (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM2 P)).toSection x := by
      rw [iteratedCovGrad_add (I := I) g₀ 0 4 w _ _, SmoothCcTensor.toSection_add]
      rfl
    have h34 : (iteratedCovGrad (I := I) g₀ 0 4 w
        (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM3 P +
          koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM4 P)).toSection x =
        (iteratedCovGrad (I := I) g₀ 0 4 w
          (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM3 P)).toSection x +
        (iteratedCovGrad (I := I) g₀ 0 4 w
          (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM4 P)).toSection x := by
      rw [iteratedCovGrad_add (I := I) g₀ 0 4 w _ _, SmoothCcTensor.toSection_add]
      rfl
    have hA1 := hCW1 g₁ P htie hδ_le hδ0 hbound w (i + 1) (by omega) x
    rw [show ccOperatorFieldComp (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 tauM1
          (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
            (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovecCc (I := I) g₀ P))
            (connDiffLoweredCc (I := I) g₀ g₁))) =
        koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM1 P from rfl] at hA1
    have hA2 := hCW2 g₁ P htie hδ_le hδ0 hbound w (i + 1) (by omega) x
    rw [show ccOperatorFieldComp (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 tauM2
          (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
            (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovecCc (I := I) g₀ P))
            (connDiffLoweredCc (I := I) g₀ g₁))) =
        koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM2 P from rfl] at hA2
    have hA3 := hCW3 g₁ P htie hδ_le hδ0 hbound w (i + 1) (by omega) x
    rw [show ccOperatorFieldComp (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 tauM3
          (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
            (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovecCc (I := I) g₀ P))
            (connDiffLoweredCc (I := I) g₀ g₁))) =
        koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM3 P from rfl] at hA3
    have hA4 := hCW4 g₁ P htie hδ_le hδ0 hbound w (i + 1) (by omega) x
    rw [show ccOperatorFieldComp (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 tauM4
          (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
            (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovecCc (I := I) g₀ P))
            (connDiffLoweredCc (I := I) g₀ g₁))) =
        koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM4 P from rfl] at hA4
    calc fr * (fr * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
          ((iteratedCovGrad (I := I) g₀ 0 4 w
            ((koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM1 P +
                koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM2 P) -
              (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM3 P +
                koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM4 P))).toSection x))
        ≤ fr * (fr * (2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
            ((iteratedCovGrad (I := I) g₀ 0 4 w
              (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM1 P +
                koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM2 P)).toSection x)
          + 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
            ((iteratedCovGrad (I := I) g₀ 0 4 w
              (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM3 P +
                koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM4 P)).toSection x))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hfr_nn) hfr_nn
          rw [hsub]
          exact riemannianFiberNormSq_sub_le_pt (I := I) (M := M) g₀ 0 (4 + w) x _ _
      _ ≤ fr * (fr *
          (2 * (2 * (CW1 w * Combinatorics.boundedFactorGridWindow b (i + 1) (w + 3))
              + 2 * (CW2 w * Combinatorics.boundedFactorGridWindow b (i + 1) (w + 3)))
          + 2 * (2 * (CW3 w * Combinatorics.boundedFactorGridWindow b (i + 1) (w + 3))
              + 2 * (CW4 w * Combinatorics.boundedFactorGridWindow b (i + 1) (w + 3))))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hfr_nn) hfr_nn
          have hx12 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
              ((iteratedCovGrad (I := I) g₀ 0 4 w
                (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM1 P +
                  koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM2 P)).toSection x) ≤
              2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
                ((iteratedCovGrad (I := I) g₀ 0 4 w
                  (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM1 P)).toSection x)
              + 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
                ((iteratedCovGrad (I := I) g₀ 0 4 w
                  (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM2 P)).toSection x) := by
            rw [h12]
            exact riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (4 + w) x _ _
          have hx34 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
              ((iteratedCovGrad (I := I) g₀ 0 4 w
                (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM3 P +
                  koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM4 P)).toSection x) ≤
              2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
                ((iteratedCovGrad (I := I) g₀ 0 4 w
                  (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM3 P)).toSection x)
              + 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
                ((iteratedCovGrad (I := I) g₀ 0 4 w
                  (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM4 P)).toSection x) := by
            rw [h34]
            exact riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (4 + w) x _ _
          linarith [hA1, hA2, hA3, hA4, hx12, hx34]
      _ = CX w * Combinatorics.boundedFactorGridWindow b (i + 1) (w + 3) := by
          simp only [hCX_def]
          ring
  refine le_trans (mul_le_mul_of_nonneg_left
    (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le (I := I) (M := M) g₀ i 2 6 2
      (secondMetricPairTraceOp (I := I) (M := M) g₀ g₁)
      (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 ricciFoldRemainderSlotPerm
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2
          ((koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM1 P +
              koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM2 P) -
            (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM3 P +
              koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM4 P)))) x)
    (by norm_num : (0 : ℝ) ≤ 4)) ?_
  calc (4 : ℝ) * (diagonalGridGrowthFactor (E := E) i *
        ∑ u ∈ Finset.range (i + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + u) x
              ((iteratedCovGrad (I := I) g₀ 6 2 u
                (secondMetricPairTraceOp (I := I) (M := M) g₀ g₁)).toSection x) *
            ∑ w ∈ Finset.range (i + 1 - u),
              riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + w) x
                ((iteratedCovGrad (I := I) g₀ 2 6 w
                  (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 ricciFoldRemainderSlotPerm
                    (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                      ((koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM1 P +
                          koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM2 P) -
                        (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ tauM3 P +
                          koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁
                            tauM4 P))))).toSection x))
      ≤ 4 * (diagonalGridGrowthFactor (E := E) i *
          ∑ u ∈ Finset.range (i + 1),
            (CPT u * Combinatorics.boundedFactorGridWindow b (i + 1) (u + 1)) *
            ∑ w ∈ Finset.range (i + 1 - u),
              (CX w * Combinatorics.boundedFactorGridWindow b (i + 1) (w + 3))) := by
        refine mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun u hu => ?_)
            (appCcGdiag_nonneg (E := E) i)) (by norm_num)
        rw [Finset.mem_range] at hu
        refine mul_le_mul (hPT u (by omega)) (Finset.sum_le_sum fun w hw => ?_)
          (Finset.sum_nonneg fun w _ =>
            riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (6 + w) x _)
          (mul_nonneg (hCPT_nn u)
            (Combinatorics.boundedFactorGridWindow_nonneg b hb_nn _ _))
        rw [Finset.mem_range] at hw
        exact hWX w (by omega)
    _ ≤ 4 * ((diagonalGridGrowthFactor (E := E) i *
          ∑ u ∈ Finset.range (i + 1), CPT u *
            ∑ w ∈ Finset.range (i + 1 - u),
              CX w * Combinatorics.windowPairCellCount (u + 1) (w + 3)) *
          Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        rw [mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg (E := E) i)
        rw [Finset.sum_mul]
        refine Finset.sum_le_sum fun u hu => ?_
        rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_le_sum fun w hw => ?_
        rw [Finset.mem_range] at hu hw
        calc CPT u * Combinatorics.boundedFactorGridWindow b (i + 1) (u + 1) *
              (CX w * Combinatorics.boundedFactorGridWindow b (i + 1) (w + 3))
            = (CPT u * CX w) *
                (Combinatorics.boundedFactorGridWindow b (i + 1) (u + 1) *
                  Combinatorics.boundedFactorGridWindow b (i + 1) (w + 3)) := by ring
          _ ≤ (CPT u * CX w) *
                (Combinatorics.windowPairCellCount (u + 1) (w + 3) *
                  Combinatorics.boundedFactorGridWindow b (i + 1)
                    ((u + 1) + (w + 3) - 1)) := by
              refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hCPT_nn u) (hCX_nn w))
              exact Combinatorics.boundedFactorGridWindow_mul_le b hb_nn (i + 1) (u + 1)
                (w + 3) (by omega) (by omega)
          _ ≤ (CPT u * CX w) *
                (Combinatorics.windowPairCellCount (u + 1) (w + 3) *
                  Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3)) := by
              refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hCPT_nn u) (hCX_nn w))
              refine mul_le_mul_of_nonneg_left ?_
                (Combinatorics.windowPairCellCount_nonneg _ _)
              exact Combinatorics.boundedFactorGridWindow_mono b hb_nn (le_refl _) (by omega)
          _ = CPT u * (CX w * Combinatorics.windowPairCellCount (u + 1) (w + 3)) *
                Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) := by ring
    _ = (4 * (diagonalGridGrowthFactor (E := E) i *
          ∑ u ∈ Finset.range (i + 1), CPT u *
            ∑ w ∈ Finset.range (i + 1 - u),
              CX w * Combinatorics.windowPairCellCount (u + 1) (w + 3))) *
          Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) := by ring


theorem rfns_iteratedCovGrad_ricciArmRicciFoldRemainderFieldMetricDifference_boundedFactorGridWindow_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmRicciFoldRemainderField (I := I) (M := M) g₀ g₁
                (metricDifferenceCcTensor (I := I) (M := M) g₀ g₁))).toSection x) ≤
          C i * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3) := by
  classical
  obtain ⟨CPT, hCPT_nn, hCPT⟩ :=
    exists_rfns_icg_mvPairTraceOp_window (I := I) (M := M) g₀ hδ₀
  obtain ⟨CWA, hCWA_nn, hCWA⟩ :=
    exists_riemannianFiberNormSq_iteratedCovGrad_ricciFoldWeightGeneral_boundedFactorGridWindow_le (I := I) (M := M) g₀
      (Equiv.swap (1 : Fin 6) 3) hδ₀
  obtain ⟨CWB, hCWB_nn, hCWB⟩ :=
    exists_riemannianFiberNormSq_iteratedCovGrad_ricciFoldWeightGeneral_boundedFactorGridWindow_le (I := I) (M := M) g₀ ricciFoldWeightBPerm hδ₀
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : 0 ≤ fr := Nat.cast_nonneg _
  set CX : ℕ → ℝ := fun w => fr ^ 2 * (2 * CWA w + 2 * CWB w) with hCX_def
  have hCX_nn : ∀ w, 0 ≤ CX w := fun w => by
    have h1 := hCWA_nn w
    have h2 := hCWB_nn w
    have h3 : (0 : ℝ) ≤ fr ^ 2 := by positivity
    simp only [hCX_def]
    nlinarith
  refine ⟨fun i => (1 / 4 : ℝ) * (diagonalGridGrowthFactor (E := E) i *
      ∑ u ∈ Finset.range (i + 1), CPT u *
        ∑ w ∈ Finset.range (i + 1 - u),
          CX w * Combinatorics.windowPairCellCount (u + 1) (w + 1)),
    fun i => by
      refine mul_nonneg (by norm_num)
        (mul_nonneg (appCcGdiag_nonneg (E := E) i)
          (Finset.sum_nonneg fun u _ => mul_nonneg (hCPT_nn u)
            (Finset.sum_nonneg fun w _ => mul_nonneg (hCX_nn w)
              (Combinatorics.windowPairCellCount_nonneg _ _)))), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hbound i x
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) with hb_def
  have hb_nn : ∀ l, 0 ≤ b l :=
    fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  rw [metricDifferenceCcTensor_eq_symmS (I := I) (M := M) g₀ g₁ P htie]
  rw [ricciFoldRemainderField_eq_refold (I := I) (M := M) g₀ g₁ (ccTensor02Symm (I := I) g₀ P)]
  have hsm : (iteratedCovGrad (I := I) g₀ 2 2 i
      ((-(1 / 2) : ℝ) •
        ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 (secondMetricPairTraceOp (I := I) (M := M) g₀ g₁)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 ricciFoldRemainderSlotPerm
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (ricciFoldWeightA (I := I) (M := M) g₀ (ccTensor02Symm (I := I) g₀ P) +
                ricciFoldWeightB (I := I) (M := M) g₀ (ccTensor02Symm (I := I) g₀ P)))))).toSection x =
      (-(1 / 2) : ℝ) • ((iteratedCovGrad (I := I) g₀ 2 2 i
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 (secondMetricPairTraceOp (I := I) (M := M) g₀ g₁)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 ricciFoldRemainderSlotPerm
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (ricciFoldWeightA (I := I) (M := M) g₀ (ccTensor02Symm (I := I) g₀ P) +
                ricciFoldWeightB (I := I) (M := M) g₀
                  (ccTensor02Symm (I := I) g₀ P)))))).toSection x) := by
    rw [iteratedCovGrad_smul_real (I := I) g₀ 2 2 i (-(1 / 2) : ℝ) _,
      SmoothCcTensor.toSection_smul]
    rfl
  rw [hsm, riemannianFiberNormSq_smul_value (I := I) (M := M) g₀ 2 (2 + i) x (-(1 / 2) : ℝ) _,
    show ((-(1 / 2) : ℝ)) ^ 2 = 1 / 4 from by norm_num]
  have hPT : ∀ u : ℕ, u ≤ i →
      riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + u) x
          ((iteratedCovGrad (I := I) g₀ 6 2 u
            (secondMetricPairTraceOp (I := I) (M := M) g₀ g₁)).toSection x) ≤
        CPT u * Combinatorics.boundedFactorGridWindow b (i + 1) (u + 1) :=
    fun u hu => hCPT g₁ P htie hδ_le hδ0 hbound u (i + 1) (by omega) x
  have hWX : ∀ w : ℕ, w ≤ i →
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + w) x
          ((iteratedCovGrad (I := I) g₀ 2 6 w
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 ricciFoldRemainderSlotPerm
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (ricciFoldWeightA (I := I) (M := M) g₀ (ccTensor02Symm (I := I) g₀ P) +
                  ricciFoldWeightB (I := I) (M := M) g₀
                    (ccTensor02Symm (I := I) g₀ P))))).toSection x) ≤
        CX w * Combinatorics.boundedFactorGridWindow b (i + 1) (w + 1) := by
    intro w hw
    rw [riemannianFiberNormSq_iteratedCovGrad_rsDomDomCongrSection_eq (I := I) (M := M) g₀ 2 6 ricciFoldRemainderSlotPerm _ w x]
    rw [show slotExtendIter (I := I) (M := M) g₀ 0 4 2
        (ricciFoldWeightA (I := I) (M := M) g₀ (ccTensor02Symm (I := I) g₀ P) +
          ricciFoldWeightB (I := I) (M := M) g₀ (ccTensor02Symm (I := I) g₀ P)) =
        slotExtend (I := I) (M := M) g₀ 1 5 (slotExtend (I := I) (M := M) g₀ 0 4
          (ricciFoldWeightA (I := I) (M := M) g₀ (ccTensor02Symm (I := I) g₀ P) +
            ricciFoldWeightB (I := I) (M := M) g₀ (ccTensor02Symm (I := I) g₀ P))) from rfl]
    refine le_trans (rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 1 5
      (slotExtend (I := I) (M := M) g₀ 0 4
        (ricciFoldWeightA (I := I) (M := M) g₀ (ccTensor02Symm (I := I) g₀ P) +
          ricciFoldWeightB (I := I) (M := M) g₀ (ccTensor02Symm (I := I) g₀ P))) w x) ?_
    refine le_trans (mul_le_mul_of_nonneg_left
      (rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 0 4
        (ricciFoldWeightA (I := I) (M := M) g₀ (ccTensor02Symm (I := I) g₀ P) +
          ricciFoldWeightB (I := I) (M := M) g₀ (ccTensor02Symm (I := I) g₀ P)) w x) hfr_nn) ?_
    have hsplit : (iteratedCovGrad (I := I) g₀ 0 4 w
        (ricciFoldWeightA (I := I) (M := M) g₀ (ccTensor02Symm (I := I) g₀ P) +
          ricciFoldWeightB (I := I) (M := M) g₀ (ccTensor02Symm (I := I) g₀ P))).toSection x =
        (iteratedCovGrad (I := I) g₀ 0 4 w
          (ricciFoldWeightA (I := I) (M := M) g₀ (ccTensor02Symm (I := I) g₀ P))).toSection x +
        (iteratedCovGrad (I := I) g₀ 0 4 w
          (ricciFoldWeightB (I := I) (M := M) g₀ (ccTensor02Symm (I := I) g₀ P))).toSection x := by
      rw [iteratedCovGrad_add (I := I) g₀ 0 4 w _ _, SmoothCcTensor.toSection_add]
      rfl
    have hA := hCWA P hδ_le hδ0 hbound w (i + 1) (by omega) x
    have hB := hCWB P hδ_le hδ0 hbound w (i + 1) (by omega) x
    rw [show (ccOperatorFieldComp (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 (Equiv.swap (1 : Fin 6) 3)
          (ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 6
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀))
            (ccTensor02Symm (I := I) g₀ P)))) =
        ricciFoldWeightA (I := I) (M := M) g₀ (ccTensor02Symm (I := I) g₀ P) from rfl] at hA
    rw [show (ccOperatorFieldComp (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 ricciFoldWeightBPerm
          (ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 6
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀))
            (ccTensor02Symm (I := I) g₀ P)))) =
        ricciFoldWeightB (I := I) (M := M) g₀ (ccTensor02Symm (I := I) g₀ P) from rfl] at hB
    calc fr * (fr * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
          ((iteratedCovGrad (I := I) g₀ 0 4 w
            (ricciFoldWeightA (I := I) (M := M) g₀ (ccTensor02Symm (I := I) g₀ P) +
              ricciFoldWeightB (I := I) (M := M) g₀ (ccTensor02Symm (I := I) g₀ P))).toSection x))
        ≤ fr * (fr * (2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
            ((iteratedCovGrad (I := I) g₀ 0 4 w
              (ricciFoldWeightA (I := I) (M := M) g₀ (ccTensor02Symm (I := I) g₀ P))).toSection x)
          + 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
            ((iteratedCovGrad (I := I) g₀ 0 4 w
              (ricciFoldWeightB (I := I) (M := M) g₀ (ccTensor02Symm (I := I) g₀ P))).toSection x))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hfr_nn) hfr_nn
          rw [hsplit]
          exact riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (4 + w) x _ _
      _ ≤ fr * (fr * (2 * (CWA w * Combinatorics.boundedFactorGridWindow b (i + 1) (w + 1))
          + 2 * (CWB w * Combinatorics.boundedFactorGridWindow b (i + 1) (w + 1)))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hfr_nn) hfr_nn
          have hnnA := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (4 + w) x
            ((iteratedCovGrad (I := I) g₀ 0 4 w
              (ricciFoldWeightA (I := I) (M := M) g₀ (ccTensor02Symm (I := I) g₀ P))).toSection x)
          linarith [hA, hB]
      _ = CX w * Combinatorics.boundedFactorGridWindow b (i + 1) (w + 1) := by
          simp only [hCX_def]
          ring
  refine le_trans (mul_le_mul_of_nonneg_left
    (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le (I := I) (M := M) g₀ i 2 6 2
      (secondMetricPairTraceOp (I := I) (M := M) g₀ g₁)
      (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 ricciFoldRemainderSlotPerm
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2
          (ricciFoldWeightA (I := I) (M := M) g₀ (ccTensor02Symm (I := I) g₀ P) +
            ricciFoldWeightB (I := I) (M := M) g₀ (ccTensor02Symm (I := I) g₀ P)))) x)
    (by norm_num : (0 : ℝ) ≤ 1 / 4)) ?_
  have hW_nn : 0 ≤ Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) :=
    Combinatorics.boundedFactorGridWindow_nonneg b hb_nn _ _
  calc (1 / 4 : ℝ) * (diagonalGridGrowthFactor (E := E) i *
        ∑ u ∈ Finset.range (i + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + u) x
              ((iteratedCovGrad (I := I) g₀ 6 2 u
                (secondMetricPairTraceOp (I := I) (M := M) g₀ g₁)).toSection x) *
            ∑ w ∈ Finset.range (i + 1 - u),
              riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + w) x
                ((iteratedCovGrad (I := I) g₀ 2 6 w
                  (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 ricciFoldRemainderSlotPerm
                    (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                      (ricciFoldWeightA (I := I) (M := M) g₀ (ccTensor02Symm (I := I) g₀ P) +
                        ricciFoldWeightB (I := I) (M := M) g₀
                          (ccTensor02Symm (I := I) g₀ P))))).toSection x))
      ≤ (1 / 4 : ℝ) * (diagonalGridGrowthFactor (E := E) i *
          ∑ u ∈ Finset.range (i + 1),
            (CPT u * Combinatorics.boundedFactorGridWindow b (i + 1) (u + 1)) *
            ∑ w ∈ Finset.range (i + 1 - u),
              (CX w * Combinatorics.boundedFactorGridWindow b (i + 1) (w + 1))) := by
        refine mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun u hu => ?_)
            (appCcGdiag_nonneg (E := E) i)) (by norm_num)
        rw [Finset.mem_range] at hu
        refine mul_le_mul (hPT u (by omega)) (Finset.sum_le_sum fun w hw => ?_)
          (Finset.sum_nonneg fun w _ =>
            riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (6 + w) x _)
          (mul_nonneg (hCPT_nn u)
            (Combinatorics.boundedFactorGridWindow_nonneg b hb_nn _ _))
        rw [Finset.mem_range] at hw
        exact hWX w (by omega)
    _ ≤ (1 / 4 : ℝ) * ((diagonalGridGrowthFactor (E := E) i *
          ∑ u ∈ Finset.range (i + 1), CPT u *
            ∑ w ∈ Finset.range (i + 1 - u),
              CX w * Combinatorics.windowPairCellCount (u + 1) (w + 1)) *
          Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        rw [mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg (E := E) i)
        rw [Finset.sum_mul]
        refine Finset.sum_le_sum fun u hu => ?_
        rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_le_sum fun w hw => ?_
        rw [Finset.mem_range] at hu hw
        calc CPT u * Combinatorics.boundedFactorGridWindow b (i + 1) (u + 1) *
              (CX w * Combinatorics.boundedFactorGridWindow b (i + 1) (w + 1))
            = (CPT u * CX w) *
                (Combinatorics.boundedFactorGridWindow b (i + 1) (u + 1) *
                  Combinatorics.boundedFactorGridWindow b (i + 1) (w + 1)) := by ring
          _ ≤ (CPT u * CX w) *
                (Combinatorics.windowPairCellCount (u + 1) (w + 1) *
                  Combinatorics.boundedFactorGridWindow b (i + 1) ((u + 1) + (w + 1) - 1)) := by
              refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hCPT_nn u) (hCX_nn w))
              exact Combinatorics.boundedFactorGridWindow_mul_le b hb_nn (i + 1) (u + 1)
                (w + 1) (by omega) (by omega)
          _ ≤ (CPT u * CX w) *
                (Combinatorics.windowPairCellCount (u + 1) (w + 1) *
                  Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3)) := by
              refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hCPT_nn u) (hCX_nn w))
              refine mul_le_mul_of_nonneg_left ?_
                (Combinatorics.windowPairCellCount_nonneg _ _)
              exact Combinatorics.boundedFactorGridWindow_mono b hb_nn (le_refl _) (by omega)
          _ = CPT u * (CX w * Combinatorics.windowPairCellCount (u + 1) (w + 1)) *
                Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) := by ring
    _ = ((1 / 4 : ℝ) * (diagonalGridGrowthFactor (E := E) i *
          ∑ u ∈ Finset.range (i + 1), CPT u *
            ∑ w ∈ Finset.range (i + 1 - u),
              CX w * Combinatorics.windowPairCellCount (u + 1) (w + 1))) *
          Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) := by ring

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem appCcRS_smul_left_local (g : SmoothRiemannianMetric I M) (a b c : ℕ)
    (k : ℝ) (Φ : SmoothCcTensor g b c) (W : SmoothCcTensor g a b) :
    ccOperatorFieldComp (I := I) (M := M) g a b c (k • Φ) W =
      k • ccOperatorFieldComp (I := I) (M := M) g a b c Φ W := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((k • ccOperatorFieldComp (I := I) (M := M) g a b c Φ W).toSection x) =
      k • (ccOperatorFieldComp (I := I) (M := M) g a b c Φ W).toSection x from by
    rw [SmoothCcTensor.toSection_smul]; rfl]
  rw [appCcRS_toSection, appCcRS_toSection]
  rw [show ((k • Φ).toSection x : TensorRSSpace b c I x) = k • Φ.toSection x from by
    rw [SmoothCcTensor.toSection_smul]; rfl]
  rw [ContinuousLinearMap.smul_comp]

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
@[simp] private theorem appCcRS_ccSlotSwapField_involutive (g : SmoothRiemannianMetric I M)
    (C : SmoothCcTensor g 2 2) :
    ccOperatorFieldComp (I := I) (M := M) g 2 2 2
        (ccOperatorFieldComp (I := I) (M := M) g 2 2 2 C (ccInputSlotSwapField (I := I) (M := M) g))
        (ccInputSlotSwapField (I := I) (M := M) g) = C := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [appCcRS_toSection, appCcRS_toSection]
  apply ContinuousLinearMap.ext
  intro D
  simp only [ContinuousLinearMap.comp_apply]
  refine congrArg _ ?_
  change inputSlotSwapFib (I := I) (M := M) x (inputSlotSwapFib (I := I) (M := M) x D) = D
  rw [slotSwapFib_apply, slotSwapFib_apply, Tensor0SSpace.toModel_ofModel]
  rw [show ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
      (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
        (Tensor0SSpace.toModel (𝕜 := ℝ) D)) = Tensor0SSpace.toModel (𝕜 := ℝ) D from by
    ext m
    simp only [ContinuousMultilinearMap.domDomCongr_apply]
    congr 1
    funext i
    exact congrArg m (Equiv.swap_apply_self (0 : Fin 2) 1 i)]
  exact Tensor0SSpace.ofModel_toModel D


theorem rfns_iteratedCovGrad_bgRDiffRefoldRemainderFieldInputSymm_boundedFactorGridWindow_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (ccInputSlotSymm (I := I) (M := M) g₀
                (backgroundRicciCommutatorDiffRefoldRemainderField (I := I) (M := M) g₀ g₁))).toSection x) ≤
          C i * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3) := by
  classical
  obtain ⟨C₁, hC₁_nn, hC₁⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_ricciArmOrder0BgRCommCoeffFieldDifference_boundedFactorGridWindow_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨C₂, hC₂_nn, hC₂⟩ :=
    rfns_iteratedCovGrad_ricciArmSharpGradKoszulResidualFieldMetricDifference_boundedFactorGridWindow_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨C₃, hC₃_nn, hC₃⟩ :=
    rfns_iteratedCovGrad_ricciArmRicciFoldRemainderFieldMetricDifference_boundedFactorGridWindow_le
      (I := I) (M := M) g₀ hδ₀
  have hSW_ex : ∀ q : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + q) x
        ((iteratedCovGrad (I := I) g₀ 2 2 q
          (ccInputSlotSwapField (I := I) (M := M) g₀)).toSection x) ≤ c := fun q =>
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 2 (2 + q)
      (iteratedCovGrad (I := I) g₀ 2 2 q (ccInputSlotSwapField (I := I) (M := M) g₀))
  choose SW hSW_nn hSW using hSW_ex
  set CB : ℕ → ℝ := fun n => 4 * C₁ n + 4 * C₂ n + 2 * C₃ n with hCB_def
  have hCB_nn : ∀ n, 0 ≤ CB n := by
    intro n
    have h1 := hC₁_nn n
    have h2 := hC₂_nn n
    have h3 := hC₃_nn n
    simp only [hCB_def]
    linarith
  refine ⟨fun i => (1 / 2 : ℝ) * CB i +
      (1 / 2 : ℝ) * (diagonalGridGrowthFactor (E := E) i * (∑ i' ∈ Finset.range (i + 1), CB i') *
        (∑ l ∈ Finset.range (i + 1), SW l)), ?_, ?_⟩
  · intro i
    have h2 : 0 ≤ ∑ i' ∈ Finset.range (i + 1), CB i' := Finset.sum_nonneg fun i' _ => hCB_nn i'
    have h3 : 0 ≤ ∑ l ∈ Finset.range (i + 1), SW l := Finset.sum_nonneg fun l _ => hSW_nn l
    have h4 : 0 ≤ diagonalGridGrowthFactor (E := E) i := appCcGdiag_nonneg (E := E) i
    have h1 : 0 ≤ CB i := hCB_nn i
    positivity
  · intro g₁ P htie δ hδ_le hδ0 hbound i x
    set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
      ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) with hb_def
    have hb_nn : ∀ l, 0 ≤ b l :=
      fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
    set W : ℝ := Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) with hW_def
    have hW_nn : 0 ≤ W := Combinatorics.boundedFactorGridWindow_nonneg b hb_nn _ _
    set BD : SmoothCcTensor g₀ 2 2 :=
      (ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₁
          - ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₀)
        + (1 / 2 : ℝ) • ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀ g₁
            (metricDifferenceCcTensor (I := I) (M := M) g₀ g₁)
        - ricciArmRicciFoldRemainderField (I := I) (M := M) g₀ g₁
            (metricDifferenceCcTensor (I := I) (M := M) g₀ g₁) with hBD_def
    have hB : ∀ n : ℕ, n ≤ i →
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 2 2 n BD).toSection x) ≤
        CB n * W := by
      intro n hn
      have hwin : Combinatorics.boundedFactorGridWindow b (n + 1) (n + 3) ≤ W := by
        rw [hW_def]
        exact Combinatorics.boundedFactorGridWindow_mono b hb_nn (by omega) (by omega)
      have h1 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 2 2 n
            (ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₁
              - ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₀)).toSection x) ≤
          C₁ n * W :=
        le_trans (hC₁ g₁ P htie hδ_le hδ0 hbound n x)
          (mul_le_mul_of_nonneg_left hwin (hC₁_nn n))
      have h2 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 2 2 n
            (ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀ g₁
              (metricDifferenceCcTensor (I := I) (M := M) g₀ g₁))).toSection x) ≤
          C₂ n * W :=
        le_trans (hC₂ g₁ P htie hδ_le hδ0 hbound n x)
          (mul_le_mul_of_nonneg_left hwin (hC₂_nn n))
      have h3 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 2 2 n
            (ricciArmRicciFoldRemainderField (I := I) (M := M) g₀ g₁
              (metricDifferenceCcTensor (I := I) (M := M) g₀ g₁))).toSection x) ≤
          C₃ n * W :=
        le_trans (hC₃ g₁ P htie hδ_le hδ0 hbound n x)
          (mul_le_mul_of_nonneg_left hwin (hC₃_nn n))
      have h2' : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 2 2 n
            ((1 / 2 : ℝ) • ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀ g₁
              (metricDifferenceCcTensor (I := I) (M := M) g₀ g₁))).toSection x) ≤
          C₂ n * W := by
        rw [iteratedCovGrad_smul_real,
          show ((1 / 2 : ℝ) • iteratedCovGrad (I := I) g₀ 2 2 n
              (ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀ g₁
                (metricDifferenceCcTensor (I := I) (M := M) g₀ g₁))).toSection x =
            (1 / 2 : ℝ) • (iteratedCovGrad (I := I) g₀ 2 2 n
              (ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀ g₁
                (metricDifferenceCcTensor (I := I) (M := M) g₀ g₁))).toSection x from by
            rw [SmoothCcTensor.toSection_smul]; rfl,
          riemannianFiberNormSq_smul_value,
          show (1 / 2 : ℝ) ^ 2 = 1 / 4 from by norm_num]
        have hnn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 2 2 n
            (ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀ g₁
              (metricDifferenceCcTensor (I := I) (M := M) g₀ g₁))).toSection x)
        linarith [h2]
      have hsplit : (iteratedCovGrad (I := I) g₀ 2 2 n BD).toSection x =
          ((iteratedCovGrad (I := I) g₀ 2 2 n
            (ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₁
              - ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₀)).toSection x
          + (iteratedCovGrad (I := I) g₀ 2 2 n
              ((1 / 2 : ℝ) • ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀ g₁
                (metricDifferenceCcTensor (I := I) (M := M) g₀ g₁))).toSection x)
          - (iteratedCovGrad (I := I) g₀ 2 2 n
              (ricciArmRicciFoldRemainderField (I := I) (M := M) g₀ g₁
                (metricDifferenceCcTensor (I := I) (M := M) g₀ g₁))).toSection x := by
        rw [hBD_def, iteratedCovGrad_sub, iteratedCovGrad_add,
          SmoothCcTensor.toSection_sub, SmoothCcTensor.toSection_add]
        rfl
      rw [hsplit]
      have hsub := riemannianFiberNormSq_sub_le (I := I) (M := M) g₀ 2 (2 + n) x
        ((iteratedCovGrad (I := I) g₀ 2 2 n
          (ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₁
            - ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₀)).toSection x
        + (iteratedCovGrad (I := I) g₀ 2 2 n
            ((1 / 2 : ℝ) • ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀ g₁
              (metricDifferenceCcTensor (I := I) (M := M) g₀ g₁))).toSection x)
        ((iteratedCovGrad (I := I) g₀ 2 2 n
          (ricciArmRicciFoldRemainderField (I := I) (M := M) g₀ g₁
            (metricDifferenceCcTensor (I := I) (M := M) g₀ g₁))).toSection x)
      have hadd := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 (2 + n) x
        ((iteratedCovGrad (I := I) g₀ 2 2 n
          (ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₁
            - ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₀)).toSection x)
        ((iteratedCovGrad (I := I) g₀ 2 2 n
          ((1 / 2 : ℝ) • ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀ g₁
            (metricDifferenceCcTensor (I := I) (M := M) g₀ g₁))).toSection x)
      have hCBW : CB n * W = 4 * (C₁ n * W) + 4 * (C₂ n * W) + 2 * (C₃ n * W) := by
        simp only [hCB_def]
        ring
      refine le_trans hsub ?_
      rw [hCBW]
      linarith [hadd, h1, h2', h3]
    have hsubject : ccInputSlotSymm (I := I) (M := M) g₀
        (backgroundRicciCommutatorDiffRefoldRemainderField (I := I) (M := M) g₀ g₁) =
        (1 / 2 : ℝ) • (BD
          + ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 2 BD
            (ccInputSlotSwapField (I := I) (M := M) g₀)) := by
      rw [show ccInputSlotSymm (I := I) (M := M) g₀
          (backgroundRicciCommutatorDiffRefoldRemainderField (I := I) (M := M) g₀ g₁) =
          (1 / 2 : ℝ) • (backgroundRicciCommutatorDiffRefoldRemainderField (I := I) (M := M) g₀ g₁
            + ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 2
              (backgroundRicciCommutatorDiffRefoldRemainderField (I := I) (M := M) g₀ g₁)
              (ccInputSlotSwapField (I := I) (M := M) g₀)) from rfl]
      refine congrArg (fun t => (1 / 2 : ℝ) • t) ?_
      rw [hBD_def]
      rw [show backgroundRicciCommutatorDiffRefoldRemainderField (I := I) (M := M) g₀ g₁ =
          ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 2
              (ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₁
                - ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₀)
              (ccInputSlotSwapField (I := I) (M := M) g₀)
            + (1 / 2 : ℝ) • ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀ g₁
                (metricDifferenceCcTensor (I := I) (M := M) g₀ g₁)
            - ricciArmRicciFoldRemainderField (I := I) (M := M) g₀ g₁
                (metricDifferenceCcTensor (I := I) (M := M) g₀ g₁) from rfl]
      simp only [appCcRS_sub_left, appCcRS_add_left, appCcRS_smul_left_local,
        appCcRS_ccSlotSwapField_involutive]
      abel
    rw [hsubject]
    have hsm : (iteratedCovGrad (I := I) g₀ 2 2 i
        ((1 / 2 : ℝ) • (BD
          + ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 2 BD
            (ccInputSlotSwapField (I := I) (M := M) g₀)))).toSection x =
        (1 / 2 : ℝ) • ((iteratedCovGrad (I := I) g₀ 2 2 i
          (BD
            + ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 2 BD
              (ccInputSlotSwapField (I := I) (M := M) g₀))).toSection x) := by
      rw [iteratedCovGrad_smul_real (I := I) g₀ 2 2 i (1 / 2 : ℝ) _,
        SmoothCcTensor.toSection_smul]
      rfl
    rw [hsm, riemannianFiberNormSq_smul_value (I := I) (M := M) g₀ 2 (2 + i) x (1 / 2 : ℝ) _,
      show (1 / 2 : ℝ) ^ 2 = 1 / 4 from by norm_num]
    have hsplit2 : (iteratedCovGrad (I := I) g₀ 2 2 i
        (BD
          + ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 2 BD
            (ccInputSlotSwapField (I := I) (M := M) g₀))).toSection x =
        (iteratedCovGrad (I := I) g₀ 2 2 i BD).toSection x
        + (iteratedCovGrad (I := I) g₀ 2 2 i
            (ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 2 BD
              (ccInputSlotSwapField (I := I) (M := M) g₀))).toSection x := by
      rw [iteratedCovGrad_add (I := I) g₀ 2 2 i _ _, SmoothCcTensor.toSection_add]
      rfl
    rw [hsplit2]
    refine le_trans (mul_le_mul_of_nonneg_left
      (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 (2 + i) x _ _)
      (by norm_num : (0 : ℝ) ≤ 1 / 4)) ?_
    have hQi : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 2 i BD).toSection x) ≤ CB i * W :=
      hB i (le_refl i)
    have hApp : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 2 i
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 2 BD
            (ccInputSlotSwapField (I := I) (M := M) g₀))).toSection x) ≤
        diagonalGridGrowthFactor (E := E) i * ((∑ i' ∈ Finset.range (i + 1), CB i') *
          ((∑ l ∈ Finset.range (i + 1), SW l) * W)) := by
      refine le_trans (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le
        (I := I) (M := M) g₀ i 2 2 2 BD
        (ccInputSlotSwapField (I := I) (M := M) g₀) x) ?_
      refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg (E := E) i)
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun i' hi' => ?_
      rw [Finset.mem_range] at hi'
      have hswapsum : (∑ l ∈ Finset.range (i + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 2 2 l
              (ccInputSlotSwapField (I := I) (M := M) g₀)).toSection x)) ≤
          ∑ l ∈ Finset.range (i + 1), SW l := by
        refine le_trans (Finset.sum_le_sum fun l _ => hSW l x) ?_
        refine Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_mono (by omega)) ?_
        exact fun l _ _ => hSW_nn l
      have hBi' := hB i' (by omega)
      have hswap_nn : 0 ≤ ∑ l ∈ Finset.range (i + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 2 2 l
              (ccInputSlotSwapField (I := I) (M := M) g₀)).toSection x) :=
        Finset.sum_nonneg fun l _ =>
          riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (2 + l) x _
      calc riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i') x
              ((iteratedCovGrad (I := I) g₀ 2 2 i' BD).toSection x) *
            ∑ l ∈ Finset.range (i + 1 - i'),
              riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + l) x
                ((iteratedCovGrad (I := I) g₀ 2 2 l
                  (ccInputSlotSwapField (I := I) (M := M) g₀)).toSection x)
          ≤ (CB i' * W) * (∑ l ∈ Finset.range (i + 1), SW l) :=
            mul_le_mul hBi' hswapsum hswap_nn (mul_nonneg (hCB_nn i') hW_nn)
        _ = CB i' * ((∑ l ∈ Finset.range (i + 1), SW l) * W) := by ring
    calc (1 / 4 : ℝ) * (2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i BD).toSection x)
          + 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 2 BD
                (ccInputSlotSwapField (I := I) (M := M) g₀))).toSection x))
        ≤ (1 / 4 : ℝ) * (2 * (CB i * W)
            + 2 * (diagonalGridGrowthFactor (E := E) i * ((∑ i' ∈ Finset.range (i + 1), CB i') *
              ((∑ l ∈ Finset.range (i + 1), SW l) * W)))) := by
          nlinarith [hQi, hApp]
      _ = ((1 / 2 : ℝ) * CB i +
            (1 / 2 : ℝ) * (diagonalGridGrowthFactor (E := E) i * (∑ i' ∈ Finset.range (i + 1), CB i') *
              (∑ l ∈ Finset.range (i + 1), SW l))) * W := by ring

section qCommConversion

section NormedQCommConversion

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

open DifferentialGeometry.Analysis.Sobolev.TensorHilbert

variable (g₀ g₁ : SmoothRiemannianMetric I M)

omit [NeZero (Module.finrank ℝ E)] [TopologicalSpace M] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma toModel_vec3_slot1_sum_smul (_x : M)
    (Zm : Tensor0SModel 3 ℝ E) (d : ℕ) (t : Fin d → ℝ) (u : Fin d → E) (a b : E) :
    Zm ![a, ∑ c, t c • u c, b] = ∑ c, t c * Zm ![a, u c, b] := by
  classical
  have h1 : ∀ v : E, (![a, v, b] : Fin 3 → E) = Function.update ![a, (0 : E), b] 1 v := by
    intro v
    funext k
    fin_cases k <;> simp [Function.update]
  have hgen : ∀ ss : Finset (Fin d),
      Zm (Function.update ![a, (0 : E), b] 1 (∑ c ∈ ss, t c • u c)) =
        ∑ c ∈ ss, t c * Zm (Function.update ![a, (0 : E), b] 1 (u c)) := by
    intro ss
    induction ss using Finset.induction_on with
    | empty =>
        rw [Finset.sum_empty, Finset.sum_empty]
        rw [show (0 : E) = ((0 : ℝ) • (0 : E)) from (zero_smul ℝ (0 : E)).symm]
        rw [ContinuousMultilinearMap.map_update_smul]
        rw [zero_smul]
    | @insert a' ss ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha]
        rw [ContinuousMultilinearMap.map_update_add]
        rw [ih]
        congr 1
        rw [ContinuousMultilinearMap.map_update_smul]
        rw [smul_eq_mul]
  have h2 := hgen Finset.univ
  rw [h1, h2]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← h1 (u c)]

private def sigmaQ1 : Equiv.Perm (Fin 6) :=
  ⟨fun i => (![5, 4, 0, 3, 1, 2] : Fin 6 → Fin 6) i,
   fun i => (![2, 4, 5, 3, 1, 0] : Fin 6 → Fin 6) i,
   by decide, by decide⟩

private def sigmaQ2 : Equiv.Perm (Fin 6) :=
  ⟨fun i => (![5, 2, 0, 3, 1, 4] : Fin 6 → Fin 6) i,
   fun i => (![2, 4, 1, 3, 5, 0] : Fin 6 → Fin 6) i,
   by decide, by decide⟩

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 12800000 in
private lemma qCommFoldWeights_unitModel_eq_kernel (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
    (x : M) (p q v0 v1 : TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 4
        (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ1 P -
          koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ2 P) x
        ![(v0 : E), (v1 : E), (p : E), (q : E)] =
      connDiffIteratedCommKernelBilin (I := I) g₀ g₁ x p q v0 v1 := by
  classical
  have hM1 : unitModel (I := I) (M := M) g₀ 4
      (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ1 P) x
      ![(v0 : E), (v1 : E), (p : E), (q : E)] =
      ∑ e : Fin (Module.finrank ℝ E),
        g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q p)
            (smoothOrthoFrame (I := I) g₀ x e x) *
          unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
            ![(v1 : E),
              ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E),
              (v0 : E)] := by
    rw [show koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ1 P =
        ccOperatorFieldComp (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 sigmaQ1
            (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
              (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovecCc (I := I) g₀ P))
              (connDiffLoweredCc (I := I) g₀ g₁))) from rfl]
    rw [koszulConnDiffFoldWeight_unitModel_general (I := I) (M := M) g₀ g₁ sigmaQ1 P x
      ![(v0 : E), (v1 : E), (p : E), (q : E)]]
    refine Finset.sum_congr rfl fun e _ => ?_
    have h1 : unitModel (I := I) (M := M) g₀ 3 (connDiffLoweredCc (I := I) g₀ g₁) x
        ![((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (sigmaQ1 0)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (sigmaQ1 1)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (sigmaQ1 2))] =
        unitModel (I := I) (M := M) g₀ 3 (connDiffLoweredCc (I := I) g₀ g₁) x
          ![(q : E), (p : E),
            ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)] := by
      refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl
    have h2 : unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
        ![((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (sigmaQ1 3)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (sigmaQ1 4)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (sigmaQ1 5))] =
        unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
          ![(v1 : E),
            ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E),
            (v0 : E)] := by
      refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl
    rw [h1, h2]
    congr 1
    have h12 := connDiffLowered_unitModel_value (I := I) (M := M) g₀ g₁ x
      ![q, p, smoothOrthoFrame (I := I) g₀ x e x]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons] at h12
    exact h12
  have hM2 : unitModel (I := I) (M := M) g₀ 4
      (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ2 P) x
      ![(v0 : E), (v1 : E), (p : E), (q : E)] =
      ∑ e : Fin (Module.finrank ℝ E),
        g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q v0)
            (smoothOrthoFrame (I := I) g₀ x e x) *
          unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
            ![(v1 : E),
              ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E),
              (p : E)] := by
    rw [show koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ2 P =
        ccOperatorFieldComp (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 sigmaQ2
            (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
              (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovecCc (I := I) g₀ P))
              (connDiffLoweredCc (I := I) g₀ g₁))) from rfl]
    rw [koszulConnDiffFoldWeight_unitModel_general (I := I) (M := M) g₀ g₁ sigmaQ2 P x
      ![(v0 : E), (v1 : E), (p : E), (q : E)]]
    refine Finset.sum_congr rfl fun e _ => ?_
    have h1 : unitModel (I := I) (M := M) g₀ 3 (connDiffLoweredCc (I := I) g₀ g₁) x
        ![((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (sigmaQ2 0)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (sigmaQ2 1)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (sigmaQ2 2))] =
        unitModel (I := I) (M := M) g₀ 3 (connDiffLoweredCc (I := I) g₀ g₁) x
          ![(q : E), (v0 : E),
            ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)] := by
      refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl
    have h2 : unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
        ![((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (sigmaQ2 3)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (sigmaQ2 4)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (sigmaQ2 5))] =
        unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
          ![(v1 : E),
            ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E),
            (p : E)] := by
      refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl
    rw [h1, h2]
    congr 1
    have h12 := connDiffLowered_unitModel_value (I := I) (M := M) g₀ g₁ x
      ![q, v0, smoothOrthoFrame (I := I) g₀ x e x]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons] at h12
    exact h12
  have hexp : ∀ r s : TangentSpace I x,
      ((PDE.DeTurck.connDiff (I := I) g₁ g₀ x r s : TangentSpace I x) : E) =
        ∑ e : Fin (Module.finrank ℝ E),
          g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x r s)
            (smoothOrthoFrame (I := I) g₀ x e x) •
          ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E) := by
    intro r s
    rw [show (∑ e : Fin (Module.finrank ℝ E),
        g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x r s)
          (smoothOrthoFrame (I := I) g₀ x e x) •
        ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)) =
        ((∑ e : Fin (Module.finrank ℝ E),
          g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x r s)
            (smoothOrthoFrame (I := I) g₀ x e x) •
          smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E) from rfl]
    conv_lhs => rw [orthoFrame_expansion_at_center (I := I) (M := M) g₀ x
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x r s)]
  have hT1 : g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q p) v0) v1 =
      ∑ e : Fin (Module.finrank ℝ E),
        g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q p)
            (smoothOrthoFrame (I := I) g₀ x e x) *
          unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
            ![(v1 : E),
              ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E),
              (v0 : E)] := by
    rw [← koszulCovecCc_unitModel_eq_connDiff_g1_inner (I := I) (M := M) g₀ g₁ P htie x
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q p) v0 v1]
    conv_lhs => rw [hexp q p]
    exact toModel_vec3_slot1_sum_smul (E := E) x
      (unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x)
      (Module.finrank ℝ E)
      (fun e => g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q p)
        (smoothOrthoFrame (I := I) g₀ x e x))
      (fun e => ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E))
      ((v1 : TangentSpace I x) : E) ((v0 : TangentSpace I x) : E)
  have hT2 : g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q v0) p) v1 =
      ∑ e : Fin (Module.finrank ℝ E),
        g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q v0)
            (smoothOrthoFrame (I := I) g₀ x e x) *
          unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
            ![(v1 : E),
              ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E),
              (p : E)] := by
    rw [← koszulCovecCc_unitModel_eq_connDiff_g1_inner (I := I) (M := M) g₀ g₁ P htie x
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q v0) p v1]
    conv_lhs => rw [hexp q v0]
    exact toModel_vec3_slot1_sum_smul (E := E) x
      (unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x)
      (Module.finrank ℝ E)
      (fun e => g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q v0)
        (smoothOrthoFrame (I := I) g₀ x e x))
      (fun e => ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E))
      ((v1 : TangentSpace I x) : E) ((p : TangentSpace I x) : E)
  rw [unitModel_sub_pt (I := I) (M := M) g₀ 4
    (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ1 P)
    (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ2 P) x]
  rw [ContinuousMultilinearMap.sub_apply]
  rw [hM1, hM2]
  rw [connDiffAACommKernelBilin_apply (I := I) g₀ g₁ x p q v0 v1]
  rw [hT1, hT2]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 12800000 in
private lemma ricciArmOrder0AACommCoeffField_eq_refold (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w) :
    ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁ =
      ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 (secondMetricPairTraceOp (I := I) (M := M) g₀ g₁)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 ricciFoldRemainderSlotPerm
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ1 P -
              koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ2 P))) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply tensorRSSpace_ext 2 2 x
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  beta_reduce
  rw [mvPairTraceOp_apply_toModel (I := I) (M := M) g₀ g₁
    (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ1 P -
      koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ2 P) x D v]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁).toSection x) D) =
      connDiffAACommBiContrFib (I := I) g₀ g₁ x D from rfl]
  rw [connDiffAACommBiContrFib_toModel (I := I) g₀ g₁ x D v]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [show unitModel (I := I) (M := M) g₀ 4
      (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ1 P -
        koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ2 P) x
      ![v 0, v 1, (smoothOrthoFrame (I := I) g₁ x a x : E),
        (smoothOrthoFrame (I := I) g₁ x b x : E)] =
      connDiffIteratedCommKernelBilin (I := I) g₀ g₁ x
        (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x)
        (v 0) (v 1) from
    qCommFoldWeights_unitModel_eq_kernel (I := I) (M := M) g₀ g₁ P htie x
      (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x)
      (v 0) (v 1)]

lemma exists_riemannianFiberNormSq_iteratedCovGrad_ricciArmOrder0AACommCoeffField_window
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁)).toSection x) ≤
          C i * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3) := by
  classical
  obtain ⟨CPT, hCPT_nn, hCPT⟩ :=
    exists_rfns_icg_mvPairTraceOp_window (I := I) (M := M) g₀ hδ₀
  obtain ⟨CW1, hCW1_nn, hCW1⟩ :=
    exists_riemannianFiberNormSq_iteratedCovGrad_koszulConnDiffFoldWeightGeneral_boundedFactorGridWindow_le (I := I) (M := M) g₀ sigmaQ1 hδ₀
  obtain ⟨CW2, hCW2_nn, hCW2⟩ :=
    exists_riemannianFiberNormSq_iteratedCovGrad_koszulConnDiffFoldWeightGeneral_boundedFactorGridWindow_le (I := I) (M := M) g₀ sigmaQ2 hδ₀
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : 0 ≤ fr := Nat.cast_nonneg _
  set CX : ℕ → ℝ := fun w => fr ^ 2 * (2 * CW1 w + 2 * CW2 w) with hCX_def
  have hCX_nn : ∀ w, 0 ≤ CX w := fun w => by
    have h1 := hCW1_nn w
    have h2 := hCW2_nn w
    have h5 : (0 : ℝ) ≤ fr ^ 2 := by positivity
    simp only [hCX_def]
    nlinarith
  refine ⟨fun i => diagonalGridGrowthFactor (E := E) i *
      ∑ u ∈ Finset.range (i + 1), CPT u *
        ∑ w ∈ Finset.range (i + 1 - u),
          CX w * Combinatorics.windowPairCellCount (u + 1) (w + 3),
    fun i => mul_nonneg (appCcGdiag_nonneg (E := E) i)
      (Finset.sum_nonneg fun u _ => mul_nonneg (hCPT_nn u)
        (Finset.sum_nonneg fun w _ => mul_nonneg (hCX_nn w)
          (Combinatorics.windowPairCellCount_nonneg _ _))), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hbound i x
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) with hb_def
  have hb_nn : ∀ l, 0 ≤ b l :=
    fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  rw [ricciArmOrder0AACommCoeffField_eq_refold (I := I) (M := M) g₀ g₁ P htie]
  have hPT : ∀ u : ℕ, u ≤ i →
      riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + u) x
          ((iteratedCovGrad (I := I) g₀ 6 2 u
            (secondMetricPairTraceOp (I := I) (M := M) g₀ g₁)).toSection x) ≤
        CPT u * Combinatorics.boundedFactorGridWindow b (i + 1) (u + 1) :=
    fun u hu => hCPT g₁ P htie hδ_le hδ0 hbound u (i + 1) (by omega) x
  have hWX : ∀ w : ℕ, w ≤ i →
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + w) x
          ((iteratedCovGrad (I := I) g₀ 2 6 w
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 ricciFoldRemainderSlotPerm
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ1 P -
                  koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ2 P)))).toSection x) ≤
        CX w * Combinatorics.boundedFactorGridWindow b (i + 1) (w + 3) := by
    intro w hw
    rw [riemannianFiberNormSq_iteratedCovGrad_rsDomDomCongrSection_eq (I := I) (M := M) g₀ 2 6 ricciFoldRemainderSlotPerm _ w x]
    rw [show slotExtendIter (I := I) (M := M) g₀ 0 4 2
        (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ1 P -
          koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ2 P) =
        slotExtend (I := I) (M := M) g₀ 1 5 (slotExtend (I := I) (M := M) g₀ 0 4
          (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ1 P -
            koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ2 P)) from rfl]
    refine le_trans (rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 1 5
      (slotExtend (I := I) (M := M) g₀ 0 4
        (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ1 P -
          koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ2 P)) w x) ?_
    refine le_trans (mul_le_mul_of_nonneg_left
      (rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 0 4
        (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ1 P -
          koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ2 P) w x) hfr_nn) ?_
    have hsub : (iteratedCovGrad (I := I) g₀ 0 4 w
        (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ1 P -
          koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ2 P)).toSection x =
        (iteratedCovGrad (I := I) g₀ 0 4 w
          (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ1 P)).toSection x -
        (iteratedCovGrad (I := I) g₀ 0 4 w
          (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ2 P)).toSection x := by
      rw [sub_eq_add_neg (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ1 P)
        (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ2 P)]
      rw [iteratedCovGrad_add (I := I) g₀ 0 4 w _ _,
        iteratedCovGrad_neg (I := I) g₀ 0 4 w _, SmoothCcTensor.toSection_add]
      rw [show (((iteratedCovGrad (I := I) g₀ 0 4 w
            (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ1 P)).toSection +
          (-(iteratedCovGrad (I := I) g₀ 0 4 w
            (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ2 P))).toSection) x) =
          (iteratedCovGrad (I := I) g₀ 0 4 w
            (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ1 P)).toSection x +
          (-(iteratedCovGrad (I := I) g₀ 0 4 w
            (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ2 P))).toSection x from rfl]
      rw [show ((-(iteratedCovGrad (I := I) g₀ 0 4 w
          (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ2 P))).toSection x) =
          -((iteratedCovGrad (I := I) g₀ 0 4 w
            (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ2 P)).toSection x) from by
        rw [SmoothCcTensor.toSection_neg]; rfl]
      rw [← sub_eq_add_neg]
    have hA1 := hCW1 g₁ P htie hδ_le hδ0 hbound w (i + 1) (by omega) x
    rw [show ccOperatorFieldComp (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 sigmaQ1
          (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
            (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovecCc (I := I) g₀ P))
            (connDiffLoweredCc (I := I) g₀ g₁))) =
        koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ1 P from rfl] at hA1
    have hA2 := hCW2 g₁ P htie hδ_le hδ0 hbound w (i + 1) (by omega) x
    rw [show ccOperatorFieldComp (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 sigmaQ2
          (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
            (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovecCc (I := I) g₀ P))
            (connDiffLoweredCc (I := I) g₀ g₁))) =
        koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ2 P from rfl] at hA2
    calc fr * (fr * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
          ((iteratedCovGrad (I := I) g₀ 0 4 w
            (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ1 P -
              koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ2 P)).toSection x))
        ≤ fr * (fr * (2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
            ((iteratedCovGrad (I := I) g₀ 0 4 w
              (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ1 P)).toSection x)
          + 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
            ((iteratedCovGrad (I := I) g₀ 0 4 w
              (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ2 P)).toSection x))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hfr_nn) hfr_nn
          rw [hsub]
          exact riemannianFiberNormSq_sub_le_pt (I := I) (M := M) g₀ 0 (4 + w) x _ _
      _ ≤ fr * (fr *
          (2 * (CW1 w * Combinatorics.boundedFactorGridWindow b (i + 1) (w + 3))
            + 2 * (CW2 w * Combinatorics.boundedFactorGridWindow b (i + 1) (w + 3)))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hfr_nn) hfr_nn
          linarith [hA1, hA2]
      _ = CX w * Combinatorics.boundedFactorGridWindow b (i + 1) (w + 3) := by
          simp only [hCX_def]
          ring
  refine le_trans (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le (I := I)
    (M := M) g₀ i 2 6 2 (secondMetricPairTraceOp (I := I) (M := M) g₀ g₁)
    (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 ricciFoldRemainderSlotPerm
      (slotExtendIter (I := I) (M := M) g₀ 0 4 2
        (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ1 P -
          koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ2 P))) x) ?_
  calc diagonalGridGrowthFactor (E := E) i *
        ∑ u ∈ Finset.range (i + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + u) x
              ((iteratedCovGrad (I := I) g₀ 6 2 u
                (secondMetricPairTraceOp (I := I) (M := M) g₀ g₁)).toSection x) *
            ∑ w ∈ Finset.range (i + 1 - u),
              riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + w) x
                ((iteratedCovGrad (I := I) g₀ 2 6 w
                  (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 ricciFoldRemainderSlotPerm
                    (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                      (koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁ sigmaQ1 P -
                        koszulConnDiffFoldWeight (I := I) (M := M) g₀ g₁
                          sigmaQ2 P)))).toSection x)
      ≤ diagonalGridGrowthFactor (E := E) i *
          ∑ u ∈ Finset.range (i + 1),
            (CPT u * Combinatorics.boundedFactorGridWindow b (i + 1) (u + 1)) *
            ∑ w ∈ Finset.range (i + 1 - u),
              (CX w * Combinatorics.boundedFactorGridWindow b (i + 1) (w + 3)) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun u hu => ?_)
          (appCcGdiag_nonneg (E := E) i)
        rw [Finset.mem_range] at hu
        refine mul_le_mul (hPT u (by omega)) (Finset.sum_le_sum fun w hw => ?_)
          (Finset.sum_nonneg fun w _ =>
            riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (6 + w) x _)
          (mul_nonneg (hCPT_nn u)
            (Combinatorics.boundedFactorGridWindow_nonneg b hb_nn _ _))
        rw [Finset.mem_range] at hw
        exact hWX w (by omega)
    _ ≤ (diagonalGridGrowthFactor (E := E) i *
          ∑ u ∈ Finset.range (i + 1), CPT u *
            ∑ w ∈ Finset.range (i + 1 - u),
              CX w * Combinatorics.windowPairCellCount (u + 1) (w + 3)) *
          Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) := by
        rw [mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg (E := E) i)
        rw [Finset.sum_mul]
        refine Finset.sum_le_sum fun u hu => ?_
        rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_le_sum fun w hw => ?_
        rw [Finset.mem_range] at hu hw
        calc CPT u * Combinatorics.boundedFactorGridWindow b (i + 1) (u + 1) *
              (CX w * Combinatorics.boundedFactorGridWindow b (i + 1) (w + 3))
            = (CPT u * CX w) *
                (Combinatorics.boundedFactorGridWindow b (i + 1) (u + 1) *
                  Combinatorics.boundedFactorGridWindow b (i + 1) (w + 3)) := by ring
          _ ≤ (CPT u * CX w) *
                (Combinatorics.windowPairCellCount (u + 1) (w + 3) *
                  Combinatorics.boundedFactorGridWindow b (i + 1)
                    ((u + 1) + (w + 3) - 1)) := by
              refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hCPT_nn u) (hCX_nn w))
              exact Combinatorics.boundedFactorGridWindow_mul_le b hb_nn (i + 1) (u + 1)
                (w + 3) (by omega) (by omega)
          _ ≤ (CPT u * CX w) *
                (Combinatorics.windowPairCellCount (u + 1) (w + 3) *
                  Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3)) := by
              refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hCPT_nn u) (hCX_nn w))
              refine mul_le_mul_of_nonneg_left ?_
                (Combinatorics.windowPairCellCount_nonneg _ _)
              exact Combinatorics.boundedFactorGridWindow_mono b hb_nn (le_refl _) (by omega)
          _ = CPT u * (CX w * Combinatorics.windowPairCellCount (u + 1) (w + 3)) *
                Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) := by ring

end NormedQCommConversion

end qCommConversion

section NormedAACommInputSymmetrization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E


theorem rfns_iteratedCovGrad_ricciArmOrder0AACommCoeffFieldInputSymm_boundedFactorGridWindow_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (ccInputSlotSymm (I := I) (M := M) g₀
                (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁))).toSection x) ≤
          C i * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3) := by
  classical
  obtain ⟨Cq, hCq_nn, hCq⟩ :=
    exists_riemannianFiberNormSq_iteratedCovGrad_ricciArmOrder0AACommCoeffField_window (I := I) (M := M) g₀ hδ₀
  have hSW_ex : ∀ q : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + q) x
        ((iteratedCovGrad (I := I) g₀ 2 2 q
          (ccInputSlotSwapField (I := I) (M := M) g₀)).toSection x) ≤ c := fun q =>
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 2 (2 + q)
      (iteratedCovGrad (I := I) g₀ 2 2 q (ccInputSlotSwapField (I := I) (M := M) g₀))
  choose SW hSW_nn hSW using hSW_ex
  refine ⟨fun i => (1 / 2 : ℝ) * Cq i +
      (1 / 2 : ℝ) * (diagonalGridGrowthFactor (E := E) i * (∑ i' ∈ Finset.range (i + 1), Cq i') *
        (∑ l ∈ Finset.range (i + 1), SW l)), ?_, ?_⟩
  · intro i
    have h2 : 0 ≤ ∑ i' ∈ Finset.range (i + 1), Cq i' := Finset.sum_nonneg fun i' _ => hCq_nn i'
    have h3 : 0 ≤ ∑ l ∈ Finset.range (i + 1), SW l := Finset.sum_nonneg fun l _ => hSW_nn l
    have h4 : 0 ≤ diagonalGridGrowthFactor (E := E) i := appCcGdiag_nonneg (E := E) i
    have h1 : 0 ≤ Cq i := hCq_nn i
    positivity
  · intro g₁ P htie δ hδ_le hδ0 hbound i x
    set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
      ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) with hb_def
    have hb_nn : ∀ l, 0 ≤ b l :=
      fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
    set W : ℝ := Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) with hW_def
    have hW_nn : 0 ≤ W := Combinatorics.boundedFactorGridWindow_nonneg b hb_nn _ _
    have hQ : ∀ n : ℕ, n ≤ i →
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 2 2 n
            (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁)).toSection x) ≤
        Cq n * W := by
      intro n hn
      refine le_trans (hCq g₁ P htie hδ_le hδ0 hbound n x) ?_
      refine mul_le_mul_of_nonneg_left ?_ (hCq_nn n)
      rw [hW_def]
      exact Combinatorics.boundedFactorGridWindow_mono b hb_nn (by omega) (by omega)
    have hsubject : ccInputSlotSymm (I := I) (M := M) g₀
        (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁) =
        (1 / 2 : ℝ) • (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁
          + ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 2
            (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁)
            (ccInputSlotSwapField (I := I) (M := M) g₀)) := rfl
    rw [hsubject]
    have hsm : (iteratedCovGrad (I := I) g₀ 2 2 i
        ((1 / 2 : ℝ) • (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁
          + ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 2
            (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁)
            (ccInputSlotSwapField (I := I) (M := M) g₀)))).toSection x =
        (1 / 2 : ℝ) • ((iteratedCovGrad (I := I) g₀ 2 2 i
          (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁
            + ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 2
              (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁)
              (ccInputSlotSwapField (I := I) (M := M) g₀))).toSection x) := by
      rw [iteratedCovGrad_smul_real (I := I) g₀ 2 2 i (1 / 2 : ℝ) _,
        SmoothCcTensor.toSection_smul]
      rfl
    rw [hsm, riemannianFiberNormSq_smul_value (I := I) (M := M) g₀ 2 (2 + i) x (1 / 2 : ℝ) _,
      show (1 / 2 : ℝ) ^ 2 = 1 / 4 from by norm_num]
    have hsplit : (iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁
          + ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 2
            (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁)
            (ccInputSlotSwapField (I := I) (M := M) g₀))).toSection x =
        (iteratedCovGrad (I := I) g₀ 2 2 i
          (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁)).toSection x
        + (iteratedCovGrad (I := I) g₀ 2 2 i
            (ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 2
              (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁)
              (ccInputSlotSwapField (I := I) (M := M) g₀))).toSection x := by
      rw [iteratedCovGrad_add (I := I) g₀ 2 2 i _ _, SmoothCcTensor.toSection_add]
      rfl
    rw [hsplit]
    refine le_trans (mul_le_mul_of_nonneg_left
      (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 (2 + i) x _ _)
      (by norm_num : (0 : ℝ) ≤ 1 / 4)) ?_
    have hQi : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 2 i
          (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁)).toSection x) ≤
        Cq i * W :=
      hQ i (le_refl i)
    have hApp : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 2 i
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 2
            (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁)
            (ccInputSlotSwapField (I := I) (M := M) g₀))).toSection x) ≤
        diagonalGridGrowthFactor (E := E) i * ((∑ i' ∈ Finset.range (i + 1), Cq i') *
          ((∑ l ∈ Finset.range (i + 1), SW l) * W)) := by
      refine le_trans (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le
        (I := I) (M := M) g₀ i 2 2 2
        (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁)
        (ccInputSlotSwapField (I := I) (M := M) g₀) x) ?_
      refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg (E := E) i)
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun i' hi' => ?_
      rw [Finset.mem_range] at hi'
      have hswapsum : (∑ l ∈ Finset.range (i + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 2 2 l
              (ccInputSlotSwapField (I := I) (M := M) g₀)).toSection x)) ≤
          ∑ l ∈ Finset.range (i + 1), SW l := by
        refine le_trans (Finset.sum_le_sum fun l _ => hSW l x) ?_
        refine Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_mono (by omega)) ?_
        exact fun l _ _ => hSW_nn l
      have hQi' := hQ i' (by omega)
      have hswap_nn : 0 ≤ ∑ l ∈ Finset.range (i + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 2 2 l
              (ccInputSlotSwapField (I := I) (M := M) g₀)).toSection x) :=
        Finset.sum_nonneg fun l _ =>
          riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (2 + l) x _
      calc riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i') x
              ((iteratedCovGrad (I := I) g₀ 2 2 i'
                (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁)).toSection x) *
            ∑ l ∈ Finset.range (i + 1 - i'),
              riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + l) x
                ((iteratedCovGrad (I := I) g₀ 2 2 l
                  (ccInputSlotSwapField (I := I) (M := M) g₀)).toSection x)
          ≤ (Cq i' * W) * (∑ l ∈ Finset.range (i + 1), SW l) :=
            mul_le_mul hQi' hswapsum hswap_nn (mul_nonneg (hCq_nn i') hW_nn)
        _ = Cq i' * ((∑ l ∈ Finset.range (i + 1), SW l) * W) := by ring
    calc (1 / 4 : ℝ) * (2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁)).toSection x)
          + 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 2
                (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁)
                (ccInputSlotSwapField (I := I) (M := M) g₀))).toSection x))
        ≤ (1 / 4 : ℝ) * (2 * (Cq i * W)
            + 2 * (diagonalGridGrowthFactor (E := E) i * ((∑ i' ∈ Finset.range (i + 1), Cq i') *
              ((∑ l ∈ Finset.range (i + 1), SW l) * W)))) := by
          nlinarith [hQi, hApp]
      _ = ((1 / 2 : ℝ) * Cq i +
            (1 / 2 : ℝ) * (diagonalGridGrowthFactor (E := E) i * (∑ i' ∈ Finset.range (i + 1), Cq i') *
              (∑ l ∈ Finset.range (i + 1), SW l))) * W := by ring

end NormedAACommInputSymmetrization

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000

open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

set_option maxHeartbeats 3200000 in

omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem refoldKernelContractionMonomialField_eq_mvPairTraceRefold
    (g₀ g₁ : SmoothRiemannianMetric I M) (G : SmoothCcTensor g₀ 0 4)
    (σ : Equiv.Perm (Fin 4)) :
    refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁ G σ =
      ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 (secondMetricPairTraceOp (I := I) (M := M) g₀ g₁)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 ricciFoldRemainderSlotPerm
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (domDomCongrSection (I := I) g₀
              (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ) G))) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  refine tensorRSSpace_ext 2 2 x (fun D => ?_)
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun v => ?_)
  rw [mvPairTraceOp_apply_toModel (I := I) (M := M) g₀ g₁
    (domDomCongrSection (I := I) g₀
      (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ) G) x D v]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁ G σ).toSection x) D) =
      curvatureRefoldMonomialOrthonormalFrameBiContraction (I := I) (M := M) g₁
        (ccTensorRank4EvalAtUnitZeroSec (I := I) (M := M) g₀ G) σ x D from rfl]
  rw [curvatureRefoldMonomialOrthonormalFrameBiContraction,
    refoldKernelContractionMonomialFibFixedFrame_toModel]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  refine Finset.sum_congr rfl (fun a _ => ?_)
  refine congrArg₂ (· * ·) rfl ?_
  rw [domDomCongrSection_unitModel (I := I) g₀
    (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ) G x,
    ContinuousMultilinearMap.domDomCongr_apply]
  rw [show unitModel (I := I) (M := M) g₀ 4 G x =
      Tensor0SSpace.toModel (𝕜 := ℝ)
        (ccTensorRank4EvalAtUnitZeroSec (I := I) (M := M) g₀ G x) from rfl]
  refine congrArg _ ?_
  funext j
  rw [show ((Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ) j) =
      ((Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) (σ j)) from rfl]
  have hcons : ∀ k : Fin 4,
      (Fin.cons ((smoothOrthoFrame (I := I) g₁ x a x : TangentSpace I x) : E)
        (Fin.cons ((smoothOrthoFrame (I := I) g₁ x b x : TangentSpace I x) : E) v) :
          Fin 4 → E) k =
      (![v 0, v 1, (smoothOrthoFrame (I := I) g₁ x a x : E),
        (smoothOrthoFrame (I := I) g₁ x b x : E)] : Fin 4 → E)
        ((Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) k) := by
    intro k
    fin_cases k <;>
      simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_def] <;> rfl
  exact hcons (σ j)

private theorem exists_rfns_icg_refoldKernelContractionMonomialField_window
    (g₀ : SmoothRiemannianMetric I M) (σ : Equiv.Perm (Fin 4)) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁
                (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P))
                σ)).toSection x) ≤
          C i * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 2) (i + 3) := by
  classical
  obtain ⟨CPT, hCPT_nn, hCPT⟩ :=
    exists_rfns_icg_mvPairTraceOp_window (I := I) (M := M) g₀ hδ₀
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : 0 ≤ fr := Nat.cast_nonneg _
  refine ⟨fun i => diagonalGridGrowthFactor (E := E) i *
      ∑ n ∈ Finset.range (i + 1), CPT n * ∑ l ∈ Finset.range (i + 1 - n), fr ^ 2,
    fun i => mul_nonneg (appCcGdiag_nonneg (E := E) i)
      (Finset.sum_nonneg fun n _ => mul_nonneg (hCPT_nn n)
        (Finset.sum_nonneg fun l _ => by positivity)), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hbound i x
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) with hb_def
  have hb_nn : ∀ l, 0 ≤ b l :=
    fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  rw [refoldKernelContractionMonomialField_eq_mvPairTraceRefold (I := I) (M := M) g₀ g₁
    (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P)) σ]
  refine le_trans (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le
    (I := I) (M := M) g₀ i 2 6 2 (secondMetricPairTraceOp (I := I) (M := M) g₀ g₁)
    (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 ricciFoldRemainderSlotPerm
      (slotExtendIter (I := I) (M := M) g₀ 0 4 2
        (domDomCongrSection (I := I) g₀
          (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ)
          (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P))))) x) ?_
  have hPT : ∀ n : ℕ, n ≤ i →
      riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 6 2 n
            (secondMetricPairTraceOp (I := I) (M := M) g₀ g₁)).toSection x) ≤
        CPT n * Combinatorics.boundedFactorGridWindow b (i + 2) (n + 1) :=
    fun n hn => hCPT g₁ P htie hδ_le hδ0 hbound n (i + 2) (by omega) x
  have hWb : ∀ l : ℕ,
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
          ((iteratedCovGrad (I := I) g₀ 2 6 l
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 ricciFoldRemainderSlotPerm
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (domDomCongrSection (I := I) g₀
                  (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ)
                  (iteratedCovGrad (I := I) g₀ 0 2 2
                    (ccTensor02Symm (I := I) (M := M) g₀ P)))))).toSection x) ≤
        fr ^ 2 * b (2 + l) := by
    intro l
    rw [riemannianFiberNormSq_iteratedCovGrad_rsDomDomCongrSection_eq (I := I) (M := M) g₀ 2 6 ricciFoldRemainderSlotPerm _ l x]
    rw [show slotExtendIter (I := I) (M := M) g₀ 0 4 2
        (domDomCongrSection (I := I) g₀
          (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ)
          (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P))) =
        slotExtend (I := I) (M := M) g₀ 1 5
          (slotExtend (I := I) (M := M) g₀ 0 4
            (domDomCongrSection (I := I) g₀
              (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ)
              (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P))))
        from rfl]
    refine le_trans (rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 1 5 _ l x) ?_
    refine le_trans (mul_le_mul_of_nonneg_left
      (rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 0 4 _ l x) hfr_nn) ?_
    rw [riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ)
      (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P)) l x]
    rw [riemannianFiberNormSq_iteratedCovGrad_comp (I := I) (M := M) g₀ 0 2 2 l
      (ccTensor02Symm (I := I) (M := M) g₀ P) x]
    have hsymm := rfns_iteratedCovGrad_symmS_pointwise (I := I) (M := M) g₀ P (2 + l) x
    have hstep : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (2 + l)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (2 + l)
          (ccTensor02Symm (I := I) (M := M) g₀ P)).toSection x) ≤ b (2 + l) := hsymm
    calc fr * (fr * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (2 + l)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (2 + l)
              (ccTensor02Symm (I := I) (M := M) g₀ P)).toSection x))
        ≤ fr * (fr * b (2 + l)) := by
          refine mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hstep hfr_nn) hfr_nn
      _ = fr ^ 2 * b (2 + l) := by ring
  have hterm : ∀ n ∈ Finset.range (i + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 6 2 n
            (secondMetricPairTraceOp (I := I) (M := M) g₀ g₁)).toSection x) *
        ∑ l ∈ Finset.range (i + 1 - n),
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
            ((iteratedCovGrad (I := I) g₀ 2 6 l
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 ricciFoldRemainderSlotPerm
                (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                  (domDomCongrSection (I := I) g₀
                    (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ)
                    (iteratedCovGrad (I := I) g₀ 0 2 2
                      (ccTensor02Symm (I := I) (M := M) g₀ P)))))).toSection x) ≤
      (CPT n * ∑ l ∈ Finset.range (i + 1 - n), fr ^ 2) *
        Combinatorics.boundedFactorGridWindow b (i + 2) (i + 3) := by
    intro n hn
    rw [Finset.mem_range] at hn
    have hn' : n ≤ i := by omega
    have hsumW : (∑ l ∈ Finset.range (i + 1 - n),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
          ((iteratedCovGrad (I := I) g₀ 2 6 l
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 ricciFoldRemainderSlotPerm
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (domDomCongrSection (I := I) g₀
                  (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ)
                  (iteratedCovGrad (I := I) g₀ 0 2 2
                    (ccTensor02Symm (I := I) (M := M) g₀ P)))))).toSection x)) ≤
        ∑ l ∈ Finset.range (i + 1 - n), fr ^ 2 * b (2 + l) :=
      Finset.sum_le_sum (fun l _ => hWb l)
    have hW_nn : 0 ≤ ∑ l ∈ Finset.range (i + 1 - n),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
          ((iteratedCovGrad (I := I) g₀ 2 6 l
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 ricciFoldRemainderSlotPerm
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (domDomCongrSection (I := I) g₀
                  (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ)
                  (iteratedCovGrad (I := I) g₀ 0 2 2
                    (ccTensor02Symm (I := I) (M := M) g₀ P)))))).toSection x) :=
      Finset.sum_nonneg (fun l _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (6 + l) x _)
    refine le_trans (mul_le_mul (hPT n hn') hsumW hW_nn
      (mul_nonneg (hCPT_nn n)
        (Combinatorics.boundedFactorGridWindow_nonneg b hb_nn _ _))) ?_
    rw [Finset.mul_sum]
    rw [show (CPT n * ∑ l ∈ Finset.range (i + 1 - n), fr ^ 2) *
        Combinatorics.boundedFactorGridWindow b (i + 2) (i + 3) =
        ∑ l ∈ Finset.range (i + 1 - n),
          CPT n * fr ^ 2 * Combinatorics.boundedFactorGridWindow b (i + 2) (i + 3) from by
      rw [Finset.mul_sum, Finset.sum_mul]]
    refine Finset.sum_le_sum (fun l hl => ?_)
    rw [Finset.mem_range] at hl
    have habsorb : b (2 + l) * Combinatorics.boundedFactorGridWindow b (i + 2) (n + 1) ≤
        Combinatorics.boundedFactorGridWindow b (i + 2) ((n + 1) + (2 + l)) :=
      Combinatorics.single_factor_mul_boundedFactorGridWindow_le b hb_nn
        (by omega) (by omega)
    have hmono : Combinatorics.boundedFactorGridWindow b (i + 2) ((n + 1) + (2 + l)) ≤
        Combinatorics.boundedFactorGridWindow b (i + 2) (i + 3) :=
      Combinatorics.boundedFactorGridWindow_mono b hb_nn (le_refl _) (by omega)
    calc CPT n * Combinatorics.boundedFactorGridWindow b (i + 2) (n + 1) *
            (fr ^ 2 * b (2 + l))
        = (CPT n * fr ^ 2) *
            (b (2 + l) * Combinatorics.boundedFactorGridWindow b (i + 2) (n + 1)) := by
          ring
      _ ≤ (CPT n * fr ^ 2) *
            Combinatorics.boundedFactorGridWindow b (i + 2) ((n + 1) + (2 + l)) :=
          mul_le_mul_of_nonneg_left habsorb
            (mul_nonneg (hCPT_nn n) (by positivity))
      _ ≤ (CPT n * fr ^ 2) *
            Combinatorics.boundedFactorGridWindow b (i + 2) (i + 3) :=
          mul_le_mul_of_nonneg_left hmono
            (mul_nonneg (hCPT_nn n) (by positivity))
      _ = CPT n * fr ^ 2 * Combinatorics.boundedFactorGridWindow b (i + 2) (i + 3) := by
          ring
  refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm)
    (appCcGdiag_nonneg (E := E) i)) ?_
  rw [← Finset.sum_mul]
  exact le_of_eq (by ring)

private theorem exists_rfns_icg_refoldKernelContractionField_window
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (refoldKernelContractionField (I := I) (M := M) g₀ g₁
                (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P))
                (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
                (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1)).toSection x) ≤
          C i * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 2) (i + 3) := by
  classical
  obtain ⟨C1, hC1_nn, hC1⟩ :=
    exists_rfns_icg_refoldKernelContractionMonomialField_window (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 4) 2) hδ₀
  obtain ⟨C2, hC2_nn, hC2⟩ :=
    exists_rfns_icg_refoldKernelContractionMonomialField_window (I := I) (M := M) g₀
      (Equiv.swap (1 : Fin 4) 3) hδ₀
  obtain ⟨C3, hC3_nn, hC3⟩ :=
    exists_rfns_icg_refoldKernelContractionMonomialField_window (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) hδ₀
  obtain ⟨C4, hC4_nn, hC4⟩ :=
    exists_rfns_icg_refoldKernelContractionMonomialField_window (I := I) (M := M) g₀
      (1 : Equiv.Perm (Fin 4)) hδ₀
  refine ⟨fun i => 2 * C1 i + 2 * C2 i + C3 i + C4 i,
    fun i => by
      have := hC1_nn i; have := hC2_nn i; have := hC3_nn i; have := hC4_nn i; linarith, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hbound i x
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) with hb_def
  have hb_nn : ∀ l, 0 ≤ b l :=
    fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  set G : SmoothCcTensor g₀ 0 4 :=
    iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P) with hG_def
  set m1 := refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁ G
    (Equiv.swap (0 : Fin 4) 2) with hm1_def
  set m2 := refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁ G
    (Equiv.swap (1 : Fin 4) 3) with hm2_def
  set m3 := refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁ G
    (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) with hm3_def
  set m4 := refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁ G
    (1 : Equiv.Perm (Fin 4)) with hm4_def
  have hker : refoldKernelContractionField (I := I) (M := M) g₀ g₁ G
      (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
      (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1 =
      (1 / 2 : ℝ) • (m1 + m2 - m3 - m4) := rfl
  have hsm : (iteratedCovGrad (I := I) g₀ 2 2 i
      ((1 / 2 : ℝ) • (m1 + m2 - m3 - m4))).toSection x =
      (1 / 2 : ℝ) • ((iteratedCovGrad (I := I) g₀ 2 2 i
        (m1 + m2 - m3 - m4)).toSection x) := by
    rw [iteratedCovGrad_smul_real (I := I) g₀ 2 2 i (1 / 2 : ℝ) _,
      SmoothCcTensor.toSection_smul]
    rfl
  have hsplit : (iteratedCovGrad (I := I) g₀ 2 2 i (m1 + m2 - m3 - m4)).toSection x =
      ((iteratedCovGrad (I := I) g₀ 2 2 i m1).toSection x
        + (iteratedCovGrad (I := I) g₀ 2 2 i m2).toSection x
        - (iteratedCovGrad (I := I) g₀ 2 2 i m3).toSection x)
        - (iteratedCovGrad (I := I) g₀ 2 2 i m4).toSection x := by
    rw [show m1 + m2 - m3 - m4 = (m1 + m2 - m3) - m4 from rfl, iteratedCovGrad_sub,
      show m1 + m2 - m3 = (m1 + m2) - m3 from rfl, iteratedCovGrad_sub, iteratedCovGrad_add]
    rw [SmoothCcTensor.toSection_sub, SmoothCcTensor.toSection_sub,
      SmoothCcTensor.toSection_add]
    rfl
  rw [hker, hsm, hsplit]
  rw [riemannianFiberNormSq_smul_value (I := I) (M := M) g₀ 2 (2 + i) x (1 / 2 : ℝ) _,
    show (1 / 2 : ℝ) ^ 2 = 1 / 4 from by norm_num]
  have h1 := hC1 g₁ P htie hδ_le hδ0 hbound i x
  have h2 := hC2 g₁ P htie hδ_le hδ0 hbound i x
  have h3 := hC3 g₁ P htie hδ_le hδ0 hbound i x
  have h4 := hC4 g₁ P htie hδ_le hδ0 hbound i x
  have hs1 := riemannianFiberNormSq_sub_le (I := I) (M := M) g₀ 2 (2 + i) x
    ((iteratedCovGrad (I := I) g₀ 2 2 i m1).toSection x
      + (iteratedCovGrad (I := I) g₀ 2 2 i m2).toSection x
      - (iteratedCovGrad (I := I) g₀ 2 2 i m3).toSection x)
    ((iteratedCovGrad (I := I) g₀ 2 2 i m4).toSection x)
  have hs2 := riemannianFiberNormSq_sub_le (I := I) (M := M) g₀ 2 (2 + i) x
    ((iteratedCovGrad (I := I) g₀ 2 2 i m1).toSection x
      + (iteratedCovGrad (I := I) g₀ 2 2 i m2).toSection x)
    ((iteratedCovGrad (I := I) g₀ 2 2 i m3).toSection x)
  have hs3 := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 (2 + i) x
    ((iteratedCovGrad (I := I) g₀ 2 2 i m1).toSection x)
    ((iteratedCovGrad (I := I) g₀ 2 2 i m2).toSection x)
  have hgrid_nn : 0 ≤ Combinatorics.boundedFactorGridWindow b (i + 2) (i + 3) :=
    Combinatorics.boundedFactorGridWindow_nonneg b hb_nn _ _
  nlinarith [h1, h2, h3, h4, hs1, hs2, hs3, hgrid_nn, hC1_nn i, hC2_nn i, hC3_nn i,
    hC4_nn i]


theorem rfns_iteratedCovGrad_refoldKernelContractionFieldInputSymm_boundedFactorGridWindow_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (ccInputSlotSymm (I := I) (M := M) g₀
                (refoldKernelContractionField (I := I) (M := M) g₀ g₁
                  (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P))
                  (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
                  (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1))).toSection
              x) ≤
          C i * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 2) (i + 3) := by
  classical
  obtain ⟨Ck, hCk_nn, hCk⟩ :=
    exists_rfns_icg_refoldKernelContractionField_window (I := I) (M := M) g₀ hδ₀
  have hSW_ex : ∀ q : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + q) x
        ((iteratedCovGrad (I := I) g₀ 2 2 q
          (ccInputSlotSwapField (I := I) (M := M) g₀)).toSection x) ≤ c := fun q =>
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 2 (2 + q)
      (iteratedCovGrad (I := I) g₀ 2 2 q (ccInputSlotSwapField (I := I) (M := M) g₀))
  choose SW hSW_nn hSW using hSW_ex
  refine ⟨fun i => (1 / 2 : ℝ) * Ck i +
      (1 / 2 : ℝ) * (diagonalGridGrowthFactor (E := E) i * (∑ i' ∈ Finset.range (i + 1), Ck i') *
        (∑ l ∈ Finset.range (i + 1), SW l)), ?_, ?_⟩
  · intro i
    have h2 : 0 ≤ ∑ i' ∈ Finset.range (i + 1), Ck i' :=
      Finset.sum_nonneg fun i' _ => hCk_nn i'
    have h3 : 0 ≤ ∑ l ∈ Finset.range (i + 1), SW l :=
      Finset.sum_nonneg fun l _ => hSW_nn l
    have h4 : 0 ≤ diagonalGridGrowthFactor (E := E) i := appCcGdiag_nonneg (E := E) i
    have h1 : 0 ≤ Ck i := hCk_nn i
    positivity
  · intro g₁ P htie δ hδ_le hδ0 hbound i x
    set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
      ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) with hb_def
    have hb_nn : ∀ l, 0 ≤ b l :=
      fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
    set W : ℝ := Combinatorics.boundedFactorGridWindow b (i + 2) (i + 3) with hW_def
    have hW_nn : 0 ≤ W := Combinatorics.boundedFactorGridWindow_nonneg b hb_nn _ _
    set K : SmoothCcTensor g₀ 2 2 :=
      refoldKernelContractionField (I := I) (M := M) g₀ g₁
        (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P))
        (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
        (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1 with hK_def
    have hQ : ∀ n : ℕ, n ≤ i →
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 2 2 n K).toSection x) ≤ Ck n * W := by
      intro n hn
      refine le_trans (hCk g₁ P htie hδ_le hδ0 hbound n x) ?_
      refine mul_le_mul_of_nonneg_left ?_ (hCk_nn n)
      rw [hW_def]
      exact Combinatorics.boundedFactorGridWindow_mono b hb_nn (by omega) (by omega)
    have hsubject : ccInputSlotSymm (I := I) (M := M) g₀ K =
        (1 / 2 : ℝ) • (K + ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 2 K
          (ccInputSlotSwapField (I := I) (M := M) g₀)) := rfl
    rw [hsubject]
    have hsm : (iteratedCovGrad (I := I) g₀ 2 2 i
        ((1 / 2 : ℝ) • (K + ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 2 K
          (ccInputSlotSwapField (I := I) (M := M) g₀)))).toSection x =
        (1 / 2 : ℝ) • ((iteratedCovGrad (I := I) g₀ 2 2 i
          (K + ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 2 K
            (ccInputSlotSwapField (I := I) (M := M) g₀))).toSection x) := by
      rw [iteratedCovGrad_smul_real (I := I) g₀ 2 2 i (1 / 2 : ℝ) _,
        SmoothCcTensor.toSection_smul]
      rfl
    rw [hsm, riemannianFiberNormSq_smul_value (I := I) (M := M) g₀ 2 (2 + i) x (1 / 2 : ℝ) _,
      show (1 / 2 : ℝ) ^ 2 = 1 / 4 from by norm_num]
    have hsplit : (iteratedCovGrad (I := I) g₀ 2 2 i
        (K + ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 2 K
          (ccInputSlotSwapField (I := I) (M := M) g₀))).toSection x =
        (iteratedCovGrad (I := I) g₀ 2 2 i K).toSection x
        + (iteratedCovGrad (I := I) g₀ 2 2 i
            (ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 2 K
              (ccInputSlotSwapField (I := I) (M := M) g₀))).toSection x := by
      rw [iteratedCovGrad_add (I := I) g₀ 2 2 i _ _, SmoothCcTensor.toSection_add]
      rfl
    rw [hsplit]
    refine le_trans (mul_le_mul_of_nonneg_left
      (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 (2 + i) x _ _)
      (by norm_num : (0 : ℝ) ≤ 1 / 4)) ?_
    have hQi : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 2 i K).toSection x) ≤ Ck i * W :=
      hQ i (le_refl i)
    have hApp : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 2 i
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 2 K
            (ccInputSlotSwapField (I := I) (M := M) g₀))).toSection x) ≤
        diagonalGridGrowthFactor (E := E) i * ((∑ i' ∈ Finset.range (i + 1), Ck i') *
          ((∑ l ∈ Finset.range (i + 1), SW l) * W)) := by
      refine le_trans (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le
        (I := I) (M := M) g₀ i 2 2 2 K (ccInputSlotSwapField (I := I) (M := M) g₀) x) ?_
      refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg (E := E) i)
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun i' hi' => ?_
      rw [Finset.mem_range] at hi'
      have hswapsum : (∑ l ∈ Finset.range (i + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 2 2 l
              (ccInputSlotSwapField (I := I) (M := M) g₀)).toSection x)) ≤
          ∑ l ∈ Finset.range (i + 1), SW l := by
        refine le_trans (Finset.sum_le_sum fun l _ => hSW l x) ?_
        refine Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_mono (by omega)) ?_
        exact fun l _ _ => hSW_nn l
      have hQi' := hQ i' (by omega)
      have hswap_nn : 0 ≤ ∑ l ∈ Finset.range (i + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 2 2 l
              (ccInputSlotSwapField (I := I) (M := M) g₀)).toSection x) :=
        Finset.sum_nonneg fun l _ =>
          riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (2 + l) x _
      calc riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i') x
              ((iteratedCovGrad (I := I) g₀ 2 2 i' K).toSection x) *
            ∑ l ∈ Finset.range (i + 1 - i'),
              riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + l) x
                ((iteratedCovGrad (I := I) g₀ 2 2 l
                  (ccInputSlotSwapField (I := I) (M := M) g₀)).toSection x)
          ≤ (Ck i' * W) * (∑ l ∈ Finset.range (i + 1), SW l) :=
            mul_le_mul hQi' hswapsum hswap_nn (mul_nonneg (hCk_nn i') hW_nn)
        _ = Ck i' * ((∑ l ∈ Finset.range (i + 1), SW l) * W) := by ring
    calc (1 / 4 : ℝ) * (2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i K).toSection x)
          + 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 2 K
                (ccInputSlotSwapField (I := I) (M := M) g₀))).toSection x))
        ≤ (1 / 4 : ℝ) * (2 * (Ck i * W)
            + 2 * (diagonalGridGrowthFactor (E := E) i * ((∑ i' ∈ Finset.range (i + 1), Ck i') *
              ((∑ l ∈ Finset.range (i + 1), SW l) * W)))) := by
          nlinarith [hQi, hApp]
      _ = ((1 / 2 : ℝ) * Ck i +
            (1 / 2 : ℝ) * (diagonalGridGrowthFactor (E := E) i * (∑ i' ∈ Finset.range (i + 1), Ck i') *
              (∑ l ∈ Finset.range (i + 1), SW l))) * W := by ring

section k4aRefoldCorner

private def k4aArrVal (i v : ℕ) : ℕ :=
  if v = 0 then i + 1
  else if v = 1 then i + 3
  else if v < i + 2 then v - 2
  else if v = i + 2 then i + 4
  else if v = i + 3 then i + 5
  else if v = i + 4 then i
  else i + 2

private lemma k4aArrVal_lt (i v : ℕ) (_hv : v < i + 6) : k4aArrVal i v < 6 + i := by
  unfold k4aArrVal
  split_ifs <;> omega

private lemma k4aArrVal_eq_sub (i v : ℕ) (h2 : 2 ≤ v) (h : v < i + 2) :
    k4aArrVal i v = v - 2 := by
  unfold k4aArrVal
  rw [if_neg (by omega), if_neg (by omega), if_pos h]

private lemma k4aArrVal_at_i2 (i : ℕ) : k4aArrVal i (i + 2) = i + 4 := by
  unfold k4aArrVal
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl]

private lemma k4aArrVal_at_i3 (i : ℕ) : k4aArrVal i (i + 3) = i + 5 := by
  unfold k4aArrVal
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl]

private lemma k4aArrVal_at_i4 (i : ℕ) : k4aArrVal i (i + 4) = i := by
  unfold k4aArrVal
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_pos rfl]

private lemma k4aArrVal_at_i5 (i : ℕ) : k4aArrVal i (i + 5) = i + 2 := by
  unfold k4aArrVal
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega)]

private lemma k4a_decomposeFin_symm_val {m : ℕ} (ρ : Equiv.Perm (Fin m)) (j : Fin (m + 1)) :
    (((Equiv.Perm.decomposeFin.symm (0, ρ)) j : Fin (m + 1)) : ℕ) =
      if h : (j : ℕ) = 0 then 0
      else ((ρ ⟨(j : ℕ) - 1, by have := j.isLt; omega⟩ : Fin m) : ℕ) + 1 := by
  refine Fin.cases ?_ (fun j' => ?_) j
  · rw [Equiv.Perm.decomposeFin_symm_apply_zero]
    simp
  · rw [Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self, Equiv.refl_apply]
    rw [dif_neg (by simp [Fin.val_succ] : ¬((Fin.succ j' : Fin (m + 1)) : ℕ) = 0)]
    have harg : (⟨((Fin.succ j' : Fin (m + 1)) : ℕ) - 1,
        by have h1 := (Fin.succ j').isLt; have h2 := j'.isLt; omega⟩ : Fin m) = j' :=
      Fin.ext (by simp)
    rw [harg]
    simp [Fin.val_succ]

private lemma k4a_swap01_val {m : ℕ} (j : Fin (m + 2)) :
    (((Equiv.swap (0 : Fin (m + 2)) 1) j : Fin (m + 2)) : ℕ) =
      if (j : ℕ) = 0 then 1 else if (j : ℕ) = 1 then 0 else (j : ℕ) := by
  rcases eq_or_ne j 0 with h0 | h0
  · subst h0
    rw [Equiv.swap_apply_left]
    simp
  · rcases eq_or_ne j 1 with h1 | h1
    · subst h1
      rw [Equiv.swap_apply_right]
      simp
    · rw [Equiv.swap_apply_of_ne_of_ne h0 h1]
      rw [if_neg (fun hv => h0 (Fin.ext (by simpa using hv))),
        if_neg (fun hv => h1 (Fin.ext (by simpa using hv)))]

private lemma k4a_step_perm_val {m : ℕ} (τ : Equiv.Perm (Fin (m + 2))) (i : ℕ)
    (hτ : ∀ j : Fin (m + 2), ((τ j : Fin (m + 2)) : ℕ) = k4aArrVal i (j : ℕ))
    (hm : m = 4 + i) (j : Fin (m + 3)) :
    ((((Equiv.Perm.decomposeFin.symm (0, Equiv.swap (0 : Fin (m + 2)) 1)).trans
          ((Equiv.swap (0 : Fin (m + 3)) 1).trans
            (Equiv.Perm.decomposeFin.symm (0, τ)))) j : Fin (m + 3)) : ℕ) =
      k4aArrVal (i + 1) (j : ℕ) := by
  rw [Equiv.trans_apply, Equiv.trans_apply]
  have hj1 := k4a_decomposeFin_symm_val (Equiv.swap (0 : Fin (m + 2)) 1) j
  set j1 : Fin (m + 3) := (Equiv.Perm.decomposeFin.symm (0, Equiv.swap (0 : Fin (m + 2)) 1)) j
    with hj1_def
  have hj2 := k4a_swap01_val (m := m + 1) ((Equiv.swap (0 : Fin (m + 3)) 1) j1)
  set j2 : Fin (m + 3) := (Equiv.swap (0 : Fin (m + 3)) 1) j1 with hj2_def
  have hj2v := k4a_swap01_val (m := m + 1) j1
  have hj3 := k4a_decomposeFin_symm_val τ j2
  rw [hj3]
  have hjlt : (j : ℕ) < m + 3 := j.isLt
  by_cases h0 : (j : ℕ) = 0
  · rw [dif_pos h0] at hj1
    have hj1v : (j1 : ℕ) = 0 := hj1
    have hj2vv : (j2 : ℕ) = 1 := by rw [hj2_def, hj2v, if_pos hj1v]
    rw [dif_neg (by omega)]
    rw [hτ ⟨(j2 : ℕ) - 1, by omega⟩]
    have harg0 : ((⟨(j2 : ℕ) - 1, by omega⟩ : Fin (m + 2)) : ℕ) = 0 := by
      simp [hj2vv]
    rw [harg0]
    unfold k4aArrVal
    simp only [h0]
    split_ifs <;> omega
  · rw [dif_neg h0] at hj1
    rw [k4a_swap01_val (m := m) ⟨(j : ℕ) - 1, by omega⟩] at hj1
    simp only [] at hj1
    by_cases h1 : (j : ℕ) = 1
    · have hj1v : (j1 : ℕ) = 2 := by
        rw [hj1]
        simp [h1]
      have hj2vv : (j2 : ℕ) = 2 := by
        rw [hj2_def, hj2v, if_neg (by omega), if_neg (by omega), hj1v]
      rw [dif_neg (by omega)]
      rw [hτ ⟨(j2 : ℕ) - 1, by omega⟩]
      have harg1 : ((⟨(j2 : ℕ) - 1, by omega⟩ : Fin (m + 2)) : ℕ) = 1 := by
        simp [hj2vv]
      rw [harg1]
      unfold k4aArrVal
      simp only [h1]
      split_ifs <;> omega
    · by_cases h2 : (j : ℕ) = 2
      · have hj1v : (j1 : ℕ) = 1 := by
          rw [hj1]
          simp [h2]
        have hj2vv : (j2 : ℕ) = 0 := by
          rw [hj2_def, hj2v, if_neg (by omega), if_pos hj1v]
        rw [dif_pos hj2vv]
        unfold k4aArrVal
        simp only [h2]
        split_ifs <;> omega
      · have hj1v : (j1 : ℕ) = (j : ℕ) := by
          rw [hj1]
          rw [if_neg (by omega), if_neg (by omega)]
          omega
        have hj2vv : (j2 : ℕ) = (j : ℕ) := by
          rw [hj2_def, hj2v, if_neg (by omega), if_neg (by omega), hj1v]
        rw [dif_neg (by omega)]
        rw [hτ ⟨(j2 : ℕ) - 1, by omega⟩]
        have harg : ((⟨(j2 : ℕ) - 1, by omega⟩ : Fin (m + 2)) : ℕ) = (j : ℕ) - 1 := by
          simp [hj2vv]
        rw [harg]
        unfold k4aArrVal
        split_ifs <;> omega

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma k4a_covGrad_castRankCc_db (g : SmoothRiemannianMetric I M) (r : ℕ) {a b : ℕ}
    (h : a = b) (W : SmoothCcTensor g r a) :
    covGrad (I := I) (M := M) g r b (castCcTensorRank g r h W) =
      castCcTensorRank g r (by omega : a + 1 = b + 1)
        (covGrad (I := I) (M := M) g r a W) := by
  subst h
  rfl

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma k4a_rsDomDomCongrSection_comp (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (σ ρ : Equiv.Perm (Fin s)) (S : SmoothCcTensor g r s) :
    rsDomDomCongrSection (I := I) (M := M) g r s σ
        (rsDomDomCongrSection (I := I) (M := M) g r s ρ S) =
      rsDomDomCongrSection (I := I) (M := M) g r s (ρ.trans σ) S := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [rsDomDomCongrSection_toSection, rsDomDomCongrSection_toSection,
    rsDomDomCongrSection_toSection]
  exact rsDomDomCongr_rsDomDomCongr (I := I) (M := M) σ ρ (S.toSection x)

omit [NeZero (Module.finrank ℝ E)] in
private lemma k4a_covGrad_rsDomDomCongrSection (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (σ : Equiv.Perm (Fin s)) (S : SmoothCcTensor g r s) :
    covGrad (I := I) (M := M) g r s (rsDomDomCongrSection (I := I) (M := M) g r s σ S) =
      rsDomDomCongrSection (I := I) (M := M) g r (s + 1)
        (Equiv.Perm.decomposeFin.symm (0, σ))
        (covGrad (I := I) (M := M) g r s S) := by
  classical
  have hrel : ∀ (y : M) (d : Tensor0SSpace r I y),
      Tensor0SSpace.toModel
          ((show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace s I y from
            (rsDomDomCongrSection (I := I) (M := M) g r s σ S).toSection y) d) =
        ContinuousMultilinearMap.domDomCongr σ
          (Tensor0SSpace.toModel
            ((show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace s I y from S.toSection y) d)) := by
    intro y d
    rw [rsDomDomCongrSection_toSection, toModel_rsDomDomCongr_apply]
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  have hsec : (covGrad (I := I) (M := M) g r s
        (rsDomDomCongrSection (I := I) (M := M) g r s σ S)).toSection x =
      tensorRS_domDomCongr (I := I) (M := M) (Equiv.Perm.decomposeFin.symm (0, σ))
        ((covGrad (I := I) (M := M) g r s S).toSection x) := by
    apply ContinuousLinearMap.ext
    intro d
    apply Tensor0SSpace.toModel_injective
    change Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (covGrad (I := I) (M := M) g r s
            (rsDomDomCongrSection (I := I) (M := M) g r s σ S)).toSection x) d) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          tensorRS_domDomCongr (I := I) (M := M) (Equiv.Perm.decomposeFin.symm (0, σ))
            ((covGrad (I := I) (M := M) g r s S).toSection x)) d)
    rw [toModel_rsDomDomCongr_apply (I := I) (M := M) (Equiv.Perm.decomposeFin.symm (0, σ))
      ((covGrad (I := I) (M := M) g r s S).toSection x) d]
    exact ContinuousMultilinearMap.ext (fun v =>
      covGrad_rs_toModel_domDomCongr (I := I) (M := M) g r s σ S
        (rsDomDomCongrSection (I := I) (M := M) g r s σ S) hrel x d v)
  rw [hsec, rsDomDomCongrSection_toSection]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma k4a_slotExtend_rsDomDomCongrSection (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ρ : Equiv.Perm (Fin s)) (S : SmoothCcTensor g r s) :
    slotExtend (I := I) (M := M) g r s
        (rsDomDomCongrSection (I := I) (M := M) g r s ρ S) =
      rsDomDomCongrSection (I := I) (M := M) g (r + 1) (s + 1)
        (Equiv.Perm.decomposeFin.symm (0, ρ))
        (slotExtend (I := I) (M := M) g r s S) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  have hsec : (slotExtend (I := I) (M := M) g r s
        (rsDomDomCongrSection (I := I) (M := M) g r s ρ S)).toSection x =
      tensorRS_domDomCongr (I := I) (M := M) (Equiv.Perm.decomposeFin.symm (0, ρ))
        ((slotExtend (I := I) (M := M) g r s S).toSection x) := by
    apply ContinuousLinearMap.ext
    intro d
    apply Tensor0SSpace.toModel_injective
    change Tensor0SSpace.toModel
        ((show Tensor0SSpace (r + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (slotExtend (I := I) (M := M) g r s
            (rsDomDomCongrSection (I := I) (M := M) g r s ρ S)).toSection x) d) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace (r + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          tensorRS_domDomCongr (I := I) (M := M) (Equiv.Perm.decomposeFin.symm (0, ρ))
            ((slotExtend (I := I) (M := M) g r s S).toSection x)) d)
    rw [toModel_rsDomDomCongr_apply (I := I) (M := M) (Equiv.Perm.decomposeFin.symm (0, ρ))
      ((slotExtend (I := I) (M := M) g r s S).toSection x) d]
    apply ContinuousMultilinearMap.ext
    intro v
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    have hlam : (fun k : Fin (s + 1) => v ((Equiv.Perm.decomposeFin.symm (0, ρ)) k)) =
        Fin.cons (v 0) (fun k : Fin s => v (Fin.succ (ρ k))) := by
      funext k
      refine Fin.cases ?_ (fun k' => ?_) k
      · rw [Equiv.Perm.decomposeFin_symm_apply_zero, Fin.cons_zero]
      · rw [Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self, Equiv.refl_apply,
          Fin.cons_succ]
    rw [hlam]
    rw [show Tensor0SSpace.toModel
        ((show Tensor0SSpace (r + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (slotExtend (I := I) (M := M) g r s S).toSection x) d)
        (Fin.cons (v 0) (fun k : Fin s => v (Fin.succ (ρ k)))) =
        Tensor0SSpace.toModel
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from S.toSection x)
            ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x) d (v 0)))
          (fun k : Fin s => v (Fin.succ (ρ k))) from
      slotExtendFib_apply_eval (I := I) (M := M) g r s x
        (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from S.toSection x)
        d (v 0) (fun k : Fin s => v (Fin.succ (ρ k)))]
    conv_lhs => rw [show v = Fin.cons (v 0) (Matrix.vecTail v) from (Fin.cons_self_tail v).symm]
    rw [show Tensor0SSpace.toModel
        ((show Tensor0SSpace (r + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (slotExtend (I := I) (M := M) g r s
            (rsDomDomCongrSection (I := I) (M := M) g r s ρ S)).toSection x) d)
        (Fin.cons (v 0) (Matrix.vecTail v)) =
        Tensor0SSpace.toModel
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
            (rsDomDomCongrSection (I := I) (M := M) g r s ρ S).toSection x)
            ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x) d (v 0)))
          (Matrix.vecTail v) from
      slotExtendFib_apply_eval (I := I) (M := M) g r s x
        (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
          (rsDomDomCongrSection (I := I) (M := M) g r s ρ S).toSection x)
        d (v 0) (Matrix.vecTail v)]
    rw [show Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
          (rsDomDomCongrSection (I := I) (M := M) g r s ρ S).toSection x)
          ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x) d (v 0)))
        (Matrix.vecTail v) =
        Tensor0SSpace.toModel
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from S.toSection x)
            ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x) d (v 0)))
          (fun k : Fin s => Matrix.vecTail v (ρ k)) from by
      rw [rsDomDomCongrSection_toSection, toModel_rsDomDomCongr_apply,
        ContinuousMultilinearMap.domDomCongr_apply]]
    rfl
  rw [hsec, rsDomDomCongrSection_toSection]

omit [NeZero (Module.finrank ℝ E)] in
private lemma k4a_covGrad_slotExtend_toSection
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (Φ : SmoothCcTensor g r s) (x : M) :
    (covGrad (I := I) (M := M) g (r + 1) (s + 1)
        (slotExtend (I := I) (M := M) g r s Φ)).toSection x =
      tensorRS_domDomCongr (I := I) (M := M) (r := r + 1) (Equiv.swap (0 : Fin (s + 1 + 1)) 1)
        ((slotExtend (I := I) (M := M) g r (s + 1)
          (covGrad (I := I) (M := M) g r s Φ)).toSection x) := by
  classical
  apply ContinuousLinearMap.ext
  intro d
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  have hfib : ∀ (y : Tensor0SSpace (s + 1 + 1) I x) (w : Fin (s + 1 + 1) → TangentSpace I x),
      Tensor0SSpace.toModel y w = (y : Tensor0SSpace (s + 1 + 1) I x) w := fun _ _ => rfl
  conv_rhs => rw [hfib, rsDomDomCongr_apply_eval (I := I) (M := M) (r := r + 1)
    (Equiv.swap (0 : Fin (s + 1 + 1)) 1)
    ((slotExtend (I := I) (M := M) g r (s + 1)
      (covGrad (I := I) (M := M) g r s Φ)).toSection x) d m]
  conv_rhs => rw [← hfib]
  rw [covGrad_toSection_apply_eval (I := I) (M := M) g (r + 1) (s + 1)
    (slotExtend (I := I) (M := M) g r s Φ) x d m]
  rw [DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.tensorCovDerivAt_slotExtend_eq
    (I := I) (M := M) g r s Φ x (m 0)]
  rw [show Matrix.vecTail m =
      Fin.cons (m 1) (fun k : Fin s => m (Fin.succ (Fin.succ k))) from by
    funext k
    refine Fin.cases ?_ (fun i => ?_) k
    · change m (Fin.succ 0) = _
      rw [Fin.cons_zero]; rfl
    · change m (Fin.succ (Fin.succ i)) = _
      rw [Fin.cons_succ]]
  rw [slotExtendFib_apply_eval (I := I) (M := M) g r s x
    (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
      tensorCovDerivAt (I := I) (M := M) g r s Φ x (m 0))
    d (m 1) (fun k : Fin s => m (Fin.succ (Fin.succ k)))]
  rw [slotExtend_toSection (I := I) (M := M) g r (s + 1) (covGrad (I := I) (M := M) g r s Φ) x]
  rw [show (fun k => m ((Equiv.swap (0 : Fin (s + 1 + 1)) 1) k)) =
      Fin.cons (m 1) (fun k : Fin (s + 1) => m ((Equiv.swap (0 : Fin (s + 1 + 1)) 1) (Fin.succ k)))
      from by
    funext k
    refine Fin.cases ?_ (fun i => ?_) k
    · simp only [Fin.cons_zero]
      rw [Equiv.swap_apply_left]
    · rw [Fin.cons_succ]]
  rw [slotExtendFib_apply_eval (I := I) (M := M) g r (s + 1) x
    (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (s + 1) I x from
      (covGrad (I := I) (M := M) g r s Φ).toSection x)
    d (m 1) (fun k : Fin (s + 1) => m ((Equiv.swap (0 : Fin (s + 1 + 1)) 1) (Fin.succ k)))]
  rw [covGrad_toSection_apply_eval (I := I) (M := M) g r s Φ x
    ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x) d (m 1))
    (fun k : Fin (s + 1) => m ((Equiv.swap (0 : Fin (s + 1 + 1)) 1) (Fin.succ k)))]
  have hdir : m ((Equiv.swap (0 : Fin (s + 1 + 1)) 1) (Fin.succ (0 : Fin (s + 1)))) = m 0 := by
    rw [show (Fin.succ (0 : Fin (s + 1)) : Fin (s + 1 + 1)) = 1 from rfl, Equiv.swap_apply_right]
  have htail : (Matrix.vecTail (fun k : Fin (s + 1) =>
        m ((Equiv.swap (0 : Fin (s + 1 + 1)) 1) (Fin.succ k)))) =
      (fun k : Fin s => m (Fin.succ (Fin.succ k))) := by
    funext k
    change m ((Equiv.swap (0 : Fin (s + 1 + 1)) 1) (Fin.succ (Fin.succ k))) =
      m (Fin.succ (Fin.succ k))
    rw [Equiv.swap_apply_of_ne_of_ne]
    · exact (Fin.succ_ne_zero _)
    · rw [show (1 : Fin (s + 1 + 1)) = Fin.succ (0 : Fin (s + 1)) from rfl]
      exact fun h => Fin.succ_ne_zero _ (Fin.succ_injective _ h)
  rw [hdir, htail]

omit [NeZero (Module.finrank ℝ E)] in
private lemma k4a_covGrad_slotExtend (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) :
    covGrad (I := I) (M := M) g (r + 1) (s + 1) (slotExtend (I := I) (M := M) g r s Φ) =
      rsDomDomCongrSection (I := I) (M := M) g (r + 1) (s + 1 + 1)
        (Equiv.swap (0 : Fin (s + 1 + 1)) 1)
        (slotExtend (I := I) (M := M) g r (s + 1)
          (covGrad (I := I) (M := M) g r s Φ)) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [k4a_covGrad_slotExtend_toSection (I := I) (M := M) g r s Φ x,
    rsDomDomCongrSection_toSection]

omit [NeZero (Module.finrank ℝ E)] in
private lemma k4a_icg_refoldArgument_structure (g₀ : SmoothRiemannianMetric I M)
    (V : SmoothCcTensor g₀ 0 4) (i : ℕ) :
    ∃ τ : Equiv.Perm (Fin (((4 + i) + 1) + 1)),
      (∀ j : Fin (((4 + i) + 1) + 1),
        ((τ j : Fin (((4 + i) + 1) + 1)) : ℕ) = k4aArrVal i (j : ℕ)) ∧
      iteratedCovGrad (I := I) g₀ 2 6 i
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 ricciFoldRemainderSlotPerm
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2 V)) =
        castCcTensorRank g₀ 2 (by omega : ((4 + i) + 1) + 1 = 6 + i)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 (((4 + i) + 1) + 1) τ
            (slotExtend (I := I) (M := M) g₀ 1 ((4 + i) + 1)
              (slotExtend (I := I) (M := M) g₀ 0 (4 + i)
                (iteratedCovGrad (I := I) g₀ 0 4 i V)))) := by
  induction i with
  | zero =>
      refine ⟨ricciFoldRemainderSlotPerm, by decide, ?_⟩
      rw [iteratedCovGrad_zero, iteratedCovGrad_zero]
      rfl
  | succ i ih =>
      obtain ⟨τ, hτ, hEq⟩ := ih
      refine ⟨(Equiv.Perm.decomposeFin.symm
            (0, Equiv.swap (0 : Fin (((4 + i) + 1) + 1)) 1)).trans
          ((Equiv.swap (0 : Fin ((((4 + i) + 1) + 1) + 1)) 1).trans
            (Equiv.Perm.decomposeFin.symm (0, τ))), ?_, ?_⟩
      · intro j
        exact k4a_step_perm_val (m := 4 + i) τ i hτ rfl j
      · rw [iteratedCovGrad_succ, hEq]
        rw [k4a_covGrad_castRankCc_db]
        rw [k4a_covGrad_rsDomDomCongrSection]
        rw [k4a_covGrad_slotExtend (I := I) (M := M) g₀ 1 ((4 + i) + 1)]
        rw [k4a_covGrad_slotExtend (I := I) (M := M) g₀ 0 (4 + i)]
        rw [k4a_slotExtend_rsDomDomCongrSection]
        rw [k4a_rsDomDomCongrSection_comp, k4a_rsDomDomCongrSection_comp]
        rw [← iteratedCovGrad_succ]
        rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma k4a_castRankCc_db_toModel (g : SmoothRiemannianMetric I M) (r : ℕ) {a b : ℕ}
    (h : a = b) (W : SmoothCcTensor g r a) (x : M) (D : Tensor0SSpace r I x)
    (w : Fin b → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace b I x from
          (castCcTensorRank g r h W).toSection x) D) (fun k => (w k : E)) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace a I x from W.toSection x) D)
        (fun q : Fin a => (w (Fin.cast h q) : E)) := by
  subst h
  rfl

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma k4a_slotExtend_two_toModel (g₀ : SmoothRiemannianMetric I M) (c : ℕ)
    (S : SmoothCcTensor g₀ 0 c) (x : M) (D : Tensor0SSpace 2 I x)
    (u : Fin ((c + 1) + 1) → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace ((c + 1) + 1) I x from
          (slotExtend (I := I) (M := M) g₀ 1 (c + 1)
            (slotExtend (I := I) (M := M) g₀ 0 c S)).toSection x) D)
        (fun k => (u k : E)) =
      Tensor0SSpace.toModel D ![(u 0 : E), (u 1 : E)] *
        unitModel (I := I) (M := M) g₀ c S x
          (fun k : Fin c => (u ⟨(k : ℕ) + 2, by omega⟩ : E)) := by
  have hu : (fun k : Fin ((c + 1) + 1) => (u k : E)) =
      Fin.cons (show E from u 0)
        (Fin.cons (show E from u 1)
          (fun k : Fin c => (u ⟨(k : ℕ) + 2, by omega⟩ : E))) := by
    funext k
    refine Fin.cases rfl (fun k1 => ?_) k
    refine Fin.cases rfl (fun k2 => ?_) k1
    change (u (Fin.succ (Fin.succ k2)) : E) = (u ⟨(k2 : ℕ) + 2, by omega⟩ : E)
    congr 1
  rw [hu]
  rw [slotExtend_toModel_cons (I := I) (M := M) g₀ 1 (c + 1)
    (slotExtend (I := I) (M := M) g₀ 0 c S) x D (u 0)]
  rw [slotExtend_toModel_cons (I := I) (M := M) g₀ 0 c S x
    (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D (u 0)) (u 1)]
  set t : Tensor0SSpace 0 I x :=
    tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 0 x
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D (u 0)) (u 1) with ht_def
  have htval : Tensor0SSpace.toModel t (fun i : Fin 0 => i.elim0) =
      Tensor0SSpace.toModel D ![(u 0 : E), (u 1 : E)] := by
    rw [ht_def]
    have h1 := TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 0)
      (T := tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D (u 0)) (v0 := (u 1 : E))
      (vs := fun i : Fin 0 => i.elim0)
    rw [h1]
    have h2 := TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 1)
      (T := D) (v0 := (u 0 : E)) (vs := Fin.cons (show E from u 1) (fun i : Fin 0 => i.elim0))
    rw [h2]
    refine congrArg _ ?_
    funext k
    refine Fin.cases rfl (fun i => ?_) k
    refine Fin.cases rfl (fun i2 => i2.elim0) i
  have hdecomp := tensor0S_rank0_eq_smul_unit (I := I) (M := M) x t
  rw [htval] at hdecomp
  rw [hdecomp, map_smul]
  rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  rfl

omit [NeZero (Module.finrank ℝ E)] in
private lemma k4a_icg_refoldArgument_toModel (g₀ : SmoothRiemannianMetric I M)
    (V : SmoothCcTensor g₀ 0 4) (i : ℕ) (x : M) (D : Tensor0SSpace 2 I x)
    (w : Fin (6 + i) → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace (6 + i) I x from
          (iteratedCovGrad (I := I) g₀ 2 6 i
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 ricciFoldRemainderSlotPerm
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2 V))).toSection x) D)
        (fun k => (w k : E)) =
      Tensor0SSpace.toModel D
          ![(w ⟨i + 1, by omega⟩ : E), (w ⟨i + 3, by omega⟩ : E)] *
        unitModel (I := I) (M := M) g₀ (4 + i) (iteratedCovGrad (I := I) g₀ 0 4 i V) x
          (fun q : Fin (4 + i) =>
            (w ⟨k4aArrVal i ((q : ℕ) + 2), k4aArrVal_lt i _ (by have := q.isLt; omega)⟩ : E)) := by
  classical
  obtain ⟨τ, hτ, hEq⟩ := k4a_icg_refoldArgument_structure (I := I) (M := M) g₀ V i
  rw [hEq]
  rw [k4a_castRankCc_db_toModel (I := I) (M := M) g₀ 2
    (by omega : ((4 + i) + 1) + 1 = 6 + i)
    (rsDomDomCongrSection (I := I) (M := M) g₀ 2 (((4 + i) + 1) + 1) τ
      (slotExtend (I := I) (M := M) g₀ 1 ((4 + i) + 1)
        (slotExtend (I := I) (M := M) g₀ 0 (4 + i)
          (iteratedCovGrad (I := I) g₀ 0 4 i V)))) x D w]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace (((4 + i) + 1) + 1) I x from
      (rsDomDomCongrSection (I := I) (M := M) g₀ 2 (((4 + i) + 1) + 1) τ
        (slotExtend (I := I) (M := M) g₀ 1 ((4 + i) + 1)
          (slotExtend (I := I) (M := M) g₀ 0 (4 + i)
            (iteratedCovGrad (I := I) g₀ 0 4 i V)))).toSection x) D) =
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace (((4 + i) + 1) + 1) I x from
        tensorRS_domDomCongr (I := I) (M := M) τ
          ((slotExtend (I := I) (M := M) g₀ 1 ((4 + i) + 1)
            (slotExtend (I := I) (M := M) g₀ 0 (4 + i)
              (iteratedCovGrad (I := I) g₀ 0 4 i V))).toSection x)) D) from by
    rw [rsDomDomCongrSection_toSection]]
  rw [toModel_rsDomDomCongr_apply (I := I) (M := M) τ
    ((slotExtend (I := I) (M := M) g₀ 1 ((4 + i) + 1)
      (slotExtend (I := I) (M := M) g₀ 0 (4 + i)
        (iteratedCovGrad (I := I) g₀ 0 4 i V))).toSection x) D]
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  rw [show (fun k : Fin (((4 + i) + 1) + 1) =>
      (fun q : Fin (((4 + i) + 1) + 1) =>
        (w (Fin.cast (by omega : ((4 + i) + 1) + 1 = 6 + i) q) : E)) (τ k)) =
      (fun k : Fin (((4 + i) + 1) + 1) =>
        ((w (Fin.cast (by omega : ((4 + i) + 1) + 1 = 6 + i) (τ k)) : TangentSpace I x) : E))
      from rfl]
  rw [k4a_slotExtend_two_toModel (I := I) (M := M) g₀ (4 + i)
    (iteratedCovGrad (I := I) g₀ 0 4 i V) x D
    (fun k : Fin (((4 + i) + 1) + 1) =>
      w (Fin.cast (by omega : ((4 + i) + 1) + 1 = 6 + i) (τ k)))]
  refine congrArg₂ (· * ·) ?_ ?_
  · refine congrArg _ ?_
    funext k
    fin_cases k
    · change (w (Fin.cast _ (τ 0)) : E) = (w ⟨i + 1, _⟩ : E)
      congr 1
      refine Fin.ext ?_
      rw [Fin.val_cast, hτ 0]
      rfl
    · change (w (Fin.cast _ (τ 1)) : E) = (w ⟨i + 3, _⟩ : E)
      congr 1
      refine Fin.ext ?_
      rw [Fin.val_cast, hτ 1]
      rfl
  · refine congrArg _ ?_
    funext q
    congr 1
    refine Fin.ext ?_
    rw [Fin.val_cast, hτ ⟨(q : ℕ) + 2, by have := q.isLt; omega⟩]

private def k4a_slotExtendIterFib (g : SmoothRiemannianMetric I M) (b c : ℕ) (x : M)
    (A : Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x) :
    ∀ w : ℕ, Tensor0SSpace (b + w) I x →L[ℝ] Tensor0SSpace (c + w) I x
  | 0 => A
  | (w + 1) => slotExtendPointwise (I := I) (M := M) g (b + w) (c + w) x
      (k4a_slotExtendIterFib g b c x A w)

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma k4a_appCcLeibnizPsi_succ_succ_eq (g : SmoothRiemannianMetric I M) (b c : ℕ)
    (Φ : SmoothCcTensor g b c) (i j : ℕ) :
    appCcLeibnizPsi (I := I) (M := M) g b c Φ (i + 1) (j + 1) =
      (if j + 1 < i + 1 then
          covGrad (I := I) (M := M) g (b + (j + 1)) (c + i)
            (appCcLeibnizPsi (I := I) (M := M) g b c Φ i (j + 1))
        else 0) +
        slotExtend (I := I) (M := M) g (b + j) (c + i)
          (appCcLeibnizPsi (I := I) (M := M) g b c Φ i j) := by
  rw [show appCcLeibnizPsi (I := I) (M := M) g b c Φ (i + 1) (j + 1) =
      (if j + 1 < i + 1 then
          covGrad (I := I) (M := M) g (b + (j + 1)) (c + i)
            (appCcLeibnizPsi (I := I) (M := M) g b c Φ i (j + 1))
        else 0) +
        castCcTensorSourceRank g (c + (i + 1)) (by omega : (b + j) + 1 = b + (j + 1))
          (castCcTensorRank g ((b + j) + 1) (by omega : (c + i) + 1 = c + (i + 1))
            (slotExtend (I := I) (M := M) g (b + j) (c + i)
              (appCcLeibnizPsi (I := I) (M := M) g b c Φ i j))) from rfl]
  rw [castCcTensorRank, castCcTensorSourceRank]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma k4a_appCcLeibnizPsi_diag_toSection (g : SmoothRiemannianMetric I M) (b c : ℕ)
    (Φ : SmoothCcTensor g b c) (i : ℕ) (x : M) :
    ((appCcLeibnizPsi (I := I) (M := M) g b c Φ i i).toSection x :
        Tensor0SSpace (b + i) I x →L[ℝ] Tensor0SSpace (c + i) I x) =
      k4a_slotExtendIterFib (I := I) (M := M) g b c x
        (show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φ.toSection x) i := by
  induction i with
  | zero => rfl
  | succ i ih =>
      have hdiag : appCcLeibnizPsi (I := I) (M := M) g b c Φ (i + 1) (i + 1) =
          slotExtend (I := I) (M := M) g (b + i) (c + i)
            (appCcLeibnizPsi (I := I) (M := M) g b c Φ i i) := by
        rw [k4a_appCcLeibnizPsi_succ_succ_eq (I := I) (M := M) g b c Φ i i]
        rw [if_neg (by omega : ¬ (i + 1 < i + 1)), zero_add]
      rw [hdiag]
      rw [show (k4a_slotExtendIterFib (I := I) (M := M) g b c x
            (show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φ.toSection x) (i + 1)) =
          slotExtendPointwise (I := I) (M := M) g (b + i) (c + i) x
            (k4a_slotExtendIterFib (I := I) (M := M) g b c x
              (show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φ.toSection x) i)
          from rfl]
      rw [← ih]
      rfl

omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma k4a_mvPairTraceOp_fib_toModel (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (Z : Tensor0SSpace 6 I x) (v : Fin 2 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 6 I x →L[ℝ] Tensor0SSpace 2 I x from
          (secondMetricPairTraceOp (I := I) (M := M) g₀ g₁).toSection x) Z)
        (fun j => (v j : E)) =
      ∑ b : Fin (Module.finrank ℝ E), ∑ a : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel Z
          (Fin.cons ((smoothOrthoFrame (I := I) g₁ x a x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₁ x a x : TangentSpace I x) : E)
              (Fin.cons ((smoothOrthoFrame (I := I) g₁ x b x : TangentSpace I x) : E)
                (Fin.cons ((smoothOrthoFrame (I := I) g₁ x b x : TangentSpace I x) : E)
                  (fun j => (v j : E)))))) := by
  classical
  rw [show ((show Tensor0SSpace 6 I x →L[ℝ] Tensor0SSpace 2 I x from
      (secondMetricPairTraceOp (I := I) (M := M) g₀ g₁).toSection x) Z) =
      cometricDoubleTraceFib (I := I) g₁ 2 x
        (cometricDoubleTraceFib (I := I) g₁ 4 x Z) from by
    rw [show secondMetricPairTraceOp (I := I) (M := M) g₀ g₁ =
        ccOperatorFieldComp (I := I) (M := M) g₀ 6 4 2
          (secondMetricCometricDoubleTraceField (I := I) (M := M) g₀ g₁ 2)
          (secondMetricCometricDoubleTraceField (I := I) (M := M) g₀ g₁ 4) from rfl]
    rw [appCcRS_toSection]
    rfl]
  rw [cometricDoubleTraceFib_toModel (I := I) g₁ 2 x]
  rw [modelDoubleTrace_apply (E := E) 2 (cometricLmodel (I := I) g₁ x)]
  rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) g₁ x
    (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
    (Tensor0SSpace.toModel (cometricDoubleTraceFib (I := I) g₁ 4 x Z))
    (fun j => (v j : E))]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [cometricDoubleTraceFib_toModel (I := I) g₁ 4 x Z]
  rw [modelDoubleTrace_apply (E := E) 4 (cometricLmodel (I := I) g₁ x)]
  rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) g₁ x
    (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
    (Tensor0SSpace.toModel Z)
    (Fin.cons ((smoothOrthoFrame (I := I) g₁ x b x : TangentSpace I x) : E)
      (Fin.cons ((smoothOrthoFrame (I := I) g₁ x b x : TangentSpace I x) : E)
        (fun j => (v j : E))))]

private def k4aTuple (g₁ : SmoothRiemannianMetric I M) (x : M) (i : ℕ)
    (u : Fin (2 + i) → TangentSpace I x) (a b : Fin (Module.finrank ℝ E)) :
    Fin (6 + i) → E := fun k =>
  if h : (k : ℕ) < i then ((u ⟨(k : ℕ), by omega⟩ : TangentSpace I x) : E)
  else if (k : ℕ) = i ∨ (k : ℕ) = i + 1 then
    ((smoothOrthoFrame (I := I) g₁ x a x : TangentSpace I x) : E)
  else if (k : ℕ) = i + 2 ∨ (k : ℕ) = i + 3 then
    ((smoothOrthoFrame (I := I) g₁ x b x : TangentSpace I x) : E)
  else if (k : ℕ) = i + 4 then ((u ⟨i, by omega⟩ : TangentSpace I x) : E)
  else ((u ⟨i + 1, by omega⟩ : TangentSpace I x) : E)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma k4aTuple_zero (g₁ : SmoothRiemannianMetric I M) (x : M)
    (u : Fin 2 → TangentSpace I x) (a b : Fin (Module.finrank ℝ E)) :
    k4aTuple (I := I) (M := M) g₁ x 0 u a b =
      Fin.cons ((smoothOrthoFrame (I := I) g₁ x a x : TangentSpace I x) : E)
        (Fin.cons ((smoothOrthoFrame (I := I) g₁ x a x : TangentSpace I x) : E)
          (Fin.cons ((smoothOrthoFrame (I := I) g₁ x b x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₁ x b x : TangentSpace I x) : E)
              (fun j => (u j : E))))) := by
  funext k
  fin_cases k <;> rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma k4aTuple_succ (g₁ : SmoothRiemannianMetric I M) (x : M) (w : ℕ)
    (u : Fin (2 + (w + 1)) → TangentSpace I x) (a b : Fin (Module.finrank ℝ E)) :
    k4aTuple (I := I) (M := M) g₁ x (w + 1) u a b =
      Fin.cons ((u 0 : TangentSpace I x) : E)
        (k4aTuple (I := I) (M := M) g₁ x w (fun k => u (Fin.succ k)) a b) := by
  funext k
  refine Fin.cases ?_ (fun k' => ?_) k
  · rw [Fin.cons_zero]
    unfold k4aTuple
    rw [dif_pos (by simp : ((0 : Fin (6 + (w + 1))) : ℕ) < w + 1)]
    exact congrArg u (Fin.ext (by simp))
  · rw [Fin.cons_succ]
    unfold k4aTuple
    by_cases h1 : (k' : ℕ) < w
    · rw [dif_pos (show ((Fin.succ k' : Fin (6 + (w + 1))) : ℕ) < w + 1 by
        simp only [Fin.val_succ]; omega), dif_pos h1]
      beta_reduce
      exact congrArg u (Fin.ext (by simp [Fin.val_succ]))
    · rw [dif_neg (show ¬ ((Fin.succ k' : Fin (6 + (w + 1))) : ℕ) < w + 1 by
        simp only [Fin.val_succ]; omega), dif_neg h1]
      by_cases h2 : (k' : ℕ) = w ∨ (k' : ℕ) = w + 1
      · rw [if_pos (show ((Fin.succ k' : Fin (6 + (w + 1))) : ℕ) = (w + 1) ∨
            ((Fin.succ k' : Fin (6 + (w + 1))) : ℕ) = (w + 1) + 1 by
          simp only [Fin.val_succ]; omega), if_pos h2]
      · rw [if_neg (show ¬ (((Fin.succ k' : Fin (6 + (w + 1))) : ℕ) = (w + 1) ∨
            ((Fin.succ k' : Fin (6 + (w + 1))) : ℕ) = (w + 1) + 1) by
          simp only [Fin.val_succ]; omega), if_neg h2]
        by_cases h3 : (k' : ℕ) = w + 2 ∨ (k' : ℕ) = w + 3
        · rw [if_pos (show ((Fin.succ k' : Fin (6 + (w + 1))) : ℕ) = (w + 1) + 2 ∨
              ((Fin.succ k' : Fin (6 + (w + 1))) : ℕ) = (w + 1) + 3 by
            simp only [Fin.val_succ]; omega), if_pos h3]
        · rw [if_neg (show ¬ (((Fin.succ k' : Fin (6 + (w + 1))) : ℕ) = (w + 1) + 2 ∨
              ((Fin.succ k' : Fin (6 + (w + 1))) : ℕ) = (w + 1) + 3) by
            simp only [Fin.val_succ]; omega), if_neg h3]
          by_cases h4 : (k' : ℕ) = w + 4
          · rw [if_pos (show ((Fin.succ k' : Fin (6 + (w + 1))) : ℕ) = (w + 1) + 4 by
              simp only [Fin.val_succ]; omega), if_pos h4]
            beta_reduce
            exact congrArg u (Fin.ext (by simp))
          · rw [if_neg (show ¬ ((Fin.succ k' : Fin (6 + (w + 1))) : ℕ) = (w + 1) + 4 by
              simp only [Fin.val_succ]; omega), if_neg h4]
            beta_reduce
            exact congrArg u (Fin.ext (by simp))

omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma k4a_sEIterFib_mvPT_toModel (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    ∀ (i : ℕ) (Y : Tensor0SSpace (6 + i) I x) (u : Fin (2 + i) → TangentSpace I x),
    Tensor0SSpace.toModel
        (k4a_slotExtendIterFib (I := I) (M := M) g₀ 6 2 x
          (show Tensor0SSpace 6 I x →L[ℝ] Tensor0SSpace 2 I x from
            (secondMetricPairTraceOp (I := I) (M := M) g₀ g₁).toSection x) i Y)
        (fun k => (u k : E)) =
      ∑ b : Fin (Module.finrank ℝ E), ∑ a : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel Y (k4aTuple (I := I) (M := M) g₁ x i u a b)
  | 0, Y, u => by
      rw [show k4a_slotExtendIterFib (I := I) (M := M) g₀ 6 2 x
          (show Tensor0SSpace 6 I x →L[ℝ] Tensor0SSpace 2 I x from
            (secondMetricPairTraceOp (I := I) (M := M) g₀ g₁).toSection x) 0 Y =
          (show Tensor0SSpace 6 I x →L[ℝ] Tensor0SSpace 2 I x from
            (secondMetricPairTraceOp (I := I) (M := M) g₀ g₁).toSection x) Y from rfl]
      rw [k4a_mvPairTraceOp_fib_toModel (I := I) (M := M) g₀ g₁ x Y u]
      refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
      rw [k4aTuple_zero (I := I) (M := M) g₁ x u a b]
  | (w + 1), Y, u => by
      have hu : (fun k : Fin (2 + (w + 1)) => (u k : E)) =
          Fin.cons ((u 0 : TangentSpace I x) : E)
            (fun k : Fin (2 + w) => ((u (Fin.succ k) : TangentSpace I x) : E)) := by
        funext k
        exact Fin.cases rfl (fun k' => rfl) k
      rw [show k4a_slotExtendIterFib (I := I) (M := M) g₀ 6 2 x
          (show Tensor0SSpace 6 I x →L[ℝ] Tensor0SSpace 2 I x from
            (secondMetricPairTraceOp (I := I) (M := M) g₀ g₁).toSection x) (w + 1) Y =
          slotExtendPointwise (I := I) (M := M) g₀ (6 + w) (2 + w) x
            (k4a_slotExtendIterFib (I := I) (M := M) g₀ 6 2 x
              (show Tensor0SSpace 6 I x →L[ℝ] Tensor0SSpace 2 I x from
                (secondMetricPairTraceOp (I := I) (M := M) g₀ g₁).toSection x) w) Y from rfl]
      rw [hu]
      refine Eq.trans (slotExtendFib_apply_eval (I := I) (M := M) g₀ (6 + w) (2 + w) x
        (k4a_slotExtendIterFib (I := I) (M := M) g₀ 6 2 x
          (show Tensor0SSpace 6 I x →L[ℝ] Tensor0SSpace 2 I x from
            (secondMetricPairTraceOp (I := I) (M := M) g₀ g₁).toSection x) w)
        Y ((u 0 : TangentSpace I x) : E)
        (fun k : Fin (2 + w) => ((u (Fin.succ k) : TangentSpace I x) : E))) ?_
      refine Eq.trans (k4a_sEIterFib_mvPT_toModel g₀ g₁ x w
        ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (6 + w) x) Y
          ((u 0 : TangentSpace I x) : E))
        (fun k : Fin (2 + w) => u (Fin.succ k))) ?_
      refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
      rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 6 + w)
        (T := Y) (v0 := ((u 0 : TangentSpace I x) : E))
        (vs := k4aTuple (I := I) (M := M) g₁ x w (fun k => u (Fin.succ k)) a b)]
      refine congrArg _ ?_
      exact (k4aTuple_succ (I := I) (M := M) g₁ x w u a b).symm

open DifferentialGeometry.Analysis.Sobolev.TensorHilbert in
omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma k4a_frame_collapse (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (v z : TangentSpace I x) :
    ∑ a : Fin (Module.finrank ℝ E),
        g₀.inner x v (smoothOrthoFrame (I := I) g₁ x a x) *
          g₀.inner x z (smoothOrthoFrame (I := I) g₁ x a x) =
      g₀.inner x v (metricComparisonEndo (I := I) g₀ g₁ x z) := by
  classical
  have hg1w : ∀ u : TangentSpace I x,
      g₁.inner x (metricComparisonEndo (I := I) g₀ g₁ x z) u = g₀.inner x z u := by
    intro u
    rw [gInvRaisedEndo_apply, inverseMetricSharpFib_inner]
    rw [show cotangentToDualLinear (I := I) (x := x)
        (g0FlatCLM (I := I) g₀ x z) u =
        cotangentToDual (I := I) (x := x) (g0FlatCLM (I := I) g₀ x z) u from rfl]
    rw [cotangentToDual_g0FlatCLM]
  have hrepr := mvOrthoFrame_center_repr (I := I) (M := M) g₁ x
    (metricComparisonEndo (I := I) g₀ g₁ x z)
  conv_rhs => rw [hrepr]
  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_smul, smul_eq_mul]
  have hcoef : g₁.inner x (smoothOrthoFrame (I := I) g₁ x a x)
      (metricComparisonEndo (I := I) g₀ g₁ x z) =
      g₀.inner x z (smoothOrthoFrame (I := I) g₁ x a x) := by
    rw [g₁.symm x (smoothOrthoFrame (I := I) g₁ x a x)
      (metricComparisonEndo (I := I) g₀ g₁ x z)]
    exact hg1w (smoothOrthoFrame (I := I) g₁ x a x)
  rw [hcoef]
  ring

open DifferentialGeometry.Analysis.Sobolev.TensorHilbert in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma k4a_W_op_bound (g₀ g₁ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
    {δ₀ δ : ℝ} (hδ₀ : δ₀ < 1) (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
    (hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
    (x : M) (u : TangentSpace I x) :
    g₀.inner x (metricComparisonEndo (I := I) g₀ g₁ x u) (metricComparisonEndo (I := I) g₀ g₁ x u) ≤
      (1 / (1 - δ₀)) ^ 2 * g₀.inner x u u := by
  have h1δ : (0 : ℝ) < 1 - δ := by linarith
  have h1δ₀ : (0 : ℝ) < 1 - δ₀ := by linarith
  have hs := sqrt_inner_gInvRaisedEndo_le (I := I) (M := M) g₀ g₁
    (fun y => ccTensorBilinSymm (I := I) g₀ P y) htie
    (show δ < 1 from by linarith) hδ0 hbound x u
  have h0T : 0 ≤ g₀.inner x (metricComparisonEndo (I := I) g₀ g₁ x u)
      (metricComparisonEndo (I := I) g₀ g₁ x u) :=
    DifferentialGeometry.Analysis.Laplacian.metric_inner_self_nonneg (I := I) (M := M) g₀ x _
  have h0u : 0 ≤ g₀.inner x u u :=
    DifferentialGeometry.Analysis.Laplacian.metric_inner_self_nonneg (I := I) (M := M) g₀ x u
  have hinv : 1 / (1 - δ) ≤ 1 / (1 - δ₀) := by
    rw [div_le_div_iff₀ h1δ h1δ₀]
    linarith
  have hsq := Real.sq_sqrt h0T
  have hsqu := Real.sq_sqrt h0u
  have h1 : Real.sqrt (g₀.inner x (metricComparisonEndo (I := I) g₀ g₁ x u)
      (metricComparisonEndo (I := I) g₀ g₁ x u)) ≤
      (1 / (1 - δ₀)) * Real.sqrt (g₀.inner x u u) :=
    le_trans hs (mul_le_mul_of_nonneg_right hinv (Real.sqrt_nonneg _))
  calc g₀.inner x (metricComparisonEndo (I := I) g₀ g₁ x u) (metricComparisonEndo (I := I) g₀ g₁ x u)
      = Real.sqrt (g₀.inner x (metricComparisonEndo (I := I) g₀ g₁ x u)
          (metricComparisonEndo (I := I) g₀ g₁ x u)) ^ 2 := hsq.symm
    _ ≤ ((1 / (1 - δ₀)) * Real.sqrt (g₀.inner x u u)) ^ 2 := by
        nlinarith [h1, Real.sqrt_nonneg (g₀.inner x (metricComparisonEndo (I := I) g₀ g₁ x u)
          (metricComparisonEndo (I := I) g₀ g₁ x u))]
    _ = (1 / (1 - δ₀)) ^ 2 * g₀.inner x u u := by
        rw [mul_pow, hsqu]

open DifferentialGeometry.Analysis.Sobolev.TensorHilbert in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma k4a_W_absorption (g₀ g₁ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
    {δ₀ δ : ℝ} (hδ₀ : δ₀ < 1) (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
    (hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
    (x : M) {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ i j : Fin n, g₀.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (hpars : ∀ v : TangentSpace I x,
      ∑ i : Fin n, g₀.inner x (e i) v ^ 2 = g₀.inner x v v)
    (B : Fin n → ℝ) :
    ∑ r : Fin n,
        (∑ p : Fin n, g₀.inner x (e r) (metricComparisonEndo (I := I) g₀ g₁ x (e p)) * B p) ^ 2 ≤
      (1 / (1 - δ₀)) ^ 2 * ∑ p : Fin n, (B p) ^ 2 := by
  classical
  set u : TangentSpace I x := ∑ p : Fin n, B p • e p with hu_def
  have hlin : ∀ r : Fin n,
      (∑ p : Fin n, g₀.inner x (e r) (metricComparisonEndo (I := I) g₀ g₁ x (e p)) * B p) =
        g₀.inner x (e r) (metricComparisonEndo (I := I) g₀ g₁ x u) := by
    intro r
    rw [hu_def, map_sum, map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [map_smul, map_smul, smul_eq_mul]
    ring
  rw [Finset.sum_congr rfl (fun r _ => by rw [hlin r])]
  rw [hpars (metricComparisonEndo (I := I) g₀ g₁ x u)]
  have hone : ∀ w : TangentSpace I x,
      g₀.inner x w u = ∑ q : Fin n, B q * g₀.inner x w (e q) := by
    intro w
    rw [hu_def, map_sum]
    exact Finset.sum_congr rfl fun q _ => by rw [map_smul, smul_eq_mul]
  have htwo : ∀ q : Fin n, g₀.inner x u (e q) = B q := by
    intro q
    rw [g₀.symm x u (e q), hone (e q)]
    rw [Finset.sum_congr rfl (fun p (_ : p ∈ Finset.univ) => by
      rw [horth q p] :
      ∀ p ∈ Finset.univ, B p * g₀.inner x (e q) (e p) =
        B p * (if q = p then (1 : ℝ) else 0))]
    rw [Finset.sum_eq_single q (fun p _ hp => by rw [if_neg (fun hqp => hp hqp.symm), mul_zero])
      (fun hq => absurd (Finset.mem_univ q) hq)]
    rw [if_pos rfl, mul_one]
  have hnorm : g₀.inner x u u = ∑ p : Fin n, (B p) ^ 2 := by
    calc g₀.inner x u u = ∑ q : Fin n, B q * g₀.inner x u (e q) := hone u
      _ = ∑ p : Fin n, (B p) ^ 2 := Finset.sum_congr rfl fun q _ => by rw [htwo q]; ring
  rw [← hnorm]
  exact k4a_W_op_bound (I := I) (M := M) g₀ g₁ P htie hδ₀ hδ_le hδ0 hbound x u

omit [NeZero (Module.finrank ℝ E)] in
private lemma k4a_toModel_update_sum {m : ℕ} (Zm : Tensor0SModel m ℝ E)
    (w : Fin m → E) (t : Fin m) (d : ℕ) (c : Fin d → ℝ) (u : Fin d → E) :
    Zm (Function.update w t (∑ j, c j • u j)) =
      ∑ j, c j * Zm (Function.update w t (u j)) := by
  classical
  have hgen : ∀ ss : Finset (Fin d),
      Zm (Function.update w t (∑ j ∈ ss, c j • u j)) =
        ∑ j ∈ ss, c j * Zm (Function.update w t (u j)) := by
    intro ss
    induction ss using Finset.induction_on with
    | empty =>
        rw [Finset.sum_empty, Finset.sum_empty]
        rw [show (0 : E) = ((0 : ℝ) • (0 : E)) from (zero_smul ℝ (0 : E)).symm]
        rw [ContinuousMultilinearMap.map_update_smul]
        rw [zero_smul]
    | @insert a ss ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha]
        rw [ContinuousMultilinearMap.map_update_add]
        rw [ih]
        congr 1
        rw [ContinuousMultilinearMap.map_update_smul]
        rw [smul_eq_mul]
  exact hgen Finset.univ

private def k4aR (i : ℕ) {n : ℕ} (J : Fin (2 + i) → Fin n) (p q : Fin n) :
    Fin (4 + i) → Fin n := fun t =>
  if h : (t : ℕ) < 2 + i then J ⟨(t : ℕ), h⟩
  else if (t : ℕ) = 2 + i then p
  else q

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma k4aTuple_apply_lt (g₁ : SmoothRiemannianMetric I M) (x : M) (i : ℕ)
    (u : Fin (2 + i) → TangentSpace I x) (a b : Fin (Module.finrank ℝ E))
    (t : Fin (6 + i)) (h : (t : ℕ) < i) :
    k4aTuple (I := I) (M := M) g₁ x i u a b t =
      ((u ⟨(t : ℕ), by omega⟩ : TangentSpace I x) : E) := by
  unfold k4aTuple
  rw [dif_pos h]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma k4aTuple_apply_fa (g₁ : SmoothRiemannianMetric I M) (x : M) (i : ℕ)
    (u : Fin (2 + i) → TangentSpace I x) (a b : Fin (Module.finrank ℝ E))
    (t : Fin (6 + i)) (h : (t : ℕ) = i ∨ (t : ℕ) = i + 1) :
    k4aTuple (I := I) (M := M) g₁ x i u a b t =
      ((smoothOrthoFrame (I := I) g₁ x a x : TangentSpace I x) : E) := by
  unfold k4aTuple
  rw [dif_neg (by omega), if_pos h]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma k4aTuple_apply_fb (g₁ : SmoothRiemannianMetric I M) (x : M) (i : ℕ)
    (u : Fin (2 + i) → TangentSpace I x) (a b : Fin (Module.finrank ℝ E))
    (t : Fin (6 + i)) (h : (t : ℕ) = i + 2 ∨ (t : ℕ) = i + 3) :
    k4aTuple (I := I) (M := M) g₁ x i u a b t =
      ((smoothOrthoFrame (I := I) g₁ x b x : TangentSpace I x) : E) := by
  unfold k4aTuple
  rw [dif_neg (by omega), if_neg (by omega), if_pos h]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma k4aTuple_apply_i4 (g₁ : SmoothRiemannianMetric I M) (x : M) (i : ℕ)
    (u : Fin (2 + i) → TangentSpace I x) (a b : Fin (Module.finrank ℝ E))
    (t : Fin (6 + i)) (h : (t : ℕ) = i + 4) :
    k4aTuple (I := I) (M := M) g₁ x i u a b t =
      ((u ⟨i, by omega⟩ : TangentSpace I x) : E) := by
  unfold k4aTuple
  rw [dif_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma k4aTuple_apply_last (g₁ : SmoothRiemannianMetric I M) (x : M) (i : ℕ)
    (u : Fin (2 + i) → TangentSpace I x) (a b : Fin (Module.finrank ℝ E))
    (t : Fin (6 + i)) (h : i + 5 ≤ (t : ℕ)) :
    k4aTuple (I := I) (M := M) g₁ x i u a b t =
      ((u ⟨i + 1, by omega⟩ : TangentSpace I x) : E) := by
  unfold k4aTuple
  rw [dif_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma k4a_mixTuple_eq_update (g₁ : SmoothRiemannianMetric I M) (x : M) (i : ℕ)
    {n : ℕ} (e : Fin n → TangentSpace I x) (J : Fin (2 + i) → Fin n)
    (a b : Fin (Module.finrank ℝ E)) :
    (fun q' : Fin (4 + i) =>
        k4aTuple (I := I) (M := M) g₁ x i (fun k => e (J k)) a b
          ⟨k4aArrVal i ((q' : ℕ) + 2),
            k4aArrVal_lt i ((q' : ℕ) + 2) (by have := q'.isLt; omega)⟩) =
      Function.update
        (Function.update
          (fun t : Fin (4 + i) =>
            if h : (t : ℕ) < 2 + i then ((e (J ⟨(t : ℕ), h⟩) : TangentSpace I x) : E)
            else (0 : E))
          ⟨2 + i, by omega⟩
          ((smoothOrthoFrame (I := I) g₁ x a x : TangentSpace I x) : E))
        ⟨3 + i, by omega⟩
        ((smoothOrthoFrame (I := I) g₁ x b x : TangentSpace I x) : E) := by
  classical
  funext t
  rw [Function.update_apply, Function.update_apply]
  by_cases h3 : (t : ℕ) = 3 + i
  · rw [if_pos (Fin.ext h3 : t = ⟨3 + i, by omega⟩)]
    have hidx : (⟨k4aArrVal i ((t : ℕ) + 2),
        k4aArrVal_lt i ((t : ℕ) + 2) (by have := t.isLt; omega)⟩ : Fin (6 + i)) =
        ⟨i + 2, by omega⟩ := by
      refine Fin.ext ?_
      change k4aArrVal i ((t : ℕ) + 2) = i + 2
      rw [show (t : ℕ) + 2 = i + 5 from by omega]
      exact k4aArrVal_at_i5 i
    rw [hidx]
    exact k4aTuple_apply_fb (I := I) (M := M) g₁ x i (fun k => e (J k)) a b _ (Or.inl rfl)
  · rw [if_neg (fun ht' => h3 (by rw [ht']))]
    by_cases h2 : (t : ℕ) = 2 + i
    · rw [if_pos (Fin.ext h2 : t = ⟨2 + i, by omega⟩)]
      have hidx : (⟨k4aArrVal i ((t : ℕ) + 2),
          k4aArrVal_lt i ((t : ℕ) + 2) (by have := t.isLt; omega)⟩ : Fin (6 + i)) =
          ⟨i, by omega⟩ := by
        refine Fin.ext ?_
        change k4aArrVal i ((t : ℕ) + 2) = i
        rw [show (t : ℕ) + 2 = i + 4 from by omega]
        exact k4aArrVal_at_i4 i
      rw [hidx]
      exact k4aTuple_apply_fa (I := I) (M := M) g₁ x i (fun k => e (J k)) a b _ (Or.inl rfl)
    · rw [if_neg (fun ht' => h2 (by rw [ht']))]
      have ht : (t : ℕ) < 2 + i := by have := t.isLt; omega
      rw [dif_pos ht]
      by_cases hlt : (t : ℕ) < i
      · have hidx : (⟨k4aArrVal i ((t : ℕ) + 2),
            k4aArrVal_lt i ((t : ℕ) + 2) (by have := t.isLt; omega)⟩ : Fin (6 + i)) =
            ⟨(t : ℕ), by omega⟩ := by
          refine Fin.ext ?_
          change k4aArrVal i ((t : ℕ) + 2) = (t : ℕ)
          rw [k4aArrVal_eq_sub i ((t : ℕ) + 2) (by omega) (by omega)]
          omega
        rw [hidx]
        rw [k4aTuple_apply_lt (I := I) (M := M) g₁ x i (fun k => e (J k)) a b _
          (show ((⟨(t : ℕ), by omega⟩ : Fin (6 + i)) : ℕ) < i from hlt)]
      · by_cases hi : (t : ℕ) = i
        · have hidx : (⟨k4aArrVal i ((t : ℕ) + 2),
              k4aArrVal_lt i ((t : ℕ) + 2) (by have := t.isLt; omega)⟩ : Fin (6 + i)) =
              ⟨i + 4, by omega⟩ := by
            refine Fin.ext ?_
            change k4aArrVal i ((t : ℕ) + 2) = i + 4
            rw [show (t : ℕ) + 2 = i + 2 from by omega]
            exact k4aArrVal_at_i2 i
          rw [hidx]
          rw [k4aTuple_apply_i4 (I := I) (M := M) g₁ x i (fun k => e (J k)) a b _ rfl]
          exact congrArg e (congrArg J (Fin.ext hi.symm))
        · have hi1 : (t : ℕ) = i + 1 := by omega
          have hidx : (⟨k4aArrVal i ((t : ℕ) + 2),
              k4aArrVal_lt i ((t : ℕ) + 2) (by have := t.isLt; omega)⟩ : Fin (6 + i)) =
              ⟨i + 5, by omega⟩ := by
            refine Fin.ext ?_
            change k4aArrVal i ((t : ℕ) + 2) = i + 5
            rw [show (t : ℕ) + 2 = i + 3 from by omega]
            exact k4aArrVal_at_i3 i
          rw [hidx]
          rw [k4aTuple_apply_last (I := I) (M := M) g₁ x i (fun k => e (J k)) a b _
            (le_refl (i + 5))]
          exact congrArg e (congrArg J (Fin.ext hi1.symm))

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma k4a_update_update_eq_R (x : M) (i : ℕ)
    {n : ℕ} (e : Fin n → TangentSpace I x) (J : Fin (2 + i) → Fin n) (p q : Fin n) :
    Function.update
        (Function.update
          (fun t : Fin (4 + i) =>
            if h : (t : ℕ) < 2 + i then ((e (J ⟨(t : ℕ), h⟩) : TangentSpace I x) : E)
            else (0 : E))
          ⟨2 + i, by omega⟩ ((e p : TangentSpace I x) : E))
        ⟨3 + i, by omega⟩ ((e q : TangentSpace I x) : E) =
      fun t : Fin (4 + i) => ((e (k4aR i J p q t) : TangentSpace I x) : E) := by
  classical
  funext t
  rw [Function.update_apply, Function.update_apply]
  unfold k4aR
  by_cases h3 : (t : ℕ) = 3 + i
  · rw [if_pos (Fin.ext h3 : t = ⟨3 + i, by omega⟩), dif_neg (by omega), if_neg (by omega)]
  · rw [if_neg (fun ht' => h3 (by rw [ht']))]
    by_cases h2 : (t : ℕ) = 2 + i
    · rw [if_pos (Fin.ext h2 : t = ⟨2 + i, by omega⟩), dif_neg (by omega), if_pos h2]
    · rw [if_neg (fun ht' => h2 (by rw [ht']))]
      have ht : (t : ℕ) < 2 + i := by have := t.isLt; omega
      rw [dif_pos ht, dif_pos ht]

private lemma k4aR_apply_lt (i : ℕ) {n : ℕ} (J : Fin (2 + i) → Fin n) (p q : Fin n)
    (t : Fin (4 + i)) (h : (t : ℕ) < 2 + i) :
    k4aR i J p q t = J ⟨(t : ℕ), h⟩ := by
  unfold k4aR
  rw [dif_pos h]

private lemma k4aR_apply_p (i : ℕ) {n : ℕ} (J : Fin (2 + i) → Fin n) (p q : Fin n)
    (t : Fin (4 + i)) (h : (t : ℕ) = 2 + i) :
    k4aR i J p q t = p := by
  unfold k4aR
  rw [dif_neg (by omega), if_pos h]

private lemma k4aR_apply_q (i : ℕ) {n : ℕ} (J : Fin (2 + i) → Fin n) (p q : Fin n)
    (t : Fin (4 + i)) (h2 : ¬ (t : ℕ) < 2 + i) (h3 : ¬ (t : ℕ) = 2 + i) :
    k4aR i J p q t = q := by
  unfold k4aR
  rw [dif_neg h2, if_neg h3]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma k4a_rfns_icg_order_congr (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {m m' : ℕ} (h : m = m') (S : SmoothCcTensor g r s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r (s + m) x
        ((iteratedCovGrad (I := I) g r s m S).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g r (s + m') x
        ((iteratedCovGrad (I := I) g r s m' S).toSection x) := by
  subst h
  rfl

private lemma k4a_sum_reorg {d m : ℕ} (A B : Fin d → ℝ) (C D : Fin m → Fin d → ℝ)
    (Z : Fin m → Fin m → ℝ) :
    (∑ bb : Fin d, ∑ aa : Fin d, (A aa * B bb) *
        ∑ q : Fin m, C q bb * ∑ p : Fin m, D p aa * Z p q) =
      ∑ q : Fin m, (∑ bb : Fin d, B bb * C q bb) *
        ∑ p : Fin m, (∑ aa : Fin d, A aa * D p aa) * Z p q := by
  classical
  calc (∑ bb : Fin d, ∑ aa : Fin d, (A aa * B bb) *
        ∑ q : Fin m, C q bb * ∑ p : Fin m, D p aa * Z p q)
      = ∑ bb : Fin d, ∑ aa : Fin d, ∑ q : Fin m, ∑ p : Fin m,
          (A aa * B bb) * (C q bb * (D p aa * Z p q)) := by
        refine Finset.sum_congr rfl fun bb _ => Finset.sum_congr rfl fun aa _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
    _ = ∑ bb : Fin d, ∑ q : Fin m, ∑ aa : Fin d, ∑ p : Fin m,
          (A aa * B bb) * (C q bb * (D p aa * Z p q)) :=
        Finset.sum_congr rfl fun bb _ => Finset.sum_comm
    _ = ∑ bb : Fin d, ∑ q : Fin m, ∑ p : Fin m, ∑ aa : Fin d,
          (A aa * B bb) * (C q bb * (D p aa * Z p q)) :=
        Finset.sum_congr rfl fun bb _ => Finset.sum_congr rfl fun q _ => Finset.sum_comm
    _ = ∑ q : Fin m, ∑ bb : Fin d, ∑ p : Fin m, ∑ aa : Fin d,
          (A aa * B bb) * (C q bb * (D p aa * Z p q)) := Finset.sum_comm
    _ = ∑ q : Fin m, ∑ p : Fin m, ∑ bb : Fin d, ∑ aa : Fin d,
          (A aa * B bb) * (C q bb * (D p aa * Z p q)) :=
        Finset.sum_congr rfl fun q _ => Finset.sum_comm
    _ = ∑ q : Fin m, (∑ bb : Fin d, B bb * C q bb) *
          ∑ p : Fin m, (∑ aa : Fin d, A aa * D p aa) * Z p q := by
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun bb _ => ?_
        rw [show (B bb * C q bb) * ((∑ aa : Fin d, A aa * D p aa) * Z p q) =
            (∑ aa : Fin d, A aa * D p aa) * ((B bb * C q bb) * Z p q) from by ring]
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun aa _ => ?_
        ring

open DifferentialGeometry.Analysis.Sobolev.TensorHilbert in
set_option maxHeartbeats 6400000 in

theorem riemannianFiberNormSq_compRS_mvPairTraceOp_leibnizCorner_le
    (g₀ g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
    {δ₀ δ : ℝ} (hδ₀ : δ₀ < 1) (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
    (hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
    (σ : Equiv.Perm (Fin 4)) (i : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((ccOperatorFieldComp (I := I) (M := M) g₀ 2 (6 + i) (2 + i)
          (appCcLeibnizPsi (I := I) (M := M) g₀ 6 2
            (secondMetricPairTraceOp (I := I) (M := M) g₀ g₁) i i)
          (iteratedCovGrad (I := I) g₀ 2 6 i
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 ricciFoldRemainderSlotPerm
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (domDomCongrSection (I := I) g₀
                  (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ)
                  (iteratedCovGrad (I := I) g₀ 0 2 2
                    (ccTensor02Symm (I := I) (M := M) g₀ P))))))).toSection x) ≤
      ((1 / (1 - δ₀)) ^ 2) ^ 2 *
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x) := by
  classical
  set V : SmoothCcTensor g₀ 0 4 :=
    domDomCongrSection (I := I) g₀
      (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ)
      (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P)) with hV_def
  obtain ⟨n, e, bse, hn, hbse, horth, hpars, hrepr, _⟩ :=
    tangent_orthonormalBasis_witness (I := I) (M := M) g₀ x
  have hnE : n = Module.finrank ℝ E := by rw [hn]; rfl
  set Zm : Tensor0SModel (4 + i) ℝ E :=
    unitModel (I := I) (M := M) g₀ (4 + i) (iteratedCovGrad (I := I) g₀ 0 4 i V) x
    with hZm_def
  set Zc : (Fin (2 + i) → Fin n) → Fin n → Fin n → ℝ := fun J p q =>
    Zm (fun t => ((e (k4aR i J p q t) : TangentSpace I x) : E)) with hZc_def
  rw [rfns_eq_sum_componentSq_of_horth_pt (I := I) (M := M) g₀ 2 (2 + i) x _ e hnE horth]
  have hexp_fa : ∀ c : Fin (Module.finrank ℝ E),
      ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E) =
        ∑ p : Fin n, g₀.inner x (e p) (smoothOrthoFrame (I := I) g₁ x c x) •
          ((e p : TangentSpace I x) : E) :=
    fun c => hrepr (smoothOrthoFrame (I := I) g₁ x c x)
  have hupdcomm : ((⟨2 + i, by omega⟩ : Fin (4 + i))) ≠ (⟨3 + i, by omega⟩ : Fin (4 + i)) :=
    fun hcontra => by simpa using congrArg Fin.val hcontra
  have hcomp : ∀ (K : Fin 2 → Fin n) (J : Fin (2 + i) → Fin n),
      fiberNormSqComponent (I := I) (M := M) g₀ x 2 (2 + i)
        ((ccOperatorFieldComp (I := I) (M := M) g₀ 2 (6 + i) (2 + i)
          (appCcLeibnizPsi (I := I) (M := M) g₀ 6 2
            (secondMetricPairTraceOp (I := I) (M := M) g₀ g₁) i i)
          (iteratedCovGrad (I := I) g₀ 2 6 i
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 ricciFoldRemainderSlotPerm
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2 V)))).toSection x) n e K J =
        ∑ q : Fin n,
          g₀.inner x (e (K 1)) (metricComparisonEndo (I := I) g₀ g₁ x (e q)) *
            ∑ p : Fin n,
              g₀.inner x (e (K 0)) (metricComparisonEndo (I := I) g₀ g₁ x (e p)) * Zc J p q := by
    intro K J
    have hdiag := k4a_appCcLeibnizPsi_diag_toSection (I := I) (M := M) g₀ 6 2
      (secondMetricPairTraceOp (I := I) (M := M) g₀ g₁) i x
    have h1 : fiberNormSqComponent (I := I) (M := M) g₀ x 2 (2 + i)
        ((ccOperatorFieldComp (I := I) (M := M) g₀ 2 (6 + i) (2 + i)
          (appCcLeibnizPsi (I := I) (M := M) g₀ 6 2
            (secondMetricPairTraceOp (I := I) (M := M) g₀ g₁) i i)
          (iteratedCovGrad (I := I) g₀ 2 6 i
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 ricciFoldRemainderSlotPerm
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2 V)))).toSection x) n e K J =
        Tensor0SSpace.toModel
          ((k4a_slotExtendIterFib (I := I) (M := M) g₀ 6 2 x
            (show Tensor0SSpace 6 I x →L[ℝ] Tensor0SSpace 2 I x from
              (secondMetricPairTraceOp (I := I) (M := M) g₀ g₁).toSection x) i)
            ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace (6 + i) I x from
              (iteratedCovGrad (I := I) g₀ 2 6 i
                (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 ricciFoldRemainderSlotPerm
                  (slotExtendIter (I := I) (M := M) g₀ 0 4 2 V))).toSection x)
              (coframeS (I := I) (M := M) g₀ x 2 e K)))
          (fun k => (e (J k) : E)) := by
      rw [← hdiag]
      rfl
    rw [h1]
    refine Eq.trans (k4a_sEIterFib_mvPT_toModel g₀ g₁ x i
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace (6 + i) I x from
        (iteratedCovGrad (I := I) g₀ 2 6 i
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 ricciFoldRemainderSlotPerm
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2 V))).toSection x)
        (coframeS (I := I) (M := M) g₀ x 2 e K))
      (fun k => e (J k))) ?_
    have hterm : ∀ (bb aa : Fin (Module.finrank ℝ E)),
        Tensor0SSpace.toModel
            ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace (6 + i) I x from
              (iteratedCovGrad (I := I) g₀ 2 6 i
                (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 ricciFoldRemainderSlotPerm
                  (slotExtendIter (I := I) (M := M) g₀ 0 4 2 V))).toSection x)
              (coframeS (I := I) (M := M) g₀ x 2 e K))
            (k4aTuple (I := I) (M := M) g₁ x i (fun k => e (J k)) aa bb) =
          (g₀.inner x (e (K 0)) (smoothOrthoFrame (I := I) g₁ x aa x) *
            g₀.inner x (e (K 1)) (smoothOrthoFrame (I := I) g₁ x bb x)) *
            ∑ q : Fin n, g₀.inner x (e q) (smoothOrthoFrame (I := I) g₁ x bb x) *
              ∑ p : Fin n, g₀.inner x (e p) (smoothOrthoFrame (I := I) g₁ x aa x) *
                Zc J p q := by
      intro bb aa
      refine Eq.trans (k4a_icg_refoldArgument_toModel (I := I) (M := M) g₀ V i x
        (coframeS (I := I) (M := M) g₀ x 2 e K)
        (fun k => k4aTuple (E := E) (I := I) (M := M) g₁ x i
          (fun k' => e (J k')) aa bb k)) ?_
      beta_reduce
      rw [k4aTuple_apply_fa (I := I) (M := M) g₁ x i (fun k' => e (J k')) aa bb
        ⟨i + 1, by omega⟩ (Or.inr rfl)]
      rw [k4aTuple_apply_fb (I := I) (M := M) g₁ x i (fun k' => e (J k')) aa bb
        ⟨i + 3, by omega⟩ (Or.inr rfl)]
      have hcof : Tensor0SSpace.toModel (coframeS (I := I) (M := M) g₀ x 2 e K)
          ![((smoothOrthoFrame (I := I) g₁ x aa x : TangentSpace I x) : E),
            ((smoothOrthoFrame (I := I) g₁ x bb x : TangentSpace I x) : E)] =
          g₀.inner x (e (K 0)) (smoothOrthoFrame (I := I) g₁ x aa x) *
            g₀.inner x (e (K 1)) (smoothOrthoFrame (I := I) g₁ x bb x) := by
        have h := coframeS_apply (I := I) (M := M) g₀ x 2 e K
          ![smoothOrthoFrame (I := I) g₁ x aa x, smoothOrthoFrame (I := I) g₁ x bb x]
        rw [show Tensor0SSpace.toModel (coframeS (I := I) (M := M) g₀ x 2 e K)
            ![((smoothOrthoFrame (I := I) g₁ x aa x : TangentSpace I x) : E),
              ((smoothOrthoFrame (I := I) g₁ x bb x : TangentSpace I x) : E)] =
            coframeS (I := I) (M := M) g₀ x 2 e K
              ![smoothOrthoFrame (I := I) g₁ x aa x,
                smoothOrthoFrame (I := I) g₁ x bb x] from rfl]
        rw [h, Fin.prod_univ_two]
        rfl
      rw [hcof]
      refine congrArg _ ?_
      refine Eq.trans (congrArg Zm (k4a_mixTuple_eq_update (I := I) (M := M) g₁ x i e J
        aa bb)) ?_
      conv_lhs => rw [show ((smoothOrthoFrame (I := I) g₁ x bb x : TangentSpace I x) : E) =
          ∑ q : Fin n, g₀.inner x (e q) (smoothOrthoFrame (I := I) g₁ x bb x) •
            ((e q : TangentSpace I x) : E) from hexp_fa bb]
      rw [k4a_toModel_update_sum Zm _ ⟨3 + i, by omega⟩ n
        (fun q => g₀.inner x (e q) (smoothOrthoFrame (I := I) g₁ x bb x))
        (fun q => ((e q : TangentSpace I x) : E))]
      refine Finset.sum_congr rfl fun q _ => ?_
      refine congrArg _ ?_
      rw [Function.update_comm hupdcomm]
      conv_lhs => rw [show ((smoothOrthoFrame (I := I) g₁ x aa x : TangentSpace I x) : E) =
          ∑ p : Fin n, g₀.inner x (e p) (smoothOrthoFrame (I := I) g₁ x aa x) •
            ((e p : TangentSpace I x) : E) from hexp_fa aa]
      rw [k4a_toModel_update_sum Zm _ ⟨2 + i, by omega⟩ n
        (fun p => g₀.inner x (e p) (smoothOrthoFrame (I := I) g₁ x aa x))
        (fun p => ((e p : TangentSpace I x) : E))]
      refine Finset.sum_congr rfl fun p _ => ?_
      refine congrArg _ ?_
      rw [Function.update_comm (Ne.symm hupdcomm)]
      rw [k4a_update_update_eq_R (I := I) (M := M) x i e J p q]
    refine Eq.trans (Finset.sum_congr rfl fun bb _ => Finset.sum_congr rfl fun aa _ =>
      hterm bb aa) ?_
    refine Eq.trans (k4a_sum_reorg
      (fun aa => g₀.inner x (e (K 0)) (smoothOrthoFrame (I := I) g₁ x aa x))
      (fun bb => g₀.inner x (e (K 1)) (smoothOrthoFrame (I := I) g₁ x bb x))
      (fun q bb => g₀.inner x (e q) (smoothOrthoFrame (I := I) g₁ x bb x))
      (fun p aa => g₀.inner x (e p) (smoothOrthoFrame (I := I) g₁ x aa x))
      (fun p q => Zc J p q)) ?_
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [k4a_frame_collapse (I := I) (M := M) g₀ g₁ x (e (K 1)) (e q)]
    refine congrArg _ ?_
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [k4a_frame_collapse (I := I) (M := M) g₀ g₁ x (e (K 0)) (e p)]
  rw [Finset.sum_congr rfl (fun K (_ : K ∈ Finset.univ) => Finset.sum_congr rfl
    (fun J (_ : J ∈ Finset.univ) => by rw [hcomp K J]))]
  have habs1 : ∀ (J : Fin (2 + i) → Fin n) (k0 : Fin n),
      (∑ k1 : Fin n, (∑ q : Fin n,
          g₀.inner x (e k1) (metricComparisonEndo (I := I) g₀ g₁ x (e q)) *
            ∑ p : Fin n,
              g₀.inner x (e k0) (metricComparisonEndo (I := I) g₀ g₁ x (e p)) * Zc J p q) ^ 2) ≤
        (1 / (1 - δ₀)) ^ 2 * ∑ q : Fin n,
          (∑ p : Fin n,
            g₀.inner x (e k0) (metricComparisonEndo (I := I) g₀ g₁ x (e p)) * Zc J p q) ^ 2 :=
    fun J k0 => k4a_W_absorption (I := I) (M := M) g₀ g₁ P htie hδ₀ hδ_le hδ0 hbound x e
      horth hpars (fun q => ∑ p : Fin n,
        g₀.inner x (e k0) (metricComparisonEndo (I := I) g₀ g₁ x (e p)) * Zc J p q)
  have habs0 : ∀ (J : Fin (2 + i) → Fin n) (q : Fin n),
      (∑ k0 : Fin n, (∑ p : Fin n,
          g₀.inner x (e k0) (metricComparisonEndo (I := I) g₀ g₁ x (e p)) * Zc J p q) ^ 2) ≤
        (1 / (1 - δ₀)) ^ 2 * ∑ p : Fin n, (Zc J p q) ^ 2 :=
    fun J q => k4a_W_absorption (I := I) (M := M) g₀ g₁ P htie hδ₀ hδ_le hδ0 hbound x e
      horth hpars (fun p => Zc J p q)
  have hd2_nn : (0 : ℝ) ≤ (1 / (1 - δ₀)) ^ 2 := sq_nonneg _
  have hKsplit : (∑ K : Fin 2 → Fin n, ∑ J : Fin (2 + i) → Fin n,
      (∑ q : Fin n,
        g₀.inner x (e (K 1)) (metricComparisonEndo (I := I) g₀ g₁ x (e q)) *
          ∑ p : Fin n,
            g₀.inner x (e (K 0)) (metricComparisonEndo (I := I) g₀ g₁ x (e p)) * Zc J p q) ^ 2) =
      ∑ J : Fin (2 + i) → Fin n, ∑ k0 : Fin n, ∑ k1 : Fin n,
        (∑ q : Fin n,
          g₀.inner x (e k1) (metricComparisonEndo (I := I) g₀ g₁ x (e q)) *
            ∑ p : Fin n,
              g₀.inner x (e k0) (metricComparisonEndo (I := I) g₀ g₁ x (e p)) * Zc J p q) ^ 2 := by
    refine Eq.trans Finset.sum_comm ?_
    refine Finset.sum_congr rfl fun J _ => ?_
    calc (∑ K : Fin 2 → Fin n,
        (∑ q : Fin n,
          g₀.inner x (e (K 1)) (metricComparisonEndo (I := I) g₀ g₁ x (e q)) *
            ∑ p : Fin n,
              g₀.inner x (e (K 0)) (metricComparisonEndo (I := I) g₀ g₁ x (e p)) * Zc J p q) ^ 2)
        = ∑ pr : Fin n × Fin n,
            (∑ q : Fin n,
              g₀.inner x (e pr.2) (metricComparisonEndo (I := I) g₀ g₁ x (e q)) *
                ∑ p : Fin n,
                  g₀.inner x (e pr.1) (metricComparisonEndo (I := I) g₀ g₁ x (e p)) *
                    Zc J p q) ^ 2 :=
          Fintype.sum_equiv (finTwoArrowEquiv (Fin n)) _ _ (fun K => rfl)
      _ = ∑ k0 : Fin n, ∑ k1 : Fin n,
            (∑ q : Fin n,
              g₀.inner x (e k1) (metricComparisonEndo (I := I) g₀ g₁ x (e q)) *
                ∑ p : Fin n,
                  g₀.inner x (e k0) (metricComparisonEndo (I := I) g₀ g₁ x (e p)) *
                    Zc J p q) ^ 2 := Fintype.sum_prod_type _
  rw [hKsplit]
  have hstep1 : (∑ J : Fin (2 + i) → Fin n, ∑ k0 : Fin n, ∑ k1 : Fin n,
      (∑ q : Fin n,
        g₀.inner x (e k1) (metricComparisonEndo (I := I) g₀ g₁ x (e q)) *
          ∑ p : Fin n,
            g₀.inner x (e k0) (metricComparisonEndo (I := I) g₀ g₁ x (e p)) * Zc J p q) ^ 2) ≤
      (1 / (1 - δ₀)) ^ 2 * ((1 / (1 - δ₀)) ^ 2 *
        ∑ J : Fin (2 + i) → Fin n, ∑ q : Fin n, ∑ p : Fin n, (Zc J p q) ^ 2) := by
    calc (∑ J : Fin (2 + i) → Fin n, ∑ k0 : Fin n, ∑ k1 : Fin n,
        (∑ q : Fin n,
          g₀.inner x (e k1) (metricComparisonEndo (I := I) g₀ g₁ x (e q)) *
            ∑ p : Fin n,
              g₀.inner x (e k0) (metricComparisonEndo (I := I) g₀ g₁ x (e p)) * Zc J p q) ^ 2)
        ≤ ∑ J : Fin (2 + i) → Fin n, ∑ k0 : Fin n, (1 / (1 - δ₀)) ^ 2 *
            ∑ q : Fin n, (∑ p : Fin n,
              g₀.inner x (e k0) (metricComparisonEndo (I := I) g₀ g₁ x (e p)) * Zc J p q) ^ 2 :=
          Finset.sum_le_sum fun J _ => Finset.sum_le_sum fun k0 _ => habs1 J k0
      _ = ∑ J : Fin (2 + i) → Fin n, ((1 / (1 - δ₀)) ^ 2 *
            ∑ q : Fin n, ∑ k0 : Fin n, (∑ p : Fin n,
              g₀.inner x (e k0) (metricComparisonEndo (I := I) g₀ g₁ x (e p)) * Zc J p q) ^ 2) :=
          Finset.sum_congr rfl fun J _ =>
            Eq.trans (Finset.mul_sum _ _ _).symm
              (congrArg (fun t => (1 / (1 - δ₀)) ^ 2 * t) Finset.sum_comm)
      _ ≤ ∑ J : Fin (2 + i) → Fin n, ((1 / (1 - δ₀)) ^ 2 *
            ∑ q : Fin n, ((1 / (1 - δ₀)) ^ 2 * ∑ p : Fin n, (Zc J p q) ^ 2)) := by
          refine Finset.sum_le_sum fun J _ => ?_
          refine mul_le_mul_of_nonneg_left ?_ hd2_nn
          exact Finset.sum_le_sum fun q _ => habs0 J q
      _ = ∑ J : Fin (2 + i) → Fin n, ((1 / (1 - δ₀)) ^ 2 * ((1 / (1 - δ₀)) ^ 2 *
            ∑ q : Fin n, ∑ p : Fin n, (Zc J p q) ^ 2)) :=
          Finset.sum_congr rfl fun J _ =>
            congrArg (fun t => (1 / (1 - δ₀)) ^ 2 * t) (Finset.mul_sum _ _ _).symm
      _ = (1 / (1 - δ₀)) ^ 2 * ((1 / (1 - δ₀)) ^ 2 *
            ∑ J : Fin (2 + i) → Fin n, ∑ q : Fin n, ∑ p : Fin n, (Zc J p q) ^ 2) := by
          rw [← Finset.mul_sum, ← Finset.mul_sum]
  refine le_trans hstep1 ?_
  have hbij : (∑ J : Fin (2 + i) → Fin n, ∑ q : Fin n, ∑ p : Fin n, (Zc J p q) ^ 2) =
      ∑ R : Fin (4 + i) → Fin n,
        (Zm (fun t => ((e (R t) : TangentSpace I x) : E))) ^ 2 := by
    rw [show (∑ J : Fin (2 + i) → Fin n, ∑ q : Fin n, ∑ p : Fin n, (Zc J p q) ^ 2) =
        ∑ tr : (Fin (2 + i) → Fin n) × Fin n × Fin n,
          (Zc tr.1 tr.2.2 tr.2.1) ^ 2 from by
      rw [Fintype.sum_prod_type]
      exact Finset.sum_congr rfl fun J _ =>
        (Fintype.sum_prod_type (fun y : Fin n × Fin n => (Zc J y.2 y.1) ^ 2)).symm]
    refine Fintype.sum_bijective
      (fun tr : (Fin (2 + i) → Fin n) × Fin n × Fin n => k4aR i tr.1 tr.2.2 tr.2.1) ?_ _ _
      (fun tr => by rw [hZc_def])
    refine Function.bijective_iff_has_inverse.mpr
      ⟨fun R => (fun j => R ⟨(j : ℕ), by have := j.isLt; omega⟩,
        R ⟨3 + i, by omega⟩, R ⟨2 + i, by omega⟩), ?_, ?_⟩
    · rintro ⟨J', qq, pp⟩
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · funext j
        refine Eq.trans (k4aR_apply_lt i J' pp qq ⟨(j : ℕ), by have := j.isLt; omega⟩
          j.isLt) ?_
        exact congrArg J' (Fin.ext rfl)
      · exact k4aR_apply_q i J' pp qq ⟨3 + i, by omega⟩
          (by change ¬(3 + i < 2 + i); omega) (by change ¬(3 + i = 2 + i); omega)
      · exact k4aR_apply_p i J' pp qq ⟨2 + i, by omega⟩ rfl
    · intro R
      funext t
      change k4aR i (fun j => R ⟨(j : ℕ), by have := j.isLt; omega⟩)
        (R ⟨2 + i, by omega⟩) (R ⟨3 + i, by omega⟩) t = R t
      by_cases hlt : (t : ℕ) < 2 + i
      · refine Eq.trans (k4aR_apply_lt i _ _ _ t hlt) ?_
        exact congrArg R (Fin.ext rfl)
      · by_cases heq2 : (t : ℕ) = 2 + i
        · refine Eq.trans (k4aR_apply_p i _ _ _ t heq2) ?_
          exact congrArg R (Fin.ext (by simpa using heq2.symm))
        · refine Eq.trans (k4aR_apply_q i _ _ _ t hlt heq2) ?_
          have heq3 : (t : ℕ) = 3 + i := by have := t.isLt; omega
          exact congrArg R (Fin.ext (by simpa using heq3.symm))
  rw [hbij]
  have hZmass : (∑ R : Fin (4 + i) → Fin n,
      (Zm (fun t => ((e (R t) : TangentSpace I x) : E))) ^ 2) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
        ((iteratedCovGrad (I := I) g₀ 0 4 i V).toSection x) := by
    rw [rfns_eq_sum_componentSq_of_horth_pt (I := I) (M := M) g₀ 0 (4 + i) x
      ((iteratedCovGrad (I := I) g₀ 0 4 i V).toSection x) e hnE horth]
    rw [Fintype.sum_unique (fun K : Fin 0 → Fin n =>
      ∑ R : Fin (4 + i) → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g₀ x 0 (4 + i)
          ((iteratedCovGrad (I := I) g₀ 0 4 i V).toSection x) n e K R) ^ 2)]
    refine Finset.sum_congr rfl fun R _ => ?_
    refine congrArg (· ^ 2) ?_
    refine Eq.trans ?_ (fiberNormSqComponent_zero_toModel_pt (I := I) (M := M) g₀ (4 + i) x
      (iteratedCovGrad (I := I) g₀ 0 4 i V) e default R).symm
    rfl
  rw [hZmass]
  have hVjets : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
      ((iteratedCovGrad (I := I) g₀ 0 4 i V).toSection x) ≤
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x) := by
    calc riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
          ((iteratedCovGrad (I := I) g₀ 0 4 i V).toSection x)
        = riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 4 i
              (iteratedCovGrad (I := I) g₀ 0 2 2
                (ccTensor02Symm (I := I) (M := M) g₀ P))).toSection x) := by
          rw [hV_def]
          exact riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M)
            g₀ (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ)
            (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P)) i x
      _ = riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (2 + i)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (2 + i)
              (ccTensor02Symm (I := I) (M := M) g₀ P)).toSection x) :=
          riemannianFiberNormSq_iteratedCovGrad_comp (I := I) (M := M) g₀ 0 2 2 i
            (ccTensor02Symm (I := I) (M := M) g₀ P) x
      _ ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (2 + i)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (2 + i) P).toSection x) :=
          rfns_iteratedCovGrad_symmS_pointwise (I := I) (M := M) g₀ P (2 + i) x
      _ = riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x) :=
          k4a_rfns_icg_order_congr (I := I) (M := M) g₀ 0 2
            (by omega : 2 + i = i + 2) P x
  calc (1 / (1 - δ₀)) ^ 2 * ((1 / (1 - δ₀)) ^ 2 *
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
          ((iteratedCovGrad (I := I) g₀ 0 4 i V).toSection x))
      ≤ (1 / (1 - δ₀)) ^ 2 * ((1 / (1 - δ₀)) ^ 2 *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hVjets hd2_nn) hd2_nn
    _ = ((1 / (1 - δ₀)) ^ 2) ^ 2 *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x) := by
        ring


theorem exists_rfns_icg_refoldKernelContractionMonomialField_leibnizResidual_window
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (σ : Equiv.Perm (Fin 4)) (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁
                (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P))
                σ)).toSection x
              - (ccOperatorFieldComp (I := I) (M := M) g₀ 2 (6 + i) (2 + i)
                (appCcLeibnizPsi (I := I) (M := M) g₀ 6 2
                  (secondMetricPairTraceOp (I := I) (M := M) g₀ g₁) i i)
                (iteratedCovGrad (I := I) g₀ 2 6 i
                  (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 ricciFoldRemainderSlotPerm
                    (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                      (domDomCongrSection (I := I) g₀
                        (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ)
                        (iteratedCovGrad (I := I) g₀ 0 2 2
                          (ccTensor02Symm (I := I) (M := M) g₀ P))))))).toSection x) ≤
          K i * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3) := by
  classical
  obtain ⟨CPT, hCPT_nn, hCPT⟩ :=
    exists_rfns_icg_mvPairTraceOp_window (I := I) (M := M) g₀ hδ₀
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : (0 : ℝ) ≤ fr := Nat.cast_nonneg _
  refine ⟨fun i => (i : ℝ) * diagonalGridGrowthFactor (E := E) i *
      ∑ k ∈ Finset.range i, CPT (i - k) * fr ^ 2,
    fun i => mul_nonneg (mul_nonneg (Nat.cast_nonneg i) (appCcGdiag_nonneg (E := E) i))
      (Finset.sum_nonneg fun k _ => mul_nonneg (hCPT_nn (i - k)) (by positivity)), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hbound σ i x
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) with hb_def
  have hb_nn : ∀ l, 0 ≤ b l :=
    fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  set Xarg : SmoothCcTensor g₀ 2 6 :=
    rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 ricciFoldRemainderSlotPerm
      (slotExtendIter (I := I) (M := M) g₀ 0 4 2
        (domDomCongrSection (I := I) g₀
          (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ)
          (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P))))
    with hX_def
  have hsub : (iteratedCovGrad (I := I) g₀ 2 2 i
      (refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁
        (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P))
        σ)).toSection x
      - (ccOperatorFieldComp (I := I) (M := M) g₀ 2 (6 + i) (2 + i)
        (appCcLeibnizPsi (I := I) (M := M) g₀ 6 2
          (secondMetricPairTraceOp (I := I) (M := M) g₀ g₁) i i)
        (iteratedCovGrad (I := I) g₀ 2 6 i Xarg)).toSection x =
      ((∑ k ∈ Finset.range i,
        ccOperatorFieldComp (I := I) (M := M) g₀ 2 (6 + k) (2 + i)
          (appCcLeibnizPsi (I := I) (M := M) g₀ 6 2
            (secondMetricPairTraceOp (I := I) (M := M) g₀ g₁) i k)
          (iteratedCovGrad (I := I) g₀ 2 6 k Xarg)).toSection x) := by
    rw [refoldKernelContractionMonomialField_eq_mvPairTraceRefold (I := I) (M := M) g₀ g₁
      (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P)) σ]
    rw [← hX_def]
    rw [iteratedCovGrad_appCcRS_eq_argCorner_add_lower (I := I) (M := M) g₀ 2 6 2
      (secondMetricPairTraceOp (I := I) (M := M) g₀ g₁) Xarg i]
    rw [show ((ccOperatorFieldComp (I := I) (M := M) g₀ 2 (6 + i) (2 + i)
        (appCcLeibnizPsi (I := I) (M := M) g₀ 6 2
          (secondMetricPairTraceOp (I := I) (M := M) g₀ g₁) i i)
        (iteratedCovGrad (I := I) g₀ 2 6 i Xarg) +
        ∑ k ∈ Finset.range i,
          ccOperatorFieldComp (I := I) (M := M) g₀ 2 (6 + k) (2 + i)
            (appCcLeibnizPsi (I := I) (M := M) g₀ 6 2
              (secondMetricPairTraceOp (I := I) (M := M) g₀ g₁) i k)
            (iteratedCovGrad (I := I) g₀ 2 6 k Xarg)).toSection x) =
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 (6 + i) (2 + i)
          (appCcLeibnizPsi (I := I) (M := M) g₀ 6 2
            (secondMetricPairTraceOp (I := I) (M := M) g₀ g₁) i i)
          (iteratedCovGrad (I := I) g₀ 2 6 i Xarg)).toSection x +
        (∑ k ∈ Finset.range i,
          ccOperatorFieldComp (I := I) (M := M) g₀ 2 (6 + k) (2 + i)
            (appCcLeibnizPsi (I := I) (M := M) g₀ 6 2
              (secondMetricPairTraceOp (I := I) (M := M) g₀ g₁) i k)
            (iteratedCovGrad (I := I) g₀ 2 6 k Xarg)).toSection x from by
      rw [SmoothCcTensor.toSection_add]
      rfl]
    rw [add_sub_cancel_left]
  rw [hsub]
  refine le_trans (rfns_appCcRS_argLower_le (I := I) (M := M) g₀ 2 6 2
    (secondMetricPairTraceOp (I := I) (M := M) g₀ g₁) Xarg i x) ?_
  have hWb : ∀ k : ℕ,
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + k) x
          ((iteratedCovGrad (I := I) g₀ 2 6 k Xarg).toSection x) ≤
        fr ^ 2 * b (2 + k) := by
    intro k
    rw [hX_def]
    rw [riemannianFiberNormSq_iteratedCovGrad_rsDomDomCongrSection_eq (I := I) (M := M) g₀ 2 6 ricciFoldRemainderSlotPerm _ k x]
    rw [show slotExtendIter (I := I) (M := M) g₀ 0 4 2
        (domDomCongrSection (I := I) g₀
          (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ)
          (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P))) =
        slotExtend (I := I) (M := M) g₀ 1 5
          (slotExtend (I := I) (M := M) g₀ 0 4
            (domDomCongrSection (I := I) g₀
              (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ)
              (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P))))
        from rfl]
    refine le_trans (rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 1 5 _ k x) ?_
    refine le_trans (mul_le_mul_of_nonneg_left
      (rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 0 4 _ k x) hfr_nn) ?_
    rw [riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ)
      (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P)) k x]
    rw [riemannianFiberNormSq_iteratedCovGrad_comp (I := I) (M := M) g₀ 0 2 2 k
      (ccTensor02Symm (I := I) (M := M) g₀ P) x]
    have hstep := rfns_iteratedCovGrad_symmS_pointwise (I := I) (M := M) g₀ P (2 + k) x
    calc fr * (fr * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (2 + k)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (2 + k)
              (ccTensor02Symm (I := I) (M := M) g₀ P)).toSection x))
        ≤ fr * (fr * b (2 + k)) := by
          refine mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hstep hfr_nn) hfr_nn
      _ = fr ^ 2 * b (2 + k) := by ring
  have hterm : ∀ k ∈ Finset.range i,
      riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + (i - k)) x
          ((iteratedCovGrad (I := I) g₀ 6 2 (i - k)
            (secondMetricPairTraceOp (I := I) (M := M) g₀ g₁)).toSection x) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + k) x
          ((iteratedCovGrad (I := I) g₀ 2 6 k Xarg).toSection x) ≤
      (CPT (i - k) * fr ^ 2) * Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hker := hCPT g₁ P htie hδ_le hδ0 hbound (i - k) (i + 1) (by omega) x
    have harg := hWb k
    have hker_nn : (0 : ℝ) ≤ CPT (i - k) * Combinatorics.boundedFactorGridWindow b
        (i + 1) ((i - k) + 1) :=
      mul_nonneg (hCPT_nn (i - k))
        (Combinatorics.boundedFactorGridWindow_nonneg b hb_nn _ _)
    refine le_trans (mul_le_mul hker harg
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (6 + k) x _) hker_nn) ?_
    have habsorb : b (2 + k) * Combinatorics.boundedFactorGridWindow b (i + 1)
        ((i - k) + 1) ≤
        Combinatorics.boundedFactorGridWindow b (i + 1) (((i - k) + 1) + (2 + k)) :=
      Combinatorics.single_factor_mul_boundedFactorGridWindow_le b hb_nn
        (by omega) (by omega)
    calc (CPT (i - k) * Combinatorics.boundedFactorGridWindow b (i + 1) ((i - k) + 1)) *
          (fr ^ 2 * b (2 + k))
        = (CPT (i - k) * fr ^ 2) *
            (b (2 + k) * Combinatorics.boundedFactorGridWindow b (i + 1) ((i - k) + 1)) := by
          ring
      _ ≤ (CPT (i - k) * fr ^ 2) *
            Combinatorics.boundedFactorGridWindow b (i + 1) (((i - k) + 1) + (2 + k)) :=
          mul_le_mul_of_nonneg_left habsorb
            (mul_nonneg (hCPT_nn (i - k)) (by positivity))
      _ = (CPT (i - k) * fr ^ 2) *
            Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) := by
          rw [show ((i - k) + 1) + (2 + k) = i + 3 from by omega]
  calc (i : ℝ) * diagonalGridGrowthFactor (E := E) i *
        ∑ k ∈ Finset.range i,
          riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + (i - k)) x
              ((iteratedCovGrad (I := I) g₀ 6 2 (i - k)
                (secondMetricPairTraceOp (I := I) (M := M) g₀ g₁)).toSection x) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + k) x
              ((iteratedCovGrad (I := I) g₀ 2 6 k Xarg).toSection x)
      ≤ (i : ℝ) * diagonalGridGrowthFactor (E := E) i *
          ∑ k ∈ Finset.range i,
            (CPT (i - k) * fr ^ 2) *
              Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm)
          (mul_nonneg (Nat.cast_nonneg i) (appCcGdiag_nonneg (E := E) i))
    _ = ((i : ℝ) * diagonalGridGrowthFactor (E := E) i *
          ∑ k ∈ Finset.range i, CPT (i - k) * fr ^ 2) *
          Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) := by
        rw [← Finset.sum_mul]
        ring

end k4aRefoldCorner

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
