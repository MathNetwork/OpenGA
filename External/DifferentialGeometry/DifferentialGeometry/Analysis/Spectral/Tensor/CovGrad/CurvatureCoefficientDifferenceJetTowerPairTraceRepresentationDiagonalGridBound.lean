import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTowerCurvDiffGridWindow
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTowerRiemannLoweredDifference
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTowerRiemannMixedBiContraction
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricArmCoeffJetTower
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifference
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradLinear
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.InverseMetricRaisedEndomorphismJetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CometricDoubleTraceField
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RecoveryEndomorphismJetBound
import DifferentialGeometry.Tensor.Multilinear.Basis
import DifferentialGeometry.Tensor.Mixed.Field
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqSmoothCcUniformBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.FiberNormSubadditivity
import DifferentialGeometry.Analysis.Sobolev.GagliardoNirenbergLpFiberNorm
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderHigherOrderTame
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceJetTower
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RaisedKoszulCovariantJetTower
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RaisedKoszulParallelRaiseJetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceArmRfnsBound
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnDiffPalatini
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.AppCcDropIteratedGrid
import DifferentialGeometry.Analysis.Sobolev.BoundedFactorProductGrid
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Fin.Tuple.NatAntidiagonal
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTowerPairTraceRepresentationIdentity


noncomputable section

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization (metricCauchySchwarzBound ccTensorBilinSymm smoothCcTensorBilinForm ccTensorBilin_apply ccTensorModel ccTensorMultilinear ccTensorBilinSymm_contMDiff ccTensorBilinSymm_apply ccTensorBilinSymm_symm)
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma iteratedCovGrad_smul_b (g : SmoothRiemannianMetric I M) (r s j : ℕ)
    (c : ℝ) (w : SmoothCcTensor g r s) :
    iteratedCovGrad (I := I) g r s j (c • w) = c • iteratedCovGrad (I := I) g r s j w := by
  induction j with
  | zero => simp only [iteratedCovGrad_zero]
  | succ j ih =>
    rw [iteratedCovGrad_succ, iteratedCovGrad_succ, ih, covGrad_smul]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma rfns_smul_b (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (c : ℝ) (v : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (c • v) =
      c ^ 2 * riemannianFiberNormSq (I := I) (M := M) g r s x v := by
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (c • v),
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x v]
  rw [TensorRSSpace.toModel_smul, tensorInnerPointwise_smul_left,
    tensorInnerPointwise_smul_right]
  ring

theorem riemannianFiberNormSq_iteratedCovGrad_riemannMixedCoeff_backgroundDifference_le_loweredDifference
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0RiemannMixedCoeff (I := I) (M := M) g₀ g₁ -
                ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)).toSection x) ≤
          C i * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 4 i
              (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x) := by
  classical
  have hcB : ∀ j : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ (6 + j) (2 + j) x
        ((slotExtendIter (I := I) (M := M) g₀ 6 2 j
          (pairTraceKernel (I := I) (M := M) g₀)).toSection x) ≤ c := fun j =>
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ (6 + j) (2 + j)
      (slotExtendIter (I := I) (M := M) g₀ 6 2 j (pairTraceKernel (I := I) (M := M) g₀))
  choose cB hcB0 hcBb using hcB
  refine ⟨fun i => 4 * cB i * ((Module.finrank ℝ E : ℝ) * (Module.finrank ℝ E : ℝ)),
    fun i => by
      have := hcB0 i
      positivity, ?_⟩
  intro g₁ i x
  rw [mixedCoeff_backgroundDifference_eq_pairTrace (I := I) (M := M) g₀ g₁]
  set WB : SmoothCcTensor g₀ 2 6 :=
    rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 pairTraceKernelSlotPerm
      (slotExtendIter (I := I) (M := M) g₀ 0 4 2
        (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)) with hWB_def
  have hsmul : (iteratedCovGrad (I := I) g₀ 2 2 i
      ((2 : ℝ) • ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 (pairTraceKernel (I := I) (M := M) g₀)
        WB)).toSection x =
      (2 : ℝ) • ((iteratedCovGrad (I := I) g₀ 2 2 i
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 (pairTraceKernel (I := I) (M := M) g₀)
          WB)).toSection x) := by
    rw [iteratedCovGrad_smul_b]
    rw [SmoothCcTensor.toSection_smul]
    rfl
  rw [hsmul, rfns_smul_b]
  rw [iteratedCovGrad_appCcRS_parallel (I := I) (M := M) g₀ 2 6 2
    (pairTraceKernel (I := I) (M := M) g₀) (phiDtPair_covGrad_zero (I := I) (M := M) g₀) WB i]
  have hcomp : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
      ((ccOperatorFieldComp (I := I) (M := M) g₀ 2 (6 + i) (2 + i)
        (slotExtendIter (I := I) (M := M) g₀ 6 2 i (pairTraceKernel (I := I) (M := M) g₀))
        (iteratedCovGrad (I := I) g₀ 2 6 i WB)).toSection x) ≤
      riemannianFiberNormSq (I := I) (M := M) g₀ (6 + i) (2 + i) x
          ((slotExtendIter (I := I) (M := M) g₀ 6 2 i
            (pairTraceKernel (I := I) (M := M) g₀)).toSection x) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + i) x
          ((iteratedCovGrad (I := I) g₀ 2 6 i WB).toSection x) := by
    rw [appCcRS_toSection]
    exact riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ 2 (6 + i) (2 + i) x
      ((slotExtendIter (I := I) (M := M) g₀ 6 2 i
        (pairTraceKernel (I := I) (M := M) g₀)).toSection x)
      ((iteratedCovGrad (I := I) g₀ 2 6 i WB).toSection x)
  have hWBjets : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + i) x
      ((iteratedCovGrad (I := I) g₀ 2 6 i WB).toSection x) ≤
      ((Module.finrank ℝ E : ℝ) * (Module.finrank ℝ E : ℝ)) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
          ((iteratedCovGrad (I := I) g₀ 0 4 i
            (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x) := by
    have heq1 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 6 i WB).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + i) x
          ((iteratedCovGrad (I := I) g₀ 2 6 i
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁))).toSection x) := by
      rw [hWB_def]
      exact riemannianFiberNormSq_iteratedCovGrad_rs_eq_of_section_domDomCongr (I := I) (M := M) g₀ 2 6 pairTraceKernelSlotPerm
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2
          (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁))
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 pairTraceKernelSlotPerm
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)))
        (fun y d => by
          rw [rsDomDomCongrSection_toSection, toModel_rsDomDomCongr_apply]) i x
    rw [heq1]
    have hstep1 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 6 i
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁))).toSection x) ≤
        (Module.finrank ℝ E : ℝ) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (5 + i) x
            ((iteratedCovGrad (I := I) g₀ 1 5 i
              (slotExtend (I := I) (M := M) g₀ 0 4
                (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁))).toSection x) :=
      rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 1 5
        (slotExtend (I := I) (M := M) g₀ 0 4
          (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)) i x
    have hstep2 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (5 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 5 i
          (slotExtend (I := I) (M := M) g₀ 0 4
            (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁))).toSection x) ≤
        (Module.finrank ℝ E : ℝ) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 4 i
              (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x) :=
      rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 0 4
        (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁) i x
    have hfr : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
    calc riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + i) x
          ((iteratedCovGrad (I := I) g₀ 2 6 i
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁))).toSection x)
        ≤ (Module.finrank ℝ E : ℝ) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (5 + i) x
            ((iteratedCovGrad (I := I) g₀ 1 5 i
              (slotExtend (I := I) (M := M) g₀ 0 4
                (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁))).toSection x) :=
          hstep1
      _ ≤ (Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 4 i
              (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x)) :=
          mul_le_mul_of_nonneg_left hstep2 hfr
      _ = ((Module.finrank ℝ E : ℝ) * (Module.finrank ℝ E : ℝ)) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 4 i
              (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x) := by
          ring
  have hrfns_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (6 + i) x
    ((iteratedCovGrad (I := I) g₀ 2 6 i WB).toSection x)
  have hCD_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (4 + i) x
    ((iteratedCovGrad (I := I) g₀ 0 4 i
      (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x)
  calc (2 : ℝ) ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((ccOperatorFieldComp (I := I) (M := M) g₀ 2 (6 + i) (2 + i)
          (slotExtendIter (I := I) (M := M) g₀ 6 2 i (pairTraceKernel (I := I) (M := M) g₀))
          (iteratedCovGrad (I := I) g₀ 2 6 i WB)).toSection x)
      ≤ (2 : ℝ) ^ 2 * (riemannianFiberNormSq (I := I) (M := M) g₀ (6 + i) (2 + i) x
          ((slotExtendIter (I := I) (M := M) g₀ 6 2 i
            (pairTraceKernel (I := I) (M := M) g₀)).toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 6 i WB).toSection x)) := by
        have := hcomp
        nlinarith
    _ ≤ (2 : ℝ) ^ 2 * (cB i *
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 6 i WB).toSection x)) := by
        have h1 := hcBb i x
        nlinarith
    _ ≤ (2 : ℝ) ^ 2 * (cB i * (((Module.finrank ℝ E : ℝ) * (Module.finrank ℝ E : ℝ)) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 4 i
              (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x))) := by
        have := hcB0 i
        nlinarith [hWBjets]
    _ = (4 * cB i * ((Module.finrank ℝ E : ℝ) * (Module.finrank ℝ E : ℝ))) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 4 i
              (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x) := by
        ring

theorem riemannianFiberNormSq_iteratedCovGrad_riemannLoweredCcFirstArgDifference_diagonalProductGrid_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 4 i
              (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁ -
                riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)).toSection x) ≤
          C i * ∑ k ∈ Finset.range (i + 3),
            ∑ n ∈ Finset.range (k + 1),
              ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
                ∏ m : Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T).toSection x) := by
  classical
  obtain ⟨CAd, hCAd_nn, hCAd⟩ :=
    rfns_iteratedCovGrad_riemannLoweredBackgroundDifference_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨cbg, hcbg_nn, hcbg⟩ := exists_iteratedCovGrad_fiberNormSq_bound (I := I) (M := M) g₀ 0 4
    (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)
  set BB : ℕ → ℕ → ℝ := fun i i' => ((Module.finrank ℝ E : ℝ) ^ 2 * δ₀ ^ 2 + 1) *
    ∑ l ∈ Finset.range (i + 1 - i'),
      (2 * CAd l * gridSumPairCount (i' + 1) (l + 3) + 2 * cbg l) with hBB_def
  have hBBsum_nn : ∀ i i', 0 ≤ ∑ l ∈ Finset.range (i + 1 - i'),
      (2 * CAd l * gridSumPairCount (i' + 1) (l + 3) + 2 * cbg l) := by
    intro i i'
    refine Finset.sum_nonneg fun l _ => add_nonneg ?_ ?_
    · have := hCAd_nn l
      have := gridSumPairCount_nonneg (i' + 1) (l + 3)
      positivity
    · have := hcbg_nn l
      linarith
  have hc0fac_nn : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) ^ 2 * δ₀ ^ 2 + 1 := by positivity
  have hBB_nn : ∀ i i', 0 ≤ BB i i' := by
    intro i i'
    rw [hBB_def]
    exact mul_nonneg hc0fac_nn (hBBsum_nn i i')
  have hBBval : ∀ i i', BB i i' = ((Module.finrank ℝ E : ℝ) ^ 2 * δ₀ ^ 2 + 1) *
      ∑ l ∈ Finset.range (i + 1 - i'),
        (2 * CAd l * gridSumPairCount (i' + 1) (l + 3) + 2 * cbg l) := by
    intro i i'
    rw [hBB_def]
  clear_value BB
  refine ⟨fun i => diagonalGridGrowthFactor (E := E) i *
      ∑ i' ∈ Finset.range (i + 1), (Module.finrank ℝ E : ℝ) ^ 3 * BB i i',
    fun i => mul_nonneg (appCcGdiag_nonneg (E := E) i)
      (Finset.sum_nonneg fun i' _ => mul_nonneg (by positivity) (hBB_nn i i')), ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound i x
  set b : ℕ → ℝ := fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
    ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x) with hb_def
  have hb : ∀ j, 0 ≤ b j :=
    fun j => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j) x _
  have hgoal_eq : (∑ k ∈ Finset.range (i + 3),
      ∑ n ∈ Finset.range (k + 1),
        ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
          ∏ m : Fin n, b (e m)) =
      ∑ k ∈ Finset.range (i + 3), Combinatorics.antidiagonalTupleGrid b k := rfl
  rw [hgoal_eq]
  set WW : ℝ := ∑ k ∈ Finset.range (i + 3), Combinatorics.antidiagonalTupleGrid b k
    with hWW_def
  have hgsum_le_WW : ∀ m : ℕ, m ≤ i + 3 →
      (∑ k ∈ Finset.range m, Combinatorics.antidiagonalTupleGrid b k) ≤ WW := by
    intro m hm
    rw [hWW_def]
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hm) ?_
    intro k _ _
    exact Combinatorics.antidiagonalTupleGrid_nonneg b hb k
  have hWW_nn : 0 ≤ WW := by
    rw [hWW_def]
    exact Finset.sum_nonneg fun k _ => Combinatorics.antidiagonalTupleGrid_nonneg b hb k
  have hWW_ge1 : (1 : ℝ) ≤ WW := by
    rw [hWW_def]
    calc (1 : ℝ) = Combinatorics.antidiagonalTupleGrid b 0 :=
          (Combinatorics.antidiagonalTupleGrid_zero b).symm
      _ ≤ ∑ k ∈ Finset.range (i + 3), Combinatorics.antidiagonalTupleGrid b k :=
          Finset.single_le_sum
            (f := fun k => Combinatorics.antidiagonalTupleGrid b k)
            (fun k _ => Combinatorics.antidiagonalTupleGrid_nonneg b hb k)
            (Finset.mem_range.mpr (by omega))
  clear_value WW
  rw [riemannG1LoweringDifference_slotInsert_repr (I := I) (M := M) g₀ g₁ T htie]
  rw [riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
    (Equiv.swap (0 : Fin 4) 1)
    (ccOperatorFieldComp (I := I) (M := M) g₀ 0 4 4
      (endoSlotZeroCcTensor (I := I) (M := M) g₀ 3
        (perturbationSharpEndoField (I := I) (M := M) g₀ T))
      (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
        (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁))) i x]
  refine le_trans (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le
    (I := I) (M := M) g₀ i 0 4 4
    (endoSlotZeroCcTensor (I := I) (M := M) g₀ 3
      (perturbationSharpEndoField (I := I) (M := M) g₀ T))
    (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
      (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)) x) ?_
  have hL01 : ∀ l : ℕ,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 4 l
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
            (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁))).toSection x) ≤
      2 * CAd l * (∑ k ∈ Finset.range (l + 3), Combinatorics.antidiagonalTupleGrid b k) +
        2 * cbg l := by
    intro l
    rw [riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 4) 1) (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁) l x]
    have hsplit : riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁ =
        riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁ +
          riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀ := by
      rw [riemannLoweredBackgroundDifference, sub_add_cancel]
    have hsec : (iteratedCovGrad (I := I) g₀ 0 4 l
        (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)).toSection x =
        (iteratedCovGrad (I := I) g₀ 0 4 l
          (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x +
        (iteratedCovGrad (I := I) g₀ 0 4 l
          (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)).toSection x := by
      rw [hsplit, iteratedCovGrad_add, SmoothCcTensor.toSection_add]
      rfl
    rw [hsec]
    refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (4 + l) x _ _) ?_
    have h1 := hCAd g₁ T htie hδ_le hδ0 hbound l x
    rw [show (∑ k ∈ Finset.range (l + 3),
        ∑ n ∈ Finset.range (k + 1),
          ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
            ∏ m : Fin n, b (e m)) =
        ∑ k ∈ Finset.range (l + 3), Combinatorics.antidiagonalTupleGrid b k from rfl] at h1
    have h2 := hcbg l x
    have h1nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (4 + l) x
      ((iteratedCovGrad (I := I) g₀ 0 4 l
        (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x)
    linarith
  have hcell : ∀ i' ∈ Finset.range (i + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 (4 + i') x
          ((iteratedCovGrad (I := I) g₀ 4 4 i'
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ 3
              (perturbationSharpEndoField (I := I) (M := M) g₀ T))).toSection x) *
        ∑ l ∈ Finset.range (i + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 4 l
              (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
                (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁))).toSection x) ≤
      ((Module.finrank ℝ E : ℝ) ^ 3 * BB i i') * WW := by
    intro i' hi'
    have hi'le : i' ≤ i := by
      rw [Finset.mem_range] at hi'; omega
    have hA2 : (∑ l ∈ Finset.range (i + 1 - i'),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 4 l
            (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
              (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁))).toSection x)) ≤
        ∑ l ∈ Finset.range (i + 1 - i'),
          (2 * CAd l * (∑ k ∈ Finset.range (l + 3), Combinatorics.antidiagonalTupleGrid b k) +
            2 * cbg l) :=
      Finset.sum_le_sum fun l _ => hL01 l
    have hprod_nn1 : 0 ≤ ∑ l ∈ Finset.range (i + 1 - i'),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 4 l
            (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
              (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁))).toSection x) :=
      Finset.sum_nonneg fun l _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (4 + l) x _
    have hsum2_nn : 0 ≤ ∑ l ∈ Finset.range (i + 1 - i'),
        (2 * CAd l * (∑ k ∈ Finset.range (l + 3), Combinatorics.antidiagonalTupleGrid b k) +
          2 * cbg l) := by
      refine Finset.sum_nonneg fun l _ => add_nonneg ?_ ?_
      · have := hCAd_nn l
        have : 0 ≤ ∑ k ∈ Finset.range (l + 3), Combinatorics.antidiagonalTupleGrid b k :=
          Finset.sum_nonneg fun k _ => Combinatorics.antidiagonalTupleGrid_nonneg b hb k
        positivity
      · have := hcbg_nn l
        linarith
    have hpairsum : ∀ gsA : ℝ, 0 ≤ gsA →
        (∀ m3ok : ∀ l ∈ Finset.range (i + 1 - i'),
          gsA * (∑ k ∈ Finset.range (l + 3), Combinatorics.antidiagonalTupleGrid b k) ≤
            gridSumPairCount (i' + 1) (l + 3) * WW, gsA ≤ WW →
        gsA * ∑ l ∈ Finset.range (i + 1 - i'),
          (2 * CAd l * (∑ k ∈ Finset.range (l + 3),
            Combinatorics.antidiagonalTupleGrid b k) + 2 * cbg l) ≤
        (∑ l ∈ Finset.range (i + 1 - i'),
          (2 * CAd l * gridSumPairCount (i' + 1) (l + 3) + 2 * cbg l)) * WW) := by
      intro gsA hgsA_nn hm3 hgsA_le
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_le_sum fun l hl => ?_
      have h1 : gsA * (2 * CAd l * (∑ k ∈ Finset.range (l + 3),
          Combinatorics.antidiagonalTupleGrid b k)) ≤
          2 * CAd l * gridSumPairCount (i' + 1) (l + 3) * WW := by
        calc gsA * (2 * CAd l * (∑ k ∈ Finset.range (l + 3),
            Combinatorics.antidiagonalTupleGrid b k))
            = (2 * CAd l) * (gsA * (∑ k ∈ Finset.range (l + 3),
              Combinatorics.antidiagonalTupleGrid b k)) := by ring
          _ ≤ (2 * CAd l) * (gridSumPairCount (i' + 1) (l + 3) * WW) := by
              refine mul_le_mul_of_nonneg_left (hm3 l hl) ?_
              have := hCAd_nn l
              linarith
          _ = 2 * CAd l * gridSumPairCount (i' + 1) (l + 3) * WW := by ring
      have h2 : gsA * (2 * cbg l) ≤ 2 * cbg l * WW := by
        calc gsA * (2 * cbg l) = (2 * cbg l) * gsA := by ring
          _ ≤ (2 * cbg l) * WW := by
              refine mul_le_mul_of_nonneg_left hgsA_le ?_
              have := hcbg_nn l
              linarith
          _ = 2 * cbg l * WW := by ring
      calc gsA * (2 * CAd l * (∑ k ∈ Finset.range (l + 3),
            Combinatorics.antidiagonalTupleGrid b k) + 2 * cbg l)
          = gsA * (2 * CAd l * (∑ k ∈ Finset.range (l + 3),
              Combinatorics.antidiagonalTupleGrid b k)) + gsA * (2 * cbg l) := by ring
        _ ≤ 2 * CAd l * gridSumPairCount (i' + 1) (l + 3) * WW + 2 * cbg l * WW :=
            add_le_add h1 h2
        _ = (2 * CAd l * gridSumPairCount (i' + 1) (l + 3) + 2 * cbg l) * WW := by ring
    have hSIsymm : riemannianFiberNormSq (I := I) (M := M) g₀ 4 (4 + i') x
        ((iteratedCovGrad (I := I) g₀ 4 4 i'
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ 3
            (perturbationSharpEndoField (I := I) (M := M) g₀ T))).toSection x) ≤
        (Module.finrank ℝ E : ℝ) ^ 3 *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i') x
            ((iteratedCovGrad (I := I) g₀ 0 2 i'
              (ccTensor02Symm (I := I) (M := M) g₀ T)).toSection x) :=
      rfns_iteratedCovGrad_slotInsert3_perturbationSharp_le (I := I) (M := M) g₀ T i' x
    match i' with
    | 0 =>
        have hsym0 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 0) x
            ((iteratedCovGrad (I := I) g₀ 0 2 0
              (ccTensor02Symm (I := I) (M := M) g₀ T)).toSection x) ≤
            (Module.finrank ℝ E : ℝ) ^ 2 * δ₀ ^ 2 := by
          rw [iteratedCovGrad_zero]
          refine le_trans (rfns_symmS_zero_le_of_ball (I := I) (M := M) g₀ T hδ0 hbound x) ?_
          have hδsq : δ ^ 2 ≤ δ₀ ^ 2 := by nlinarith [hδ_le, hδ0]
          have : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) ^ 2 := by positivity
          nlinarith
        have hm3 : ∀ l ∈ Finset.range (i + 1 - 0),
            ((Module.finrank ℝ E : ℝ) ^ 2 * δ₀ ^ 2) *
              (∑ k ∈ Finset.range (l + 3), Combinatorics.antidiagonalTupleGrid b k) ≤
            ((Module.finrank ℝ E : ℝ) ^ 2 * δ₀ ^ 2) *
              (gridSumPairCount (0 + 1) (l + 3) * WW) := by
          intro l hl
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have hl_le : l ≤ i := by
            rw [Finset.mem_range] at hl; omega
          have hgs := gridSum_mul_gridSum_le b hb (0 + 1) (l + 3) (i + 3) (by omega)
          have h1eq : (∑ k ∈ Finset.range (0 + 1),
              Combinatorics.antidiagonalTupleGrid b k) = 1 := by
            rw [Finset.sum_range_one, Combinatorics.antidiagonalTupleGrid_zero]
          rw [h1eq, one_mul] at hgs
          refine le_trans hgs ?_
          refine mul_le_mul_of_nonneg_left ?_ (gridSumPairCount_nonneg _ _)
          exact hgsum_le_WW (i + 3) (le_refl _)
        calc riemannianFiberNormSq (I := I) (M := M) g₀ 4 (4 + 0) x
              ((iteratedCovGrad (I := I) g₀ 4 4 0
                (endoSlotZeroCcTensor (I := I) (M := M) g₀ 3
                  (perturbationSharpEndoField (I := I) (M := M) g₀ T))).toSection x) *
            ∑ l ∈ Finset.range (i + 1 - 0),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
                ((iteratedCovGrad (I := I) g₀ 0 4 l
                  (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
                    (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁))).toSection x)
            ≤ ((Module.finrank ℝ E : ℝ) ^ 3 *
                ((Module.finrank ℝ E : ℝ) ^ 2 * δ₀ ^ 2)) *
              ∑ l ∈ Finset.range (i + 1 - 0),
                (2 * CAd l * (∑ k ∈ Finset.range (l + 3),
                  Combinatorics.antidiagonalTupleGrid b k) + 2 * cbg l) := by
              refine mul_le_mul (le_trans hSIsymm ?_) hA2 hprod_nn1 (by positivity)
              exact mul_le_mul_of_nonneg_left hsym0 (by positivity)
          _ = (Module.finrank ℝ E : ℝ) ^ 3 *
              (((Module.finrank ℝ E : ℝ) ^ 2 * δ₀ ^ 2) *
                ∑ l ∈ Finset.range (i + 1 - 0),
                  (2 * CAd l * (∑ k ∈ Finset.range (l + 3),
                    Combinatorics.antidiagonalTupleGrid b k) + 2 * cbg l)) := by ring
          _ ≤ (Module.finrank ℝ E : ℝ) ^ 3 *
              ((∑ l ∈ Finset.range (i + 1 - 0),
                (2 * CAd l * gridSumPairCount (0 + 1) (l + 3) + 2 * cbg l)) *
                (((Module.finrank ℝ E : ℝ) ^ 2 * δ₀ ^ 2) * WW)) := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              rw [Finset.mul_sum, Finset.sum_mul]
              refine Finset.sum_le_sum fun l hl => ?_
              have hc0nn : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) ^ 2 * δ₀ ^ 2 := by positivity
              have hCADl := hCAd_nn l
              have hcbgl := hcbg_nn l
              have hml := hm3 l hl
              have hgsl_nn : 0 ≤ ∑ k ∈ Finset.range (l + 3),
                  Combinatorics.antidiagonalTupleGrid b k :=
                Finset.sum_nonneg fun k _ =>
                  Combinatorics.antidiagonalTupleGrid_nonneg b hb k
              have hgspc_nn := gridSumPairCount_nonneg (0 + 1) (l + 3)
              nlinarith [mul_le_mul_of_nonneg_left hml (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hCADl),
                mul_nonneg hc0nn hcbgl, hWW_ge1, hWW_nn,
                mul_nonneg (mul_nonneg hc0nn hcbgl) (sub_nonneg.mpr hWW_ge1)]
          _ ≤ ((Module.finrank ℝ E : ℝ) ^ 3 * BB i 0) * WW := by
              rw [hBBval i 0]
              have hsum_nn := hBBsum_nn i 0
              have hc0nn : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) ^ 2 * δ₀ ^ 2 := by positivity
              have hfr3 : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) ^ 3 := by positivity
              have hstep : ((∑ l ∈ Finset.range (i + 1 - 0),
                  (2 * CAd l * gridSumPairCount (0 + 1) (l + 3) + 2 * cbg l)) *
                    (((Module.finrank ℝ E : ℝ) ^ 2 * δ₀ ^ 2) * WW)) ≤
                  (((Module.finrank ℝ E : ℝ) ^ 2 * δ₀ ^ 2 + 1) *
                    ∑ l ∈ Finset.range (i + 1 - 0),
                      (2 * CAd l * gridSumPairCount (0 + 1) (l + 3) + 2 * cbg l)) * WW := by
                have hsum_nn0 := hBBsum_nn i 0
                nlinarith [mul_nonneg hsum_nn0 hWW_nn]
              calc (Module.finrank ℝ E : ℝ) ^ 3 *
                    ((∑ l ∈ Finset.range (i + 1 - 0),
                      (2 * CAd l * gridSumPairCount (0 + 1) (l + 3) + 2 * cbg l)) *
                      (((Module.finrank ℝ E : ℝ) ^ 2 * δ₀ ^ 2) * WW))
                  ≤ (Module.finrank ℝ E : ℝ) ^ 3 *
                      ((((Module.finrank ℝ E : ℝ) ^ 2 * δ₀ ^ 2 + 1) *
                        ∑ l ∈ Finset.range (i + 1 - 0),
                          (2 * CAd l * gridSumPairCount (0 + 1) (l + 3) + 2 * cbg l)) * WW) :=
                    mul_le_mul_of_nonneg_left hstep hfr3
                _ = ((Module.finrank ℝ E : ℝ) ^ 3 *
                      (((Module.finrank ℝ E : ℝ) ^ 2 * δ₀ ^ 2 + 1) *
                        ∑ l ∈ Finset.range (i + 1 - 0),
                          (2 * CAd l * gridSumPairCount (0 + 1) (l + 3) + 2 * cbg l))) * WW := by
                    ring
    | (i'' + 1) =>
        have hb_le_grid : b (i'' + 1) ≤ Combinatorics.antidiagonalTupleGrid b (i'' + 1) := by
          have hmem : (fun _ : Fin 1 => (i'' + 1)) ∈
              Finset.Nat.antidiagonalTuple 1 (i'' + 1) := by
            rw [Finset.Nat.mem_antidiagonalTuple]
            rw [Fin.sum_univ_one]
          have := prodTerm_le_antidiagonalTupleGrid b hb (i'' + 1) 1
            (show (1 : ℕ) < (i'' + 1) + 1 by omega) (fun _ => (i'' + 1)) hmem
          simpa using this
        have hgrid_le_gsum : Combinatorics.antidiagonalTupleGrid b (i'' + 1) ≤
            ∑ k ∈ Finset.range ((i'' + 1) + 1), Combinatorics.antidiagonalTupleGrid b k :=
          Finset.single_le_sum
            (f := fun k => Combinatorics.antidiagonalTupleGrid b k)
            (fun k _ => Combinatorics.antidiagonalTupleGrid_nonneg b hb k)
            (Finset.mem_range.mpr (by omega))
        have hsym_le : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i'' + 1)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i'' + 1)
              (ccTensor02Symm (I := I) (M := M) g₀ T)).toSection x) ≤
            ∑ k ∈ Finset.range ((i'' + 1) + 1), Combinatorics.antidiagonalTupleGrid b k :=
          le_trans (rfns_iteratedCovGrad_symmS_pointwise (I := I) (M := M) g₀ T (i'' + 1) x)
            (le_trans hb_le_grid hgrid_le_gsum)
        have hm3 : ∀ l ∈ Finset.range (i + 1 - (i'' + 1)),
            (∑ k ∈ Finset.range ((i'' + 1) + 1), Combinatorics.antidiagonalTupleGrid b k) *
              (∑ k ∈ Finset.range (l + 3), Combinatorics.antidiagonalTupleGrid b k) ≤
            gridSumPairCount ((i'' + 1) + 1) (l + 3) * WW := by
          intro l hl
          have hl_le : l ≤ i - (i'' + 1) := by
            rw [Finset.mem_range] at hl
            omega
          have hii : i'' + 1 ≤ i := hi'le
          have hgs := gridSum_mul_gridSum_le b hb ((i'' + 1) + 1) (l + 3) (i + 3) (by omega)
          refine le_trans hgs ?_
          refine mul_le_mul_of_nonneg_left ?_ (gridSumPairCount_nonneg _ _)
          exact hgsum_le_WW (i + 3) (le_refl _)
        have hgsA_le : (∑ k ∈ Finset.range ((i'' + 1) + 1),
            Combinatorics.antidiagonalTupleGrid b k) ≤ WW :=
          hgsum_le_WW ((i'' + 1) + 1) (by omega)
        have hgsA_nn : 0 ≤ ∑ k ∈ Finset.range ((i'' + 1) + 1),
            Combinatorics.antidiagonalTupleGrid b k :=
          Finset.sum_nonneg fun k _ => Combinatorics.antidiagonalTupleGrid_nonneg b hb k
        have hmain := hpairsum (∑ k ∈ Finset.range ((i'' + 1) + 1),
          Combinatorics.antidiagonalTupleGrid b k) hgsA_nn
          (fun l hl => by
            calc (∑ k ∈ Finset.range ((i'' + 1) + 1),
                  Combinatorics.antidiagonalTupleGrid b k) *
                  (∑ k ∈ Finset.range (l + 3), Combinatorics.antidiagonalTupleGrid b k)
                ≤ gridSumPairCount ((i'' + 1) + 1) (l + 3) * WW := hm3 l hl)
          hgsA_le
        calc riemannianFiberNormSq (I := I) (M := M) g₀ 4 (4 + (i'' + 1)) x
              ((iteratedCovGrad (I := I) g₀ 4 4 (i'' + 1)
                (endoSlotZeroCcTensor (I := I) (M := M) g₀ 3
                  (perturbationSharpEndoField (I := I) (M := M) g₀ T))).toSection x) *
            ∑ l ∈ Finset.range (i + 1 - (i'' + 1)),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
                ((iteratedCovGrad (I := I) g₀ 0 4 l
                  (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
                    (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁))).toSection x)
            ≤ ((Module.finrank ℝ E : ℝ) ^ 3 *
                ∑ k ∈ Finset.range ((i'' + 1) + 1), Combinatorics.antidiagonalTupleGrid b k) *
              ∑ l ∈ Finset.range (i + 1 - (i'' + 1)),
                (2 * CAd l * (∑ k ∈ Finset.range (l + 3),
                  Combinatorics.antidiagonalTupleGrid b k) + 2 * cbg l) := by
              refine mul_le_mul (le_trans hSIsymm ?_) hA2 hprod_nn1 (by positivity)
              exact mul_le_mul_of_nonneg_left hsym_le (by positivity)
          _ = (Module.finrank ℝ E : ℝ) ^ 3 *
              ((∑ k ∈ Finset.range ((i'' + 1) + 1), Combinatorics.antidiagonalTupleGrid b k) *
                ∑ l ∈ Finset.range (i + 1 - (i'' + 1)),
                  (2 * CAd l * (∑ k ∈ Finset.range (l + 3),
                    Combinatorics.antidiagonalTupleGrid b k) + 2 * cbg l)) := by ring
          _ ≤ (Module.finrank ℝ E : ℝ) ^ 3 *
              ((∑ l ∈ Finset.range (i + 1 - (i'' + 1)),
                (2 * CAd l * gridSumPairCount ((i'' + 1) + 1) (l + 3) + 2 * cbg l)) * WW) := by
              exact mul_le_mul_of_nonneg_left hmain (by positivity)
          _ ≤ ((Module.finrank ℝ E : ℝ) ^ 3 * BB i (i'' + 1)) * WW := by
              rw [hBBval i (i'' + 1)]
              have hsum_nn := hBBsum_nn i (i'' + 1)
              have hc0nn : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) ^ 2 * δ₀ ^ 2 := by positivity
              have hfr3 : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) ^ 3 := by positivity
              have hstep : (∑ l ∈ Finset.range (i + 1 - (i'' + 1)),
                  (2 * CAd l * gridSumPairCount ((i'' + 1) + 1) (l + 3) + 2 * cbg l)) ≤
                  ((Module.finrank ℝ E : ℝ) ^ 2 * δ₀ ^ 2 + 1) *
                    ∑ l ∈ Finset.range (i + 1 - (i'' + 1)),
                      (2 * CAd l * gridSumPairCount ((i'' + 1) + 1) (l + 3) + 2 * cbg l) := by
                nlinarith [mul_nonneg hc0nn hsum_nn]
              calc (Module.finrank ℝ E : ℝ) ^ 3 *
                    ((∑ l ∈ Finset.range (i + 1 - (i'' + 1)),
                      (2 * CAd l * gridSumPairCount ((i'' + 1) + 1) (l + 3) + 2 * cbg l)) * WW)
                  = ((Module.finrank ℝ E : ℝ) ^ 3 *
                      ∑ l ∈ Finset.range (i + 1 - (i'' + 1)),
                        (2 * CAd l * gridSumPairCount ((i'' + 1) + 1) (l + 3) + 2 * cbg l)) *
                      WW := by ring
                _ ≤ ((Module.finrank ℝ E : ℝ) ^ 3 *
                      (((Module.finrank ℝ E : ℝ) ^ 2 * δ₀ ^ 2 + 1) *
                        ∑ l ∈ Finset.range (i + 1 - (i'' + 1)),
                          (2 * CAd l * gridSumPairCount ((i'' + 1) + 1) (l + 3) + 2 * cbg l))) *
                      WW := by
                    refine mul_le_mul_of_nonneg_right ?_ hWW_nn
                    exact mul_le_mul_of_nonneg_left hstep hfr3
  calc diagonalGridGrowthFactor (E := E) i *
        ∑ i' ∈ Finset.range (i + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 4 (4 + i') x
              ((iteratedCovGrad (I := I) g₀ 4 4 i'
                (endoSlotZeroCcTensor (I := I) (M := M) g₀ 3
                  (perturbationSharpEndoField (I := I) (M := M) g₀ T))).toSection x) *
            ∑ l ∈ Finset.range (i + 1 - i'),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
                ((iteratedCovGrad (I := I) g₀ 0 4 l
                  (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
                    (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁))).toSection x)
      ≤ diagonalGridGrowthFactor (E := E) i *
          ∑ i' ∈ Finset.range (i + 1), ((Module.finrank ℝ E : ℝ) ^ 3 * BB i i') * WW :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hcell) (appCcGdiag_nonneg (E := E) i)
    _ = (diagonalGridGrowthFactor (E := E) i *
          ∑ i' ∈ Finset.range (i + 1), (Module.finrank ℝ E : ℝ) ^ 3 * BB i i') * WW := by
        rw [← Finset.sum_mul]
        ring

end Connection
end Integral
end DifferentialGeometry
end
