import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTowerCurvDiffGridWindow
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTowerRiemannLoweredDifference
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTowerRiemannMixedBiContraction
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTowerPairTraceRepresentation
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

section NormedRiemannCoefficientGrid

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private lemma riemannianFiberNormSq_iteratedCovGrad_slotExtendIterDomDomCongr_le (g₀ : SmoothRiemannianMetric I M)
    (X : SmoothCcTensor g₀ 0 4) (l : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
        ((iteratedCovGrad (I := I) g₀ 2 6 l
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 pairTraceKernelSlotPerm
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X))).toSection x) ≤
      ((Module.finrank ℝ E : ℝ) * (Module.finrank ℝ E : ℝ)) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 4 l X).toSection x) := by
  have heq1 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
      ((iteratedCovGrad (I := I) g₀ 2 6 l
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 pairTraceKernelSlotPerm
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X))).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
        ((iteratedCovGrad (I := I) g₀ 2 6 l
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X)).toSection x) :=
    riemannianFiberNormSq_iteratedCovGrad_rs_eq_of_section_domDomCongr (I := I) (M := M) g₀ 2 6 pairTraceKernelSlotPerm
      (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X)
      (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 pairTraceKernelSlotPerm
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X))
      (fun y d => by
        rw [rsDomDomCongrSection_toSection, toModel_rsDomDomCongr_apply]) l x
  rw [heq1]
  have hfr : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  calc riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
        ((iteratedCovGrad (I := I) g₀ 2 6 l
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X)).toSection x)
      ≤ (Module.finrank ℝ E : ℝ) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (5 + l) x
          ((iteratedCovGrad (I := I) g₀ 1 5 l
            (slotExtend (I := I) (M := M) g₀ 0 4 X)).toSection x) :=
        rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 1 5
          (slotExtend (I := I) (M := M) g₀ 0 4 X) l x
    _ ≤ (Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 4 l X).toSection x)) :=
        mul_le_mul_of_nonneg_left
          (rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 0 4 X l x) hfr
    _ = ((Module.finrank ℝ E : ℝ) * (Module.finrank ℝ E : ℝ)) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 4 l X).toSection x) := by ring

set_option maxHeartbeats 12800000 in

set_option maxHeartbeats 12800000 in
theorem riemannianFiberNormSq_iteratedCovGrad_riemannCoeff_metricFactorTelescope_traceConversion_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                ricciArmOrder0RiemannMixedCoeff (I := I) (M := M) g₀ g₁)).toSection x) ≤
          C i * ∑ j ∈ Finset.range (i + 1),
            (∑ n ∈ Finset.range (j + 1),
              ∑ e ∈ Finset.Nat.antidiagonalTuple n j,
                ∏ m : Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T).toSection x)) *
            ∑ l ∈ Finset.range (i + 1 - j),
              (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
                  ((iteratedCovGrad (I := I) g₀ 0 4 l
                    (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)).toSection x) +
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
                  ((iteratedCovGrad (I := I) g₀ 0 4 l
                    (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁ -
                      riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)).toSection x)) := by
  classical
  obtain ⟨CΔ, hCΔ_nn, hCΔ⟩ := exists_fiberNormSq_iteratedCovGrad_pairTraceOp_diff_grid
    (I := I) (M := M) g₀ hδ₀
  have hcB : ∀ j : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ (6 + j) (2 + j) x
        ((slotExtendIter (I := I) (M := M) g₀ 6 2 j
          (pairTraceKernel (I := I) (M := M) g₀)).toSection x) ≤ c := fun j =>
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ (6 + j) (2 + j)
      (slotExtendIter (I := I) (M := M) g₀ 6 2 j (pairTraceKernel (I := I) (M := M) g₀))
  choose cB hcB0 hcBb using hcB
  set dim : ℝ := (Module.finrank ℝ E : ℝ) with hdim_def
  have hdim_nn : 0 ≤ dim := Nat.cast_nonneg _
  refine ⟨fun i => 8 * (cB i * (dim * dim)) +
      8 * (diagonalGridGrowthFactor (E := E) i * (∑ j ∈ Finset.range (i + 1), CΔ j) * (dim * dim) * 2),
    fun i => by
      have h1 := hcB0 i
      have h2 : 0 ≤ ∑ j ∈ Finset.range (i + 1), CΔ j :=
        Finset.sum_nonneg fun j _ => hCΔ_nn j
      have h3 := appCcGdiag_nonneg (E := E) i
      positivity, ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound i x
  set b : ℕ → ℝ := fun j' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j') x
    ((iteratedCovGrad (I := I) g₀ 0 2 j' T).toSection x) with hb_def
  have hb : ∀ j', 0 ≤ b j' :=
    fun j' => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j') x _
  set L01 : SmoothCcTensor g₀ 0 4 := riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁ with hL01_def
  set Ldiff : SmoothCcTensor g₀ 0 4 :=
    riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁ -
      riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁ with hLdiff_def
  set Lterm : ℕ → ℝ := fun l =>
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 4 l L01).toSection x) +
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 4 l Ldiff).toSection x) with hLterm_def
  have hLterm_nn : ∀ l, 0 ≤ Lterm l := by
    intro l
    rw [hLterm_def]
    exact add_nonneg (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (4 + l) x _)
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (4 + l) x _)
  set RHS : ℝ := ∑ j ∈ Finset.range (i + 1),
    Combinatorics.antidiagonalTupleGrid b j * ∑ l ∈ Finset.range (i + 1 - j), Lterm l
    with hRHS_def
  have hRHS_cell_nn : ∀ j, 0 ≤ Combinatorics.antidiagonalTupleGrid b j *
      ∑ l ∈ Finset.range (i + 1 - j), Lterm l := fun j =>
    mul_nonneg (Combinatorics.antidiagonalTupleGrid_nonneg b hb j)
      (Finset.sum_nonneg fun l _ => hLterm_nn l)
  have hRHS_nn : 0 ≤ RHS := by
    rw [hRHS_def]
    exact Finset.sum_nonneg fun j _ => hRHS_cell_nn j
  have hgoal_eq : (∑ j ∈ Finset.range (i + 1),
      (∑ n ∈ Finset.range (j + 1),
        ∑ e ∈ Finset.Nat.antidiagonalTuple n j,
          ∏ m : Fin n, b (e m)) *
      ∑ l ∈ Finset.range (i + 1 - j),
        (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 4 l L01).toSection x) +
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 4 l Ldiff).toSection x))) = RHS := rfl
  rw [hgoal_eq]
  clear_value RHS
  have hdecomp : ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
      ricciArmOrder0RiemannMixedCoeff (I := I) (M := M) g₀ g₁ =
      (2 : ℝ) • (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
          (pairTraceOp (I := I) (M := M) g₀ g₁ - pairTraceOp (I := I) (M := M) g₀ g₀)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 pairTraceKernelSlotPerm
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁))) +
        ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 (pairTraceOp (I := I) (M := M) g₀ g₀)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 pairTraceKernelSlotPerm
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2 Ldiff))) := by
    rw [riemannCoeff_eq_pairTrace (I := I) (M := M) g₀ g₁]
    rw [riemannMixedCoeff_eq_pairTrace (I := I) (M := M) g₀ g₁]
    rw [← smul_sub]
    congr 1
    rw [appCcRS_sub_left_local (I := I) (M := M) g₀ 2 6 2]
    have hWsub : rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 pairTraceKernelSlotPerm
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2 Ldiff) =
        rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 pairTraceKernelSlotPerm
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁)) -
        rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 pairTraceKernelSlotPerm
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)) := by
      rw [hLdiff_def]
      rw [show slotExtendIter (I := I) (M := M) g₀ 0 4 2
          (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁ -
            riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁) =
          slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁) -
          slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁) from by
        rw [show ∀ Y : SmoothCcTensor g₀ 0 4,
            slotExtendIter (I := I) (M := M) g₀ 0 4 2 Y =
            slotExtend (I := I) (M := M) g₀ 1 5
              (slotExtend (I := I) (M := M) g₀ 0 4 Y) from fun Y => rfl]
        rw [slotExtend_sub_cc (I := I) (M := M) g₀ 0 4]
        rw [slotExtend_sub_cc (I := I) (M := M) g₀ 1 5]
        rfl]
      rw [rsDomDomCongrSection_sub_cc (I := I) (M := M) g₀ 2 6 pairTraceKernelSlotPerm]
    rw [hWsub]
    rw [appCcRS_sub_right_cc (I := I) (M := M) g₀ 2 6 2 (pairTraceOp (I := I) (M := M) g₀ g₀)]
    abel
  rw [hdecomp]
  have hsmulsec : (iteratedCovGrad (I := I) g₀ 2 2 i
      ((2 : ℝ) • (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
          (pairTraceOp (I := I) (M := M) g₀ g₁ - pairTraceOp (I := I) (M := M) g₀ g₀)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 pairTraceKernelSlotPerm
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁))) +
        ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 (pairTraceOp (I := I) (M := M) g₀ g₀)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 pairTraceKernelSlotPerm
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2 Ldiff))))).toSection x =
      (2 : ℝ) • ((iteratedCovGrad (I := I) g₀ 2 2 i
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
          (pairTraceOp (I := I) (M := M) g₀ g₁ - pairTraceOp (I := I) (M := M) g₀ g₀)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 pairTraceKernelSlotPerm
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁))))).toSection x +
      (iteratedCovGrad (I := I) g₀ 2 2 i
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 (pairTraceOp (I := I) (M := M) g₀ g₀)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 pairTraceKernelSlotPerm
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2 Ldiff)))).toSection x) := by
    rw [iteratedCovGrad_smul_b, iteratedCovGrad_add]
    rw [SmoothCcTensor.toSection_smul, SmoothCcTensor.toSection_add]
    rfl
  rw [hsmulsec, rfns_smul_b]
  have hT2 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
      ((iteratedCovGrad (I := I) g₀ 2 2 i
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 (pairTraceOp (I := I) (M := M) g₀ g₀)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 pairTraceKernelSlotPerm
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2 Ldiff)))).toSection x) ≤
      (cB i * (dim * dim)) * RHS := by
    rw [pairTraceOp_self_eq (I := I) (M := M) g₀]
    rw [iteratedCovGrad_appCcRS_parallel (I := I) (M := M) g₀ 2 6 2
      (pairTraceKernel (I := I) (M := M) g₀) (phiDtPair_covGrad_zero (I := I) (M := M) g₀) _ i]
    have hcomp : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((ccOperatorFieldComp (I := I) (M := M) g₀ 2 (6 + i) (2 + i)
          (slotExtendIter (I := I) (M := M) g₀ 6 2 i (pairTraceKernel (I := I) (M := M) g₀))
          (iteratedCovGrad (I := I) g₀ 2 6 i
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 pairTraceKernelSlotPerm
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2 Ldiff)))).toSection x) ≤
        riemannianFiberNormSq (I := I) (M := M) g₀ (6 + i) (2 + i) x
            ((slotExtendIter (I := I) (M := M) g₀ 6 2 i
              (pairTraceKernel (I := I) (M := M) g₀)).toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 6 i
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 pairTraceKernelSlotPerm
                (slotExtendIter (I := I) (M := M) g₀ 0 4 2 Ldiff))).toSection x) := by
      rw [appCcRS_toSection]
      exact riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ 2 (6 + i) (2 + i) x _ _
    refine le_trans hcomp ?_
    have h1 := hcBb i x
    have h2 := riemannianFiberNormSq_iteratedCovGrad_slotExtendIterDomDomCongr_le (I := I) (M := M) g₀ Ldiff i x
    rw [← hdim_def] at h2
    have hLd_le_RHS : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
        ((iteratedCovGrad (I := I) g₀ 0 4 i Ldiff).toSection x) ≤ RHS := by
      rw [hRHS_def]
      have hcell0 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
          ((iteratedCovGrad (I := I) g₀ 0 4 i Ldiff).toSection x) ≤
          Combinatorics.antidiagonalTupleGrid b 0 * ∑ l ∈ Finset.range (i + 1 - 0), Lterm l := by
        rw [Combinatorics.antidiagonalTupleGrid_zero, one_mul]
        have hLi : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 4 i Ldiff).toSection x) ≤ Lterm i := by
          rw [hLterm_def]
          have := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (4 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 4 i L01).toSection x)
          linarith
        refine le_trans hLi ?_
        exact Finset.single_le_sum (f := fun l => Lterm l) (fun l _ => hLterm_nn l)
          (Finset.mem_range.mpr (by omega))
      refine le_trans hcell0 ?_
      exact Finset.single_le_sum
        (f := fun j => Combinatorics.antidiagonalTupleGrid b j *
          ∑ l ∈ Finset.range (i + 1 - j), Lterm l)
        (fun j _ => hRHS_cell_nn j) (Finset.mem_range.mpr (by omega))
    have hWB_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (6 + i) x
      ((iteratedCovGrad (I := I) g₀ 2 6 i
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 pairTraceKernelSlotPerm
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2 Ldiff))).toSection x)
    have hLd_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (4 + i) x
      ((iteratedCovGrad (I := I) g₀ 0 4 i Ldiff).toSection x)
    calc riemannianFiberNormSq (I := I) (M := M) g₀ (6 + i) (2 + i) x
          ((slotExtendIter (I := I) (M := M) g₀ 6 2 i
            (pairTraceKernel (I := I) (M := M) g₀)).toSection x) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + i) x
          ((iteratedCovGrad (I := I) g₀ 2 6 i
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 pairTraceKernelSlotPerm
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2 Ldiff))).toSection x)
        ≤ cB i * ((dim * dim) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
              ((iteratedCovGrad (I := I) g₀ 0 4 i Ldiff).toSection x)) := by
          have hdd : (0 : ℝ) ≤ dim * dim := by positivity
          nlinarith [mul_le_mul h1 h2 hWB_nn (hcB0 i), hcB0 i]
      _ ≤ cB i * ((dim * dim) * RHS) := by
          have hdd : (0 : ℝ) ≤ dim * dim := by positivity
          have hmono := mul_le_mul_of_nonneg_left hLd_le_RHS
            (mul_nonneg (hcB0 i) hdd)
          nlinarith [hmono]
      _ = (cB i * (dim * dim)) * RHS := by ring
  have hT1 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
      ((iteratedCovGrad (I := I) g₀ 2 2 i
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
          (pairTraceOp (I := I) (M := M) g₀ g₁ - pairTraceOp (I := I) (M := M) g₀ g₀)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 pairTraceKernelSlotPerm
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁))))).toSection x) ≤
      (diagonalGridGrowthFactor (E := E) i * (∑ j ∈ Finset.range (i + 1), CΔ j) * (dim * dim) * 2) * RHS := by
    refine le_trans (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le
      (I := I) (M := M) g₀ i 2 6 2
      (pairTraceOp (I := I) (M := M) g₀ g₁ - pairTraceOp (I := I) (M := M) g₀ g₀)
      (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 pairTraceKernelSlotPerm
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2
          (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁))) x) ?_
    have hL11 : ∀ l : ℕ, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 4 l
          (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁)).toSection x) ≤ 2 * Lterm l := by
      intro l
      have hsec : (iteratedCovGrad (I := I) g₀ 0 4 l
          (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁)).toSection x =
          (iteratedCovGrad (I := I) g₀ 0 4 l L01).toSection x +
          (iteratedCovGrad (I := I) g₀ 0 4 l Ldiff).toSection x := by
        rw [show riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁ = L01 + Ldiff from by
          rw [hL01_def, hLdiff_def]
          abel]
        rw [iteratedCovGrad_add, SmoothCcTensor.toSection_add]
        rfl
      rw [hsec]
      refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (4 + l) x _ _) ?_
      rw [hLterm_def]
      ring_nf
      rfl
    have hcell : ∀ j ∈ Finset.range (i + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + j) x
            ((iteratedCovGrad (I := I) g₀ 6 2 j
              (pairTraceOp (I := I) (M := M) g₀ g₁ -
                pairTraceOp (I := I) (M := M) g₀ g₀)).toSection x) *
          ∑ l ∈ Finset.range (i + 1 - j),
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
              ((iteratedCovGrad (I := I) g₀ 2 6 l
                (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 pairTraceKernelSlotPerm
                  (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                    (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁)))).toSection x) ≤
        (CΔ j * (dim * dim) * 2) * RHS := by
      intro j hj
      have hj_le : j ≤ i := by
        rw [Finset.mem_range] at hj
        omega
      have hA1 := hCΔ g₁ T htie hδ_le hδ0 hbound j x
      have hA2 : (∑ l ∈ Finset.range (i + 1 - j),
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
            ((iteratedCovGrad (I := I) g₀ 2 6 l
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 pairTraceKernelSlotPerm
                (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                  (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁)))).toSection x)) ≤
          ∑ l ∈ Finset.range (i + 1 - j), (dim * dim) * (2 * Lterm l) := by
        refine Finset.sum_le_sum fun l _ => ?_
        refine le_trans (riemannianFiberNormSq_iteratedCovGrad_slotExtendIterDomDomCongr_le (I := I) (M := M) g₀
          (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁) l x) ?_
        exact mul_le_mul_of_nonneg_left (hL11 l) (by positivity)
      have hA1_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 6 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 6 2 j
          (pairTraceOp (I := I) (M := M) g₀ g₁ -
            pairTraceOp (I := I) (M := M) g₀ g₀)).toSection x)
      have hA2_nn : 0 ≤ ∑ l ∈ Finset.range (i + 1 - j),
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
            ((iteratedCovGrad (I := I) g₀ 2 6 l
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 pairTraceKernelSlotPerm
                (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                  (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁)))).toSection x) :=
        Finset.sum_nonneg fun l _ =>
          riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (6 + l) x _
      have hgrid_nn : 0 ≤ CΔ j * ∑ l' ∈ Finset.range (j + 1),
          Combinatorics.antidiagonalTupleGrid b l' :=
        mul_nonneg (hCΔ_nn j) (Finset.sum_nonneg fun l' _ =>
          Combinatorics.antidiagonalTupleGrid_nonneg b hb l')
      have hkey : (CΔ j * ∑ l' ∈ Finset.range (j + 1),
          Combinatorics.antidiagonalTupleGrid b l') *
          ∑ l ∈ Finset.range (i + 1 - j), (dim * dim) * (2 * Lterm l) ≤
          (CΔ j * (dim * dim) * 2) * RHS := by
        have hexpand : (∑ l' ∈ Finset.range (j + 1),
            Combinatorics.antidiagonalTupleGrid b l') *
            (∑ l ∈ Finset.range (i + 1 - j), Lterm l) ≤ RHS := by
          rw [Finset.sum_mul]
          rw [hRHS_def]
          have hstep : ∀ l' ∈ Finset.range (j + 1),
              Combinatorics.antidiagonalTupleGrid b l' *
                (∑ l ∈ Finset.range (i + 1 - j), Lterm l) ≤
              Combinatorics.antidiagonalTupleGrid b l' *
                ∑ l ∈ Finset.range (i + 1 - l'), Lterm l := by
            intro l' hl'
            refine mul_le_mul_of_nonneg_left ?_
              (Combinatorics.antidiagonalTupleGrid_nonneg b hb l')
            refine Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.range_subset_range.mpr ?_) (fun l _ _ => hLterm_nn l)
            rw [Finset.mem_range] at hl'
            omega
          refine le_trans (Finset.sum_le_sum hstep) ?_
          refine Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.range_subset_range.mpr (by omega)) ?_
          intro j' _ _
          exact hRHS_cell_nn j'
        calc (CΔ j * ∑ l' ∈ Finset.range (j + 1),
              Combinatorics.antidiagonalTupleGrid b l') *
              ∑ l ∈ Finset.range (i + 1 - j), (dim * dim) * (2 * Lterm l)
            = (CΔ j * (dim * dim) * 2) *
              ((∑ l' ∈ Finset.range (j + 1), Combinatorics.antidiagonalTupleGrid b l') *
                (∑ l ∈ Finset.range (i + 1 - j), Lterm l)) := by
              have hfac : (∑ l ∈ Finset.range (i + 1 - j),
                  (dim * dim) * (2 * Lterm l)) =
                  (dim * dim * 2) * ∑ l ∈ Finset.range (i + 1 - j), Lterm l := by
                rw [Finset.mul_sum]
                exact Finset.sum_congr rfl fun l _ => by ring
              rw [hfac]
              ring
          _ ≤ (CΔ j * (dim * dim) * 2) * RHS := by
              refine mul_le_mul_of_nonneg_left hexpand ?_
              have := hCΔ_nn j
              positivity
      calc riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + j) x
            ((iteratedCovGrad (I := I) g₀ 6 2 j
              (pairTraceOp (I := I) (M := M) g₀ g₁ -
                pairTraceOp (I := I) (M := M) g₀ g₀)).toSection x) *
          ∑ l ∈ Finset.range (i + 1 - j),
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
              ((iteratedCovGrad (I := I) g₀ 2 6 l
                (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 pairTraceKernelSlotPerm
                  (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                    (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁)))).toSection x)
          ≤ (CΔ j * ∑ l' ∈ Finset.range (j + 1),
              Combinatorics.antidiagonalTupleGrid b l') *
            ∑ l ∈ Finset.range (i + 1 - j), (dim * dim) * (2 * Lterm l) :=
            mul_le_mul hA1 hA2 hA2_nn hgrid_nn
        _ ≤ (CΔ j * (dim * dim) * 2) * RHS := hkey
    calc diagonalGridGrowthFactor (E := E) i *
          ∑ j ∈ Finset.range (i + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + j) x
                ((iteratedCovGrad (I := I) g₀ 6 2 j
                  (pairTraceOp (I := I) (M := M) g₀ g₁ -
                    pairTraceOp (I := I) (M := M) g₀ g₀)).toSection x) *
              ∑ l ∈ Finset.range (i + 1 - j),
                riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
                  ((iteratedCovGrad (I := I) g₀ 2 6 l
                    (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 pairTraceKernelSlotPerm
                      (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                        (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁)))).toSection x)
        ≤ diagonalGridGrowthFactor (E := E) i *
            ∑ j ∈ Finset.range (i + 1), (CΔ j * (dim * dim) * 2) * RHS :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum hcell) (appCcGdiag_nonneg (E := E) i)
      _ = (diagonalGridGrowthFactor (E := E) i * (∑ j ∈ Finset.range (i + 1), CΔ j) * (dim * dim) * 2) *
            RHS := by
          rw [← Finset.sum_mul]
          rw [← Finset.sum_mul]
          rw [← Finset.sum_mul]
          ring
  calc (2 : ℝ) ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 2 i
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
            (pairTraceOp (I := I) (M := M) g₀ g₁ - pairTraceOp (I := I) (M := M) g₀ g₀)
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 pairTraceKernelSlotPerm
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁))))).toSection x +
        (iteratedCovGrad (I := I) g₀ 2 2 i
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 (pairTraceOp (I := I) (M := M) g₀ g₀)
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 pairTraceKernelSlotPerm
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2 Ldiff)))).toSection x)
      ≤ (2 : ℝ) ^ 2 * (2 * ((diagonalGridGrowthFactor (E := E) i * (∑ j ∈ Finset.range (i + 1), CΔ j) *
            (dim * dim) * 2) * RHS) + 2 * ((cB i * (dim * dim)) * RHS)) := by
        have hadd := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 2 2 i
            (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
              (pairTraceOp (I := I) (M := M) g₀ g₁ - pairTraceOp (I := I) (M := M) g₀ g₀)
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 pairTraceKernelSlotPerm
                (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                  (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁))))).toSection x)
          ((iteratedCovGrad (I := I) g₀ 2 2 i
            (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 (pairTraceOp (I := I) (M := M) g₀ g₀)
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 pairTraceKernelSlotPerm
                (slotExtendIter (I := I) (M := M) g₀ 0 4 2 Ldiff)))).toSection x)
        nlinarith [hT1, hT2, hadd]
    _ ≤ (8 * (cB i * (dim * dim)) +
          8 * (diagonalGridGrowthFactor (E := E) i * (∑ j ∈ Finset.range (i + 1), CΔ j) *
            (dim * dim) * 2)) * RHS := by
        nlinarith [hRHS_nn]

theorem riemannianFiberNormSq_iteratedCovGrad_riemannMixedCoeff_backgroundDifference_diagonalProductGrid_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0RiemannMixedCoeff (I := I) (M := M) g₀ g₁ -
                ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)).toSection x) ≤
          C i * ∑ k ∈ Finset.range (i + 3),
            ∑ n ∈ Finset.range (k + 1),
              ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
                ∏ m : Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T).toSection x) := by
  classical
  obtain ⟨CB, hCB_nn, hCB⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_riemannMixedCoeff_backgroundDifference_le_loweredDifference
      (I := I) (M := M) g₀
  obtain ⟨CA, hCA_nn, hCA⟩ :=
    rfns_iteratedCovGrad_riemannLoweredBackgroundDifference_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  refine ⟨fun i => CB i * CA i, fun i => mul_nonneg (hCB_nn i) (hCA_nn i), ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound i x
  refine le_trans (hCB g₁ i x) ?_
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (hCA g₁ T htie hδ_le hδ0 hbound i x) (hCB_nn i)

theorem riemannianFiberNormSq_iteratedCovGrad_riemannCoeff_metricFactorTelescope_diagonalProductGrid_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                ricciArmOrder0RiemannMixedCoeff (I := I) (M := M) g₀ g₁)).toSection x) ≤
          C i * ∑ k ∈ Finset.range (i + 3),
            ∑ n ∈ Finset.range (k + 1),
              ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
                ∏ m : Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T).toSection x) := by
  classical
  obtain ⟨CC, hCC_nn, hCC⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_riemannCoeff_metricFactorTelescope_traceConversion_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨C1, hC1_nn, hC1⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_riemannLoweredCcFirstArgDifference_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨CA, hCA_nn, hCA⟩ :=
    rfns_iteratedCovGrad_riemannLoweredBackgroundDifference_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨cbg, hcbg_nn, hcbg⟩ := exists_iteratedCovGrad_fiberNormSq_bound (I := I) (M := M) g₀ 0 4
    (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)
  refine ⟨fun i => CC i * ∑ j ∈ Finset.range (i + 1), ∑ l ∈ Finset.range (i + 1),
      (2 * cbg l + (2 * CA l + C1 l) * tWindowMulConst l j),
    fun i => mul_nonneg (hCC_nn i) (Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun l _ =>
      add_nonneg (by have := hcbg_nn l; linarith)
        (mul_nonneg (by have := hCA_nn l; have := hC1_nn l; linarith)
          (tWindowMulConst_nonneg l j))), ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound i x
  set b : ℕ → ℝ := fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
    ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x) with hb_def
  have hb : ∀ j, 0 ≤ b j :=
    fun j => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j) x _
  have hP : ∀ l : ℕ,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 4 l
          (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)).toSection x) ≤
      2 * cbg l + 2 * CA l * tWindow b l := by
    intro l
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
    have h1 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 4 l
          (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x) ≤
        CA l * tWindow b l := by
      have h := hCA g₁ T htie hδ_le hδ0 hbound l x
      rw [← tWindow_eq_tripleSum (I := I) (M := M) g₀ T x l] at h
      exact h
    have h2 := hcbg l x
    linarith
  have hQ : ∀ l : ℕ,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 4 l
          (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁ -
            riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)).toSection x) ≤
      C1 l * tWindow b l := by
    intro l
    have h := hC1 g₁ T htie hδ_le hδ0 hbound l x
    rw [← tWindow_eq_tripleSum (I := I) (M := M) g₀ T x l] at h
    exact h
  refine le_trans (hCC g₁ T htie hδ_le hδ0 hbound i x) ?_
  rw [← tWindow_eq_tripleSum (I := I) (M := M) g₀ T x i]
  have hjl : ∀ j ∈ Finset.range (i + 1),
      (∑ n ∈ Finset.range (j + 1),
        ∑ e ∈ Finset.Nat.antidiagonalTuple n j,
          ∏ m : Fin n, b (e m)) *
        (∑ l ∈ Finset.range (i + 1 - j),
          (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 4 l
                (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)).toSection x) +
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 4 l
                (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁ -
                  riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)).toSection x))) ≤
      (∑ l ∈ Finset.range (i + 1),
        (2 * cbg l + (2 * CA l + C1 l) * tWindowMulConst l j)) * tWindow b i := by
    intro j hj
    have hjle : j ≤ i := by
      have := Finset.mem_range.mp hj
      omega
    have hgrid_eq : (∑ n ∈ Finset.range (j + 1),
        ∑ e ∈ Finset.Nat.antidiagonalTuple n j, ∏ m : Fin n, b (e m)) =
        Combinatorics.antidiagonalTupleGrid b j := rfl
    rw [hgrid_eq, mul_comm (Combinatorics.antidiagonalTupleGrid b j)]
    rw [Finset.sum_mul]
    have hterm : ∀ l ∈ Finset.range (i + 1 - j),
        (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 4 l
              (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)).toSection x) +
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 4 l
              (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁ -
                riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)).toSection x)) *
          Combinatorics.antidiagonalTupleGrid b j ≤
        (2 * cbg l + (2 * CA l + C1 l) * tWindowMulConst l j) * tWindow b i := by
      intro l hl
      have hlle : l ≤ i - j := by
        have := Finset.mem_range.mp hl
        omega
      have hlj : l + j ≤ i := by omega
      have hgrid_nn : 0 ≤ Combinatorics.antidiagonalTupleGrid b j :=
        Combinatorics.antidiagonalTupleGrid_nonneg b hb j
      have hgrid_le : Combinatorics.antidiagonalTupleGrid b j ≤ tWindow b i :=
        antidiagonalTupleGrid_le_tWindow b hb (by omega)
      have hsum_le : (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 4 l
              (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)).toSection x) +
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 4 l
              (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁ -
                riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)).toSection x)) ≤
          2 * cbg l + (2 * CA l + C1 l) * tWindow b l := by
        have h1 := hP l
        have h2 := hQ l
        have hW_nn : 0 ≤ tWindow b l := tWindow_nonneg b hb l
        nlinarith [hCA_nn l, hC1_nn l]
      calc (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 4 l
                (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)).toSection x) +
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 4 l
                (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁ -
                  riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)).toSection x)) *
            Combinatorics.antidiagonalTupleGrid b j
          ≤ (2 * cbg l + (2 * CA l + C1 l) * tWindow b l) *
              Combinatorics.antidiagonalTupleGrid b j :=
            mul_le_mul_of_nonneg_right hsum_le hgrid_nn
        _ = 2 * cbg l * Combinatorics.antidiagonalTupleGrid b j +
              (2 * CA l + C1 l) * (tWindow b l * Combinatorics.antidiagonalTupleGrid b j) := by
            ring
        _ ≤ 2 * cbg l * tWindow b i +
              (2 * CA l + C1 l) * (tWindowMulConst l j * tWindow b (l + j)) := by
            have hmul := tWindow_mul_antidiagonalTupleGrid_le b hb l j
            have hnn1 : 0 ≤ 2 * cbg l := by have := hcbg_nn l; linarith
            have hnn2 : 0 ≤ 2 * CA l + C1 l := by
              have := hCA_nn l; have := hC1_nn l; linarith
            exact add_le_add (mul_le_mul_of_nonneg_left hgrid_le hnn1)
              (mul_le_mul_of_nonneg_left hmul hnn2)
        _ ≤ 2 * cbg l * tWindow b i +
              (2 * CA l + C1 l) * (tWindowMulConst l j * tWindow b i) := by
            have hnn2 : 0 ≤ 2 * CA l + C1 l := by
              have := hCA_nn l; have := hC1_nn l; linarith
            exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (tWindow_mono b hb hlj)
                (tWindowMulConst_nonneg l j)) hnn2)
        _ = (2 * cbg l + (2 * CA l + C1 l) * tWindowMulConst l j) * tWindow b i := by
            ring
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.sum_mul]
    refine mul_le_mul_of_nonneg_right ?_ (tWindow_nonneg b hb i)
    refine Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.mpr (by omega)) ?_
    intro l _ _
    exact add_nonneg (by have := hcbg_nn l; linarith)
      (mul_nonneg (by have := hCA_nn l; have := hC1_nn l; linarith)
        (tWindowMulConst_nonneg l j))
  calc CC i * ∑ j ∈ Finset.range (i + 1),
        (∑ n ∈ Finset.range (j + 1),
          ∑ e ∈ Finset.Nat.antidiagonalTuple n j,
            ∏ m : Fin n, b (e m)) *
          ∑ l ∈ Finset.range (i + 1 - j),
            (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
                ((iteratedCovGrad (I := I) g₀ 0 4 l
                  (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)).toSection x) +
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
                ((iteratedCovGrad (I := I) g₀ 0 4 l
                  (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁ -
                    riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)).toSection x))
      ≤ CC i * ∑ j ∈ Finset.range (i + 1),
          (∑ l ∈ Finset.range (i + 1),
            (2 * cbg l + (2 * CA l + C1 l) * tWindowMulConst l j)) * tWindow b i :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hjl) (hCC_nn i)
    _ = CC i * (∑ j ∈ Finset.range (i + 1), ∑ l ∈ Finset.range (i + 1),
          (2 * cbg l + (2 * CA l + C1 l) * tWindowMulConst l j)) * tWindow b i := by
        rw [← Finset.sum_mul]
        ring

theorem riemannianFiberNormSq_iteratedCovGrad_ricciArmOrder0RiemannCoeff_backgroundDifference_diagonalProductGrid_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)).toSection x) ≤
          C i * ∑ k ∈ Finset.range (i + 3),
            ∑ n ∈ Finset.range (k + 1),
              ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
                ∏ m : Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T).toSection x) := by
  classical
  obtain ⟨Ca, hCa_nn, hCa⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_riemannMixedCoeff_backgroundDifference_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨Cb, hCb_nn, hCb⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_riemannCoeff_metricFactorTelescope_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  refine ⟨fun i => 2 * Cb i + 2 * Ca i,
    fun i => by have := hCa_nn i; have := hCb_nn i; linarith, ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound i x
  have hb : ∀ j : ℕ, 0 ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
      ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x) :=
    fun j => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j) x _
  rw [← tWindow_eq_tripleSum (I := I) (M := M) g₀ T x i]
  have hsplit : ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
      ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ =
      (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
        ricciArmOrder0RiemannMixedCoeff (I := I) (M := M) g₀ g₁) +
      (ricciArmOrder0RiemannMixedCoeff (I := I) (M := M) g₀ g₁ -
        ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) := by
    rw [sub_add_sub_cancel]
  have hsec : (iteratedCovGrad (I := I) g₀ 2 2 i
      (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
        ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)).toSection x =
      (iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
          ricciArmOrder0RiemannMixedCoeff (I := I) (M := M) g₀ g₁)).toSection x +
        (iteratedCovGrad (I := I) g₀ 2 2 i
          (ricciArmOrder0RiemannMixedCoeff (I := I) (M := M) g₀ g₁ -
            ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)).toSection x := by
    rw [hsplit, iteratedCovGrad_add (I := I) g₀ 2 2 i _ _, SmoothCcTensor.toSection_add]
    rfl
  rw [hsec]
  refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 (2 + i) x _ _) ?_
  have h1 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
      ((iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
          ricciArmOrder0RiemannMixedCoeff (I := I) (M := M) g₀ g₁)).toSection x) ≤
      Cb i * tWindow (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x)) i := by
    rw [tWindow_eq_tripleSum (I := I) (M := M) g₀ T x i]
    exact hCb g₁ T htie hδ_le hδ0 hbound i x
  have h2 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
      ((iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciArmOrder0RiemannMixedCoeff (I := I) (M := M) g₀ g₁ -
          ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)).toSection x) ≤
      Ca i * tWindow (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x)) i := by
    rw [tWindow_eq_tripleSum (I := I) (M := M) g₀ T x i]
    exact hCa g₁ T htie hδ_le hδ0 hbound i x
  rw [show (2 * Cb i + 2 * Ca i) *
      tWindow (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x)) i =
      2 * (Cb i * tWindow (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x)) i) +
        2 * (Ca i * tWindow (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x)) i) from by ring]
  linarith

end NormedRiemannCoefficientGrid

theorem ricciEndomorphismBackgroundDifferenceField_slotInsert_perOrder_l2_ballUniform
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
        ∀ (i : ℕ), i ≤ a →
          ‖iteratedCovGrad (I := I) g₀ 1 1 i
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
              (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))‖ ^ 2 ≤ K i := by
  obtain ⟨C, hC_nn, hgrid⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_slotInsertEndoCc_zero_ricEndoBackgroundDifferenceField_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨Kg, hKg_nn, hKg⟩ :=
    curvDiffGrid_integral_ballUniform_window (I := I) (M := M) g₀ a ha_super hR
  refine ⟨fun i => C i * ∑ k ∈ Finset.range (i + 3), Kg k,
    fun i => mul_nonneg (hC_nn i) (Finset.sum_nonneg (fun k _ => hKg_nn k)), ?_⟩
  intro g₁ P δ hδ_le hδ htie hPball i hi
  by_cases hM : Nonempty M
  · obtain ⟨x₀⟩ := hM
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
        have h1 : δ * Real.sqrt (g₀.inner x₀ v v) < 0 := mul_neg_of_neg_of_pos hδc' hsqrt_pos
        exact mul_neg_of_neg_of_pos h1 hsqrt_pos
      linarith [le_trans habs_nn hbound]
    have hkle : ∀ k ∈ Finset.range (i + 3), k ≤ a + 2 := by
      intro k hk
      rw [Finset.mem_range] at hk
      omega
    have hF_int : MeasureTheory.Integrable
        (fun x => C i * ∑ k ∈ Finset.range (i + 3),
          ∑ n ∈ Finset.range (k + 1),
            ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
              ∏ m : Fin n,
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
        (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
      (MeasureTheory.integrable_finset_sum _
        (fun k hk => (hKg P hPball k (hkle k hk)).1)).const_mul (C i)
    have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 1 (1 + i)
      (iteratedCovGrad (I := I) g₀ 1 1 i
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁)))
      (fun x => C i * ∑ k ∈ Finset.range (i + 3),
        ∑ n ∈ Finset.range (k + 1),
          ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
            ∏ m : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
      hF_int
      (fun x => hgrid g₁ P htie hδ_le hδ0 hδ i x)
    refine le_trans key ?_
    rw [MeasureTheory.integral_const_mul,
      MeasureTheory.integral_finset_sum _ (fun k hk => (hKg P hPball k (hkle k hk)).1)]
    exact mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun k hk => (hKg P hPball k (hkle k hk)).2)) (hC_nn i)
  · haveI hM' : IsEmpty M := not_nonempty_iff.mp hM
    have hz : ‖iteratedCovGrad (I := I) g₀ 1 1 i
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))‖ = 0 := by
      rw [SmoothCcTensor.norm_def, tensorL2Norm_def, tensorL2Inner,
        MeasureTheory.integral_of_isEmpty, Real.sqrt_zero]
    rw [hz]
    simpa using mul_nonneg (hC_nn i) (Finset.sum_nonneg (fun k _ => hKg_nn k))

theorem ricciArmOrder0RiemannCoeff_backgroundDifference_perOrder_l2_ballUniform
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
        ∀ (i : ℕ), i ≤ a →
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
              ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 ≤ K i := by
  obtain ⟨C, hC_nn, hgrid⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_ricciArmOrder0RiemannCoeff_backgroundDifference_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨Kg, hKg_nn, hKg⟩ :=
    curvDiffGrid_integral_ballUniform_window (I := I) (M := M) g₀ a ha_super hR
  refine ⟨fun i => C i * ∑ k ∈ Finset.range (i + 3), Kg k,
    fun i => mul_nonneg (hC_nn i) (Finset.sum_nonneg (fun k _ => hKg_nn k)), ?_⟩
  intro g₁ P δ hδ_le hδ htie hPball i hi
  by_cases hM : Nonempty M
  · obtain ⟨x₀⟩ := hM
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
        have h1 : δ * Real.sqrt (g₀.inner x₀ v v) < 0 := mul_neg_of_neg_of_pos hδc' hsqrt_pos
        exact mul_neg_of_neg_of_pos h1 hsqrt_pos
      linarith [le_trans habs_nn hbound]
    have hkle : ∀ k ∈ Finset.range (i + 3), k ≤ a + 2 := by
      intro k hk
      rw [Finset.mem_range] at hk
      omega
    have hF_int : MeasureTheory.Integrable
        (fun x => C i * ∑ k ∈ Finset.range (i + 3),
          ∑ n ∈ Finset.range (k + 1),
            ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
              ∏ m : Fin n,
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
        (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
      (MeasureTheory.integrable_finset_sum _
        (fun k hk => (hKg P hPball k (hkle k hk)).1)).const_mul (C i)
    have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 2 (2 + i)
      (iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
          ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀))
      (fun x => C i * ∑ k ∈ Finset.range (i + 3),
        ∑ n ∈ Finset.range (k + 1),
          ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
            ∏ m : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
      hF_int
      (fun x => hgrid g₁ P htie hδ_le hδ0 hδ i x)
    refine le_trans key ?_
    rw [MeasureTheory.integral_const_mul,
      MeasureTheory.integral_finset_sum _ (fun k hk => (hKg P hPball k (hkle k hk)).1)]
    exact mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun k hk => (hKg P hPball k (hkle k hk)).2)) (hC_nn i)
  · haveI hM' : IsEmpty M := not_nonempty_iff.mp hM
    have hz : ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
          ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)‖ = 0 := by
      rw [SmoothCcTensor.norm_def, tensorL2Norm_def, tensorL2Inner,
        MeasureTheory.integral_of_isEmpty, Real.sqrt_zero]
    rw [hz]
    simpa using mul_nonneg (hC_nn i) (Finset.sum_nonneg (fun k _ => hKg_nn k))

theorem ricciArmOrder0CurvCoeff_backgroundDifference_perOrder_l2_ballUniform
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
        ∀ (i : ℕ), i ≤ a →
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
              ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 ≤ K i := by
  obtain ⟨K, hK_nn, hK⟩ :=
    ricciEndomorphismBackgroundDifferenceField_slotInsert_perOrder_l2_ballUniform
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  refine ⟨fun i => 4 * (Module.finrank ℝ E : ℝ) * K i,
    fun i => mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (hK_nn i), ?_⟩
  intro g₁ P δ hδ_le hδ htie hPball i hi
  have hKi := hK g₁ P hδ_le hδ htie hPball i hi
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 2 2 i
            (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
              ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)).toSection x) ≤
        4 * (Module.finrank ℝ E : ℝ) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
            ((iteratedCovGrad (I := I) g₀ 1 1 i
              (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
                (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))).toSection x) := by
    intro x
    have hsec : (iteratedCovGrad (I := I) g₀ 2 2 i
          (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
            ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)).toSection x =
        (iteratedCovGrad (I := I) g₀ 2 2 i
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
              (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))).toSection x +
          (iteratedCovGrad (I := I) g₀ 2 2 i
            (reindexCoeffGen (I := I) (M := M) g₀ 2 2
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
                (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
                  (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁)))
              (Equiv.swap (0 : Fin 2) 1))).toSection x := by
      rw [ricciArmOrder0CurvCoeff_backgroundDifference_decomp (I := I) (M := M) g₀ g₁,
        iteratedCovGrad_add (I := I) g₀ 2 2 i
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
            (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))
          (reindexCoeffGen (I := I) (M := M) g₀ 2 2
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
              (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
                (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁)))
            (Equiv.swap (0 : Fin 2) 1)),
        SmoothCcTensor.toSection_add]
      rfl
    rw [hsec]
    refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 (2 + i) x _ _) ?_
    have hswap : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 2 i
          (reindexCoeffGen (I := I) (M := M) g₀ 2 2
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
              (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
                (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁)))
            (Equiv.swap (0 : Fin 2) 1))).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 2 2 i
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
              (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))).toSection x) :=
      rfns_iteratedCovGrad_rsDomDomCongr_both_eq (I := I) (M := M) g₀ 2 2
        (Equiv.swap (0 : Fin 2) 1) (Equiv.swap (0 : Fin 2) 1)
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
          (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁)) i x
    rw [hswap]
    have hendo : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 2 i
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
            (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))).toSection x) ≤
        (Module.finrank ℝ E : ℝ) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
            ((iteratedCovGrad (I := I) g₀ 1 1 i
              (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
                (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))).toSection x) := by
      have h := rfns_iteratedCovGrad_slotInsertEndoCc_le_endo (I := I) (M := M) g₀ 1
        (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁) i x
      rw [pow_one] at h
      exact h
    linarith [hendo]
  have hF_int : MeasureTheory.Integrable
      (fun x => 4 * (Module.finrank ℝ E : ℝ) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
          ((iteratedCovGrad (I := I) g₀ 1 1 i
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
              (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))).toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    (integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 1 (1 + i)
      (iteratedCovGrad (I := I) g₀ 1 1 i
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁)))).const_mul _
  have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 2 (2 + i)
    (iteratedCovGrad (I := I) g₀ 2 2 i
      (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
        ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀))
    (fun x => 4 * (Module.finrank ℝ E : ℝ) *
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 1 i
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
            (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))).toSection x))
    hF_int hpt
  refine le_trans key ?_
  rw [MeasureTheory.integral_const_mul]
  rw [← tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g₀ 1 (1 + i)
    (iteratedCovGrad (I := I) g₀ 1 1 i
      (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
        (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁)))]
  rw [← SmoothCcTensor.norm_def]
  exact mul_le_mul_of_nonneg_left hKi (by positivity)

section NormedTameWindow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem curvDiffGrid_productTerm_integral_tame_le
    (g₀ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2)
    {R : ℝ} (hR : 0 ≤ R)
    (i : ℕ) (hi1 : 1 ≤ i)
    {Λ : ℝ} (hΛ_nn : 0 ≤ Λ)
    (hΛsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (P.toSection x) ≤ Λ ^ 2)
    (hNi : ‖iteratedCovGrad (I := I) g₀ 0 2 i P‖ ≤ R)
    {C : ℝ} (hC_nn : 0 ≤ C)
    (hGNP : ∀ j : ℕ, 0 < j → j < i →
      (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
              ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) ^ ((i : ℝ) / (j : ℝ))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ^ ((j : ℝ) / (i : ℝ)) ≤
        C * Λ ^ (2 * (1 - (j : ℝ) / (i : ℝ))) * R ^ (2 * (j : ℝ) / (i : ℝ)))
    (n : ℕ) (hn_le : n ≤ i) (e : Fin n → ℕ) (he : ∑ m, e m = i) :
    MeasureTheory.Integrable
        (fun x => ∏ m : Fin n,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
        (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
      (∫ x, ∏ m : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
        (i : ℝ) * (max Λ (max C 1)) ^ (7 * i) * R ^ 2 := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  set μ : MeasureTheory.Measure M := riemannianVolumeMeasure (I := I) (M := M) g₀ with hμ
  haveI : IsFiniteMeasure μ := by rw [hμ]; infer_instance
  have hi_pos : 0 < i := hi1
  have hiR_pos : (0 : ℝ) < (i : ℝ) := by exact_mod_cast hi_pos
  have hiR_ne : (i : ℝ) ≠ 0 := ne_of_gt hiR_pos
  have hnn : ∀ (j : ℕ) (x : M),
      0 ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x) :=
    fun j x => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j) x _
  have hcont : ∀ j : ℕ, Continuous (fun x => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
      ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) := by
    intro j
    have hc := Integral.L2.SmoothCcTensor.continuous_inner_self (I := I) (M := M)
      (iteratedCovGrad (I := I) g₀ 0 2 j P)
    refine hc.congr (fun x => ?_)
    rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x),
      ← Integral.L2.SmoothCcTensor.toFun_apply (I := I) (M := M)
        (iteratedCovGrad (I := I) g₀ 0 2 j P) x]
  have hint : ∀ j : ℕ, MeasureTheory.Integrable
      (fun x => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) μ := by
    intro j
    rw [hμ]
    exact integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 0 (2 + j)
      (iteratedCovGrad (I := I) g₀ 0 2 j P)
  have hint_rpow : ∀ (j : ℕ) (p : ℝ), 0 ≤ p → MeasureTheory.Integrable
      (fun x => (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) ^ p) μ := by
    intro j p hp
    have hcp : Continuous (fun x => (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) ^ p) :=
      (hcont j).rpow_const (fun x => Or.inr hp)
    exact hcp.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hint_prod : MeasureTheory.Integrable
      (fun x => ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) μ := by
    have hcp : Continuous (fun x => ∏ m : Fin n,
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) :=
      continuous_finset_prod Finset.univ (fun m _ => hcont (e m))
    exact hcp.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  refine ⟨hint_prod, ?_⟩
  set Mbar : ℝ := max Λ (max C 1) with hMbar
  have hMbar1 : (1 : ℝ) ≤ Mbar := le_trans (le_max_right C 1) (le_max_right Λ _)
  have hMbar_nn : 0 ≤ Mbar := le_trans zero_le_one hMbar1
  have hΛ_le : Λ ≤ Mbar := le_max_left _ _
  have hC_le : C ≤ Mbar := le_trans (le_max_left C 1) (le_max_right Λ _)
  set Sset : Finset (Fin n) := Finset.univ.filter (fun m => 0 < e m) with hSset
  set Zset : Finset (Fin n) := Finset.univ.filter (fun m => ¬ (0 < e m)) with hZset
  have hsplit : ∀ x : M,
      (∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) =
        (∏ m ∈ Sset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) *
          (∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) := by
    intro x
    rw [hSset, hZset]
    exact (Finset.prod_filter_mul_prod_filter_not Finset.univ (fun m => 0 < e m)
      (fun m => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))).symm
  have hZbound : ∀ x : M,
      (∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ≤ Λ ^ (2 * Zset.card) := by
    intro x
    calc (∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
        ≤ ∏ _m ∈ Zset, Λ ^ 2 := by
          apply Finset.prod_le_prod (fun m _ => hnn (e m) x)
          intro m hm
          have hem0 : e m = 0 := by have := (Finset.mem_filter.mp hm).2; omega
          rw [hem0]; exact hΛsup x
      _ = Λ ^ (2 * Zset.card) := by rw [Finset.prod_const, ← pow_mul]
  have hZsum0 : ∑ m ∈ Zset, e m = 0 := by
    apply Finset.sum_eq_zero
    intro m hm
    have := (Finset.mem_filter.mp hm).2; omega
  have hSsum : ∑ m ∈ Sset, e m = i := by
    have h := Finset.sum_filter_add_sum_filter_not Finset.univ (fun m => 0 < e m) e
    rw [← hSset, ← hZset, hZsum0, add_zero, he] at h
    exact h
  have hScard_pos : 1 ≤ Sset.card := by
    rcases Nat.eq_zero_or_pos Sset.card with h0 | hp
    · exfalso
      rw [Finset.card_eq_zero] at h0
      rw [h0, Finset.sum_empty] at hSsum
      omega
    · exact hp
  rcases Nat.lt_or_ge Sset.card 2 with hScard_lt2 | hScard_ge2
  · have hScard1 : Sset.card = 1 := by omega
    obtain ⟨m₀, hm₀⟩ := Finset.card_eq_one.mp hScard1
    have hem₀ : e m₀ = i := by
      have hss : ∑ m ∈ Sset, e m = e m₀ := by rw [hm₀, Finset.sum_singleton]
      rw [hss] at hSsum; exact hSsum
    have hSprod : ∀ x : M,
        (∏ m ∈ Sset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) =
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x) := by
      intro x; rw [hm₀, Finset.prod_singleton, hem₀]
    have hpt : ∀ x : M,
        (∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ≤
          Λ ^ (2 * Zset.card) * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x) := by
      intro x
      rw [hsplit x, hSprod x]
      calc (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
              ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x)) *
            (∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
          ≤ (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
              ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x)) * Λ ^ (2 * Zset.card) :=
            mul_le_mul_of_nonneg_left (hZbound x) (hnn i x)
        _ = Λ ^ (2 * Zset.card) * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
              ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x) := mul_comm _ _
    have hintFi : (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x) ∂μ) ≤ R ^ 2 := by
      have heq : (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x) ∂μ) =
          ‖iteratedCovGrad (I := I) g₀ 0 2 i P‖ ^ 2 := by
        rw [SmoothCcTensor.norm_def (iteratedCovGrad (I := I) g₀ 0 2 i P), hμ]
        exact (tensorL2Norm_sq_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i)
          ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection)).symm
      rw [heq]
      nlinarith [hNi, norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 i P), hR]
    have hΛZ_nn : 0 ≤ Λ ^ (2 * Zset.card) := pow_nonneg hΛ_nn _
    calc (∫ x, ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x) ∂μ)
        ≤ ∫ x, Λ ^ (2 * Zset.card) * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x) ∂μ :=
          MeasureTheory.integral_mono hint_prod ((hint i).const_mul _) hpt
      _ = Λ ^ (2 * Zset.card) * ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x) ∂μ :=
          MeasureTheory.integral_const_mul _ _
      _ ≤ Λ ^ (2 * Zset.card) * R ^ 2 := mul_le_mul_of_nonneg_left hintFi hΛZ_nn
      _ ≤ (i : ℝ) * Mbar ^ (7 * i) * R ^ 2 := by
          have hZle : Zset.card ≤ i := le_trans (Finset.card_le_univ _) (by simpa using hn_le)
          have e1 : Λ ^ (2 * Zset.card) ≤ Mbar ^ (7 * i) :=
            le_trans (pow_le_pow_left₀ hΛ_nn hΛ_le _)
              (pow_le_pow_right₀ hMbar1 (by omega))
          have e4 : Λ ^ (2 * Zset.card) * R ^ 2 ≤ Mbar ^ (7 * i) * R ^ 2 :=
            mul_le_mul_of_nonneg_right e1 (sq_nonneg R)
          have e5 : Mbar ^ (7 * i) * R ^ 2 ≤ (i : ℝ) * Mbar ^ (7 * i) * R ^ 2 := by
            have h1i : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi1
            have hMR : 0 ≤ Mbar ^ (7 * i) * R ^ 2 :=
              mul_nonneg (pow_nonneg hMbar_nn _) (sq_nonneg R)
            calc Mbar ^ (7 * i) * R ^ 2 = 1 * (Mbar ^ (7 * i) * R ^ 2) := by ring
              _ ≤ (i : ℝ) * (Mbar ^ (7 * i) * R ^ 2) := mul_le_mul_of_nonneg_right h1i hMR
              _ = (i : ℝ) * Mbar ^ (7 * i) * R ^ 2 := by ring
          exact le_trans e4 e5
  · have hem_lt : ∀ m ∈ Sset, e m < i := by
      intro m hm
      have hmpos : 0 < e m := (Finset.mem_filter.mp hm).2
      have hadd : e m + ∑ m' ∈ Sset.erase m, e m' = ∑ m' ∈ Sset, e m' :=
        Finset.add_sum_erase Sset e hm
      rw [hSsum] at hadd
      have herase_ne : (Sset.erase m).Nonempty := by
        rw [← Finset.card_pos, Finset.card_erase_of_mem hm]; omega
      obtain ⟨m', hm'⟩ := herase_ne
      have hm'S : m' ∈ Sset := Finset.mem_of_mem_erase hm'
      have hm'pos : 1 ≤ e m' := (Finset.mem_filter.mp hm'S).2
      have hle : e m' ≤ ∑ m'' ∈ Sset.erase m, e m'' :=
        Finset.single_le_sum (fun k _ => Nat.zero_le _) hm'
      omega
    have hAMGM : ∀ x : M,
        (∏ m ∈ Sset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ≤
          ∑ m ∈ Sset, ((e m : ℝ) / i) *
            (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) := by
      intro x
      have hw_nn : ∀ m ∈ Sset, 0 ≤ (e m : ℝ) / i := fun m _ => by positivity
      have hw_sum : ∑ m ∈ Sset, (e m : ℝ) / i = 1 := by
        rw [← Finset.sum_div]
        rw [show (∑ m ∈ Sset, (e m : ℝ)) = ((i : ℕ) : ℝ) from by
          rw [← Nat.cast_sum]; exact_mod_cast hSsum]
        exact div_self hiR_ne
      have hz_nn : ∀ m ∈ Sset, 0 ≤ (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) :=
        fun m _ => Real.rpow_nonneg (hnn (e m) x) _
      have hAM := Real.geom_mean_le_arith_mean_weighted Sset (fun m => (e m : ℝ) / i)
        (fun m => (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)))
        hw_nn hw_sum hz_nn
      have hLHS : (∏ m ∈ Sset, ((riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)))
            ^ ((e m : ℝ) / i)) =
          ∏ m ∈ Sset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x) := by
        apply Finset.prod_congr rfl
        intro m hm
        have hmpos : 0 < e m := (Finset.mem_filter.mp hm).2
        have hemR_ne : (e m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hmpos.ne'
        rw [← Real.rpow_mul (hnn (e m) x)]
        rw [show ((i : ℝ) / (e m : ℝ)) * ((e m : ℝ) / i) = 1 by field_simp]
        rw [Real.rpow_one]
      rw [hLHS] at hAM
      exact hAM
    have hfactor : ∀ m ∈ Sset,
        (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ) ≤
          Mbar ^ (5 * i) * R ^ 2 := by
      intro m hm
      have hmpos : 0 < e m := (Finset.mem_filter.mp hm).2
      have hem_lt_i : e m < i := hem_lt m hm
      have hemR_pos : (0 : ℝ) < (e m : ℝ) := by exact_mod_cast hmpos
      have hemR_ne : (e m : ℝ) ≠ 0 := ne_of_gt hemR_pos
      have hgn := hGNP (e m) hmpos hem_lt_i
      set Ival : ℝ := ∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ
        with hIval
      have hIval_nn : 0 ≤ Ival := by
        rw [hIval]; exact integral_nonneg (fun x => Real.rpow_nonneg (hnn (e m) x) _)
      have hθ_nn : 0 ≤ (e m : ℝ) / i := by positivity
      have hθ_le1 : (e m : ℝ) / i ≤ 1 := by
        rw [div_le_one hiR_pos]; exact_mod_cast Nat.le_of_lt hem_lt_i
      have hexp1_nn : 0 ≤ 2 * (1 - (e m : ℝ) / i) := by nlinarith
      have hexp1_le : 2 * (1 - (e m : ℝ) / i) ≤ 2 := by nlinarith
      have hΛpow : Λ ^ (2 * (1 - (e m : ℝ) / i)) ≤ Mbar ^ (2 : ℕ) := by
        calc Λ ^ (2 * (1 - (e m : ℝ) / i)) ≤ Mbar ^ (2 * (1 - (e m : ℝ) / i)) :=
              Real.rpow_le_rpow hΛ_nn hΛ_le hexp1_nn
          _ ≤ Mbar ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hMbar1 hexp1_le
          _ = Mbar ^ (2 : ℕ) := by rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      have hbase_le : C * Λ ^ (2 * (1 - (e m : ℝ) / i)) ≤ Mbar ^ (3 : ℕ) := by
        have h1 : C * Λ ^ (2 * (1 - (e m : ℝ) / i)) ≤ Mbar * Mbar ^ (2 : ℕ) :=
          mul_le_mul hC_le hΛpow (Real.rpow_nonneg hΛ_nn _) hMbar_nn
        calc C * Λ ^ (2 * (1 - (e m : ℝ) / i)) ≤ Mbar * Mbar ^ (2 : ℕ) := h1
          _ = Mbar ^ (3 : ℕ) := by ring
      have hbase_nn : 0 ≤ C * Λ ^ (2 * (1 - (e m : ℝ) / i)) :=
        mul_nonneg hC_nn (Real.rpow_nonneg hΛ_nn _)
      have hIval_eq : Ival = (Ival ^ ((e m : ℝ) / i)) ^ ((i : ℝ) / (e m : ℝ)) := by
        rw [← Real.rpow_mul hIval_nn]
        rw [show ((e m : ℝ) / i) * ((i : ℝ) / (e m : ℝ)) = 1 by field_simp]
        rw [Real.rpow_one]
      have hM3_one : (1 : ℝ) ≤ Mbar ^ (3 : ℕ) :=
        le_trans hMbar1 (le_self_pow₀ hMbar1 (by norm_num))
      have hidiv : (i : ℝ) / (e m : ℝ) ≤ (i : ℝ) :=
        div_le_self hiR_pos.le (by exact_mod_cast hmpos)
      have hsplit_pow : (C * Λ ^ (2 * (1 - (e m : ℝ) / i)) * R ^ (2 * (e m : ℝ) / i))
            ^ ((i : ℝ) / (e m : ℝ)) =
          (C * Λ ^ (2 * (1 - (e m : ℝ) / i))) ^ ((i : ℝ) / (e m : ℝ)) *
            (R ^ (2 * (e m : ℝ) / i)) ^ ((i : ℝ) / (e m : ℝ)) :=
        Real.mul_rpow hbase_nn (Real.rpow_nonneg hR _)
      have hRcollapse : (R ^ (2 * (e m : ℝ) / i)) ^ ((i : ℝ) / (e m : ℝ)) = R ^ (2 : ℕ) := by
        rw [← Real.rpow_mul hR]
        rw [show (2 * (e m : ℝ) / i) * ((i : ℝ) / (e m : ℝ)) = 2 by field_simp]
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      have hbasepow : (C * Λ ^ (2 * (1 - (e m : ℝ) / i))) ^ ((i : ℝ) / (e m : ℝ)) ≤
          Mbar ^ (5 * i) := by
        calc (C * Λ ^ (2 * (1 - (e m : ℝ) / i))) ^ ((i : ℝ) / (e m : ℝ))
            ≤ (Mbar ^ (3 : ℕ)) ^ ((i : ℝ) / (e m : ℝ)) :=
              Real.rpow_le_rpow hbase_nn hbase_le (by positivity)
          _ ≤ (Mbar ^ (3 : ℕ)) ^ ((i : ℝ)) :=
              Real.rpow_le_rpow_of_exponent_le hM3_one hidiv
          _ = (Mbar ^ (3 : ℕ)) ^ (i : ℕ) := by rw [Real.rpow_natCast]
          _ = Mbar ^ (3 * i) := by rw [← pow_mul]
          _ ≤ Mbar ^ (5 * i) := pow_le_pow_right₀ hMbar1 (by omega)
      calc Ival = (Ival ^ ((e m : ℝ) / i)) ^ ((i : ℝ) / (e m : ℝ)) := hIval_eq
        _ ≤ (C * Λ ^ (2 * (1 - (e m : ℝ) / i)) * R ^ (2 * (e m : ℝ) / i))
              ^ ((i : ℝ) / (e m : ℝ)) :=
            Real.rpow_le_rpow (Real.rpow_nonneg hIval_nn _) hgn (by positivity)
        _ = (C * Λ ^ (2 * (1 - (e m : ℝ) / i))) ^ ((i : ℝ) / (e m : ℝ)) *
              (R ^ (2 * (e m : ℝ) / i)) ^ ((i : ℝ) / (e m : ℝ)) := hsplit_pow
        _ = (C * Λ ^ (2 * (1 - (e m : ℝ) / i))) ^ ((i : ℝ) / (e m : ℝ)) * R ^ (2 : ℕ) := by
            rw [hRcollapse]
        _ ≤ Mbar ^ (5 * i) * R ^ 2 := mul_le_mul_of_nonneg_right hbasepow (sq_nonneg R)
    have hSsum_factor : ∑ m ∈ Sset, ((e m : ℝ) / i) *
        (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ) ≤
        Mbar ^ (5 * i) * R ^ 2 := by
      have hw_nn : ∀ m ∈ Sset, 0 ≤ (e m : ℝ) / i := fun m _ => by positivity
      have hw_sum : ∑ m ∈ Sset, (e m : ℝ) / i = 1 := by
        rw [← Finset.sum_div]
        rw [show (∑ m ∈ Sset, (e m : ℝ)) = ((i : ℕ) : ℝ) from by
          rw [← Nat.cast_sum]; exact_mod_cast hSsum]
        exact div_self hiR_ne
      calc ∑ m ∈ Sset, ((e m : ℝ) / i) *
            (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ)
          ≤ ∑ m ∈ Sset, ((e m : ℝ) / i) * (Mbar ^ (5 * i) * R ^ 2) := by
            apply Finset.sum_le_sum
            intro m hm
            exact mul_le_mul_of_nonneg_left (hfactor m hm) (hw_nn m hm)
        _ = (∑ m ∈ Sset, (e m : ℝ) / i) * (Mbar ^ (5 * i) * R ^ 2) := by rw [Finset.sum_mul]
        _ = Mbar ^ (5 * i) * R ^ 2 := by rw [hw_sum, one_mul]
    have hpt2 : ∀ x : M,
        (∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ≤
          Λ ^ (2 * Zset.card) * ∑ m ∈ Sset, ((e m : ℝ) / i) *
            (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) := by
      intro x
      rw [hsplit x]
      have hZnn : 0 ≤ ∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x) :=
        Finset.prod_nonneg (fun m _ => hnn (e m) x)
      have hsum_nn : 0 ≤ ∑ m ∈ Sset, ((e m : ℝ) / i) *
          (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) :=
        Finset.sum_nonneg (fun m _ => mul_nonneg (by positivity) (Real.rpow_nonneg (hnn (e m) x) _))
      calc (∏ m ∈ Sset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) *
            (∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
          ≤ (∑ m ∈ Sset, ((e m : ℝ) / i) *
              (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ))) *
              Λ ^ (2 * Zset.card) :=
            mul_le_mul (hAMGM x) (hZbound x) hZnn hsum_nn
        _ = Λ ^ (2 * Zset.card) * ∑ m ∈ Sset, ((e m : ℝ) / i) *
              (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) :=
            mul_comm _ _
    have hsum_int : MeasureTheory.Integrable
        (fun x => ∑ m ∈ Sset, ((e m : ℝ) / i) *
          (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ))) μ := by
      apply MeasureTheory.integrable_finset_sum
      intro m _
      exact (hint_rpow (e m) ((i : ℝ) / (e m : ℝ)) (by positivity)).const_mul _
    have hint_eq : (∫ x, ∑ m ∈ Sset, ((e m : ℝ) / i) *
          (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ) =
        ∑ m ∈ Sset, ((e m : ℝ) / i) *
          (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ) := by
      rw [MeasureTheory.integral_finset_sum]
      · apply Finset.sum_congr rfl
        intro m _; rw [MeasureTheory.integral_const_mul]
      · intro m _
        exact (hint_rpow (e m) ((i : ℝ) / (e m : ℝ)) (by positivity)).const_mul _
    have hΛZ_nn : 0 ≤ Λ ^ (2 * Zset.card) := pow_nonneg hΛ_nn _
    calc (∫ x, ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x) ∂μ)
        ≤ ∫ x, Λ ^ (2 * Zset.card) * ∑ m ∈ Sset, ((e m : ℝ) / i) *
            (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ :=
          MeasureTheory.integral_mono hint_prod (hsum_int.const_mul _) hpt2
      _ = Λ ^ (2 * Zset.card) * ∫ x, ∑ m ∈ Sset, ((e m : ℝ) / i) *
            (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ :=
          MeasureTheory.integral_const_mul _ _
      _ ≤ Λ ^ (2 * Zset.card) * (Mbar ^ (5 * i) * R ^ 2) := by
          rw [hint_eq]
          exact mul_le_mul_of_nonneg_left hSsum_factor hΛZ_nn
      _ ≤ (i : ℝ) * Mbar ^ (7 * i) * R ^ 2 := by
          have hZle : Zset.card ≤ i := le_trans (Finset.card_le_univ _) (by simpa using hn_le)
          have e1 : Λ ^ (2 * Zset.card) ≤ Mbar ^ (2 * i) :=
            le_trans (pow_le_pow_left₀ hΛ_nn hΛ_le _) (pow_le_pow_right₀ hMbar1 (by omega))
          have e3 : Mbar ^ (2 * i) * Mbar ^ (5 * i) = Mbar ^ (7 * i) := by
            rw [← pow_add]; congr 1; ring
          have e4 : Λ ^ (2 * Zset.card) * (Mbar ^ (5 * i) * R ^ 2) ≤
              Mbar ^ (2 * i) * (Mbar ^ (5 * i) * R ^ 2) :=
            mul_le_mul_of_nonneg_right e1
              (mul_nonneg (pow_nonneg hMbar_nn _) (sq_nonneg R))
          have e5 : Mbar ^ (7 * i) * R ^ 2 ≤ (i : ℝ) * Mbar ^ (7 * i) * R ^ 2 := by
            have h1i : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi1
            have hMR : 0 ≤ Mbar ^ (7 * i) * R ^ 2 :=
              mul_nonneg (pow_nonneg hMbar_nn _) (sq_nonneg R)
            calc Mbar ^ (7 * i) * R ^ 2 = 1 * (Mbar ^ (7 * i) * R ^ 2) := by ring
              _ ≤ (i : ℝ) * (Mbar ^ (7 * i) * R ^ 2) := mul_le_mul_of_nonneg_right h1i hMR
              _ = (i : ℝ) * Mbar ^ (7 * i) * R ^ 2 := by ring
          calc Λ ^ (2 * Zset.card) * (Mbar ^ (5 * i) * R ^ 2)
              ≤ Mbar ^ (2 * i) * (Mbar ^ (5 * i) * R ^ 2) := e4
            _ = Mbar ^ (7 * i) * R ^ 2 := by rw [← mul_assoc, e3]
            _ ≤ (i : ℝ) * Mbar ^ (7 * i) * R ^ 2 := e5

theorem antidiagonalTupleGrid_integral_ballUniform_tameWindow
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (P : SmoothCcTensor g₀ 0 2),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ),
          MeasureTheory.Integrable
              (fun x => ∑ n ∈ Finset.range (i + 1),
                ∑ e ∈ Finset.Nat.antidiagonalTuple n i,
                  ∏ m : Fin n,
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                      ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
              (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
            (∫ x, ∑ n ∈ Finset.range (i + 1),
                  ∑ e ∈ Finset.Nat.antidiagonalTuple n i,
                    ∏ m : Fin n,
                      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                        ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
                ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
              K i * (1 + ∑ j ∈ Finset.range (i + 1),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  obtain ⟨Cemb, hCemb_nn, hCemb⟩ :=
    DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.deTurckSmoothRemainderDiff_supercritical_pointwise_jet_le_fixedWindow
      (I := I) (M := M) g₀ a ha_super
  set Lam : ℝ := Cemb * Real.sqrt ((a + 1 + 1 : ℕ) : ℝ) * R with hLam
  have hLam_nn : 0 ≤ Lam := by rw [hLam]; positivity
  set Cgn : ℕ → ℝ := fun k =>
    if h : 1 ≤ k then
      (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
        (I := I) (M := M) g₀ 0 2 k h).choose
    else 0 with hCgn
  have hCgn_nn : ∀ k, 0 ≤ Cgn k := by
    intro k
    simp only [hCgn]
    split_ifs with h
    · exact (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
        (I := I) (M := M) g₀ 0 2 k h).choose_spec.1
    · exact le_refl 0
  set Gfun : ℕ → ℝ := fun k => (k : ℝ) * (max Lam (max (Cgn k) 1)) ^ (7 * k) with hGfun
  have hGfun_nn : ∀ k, 0 ≤ Gfun k := by
    intro k
    rw [hGfun]
    apply mul_nonneg (Nat.cast_nonneg k)
    apply pow_nonneg
    exact le_trans zero_le_one
      (le_trans (le_max_right (Cgn k) 1) (le_max_right Lam _))
  set vol : ℝ := ((riemannianVolumeMeasure (I := I) (M := M) g₀) Set.univ).toReal with hvol
  have hvol_nn : 0 ≤ vol := ENNReal.toReal_nonneg
  have hK_nn : ∀ k, 0 ≤ (∑ n ∈ Finset.range (k + 1),
      ((Finset.Nat.antidiagonalTuple n k).card : ℝ)) * Gfun k + vol := by
    intro k
    exact add_nonneg
      (mul_nonneg (Finset.sum_nonneg (fun n _ => Nat.cast_nonneg _)) (hGfun_nn k)) hvol_nn
  refine ⟨fun k => (∑ n ∈ Finset.range (k + 1),
      ((Finset.Nat.antidiagonalTuple n k).card : ℝ)) * Gfun k + vol, hK_nn, ?_⟩
  intro P hPball i
  have hwin_nn : 0 ≤ ∑ j ∈ Finset.range (i + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hone_le : (1 : ℝ) ≤ 1 + ∑ j ∈ Finset.range (i + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 := by linarith
  by_cases hi0 : i = 0
  · subst hi0
    have hgrid0 : (fun x => ∑ n ∈ Finset.range (0 + 1),
        ∑ e ∈ Finset.Nat.antidiagonalTuple n 0, ∏ m : Fin n,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) = (fun _ : M => (1 : ℝ)) := by
      funext x
      simp only [Nat.zero_add, Finset.sum_range_one, Finset.Nat.antidiagonalTuple_zero_zero,
        Finset.sum_singleton, Finset.univ_eq_empty, Finset.prod_empty]
    refine ⟨?_, ?_⟩
    · rw [hgrid0]; exact MeasureTheory.integrable_const 1
    · rw [hgrid0, MeasureTheory.integral_const, smul_eq_mul, mul_one,
        MeasureTheory.measureReal_def, ← hvol]
      calc vol ≤ ((∑ n ∈ Finset.range (0 + 1),
              ((Finset.Nat.antidiagonalTuple n 0).card : ℝ)) * Gfun 0 + vol) * 1 := by
            rw [mul_one]
            exact le_add_of_nonneg_left
              (mul_nonneg (Finset.sum_nonneg (fun n _ => Nat.cast_nonneg _)) (hGfun_nn 0))
        _ ≤ ((∑ n ∈ Finset.range (0 + 1),
              ((Finset.Nat.antidiagonalTuple n 0).card : ℝ)) * Gfun 0 + vol) *
            (1 + ∑ j ∈ Finset.range (0 + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hone_le (hK_nn 0)
  · have hi1 : 1 ≤ i := Nat.one_le_iff_ne_zero.mpr hi0
    have hΛsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (P.toSection x) ≤
        Lam ^ 2 := by
      intro x
      have hsum_le : ∑ j ∈ Finset.range (a + 1 + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 ≤ ((a + 1 + 1 : ℕ) : ℝ) * R ^ 2 := by
        calc ∑ j ∈ Finset.range (a + 1 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2
            ≤ ∑ j ∈ Finset.range (a + 1 + 1), R ^ 2 := by
              apply Finset.sum_le_sum
              intro j hj
              have hjle : j ≤ a + 2 := by have := Finset.mem_range.mp hj; omega
              nlinarith [norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 j P), hPball j hjle, hR]
          _ = ((a + 1 + 1 : ℕ) : ℝ) * R ^ 2 := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hsingle : riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (P.toSection x) ≤
          ∑ m ∈ Finset.range 3, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 m P).toSection x) := by
        have h0mem : (0 : ℕ) ∈ Finset.range 3 := by norm_num
        have hsl := Finset.single_le_sum
          (f := fun m => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 m P).toSection x))
          (fun m _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + m) x _) h0mem
        simpa using hsl
      have hLam2 : Lam ^ 2 = Cemb ^ 2 * ((a + 1 + 1 : ℕ) : ℝ) * R ^ 2 := by
        rw [hLam, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
      have hchain : ∑ m ∈ Finset.range 3, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 m P).toSection x) ≤ Lam ^ 2 := by
        refine le_trans (hCemb P x) ?_
        rw [hLam2]
        calc Cemb ^ 2 * ∑ j ∈ Finset.range (a + 1 + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2
            ≤ Cemb ^ 2 * (((a + 1 + 1 : ℕ) : ℝ) * R ^ 2) :=
              mul_le_mul_of_nonneg_left hsum_le (by positivity)
          _ = Cemb ^ 2 * ((a + 1 + 1 : ℕ) : ℝ) * R ^ 2 := by ring
      exact le_trans hsingle hchain
    have hGNspec := (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
      (I := I) (M := M) g₀ 0 2 i hi1).choose_spec.2
    have hGNP : ∀ j : ℕ, 0 < j → j < i →
        (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
                ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) ^ ((i : ℝ) / (j : ℝ))
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ^ ((j : ℝ) / (i : ℝ)) ≤
          Cgn i * Lam ^ (2 * (1 - (j : ℝ) / (i : ℝ))) *
            ‖iteratedCovGrad (I := I) g₀ 0 2 i P‖ ^ (2 * (j : ℝ) / (i : ℝ)) := by
      intro j hj0 hji
      have hb := hGNspec P Lam hLam_nn hΛsup j hj0 hji
      have hchoose : (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
          (I := I) (M := M) g₀ 0 2 i hi1).choose = Cgn i := by
        rw [hCgn]; simp only [dif_pos hi1]
      rw [hchoose] at hb
      have hnorm : Integral.L2.tensorL2Norm (I := I) g₀ 0 (2 + i)
          (iteratedCovGrad (I := I) g₀ 0 2 i P).toFun = ‖iteratedCovGrad (I := I) g₀ 0 2 i P‖ :=
        (SmoothCcTensor.norm_def (iteratedCovGrad (I := I) g₀ 0 2 i P)).symm
      rw [hnorm] at hb
      exact hb
    have hPT : ∀ n ∈ Finset.range (i + 1), ∀ e ∈ Finset.Nat.antidiagonalTuple n i,
        MeasureTheory.Integrable (fun x => ∏ m : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
          (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
        (∫ x, ∏ m : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
          Gfun i * ‖iteratedCovGrad (I := I) g₀ 0 2 i P‖ ^ 2 := by
      intro n hn e he
      have hn_le : n ≤ i := by have := Finset.mem_range.mp hn; omega
      have hsum_e : ∑ m, e m = i := Finset.Nat.mem_antidiagonalTuple.mp he
      have hres := curvDiffGrid_productTerm_integral_tame_le (I := I) (M := M) g₀ P
        (norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 i P)) i hi1 hLam_nn hΛsup
        (le_refl _) (hCgn_nn i) hGNP n hn_le e hsum_e
      refine ⟨hres.1, ?_⟩
      refine le_trans hres.2 (le_of_eq ?_)
      simp only [hGfun]
    have hgrid_int : MeasureTheory.Integrable (fun x => ∑ n ∈ Finset.range (i + 1),
        ∑ e ∈ Finset.Nat.antidiagonalTuple n i, ∏ m : Fin n,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
        (riemannianVolumeMeasure (I := I) (M := M) g₀) := by
      apply MeasureTheory.integrable_finset_sum
      intro n hn
      apply MeasureTheory.integrable_finset_sum
      intro e he
      exact (hPT n hn e he).1
    refine ⟨hgrid_int, ?_⟩
    rw [MeasureTheory.integral_finset_sum _
      (fun n hn => MeasureTheory.integrable_finset_sum _ (fun e he => (hPT n hn e he).1))]
    have hinner : ∀ n ∈ Finset.range (i + 1),
        (∫ x, ∑ e ∈ Finset.Nat.antidiagonalTuple n i, ∏ m : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) =
        ∑ e ∈ Finset.Nat.antidiagonalTuple n i, ∫ x, ∏ m : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := by
      intro n hn
      exact MeasureTheory.integral_finset_sum _ (fun e he => (hPT n hn e he).1)
    rw [Finset.sum_congr rfl hinner]
    have hle1 : ∑ n ∈ Finset.range (i + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n i,
          (∫ x, ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
        ∑ n ∈ Finset.range (i + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n i,
          Gfun i * ‖iteratedCovGrad (I := I) g₀ 0 2 i P‖ ^ 2 := by
      apply Finset.sum_le_sum; intro n hn
      apply Finset.sum_le_sum; intro e he
      exact (hPT n hn e he).2
    have heq2 : ∑ n ∈ Finset.range (i + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n i,
          Gfun i * ‖iteratedCovGrad (I := I) g₀ 0 2 i P‖ ^ 2 =
        (∑ n ∈ Finset.range (i + 1), ((Finset.Nat.antidiagonalTuple n i).card : ℝ)) *
          (Gfun i * ‖iteratedCovGrad (I := I) g₀ 0 2 i P‖ ^ 2) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl; intro n _
      rw [Finset.sum_const, nsmul_eq_mul]
    refine le_trans hle1 ?_
    rw [heq2]
    have htop_le : ‖iteratedCovGrad (I := I) g₀ 0 2 i P‖ ^ 2 ≤
        1 + ∑ j ∈ Finset.range (i + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 := by
      have hmem : i ∈ Finset.range (i + 1) := Finset.mem_range.mpr (by omega)
      have := Finset.single_le_sum
        (f := fun j => ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)
        (fun j _ => sq_nonneg _) hmem
      linarith
    have hcard_nn : 0 ≤ ∑ n ∈ Finset.range (i + 1),
        ((Finset.Nat.antidiagonalTuple n i).card : ℝ) :=
      Finset.sum_nonneg (fun n _ => Nat.cast_nonneg _)
    calc (∑ n ∈ Finset.range (i + 1), ((Finset.Nat.antidiagonalTuple n i).card : ℝ)) *
            (Gfun i * ‖iteratedCovGrad (I := I) g₀ 0 2 i P‖ ^ 2)
        ≤ (∑ n ∈ Finset.range (i + 1), ((Finset.Nat.antidiagonalTuple n i).card : ℝ)) *
            (Gfun i * (1 + ∑ j ∈ Finset.range (i + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)) := by
          refine mul_le_mul_of_nonneg_left ?_ hcard_nn
          exact mul_le_mul_of_nonneg_left htop_le (hGfun_nn i)
      _ = ((∑ n ∈ Finset.range (i + 1), ((Finset.Nat.antidiagonalTuple n i).card : ℝ)) *
            Gfun i) * (1 + ∑ j ∈ Finset.range (i + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by ring
      _ ≤ ((∑ n ∈ Finset.range (i + 1), ((Finset.Nat.antidiagonalTuple n i).card : ℝ)) *
            Gfun i + vol) * (1 + ∑ j ∈ Finset.range (i + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
          refine mul_le_mul_of_nonneg_right ?_ (by linarith)
          linarith

private lemma tame_sq_le_two_add (t u v c1 c2 : ℝ) (ht : 0 ≤ t) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (htri : t ≤ u + v) (h1 : u ^ 2 ≤ c1) (h2 : v ^ 2 ≤ c2) : t ^ 2 ≤ 2 * (c1 + c2) := by
  have huv : 0 ≤ u + v := by linarith
  nlinarith [mul_le_mul htri htri ht huv, sq_nonneg (u - v), h1, h2, hu, hv]

omit [NeZero (Module.finrank ℝ E)] in
theorem raisedKoszul_perOrder_l2_le_iteratedCovGrad_succ
    (g₀ g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
    (n : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 1 2 n (raisedKoszul (I := I) g₀ g₁)‖ ^ 2 ≤
      10 * ‖iteratedCovGrad (I := I) g₀ 0 2 (n + 1) T‖ ^ 2 := by
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 1 2 n (raisedKoszul (I := I) g₀ g₁)).toSection x) ≤
        10 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (n + 1)) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (n + 1) T).toSection x) := by
    intro x
    exact rfns_iteratedCovGrad_raisedKoszul_pointwise (I := I) (M := M) g₀ g₁ T htie n x
  have hF_int : MeasureTheory.Integrable
      (fun x => 10 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (n + 1)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (n + 1) T).toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    (integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 0 (2 + (n + 1))
      (iteratedCovGrad (I := I) g₀ 0 2 (n + 1) T)).const_mul _
  have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 1 (2 + n)
    (iteratedCovGrad (I := I) g₀ 1 2 n (raisedKoszul (I := I) g₀ g₁))
    (fun x => 10 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (n + 1)) x
      ((iteratedCovGrad (I := I) g₀ 0 2 (n + 1) T).toSection x))
    hF_int hpt
  refine le_trans key ?_
  rw [MeasureTheory.integral_const_mul]
  rw [← tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g₀ 0
    (2 + (n + 1)) (iteratedCovGrad (I := I) g₀ 0 2 (n + 1) T)]
  rw [← SmoothCcTensor.norm_def]

end NormedTameWindow

theorem slotInsertEndoCc_ricEndoBackgroundDifferenceField_perOrder_l2_tameEnvelope
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
          ‖iteratedCovGrad (I := I) g₀ 1 1 i
              (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
                (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))‖ ^ 2 ≤
            K i * (1 + ∑ j ∈ Finset.range (i + 3),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  obtain ⟨C, hC_nn, hgrid⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_slotInsertEndoCc_zero_ricEndoBackgroundDifferenceField_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨Kg, hKg_nn, hKg⟩ :=
    antidiagonalTupleGrid_integral_ballUniform_tameWindow (I := I) (M := M) g₀ a ha_super hR
  refine ⟨fun i => C i * ∑ k ∈ Finset.range (i + 3), Kg k,
    fun i => mul_nonneg (hC_nn i) (Finset.sum_nonneg (fun k _ => hKg_nn k)), ?_⟩
  intro g₁ P δ hδ_le hδ htie hPball i
  have hwin_nn : 0 ≤ ∑ j ∈ Finset.range (i + 3),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  by_cases hM : Nonempty M
  · obtain ⟨x₀⟩ := hM
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
        have h1 : δ * Real.sqrt (g₀.inner x₀ v v) < 0 := mul_neg_of_neg_of_pos hδc' hsqrt_pos
        exact mul_neg_of_neg_of_pos h1 hsqrt_pos
      linarith [le_trans habs_nn hbound]
    have hF_int : MeasureTheory.Integrable
        (fun x => C i * ∑ k ∈ Finset.range (i + 3),
          ∑ n ∈ Finset.range (k + 1),
            ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
              ∏ m : Fin n,
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
        (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
      (MeasureTheory.integrable_finset_sum _
        (fun k hk => (hKg P hPball k).1)).const_mul (C i)
    have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 1 (1 + i)
      (iteratedCovGrad (I := I) g₀ 1 1 i
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁)))
      (fun x => C i * ∑ k ∈ Finset.range (i + 3),
        ∑ n ∈ Finset.range (k + 1),
          ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
            ∏ m : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
      hF_int
      (fun x => hgrid g₁ P htie hδ_le hδ0 hδ i x)
    refine le_trans key ?_
    rw [MeasureTheory.integral_const_mul,
      MeasureTheory.integral_finset_sum _ (fun k hk => (hKg P hPball k).1)]
    have hsum_le : ∑ k ∈ Finset.range (i + 3),
          (∫ x, ∑ n ∈ Finset.range (k + 1),
              ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
                ∏ m : Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
        (∑ k ∈ Finset.range (i + 3), Kg k) *
          (1 + ∑ j ∈ Finset.range (i + 3), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum (fun k hk => ?_)
      refine le_trans (hKg P hPball k).2 ?_
      refine mul_le_mul_of_nonneg_left ?_ (hKg_nn k)
      have hsub : ∑ j ∈ Finset.range (k + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 ≤
          ∑ j ∈ Finset.range (i + 3), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 := by
        refine Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_mono ?_) (fun j _ _ => sq_nonneg _)
        rw [Finset.mem_range] at hk
        omega
      linarith
    calc C i * ∑ k ∈ Finset.range (i + 3),
            (∫ x, ∑ n ∈ Finset.range (k + 1),
                ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
                  ∏ m : Fin n,
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                      ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀))
        ≤ C i * ((∑ k ∈ Finset.range (i + 3), Kg k) *
            (1 + ∑ j ∈ Finset.range (i + 3), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left hsum_le (hC_nn i)
      _ = (C i * ∑ k ∈ Finset.range (i + 3), Kg k) *
            (1 + ∑ j ∈ Finset.range (i + 3), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
          ring
  · haveI hM' : IsEmpty M := not_nonempty_iff.mp hM
    have hz : ‖iteratedCovGrad (I := I) g₀ 1 1 i
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))‖ = 0 := by
      rw [SmoothCcTensor.norm_def, tensorL2Norm_def, tensorL2Inner,
        MeasureTheory.integral_of_isEmpty, Real.sqrt_zero]
    rw [hz]
    have hK_nn : 0 ≤ C i * ∑ k ∈ Finset.range (i + 3), Kg k :=
      mul_nonneg (hC_nn i) (Finset.sum_nonneg (fun k _ => hKg_nn k))
    nlinarith [hwin_nn, hK_nn]

theorem ricciArmOrder0RiemannCoeff_backgroundDifference_perOrder_l2_tameEnvelope
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
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 ≤
            K i * (1 + ∑ j ∈ Finset.range (i + 3),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  obtain ⟨C, hC_nn, hgrid⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_ricciArmOrder0RiemannCoeff_backgroundDifference_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨Kg, hKg_nn, hKg⟩ :=
    antidiagonalTupleGrid_integral_ballUniform_tameWindow (I := I) (M := M) g₀ a ha_super hR
  refine ⟨fun i => C i * ∑ k ∈ Finset.range (i + 3), Kg k,
    fun i => mul_nonneg (hC_nn i) (Finset.sum_nonneg (fun k _ => hKg_nn k)), ?_⟩
  intro g₁ P δ hδ_le hδ htie hPball i
  have hwin_nn : 0 ≤ ∑ j ∈ Finset.range (i + 3),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  by_cases hM : Nonempty M
  · obtain ⟨x₀⟩ := hM
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
        have h1 : δ * Real.sqrt (g₀.inner x₀ v v) < 0 := mul_neg_of_neg_of_pos hδc' hsqrt_pos
        exact mul_neg_of_neg_of_pos h1 hsqrt_pos
      linarith [le_trans habs_nn hbound]
    have hF_int : MeasureTheory.Integrable
        (fun x => C i * ∑ k ∈ Finset.range (i + 3),
          ∑ n ∈ Finset.range (k + 1),
            ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
              ∏ m : Fin n,
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
        (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
      (MeasureTheory.integrable_finset_sum _
        (fun k hk => (hKg P hPball k).1)).const_mul (C i)
    have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 2 (2 + i)
      (iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
          ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀))
      (fun x => C i * ∑ k ∈ Finset.range (i + 3),
        ∑ n ∈ Finset.range (k + 1),
          ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
            ∏ m : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
      hF_int
      (fun x => hgrid g₁ P htie hδ_le hδ0 hδ i x)
    refine le_trans key ?_
    rw [MeasureTheory.integral_const_mul,
      MeasureTheory.integral_finset_sum _ (fun k hk => (hKg P hPball k).1)]
    have hsum_le : ∑ k ∈ Finset.range (i + 3),
          (∫ x, ∑ n ∈ Finset.range (k + 1),
              ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
                ∏ m : Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
        (∑ k ∈ Finset.range (i + 3), Kg k) *
          (1 + ∑ j ∈ Finset.range (i + 3), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum (fun k hk => ?_)
      refine le_trans (hKg P hPball k).2 ?_
      refine mul_le_mul_of_nonneg_left ?_ (hKg_nn k)
      have hsub : ∑ j ∈ Finset.range (k + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 ≤
          ∑ j ∈ Finset.range (i + 3), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 := by
        refine Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_mono ?_) (fun j _ _ => sq_nonneg _)
        rw [Finset.mem_range] at hk
        omega
      linarith
    calc C i * ∑ k ∈ Finset.range (i + 3),
            (∫ x, ∑ n ∈ Finset.range (k + 1),
                ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
                  ∏ m : Fin n,
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                      ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀))
        ≤ C i * ((∑ k ∈ Finset.range (i + 3), Kg k) *
            (1 + ∑ j ∈ Finset.range (i + 3), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left hsum_le (hC_nn i)
      _ = (C i * ∑ k ∈ Finset.range (i + 3), Kg k) *
            (1 + ∑ j ∈ Finset.range (i + 3), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
          ring
  · haveI hM' : IsEmpty M := not_nonempty_iff.mp hM
    have hz : ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
          ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)‖ = 0 := by
      rw [SmoothCcTensor.norm_def, tensorL2Norm_def, tensorL2Inner,
        MeasureTheory.integral_of_isEmpty, Real.sqrt_zero]
    rw [hz]
    have hK_nn : 0 ≤ C i * ∑ k ∈ Finset.range (i + 3), Kg k :=
      mul_nonneg (hC_nn i) (Finset.sum_nonneg (fun k _ => hKg_nn k))
    nlinarith [hwin_nn, hK_nn]

theorem ricciArmOrder0CurvCoeff_backgroundDifference_perOrder_l2_tameEnvelope
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
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
                ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 ≤
            K i * (1 + ∑ j ∈ Finset.range (i + 3),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  obtain ⟨K, hK_nn, hK⟩ :=
    slotInsertEndoCc_ricEndoBackgroundDifferenceField_perOrder_l2_tameEnvelope
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  refine ⟨fun i => 4 * (Module.finrank ℝ E : ℝ) * K i,
    fun i => mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (hK_nn i), ?_⟩
  intro g₁ P δ hδ_le hδ htie hPball i
  have hKi := hK g₁ P hδ_le hδ htie hPball i
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 2 2 i
            (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
              ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)).toSection x) ≤
        4 * (Module.finrank ℝ E : ℝ) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
            ((iteratedCovGrad (I := I) g₀ 1 1 i
              (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
                (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))).toSection x) := by
    intro x
    have hsec : (iteratedCovGrad (I := I) g₀ 2 2 i
          (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
            ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)).toSection x =
        (iteratedCovGrad (I := I) g₀ 2 2 i
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
              (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))).toSection x +
          (iteratedCovGrad (I := I) g₀ 2 2 i
            (reindexCoeffGen (I := I) (M := M) g₀ 2 2
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
                (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
                  (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁)))
              (Equiv.swap (0 : Fin 2) 1))).toSection x := by
      rw [ricciArmOrder0CurvCoeff_backgroundDifference_decomp (I := I) (M := M) g₀ g₁,
        iteratedCovGrad_add (I := I) g₀ 2 2 i
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
            (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))
          (reindexCoeffGen (I := I) (M := M) g₀ 2 2
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
              (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
                (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁)))
            (Equiv.swap (0 : Fin 2) 1)),
        SmoothCcTensor.toSection_add]
      rfl
    rw [hsec]
    refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 (2 + i) x _ _) ?_
    have hswap : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 2 i
          (reindexCoeffGen (I := I) (M := M) g₀ 2 2
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
              (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
                (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁)))
            (Equiv.swap (0 : Fin 2) 1))).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 2 2 i
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
              (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))).toSection x) :=
      rfns_iteratedCovGrad_rsDomDomCongr_both_eq (I := I) (M := M) g₀ 2 2
        (Equiv.swap (0 : Fin 2) 1) (Equiv.swap (0 : Fin 2) 1)
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
          (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁)) i x
    rw [hswap]
    have hendo : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 2 i
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
            (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))).toSection x) ≤
        (Module.finrank ℝ E : ℝ) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
            ((iteratedCovGrad (I := I) g₀ 1 1 i
              (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
                (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))).toSection x) := by
      have h := rfns_iteratedCovGrad_slotInsertEndoCc_le_endo (I := I) (M := M) g₀ 1
        (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁) i x
      rw [pow_one] at h
      exact h
    linarith [hendo]
  have hF_int : MeasureTheory.Integrable
      (fun x => 4 * (Module.finrank ℝ E : ℝ) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
          ((iteratedCovGrad (I := I) g₀ 1 1 i
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
              (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))).toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    (integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 1 (1 + i)
      (iteratedCovGrad (I := I) g₀ 1 1 i
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁)))).const_mul _
  have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 2 (2 + i)
    (iteratedCovGrad (I := I) g₀ 2 2 i
      (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
        ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀))
    (fun x => 4 * (Module.finrank ℝ E : ℝ) *
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 1 i
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
            (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))).toSection x))
    hF_int hpt
  refine le_trans key ?_
  rw [MeasureTheory.integral_const_mul]
  rw [← tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g₀ 1 (1 + i)
    (iteratedCovGrad (I := I) g₀ 1 1 i
      (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
        (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁)))]
  rw [← SmoothCcTensor.norm_def]
  calc 4 * (Module.finrank ℝ E : ℝ) *
          ‖iteratedCovGrad (I := I) g₀ 1 1 i
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
              (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))‖ ^ 2
      ≤ 4 * (Module.finrank ℝ E : ℝ) *
          (K i * (1 + ∑ j ∈ Finset.range (i + 3),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)) := by
        refine mul_le_mul_of_nonneg_left hKi ?_
        exact mul_nonneg (by norm_num) (Nat.cast_nonneg _)
    _ = 4 * (Module.finrank ℝ E : ℝ) * K i *
          (1 + ∑ j ∈ Finset.range (i + 3),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by ring

theorem ricciArmOrder0BaseCoeff_backgroundDifference_perOrder_l2_tameEnvelope
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
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
              ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁) -
                (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
                  ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀))‖ ^ 2 ≤
            K i * (1 + ∑ j ∈ Finset.range (i + 3),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  obtain ⟨KR, hKR_nn, hKR⟩ :=
    ricciArmOrder0RiemannCoeff_backgroundDifference_perOrder_l2_tameEnvelope
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨KC, hKC_nn, hKC⟩ :=
    ricciArmOrder0CurvCoeff_backgroundDifference_perOrder_l2_tameEnvelope
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  refine ⟨fun i => 2 * (KR i + KC i), fun i => by linarith [hKR_nn i, hKC_nn i], ?_⟩
  intro g₁ P δ hδ_le hδ htie hPball i
  have hwin_nn : 0 ≤ ∑ j ∈ Finset.range (i + 3),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hR2 := hKR g₁ P hδ_le hδ htie hPball i
  have hC2 := hKC g₁ P hδ_le hδ htie hPball i
  have hre : (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
        ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁) -
      (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
        ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) =
      (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
        ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) -
      (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
        ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) := by
    abel
  rw [hre, iteratedCovGrad_sub (I := I) g₀ 2 2 i
    (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
      ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)
    (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
      ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)]
  have hkey := tame_sq_le_two_add
    ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
          ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)
      - iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
          ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)‖
    ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
          ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)‖
    ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
          ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)‖
    (KR i * (1 + ∑ j ∈ Finset.range (i + 3), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2))
    (KC i * (1 + ∑ j ∈ Finset.range (i + 3), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2))
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (norm_sub_le _ _) hR2 hC2
  refine le_trans hkey (le_of_eq ?_)
  ring

theorem ricciArmOrder0BaseCoeff_perOrder_l2_tameEnvelope_generic
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
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁)‖ ^ 2 ≤
            K i * (1 + ∑ j ∈ Finset.range (i + 3),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  obtain ⟨KD, hKD_nn, hKD⟩ :=
    ricciArmOrder0BaseCoeff_backgroundDifference_perOrder_l2_tameEnvelope
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  refine ⟨fun i => 2 * (‖iteratedCovGrad (I := I) g₀ 2 2 i
      (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
        ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 + KD i),
    fun i => by
      linarith [hKD_nn i, sq_nonneg ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
          ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)‖], ?_⟩
  intro g₁ P δ hδ_le hδ htie hPball i
  have hwin_nn : 0 ≤ ∑ j ∈ Finset.range (i + 3),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hD := hKD g₁ P hδ_le hδ htie hPball i
  have hsplit : ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
      ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ =
      (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
        ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) +
      ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
          ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁) -
        (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
          ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)) := by
    abel
  rw [hsplit, iteratedCovGrad_add (I := I) g₀ 2 2 i
    (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
      ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)
    ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
        ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁) -
      (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
        ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀))]
  have hbg_le : ‖iteratedCovGrad (I := I) g₀ 2 2 i
      (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
        ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 ≤
      ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
          ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 *
        (1 + ∑ j ∈ Finset.range (i + 3), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
    have hbg_nn : 0 ≤ ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
          ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 := sq_nonneg _
    nlinarith [hbg_nn, hwin_nn]
  have hkey := tame_sq_le_two_add
    ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
          ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)
      + iteratedCovGrad (I := I) g₀ 2 2 i
        ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
            ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁) -
          (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
            ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀))‖
    ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
          ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)‖
    ‖iteratedCovGrad (I := I) g₀ 2 2 i
        ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
            ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁) -
          (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
            ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀))‖
    (‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
          ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 *
      (1 + ∑ j ∈ Finset.range (i + 3), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2))
    (KD i * (1 + ∑ j ∈ Finset.range (i + 3), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2))
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (norm_add_le _ _) hbg_le hD
  refine le_trans hkey (le_of_eq ?_)
  ring

end Connection
end Integral
end DifferentialGeometry
end
