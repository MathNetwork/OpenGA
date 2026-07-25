import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTowerCurvDiffGridWindow
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTowerRiemannLoweredDifference
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

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck in
theorem riemannianFiberNormSq_iteratedCovGrad_ricciMixedSharpBackgroundDifference_diagonalProductGrid_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
            ((iteratedCovGrad (I := I) g₀ 1 1 i
              (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
                  (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁) -
                endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
                  (ricciEndomorphismField (I := I) (M := M) g₀))).toSection x) ≤
          C i * ∑ k ∈ Finset.range (i + 3),
            ∑ n ∈ Finset.range (k + 1),
              ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
                ∏ m : Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T).toSection x) := by
  classical
  obtain ⟨CA, hCA_nn, hCA⟩ :=
    rfns_iteratedCovGrad_riemannLoweredBackgroundDifference_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨cPhi, hcPhi_nn, hcPhi⟩ := exists_bound_riemannianFiberNormSq_smoothCcTensor
    (I := I) (M := M) g₀ 4 2 (cometricDoubleTraceField (I := I) g₀ 2)
  refine ⟨fun i => diagonalGridGrowthFactor (E := E) i * cPhi * (∑ l ∈ Finset.range (i + 1), CA l),
    fun i => mul_nonneg (mul_nonneg (appCcGdiag_nonneg (E := E) i) hcPhi_nn)
      (Finset.sum_nonneg fun l _ => hCA_nn l), ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound i x
  have hb : ∀ j : ℕ, 0 ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
      ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x) :=
    fun j => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j) x _
  rw [slotInsert_ricMixedSharp_sub_ricEndoRaised_eq_raise_doubleTrace (I := I) (M := M) g₀ g₁]
  rw [riemannianFiberNormSq_iteratedCovGrad_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ 0
    (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
      (ccOperatorFieldComp (I := I) (M := M) g₀ 0 4 2
        (cometricDoubleTraceField (I := I) g₀ 2)
        (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁))) i x]
  rw [riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
    (Equiv.swap (0 : Fin 2) 1)
    (ccOperatorFieldComp (I := I) (M := M) g₀ 0 4 2
      (cometricDoubleTraceField (I := I) g₀ 2)
      (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)) i x]
  refine le_trans (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le
    (I := I) (M := M) g₀ i 0 4 2 (cometricDoubleTraceField (I := I) g₀ 2)
    (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁) x) ?_
  have hAzero : ∀ m : ℕ,
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + (m + 1)) x
        ((iteratedCovGrad (I := I) g₀ 4 2 (m + 1)
          (cometricDoubleTraceField (I := I) g₀ 2)).toSection x) = 0 := by
    intro m
    rw [← rfns_iteratedCovGrad_covGrad_comm_rs (I := I) (M := M) g₀ 4 2 m
      (cometricDoubleTraceField (I := I) g₀ 2) x]
    rw [show covGrad (I := I) (M := M) g₀ 4 2 (cometricDoubleTraceField (I := I) g₀ 2) =
        (0 : SmoothCcTensor g₀ 4 3) from
      cometricDoubleTraceField_covGrad_eq_zero (I := I) g₀ 2]
    rw [show iteratedCovGrad (I := I) g₀ 4 3 m (0 : SmoothCcTensor g₀ 4 3) =
        (0 : SmoothCcTensor g₀ 4 (3 + m)) from by
      induction m with
      | zero => rw [iteratedCovGrad_zero]
      | succ m' ih => rw [iteratedCovGrad_succ, ih, covGrad_zero]]
    rw [show ((0 : SmoothCcTensor g₀ 4 (3 + m)).toSection x) =
        (0 : TensorRSSpace 4 (3 + m) I x) from by
      rw [SmoothCcTensor.toSection_zero]; rfl]
    exact riemannianFiberNormSq_zero (I := I) (M := M) g₀ 4 (3 + m) x
  have hBmono : ∀ i' : ℕ,
      (∑ l ∈ Finset.range (i + 1 - i'),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 4 l
            (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x)) ≤
      ∑ l ∈ Finset.range (i + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 4 l
            (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x) := by
    intro i'
    refine Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.mpr (by omega)) ?_
    intro l _ _
    exact riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (4 + l) x _
  have hterm : ∀ i' ∈ Finset.range (i + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + i') x
          ((iteratedCovGrad (I := I) g₀ 4 2 i'
            (cometricDoubleTraceField (I := I) g₀ 2)).toSection x) *
        (∑ l ∈ Finset.range (i + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 4 l
              (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x)) ≤
      (if i' = 0 then
        cPhi * ∑ l ∈ Finset.range (i + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 4 l
              (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x)
      else 0) := by
    intro i' _
    match i' with
    | 0 =>
        rw [if_pos rfl]
        have hA0 : riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + 0) x
            ((iteratedCovGrad (I := I) g₀ 4 2 0
              (cometricDoubleTraceField (I := I) g₀ 2)).toSection x) ≤ cPhi := by
          rw [iteratedCovGrad_zero]
          exact hcPhi x
        refine mul_le_mul hA0 (hBmono 0) (Finset.sum_nonneg fun l _ =>
          riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (4 + l) x _) hcPhi_nn
    | (m + 1) =>
        rw [if_neg (by omega)]
        rw [hAzero m, zero_mul]
  refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm)
    (appCcGdiag_nonneg (E := E) i)) ?_
  rw [Finset.sum_ite_eq' (Finset.range (i + 1)) 0]
  rw [if_pos (Finset.mem_range.mpr (by omega))]
  have hBgrid : (∑ l ∈ Finset.range (i + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 4 l
          (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x)) ≤
      (∑ l ∈ Finset.range (i + 1), CA l) *
        tWindow (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x)) i := by
    calc (∑ l ∈ Finset.range (i + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 4 l
            (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x))
        ≤ ∑ l ∈ Finset.range (i + 1), CA l *
            tWindow (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
              ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x)) l := by
          refine Finset.sum_le_sum (fun l _ => ?_)
          have h := hCA g₁ T htie hδ_le hδ0 hbound l x
          rw [← tWindow_eq_tripleSum (I := I) (M := M) g₀ T x l] at h
          exact h
      _ ≤ ∑ l ∈ Finset.range (i + 1), CA l *
            tWindow (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
              ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x)) i := by
          refine Finset.sum_le_sum (fun l hl => ?_)
          refine mul_le_mul_of_nonneg_left ?_ (hCA_nn l)
          exact tWindow_mono _ hb (by
            have := Finset.mem_range.mp hl
            omega)
      _ = (∑ l ∈ Finset.range (i + 1), CA l) *
            tWindow (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
              ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x)) i := by
          rw [Finset.sum_mul]
  rw [← tWindow_eq_tripleSum (I := I) (M := M) g₀ T x i]
  calc diagonalGridGrowthFactor (E := E) i *
        (cPhi * ∑ l ∈ Finset.range (i + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 4 l
              (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x))
      ≤ diagonalGridGrowthFactor (E := E) i * (cPhi * ((∑ l ∈ Finset.range (i + 1), CA l) *
          tWindow (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
            ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x)) i)) := by
        refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg (E := E) i)
        exact mul_le_mul_of_nonneg_left hBgrid hcPhi_nn
    _ = diagonalGridGrowthFactor (E := E) i * cPhi * (∑ l ∈ Finset.range (i + 1), CA l) *
          tWindow (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
            ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x)) i := by
        ring

private lemma diagonalGrid_assembly_arith (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j)
    (i : ℕ) (G : ℝ) (hG : 0 ≤ G)
    (CL CD cbg : ℕ → ℝ) (hCL_nn : ∀ k, 0 ≤ CL k) (hCD_nn : ∀ k, 0 ≤ CD k)
    (hcbg_nn : ∀ k, 0 ≤ cbg k)
    (t u ap : ℝ) (wj vl : ℕ → ℝ)
    (ht : t ≤ 2 * u + 2 * ap)
    (hu : u ≤ CL i * tWindow b i)
    (hap : ap ≤ G * ∑ j ∈ Finset.range (i + 1), wj j * ∑ l ∈ Finset.range (i + 1 - j), vl l)
    (hwj : ∀ j, j ≤ i → wj j ≤ (2 * CL j + 2 * cbg j) * tWindow b j)
    (hvl_nn : ∀ l, 0 ≤ vl l)
    (hvl : ∀ l, l ≤ i → vl l ≤ CD l * Combinatorics.antidiagonalTupleGrid b l) :
    t ≤ (2 * CL i + 2 * (G * ∑ j ∈ Finset.range (i + 1), (2 * CL j + 2 * cbg j) *
        ∑ l ∈ Finset.range (i + 1 - j), CD l * tWindowMulConst j l)) * tWindow b i := by
  have hstep : ∀ j ∈ Finset.range (i + 1),
      wj j * ∑ l ∈ Finset.range (i + 1 - j), vl l ≤
        ((2 * CL j + 2 * cbg j) * ∑ l ∈ Finset.range (i + 1 - j),
          CD l * tWindowMulConst j l) * tWindow b i := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hj_le : j ≤ i := by omega
    have hcj_nn : 0 ≤ 2 * CL j + 2 * cbg j := by
      have := hCL_nn j
      have := hcbg_nn j
      linarith
    have h1 : wj j * ∑ l ∈ Finset.range (i + 1 - j), vl l ≤
        ((2 * CL j + 2 * cbg j) * tWindow b j) * ∑ l ∈ Finset.range (i + 1 - j), vl l :=
      mul_le_mul_of_nonneg_right (hwj j hj_le) (Finset.sum_nonneg (fun l _ => hvl_nn l))
    refine le_trans h1 ?_
    have h2 : ∀ l ∈ Finset.range (i + 1 - j), tWindow b j * vl l ≤
        CD l * tWindowMulConst j l * tWindow b i := by
      intro l hl
      rw [Finset.mem_range] at hl
      have hl_le : l ≤ i := by omega
      have hjl : j + l ≤ i := by omega
      have h3 : tWindow b j * vl l ≤
          tWindow b j * (CD l * Combinatorics.antidiagonalTupleGrid b l) :=
        mul_le_mul_of_nonneg_left (hvl l hl_le) (tWindow_nonneg b hb j)
      refine le_trans h3 ?_
      rw [show tWindow b j * (CD l * Combinatorics.antidiagonalTupleGrid b l) =
          CD l * (tWindow b j * Combinatorics.antidiagonalTupleGrid b l) from by ring]
      calc CD l * (tWindow b j * Combinatorics.antidiagonalTupleGrid b l)
          ≤ CD l * (tWindowMulConst j l * tWindow b (j + l)) :=
            mul_le_mul_of_nonneg_left
              (tWindow_mul_antidiagonalTupleGrid_le b hb j l) (hCD_nn l)
        _ ≤ CD l * (tWindowMulConst j l * tWindow b i) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (tWindow_mono b hb hjl)
                (tWindowMulConst_nonneg j l)) (hCD_nn l)
        _ = CD l * tWindowMulConst j l * tWindow b i := by ring
    calc ((2 * CL j + 2 * cbg j) * tWindow b j) * ∑ l ∈ Finset.range (i + 1 - j), vl l
        = (2 * CL j + 2 * cbg j) * ∑ l ∈ Finset.range (i + 1 - j), tWindow b j * vl l := by
          rw [mul_assoc, Finset.mul_sum]
      _ ≤ (2 * CL j + 2 * cbg j) * ∑ l ∈ Finset.range (i + 1 - j),
            CD l * tWindowMulConst j l * tWindow b i :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum h2) hcj_nn
      _ = ((2 * CL j + 2 * cbg j) * ∑ l ∈ Finset.range (i + 1 - j),
            CD l * tWindowMulConst j l) * tWindow b i := by
          rw [← Finset.sum_mul]
          ring
  have hW_nn : 0 ≤ tWindow b i := tWindow_nonneg b hb i
  have hap2 : ap ≤ G * ((∑ j ∈ Finset.range (i + 1), (2 * CL j + 2 * cbg j) *
      ∑ l ∈ Finset.range (i + 1 - j), CD l * tWindowMulConst j l) * tWindow b i) := by
    refine le_trans hap ?_
    refine mul_le_mul_of_nonneg_left ?_ hG
    refine le_trans (Finset.sum_le_sum hstep) (le_of_eq ?_)
    rw [← Finset.sum_mul]
  have hu2 : u ≤ CL i * tWindow b i := hu
  calc t ≤ 2 * u + 2 * ap := ht
    _ ≤ 2 * (CL i * tWindow b i) + 2 * (G * ((∑ j ∈ Finset.range (i + 1),
          (2 * CL j + 2 * cbg j) * ∑ l ∈ Finset.range (i + 1 - j),
            CD l * tWindowMulConst j l) * tWindow b i)) := by linarith
    _ = (2 * CL i + 2 * (G * ∑ j ∈ Finset.range (i + 1), (2 * CL j + 2 * cbg j) *
          ∑ l ∈ Finset.range (i + 1 - j), CD l * tWindowMulConst j l)) * tWindow b i := by
        ring

theorem riemannianFiberNormSq_iteratedCovGrad_slotInsertEndoCc_zero_ricEndoBackgroundDifferenceField_diagonalProductGrid_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
            ((iteratedCovGrad (I := I) g₀ 1 1 i
              (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
                (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))).toSection x) ≤
          C i * ∑ k ∈ Finset.range (i + 3),
            ∑ n ∈ Finset.range (k + 1),
              ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
                ∏ m : Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T).toSection x) := by
  classical
  obtain ⟨CL, hCL_nn, hCL⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_ricciMixedSharpBackgroundDifference_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨CD, hCD_nn, hCD⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_slotInsertEndoCc_zero_gInvDiffRaisedEndoField_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨cbg, hcbg_nn, hcbg⟩ := exists_iteratedCovGrad_fiberNormSq_bound (I := I) (M := M) g₀ 1 1
    (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0 (ricciEndomorphismField (I := I) (M := M) g₀))
  refine ⟨fun i => 2 * CL i + 2 * (diagonalGridGrowthFactor (E := E) i *
      ∑ j ∈ Finset.range (i + 1), (2 * CL j + 2 * cbg j) *
        ∑ l ∈ Finset.range (i + 1 - j), CD l * tWindowMulConst j l),
    fun i => ?_, ?_⟩
  · have h1 : 0 ≤ diagonalGridGrowthFactor (E := E) i := appCcGdiag_nonneg (E := E) i
    have h2 : 0 ≤ ∑ j ∈ Finset.range (i + 1), (2 * CL j + 2 * cbg j) *
        ∑ l ∈ Finset.range (i + 1 - j), CD l * tWindowMulConst j l :=
      Finset.sum_nonneg (fun j _ => mul_nonneg
        (by have := hCL_nn j; have := hcbg_nn j; linarith)
        (Finset.sum_nonneg (fun l _ => mul_nonneg (hCD_nn l) (tWindowMulConst_nonneg j l))))
    have h3 := mul_nonneg h1 h2
    have h4 := hCL_nn i
    linarith
  · intro g₁ T htie δ hδ_le hδ0 hbound i x
    have hb : ∀ j : ℕ, 0 ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x) :=
      fun j => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j) x _
    rw [← tWindow_eq_tripleSum (I := I) (M := M) g₀ T x i]
    have hsec : (iteratedCovGrad (I := I) g₀ 1 1 i
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))).toSection x =
        (iteratedCovGrad (I := I) g₀ 1 1 i
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
              (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁) -
            endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
              (ricciEndomorphismField (I := I) (M := M) g₀))).toSection x +
          (iteratedCovGrad (I := I) g₀ 1 1 i
            (ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 1
              (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
                (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁))
              (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
                (gInvDiffRaisedEndoField (I := I) g₀ g₁)))).toSection x := by
      rw [slotInsertEndoCc_zero_ricEndoBackgroundDifference_telescope (I := I) (M := M) g₀ g₁,
        iteratedCovGrad_add (I := I) g₀ 1 1 i _ _, SmoothCcTensor.toSection_add]
      rfl
    have hLHS : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 1 i
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
            (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))).toSection x) ≤
        2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
            ((iteratedCovGrad (I := I) g₀ 1 1 i
              (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
                  (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁) -
                endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
                  (ricciEndomorphismField (I := I) (M := M) g₀))).toSection x) +
          2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
            ((iteratedCovGrad (I := I) g₀ 1 1 i
              (ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 1
                (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
                  (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁))
                (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
                  (gInvDiffRaisedEndoField (I := I) g₀ g₁)))).toSection x) := by
      rw [hsec]
      exact riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 1 (1 + i) x _ _
    have hu : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 1 i
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
              (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁) -
            endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
              (ricciEndomorphismField (I := I) (M := M) g₀))).toSection x) ≤
        CL i * tWindow (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x)) i := by
      rw [tWindow_eq_tripleSum (I := I) (M := M) g₀ T x i]
      exact hCL g₁ T htie hδ_le hδ0 hbound i x
    have hap := riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le
      (I := I) (M := M) g₀ i 1 1 1
      (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0 (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁))
      (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0 (gInvDiffRaisedEndoField (I := I) g₀ g₁)) x
    have hwj : ∀ j, j ≤ i → riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + j) x
        ((iteratedCovGrad (I := I) g₀ 1 1 j
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
            (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁))).toSection x) ≤
        (2 * CL j + 2 * cbg j) *
          tWindow (fun j' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j') x
            ((iteratedCovGrad (I := I) g₀ 0 2 j' T).toSection x)) j := by
      intro j hj
      have hsplit : endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁) =
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
              (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁) -
            endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
              (ricciEndomorphismField (I := I) (M := M) g₀)) +
          endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
            (ricciEndomorphismField (I := I) (M := M) g₀) := by
        rw [sub_add_cancel]
      have hsec2 : (iteratedCovGrad (I := I) g₀ 1 1 j
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
            (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁))).toSection x =
          (iteratedCovGrad (I := I) g₀ 1 1 j
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
                (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁) -
              endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
                (ricciEndomorphismField (I := I) (M := M) g₀))).toSection x +
            (iteratedCovGrad (I := I) g₀ 1 1 j
              (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
                (ricciEndomorphismField (I := I) (M := M) g₀))).toSection x := by
        conv_lhs => rw [hsplit]
        rw [iteratedCovGrad_add (I := I) g₀ 1 1 j _ _, SmoothCcTensor.toSection_add]
        rfl
      rw [hsec2]
      refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 1 (1 + j) x _ _) ?_
      have hone : 1 ≤ tWindow (fun j' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j') x
          ((iteratedCovGrad (I := I) g₀ 0 2 j' T).toSection x)) j :=
        one_le_tWindow _ hb j
      have hb1 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + j) x
          ((iteratedCovGrad (I := I) g₀ 1 1 j
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
                (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁) -
              endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
                (ricciEndomorphismField (I := I) (M := M) g₀))).toSection x) ≤
          CL j * tWindow (fun j' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j') x
            ((iteratedCovGrad (I := I) g₀ 0 2 j' T).toSection x)) j := by
        rw [tWindow_eq_tripleSum (I := I) (M := M) g₀ T x j]
        exact hCL g₁ T htie hδ_le hδ0 hbound j x
      have hb2 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + j) x
          ((iteratedCovGrad (I := I) g₀ 1 1 j
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
              (ricciEndomorphismField (I := I) (M := M) g₀))).toSection x) ≤
          cbg j * tWindow (fun j' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j') x
            ((iteratedCovGrad (I := I) g₀ 0 2 j' T).toSection x)) j :=
        le_trans (hcbg j x) (le_mul_of_one_le_right (hcbg_nn j) hone)
      linarith
    have hvl : ∀ l, l ≤ i → riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
        ((iteratedCovGrad (I := I) g₀ 1 1 l
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
            (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x) ≤
        CD l * Combinatorics.antidiagonalTupleGrid
          (fun j' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j') x
            ((iteratedCovGrad (I := I) g₀ 0 2 j' T).toSection x)) l := by
      intro l _
      rw [antidiagonalTupleGrid_eq_doubleSum (I := I) (M := M) g₀ T x l]
      exact hCD g₁ T htie hδ_le hδ0 hbound l x
    exact diagonalGrid_assembly_arith
      (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x)) hb i
      (diagonalGridGrowthFactor (E := E) i) (appCcGdiag_nonneg (E := E) i)
      CL CD cbg hCL_nn hCD_nn hcbg_nn
      (riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 1 i
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
            (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))).toSection x))
      (riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 1 i
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
              (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁) -
            endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
              (ricciEndomorphismField (I := I) (M := M) g₀))).toSection x))
      (riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 1 i
          (ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 1
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
              (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁))
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
              (gInvDiffRaisedEndoField (I := I) g₀ g₁)))).toSection x))
      (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + j) x
        ((iteratedCovGrad (I := I) g₀ 1 1 j
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
            (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁))).toSection x))
      (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
        ((iteratedCovGrad (I := I) g₀ 1 1 l
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
            (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x))
      hLHS hu hap hwj
      (fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (1 + l) x _)
      hvl

section RiemannMixedBiContr

section NormedRiemannMixedBiContr

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

set_option backward.isDefEq.respectTransparency false

open DifferentialGeometry.Integral.DivergenceTheorem

def riemannMixedKernelBilin (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (p q : TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun v0 => (g₀.inner x (riemannOp (LeviCivita (I := I) g₁) x v0 p q))
      map_add' := fun v0 v0' => by
        rw [(riemannOp (LeviCivita (I := I) g₁) x).map_add v0 v0',
          ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply, map_add]
      map_smul' := fun c v0 => by
        rw [(riemannOp (LeviCivita (I := I) g₁) x).map_smul c v0,
          ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, map_smul,
          RingHom.id_apply] }

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
@[simp] theorem riemannMixedKernelBilin_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (p q v0 v1 : TangentSpace I x) :
    riemannMixedKernelBilin (I := I) g₀ g₁ x p q v0 v1 =
      g₀.inner x (riemannOp (LeviCivita (I := I) g₁) x v0 p q) v1 := by
  rw [riemannMixedKernelBilin, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
    AddHom.coe_mk]

def riemannMixedSummandFib (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (p q : TangentSpace I x) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  haveI : FiniteDimensional ℝ (Tensor0SSpace 2 I x) := inferInstance
  LinearMap.toContinuousLinearMap
    { toFun := fun D =>
        (Tensor0SSpace.toModel D ![(p : E), (q : E)]) •
          Tensor0SSpace.ofModel (I := I) (x := x)
            (bilinFormToModel E (riemannMixedKernelBilin (I := I) g₀ g₁ x p q))
      map_add' := fun D D' => by
        rw [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply, add_smul]
      map_smul' := fun c D => by
        rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul,
          RingHom.id_apply, mul_smul] }

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
@[simp] theorem riemannMixedSummandFib_toModel (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (p q : TangentSpace I x) (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel (riemannMixedSummandFib (I := I) g₀ g₁ x p q D) v =
      (Tensor0SSpace.toModel D ![(p : E), (q : E)]) *
        g₀.inner x (riemannOp (LeviCivita (I := I) g₁) x (v 0) p q) (v 1) := by
  rw [riemannMixedSummandFib, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
    AddHom.coe_mk, Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply,
    Tensor0SSpace.toModel_ofModel, bilinFormToModel_apply, smul_eq_mul]
  rfl

def riemannMixedBiContrFibFixedFrame (g₀ g₁ : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  (2 : ℝ) • ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
    riemannMixedSummandFib (I := I) g₀ g₁ x (B a x) (B b x)

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem riemannMixedBiContrFibFixedFrame_toModel (g₀ g₁ : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M)
    (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel (riemannMixedBiContrFibFixedFrame (I := I) g₀ g₁ B x D) v =
      2 * ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        g₀.inner x (riemannOp (LeviCivita (I := I) g₁) x (v 0) (B a x) (B b x)) (v 1) *
          Tensor0SSpace.toModel D ![(B a x : E), (B b x : E)] := by
  classical
  rw [riemannMixedBiContrFibFixedFrame, ContinuousLinearMap.smul_apply,
    Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  congr 1
  rw [ContinuousLinearMap.sum_apply, ← Tensor0SSpace.toModelL_apply, map_sum,
    ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [ContinuousLinearMap.sum_apply, Tensor0SSpace.toModelL_apply, ← Tensor0SSpace.toModelL_apply,
    map_sum, ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Tensor0SSpace.toModelL_apply, riemannMixedSummandFib_toModel]
  ring

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem mixedKernelScalar_global (g₀ g₁ : SmoothRiemannianMetric I M)
    {Y W p q : Π b : M, TangentSpace I b}
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W))
    (hp : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% p))
    (hq : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% q)) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => g₀.inner x
        (riemannOp (LeviCivita (I := I) g₁) x (Y x) (p x) (q x)) (W x)) := by
  classical
  have hRsec : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => riemannSec (LeviCivita (I := I) g₁) Y p q b)) :=
    riemannSec_contMDiff (cov := LeviCivita (I := I) g₁) hY hp hq
  have hcongr : (fun x : M => g₀.inner x
        (riemannOp (LeviCivita (I := I) g₁) x (Y x) (p x) (q x)) (W x)) =
      (fun x : M => g₀.inner x (riemannSec (LeviCivita (I := I) g₁) Y p q x) (W x)) := by
    funext x
    rw [riemannOp_apply_smooth (cov := LeviCivita (I := I) g₁) hY hp hq]
  rw [hcongr]
  exact contMDiff_g_inner_of_smooth_sections (I := I) g₀
    ⟨fun b => riemannSec (LeviCivita (I := I) g₁) Y p q b, hRsec⟩ ⟨fun b => W b, hW⟩

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem riemannMixedKernelBilin_homSection_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M)
    {p q : Π b : M, TangentSpace I b}
    (hp : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% p))
    (hq : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% q)) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun b : M => TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ)
        x (riemannMixedKernelBilin (I := I) g₀ g₁ x (p x) (q x))) := by
  classical
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun x : M => TangentSpace I x →L[ℝ] ℝ)
    (φ := fun x : M => riemannMixedKernelBilin (I := I) g₀ g₁ x (p x) (q x))
  intro Y
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun _ : M => ℝ)
    (φ := fun x : M => riemannMixedKernelBilin (I := I) g₀ g₁ x (p x) (q x) (Y x))
  intro W
  have h_scalar := mixedKernelScalar_global (I := I) g₀ g₁ Y.contMDiff W.contMDiff hp hq
  intro x
  rw [contMDiffAt_section]
  refine (h_scalar.contMDiffAt).congr_of_eventuallyEq ?_
  filter_upwards with y
  change riemannMixedKernelBilin (I := I) g₀ g₁ y (p y) (q y) (Y y) (W y) =
    (trivializationAt ℝ (Bundle.Trivial M ℝ) x ⟨y, _⟩).2
  rw [riemannMixedKernelBilin_apply]
  rfl

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem riemannMixedBiContrFibFixedFrame_apply_section_contMDiff
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (Y : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun x : M => Tensor0SSpace 2 I x⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) x
        (riemannMixedBiContrFibFixedFrame (I := I) g₀ g₁ B x (Y x))) := by
  classical
  have hsummand : ∀ a b : Fin (Module.finrank ℝ E),
      ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
          (E := fun z : M => Tensor0SSpace 2 I z) x
          (riemannMixedSummandFib (I := I) g₀ g₁ x (B a x) (B b x) (Y x))) := by
    intro a b
    have hscalar : ContMDiff I 𝓘(ℝ, ℝ) ∞
        (fun x : M => Tensor0SSpace.toModel (Y x) ![(B a x : E), (B b x : E)]) := by
      have h := TensorMultilinear.contMDiff_section_apply (n := 2)
        (fun b => Y b) Y.contMDiff
        (![fun z => B a z, fun z => B b z])
        (by
          intro i
          fin_cases i
          · exact hB a
          · exact hB b)
      refine h.congr ?_
      intro x
      congr 1
      funext i
      fin_cases i <;> rfl
    have hbilin := contMDiff_bilinSection_of_homSection (I := I)
      (fun x => riemannMixedKernelBilin (I := I) g₀ g₁ x (B a x) (B b x))
      (riemannMixedKernelBilin_homSection_contMDiff (I := I) g₀ g₁ (hB a) (hB b))
    have hsmul := ContMDiff.smul_section (f := fun x => Tensor0SSpace.toModel (Y x)
        ![(B a x : E), (B b x : E)])
      (s := fun x => Tensor0SSpace.ofModel (I := I) (x := x)
        (bilinFormToModel (TangentSpace I x)
          (riemannMixedKernelBilin (I := I) g₀ g₁ x (B a x) (B b x))))
      hscalar hbilin
    refine hsmul.congr ?_
    intro x
    rfl
  set S : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯ :=
    fun a b =>
      { toFun := fun x : M => riemannMixedSummandFib (I := I) g₀ g₁ x (B a x) (B b x) (Y x)
        contMDiff_toFun := hsummand a b } with hS_def
  set Stot : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯ :=
    (2 : ℝ) • ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), S a b
    with hStot_def
  have hStot := Stot.contMDiff
  refine hStot.congr ?_
  intro x
  refine congrArg (TotalSpace.mk' (Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SSpace 2 I z) x) ?_
  rw [riemannMixedBiContrFibFixedFrame, hStot_def, ContMDiffSection.coe_smul, Pi.smul_apply]
  have hcoeOuter : ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), S a b :
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
        Π z : M, Tensor0SSpace 2 I z) =
      ∑ a : Fin (Module.finrank ℝ E),
        ((∑ b : Fin (Module.finrank ℝ E), S a b :
          Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
          Π z : M, Tensor0SSpace 2 I z) :=
    map_sum (ContMDiffSection.coeAddHom I (Tensor0SModel 2 ℝ E) ∞
      (fun z : M => Tensor0SSpace 2 I z))
      (fun a => ∑ b : Fin (Module.finrank ℝ E), S a b) Finset.univ
  have hcoeInner : ∀ a : Fin (Module.finrank ℝ E),
      ((∑ b : Fin (Module.finrank ℝ E), S a b :
        Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
        Π z : M, Tensor0SSpace 2 I z) =
      ∑ b : Fin (Module.finrank ℝ E), ((S a b : Π z : M, Tensor0SSpace 2 I z)) := fun a =>
    map_sum (ContMDiffSection.coeAddHom I (Tensor0SModel 2 ℝ E) ∞
      (fun z : M => Tensor0SSpace 2 I z)) (fun b => S a b) Finset.univ
  have hsum : ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), S a b :
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
        Π z : M, Tensor0SSpace 2 I z) x =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        (S a b : Π z : M, Tensor0SSpace 2 I z) x := by
    rw [hcoeOuter, Finset.sum_apply]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [hcoeInner a, Finset.sum_apply]
  rw [hsum, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply]
  congr 1
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [ContinuousLinearMap.sum_apply]
  rfl

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem riemannMixedBiContrFibFixedFrame_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i))) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (riemannMixedBiContrFibFixedFrame (I := I) g₀ g₁ B x))) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I)
    (F₁ := Tensor0SModel 2 ℝ E) (V₁ := fun z : M => Tensor0SSpace 2 I z)
    (F₂ := Tensor0SModel 2 ℝ E) (V₂ := fun z : M => Tensor0SSpace 2 I z)
    (φ := fun x : M => riemannMixedBiContrFibFixedFrame (I := I) g₀ g₁ B x)
  intro Y
  exact riemannMixedBiContrFibFixedFrame_apply_section_contMDiff (I := I) g₀ g₁ B hB Y

def frameRiemannMixedKernel (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (v0 v1 : TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun p => (g₀.inner x).flip v1 |>.comp
        ((riemannOp (LeviCivita (I := I) g₁) x v0 p))
      map_add' := fun p p' => by
        ext q
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
          (riemannOp (LeviCivita (I := I) g₁) x v0).map_add p p', map_add]
      map_smul' := fun c p => by
        ext q
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
          RingHom.id_apply, (riemannOp (LeviCivita (I := I) g₁) x v0).map_smul c p, map_smul] }

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem frameRiemannMixedKernel_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (v0 v1 p q : TangentSpace I x) :
    frameRiemannMixedKernel (I := I) g₀ g₁ x v0 v1 p q =
      g₀.inner x (riemannOp (LeviCivita (I := I) g₁) x v0 p q) v1 := by
  rw [frameRiemannMixedKernel, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
    AddHom.coe_mk, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]

def riemannMixedBiContrFib (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  riemannMixedBiContrFibFixedFrame (I := I) g₀ g₁ (smoothOrthoFrame (I := I) g₀ x) x

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private theorem riemannMixedBiContrFibFixedFrame_eq_of_orthonormal
    (g₀ g₁ : SmoothRiemannianMetric I M) (y : M)
    (B C : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i j, g₀.inner y (B i y) (B j y) = if i = j then (1 : ℝ) else 0)
    (hC : ∀ i j, g₀.inner y (C i y) (C j y) = if i = j then (1 : ℝ) else 0) :
    riemannMixedBiContrFibFixedFrame (I := I) g₀ g₁ B y =
      riemannMixedBiContrFibFixedFrame (I := I) g₀ g₁ C y := by
  classical
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  rw [riemannMixedBiContrFibFixedFrame_toModel, riemannMixedBiContrFibFixedFrame_toModel]
  apply congrArg (fun z : ℝ => 2 * z)
  have hrewrite : ∀ (Bf : Fin (Module.finrank ℝ E) → TangentSpace I y),
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        g₀.inner y (riemannOp (LeviCivita (I := I) g₁) y (v 0) (Bf a) (Bf b)) (v 1) *
          Tensor0SSpace.toModel D ![(Bf a : E), (Bf b : E)] =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        frameRiemannMixedKernel (I := I) g₀ g₁ y (v 0) (v 1) (Bf a) (Bf b) *
          (bilinFormToModel (TangentSpace I y)).symm (Tensor0SSpace.toModel D) (Bf a) (Bf b) := by
    intro Bf
    refine Finset.sum_congr rfl (fun a _ => ?_)
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [frameRiemannMixedKernel_apply (I := I) g₀ g₁ y (v 0) (v 1) (Bf a) (Bf b),
      bilinFormToModel_symm_apply (TangentSpace I y) (Tensor0SSpace.toModel D) (Bf a) (Bf b)]
    rfl
  rw [hrewrite (fun a => B a y), hrewrite (fun a => C a y)]
  exact double_frame_bilin_trace_indep (I := I) g₀ y
    (frameRiemannMixedKernel (I := I) g₀ g₁ y (v 0) (v 1))
    ((bilinFormToModel (TangentSpace I y)).symm (Tensor0SSpace.toModel D))
    (fun a => B a y) (fun a => C a y) hB hC

omit [CompactSpace M] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem riemannMixedBiContrFib_eq_fixedFrame_on_nbhd (g₀ g₁ : SmoothRiemannianMetric I M)
    (x₀ : M) {y : M} (hy : y ∈ smoothOrthoFrameNbhd (I := I) (M := M) x₀) :
    riemannMixedBiContrFib (I := I) (M := M) g₀ g₁ y =
      riemannMixedBiContrFibFixedFrame (I := I) g₀ g₁ (smoothOrthoFrame (I := I) g₀ x₀) y := by
  rw [riemannMixedBiContrFib]
  exact riemannMixedBiContrFibFixedFrame_eq_of_orthonormal (I := I) g₀ g₁ y
    (smoothOrthoFrame (I := I) g₀ y) (smoothOrthoFrame (I := I) g₀ x₀)
    (fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g₀ y i j)
    (fun i j => smoothOrthoFrame_orthonormal (I := I) g₀ x₀ hy i j)

omit [CompactSpace M] [I.Boundaryless] in
theorem riemannMixedBiContrFib_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (riemannMixedBiContrFib (I := I) (M := M) g₀ g₁ x))) := by
  classical
  intro x₀
  have h_fixed : ContMDiffAt I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (riemannMixedBiContrFibFixedFrame (I := I) g₀ g₁
          (smoothOrthoFrame (I := I) g₀ x₀) x))) x₀ :=
    riemannMixedBiContrFibFixedFrame_contMDiff (I := I) g₀ g₁ (smoothOrthoFrame (I := I) g₀ x₀)
      (fun i => smoothOrthoFrame_smooth (I := I) g₀ x₀ i) x₀
  refine h_fixed.congr_of_eventuallyEq ?_
  filter_upwards [smoothOrthoFrameNbhd_mem_nhds (I := I) (M := M) x₀] with y hy
  exact congrArg (TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
    (E := fun z : M => TensorRSSpace 2 2 I z) y)
    (congrArg TensorRSSpace.ofCLM
      (riemannMixedBiContrFib_eq_fixedFrame_on_nbhd (I := I) g₀ g₁ x₀ hy))

def ricciArmOrder0RiemannMixedCoeff (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (riemannMixedBiContrFib (I := I) (M := M) g₀ g₁ x))
      contMDiff_toFun := riemannMixedBiContrFib_contMDiff (I := I) (M := M) g₀ g₁ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

omit [I.Boundaryless] in
theorem ricciArmOrder0RiemannMixedCoeff_toSection (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (ricciArmOrder0RiemannMixedCoeff (I := I) (M := M) g₀ g₁).toSection x =
      (show TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (riemannMixedBiContrFib (I := I) (M := M) g₀ g₁ x)) := rfl

set_option backward.isDefEq.respectTransparency false in
omit [I.Boundaryless] in
theorem ricciArmOrder0RiemannMixedCoeff_self (g₀ : SmoothRiemannianMetric I M) :
    ricciArmOrder0RiemannMixedCoeff (I := I) (M := M) g₀ g₀ =
      ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  rw [show ((ricciArmOrder0RiemannMixedCoeff (I := I) (M := M) g₀ g₀).toSection x) D =
      riemannMixedBiContrFib (I := I) (M := M) g₀ g₀ x D from rfl]
  rw [show ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀).toSection x) D =
      riemannBiContrFib (I := I) g₀ x D from rfl]
  rw [riemannMixedBiContrFib, riemannBiContrFib, riemannMixedBiContrFibFixedFrame_toModel,
    riemannBiContrFibFixedFrame_toModel]

end NormedRiemannMixedBiContr

end RiemannMixedBiContr

end Connection
end Integral
end DifferentialGeometry
end
