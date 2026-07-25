import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.PouComponentBound.ChartAlphaPouAlphaPouBetaCovBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RawConnLapL2SobolevBounds.RawTensorConnLapL2WtwokTwoBound


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set IsManifold ContinuousLinearMap Filter
open MeasureTheory
open scoped Manifold Topology Bundle ContDiff BigOperators ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Tensor
open Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Sobolev.Tensor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
private lemma sum_wkpNorm_sq_α_le_wtwokTwoNorm_sq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T : SmoothCcTensor g r s) :
    (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
        ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
          (iteratedWeakSobolevNorm (d := Module.finrank ℝ E) 0 2
              (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
              (chartTargetEuclid (I := I) (M := M) α)) ^ 2) ≤
      (wtwokTwoNorm (I := I) (M := M) g 0 T) ^ 2 := by
  classical
  set w : M → (Fin r → Fin (Module.finrank ℝ E)) →
      (Fin s → Fin (Module.finrank ℝ E)) → ℝ≥0∞ :=
    fun α' Idx Jdx => iteratedWeakSobolevNorm (d := Module.finrank ℝ E) 0 2
      (tensorChartComp (I := I) (M := M) g r s T α' Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α') with hw_def
  set S : M → ℝ≥0∞ := fun α' =>
    ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
      ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
        w α' Idx Jdx with hS_def
  have h_inner :
      ∀ Idx : Fin r → Fin (Module.finrank ℝ E),
        (∑ Jdx : Fin s → Fin (Module.finrank ℝ E), (w α Idx Jdx) ^ 2) ≤
          (∑ Jdx : Fin s → Fin (Module.finrank ℝ E), w α Idx Jdx) ^ 2 := by
    intro Idx
    exact Finset.sum_sq_le_sq_sum_of_nonneg (fun Jdx _ => zero_le _)
  set u : (Fin r → Fin (Module.finrank ℝ E)) → ℝ≥0∞ :=
    fun Idx => ∑ Jdx : Fin s → Fin (Module.finrank ℝ E), w α Idx Jdx with hu_def
  have h_outer : (∑ Idx : Fin r → Fin (Module.finrank ℝ E), (u Idx) ^ 2) ≤
      (∑ Idx : Fin r → Fin (Module.finrank ℝ E), u Idx) ^ 2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg (fun Idx _ => zero_le _)
  have h_double :
      (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E), (w α Idx Jdx) ^ 2) ≤
        (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E), w α Idx Jdx) ^ 2 := by
    refine le_trans ?_ h_outer
    refine Finset.sum_le_sum ?_
    intro Idx _
    exact h_inner Idx
  have hSα_eq : S α =
      ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
        ∑ Jdx : Fin s → Fin (Module.finrank ℝ E), w α Idx Jdx := rfl
  have h_tsum_le : S α ≤ ∑' β : M, S β := ENNReal.le_tsum α
  have h_tsum_eq : (∑' β : M, S β) = wtwokTwoNorm (I := I) (M := M) g 0 T := by
    unfold wtwokTwoNorm
    refine tsum_congr ?_
    intro β
    change (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E), w β Idx Jdx) =
        ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (2 * 0) 2
              (tensorChartComp (I := I) (M := M) g r s T β Idx Jdx)
              (chartTargetEuclid (I := I) (M := M) β)
    refine Finset.sum_congr rfl (fun Idx _ => ?_)
    refine Finset.sum_congr rfl (fun Jdx _ => ?_)
    change iteratedWeakSobolevNorm (d := Module.finrank ℝ E) 0 2
        (tensorChartComp (I := I) (M := M) g r s T β Idx Jdx)
        (chartTargetEuclid (I := I) (M := M) β) =
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (2 * 0) 2
        (tensorChartComp (I := I) (M := M) g r s T β Idx Jdx)
        (chartTargetEuclid (I := I) (M := M) β)
    congr 1
  have h_Sα_le_wt : S α ≤ wtwokTwoNorm (I := I) (M := M) g 0 T := by
    rw [← h_tsum_eq]
    exact h_tsum_le
  have h_Sα_sq_le_wt_sq :
      (S α) ^ 2 ≤ (wtwokTwoNorm (I := I) (M := M) g 0 T) ^ 2 := by
    have := h_Sα_le_wt
    exact pow_le_pow_left' this 2
  calc (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            (iteratedWeakSobolevNorm (d := Module.finrank ℝ E) 0 2
                (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
                (chartTargetEuclid (I := I) (M := M) α)) ^ 2)
      = (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E), (w α Idx Jdx) ^ 2) := by
        refine Finset.sum_congr rfl (fun Idx _ => ?_)
        refine Finset.sum_congr rfl (fun Jdx _ => ?_)
        rfl
    _ ≤ (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E), w α Idx Jdx) ^ 2 := h_double
    _ = (S α) ^ 2 := by rw [hSα_eq]
    _ ≤ (wtwokTwoNorm (I := I) (M := M) g 0 T) ^ 2 := h_Sα_sq_le_wt_sq

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chart_α_pou_sq_repr_L2_le_wtwokTwoNorm_sq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (T : SmoothCcTensor g r s),
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2 *
                ‖tensorRSChartE_section_repr (I := I) r s α
                    (fun z : M => T.toSection z)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ ^ 2)
            ∂(volume : Measure EuclN) ≤
          ENNReal.ofReal K *
            (wtwokTwoNorm (I := I) (M := M) g 0 T) ^ 2 := by
  classical
  obtain ⟨K_up, hK_up_nn, hK_up_le⟩ :=
    chartTargetPouWeightedL2NormSq_repr_le_sum_chartComp_L2NormSq
      (E := E) (I := I) (M := M) g r s α
  refine ⟨K_up, hK_up_nn, ?_⟩
  intro T
  have h_LHS_eq :
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal
            (((chartAtlasPOU I M α : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2 *
              ‖tensorRSChartE_section_repr (I := I) r s α
                  (fun z : M => T.toSection z)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ ^ 2)
          ∂(volume : Measure EuclN) =
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
              ENNReal.ofReal
                (‖tensorRSChartE_section_repr (I := I) r s α
                    (fun z : M => T.toSection z)
                    ((extChartAt I α).symm
                      ((toEuclidean (E := E)).symm y))‖ ^ 2)
            ∂(volume : Measure EuclN) := by
    refine lintegral_congr_ae ?_
    refine Filter.Eventually.of_forall ?_
    intro y
    exact ENNReal.ofReal_mul (sq_nonneg _)
  rw [h_LHS_eq]
  refine le_trans (hK_up_le T) ?_
  have h_sum_le := sum_wkpNorm_sq_α_le_wtwokTwoNorm_sq
    (I := I) (M := M) g r s α T
  exact mul_le_mul_of_nonneg_left h_sum_le (zero_le _)

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
