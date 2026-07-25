import DifferentialGeometry.Analysis.Sobolev.Tensor.ChartComponents
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Tensor

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

noncomputable def tensorPouSobolevNorm
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (k : ℕ) (T : SmoothCcTensor g r s) : ℝ≥0∞ :=
  (∑' α : M,
    ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)),
      ∑ j ∈ Finset.range (2 * k + 1),
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal
            (((chartAtlasPOU I M α : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
              ‖iteratedFDeriv ℝ j
                  (tensorChartComponentRaw (I := I) (M := M) g r s T α IJ.1 IJ.2
                    ∘ (extChartAt I α).symm)
                  ((toEuclidean (E := E)).symm y)‖ ^ 2)
          ∂(volume :
            Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))) ^ (1 / 2 : ℝ)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem tensorPouSobolevNorm_eq
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (k : ℕ) (T : SmoothCcTensor g r s) :
    tensorPouSobolevNorm (I := I) (M := M) g k T =
      (∑' α : M,
        ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
          ∑ j ∈ Finset.range (2 * k + 1),
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                  ‖iteratedFDeriv ℝ j
                      (tensorChartComponentRaw (I := I) (M := M) g r s T α
                          IJ.1 IJ.2
                        ∘ (extChartAt I α).symm)
                      ((toEuclidean (E := E)).symm y)‖ ^ 2)
              ∂(volume :
                Measure (EuclideanSpace ℝ
                  (Fin (Module.finrank ℝ E))))) ^ (1 / 2 : ℝ) := rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem tensorPouSobolevNorm_nonneg
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (k : ℕ) (T : SmoothCcTensor g r s) :
    0 ≤ tensorPouSobolevNorm (I := I) (M := M) g k T :=
  zero_le _

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma tensorChartComponentRaw_zero_section
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tensorChartComponentRaw (I := I) (M := M) g r s
        (0 : SmoothCcTensor g r s) α Idx Jdx = (fun _ : M => 0) := by
  classical
  funext x
  have h := tensorChartComponent_smul (I := I) (M := M) g r s (0 : ℝ)
    (0 : SmoothCcTensor g r s) α Idx Jdx
  unfold tensorChartComponentRaw
  have h0 : (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ x
          ((0 : SmoothCcTensor g r s).toSection x) = 0 := by
    have hsec : (0 : SmoothCcTensor g r s).toSection x = 0 := by rfl
    rw [hsec]
    exact map_zero _
  change tensorChartComponentProjection (E := E) r s Idx Jdx
      (tensorTrivProj (I := I) (M := M) g r s
        (0 : SmoothCcTensor g r s) α x) = 0
  unfold tensorTrivProj
  rw [h0]
  exact map_zero _

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma tensorChartComponentRaw_comp_zero_section
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    (tensorChartComponentRaw (I := I) (M := M) g r s
        (0 : SmoothCcTensor g r s) α Idx Jdx ∘ (extChartAt I α).symm) =
      (fun _ : E => (0 : ℝ)) := by
  funext x
  change tensorChartComponentRaw (I := I) (M := M) g r s
      (0 : SmoothCcTensor g r s) α Idx Jdx ((extChartAt I α).symm x) = 0
  rw [tensorChartComponentRaw_zero_section (I := I) (M := M) g r s α Idx Jdx]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem tensorPouSobolevNorm_zero_section
    (g : SmoothRiemannianMetric I M) {r s : ℕ} (k : ℕ) :
    tensorPouSobolevNorm (I := I) (M := M) g k
        (0 : SmoothCcTensor g r s) = 0 := by
  classical
  rw [tensorPouSobolevNorm_eq]
  have htsum :
      (∑' α : M,
        ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
          ∑ j ∈ Finset.range (2 * k + 1),
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                  ‖iteratedFDeriv ℝ j
                      (tensorChartComponentRaw (I := I) (M := M) g r s
                          (0 : SmoothCcTensor g r s) α IJ.1 IJ.2
                        ∘ (extChartAt I α).symm)
                      ((toEuclidean (E := E)).symm y)‖ ^ 2)
              ∂(volume :
                Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))) =
        0 := by
    have hpt : ∀ α : M,
        (∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
          ∑ j ∈ Finset.range (2 * k + 1),
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                  ‖iteratedFDeriv ℝ j
                      (tensorChartComponentRaw (I := I) (M := M) g r s
                          (0 : SmoothCcTensor g r s) α IJ.1 IJ.2
                        ∘ (extChartAt I α).symm)
                      ((toEuclidean (E := E)).symm y)‖ ^ 2)
              ∂(volume :
                Measure (EuclideanSpace ℝ
                  (Fin (Module.finrank ℝ E))))) = 0 := by
      intro α
      refine Finset.sum_eq_zero ?_
      intro IJ _
      refine Finset.sum_eq_zero ?_
      intro j _
      have hraw := tensorChartComponentRaw_comp_zero_section
        (I := I) (M := M) g r s α IJ.1 IJ.2
      have hiter : iteratedFDeriv ℝ j
          (tensorChartComponentRaw (I := I) (M := M) g r s
              (0 : SmoothCcTensor g r s) α IJ.1 IJ.2
            ∘ (extChartAt I α).symm) = 0 := by
        rw [hraw]
        exact iteratedFDeriv_fun_zero
      have hintegrand_zero :
          (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
            ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                ‖iteratedFDeriv ℝ j
                    (tensorChartComponentRaw (I := I) (M := M) g r s
                        (0 : SmoothCcTensor g r s) α IJ.1 IJ.2
                      ∘ (extChartAt I α).symm)
                    ((toEuclidean (E := E)).symm y)‖ ^ 2)) =
            (fun _ => 0) := by
        funext y
        rw [hiter]
        simp
      rw [hintegrand_zero]
      simp
    rw [tsum_congr hpt]
    exact tsum_zero
  rw [htsum]
  exact ENNReal.zero_rpow_of_pos (by norm_num)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem tensorPouSobolevNorm_le_succ
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (k : ℕ) (T : SmoothCcTensor g r s) :
    tensorPouSobolevNorm (I := I) (M := M) g k T ≤
      tensorPouSobolevNorm (I := I) (M := M) g (k + 1) T := by
  classical
  rw [tensorPouSobolevNorm_eq, tensorPouSobolevNorm_eq]
  have hrange : Finset.range (2 * k + 1) ⊆ Finset.range (2 * (k + 1) + 1) :=
    Finset.range_subset_range.mpr (by omega)
  have hper_chart : ∀ α : M,
      (∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
          (Fin s → Fin (Module.finrank ℝ E)),
        ∑ j ∈ Finset.range (2 * k + 1),
          ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                ‖iteratedFDeriv ℝ j
                    (tensorChartComponentRaw (I := I) (M := M) g r s T α
                        IJ.1 IJ.2
                      ∘ (extChartAt I α).symm)
                    ((toEuclidean (E := E)).symm y)‖ ^ 2)
            ∂(volume :
              Measure (EuclideanSpace ℝ
                (Fin (Module.finrank ℝ E))))) ≤
      (∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
          (Fin s → Fin (Module.finrank ℝ E)),
        ∑ j ∈ Finset.range (2 * (k + 1) + 1),
          ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                ‖iteratedFDeriv ℝ j
                    (tensorChartComponentRaw (I := I) (M := M) g r s T α
                        IJ.1 IJ.2
                      ∘ (extChartAt I α).symm)
                    ((toEuclidean (E := E)).symm y)‖ ^ 2)
            ∂(volume :
              Measure (EuclideanSpace ℝ
                (Fin (Module.finrank ℝ E))))) := by
    intro α
    refine Finset.sum_le_sum ?_
    intro IJ _
    exact Finset.sum_le_sum_of_subset_of_nonneg hrange
      (by intro j _ _; exact zero_le _)
  have htsum_le :
      (∑' α : M,
        ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
          ∑ j ∈ Finset.range (2 * k + 1),
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                  ‖iteratedFDeriv ℝ j
                      (tensorChartComponentRaw (I := I) (M := M) g r s T α
                          IJ.1 IJ.2
                        ∘ (extChartAt I α).symm)
                      ((toEuclidean (E := E)).symm y)‖ ^ 2)
              ∂(volume :
                Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))) ≤
        (∑' α : M,
          ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
              (Fin s → Fin (Module.finrank ℝ E)),
            ∑ j ∈ Finset.range (2 * (k + 1) + 1),
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                ENNReal.ofReal
                  (((chartAtlasPOU I M α : M → ℝ)
                      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                    ‖iteratedFDeriv ℝ j
                        (tensorChartComponentRaw (I := I) (M := M) g r s T α
                            IJ.1 IJ.2
                          ∘ (extChartAt I α).symm)
                        ((toEuclidean (E := E)).symm y)‖ ^ 2)
                ∂(volume :
                  Measure (EuclideanSpace ℝ
                    (Fin (Module.finrank ℝ E))))) := by
    exact ENNReal.tsum_le_tsum hper_chart
  exact ENNReal.rpow_le_rpow htsum_le (by norm_num)

end Tensor
end Sobolev
end Analysis
end DifferentialGeometry
