import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.HilbertSpace
import DifferentialGeometry.Analysis.Sobolev.Tensor.PouWeightedHsNorm

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace HebeyBlock

open Bundle Manifold MeasureTheory Set
open scoped Manifold ContDiff ENNReal BigOperators

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.Tensor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] in
theorem chart_frame_component_norm_bound
    (g : SmoothRiemannianMetric I M) (r s k : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ T : SmoothCcTensor g r s,
        ((∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
              (Fin s → Fin (Module.finrank ℝ E)),
            ∑ j ∈ Finset.range (2 * k + 1),
              ∑ basisIdx : Fin j → Fin (Module.finrank ℝ E),
                ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                  ENNReal.ofReal
                    (((chartAtlasPOU I M α : M → ℝ)
                        ((extChartAt I α).symm
                          ((toEuclidean (E := E)).symm y))) *
                      |(iteratedFDeriv ℝ j
                            (tensorChartComponentRaw (I := I) (M := M)
                                g r s T α IJ.1 IJ.2
                              ∘ (extChartAt I α).symm
                              ∘ (toEuclidean (E := E)).symm)
                            y)
                          (fun i => EuclideanSpace.basisFun
                            (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2)
                  ∂(volume :
                    Measure (EuclideanSpace ℝ
                      (Fin (Module.finrank ℝ E)))))).toReal ≤
          C * (tensorPouSobolevHsNorm (I := I) (M := M) g k T).toReal ^ 2 := by
  classical
  refine ⟨1, le_of_lt one_pos, ?_⟩
  intro T
  set Fα : ℝ≥0∞ :=
    ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)),
      ∑ j ∈ Finset.range (2 * k + 1),
        ∑ basisIdx : Fin j → Fin (Module.finrank ℝ E),
          ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                |(iteratedFDeriv ℝ j
                      (tensorChartComponentRaw (I := I) (M := M)
                          g r s T α IJ.1 IJ.2
                        ∘ (extChartAt I α).symm
                        ∘ (toEuclidean (E := E)).symm)
                      y)
                    (fun i => EuclideanSpace.basisFun
                      (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2)
            ∂(volume :
              Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))
    with hFα_def
  have htsum_eq :
      (∑' β : M,
        ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
          ∑ j ∈ Finset.range (2 * k + 1),
            ∑ basisIdx : Fin j → Fin (Module.finrank ℝ E),
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) β,
                ENNReal.ofReal
                  (((chartAtlasPOU I M β : M → ℝ)
                      ((extChartAt I β).symm ((toEuclidean (E := E)).symm y))) *
                    |(iteratedFDeriv ℝ j
                          (tensorChartComponentRaw (I := I) (M := M)
                              g r s T β IJ.1 IJ.2
                            ∘ (extChartAt I β).symm
                            ∘ (toEuclidean (E := E)).symm)
                          y)
                        (fun i => EuclideanSpace.basisFun
                          (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2)
                ∂(volume :
                  Measure (EuclideanSpace ℝ
                    (Fin (Module.finrank ℝ E))))) =
        tensorPouSobolevHsNormSq (I := I) (M := M) g k T :=
    (tensorPouSobolevHsNormSq_eq_inner_sum
      (I := I) (M := M) g k T).symm
  have hFα_le_tsum :
      Fα ≤ ∑' β : M,
        ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
          ∑ j ∈ Finset.range (2 * k + 1),
            ∑ basisIdx : Fin j → Fin (Module.finrank ℝ E),
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) β,
                ENNReal.ofReal
                  (((chartAtlasPOU I M β : M → ℝ)
                      ((extChartAt I β).symm ((toEuclidean (E := E)).symm y))) *
                    |(iteratedFDeriv ℝ j
                          (tensorChartComponentRaw (I := I) (M := M)
                              g r s T β IJ.1 IJ.2
                            ∘ (extChartAt I β).symm
                            ∘ (toEuclidean (E := E)).symm)
                          y)
                        (fun i => EuclideanSpace.basisFun
                          (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2)
                ∂(volume :
                  Measure (EuclideanSpace ℝ
                    (Fin (Module.finrank ℝ E)))) := by
    rw [hFα_def]
    exact ENNReal.le_tsum α
  have hFα_le_sq : Fα ≤ tensorPouSobolevHsNormSq (I := I) (M := M) g k T := by
    refine hFα_le_tsum.trans ?_
    rw [htsum_eq]
  have hNormSq_lt_top : tensorPouSobolevHsNormSq (I := I) (M := M) g k T < ⊤ :=
    tensorPouSobolevHsNormSq_lt_top (I := I) (M := M) g k T
  have hNormSq_ne_top : tensorPouSobolevHsNormSq (I := I) (M := M) g k T ≠ ⊤ :=
    hNormSq_lt_top.ne
  have htoReal_le : Fα.toReal ≤
      (tensorPouSobolevHsNormSq (I := I) (M := M) g k T).toReal :=
    ENNReal.toReal_mono hNormSq_ne_top hFα_le_sq
  have hSq_eq_pow : tensorPouSobolevHsNormSq (I := I) (M := M) g k T =
      tensorPouSobolevHsNorm (I := I) (M := M) g k T ^ 2 := rfl
  have hSq_toReal : (tensorPouSobolevHsNormSq (I := I) (M := M) g k T).toReal =
      (tensorPouSobolevHsNorm (I := I) (M := M) g k T).toReal ^ 2 := by
    rw [hSq_eq_pow, ENNReal.toReal_pow]
  rw [one_mul]
  calc Fα.toReal
      ≤ (tensorPouSobolevHsNormSq (I := I) (M := M) g k T).toReal := htoReal_le
    _ = (tensorPouSobolevHsNorm (I := I) (M := M) g k T).toReal ^ 2 := hSq_toReal

end HebeyBlock
end RicciFlow
end PDE
end DifferentialGeometry
