import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.EigenvalueTailSummableFromCounting








































noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral
namespace MetricRealization

open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
















def EigenvalueCountingBound (g : SmoothRiemannianMetric I M) (r s : ℕ) : Prop :=
  ∃ (q : ℕ) (A : ℝ), 0 ≤ A ∧
    ∃ count : ℝ → Finset (TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s),
      (∀ (Λ : ℝ) (i : TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s),
        1 + TensorEigenIdx.lambda (I := I) (M := M) i < Λ → i ∈ count Λ) ∧
      (∀ Λ : ℝ, ((count Λ).card : ℝ) ≤ A * Λ ^ q)












omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem eigenvalueTailSummable_of_countingBound
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h : EigenvalueCountingBound (I := I) (M := M) g r s) :
    EigenvalueTailSummable (I := I) (M := M) g r s := by
  obtain ⟨q, A, hA, count, hcount_mem, hcount_card⟩ := h
  refine eigenvalueTailSummable_of_polynomial_counting_bound (I := I) (M := M) g r s q A hA
    (fun n => count ((2 : ℝ) ^ (n + 1))) ?_ ?_
  · intro n i hi
    exact hcount_mem ((2 : ℝ) ^ (n + 1)) i hi
  · intro n
    refine (hcount_card ((2 : ℝ) ^ (n + 1))).trans (le_of_eq ?_)
    congr 1
    rw [← pow_mul]







theorem spectralChartRegularity_of_countingBound
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h : EigenvalueCountingBound (I := I) (M := M) g r s) :
    SpectralChartRegularity (I := I) (M := M) g r s :=
  spectralChartRegularity_of_eigenvalueTailSummable (I := I) (M := M) g r s
    (eigenvalueTailSummable_of_countingBound (I := I) (M := M) g r s h)














theorem spectralSmoothRealizesAsSmooth_of_countingBound
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h : EigenvalueCountingBound (I := I) (M := M) g r s) :
    SpectralSmoothRealizesAsSmooth (I := I) (M := M) g r s :=
  spectralSmoothRealizesAsSmooth_of_eigenvalueTailSummable (I := I) (M := M) g r s
    (eigenvalueTailSummable_of_countingBound (I := I) (M := M) g r s h)

end MetricRealization
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
