import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifference
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqSmoothCcUniformBound
import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.PreHilbert

noncomputable section

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem exists_ricciArmPrincipalCoeffPure_self_fibre_jetL2_bound
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) :
    ∃ Λ Γ : ℝ, 0 ≤ Λ ∧ 0 ≤ Γ ∧
      (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
          ((ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₀).toSection x) ≤ Λ ^ 2) ∧
      (∑ i ∈ Finset.range (a + 1),
          ‖iteratedCovGrad (I := I) g₀ 4 2 i
            (ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₀)‖ ^ 2) ≤ Γ ^ 2 := by
  obtain ⟨K, hK_nn, hK⟩ := exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M)
    g₀ 4 2 (ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₀)
  refine ⟨Real.sqrt K, Real.sqrt (∑ i ∈ Finset.range (a + 1),
      ‖iteratedCovGrad (I := I) g₀ 4 2 i
        (ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₀)‖ ^ 2),
    Real.sqrt_nonneg _, Real.sqrt_nonneg _, ?_, ?_⟩
  · intro x
    rw [Real.sq_sqrt hK_nn]
    exact hK x
  · rw [Real.sq_sqrt (by positivity)]

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
