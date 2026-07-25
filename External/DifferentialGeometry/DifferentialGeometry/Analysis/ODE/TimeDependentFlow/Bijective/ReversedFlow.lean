import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothInSpace
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary






namespace DifferentialGeometry.PDE.RicciFlow.ODE

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem time_reversed_flow_exists
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (h : ∃ T : ℝ, 0 < T ∧
      ∃ Φ Ψ : ℝ → M → M,
        (∀ x : M, Φ 0 x = x) ∧
        (∀ x : M, Ψ 0 x = x) ∧
        (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M,
          HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => (Φ s) x) (Set.Ici 0) t
            ((ContinuousLinearMap.id ℝ ℝ).smulRight (X t (Φ t x)))) ∧
        (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M,
          HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => (Ψ s) x) (Set.Ici 0) t
            ((ContinuousLinearMap.id ℝ ℝ).smulRight (-(X t (Ψ t x)))))) :
    ∃ T : ℝ, 0 < T ∧
      ∃ Φ Ψ : ℝ → M → M,
        (∀ x : M, Φ 0 x = x) ∧
        (∀ x : M, Ψ 0 x = x) ∧
        (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M,
          HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => (Φ s) x) (Set.Ici 0) t
            ((ContinuousLinearMap.id ℝ ℝ).smulRight (X t (Φ t x)))) ∧
        (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M,
          HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => (Ψ s) x) (Set.Ici 0) t
            ((ContinuousLinearMap.id ℝ ℝ).smulRight (-(X t (Ψ t x))))) := h

end DifferentialGeometry.PDE.RicciFlow.ODE
