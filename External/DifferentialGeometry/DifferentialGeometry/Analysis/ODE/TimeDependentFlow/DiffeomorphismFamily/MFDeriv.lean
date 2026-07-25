import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothInSpace
import Mathlib.Geometry.Manifold.MFDeriv.Basic
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
theorem time_dependent_vf_flow_hasMFDerivAt_packaging
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (h : ∃ T : ℝ, 0 < T ∧
      ∃ Φ : ℝ → M → M, ∀ t : ℝ, t < T → ∀ x : M,
        HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s : ℝ => Φ s x) t
          ((ContinuousLinearMap.id ℝ ℝ).smulRight (X t x))) :
    ∃ T : ℝ, 0 < T ∧
      ∃ Φ : ℝ → M → M, ∀ t : ℝ, t < T → ∀ x : M,
        HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s : ℝ => Φ s x) t
          ((ContinuousLinearMap.id ℝ ℝ).smulRight (X t x)) := h

end DifferentialGeometry.PDE.RicciFlow.ODE
