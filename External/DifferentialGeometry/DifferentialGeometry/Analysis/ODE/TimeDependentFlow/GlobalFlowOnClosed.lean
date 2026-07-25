import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.ChartLocalExistence.ChartLocalPicard
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.ChartLocalExistence.PointwiseLocal
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.ChartLocalExistence.UniformExistence
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.ChartLocalExistence.Glue
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothInSpace
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.Bijective

namespace DifferentialGeometry.PDE.RicciFlow.ODE

open Bundle
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem time_dependent_vf_globalflow_on_closed_mfd
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (hper : ∀ α : M, ChartLocalPicardData X α)
    (hper_neg : ∀ α : M, ChartLocalPicardData (fun t x => -(X t x)) α) :
    ∃ T : ℝ, 0 < T ∧
      ∃ Φ Ψ : ℝ → M → M,
        (∀ x : M, Φ 0 x = x) ∧
        (∀ x : M, Ψ 0 x = x) ∧
        (∀ x : M, ∃ α : M, ∀ s : ℝ,
          Φ s x = (chartAt H α).symm
            (I.symm ((hper α).flow (I ((chartAt H α) x)) s))) ∧
        (∀ x : M, ∃ α : M, ∀ s : ℝ,
          Ψ s x = (chartAt H α).symm
            (I.symm ((hper_neg α).flow (I ((chartAt H α) x)) s))) :=
  time_dependent_vf_flow_bijective_and_inverse_smooth X hper hper_neg

end DifferentialGeometry.PDE.RicciFlow.ODE
