import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.ChartLocalExistence.ChartLocalPicard
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.ChartLocalExistence.UniformExistence

namespace DifferentialGeometry.PDE.RicciFlow.ODE

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

def ChartCoordPicardRegular (X : ℝ → ∀ x : M, TangentSpace I x) : Prop :=
  ContinuousOn (Function.uncurry (fun t x => X t x)) (Set.univ : Set (ℝ × M)) ∧
    ∀ α : M, ∃ L K r : ℝ, 0 < L ∧ 0 < r ∧ 0 ≤ K ∧
      ∀ t ∈ Set.Icc (0 : ℝ) L,
        LipschitzOnWith (Real.toNNReal K)
          (fun y : E => (X t ((chartAt H α).symm (I.symm y)) : E))
          (Metric.ball (I ((chartAt H α) α)) r)

noncomputable def chartLocalPicardData_of_regular
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (hReg : ChartCoordPicardRegular X) (α : M) :
    ChartLocalPicardData X α :=
  let h := time_dependent_vf_chart_local_picard_with_lipschitz X α
    hReg.1 (hReg.2 α)
  { T := h.choose
    T_pos := h.choose_spec.1
    r := h.choose_spec.2.choose
    r_pos := h.choose_spec.2.choose_spec.1
    flow := h.choose_spec.2.choose_spec.2.choose
    flow_spec := h.choose_spec.2.choose_spec.2.choose_spec }

end DifferentialGeometry.PDE.RicciFlow.ODE
