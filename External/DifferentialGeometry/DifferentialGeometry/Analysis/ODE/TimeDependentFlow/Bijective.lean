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

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem time_dependent_vf_flow_bijective_and_inverse_smooth
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (hper : ∀ α : M, ChartLocalPicardData X α)
    (hperNeg : ∀ α : M, ChartLocalPicardData (fun t x => -(X t x)) α) :
    ∃ T : ℝ, 0 < T ∧
      ∃ Φ Ψ : ℝ → M → M,
        (∀ x : M, Φ 0 x = x) ∧
        (∀ x : M, Ψ 0 x = x) ∧
        (∀ x : M, ∃ α : M, ∀ s : ℝ,
          Φ s x = (chartAt H α).symm
            (I.symm ((hper α).flow (I ((chartAt H α) x)) s))) ∧
        (∀ x : M, ∃ α : M, ∀ s : ℝ,
          Ψ s x = (chartAt H α).symm
            (I.symm ((hperNeg α).flow (I ((chartAt H α) x)) s))) := by
  obtain ⟨T_fwd, hT_fwd_pos, S_fwd, _hCover_fwd, Φ, hΦ_init, hΦ_repr⟩ :=
    time_dependent_vf_global_flow_glue X hper
  obtain ⟨T_rev, hT_rev_pos, S_rev, _hCover_rev, Ψ, hΨ_init, hΨ_repr⟩ :=
    time_dependent_vf_global_flow_glue (fun t x => -(X t x)) hperNeg
  refine ⟨min T_fwd T_rev, lt_min hT_fwd_pos hT_rev_pos, Φ, Ψ,
    hΦ_init, hΨ_init, ?_, ?_⟩
  · intro x
    obtain ⟨α, _hαS, _hxU, hrepr⟩ := hΦ_repr x
    exact ⟨α, hrepr⟩
  · intro x
    obtain ⟨α, _hαS, _hxU, hrepr⟩ := hΨ_repr x
    exact ⟨α, hrepr⟩

end DifferentialGeometry.PDE.RicciFlow.ODE
