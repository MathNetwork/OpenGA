import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.Regularity.ChartLocalPicardRegular
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.DiffeomorphismFamily.ManifoldFlowFamily

namespace DifferentialGeometry.PDE.RicciFlow.ODE

open Bundle
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

theorem manifoldFlowFamily_of_regular
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (hReg : ChartCoordPicardRegular X)
    (hRegNeg : ChartCoordPicardRegular (fun t x => -(X t x)))
    (hSmoothX_chart : ∀ α : M, ContDiff ℝ ∞ (Function.uncurry fun t y =>
      (X t ((chartAt H α).symm (I.symm y)) : E)))
    (hSmoothNegX_chart : ∀ α : M, ContDiff ℝ ∞ (Function.uncurry fun t y =>
      ((-X t ((chartAt H α).symm (I.symm y))) : E)))
    (hLocalFwd : ∀ (Φ : ℝ → M → M) (T : ℝ), 0 < T →
      (∀ x : M, ∃ α : M, x ∈ (chartLocalPicardData_of_regular X hReg α).U ∧
        ∀ s : ℝ, Φ s x = (chartAt H α).symm
          (I.symm ((chartLocalPicardData_of_regular X hReg α).flow
            (I ((chartAt H α) x)) s))) →
      ∀ x : M, ∃ (ρ : ℝ) (_ : 0 < ρ) (flow : E → ℝ → E),
        ContDiffOn ℝ ∞ (Function.uncurry flow)
          (Metric.ball (I ((chartAt H x) x)) ρ ×ˢ Set.Ioo 0 T) ∧
        (∀ s ∈ Set.Ioo (0 : ℝ) T, ∀ y ∈ (chartAt H x).source,
          I ((chartAt H x) y) ∈ Metric.ball (I ((chartAt H x) x)) ρ →
          Φ s y = (chartAt H x).symm (I.symm (flow (I ((chartAt H x) y)) s))) ∧
        (∀ t ∈ Set.Ioo (0 : ℝ) T,
          I.symm (flow (I ((chartAt H x) x)) t) ∈ (chartAt H x).target))
    (hLocalRev : ∀ (Ψ : ℝ → M → M) (T : ℝ), 0 < T →
      (∀ x : M, ∃ α : M, x ∈ (chartLocalPicardData_of_regular
          (fun t x => -(X t x)) hRegNeg α).U ∧
        ∀ s : ℝ, Ψ s x = (chartAt H α).symm
          (I.symm ((chartLocalPicardData_of_regular
            (fun t x => -(X t x)) hRegNeg α).flow (I ((chartAt H α) x)) s))) →
      ∀ x : M, ∃ (ρ : ℝ) (_ : 0 < ρ) (flow : E → ℝ → E),
        ContDiffOn ℝ ∞ (Function.uncurry flow)
          (Metric.ball (I ((chartAt H x) x)) ρ ×ˢ Set.Ioo 0 T) ∧
        (∀ s ∈ Set.Ioo (0 : ℝ) T, ∀ y ∈ (chartAt H x).source,
          I ((chartAt H x) y) ∈ Metric.ball (I ((chartAt H x) x)) ρ →
          Ψ s y = (chartAt H x).symm (I.symm (flow (I ((chartAt H x) y)) s))) ∧
        (∀ t ∈ Set.Ioo (0 : ℝ) T,
          I.symm (flow (I ((chartAt H x) x)) t) ∈ (chartAt H x).target))
    (hBijPerChart : ∀ (Φ Ψ : ℝ → M → M),
      (∀ x, Φ 0 x = x) → (∀ x, Ψ 0 x = x) →
      (∀ x : M, ∃ α : M, ∀ s : ℝ,
        Φ s x = (chartAt H α).symm
          (I.symm ((chartLocalPicardData_of_regular X hReg α).flow
            (I ((chartAt H α) x)) s))) →
      (∀ x : M, ∃ α : M, ∀ s : ℝ,
        Ψ s x = (chartAt H α).symm
          (I.symm ((chartLocalPicardData_of_regular
            (fun t x => -(X t x)) hRegNeg α).flow (I ((chartAt H α) x)) s))) →
      ∀ α : M,
        ∃ S_α : ℝ, 0 < S_α ∧
          ∀ x ∈ (chartLocalPicardData_of_regular X hReg α).U ∩
              (chartLocalPicardData_of_regular (fun t x => -(X t x)) hRegNeg α).U,
            ∀ s ∈ Set.Ico (0 : ℝ) S_α,
              Ψ s (Φ s x) = x ∧ Φ s (Ψ s x) = x) :
    ∃ (T : ℝ) (_ : 0 < T) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M)) (Φ : ℝ → M → M),
        Φ_fam 0 = Diffeomorph.refl I M ∞ ∧
        (∀ x : M, Φ 0 x = x) ∧
        (∀ t : ℝ, 0 < t → t < T → ∀ x : M, Φ_fam t x = Φ t x) :=
  manifoldFlowFamily_exists X
    (fun α => chartLocalPicardData_of_regular X hReg α)
    (fun α => chartLocalPicardData_of_regular (fun t x => -(X t x)) hRegNeg α)
    hSmoothX_chart hSmoothNegX_chart hLocalFwd hLocalRev hBijPerChart

end DifferentialGeometry.PDE.RicciFlow.ODE
