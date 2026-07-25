import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.NablaRiemannHeat
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.MultiNormHeat

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false











































































noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open scoped BigOperators








section ScalarProducer

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]










omit [TopologicalSpace M] in
theorem nablaRm04NormHeatBoundSharp_scalar
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (u uLap nabla2 reaction v : Real -> M -> Real) (cReact : Real)
    (h_heat : NablaRm04NormHeatEquationOn (D := D) u uLap nabla2 reaction)
    (hreact_bound : ∀ (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
      (x : M), reaction (t : Real) x ≤ cReact * Real.sqrt (v (t : Real) x) * u (t : Real) x) :
    ∀ (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
      ∃ d : Real,
        HasDerivWithinAt (fun s : Real => u s x) d D.carrier (t : Real) ∧
        d ≤ uLap (t : Real) x +
          (-2 * nabla2 (t : Real) x +
            cReact * Real.sqrt (v (t : Real) x) * u (t : Real) x) := by
  intro t x
  refine ⟨_, h_heat t x, ?_⟩
  have hr := hreact_bound t x
  linarith [hr]

















omit [TopologicalSpace M] in
theorem nablaRm04NormHeatBoundOn_scalar
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (u uLap nabla2 reaction v : Real -> M -> Real) (cReact : Real)
    (h_heat : NablaRm04NormHeatEquationOn (D := D) u uLap nabla2 reaction)
    (hnabla2_nonneg : ∀ (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
      (x : M), 0 ≤ nabla2 (t : Real) x)
    (hreact_bound : ∀ (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
      (x : M), reaction (t : Real) x ≤ cReact * Real.sqrt (v (t : Real) x) * u (t : Real) x) :
    NablaRm04NormHeatBoundOn (D := D) u uLap v cReact := by
  intro t x
  obtain ⟨d, hderiv, hle⟩ :=
    nablaRm04NormHeatBoundSharp_scalar (D := D) u uLap nabla2 reaction v cReact
      h_heat hreact_bound t x
  refine ⟨d, hderiv, ?_⟩
  have hdrop : 0 ≤ 2 * nabla2 (t : Real) x := by
    have := hnabla2_nonneg t x; linarith
  linarith [hle, hdrop]

end ScalarProducer















section BochnerBridge

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]


















omit [TopologicalSpace M] [SigmaCompactSpace M] [T2Space M] [DecidableEq Idx] in
theorem nablaRm04NormHeatEquationOn_of_multiBochner
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (level levelDt levelLap : Real -> M -> (Fin 5 → Idx) → Real)
    (nextLevel : Real -> M -> (Fin (5 + 1) → Idx) → Real)
    (normSq normLap nextNormSq : Real -> M -> Real)
    (h_dt : MultiLevelTimeDerivOn (D := D) level levelDt)
    (h_normSq : MultiNormSqDef (M := M) level normSq)
    (h_lap : MultiNormLaplacianSplit (M := M) level levelLap nextLevel
      normLap nextNormSq) :
    NablaRm04NormHeatEquationOn (D := D) normSq normLap nextNormSq
      (multiReactionDown level levelDt levelLap) := by
  intro t x
  exact multiNormHeatEquationOn_of_components (D := D) level levelDt levelLap
    nextLevel normSq normLap nextNormSq h_dt h_normSq h_lap t x



















omit [TopologicalSpace M] [SigmaCompactSpace M] [T2Space M] [DecidableEq Idx] in
theorem nablaRm04NormHeatBoundOn_of_multiBochner_residual
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (level levelDt levelLap : Real -> M -> (Fin 5 → Idx) → Real)
    (nextLevel : Real -> M -> (Fin (5 + 1) → Idx) → Real)
    (star : Real -> M -> (Fin 5 → Idx) → Real)
    (normSq normLap nextNormSq v : Real -> M -> Real) (cReact : Real)
    (h_dt : MultiLevelTimeDerivOn (D := D) level levelDt)
    (h_normSq : MultiNormSqDef (M := M) level normSq)
    (h_lap : MultiNormLaplacianSplit (M := M) level levelLap nextLevel
      normLap nextNormSq)
    (hres : ∀ (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M)
      (m : Fin 5 → Idx),
      levelDt (t : Real) x m - levelLap (t : Real) x m = star (t : Real) x m)
    (hnext_nonneg : ∀ (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
      (x : M), 0 ≤ nextNormSq (t : Real) x)
    (hstar_bound : ∀ (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
      (x : M),
      2 * compPairMulti (star (t : Real) x) (level (t : Real) x) ≤
        cReact * Real.sqrt (v (t : Real) x) * normSq (t : Real) x) :
    NablaRm04NormHeatBoundOn (D := D) normSq normLap v cReact := by

  have h_heat :
      NablaRm04NormHeatEquationOn (D := D) normSq normLap nextNormSq
        (multiReactionDown level levelDt levelLap) :=
    nablaRm04NormHeatEquationOn_of_multiBochner (D := D) level levelDt levelLap
      nextLevel normSq normLap nextNormSq h_dt h_normSq h_lap

  refine nablaRm04NormHeatBoundOn_scalar (D := D) normSq normLap nextNormSq
    (multiReactionDown level levelDt levelLap) v cReact h_heat hnext_nonneg ?_
  intro t x
  rw [multiReactionDown_eq_of_residual level levelDt levelLap star (t : Real) x
    (hres t x)]
  exact hstar_bound t x

end BochnerBridge











































end DifferentialGeometry.PDE.RicciFlow
