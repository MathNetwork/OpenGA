import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.NablaRiemannHeat

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false










































noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open scoped BigOperators








section PointwiseAlgebra

variable {Idx : Type*} [Fintype Idx]




def compPairMulti {r : ℕ} (A B : (Fin r → Idx) → Real) : Real :=
  ∑ m : Fin r → Idx, A m * B m

theorem compPairMulti_self {r : ℕ} (A : (Fin r → Idx) → Real) :
    compPairMulti A A = compNormSqMulti A := by
  unfold compPairMulti compNormSqMulti
  refine Finset.sum_congr rfl fun m _ => ?_
  ring

theorem compPairMulti_comm {r : ℕ} (A B : (Fin r → Idx) → Real) :
    compPairMulti A B = compPairMulti B A := by
  unfold compPairMulti
  refine Finset.sum_congr rfl fun m _ => ?_
  ring

end PointwiseAlgebra










section Producer

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]





def MultiLevelTimeDerivOn {r : ℕ}
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (level : Real -> M -> (Fin r → Idx) → Real)
    (levelDt : Real -> M -> (Fin r → Idx) → Real) : Prop :=
  ∀ (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M)
    (m : Fin r → Idx),
    HasDerivWithinAt
      (fun s : Real => level s x m)
      (levelDt (t : Real) x m)
      D.carrier
      (t : Real)


def MultiNormSqDef {r : ℕ}
    (level : Real -> M -> (Fin r → Idx) → Real)
    (normSq : Real -> M -> Real) : Prop :=
  ∀ (t : Real) (x : M), normSq t x = compNormSqMulti (level t x)







def MultiNormLaplacianSplit {r : ℕ}
    (level : Real -> M -> (Fin r → Idx) → Real)
    (levelLap : Real -> M -> (Fin r → Idx) → Real)
    (nextLevel : Real -> M -> (Fin (r + 1) → Idx) → Real)
    (normLap nextNormSq : Real -> M -> Real) : Prop :=
  (∀ (t : Real) (x : M),
      normLap t x =
        2 * compPairMulti (levelLap t x) (level t x) +
          2 * nextNormSq t x) ∧
    (∀ (t : Real) (x : M),
      nextNormSq t x = compNormSqMulti (nextLevel t x))





def multiReactionDown {r : ℕ}
    (level levelDt levelLap : Real -> M -> (Fin r → Idx) → Real)
    (t : Real) (x : M) : Real :=
  2 * compPairMulti (fun m => levelDt t x m - levelLap t x m) (level t x)





omit [TopologicalSpace M] [SigmaCompactSpace M] [T2Space M] [DecidableEq Idx] in
theorem hasDerivWithinAt_compNormSqMulti {r : ℕ}
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (level levelDt : Real -> M -> (Fin r → Idx) → Real)
    (h_dt : MultiLevelTimeDerivOn (D := D) level levelDt)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M) :
    HasDerivWithinAt
      (fun s : Real => compNormSqMulti (level s x))
      (2 * compPairMulti (levelDt (t : Real) x) (level (t : Real) x))
      D.carrier
      (t : Real) := by
  classical
  have hsum :
      HasDerivWithinAt
        (fun s : Real => ∑ m : Fin r → Idx, (level s x m) ^ 2)
        (∑ m : Fin r → Idx,
          2 * level (t : Real) x m * levelDt (t : Real) x m)
        D.carrier
        (t : Real) := by
    refine HasDerivWithinAt.fun_sum ?_
    intro m _hm
    have hm := h_dt t x m

    have hmul := hm.mul hm
    have hgoal :
        HasDerivWithinAt (fun s : Real => level s x m * level s x m)
          (2 * level (t : Real) x m * levelDt (t : Real) x m) D.carrier (t : Real) := by
      refine hmul.congr_deriv ?_
      ring
    simpa [pow_two] using hgoal

  have hval :
      (∑ m : Fin r → Idx,
          2 * level (t : Real) x m * levelDt (t : Real) x m) =
        2 * compPairMulti (levelDt (t : Real) x) (level (t : Real) x) := by
    unfold compPairMulti
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  rw [hval] at hsum
  simpa [compNormSqMulti] using hsum















omit [TopologicalSpace M] [SigmaCompactSpace M] [T2Space M] [DecidableEq Idx] in
theorem multiNormHeatEquationOn_of_components {r : ℕ}
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (level levelDt levelLap : Real -> M -> (Fin r → Idx) → Real)
    (nextLevel : Real -> M -> (Fin (r + 1) → Idx) → Real)
    (normSq normLap nextNormSq : Real -> M -> Real)
    (h_dt : MultiLevelTimeDerivOn (D := D) level levelDt)
    (h_normSq : MultiNormSqDef (M := M) level normSq)
    (h_lap : MultiNormLaplacianSplit (M := M) level levelLap nextLevel
      normLap nextNormSq) :
    ∀ (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
      HasDerivWithinAt
        (fun s : Real => normSq s x)
        (normLap (t : Real) x +
          (-2 * nextNormSq (t : Real) x +
            multiReactionDown level levelDt levelLap (t : Real) x))
        D.carrier
        (t : Real) := by
  classical
  obtain ⟨h_lap_eq, _h_next⟩ := h_lap
  intro t x

  have hderiv :
      HasDerivWithinAt
        (fun s : Real => compNormSqMulti (level s x))
        (2 * compPairMulti (levelDt (t : Real) x) (level (t : Real) x))
        D.carrier
        (t : Real) :=
    hasDerivWithinAt_compNormSqMulti (D := D) level levelDt h_dt t x

  have hfun :
      HasDerivWithinAt
        (fun s : Real => normSq s x)
        (2 * compPairMulti (levelDt (t : Real) x) (level (t : Real) x))
        D.carrier
        (t : Real) := by
    refine hderiv.congr ?_ ?_
    · intro s _hs; exact h_normSq s x
    · exact h_normSq (t : Real) x


  have hval :
      normLap (t : Real) x +
          (-2 * nextNormSq (t : Real) x +
            multiReactionDown level levelDt levelLap (t : Real) x) =
        2 * compPairMulti (levelDt (t : Real) x) (level (t : Real) x) := by
    rw [h_lap_eq (t : Real) x]


    set N : Real := nextNormSq (t : Real) x with hNdef
    have hpair :
        compPairMulti (levelLap (t : Real) x) (level (t : Real) x) +
            compPairMulti
              (fun m => levelDt (t : Real) x m - levelLap (t : Real) x m)
              (level (t : Real) x) =
          compPairMulti (levelDt (t : Real) x) (level (t : Real) x) := by
      unfold compPairMulti
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun m _ => ?_
      ring
    unfold multiReactionDown

    have : 2 * compPairMulti (levelLap (t : Real) x) (level (t : Real) x) + 2 * N +
          (-2 * N +
            2 * compPairMulti
              (fun m => levelDt (t : Real) x m - levelLap (t : Real) x m)
              (level (t : Real) x)) =
        2 * (compPairMulti (levelLap (t : Real) x) (level (t : Real) x) +
          compPairMulti
            (fun m => levelDt (t : Real) x m - levelLap (t : Real) x m)
            (level (t : Real) x)) := by ring
    rw [this, hpair]
  rw [hval]
  exact hfun









































omit [TopologicalSpace M] [SigmaCompactSpace M] [T2Space M] [DecidableEq Idx] in
theorem multiReactionDown_eq_of_residual {r : ℕ}
    (level levelDt levelLap star : Real -> M -> (Fin r → Idx) → Real)
    (t : Real) (x : M)
    (hres : ∀ m : Fin r → Idx,
      levelDt t x m - levelLap t x m = star t x m) :
    multiReactionDown level levelDt levelLap t x =
      2 * compPairMulti (star t x) (level t x) := by
  unfold multiReactionDown compPairMulti
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only []
  rw [hres m]

end Producer

end DifferentialGeometry.PDE.RicciFlow
