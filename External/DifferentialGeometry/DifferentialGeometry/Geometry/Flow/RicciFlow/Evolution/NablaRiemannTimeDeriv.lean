import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.RmRealizationBridge

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false




























































noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open DifferentialGeometry
open scoped Manifold ContDiff BigOperators









section StepDeriv

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]









def covDerivStepDt {r : ℕ}
    (chrDt : Idx → Idx → Idx → Real)
    (A : (Fin r → Idx) → Real) : (Fin (r + 1) → Idx) → Real :=
  fun n =>
    ∑ s : Fin r, ∑ p : Idx,
      chrDt (n 0) (Fin.tail n s) p * A (Function.update (Fin.tail n) s p)


























omit [DecidableEq Idx] in
theorem covDerivStepComp_hasDerivWithinAt {r : ℕ}
    (frame : Idx → (x : M) → TangentSpace I x)
    (A Adt : Real → M → (Fin r → Idx) → Real)
    (chr chrDt : Real → M → Idx → Idx → Idx → Real)
    {D : Set Real} {t : Real} (x : M) (n : Fin (r + 1) → Idx)
    (hA : ∀ m : Fin r → Idx,
      HasDerivWithinAt (fun s : Real => A s x m) (Adt t x m) D t)
    (hchr : ∀ i a p : Idx,
      HasDerivWithinAt (fun s : Real => chr s x i a p) (chrDt t x i a p) D t)
    (hswap : ∀ m : Fin r → Idx,
      HasDerivWithinAt
        (fun s : Real =>
          extDerivFun (I := I) (fun y : M => A s y m) x (frame (n 0) x))
        (extDerivFun (I := I) (fun y : M => Adt t y m) x (frame (n 0) x))
        D t) :
    HasDerivWithinAt
      (fun s : Real =>
        covDerivStepComp
          (frameExtData (I := I) frame (fun y : M => A s y) x)
          (chr s x) (A s x) n)
      (covDerivStepComp
          (frameExtData (I := I) frame (fun y : M => Adt t y) x)
          (chr t x) (Adt t x) n -
        covDerivStepDt (chrDt t x) (A t x) n)
      D t := by
  classical

  have hlead := hswap (Fin.tail n)

  have hcorr :
      HasDerivWithinAt
        (fun s : Real =>
          ∑ slot : Fin r, ∑ p : Idx,
            chr s x (n 0) (Fin.tail n slot) p *
              A s x (Function.update (Fin.tail n) slot p))
        (∑ slot : Fin r, ∑ p : Idx,
          (chrDt t x (n 0) (Fin.tail n slot) p *
              A t x (Function.update (Fin.tail n) slot p) +
            chr t x (n 0) (Fin.tail n slot) p *
              Adt t x (Function.update (Fin.tail n) slot p)))
        D t := by
    refine HasDerivWithinAt.fun_sum ?_
    intro slot _hslot
    refine HasDerivWithinAt.fun_sum ?_
    intro p _hp
    exact (hchr (n 0) (Fin.tail n slot) p).mul (hA (Function.update (Fin.tail n) slot p))



  have hmain :
      HasDerivWithinAt
        (fun s : Real =>
          covDerivStepComp
            (frameExtData (I := I) frame (fun y : M => A s y) x)
            (chr s x) (A s x) n)
        (extDerivFun (I := I) (fun y : M => Adt t y (Fin.tail n)) x (frame (n 0) x) -
          ∑ slot : Fin r, ∑ p : Idx,
            (chrDt t x (n 0) (Fin.tail n slot) p *
                A t x (Function.update (Fin.tail n) slot p) +
              chr t x (n 0) (Fin.tail n slot) p *
                Adt t x (Function.update (Fin.tail n) slot p)))
        D t :=
    hlead.sub hcorr
  refine hmain.congr_deriv ?_



  rw [covDerivStepComp, frameExtData, covDerivStepDt]
  simp only [Finset.sum_add_distrib]
  ring

end StepDeriv










section Realized

open Tensor0SBundle
open DifferentialGeometry.Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]






















omit [I.Boundaryless] [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
theorem iteratedRmComp_one_hasDerivWithinAt
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (x₀ : M)
    (rm04Dt : Real → M → (Fin 4 → CoordinateIdx (𝕜 := Real) E) → Real)
    (chrDt : Real → M →
      CoordinateIdx (𝕜 := Real) E → CoordinateIdx (𝕜 := Real) E →
      CoordinateIdx (𝕜 := Real) E → Real)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x : M)
    (n : Fin 5 → CoordinateIdx (𝕜 := Real) E)
    (hrm : ∀ m : Fin 4 → CoordinateIdx (𝕜 := Real) E,
      HasDerivWithinAt
        (fun s : Real => realizedRmBase (I := I) S x₀ s x m)
        (rm04Dt (t : Real) x m) D.carrier (t : Real))
    (hchr : ∀ i a p : CoordinateIdx (𝕜 := Real) E,
      HasDerivWithinAt
        (fun s : Real => realizedChr (I := I) S x₀ s x i a p)
        (chrDt (t : Real) x i a p) D.carrier (t : Real))
    (hswap : ∀ m : Fin 4 → CoordinateIdx (𝕜 := Real) E,
      HasDerivWithinAt
        (fun s : Real =>
          extDerivFun (I := I) (fun y : M => realizedRmBase (I := I) S x₀ s y m) x
            (coordinateFrameAt (I := I) x₀ (n 0) x))
        (extDerivFun (I := I) (fun y : M => rm04Dt (t : Real) y m) x
          (coordinateFrameAt (I := I) x₀ (n 0) x))
        D.carrier (t : Real)) :
    HasDerivWithinAt
      (fun s : Real =>
        iteratedRmComp (I := I) (coordinateFrameAt (I := I) x₀)
          (realizedChr (I := I) S x₀) (realizedRmBase (I := I) S x₀) 1 s x n)
      (covDerivStepComp
          (frameExtData (I := I) (coordinateFrameAt (I := I) x₀)
            (fun y : M => rm04Dt (t : Real) y) x)
          (realizedChr (I := I) S x₀ (t : Real) x)
          (rm04Dt (t : Real) x) n -
        covDerivStepDt (chrDt (t : Real) x)
          (realizedRmBase (I := I) S x₀ (t : Real) x) n)
      D.carrier (t : Real) := by

  have hunfold :
      (fun s : Real =>
        iteratedRmComp (I := I) (coordinateFrameAt (I := I) x₀)
          (realizedChr (I := I) S x₀) (realizedRmBase (I := I) S x₀) 1 s x n) =
        fun s : Real =>
          covDerivStepComp
            (frameExtData (I := I) (coordinateFrameAt (I := I) x₀)
              (fun y : M => realizedRmBase (I := I) S x₀ s y) x)
            (realizedChr (I := I) S x₀ s x)
            (realizedRmBase (I := I) S x₀ s x) n := by
    funext s
    rw [iteratedRmComp_succ]
    simp only [iteratedRmComp_zero]
  rw [hunfold]
  exact covDerivStepComp_hasDerivWithinAt
    (I := I) (coordinateFrameAt (I := I) x₀)
    (realizedRmBase (I := I) S x₀) rm04Dt
    (realizedChr (I := I) S x₀) chrDt
    x n hrm hchr hswap

end Realized

end DifferentialGeometry.PDE.RicciFlow
