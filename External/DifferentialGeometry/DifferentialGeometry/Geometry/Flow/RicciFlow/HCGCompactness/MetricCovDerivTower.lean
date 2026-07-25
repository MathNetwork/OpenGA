import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.RmRealizationBridge
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricCovDerivLinear

set_option autoImplicit false
set_option linter.style.longLine false


























noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Integral.Connection
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {u : Set M}









def iterCovComp {r : ℕ}
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr : M → Idx → Idx → Idx → Real)
    (base : M → (Fin r → Idx) → Real) :
    (a : ℕ) → M → (Fin (r + a) → Idx) → Real
  | 0 => base
  | (a + 1) => fun x =>
      covDerivStepComp
        (frameExtData (I := I) frame
          (fun y : M => iterCovComp frame chr base a y) x)
        (chr x)
        (iterCovComp frame chr base a x)

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [DecidableEq Idx] in
@[simp] theorem iterCovComp_zero {r : ℕ}
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr : M → Idx → Idx → Idx → Real)
    (base : M → (Fin r → Idx) → Real) :
    iterCovComp (I := I) frame chr base 0 = base := rfl

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [DecidableEq Idx] in
theorem iterCovComp_succ {r : ℕ}
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr : M → Idx → Idx → Idx → Real)
    (base : M → (Fin r → Idx) → Real) (a : ℕ) (x : M) :
    iterCovComp (I := I) frame chr base (a + 1) x =
      covDerivStepComp
        (frameExtData (I := I) frame
          (fun y : M => iterCovComp (I := I) frame chr base a y) x)
        (chr x)
        (iterCovComp (I := I) frame chr base a x) := rfl







omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem iterCov_realizes
    (gRef : SmoothRiemannianMetric I M) {r : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r) (a : ℕ) :
    TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (r + a) (leviCivitaConnectionOfMetric (I := I) gRef)
      (iterCov (I := I) gRef r T a)
      (iterCov (I := I) gRef r T (a + 1)) := by
  have hcov :
      CovariantDerivative.ContMDiffCovariantDerivativeLocally
        (I := I) (E := E) (M := M) (leviCivitaConnectionOfMetric (I := I) gRef)
        (∞ : WithTop ℕ∞) :=
    leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
      (I := I) (M := M) gRef
  intro X x slots
  rw [iterCov_succ, covStep_apply]
  exact totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    (r + a) (leviCivitaConnectionOfMetric (I := I) gRef)
    (iterCov (I := I) gRef r T a)
    (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M) (r + a)
      (leviCivitaConnectionOfMetric (I := I) gRef) hcov
      (iterCov (I := I) gRef r T a))
    X x slots













omit [I.Boundaryless] [DecidableEq Idx] in
omit [SigmaCompactSpace M] in
theorem iterCovComp_eq_iterCov
    (gRef : SmoothRiemannianMetric I M) {r : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r)
    (frame : Idx → (x : M) → TangentSpace I x)
    (hframe : IsLocalFrameOn I E (1 : WithTop ℕ∞) frame u) (hu : IsOpen u) :
    ∀ (a : ℕ) {x : M}, x ∈ u → ∀ n : Fin (r + a) → Idx,
      iterCovComp (I := I) frame
          (fun y : M =>
            christoffelSymbolInFrame
              (leviCivitaConnectionOfMetric (I := I) gRef) frame hframe y)
          (frameComp0S (I := I) T frame) a x n =
        iterCov (I := I) gRef r T a x (frameTuple (I := I) frame x n) := by
  classical
  intro a
  induction a with
  | zero =>
      intro x hx n
      rw [iterCovComp_zero]
      rfl
  | succ a ih =>
      intro x hx n


      have hlevela :
          (fun y : M =>
              iterCovComp (I := I) frame
                (fun z : M =>
                  christoffelSymbolInFrame
                    (leviCivitaConnectionOfMetric (I := I) gRef) frame hframe z)
                (frameComp0S (I := I) T frame) a y) =ᶠ[nhds x]
            fun y : M =>
              frameComp0S (I := I) (iterCov (I := I) gRef r T a) frame y := by
        refine Filter.eventually_of_mem (hu.mem_nhds hx) ?_
        intro y hy
        funext m
        simpa [frameComp0S, frameTuple] using ih hy m

      rw [iterCovComp_succ]

      have hext :
          frameExtData (I := I) frame
              (fun y : M =>
                iterCovComp (I := I) frame
                  (fun z : M =>
                    christoffelSymbolInFrame
                      (leviCivitaConnectionOfMetric (I := I) gRef) frame hframe z)
                  (frameComp0S (I := I) T frame) a y) x =
            frameExtData (I := I) frame
              (frameComp0S (I := I) (iterCov (I := I) gRef r T a) frame) x := by
        funext m d
        simp only [frameExtData]
        refine extDerivFun_eventuallyEq_congr (I := I) _ ?_
        exact hlevela.mono fun y hy => congrFun hy m
      have hbase :
          iterCovComp (I := I) frame
              (fun z : M =>
                christoffelSymbolInFrame
                  (leviCivitaConnectionOfMetric (I := I) gRef) frame hframe z)
              (frameComp0S (I := I) T frame) a x =
            frameComp0S (I := I) (iterCov (I := I) gRef r T a) frame x :=
        hlevela.self_of_nhds
      rw [hext, hbase]

      exact covDerivStepComp_frameComp_eq
        (I := I) (leviCivitaConnectionOfMetric (I := I) gRef)
        (iterCov (I := I) gRef r T a)
        (iterCov (I := I) gRef r T (a + 1))
        (iterCov_realizes (I := I) gRef T a)
        frame hframe hu hx n

end DifferentialGeometry.PDE.RicciFlow
