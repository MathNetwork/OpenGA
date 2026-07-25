import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.RmRealizationBridge

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false






































noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle
open DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]










section Field

variable {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}









def nablaKRm04Field
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    (k : ℕ) →
      Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) (4 + k)
  | 0 => S.base.rm04 t
  | (k + 1) =>
      totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (4 + k) (S.family.connection t) (nablaKRm04Field S t k)
        (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
          (4 + k) (S.family.connection t) (connSmoothInf (I := I) S t)
          (nablaKRm04Field S t k))

omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
@[simp] theorem nablaKRm04Field_zero
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    nablaKRm04Field (I := I) S t 0 = S.base.rm04 t := rfl

omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem nablaKRm04Field_succ
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (k : ℕ) :
    nablaKRm04Field (I := I) S t (k + 1) =
      totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (4 + k) (S.family.connection t) (nablaKRm04Field (I := I) S t k)
        (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
          (4 + k) (S.family.connection t) (connSmoothInf (I := I) S t)
          (nablaKRm04Field (I := I) S t k)) := rfl





omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem nablaKRm04Field_realizes
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (k : ℕ) :
    TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (4 + k) (S.family.connection t) (nablaKRm04Field (I := I) S t k)
      (nablaKRm04Field (I := I) S t (k + 1)) := by
  rw [nablaKRm04Field_succ]
  exact totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    (4 + k) (S.family.connection t) (nablaKRm04Field (I := I) S t k)
    (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
      (4 + k) (S.family.connection t) (connSmoothInf (I := I) S t)
      (nablaKRm04Field (I := I) S t k))

end Field













section Bridge

variable {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}









omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem iteratedRmComp_eq_nablaKRm04Field
    (S : SolutionOn (I := I) (M := M) D)
    (x₀ : M) (t : Real) :
    ∀ (k : ℕ) {x : M}, x ∈ coordinateFrameSet (I := I) x₀ →
      ∀ n : Fin (4 + k) → CoordinateIdx (𝕜 := Real) E,
        iteratedRmComp (I := I) (coordinateFrameAt (I := I) x₀)
            (realizedChr (I := I) S x₀) (realizedRmBase (I := I) S x₀) k t x n =
          nablaKRm04Field (I := I) S t k x
            (frameTuple (I := I) (coordinateFrameAt (I := I) x₀) x n) := by
  classical
  set frame := coordinateFrameAt (I := I) x₀ with hframe_def
  intro k
  induction k with
  | zero =>
      intro x hx n
      simp only [iteratedRmComp_zero, nablaKRm04Field_zero, realizedRmBase,
        frameComp0S, hframe_def]
  | succ k ih =>
      intro x hx n


      have hlevelk :
          (fun y : M =>
              iteratedRmComp (I := I) frame
                (realizedChr (I := I) S x₀) (realizedRmBase (I := I) S x₀) k t y) =ᶠ[nhds x]
            fun y : M =>
              frameComp0S (I := I) (nablaKRm04Field (I := I) S t k) frame y := by
        refine Filter.eventually_of_mem
          ((coordinateFrameSet_open (I := I) x₀).mem_nhds hx) ?_
        intro y hy
        funext m
        simpa [frameComp0S, hframe_def] using ih hy m

      rw [iteratedRmComp_succ]

      have hext :
          frameExtData (I := I) frame
              (fun y : M =>
                iteratedRmComp (I := I) frame
                  (realizedChr (I := I) S x₀) (realizedRmBase (I := I) S x₀) k t y) x =
            frameExtData (I := I) frame
              (frameComp0S (I := I) (nablaKRm04Field (I := I) S t k) frame) x := by
        funext m d
        simp only [frameExtData]
        refine extDerivFun_eventuallyEq_congr (I := I) _ ?_
        exact hlevelk.mono fun y hy => congrFun hy m
      have hbase :
          iteratedRmComp (I := I) frame
              (realizedChr (I := I) S x₀) (realizedRmBase (I := I) S x₀) k t x =
            frameComp0S (I := I) (nablaKRm04Field (I := I) S t k) frame x :=
        hlevelk.self_of_nhds
      rw [hext, hbase]

      have hstep :=
        covDerivStepComp_frameComp_eq
          (I := I) (S.family.connection t) (nablaKRm04Field (I := I) S t k)
          (nablaKRm04Field (I := I) S t (k + 1))
          (nablaKRm04Field_realizes (I := I) S t k)
          frame
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
          (coordinateFrameSet_open (I := I) x₀) hx n

      simpa [realizedChr, hframe_def] using hstep



omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem iteratedRmComp_one_eq_nablaKRm04Field
    (S : SolutionOn (I := I) (M := M) D)
    (x₀ : M) (t : Real)
    {x : M} (hx : x ∈ coordinateFrameSet (I := I) x₀)
    (n : Fin (4 + 1) → CoordinateIdx (𝕜 := Real) E) :
    iteratedRmComp (I := I) (coordinateFrameAt (I := I) x₀)
        (realizedChr (I := I) S x₀) (realizedRmBase (I := I) S x₀) 1 t x n =
      nablaKRm04Field (I := I) S t 1 x
        (frameTuple (I := I) (coordinateFrameAt (I := I) x₀) x n) :=
  iteratedRmComp_eq_nablaKRm04Field (I := I) S x₀ t 1 hx n












omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem iterRmLF_eq_nabla
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (S : SolutionOn (I := I) (M := M) D) (t : Real)
    (frame : Idx → (y : M) → TangentSpace I y) {u : Set M}
    (hframe : IsLocalFrameOn I E (1 : WithTop ℕ∞) frame u) (hu : IsOpen u) :
    ∀ (k : ℕ) {x : M}, x ∈ u →
      ∀ n : Fin (4 + k) → Idx,
        iteratedRmComp (I := I) frame
            (fun s y => christoffelSymbolInFrame (S.family.connection s) frame hframe y)
            (fun s => frameComp0S (I := I) (S.base.rm04 s) frame) k t x n =
          nablaKRm04Field (I := I) S t k x (frameTuple (I := I) frame x n) := by
  classical
  intro k
  induction k with
  | zero =>
      intro x _hx n
      simp only [iteratedRmComp_zero, nablaKRm04Field_zero, frameComp0S]
  | succ k ih =>
      intro x hx n


      have hlevelk :
          (fun y : M =>
              iteratedRmComp (I := I) frame
                (fun s y => christoffelSymbolInFrame (S.family.connection s) frame hframe y)
                (fun s => frameComp0S (I := I) (S.base.rm04 s) frame) k t y) =ᶠ[nhds x]
            fun y : M =>
              frameComp0S (I := I) (nablaKRm04Field (I := I) S t k) frame y := by
        refine Filter.eventually_of_mem (hu.mem_nhds hx) ?_
        intro y hy
        funext m
        simpa [frameComp0S] using ih hy m
      rw [iteratedRmComp_succ]
      have hext :
          frameExtData (I := I) frame
              (fun y : M =>
                iteratedRmComp (I := I) frame
                  (fun s y => christoffelSymbolInFrame (S.family.connection s) frame hframe y)
                  (fun s => frameComp0S (I := I) (S.base.rm04 s) frame) k t y) x =
            frameExtData (I := I) frame
              (frameComp0S (I := I) (nablaKRm04Field (I := I) S t k) frame) x := by
        funext m d
        simp only [frameExtData]
        refine extDerivFun_eventuallyEq_congr (I := I) _ ?_
        exact hlevelk.mono fun y hy => congrFun hy m
      have hbase :
          iteratedRmComp (I := I) frame
              (fun s y => christoffelSymbolInFrame (S.family.connection s) frame hframe y)
              (fun s => frameComp0S (I := I) (S.base.rm04 s) frame) k t x =
            frameComp0S (I := I) (nablaKRm04Field (I := I) S t k) frame x :=
        hlevelk.self_of_nhds
      rw [hext, hbase]
      have hstep :=
        covDerivStepComp_frameComp_eq
          (I := I) (S.family.connection t) (nablaKRm04Field (I := I) S t k)
          (nablaKRm04Field (I := I) S t (k + 1))
          (nablaKRm04Field_realizes (I := I) S t k)
          frame hframe hu hx n
      simpa using hstep

end Bridge









section RicciIdentity

variable {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}



omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem nablaKRm04_nabla0SSectionRealizes
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (k : ℕ) :
    DifferentialGeometry.Integral.Connection.Nabla0SSectionRealizes (I := I) (4 + k)
      (S.family.connection t) (nablaKRm04Field (I := I) S t k)
      (nablaKRm04Field (I := I) S t (k + 1)) := by
  intro y X slots
  exact nablaKRm04Field_realizes (I := I) S t k X y slots






omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem nablaKRm04_nabla20SRealizesAt
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (k : ℕ) (x : M) :
    DifferentialGeometry.Integral.Connection.Nabla20SRealizesAt (I := I) (4 + k)
      (S.family.connection t) (nablaKRm04Field (I := I) S t k)
      (nablaKRm04Field (I := I) S t (k + 1)) x
      (nablaKRm04Field (I := I) S t (k + 2) x) := by
  refine ⟨nablaKRm04_nabla0SSectionRealizes (I := I) S t k, ?_⟩
  intro X slots
  exact nablaKRm04Field_realizes (I := I) S t (k + 1) X x slots







omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem nablaKRm04_ricciIdentityAt
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (k : ℕ) (x : M) :
    DifferentialGeometry.Integral.Connection.Tensor0SRicciIdentityAt (I := I)
      (S.base.rm13 (t : Real)) (nablaKRm04Field (I := I) S (t : Real) k x)
      (nablaKRm04Field (I := I) S (t : Real) (k + 2) x) := by
  have hcov :
      CovariantDerivative.ContMDiffCovariantDerivativeLocally
        (S.family.connection (t : Real)) (1 : WithTop ℕ∞) :=
    connSmoothOfSol (I := I) S hS (t : Real) (D.regular_subset t.2)
  have htor : (S.family.connection (t : Real)).torsion x = 0 := by
    have htf :=
      DifferentialGeometry.Integral.Connection.torsionFree_of_isLeviCivita
        (I := I) (lcAt_regular (I := I) S hS t)
    simpa [DifferentialGeometry.Integral.Connection.IsTorsionFreeAt] using htf x
  exact DifferentialGeometry.Integral.Connection.tensor0S_ricciIdentity_of_torsionFree
    (I := I) (S.family.connection (t : Real)) hcov (S.base.rm13 (t : Real))
    (nablaKRm04Field (I := I) S (t : Real) k)
    (nablaKRm04Field (I := I) S (t : Real) (k + 1))
    (nablaKRm04Field (I := I) S (t : Real) k x)
    (nablaKRm04Field (I := I) S (t : Real) (k + 1) x)
    (nablaKRm04Field (I := I) S (t : Real) (k + 2) x)
    (rm13OfSol (I := I) S (t : Real) (D.regular_subset t.2)) rfl rfl
    (nablaKRm04_nabla20SRealizesAt (I := I) S (t : Real) k x) htor

end RicciIdentity

end DifferentialGeometry.PDE.RicciFlow
