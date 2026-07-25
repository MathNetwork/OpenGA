import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.IteratedNablaRmTower

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



section FrameTuple

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]



def frameTuple {r : ℕ}
    (frame : Idx → (x : M) → TangentSpace I x) (x : M) (m : Fin r → Idx) :
    Fin r → TangentSpace I x :=
  fun q => frame (m q) x



def frameComp0S {r : ℕ}
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r)
    (frame : Idx → (x : M) → TangentSpace I x) :
    M → (Fin r → Idx) → Real :=
  fun x m => A x (frameTuple (I := I) frame x m)

omit [I.Boundaryless] [IsManifold I ∞ M] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [Fintype Idx] [DecidableEq Idx] in
@[simp] theorem frameComp0S_apply {r : ℕ}
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r)
    (frame : Idx → (x : M) → TangentSpace I x) (x : M) (m : Fin r → Idx) :
    frameComp0S (I := I) A frame x m = A x (fun q => frame (m q) x) := rfl



omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [Fintype Idx] [DecidableEq Idx] in
theorem frameTuple_eq_cons {r : ℕ}
    (frame : Idx → (x : M) → TangentSpace I x) (x : M) (n : Fin (r + 1) → Idx) :
    frameTuple (I := I) frame x n =
      Fin.cons (frame (n 0) x) (frameTuple (I := I) frame x (Fin.tail n)) := by
  funext q
  refine Fin.cases ?_ ?_ q
  · simp [frameTuple]
  · intro q
    simp [frameTuple, Fin.tail]

end FrameTuple












section StepBridge

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {u : Set M}









omit [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M] [DecidableEq Idx] in
theorem covDerivStepComp_frameComp_eq {s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (nablaA : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1))
    (hreal : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      s cov A nablaA)
    (frame : Idx → (x : M) → TangentSpace I x)
    (hframe : IsLocalFrameOn I E (1 : WithTop ℕ∞) frame u) (hu : IsOpen u)
    {x : M} (hx : x ∈ u) (n : Fin (s + 1) → Idx) :
    covDerivStepComp
        (frameExtData (I := I) frame (frameComp0S (I := I) A frame) x)
        (christoffelSymbolInFrame cov frame hframe x)
        (frameComp0S (I := I) A frame x) n =
      nablaA x (frameTuple (I := I) frame x n) := by
  classical

  set V : Fin s → (y : M) → TangentSpace I y :=
    fun q y => frame (Fin.tail n q) y with hV_def

  obtain ⟨X, hX⟩ :=
    ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x (frame (n 0) x)

  have hV_at : ∀ q : Fin s,
      ContMDiffAt I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
        (fun y : M => (⟨y, V q y⟩ : TotalSpace E (TangentSpace I : M → Type _))) x := by
    intro q
    have htop :
        ContMDiffAt I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
          (fun y : M =>
            (⟨y, frame (Fin.tail n q) y⟩ :
              TotalSpace E (TangentSpace I : M → Type _))) x :=
      (hframe.contMDiffAt hu hx (Fin.tail n q))
    simpa [hV_def] using htop

  have heval :=
    (hreal X x (fun q : Fin s => V q x)).trans
      (nabla0SFun_eval_C1_slots
        (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        cov X V A x hV_at)


  unfold covDerivStepComp
  rw [frameTuple_eq_cons (I := I) frame x n]

  rw [show
      nablaA x (Fin.cons (frame (n 0) x)
          (frameTuple (I := I) frame x (Fin.tail n))) =
        nablaA x (Fin.cons (X x) (fun q : Fin s => V q x)) by
        rw [hX]; rfl]
  rw [heval, hX]

  have hext :
      extDerivFun (I := I)
          (fun p : M => A p (fun q : Fin s => V q p)) x (frame (n 0) x) =
        frameExtData (I := I) frame (frameComp0S (I := I) A frame) x
          (Fin.tail n) (n 0) := by
    rfl
  rw [hext]

  congr 1

  have hslot : ∀ q : Fin s,
      A x
          (Function.update (fun b : Fin s => V b x) q ((cov (V q) x) (frame (n 0) x))) =
        ∑ p : Idx,
          christoffelSymbolInFrame cov frame hframe x (n 0) (Fin.tail n q) p *
            frameComp0S (I := I) A frame x
              (Function.update (Fin.tail n) q p) := by
    intro q
    have hVq : V q = frame (Fin.tail n q) := by funext y; rfl
    have hcov :
        (cov (V q) x) (frame (n 0) x) =
          ∑ p : Idx,
            christoffelSymbolInFrame cov frame hframe x (n 0) (Fin.tail n q) p •
              frame p x := by
      rw [hVq]
      exact covariantDerivative_eq_sum_christoffel
        (𝕜 := Real) (I := I) (cov := cov) (frame := frame) (hframe := hframe) hx
        (n 0) (Fin.tail n q)
    rw [hcov]
    rw [show
        A x
            (Function.update (fun b : Fin s => V b x) q
              (∑ p : Idx,
                christoffelSymbolInFrame cov frame hframe x (n 0) (Fin.tail n q) p •
                  frame p x)) =
          (A x).toMultilinearMap
            (Function.update (fun b : Fin s => V b x) q
              (∑ p : Idx,
                christoffelSymbolInFrame cov frame hframe x (n 0) (Fin.tail n q) p •
                  frame p x)) from rfl]
    rw [MultilinearMap.map_update_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [MultilinearMap.map_update_smul]

    have hupd :
        Function.update (fun b : Fin s => V b x) q (frame p x) =
          frameTuple (I := I) frame x (Function.update (Fin.tail n) q p) := by
      funext r
      by_cases hr : r = q
      · subst hr; simp [frameTuple, Function.update_self]
      · simp [frameTuple, Function.update_of_ne hr, hV_def]
    rw [show
        (A x).toMultilinearMap (Function.update (fun b : Fin s => V b x) q (frame p x)) =
          A x (Function.update (fun b : Fin s => V b x) q (frame p x)) from rfl]
    rw [hupd]
    simp [frameComp0S, smul_eq_mul]

  exact Finset.sum_congr rfl fun q _ => (hslot q).symm

end StepBridge



section Solution



omit [I.Boundaryless] [IsManifold I 2 M] in
omit [SigmaCompactSpace M] [T2Space M] in
theorem connSmoothInf
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (S.family.connection t) (∞ : WithTop ℕ∞) := by
  simpa [SolutionFamily.connection, metricCov] using
    metricCov_smooth (I := I) (M := M) (S.base.metric t)



omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem extDerivFun_eventuallyEq_congr
    {f g : M → Real} {x : M} (V : TangentSpace I x)
    (h : f =ᶠ[nhds x] g) :
    extDerivFun (I := I) f x V = extDerivFun (I := I) g x V := by
  rw [extDerivFun_real_eq_mfderiv (I := I) f x V,
    extDerivFun_real_eq_mfderiv (I := I) g x V]
  rw [Filter.EventuallyEq.mfderiv_eq (I := I) (I' := 𝓘(Real, Real)) h]
  rfl









def nablaRm04Field
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 5 :=
  totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    4 (S.family.connection t) (S.base.rm04 t)
    (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
      4 (S.family.connection t) (connSmoothInf (I := I) S t) (S.base.rm04 t))



def nabla2Rm04Field
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 6 :=
  totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    5 (S.family.connection t) (nablaRm04Field (I := I) S t)
    (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
      5 (S.family.connection t) (connSmoothInf (I := I) S t)
      (nablaRm04Field (I := I) S t))




def nabla3Rm04Field
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 7 :=
  totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    6 (S.family.connection t) (nabla2Rm04Field (I := I) S t)
    (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
      6 (S.family.connection t) (connSmoothInf (I := I) S t)
      (nabla2Rm04Field (I := I) S t))

omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem nablaRm04Field_realizes
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      4 (S.family.connection t) (S.base.rm04 t) (nablaRm04Field (I := I) S t) :=
  totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    4 (S.family.connection t) (S.base.rm04 t)
    (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
      4 (S.family.connection t) (connSmoothInf (I := I) S t) (S.base.rm04 t))

omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem nabla2Rm04Field_realizes
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      5 (S.family.connection t) (nablaRm04Field (I := I) S t)
      (nabla2Rm04Field (I := I) S t) :=
  totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    5 (S.family.connection t) (nablaRm04Field (I := I) S t)
    (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
      5 (S.family.connection t) (connSmoothInf (I := I) S t)
      (nablaRm04Field (I := I) S t))

omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem nabla3Rm04Field_realizes
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      6 (S.family.connection t) (nabla2Rm04Field (I := I) S t)
      (nabla3Rm04Field (I := I) S t) :=
  totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    6 (S.family.connection t) (nabla2Rm04Field (I := I) S t)
    (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
      6 (S.family.connection t) (connSmoothInf (I := I) S t)
      (nabla2Rm04Field (I := I) S t))









def realizedChr
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (x₀ : M) :
    Real → M → CoordinateIdx (𝕜 := Real) E → CoordinateIdx (𝕜 := Real) E →
      CoordinateIdx (𝕜 := Real) E → Real :=
  fun t x =>
    christoffelSymbolInFrame (S.family.connection t)
      (coordinateFrameAt (I := I) x₀)
      (coordinateFrameAt_isLocalFrame_one (I := I) x₀) x



def realizedRmBase
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (x₀ : M) :
    Real → M → (Fin 4 → CoordinateIdx (𝕜 := Real) E) → Real :=
  fun t => frameComp0S (I := I) (S.base.rm04 t) (coordinateFrameAt (I := I) x₀)

omit [I.Boundaryless] [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
@[simp] theorem realizedRmBase_apply
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (x₀ : M)
    (t : Real) (x : M) (m : Fin 4 → CoordinateIdx (𝕜 := Real) E) :
    realizedRmBase (I := I) S x₀ t x m =
      S.base.rm04 t x (fun q => coordinateFrameAt (I := I) x₀ (m q) x) := rfl











omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem iteratedRmComp_one_eq_nablaRm04Field
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (x₀ : M) (t : Real)
    {x : M} (hx : x ∈ coordinateFrameSet (I := I) x₀)
    (n : Fin 5 → CoordinateIdx (𝕜 := Real) E) :
    iteratedRmComp (I := I) (coordinateFrameAt (I := I) x₀)
        (realizedChr (I := I) S x₀) (realizedRmBase (I := I) S x₀) 1 t x n =
      nablaRm04Field (I := I) S t x
        (frameTuple (I := I) (coordinateFrameAt (I := I) x₀) x n) := by
  rw [iteratedRmComp_succ]
  simp only [iteratedRmComp_zero]
  exact covDerivStepComp_frameComp_eq
    (I := I) (S.family.connection t) (S.base.rm04 t) (nablaRm04Field (I := I) S t)
    (nablaRm04Field_realizes (I := I) S t)
    (coordinateFrameAt (I := I) x₀)
    (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
    (coordinateFrameSet_open (I := I) x₀) hx n











omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem iteratedRmComp_two_eq_nabla2Rm04Field
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (x₀ : M) (t : Real)
    (n : Fin 6 → CoordinateIdx (𝕜 := Real) E) :
    iteratedRmComp (I := I) (coordinateFrameAt (I := I) x₀)
        (realizedChr (I := I) S x₀) (realizedRmBase (I := I) S x₀) 2 t x₀ n =
      nabla2Rm04Field (I := I) S t x₀
        (frameTuple (I := I) (coordinateFrameAt (I := I) x₀) x₀ n) := by
  classical
  set frame := coordinateFrameAt (I := I) x₀ with hframe_def


  have hlevel1 :
      (fun y : M =>
          iteratedRmComp (I := I) frame
            (realizedChr (I := I) S x₀) (realizedRmBase (I := I) S x₀) 1 t y) =ᶠ[nhds x₀]
        fun y : M =>
          frameComp0S (I := I) (nablaRm04Field (I := I) S t) frame y := by
    refine Filter.eventually_of_mem
      ((coordinateFrameSet_open (I := I) x₀).mem_nhds (coordinateFrameAt_mem (I := I) x₀))
      ?_
    intro y hy
    funext m
    simpa [frameComp0S, hframe_def] using
      iteratedRmComp_one_eq_nablaRm04Field (I := I) S x₀ t hy m

  rw [iteratedRmComp_succ]

  have hext :
      frameExtData (I := I) frame
          (fun y : M =>
            iteratedRmComp (I := I) frame
              (realizedChr (I := I) S x₀) (realizedRmBase (I := I) S x₀) 1 t y) x₀ =
        frameExtData (I := I) frame
          (frameComp0S (I := I) (nablaRm04Field (I := I) S t) frame) x₀ := by
    funext m d
    simp only [frameExtData]
    refine extDerivFun_eventuallyEq_congr (I := I) _ ?_
    exact hlevel1.mono fun y hy => congrFun hy m
  have hbase :
      iteratedRmComp (I := I) frame
          (realizedChr (I := I) S x₀) (realizedRmBase (I := I) S x₀) 1 t x₀ =
        frameComp0S (I := I) (nablaRm04Field (I := I) S t) frame x₀ :=
    hlevel1.self_of_nhds
  rw [hext, hbase]

  exact covDerivStepComp_frameComp_eq
    (I := I) (S.family.connection t) (nablaRm04Field (I := I) S t)
    (nabla2Rm04Field (I := I) S t)
    (nabla2Rm04Field_realizes (I := I) S t)
    frame
    (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
    (coordinateFrameSet_open (I := I) x₀) (coordinateFrameAt_mem (I := I) x₀) n

end Solution








section RicciIdentity



omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem rm04_nabla0SSectionRealizes
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    DifferentialGeometry.Integral.Connection.Nabla0SSectionRealizes (I := I) 4
      (S.family.connection t) (S.base.rm04 t) (nablaRm04Field (I := I) S t) := by
  intro y X slots
  exact nablaRm04Field_realizes (I := I) S t X y slots



omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem nablaRm04_nabla0SSectionRealizes
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    DifferentialGeometry.Integral.Connection.Nabla0SSectionRealizes (I := I) 5
      (S.family.connection t) (nablaRm04Field (I := I) S t)
      (nabla2Rm04Field (I := I) S t) := by
  intro y X slots
  exact nabla2Rm04Field_realizes (I := I) S t X y slots




omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem rm04_nabla20SRealizesAt
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M) :
    DifferentialGeometry.Integral.Connection.Nabla20SRealizesAt (I := I) 4
      (S.family.connection t) (S.base.rm04 t) (nablaRm04Field (I := I) S t) x
      (nabla2Rm04Field (I := I) S t x) := by
  refine ⟨rm04_nabla0SSectionRealizes (I := I) S t, ?_⟩
  intro X slots
  exact nabla2Rm04Field_realizes (I := I) S t X x slots




omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem nablaRm04_nabla20SRealizesAt
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M) :
    DifferentialGeometry.Integral.Connection.Nabla20SRealizesAt (I := I) 5
      (S.family.connection t) (nablaRm04Field (I := I) S t)
      (nabla2Rm04Field (I := I) S t) x
      (nabla3Rm04Field (I := I) S t x) := by
  refine ⟨nablaRm04_nabla0SSectionRealizes (I := I) S t, ?_⟩
  intro X slots
  exact nabla3Rm04Field_realizes (I := I) S t X x slots




omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem rm04_ricciIdentityAt
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x : M) :
    DifferentialGeometry.Integral.Connection.Tensor0SRicciIdentityAt (I := I)
      (S.base.rm13 (t : Real)) (S.base.rm04 (t : Real) x)
      (nabla2Rm04Field (I := I) S (t : Real) x) := by
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
    (S.base.rm04 (t : Real)) (nablaRm04Field (I := I) S (t : Real))
    (S.base.rm04 (t : Real) x) (nablaRm04Field (I := I) S (t : Real) x)
    (nabla2Rm04Field (I := I) S (t : Real) x)
    (rm13OfSol (I := I) S (t : Real) (D.regular_subset t.2)) rfl rfl
    (rm04_nabla20SRealizesAt (I := I) S (t : Real) x) htor




omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem nablaRm04_ricciIdentityAt
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x : M) :
    DifferentialGeometry.Integral.Connection.Tensor0SRicciIdentityAt (I := I)
      (S.base.rm13 (t : Real)) (nablaRm04Field (I := I) S (t : Real) x)
      (nabla3Rm04Field (I := I) S (t : Real) x) := by
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
    (nablaRm04Field (I := I) S (t : Real)) (nabla2Rm04Field (I := I) S (t : Real))
    (nablaRm04Field (I := I) S (t : Real) x)
    (nabla2Rm04Field (I := I) S (t : Real) x)
    (nabla3Rm04Field (I := I) S (t : Real) x)
    (rm13OfSol (I := I) S (t : Real) (D.regular_subset t.2)) rfl rfl
    (nablaRm04_nabla20SRealizesAt (I := I) S (t : Real) x) htor

end RicciIdentity

end DifferentialGeometry.PDE.RicciFlow
