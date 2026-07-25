import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.RmRaisingBridge
import DifferentialGeometry.Tensor.RSTensor.MetricTrace.Higher

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


























































noncomputable section

namespace DifferentialGeometry.Integral.Connection

open Bundle Tensor0SBundle Filter
open DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]









private def freezeAllButSlots
    (Y : Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (q : Fin 4)
    (Z : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _)) :
    Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _) :=
  Function.update Y q Z

omit [FiniteDimensional ℝ E] in
private theorem freezeAllButSlots_apply
    (Y : Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (q : Fin 4)
    (Z : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (p : M) :
    (fun i : Fin 4 => freezeAllButSlots (I := I) Y q Z i p) =
      Function.update (fun i : Fin 4 => Y i p) q (Z p) := by
  funext i
  by_cases hi : i = q
  · subst hi; simp [freezeAllButSlots]
  · simp [freezeAllButSlots, Function.update_of_ne hi]







set_option backward.isDefEq.respectTransparency false in




noncomputable def freezeAllBut04Field
    [CompleteSpace E]
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (q : Fin 4)
    (Y : Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _)) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1 := by
  letI := tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H) (I := I)
    (M := M) 1
  let F : (p : M) →
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 p :=
    fun p : M => oneFormAtSlot0S (I := I) (A p) (fun i : Fin 4 => Y i p) q
  refine ⟨F, ?_⟩
  let d := Module.finrank Real E
  let b : Module.Basis (Fin d) Real E := Module.finBasis Real E
  refine (contMDiff_multilinearSection_iff_coord (TangentSpace I)
    (∞ : WithTop ℕ∞) b F).mpr ?_
  intro σ x₀


  have hcoeff :
      ContMDiffAt I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
        (fun y : M =>
          A y (Function.update (fun i : Fin 4 => Y i y) q
            (coordinateFrameAt (I := I) x₀ (σ 0) y)))
        x₀ := by
    let v : Fin 4 → (y : M) → TangentSpace I y :=
      fun i y => Function.update (fun j : Fin 4 => Y j y) q
        (coordinateFrameAt (I := I) x₀ (σ 0) y) i
    have hv : ∀ i : Fin 4,
        ContMDiffAt I (I.prod 𝓘(Real, E)) (∞ : WithTop ℕ∞)
          (fun y : M =>
            TotalSpace.mk' E (E := fun x : M => TangentSpace I x) y (v i y)) x₀ := by
      intro i
      by_cases hi : i = q
      · subst hi
        have hframe :
            ContMDiffAt I (I.prod 𝓘(Real, E)) (∞ : WithTop ℕ∞)
              (fun y : M =>
                TotalSpace.mk' E (E := fun x : M => TangentSpace I x) y
                  (coordinateFrameAt (I := I) x₀ (σ 0) y)) x₀ :=
          (coordinateFrameAt_isLocalFrame (I := I) x₀).contMDiffAt
            (coordinateFrameSet_open (I := I) x₀)
            (coordinateFrameAt_mem (I := I) x₀) (σ 0)
        refine hframe.congr_of_eventuallyEq ?_
        filter_upwards with y
        simp [v, Function.update_self]
      · have hYi := (Y i).contMDiff x₀
        refine hYi.congr_of_eventuallyEq ?_
        filter_upwards with y
        simp [v, Function.update_of_ne hi]
    have hA := TensorMultilinear.contMDiffAt_section_apply_gen
      (𝕜 := Real) (I := I) (M := M) (n := 4)
      (T := fun y : M => A y) (A.contMDiff x₀) v hv
    simpa [v, Tensor0SSpace.toModel, tensor0SSpace_continuousLinearEquiv_apply]
      using hA
  refine hcoeff.congr_of_eventuallyEq ?_
  let e := coordinateTrivializationAt (𝕜 := Real) (I := I) x₀
  have hx₀ : x₀ ∈ coordinateFrameSet (𝕜 := Real) (I := I) x₀ :=
    coordinateFrameAt_mem (𝕜 := Real) (I := I) x₀
  filter_upwards [(coordinateFrameSet_open (𝕜 := Real) (I := I) x₀).mem_nhds hx₀]
    with y hy
  rw [continuousMultilinearMap_basis_repr]
  change ((trivializationAt (Tensor0SModel 1 Real E)
      (Bundle.continuousMultilinearMap Real 1 E
        (TangentSpace I : M → Type _)) x₀
      ⟨y, F y⟩).2)
      (fun a : Fin 1 => b (σ a)) =
    A y (Function.update (fun i : Fin 4 => Y i y) q
      (coordinateFrameAt (I := I) x₀ (σ 0) y))
  change (F y).compContinuousLinearMap
      (fun _ : Fin 1 =>
        (trivializationAt E (TangentSpace I : M → Type _) x₀).symmL Real y)
      (fun a : Fin 1 => b (σ a)) =
    A y (Function.update (fun i : Fin 4 => Y i y) q
      (coordinateFrameAt (I := I) x₀ (σ 0) y))
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have hslot :
      (fun a : Fin 1 =>
        (trivializationAt E (TangentSpace I : M → Type _) x₀).symmL Real y
          (b (σ a))) =
        (fun _ : Fin 1 => coordinateFrameAt (I := I) x₀ (σ 0) y) := by
    funext a
    fin_cases a
    · change
        (coordinateTrivializationAt (𝕜 := Real) (I := I) x₀).symmL Real y
            (b (σ 0)) =
          coordinateFrameAt (I := I) x₀ (σ 0) y
      change e.symmL Real y (b (σ 0)) = e.localFrame b (σ 0) y
      rw [Bundle.Trivialization.localFrame_apply_of_mem_baseSet
        (e := e) (b := b) (i := σ 0) hy]
      rfl
  rw [hslot]
  change F y (fun _ : Fin 1 => coordinateFrameAt (I := I) x₀ (σ 0) y) = _
  simp only [F, oneFormAtSlot0S_apply]

@[simp] theorem freezeAllBut04Field_apply
    [CompleteSpace E]
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (q : Fin 4)
    (Y : Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (x : M) :
    freezeAllBut04Field (I := I) (M := M) A q Y x =
      oneFormAtSlot0S (I := I) (A x) (fun i : Fin 4 => Y i x) q := by
  rfl

theorem freezeAllBut04Field_apply_vec
    [CompleteSpace E]
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (q : Fin 4)
    (Y : Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (x : M) (W : TangentSpace I x) :
    freezeAllBut04Field (I := I) (M := M) A q Y x (fun _ : Fin 1 => W) =
      A x (Function.update (fun i : Fin 4 => Y i x) q W) := by
  rw [freezeAllBut04Field_apply]
  exact oneFormAtSlot0S_apply (I := I) (A x) (fun i : Fin 4 => Y i x) q W








private theorem allBut04FreezeNabla
    [T2Space M] [CompleteSpace E] [I.Boundaryless] [IsManifold I 1 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov 1)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (q : Fin 4)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (Y : Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    {x : M}
    (hYzero : ∀ i : Fin 4, i ≠ q → ((cov (fun p : M => Y i p) x) (X x)) = 0)
    (U : TangentSpace I x) :
    let B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) 1 :=
      freezeAllBut04Field (I := I) (M := M) A q Y
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        1 cov B x (vec2 (I := I) (X x) U) =
      totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        4 cov A x (Fin.cons (X x)
          (Function.update (fun i : Fin 4 => Y i x) q U)) := by
  classical
  let B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1 :=
    freezeAllBut04Field (I := I) (M := M) A q Y

  obtain ⟨Usec, hUsec, hUcov⟩ :=
    TensorLieDeriv.exists_cov_zero_at_apply (I := I) cov hcov x U

  let V4 : Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _) :=
    freezeAllButSlots (I := I) Y q Usec

  let V1 : Fin 1 → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _)
    | _ => Usec
  have hBtot :=
    totalNabla0SFun_apply_section (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 1 cov X B x (fun _ : Fin 1 => U)
  have hAtot :=
    totalNabla0SFun_apply_section (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 4 cov X A x
      (Function.update (fun i : Fin 4 => Y i x) q U)
  have hBeval :=
    nabla0SFun_eval_smooth_slots (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) cov X V1 B x
  have hAeval :=
    nabla0SFun_eval_smooth_slots (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) cov X V4 A x

  have hderiv :
      extDerivFun (I := I)
          (fun p : M => B p (fun a : Fin 1 => V1 a p)) x (X x) =
        extDerivFun (I := I)
          (fun p : M => A p (fun a : Fin 4 => V4 a p)) x (X x) := by
    have hfun :
        (fun p : M => B p (fun a : Fin 1 => V1 a p)) =
          fun p : M => A p (fun a : Fin 4 => V4 a p) := by
      funext p
      have hV1p :
          (fun a : Fin 1 => V1 a p) = (fun _ : Fin 1 => Usec p) := by
        funext a
        fin_cases a
        rfl
      have hV4p :
          (fun a : Fin 4 => V4 a p) =
            Function.update (fun i : Fin 4 => Y i p) q (Usec p) :=
        freezeAllButSlots_apply (I := I) Y q Usec p
      rw [hV1p, hV4p]
      rw [show
          B p (fun _ : Fin 1 => Usec p) =
            A p (Function.update (fun i : Fin 4 => Y i p) q (Usec p)) from
        freezeAllBut04Field_apply_vec (I := I) (M := M) A q Y p (Usec p)]
    rw [hfun]


  have hBcorr :
      (∑ a : Fin 1,
        B x
          (Function.update (fun b : Fin 1 => V1 b x) a
            ((cov (fun p : M => V1 a p) x) (X x)))) =
        A x
          (Function.update (fun i : Fin 4 => Y i x) q
            ((cov (fun p : M => Usec p) x) (X x))) := by
    rw [Fin.sum_univ_one]
    rw [show
        Function.update (fun b : Fin 1 => V1 b x) 0
            ((cov (fun p : M => V1 0 p) x) (X x)) =
          (fun _ : Fin 1 => (cov (fun p : M => Usec p) x) (X x)) by
      funext a
      fin_cases a
      simp [V1]]
    rw [show
        B x (fun _ : Fin 1 => (cov (fun p : M => Usec p) x) (X x)) =
          A x (Function.update (fun i : Fin 4 => Y i x) q
            ((cov (fun p : M => Usec p) x) (X x))) from
      freezeAllBut04Field_apply_vec (I := I) (M := M) A q Y x
        ((cov (fun p : M => Usec p) x) (X x))]
  have hAcorr :
      (∑ a : Fin 4,
        A x
          (Function.update (fun b : Fin 4 => V4 b x) a
            ((cov (fun p : M => V4 a p) x) (X x)))) =
        A x
          (Function.update (fun i : Fin 4 => Y i x) q
            ((cov (fun p : M => Usec p) x) (X x))) := by

    have hV4x :
        (fun a : Fin 4 => V4 a x) =
          Function.update (fun i : Fin 4 => Y i x) q (Usec x) :=
      freezeAllButSlots_apply (I := I) Y q Usec x
    rw [Finset.sum_eq_single q]
    ·
      have hVq : (fun p : M => V4 q p) = (fun p : M => Usec p) := by
        funext p
        simp [V4, freezeAllButSlots]
      rw [hVq, hV4x]

      congr 1
      funext i
      by_cases hi : i = q
      · subst hi; simp
      · simp [Function.update_of_ne hi]
    ·
      intro a _ ha
      have hVa : (fun p : M => V4 a p) = (fun p : M => Y a p) := by
        funext p
        simp [V4, freezeAllButSlots, Function.update_of_ne ha]
      rw [hVa, hYzero a ha]
      exact metricTrace_tensor0S_update_zero (I := I) (A x) _ a
    · intro hq
      exact absurd (Finset.mem_univ q) hq
  calc
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        1 cov B x (vec2 (I := I) (X x) U)
        =
      nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        1 cov X B x (fun _ : Fin 1 => U) := by
        have h := hBtot
        rw [show Fin.cons (X x) (fun _ : Fin 1 => U) = vec2 (I := I) (X x) U by
          funext a
          fin_cases a <;> rfl] at h
        exact h
    _ =
      nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        4 cov X A x (Function.update (fun i : Fin 4 => Y i x) q U) := by
        have hV1x :
            (fun a : Fin 1 => V1 a x) = (fun _ : Fin 1 => U) := by
          funext a
          fin_cases a
          simp [V1, hUsec]
        have hV4x :
            (fun a : Fin 4 => V4 a x) =
              Function.update (fun i : Fin 4 => Y i x) q U := by
          rw [freezeAllButSlots_apply (I := I) Y q Usec x, hUsec]
        rw [← hV1x, ← hV4x]
        rw [hBeval, hAeval, hderiv, hBcorr, hAcorr]
    _ =
      totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        4 cov A x (Fin.cons (X x)
          (Function.update (fun i : Fin 4 => Y i x) q U)) := hAtot.symm

end DifferentialGeometry.Integral.Connection



namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Integral.Connection
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]





def rmFrozenSlotField
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (q : Fin 4)
    (Y : Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _)) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1 :=
  freezeAllBut04Field (I := I) (M := M) (S.base.rm04 t) q Y

omit [I.Boundaryless] [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
@[simp] theorem rmFrozenSlotField_apply
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (q : Fin 4)
    (Y : Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (x : M) :
    rmFrozenSlotField (I := I) S t q Y x =
      oneFormAtSlot0S (I := I) (S.base.rm04 t x) (fun i : Fin 4 => Y i x) q :=
  rfl

omit [I.Boundaryless] [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
theorem rmFrozenSlotField_apply_vec
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (q : Fin 4)
    (Y : Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (x : M) (W : TangentSpace I x) :
    rmFrozenSlotField (I := I) S t q Y x (fun _ : Fin 1 => W) =
      S.base.rm04 t x (Function.update (fun i : Fin 4 => Y i x) q W) :=
  freezeAllBut04Field_apply_vec (I := I) (M := M) (S.base.rm04 t) q Y x W


omit [I.Boundaryless] [IsManifold I 2 M] in
omit [SigmaCompactSpace M] [T2Space M] in
private theorem rmFrozen_connSmoothInf
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (S.family.connection t) (∞ : WithTop ℕ∞) := by
  simpa [SolutionFamily.connection, metricCov] using
    metricCov_smooth (I := I) (M := M) (S.base.metric t)



def nablaRmFrozenSlotField
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (q : Fin 4)
    (Y : Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _)) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2 :=
  totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    1 (S.family.connection t) (rmFrozenSlotField (I := I) S t q Y)
    (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
      1 (S.family.connection t) (rmFrozen_connSmoothInf (I := I) S t)
      (rmFrozenSlotField (I := I) S t q Y))




omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem nablaRmFrozenSlotField_realizes
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (q : Fin 4)
    (Y : Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _)) :
    TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      1 (S.family.connection t) (rmFrozenSlotField (I := I) S t q Y)
      (nablaRmFrozenSlotField (I := I) S t q Y) :=
  totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    1 (S.family.connection t) (rmFrozenSlotField (I := I) S t q Y)
    (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
      1 (S.family.connection t) (rmFrozen_connSmoothInf (I := I) S t)
      (rmFrozenSlotField (I := I) S t q Y))















omit [SigmaCompactSpace M] in
theorem nablaRmFrozenSlot_eval
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (q : Fin 4)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (Y : Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (x₀ : M)
    (hYzero : ∀ i : Fin 4, i ≠ q →
      ((S.family.connection (t : Real) (fun p : M => Y i p) x₀) (X x₀)) = 0)
    (U : TangentSpace I x₀) :
    nablaRmFrozenSlotField (I := I) S (t : Real) q Y x₀
        (vec2 (I := I) (X x₀) U) =
      nablaRm04Field (I := I) S (t : Real) x₀
        (Fin.cons (X x₀)
          (Function.update (fun i : Fin 4 => Y i x₀) q U)) := by
  have hcov :
      CovariantDerivative.ContMDiffCovariantDerivativeLocally
        (S.family.connection (t : Real)) (1 : WithTop ℕ∞) :=
    connSmoothOfSol (I := I) S hS (t : Real) (D.regular_subset t.2)


  have hBval :
      nablaRmFrozenSlotField (I := I) S (t : Real) q Y x₀
          (vec2 (I := I) (X x₀) U) =
        totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          1 (S.family.connection (t : Real))
          (rmFrozenSlotField (I := I) S (t : Real) q Y) x₀
          (vec2 (I := I) (X x₀) U) := by
    rfl

  have hAval :
      nablaRm04Field (I := I) S (t : Real) x₀
          (Fin.cons (X x₀)
            (Function.update (fun i : Fin 4 => Y i x₀) q U)) =
        totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          4 (S.family.connection (t : Real)) (S.base.rm04 (t : Real)) x₀
          (Fin.cons (X x₀)
            (Function.update (fun i : Fin 4 => Y i x₀) q U)) := by
    rfl
  rw [hBval, hAval]
  exact allBut04FreezeNabla (I := I) (M := M)
    (S.family.connection (t : Real)) hcov (S.base.rm04 (t : Real)) q X Y hYzero U

end DifferentialGeometry.PDE.RicciFlow
