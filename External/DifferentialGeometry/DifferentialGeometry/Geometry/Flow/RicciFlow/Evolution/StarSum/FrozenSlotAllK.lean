import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.RmFrozenSlotField

set_option autoImplicit false
set_option linter.style.longLine false

















noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle Filter DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

set_option backward.isDefEq.respectTransparency false in





noncomputable def freezeAllBut0SField {s : ℕ}
    [CompleteSpace E]
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (q : Fin s)
    (Y : Fin s → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _)) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1 := by
  letI := tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H) (I := I)
    (M := M) 1
  let F : (p : M) →
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 p :=
    fun p : M => oneFormAtSlot0S (I := I) (A p) (fun i : Fin s => Y i p) q
  refine ⟨F, ?_⟩
  let d := Module.finrank Real E
  let b : Module.Basis (Fin d) Real E := Module.finBasis Real E
  refine (contMDiff_multilinearSection_iff_coord (TangentSpace I)
    (∞ : WithTop ℕ∞) b F).mpr ?_
  intro σ x₀
  have hcoeff :
      ContMDiffAt I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
        (fun y : M =>
          A y (Function.update (fun i : Fin s => Y i y) q
            (coordinateFrameAt (I := I) x₀ (σ 0) y)))
        x₀ := by
    let v : Fin s → (y : M) → TangentSpace I y :=
      fun i y => Function.update (fun j : Fin s => Y j y) q
        (coordinateFrameAt (I := I) x₀ (σ 0) y) i
    have hv : ∀ i : Fin s,
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
      (𝕜 := Real) (I := I) (M := M) (n := s)
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
    A y (Function.update (fun i : Fin s => Y i y) q
      (coordinateFrameAt (I := I) x₀ (σ 0) y))
  change (F y).compContinuousLinearMap
      (fun _ : Fin 1 =>
        (trivializationAt E (TangentSpace I : M → Type _) x₀).symmL Real y)
      (fun a : Fin 1 => b (σ a)) =
    A y (Function.update (fun i : Fin s => Y i y) q
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

@[simp] theorem freezeAllBut0SField_apply {s : ℕ}
    [CompleteSpace E]
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (q : Fin s)
    (Y : Fin s → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (x : M) :
    freezeAllBut0SField (I := I) (M := M) A q Y x =
      oneFormAtSlot0S (I := I) (A x) (fun i : Fin s => Y i x) q := by
  rfl

theorem freezeAllBut0SField_apply_vec {s : ℕ}
    [CompleteSpace E]
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (q : Fin s)
    (Y : Fin s → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (x : M) (W : TangentSpace I x) :
    freezeAllBut0SField (I := I) (M := M) A q Y x (fun _ : Fin 1 => W) =
      A x (Function.update (fun i : Fin s => Y i x) q W) := by
  rw [freezeAllBut0SField_apply]
  exact oneFormAtSlot0S_apply (I := I) (A x) (fun i : Fin s => Y i x) q W


omit [FiniteDimensional ℝ E] in
private theorem updateSlots_apply {s : ℕ}
    (Y : Fin s → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (q : Fin s)
    (Z : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (p : M) :
    (fun i : Fin s => (Function.update Y q Z) i p) =
      Function.update (fun i : Fin s => Y i p) q (Z p) := by
  funext i
  by_cases hi : i = q
  · subst hi; simp
  · simp [Function.update_of_ne hi]





theorem allBut0SFreezeNabla {s : ℕ}
    [T2Space M] [CompleteSpace E] [I.Boundaryless] [IsManifold I 1 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov 1)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (q : Fin s)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (Y : Fin s → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    {x : M}
    (hYzero : ∀ i : Fin s, i ≠ q → ((cov (fun p : M => Y i p) x) (X x)) = 0)
    (U : TangentSpace I x) :
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        1 cov (freezeAllBut0SField (I := I) (M := M) A q Y) x (vec2 (I := I) (X x) U) =
      totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        s cov A x (Fin.cons (X x)
          (Function.update (fun i : Fin s => Y i x) q U)) := by
  classical
  set B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1 :=
    freezeAllBut0SField (I := I) (M := M) A q Y with hB_def
  obtain ⟨Usec, hUsec, hUcov⟩ :=
    TensorLieDeriv.exists_cov_zero_at_apply (I := I) cov hcov x U
  set V4 : Fin s → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _) := Function.update Y q Usec with hV4_def
  let V1 : Fin 1 → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _)
    | _ => Usec
  have hBtot :=
    totalNabla0SFun_apply_section (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 1 cov X B x (fun _ : Fin 1 => U)
  have hAtot :=
    totalNabla0SFun_apply_section (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) s cov X A x
      (Function.update (fun i : Fin s => Y i x) q U)
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
          (fun p : M => A p (fun a : Fin s => V4 a p)) x (X x) := by
    have hfun :
        (fun p : M => B p (fun a : Fin 1 => V1 a p)) =
          fun p : M => A p (fun a : Fin s => V4 a p) := by
      funext p
      have hV1p :
          (fun a : Fin 1 => V1 a p) = (fun _ : Fin 1 => Usec p) := by
        funext a; fin_cases a; rfl
      have hV4p :
          (fun a : Fin s => V4 a p) =
            Function.update (fun i : Fin s => Y i p) q (Usec p) := by
        rw [hV4_def]; exact updateSlots_apply (I := I) Y q Usec p
      rw [hV1p, hV4p, hB_def]
      rw [show
          freezeAllBut0SField (I := I) (M := M) A q Y p (fun _ : Fin 1 => Usec p) =
            A p (Function.update (fun i : Fin s => Y i p) q (Usec p)) from
        freezeAllBut0SField_apply_vec (I := I) (M := M) A q Y p (Usec p)]
    rw [hfun]
  have hBcorr :
      (∑ a : Fin 1,
        B x
          (Function.update (fun b : Fin 1 => V1 b x) a
            ((cov (fun p : M => V1 a p) x) (X x)))) =
        A x
          (Function.update (fun i : Fin s => Y i x) q
            ((cov (fun p : M => Usec p) x) (X x))) := by
    rw [Fin.sum_univ_one]
    rw [show
        Function.update (fun b : Fin 1 => V1 b x) 0
            ((cov (fun p : M => V1 0 p) x) (X x)) =
          (fun _ : Fin 1 => (cov (fun p : M => Usec p) x) (X x)) by
      funext a; fin_cases a; simp [V1]]
    rw [hB_def, show
        freezeAllBut0SField (I := I) (M := M) A q Y x
            (fun _ : Fin 1 => (cov (fun p : M => Usec p) x) (X x)) =
          A x (Function.update (fun i : Fin s => Y i x) q
            ((cov (fun p : M => Usec p) x) (X x))) from
      freezeAllBut0SField_apply_vec (I := I) (M := M) A q Y x
        ((cov (fun p : M => Usec p) x) (X x))]
  have hAcorr :
      (∑ a : Fin s,
        A x
          (Function.update (fun b : Fin s => V4 b x) a
            ((cov (fun p : M => V4 a p) x) (X x)))) =
        A x
          (Function.update (fun i : Fin s => Y i x) q
            ((cov (fun p : M => Usec p) x) (X x))) := by
    have hV4x :
        (fun a : Fin s => V4 a x) =
          Function.update (fun i : Fin s => Y i x) q (Usec x) := by
      rw [hV4_def]; exact updateSlots_apply (I := I) Y q Usec x
    rw [Finset.sum_eq_single q]
    · have hVq : (fun p : M => V4 q p) = (fun p : M => Usec p) := by
        funext p; simp [hV4_def, Function.update_self]
      rw [hVq, hV4x]
      congr 1
      funext i
      by_cases hi : i = q
      · subst hi; simp
      · simp [Function.update_of_ne hi]
    · intro a _ ha
      have hVa : (fun p : M => V4 a p) = (fun p : M => Y a p) := by
        funext p; simp [hV4_def, Function.update_of_ne ha]
      rw [hVa, hYzero a ha]
      exact metricTrace_tensor0S_update_zero (I := I) (A x) _ a
    · intro hq; exact absurd (Finset.mem_univ q) hq
  calc
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        1 cov B x (vec2 (I := I) (X x) U)
        =
      nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        1 cov X B x (fun _ : Fin 1 => U) := by
        have h := hBtot
        rw [show Fin.cons (X x) (fun _ : Fin 1 => U) = vec2 (I := I) (X x) U by
          funext a; fin_cases a <;> rfl] at h
        exact h
    _ =
      nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        s cov X A x (Function.update (fun i : Fin s => Y i x) q U) := by
        have hV1x :
            (fun a : Fin 1 => V1 a x) = (fun _ : Fin 1 => U) := by
          funext a; fin_cases a; simp [V1, hUsec]
        have hV4x :
            (fun a : Fin s => V4 a x) =
              Function.update (fun i : Fin s => Y i x) q U := by
          rw [hV4_def, updateSlots_apply (I := I) Y q Usec x, hUsec]
        rw [← hV1x, ← hV4x]
        rw [hBeval, hAeval, hderiv, hBcorr, hAcorr]
    _ =
      totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        s cov A x (Fin.cons (X x)
          (Function.update (fun i : Fin s => Y i x) q U)) := hAtot.symm

end DifferentialGeometry.PDE.RicciFlow
