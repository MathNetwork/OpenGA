import DifferentialGeometry.Tensor.RSTensor.ContractionLeibniz
import DifferentialGeometry.Tensor.Multilinear.DomDomCongrSection

set_option autoImplicit false
set_option linter.style.longLine false


















namespace Tensor0SBundle

set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff BigOperators
open Bundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [CompleteSpace E] [IsManifold I ∞ M]




noncomputable def leibnizRightEquiv (s q : ℕ) : Fin (s + (q + 1)) ≃ Fin (s + q + 1) :=
  (finCongr (by omega : s + (q + 1) = s + q + 1)).trans
    (Fin.cycleRange ⟨s, by omega⟩)



def leibnizLeftEquiv (s q : ℕ) : Fin (s + 1 + q) ≃ Fin (s + q + 1) :=
  finCongr (by omega)





omit [CompleteSpace E] in
theorem nabla0S_product_realizes {s q : ℕ}
    [T2Space M] [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) q)
    (nablaA : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1))
    (nablaB : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (q + 1))
    (hA : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      s cov A nablaA)
    (hB : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      q cov B nablaB) :
    TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + q) cov
      (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
        (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := s) (q := q) A B)
      (MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
          (E := TangentSpace I) (∞ : WithTop ℕ∞) (leibnizLeftEquiv s q)
          (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
            (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := s + 1) (q := q)
            nablaA B)
        + MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
          (E := TangentSpace I) (∞ : WithTop ℕ∞) (leibnizRightEquiv s q)
          (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
            (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := s) (q := q + 1)
            A nablaB)) := by
  classical
  intro X x slots
  let V : Fin (s + q) -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) :=
    fun a =>
      (ContMDiffSection.exists_eq_at_gen
        (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
        x (slots a)).choose
  have hV : ∀ a : Fin (s + q), V a x = slots a := fun a =>
    (ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
      x (slots a)).choose_spec
  have hslots : (fun a : Fin (s + q) => V a x) = slots := funext hV
  have hmain :=
    nabla0SFun_product_eval (I := I) cov A B nablaA nablaB hA hB X V x


  rw [show slots = (fun a : Fin (s + q) => V a x) from hslots.symm, hmain]

  change
    (ContinuousMultilinearMap.domDomCongr (leibnizLeftEquiv s q)
        ((MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
          (E := TangentSpace I) (n := (∞ : WithTop ℕ∞))
          (s := s + 1) (q := q) nablaA B) x))
        (Fin.cons (X x) (fun a : Fin (s + q) => V a x)) +
      (ContinuousMultilinearMap.domDomCongr (leibnizRightEquiv s q)
        ((MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
          (E := TangentSpace I) (n := (∞ : WithTop ℕ∞))
          (s := s) (q := q + 1) A nablaB) x))
        (Fin.cons (X x) (fun a : Fin (s + q) => V a x)) = _
  rw [Tensor0SSpace.domDomCongr_apply, Tensor0SSpace.domDomCongr_apply,
    tensor0SField_product_apply, tensor0SField_product_apply]
  refine congrArg₂ (· + ·)
    (congrArg₂ (· * ·) (congrArg (nablaA x) ?_) (congrArg (B x) ?_))
    (congrArg₂ (· * ·) (congrArg (A x) ?_) (congrArg (nablaB x) ?_))
  ·
    funext a
    refine Fin.cases ?_ (fun a => ?_) a
    · simp only [leibnizLeftEquiv, Function.comp_apply, finCongr_apply, Fin.cons_zero]
      rw [show (Fin.cast (by omega : s + 1 + q = s + q + 1) (Fin.castAdd q (0 : Fin (s + 1))))
            = (0 : Fin (s + q + 1)) from by
        ext; simp only [Fin.val_cast, Fin.val_castAdd, Fin.val_zero]]
      exact Fin.cons_zero _ _
    · simp only [leibnizLeftEquiv, Function.comp_apply, finCongr_apply]
      rw [show (Fin.cast (by omega : s + 1 + q = s + q + 1) (Fin.castAdd q a.succ))
            = (Fin.castAdd q a).succ from by
        ext; simp only [Fin.val_cast, Fin.val_castAdd, Fin.val_succ]]
      simp only [Fin.cons_succ]
  ·
    funext a
    simp only [leibnizLeftEquiv, finCongr_apply, Function.comp_apply]
    rw [show (Fin.cast (by omega : s + 1 + q = s + q + 1) (Fin.natAdd (s + 1) a))
          = (Fin.natAdd s a).succ from by
      ext; simp only [Fin.val_cast, Fin.val_natAdd, Fin.val_succ]; omega]
    rw [Fin.cons_succ]
  ·
    funext a
    have hidx : leibnizRightEquiv s q (Fin.castAdd (q + 1) a) = (Fin.castAdd q a).succ := by
      rw [leibnizRightEquiv, Equiv.trans_apply, finCongr_apply,
        show (Fin.cast (by omega : s + (q + 1) = s + q + 1) (Fin.castAdd (q + 1) a))
            = (⟨a, by omega⟩ : Fin (s + q + 1)) from by ext; simp,
        Fin.cycleRange_of_lt (by simp only [Fin.lt_def]; omega)]
      ext
      rw [Fin.val_add_one_of_lt (by simp only [Fin.lt_def, Fin.val_last]; omega)]
      simp [Fin.val_succ]
    simp only [Function.comp_apply, hidx, Fin.cons_succ]
  ·
    funext a
    refine Fin.cases ?_ (fun a => ?_) a
    · have hidx : leibnizRightEquiv s q (Fin.natAdd s (0 : Fin (q + 1))) = 0 := by
        rw [leibnizRightEquiv, Equiv.trans_apply, finCongr_apply,
          show (Fin.cast (by omega : s + (q + 1) = s + q + 1) (Fin.natAdd s (0 : Fin (q + 1))))
              = (⟨s, by omega⟩ : Fin (s + q + 1)) from by ext; simp,
          Fin.cycleRange_self]
      simp only [Function.comp_apply, hidx, Fin.cons_zero]
    · have hidx : leibnizRightEquiv s q (Fin.natAdd s a.succ) = (Fin.natAdd s a).succ := by
        rw [leibnizRightEquiv, Equiv.trans_apply, finCongr_apply,
          show (Fin.cast (by omega : s + (q + 1) = s + q + 1) (Fin.natAdd s a.succ))
              = (⟨s + 1 + a, by omega⟩ : Fin (s + q + 1)) from by
            ext; simp [Fin.val_succ]; omega,
          Fin.cycleRange_of_gt (by simp only [Fin.lt_def]; omega)]
        ext; simp [Fin.val_succ]; omega
      simp only [Function.comp_apply, hidx, Fin.cons_succ]

end Tensor0SBundle
