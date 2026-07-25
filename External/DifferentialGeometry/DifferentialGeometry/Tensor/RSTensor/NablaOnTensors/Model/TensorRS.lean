import DifferentialGeometry.Tensor.RSTensor.Derivation.NablaOnTensors
import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.Model.Tensor0S




namespace TensorLieDeriv

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Set IsManifold ContinuousLinearMap VectorField Filter Tensor0SBundle Function
open scoped Manifold Topology Bundle ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable (n : WithTop ℕ∞ := ⊤) [IsManifold I n M]
variable {x x₀ : M} {s : Set M}

variable [CompleteSpace 𝕜]

section ModelCovariantDerivative














omit [CompleteSpace 𝕜] in
theorem fderivWithin_tensorRSModel_eval_slots {r s : ℕ}
    (T : E → TensorRSModel r s 𝕜 E)
    (β : E → Tensor0SModel (𝕜 := 𝕜) (E := E) r)
    (V : Fin s → E → E)
    (u : Set E) (y Xy : E)
    (hT : DifferentiableWithinAt 𝕜 T u y)
    (hβ : DifferentiableWithinAt 𝕜 β u y)
    (hV : ∀ a : Fin s, DifferentiableWithinAt 𝕜 (V a) u y)
    (hu : UniqueDiffWithinAt 𝕜 u y) :
    fderivWithin 𝕜 (fun z : E => (T z (β z)) (fun a : Fin s => V a z)) u y Xy =
      ((fderivWithin 𝕜 T u y Xy) (β y)) (fun a : Fin s => V a y) +
        (T y (fderivWithin 𝕜 β u y Xy)) (fun a : Fin s => V a y) +
        ∑ a : Fin s,
          (T y (β y)) (Function.update (fun b : Fin s => V b y) a
            (fderivWithin 𝕜 (V a) u y Xy)) := by
  classical
  let α : E → Tensor0SModel (𝕜 := 𝕜) (E := E) s := fun z => T z (β z)
  have hα : DifferentiableWithinAt 𝕜 α u y := hT.clm_apply hβ
  have hslots := fderivWithin_tensor0SModel_eval_slots
    (𝕜 := 𝕜) (E := E) (s := s) α V u y Xy hα hV hu
  have hαderiv :
      fderivWithin 𝕜 α u y =
        (T y).comp (fderivWithin 𝕜 β u y) +
          (fderivWithin 𝕜 T u y).flip (β y) := by
    simpa [α] using fderivWithin_clm_apply (𝕜 := 𝕜) (s := u) (x := y) hu hT hβ
  rw [hslots, hαderiv]
  simp [α, add_assoc, add_comm]



theorem covariantDeriv_tensorRSModelWithin_eval_derivation {r s : ℕ}
    (T : E → TensorRSModel r s 𝕜 E)
    (β : E → Tensor0SModel (𝕜 := 𝕜) (E := E) r)
    (V : Fin s → E → E)
    (X : E → E) (ΓX : E → E →L[𝕜] E)
    (u : Set E) (y : E)
    (hT : DifferentiableWithinAt 𝕜 T u y)
    (hβ : DifferentiableWithinAt 𝕜 β u y)
    (hV : ∀ a : Fin s, DifferentiableWithinAt 𝕜 (V a) u y)
    (hu : UniqueDiffWithinAt 𝕜 u y) :
    (covariantDeriv_tensorRSModelWithin (𝕜 := 𝕜) (E := E)
        r s X ΓX T u y (β y)) (fun a : Fin s => V a y)
      =
        fderivWithin 𝕜
          (fun z : E => (T z (β z)) (fun a : Fin s => V a z))
          u y (X y)
        - (T y
          (covariantDeriv_tensor0SModelWithin (𝕜 := 𝕜) (E := E)
            r X ΓX β u y))
          (fun a : Fin s => V a y)
        - ∑ a : Fin s,
          (T y (β y))
            (Function.update
              (fun b : Fin s => V b y)
              a
              (fderivWithin 𝕜 (V a) u y (X y) + ΓX y (V a y))) := by
  classical
  have hprod := fderivWithin_tensorRSModel_eval_slots
    (𝕜 := 𝕜) (E := E) (r := r) (s := s)
    T β V u y (X y) hT hβ hV hu
  rw [covariantDeriv_tensorRSModelWithin]
  rw [covariantDeriv_tensorRSModelAt_eval]
  rw [hprod]
  have hβcov :
      ((T y)
        (covariantDeriv_tensor0SModelWithin (𝕜 := 𝕜) (E := E)
          r X ΓX β u y)) (fun a : Fin s => V a y) =
        ((T y) (fderivWithin 𝕜 β u y (X y))) (fun a : Fin s => V a y) -
          ((T y) ((lieDeriv_correctionL (𝕜 := 𝕜) (E := E) r (ΓX y)) (β y)))
            (fun a : Fin s => V a y) := by
    simp [covariantDeriv_tensor0SModelWithin, covariantDeriv_tensor0SModelAt,
      lieDeriv_correctionL_apply]
  have hCorrS :
      ((lieDeriv_correctionL (𝕜 := 𝕜) (E := E) s (ΓX y)) ((T y) (β y)))
          (fun a : Fin s => V a y) =
        ∑ a : Fin s,
          ((T y) (β y))
            (Function.update (fun b : Fin s => V b y) a (ΓX y (V a y))) := by
    exact lieDeriv_correctionL_apply_slots (𝕜 := 𝕜) (E := E)
      (s := s) (ΓX y) ((T y) (β y)) (fun a : Fin s => V a y)
  have hsum :
      (∑ a : Fin s,
          ((T y) (β y))
            (Function.update
              (fun b : Fin s => V b y)
              a
              (fderivWithin 𝕜 (V a) u y (X y) + ΓX y (V a y)))) =
        (∑ a : Fin s,
          ((T y) (β y))
            (Function.update
              (fun b : Fin s => V b y)
              a
              (fderivWithin 𝕜 (V a) u y (X y)))) +
        ∑ a : Fin s,
          ((T y) (β y))
            (Function.update (fun b : Fin s => V b y) a (ΓX y (V a y))) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    exact ((T y) (β y)).map_update_add
      (fun b : Fin s => V b y) a
      (fderivWithin 𝕜 (V a) u y (X y)) (ΓX y (V a y))
  rw [hβcov, hCorrS, hsum]
  abel

section ChristoffelModelRS

omit [CompleteSpace 𝕜] in
private theorem tensor0SModel_eval_update_basis_sum_modelRS {d s : ℕ}
    (basis : Module.Basis (Fin d) 𝕜 E)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) s)
    (v : Fin s → E) (i : Fin s) (w : E) :
    α (Function.update v i w) =
      ∑ k : Fin d, basis.coord k w *
        α (Function.update v i (basis k)) := by
  classical
  have hw : w = ∑ k : Fin d, basis.coord k w • basis k := by
    exact (basis.sum_repr w).symm
  calc
    α (Function.update v i w) =
        α (Function.update v i (∑ k : Fin d, basis.coord k w • basis k)) := by
      exact congrArg (fun z => α (Function.update v i z)) hw
    _ = ∑ k : Fin d,
        α (Function.update v i (basis.coord k w • basis k)) := by
      have h := α.toMultilinearMap.map_update_sum
        (Finset.univ : Finset (Fin d)) i (fun k : Fin d => basis.coord k w • basis k) v
      simpa using h
    _ = ∑ k : Fin d, basis.coord k w *
        α (Function.update v i (basis k)) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [α.map_update_smul]
      simp [smul_eq_mul]

private theorem continuousMultilinearMap_basis_apply_basis {d s : ℕ}
    (basis : Module.Basis (Fin d) 𝕜 E)
    (upper lower : Fin s → Fin d) :
    ((continuousMultilinearMap_basis (𝕜 := 𝕜) (F := E) basis s) upper)
        (fun b : Fin s => basis (lower b)) =
      if upper = lower then 1 else 0 := by
  have h := continuousMultilinearMap_basis_repr
    (𝕜 := 𝕜) (F := E) basis s
    ((continuousMultilinearMap_basis (𝕜 := 𝕜) (F := E) basis s) upper)
    lower
  simpa [Module.Basis.repr_self, Finsupp.single_apply] using h.symm

omit [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜] in
private theorem basis_coord_update_sum_comm {d r : ℕ}
    (basis : Module.Basis (Fin d) 𝕜 E)
    (ΓX : E →L[𝕜] E)
    (upper lower : Fin r → Fin d)
    (a : Fin r) :
    (∑ k : Fin d,
        basis.coord k (ΓX (basis (lower a))) *
          (if upper = Function.update lower a k then (1 : 𝕜) else 0)) =
      ∑ k : Fin d,
        basis.coord (upper a) (ΓX (basis k)) *
          (if Function.update upper a k = lower then (1 : 𝕜) else 0) := by
  classical
  by_cases hout : ∀ b : Fin r, b ≠ a → upper b = lower b
  · have hleft_update : upper = Function.update lower a (upper a) := by
      funext b
      by_cases hb : b = a
      · subst hb
        simp
      · simp [Function.update, hb, hout b hb]
    have hright_update : Function.update upper a (lower a) = lower := by
      funext b
      by_cases hb : b = a
      · subst hb
        simp
      · simp [Function.update, hb, hout b hb]
    have hleft :
        (∑ k : Fin d,
          basis.coord k (ΓX (basis (lower a))) *
            (if upper = Function.update lower a k then (1 : 𝕜) else 0)) =
          basis.coord (upper a) (ΓX (basis (lower a))) := by
      rw [Finset.sum_eq_single (upper a)]
      · rw [if_pos hleft_update]
        simp
      · intro k _ hk
        have hne : upper ≠ Function.update lower a k := by
          intro h
          have ha := congrFun h a
          simp at ha
          exact hk ha.symm
        rw [if_neg hne]
        simp
      · intro hnot
        exact False.elim (hnot (Finset.mem_univ _))
    have hright :
        (∑ k : Fin d,
          basis.coord (upper a) (ΓX (basis k)) *
            (if Function.update upper a k = lower then (1 : 𝕜) else 0)) =
          basis.coord (upper a) (ΓX (basis (lower a))) := by
      rw [Finset.sum_eq_single (lower a)]
      · rw [if_pos hright_update]
        simp
      · intro k _ hk
        have hne : Function.update upper a k ≠ lower := by
          intro h
          have ha : k = lower a := by
            simpa using congrFun h a
          exact hk ha
        rw [if_neg hne]
        simp
      · intro hnot
        exact False.elim (hnot (Finset.mem_univ _))
    rw [hleft, hright]
  · push Not at hout
    rcases hout with ⟨b, hb, hneq⟩
    have hleft_zero :
        (∑ k : Fin d,
          basis.coord k (ΓX (basis (lower a))) *
            (if upper = Function.update lower a k then (1 : 𝕜) else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      have hne : upper ≠ Function.update lower a k := by
        intro h
        have hb_eq : upper b = lower b := by
          simpa [Function.update, hb] using congrFun h b
        exact hneq hb_eq
      simp [hne]
    have hright_zero :
        (∑ k : Fin d,
          basis.coord (upper a) (ΓX (basis k)) *
            (if Function.update upper a k = lower then (1 : 𝕜) else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      have hne : Function.update upper a k ≠ lower := by
        intro h
        have hb_eq : upper b = lower b := by
          simpa [Function.update, hb] using congrFun h b
        exact hneq hb_eq
      simp [hne]
    rw [hleft_zero, hright_zero]


theorem lieDeriv_correctionL_apply_basis_slots_expanded {d s : ℕ}
    (basis : Module.Basis (Fin d) 𝕜 E)
    (ΓX : E →L[𝕜] E)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) s)
    (lower : Fin s → Fin d) :
    ((lieDeriv_correctionL (𝕜 := 𝕜) (E := E) s ΓX α)
        (fun b : Fin s => basis (lower b))) =
      ∑ b : Fin s, ∑ k : Fin d,
        connectionEndomorphismCoeff basis ΓX (lower b) k *
          α (Function.update
            (fun c : Fin s => basis (lower c))
            b
            (basis k)) := by
  classical
  rw [lieDeriv_correctionL_apply_slots]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [tensor0SModel_eval_update_basis_sum_modelRS basis α
    (fun c : Fin s => basis (lower c)) b (ΓX (basis (lower b)))]
  simp [connectionEndomorphismCoeff]








theorem lieDeriv_correctionL_apply_basisTensor0S {d r : ℕ}
    (basis : Module.Basis (Fin d) 𝕜 E)
    (ΓX : E →L[𝕜] E)
    (upper : Fin r → Fin d) :
    lieDeriv_correctionL (𝕜 := 𝕜) (E := E) r ΓX
      ((continuousMultilinearMap_basis (𝕜 := 𝕜) (F := E) basis r) upper)
    =
      ∑ a : Fin r, ∑ k : Fin d,
        connectionEndomorphismCoeff basis ΓX k (upper a) •
          ((continuousMultilinearMap_basis (𝕜 := 𝕜) (F := E) basis r)
            (Function.update upper a k)) := by
  classical
  apply (continuousMultilinearMap_basis (𝕜 := 𝕜) (F := E) basis r).repr.injective
  ext lower
  rw [continuousMultilinearMap_basis_repr]
  simp only [map_sum, map_smul, Module.Basis.repr_self]
  simp only [Finsupp.finset_sum_apply, Finsupp.smul_apply,
    Finsupp.single_apply, smul_eq_mul]
  rw [lieDeriv_correctionL_apply_slots]
  change
    (∑ a : Fin r,
      ((continuousMultilinearMap_basis (𝕜 := 𝕜) (F := E) basis r) upper)
        (Function.update (fun b : Fin r => basis (lower b)) a (ΓX (basis (lower a))))) =
    ∑ a : Fin r,
      ∑ k : Fin d,
        connectionEndomorphismCoeff basis ΓX k (upper a) *
          (if Function.update upper a k = lower then (1 : 𝕜) else 0)
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [tensor0SModel_eval_update_basis_sum_modelRS basis
    ((continuousMultilinearMap_basis (𝕜 := 𝕜) (F := E) basis r) upper)
    (fun b : Fin r => basis (lower b)) a (ΓX (basis (lower a)))]
  simp only [connectionEndomorphismCoeff]
  trans
      ∑ k : Fin d,
        basis.coord k (ΓX (basis (lower a))) *
          (if upper = Function.update lower a k then (1 : 𝕜) else 0)
  · apply Finset.sum_congr rfl
    intro k _
    congr 1
    have hslots :
        Function.update (fun b : Fin r => basis (lower b)) a (basis k) =
          fun b : Fin r => basis (Function.update lower a k b) := by
      funext b
      by_cases hb : b = a
      · subst hb
        simp
      · simp [Function.update, hb]
    rw [hslots, continuousMultilinearMap_basis_apply_basis]
  · exact basis_coord_update_sum_comm basis ΓX upper lower a



theorem covariantDeriv_tensorRSModelAt_apply_basis_slots {d r s : ℕ}
    (basis : Module.Basis (Fin d) 𝕜 E)
    (dT_X : TensorRSModel r s 𝕜 E)
    (ΓX : E →L[𝕜] E)
    (T : TensorRSModel r s 𝕜 E)
    (upper : Fin r → Fin d)
    (lower : Fin s → Fin d) :
    (covariantDeriv_tensorRSModelAt
        (𝕜 := 𝕜) (E := E) r s dT_X ΓX T
        ((continuousMultilinearMap_basis (𝕜 := 𝕜) (F := E) basis r) upper))
      (fun b : Fin s => basis (lower b))
    =
      (dT_X
        ((continuousMultilinearMap_basis (𝕜 := 𝕜) (F := E) basis r) upper))
        (fun b : Fin s => basis (lower b))
      +
      ∑ a : Fin r, ∑ k : Fin d,
        connectionEndomorphismCoeff basis ΓX k (upper a) *
          (T
            ((continuousMultilinearMap_basis (𝕜 := 𝕜) (F := E) basis r)
              (Function.update upper a k)))
            (fun b : Fin s => basis (lower b))
      -
      ∑ b : Fin s, ∑ k : Fin d,
        connectionEndomorphismCoeff basis ΓX (lower b) k *
          (T
            ((continuousMultilinearMap_basis (𝕜 := 𝕜) (F := E) basis r) upper))
            (Function.update
              (fun c : Fin s => basis (lower c))
              b
              (basis k)) := by
  classical
  rw [covariantDeriv_tensorRSModelAt_eval]
  have hupper := lieDeriv_correctionL_apply_basisTensor0S
    (𝕜 := 𝕜) (E := E) basis ΓX upper
  have hlower_expanded := lieDeriv_correctionL_apply_basis_slots_expanded
    (𝕜 := 𝕜) (E := E) basis ΓX
    (T ((continuousMultilinearMap_basis (𝕜 := 𝕜) (F := E) basis r) upper))
    lower
  rw [hupper, hlower_expanded]
  simp only [map_sum, map_smul,
    ContinuousMultilinearMap.sum_apply, ContinuousMultilinearMap.smul_apply,
    smul_eq_mul]
  abel






theorem covDerivRS_sub_apply {d r s : ℕ}
    (basis : Module.Basis (Fin d) 𝕜 E)
    (dT_X : TensorRSModel r s 𝕜 E)
    (ΓX ΓX' : E →L[𝕜] E)
    (T : TensorRSModel r s 𝕜 E)
    (upper : Fin r → Fin d)
    (lower : Fin s → Fin d) :
    ((covariantDeriv_tensorRSModelAt
          (𝕜 := 𝕜) (E := E) r s dT_X ΓX T -
        covariantDeriv_tensorRSModelAt
          (𝕜 := 𝕜) (E := E) r s dT_X ΓX' T)
        ((continuousMultilinearMap_basis (𝕜 := 𝕜) (F := E) basis r) upper))
      (fun b : Fin s => basis (lower b))
    =
      (((∑ a : Fin r, ∑ k : Fin d,
        connectionEndomorphismCoeff basis ΓX k (upper a) *
          (T
            ((continuousMultilinearMap_basis (𝕜 := 𝕜) (F := E) basis r)
              (Function.update upper a k)))
            (fun b : Fin s => basis (lower b))) -
        (∑ a : Fin r, ∑ k : Fin d,
        connectionEndomorphismCoeff basis ΓX' k (upper a) *
          (T
            ((continuousMultilinearMap_basis (𝕜 := 𝕜) (F := E) basis r)
              (Function.update upper a k)))
            (fun b : Fin s => basis (lower b))))
      -
      ((∑ b : Fin s, ∑ k : Fin d,
        connectionEndomorphismCoeff basis ΓX (lower b) k *
          (T
            ((continuousMultilinearMap_basis (𝕜 := 𝕜) (F := E) basis r) upper))
            (Function.update
              (fun c : Fin s => basis (lower c))
              b
              (basis k))) -
        (∑ b : Fin s, ∑ k : Fin d,
        connectionEndomorphismCoeff basis ΓX' (lower b) k *
          (T
            ((continuousMultilinearMap_basis (𝕜 := 𝕜) (F := E) basis r) upper))
            (Function.update
              (fun c : Fin s => basis (lower c))
              b
              (basis k))))) := by
  classical
  simp only [ContinuousLinearMap.sub_apply, ContinuousMultilinearMap.sub_apply]
  rw [covariantDeriv_tensorRSModelAt_apply_basis_slots basis dT_X ΓX T upper lower]
  rw [covariantDeriv_tensorRSModelAt_apply_basis_slots basis dT_X ΓX' T upper lower]
  abel



theorem covariantDeriv_tensorRSModelWithin_apply_basis_slots {d r s : ℕ}
    (basis : Module.Basis (Fin d) 𝕜 E)
    (X : E → E)
    (ΓX : E → E →L[𝕜] E)
    (T : E → TensorRSModel r s 𝕜 E)
    (u : Set E)
    (x : E)
    (upper : Fin r → Fin d)
    (lower : Fin s → Fin d) :
    (covariantDeriv_tensorRSModelWithin
        (𝕜 := 𝕜) (E := E) r s X ΓX T u x
        ((continuousMultilinearMap_basis (𝕜 := 𝕜) (F := E) basis r) upper))
      (fun b : Fin s => basis (lower b))
    =
      (fderivWithin 𝕜 T u x (X x)
        ((continuousMultilinearMap_basis (𝕜 := 𝕜) (F := E) basis r) upper))
        (fun b : Fin s => basis (lower b))
      +
      ∑ a : Fin r, ∑ k : Fin d,
        connectionEndomorphismCoeff basis (ΓX x) k (upper a) *
          (T x
            ((continuousMultilinearMap_basis (𝕜 := 𝕜) (F := E) basis r)
              (Function.update upper a k)))
            (fun b : Fin s => basis (lower b))
      -
      ∑ b : Fin s, ∑ k : Fin d,
        connectionEndomorphismCoeff basis (ΓX x) (lower b) k *
          (T x
            ((continuousMultilinearMap_basis (𝕜 := 𝕜) (F := E) basis r) upper))
            (Function.update
              (fun c : Fin s => basis (lower c))
              b
              (basis k)) := by
  unfold covariantDeriv_tensorRSModelWithin
  exact covariantDeriv_tensorRSModelAt_apply_basis_slots
    (𝕜 := 𝕜) (E := E) basis
    (fderivWithin 𝕜 T u x (X x)) (ΓX x) (T x) upper lower

end ChristoffelModelRS

end ModelCovariantDerivative

end

end TensorLieDeriv
