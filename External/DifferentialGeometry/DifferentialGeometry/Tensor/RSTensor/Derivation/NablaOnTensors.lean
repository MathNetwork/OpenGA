import DifferentialGeometry.Tensor.RSTensor.Derivation.LieDerivative
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic


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

def covariantDeriv_tensor0SModelAt (s : ℕ)
    (dα_X : Tensor0SModel (𝕜 := 𝕜) (E := E) s) (ΓX : E →L[𝕜] E)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) s) :
    Tensor0SModel (𝕜 := 𝕜) (E := E) s :=
  dα_X - lieDeriv_correction s ΓX α

omit [CompleteSpace 𝕜] in
@[simp] lemma covariantDeriv_tensor0SModelAt_apply (s : ℕ)
    (dα_X : Tensor0SModel (𝕜 := 𝕜) (E := E) s) (ΓX : E →L[𝕜] E)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) s) :
    covariantDeriv_tensor0SModelAt (𝕜 := 𝕜) (E := E) s dα_X ΓX α =
      dα_X - lieDeriv_correction s ΓX α := by
  rfl

def covariantDeriv_tensor0SModel (s : ℕ)
    (X : E → E) (ΓX : E → E →L[𝕜] E)
    (α : E → Tensor0SModel (𝕜 := 𝕜) (E := E) s) (x : E) :
    Tensor0SModel (𝕜 := 𝕜) (E := E) s :=
  covariantDeriv_tensor0SModelAt (𝕜 := 𝕜) (E := E) s
    (fderiv 𝕜 α x (X x)) (ΓX x) (α x)

def covariantDeriv_tensor0SModelWithin (s : ℕ)
    (X : E → E) (ΓX : E → E →L[𝕜] E)
    (α : E → Tensor0SModel (𝕜 := 𝕜) (E := E) s) (u : Set E) (x : E) :
    Tensor0SModel (𝕜 := 𝕜) (E := E) s :=
  covariantDeriv_tensor0SModelAt (𝕜 := 𝕜) (E := E) s
    (fderivWithin 𝕜 α u x (X x)) (ΓX x) (α x)

def covariantDeriv_tensorRSModelAt (r s : ℕ)
    (dT_X : TensorRSModel r s 𝕜 E) (ΓX : E →L[𝕜] E)
    (T : TensorRSModel r s 𝕜 E) :
    TensorRSModel r s 𝕜 E :=
  dT_X
    - (lieDeriv_correctionL (𝕜 := 𝕜) (E := E) s ΓX).comp T
    + T.comp (lieDeriv_correctionL (𝕜 := 𝕜) (E := E) r ΓX)

@[simp] theorem covariantDeriv_tensorRSModelAt_apply (r s : ℕ)
    (dT_X : TensorRSModel r s 𝕜 E) (ΓX : E →L[𝕜] E)
    (T : TensorRSModel r s 𝕜 E) :
    covariantDeriv_tensorRSModelAt (𝕜 := 𝕜) (E := E) r s dT_X ΓX T =
      dT_X
        - (lieDeriv_correctionL (𝕜 := 𝕜) (E := E) s ΓX).comp T
        + T.comp (lieDeriv_correctionL (𝕜 := 𝕜) (E := E) r ΓX) := by
  rfl

theorem covariantDeriv_tensorRSModelAt_eval (r s : ℕ)
    (dT_X : TensorRSModel r s 𝕜 E) (ΓX : E →L[𝕜] E)
    (T : TensorRSModel r s 𝕜 E)
    (β : Tensor0SModel (𝕜 := 𝕜) (E := E) r) (v : Fin s → E) :
    (covariantDeriv_tensorRSModelAt (𝕜 := 𝕜) (E := E) r s dT_X ΓX T β) v =
      (dT_X β) v -
        ((lieDeriv_correctionL (𝕜 := 𝕜) (E := E) s ΓX) (T β)) v +
        (T ((lieDeriv_correctionL (𝕜 := 𝕜) (E := E) r ΓX) β)) v := by
  simp [covariantDeriv_tensorRSModelAt, sub_eq_add_neg, add_assoc]

section ChristoffelModel

variable {Idx : Type*} [Fintype Idx]

def connectionEndomorphismCoeff
    (basis : Module.Basis Idx 𝕜 E) (ΓX : E →L[𝕜] E)
    (j k : Idx) : 𝕜 :=
  basis.coord k (ΓX (basis j))

omit [CompleteSpace 𝕜] in
private theorem tensor0SModel_eval_update_basis_sum {s : ℕ}
    (basis : Module.Basis Idx 𝕜 E)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) s)
    (v : Fin s → E) (i : Fin s) (w : E) :
    α (Function.update v i w) =
      ∑ k : Idx, basis.coord k w *
        α (Function.update v i (basis k)) := by
  classical
  have hw : w = ∑ k : Idx, basis.coord k w • basis k := by
    exact (basis.sum_repr w).symm
  calc
    α (Function.update v i w) =
        α (Function.update v i (∑ k : Idx, basis.coord k w • basis k)) := by
      exact congrArg (fun z => α (Function.update v i z)) hw
    _ = ∑ k : Idx,
        α (Function.update v i (basis.coord k w • basis k)) := by
      have h := α.toMultilinearMap.map_update_sum
        (Finset.univ : Finset Idx) i (fun k : Idx => basis.coord k w • basis k) v
      simpa using h
    _ = ∑ k : Idx, basis.coord k w *
        α (Function.update v i (basis k)) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [α.map_update_smul]
      simp [smul_eq_mul]

omit [CompleteSpace 𝕜] in
private theorem tensor0SModel_one_eval_basis_sum
    (basis : Module.Basis Idx 𝕜 E)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) 1) (v : E) :
    α (fun _ : Fin 1 => v) =
      ∑ k : Idx, basis.coord k v * α (fun _ : Fin 1 => basis k) := by
  have hupdate (w : E) :
      Function.update (fun _ : Fin 1 => v) (0 : Fin 1) w =
        fun _ : Fin 1 => w := by
    funext q
    fin_cases q
    simp
  have h := tensor0SModel_eval_update_basis_sum basis α
    (fun _ : Fin 1 => v) (0 : Fin 1) v
  simpa [hupdate] using h

omit [CompleteSpace 𝕜] in
private theorem tensor0SModel_two_eval_first_basis_sum
    (basis : Module.Basis Idx 𝕜 E)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) 2) (v w : E) :
    α (fun q : Fin 2 => if q = 0 then v else w) =
      ∑ k : Idx, basis.coord k v *
        α (fun q : Fin 2 => if q = 0 then basis k else w) := by
  let base : Fin 2 → E := fun q => if q = 0 then v else w
  have hupdate (z : E) :
      Function.update base (0 : Fin 2) z =
        fun q : Fin 2 => if q = 0 then z else w := by
    funext q
    fin_cases q <;> simp [base]
  have h := tensor0SModel_eval_update_basis_sum basis α base (0 : Fin 2) v
  have hbase : Function.update base (0 : Fin 2) v = base := by
    funext q
    fin_cases q <;> simp [base]
  simpa [hbase, hupdate] using h

omit [CompleteSpace 𝕜] in
private theorem tensor0SModel_two_eval_second_basis_sum
    (basis : Module.Basis Idx 𝕜 E)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) 2) (v w : E) :
    α (fun q : Fin 2 => if q = 0 then v else w) =
      ∑ k : Idx, basis.coord k w *
        α (fun q : Fin 2 => if q = 0 then v else basis k) := by
  let base : Fin 2 → E := fun q => if q = 0 then v else w
  have hupdate (z : E) :
      Function.update base (1 : Fin 2) z =
        fun q : Fin 2 => if q = 0 then v else z := by
    funext q
    fin_cases q <;> simp [base]
  have h := tensor0SModel_eval_update_basis_sum basis α base (1 : Fin 2) w
  have hbase : Function.update base (1 : Fin 2) w = base := by
    funext q
    fin_cases q <;> simp [base]
  simpa [hbase, hupdate] using h

omit [CompleteSpace 𝕜] in
theorem covariantDeriv_tensor0SModelAt_apply_basis_slots {s : ℕ}
    (basis : Module.Basis Idx 𝕜 E)
    (dα_X : Tensor0SModel (𝕜 := 𝕜) (E := E) s)
    (ΓX : E →L[𝕜] E)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) s)
    (slots : Fin s → Idx) :
    covariantDeriv_tensor0SModelAt (𝕜 := 𝕜) (E := E) s dα_X ΓX α
        (fun a : Fin s => basis (slots a)) =
      dα_X (fun a : Fin s => basis (slots a)) -
        ∑ a : Fin s, ∑ k : Idx,
          connectionEndomorphismCoeff basis ΓX (slots a) k *
            α (Function.update (fun b : Fin s => basis (slots b)) a (basis k)) := by
  classical
  unfold covariantDeriv_tensor0SModelAt lieDeriv_correction substituteArg
    connectionEndomorphismCoeff
  simp only [ContinuousMultilinearMap.sub_apply, ContinuousMultilinearMap.sum_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  have hslot :
      α (fun b : Fin s =>
          (if b = a then ΓX else ContinuousLinearMap.id 𝕜 E) (basis (slots b))) =
        α (Function.update (fun b : Fin s => basis (slots b)) a (ΓX (basis (slots a)))) := by
    congr 1
    funext b
    by_cases hb : b = a
    · subst hb
      simp
    · simp [Function.update, hb]
  rw [hslot]
  exact tensor0SModel_eval_update_basis_sum basis α
    (fun b : Fin s => basis (slots b)) a (ΓX (basis (slots a)))

omit [CompleteSpace 𝕜] in
theorem covariantDeriv_tensor0SModelWithin_apply_basis_slots {s : ℕ}
    (basis : Module.Basis Idx 𝕜 E)
    (X : E → E) (ΓX : E → E →L[𝕜] E)
    (α : E → Tensor0SModel (𝕜 := 𝕜) (E := E) s)
    (u : Set E) (x : E) (slots : Fin s → Idx) :
    covariantDeriv_tensor0SModelWithin (𝕜 := 𝕜) (E := E) s X ΓX α u x
        (fun a : Fin s => basis (slots a)) =
      fderivWithin 𝕜 α u x (X x) (fun a : Fin s => basis (slots a)) -
        ∑ a : Fin s, ∑ k : Idx,
          connectionEndomorphismCoeff basis (ΓX x) (slots a) k *
            α x (Function.update (fun b : Fin s => basis (slots b)) a (basis k)) := by
  unfold covariantDeriv_tensor0SModelWithin
  exact covariantDeriv_tensor0SModelAt_apply_basis_slots (𝕜 := 𝕜) (E := E)
    basis (fderivWithin 𝕜 α u x (X x)) (ΓX x) (α x) slots

omit [CompleteSpace 𝕜] in
theorem covariantDeriv_tensor0SModelAt_one_apply_basis
    (basis : Module.Basis Idx 𝕜 E)
    (dα_X : Tensor0SModel (𝕜 := 𝕜) (E := E) 1)
    (ΓX : E →L[𝕜] E)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) 1)
    (j : Idx) :
    covariantDeriv_tensor0SModelAt (𝕜 := 𝕜) (E := E) 1 dα_X ΓX α
        (fun _ : Fin 1 => basis j) =
      dα_X (fun _ : Fin 1 => basis j) -
        ∑ k : Idx, connectionEndomorphismCoeff basis ΓX j k *
          α (fun _ : Fin 1 => basis k) := by
  unfold covariantDeriv_tensor0SModelAt lieDeriv_correction substituteArg
    connectionEndomorphismCoeff
  simp only [ContinuousMultilinearMap.sub_apply,
    Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have hcorr :
      α (fun i : Fin 1 =>
        (if i = 0 then ΓX else ContinuousLinearMap.id 𝕜 E) (basis j)) =
        α (fun _ : Fin 1 => ΓX (basis j)) := by
    congr 1
    funext q
    fin_cases q
    simp
  rw [hcorr]
  rw [tensor0SModel_one_eval_basis_sum basis α (ΓX (basis j))]

omit [CompleteSpace 𝕜] in
theorem covariantDeriv_tensor0SModelAt_two_apply_basis
    (basis : Module.Basis Idx 𝕜 E)
    (dA_X : Tensor0SModel (𝕜 := 𝕜) (E := E) 2)
    (ΓX : E →L[𝕜] E)
    (A : Tensor0SModel (𝕜 := 𝕜) (E := E) 2)
    (j l : Idx) :
    covariantDeriv_tensor0SModelAt (𝕜 := 𝕜) (E := E) 2 dA_X ΓX A
        (fun q : Fin 2 => if q = 0 then basis j else basis l) =
      dA_X (fun q : Fin 2 => if q = 0 then basis j else basis l) -
        ∑ k : Idx, connectionEndomorphismCoeff basis ΓX j k *
          A (fun q : Fin 2 => if q = 0 then basis k else basis l) -
        ∑ k : Idx, connectionEndomorphismCoeff basis ΓX l k *
          A (fun q : Fin 2 => if q = 0 then basis j else basis k) := by
  unfold covariantDeriv_tensor0SModelAt lieDeriv_correction substituteArg
    connectionEndomorphismCoeff
  simp only [ContinuousMultilinearMap.sub_apply, ContinuousMultilinearMap.sum_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have hfin :
      (∑ i : Fin 2,
          A (fun j_1 : Fin 2 =>
            (if j_1 = i then ΓX else ContinuousLinearMap.id 𝕜 E)
              ((fun q : Fin 2 => if q = 0 then basis j else basis l) j_1))) =
        A (fun q : Fin 2 => if q = 0 then ΓX (basis j) else basis l) +
          A (fun q : Fin 2 => if q = 0 then basis j else ΓX (basis l)) := by
    rw [Fin.sum_univ_two]
    congr 1
    · congr 1
      funext q
      fin_cases q <;> simp
    · congr 1
      funext q
      fin_cases q <;> simp
  rw [hfin]
  rw [tensor0SModel_two_eval_first_basis_sum basis A (ΓX (basis j)) (basis l)]
  rw [tensor0SModel_two_eval_second_basis_sum basis A (basis j) (ΓX (basis l))]
  abel

omit [CompleteSpace 𝕜] in
theorem covariantDeriv_tensor0SModelWithin_one_apply_basis
    (basis : Module.Basis Idx 𝕜 E)
    (X : E → E) (ΓX : E → E →L[𝕜] E)
    (α : E → Tensor0SModel (𝕜 := 𝕜) (E := E) 1)
    (u : Set E) (x : E) (j : Idx) :
    covariantDeriv_tensor0SModelWithin (𝕜 := 𝕜) (E := E) 1 X ΓX α u x
        (fun _ : Fin 1 => basis j) =
      fderivWithin 𝕜 α u x (X x) (fun _ : Fin 1 => basis j) -
        ∑ k : Idx, connectionEndomorphismCoeff basis (ΓX x) j k *
          α x (fun _ : Fin 1 => basis k) := by
  unfold covariantDeriv_tensor0SModelWithin
  exact covariantDeriv_tensor0SModelAt_one_apply_basis (𝕜 := 𝕜) (E := E)
    basis (fderivWithin 𝕜 α u x (X x)) (ΓX x) (α x) j

omit [CompleteSpace 𝕜] in
theorem covariantDeriv_tensor0SModelWithin_two_apply_basis
    (basis : Module.Basis Idx 𝕜 E)
    (X : E → E) (ΓX : E → E →L[𝕜] E)
    (A : E → Tensor0SModel (𝕜 := 𝕜) (E := E) 2)
    (u : Set E) (x : E) (j l : Idx) :
    covariantDeriv_tensor0SModelWithin (𝕜 := 𝕜) (E := E) 2 X ΓX A u x
        (fun q : Fin 2 => if q = 0 then basis j else basis l) =
      fderivWithin 𝕜 A u x (X x)
          (fun q : Fin 2 => if q = 0 then basis j else basis l) -
        ∑ k : Idx, connectionEndomorphismCoeff basis (ΓX x) j k *
          A x (fun q : Fin 2 => if q = 0 then basis k else basis l) -
        ∑ k : Idx, connectionEndomorphismCoeff basis (ΓX x) l k *
          A x (fun q : Fin 2 => if q = 0 then basis j else basis k) := by
  unfold covariantDeriv_tensor0SModelWithin
  exact covariantDeriv_tensor0SModelAt_two_apply_basis (𝕜 := 𝕜) (E := E)
    basis (fderivWithin 𝕜 A u x (X x)) (ΓX x) (A x) j l

omit [CompleteSpace 𝕜] in
theorem covariantDeriv_tensor0SModelWithin_one_apply_basis_clm
    (basis : Module.Basis Idx 𝕜 E)
    (X : E → E) (ΓX : E → E →L[𝕜] E)
    (α : E → ContinuousMultilinearMap 𝕜 (fun _ : Fin 1 => E) 𝕜)
    (u : Set E) (x : E) (j : Idx) :
    covariantDeriv_tensor0SModelWithin (𝕜 := 𝕜) (E := E) 1 X ΓX α u x
        (fun _ : Fin 1 => basis j) =
      fderivWithin 𝕜 α u x (X x) (fun _ : Fin 1 => basis j) -
        ∑ k : Idx, connectionEndomorphismCoeff basis (ΓX x) j k *
          α x (fun _ : Fin 1 => basis k) := by
  exact covariantDeriv_tensor0SModelWithin_one_apply_basis (𝕜 := 𝕜) (E := E)
    basis X ΓX α u x j

omit [CompleteSpace 𝕜] in
theorem covariantDeriv_tensor0SModelWithin_two_apply_basis_clm
    (basis : Module.Basis Idx 𝕜 E)
    (X : E → E) (ΓX : E → E →L[𝕜] E)
    (A : E → ContinuousMultilinearMap 𝕜 (fun _ : Fin 2 => E) 𝕜)
    (u : Set E) (x : E) (j l : Idx) :
    covariantDeriv_tensor0SModelWithin (𝕜 := 𝕜) (E := E) 2 X ΓX A u x
        (fun q : Fin 2 => if q = 0 then basis j else basis l) =
      fderivWithin 𝕜 A u x (X x)
          (fun q : Fin 2 => if q = 0 then basis j else basis l) -
        ∑ k : Idx, connectionEndomorphismCoeff basis (ΓX x) j k *
          A x (fun q : Fin 2 => if q = 0 then basis k else basis l) -
        ∑ k : Idx, connectionEndomorphismCoeff basis (ΓX x) l k *
          A x (fun q : Fin 2 => if q = 0 then basis j else basis k) := by
  exact covariantDeriv_tensor0SModelWithin_two_apply_basis (𝕜 := 𝕜) (E := E)
    basis X ΓX A u x j l

end ChristoffelModel

def covariantDeriv_tensorRSModel (r s : ℕ)
    (X : E → E) (ΓX : E → E →L[𝕜] E)
    (T : E → TensorRSModel r s 𝕜 E) (x : E) :
    TensorRSModel r s 𝕜 E :=
  covariantDeriv_tensorRSModelAt (𝕜 := 𝕜) (E := E) r s
    (fderiv 𝕜 T x (X x)) (ΓX x) (T x)

def covariantDeriv_tensorRSModelWithin (r s : ℕ)
    (X : E → E) (ΓX : E → E →L[𝕜] E)
    (T : E → TensorRSModel r s 𝕜 E) (u : Set E) (x : E) :
    TensorRSModel r s 𝕜 E :=
  covariantDeriv_tensorRSModelAt (𝕜 := 𝕜) (E := E) r s
    (fderivWithin 𝕜 T u x (X x)) (ΓX x) (T x)

omit [CompleteSpace 𝕜] in
lemma covariantSlotCorrection_modelProduct (s q : ℕ) (ΓX : E →L[𝕜] E)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) s)
    (β : Tensor0SModel (𝕜 := 𝕜) (E := E) q) :
    lieDeriv_correction (s + q) ΓX
        (Bundle.continuousMultilinearMap.modelProduct s q α β) =
      Bundle.continuousMultilinearMap.modelProduct s q
          (lieDeriv_correction s ΓX α) β +
        Bundle.continuousMultilinearMap.modelProduct s q
          α (lieDeriv_correction q ΓX β) :=
  lieDeriv_correction_modelProduct (𝕜 := 𝕜) (E := E) s q ΓX α β

end ModelCovariantDerivative

section TangentCovariantDerivative

variable [IsManifold I 1 M]

def covariantDeriv_vectorField
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X Y : (x : M) → TangentSpace I x) (x : M) :
    TangentSpace I x :=
  cov Y x (X x)

omit [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜] in
@[simp] lemma covariantDeriv_vectorField_apply
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X Y : (x : M) → TangentSpace I x) (x : M) :
    covariantDeriv_vectorField (I := I) cov X Y x = cov Y x (X x) := by
  rfl

noncomputable def tangentConstInChart (x₀ : M) (v : E) (p : M) :
    TangentSpace I p :=
  (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 p v

omit [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜] in
@[simp] lemma tangentConstInChart_apply (x₀ : M) (v : E) (p : M) :
    tangentConstInChart (𝕜 := 𝕜) (I := I) x₀ v p =
      (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 p v := by
  rfl

omit [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜] in
lemma tangentConstInChart_add (x₀ : M) (v w : E) :
    (tangentConstInChart x₀ (v + w) : (p : M) → TangentSpace I p) =
      (tangentConstInChart x₀ v : (p : M) → TangentSpace I p) +
        tangentConstInChart x₀ w := by
  funext p
  change (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 p (v + w) =
    (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 p v +
      (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 p w
  exact map_add _ _ _

omit [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜] in
lemma tangentConstInChart_smul (x₀ : M) (a : 𝕜) (v : E) :
    (tangentConstInChart x₀ (a • v) : (p : M) → TangentSpace I p) =
      a • (tangentConstInChart x₀ v : (p : M) → TangentSpace I p) := by
  funext p
  change (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 p (a • v) =
    a • (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 p v
  exact map_smul _ _ _

section ConnectionEndomorphism

variable [IsManifold I 2 M]

omit [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜] in
lemma mdifferentiableAt_tangentConstInChart_of_mem
    {x₀ p : M} (v : E)
    (hp : p ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    MDiffAt (T% (tangentConstInChart x₀ v : (p : M) → TangentSpace I p)) p := by
  let e := trivializationAt E (TangentSpace I) x₀
  refine (e.mdifferentiableAt_section_iff I
    (tangentConstInChart x₀ v : (p : M) → TangentSpace I p) hp).mpr ?_
  have hconst :
      (fun y : M =>
        (e ((T% (tangentConstInChart x₀ v : (p : M) → TangentSpace I p)) y)).2) =ᶠ[𝓝 p]
          fun _ : M => v := by
    filter_upwards [e.open_baseSet.mem_nhds hp] with y hy
    have hcoe : ⇑(e.linearMapAt 𝕜 y) = fun z => (e ⟨y, z⟩).2 :=
      e.coe_linearMapAt_of_mem (R := 𝕜) hy
    simpa [Bundle.Trivialization.continuousLinearMapAt_apply, hcoe] using
      (e.continuousLinearMapAt_symmL (R := 𝕜) hy v)
  exact hconst.mdifferentiableAt_iff.mpr mdifferentiableAt_const

noncomputable def connectionEndomorphismInChart
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : (x : M) → TangentSpace I x) (x₀ : M) (y : E) :
    E →L[𝕜] E := by
  classical
  let e := trivializationAt E (TangentSpace I) x₀
  let p := (extChartAt I x₀).symm y
  refine LinearMap.toContinuousLinearMap ?_
  refine
    { toFun := fun v =>
        if y ∈ (extChartAt I x₀).target then
          e.continuousLinearMapAt 𝕜 p
            ((cov (tangentConstInChart x₀ v) p) (X p))
        else
          0
      map_add' := ?_
      map_smul' := ?_ }
  · intro v w
    by_cases hy : y ∈ (extChartAt I x₀).target
    · have hp_source : p ∈ (extChartAt I x₀).source := (extChartAt I x₀).map_target hy
      have hp_base : p ∈ e.baseSet := by
        simpa [e, p, TangentBundle.trivializationAt_baseSet, extChartAt_source] using hp_source
      have hv : MDiffAt
          (T% (tangentConstInChart x₀ v : (p : M) → TangentSpace I p)) p :=
        mdifferentiableAt_tangentConstInChart_of_mem
          (x₀ := x₀) (p := p) v hp_base
      have hw : MDiffAt
          (T% (tangentConstInChart x₀ w : (p : M) → TangentSpace I p)) p :=
        mdifferentiableAt_tangentConstInChart_of_mem
          (x₀ := x₀) (p := p) w hp_base
      have hsection :
          (tangentConstInChart x₀ (v + w) : (p : M) → TangentSpace I p) =
            (tangentConstInChart x₀ v : (p : M) → TangentSpace I p) +
              tangentConstInChart x₀ w :=
        tangentConstInChart_add x₀ v w
      have hcov :
          cov ((tangentConstInChart x₀ v : (p : M) → TangentSpace I p) +
              tangentConstInChart x₀ w) p =
            cov (tangentConstInChart x₀ v) p +
              cov (tangentConstInChart x₀ w) p :=
        cov.isCovariantDerivativeOnUniv.add hv hw
      rw [if_pos hy, if_pos hy, if_pos hy]
      rw [hsection, hcov]
      simp [map_add]
    · rw [if_neg hy, if_neg hy, if_neg hy]
      simp
  · intro a v
    by_cases hy : y ∈ (extChartAt I x₀).target
    · have hp_source : p ∈ (extChartAt I x₀).source := (extChartAt I x₀).map_target hy
      have hp_base : p ∈ e.baseSet := by
        simpa [e, p, TangentBundle.trivializationAt_baseSet, extChartAt_source] using hp_source
      have hv : MDiffAt
          (T% (tangentConstInChart x₀ v : (p : M) → TangentSpace I p)) p :=
        mdifferentiableAt_tangentConstInChart_of_mem
          (x₀ := x₀) (p := p) v hp_base
      have hsection :
          (tangentConstInChart x₀ (a • v) : (p : M) → TangentSpace I p) =
            a • (tangentConstInChart x₀ v : (p : M) → TangentSpace I p) :=
        tangentConstInChart_smul x₀ a v
      have hcov :
          cov (a • (tangentConstInChart x₀ v : (p : M) → TangentSpace I p)) p =
            a • cov (tangentConstInChart x₀ v) p :=
        cov.isCovariantDerivativeOnUniv.smul_const a hv
      rw [if_pos hy, if_pos hy]
      rw [hsection, hcov]
      simp [map_smul]
    · rw [if_neg hy, if_neg hy]
      simp

@[simp] lemma connectionEndomorphismInChart_apply_of_mem
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : (x : M) → TangentSpace I x) (x₀ : M) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) (v : E) :
    connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov X x₀ y v =
      (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt 𝕜
        ((extChartAt I x₀).symm y)
        ((cov (tangentConstInChart x₀ v)
          ((extChartAt I x₀).symm y))
          (X ((extChartAt I x₀).symm y))) := by
  classical
  change (if y ∈ (extChartAt I x₀).target then
      (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt 𝕜
        ((extChartAt I x₀).symm y)
        ((cov (tangentConstInChart x₀ v) ((extChartAt I x₀).symm y))
          (X ((extChartAt I x₀).symm y)))
    else 0) =
      (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt 𝕜
        ((extChartAt I x₀).symm y)
        ((cov (tangentConstInChart x₀ v) ((extChartAt I x₀).symm y))
          (X ((extChartAt I x₀).symm y)))
  rw [if_pos hy]

@[simp] lemma connectionEndomorphismInChart_apply_of_notMem
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : (x : M) → TangentSpace I x) (x₀ : M) {y : E}
    (hy : y ∉ (extChartAt I x₀).target) (v : E) :
    connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov X x₀ y v = 0 := by
  classical
  change (if y ∈ (extChartAt I x₀).target then
      (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt 𝕜
        ((extChartAt I x₀).symm y)
        ((cov (tangentConstInChart x₀ v) ((extChartAt I x₀).symm y))
          (X ((extChartAt I x₀).symm y)))
    else 0) = 0
  rw [if_neg hy]

end ConnectionEndomorphism

end TangentCovariantDerivative

section SmoothVectorFieldRSNabla

variable [IsManifold I 1 M] [IsManifold I (n + 1) M]

noncomputable def tensor0SModelAt (s : ℕ) (x₀ x : M)
    (A : Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s x) :
    Tensor0SModel (𝕜 := 𝕜) (E := E) s :=
  ((trivializationAt (Tensor0SModel (𝕜 := 𝕜) (E := E) s)
      (Bundle.continuousMultilinearMap 𝕜 s E (TangentSpace I : M → Type _)) x₀)
    ⟨x, A⟩).2

omit [CompleteSpace 𝕜] in
theorem tensor0SModelAt_trivializationAt_symm (s : ℕ) (x₀ : M)
    (T : Tensor0SModel (𝕜 := 𝕜) (E := E) s) :
    tensor0SModelAt (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s x₀ x₀
        ((trivializationAt (Tensor0SModel (𝕜 := 𝕜) (E := E) s)
          (Bundle.continuousMultilinearMap 𝕜 s E (TangentSpace I : M → Type _)) x₀).symm
          x₀ T) = T := by
  unfold tensor0SModelAt
  exact congrArg Prod.snd
    ((trivializationAt (Tensor0SModel (𝕜 := 𝕜) (E := E) s)
      (Bundle.continuousMultilinearMap 𝕜 s E (TangentSpace I : M → Type _)) x₀).apply_mk_symm
        (mem_baseSet_trivializationAt (Tensor0SModel (𝕜 := 𝕜) (E := E) s)
          (Bundle.continuousMultilinearMap 𝕜 s E (TangentSpace I : M → Type _)) x₀)
        T)

noncomputable def tensor0SModelInChart (s : ℕ) (x₀ : M)
    (A : (x : M) →
      Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s x)
    (y : E) : Tensor0SModel (𝕜 := 𝕜) (E := E) s :=
  tensor0SModelAt (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
    s x₀ ((extChartAt I x₀).symm y) (A ((extChartAt I x₀).symm y))

omit [IsManifold I n M] [CompleteSpace 𝕜] [IsManifold I (n + 1) M] in
theorem tensor0SModelInChart_contMDiffWithinAt (s : ℕ) (x₀ : M)
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := n) s) :
    ContMDiffWithinAt 𝓘(𝕜, E) 𝓘(𝕜, Tensor0SModel (𝕜 := 𝕜) (E := E) s) n
      (tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H)
        (I := I) (M := M) s x₀ (fun x => α x))
      (((extChartAt I x₀).symm ⁻¹' Set.univ) ∩ Set.range I)
      (extChartAt I x₀ x₀) := by
  let S : Set E := ((extChartAt I x₀).symm ⁻¹' Set.univ) ∩ Set.range I
  have hα_model :
      ContMDiffAt I 𝓘(𝕜, Tensor0SModel (𝕜 := 𝕜) (E := E) s) n
        (fun x : M =>
          tensor0SModelAt (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
            s x₀ x (α x)) x₀ := by
    have h := α.contMDiff x₀
    rw [contMDiffAt_section] at h
    simpa [tensor0SModelAt] using h
  have hsymm :
      ContMDiffWithinAt 𝓘(𝕜, E) I n (extChartAt I x₀).symm S
        (extChartAt I x₀ x₀) := by
    simpa [S] using
      contMDiffWithinAt_extChartAt_symm_range_self (I := I) (n := n) x₀
  have hα_model_center :
      ContMDiffAt I 𝓘(𝕜, Tensor0SModel (𝕜 := 𝕜) (E := E) s) n
        (fun x : M =>
          tensor0SModelAt (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
            s x₀ x (α x))
        ((extChartAt I x₀).symm (extChartAt I x₀ x₀)) := by
    simpa [extChartAt_to_inv] using hα_model
  have hcomp := ContMDiffAt.comp_contMDiffWithinAt
    (I := 𝓘(𝕜, E)) (I' := I)
    (I'' := 𝓘(𝕜, Tensor0SModel (𝕜 := 𝕜) (E := E) s))
    (x := extChartAt I x₀ x₀) hα_model_center hsymm
  simpa [S, tensor0SModelInChart, Function.comp] using hcomp

noncomputable def mcovariantDeriv_tensor0SWithin (s : ℕ)
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (ΓX : E → E →L[𝕜] E)
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) s)
    (u : Set M) (x₀ : M) : Tensor0SSpace s I x₀ := by
  let X' := mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm X (range I)
  let α' : E → Tensor0SModel (𝕜 := 𝕜) (E := E) s :=
    tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      s x₀ (fun x => α x)
  exact
    (trivializationAt (Tensor0SModel (𝕜 := 𝕜) (E := E) s)
      (Bundle.continuousMultilinearMap 𝕜 s E (TangentSpace I : M → Type _)) x₀).symm
        x₀
      (covariantDeriv_tensor0SModelWithin s X' ΓX α'
        ((extChartAt I x₀).symm ⁻¹' u ∩ range I)
        (extChartAt I x₀ x₀))

omit [IsManifold I n M] [IsManifold I (n + 1) M] [CompleteSpace 𝕜] in
theorem mcovariantDeriv_tensor0SWithin_one_apply_basis
    {Idx : Type*} [Fintype Idx]
    (basis : Module.Basis Idx 𝕜 E)
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (ΓX : E → E →L[𝕜] E)
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := n) 1)
    (u : Set M) (x₀ : M) (j : Idx) :
    (tensor0SModelAt (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        1 x₀ x₀
        (mcovariantDeriv_tensor0SWithin (𝕜 := 𝕜) (E := E) (H := H)
          (I := I) (M := M) (n := n) 1 X ΓX α u x₀))
        (fun _ : Fin 1 => basis j) =
      fderivWithin 𝕜
          (fun y =>
            tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H)
              (I := I) (M := M) 1 x₀ (fun x => α x) y)
          (((extChartAt I x₀).symm ⁻¹' u) ∩ range I)
          (extChartAt I x₀ x₀)
          (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
            X (range I) (extChartAt I x₀ x₀))
          (fun _ : Fin 1 => basis j) -
        ∑ k : Idx,
          connectionEndomorphismCoeff basis (ΓX (extChartAt I x₀ x₀)) j k *
            (tensor0SModelAt (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
              1 x₀ x₀ (α x₀)) (fun _ : Fin 1 => basis k) := by
  classical
  unfold mcovariantDeriv_tensor0SWithin
  rw [tensor0SModelAt_trivializationAt_symm]
  rw [covariantDeriv_tensor0SModelWithin_one_apply_basis_clm (basis := basis)]
  simp only [tensor0SModelInChart]
  rw [extChartAt_to_inv]
  rfl

omit [IsManifold I n M] [IsManifold I (n + 1) M] [CompleteSpace 𝕜] in
theorem mcovariantDeriv_tensor0SWithin_two_apply_basis
    {Idx : Type*} [Fintype Idx]
    (basis : Module.Basis Idx 𝕜 E)
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (ΓX : E → E →L[𝕜] E)
    (A : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := n) 2)
    (u : Set M) (x₀ : M) (j l : Idx) :
    (tensor0SModelAt (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        2 x₀ x₀
        (mcovariantDeriv_tensor0SWithin (𝕜 := 𝕜) (E := E) (H := H)
          (I := I) (M := M) (n := n) 2 X ΓX A u x₀))
        (fun q : Fin 2 => if q = 0 then basis j else basis l) =
      fderivWithin 𝕜
          (fun y =>
            tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H)
              (I := I) (M := M) 2 x₀ (fun x => A x) y)
          (((extChartAt I x₀).symm ⁻¹' u) ∩ range I)
          (extChartAt I x₀ x₀)
          (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
            X (range I) (extChartAt I x₀ x₀))
          (fun q : Fin 2 => if q = 0 then basis j else basis l) -
        ∑ k : Idx,
          connectionEndomorphismCoeff basis (ΓX (extChartAt I x₀ x₀)) j k *
            (tensor0SModelAt (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
              2 x₀ x₀ (A x₀)) (fun q : Fin 2 => if q = 0 then basis k else basis l) -
        ∑ k : Idx,
          connectionEndomorphismCoeff basis (ΓX (extChartAt I x₀ x₀)) l k *
            (tensor0SModelAt (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
              2 x₀ x₀ (A x₀)) (fun q : Fin 2 => if q = 0 then basis j else basis k) := by
  classical
  unfold mcovariantDeriv_tensor0SWithin
  rw [tensor0SModelAt_trivializationAt_symm]
  rw [covariantDeriv_tensor0SModelWithin_two_apply_basis_clm (basis := basis)]
  simp only [tensor0SModelInChart]
  rw [extChartAt_to_inv]
  rfl

omit [IsManifold I n M] [IsManifold I (n + 1) M] [CompleteSpace 𝕜] in
theorem mcovariantDeriv_tensor0SWithin_apply_basis_slots
    {Idx : Type*} [Fintype Idx] {s : ℕ}
    (basis : Module.Basis Idx 𝕜 E)
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (ΓX : E → E →L[𝕜] E)
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := n) s)
    (u : Set M) (x₀ : M) (slots : Fin s → Idx) :
    (tensor0SModelAt (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s x₀ x₀
        (mcovariantDeriv_tensor0SWithin (𝕜 := 𝕜) (E := E) (H := H)
          (I := I) (M := M) (n := n) s X ΓX α u x₀))
        (fun a : Fin s => basis (slots a)) =
      fderivWithin 𝕜
          (fun y =>
            tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H)
              (I := I) (M := M) s x₀ (fun x => α x) y)
          (((extChartAt I x₀).symm ⁻¹' u) ∩ range I)
          (extChartAt I x₀ x₀)
          (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
            X (range I) (extChartAt I x₀ x₀))
          (fun a : Fin s => basis (slots a)) -
        ∑ a : Fin s, ∑ k : Idx,
          connectionEndomorphismCoeff basis (ΓX (extChartAt I x₀ x₀)) (slots a) k *
            (tensor0SModelAt (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
              s x₀ x₀ (α x₀))
              (Function.update (fun b : Fin s => basis (slots b)) a (basis k)) := by
  classical
  unfold mcovariantDeriv_tensor0SWithin
  rw [tensor0SModelAt_trivializationAt_symm]
  rw [covariantDeriv_tensor0SModelWithin_apply_basis_slots (basis := basis)]
  simp only [tensor0SModelInChart]
  rw [extChartAt_to_inv]
  rfl

noncomputable def mcovariantDeriv_tensor0S (s : ℕ)
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (ΓX : E → E →L[𝕜] E)
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) s)
    (x₀ : M) : Tensor0SSpace s I x₀ :=
  mcovariantDeriv_tensor0SWithin (n := n) s X ΓX α univ x₀

noncomputable def mcovariantDeriv_tensorRSWithin (r s : ℕ)
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (ΓX : E → E →L[𝕜] E)
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r s)
    (u : Set M) (x₀ : M) : TensorRSSpace r s I x₀ := by
  letI := tensorRSBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s
  let X' := mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm X (range I)
  let T' : E → TensorRSModel r s 𝕜 E :=
    fun y =>
      ((trivializationAt (TensorRSModel r s 𝕜 E)
          (fun x => TensorRSSpace r s I x) x₀)
        ⟨(extChartAt I x₀).symm y, T.toFun ((extChartAt I x₀).symm y)⟩).2
  exact
    (trivializationAt (TensorRSModel r s 𝕜 E)
        (fun x => TensorRSSpace r s I x) x₀).symm x₀
      (covariantDeriv_tensorRSModelWithin r s X' ΓX T'
        ((extChartAt I x₀).symm ⁻¹' u ∩ range I)
        (extChartAt I x₀ x₀))

noncomputable def mcovariantDeriv_tensorRS (r s : ℕ)
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (ΓX : E → E →L[𝕜] E)
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r s)
    (x₀ : M) : TensorRSSpace r s I x₀ :=
  mcovariantDeriv_tensorRSWithin (n := n) r s X ΓX T univ x₀

section ExtractedConnection

variable [IsManifold I 2 M]

noncomputable def mcovariantDeriv_tensor0SWithinFromConnection (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) s)
    (u : Set M) (x₀ : M) : Tensor0SSpace s I x₀ :=
  mcovariantDeriv_tensor0SWithin (n := n) s X
    (connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀) α u x₀

noncomputable def mcovariantDeriv_tensor0SFromConnection (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) s)
    (x₀ : M) : Tensor0SSpace s I x₀ :=
  mcovariantDeriv_tensor0SWithinFromConnection (n := n) s cov X α univ x₀

noncomputable def mcovariantDeriv_tensorRSWithinFromConnection (r s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r s)
    (u : Set M) (x₀ : M) : TensorRSSpace r s I x₀ :=
  mcovariantDeriv_tensorRSWithin (n := n) r s X
    (connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀) T u x₀

noncomputable def mcovariantDeriv_tensorRSFromConnection (r s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r s)
    (x₀ : M) : TensorRSSpace r s I x₀ :=
  mcovariantDeriv_tensorRSWithinFromConnection (n := n) r s cov X T univ x₀

end ExtractedConnection

end SmoothVectorFieldRSNabla

end

end TensorLieDeriv

namespace Tensor0SBundle

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Set IsManifold ContinuousLinearMap VectorField Filter Function TensorLieDeriv
open scoped Manifold Topology Bundle ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [CompleteSpace 𝕜]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable {n : WithTop ℕ∞}
variable [IsManifold I n M]
variable [IsManifold I (n + 1) M]

noncomputable def nabla0SFun (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := n) s)
    (x : M) : Tensor0SSpace s I x :=
  TensorLieDeriv.mcovariantDeriv_tensor0SFromConnection
    (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
    (n := n) s cov X α x

noncomputable def nablaRSFun (r s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := n) r s)
    (x : M) : TensorRSSpace r s I x :=
  TensorLieDeriv.mcovariantDeriv_tensorRSFromConnection
    (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
    (n := n) r s cov X T x

omit [IsManifold I n M] [IsManifold I (n + 1) M] in
@[simp] theorem nabla0SFun_apply (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := n) s)
    (x : M) :
    nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s cov X α x =
      TensorLieDeriv.mcovariantDeriv_tensor0SFromConnection
        (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        (n := n) s cov X α x := rfl

omit [IsManifold I n M] [IsManifold I (n + 1) M] in
@[simp] theorem nablaRSFun_apply (r s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := n) r s)
    (x : M) :
    nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s cov X T x =
      TensorLieDeriv.mcovariantDeriv_tensorRSFromConnection
        (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        (n := n) r s cov X T x := rfl

abbrev Nabla0SRegular (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := n) s) : Prop :=
  letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s
  ContMDiff I (I.prod 𝓘(𝕜, Tensor0SModel s 𝕜 E)) n
    (fun x : M =>
      (⟨x, nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s cov X α x⟩ :
        TotalSpace (Tensor0SModel s 𝕜 E) (fun x : M => Tensor0SSpace s I x)))

abbrev NablaRSRegular (r s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := n) r s) : Prop :=
  letI := tensorRSBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s
  ContMDiff I (I.prod 𝓘(𝕜, TensorRSModel r s 𝕜 E)) n
    (fun x : M =>
      (⟨x, nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        r s cov X T x⟩ :
        TotalSpace (TensorRSModel r s 𝕜 E) (fun x : M => TensorRSSpace r s I x)))

noncomputable def nabla0S (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := n) s)
    (hreg : Nabla0SRegular (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      s cov X α) :
    Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := n) s :=
  letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s
  ⟨nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s cov X α, hreg⟩

noncomputable def nablaRS (r s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := n) r s)
    (hreg : NablaRSRegular (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      r s cov X T) :
    TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := n) r s :=
  letI := tensorRSBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s
  ⟨nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s cov X T, hreg⟩

omit [IsManifold I n M] [IsManifold I (n + 1) M] in
@[simp] theorem nabla0S_apply (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := n) s)
    (hreg : Nabla0SRegular (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      s cov X α)
    (x : M) :
    nabla0S (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s cov X α hreg x =
      nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s cov X α x := rfl

omit [IsManifold I n M] [IsManifold I (n + 1) M] in
@[simp] theorem nablaRS_apply (r s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := n) r s)
    (hreg : NablaRSRegular (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      r s cov X T)
    (x : M) :
    nablaRS (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s cov X T hreg x =
      nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s cov X T x := rfl

end

end Tensor0SBundle
