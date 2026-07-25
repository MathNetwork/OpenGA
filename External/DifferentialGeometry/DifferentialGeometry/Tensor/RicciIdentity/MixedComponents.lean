import DifferentialGeometry.Geometry.Coordinates.NablaComponents.TensorRS.Basic
import DifferentialGeometry.Geometry.Coordinates.NablaComponents.TensorRS.ApplyInput
import DifferentialGeometry.Geometry.Coordinates.NablaComponents.TensorRS.ModelBridge
import DifferentialGeometry.Geometry.Coordinates.NablaComponents.TensorRS.Formula
import DifferentialGeometry.Geometry.Coordinates.NablaComponents.TensorRS.Special12
import DifferentialGeometry.Tensor.Auxiliary.DerivationAlgebra
import DifferentialGeometry.Tensor.RSTensor.Components
import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.HigherOrder

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false









noncomputable section

namespace DifferentialGeometry.Integral.Connection

open Bundle Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

section MixedComponentAlgebra


def deltaMulti {Idx : Type*} {r : ℕ} [DecidableEq Idx]
    (L A : Fin r -> Idx) : Real :=
  if A = L then 1 else 0



def covariantCurvAction {Idx : Type*} [Fintype Idx] {n : ℕ}
    (R : Idx -> Idx -> Idx -> Idx -> Real) (i j : Idx)
    (A : (Fin n -> Idx) -> Real) (K : Fin n -> Idx) : Real :=
  -∑ q : Fin n, ∑ m : Idx,
    R i j m (K q) * A (Function.update K q m)



theorem contractUpper_components_eq_component_applyInput
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {r s : ℕ} {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (T : TensorRSSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) r s x)
    (theta :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) r x)
    (K : Fin s -> Idx) :
    contractUpper
        (fun L : Fin r -> Idx => component0S (I := I) basis theta L)
        (fun L : Fin r -> Idx => fun K : Fin s -> Idx =>
          componentRS_gen (I := I) basis T L K) K =
      component0S (I := I) basis (T theta) K := by
  rw [Tensor0SBundle.componentRS_apply_input_eq_sum (I := I) basis T theta K]
  rfl

@[simp] theorem deltaMulti_self {Idx : Type*} {r : ℕ} [DecidableEq Idx]
    (L : Fin r -> Idx) :
    deltaMulti L L = 1 := by
  simp [deltaMulti]

theorem deltaMulti_eq_zero_of_ne {Idx : Type*} {r : ℕ} [DecidableEq Idx]
    {L A : Fin r -> Idx} (h : A ≠ L) :
    deltaMulti L A = 0 := by
  simp [deltaMulti, h]

@[simp] theorem contractUpper_deltaMulti {Idx : Type*}
    [Fintype Idx] [DecidableEq Idx] {r s : ℕ}
    (L : Fin r -> Idx)
    (beta : (Fin r -> Idx) -> (Fin s -> Idx) -> Real)
    (K : Fin s -> Idx) :
    contractUpper (deltaMulti L) beta K = beta L K := by
  classical
  unfold contractUpper
  change (∑ A : Fin r -> Idx, deltaMulti L A * beta A K) = beta L K
  calc
    (∑ A : Fin r -> Idx, deltaMulti L A * beta A K)
        = deltaMulti L L * beta L K := by
          exact Fintype.sum_eq_single (α := Fin r -> Idx) (M := Real)
            (f := fun A : Fin r -> Idx => deltaMulti L A * beta A K) L
            (by
              intro A hA
              simp [deltaMulti, hA])
    _ = beta L K := by
          simp [deltaMulti]

private lemma deltaMulti_update_eq_one_iff {Idx : Type*}
    [DecidableEq Idx] {r : ℕ}
    (L A : Fin r -> Idx) (p : Fin r) (m : Idx) :
    deltaMulti L (Function.update A p m) = 1 ↔
      Function.update A p m = L := by
  by_cases h : Function.update A p m = L
  · simp [deltaMulti, h]
  · simp [deltaMulti, h]

private lemma update_eq_of_update_eq {Idx : Type*}
    [DecidableEq Idx] {r : ℕ}
    {L A : Fin r -> Idx} {p : Fin r} {m : Idx}
    (h : Function.update A p m = L) :
    A = Function.update L p (A p) := by
  funext q
  by_cases hpq : q = p
  · subst hpq
    simp
  · have hq := congrFun h q
    simpa [Function.update, hpq] using hq

private lemma update_value_eq_of_update_eq {Idx : Type*}
    [DecidableEq Idx] {r : ℕ}
    {L A : Fin r -> Idx} {p : Fin r} {m : Idx}
    (h : Function.update A p m = L) :
    m = L p := by
  have hp := congrFun h p
  simpa using hp

private lemma update_update_same_apply {Idx : Type*}
    [DecidableEq Idx] {r : ℕ}
    (L : Fin r -> Idx) (p : Fin r) (m : Idx) :
    Function.update (Function.update L p m) p (L p) = L := by
  funext q
  by_cases hpq : q = p
  · subst hpq
    simp
  · simp [Function.update, hpq]

private def updateSwapEquiv {Idx : Type*} [DecidableEq Idx] {r : ℕ}
    (p : Fin r) : ((Fin r -> Idx) × Idx) ≃ ((Fin r -> Idx) × Idx) where
  toFun Am := (Function.update Am.1 p Am.2, Am.1 p)
  invFun Am := (Function.update Am.1 p Am.2, Am.1 p)
  left_inv := by
    intro Am
    cases Am with
    | mk A m =>
        ext q <;> simp
  right_inv := by
    intro Am
    cases Am with
    | mk A m =>
        ext q <;> simp

private lemma sum_delta_update_pair {Idx : Type*}
    [Fintype Idx] [DecidableEq Idx] {r s : ℕ}
    (R : Idx -> Idx -> Idx -> Idx -> Real) (i j : Idx)
    (L : Fin r -> Idx) (p : Fin r)
    (beta : (Fin r -> Idx) -> (Fin s -> Idx) -> Real)
    (K : Fin s -> Idx) :
    (∑ A : Fin r -> Idx, ∑ m : Idx,
      R i j m (A p) * deltaMulti L (Function.update A p m) * beta A K)
      =
    ∑ m : Idx, R i j (L p) m *
      beta (Function.update L p m) K := by
  classical
  let F : ((Fin r -> Idx) × Idx) -> Real := fun Am =>
    R i j Am.2 (Am.1 p) *
      deltaMulti L (Function.update Am.1 p Am.2) * beta Am.1 K
  let G : ((Fin r -> Idx) × Idx) -> Real := fun Bm =>
    R i j (Bm.1 p) Bm.2 * deltaMulti L Bm.1 *
      beta (Function.update Bm.1 p Bm.2) K
  have hFG : ∑ Am, F Am = ∑ Bm, G Bm := by
    refine Fintype.sum_equiv (updateSwapEquiv (Idx := Idx) p) F G ?_
    intro Am
    cases Am with
    | mk A m =>
        simp [F, G, updateSwapEquiv]
  have hG :
      (∑ Bm, G Bm) =
        ∑ m : Idx, R i j (L p) m *
          beta (Function.update L p m) K := by
    calc
      (∑ Bm : (Fin r -> Idx) × Idx, G Bm)
          = ∑ B : Fin r -> Idx, ∑ m : Idx, G (B, m) := by
              rw [Fintype.sum_prod_type]
      _ = ∑ B : Fin r -> Idx,
            (if B = L then
              ∑ m : Idx, R i j (L p) m *
                beta (Function.update L p m) K
            else 0) := by
              refine Fintype.sum_congr _ _ ?_
              intro B
              by_cases hB : B = L
              · subst hB
                simp [G, deltaMulti]
              · simp [G, deltaMulti, hB]
      _ = ∑ m : Idx, R i j (L p) m *
            beta (Function.update L p m) K := by
              let S : Real := ∑ m : Idx, R i j (L p) m *
                beta (Function.update L p m) K
              change (∑ B : Fin r -> Idx,
                (if B = L then S else 0)) = S
              calc
                (∑ B : Fin r -> Idx, (if B = L then S else 0))
                    = (if L = L then S else 0) := by
                      refine Fintype.sum_eq_single
                        (α := Fin r -> Idx) (M := Real)
                        (f := fun B : Fin r -> Idx =>
                          if B = L then S else 0) L ?_
                      intro B hB
                      simp [hB]
                _ = S := by simp
  calc
    (∑ A : Fin r -> Idx, ∑ m : Idx,
      R i j m (A p) * deltaMulti L (Function.update A p m) * beta A K)
        = ∑ Am : (Fin r -> Idx) × Idx, F Am := by
            rw [Fintype.sum_prod_type]
    _ = ∑ Bm : (Fin r -> Idx) × Idx, G Bm := hFG
    _ = ∑ m : Idx, R i j (L p) m *
          beta (Function.update L p m) K := hG

private lemma contractUpper_covariantCurvAction_deltaMulti
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {r s : ℕ}
    (R : Idx -> Idx -> Idx -> Idx -> Real) (i j : Idx)
    (L : Fin r -> Idx)
    (beta : (Fin r -> Idx) -> (Fin s -> Idx) -> Real)
    (K : Fin s -> Idx) :
    contractUpper (covariantCurvAction R i j (deltaMulti L)) beta K =
      -∑ p : Fin r, ∑ m : Idx,
        R i j (L p) m * beta (Function.update L p m) K := by
  classical
  unfold contractUpper covariantCurvAction
  simp_rw [neg_mul]
  calc
    (∑ A : Fin r -> Idx,
      -((∑ q : Fin r, ∑ m : Idx,
          R i j m (A q) * deltaMulti L (Function.update A q m)) *
        beta A K))
        = -∑ A : Fin r -> Idx, (∑ q : Fin r, ∑ m : Idx,
          R i j m (A q) * deltaMulti L (Function.update A q m)) *
            beta A K := by
            simp [Finset.sum_neg_distrib]
    _ = -∑ A : Fin r -> Idx, ∑ q : Fin r, ∑ m : Idx,
          R i j m (A q) * deltaMulti L (Function.update A q m) *
            beta A K := by
            congr 1
            refine Fintype.sum_congr _ _ ?_
            intro A
            simp [Finset.sum_mul, mul_assoc]
    _ = -∑ q : Fin r, ∑ A : Fin r -> Idx, ∑ m : Idx,
          R i j m (A q) * deltaMulti L (Function.update A q m) *
            beta A K := by
            rw [Finset.sum_comm]
    _ = -∑ q : Fin r, ∑ m : Idx,
          R i j (L q) m * beta (Function.update L q m) K := by
            congr 1
            refine Fintype.sum_congr _ _ ?_
            intro q
            exact sum_delta_update_pair R i j L q beta K





theorem contract_covariantCurvAction_deltaMulti_eq_mixedCurvAction
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {r s : ℕ}
    (R : Idx -> Idx -> Idx -> Idx -> Real) (i j : Idx)
    (L : Fin r -> Idx) (K : Fin s -> Idx)
    (beta : (Fin r -> Idx) -> (Fin s -> Idx) -> Real) :
    covariantCurvAction R i j
        (contractUpper (deltaMulti L) beta) K -
      contractUpper
        (covariantCurvAction R i j (deltaMulti L)) beta K
      =
        (∑ p : Fin r, ∑ m : Idx,
          R i j (L p) m * beta (Function.update L p m) K) -
        (∑ q : Fin s, ∑ m : Idx,
          R i j m (K q) * beta L (Function.update K q m)) := by
  classical
  rw [contractUpper_covariantCurvAction_deltaMulti]
  unfold covariantCurvAction
  simp_rw [contractUpper_deltaMulti]
  ring




def mixedCurvAction {Idx : Type*} [Fintype Idx] {r s : ℕ}
    (R : Idx -> Idx -> Idx -> Idx -> Real) (i j : Idx)
    (beta : (Fin r -> Idx) -> (Fin s -> Idx) -> Real)
    (L : Fin r -> Idx) (K : Fin s -> Idx) : Real :=
  (∑ p : Fin r, ∑ m : Idx,
    R i j (L p) m * beta (Function.update L p m) K) -
  (∑ q : Fin s, ∑ m : Idx,
    R i j m (K q) * beta L (Function.update K q m))



def MixedRicciIdentityCoord {Idx : Type*} [Fintype Idx] {r s : ℕ}
    (R : Idx -> Idx -> Idx -> Idx -> Real) (i j : Idx)
    (commBeta beta : (Fin r -> Idx) -> (Fin s -> Idx) -> Real) : Prop :=
  ∀ L K, commBeta L K = mixedCurvAction R i j beta L K








theorem mixedRicciIdentityCoord_of_contract_probe_identities
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {r s : ℕ}
    (R : Idx -> Idx -> Idx -> Idx -> Real) (i j : Idx)
    (commBeta beta : (Fin r -> Idx) -> (Fin s -> Idx) -> Real)
    (commContract : (Fin r -> Idx) -> (Fin s -> Idx) -> Real)
    (commProbe : (Fin r -> Idx) -> (Fin r -> Idx) -> Real)
    (hcontract : ∀ L K,
      contractUpper (deltaMulti L) commBeta K =
        commContract L K - contractUpper (commProbe L) beta K)
    (hcontractCov : ∀ L K,
      commContract L K =
        covariantCurvAction R i j (contractUpper (deltaMulti L) beta) K)
    (hprobeCov : ∀ L A,
      commProbe L A = covariantCurvAction R i j (deltaMulti L) A) :
    MixedRicciIdentityCoord R i j commBeta beta := by
  classical
  intro L K
  have hprobeContract :
      contractUpper (commProbe L) beta K =
        contractUpper (covariantCurvAction R i j (deltaMulti L)) beta K := by
    unfold contractUpper
    refine Finset.sum_congr rfl fun A _ => ?_
    rw [hprobeCov L A]
  have hcomm :
      commBeta L K =
        covariantCurvAction R i j (contractUpper (deltaMulti L) beta) K -
          contractUpper (covariantCurvAction R i j (deltaMulti L)) beta K := by
    calc
      commBeta L K = contractUpper (deltaMulti L) commBeta K := by
          rw [contractUpper_deltaMulti]
      _ = commContract L K - contractUpper (commProbe L) beta K := hcontract L K
      _ = covariantCurvAction R i j (contractUpper (deltaMulti L) beta) K -
            contractUpper (covariantCurvAction R i j (deltaMulti L)) beta K := by
          rw [hcontractCov L K, hprobeContract]
  rw [hcomm, mixedCurvAction]
  exact contract_covariantCurvAction_deltaMulti_eq_mixedCurvAction R i j L K beta







theorem mixedRicciIdentityCoord_of_second_product_identities
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {r s : ℕ}
    (R : Idx -> Idx -> Idx -> Idx -> Real) (i j : Idx)
    (commBeta beta beta_i beta_j beta_ij beta_ji :
      (Fin r -> Idx) -> (Fin s -> Idx) -> Real)
    (commContract contract_ij contract_ji :
      (Fin r -> Idx) -> (Fin s -> Idx) -> Real)
    (commProbe probe_i probe_j probe_ij probe_ji :
      (Fin r -> Idx) -> (Fin r -> Idx) -> Real)
    (hcommBeta : ∀ L K, commBeta L K = beta_ij L K - beta_ji L K)
    (hcommContract : ∀ L K, commContract L K = contract_ij L K - contract_ji L K)
    (hcommProbe : ∀ L A, commProbe L A = probe_ij L A - probe_ji L A)
    (hprod_ij : ∀ L K,
      contract_ij L K =
        contractUpper (probe_ij L) beta K +
          contractUpper (probe_j L) beta_i K +
          contractUpper (probe_i L) beta_j K +
          contractUpper (deltaMulti L) beta_ij K)
    (hprod_ji : ∀ L K,
      contract_ji L K =
        contractUpper (probe_ji L) beta K +
          contractUpper (probe_i L) beta_j K +
          contractUpper (probe_j L) beta_i K +
          contractUpper (deltaMulti L) beta_ji K)
    (hcontractCov : ∀ L K,
      commContract L K =
        covariantCurvAction R i j (contractUpper (deltaMulti L) beta) K)
    (hprobeCov : ∀ L A,
      commProbe L A = covariantCurvAction R i j (deltaMulti L) A) :
    MixedRicciIdentityCoord R i j commBeta beta := by
  classical
  refine mixedRicciIdentityCoord_of_contract_probe_identities
    R i j commBeta beta commContract commProbe ?_ hcontractCov hprobeCov
  intro L K
  have hprod :=
    contractUpper_commutator_of_second_product_rules
      (Idx := Idx) (r := r) (s := s)
      (theta := deltaMulti L)
      (theta_i := probe_i L)
      (theta_j := probe_j L)
      (theta_ij := probe_ij L)
      (theta_ji := probe_ji L)
      (beta := beta)
      (beta_i := beta_i)
      (beta_j := beta_j)
      (beta_ij := beta_ij)
      (beta_ji := beta_ji)
      (contract_ij := contract_ij L)
      (contract_ji := contract_ji L)
      (hij := hprod_ij L)
      (hji := hprod_ji L)
      K
  calc
    contractUpper (deltaMulti L) commBeta K =
        contractUpper (deltaMulti L)
          (fun A K => beta_ij A K - beta_ji A K) K := by
          unfold contractUpper
          refine Finset.sum_congr rfl fun A _ => ?_
          rw [hcommBeta A K]
    _ = (contract_ij L K - contract_ji L K) -
        contractUpper (fun A => probe_ij L A - probe_ji L A) beta K := hprod
    _ = commContract L K - contractUpper (commProbe L) beta K := by
          rw [hcommContract L K]
          congr 1
          unfold contractUpper
          refine Finset.sum_congr rfl fun A _ => ?_
          rw [hcommProbe L A]



omit [IsManifold I ∞ M] in
theorem coordDeriv_applyInput_eq_contractUpper
    [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I (∞ : WithTop ℕ∞) M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    {r s : ℕ}
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (T : TensorRSField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s)
    (theta : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r)
    (x₀ : M) (K : Fin s -> DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E) :
    DifferentialGeometry.Tensor.Coordinates.coordDeriv0SAt (I := I) (fun x => X x) x₀
        (fun y : M =>
          tensorRSField_applyInput (𝕜 := Real) (E := E) (H := H) (I := I)
            (M := M) (∞ : WithTop ℕ∞) T theta y)
        K =
      contractUpper
        (fun L : Fin r -> DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E =>
          DifferentialGeometry.Tensor.Coordinates.coordDeriv0SAt (I := I) (fun x => X x) x₀
            (fun x => theta x) L)
        (fun L : Fin r -> DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E =>
          fun K : Fin s -> DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E =>
            DifferentialGeometry.Tensor.Coordinates.coordComponentRSAt (I := I) (T x₀) L K)
        K +
      contractUpper
        (fun L : Fin r -> DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E =>
          DifferentialGeometry.Tensor.Coordinates.coordComponent0SAt (I := I) (theta x₀) L)
        (fun L : Fin r -> DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E =>
          fun K : Fin s -> DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E =>
            DifferentialGeometry.Tensor.Coordinates.coordDerivRSAt (I := I) (fun x => X x) x₀
              (fun x => T x) L K)
        K := by
  rw [DifferentialGeometry.Tensor.Coordinates.coordDeriv0SAt_applyInput_eq_sum (I := I) X T theta x₀ K]
  rfl










theorem mixedRicciIdentityCoord_of_coordinate_second_product
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {r s : ℕ}
    (R : Idx -> Idx -> Idx -> Idx -> Real) (i j : Idx)
    (commBeta beta beta_i beta_j beta_ij beta_ji :
      (Fin r -> Idx) -> (Fin s -> Idx) -> Real)
    (commContract contract_ij contract_ji :
      (Fin r -> Idx) -> (Fin s -> Idx) -> Real)
    (commProbe probe_i probe_j probe_ij probe_ji :
      (Fin r -> Idx) -> (Fin r -> Idx) -> Real)
    (prod_ij_left prod_ij_right prod_ji_left prod_ji_right :
      (Fin r -> Idx) -> (Fin s -> Idx) -> Real)
    (hcommBeta : ∀ L K, commBeta L K = beta_ij L K - beta_ji L K)
    (hcommContract : ∀ L K, commContract L K = contract_ij L K - contract_ji L K)
    (hcommProbe : ∀ L A, commProbe L A = probe_ij L A - probe_ji L A)
    (hcontract_ij : ∀ L K,
      contract_ij L K = prod_ij_left L K + prod_ij_right L K)
    (hprod_ij_left : ∀ L K,
      prod_ij_left L K =
        contractUpper (probe_ij L) beta K +
          contractUpper (probe_j L) beta_i K)
    (hprod_ij_right : ∀ L K,
      prod_ij_right L K =
        contractUpper (probe_i L) beta_j K +
          contractUpper (deltaMulti L) beta_ij K)
    (hcontract_ji : ∀ L K,
      contract_ji L K = prod_ji_left L K + prod_ji_right L K)
    (hprod_ji_left : ∀ L K,
      prod_ji_left L K =
        contractUpper (probe_ji L) beta K +
          contractUpper (probe_i L) beta_j K)
    (hprod_ji_right : ∀ L K,
      prod_ji_right L K =
        contractUpper (probe_j L) beta_i K +
          contractUpper (deltaMulti L) beta_ji K)
    (hcontractCov : ∀ L K,
      commContract L K =
        covariantCurvAction R i j (contractUpper (deltaMulti L) beta) K)
    (hprobeCov : ∀ L A,
      commProbe L A = covariantCurvAction R i j (deltaMulti L) A) :
    MixedRicciIdentityCoord R i j commBeta beta := by
  classical
  refine mixedRicciIdentityCoord_of_second_product_identities
    R i j commBeta beta beta_i beta_j beta_ij beta_ji
    commContract contract_ij contract_ji
    commProbe probe_i probe_j probe_ij probe_ji
    hcommBeta hcommContract hcommProbe ?_ ?_ hcontractCov hprobeCov
  · intro L K
    exact contractUpper_second_product_of_first_product_rules
      (Idx := Idx) (r := r) (s := s)
      (theta := deltaMulti L)
      (theta_i := probe_i L)
      (theta_j := probe_j L)
      (theta_ij := probe_ij L)
      (beta := beta)
      (beta_i := beta_i)
      (beta_j := beta_j)
      (beta_ij := beta_ij)
      (contract_ij := contract_ij L)
      (left := prod_ij_left L)
      (right := prod_ij_right L)
      (hcontract := hcontract_ij L)
      (hleft := hprod_ij_left L)
      (hright := hprod_ij_right L)
      K
  · intro L K
    exact contractUpper_second_product_of_first_product_rules
      (Idx := Idx) (r := r) (s := s)
      (theta := deltaMulti L)
      (theta_i := probe_j L)
      (theta_j := probe_i L)
      (theta_ij := probe_ji L)
      (beta := beta)
      (beta_i := beta_j)
      (beta_j := beta_i)
      (beta_ij := beta_ji)
      (contract_ij := contract_ji L)
      (left := prod_ji_left L)
      (right := prod_ji_right L)
      (hcontract := hcontract_ji L)
      (hleft := hprod_ji_left L)
      (hright := hprod_ji_right L)
      K

end MixedComponentAlgebra

end DifferentialGeometry.Integral.Connection
