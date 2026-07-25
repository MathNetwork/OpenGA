import Mathlib.Analysis.InnerProductSpace.Spectrum
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Coordinate
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.KroneckerQuadForm

set_option autoImplicit false
set_option linter.style.longLine false









namespace Tensor0SBundle

noncomputable section

open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

section DiagonalCoordinate

variable {Idx : Type*} [DecidableEq Idx]
variable {x : M}


def diagonalInvMetric (μ : Idx -> Real) : Idx -> Idx -> Real :=
  fun i j => if i = j then μ i else 0


def identityInvMetric : Idx -> Idx -> Real :=
  diagonalInvMetric (fun _ : Idx => 1)

@[simp] theorem diagonalInvMetric_apply_self (μ : Idx -> Real) (i : Idx) :
    diagonalInvMetric μ i i = μ i := by
  simp [diagonalInvMetric]

@[simp] theorem identityInvMetric_apply_self (i : Idx) :
    identityInvMetric (Idx := Idx) i i = 1 := by
  simp [identityInvMetric]

theorem diagonalInvMetric_eq_zero_of_ne {μ : Idx -> Real} {i j : Idx}
    (hij : i ≠ j) :
    diagonalInvMetric μ i j = 0 := by
  simp [diagonalInvMetric, hij]

private theorem prod_diagonalInvMetric_eq_zero_of_ne
    {s : Nat} {μ : Idx -> Real} {I0 J0 : Fin s -> Idx}
    (hIJ : I0 ≠ J0) :
    (∏ a : Fin s, diagonalInvMetric μ (I0 a) (J0 a)) = 0 := by
  classical
  have hsome : exists a : Fin s, I0 a ≠ J0 a := by
    by_contra hnone
    apply hIJ
    funext a
    by_contra ha
    exact hnone ⟨a, ha⟩
  rcases hsome with ⟨a, ha⟩
  exact Finset.prod_eq_zero (Finset.mem_univ a)
    (diagonalInvMetric_eq_zero_of_ne (μ := μ) ha)

omit [DecidableEq Idx] in
private theorem prod_mu_le_pow
    {s : Nat} {μ : Idx -> Real} {C : Real}
    (hμ_nonneg : forall i : Idx, 0 <= μ i)
    (hμ_le : forall i : Idx, μ i <= C)
    (I0 : Fin s -> Idx) :
    (∏ a : Fin s, μ (I0 a)) <= C ^ s := by
  calc
    (∏ a : Fin s, μ (I0 a)) <= ∏ _a : Fin s, C := by
          apply Finset.prod_le_prod
          · intro a _
            exact hμ_nonneg (I0 a)
          · intro a _
            exact hμ_le (I0 a)
    _ = C ^ s := by simp

variable [Fintype Idx]


omit [FiniteDimensional ℝ E] in
theorem coordInner0S_diagonal_eq_sum
    (s : Nat) (μ : Idx -> Real)
    (A : Tensor0SSpace s I x)
    (basis : Module.Basis Idx Real (TangentSpace I x)) :
    coordInner0S (I := I) (x := x) s (diagonalInvMetric μ) A A basis =
      ∑ I0 : Fin s -> Idx,
        (∏ a : Fin s, μ (I0 a)) *
          (tensor0SComponent (I := I) A (fun i => basis i) I0) ^ 2 := by
  classical
  unfold coordInner0S
  apply Finset.sum_congr rfl
  intro I0 _
  rw [Finset.sum_eq_single I0]
  · simp [diagonalInvMetric, pow_two]
    ring
  · intro J0 _ hJ0
    have hprod :
        (∏ a : Fin s, diagonalInvMetric μ (I0 a) (J0 a)) = 0 :=
      prod_diagonalInvMetric_eq_zero_of_ne (μ := μ) (Ne.symm hJ0)
    rw [hprod]
    ring
  · intro hnotmem
    exact False.elim (hnotmem (Finset.mem_univ I0))


omit [FiniteDimensional ℝ E] in
theorem coordInner0S_identity_eq_sum_sq
    (s : Nat) (A : Tensor0SSpace s I x)
    (basis : Module.Basis Idx Real (TangentSpace I x)) :
    coordInner0S (I := I) (x := x) s identityInvMetric A A basis =
      ∑ I0 : Fin s -> Idx,
        (tensor0SComponent (I := I) A (fun i => basis i) I0) ^ 2 := by
  classical
  change coordInner0S (I := I) (x := x) s (diagonalInvMetric (fun _ : Idx => 1))
      A A basis =
    ∑ I0 : Fin s -> Idx,
      (tensor0SComponent (I := I) A (fun i => basis i) I0) ^ 2
  rw [coordInner0S_diagonal_eq_sum (I := I) (x := x) s (fun _ : Idx => 1) A basis]
  simp


omit [FiniteDimensional ℝ E] in
theorem coordInner0S_identity_eq_sum
    (s : Nat) (A B : Tensor0SSpace s I x)
    (basis : Module.Basis Idx Real (TangentSpace I x)) :
    coordInner0S (I := I) (x := x) s identityInvMetric A B basis =
      ∑ I0 : Fin s -> Idx,
        tensor0SComponent (I := I) A (fun i => basis i) I0 *
          tensor0SComponent (I := I) B (fun i => basis i) I0 := by
  classical
  unfold coordInner0S
  apply Finset.sum_congr rfl
  intro I0 _
  rw [Finset.sum_eq_single I0]
  · simp [identityInvMetric, diagonalInvMetric]
  · intro J0 _ hJ0
    have hprod :
        (∏ a : Fin s, identityInvMetric (Idx := Idx) (I0 a) (J0 a)) = 0 := by
      exact prod_diagonalInvMetric_eq_zero_of_ne
        (μ := fun _ : Idx => 1) (Ne.symm hJ0)
    rw [hprod]
    ring
  · intro hnotmem
    exact False.elim (hnotmem (Finset.mem_univ I0))



theorem inner0S_basisTensor_left_identity
    (g : SmoothMetric_gen I M) (x : M) (s : Nat)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      MetricInverseInBasis_gen (I := I) g x basis (identityInvMetric (Idx := Idx)))
    (slots : Fin s -> Idx) (A : Tensor0SSpace s I x) :
    inner0S (I := I) g x s (basisTensor0S (I := I) basis slots) A =
      component0S (I := I) basis A slots := by
  classical
  rw [inner0S_eq_coord (I := I) g x s basis (identityInvMetric (Idx := Idx)) hinv,
    coordInner0S_identity_eq_sum (I := I) (x := x) s
      (basisTensor0S (I := I) basis slots) A basis]
  rw [Finset.sum_eq_single slots]
  · change
      component0S (I := I) basis (basisTensor0S (I := I) basis slots) slots *
          component0S (I := I) basis A slots =
        component0S (I := I) basis A slots
    rw [basisTensor0S_component]
    simp
  · intro slots' _ hslots'
    have hcomp :
        tensor0SComponent (I := I) (basisTensor0S (I := I) basis slots)
          (fun i => basis i) slots' = 0 := by
      change component0S (I := I) basis
        (basisTensor0S (I := I) basis slots) slots' = 0
      rw [basisTensor0S_component]
      simp [Ne.symm hslots']
    rw [hcomp]
    ring
  · intro hnotmem
    exact False.elim (hnotmem (Finset.mem_univ slots))



theorem inner0S_basisTensor_right_identity
    (g : SmoothMetric_gen I M) (x : M) (s : Nat)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      MetricInverseInBasis_gen (I := I) g x basis (identityInvMetric (Idx := Idx)))
    (A : Tensor0SSpace s I x) (slots : Fin s -> Idx) :
    inner0S (I := I) g x s A (basisTensor0S (I := I) basis slots) =
      component0S (I := I) basis A slots := by
  classical
  rw [inner0S_eq_coord (I := I) g x s basis (identityInvMetric (Idx := Idx)) hinv,
    coordInner0S_identity_eq_sum (I := I) (x := x) s
      A (basisTensor0S (I := I) basis slots) basis]
  rw [Finset.sum_eq_single slots]
  · change
      component0S (I := I) basis A slots *
          component0S (I := I) basis (basisTensor0S (I := I) basis slots) slots =
        component0S (I := I) basis A slots
    rw [basisTensor0S_component]
    simp
  · intro slots' _ hslots'
    have hcomp :
        tensor0SComponent (I := I) (basisTensor0S (I := I) basis slots)
          (fun i => basis i) slots' = 0 := by
      change component0S (I := I) basis
        (basisTensor0S (I := I) basis slots) slots' = 0
      rw [basisTensor0S_component]
      simp [Ne.symm hslots']
    rw [hcomp]
    ring
  · intro hnotmem
    exact False.elim (hnotmem (Finset.mem_univ slots))



theorem normSq0S_identity_eq_sum_sq
    (g : SmoothMetric_gen I M) (x : M) (s : Nat)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      MetricInverseInBasis_gen (I := I) g x basis (identityInvMetric (Idx := Idx)))
    (A : Tensor0SSpace s I x) :
    normSq0S (I := I) g x s A =
      ∑ slots : Fin s -> Idx,
        (component0S (I := I) basis A slots) ^ 2 := by
  rw [normSq0S_eq_coord (I := I) g x s basis
    (identityInvMetric (Idx := Idx)) hinv,
    coordInner0S_identity_eq_sum_sq (I := I) (x := x) s A basis]
  apply Finset.sum_congr rfl
  intro slots _
  rfl




theorem normSq0S_le_card_of_component_bound
    (g : SmoothMetric_gen I M) (x : M) (s : Nat)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      MetricInverseInBasis_gen (I := I) g x basis (identityInvMetric (Idx := Idx)))
    (A : Tensor0SSpace s I x) (B : Real) (hBnn : 0 ≤ B)
    (hB : ∀ slots : Fin s -> Idx,
      |component0S (I := I) basis A slots| ≤ B) :
    normSq0S (I := I) g x s A ≤
      (Fintype.card (Fin s -> Idx) : Real) * B ^ 2 := by
  rw [normSq0S_identity_eq_sum_sq (I := I) g x s basis hinv A]
  calc
    (∑ slots : Fin s -> Idx,
        (component0S (I := I) basis A slots) ^ 2)
        ≤ ∑ _slots : Fin s -> Idx, B ^ 2 := by
          apply Finset.sum_le_sum
          intro slots _
          have habs :
              |component0S (I := I) basis A slots| ≤ |B| := by
            simpa [abs_of_nonneg hBnn] using hB slots
          have hsq := sq_le_sq.mpr habs
          simpa [sq_abs] using hsq
    _ = (Fintype.card (Fin s -> Idx) : Real) * B ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]



theorem normSq0S_three_identity_eq_sum
    (g : SmoothMetric_gen I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      MetricInverseInBasis_gen (I := I) g x basis (identityInvMetric (Idx := Idx)))
    (A : Tensor0SSpace 3 I x) :
    normSq0S (I := I) g x 3 A =
      ∑ d : Idx, ∑ a : Idx, ∑ b : Idx,
        (component0S (I := I) basis A
          (Fin.cons d (fun q : Fin 2 => if q = 0 then a else b))) ^ 2 := by
  rw [normSq0S_identity_eq_sum_sq (I := I) g x 3 basis hinv A]
  rw [sum_fin_succ_fun (s := 2)]
  apply Finset.sum_congr rfl
  intro d _
  rw [sum_fin_two_fun]







omit [FiniteDimensional ℝ E] in
theorem coordInner0S_diagonal_le_pow_identity
    (s : Nat) (μ : Idx -> Real) (C : Real)
    (hμ_nonneg : forall i : Idx, 0 <= μ i)
    (hμ_le : forall i : Idx, μ i <= C)
    (A : Tensor0SSpace s I x)
    (basis : Module.Basis Idx Real (TangentSpace I x)) :
    coordInner0S (I := I) (x := x) s (diagonalInvMetric μ) A A basis <=
      C ^ s * coordInner0S (I := I) (x := x) s identityInvMetric A A basis := by
  classical
  rw [coordInner0S_diagonal_eq_sum (I := I) (x := x) s μ A basis,
    coordInner0S_identity_eq_sum_sq (I := I) (x := x) s A basis]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro I0 _
  exact mul_le_mul_of_nonneg_right
    (prod_mu_le_pow (μ := μ) (C := C) hμ_nonneg hμ_le I0)
    (sq_nonneg _)







omit [FiniteDimensional ℝ E] in
theorem coordInner0S_identity_le_pow_diagonal
    (s : Nat) (μ : Idx -> Real) (m : Real) (hm : 0 < m)
    (hμ_lb : forall i : Idx, m <= μ i)
    (A : Tensor0SSpace s I x)
    (basis : Module.Basis Idx Real (TangentSpace I x)) :
    coordInner0S (I := I) (x := x) s identityInvMetric A A basis <=
      (1 / m) ^ s *
        coordInner0S (I := I) (x := x) s (diagonalInvMetric μ) A A basis := by
  classical
  rw [coordInner0S_diagonal_eq_sum (I := I) (x := x) s μ A basis,
    coordInner0S_identity_eq_sum_sq (I := I) (x := x) s A basis,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro I0 _
  have hprod : m ^ s <= ∏ a : Fin s, μ (I0 a) := by
    calc m ^ s = ∏ _a : Fin s, m := by simp
      _ <= ∏ a : Fin s, μ (I0 a) :=
          Finset.prod_le_prod (fun a _ => hm.le) (fun a _ => hμ_lb (I0 a))
  have hge1 : (1 : Real) <= (1 / m) ^ s * ∏ a : Fin s, μ (I0 a) := by
    have hms : (1 / m) ^ s * m ^ s = 1 := by
      rw [← mul_pow, one_div, inv_mul_cancel₀ hm.ne', one_pow]
    calc (1 : Real) = (1 / m) ^ s * m ^ s := hms.symm
      _ <= (1 / m) ^ s * ∏ a : Fin s, μ (I0 a) :=
          mul_le_mul_of_nonneg_left hprod (by positivity)
  nlinarith [hge1, sq_nonneg (tensor0SComponent (I := I) A (fun i => basis i) I0)]









theorem normSq0S_diag_le
    (g h : SmoothMetric_gen I M) (x : M) (s : Nat)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (μ : Idx -> Real) (C : Real)
    (hginv :
      MetricInverseInBasis_gen (I := I) g x basis (identityInvMetric (Idx := Idx)))
    (hhinv :
      MetricInverseInBasis_gen (I := I) h x basis (diagonalInvMetric μ))
    (hμ_nonneg : forall i : Idx, 0 <= μ i)
    (hμ_le : forall i : Idx, μ i <= C)
    (A : Tensor0SSpace s I x) :
    normSq0S (I := I) h x s A <= C ^ s * normSq0S (I := I) g x s A := by
  rw [normSq0S_eq_coord (I := I) h x s basis (diagonalInvMetric μ) hhinv A,
    normSq0S_eq_coord (I := I) g x s basis (identityInvMetric (Idx := Idx)) hginv A]
  exact coordInner0S_diagonal_le_pow_identity (I := I) (x := x) s μ C hμ_nonneg hμ_le A basis







omit [FiniteDimensional ℝ E] in
theorem coordInner0S_identity_le_pow_quad
    (s : Nat) (Q : Idx -> Idx -> Real) (C : Real) (hC : 0 < C)
    (hQsymm : forall i j : Idx, Q i j = Q j i)
    (hQlb : forall w : Idx -> Real,
      (1 / C) * ∑ i : Idx, w i ^ 2 <= ∑ i : Idx, ∑ j : Idx, Q i j * (w i * w j))
    (A : Tensor0SSpace s I x)
    (basis : Module.Basis Idx Real (TangentSpace I x)) :
    coordInner0S (I := I) (x := x) s identityInvMetric A A basis <=
      C ^ s * coordInner0S (I := I) (x := x) s Q A A basis := by
  classical
  have hkey := DifferentialGeometry.HCGCompactness.quadForm_id_le_pow Q C hC hQsymm hQlb s
    (fun I0 => tensor0SComponent (I := I) A (fun i => basis i) I0)
  have hQform : coordInner0S (I := I) (x := x) s Q A A basis
      = ∑ I0 : Fin s -> Idx, ∑ J0 : Fin s -> Idx,
          (∏ a : Fin s, Q (I0 a) (J0 a)) *
            (tensor0SComponent (I := I) A (fun i => basis i) I0 *
              tensor0SComponent (I := I) A (fun i => basis i) J0) := by
    unfold coordInner0S
    exact Finset.sum_congr rfl fun I0 _ => Finset.sum_congr rfl fun J0 _ =>
      mul_assoc _ _ _
  rw [coordInner0S_identity_eq_sum_sq (I := I) (x := x) s A basis, hQform]
  have hmul : (C * (1 / C)) ^ s = 1 := by
    rw [mul_one_div, div_self hC.ne', one_pow]
  calc (∑ I0 : Fin s -> Idx,
        tensor0SComponent (I := I) A (fun i => basis i) I0 ^ 2)
      = C ^ s * ((1 / C) ^ s * ∑ I0 : Fin s -> Idx,
          tensor0SComponent (I := I) A (fun i => basis i) I0 ^ 2) := by
        rw [← mul_assoc, ← mul_pow, hmul, one_mul]
    _ <= C ^ s * (∑ I0 : Fin s -> Idx, ∑ J0 : Fin s -> Idx,
          (∏ a : Fin s, Q (I0 a) (J0 a)) *
            (tensor0SComponent (I := I) A (fun i => basis i) I0 *
              tensor0SComponent (I := I) A (fun i => basis i) J0)) :=
        mul_le_mul_of_nonneg_left hkey (le_of_lt (pow_pos hC s))






theorem sum_comp_sq_le_pow_normSq0S
    (g : SmoothMetric_gen I M) (x : M) (s : Nat)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (Q : Idx -> Idx -> Real) (C : Real) (hC : 0 < C)
    (hginv : MetricInverseInBasis_gen (I := I) g x basis Q)
    (hQsymm : forall i j : Idx, Q i j = Q j i)
    (hQlb : forall w : Idx -> Real,
      (1 / C) * ∑ i : Idx, w i ^ 2 <= ∑ i : Idx, ∑ j : Idx, Q i j * (w i * w j))
    (A : Tensor0SSpace s I x) :
    (∑ I0 : Fin s -> Idx,
        tensor0SComponent (I := I) A (fun i => basis i) I0 ^ 2) <=
      C ^ s * normSq0S (I := I) g x s A := by
  rw [normSq0S_eq_coord (I := I) g x s basis Q hginv A,
    ← coordInner0S_identity_eq_sum_sq (I := I) (x := x) s A basis]
  exact coordInner0S_identity_le_pow_quad (I := I) (x := x) s Q C hC hQsymm hQlb A basis






theorem normSq0S_le_pow_sum_comp_sq
    (g : SmoothMetric_gen I M) (x : M) (s : Nat)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (Q : Idx -> Idx -> Real) (ε : Real) (hε0 : 0 <= ε)
    (hginv : MetricInverseInBasis_gen (I := I) g x basis Q)
    (hnear : forall i j : Idx, |Q i j - (if i = j then (1 : Real) else 0)| <= ε)
    (A : Tensor0SSpace s I x) :
    normSq0S (I := I) g x s A <=
      ((1 + ε) * (Fintype.card Idx : Real)) ^ s *
        ∑ I0 : Fin s -> Idx,
          tensor0SComponent (I := I) A (fun i => basis i) I0 ^ 2 := by
  classical
  rw [normSq0S_eq_coord (I := I) g x s basis Q hginv A]
  have hQform : coordInner0S (I := I) (x := x) s Q A A basis
      = ∑ I0 : Fin s -> Idx, ∑ J0 : Fin s -> Idx,
          (∏ a : Fin s, Q (I0 a) (J0 a)) *
            (tensor0SComponent (I := I) A (fun i => basis i) I0 *
              tensor0SComponent (I := I) A (fun i => basis i) J0) := by
    unfold coordInner0S
    exact Finset.sum_congr rfl fun I0 _ => Finset.sum_congr rfl fun J0 _ =>
      mul_assoc _ _ _
  rw [hQform]
  exact DifferentialGeometry.HCGCompactness.quad_ub_of_near_id Q ε hε0 hnear s
    (fun I0 => tensor0SComponent (I := I) A (fun i => basis i) I0)

end DiagonalCoordinate

section MetricEquiv







theorem exists_diagInv_of_equiv
    (g h : SmoothMetric_gen I M) (x : M) {C : Real}
    (hC : 1 <= C)
    (hequiv :
      forall v : TangentSpace I x,
        C⁻¹ * g.inner x v v <= h.inner x v v /\
          h.inner x v v <= C * g.inner x v v) :
    exists mu : Fin (Module.finrank Real (TangentSpace I x)) -> Real,
    exists basis :
      Module.Basis (Fin (Module.finrank Real (TangentSpace I x))) Real
        (TangentSpace I x),
      MetricInverseInBasis_gen
        (I := I) g x basis
        (identityInvMetric
          (Idx := Fin (Module.finrank Real (TangentSpace I x)))) /\
      MetricInverseInBasis_gen
        (I := I) h x basis (diagonalInvMetric mu) /\
      (forall i : Fin (Module.finrank Real (TangentSpace I x)), 0 <= mu i) /\
      (forall i : Fin (Module.finrank Real (TangentSpace I x)), mu i <= C) := by
  classical
  let D := (tangentMetricData_gen (I := I) g x).metric
  letI : InnerProductSpace.Core Real (TangentSpace I x) := D.toCore
  letI : NormedAddCommGroup (TangentSpace I x) :=
    @InnerProductSpace.Core.toNormedAddCommGroup Real (TangentSpace I x) _ _ _
      D.toCore
  letI : InnerProductSpace Real (TangentSpace I x) :=
    @InnerProductSpace.ofCore Real (TangentSpace I x) _ _ _ D.toCore.toCore
  let T : TangentSpace I x →ₗ[Real] TangentSpace I x :=
    ((tangentFlatEquiv_gen (I := I) g x).symm.toLinearMap).comp
      (tangentFlatEquiv_gen (I := I) h x).toLinearMap
  have hTg (X Y : TangentSpace I x) :
      g.inner x (T X) Y = h.inner x X Y := by
    change (tangentFlatEquiv_gen (I := I) g x
        ((tangentFlatEquiv_gen (I := I) g x).symm
          ((tangentFlatEquiv_gen (I := I) h x) X))) Y =
      h.inner x X Y
    rw [(tangentFlatEquiv_gen (I := I) g x).apply_symm_apply]
    rfl
  have hT : T.IsSymmetric := by
    intro X Y
    rw [MetricFiberData.toCore_inner D (T X) Y,
      MetricFiberData.toCore_inner D X (T Y)]
    calc
      g.inner x (T X) Y = h.inner x X Y := hTg X Y
      _ = h.inner x Y X := h.symm x X Y
      _ = g.inner x (T Y) X := (hTg Y X).symm
      _ = g.inner x X (T Y) := g.symm x (T Y) X
  let n := Module.finrank Real (TangentSpace I x)
  have hn : Module.finrank Real (TangentSpace I x) = n := rfl
  let ob := hT.eigenvectorBasis hn
  let basis : Module.Basis (Fin n) Real (TangentSpace I x) := ob.toBasis
  let lam : Fin n -> Real := fun i => hT.eigenvalues hn i
  let mu : Fin n -> Real := fun i => (lam i)⁻¹
  have hg_orth :
      forall i j : Fin n,
        g.inner x (basis i) (basis j) = if i = j then 1 else 0 := by
    intro i j
    have hij := ob.inner_eq_ite i j
    have hinner :
        Inner.inner Real (ob i) (ob j) = D.inner (ob i) (ob j) :=
      MetricFiberData.toCore_inner D (ob i) (ob j)
    simpa [basis, MetricFiberData.inner, tangentMetricData_gen]
      using hinner.symm.trans hij
  have hT_eig (i : Fin n) :
      T (basis i) = lam i • basis i := by
    simp [basis, lam, ob, hT.apply_eigenvectorBasis hn i]
  have hh_diag :
      forall i j : Fin n,
        h.inner x (basis i) (basis j) = if i = j then lam i else 0 := by
    intro i j
    calc
      h.inner x (basis i) (basis j) =
          g.inner x (T (basis i)) (basis j) := (hTg (basis i) (basis j)).symm
      _ = g.inner x (lam i • basis i) (basis j) := by rw [hT_eig i]
      _ = if i = j then lam i else 0 := by
          by_cases hij : i = j
          · simp [hij, hg_orth]
          · simp [hij, hg_orth]
  have hginv :
      MetricInverseInBasis_gen
        (I := I) g x basis (identityInvMetric (Idx := Fin n)) := by
    intro i j
    constructor
    · simp [identityInvMetric, diagonalInvMetric, hg_orth]
    · simp [identityInvMetric, diagonalInvMetric, hg_orth]
  have hlam_pos : forall i : Fin n, 0 < lam i := by
    intro i
    have hne : basis i ≠ 0 := by
      simpa [basis] using ob.orthonormal.ne_zero i
    have hpos : 0 < h.inner x (basis i) (basis i) := h.pos x (basis i) hne
    have hii := hh_diag i i
    rw [hii] at hpos
    simpa using hpos
  have hC_pos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hlam_lower : forall i : Fin n, C⁻¹ <= lam i := by
    intro i
    have hlow := (hequiv (basis i)).1
    have hgii := hg_orth i i
    have hhii := hh_diag i i
    simpa [hgii, hhii] using hlow
  have hmu_nonneg : forall i : Fin n, 0 <= mu i := by
    intro i
    exact le_of_lt (inv_pos.mpr (hlam_pos i))
  have hmu_le : forall i : Fin n, mu i <= C := by
    intro i
    have h :=
      (one_div_le (hlam_pos i) hC_pos).mpr (by
        simpa [one_div] using hlam_lower i)
    simpa [mu, one_div] using h
  have hhinv :
      MetricInverseInBasis_gen
        (I := I) h x basis (diagonalInvMetric mu) := by
    intro i j
    have hmulam (i : Fin n) : mu i * lam i = 1 := by
      simpa [mu] using inv_mul_cancel₀ (ne_of_gt (hlam_pos i))
    have hlammu (i : Fin n) : lam i * mu i = 1 := by
      simpa [mu] using mul_inv_cancel₀ (ne_of_gt (hlam_pos i))
    constructor
    · rw [Finset.sum_eq_single i]
      · by_cases hij : i = j
        · subst j
          simp [diagonalInvMetric, hh_diag, hmulam]
        · simp [diagonalInvMetric, hh_diag, hij]
      · intro k _ hk
        simp [diagonalInvMetric, Ne.symm hk]
      · intro hi
        exact False.elim (hi (Finset.mem_univ i))
    · rw [Finset.sum_eq_single j]
      · by_cases hij : i = j
        · subst j
          simp [diagonalInvMetric, hh_diag, hlammu]
        · simp [diagonalInvMetric, hh_diag, hij]
      · intro k _ hk
        simp [diagonalInvMetric, hk]
      · intro hj
        exact False.elim (hj (Finset.mem_univ j))
  exact ⟨mu, basis, hginv, hhinv, hmu_nonneg, hmu_le⟩


omit [FiniteDimensional ℝ E] in
theorem metric_equiv_symm
    (g h : SmoothMetric_gen I M) (x : M) {C : Real}
    (hC : 1 <= C)
    (hequiv :
      forall v : TangentSpace I x,
        C⁻¹ * g.inner x v v <= h.inner x v v /\
          h.inner x v v <= C * g.inner x v v) :
    forall v : TangentSpace I x,
      C⁻¹ * h.inner x v v <= g.inner x v v /\
        g.inner x v v <= C * h.inner x v v := by
  intro v
  have hC_pos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hC_nonneg : 0 <= C := le_of_lt hC_pos
  have hCinv_nonneg : 0 <= C⁻¹ := inv_nonneg.mpr hC_nonneg
  have hlow := (hequiv v).1
  have hhigh := (hequiv v).2
  constructor
  · calc
      C⁻¹ * h.inner x v v <= C⁻¹ * (C * g.inner x v v) :=
        mul_le_mul_of_nonneg_left hhigh hCinv_nonneg
      _ = g.inner x v v := by
        field_simp [hC_pos.ne']
  · calc
      g.inner x v v = C * (C⁻¹ * g.inner x v v) := by
        field_simp [hC_pos.ne']
      _ <= C * h.inner x v v :=
        mul_le_mul_of_nonneg_left hlow hC_nonneg



theorem normSq0S_upper_le_of_equiv
    (g h : SmoothMetric_gen I M) (x : M) (s : Nat) {C : Real}
    (hC : 1 <= C)
    (hequiv :
      forall v : TangentSpace I x,
        C⁻¹ * g.inner x v v <= h.inner x v v /\
          h.inner x v v <= C * g.inner x v v)
    (T : Tensor0SSpace s I x) :
    normSq0S (I := I) h x s T <=
      C ^ s * normSq0S (I := I) g x s T := by
  obtain ⟨mu, basis, hginv, hhinv, hmu_nonneg, hmu_le⟩ :=
    exists_diagInv_of_equiv (I := I) g h x hC hequiv
  exact normSq0S_diag_le
    (I := I) (g := g) (h := h) (x := x) (s := s)
    basis mu C hginv hhinv hmu_nonneg hmu_le T



theorem normSq0S_lower_le_of_equiv
    (g h : SmoothMetric_gen I M) (x : M) (s : Nat) {C : Real}
    (hC : 1 <= C)
    (hequiv :
      forall v : TangentSpace I x,
        C⁻¹ * g.inner x v v <= h.inner x v v /\
          h.inner x v v <= C * g.inner x v v)
    (T : Tensor0SSpace s I x) :
    (C ^ s)⁻¹ * normSq0S (I := I) g x s T <=
      normSq0S (I := I) h x s T := by
  have hsymm := metric_equiv_symm (I := I) g h x hC hequiv
  have hupper :=
    normSq0S_upper_le_of_equiv
      (I := I) h g x s hC hsymm T
  have hC_pos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hpow_pos : 0 < C ^ s := pow_pos hC_pos s
  rw [inv_mul_le_iff₀ hpow_pos]
  exact hupper



theorem normSq0S_le_of_metric_equiv
    (g h : SmoothMetric_gen I M) (x : M) (s : Nat) {C : Real}
    (hC : 1 <= C)
    (hequiv :
      forall v : TangentSpace I x,
        C⁻¹ * g.inner x v v <= h.inner x v v /\
          h.inner x v v <= C * g.inner x v v)
    (T : Tensor0SSpace s I x) :
    C ^ (-(s : Int)) * normSq0S (I := I) g x s T <=
      normSq0S (I := I) h x s T /\
    normSq0S (I := I) h x s T <=
      C ^ (s : Int) * normSq0S (I := I) g x s T := by
  have hlower :=
    normSq0S_lower_le_of_equiv
      (I := I) g h x s hC hequiv T
  have hupper :=
    normSq0S_upper_le_of_equiv
      (I := I) g h x s hC hequiv T
  constructor
  · simpa using hlower
  · simpa using hupper






theorem sqrt_normSq0S_le_of_metric_equiv
    (g h : SmoothMetric_gen I M) (x : M) (s : Nat) {C : Real}
    (hC : 1 <= C)
    (hequiv :
      forall v : TangentSpace I x,
        C⁻¹ * g.inner x v v <= h.inner x v v /\
          h.inner x v v <= C * g.inner x v v)
    (T : Tensor0SSpace s I x) :
    Real.sqrt (normSq0S (I := I) h x s T) <=
      Real.sqrt (C ^ s) * Real.sqrt (normSq0S (I := I) g x s T) := by
  have hub := normSq0S_upper_le_of_equiv (I := I) g h x s hC hequiv T
  have hCs_nonneg : (0 : Real) <= C ^ s := pow_nonneg (le_trans zero_le_one hC) s
  calc Real.sqrt (normSq0S (I := I) h x s T)
      <= Real.sqrt (C ^ s * normSq0S (I := I) g x s T) := Real.sqrt_le_sqrt hub
    _ = Real.sqrt (C ^ s) * Real.sqrt (normSq0S (I := I) g x s T) :=
        Real.sqrt_mul hCs_nonneg _

end MetricEquiv

section PointwiseCS

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]


private theorem sqrt_prod {α : Type*} (s : Finset α) (f : α -> Real)
    (hf : ∀ a ∈ s, 0 <= f a) :
    Real.sqrt (∏ a ∈ s, f a) = ∏ a ∈ s, Real.sqrt (f a) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
      rw [Finset.prod_cons, Finset.prod_cons,
        Real.sqrt_mul (hf a (Finset.mem_cons_self a s)),
        ih (fun b hb => hf b (Finset.mem_cons_of_mem hb))]






theorem abs_apply_le_sqrt_normSq0S
    (g : SmoothMetric_gen I M) (x : M) (s : Nat)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hON : forall i j : Idx,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (T : Tensor0SSpace s I x) (v : Fin s -> TangentSpace I x) :
    |T v| <=
      Real.sqrt (normSq0S (I := I) g x s T) *
        ∏ a : Fin s, Real.sqrt (g.inner x (v a) (v a)) := by
  classical

  have hinv : MetricInverseInBasis_gen (I := I) g x basis
      (identityInvMetric (Idx := Idx)) := by
    intro i j
    constructor <;> simp [identityInvMetric, diagonalInvMetric, hON]

  have hexp : T v = ∑ I0 : Fin s -> Idx,
      (∏ a : Fin s, basis.repr (v a) (I0 a)) *
        T (fun a : Fin s => basis (I0 a)) := by
    calc T v
        = T (fun a : Fin s => ∑ i : Idx, basis.repr (v a) i • basis i) := by
          congr 1
          funext a
          exact (basis.sum_repr (v a)).symm
      _ = ∑ I0 : Fin s -> Idx,
            T (fun a : Fin s => basis.repr (v a) (I0 a) • basis (I0 a)) :=
          T.map_sum (fun a i => basis.repr (v a) i • basis i)
      _ = ∑ I0 : Fin s -> Idx,
            (∏ a : Fin s, basis.repr (v a) (I0 a)) *
              T (fun a : Fin s => basis (I0 a)) := by
          refine Finset.sum_congr rfl fun I0 _ => ?_
          rw [T.map_smul_univ, smul_eq_mul]
  rw [hexp]

  have hCS2 : (∑ I0 : Fin s -> Idx,
        (∏ a : Fin s, basis.repr (v a) (I0 a)) *
          T (fun a : Fin s => basis (I0 a))) ^ 2 <=
      (∑ I0 : Fin s -> Idx, (∏ a : Fin s, basis.repr (v a) (I0 a)) ^ 2) *
        (∑ I0 : Fin s -> Idx, T (fun a : Fin s => basis (I0 a)) ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
  have habs : |∑ I0 : Fin s -> Idx,
        (∏ a : Fin s, basis.repr (v a) (I0 a)) *
          T (fun a : Fin s => basis (I0 a))| <=
      Real.sqrt (∑ I0 : Fin s -> Idx,
          (∏ a : Fin s, basis.repr (v a) (I0 a)) ^ 2) *
        Real.sqrt (∑ I0 : Fin s -> Idx,
          T (fun a : Fin s => basis (I0 a)) ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs,
      ← Real.sqrt_mul (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    exact Real.sqrt_le_sqrt hCS2
  refine le_trans habs ?_

  have hfac1 : (∑ I0 : Fin s -> Idx,
        (∏ a : Fin s, basis.repr (v a) (I0 a)) ^ 2)
      = ∏ a : Fin s, ∑ i : Idx, basis.repr (v a) i ^ 2 := by
    rw [Finset.prod_univ_sum]
    refine Finset.sum_congr rfl fun I0 _ => ?_
    rw [← Finset.prod_pow]

  have hPar : ∀ a : Fin s, (∑ i : Idx, basis.repr (v a) i ^ 2)
      = g.inner x (v a) (v a) := by
    intro a
    conv_rhs =>
      rw [show v a = ∑ i : Idx, basis.repr (v a) i • basis i from
        (basis.sum_repr (v a)).symm]
    simp only [map_sum, map_smul, ContinuousLinearMap.coe_sum',
      Finset.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, hON,
      mul_ite, mul_one, mul_zero, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_ite_eq Finset.univ i
      (fun j => basis.repr (v a) j * basis.repr (v a) i)]
    simp [sq]

  have hfac2 : (∑ I0 : Fin s -> Idx, T (fun a : Fin s => basis (I0 a)) ^ 2)
      = normSq0S (I := I) g x s T := by
    rw [normSq0S_identity_eq_sum_sq (I := I) g x s basis hinv]
    refine Finset.sum_congr rfl fun I0 _ => ?_
    rw [component0S_apply]
  rw [hfac1, hfac2, mul_comm]
  refine mul_le_mul_of_nonneg_left (le_of_eq ?_) (Real.sqrt_nonneg _)
  rw [sqrt_prod Finset.univ _ (fun a _ =>
    Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [hPar a]

end PointwiseCS

end

end Tensor0SBundle
