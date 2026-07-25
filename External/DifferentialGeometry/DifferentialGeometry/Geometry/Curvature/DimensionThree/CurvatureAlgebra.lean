import Mathlib.Tactic




















noncomputable section

namespace DifferentialGeometry.Integral.Connection

open scoped BigOperators


def delta3 (i j : Fin 3) : Real :=
  if i = j then 1 else 0


def stdRicci3 (R : Fin 3 -> Fin 3 -> Fin 3 -> Fin 3 -> Real)
    (i j : Fin 3) : Real :=
  R 0 i 0 j + R 1 i 1 j + R 2 i 2 j


def stdScalar3 (R : Fin 3 -> Fin 3 -> Fin 3 -> Fin 3 -> Real) : Real :=
  stdRicci3 R 0 0 + stdRicci3 R 1 1 + stdRicci3 R 2 2







def stdRiemannFromRicciRhs3
    (R : Fin 3 -> Fin 3 -> Fin 3 -> Fin 3 -> Real)
    (i j k l : Fin 3) : Real :=
  delta3 i k * stdRicci3 R j l
    - delta3 i l * stdRicci3 R j k
    - delta3 j k * stdRicci3 R i l
    + delta3 j l * stdRicci3 R i k
    - (1 / 2 : Real) * stdScalar3 R *
        (delta3 i k * delta3 j l - delta3 i l * delta3 j k)






def displayedRiemannFromRicciRhs3
    (R : Fin 3 -> Fin 3 -> Fin 3 -> Fin 3 -> Real)
    (i j k l : Fin 3) : Real :=
  stdRicci3 R i l * delta3 j k
    - stdRicci3 R j l * delta3 i k
    - stdRicci3 R i k * delta3 j l
    + stdRicci3 R j k * delta3 i l
    - (1 / 2 : Real) * stdScalar3 R *
        (delta3 i l * delta3 j k - delta3 j l * delta3 i k)


def stdRiemannFromRicciResidual3
    (R : Fin 3 -> Fin 3 -> Fin 3 -> Fin 3 -> Real)
    (i j k l : Fin 3) : Real :=
  R i j k l - stdRiemannFromRicciRhs3 R i j k l



structure AlgebraicCurvatureSymmetries3
    (R : Fin 3 -> Fin 3 -> Fin 3 -> Fin 3 -> Real) : Prop where
  anti_first : forall i j k l, R j i k l = -R i j k l
  anti_last : forall i j k l, R i j l k = -R i j k l
  block_symm : forall i j k l, R k l i j = R i j k l

private theorem stdRicci3_symm_of_block
    {R : Fin 3 -> Fin 3 -> Fin 3 -> Fin 3 -> Real}
    (h_block : forall i j k l, R k l i j = R i j k l) :
    forall i j, stdRicci3 R i j = stdRicci3 R j i := by
  intro i j
  unfold stdRicci3
  have h0 := h_block 0 i 0 j
  have h1 := h_block 1 i 1 j
  have h2 := h_block 2 i 2 j
  linarith

private theorem stdRiemannFromRicciRhs3_anti_first
    {R : Fin 3 -> Fin 3 -> Fin 3 -> Fin 3 -> Real}
    (hRic_symm : forall i j, stdRicci3 R i j = stdRicci3 R j i) :
    forall i j k l,
      stdRiemannFromRicciRhs3 R j i k l =
        -stdRiemannFromRicciRhs3 R i j k l := by
  intro i j k l
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [stdRiemannFromRicciRhs3, stdScalar3, delta3, hRic_symm] <;> ring

private theorem stdRiemannFromRicciRhs3_anti_last
    {R : Fin 3 -> Fin 3 -> Fin 3 -> Fin 3 -> Real}
    (hRic_symm : forall i j, stdRicci3 R i j = stdRicci3 R j i) :
    forall i j k l,
      stdRiemannFromRicciRhs3 R i j l k =
        -stdRiemannFromRicciRhs3 R i j k l := by
  intro i j k l
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [stdRiemannFromRicciRhs3, stdScalar3, delta3, hRic_symm] <;> ring

private theorem stdRiemannFromRicciRhs3_block_symm
    {R : Fin 3 -> Fin 3 -> Fin 3 -> Fin 3 -> Real}
    (hRic_symm : forall i j, stdRicci3 R i j = stdRicci3 R j i) :
    forall i j k l,
      stdRiemannFromRicciRhs3 R k l i j =
        stdRiemannFromRicciRhs3 R i j k l := by
  intro i j k l
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [stdRiemannFromRicciRhs3, stdScalar3, delta3, hRic_symm] <;> ring

private theorem displayedRiemannFromRicciRhs3_eq_neg_stdRhs
    {R : Fin 3 -> Fin 3 -> Fin 3 -> Fin 3 -> Real}
    (hRic_symm : forall i j, stdRicci3 R i j = stdRicci3 R j i) :
    forall i j k l,
      displayedRiemannFromRicciRhs3 R i j k l =
        -stdRiemannFromRicciRhs3 R i j k l := by
  intro i j k l
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [displayedRiemannFromRicciRhs3, stdRiemannFromRicciRhs3, stdScalar3,
      delta3, hRic_symm] <;> ring



theorem tensor04_fin3_eq_zero_of_ordered_pair_components
    (T : Fin 3 -> Fin 3 -> Fin 3 -> Fin 3 -> Real)
    (h_anti_first : forall i j k l, T j i k l = -T i j k l)
    (h_anti_last : forall i j k l, T i j l k = -T i j k l)
    (h_components : forall i j k l, i < j -> k < l -> T i j k l = 0) :
    forall i j k l, T i j k l = 0 := by
  intro i j k l
  by_cases hij_eq : i = j
  · subst j
    have h := h_anti_first i i k l
    linarith
  by_cases hkl_eq : k = l
  · subst l
    have h := h_anti_last i j k k
    linarith
  rcases lt_or_gt_of_ne hij_eq with hij_lt | hji_lt
  · rcases lt_or_gt_of_ne hkl_eq with hkl_lt | hlk_lt
    · exact h_components i j k l hij_lt hkl_lt
    · have hlast := h_anti_last i j l k
      have h0 := h_components i j l k hij_lt hlk_lt
      linarith
  · rcases lt_or_gt_of_ne hkl_eq with hkl_lt | hlk_lt
    · have hfirst := h_anti_first j i k l
      have h0 := h_components j i k l hji_lt hkl_lt
      linarith
    · have hfirst := h_anti_first j i k l
      have hlast := h_anti_last j i l k
      have h0 := h_components j i l k hji_lt hlk_lt
      linarith




theorem tensor04_fin3_eq_zero_of_ordered_block_components
    (T : Fin 3 -> Fin 3 -> Fin 3 -> Fin 3 -> Real)
    (h_anti_first : forall i j k l, T j i k l = -T i j k l)
    (h_anti_last : forall i j k l, T i j l k = -T i j k l)
    (h_block : forall i j k l, T k l i j = T i j k l)
    (h_components : forall i j k l, i < j -> k < l ->
      (i < k \/ (i = k /\ j <= l)) -> T i j k l = 0) :
    forall i j k l, T i j k l = 0 := by
  apply tensor04_fin3_eq_zero_of_ordered_pair_components T h_anti_first h_anti_last
  intro i j k l hij hkl
  by_cases hlex : i < k \/ (i = k /\ j <= l)
  · exact h_components i j k l hij hkl hlex
  · have hswap_lex : k < i \/ (k = i /\ l <= j) := by
      have h_not_i_lt_k : ¬ i < k := by
        intro hik
        exact hlex (Or.inl hik)
      have hki : k <= i := le_of_not_gt h_not_i_lt_k
      rcases lt_or_eq_of_le hki with hki_lt | hki_eq
      · exact Or.inl hki_lt
      · have hik_eq : i = k := hki_eq.symm
        have h_not_j_le_l : ¬ j <= l := by
          intro hjl
          exact hlex (Or.inr ⟨hik_eq, hjl⟩)
        have hlj : l <= j := le_of_lt (lt_of_not_ge h_not_j_le_l)
        exact Or.inr ⟨hki_eq, hlj⟩
    calc
      T i j k l = T k l i j := by
        exact (h_block i j k l).symm
      _ = 0 := h_components k l i j hkl hij hswap_lex






structure RiemannFromRicci3DResidualPackage
    (R : Fin 3 -> Fin 3 -> Fin 3 -> Fin 3 -> Real) : Prop where
  anti_first : forall i j k l,
    stdRiemannFromRicciResidual3 R j i k l =
      -stdRiemannFromRicciResidual3 R i j k l
  anti_last : forall i j k l,
    stdRiemannFromRicciResidual3 R i j l k =
      -stdRiemannFromRicciResidual3 R i j k l
  block_symm : forall i j k l,
    stdRiemannFromRicciResidual3 R k l i j =
      stdRiemannFromRicciResidual3 R i j k l
  c0101 : stdRiemannFromRicciResidual3 R 0 1 0 1 = 0
  c0102 : stdRiemannFromRicciResidual3 R 0 1 0 2 = 0
  c0112 : stdRiemannFromRicciResidual3 R 0 1 1 2 = 0
  c0202 : stdRiemannFromRicciResidual3 R 0 2 0 2 = 0
  c0212 : stdRiemannFromRicciResidual3 R 0 2 1 2 = 0
  c1212 : stdRiemannFromRicciResidual3 R 1 2 1 2 = 0




theorem residual_package_of_algebraic_curvature_symmetries3
    {R : Fin 3 -> Fin 3 -> Fin 3 -> Fin 3 -> Real}
    (h : AlgebraicCurvatureSymmetries3 R) :
    RiemannFromRicci3DResidualPackage R := by
  have hRic_symm : forall i j, stdRicci3 R i j = stdRicci3 R j i :=
    stdRicci3_symm_of_block h.block_symm
  refine
    { anti_first := ?_
      anti_last := ?_
      block_symm := ?_
      c0101 := ?_
      c0102 := ?_
      c0112 := ?_
      c0202 := ?_
      c0212 := ?_
      c1212 := ?_ }
  · intro i j k l
    have hR := h.anti_first i j k l
    have hRhs := stdRiemannFromRicciRhs3_anti_first hRic_symm i j k l
    unfold stdRiemannFromRicciResidual3
    linarith
  · intro i j k l
    have hR := h.anti_last i j k l
    have hRhs := stdRiemannFromRicciRhs3_anti_last hRic_symm i j k l
    unfold stdRiemannFromRicciResidual3
    linarith
  · intro i j k l
    have hR := h.block_symm i j k l
    have hRhs := stdRiemannFromRicciRhs3_block_symm hRic_symm i j k l
    unfold stdRiemannFromRicciResidual3
    linarith
  · simp [stdRiemannFromRicciResidual3, stdRiemannFromRicciRhs3, stdRicci3,
      stdScalar3, delta3]
    linarith [h.anti_first 0 0 0 0, h.anti_first 1 1 1 1,
      h.anti_first 2 2 2 2, h.anti_first 1 0 1 0,
      h.anti_last 0 1 0 1, h.anti_first 2 0 2 0,
      h.anti_last 0 2 0 2, h.anti_first 2 1 2 1,
      h.anti_last 1 2 1 2]
  · simp [stdRiemannFromRicciResidual3, stdRiemannFromRicciRhs3, stdRicci3,
      stdScalar3, delta3]
    linarith [h.anti_first 1 1 1 2, h.anti_last 2 1 2 2,
      h.anti_first 2 1 2 2]
  · simp [stdRiemannFromRicciResidual3, stdRiemannFromRicciRhs3, stdRicci3,
      stdScalar3, delta3]
    linarith [h.anti_first 0 0 0 2, h.anti_last 2 0 2 2,
      h.anti_first 1 0 1 2, h.anti_last 0 1 2 1]
  · simp [stdRiemannFromRicciResidual3, stdRiemannFromRicciRhs3, stdRicci3,
      stdScalar3, delta3]
    linarith [h.anti_first 0 0 0 0, h.anti_first 1 1 1 1,
      h.anti_first 2 2 2 2, h.anti_first 1 0 1 0,
      h.anti_last 0 1 0 1, h.anti_first 2 0 2 0,
      h.anti_last 0 2 0 2, h.anti_first 2 1 2 1,
      h.anti_last 1 2 1 2]
  · simp [stdRiemannFromRicciResidual3, stdRiemannFromRicciRhs3, stdRicci3,
      stdScalar3, delta3]
    linarith [h.anti_first 0 0 0 1, h.anti_last 1 0 1 1,
      h.anti_first 2 0 2 1, h.anti_last 0 2 1 2]
  · simp [stdRiemannFromRicciResidual3, stdRiemannFromRicciRhs3, stdRicci3,
      stdScalar3, delta3]
    linarith [h.anti_first 0 0 0 0, h.anti_first 1 1 1 1,
      h.anti_first 2 2 2 2, h.anti_first 1 0 1 0,
      h.anti_last 0 1 0 1, h.anti_first 2 0 2 0,
      h.anti_last 0 2 0 2, h.anti_first 2 1 2 1,
      h.anti_last 1 2 1 2]

set_option linter.flexible false in
private theorem residual_ordered_components_of_package
    {R : Fin 3 -> Fin 3 -> Fin 3 -> Fin 3 -> Real}
    (pkg : RiemannFromRicci3DResidualPackage R) :
    forall i j k l, i < j -> k < l ->
      (i < k \/ (i = k /\ j <= l)) ->
      stdRiemannFromRicciResidual3 R i j k l = 0 := by
  intro i j k l hij hkl hlex
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp at hij hkl hlex ⊢
  all_goals
    first
    | simpa using pkg.c0101
    | simpa using pkg.c0102
    | simpa using pkg.c0112
    | simpa using pkg.c0202
    | simpa using pkg.c0212
    | simpa using pkg.c1212



theorem stdRiemannFromRicci3D_of_residual_package
    {R : Fin 3 -> Fin 3 -> Fin 3 -> Fin 3 -> Real}
    (pkg : RiemannFromRicci3DResidualPackage R) :
    forall i j k l, R i j k l = stdRiemannFromRicciRhs3 R i j k l := by
  intro i j k l
  have hz :
      stdRiemannFromRicciResidual3 R i j k l = 0 :=
    tensor04_fin3_eq_zero_of_ordered_block_components
      (stdRiemannFromRicciResidual3 R)
      pkg.anti_first pkg.anti_last pkg.block_symm
      (residual_ordered_components_of_package pkg) i j k l
  unfold stdRiemannFromRicciResidual3 at hz
  linarith



theorem stdRiemannFromRicci3D_of_algebraic_curvature_symmetries
    {R : Fin 3 -> Fin 3 -> Fin 3 -> Fin 3 -> Real}
    (h : AlgebraicCurvatureSymmetries3 R) :
    forall i j k l, R i j k l = stdRiemannFromRicciRhs3 R i j k l :=
  stdRiemannFromRicci3D_of_residual_package
    (residual_package_of_algebraic_curvature_symmetries3 h)








theorem displayedRiemannFromRicci3D_of_algebraic_curvature_symmetries
    {R : Fin 3 -> Fin 3 -> Fin 3 -> Fin 3 -> Real}
    (h : AlgebraicCurvatureSymmetries3 R) :
    forall i j k l, R i j l k = displayedRiemannFromRicciRhs3 R i j k l := by
  intro i j k l
  have hRic_symm : forall a b, stdRicci3 R a b = stdRicci3 R b a :=
    stdRicci3_symm_of_block h.block_symm
  have hstd := stdRiemannFromRicci3D_of_algebraic_curvature_symmetries h i j k l
  have hflip := h.anti_last i j k l
  have hrhs := displayedRiemannFromRicciRhs3_eq_neg_stdRhs hRic_symm i j k l
  linarith

end DifferentialGeometry.Integral.Connection
