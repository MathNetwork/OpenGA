import DifferentialGeometry.Geometry.Flow.RicciFlow.Basic.Core

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedFintypeInType false








noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]



section Components

variable {Idx : Type*} [Fintype Idx]

private def raise2By
    (G A : Idx -> Idx -> Real) (i j : Idx) : Real :=
  ∑ a : Idx, ∑ b : Idx, G i a * G j b * A a b

private def oneUpBy
    (G A : Idx -> Idx -> Real) (i k : Idx) : Real :=
  ∑ a : Idx, G k a * A i a

private def quadraticBy
    (G A : Idx -> Idx -> Real) (i j : Idx) : Real :=
  ∑ k : Idx, oneUpBy G A i k * A k j

private theorem split_raise2By_tail
    (G B : Idx -> Idx -> Real) (c : Real) (i j : Idx)
    (P Q : Idx -> Idx -> Real) :
    c * (∑ a : Idx, ∑ b : Idx,
        (P a b + Q a b + G i a * G j b * B a b)) =
      c * (∑ a : Idx, ∑ b : Idx, (P a b + Q a b)) +
        c * raise2By G B i j := by
  classical
  unfold raise2By
  simp [Finset.sum_add_distrib, Finset.mul_sum, mul_add,
    add_assoc, mul_left_comm, mul_comm]

private theorem sum_two_sub_cancel_scaled
    (L C Q R : Idx -> Idx -> Real) :
    (∑ i : Idx, ∑ j : Idx, (L i j - 2 * C i j - 2 * Q i j) * R i j) +
        4 * (∑ i : Idx, ∑ j : Idx, Q i j * R i j) +
        (∑ i : Idx, ∑ j : Idx, (L i j - 2 * C i j - 2 * Q i j) * R i j) =
      2 * (∑ i : Idx, ∑ j : Idx, L i j * R i j) +
        4 * (-(∑ i : Idx, ∑ j : Idx, C i j * R i j)) := by
  classical
  let LS : Real := ∑ i : Idx, ∑ j : Idx, L i j * R i j
  let CS : Real := ∑ i : Idx, ∑ j : Idx, C i j * R i j
  let QS : Real := ∑ i : Idx, ∑ j : Idx, Q i j * R i j
  have hpoint (i j : Idx) :
      (L i j - 2 * C i j - 2 * Q i j) * R i j =
        L i j * R i j - (C i j * R i j) * 2 - (Q i j * R i j) * 2 := by
    ring
  have hsum :
      (∑ i : Idx, ∑ j : Idx, (L i j - 2 * C i j - 2 * Q i j) * R i j) =
        LS - 2 * CS - 2 * QS := by
    calc
      (∑ i : Idx, ∑ j : Idx, (L i j - 2 * C i j - 2 * Q i j) * R i j)
          =
        ∑ i : Idx, ∑ j : Idx,
          (L i j * R i j - (C i j * R i j) * 2 - (Q i j * R i j) * 2) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          exact hpoint i j
      _ =
        (∑ i : Idx, ∑ j : Idx, L i j * R i j) -
          (∑ i : Idx, ∑ j : Idx, (C i j * R i j) * 2) -
            (∑ i : Idx, ∑ j : Idx, (Q i j * R i j) * 2) := by
          simp only [Finset.sum_sub_distrib]
      _ =
        LS - CS * 2 - QS * 2 := by
          simp only [LS, CS, QS, Finset.sum_mul]
      _ =
        LS - 2 * CS - 2 * QS := by
          ring
  rw [hsum]
  change (LS - 2 * CS - 2 * QS) + 4 * QS + (LS - 2 * CS - 2 * QS) =
    2 * LS + 4 * (-CS)
  ring

private theorem sum_mul_raise2By_comm
    (G A B : Idx -> Idx -> Real)
    (hG : forall i j, G i j = G j i) :
    (∑ i : Idx, ∑ j : Idx, A i j * raise2By G B i j) =
      ∑ i : Idx, ∑ j : Idx, B i j * raise2By G A i j := by
  classical
  unfold raise2By
  calc
    (∑ i : Idx, ∑ j : Idx,
        A i j * (∑ a : Idx, ∑ b : Idx, G i a * G j b * B a b))
        =
      ∑ i : Idx, ∑ j : Idx, ∑ a : Idx, ∑ b : Idx,
        A i j * (G i a * G j b * B a b) := by
          simp [Finset.mul_sum]
    _ =
      ∑ a : Idx, ∑ b : Idx, ∑ i : Idx, ∑ j : Idx,
        A i j * (G i a * G j b * B a b) := by
          calc
            (∑ i : Idx, ∑ j : Idx, ∑ a : Idx, ∑ b : Idx,
              A i j * (G i a * G j b * B a b))
                =
              ∑ i : Idx, ∑ a : Idx, ∑ j : Idx, ∑ b : Idx,
                A i j * (G i a * G j b * B a b) := by
                  refine Finset.sum_congr rfl fun i _ => ?_
                  rw [Finset.sum_comm]
            _ =
              ∑ a : Idx, ∑ i : Idx, ∑ j : Idx, ∑ b : Idx,
                A i j * (G i a * G j b * B a b) := by
                  rw [Finset.sum_comm]
            _ =
              ∑ a : Idx, ∑ b : Idx, ∑ i : Idx, ∑ j : Idx,
                A i j * (G i a * G j b * B a b) := by
                  refine Finset.sum_congr rfl fun a _ => ?_
                  calc
                    (∑ i : Idx, ∑ j : Idx, ∑ b : Idx,
                      A i j * (G i a * G j b * B a b))
                        =
                      ∑ i : Idx, ∑ b : Idx, ∑ j : Idx,
                        A i j * (G i a * G j b * B a b) := by
                          refine Finset.sum_congr rfl fun i _ => ?_
                          rw [Finset.sum_comm]
                    _ =
                      ∑ b : Idx, ∑ i : Idx, ∑ j : Idx,
                        A i j * (G i a * G j b * B a b) := by
                          rw [Finset.sum_comm]
    _ =
      ∑ a : Idx, ∑ b : Idx, ∑ i : Idx, ∑ j : Idx,
        B a b * (G a i * G b j * A i j) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          refine Finset.sum_congr rfl fun b _ => ?_
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hG i a, hG j b]
          ring
    _ =
      ∑ a : Idx, ∑ b : Idx,
        B a b * (∑ i : Idx, ∑ j : Idx, G a i * G b j * A i j) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          refine Finset.sum_congr rfl fun b _ => ?_
          simp [Finset.mul_sum, mul_left_comm, mul_comm]

private theorem sum_contraction_mul_eq_four_sum
    (R4 : Idx -> Idx -> Idx -> Idx -> Real)
    (A : Idx -> Idx -> Real) :
    (∑ i : Idx, ∑ j : Idx,
      (∑ k : Idx, ∑ l : Idx, R4 i k j l * A k l) * A i j) =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        R4 i k j l * A i j * A k l := by
  classical
  calc
    (∑ i : Idx, ∑ j : Idx,
      (∑ k : Idx, ∑ l : Idx, R4 i k j l * A k l) * A i j)
        =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        (R4 i k j l * A k l) * A i j := by
        simp [Finset.sum_mul]
    _ =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        R4 i k j l * A i j * A k l := by
        refine Finset.sum_congr rfl fun i _ => ?_
        refine Finset.sum_congr rfl fun j _ => ?_
        refine Finset.sum_congr rfl fun k _ => ?_
        refine Finset.sum_congr rfl fun l _ => ?_
        ring

private theorem quadraticBy_eq_sum_right
    (G A : Idx -> Idx -> Real)
    (hG : forall i j, G i j = G j i)
    (hA : forall i j, A i j = A j i)
    (i j : Idx) :
    quadraticBy G A i j =
      ∑ a : Idx, ∑ b : Idx, G a b * A i a * A j b := by
  classical
  unfold quadraticBy oneUpBy
  calc
    (∑ k : Idx, (∑ a : Idx, G k a * A i a) * A k j)
        =
      ∑ k : Idx, ∑ a : Idx, G k a * A i a * A k j := by
        simp [Finset.sum_mul, mul_assoc]
    _ =
      ∑ k : Idx, ∑ a : Idx, G k a * A i a * A j k := by
        refine Finset.sum_congr rfl fun k _ => ?_
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [hA k j]
    _ =
      ∑ a : Idx, ∑ k : Idx, G k a * A i a * A j k := by
        rw [Finset.sum_comm]
    _ =
      ∑ a : Idx, ∑ b : Idx, G a b * A i a * A j b := by
        refine Finset.sum_congr rfl fun a _ => ?_
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [hG b a]

private theorem quadraticBy_eq_sum_left
    (G A : Idx -> Idx -> Real)
    (hG : forall i j, G i j = G j i)
    (hA : forall i j, A i j = A j i)
    (i j : Idx) :
    quadraticBy G A i j =
      ∑ a : Idx, ∑ b : Idx, G a b * A a i * A b j := by
  classical
  calc
    quadraticBy G A i j =
      ∑ a : Idx, ∑ b : Idx, G a b * A i a * A j b := by
        exact quadraticBy_eq_sum_right G A hG hA i j
    _ =
      ∑ a : Idx, ∑ b : Idx, G a b * A a i * A b j := by
        refine Finset.sum_congr rfl fun a _ => ?_
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [hA i a, hA j b]

private theorem metricDerivativeQuadraticTerms_eq_four
    (G A : Idx -> Idx -> Real)
    (hG : forall i j, G i j = G j i)
    (hA : forall i j, A i j = A j i) :
    (∑ i : Idx, ∑ j : Idx,
      A i j *
        (∑ a : Idx, ∑ b : Idx,
          (2 * raise2By G A i a * G j b * A a b +
            G i a * (2 * raise2By G A j b) * A a b))) =
      4 * (∑ i : Idx, ∑ j : Idx,
        quadraticBy G A i j * raise2By G A i j) := by
  classical
  have hright :
      (∑ i : Idx, ∑ j : Idx,
        A i j * (∑ a : Idx, ∑ b : Idx,
          2 * raise2By G A i a * G j b * A a b)) =
        2 * (∑ i : Idx, ∑ a : Idx,
          quadraticBy G A i a * raise2By G A i a) := by
    calc
      (∑ i : Idx, ∑ j : Idx,
        A i j * (∑ a : Idx, ∑ b : Idx,
          2 * raise2By G A i a * G j b * A a b))
          =
        ∑ i : Idx, ∑ j : Idx, ∑ a : Idx, ∑ b : Idx,
          A i j * (2 * raise2By G A i a * G j b * A a b) := by
            simp [Finset.mul_sum]
      _ =
        ∑ i : Idx, ∑ a : Idx, ∑ j : Idx, ∑ b : Idx,
          A i j * (2 * raise2By G A i a * G j b * A a b) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.sum_comm]
      _ =
        ∑ i : Idx, ∑ a : Idx,
          2 * raise2By G A i a *
            (∑ j : Idx, ∑ b : Idx, G j b * A i j * A a b) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            refine Finset.sum_congr rfl fun a _ => ?_
            simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
      _ =
        ∑ i : Idx, ∑ a : Idx,
          2 * raise2By G A i a * quadraticBy G A i a := by
            refine Finset.sum_congr rfl fun i _ => ?_
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [← quadraticBy_eq_sum_right G A hG hA i a]
      _ =
        2 * (∑ i : Idx, ∑ a : Idx,
          quadraticBy G A i a * raise2By G A i a) := by
            simp [Finset.mul_sum, mul_left_comm, mul_comm]
  have hleft :
      (∑ i : Idx, ∑ j : Idx,
        A i j * (∑ a : Idx, ∑ b : Idx,
          G i a * (2 * raise2By G A j b) * A a b)) =
        2 * (∑ j : Idx, ∑ b : Idx,
          quadraticBy G A j b * raise2By G A j b) := by
    calc
      (∑ i : Idx, ∑ j : Idx,
        A i j * (∑ a : Idx, ∑ b : Idx,
          G i a * (2 * raise2By G A j b) * A a b))
          =
        ∑ i : Idx, ∑ j : Idx, ∑ a : Idx, ∑ b : Idx,
          A i j * (G i a * (2 * raise2By G A j b) * A a b) := by
            simp [Finset.mul_sum]
      _ =
        ∑ j : Idx, ∑ b : Idx, ∑ i : Idx, ∑ a : Idx,
          A i j * (G i a * (2 * raise2By G A j b) * A a b) := by
            calc
              (∑ i : Idx, ∑ j : Idx, ∑ a : Idx, ∑ b : Idx,
                A i j * (G i a * (2 * raise2By G A j b) * A a b))
                  =
                ∑ j : Idx, ∑ i : Idx, ∑ a : Idx, ∑ b : Idx,
                  A i j * (G i a * (2 * raise2By G A j b) * A a b) := by
                    rw [Finset.sum_comm]
              _ =
                ∑ j : Idx, ∑ i : Idx, ∑ b : Idx, ∑ a : Idx,
                  A i j * (G i a * (2 * raise2By G A j b) * A a b) := by
                    refine Finset.sum_congr rfl fun j _ => ?_
                    refine Finset.sum_congr rfl fun i _ => ?_
                    rw [Finset.sum_comm]
              _ =
                ∑ j : Idx, ∑ b : Idx, ∑ i : Idx, ∑ a : Idx,
                  A i j * (G i a * (2 * raise2By G A j b) * A a b) := by
                    refine Finset.sum_congr rfl fun j _ => ?_
                    rw [Finset.sum_comm]
      _ =
        ∑ j : Idx, ∑ b : Idx,
          2 * raise2By G A j b *
            (∑ i : Idx, ∑ a : Idx, G i a * A i j * A a b) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            refine Finset.sum_congr rfl fun b _ => ?_
            simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
      _ =
        ∑ j : Idx, ∑ b : Idx,
          2 * raise2By G A j b * quadraticBy G A j b := by
            refine Finset.sum_congr rfl fun j _ => ?_
            refine Finset.sum_congr rfl fun b _ => ?_
            rw [← quadraticBy_eq_sum_left G A hG hA j b]
      _ =
        2 * (∑ j : Idx, ∑ b : Idx,
          quadraticBy G A j b * raise2By G A j b) := by
            simp [Finset.mul_sum, mul_left_comm, mul_comm]
  calc
    (∑ i : Idx, ∑ j : Idx,
      A i j *
        (∑ a : Idx, ∑ b : Idx,
          (2 * raise2By G A i a * G j b * A a b +
            G i a * (2 * raise2By G A j b) * A a b)))
        =
      (∑ i : Idx, ∑ j : Idx,
        A i j * (∑ a : Idx, ∑ b : Idx,
          2 * raise2By G A i a * G j b * A a b)) +
      (∑ i : Idx, ∑ j : Idx,
        A i j * (∑ a : Idx, ∑ b : Idx,
          G i a * (2 * raise2By G A j b) * A a b)) := by
          simp [Finset.sum_add_distrib, Finset.mul_sum, mul_add,
            mul_left_comm, mul_comm]
    _ =
      2 * (∑ i : Idx, ∑ j : Idx,
        quadraticBy G A i j * raise2By G A i j) +
      2 * (∑ i : Idx, ∑ j : Idx,
        quadraticBy G A i j * raise2By G A i j) := by
          rw [hright, hleft]
    _ =
      4 * (∑ i : Idx, ∑ j : Idx,
        quadraticBy G A i j * raise2By G A i j) := by
          ring

private theorem ricciNormDerivativeSimplifies_pure
    (G A L C : Idx -> Idx -> Real)
    (hG : forall i j, G i j = G j i)
    (hA : forall i j, A i j = A j i) :
    (∑ i : Idx, ∑ j : Idx,
      ((L i j - 2 * C i j - 2 * quadraticBy G A i j) *
          raise2By G A i j +
        A i j *
          (∑ a : Idx, ∑ b : Idx,
            (2 * raise2By G A i a * G j b * A a b +
              G i a * (2 * raise2By G A j b) * A a b +
                G i a * G j b *
                  (L a b - 2 * C a b - 2 * quadraticBy G A a b))))) =
      2 * (∑ i : Idx, ∑ j : Idx, L i j * raise2By G A i j) +
        4 * (-(∑ i : Idx, ∑ j : Idx, C i j * raise2By G A i j)) := by
  classical
  let B : Idx -> Idx -> Real :=
    fun i j => L i j - 2 * C i j - 2 * quadraticBy G A i j
  have hpair :
      (∑ i : Idx, ∑ j : Idx, A i j * raise2By G B i j) =
        ∑ i : Idx, ∑ j : Idx, B i j * raise2By G A i j :=
    sum_mul_raise2By_comm G A B hG
  have hmetric := metricDerivativeQuadraticTerms_eq_four G A hG hA
  calc
    (∑ i : Idx, ∑ j : Idx,
      ((L i j - 2 * C i j - 2 * quadraticBy G A i j) *
          raise2By G A i j +
        A i j *
          (∑ a : Idx, ∑ b : Idx,
            (2 * raise2By G A i a * G j b * A a b +
              G i a * (2 * raise2By G A j b) * A a b +
                G i a * G j b *
                  (L a b - 2 * C a b - 2 * quadraticBy G A a b)))))
        =
      ∑ i : Idx, ∑ j : Idx,
        (B i j * raise2By G A i j +
          A i j *
            (∑ a : Idx, ∑ b : Idx,
              (2 * raise2By G A i a * G j b * A a b +
                G i a * (2 * raise2By G A j b) * A a b)) +
          A i j * raise2By G B i j) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          let P : Idx -> Idx -> Real :=
            fun a b => 2 * raise2By G A i a * G j b * A a b
          let Q : Idx -> Idx -> Real :=
            fun a b => G i a * (2 * raise2By G A j b) * A a b
          change
            B i j * raise2By G A i j +
                A i j * (∑ a : Idx, ∑ b : Idx,
                  (P a b + Q a b + G i a * G j b * B a b)) =
              B i j * raise2By G A i j +
                A i j * (∑ a : Idx, ∑ b : Idx, (P a b + Q a b)) +
                  A i j * raise2By G B i j
          rw [split_raise2By_tail]
          ring
    _ =
      (∑ i : Idx, ∑ j : Idx,
        B i j * raise2By G A i j) +
      (∑ i : Idx, ∑ j : Idx,
        A i j *
          (∑ a : Idx, ∑ b : Idx,
            (2 * raise2By G A i a * G j b * A a b +
              G i a * (2 * raise2By G A j b) * A a b))) +
      (∑ i : Idx, ∑ j : Idx,
        A i j * raise2By G B i j) := by
          simp [Finset.sum_add_distrib, add_assoc]
    _ =
      (∑ i : Idx, ∑ j : Idx,
        B i j * raise2By G A i j) +
      4 * (∑ i : Idx, ∑ j : Idx,
        quadraticBy G A i j * raise2By G A i j) +
      (∑ i : Idx, ∑ j : Idx,
        B i j * raise2By G A i j) := by
          rw [hmetric, hpair]
    _ =
      2 * (∑ i : Idx, ∑ j : Idx, L i j * raise2By G A i j) +
        4 * (-(∑ i : Idx, ∑ j : Idx, C i j * raise2By G A i j)) := by
          simpa [B, sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm] using
            sum_two_sub_cancel_scaled
              (Idx := Idx)
              (L := L)
              (C := C)
              (Q := quadraticBy G A)
              (R := raise2By G A)



def ricciTwoTensorField
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) :
    Real -> DifferentialGeometry.Integral.Connection.RawTwoTensorField (I := I) (M := M) :=
  fun t x X Y => S.ricciAt t x (DifferentialGeometry.Integral.Connection.vec2 X Y)

omit [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem ricciTwoTensorField_apply
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (t : Real) (x : M) (X Y : TangentSpace I x) :
    ricciTwoTensorField (I := I) S t x X Y =
      S.ricciAt t x (DifferentialGeometry.Integral.Connection.vec2 X Y) := by
  rfl


def ricciCompInFrame
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (i j : Idx) : Real :=
  S.ricciAt t x (DifferentialGeometry.Integral.Connection.vec2 (frame i x) (frame j x))

omit [Fintype Idx] in
omit [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem ricciCompInFrame_apply
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (i j : Idx) :
    ricciCompInFrame (I := I) S frame t x i j =
      S.ricciAt t x (DifferentialGeometry.Integral.Connection.vec2 (frame i x) (frame j x)) := by
  rfl




abbrev raisedRicciCompInFrame
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (i j : Idx) : Real :=
  DifferentialGeometry.Integral.Connection.raisedRicciComponentsInFrame (I := I) (M := M) (Time := Real)
    (ricciTwoTensorField (I := I) S) gInv frame t x i j

omit [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem raisedRicciCompInFrame_apply
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (i j : Idx) :
    raisedRicciCompInFrame (I := I) S gInv frame t x i j =
      ∑ a : Idx, ∑ b : Idx,
        gInv t x i a * gInv t x j b *
          ricciCompInFrame (I := I) S frame t x a b := by
  rfl



def ricciOneUpCompInFrame
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (i k : Idx) : Real :=
  ∑ a : Idx, gInv t x k a * ricciCompInFrame (I := I) S frame t x i a

omit [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem ricciOneUpCompInFrame_apply
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (i k : Idx) :
    ricciOneUpCompInFrame (I := I) S gInv frame t x i k =
      ∑ a : Idx, gInv t x k a * ricciCompInFrame (I := I) S frame t x i a := by
  rfl


def ricciQuadraticCompInFrame
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (i j : Idx) : Real :=
  ∑ k : Idx,
    ricciOneUpCompInFrame (I := I) S gInv frame t x i k *
      ricciCompInFrame (I := I) S frame t x k j

omit [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem ricciQuadraticCompInFrame_apply
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (i j : Idx) :
    ricciQuadraticCompInFrame (I := I) S gInv frame t x i j =
      ∑ k : Idx,
        ricciOneUpCompInFrame (I := I) S gInv frame t x i k *
          ricciCompInFrame (I := I) S frame t x k j := by
  rfl


def rmRicciContractionCompInFrame
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (i j : Idx) : Real :=
  ∑ k : Idx, ∑ l : Idx,
    DifferentialGeometry.Integral.Connection.rm04Comp (I := I) (Rm04 t) frame x i k j l *
      raisedRicciCompInFrame (I := I) S gInv frame t x k l

omit [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem rmRicciContractionCompInFrame_apply
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (i j : Idx) :
    rmRicciContractionCompInFrame (I := I) S Rm04 gInv frame t x i j =
      ∑ k : Idx, ∑ l : Idx,
        DifferentialGeometry.Integral.Connection.rm04Comp (I := I) (Rm04 t) frame x i k j l *
          raisedRicciCompInFrame (I := I) S gInv frame t x k l := by
  rfl





def ricciEvolutionRHSInFrame
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j : Idx) : Real :=
  roughLapRic t x i j -
    2 * rmRicciContractionCompInFrame (I := I) S Rm04 gInv frame t x i j -
      2 * ricciQuadraticCompInFrame (I := I) S gInv frame t x i j

omit [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem ricciEvolutionRHSInFrame_apply
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j : Idx) :
    ricciEvolutionRHSInFrame (I := I) S Rm04 gInv frame roughLapRic t x i j =
      roughLapRic t x i j -
        2 * rmRicciContractionCompInFrame (I := I) S Rm04 gInv frame t x i j -
          2 * ricciQuadraticCompInFrame (I := I) S gInv frame t x i j := by
  rfl



abbrev ricciNormSqInFrame
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) :
    Real -> M -> Real :=
  DifferentialGeometry.Integral.Connection.ricciNormSqInFrame (I := I) (M := M) (Time := Real)
    (ricciTwoTensorField (I := I) S) gInv frame

omit [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem ricciNormSqInFrame_apply
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) :
    ricciNormSqInFrame (I := I) S gInv frame t x =
      ∑ i : Idx, ∑ j : Idx,
        ricciCompInFrame (I := I) S frame t x i j *
          raisedRicciCompInFrame (I := I) S gInv frame t x i j := by
  rfl




omit [SigmaCompactSpace M] in
theorem ricciNormSq_basis
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [DecidableEq Idx]
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    {t : Real} {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv : MetricInverseInBasis_gen
      (I := I) (M := M) (S.family.metric t) x basis
      (fun i j : Idx => gInv t x i j))
    (hbasis : ∀ i : Idx, basis i = frame i x) :
    ricciNormSqInFrame (I := I) S gInv frame t x =
      normSq0S (I := I) (S.family.metric t) x 2 (S.ricci t x) := by
  classical
  rw [normSq0S_eq_inner]
  rw [inner0S_two_eq_coord
    (I := I) (S.family.metric t) x basis
    (fun i j : Idx => gInv t x i j) hinv (S.ricci t x) (S.ricci t x)]
  simp only [ricciNormSqInFrame, DifferentialGeometry.Integral.Connection.ricciNormSqInFrame_apply,
    ricciTwoTensorField_apply, SolutionOn.ricciAt_eq,
    DifferentialGeometry.Integral.Connection.raisedRicciComponentsInFrame_apply, SolutionOn.ricci_eq,
    SolutionFamily.ricci_apply, DifferentialGeometry.Integral.Connection.vec2, hbasis, Fin.isValue,
    Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun l _ => ?_
  have hij :
      DifferentialGeometry.Integral.Connection.vec2 (I := I) (frame i x) (frame j x) =
        (fun a : Fin 2 => if a = 0 then frame i x else frame j x) := by
    funext a
    fin_cases a <;> simp [DifferentialGeometry.Integral.Connection.vec2]
  have hkl :
      DifferentialGeometry.Integral.Connection.vec2 (I := I) (frame k x) (frame l x) =
        (fun a : Fin 2 => if a = 0 then frame k x else frame l x) := by
    funext a
    fin_cases a <;> simp [DifferentialGeometry.Integral.Connection.vec2]
  rw [hij, hkl]




abbrev roughLapRicciInnerInFrame
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) :
    Real -> M -> Real :=
  DifferentialGeometry.Integral.Connection.roughLapRicciInnerInFrame (I := I) (M := M) (Time := Real)
    roughLapRic (ricciTwoTensorField (I := I) S) gInv frame

omit [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem roughLapRicciInnerInFrame_apply
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) :
    roughLapRicciInnerInFrame (I := I) S roughLapRic gInv frame t x =
      ∑ i : Idx, ∑ j : Idx,
        roughLapRic t x i j *
          raisedRicciCompInFrame (I := I) S gInv frame t x i j := by
  rfl


def nablaRicComp
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x) :
    Real -> M -> Idx -> Idx -> Idx -> Real :=
  fun t x a i j =>
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      2 (S.family.connection t) (S.ricci t) x
        (DifferentialGeometry.Integral.Connection.vec3 (I := I) (frame a x) (frame i x) (frame j x))

omit [Fintype Idx] in
omit [SigmaCompactSpace M] in
@[simp] theorem nablaRicComp_apply
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (a i j : Idx) :
    nablaRicComp (I := I) S frame t x a i j =
      totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 (S.family.connection t) (S.ricci t) x
          (DifferentialGeometry.Integral.Connection.vec3 (I := I) (frame a x) (frame i x) (frame j x)) := by
  rfl



abbrev nablaRicciNormSqInFrame
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx) :
    Real -> M -> Real :=
  DifferentialGeometry.Integral.Connection.nablaRicciNormSqInFrame (M := M) nablaRic gInv

omit [TopologicalSpace M] [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem nablaRicciNormSqInFrame_apply
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (t : Real) (x : M) :
    nablaRicciNormSqInFrame (M := M) nablaRic gInv t x =
      ∑ a : Idx, ∑ b : Idx, ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        gInv t x a b * gInv t x i k * gInv t x j l *
          nablaRic t x a i j * nablaRic t x b k l := by
  rfl

private def fin3Slots (a b c : Idx) : Fin 3 -> Idx :=
  fun q => if q = 0 then a else if q = 1 then b else c

omit [Fintype Idx] in
@[simp] private theorem fin3Slots_zero (a b c : Idx) :
    fin3Slots (Idx := Idx) a b c 0 = a := by
  simp [fin3Slots]

omit [Fintype Idx] in
@[simp] private theorem fin3Slots_one (a b c : Idx) :
    fin3Slots (Idx := Idx) a b c 1 = b := by
  simp [fin3Slots]

omit [Fintype Idx] in
@[simp] private theorem fin3Slots_two (a b c : Idx) :
    fin3Slots (Idx := Idx) a b c 2 = c := by
  simp [fin3Slots]

private def fin3PairEquiv :
    ((Fin 3 -> Idx) × (Fin 3 -> Idx)) ≃
      (((((Idx × Idx) × Idx) × Idx) × Idx) × Idx) where
  toFun p := (((((p.1 0, p.2 0), p.1 1), p.1 2), p.2 1), p.2 2)
  invFun p :=
    (fin3Slots (Idx := Idx) p.1.1.1.1.1 p.1.1.1.2 p.1.1.2,
      fin3Slots (Idx := Idx) p.1.1.1.1.2 p.1.2 p.2)
  left_inv p := by
    ext q <;> fin_cases q <;> simp
  right_inv p := by
    rcases p with ⟨⟨⟨⟨⟨a, b⟩, i⟩, j⟩, k⟩, l⟩
    simp

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem coordInner3_eq
    {x : M}
    (gInv : Idx -> Idx -> Real)
    (A B : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (basis : Module.Basis Idx Real (TangentSpace I x)) :
    coordInner0S (I := I) (x := x) 3 gInv A B basis =
      ∑ a : Idx, ∑ b : Idx, ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        gInv a b * gInv i k * gInv j l *
          A (DifferentialGeometry.Integral.Connection.vec3 (I := I) (basis a) (basis i) (basis j)) *
            B (DifferentialGeometry.Integral.Connection.vec3 (I := I) (basis b) (basis k) (basis l)) := by
  classical
  unfold coordInner0S tensor0SComponent
  rw [← Fintype.sum_prod_type']
  rw [Fintype.sum_equiv (fin3PairEquiv (Idx := Idx))
    (fun p : (Fin 3 -> Idx) × (Fin 3 -> Idx) =>
      ((∏ q : Fin 3, gInv (p.1 q) (p.2 q)) *
        A (fun q : Fin 3 => basis (p.1 q))) *
          B (fun q : Fin 3 => basis (p.2 q)))
    (fun p : (((((Idx × Idx) × Idx) × Idx) × Idx) × Idx) =>
      ((∏ q : Fin 3,
          gInv (((fin3PairEquiv (Idx := Idx)).symm p).1 q)
            (((fin3PairEquiv (Idx := Idx)).symm p).2 q)) *
        A (fun q : Fin 3 => basis (((fin3PairEquiv (Idx := Idx)).symm p).1 q))) *
          B (fun q : Fin 3 => basis (((fin3PairEquiv (Idx := Idx)).symm p).2 q)))]
  · repeat rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    refine Finset.sum_congr rfl fun b _ => ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    refine Finset.sum_congr rfl fun l _ => ?_
    change
      ((∏ q : Fin 3,
          gInv (fin3Slots (Idx := Idx) a i j q)
            (fin3Slots (Idx := Idx) b k l q)) *
        A (fun q : Fin 3 => basis (fin3Slots (Idx := Idx) a i j q))) *
          B (fun q : Fin 3 => basis (fin3Slots (Idx := Idx) b k l q)) =
        gInv a b * gInv i k * gInv j l *
          A (DifferentialGeometry.Integral.Connection.vec3 (I := I) (basis a) (basis i) (basis j)) *
            B (DifferentialGeometry.Integral.Connection.vec3 (I := I) (basis b) (basis k) (basis l))
    rw [Fin.prod_univ_three]
    have hA :
        (fun q : Fin 3 => basis (fin3Slots (Idx := Idx) a i j q)) =
          DifferentialGeometry.Integral.Connection.vec3 (I := I) (basis a) (basis i) (basis j) := by
      funext q
      fin_cases q <;> simp [DifferentialGeometry.Integral.Connection.vec3, DifferentialGeometry.Integral.Connection.vec3]
    have hB :
        (fun q : Fin 3 => basis (fin3Slots (Idx := Idx) b k l q)) =
          DifferentialGeometry.Integral.Connection.vec3 (I := I) (basis b) (basis k) (basis l) := by
      funext q
      fin_cases q <;> simp [DifferentialGeometry.Integral.Connection.vec3, DifferentialGeometry.Integral.Connection.vec3]
    rw [hA, hB]
    simp [fin3Slots]
  · intro p
    have h1 :
        fin3Slots (Idx := Idx) (p.1 0) (p.1 1) (p.1 2) = p.1 := by
      funext q
      fin_cases q <;> simp
    have h2 :
        fin3Slots (Idx := Idx) (p.2 0) (p.2 1) (p.2 2) = p.2 := by
      funext q
      fin_cases q <;> simp
    simp [fin3PairEquiv, h1, h2]



omit [SigmaCompactSpace M] in
private theorem nablaRicciNorm_basis
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [DecidableEq Idx]
    (S : SolutionOn (I := I) (M := M) D)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    {t : Real} {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv : MetricInverseInBasis_gen
      (I := I) (M := M) (S.family.metric t) x basis
      (fun i j : Idx => gInv t x i j))
    (hbasis : ∀ i : Idx, basis i = frame i x)
    (hnabla : ∀ a i j : Idx,
      totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 (S.family.connection t) (S.ricci t) x
          (DifferentialGeometry.Integral.Connection.vec3 (I := I) (frame a x) (frame i x) (frame j x)) =
        nablaRic t x a i j) :
    nablaRicciNormSqInFrame (M := M) nablaRic gInv t x =
      ricciGradSq (I := I) S t x := by
  classical
  rw [ricciGradSq]
  rw [normSq0S_eq_coord
    (I := I) (S.family.metric t) x 3 basis
    (fun i j : Idx => gInv t x i j) hinv]
  rw [coordInner3_eq (I := I) (x := x)
    (fun i j : Idx => gInv t x i j)
    (totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      2 (S.family.connection t) (S.ricci t) x)
    (totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      2 (S.family.connection t) (S.ricci t) x)
    basis]
  have hnabla' : ∀ a i j : Idx,
      totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 (S.base.connection t) (S.base.ricci t) x
          (DifferentialGeometry.Integral.Connection.vec3 (I := I) (frame a x) (frame i x) (frame j x)) =
        nablaRic t x a i j := by
    intro a i j
    simpa [SolutionOn.family, SolutionOn.ricci] using hnabla a i j
  simp [nablaRicciNormSqInFrame, hbasis, hnabla', mul_left_comm, mul_comm]



omit [SigmaCompactSpace M] in
theorem nablaRicciNorm_can
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [DecidableEq Idx]
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    {t : Real} {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv : MetricInverseInBasis_gen
      (I := I) (M := M) (S.family.metric t) x basis
      (fun i j : Idx => gInv t x i j))
    (hbasis : ∀ i : Idx, basis i = frame i x) :
    nablaRicciNormSqInFrame (M := M) (nablaRicComp (I := I) S frame) gInv t x =
      ricciGradSq (I := I) S t x :=
  nablaRicciNorm_basis (I := I) S (nablaRicComp (I := I) S frame) gInv frame
    basis hinv hbasis (by intro a i j; rfl)


def curvRicciRicciInFrame
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) :
    Real -> M -> Real :=
  fun t x =>
    ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      DifferentialGeometry.Integral.Connection.rm04Comp (I := I) (Rm04 t) frame x i k j l *
        raisedRicciCompInFrame (I := I) S gInv frame t x i j *
          raisedRicciCompInFrame (I := I) S gInv frame t x k l

omit [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem curvRicciRicciInFrame_apply
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) :
    curvRicciRicciInFrame (I := I) S Rm04 gInv frame t x =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        DifferentialGeometry.Integral.Connection.rm04Comp (I := I) (Rm04 t) frame x i k j l *
          raisedRicciCompInFrame (I := I) S gInv frame t x i j *
            raisedRicciCompInFrame (I := I) S gInv frame t x k l := by
  rfl





def ricciNormCurvatureReactionInFrame
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) :
    Real -> M -> Real :=
  fun t x => -curvRicciRicciInFrame (I := I) S Rm04 gInv frame t x

omit [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem ricciNormCurvatureReactionInFrame_apply
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) :
    ricciNormCurvatureReactionInFrame (I := I) S Rm04 gInv frame t x =
      -curvRicciRicciInFrame (I := I) S Rm04 gInv frame t x := by
  rfl




def inverseMetricEvolutionRHSInFrame
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (i j : Idx) : Real :=
  2 * raisedRicciCompInFrame (I := I) S gInv frame t x i j


def InverseMetricEvolutionEquationInFrame
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (u : Set M) : Prop :=
  ∀ (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M), x ∈ u -> ∀ (i j : Idx),
    HasDerivWithinAt
      (fun s : Real => gInv s x i j)
      (inverseMetricEvolutionRHSInFrame (I := I) S gInv frame
        (t : Real) x i j)
      D.carrier
      (t : Real)


def raisedRicciDerivRHSInFrame
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j : Idx) : Real :=
  ∑ a : Idx, ∑ b : Idx,
    (inverseMetricEvolutionRHSInFrame (I := I) S gInv frame t x i a *
        gInv t x j b * ricciCompInFrame (I := I) S frame t x a b +
      gInv t x i a *
        inverseMetricEvolutionRHSInFrame (I := I) S gInv frame t x j b *
          ricciCompInFrame (I := I) S frame t x a b +
        gInv t x i a * gInv t x j b *
          ricciEvolutionRHSInFrame (I := I) S Rm04 gInv frame roughLapRic t x a b)


def ricciNormDerivRHSInFrame
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (t : Real) (x : M) : Real :=
  ∑ i : Idx, ∑ j : Idx,
    (ricciEvolutionRHSInFrame (I := I) S Rm04 gInv frame roughLapRic t x i j *
        raisedRicciCompInFrame (I := I) S gInv frame t x i j +
      ricciCompInFrame (I := I) S frame t x i j *
        raisedRicciDerivRHSInFrame (I := I) S Rm04 gInv frame roughLapRic t x i j)






def RicciNormDerivativeSimplifiesInFrame
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (roughLapInner reaction : Real -> M -> Real) : Prop :=
  ∀ (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
    ricciNormDerivRHSInFrame (I := I) S Rm04 gInv frame roughLapRic
        (t : Real) x =
      2 * roughLapInner (t : Real) x + 4 * reaction (t : Real) x






omit [SigmaCompactSpace M] [T2Space M] in
theorem ricciDerivSimpAt
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M)
    (hInvSym : forall i j, gInv (t : Real) x i j = gInv (t : Real) x j i)
    (hRicSym : forall i j,
      ricciCompInFrame (I := I) S frame (t : Real) x i j =
        ricciCompInFrame (I := I) S frame (t : Real) x j i) :
    ricciNormDerivRHSInFrame (I := I) S Rm04 gInv frame roughLapRic
        (t : Real) x =
      2 * roughLapRicciInnerInFrame (I := I) S roughLapRic gInv frame
          (t : Real) x +
        4 * ricciNormCurvatureReactionInFrame (I := I) S Rm04 gInv frame
          (t : Real) x := by
  classical
  let G : Idx -> Idx -> Real := fun i j => gInv (t : Real) x i j
  let A : Idx -> Idx -> Real :=
    fun i j => ricciCompInFrame (I := I) S frame (t : Real) x i j
  let L : Idx -> Idx -> Real := fun i j => roughLapRic (t : Real) x i j
  let C : Idx -> Idx -> Real :=
    fun i j =>
      rmRicciContractionCompInFrame (I := I) S Rm04 gInv frame (t : Real) x i j
  have hG : forall i j, G i j = G j i := by
    intro i j
    exact hInvSym i j
  have hA : forall i j, A i j = A j i := by
    intro i j
    exact hRicSym i j
  have hpure := ricciNormDerivativeSimplifies_pure (Idx := Idx) G A L C hG hA
  have hderiv :
      ricciNormDerivRHSInFrame (I := I) S Rm04 gInv frame roughLapRic
          (t : Real) x =
        2 * (∑ i : Idx, ∑ j : Idx, L i j * raise2By G A i j) +
          4 * (-(∑ i : Idx, ∑ j : Idx, C i j * raise2By G A i j)) := by
    change
      (∑ i : Idx, ∑ j : Idx,
        ((L i j - 2 * C i j - 2 * quadraticBy G A i j) *
            raise2By G A i j +
          A i j *
            (∑ a : Idx, ∑ b : Idx,
              (2 * raise2By G A i a * G j b * A a b +
                G i a * (2 * raise2By G A j b) * A a b +
                  G i a * G j b *
                    (L a b - 2 * C a b - 2 * quadraticBy G A a b))))) =
        2 * (∑ i : Idx, ∑ j : Idx, L i j * raise2By G A i j) +
          4 * (-(∑ i : Idx, ∑ j : Idx, C i j * raise2By G A i j))
    exact hpure
  have hrough :
      roughLapRicciInnerInFrame (I := I) S roughLapRic gInv frame (t : Real) x =
        ∑ i : Idx, ∑ j : Idx, L i j * raise2By G A i j := by
    simp [G, A, L, roughLapRicciInnerInFrame, raise2By]
  let R4 : Idx -> Idx -> Idx -> Idx -> Real :=
    fun i k j l => DifferentialGeometry.Integral.Connection.rm04Comp (I := I) (Rm04 (t : Real)) frame x i k j l
  let AR : Idx -> Idx -> Real := fun i j => raise2By G A i j
  have hcurv :
      (∑ i : Idx, ∑ j : Idx, C i j * raise2By G A i j) =
        curvRicciRicciInFrame (I := I) S Rm04 gInv frame (t : Real) x := by
    change
      (∑ i : Idx, ∑ j : Idx,
        (∑ k : Idx, ∑ l : Idx, R4 i k j l * AR k l) * AR i j) =
        ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          R4 i k j l * AR i j * AR k l
    exact sum_contraction_mul_eq_four_sum (Idx := Idx) R4 AR
  have hreaction :
      ricciNormCurvatureReactionInFrame (I := I) S Rm04 gInv frame (t : Real) x =
        -(∑ i : Idx, ∑ j : Idx, C i j * raise2By G A i j) := by
    rw [ricciNormCurvatureReactionInFrame_apply, ← hcurv]
  calc
    ricciNormDerivRHSInFrame (I := I) S Rm04 gInv frame roughLapRic
        (t : Real) x =
        2 * (∑ i : Idx, ∑ j : Idx, L i j * raise2By G A i j) +
          4 * (-(∑ i : Idx, ∑ j : Idx, C i j * raise2By G A i j)) := hderiv
    _ =
        2 * roughLapRicciInnerInFrame (I := I) S roughLapRic gInv frame (t : Real) x +
          4 * ricciNormCurvatureReactionInFrame (I := I) S Rm04 gInv frame
            (t : Real) x := by
          rw [hrough, hreaction]








omit [SigmaCompactSpace M] [T2Space M] in
theorem ricciNormDerivativeSimplifiesInFrame_canonical
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (hInvSym : forall t x i j, gInv t x i j = gInv t x j i)
    (hRicSym : forall t x i j,
      ricciCompInFrame (I := I) S frame t x i j =
        ricciCompInFrame (I := I) S frame t x j i) :
    RicciNormDerivativeSimplifiesInFrame
      (I := I) S Rm04 gInv frame roughLapRic
      (roughLapRicciInnerInFrame (I := I) S roughLapRic gInv frame)
      (ricciNormCurvatureReactionInFrame (I := I) S Rm04 gInv frame) := by
  classical
  intro t x
  let G : Idx -> Idx -> Real := fun i j => gInv (t : Real) x i j
  let A : Idx -> Idx -> Real :=
    fun i j => ricciCompInFrame (I := I) S frame (t : Real) x i j
  let L : Idx -> Idx -> Real := fun i j => roughLapRic (t : Real) x i j
  let C : Idx -> Idx -> Real :=
    fun i j =>
      rmRicciContractionCompInFrame (I := I) S Rm04 gInv frame (t : Real) x i j
  have hG : forall i j, G i j = G j i := by
    intro i j
    exact hInvSym (t : Real) x i j
  have hA : forall i j, A i j = A j i := by
    intro i j
    exact hRicSym (t : Real) x i j
  have hpure := ricciNormDerivativeSimplifies_pure (Idx := Idx) G A L C hG hA
  have hderiv :
      ricciNormDerivRHSInFrame (I := I) S Rm04 gInv frame roughLapRic
          (t : Real) x =
        2 * (∑ i : Idx, ∑ j : Idx, L i j * raise2By G A i j) +
          4 * (-(∑ i : Idx, ∑ j : Idx, C i j * raise2By G A i j)) := by
    change
      (∑ i : Idx, ∑ j : Idx,
        ((L i j - 2 * C i j - 2 * quadraticBy G A i j) *
            raise2By G A i j +
          A i j *
            (∑ a : Idx, ∑ b : Idx,
              (2 * raise2By G A i a * G j b * A a b +
                G i a * (2 * raise2By G A j b) * A a b +
                  G i a * G j b *
                    (L a b - 2 * C a b - 2 * quadraticBy G A a b))))) =
        2 * (∑ i : Idx, ∑ j : Idx, L i j * raise2By G A i j) +
          4 * (-(∑ i : Idx, ∑ j : Idx, C i j * raise2By G A i j))
    exact hpure
  have hrough :
      roughLapRicciInnerInFrame (I := I) S roughLapRic gInv frame (t : Real) x =
        ∑ i : Idx, ∑ j : Idx, L i j * raise2By G A i j := by
    simp [G, A, L, roughLapRicciInnerInFrame, raise2By]
  let R4 : Idx -> Idx -> Idx -> Idx -> Real :=
    fun i k j l => DifferentialGeometry.Integral.Connection.rm04Comp (I := I) (Rm04 (t : Real)) frame x i k j l
  let AR : Idx -> Idx -> Real := fun i j => raise2By G A i j
  have hcurv :
      (∑ i : Idx, ∑ j : Idx, C i j * raise2By G A i j) =
        curvRicciRicciInFrame (I := I) S Rm04 gInv frame (t : Real) x := by
    change
      (∑ i : Idx, ∑ j : Idx,
        (∑ k : Idx, ∑ l : Idx, R4 i k j l * AR k l) * AR i j) =
        ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          R4 i k j l * AR i j * AR k l
    exact sum_contraction_mul_eq_four_sum (Idx := Idx) R4 AR
  have hreaction :
      ricciNormCurvatureReactionInFrame (I := I) S Rm04 gInv frame (t : Real) x =
        -(∑ i : Idx, ∑ j : Idx, C i j * raise2By G A i j) := by
    rw [ricciNormCurvatureReactionInFrame_apply, ← hcurv]
  calc
    ricciNormDerivRHSInFrame (I := I) S Rm04 gInv frame roughLapRic
        (t : Real) x =
        2 * (∑ i : Idx, ∑ j : Idx, L i j * raise2By G A i j) +
          4 * (-(∑ i : Idx, ∑ j : Idx, C i j * raise2By G A i j)) := hderiv
    _ =
        2 * roughLapRicciInnerInFrame (I := I) S roughLapRic gInv frame (t : Real) x +
          4 * ricciNormCurvatureReactionInFrame (I := I) S Rm04 gInv frame
            (t : Real) x := by
          rw [hrough, hreaction]



def RicciEvolutionEquationInFrame
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real) : Prop :=
  ∀ (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M) (i j : Idx),
    HasDerivWithinAt
      (fun s : Real => ricciCompInFrame (I := I) S frame s x i j)
      (ricciEvolutionRHSInFrame (I := I) S Rm04 gInv frame roughLapRic
        (t : Real) x i j)
      D.carrier
      (t : Real)


omit [SigmaCompactSpace M] [T2Space M] in
theorem inverseMetricEvolutionEquationInFrame_apply
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    {gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx}
    {frame : Idx -> (x : M) -> TangentSpace I x}
    {u : Set M}
    (h : InverseMetricEvolutionEquationInFrame (I := I) S gInv frame u)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x : M) (hx : x ∈ u) (i j : Idx) :
    HasDerivWithinAt
      (fun s : Real => gInv s x i j)
      (inverseMetricEvolutionRHSInFrame (I := I) S gInv frame
        (t : Real) x i j)
      D.carrier
      (t : Real) :=
  h t x hx i j



omit [SigmaCompactSpace M] [T2Space M] in
theorem inverseMetricEvolutionEquationInFrame_of_components
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (u : Set M)
    (h : ∀ (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M), x ∈ u ->
      ∀ (i j : Idx),
      HasDerivWithinAt
        (fun s : Real => gInv s x i j)
        (inverseMetricEvolutionRHSInFrame (I := I) S gInv frame
          (t : Real) x i j)
        D.carrier
        (t : Real)) :
    InverseMetricEvolutionEquationInFrame (I := I) S gInv frame u :=
  h


omit [SigmaCompactSpace M] [T2Space M] in
theorem ricciEvolutionEquationInFrame_apply
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    {Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M)}
    {gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx}
    {frame : Idx -> (x : M) -> TangentSpace I x}
    {roughLapRic : Real -> M -> Idx -> Idx -> Real}
    (h : RicciEvolutionEquationInFrame (I := I) S Rm04 gInv frame roughLapRic)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x : M) (i j : Idx) :
    HasDerivWithinAt
      (fun s : Real => ricciCompInFrame (I := I) S frame s x i j)
      (ricciEvolutionRHSInFrame (I := I) S Rm04 gInv frame roughLapRic
        (t : Real) x i j)
      D.carrier
      (t : Real) :=
  h t x i j



omit [SigmaCompactSpace M] [T2Space M] in
theorem ricciEvolutionEquationInFrame_of_components
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (h : ∀ (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M) (i j : Idx),
      HasDerivWithinAt
        (fun s : Real => ricciCompInFrame (I := I) S frame s x i j)
        (ricciEvolutionRHSInFrame (I := I) S Rm04 gInv frame roughLapRic
          (t : Real) x i j)
        D.carrier
        (t : Real)) :
    RicciEvolutionEquationInFrame (I := I) S Rm04 gInv frame roughLapRic :=
  h


omit [SigmaCompactSpace M] [T2Space M] in
theorem raisedRicciCompInFrame_hasDerivWithinAt
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    {u : Set M}
    (h_inv : InverseMetricEvolutionEquationInFrame (I := I) S gInv frame u)
    (h_ricci : RicciEvolutionEquationInFrame (I := I) S Rm04 gInv frame roughLapRic)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x : M) (hx : x ∈ u) (i j : Idx) :
    HasDerivWithinAt
      (fun s : Real => raisedRicciCompInFrame (I := I) S gInv frame s x i j)
      (raisedRicciDerivRHSInFrame (I := I) S Rm04 gInv frame roughLapRic
        (t : Real) x i j)
      D.carrier
      (t : Real) := by
  simpa [raisedRicciCompInFrame, raisedRicciDerivRHSInFrame, Finset.sum_apply] using
    (HasDerivWithinAt.fun_sum
      (u := (Finset.univ : Finset Idx))
      (A := fun a s =>
        ∑ b : Idx,
          gInv s x i a * gInv s x j b *
            ricciCompInFrame (I := I) S frame s x a b)
      (A' := fun a =>
        ∑ b : Idx,
          (inverseMetricEvolutionRHSInFrame (I := I) S gInv frame
                (t : Real) x i a *
              gInv (t : Real) x j b *
                ricciCompInFrame (I := I) S frame (t : Real) x a b +
            gInv (t : Real) x i a *
              inverseMetricEvolutionRHSInFrame (I := I) S gInv frame
                (t : Real) x j b *
                ricciCompInFrame (I := I) S frame (t : Real) x a b +
              gInv (t : Real) x i a * gInv (t : Real) x j b *
                ricciEvolutionRHSInFrame
                  (I := I) S Rm04 gInv frame roughLapRic (t : Real) x a b))
      (s := D.carrier) (x := (t : Real))
      (fun a _ha =>
        by
          simpa [Finset.sum_apply] using
            (HasDerivWithinAt.fun_sum
              (u := (Finset.univ : Finset Idx))
              (A := fun b s =>
                gInv s x i a * gInv s x j b *
                  ricciCompInFrame (I := I) S frame s x a b)
              (A' := fun b =>
                (inverseMetricEvolutionRHSInFrame (I := I) S gInv frame
                      (t : Real) x i a *
                    gInv (t : Real) x j b *
                      ricciCompInFrame (I := I) S frame (t : Real) x a b +
                  gInv (t : Real) x i a *
                    inverseMetricEvolutionRHSInFrame (I := I) S gInv frame
                      (t : Real) x j b *
                      ricciCompInFrame (I := I) S frame (t : Real) x a b +
                    gInv (t : Real) x i a * gInv (t : Real) x j b *
                      ricciEvolutionRHSInFrame
                        (I := I) S Rm04 gInv frame roughLapRic (t : Real) x a b))
              (s := D.carrier) (x := (t : Real))
              (fun b _hb =>
                by
                  have hia := h_inv t x hx i a
                  have hjb := h_inv t x hx j b
                  have hrab := h_ricci t x a b
                  have hprod := (hia.mul hjb).mul hrab
                  simpa [Pi.mul_apply, mul_assoc, add_mul] using hprod))))




omit [SigmaCompactSpace M] [T2Space M] in
theorem raisedRicciDerivAt
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    {u : Set M}
    (h_inv : InverseMetricEvolutionEquationInFrame (I := I) S gInv frame u)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x : M) (hx : x ∈ u)
    (h_ricci : ∀ a b : Idx,
      HasDerivWithinAt
        (fun s : Real => ricciCompInFrame (I := I) S frame s x a b)
        (ricciEvolutionRHSInFrame (I := I) S Rm04 gInv frame roughLapRic
          (t : Real) x a b)
        D.carrier
        (t : Real))
    (i j : Idx) :
    HasDerivWithinAt
      (fun s : Real => raisedRicciCompInFrame (I := I) S gInv frame s x i j)
      (raisedRicciDerivRHSInFrame (I := I) S Rm04 gInv frame roughLapRic
        (t : Real) x i j)
      D.carrier
      (t : Real) := by
  simpa [raisedRicciCompInFrame, raisedRicciDerivRHSInFrame, Finset.sum_apply] using
    (HasDerivWithinAt.fun_sum
      (u := (Finset.univ : Finset Idx))
      (A := fun a s =>
        ∑ b : Idx,
          gInv s x i a * gInv s x j b *
            ricciCompInFrame (I := I) S frame s x a b)
      (A' := fun a =>
        ∑ b : Idx,
          (inverseMetricEvolutionRHSInFrame (I := I) S gInv frame
                (t : Real) x i a *
              gInv (t : Real) x j b *
                ricciCompInFrame (I := I) S frame (t : Real) x a b +
            gInv (t : Real) x i a *
              inverseMetricEvolutionRHSInFrame (I := I) S gInv frame
                (t : Real) x j b *
                ricciCompInFrame (I := I) S frame (t : Real) x a b +
              gInv (t : Real) x i a * gInv (t : Real) x j b *
                ricciEvolutionRHSInFrame
                  (I := I) S Rm04 gInv frame roughLapRic (t : Real) x a b))
      (s := D.carrier) (x := (t : Real))
      (fun a _ha =>
        by
          simpa [Finset.sum_apply] using
            (HasDerivWithinAt.fun_sum
              (u := (Finset.univ : Finset Idx))
              (A := fun b s =>
                gInv s x i a * gInv s x j b *
                  ricciCompInFrame (I := I) S frame s x a b)
              (A' := fun b =>
                (inverseMetricEvolutionRHSInFrame (I := I) S gInv frame
                      (t : Real) x i a *
                    gInv (t : Real) x j b *
                      ricciCompInFrame (I := I) S frame (t : Real) x a b +
                  gInv (t : Real) x i a *
                    inverseMetricEvolutionRHSInFrame (I := I) S gInv frame
                      (t : Real) x j b *
                      ricciCompInFrame (I := I) S frame (t : Real) x a b +
                    gInv (t : Real) x i a * gInv (t : Real) x j b *
                      ricciEvolutionRHSInFrame
                        (I := I) S Rm04 gInv frame roughLapRic (t : Real) x a b))
              (s := D.carrier) (x := (t : Real))
              (fun b _hb =>
                by
                  have hia := h_inv t x hx i a
                  have hjb := h_inv t x hx j b
                  have hrab := h_ricci a b
                  have hprod := (hia.mul hjb).mul hrab
                  simpa [Pi.mul_apply, mul_assoc, add_mul] using hprod))))


omit [SigmaCompactSpace M] [T2Space M] in
theorem ricciNormSqInFrame_hasDerivWithinAt
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    {u : Set M}
    (h_inv : InverseMetricEvolutionEquationInFrame (I := I) S gInv frame u)
    (h_ricci : RicciEvolutionEquationInFrame (I := I) S Rm04 gInv frame roughLapRic)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x : M) (hx : x ∈ u) :
    HasDerivWithinAt
      (fun s : Real => ricciNormSqInFrame (I := I) S gInv frame s x)
      (ricciNormDerivRHSInFrame (I := I) S Rm04 gInv frame roughLapRic
        (t : Real) x)
      D.carrier
      (t : Real) := by
  simpa [ricciNormSqInFrame, ricciNormDerivRHSInFrame, Finset.sum_apply] using
    (HasDerivWithinAt.fun_sum
      (u := (Finset.univ : Finset Idx))
      (A := fun i s =>
        ∑ j : Idx,
          ricciCompInFrame (I := I) S frame s x i j *
            raisedRicciCompInFrame (I := I) S gInv frame s x i j)
      (A' := fun i =>
        ∑ j : Idx,
          (ricciEvolutionRHSInFrame
                (I := I) S Rm04 gInv frame roughLapRic (t : Real) x i j *
              raisedRicciCompInFrame (I := I) S gInv frame (t : Real) x i j +
            ricciCompInFrame (I := I) S frame (t : Real) x i j *
              raisedRicciDerivRHSInFrame
                (I := I) S Rm04 gInv frame roughLapRic (t : Real) x i j))
      (s := D.carrier) (x := (t : Real))
      (fun i _hi =>
        by
          simpa [Finset.sum_apply] using
            (HasDerivWithinAt.fun_sum
              (u := (Finset.univ : Finset Idx))
              (A := fun j s =>
                ricciCompInFrame (I := I) S frame s x i j *
                  raisedRicciCompInFrame (I := I) S gInv frame s x i j)
              (A' := fun j =>
                (ricciEvolutionRHSInFrame
                      (I := I) S Rm04 gInv frame roughLapRic (t : Real) x i j *
                    raisedRicciCompInFrame (I := I) S gInv frame (t : Real) x i j +
                  ricciCompInFrame (I := I) S frame (t : Real) x i j *
                    raisedRicciDerivRHSInFrame
                      (I := I) S Rm04 gInv frame roughLapRic (t : Real) x i j))
              (s := D.carrier) (x := (t : Real))
              (fun j _hj =>
                by
                  have hRic := h_ricci t x i j
                  have hRaised :=
                    raisedRicciCompInFrame_hasDerivWithinAt
                      (I := I) S Rm04 gInv frame roughLapRic h_inv h_ricci t x hx i j
                  have hprod := hRic.mul hRaised
                  simpa [Pi.mul_apply] using hprod))))




omit [SigmaCompactSpace M] [T2Space M] in
theorem ricciNormSqDerivAt
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    {u : Set M}
    (h_inv : InverseMetricEvolutionEquationInFrame (I := I) S gInv frame u)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x : M) (hx : x ∈ u)
    (h_ricci : ∀ i j : Idx,
      HasDerivWithinAt
        (fun s : Real => ricciCompInFrame (I := I) S frame s x i j)
        (ricciEvolutionRHSInFrame (I := I) S Rm04 gInv frame roughLapRic
          (t : Real) x i j)
        D.carrier
        (t : Real)) :
    HasDerivWithinAt
      (fun s : Real => ricciNormSqInFrame (I := I) S gInv frame s x)
      (ricciNormDerivRHSInFrame (I := I) S Rm04 gInv frame roughLapRic
        (t : Real) x)
      D.carrier
      (t : Real) := by
  simpa [ricciNormSqInFrame, ricciNormDerivRHSInFrame, Finset.sum_apply] using
    (HasDerivWithinAt.fun_sum
      (u := (Finset.univ : Finset Idx))
      (A := fun i s =>
        ∑ j : Idx,
          ricciCompInFrame (I := I) S frame s x i j *
            raisedRicciCompInFrame (I := I) S gInv frame s x i j)
      (A' := fun i =>
        ∑ j : Idx,
          (ricciEvolutionRHSInFrame
                (I := I) S Rm04 gInv frame roughLapRic (t : Real) x i j *
              raisedRicciCompInFrame (I := I) S gInv frame (t : Real) x i j +
            ricciCompInFrame (I := I) S frame (t : Real) x i j *
              raisedRicciDerivRHSInFrame
                (I := I) S Rm04 gInv frame roughLapRic (t : Real) x i j))
      (s := D.carrier) (x := (t : Real))
      (fun i _hi =>
        by
          simpa [Finset.sum_apply] using
            (HasDerivWithinAt.fun_sum
              (u := (Finset.univ : Finset Idx))
              (A := fun j s =>
                ricciCompInFrame (I := I) S frame s x i j *
                  raisedRicciCompInFrame (I := I) S gInv frame s x i j)
              (A' := fun j =>
                (ricciEvolutionRHSInFrame
                      (I := I) S Rm04 gInv frame roughLapRic (t : Real) x i j *
                    raisedRicciCompInFrame (I := I) S gInv frame (t : Real) x i j +
                  ricciCompInFrame (I := I) S frame (t : Real) x i j *
                    raisedRicciDerivRHSInFrame
                      (I := I) S Rm04 gInv frame roughLapRic (t : Real) x i j))
              (s := D.carrier) (x := (t : Real))
              (fun j _hj =>
                by
                  have hRic := h_ricci i j
                  have hRaised :=
                    raisedRicciDerivAt
                      (I := I) S Rm04 gInv frame roughLapRic h_inv t x hx
                      h_ricci i j
                  have hprod := hRic.mul hRaised
                  simpa [Pi.mul_apply] using hprod))))

end Components


end DifferentialGeometry.PDE.RicciFlow
