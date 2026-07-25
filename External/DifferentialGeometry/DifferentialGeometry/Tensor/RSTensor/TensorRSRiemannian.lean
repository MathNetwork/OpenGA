import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Basic
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Coordinate
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Comparison
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Product
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Smooth
import Mathlib.LinearAlgebra.Trace
import DifferentialGeometry.Tensor.RSTensor.FiberMetric.TensorRSMetric

set_option autoImplicit false
set_option linter.style.longLine false















namespace Tensor0SBundle

noncomputable section

open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {Time : Type*}



def componentL2SqRS
    {x : M} {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basis : Module.Basis Idx Real (TangentSpace I x))
    {r s : Nat} (A : TensorRSSpace r s I x) : Real :=
  ∑ upper : Fin r -> Idx, ∑ lower : Fin s -> Idx,
    (componentRS_gen (I := I) basis A upper lower) ^ 2



theorem normSqRS_identity_eq_componentL2SqRS
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothMetric_gen I M) (x : M) (r s : Nat)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      MetricInverseInBasis_gen (I := I) g x basis (identityInvMetric (Idx := Idx)))
    (A : TensorRSSpace r s I x) :
    normSqRS (I := I) (g := g) (x := x) r s A =
      componentL2SqRS (I := I) basis A := by
  classical
  rw [normSqRS_eq_inner, innerRS_eq_trace]
  rw [LinearMap.trace_eq_matrix_trace Real (tensor0SBasis (I := I) basis r)
    ((adjointRS (I := I) (g := g) (x := x) r s A).comp A.toLinearMap)]
  rw [Matrix.trace]
  unfold componentL2SqRS
  apply Finset.sum_congr rfl
  intro upper _
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
  change
    (tensor0SBasis (I := I) basis r).repr
        ((adjointRS (I := I) (g := g) (x := x) r s A)
          (A (basisTensor0S (I := I) basis upper))) upper =
      ∑ lower : Fin s -> Idx,
        (componentRS_gen (I := I) basis A upper lower) ^ 2
  rw [tensor0SBasis_repr]
  rw [← inner0S_basisTensor_right_identity (I := I) g x r basis hinv
    ((adjointRS (I := I) (g := g) (x := x) r s A)
      (A (basisTensor0S (I := I) basis upper))) upper]
  rw [adjointRS_inner]
  rw [inner0S_eq_coord (I := I) g x s basis
    (identityInvMetric (Idx := Idx)) hinv,
    coordInner0S_identity_eq_sum (I := I) (x := x) s
      (A (basisTensor0S (I := I) basis upper))
      (A (basisTensor0S (I := I) basis upper)) basis]
  apply Finset.sum_congr rfl
  intro lower _
  change
    componentRS_gen (I := I) basis A upper lower *
        componentRS_gen (I := I) basis A upper lower =
      (componentRS_gen (I := I) basis A upper lower) ^ 2
  ring



theorem normSqRS_one_two_identity_eq_sum
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothMetric_gen I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      MetricInverseInBasis_gen (I := I) g x basis (identityInvMetric (Idx := Idx)))
    (A : TensorRSSpace 1 2 I x) :
    normSqRS (I := I) (g := g) (x := x) 1 2 A =
      ∑ k : Idx, ∑ i : Idx, ∑ j : Idx,
        (componentRS_gen (I := I) basis A (fun _ : Fin 1 => k)
          (fun q : Fin 2 => if q = 0 then i else j)) ^ 2 := by
  rw [normSqRS_identity_eq_componentL2SqRS (I := I) g x 1 2 basis hinv A]
  unfold componentL2SqRS
  rw [sum_fin_one_fun]
  apply Finset.sum_congr rfl
  intro k _
  rw [sum_fin_two_fun]



theorem componentRS_sq_le_componentL2SqRS
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} {r s : Nat}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (A : TensorRSSpace r s I x)
    (upper : Fin r -> Idx) (lower : Fin s -> Idx) :
    (componentRS_gen (I := I) basis A upper lower) ^ 2 <=
      componentL2SqRS (I := I) basis A := by
  classical
  unfold componentL2SqRS
  have h_lower :
      (componentRS_gen (I := I) basis A upper lower) ^ 2 <=
        ∑ lower' : Fin s -> Idx,
          (componentRS_gen (I := I) basis A upper lower') ^ 2 := by
    exact Finset.single_le_sum
      (fun lower' _ => sq_nonneg
        (componentRS_gen (I := I) basis A upper lower'))
      (by simp)
  have h_upper :
      (∑ lower' : Fin s -> Idx,
          (componentRS_gen (I := I) basis A upper lower') ^ 2) <=
        ∑ upper' : Fin r -> Idx, ∑ lower' : Fin s -> Idx,
          (componentRS_gen (I := I) basis A upper' lower') ^ 2 := by
    exact Finset.single_le_sum
      (fun upper' _ =>
        Finset.sum_nonneg
          (fun lower' _ => sq_nonneg
            (componentRS_gen (I := I) basis A upper' lower')))
      (by simp)
  exact h_lower.trans h_upper



theorem abs_componentRS_le_sqrt_normSqRS
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothMetric_gen I M) (x : M) (r s : Nat)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      MetricInverseInBasis_gen (I := I) g x basis (identityInvMetric (Idx := Idx)))
    (A : TensorRSSpace r s I x)
    (upper : Fin r -> Idx) (lower : Fin s -> Idx) :
    |componentRS_gen (I := I) basis A upper lower| <=
      Real.sqrt (normSqRS (I := I) (g := g) (x := x) r s A) := by
  classical
  have hcomp_nonneg :
      0 <= componentL2SqRS (I := I) basis A := by
    unfold componentL2SqRS
    exact Finset.sum_nonneg
      (fun upper' _ =>
        Finset.sum_nonneg
          (fun lower' _ => sq_nonneg
            (componentRS_gen (I := I) basis A upper' lower')))
  have hnorm_nonneg :
      0 <= normSqRS (I := I) (g := g) (x := x) r s A := by
    rw [normSqRS_identity_eq_componentL2SqRS
      (I := I) g x r s basis hinv A]
    exact hcomp_nonneg
  have hsq :
      |componentRS_gen (I := I) basis A upper lower| ^ 2 <=
        (Real.sqrt (normSqRS (I := I) (g := g) (x := x) r s A)) ^ 2 := by
    rw [sq_abs, Real.sq_sqrt hnorm_nonneg,
      normSqRS_identity_eq_componentL2SqRS
        (I := I) g x r s basis hinv A]
    exact componentRS_sq_le_componentL2SqRS
      (I := I) basis A upper lower
  have hsq_no_abs :
      (componentRS_gen (I := I) basis A upper lower) ^ 2 <=
        (Real.sqrt (normSqRS (I := I) (g := g) (x := x) r s A)) ^ 2 := by
    simpa [sq_abs] using hsq
  exact abs_le_of_sq_le_sq hsq_no_abs (Real.sqrt_nonneg _)




theorem sqrt_normSqRS_apply
    (g : SmoothMetric_gen I M) {x : M} {r s : Nat}
    (A : TensorRSSpace r s I x) (input : Tensor0SSpace r I x) :
    Real.sqrt (normSq0S (I := I) g x s (A input)) <=
      Real.sqrt (normSqRS (I := I) (g := g) (x := x) r s A) *
        Real.sqrt (normSq0S (I := I) g x r input) := by
  classical
  let D := (tangentMetricData_gen (I := I) g x).metric
  letI : InnerProductSpace.Core Real (TangentSpace I x) := D.toCore
  letI : NormedAddCommGroup (TangentSpace I x) :=
    @InnerProductSpace.Core.toNormedAddCommGroup Real (TangentSpace I x) _ _ _ D.toCore
  letI : InnerProductSpace Real (TangentSpace I x) :=
    @InnerProductSpace.ofCore Real (TangentSpace I x) _ _ _ D.toCore.toCore
  let ob := stdOrthonormalBasis Real (TangentSpace I x)
  let basis := ob.toBasis
  have hON : forall i j,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0 := by
    intro i j
    have hinner : Inner.inner Real (ob i) (ob j) = D.inner (ob i) (ob j) :=
      MetricFiberData.toCore_inner D (ob i) (ob j)
    change g.inner x (ob.toBasis i) (ob.toBasis j) = if i = j then (1 : Real) else 0
    rw [← TangentMetricData_gen.inner_eq_gen
      (tangentMetricData_gen (I := I) g x) (ob.toBasis i) (ob.toBasis j)]
    change D.inner (ob i) (ob j) = if i = j then (1 : Real) else 0
    rw [← hinner]
    exact ob.inner_eq_ite i j
  have hinv : MetricInverseInBasis_gen (I := I) g x basis
      (identityInvMetric
        (Idx := Fin (Module.finrank Real (TangentSpace I x)))) := by
    intro i j
    constructor <;> simp [identityInvMetric, diagonalInvMetric, hON]
  have hout :
      normSq0S (I := I) g x s (A input) =
        ∑ lower : Fin s -> Fin (Module.finrank Real (TangentSpace I x)),
          (∑ upper : Fin r -> Fin (Module.finrank Real (TangentSpace I x)),
            component0S (I := I) basis input upper *
              componentRS_gen (I := I) basis A upper lower) ^ 2 := by
    rw [normSq0S_identity_eq_sum_sq (I := I) g x s basis hinv]
    apply Finset.sum_congr rfl
    intro lower _
    rw [componentRS_apply_input_eq_sum (I := I) basis A input lower]
  have hinput :
      normSq0S (I := I) g x r input =
        ∑ upper : Fin r -> Fin (Module.finrank Real (TangentSpace I x)),
          (component0S (I := I) basis input upper) ^ 2 :=
    normSq0S_identity_eq_sum_sq (I := I) g x r basis hinv input
  have hA :
      normSqRS (I := I) (g := g) (x := x) r s A =
        ∑ upper : Fin r -> Fin (Module.finrank Real (TangentSpace I x)),
          ∑ lower : Fin s -> Fin (Module.finrank Real (TangentSpace I x)),
            (componentRS_gen (I := I) basis A upper lower) ^ 2 := by
    rw [normSqRS_identity_eq_componentL2SqRS (I := I) g x r s basis hinv A]
    rfl
  have hsq :
      (∑ lower : Fin s -> Fin (Module.finrank Real (TangentSpace I x)),
          (∑ upper : Fin r -> Fin (Module.finrank Real (TangentSpace I x)),
            component0S (I := I) basis input upper *
              componentRS_gen (I := I) basis A upper lower) ^ 2) <=
        (∑ upper : Fin r -> Fin (Module.finrank Real (TangentSpace I x)),
          ∑ lower : Fin s -> Fin (Module.finrank Real (TangentSpace I x)),
            (componentRS_gen (I := I) basis A upper lower) ^ 2) *
          (∑ upper : Fin r -> Fin (Module.finrank Real (TangentSpace I x)),
            (component0S (I := I) basis input upper) ^ 2) := by
    calc
      (∑ lower : Fin s -> Fin (Module.finrank Real (TangentSpace I x)),
          (∑ upper : Fin r -> Fin (Module.finrank Real (TangentSpace I x)),
            component0S (I := I) basis input upper *
              componentRS_gen (I := I) basis A upper lower) ^ 2)
          <= ∑ lower : Fin s -> Fin (Module.finrank Real (TangentSpace I x)),
            (∑ upper : Fin r -> Fin (Module.finrank Real (TangentSpace I x)),
              (component0S (I := I) basis input upper) ^ 2) *
            (∑ upper : Fin r -> Fin (Module.finrank Real (TangentSpace I x)),
              (componentRS_gen (I := I) basis A upper lower) ^ 2) := by
            apply Finset.sum_le_sum
            intro lower _
            exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
      _ = (∑ upper : Fin r -> Fin (Module.finrank Real (TangentSpace I x)),
              ∑ lower : Fin s -> Fin (Module.finrank Real (TangentSpace I x)),
                (componentRS_gen (I := I) basis A upper lower) ^ 2) *
            (∑ upper : Fin r -> Fin (Module.finrank Real (TangentSpace I x)),
              (component0S (I := I) basis input upper) ^ 2) := by
            rw [← Finset.mul_sum, Finset.sum_comm]
            ring
  rw [hout, hA, hinput]
  calc
    Real.sqrt
        (∑ lower : Fin s -> Fin (Module.finrank Real (TangentSpace I x)),
          (∑ upper : Fin r -> Fin (Module.finrank Real (TangentSpace I x)),
            component0S (I := I) basis input upper *
              componentRS_gen (I := I) basis A upper lower) ^ 2)
        <= Real.sqrt
          ((∑ upper : Fin r -> Fin (Module.finrank Real (TangentSpace I x)),
              ∑ lower : Fin s -> Fin (Module.finrank Real (TangentSpace I x)),
                (componentRS_gen (I := I) basis A upper lower) ^ 2) *
            (∑ upper : Fin r -> Fin (Module.finrank Real (TangentSpace I x)),
              (component0S (I := I) basis input upper) ^ 2)) :=
      Real.sqrt_le_sqrt hsq
    _ = Real.sqrt
          (∑ upper : Fin r -> Fin (Module.finrank Real (TangentSpace I x)),
            ∑ lower : Fin s -> Fin (Module.finrank Real (TangentSpace I x)),
              (componentRS_gen (I := I) basis A upper lower) ^ 2) *
        Real.sqrt
          (∑ upper : Fin r -> Fin (Module.finrank Real (TangentSpace I x)),
            (component0S (I := I) basis input upper) ^ 2) := by
      rw [Real.sqrt_mul (Finset.sum_nonneg fun _ _ =>
        Finset.sum_nonneg fun _ _ => sq_nonneg _)]


end

end Tensor0SBundle
