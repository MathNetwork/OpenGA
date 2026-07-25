import DifferentialGeometry.Tensor.RSTensor.MetricTrace.Trace04
import DifferentialGeometry.Tensor.RSTensor.NormSqProduct

set_option autoImplicit false








noncomputable section

namespace Tensor0SBundle

open Bundle
open DifferentialGeometry.Integral.Connection
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {x : M}



theorem component_le_sqrt
    (g : SmoothMetric_gen I M)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {s : Nat} (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv : MetricInverseInBasis_gen (I := I) g x basis
      (identityInvMetric (Idx := Idx)))
    (A : Tensor0SSpace s I x) (slots : Fin s -> Idx) :
    |component0S (I := I) basis A slots| <=
      Real.sqrt (normSq0S (I := I) g x s A) := by
  rw [← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  rw [normSq0S_identity_eq_sum_sq (I := I) g x s basis hinv A]
  exact Finset.single_le_sum
    (fun slots' _ => sq_nonneg (component0S (I := I) basis A slots'))
    (Finset.mem_univ slots)



theorem trace_normSq_le
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {s : Nat} (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv : MetricInverseInBasis_gen (I := I) g x basis
      (identityInvMetric (Idx := Idx)))
    (T : Tensor0SSpace (s + 2) I x) :
    normSq0S (I := I) g x s (metricTraceFirstTwo0STensor (I := I) g T) <=
      (Fintype.card (Fin s -> Idx) : Real) * (Fintype.card Idx : Real) ^ 2 *
        normSq0S (I := I) g x (s + 2) T := by
  classical
  let sourceNorm := normSq0S (I := I) g x (s + 2) T
  have hsource : 0 <= sourceNorm := by
    rw [show sourceNorm = normSq0S (I := I) g x (s + 2) T by rfl,
      normSq0S_identity_eq_sum_sq (I := I) g x (s + 2) basis hinv T]
    exact Finset.sum_nonneg fun slots _ => sq_nonneg (component0S (I := I) basis T slots)
  have htraceComp : forall slots : Fin s -> Idx,
      component0S (I := I) basis (metricTraceFirstTwo0STensor (I := I) g T) slots =
        ∑ i : Idx, component0S (I := I) basis T (Fin.cons i (Fin.cons i slots)) := by
    intro slots
    rw [component0S_apply, metricTraceFirstTwo0STensor_apply,
      metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis
        (identityInvMetric (Idx := Idx)) hinv]
    simp only [metricTrace0S2InBasis, identityInvMetric, diagonalInvMetric,
      ite_mul, one_mul, zero_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_eq_single i]
    · rw [if_pos rfl, component0S_apply]
      congr 1
      funext a
      refine Fin.cases ?_ (fun a1 => ?_) a
      · rfl
      · refine Fin.cases ?_ (fun _ => ?_) a1 <;> rfl
    · intro j _ hji
      simp only [if_neg (Ne.symm hji)]
    · intro hni
      exact absurd (Finset.mem_univ i) hni
  have htraceAbs : forall slots : Fin s -> Idx,
      |component0S (I := I) basis (metricTraceFirstTwo0STensor (I := I) g T) slots| <=
        (Fintype.card Idx : Real) * Real.sqrt sourceNorm := by
    intro slots
    rw [htraceComp slots]
    calc
      |∑ i : Idx, component0S (I := I) basis T (Fin.cons i (Fin.cons i slots))| <=
          ∑ i : Idx, |component0S (I := I) basis T (Fin.cons i (Fin.cons i slots))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ <= ∑ _i : Idx, Real.sqrt sourceNorm := by
        apply Finset.sum_le_sum
        intro i _
        exact component_le_sqrt (I := I) g basis hinv T (Fin.cons i (Fin.cons i slots))
      _ = (Fintype.card Idx : Real) * Real.sqrt sourceNorm := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [normSq0S_identity_eq_sum_sq (I := I) g x s basis hinv]
  calc
    ∑ slots : Fin s -> Idx,
        component0S (I := I) basis (metricTraceFirstTwo0STensor (I := I) g T) slots ^ 2 <=
      ∑ _slots : Fin s -> Idx,
        ((Fintype.card Idx : Real) * Real.sqrt sourceNorm) ^ 2 := by
      apply Finset.sum_le_sum
      intro slots _
      have habs := htraceAbs slots
      have hright : 0 <= (Fintype.card Idx : Real) * Real.sqrt sourceNorm :=
        mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
      exact sq_le_sq.mpr (by simpa [abs_of_nonneg hright] using habs)
    _ = (Fintype.card (Fin s -> Idx) : Real) *
        ((Fintype.card Idx : Real) * Real.sqrt sourceNorm) ^ 2 := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = (Fintype.card (Fin s -> Idx) : Real) * (Fintype.card Idx : Real) ^ 2 *
        (Real.sqrt sourceNorm) ^ 2 := by ring
    _ = (Fintype.card (Fin s -> Idx) : Real) * (Fintype.card Idx : Real) ^ 2 *
        sourceNorm := by rw [Real.sq_sqrt hsource]
    _ = (Fintype.card (Fin s -> Idx) : Real) * (Fintype.card Idx : Real) ^ 2 *
        normSq0S (I := I) g x (s + 2) T := rfl



theorem trace_normSq_rank_le
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    {s : Nat} (T : Tensor0SSpace (s + 2) I x) :
    normSq0S (I := I) g x s (metricTraceFirstTwo0STensor (I := I) g T) <=
      (Module.finrank Real E : Real) ^ (s + 2) *
        normSq0S (I := I) g x (s + 2) T := by
  classical
  let D := (tangentMetricData_gen (I := I) g x).metric
  letI : InnerProductSpace.Core Real (TangentSpace I x) := D.toCore
  letI : NormedAddCommGroup (TangentSpace I x) :=
    @InnerProductSpace.Core.toNormedAddCommGroup Real (TangentSpace I x) _ _ _ D.toCore
  letI : InnerProductSpace Real (TangentSpace I x) :=
    @InnerProductSpace.ofCore Real (TangentSpace I x) _ _ _ D.toCore.toCore
  let ob := stdOrthonormalBasis Real (TangentSpace I x)
  let basis := ob.toBasis
  have hON : forall i j, g.inner x (basis i) (basis j) =
      if i = j then (1 : Real) else 0 := by
    intro i j
    have hinner : Inner.inner Real (ob i) (ob j) = D.inner (ob i) (ob j) :=
      MetricFiberData.toCore_inner D (ob i) (ob j)
    change g.inner x (ob.toBasis i) (ob.toBasis j) = if i = j then (1 : Real) else 0
    rw [← TangentMetricData_gen.inner_eq_gen (tangentMetricData_gen (I := I) g x)
      (ob.toBasis i) (ob.toBasis j)]
    change D.inner (ob i) (ob j) = if i = j then (1 : Real) else 0
    rw [← hinner]
    exact ob.inner_eq_ite i j
  have hinv : MetricInverseInBasis_gen (I := I) g x basis
      (identityInvMetric (Idx := Fin (Module.finrank Real (TangentSpace I x)))) := by
    intro i j
    constructor <;> simp [identityInvMetric, diagonalInvMetric, hON]
  have h := trace_normSq_le (I := I) g basis hinv T
  simpa [basis, pow_add] using h

end Tensor0SBundle
