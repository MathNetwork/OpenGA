import DifferentialGeometry.Geometry.Connection.MetricCompatibility.TensorLoweringParallel
import DifferentialGeometry.Geometry.Metric.PointwiseInner.SlotPermutation
import DifferentialGeometry.Tensor.RSTensor.RankZero










noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]



lemma inner_nat_cast
    (g : SmoothRiemannianMetric I M) (x : M) {a b : ℕ} (h : a = b)
    (A B : ContinuousMultilinearMap ℝ (fun _ : Fin b => E) ℝ) :
    covariantTensorInnerPointwise (I := I) (M := M) a g x
        (A.domDomCongr (finCongr h.symm))
        (B.domDomCongr (finCongr h.symm)) =
      covariantTensorInnerPointwise (I := I) (M := M) b g x A B := by
  subst a
  simpa only [finCongr_refl] using
    (tensorInnerPointwise_0s_domDomCongr (I := I) (M := M) g x b
      (Equiv.refl (Fin b)) A B)



lemma lower_toRS0
    (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (A : Tensor0SSpace s I x) :
    lowerAllUpperIndices (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel (Tensor0SSpace.toRS0 A)) =
      (Tensor0SSpace.toModel A).domDomCongr
        (finCongr (Nat.zero_add s).symm) := by
  apply ContinuousMultilinearMap.ext
  intro v
  rw [lowerAllUpperIndices_apply, separableFormAt_zero]
  have hunit_model : Tensor0SSpace.toModel
      (Tensor0SSpace.ofModel (I := I) (x := x)
        (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ))) =
      ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ) := by
    rw [Tensor0SSpace.toModel_ofModel]
  rw [← hunit_model]
  rw [← toModel_tensorRS_apply (I := I) (M := M) 0 s x
    (Tensor0SSpace.toRS0 A)
    (Tensor0SSpace.ofModel (I := I) (x := x)
      (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)))]
  rw [Tensor0SSpace.toRS0_apply]
  have hone : tensor0SSpace_evalScalar x
      (Tensor0SSpace.ofModel (I := I) (x := x)
        (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ))) = 1 := by
    rw [Tensor0SSpace.evalScalar_apply]
    change Tensor0SSpace.toModel
      (Tensor0SSpace.ofModel (I := I) (x := x)
        (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)))
        Fin.elim0 = 1
    rw [Tensor0SSpace.toModel_ofModel]
    rfl
  rw [hone, one_smul]
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  congr 1
  funext j
  congr 1
  exact (Fin.ext (by simp)).symm



lemma inner_toRS0
    (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (A B : Tensor0SSpace s I x) :
    tensorInnerPointwise (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel (Tensor0SSpace.toRS0 A))
        (TensorRSSpace.toModel (Tensor0SSpace.toRS0 B)) =
      covariantTensorInnerPointwise (I := I) (M := M) s g x
        (Tensor0SSpace.toModel A) (Tensor0SSpace.toModel B) := by
  rw [show tensorInnerPointwise (I := I) (M := M) g 0 s x
      (TensorRSSpace.toModel (Tensor0SSpace.toRS0 A))
      (TensorRSSpace.toModel (Tensor0SSpace.toRS0 B)) =
        covariantTensorInnerPointwise (I := I) (M := M) (0 + s) g x
          (lowerAllUpperIndices (I := I) (M := M) g 0 s x
            (TensorRSSpace.toModel (Tensor0SSpace.toRS0 A)))
          (lowerAllUpperIndices (I := I) (M := M) g 0 s x
            (TensorRSSpace.toModel (Tensor0SSpace.toRS0 B))) from rfl]
  rw [lower_toRS0 (I := I) (M := M) g s x A,
    lower_toRS0 (I := I) (M := M) g s x B]
  exact inner_nat_cast (I := I) (M := M) g x (Nat.zero_add s)
    (Tensor0SSpace.toModel A) (Tensor0SSpace.toModel B)



lemma inner_toRS0_zero
    (g : SmoothRiemannianMetric I M) (x : M)
    (A B : Tensor0SSpace 0 I x) :
    tensorInnerPointwise (I := I) (M := M) g 0 0 x
        (TensorRSSpace.toModel (Tensor0SSpace.toRS0 A))
        (TensorRSSpace.toModel (Tensor0SSpace.toRS0 B)) =
      tensor0SSpace_evalScalar x A * tensor0SSpace_evalScalar x B := by
  rw [inner_toRS0 (I := I) (M := M) g 0 x,
    tensorInnerPointwise_0s_zero_arity,
    Tensor0SSpace.evalScalar_apply, Tensor0SSpace.evalScalar_apply]
  rfl



lemma inner_toRS0_scalar
    (g : SmoothRiemannianMetric I M) (x : M) (a b : ℝ) :
    tensorInnerPointwise (I := I) (M := M) g 0 0 x
        (TensorRSSpace.toModel
          (Tensor0SSpace.toRS0 ((Tensor0SNabla.tensor0Iso I M x).symm a)))
        (TensorRSSpace.toModel
          (Tensor0SSpace.toRS0 ((Tensor0SNabla.tensor0Iso I M x).symm b))) =
      a * b := by
  rw [inner_toRS0_zero (I := I) (M := M) g x]
  change Tensor0SNabla.tensor0Iso I M x ((Tensor0SNabla.tensor0Iso I M x).symm a) *
    Tensor0SNabla.tensor0Iso I M x ((Tensor0SNabla.tensor0Iso I M x).symm b) = a * b
  rw [ContinuousLinearEquiv.apply_symm_apply,
    ContinuousLinearEquiv.apply_symm_apply]

end Connection
end Integral
end DifferentialGeometry

end
