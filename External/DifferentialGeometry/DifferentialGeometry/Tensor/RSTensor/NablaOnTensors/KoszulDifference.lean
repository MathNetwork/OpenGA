import DifferentialGeometry.Tensor.RSTensor.MetricCompatibility
import DifferentialGeometry.Geometry.Connection.LeviCivita.Basic

set_option autoImplicit false
set_option linter.style.longLine false





















namespace Tensor0SBundle

noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [VectorBundle Real E (TangentSpace I : M -> Type _)]
variable [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
variable [T2Space M] [IsManifold I 1 M]
variable [CompleteSpace E] [SigmaCompactSpace M]




omit [T2Space M] [SigmaCompactSpace M] in
theorem difference_symm_at
    (cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _))
    {x : M}
    (htf : DifferentialGeometry.Integral.Connection.IsTorsionFreeAt (I := I) cov x)
    (htf' : DifferentialGeometry.Integral.Connection.IsTorsionFreeAt (I := I) cov' x)
    (X Y : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _)) :
    ((CovariantDerivative.difference cov cov' x) (Y x)) (X x) =
      ((CovariantDerivative.difference cov cov' x) (X x)) (Y x) := by
  have hdY := IsCovariantDerivativeOn.difference_apply
    (hcov := cov.isCovariantDerivativeOnUniv) (hcov' := cov'.isCovariantDerivativeOnUniv)
    (σ := fun p : M => Y p) (x := x) (hx := by trivial)
    (Y.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
  have hdX := IsCovariantDerivativeOn.difference_apply
    (hcov := cov.isCovariantDerivativeOnUniv) (hcov' := cov'.isCovariantDerivativeOnUniv)
    (σ := fun p : M => X p) (x := x) (hx := by trivial)
    (X.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
  have h1 : ((CovariantDerivative.difference cov cov' x) (Y x)) (X x)
      = (cov (fun p : M => Y p) x) (X x) - (cov' (fun p : M => Y p) x) (X x) := by
    have h := congrArg
      (fun L : TangentSpace I x →L[Real] TangentSpace I x => L (X x)) hdY
    simpa using h
  have h2 : ((CovariantDerivative.difference cov cov' x) (X x)) (Y x)
      = (cov (fun p : M => X p) x) (Y x) - (cov' (fun p : M => X p) x) (Y x) := by
    have h := congrArg
      (fun L : TangentSpace I x →L[Real] TangentSpace I x => L (Y x)) hdX
    simpa using h
  have ht := cov.torsion_apply
    (x := x) (X := fun p : M => X p) (Y := fun p : M => Y p)
    (X.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
    (Y.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
  have ht' := cov'.torsion_apply
    (x := x) (X := fun p : M => X p) (Y := fun p : M => Y p)
    (X.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
    (Y.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
  have hz : cov.torsion x (X x) (Y x) = 0 := by
    rw [show cov.torsion x = 0 from htf]
    rfl
  have hz' : cov'.torsion x (X x) (Y x) = 0 := by
    rw [show cov'.torsion x = 0 from htf']
    rfl
  rw [hz] at ht
  rw [hz'] at ht'
  rw [h1, h2]
  linear_combination (norm := module) ht' - ht




omit [CompleteSpace E] [SigmaCompactSpace M] in
theorem nabla_metric_two_term
    (cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (hmc : DifferentialGeometry.Integral.Connection.IsMetricCompatible_gen (I := I) cov g)
    (X Y Z : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x : M) :
    nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 cov' X
        (metricTensorField (I := I) g) x
        (fun q : Fin 2 => if q = 0 then Y x else Z x) =
      g.inner x (((CovariantDerivative.difference cov cov' x) (Y x)) (X x)) (Z x) +
      g.inner x (Y x) (((CovariantDerivative.difference cov cov' x) (Z x)) (X x)) := by
  have hsub := nabla0SFun_sub_cov_two (I := I) cov cov' X Y Z
    (metricTensorField (I := I) g) x
  have hzero := nabla_metric_zero (I := I) cov g hmc X x
  rw [hzero] at hsub
  let N := nabla0SFun 2 cov' X (metricTensorField (I := I) g) x
  rw [show (0 - N) = 0 + -N by rw [sub_eq_add_neg], Tensor0SSpace.add_apply,
    Tensor0SSpace.zero_apply, zero_add,
    show -N = (-1 : ℝ) • N by rw [neg_one_smul], Tensor0SSpace.smul_apply,
    neg_one_smul] at hsub
  simp only [metricTensorField_apply, if_true,
    show ((1 : Fin 2) = 0) = False from by simp, if_false] at hsub
  exact neg_injective hsub




omit [SigmaCompactSpace M] in
theorem koszul_difference
    (cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    {x : M}
    (hmc : DifferentialGeometry.Integral.Connection.IsMetricCompatible_gen (I := I) cov g)
    (htf : DifferentialGeometry.Integral.Connection.IsTorsionFreeAt (I := I) cov x)
    (htf' : DifferentialGeometry.Integral.Connection.IsTorsionFreeAt (I := I) cov' x)
    (X Y Z : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _)) :
    g.inner x (((CovariantDerivative.difference cov cov' x) (Y x)) (X x)) (Z x) =
      (1 / 2) * nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 cov' X
          (metricTensorField (I := I) g) x
          (fun q : Fin 2 => if q = 0 then Y x else Z x) +
      (1 / 2) * nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 cov' Y
          (metricTensorField (I := I) g) x
          (fun q : Fin 2 => if q = 0 then X x else Z x) -
      (1 / 2) * nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 cov' Z
          (metricTensorField (I := I) g) x
          (fun q : Fin 2 => if q = 0 then X x else Y x) := by
  have h1 := nabla_metric_two_term (I := I) cov cov' g hmc X Y Z x
  have h2 := nabla_metric_two_term (I := I) cov cov' g hmc Y X Z x
  have h3 := nabla_metric_two_term (I := I) cov cov' g hmc Z X Y x

  have hsymm1 := difference_symm_at (I := I) cov cov' htf htf' X Y
  have hsymm2 := difference_symm_at (I := I) cov cov' htf htf' X Z
  have hsymm3 := difference_symm_at (I := I) cov cov' htf htf' Y Z
  rw [← hsymm1, hsymm3] at h2
  rw [← hsymm2] at h3

  have hg1 := g.symm x (Y x)
    (((CovariantDerivative.difference cov cov' x) (Z x)) (X x))
  linarith [h1, h2, h3, hg1]

end

end Tensor0SBundle
