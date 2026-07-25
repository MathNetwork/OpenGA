import DifferentialGeometry.Geometry.Metric.Scaling
import DifferentialGeometry.Geometry.Operator.Operators

set_option autoImplicit false
set_option linter.style.longLine false







namespace DifferentialGeometry.Integral.Connection

noncomputable section

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem metricSharp_scaleMetric
    (c : Real) (hc : 0 < c) (g : SmoothRiemannianMetric I M) (x : M)
    (alpha : Module.Dual Real (TangentSpace I x)) :
    metricSharp (I := I) (scaleMetric (I := I) c hc g) x alpha =
      c⁻¹ • metricSharp (I := I) g x alpha := by
  apply metricFlatLinear_injective (I := I) (scaleMetric (I := I) c hc g) x
  ext w
  simp only [metricFlatLinear_apply]
  calc
    (scaleMetric (I := I) c hc g).inner x
        (metricSharp (I := I) (scaleMetric (I := I) c hc g) x alpha) w =
        alpha w := inner_metricSharp (I := I) (scaleMetric (I := I) c hc g) x alpha w
    _ =
        (scaleMetric (I := I) c hc g).inner x
          (c⁻¹ • metricSharp (I := I) g x alpha) w := by
          have hinner :
              ((g.inner x) ((metricFlatEquiv (I := I) g x).symm alpha)) w =
                alpha w := by
            simpa [metricSharp] using inner_metricSharp (I := I) g x alpha w
          symm
          calc
            (scaleMetric (I := I) c hc g).inner x
                (c⁻¹ • metricSharp (I := I) g x alpha) w =
                c * (c⁻¹ *
                  ((g.inner x) ((metricFlatEquiv (I := I) g x).symm alpha)) w) := by
                  rw [scaleMetric_inner]
                  simp only [metricSharp, map_smul, ContinuousLinearMap.coe_smul',
                    Pi.smul_apply, smul_eq_mul]
            _ = c * (c⁻¹ * alpha w) :=
                congrArg (fun z : Real => c * (c⁻¹ * z)) hinner
            _ = alpha w := by
                field_simp [ne_of_gt hc]


theorem gradientFun_scale
    (c : Real) (hc : 0 < c) (g : SmoothRiemannianMetric I M)
    (f : M -> Real) (x : M) :
    gradientFun (I := I) (scaleMetric (I := I) c hc g) f x =
      c⁻¹ • gradientFun (I := I) g f x := by
  simpa [gradientFun] using
    metricSharp_scaleMetric (I := I) c hc g x
      (mfderiv I 𝓘(Real, Real) f x).toLinearMap



theorem laplacian_scaleMetric
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (c : Real) (hc : 0 < c)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    {f : M -> Real} {x : M}
    (hgrad : MDiffAt (T% fun y : M => gradientFun (I := I) g f y) x) :
    laplacian (I := I) cov (scaleMetric (I := I) c hc g) f x =
      c⁻¹ * laplacian (I := I) cov g f x := by
  have hgrad_eq :
      gradientFun (I := I) (scaleMetric (I := I) c hc g) f =
        c⁻¹ • gradientFun (I := I) g f := by
    funext y
    exact gradientFun_scale (I := I) c hc g f y
  calc
    laplacian (I := I) cov (scaleMetric (I := I) c hc g) f x =
        divergence (I := I) cov (c⁻¹ • gradientFun (I := I) g f) x := by
          simp [laplacian, hgrad_eq]
    _ = c⁻¹ * laplacian (I := I) cov g f x := by
          simpa [laplacian] using
            divergence_const_smul (I := I) cov inferInstance c⁻¹ hgrad



theorem laplacian_scaleMetric_const_smul
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (c : Real) (hc : 0 < c)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    {f : M -> Real} {x : M}
    (hf : ∀ y : M, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hgrad : MDiffAt (T% fun y : M => gradientFun (I := I) g f y) x) :
    laplacian (I := I) cov (scaleMetric (I := I) c hc g) (c⁻¹ • f) x =
      c⁻¹ * c⁻¹ * laplacian (I := I) cov g f x := by
  have hgradScaled :
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (scaleMetric (I := I) c hc g) f y) x := by
    have hscale :
        MDiffAt (T% fun y : M =>
          c⁻¹ • gradientFun (I := I) g f y) x := by
      simpa [Pi.smul_apply] using
        (mdifferentiableAt_const (I := I) (c := c⁻¹)).smul_section hgrad
    have hpt : ∀ y : M,
        gradientFun (I := I) (scaleMetric (I := I) c hc g) f y =
          c⁻¹ • gradientFun (I := I) g f y := by
      intro y
      exact gradientFun_scale (I := I) c hc g f y
    have htotal :
        (T% fun y : M =>
          gradientFun (I := I) (scaleMetric (I := I) c hc g) f y) =
          (T% fun y : M => c⁻¹ • gradientFun (I := I) g f y) := by
      funext y
      change
          TotalSpace.mk' E y
              (gradientFun (I := I) (scaleMetric (I := I) c hc g) f y) =
            TotalSpace.mk' E y (c⁻¹ • gradientFun (I := I) g f y)
      rw [hpt y]
    rw [htotal]
    exact hscale
  rw [laplacian_const_smul (I := I) cov (scaleMetric (I := I) c hc g)
    c⁻¹ hf hgradScaled]
  rw [laplacian_scaleMetric (I := I) c hc cov g hgrad]
  ring

end

end DifferentialGeometry.Integral.Connection
