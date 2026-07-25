import DifferentialGeometry.Geometry.Operator.Gradient
import DifferentialGeometry.Geometry.Connection.TensorNabla.CotangentExtension


noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Integral
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

theorem gradient_eq_gradFun
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M) :
    gradientFun (I := I) g f x = gradFun (I := I) g f x := rfl

theorem gradFun_metricDual
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M)
    (v : TangentSpace I x) :
    g.inner x (gradFun (I := I) g f x) v = mfderiv I 𝓘(ℝ, ℝ) f x v :=
  inner_gradFun (I := I) g f x v

theorem gradFun_metricDual_right
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M)
    (v : TangentSpace I x) :
    g.inner x v (gradFun (I := I) g f x) = mfderiv I 𝓘(ℝ, ℝ) f x v :=
  inner_gradFun_right (I := I) g f x v

theorem metricFlatMap_gradFun
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M) :
    metricFlatMap (I := I) g x (gradFun (I := I) g f x) =
      (mfderiv I 𝓘(ℝ, ℝ) f x).toLinearMap := by
  ext v
  rw [metricFlatMap_apply]
  exact gradFun_metricDual (I := I) g f x v

lemma gradFun_eq_metricSharp_mfderiv
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M) :
    gradFun (I := I) g f x =
      metricSharp (I := I) g x (mfderiv I 𝓘(ℝ, ℝ) f x).toLinearMap := rfl

theorem gradFun_unique
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) {x : M}
    {w : TangentSpace I x}
    (hw : ∀ v : TangentSpace I x, g.inner x w v = mfderiv I 𝓘(ℝ, ℝ) f x v) :
    w = gradFun (I := I) g f x := by
  apply metricFlatLinear_injective (I := I) g x
  ext v
  rw [metricFlatLinear_apply, metricFlatLinear_apply]
  rw [hw v]
  exact (gradFun_metricDual (I := I) g f x v).symm

theorem metricFlat_gradFun_apply
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M)
    (v : TangentSpace I x) :
    metricFlat g (fun y => gradFun (I := I) g f y) x v =
      mfderiv I 𝓘(ℝ, ℝ) f x v := by
  change g.inner x (gradFun (I := I) g f x) v = _
  exact gradFun_metricDual (I := I) g f x v

theorem metricFlat_gradFun_eq_extDerivFun
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M) :
    metricFlat g (fun y => gradFun (I := I) g f y) x = extDerivFun (I := I) f x := by
  ext v
  rw [metricFlat_gradFun_apply (I := I) g f x v]
  rfl

@[simp] lemma gradFun_const
    (g : SmoothRiemannianMetric I M) (c : ℝ) (x : M) :
    gradFun (I := I) g (fun _ : M => c) x = (0 : TangentSpace I x) := by
  apply gradFun_eq_zero_of_mfderiv_eq_zero (I := I) g (f := fun _ : M => c)
  exact mfderiv_const

@[simp] lemma gradFun_zero
    (g : SmoothRiemannianMetric I M) (x : M) :
    gradFun (I := I) g (fun _ : M => (0 : ℝ)) x = (0 : TangentSpace I x) :=
  gradFun_const (I := I) g 0 x

lemma gradFun_metricDual_extDerivFun
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M)
    (v : TangentSpace I x) :
    g.inner x (gradFun (I := I) g f x) v = extDerivFun (I := I) f x v := by
  rw [gradFun_metricDual (I := I) g f x v]
  rfl

theorem gradFun_add
    (g : SmoothRiemannianMetric I M) {f h : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (hh : MDifferentiableAt I 𝓘(ℝ, ℝ) h x) :
    gradFun (I := I) g (fun y => f y + h y) x =
      gradFun (I := I) g f x + gradFun (I := I) g h x := by
  refine (gradFun_unique (I := I) g (fun y => f y + h y)
    (w := gradFun (I := I) g f x + gradFun (I := I) g h x) ?_).symm
  intro v
  have h_left : g.inner x (gradFun (I := I) g f x + gradFun (I := I) g h x) v =
      extDerivFun (I := I) f x v + extDerivFun (I := I) h x v := by
    rw [show g.inner x (gradFun (I := I) g f x + gradFun (I := I) g h x) v =
          g.inner x (gradFun (I := I) g f x) v + g.inner x (gradFun (I := I) g h x) v from
        by rw [map_add, ContinuousLinearMap.add_apply]]
    rw [gradFun_metricDual_extDerivFun (I := I) g f x v,
        gradFun_metricDual_extDerivFun (I := I) g h x v]
  have h_right :
      (mfderiv I 𝓘(ℝ, ℝ) (fun y : M => f y + h y) x v : ℝ) =
        extDerivFun (I := I) f x v + extDerivFun (I := I) h x v := by
    have hsum : (fun y : M => f y + h y) = f + h := rfl
    change extDerivFun (I := I) (fun y : M => f y + h y) x v = _
    rw [hsum, extDerivFun_add hf hh, ContinuousLinearMap.add_apply]
  rw [h_left, ← h_right]

theorem gradFun_const_smul
    (g : SmoothRiemannianMetric I M) (c : ℝ) {f : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x) :
    gradFun (I := I) g (c • f) x = c • gradFun (I := I) g f x := by
  refine (gradFun_unique (I := I) g (c • f)
    (w := c • gradFun (I := I) g f x) ?_).symm
  intro v
  have h_left : g.inner x (c • gradFun (I := I) g f x) v =
      c * extDerivFun (I := I) f x v := by
    rw [show g.inner x (c • gradFun (I := I) g f x) v =
          c * g.inner x (gradFun (I := I) g f x) v from
        by rw [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]]
    rw [gradFun_metricDual_extDerivFun (I := I) g f x v]
  have h_right : (mfderiv I 𝓘(ℝ, ℝ) (c • f) x v : ℝ) =
      c * extDerivFun (I := I) f x v := by
    have h := const_smul_mfderiv (I := I) (𝕜 := ℝ) (f := f) (z := x) hf c
    change extDerivFun (I := I) (c • f) x v = c * extDerivFun (I := I) f x v
    suffices hsmul : extDerivFun (I := I) (c • f) x = c • extDerivFun (I := I) f x by
      rw [hsmul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    change (NormedSpace.fromTangentSpace ((c • f) x)).toContinuousLinearMap ∘L
            (mfderiv I 𝓘(ℝ, ℝ) (c • f) x) =
          c • ((NormedSpace.fromTangentSpace (f x)).toContinuousLinearMap ∘L
            mfderiv I 𝓘(ℝ, ℝ) f x)
    rw [h]
    rfl
  rw [h_left, ← h_right]

theorem gradFun_contMDiff_total_section [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E x (gradFun (I := I) g f x)) :=
  gradFun_contMDiff_total (I := I) g hf

end Connection
end Integral
end DifferentialGeometry
