import DifferentialGeometry.Geometry.Metric.Scaling
import Mathlib.Geometry.Manifold.Riemannian.PathELength

set_option autoImplicit false









noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

noncomputable def riemannianEDistOf
    (g : SmoothRiemannianMetric I M) (x y : M) : ℝ≥0∞ :=
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  Manifold.riemannianEDist I x y

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
private theorem edistOf_iInf
    (g : SmoothRiemannianMetric I M) (x y : M) :
    riemannianEDistOf (I := I) g x y =
      ⨅ (γ : Path x y) (_ : CMDiff 1 γ),
        ∫⁻ t, ENNReal.ofReal (Real.sqrt
          (g.inner (γ t) (mfderiv% γ t 1) (mfderiv% γ t 1))) := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  change Manifold.riemannianEDist I x y = _
  rw [Manifold.riemannianEDist]
  refine iInf_congr fun γ => ?_
  refine iInf_congr fun hγ => ?_
  refine lintegral_congr fun t => ?_
  rw [← ofReal_norm_eq_enorm, norm_eq_sqrt_real_inner]
  congr 2

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in


theorem edistOf_scale
    (c : Real) (hc : 0 < c) (g : SmoothRiemannianMetric I M)
    (x y : M) :
    riemannianEDistOf (I := I) (scaleMetric (I := I) c hc g) x y =
      ENNReal.ofReal (Real.sqrt c) * riemannianEDistOf (I := I) g x y := by
  rw [edistOf_iInf, edistOf_iInf]
  let a : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt c)
  have ha0 : a ≠ 0 := by
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.2 hc))
  have hatop : a ≠ (∞ : ℝ≥0∞) := ENNReal.ofReal_ne_top
  change
    (⨅ (γ : Path x y) (_ : CMDiff 1 γ),
      ∫⁻ t, ENNReal.ofReal (Real.sqrt
        ((scaleMetric (I := I) c hc g).inner
          (γ t) (mfderiv% γ t 1) (mfderiv% γ t 1))) =
      a * ⨅ (γ : Path x y) (_ : CMDiff 1 γ),
        ∫⁻ t, ENNReal.ofReal (Real.sqrt
          (g.inner (γ t) (mfderiv% γ t 1) (mfderiv% γ t 1))))
  rw [ENNReal.mul_iInf_of_ne ha0 hatop]
  refine iInf_congr fun γ => ?_
  rw [ENNReal.mul_iInf_of_ne ha0 hatop]
  refine iInf_congr fun hγ => ?_
  rw [← lintegral_const_mul' a _ hatop]
  refine lintegral_congr fun t => ?_
  simp only [scaleMetric_inner]
  rw [Real.sqrt_mul hc.le]
  rw [ENNReal.ofReal_mul (Real.sqrt_nonneg c)]



theorem edistBall_scale
    (c : Real) (hc : 0 < c) (g : SmoothRiemannianMetric I M)
    (x : M) (r : Real) :
    {y : M | riemannianEDistOf (I := I)
        (scaleMetric (I := I) c hc g) x y <
          ENNReal.ofReal (Real.sqrt c * r)} =
      {y : M | riemannianEDistOf (I := I) g x y < ENNReal.ofReal r} := by
  ext y
  simp only [Set.mem_setOf_eq]
  rw [edistOf_scale]
  rw [ENNReal.ofReal_mul (Real.sqrt_nonneg c)]
  let a : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt c)
  have ha0 : a ≠ 0 := by
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.2 hc))
  have hatop : a ≠ (∞ : ℝ≥0∞) := ENNReal.ofReal_ne_top
  exact ENNReal.mul_lt_mul_iff_right ha0 hatop

end DifferentialGeometry

end
