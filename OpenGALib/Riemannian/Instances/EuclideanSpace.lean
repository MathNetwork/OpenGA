import Mathlib.Analysis.InnerProductSpace.LinearMap
import OpenGALib.Riemannian.Metric.RiemannianMetric
import OpenGALib.Riemannian.Metric.RiemannianMetric

/-!
# Standard Riemannian metric on inner product spaces

A finite-dimensional real inner product space `E` viewed as a manifold
over itself with the standard inner product as a constant metric tensor.

## Main results

* `euclideanRiemannianMetric` — the flat metric as data
  (`RiemannianMetric (𝓘(ℝ, E)) E`).
* `metricInner_euclidean` — `g.metricInner x v w = ⟪v, w⟫_ℝ` on the
  flat metric.

Reference: do Carmo, *Riemannian Geometry*, §1.1 Example 1.4.

Mathlib upstream: `Mathlib.Geometry.Manifold.Riemannian.Basic`
(`riemannianMetricVectorSpace`).
-/

namespace Riemannian

open Bundle Bornology
open scoped ContDiff Manifold InnerProductSpace

set_option backward.isDefEq.respectTransparency false in
/-- **Math.** The flat metric on a finite-dim inner product space `E`:
the constant `innerSL ℝ` as bundle-section metric tensor. -/
noncomputable def euclideanRiemannianMetric
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    RiemannianMetric (𝓘(ℝ, E)) E where
  inner _ := (innerSL ℝ (E := E) : E →L[ℝ] E →L[ℝ] ℝ)
  symm _ v w := real_inner_comm _ _
  pos _ v hv := real_inner_self_pos.2 hv
  isVonNBounded x := by
    change IsVonNBounded ℝ {v : E | ⟪v, v⟫_ℝ < 1}
    have heq : Metric.ball (0 : E) 1 = {v : E | ⟪v, v⟫_ℝ < 1} := by
      ext v
      simp only [Metric.mem_ball, dist_zero_right, norm_eq_sqrt_re_inner (𝕜 := ℝ),
        RCLike.re_to_real, Set.mem_setOf_eq]
      conv_lhs => rw [show (1 : ℝ) = √1 by simp]
      rw [Real.sqrt_lt_sqrt_iff]
      exact real_inner_self_nonneg
    rw [← heq]
    exact NormedSpace.isVonNBounded_ball ℝ E 1
  contMDiff := by
    intro x
    rw [contMDiffAt_section]
    convert contMDiffAt_const (c := innerSL ℝ (E := E))
    ext v w
    simp [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates, TangentSpace]

/-- **Math.** $\langle v, w\rangle_g = \langle v, w\rangle_\mathbb{R}$ on the flat metric. -/
@[simp]
theorem metricInner_euclidean
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x : E) (v w : E) :
    (euclideanRiemannianMetric E).metricInner x v w = ⟪v, w⟫_ℝ :=
  rfl

end Riemannian
