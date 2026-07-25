import DifferentialGeometry.Tensor.RSTensor.Defs
import DifferentialGeometry.Geometry.Metric.TensorInner.TangentRiemannian
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Defs
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Algebra
import DifferentialGeometry.Geometry.Metric.PointwiseInner.DualMetric
import DifferentialGeometry.Geometry.Metric.ChartGram
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Topology.VectorBundle.Riemannian
import Mathlib.Analysis.LocallyConvex.Bounded
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

noncomputable section

open Bundle Set IsManifold ContinuousLinearMap Bornology
open scoped Manifold Topology Bundle ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Tensor
namespace Tensor0SRiemannian

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

lemma posDef_bilin_unit_ball_isBounded
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [Nontrivial F]
    (B : F →L[ℝ] F →L[ℝ] ℝ)
    (hPD : ∀ v : F, v ≠ 0 → 0 < B v v)
    (hNN : ∀ v : F, 0 ≤ B v v)
    (hBilin_smul_left : ∀ (c : ℝ) (v w : F), B (c • v) w = c * B v w)
    (hBilin_smul_right : ∀ (c : ℝ) (v w : F), B v (c • w) = c * B v w) :
    Bornology.IsBounded {v : F | B v v < 1} := by
  haveI : ProperSpace F := FiniteDimensional.proper ℝ _
  classical
  set Q : F → ℝ := fun v => B v v with hQ_def
  have hQ_cont : Continuous Q :=
    Continuous.clm_apply B.continuous continuous_id
  have hsphere_compact : IsCompact (Metric.sphere (0 : F) 1) :=
    isCompact_sphere _ _
  have hsphere_nonempty : (Metric.sphere (0 : F) 1).Nonempty := by
    rcases exists_ne (0 : F) with ⟨v₀, hv₀⟩
    refine ⟨‖v₀‖⁻¹ • v₀, ?_⟩
    rw [Metric.mem_sphere, dist_zero_right]
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    have hv₀_norm_ne : ‖v₀‖ ≠ 0 := norm_ne_zero_iff.mpr hv₀
    exact inv_mul_cancel₀ hv₀_norm_ne
  obtain ⟨v_min, hv_min_mem, hv_min⟩ :=
    hsphere_compact.exists_isMinOn hsphere_nonempty hQ_cont.continuousOn
  set c := Q v_min with hc_def
  have hv_min_ne : v_min ≠ 0 := by
    intro h
    rw [Metric.mem_sphere, dist_zero_right, h, norm_zero] at hv_min_mem
    exact one_ne_zero hv_min_mem.symm
  have hc_pos : 0 < c := hPD v_min hv_min_ne
  have hQ_lower : ∀ v : F, c * ‖v‖ ^ 2 ≤ Q v := by
    intro v
    by_cases hv_zero : v = 0
    · subst hv_zero
      simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, mul_zero]
      exact hNN 0
    · have hv_norm_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv_zero
      have hv_norm_ne : ‖v‖ ≠ 0 := ne_of_gt hv_norm_pos
      set u := ‖v‖⁻¹ • v with hu_def
      have hu_norm : ‖u‖ = 1 := by
        rw [hu_def, norm_smul]
        rw [norm_inv, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
        exact inv_mul_cancel₀ hv_norm_ne
      have hu_sphere : u ∈ Metric.sphere (0 : F) 1 := by
        rw [Metric.mem_sphere, dist_zero_right]; exact hu_norm
      have hQu : c ≤ Q u := hv_min hu_sphere
      have hQu_eq : Q u = ‖v‖⁻¹ * ‖v‖⁻¹ * Q v := by
        change B u u = ‖v‖⁻¹ * ‖v‖⁻¹ * B v v
        rw [hu_def, hBilin_smul_left, hBilin_smul_right]
        ring
      rw [hQu_eq] at hQu
      have hT_sq_pos : 0 < ‖v‖ ^ 2 := pow_pos hv_norm_pos 2
      have hineq : c * ‖v‖ ^ 2 ≤ (‖v‖⁻¹ * ‖v‖⁻¹ * Q v) * ‖v‖ ^ 2 := by gcongr
      have hsimp : (‖v‖⁻¹ * ‖v‖⁻¹ * Q v) * ‖v‖ ^ 2 = Q v := by field_simp
      rw [hsimp] at hineq
      exact hineq
  refine (Metric.isBounded_iff_subset_ball 0).mpr ?_
  refine ⟨1 / Real.sqrt c + 1, fun v hv => ?_⟩
  rw [Set.mem_setOf_eq] at hv
  have h1 : c * ‖v‖ ^ 2 < 1 := lt_of_le_of_lt (hQ_lower v) hv
  have h2 : ‖v‖ ^ 2 < c⁻¹ := by
    have hh : ‖v‖ ^ 2 < 1 / c := by rwa [lt_div_iff₀ hc_pos, mul_comm]
    rwa [show (1 : ℝ) / c = c⁻¹ from one_div _] at hh
  have h3 : ‖v‖ < Real.sqrt (c⁻¹) := by
    rw [show ‖v‖ = Real.sqrt (‖v‖ ^ 2) from (Real.sqrt_sq (norm_nonneg _)).symm]
    exact Real.sqrt_lt_sqrt (by positivity) h2
  have hsqrt_eq : Real.sqrt (c⁻¹) = 1 / Real.sqrt c := by
    rw [Real.sqrt_inv, one_div]
  rw [hsqrt_eq] at h3
  rw [Metric.mem_ball, dist_zero_right]
  linarith

end Tensor0SRiemannian
end Tensor
end DifferentialGeometry

end
