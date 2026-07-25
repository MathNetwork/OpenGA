import DifferentialGeometry.Geometry.Metric.Basic
import DifferentialGeometry.Geometry.Metric.MetricExistence
import DifferentialGeometry.Bundle.ClmSectionSmooth
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv






















noncomputable section

open Bundle Manifold Set Metric ContinuousLinearMap Module
open scoped Manifold Topology ContDiff RealInnerProductSpace

namespace DifferentialGeometry
namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {n : ℕ} [Fact (finrank ℝ E = n + 1)]




noncomputable def dIncl (x : sphere (0 : E) 1) :
    TangentSpace (𝓡 n) x →L[ℝ] E :=
  mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) x



noncomputable def roundInner (x : sphere (0 : E) 1) :
    TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ] ℝ :=
  (ContinuousLinearMap.precomp ℝ (dIncl (n := n) x)).comp
    ((innerSL ℝ).comp (dIncl (n := n) x))

@[simp] theorem roundInner_apply (x : sphere (0 : E) 1)
    (v w : TangentSpace (𝓡 n) x) :
    roundInner (n := n) x v w = ⟪dIncl (n := n) x v, dIncl (n := n) x w⟫ := by
  simp only [roundInner, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.precomp_apply, innerSL_apply_apply]

theorem roundInner_symm (x : sphere (0 : E) 1) (v w : TangentSpace (𝓡 n) x) :
    roundInner (n := n) x v w = roundInner (n := n) x w v := by
  rw [roundInner_apply, roundInner_apply, real_inner_comm]

theorem dIncl_ne_zero {x : sphere (0 : E) 1} {v : TangentSpace (𝓡 n) x}
    (hv : v ≠ 0) : dIncl (n := n) x v ≠ 0 := by
  intro h
  refine hv (mfderiv_coe_sphere_injective x ?_)
  rw [map_zero]
  exact h

theorem roundInner_pos (x : sphere (0 : E) 1) (v : TangentSpace (𝓡 n) x)
    (hv : v ≠ 0) : 0 < roundInner (n := n) x v v := by
  rw [roundInner_apply, real_inner_self_eq_norm_mul_norm]
  exact mul_pos (norm_pos_iff.mpr (dIncl_ne_zero (n := n) hv))
    (norm_pos_iff.mpr (dIncl_ne_zero (n := n) hv))





private theorem flatInner_comp_incl_contMDiff :
    ContMDiff (𝓡 n) (𝓘(ℝ, E).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x : sphere (0 : E) 1 => TotalSpace.mk'
        (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : E => TangentSpace 𝓘(ℝ, E) x →L[ℝ] TangentSpace 𝓘(ℝ, E) x →L[ℝ] ℝ)
        (((↑) : sphere (0 : E) 1 → E) x)
        ((riemannianMetricVectorSpace E).inner (((↑) : sphere (0 : E) 1 → E) x))) :=
  ((riemannianMetricVectorSpace E).contMDiff.of_le le_top).comp contMDiff_coe_sphere




private theorem dIncl_apply_section_contMDiff
    (Y : ∀ x : sphere (0 : E) 1, TangentSpace (𝓡 n) x)
    (hY : ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun x : sphere (0 : E) 1 =>
        TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (E := TangentSpace (𝓡 n)) x (Y x))) :
    ContMDiff (𝓡 n) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun x : sphere (0 : E) 1 =>
        TotalSpace.mk' E (E := (TangentSpace 𝓘(ℝ, E) : E → Type _))
          (((↑) : sphere (0 : E) 1 → E) x)
          (mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) x (Y x))) :=
  ((contMDiff_coe_sphere (n := n)).contMDiff_tangentMap (le_refl _)).comp hY


noncomputable def roundMetric : SmoothRiemannianMetric (𝓡 n) (sphere (0 : E) 1) where
  inner x := roundInner (n := n) x
  symm x v w := roundInner_symm (n := n) x v w
  pos x v hv := roundInner_pos (n := n) x v hv
  isVonNBounded x :=
    posDef_isVonNBounded (E := EuclideanSpace ℝ (Fin n)) (roundInner (n := n) x)
      (fun v hv => roundInner_pos (n := n) x v hv)
  contMDiff := by
    classical
    haveI : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
    haveI : CompactSpace (sphere (0 : E) 1) := Metric.sphere.compactSpace _ _
    apply cotangentCov_clmSection_smooth_aux
      (V₂ := fun x : sphere (0 : E) 1 => TangentSpace (𝓡 n) x →L[ℝ] ℝ)
      (φ := fun x : sphere (0 : E) 1 => roundInner (n := n) x)
    intro Y
    apply cotangentCov_clmSection_smooth_aux
      (V₂ := fun _ : sphere (0 : E) 1 => ℝ)
      (φ := fun x : sphere (0 : E) 1 => roundInner (n := n) x (Y x))
    intro W

    have hv := dIncl_apply_section_contMDiff (n := n) (fun x => Y x) Y.contMDiff
    have hw := dIncl_apply_section_contMDiff (n := n) (fun x => W x) W.contMDiff

    have hg := flatInner_comp_incl_contMDiff (E := E) (n := n)


    have h_total : ContMDiff (𝓡 n) (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) ∞
        (fun x : sphere (0 : E) 1 => TotalSpace.mk' ℝ
          (E := Bundle.Trivial E ℝ)
          (((↑) : sphere (0 : E) 1 → E) x)
          ((riemannianMetricVectorSpace E).inner (((↑) : sphere (0 : E) 1 → E) x)
            (mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) x (Y x))
            (mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) x (W x)))) :=
      ContMDiff.clm_bundle_apply₂
        (E₁ := fun b : E => TangentSpace 𝓘(ℝ, E) b)
        (E₂ := fun b : E => TangentSpace 𝓘(ℝ, E) b)
        (E₃ := fun _ : E => ℝ)
        (b := fun x : sphere (0 : E) 1 => ((↑) : sphere (0 : E) 1 → E) x)
        (ψ := fun x : sphere (0 : E) 1 =>
          (riemannianMetricVectorSpace E).inner (((↑) : sphere (0 : E) 1 → E) x))
        (v := fun x : sphere (0 : E) 1 =>
          mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) x (Y x))
        (w := fun x : sphere (0 : E) 1 =>
          mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) x (W x))
        hg hv hw

    have h_scalar : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞
        (fun x : sphere (0 : E) 1 => roundInner (n := n) x (Y x) (W x)) := by
      have h_eq : (fun x : sphere (0 : E) 1 => roundInner (n := n) x (Y x) (W x))
          = fun x : sphere (0 : E) 1 =>
              (riemannianMetricVectorSpace E).inner (((↑) : sphere (0 : E) 1 → E) x)
                (mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) x (Y x))
                (mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) x (W x)) := by
        funext x
        rw [roundInner_apply]
        rfl
      rw [h_eq]
      intro x
      have h_at := h_total x
      rw [contMDiffAt_totalSpace] at h_at
      exact h_at.2

    intro x
    rw [contMDiffAt_section]
    refine (h_scalar.contMDiffAt).congr_of_eventuallyEq ?_
    filter_upwards with y
    rfl

@[simp] theorem roundMetric_inner (x : sphere (0 : E) 1) (v w : TangentSpace (𝓡 n) x) :
    (roundMetric (E := E) (n := n)).inner x v w
      = ⟪dIncl (n := n) x v, dIncl (n := n) x w⟫ :=
  roundInner_apply (n := n) x v w

end Geometry
end DifferentialGeometry
