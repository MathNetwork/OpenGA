import DifferentialGeometry.Geometry.Metric.Sphere.RoundMetric
import DifferentialGeometry.Geometry.Metric.Pullback
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv




















noncomputable section

open Bundle Manifold Set Metric Module
open scoped Manifold Topology ContDiff RealInnerProductSpace

namespace DifferentialGeometry
namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {n : ℕ} [Fact (finrank ℝ E = n + 1)]


noncomputable def sphereMap (e : E ≃ₗᵢ[ℝ] E) :
    sphere (0 : E) 1 → sphere (0 : E) 1 :=
  Set.codRestrict (fun x : sphere (0 : E) 1 => (e (x : E) : E)) (sphere (0 : E) 1)
    (fun x => by
      rw [mem_sphere_zero_iff_norm, e.norm_map]
      exact mem_sphere_zero_iff_norm.mp x.2)

omit [FiniteDimensional ℝ E] in
@[simp] theorem sphereMap_coe (e : E ≃ₗᵢ[ℝ] E) (x : sphere (0 : E) 1) :
    (sphereMap e x : E) = e (x : E) := rfl

theorem sphereMap_contMDiff (e : E ≃ₗᵢ[ℝ] E) :
    ContMDiff (𝓡 n) (𝓡 n) ∞ (sphereMap e) :=
  ContMDiff.codRestrict_sphere
    (e.toContinuousLinearMap.contMDiff.comp contMDiff_coe_sphere) _


noncomputable def sphereDiffeo (e : E ≃ₗᵢ[ℝ] E) :
    sphere (0 : E) 1 ≃ₘ⟮𝓡 n, 𝓡 n⟯ sphere (0 : E) 1 where
  toFun := sphereMap e
  invFun := sphereMap e.symm
  left_inv x := Subtype.ext (by simp)
  right_inv x := Subtype.ext (by simp)
  contMDiff_toFun := sphereMap_contMDiff (n := n) e
  contMDiff_invFun := sphereMap_contMDiff (n := n) e.symm

@[simp] theorem sphereDiffeo_coe (e : E ≃ₗᵢ[ℝ] E) (x : sphere (0 : E) 1) :
    ((sphereDiffeo (n := n) e x : sphere (0 : E) 1) : E) = e (x : E) := rfl



private theorem mfderiv_lie_apply (e : E ≃ₗᵢ[ℝ] E) (y w : E) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (⇑e) y w = e w := by
  have h : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (⇑e) y = e.toContinuousLinearMap := by
    rw [mfderiv_eq_fderiv, show (⇑e : E → E) = ⇑(e.toContinuousLinearMap) from rfl]
    simp only [ContinuousLinearMap.fderiv]
  rw [h]; rfl




theorem mfderiv_incl_sphereDiffeo (e : E ≃ₗᵢ[ℝ] E) (x : sphere (0 : E) 1)
    (v : TangentSpace (𝓡 n) x) :
    dIncl (n := n) (sphereDiffeo (n := n) e x)
        (mfderiv (𝓡 n) (𝓡 n) (sphereDiffeo (n := n) e) x v)
      = e (dIncl (n := n) x v) := by
  have h0 : (∞ : WithTop ℕ∞) ≠ 0 := by decide
  have hφ : MDifferentiableAt (𝓡 n) (𝓡 n) (sphereDiffeo (n := n) e) x :=
    (sphereDiffeo (n := n) e).contMDiff.mdifferentiableAt h0
  have hι_φx : MDifferentiableAt (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E)
      (sphereDiffeo (n := n) e x) := contMDiff_coe_sphere.mdifferentiableAt h0
  have hι_x : MDifferentiableAt (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) x :=
    contMDiff_coe_sphere.mdifferentiableAt h0
  have he : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (⇑e) ((x : sphere (0 : E) 1) : E) :=
    e.toContinuousLinearMap.contMDiff.mdifferentiableAt h0
  have hcomp : ((↑) : sphere (0 : E) 1 → E) ∘ ⇑(sphereDiffeo (n := n) e)
      = ⇑e ∘ ((↑) : sphere (0 : E) 1 → E) := by
    funext y; exact sphereDiffeo_coe e y
  have e1 := mfderiv_comp x hι_φx hφ
  have e2 := mfderiv_comp x he hι_x
  show mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) (sphereDiffeo (n := n) e x)
        (mfderiv (𝓡 n) (𝓡 n) (sphereDiffeo (n := n) e) x v)
      = e (mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) x v)
  rw [← ContinuousLinearMap.comp_apply, ← e1, hcomp, e2]
  exact mfderiv_lie_apply e _ _



theorem roundInner_sphereDiffeo (e : E ≃ₗᵢ[ℝ] E) (x : sphere (0 : E) 1)
    (v w : TangentSpace (𝓡 n) x) :
    roundInner (sphereDiffeo (n := n) e x)
        (mfderiv (𝓡 n) (𝓡 n) (sphereDiffeo (n := n) e) x v)
        (mfderiv (𝓡 n) (𝓡 n) (sphereDiffeo (n := n) e) x w)
      = roundInner (n := n) x v w := by
  rw [roundInner_apply, roundInner_apply,
    mfderiv_incl_sphereDiffeo, mfderiv_incl_sphereDiffeo]
  exact e.inner_map_map _ _




theorem pullbackMetric_round_eq (e : E ≃ₗᵢ[ℝ] E) :
    Diffeomorph.pullbackMetric (roundMetric (E := E) (n := n)) (sphereDiffeo (n := n) e)
      = roundMetric := by
  have hinner : (fun x => Diffeomorph.pullbackInner (roundMetric (E := E) (n := n))
        (sphereDiffeo (n := n) e) x) = (roundMetric (E := E) (n := n)).inner := by
    funext x
    refine ContinuousLinearMap.ext fun v => ContinuousLinearMap.ext fun w => ?_
    show (Diffeomorph.pullbackMetric (roundMetric (E := E) (n := n))
        (sphereDiffeo (n := n) e)).inner x v w = (roundMetric (E := E) (n := n)).inner x v w
    rw [Diffeomorph.pullbackMetric_inner]
    exact roundInner_sphereDiffeo e x v w
  unfold Diffeomorph.pullbackMetric
  congr 1

end Geometry
end DifferentialGeometry
