import DifferentialGeometry.Geometry.Comparison.Variation.FirstVariation
import DifferentialGeometry.Geometry.Comparison.Variation.CovariantChainRule
import DifferentialGeometry.Geometry.Comparison.Variation.PerpFrame
import DifferentialGeometry.Geometry.Connection.ChartBridge.Hessian
import Mathlib.Analysis.Convex.Deriv










noncomputable section

open Bundle Filter Function Manifold Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Variation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [FiniteDimensional ℝ E] in
private theorem chartRep_sec_diff
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (X : ∀ x : M, TangentSpace I x)
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X)) (t : ℝ) :
    DifferentiableAt ℝ
      (chartRepAt (I := I) γ (fun s => X (γ s)) t) t := by
  let α : M := γ t
  have hbase : α ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) α
  have hrepr : ContMDiffAt I 𝓘(ℝ, E) ∞
      (chartE_section_repr (I := I) α X) α :=
    (contMDiffAt_section_iff_chartE I α X hbase).mp hX.contMDiffAt
  have hcomp : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞
      ((chartE_section_repr (I := I) α X) ∘ γ) t :=
    hrepr.comp t hγ.contMDiffAt
  change DifferentiableAt ℝ ((chartE_section_repr (I := I) α X) ∘ γ) t
  exact (contMDiffAt_iff_contDiffAt.mp hcomp).differentiableAt (by simp)

omit [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
private theorem deriv_comp_grad
    (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) (t : ℝ) :
    deriv (f ∘ γ) t =
      g.inner (γ t) (gradFun (I := I) g f (γ t))
        ((mfderiv 𝓘(ℝ, ℝ) I γ t : ℝ →L[ℝ] TangentSpace I (γ t)) 1) := by
  have hfmd : MDifferentiableAt I 𝓘(ℝ, ℝ) f (γ t) :=
    hf.contMDiffAt.mdifferentiableAt (by simp)
  have hγmd : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t :=
    hγ.contMDiffAt.mdifferentiableAt (by simp)
  have hcomp := hfmd.hasMFDerivAt.comp t hγmd.hasMFDerivAt
  rw [hasMFDerivAt_iff_hasFDerivAt, hasFDerivAt_iff_hasDerivAt] at hcomp
  have hd : HasDerivAt (f ∘ γ)
      (mfderiv I 𝓘(ℝ, ℝ) f (γ t)
        ((mfderiv 𝓘(ℝ, ℝ) I γ t : ℝ →L[ℝ] TangentSpace I (γ t)) 1)) t := by
    simpa only [ContinuousLinearMap.comp_apply] using hcomp
  rw [hd.deriv]
  exact (gradFun_metricDual (I := I) g f (γ t)
    ((mfderiv 𝓘(ℝ, ℝ) I γ t : ℝ →L[ℝ] TangentSpace I (γ t)) 1)).symm




omit [InnerProductSpace ℝ E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem deriv2_comp_geo
    (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (hgeo : IsGeodesic (I := I) g γ) (t : ℝ) :
    (deriv^[2] (f ∘ γ)) t =
      hessFun (I := I) g f (γ t)
        ((mfderiv 𝓘(ℝ, ℝ) I γ t : ℝ →L[ℝ] TangentSpace I (γ t)) 1)
        ((mfderiv 𝓘(ℝ, ℝ) I γ t : ℝ →L[ℝ] TangentSpace I (γ t)) 1) := by
  let V : ∀ s, TangentSpace I (γ s) :=
    fun s => gradFun (I := I) g f (γ s)
  let W : ∀ s, TangentSpace I (γ s) :=
    fun s => (mfderiv 𝓘(ℝ, ℝ) I γ s : ℝ →L[ℝ] TangentSpace I (γ s)) 1
  have hfirst : deriv (f ∘ γ) = fun s => g.inner (γ s) (V s) (W s) := by
    funext s
    exact deriv_comp_grad (I := I) g hf hγ s
  have hgrad : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% fun x => gradFun (I := I) g f x) :=
    gradFun_contMDiff_total_section (I := I) g hf
  have hVdiff : DifferentiableAt ℝ (chartRepAt (I := I) γ V t) t := by
    simpa only [V] using
      chartRep_sec_diff (I := I) hγ (fun x => gradFun (I := I) g f x) hgrad t
  have hWdiff : DifferentiableAt ℝ (chartRepAt (I := I) γ W t) t := by
    simpa only [W] using velocity_chartRepAt_differentiableAt (I := I) γ hγ t
  have hinner := metric_compat_hasDerivAt_inner (I := I) (n := ∞)
    (by simp) g γ V W t hγ hVdiff hWdiff
  have hVcov : covDerivAlong (I := I) g γ V t =
      (LeviCivita (I := I) g) (fun x => gradFun (I := I) g f x) (γ t) (W t) := by
    simpa only [V, W] using
      covDerivAlong_restrict_eq_leviCivita (I := I) g γ
        (fun x => gradFun (I := I) g f x) t hγ
        (hgrad.contMDiffAt.mdifferentiableAt (by simp))
  have hWcov : covDerivAlong (I := I) g γ W t = 0 := by
    simpa only [W] using
      covDerivAlong_velocity_eq_zero_of_hasGeodesicEquationAt_C2
        (I := I) g γ t
          (hγ.contMDiffAt.of_le
            (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)))
          (hgeo t)
  calc
    (deriv^[2] (f ∘ γ)) t = deriv (deriv (f ∘ γ)) t := by rfl
    _ = deriv (fun s => g.inner (γ s) (V s) (W s)) t := by rw [hfirst]
    _ = g.inner (γ t) (covDerivAlong (I := I) g γ V t) (W t)
        + g.inner (γ t) (V t) (covDerivAlong (I := I) g γ W t) := hinner.deriv
    _ = g.inner (γ t)
        ((LeviCivita (I := I) g) (fun x => gradFun (I := I) g f x) (γ t) (W t))
        (W t) := by rw [hVcov, hWcov]; simp
    _ = hessFun (I := I) g f (γ t)
        ((mfderiv 𝓘(ℝ, ℝ) I γ t : ℝ →L[ℝ] TangentSpace I (γ t)) 1)
        ((mfderiv 𝓘(ℝ, ℝ) I γ t : ℝ →L[ℝ] TangentSpace I (γ t)) 1) := by
      simpa only [W, gradient_eq_gradFun] using
        (hessFun_eq_cov_grad (I := I) g hf (γ t) (W t) (W t)).symm



omit [InnerProductSpace ℝ E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem deriv2_comp_geo_on
    (g : SmoothRiemannianMetric I M) {f : M → ℝ} {U : Set M}
    (hU : IsOpen U) (hf : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f U)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (hgeo : IsGeodesic (I := I) g γ) {t : ℝ} (ht : γ t ∈ U) :
    (deriv^[2] (f ∘ γ)) t =
      hessFun (I := I) g f (γ t)
        ((mfderiv 𝓘(ℝ, ℝ) I γ t : ℝ →L[ℝ] TangentSpace I (γ t)) 1)
        ((mfderiv 𝓘(ℝ, ℝ) I γ t : ℝ →L[ℝ] TangentSpace I (γ t)) 1) := by
  obtain ⟨F, hF, hFf⟩ := DifferentialGeometry.exists_smooth_germ (I := I) hU ht hf
  have hcomp : (F ∘ γ) =ᶠ[𝓝 t] (f ∘ γ) :=
    hγ.continuous.continuousAt.eventually hFf
  calc
    (deriv^[2] (f ∘ γ)) t = (deriv^[2] (F ∘ γ)) t := by
      exact Filter.EventuallyEq.deriv_eq hcomp.symm.deriv
    _ = hessFun (I := I) g F (γ t)
        ((mfderiv 𝓘(ℝ, ℝ) I γ t : ℝ →L[ℝ] TangentSpace I (γ t)) 1)
        ((mfderiv 𝓘(ℝ, ℝ) I γ t : ℝ →L[ℝ] TangentSpace I (γ t)) 1) :=
      deriv2_comp_geo (I := I) g hF hγ hgeo t
    _ = hessFun (I := I) g f (γ t)
        ((mfderiv 𝓘(ℝ, ℝ) I γ t : ℝ →L[ℝ] TangentSpace I (γ t)) 1)
        ((mfderiv 𝓘(ℝ, ℝ) I γ t : ℝ →L[ℝ] TangentSpace I (γ t)) 1) := by
      rw [hessFun_congr (I := I) g hFf]



omit [InnerProductSpace ℝ E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem strictConvex_geo
    (g : SmoothRiemannianMetric I M) {f : M → ℝ} {U : Set M}
    (hU : IsOpen U) (hf : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f U)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (hgeo : IsGeodesic (I := I) g γ) {D : Set ℝ} (hD : Convex ℝ D)
    (hcont : ContinuousOn (f ∘ γ) D)
    (hmem : MapsTo γ (interior D) U)
    (hpos : ∀ t ∈ interior D,
      0 < hessFun (I := I) g f (γ t)
        ((mfderiv 𝓘(ℝ, ℝ) I γ t : ℝ →L[ℝ] TangentSpace I (γ t)) 1)
        ((mfderiv 𝓘(ℝ, ℝ) I γ t : ℝ →L[ℝ] TangentSpace I (γ t)) 1)) :
    StrictConvexOn ℝ D (f ∘ γ) := by
  apply strictConvexOn_of_deriv2_pos hD hcont
  intro t ht
  rw [deriv2_comp_geo_on (I := I) g hU hf hγ hgeo (hmem ht)]
  exact hpos t ht

end Riemannian
end Geometry
end DifferentialGeometry
