import DifferentialGeometry.Geometry.Geodesic.Equation
import DifferentialGeometry.Geometry.Geodesic.Existence
import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique



noncomputable section

open Bundle Manifold Set Filter Function
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure

section ChartFixedUniqueness

variable [I.Boundaryless] [CompleteSpace E]

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem isMIntegralCurveAt_geodesicVectorFieldChart_eventuallyEq
    {g : SmoothRiemannianMetric I M} {α : M} {t₀ : ℝ}
    {f₁ f₂ : ℝ → TangentBundle I M}
    (hα_src : (f₁ t₀).proj ∈ (chartAt H α).source)
    (hf₁ : IsMIntegralCurveAt f₁ (geodesicVectorFieldChart (I := I) g α) t₀)
    (hf₂ : IsMIntegralCurveAt f₂ (geodesicVectorFieldChart (I := I) g α) t₀)
    (h0 : f₁ t₀ = f₂ t₀) :
    f₁ =ᶠ[𝓝 t₀] f₂ := by
  have hsmooth_inf :
      ContMDiffAt I.tangent I.tangent.tangent ∞
        (fun p : TangentBundle I M =>
          (⟨p, geodesicVectorFieldChart (I := I) g α p⟩ :
            TangentBundle I.tangent (TangentBundle I M)))
        (f₁ t₀) :=
    geodesicVectorFieldChart_contMDiffAt (I := I) g α
      (p₀ := f₁ t₀) hα_src
  have hsmooth1 :
      ContMDiffAt I.tangent I.tangent.tangent 1
        (fun p : TangentBundle I M =>
          (⟨p, geodesicVectorFieldChart (I := I) g α p⟩ :
            TangentBundle I.tangent (TangentBundle I M)))
        (f₁ t₀) :=
    hsmooth_inf.of_le (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))
  exact
    isMIntegralCurveAt_eventuallyEq_of_contMDiffAt_boundaryless
      (I := I.tangent) (M := TangentBundle I M)
      (v := geodesicVectorFieldChart (I := I) g α)
      (γ := f₁) (γ' := f₂) (t₀ := t₀)
      hsmooth1 hf₁ hf₂ h0

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem projectCurve_eventuallyEq_of_isMIntegralCurveAt_geodesicVectorFieldChart
    {g : SmoothRiemannianMetric I M} {α : M} {t₀ : ℝ}
    {f₁ f₂ : ℝ → TangentBundle I M}
    (hα_src : (f₁ t₀).proj ∈ (chartAt H α).source)
    (hf₁ : IsMIntegralCurveAt f₁ (geodesicVectorFieldChart (I := I) g α) t₀)
    (hf₂ : IsMIntegralCurveAt f₂ (geodesicVectorFieldChart (I := I) g α) t₀)
    (h0 : f₁ t₀ = f₂ t₀) :
    projectCurve (I := I) f₁ =ᶠ[𝓝 t₀] projectCurve (I := I) f₂ := by
  have heq :=
    isMIntegralCurveAt_geodesicVectorFieldChart_eventuallyEq
      (I := I) (g := g) (α := α) (t₀ := t₀)
      (f₁ := f₁) (f₂ := f₂) hα_src hf₁ hf₂ h0
  refine heq.mono ?_
  intro t ht
  simp [projectCurve, ht]

end ChartFixedUniqueness

section GeodesicUniqueness

variable [I.Boundaryless] [CompleteSpace E]

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem isGeodesicAt_eventuallyEq
    {g : SmoothRiemannianMetric I M} {γ₁ γ₂ : ℝ → M} {α : M} {t₀ : ℝ}
    {f₁ f₂ : ℝ → TangentBundle I M}
    (hα_src : γ₁ t₀ ∈ (chartAt H α).source)
    (hproj₁ : ∀ t, (f₁ t).proj = γ₁ t)
    (hproj₂ : ∀ t, (f₂ t).proj = γ₂ t)
    (hf₁ : IsMIntegralCurveAt f₁ (geodesicVectorFieldChart (I := I) g α) t₀)
    (hf₂ : IsMIntegralCurveAt f₂ (geodesicVectorFieldChart (I := I) g α) t₀)
    (h0 : f₁ t₀ = f₂ t₀) :
    γ₁ =ᶠ[𝓝 t₀] γ₂ := by
  have hα_src' : (f₁ t₀).proj ∈ (chartAt H α).source := by
    rw [hproj₁ t₀]; exact hα_src
  have hproj_eq :=
    projectCurve_eventuallyEq_of_isMIntegralCurveAt_geodesicVectorFieldChart
      (I := I) (g := g) (α := α) (t₀ := t₀)
      (f₁ := f₁) (f₂ := f₂) hα_src' hf₁ hf₂ h0
  refine hproj_eq.mono ?_
  intro t ht
  rw [projectCurve_apply, projectCurve_apply] at ht
  rw [← hproj₁ t, ← hproj₂ t]; exact ht

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem isGeodesicAt_eventuallyEq_of_lift_eq
    {g : SmoothRiemannianMetric I M} {γ₁ γ₂ : ℝ → M} {t₀ : ℝ}
    {f₁ f₂ : ℝ → TangentBundle I M}
    (hproj₁ : ∀ t, (f₁ t).proj = γ₁ t)
    (hproj₂ : ∀ t, (f₂ t).proj = γ₂ t)
    (hf₁ : IsMIntegralCurveAt f₁
      (geodesicVectorFieldChart (I := I) g (γ₁ t₀)) t₀)
    (hf₂ : IsMIntegralCurveAt f₂
      (geodesicVectorFieldChart (I := I) g (γ₁ t₀)) t₀)
    (h0 : f₁ t₀ = f₂ t₀) :
    γ₁ =ᶠ[𝓝 t₀] γ₂ :=
  isGeodesicAt_eventuallyEq (I := I) (g := g) (γ₁ := γ₁) (γ₂ := γ₂)
    (α := γ₁ t₀) (t₀ := t₀) (f₁ := f₁) (f₂ := f₂)
    (mem_chart_source H (γ₁ t₀)) hproj₁ hproj₂ hf₁ hf₂ h0

end GeodesicUniqueness

end Geodesic
end Riemannian
end Geometry
end DifferentialGeometry

end
