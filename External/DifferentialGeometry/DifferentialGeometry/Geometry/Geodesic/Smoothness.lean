import DifferentialGeometry.Geometry.Geodesic.Equation
import DifferentialGeometry.Geometry.Geodesic.Existence
import DifferentialGeometry.Geometry.Geodesic.Uniqueness
import Mathlib.Analysis.ODE.PicardLindelof



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

section LiftContinuity

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma IsMIntegralCurveAt.continuousAt_lift
    {v : (p : TangentBundle I M) → TangentSpace I.tangent p} {t₀ : ℝ}
    {f : ℝ → TangentBundle I M}
    (hf : IsMIntegralCurveAt f v t₀) :
    ContinuousAt f t₀ :=
  hf.continuousAt

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma IsMIntegralCurve.continuous_lift
    {v : (p : TangentBundle I M) → TangentSpace I.tangent p}
    {f : ℝ → TangentBundle I M}
    (hf : IsMIntegralCurve f v) :
    Continuous f :=
  hf.continuous

end LiftContinuity

section BaseContinuity

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma continuous_tangentBundle_proj :
    Continuous (Bundle.TotalSpace.proj : TangentBundle I M → M) :=
  FiberBundle.continuous_proj E (TangentSpace I)

omit [NeZero (Module.finrank ℝ E)] in
theorem IsGeodesicAt.continuousAt
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M} {t₀ : ℝ}
    (hγ : IsGeodesicAt (I := I) g γ t₀) :
    ContinuousAt γ t₀ := by
  obtain ⟨α, f, hproj, _hα_src, hf⟩ := hγ
  have hf_cont : ContinuousAt f t₀ := hf.continuousAt
  have hπ_cont : ContinuousAt
      (Bundle.TotalSpace.proj : TangentBundle I M → M) (f t₀) :=
    continuous_tangentBundle_proj.continuousAt
  have hcomp : ContinuousAt (fun t => (f t).proj) t₀ := hπ_cont.comp hf_cont
  have heq : (fun t => (f t).proj) = γ := funext hproj
  rw [heq] at hcomp
  exact hcomp

end BaseContinuity

section ChartPushedDerivative

variable [I.Boundaryless]

def chartPushLift (f : ℝ → TangentBundle I M) (t₀ : ℝ) :
    ℝ → E × E := fun t => extChartAt I.tangent (f t₀) (f t)

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
@[simp] lemma chartPushLift_apply (f : ℝ → TangentBundle I M) (t₀ t : ℝ) :
    chartPushLift (I := I) f t₀ t = extChartAt I.tangent (f t₀) (f t) := rfl

def chartPushVF (g : SmoothRiemannianMetric I M) (α : M)
    (f : ℝ → TangentBundle I M) (t₀ t : ℝ) : E × E :=
  tangentCoordChange I.tangent (f t) (f t₀) (f t)
    (geodesicVectorFieldChart (I := I) g α (f t))

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
@[simp] lemma chartPushVF_apply
    (g : SmoothRiemannianMetric I M) (α : M)
    (f : ℝ → TangentBundle I M) (t₀ t : ℝ) :
    chartPushVF (I := I) g α f t₀ t =
      tangentCoordChange I.tangent (f t) (f t₀) (f t)
        (geodesicVectorFieldChart (I := I) g α (f t)) := rfl

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem chartPushLift_eventually_hasDerivAt
    {g : SmoothRiemannianMetric I M} {α : M} {t₀ : ℝ}
    {f : ℝ → TangentBundle I M}
    (hf : IsMIntegralCurveAt f (geodesicVectorFieldChart (I := I) g α) t₀) :
    ∀ᶠ t in 𝓝 t₀, HasDerivAt (chartPushLift (I := I) f t₀)
      (chartPushVF (I := I) g α f t₀ t) t := by
  have h := hf.eventually_hasDerivAt
  filter_upwards [h] with t ht
  exact ht

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma chartPushLift_eventually_differentiableAt
    {g : SmoothRiemannianMetric I M} {α : M} {t₀ : ℝ}
    {f : ℝ → TangentBundle I M}
    (hf : IsMIntegralCurveAt f (geodesicVectorFieldChart (I := I) g α) t₀) :
    ∀ᶠ t in 𝓝 t₀, DifferentiableAt ℝ (chartPushLift (I := I) f t₀) t := by
  filter_upwards [chartPushLift_eventually_hasDerivAt (I := I)
    (g := g) (α := α) (t₀ := t₀) hf] with t ht
  exact ht.differentiableAt

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma chartPushLift_continuousAt
    {f : ℝ → TangentBundle I M} {t₀ : ℝ}
    (hf_cont : ContinuousAt f t₀) :
    ContinuousAt (chartPushLift (I := I) f t₀) t₀ := by
  have hchart_cont : ContinuousAt (extChartAt I.tangent (f t₀)) (f t₀) :=
    continuousAt_extChartAt (I := I.tangent) (f t₀)
  exact hchart_cont.comp hf_cont

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
@[simp] lemma chartPushLift_self
    (f : ℝ → TangentBundle I M) (t₀ : ℝ) :
    chartPushLift (I := I) f t₀ t₀ = extChartAt I.tangent (f t₀) (f t₀) := rfl

end ChartPushedDerivative

section IsGeodesicAtChartPush

variable [I.Boundaryless] [CompleteSpace E]

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem IsGeodesicAt.exists_chartPushLift_hasDerivAt
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M} {t₀ : ℝ}
    (hγ : IsGeodesicAt (I := I) g γ t₀) :
    ∃ (α : M) (f : ℝ → TangentBundle I M),
      (∀ t, (f t).proj = γ t) ∧
      IsMIntegralCurveAt f (geodesicVectorFieldChart (I := I) g α) t₀ ∧
      ∀ᶠ t in 𝓝 t₀, HasDerivAt (chartPushLift (I := I) f t₀)
        (chartPushVF (I := I) g α f t₀ t) t := by
  obtain ⟨α, f, hproj, _hα_src, hf⟩ := hγ
  exact ⟨α, f, hproj, hf,
    chartPushLift_eventually_hasDerivAt (I := I) (g := g) (α := α)
      (t₀ := t₀) (f := f) hf⟩

end IsGeodesicAtChartPush

end Geodesic
end Riemannian
end Geometry
end DifferentialGeometry

end
