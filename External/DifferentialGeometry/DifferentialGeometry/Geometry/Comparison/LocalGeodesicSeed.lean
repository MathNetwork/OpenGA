import DifferentialGeometry.Geometry.Exponential.GaussLemma
import DifferentialGeometry.Geometry.Geodesic.Equation
import DifferentialGeometry.Geometry.Geodesic.Existence
import DifferentialGeometry.Geometry.Geodesic.MaximalInterval
import DifferentialGeometry.Geometry.Geodesic.Uniqueness
import DifferentialGeometry.Geometry.Geodesic.Homogeneity
import DifferentialGeometry.Geometry.Geodesic.CrossVFReduction
import DifferentialGeometry.Geometry.Geodesic.ProjDerivative
import DifferentialGeometry.Geometry.Exponential.Defs
import DifferentialGeometry.Geometry.Exponential.Smoothness.ZeroSectionConstancy
import DifferentialGeometry.Geometry.Connection.ParallelTransport.AlongCurve
import DifferentialGeometry.Geometry.Connection.ParallelTransport.MFDerivAlongCurve
import DifferentialGeometry.Analysis.Integration.Measure.ChartDensity
import DifferentialGeometry.Geometry.Connection.LeviCivita.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.EMetricSpace.Lipschitz



noncomputable section

open Set Function Filter Bundle Manifold
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace HopfRinow

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.MFDerivAlongCurve
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]

omit [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)] [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M] in
theorem exists_isGeodesicOn_Ioo_at
    (g : SmoothRiemannianMetric I M) (y : M) (w : TangentSpace I y) :
    ∃ (η : ℝ → M) (δ : ℝ), 0 < δ ∧ η 0 = y ∧
      IsGeodesicOn (I := I) g η (Set.Ioo (-δ) δ) := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨η, f, hf0, hηproj, hη0, hf_int, _hgeo⟩ := exists_geodesic_with_initial_velocity_at (I := I) g y w
  subst hηproj
  have hηt : ∀ t, projectCurve (I := I) f t = (f t).proj := fun _ => rfl
  have hf0proj : (f 0).proj = y := by rw [hf0]
  have hηcont : ContinuousAt (projectCurve (I := I) f) 0 := by
    have hc : Continuous (fun p : TangentBundle I M => p.proj) :=
      FiberBundle.continuous_proj E (TangentSpace I)
    exact hc.continuousAt.comp hf_int.continuousAt
  obtain ⟨ε, hε, hf_on⟩ := isMIntegralCurveAt_iff'.mp hf_int
  have hsrc_nhds : {t : ℝ | (f t).proj ∈ (chartAt H y).source} ∈ 𝓝 (0 : ℝ) := by
    have hopen : IsOpen ((chartAt H y).source) := (chartAt H y).open_source
    have hmem : (f 0).proj ∈ (chartAt H y).source := by
      rw [hf0proj]; exact mem_chart_source H y
    exact hηcont.preimage_mem_nhds (hopen.mem_nhds hmem)
  have hball_nhds : Metric.ball (0 : ℝ) ε ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds _ hε
  obtain ⟨δ, hδ, hδ_sub⟩ :=
    Metric.mem_nhds_iff.mp (Filter.inter_mem hball_nhds hsrc_nhds)
  refine ⟨projectCurve (I := I) f, δ, hδ, hη0, ?_⟩
  intro t ht
  have htball : t ∈ Metric.ball (0 : ℝ) δ := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]; exact ⟨ht.1, ht.2⟩
  have ht_both := hδ_sub htball
  have ht_ballε : t ∈ Metric.ball (0 : ℝ) ε := ht_both.1
  have ht_src : (f t).proj ∈ (chartAt H y).source := ht_both.2
  have hf_at_t : IsMIntegralCurveAt f (geodesicVectorFieldChart (I := I) g y) t :=
    hf_on.isMIntegralCurveAt (Metric.isOpen_ball.mem_nhds ht_ballε)
  have hgeo_at : IsGeodesicAt (I := I) g (projectCurve (I := I) f) t :=
    ⟨y, f, hηt, ht_src, hf_at_t⟩
  exact hgeo_at.hasGeodesicEquationAt g

omit [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)] [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M] in
theorem exists_isGeodesicOn_Ioo_at_velocity
    (g : SmoothRiemannianMetric I M) (y : M) (w : TangentSpace I y) :
    ∃ (η : ℝ → M) (δ : ℝ), 0 < δ ∧ η 0 = y ∧ ContinuousAt η 0 ∧
      (mfderiv 𝓘(ℝ, ℝ) I η 0 (1 : ℝ) : E) = (w : E) ∧
      (∀ t ∈ Set.Ioo (-δ) δ, MDifferentiableAt 𝓘(ℝ, ℝ) I η t) ∧
      (∀ t ∈ Set.Ioo (-δ) δ, η t ∈ (chartAt H y).source) ∧
      IsGeodesicOn (I := I) g η (Set.Ioo (-δ) δ) := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨η, f, hf0, hηproj, hη0, hf_int, _hgeo⟩ := exists_geodesic_with_initial_velocity_at (I := I) g y w
  subst hηproj
  have hηt : ∀ t, projectCurve (I := I) f t = (f t).proj := fun _ => rfl
  have hf0proj : (f 0).proj = y := by rw [hf0]
  have hηcont : ContinuousAt (projectCurve (I := I) f) 0 := by
    have hc : Continuous (fun p : TangentBundle I M => p.proj) :=
      FiberBundle.continuous_proj E (TangentSpace I)
    exact hc.continuousAt.comp hf_int.continuousAt
  obtain ⟨ε, hε, hf_on⟩ := isMIntegralCurveAt_iff'.mp hf_int
  have hsrc_nhds : {t : ℝ | (f t).proj ∈ (chartAt H y).source} ∈ 𝓝 (0 : ℝ) := by
    have hopen : IsOpen ((chartAt H y).source) := (chartAt H y).open_source
    have hmem : (f 0).proj ∈ (chartAt H y).source := by
      rw [hf0proj]; exact mem_chart_source H y
    exact hηcont.preimage_mem_nhds (hopen.mem_nhds hmem)
  have hball_nhds : Metric.ball (0 : ℝ) ε ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds _ hε
  obtain ⟨δ, hδ, hδ_sub⟩ :=
    Metric.mem_nhds_iff.mp (Filter.inter_mem hball_nhds hsrc_nhds)
  have hf0_src : (f 0).proj ∈ (chartAt H y).source := by
    rw [hf0proj]; exact mem_chart_source H y
  have hmf : mfderiv 𝓘(ℝ, ℝ) I (fun t => (f t).proj) 0 (1 : ℝ) = (f 0).snd :=
    IsMIntegralCurveAt.mfderiv_proj_one (I := I) (g := g) (α := y) (t₀ := 0)
      hf_int hf0_src
  have hf0snd : ((f 0).snd : E) = (w : E) := by rw [hf0]
  have hf_at_t : ∀ t ∈ Set.Ioo (-δ) δ,
      IsMIntegralCurveAt f (geodesicVectorFieldChart (I := I) g y) t ∧
        (f t).proj ∈ (chartAt H y).source := by
    intro t ht
    have htball : t ∈ Metric.ball (0 : ℝ) δ := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]; exact ⟨ht.1, ht.2⟩
    have ht_both := hδ_sub htball
    exact ⟨hf_on.isMIntegralCurveAt (Metric.isOpen_ball.mem_nhds ht_both.1), ht_both.2⟩
  refine ⟨projectCurve (I := I) f, δ, hδ, hη0, hηcont, ?_, ?_, ?_, ?_⟩
  · rw [show (projectCurve (I := I) f) = (fun t => (f t).proj) from rfl, hmf, hf0snd]
  · intro t ht
    have hfd : MDifferentiableAt 𝓘(ℝ, ℝ) I.tangent f t :=
      (hf_at_t t ht).1.hasMFDerivAt.mdifferentiableAt
    have hpd : MDifferentiableAt I.tangent I
        (Bundle.TotalSpace.proj : TangentBundle I M → M) (f t) :=
      (Bundle.contMDiffAt_proj (E := (TangentSpace I : M → Type _)) (n := 1)).mdifferentiableAt
        (by norm_num)
    exact (hpd.comp t hfd)
  · intro t ht
    exact (hf_at_t t ht).2
  · intro t ht
    have hgeo_at : IsGeodesicAt (I := I) g (projectCurve (I := I) f) t :=
      ⟨y, f, hηt, (hf_at_t t ht).2, (hf_at_t t ht).1⟩
    exact hgeo_at.hasGeodesicEquationAt g

end HopfRinow
end Riemannian
end Geometry
end DifferentialGeometry
