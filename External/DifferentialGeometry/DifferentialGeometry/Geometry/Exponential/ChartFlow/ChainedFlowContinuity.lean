import DifferentialGeometry.Geometry.Exponential.Defs
import DifferentialGeometry.Geometry.Exponential.Smoothness.ZeroSectionConstancy
import DifferentialGeometry.Geometry.Exponential.LocalDiffeomorphism
import DifferentialGeometry.Geometry.Exponential.ChartFlow.PreconnectedPropagation
import DifferentialGeometry.Geometry.Geodesic.Equation
import DifferentialGeometry.Geometry.Geodesic.MaximalInterval
import DifferentialGeometry.Geometry.Geodesic.SmoothFlow
import DifferentialGeometry.Analysis.Integration.Measure.ChartDensity
import DifferentialGeometry.Analysis.ODE.Flow.C1Regularity.ContDiffOnOne
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Compactness.Compact



noncomputable section

open Set Filter Topology Metric
open scoped Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
  [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space (TangentBundle I M)]

open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Integral.Measure

omit [NeZero (Module.finrank ℝ E)] in
theorem maximalGeodesic_continuousAt_zero
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) :
    ContinuousAt (maximalGeodesic (I := I) g p v) 0 := by
  classical
  obtain ⟨g_v, hg0, hg_int⟩ :=
    exists_isMIntegralCurveAt_geodesicVectorFieldChart (I := I) (g := g)
      (p := p) (v := v)
  have hlift_cont : ContinuousAt g_v 0 := hg_int.continuousAt
  have hπ_cont : Continuous
      (Bundle.TotalSpace.proj : TangentBundle I M → M) :=
    FiberBundle.continuous_proj E (TangentSpace I)
  have hproj_cont : ContinuousAt (fun t => (g_v t).proj) 0 :=
    hπ_cont.continuousAt.comp hlift_cont
  obtain ⟨ε, hε, h_eq⟩ :=
    picardLift_proj_eq_maximalGeodesic_on_ball (I := I) (g := g) (p := p)
      (v := v) hg0 hg_int
  have h_eventually :
      maximalGeodesic (I := I) g p v =ᶠ[𝓝 (0 : ℝ)] fun t => (g_v t).proj := by
    have h_ball : Metric.ball (0 : ℝ) ε ∈ 𝓝 (0 : ℝ) :=
      Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hε)
    filter_upwards [h_ball] with t ht using h_eq t ht
  exact hproj_cont.congr h_eventually.symm
omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] [T2Space (TangentBundle I M)] in
lemma IsGeodesicOnWithInitial.continuousOn_base
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M} {J : Set ℝ}
    {p : M} {v : TangentSpace I p}
    (hγ : IsGeodesicOnWithInitial (I := I) g γ J p v) :
    ContinuousOn γ J := by
  obtain ⟨f, hproj, _hf0, hf⟩ := hγ
  have hf_cont : ContinuousOn f J := hf.continuousOn
  have hπ : Continuous (Bundle.TotalSpace.proj : TangentBundle I M → M) :=
    FiberBundle.continuous_proj E (TangentSpace I)
  have hcomp : ContinuousOn (fun t => (f t).proj) J :=
    hπ.comp_continuousOn hf_cont
  exact hcomp.congr (fun t _ht => (hproj t).symm)

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
lemma maximalGeodesic_eqOn_lift_of_footInSource
    {g : SmoothRiemannianMetric I M} {p : M} {v : E}
    {f : ℝ → TangentBundle I M} {J : Set ℝ}
    (hJ_open : IsOpen J) (hJ_conn : IsPreconnected J) (h0J : (0 : ℝ) ∈ J)
    (hf0 : f 0 = (⟨p, v⟩ : TangentBundle I M))
    (hf_on : IsMIntegralCurveOn f (geodesicVectorFieldChart (I := I) g p) J)
    (hsrc : ∀ s ∈ J, (f s).proj ∈ (chartAt H p).source) :
    Set.EqOn (maximalGeodesic (I := I) g p v) (fun t => (f t).proj) J := by
  classical
  intro t ht
  have hwit : MaximalGeodesicWitness (I := I) g p v t :=
    ⟨projectCurve (I := I) f, J, hJ_open, hJ_conn, h0J, ht,
      ⟨f, fun s => rfl, hf0, hf_on⟩⟩
  have htmem : t ∈ maximalGeodesicInterval (I := I) g p v := hwit
  have hval : maximalGeodesic (I := I) g p v t = (f t).proj := by
    rw [maximalGeodesic_of_mem (I := I) htmem]
    obtain ⟨J', hJ'_open, hJ'_conn, h0J', htJ', f', hproj', hf'0, hf'_on⟩ :=
      maximalGeodesicChosenCurve_spec (I := I) g p v htmem
    set K : Set ℝ := J ∩ J' with hK_def
    have hK_open : IsOpen K := hJ_open.inter hJ'_open
    have hK_conn : IsPreconnected K := by
      have hJ_ord : Set.OrdConnected J := hJ_conn.ordConnected
      have hJ'_ord : Set.OrdConnected J' := hJ'_conn.ordConnected
      exact (hJ_ord.inter hJ'_ord).isPreconnected
    have h0_K : (0 : ℝ) ∈ K := ⟨h0J, h0J'⟩
    have ht_K : t ∈ K := ⟨ht, htJ'⟩
    have hf_on_K : IsMIntegralCurveOn f
        (geodesicVectorFieldChart (I := I) g p) K :=
      hf_on.mono Set.inter_subset_left
    have hf'_on_K : IsMIntegralCurveOn f'
        (geodesicVectorFieldChart (I := I) g p) K :=
      hf'_on.mono Set.inter_subset_right
    have hf_src_K : ∀ s ∈ K, (f s).proj ∈ (chartAt H p).source :=
      fun s hs => hsrc s hs.1
    have heqOn := isMIntegralCurveOn_eq_of_isPreconnected (I := I) (g := g)
      (p := p) (f₁ := f) (f₂ := f') hK_open hK_conn h0_K hf_on_K hf'_on_K
      hf_src_K (by rw [hf0, hf'0])
    have ht_eq : f t = f' t := heqOn ht_K
    rw [ht_eq]
    exact (hproj' t).symm
  exact hval

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
lemma maximalGeodesic_continuousOn_of_footInSource
    {g : SmoothRiemannianMetric I M} {p : M} {v : E}
    {f : ℝ → TangentBundle I M} {J : Set ℝ}
    (hJ_open : IsOpen J) (hJ_conn : IsPreconnected J) (h0J : (0 : ℝ) ∈ J)
    (hf0 : f 0 = (⟨p, v⟩ : TangentBundle I M))
    (hf_on : IsMIntegralCurveOn f (geodesicVectorFieldChart (I := I) g p) J)
    (hsrc : ∀ s ∈ J, (f s).proj ∈ (chartAt H p).source) :
    ContinuousOn (maximalGeodesic (I := I) g p v) J := by
  have heq := maximalGeodesic_eqOn_lift_of_footInSource (I := I)
    hJ_open hJ_conn h0J hf0 hf_on hsrc
  have hf_cont : ContinuousOn f J := hf_on.continuousOn
  have hπ : Continuous (Bundle.TotalSpace.proj : TangentBundle I M → M) :=
    FiberBundle.continuous_proj E (TangentSpace I)
  have hcomp : ContinuousOn (fun t => (f t).proj) J :=
    hπ.comp_continuousOn hf_cont
  exact hcomp.congr heq


end Exponential
end Riemannian
end Geometry
end DifferentialGeometry
