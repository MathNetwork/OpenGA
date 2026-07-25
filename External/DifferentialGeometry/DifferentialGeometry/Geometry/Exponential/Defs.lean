import DifferentialGeometry.Geometry.Geodesic.Equation
import DifferentialGeometry.Geometry.Geodesic.Existence
import DifferentialGeometry.Geometry.Geodesic.MaximalInterval
import DifferentialGeometry.Geometry.Geodesic.Uniqueness
import Mathlib.Topology.Connected.Clopen



noncomputable section

open Bundle Manifold Set Filter Function
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Integral.Measure

def expMap (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) : M :=
  maximalGeodesic (I := I) g p v 1

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma expMap_def (g : SmoothRiemannianMetric I M) (p : M)
    (v : TangentSpace I p) :
    expMap (I := I) g p v = maximalGeodesic (I := I) g p v 1 := rfl

def expDomain (g : SmoothRiemannianMetric I M) (p : M) : Set (TangentSpace I p) :=
  {v | (1 : ℝ) ∈ maximalGeodesicInterval (I := I) g p v}

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma mem_expDomain_iff
    {g : SmoothRiemannianMetric I M} {p : M} {v : TangentSpace I p} :
    v ∈ expDomain (I := I) g p ↔
      (1 : ℝ) ∈ maximalGeodesicInterval (I := I) g p v := Iff.rfl

section StationaryWitness

variable [I.Boundaryless] [CompleteSpace E]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E] in
theorem maximalGeodesicWitness_zero_all_times
    (g : SmoothRiemannianMetric I M) (p : M) (t : ℝ) :
    MaximalGeodesicWitness (I := I) g p (0 : TangentSpace I p) t := by
  classical
  refine ⟨fun _ : ℝ => p, Set.univ, isOpen_univ, isPreconnected_univ,
    Set.mem_univ _, Set.mem_univ _, ?_⟩
  refine ⟨fun _ : ℝ => (⟨p, (0 : E)⟩ : TangentBundle I M), ?_, rfl, ?_⟩
  · intro _; rfl
  · have hvf_zero : geodesicVectorFieldChart (I := I) g p
        (⟨p, (0 : E)⟩ : TangentBundle I M) = 0 :=
      geodesicVectorFieldChart_zero_section (I := I) g p
    exact (isMIntegralCurve_const hvf_zero).isMIntegralCurveOn Set.univ

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E] in
theorem zero_mem_expDomain (g : SmoothRiemannianMetric I M) (p : M) :
    (0 : TangentSpace I p) ∈ expDomain (I := I) g p :=
  maximalGeodesicWitness_zero_all_times (I := I) g p 1

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E] in
theorem expDomain_nonempty (g : SmoothRiemannianMetric I M) (p : M) :
    (expDomain (I := I) g p).Nonempty :=
  ⟨0, zero_mem_expDomain (I := I) g p⟩

end StationaryWitness

section JunkValue

variable [I.Boundaryless] [CompleteSpace E]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E] in
theorem expMap_of_not_mem_expDomain
    {g : SmoothRiemannianMetric I M} {p : M} {v : TangentSpace I p}
    (hv : v ∉ expDomain (I := I) g p) :
    expMap (I := I) g p v = p := by
  unfold expMap
  exact maximalGeodesic_of_not_mem (I := I) hv

end JunkValue

section ExpMapZeroWitnessLevel

variable [I.Boundaryless] [CompleteSpace E]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E] in
theorem maximalGeodesicChosenCurve_zero_start_eq
    (g : SmoothRiemannianMetric I M) (p : M) :
    maximalGeodesicChosenCurve (I := I) g p (0 : TangentSpace I p)
      (maximalGeodesicWitness_zero_all_times (I := I) g p 1) 0 = p := by
  obtain ⟨_J, _hJ_open, _hJ_conn, _h0J, _h1J, hγ⟩ :=
    maximalGeodesicChosenCurve_spec (I := I) g p (0 : TangentSpace I p)
      (maximalGeodesicWitness_zero_all_times (I := I) g p 1)
  exact hγ.start_eq

end ExpMapZeroWitnessLevel

section ZeroVelocityPropagation

variable [I.Boundaryless] [CompleteSpace E]
  [T2Space (TangentBundle I M)]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)] in
private lemma isMIntegralCurve_const_zero_section
    (g : SmoothRiemannianMetric I M) (p : M) :
    IsMIntegralCurve (fun _ : ℝ => (⟨p, (0 : E)⟩ : TangentBundle I M))
      (geodesicVectorFieldChart (I := I) g p) :=
  isMIntegralCurve_const (geodesicVectorFieldChart_zero_section (I := I) g p)

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem isMIntegralCurveOn_zero_section_eq_const
    (g : SmoothRiemannianMetric I M) (p : M)
    {f : ℝ → TangentBundle I M} {J : Set ℝ}
    (hJ_open : IsOpen J) (hJ_conn : IsPreconnected J) (h0J : (0 : ℝ) ∈ J)
    (hf : IsMIntegralCurveOn f (geodesicVectorFieldChart (I := I) g p) J)
    (hf0 : f 0 = (⟨p, (0 : E)⟩ : TangentBundle I M)) :
    ∀ t ∈ J, f t = (⟨p, (0 : E)⟩ : TangentBundle I M) := by
  classical
  set c : ℝ → TangentBundle I M :=
    fun _ : ℝ => (⟨p, (0 : E)⟩ : TangentBundle I M) with hc_def
  have hc_int : IsMIntegralCurve c (geodesicVectorFieldChart (I := I) g p) :=
    isMIntegralCurve_const_zero_section (I := I) g p
  haveI : PreconnectedSpace (↥J) :=
    isPreconnected_iff_preconnectedSpace.mp hJ_conn
  set Tsub : Set (↥J) := {t : ↥J | f (t : ℝ) = c (t : ℝ)} with hTsub_def
  suffices hTsub_univ : Tsub = Set.univ by
    intro t ht
    have ht_sub : (⟨t, ht⟩ : ↥J) ∈ Tsub := by
      have hu : (⟨t, ht⟩ : ↥J) ∈ (Set.univ : Set ↥J) := Set.mem_univ _
      rw [← hTsub_univ] at hu
      exact hu
    have hft : f t = c t := ht_sub
    simpa [hc_def] using hft
  have h0_mem : (⟨0, h0J⟩ : ↥J) ∈ Tsub := by
    change f 0 = c 0
    rw [hf0, hc_def]
  have hf_cont : ContinuousOn f J := hf.continuousOn
  have hc_cont : Continuous c := continuous_const
  have hf_sub_cont : Continuous (fun t : ↥J => f (t : ℝ)) := by
    refine continuousOn_iff_continuous_restrict.mp ?_
    exact hf_cont
  have hc_sub_cont : Continuous (fun t : ↥J => c (t : ℝ)) :=
    hc_cont.comp continuous_subtype_val
  haveI : T2Space (TangentBundle I M) := inferInstance
  have hTsub_closed : IsClosed Tsub := by
    have hdiag : IsClosed {p : TangentBundle I M × TangentBundle I M | p.1 = p.2} :=
      isClosed_diagonal
    have hpair_cont : Continuous
        (fun t : ↥J => (f (t : ℝ), c (t : ℝ))) :=
      hf_sub_cont.prodMk hc_sub_cont
    have : Tsub = (fun t : ↥J => (f (t : ℝ), c (t : ℝ))) ⁻¹'
        {p : TangentBundle I M × TangentBundle I M | p.1 = p.2} := by
      ext t; rfl
    rw [this]
    exact hdiag.preimage hpair_cont
  have hTsub_open : IsOpen Tsub := by
    rw [isOpen_iff_mem_nhds]
    intro t₀ ht₀
    have hft₀ : f (t₀ : ℝ) = (⟨p, (0 : E)⟩ : TangentBundle I M) := ht₀
    have hp_src : (f (t₀ : ℝ)).proj ∈ (chartAt H p).source := by
      rw [hft₀]
      exact mem_chart_source H p
    have hf_at : IsMIntegralCurveAt f (geodesicVectorFieldChart (I := I) g p)
        (t₀ : ℝ) :=
      hf.isMIntegralCurveAt (hJ_open.mem_nhds t₀.2)
    have hc_at : IsMIntegralCurveAt c (geodesicVectorFieldChart (I := I) g p)
        (t₀ : ℝ) := hc_int.isMIntegralCurveAt _
    have hfc_eq : f (t₀ : ℝ) = c (t₀ : ℝ) := hft₀
    have hf_eq_c : f =ᶠ[𝓝 (t₀ : ℝ)] c :=
      isMIntegralCurveAt_geodesicVectorFieldChart_eventuallyEq
        (I := I) (g := g) (α := p) (t₀ := (t₀ : ℝ))
        (f₁ := f) (f₂ := c) hp_src hf_at hc_at hfc_eq
    rcases Filter.eventually_iff_exists_mem.mp hf_eq_c with ⟨U, hU_nhds, hU_eq⟩
    rcases mem_nhds_iff.mp hU_nhds with ⟨V, hVU, hV_open, hV_mem⟩
    refine Filter.mem_of_superset (hV_open.preimage continuous_subtype_val
      |>.mem_nhds hV_mem) ?_
    intro s hs
    change f (s : ℝ) = c (s : ℝ)
    exact hU_eq _ (hVU hs)
  have hTsub_clopen : IsClopen Tsub := ⟨hTsub_closed, hTsub_open⟩
  exact hTsub_clopen.eq_univ ⟨_, h0_mem⟩

end ZeroVelocityPropagation

section ExpMapZero

variable [I.Boundaryless] [CompleteSpace E]
  [T2Space (TangentBundle I M)]

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem maximalGeodesicWitness_zero_curve_eq_p
    {g : SmoothRiemannianMetric I M} {p : M}
    {γ : ℝ → M} {J : Set ℝ}
    (hJ_open : IsOpen J) (hJ_conn : IsPreconnected J) (h0J : (0 : ℝ) ∈ J)
    (hγ : IsGeodesicOnWithInitial (I := I) g γ J p (0 : TangentSpace I p)) :
    ∀ s ∈ J, γ s = p := by
  obtain ⟨f, hproj, hf0, hf_int⟩ := hγ
  intro s hs
  have hf_eq : f s = (⟨p, (0 : E)⟩ : TangentBundle I M) :=
    isMIntegralCurveOn_zero_section_eq_const (I := I) g p
      hJ_open hJ_conn h0J hf_int hf0 s hs
  have := hproj s
  rw [hf_eq] at this
  exact this.symm

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem expMap_zero
    (g : SmoothRiemannianMetric I M) (p : M) :
    expMap (I := I) g p (0 : TangentSpace I p) = p := by
  unfold expMap
  have h1 : (1 : ℝ) ∈ maximalGeodesicInterval (I := I) g p
      (0 : TangentSpace I p) :=
    maximalGeodesicWitness_zero_all_times (I := I) g p 1
  rw [maximalGeodesic_of_mem (I := I) (g := g) (p := p)
    (v := (0 : TangentSpace I p)) h1]
  obtain ⟨J, hJ_open, hJ_conn, h0J, h1J, hγ⟩ :=
    maximalGeodesicChosenCurve_spec (I := I) g p (0 : TangentSpace I p) h1
  exact maximalGeodesicWitness_zero_curve_eq_p (I := I)
    hJ_open hJ_conn h0J hγ 1 h1J

end ExpMapZero

end Exponential
end Riemannian
end Geometry
end DifferentialGeometry

end
