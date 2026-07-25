import DifferentialGeometry.Geometry.Comparison.NormalCoordinates
import Mathlib.Data.ENNReal.Real



noncomputable section

open Set Function Filter Metric Bundle Manifold
open scoped Topology Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Integral.Measure

section InjectivityRadius

variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

def injRadiusSet (g : SmoothRiemannianMetric I M) (p : M) : Set ℝ≥0∞ :=
  { r : ℝ≥0∞ |
    InjOn (fun v : E => (expMap (I := I) g p (show TangentSpace I p from v) : M))
      (Metric.eball (0 : E) r) }

def injRadius (g : SmoothRiemannianMetric I M) (p : M) : ℝ≥0∞ :=
  sSup (injRadiusSet (I := I) g p)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E]
  [T2Space (TangentBundle I M)] in
lemma mem_injRadiusSet_iff (g : SmoothRiemannianMetric I M) (p : M)
    {r : ℝ≥0∞} :
    r ∈ injRadiusSet (I := I) g p ↔
      InjOn (fun v : E => (expMap (I := I) g p (show TangentSpace I p from v) : M))
        (Metric.eball (0 : E) r) := Iff.rfl

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E]
  [T2Space (TangentBundle I M)] in
lemma injRadiusSet_downward_closed (g : SmoothRiemannianMetric I M) (p : M)
    {r r' : ℝ≥0∞} (h : r' ≤ r) (hr : r ∈ injRadiusSet (I := I) g p) :
    r' ∈ injRadiusSet (I := I) g p := by
  refine InjOn.mono ?_ hr
  exact Metric.eball_subset_eball h

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E]
  [T2Space (TangentBundle I M)] in
lemma zero_mem_injRadiusSet (g : SmoothRiemannianMetric I M) (p : M) :
    (0 : ℝ≥0∞) ∈ injRadiusSet (I := I) g p := by
  classical
  change InjOn _ (Metric.eball (0 : E) (0 : ℝ≥0∞))
  rw [Metric.eball_zero]
  exact Set.injOn_empty _

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E]
  [T2Space (TangentBundle I M)] in
lemma injRadiusSet_nonempty (g : SmoothRiemannianMetric I M) (p : M) :
    (injRadiusSet (I := I) g p).Nonempty :=
  ⟨0, zero_mem_injRadiusSet (I := I) g p⟩

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E]
  [T2Space (TangentBundle I M)] in
lemma le_injRadius_of_mem (g : SmoothRiemannianMetric I M) (p : M)
    {r : ℝ≥0∞} (hr : r ∈ injRadiusSet (I := I) g p) :
    r ≤ injRadius (I := I) g p :=
  le_sSup hr

omit [NeZero (Module.finrank ℝ E)] in
lemma exists_metric_ball_subset_expMapDiffeo_source
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ r₀ : ℝ, 0 < r₀ ∧
      Metric.ball (0 : E) r₀ ⊆ (expMapDiffeo (I := I) g p).source := by
  classical
  have h_open : IsOpen (expMapDiffeo (I := I) g p).source :=
    (expMapDiffeo (I := I) g p).open_source
  have h_mem : (0 : E) ∈ (expMapDiffeo (I := I) g p).source :=
    zero_mem_expMapDiffeo_source (I := I) g p
  exact Metric.isOpen_iff.mp h_open (0 : E) h_mem

omit [NeZero (Module.finrank ℝ E)] in
lemma injOn_expMap_on_expMapDiffeo_source
    (g : SmoothRiemannianMetric I M) (p : M) :
    InjOn (fun v : E => (expMap (I := I) g p (show TangentSpace I p from v) : M))
      (expMapDiffeo (I := I) g p).source := by
  classical
  have h_inj_diffeo : InjOn (expMapDiffeo (I := I) g p)
      (expMapDiffeo (I := I) g p).source :=
    (expMapDiffeo (I := I) g p).toPartialEquiv.injOn
  intro v hv w hw hvw
  apply h_inj_diffeo hv hw
  rw [expMapDiffeo_apply_eq (I := I) g p hv,
      expMapDiffeo_apply_eq (I := I) g p hw]
  exact hvw

omit [NeZero (Module.finrank ℝ E)] in
lemma exists_pos_injOn_metric_ball
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ r₀ : ℝ, 0 < r₀ ∧
      InjOn (fun v : E => (expMap (I := I) g p (show TangentSpace I p from v) : M))
        (Metric.ball (0 : E) r₀) := by
  classical
  obtain ⟨r₀, hr₀_pos, hr₀_sub⟩ :=
    exists_metric_ball_subset_expMapDiffeo_source (I := I) g p
  refine ⟨r₀, hr₀_pos, ?_⟩
  exact (injOn_expMap_on_expMapDiffeo_source (I := I) g p).mono hr₀_sub

omit [NeZero (Module.finrank ℝ E)] in
lemma exists_pos_mem_injRadiusSet (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ r : ℝ≥0∞, 0 < r ∧ r ∈ injRadiusSet (I := I) g p := by
  classical
  obtain ⟨r₀, hr₀_pos, hr₀_inj⟩ :=
    exists_pos_injOn_metric_ball (I := I) g p
  refine ⟨ENNReal.ofReal r₀, ?_, ?_⟩
  · exact ENNReal.ofReal_pos.mpr hr₀_pos
  · change InjOn _ (Metric.eball (0 : E) (ENNReal.ofReal r₀))
    rw [Metric.eball_ofReal]
    exact hr₀_inj

omit [NeZero (Module.finrank ℝ E)] in
theorem injRadius_pos (g : SmoothRiemannianMetric I M) (p : M) :
    0 < injRadius (I := I) g p := by
  classical
  obtain ⟨r, hr_pos, hr_mem⟩ := exists_pos_mem_injRadiusSet (I := I) g p
  exact lt_of_lt_of_le hr_pos (le_injRadius_of_mem (I := I) g p hr_mem)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E]
  [T2Space (TangentBundle I M)] in
@[simp] lemma injRadius_eq_sSup (g : SmoothRiemannianMetric I M) (p : M) :
    injRadius (I := I) g p = sSup (injRadiusSet (I := I) g p) := rfl

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E]
  [T2Space (TangentBundle I M)] in
theorem injOn_expMap_eball_of_lt_injRadius
    (g : SmoothRiemannianMetric I M) (p : M) {r : ℝ≥0∞}
    (hr : r < injRadius (I := I) g p) :
    InjOn (fun v : E => (expMap (I := I) g p (show TangentSpace I p from v) : M))
      (Metric.eball (0 : E) r) := by
  classical
  rcases lt_sSup_iff.mp hr with ⟨r', hr'_mem, hr_lt_r'⟩
  have hr_le_r' : r ≤ r' := le_of_lt hr_lt_r'
  exact (mem_injRadiusSet_iff (I := I) g p).mp hr'_mem |>.mono
    (Metric.eball_subset_eball hr_le_r')

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E]
  [T2Space (TangentBundle I M)] in
theorem injOn_expMap_ball_of_ofReal_lt_injRadius
    (g : SmoothRiemannianMetric I M) (p : M) {r₀ : ℝ}
    (hr : ENNReal.ofReal r₀ < injRadius (I := I) g p) :
    InjOn (fun v : E => (expMap (I := I) g p (show TangentSpace I p from v) : M))
      (Metric.ball (0 : E) r₀) := by
  classical
  have h := injOn_expMap_eball_of_lt_injRadius (I := I) g p hr
  rwa [Metric.eball_ofReal] at h

omit [NeZero (Module.finrank ℝ E)] in
theorem injRadius_iInf_pos_of_compact_of_lowerSemicontinuous
    (g : SmoothRiemannianMetric I M) [CompactSpace M] [Nonempty M]
    (h_lsc : LowerSemicontinuous (fun p : M => injRadius (I := I) g p)) :
    0 < ⨅ p : M, injRadius (I := I) g p := by
  classical
  have h_lsc_on : LowerSemicontinuousOn (fun p : M => injRadius (I := I) g p)
      Set.univ := lowerSemicontinuousOn_univ_iff.mpr h_lsc
  obtain ⟨p₀, _hp₀_mem, h_min⟩ :=
    LowerSemicontinuousOn.exists_isMinOn (f := fun p : M => injRadius (I := I) g p)
      (s := (Set.univ : Set M)) Set.univ_nonempty isCompact_univ h_lsc_on
  have h_iInf_eq : ⨅ p : M, injRadius (I := I) g p = injRadius (I := I) g p₀ := by
    apply le_antisymm
    · exact iInf_le _ p₀
    · refine le_iInf fun p => ?_
      have := h_min (Set.mem_univ p)
      simpa using this
  rw [h_iInf_eq]
  exact injRadius_pos (I := I) g p₀

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_uniform_injectivity_radius_of_lowerSemicontinuous
    (g : SmoothRiemannianMetric I M) [CompactSpace M] [Nonempty M]
    (h_lsc : LowerSemicontinuous (fun p : M => injRadius (I := I) g p)) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ p : M,
      InjOn (fun v : E => (expMap (I := I) g p (show TangentSpace I p from v) : M))
        (Metric.ball (0 : E) r₀) := by
  classical
  have h_inf_pos := injRadius_iInf_pos_of_compact_of_lowerSemicontinuous
    (I := I) g h_lsc
  set R : ℝ≥0∞ := ⨅ p : M, injRadius (I := I) g p with hR_def
  by_cases hRtop : R = (⊤ : ℝ≥0∞)
  · refine ⟨1, one_pos, fun p => ?_⟩
    have h_le_inf : R ≤ injRadius (I := I) g p := by
      rw [hR_def]; exact iInf_le _ p
    have h_lt : ENNReal.ofReal 1 < injRadius (I := I) g p := by
      rw [hRtop] at h_le_inf
      have : ENNReal.ofReal 1 < (⊤ : ℝ≥0∞) := ENNReal.ofReal_lt_top
      exact lt_of_lt_of_le this h_le_inf
    exact injOn_expMap_ball_of_ofReal_lt_injRadius (I := I) g p h_lt
  · have hR_ne_top : R ≠ (⊤ : ℝ≥0∞) := hRtop
    have hR_pos : 0 < R := h_inf_pos
    have hR_toReal_pos : 0 < R.toReal := by
      rw [ENNReal.toReal_pos_iff]
      exact ⟨hR_pos, lt_top_iff_ne_top.mpr hR_ne_top⟩
    refine ⟨R.toReal / 2, by positivity, fun p => ?_⟩
    have h_le_inf : R ≤ injRadius (I := I) g p := by
      rw [hR_def]; exact iInf_le _ p
    have h_ofReal_lt_R : ENNReal.ofReal (R.toReal / 2) < R := by
      have hhalf_lt : R.toReal / 2 < R.toReal := by linarith
      calc ENNReal.ofReal (R.toReal / 2)
          < ENNReal.ofReal R.toReal := by
            exact (ENNReal.ofReal_lt_ofReal_iff hR_toReal_pos).mpr hhalf_lt
        _ = R := ENNReal.ofReal_toReal hR_ne_top
    have h_lt : ENNReal.ofReal (R.toReal / 2) < injRadius (I := I) g p :=
      lt_of_lt_of_le h_ofReal_lt_R h_le_inf
    exact injOn_expMap_ball_of_ofReal_lt_injRadius (I := I) g p h_lt

end InjectivityRadius

end Riemannian
end Geometry
end DifferentialGeometry

end
