import DifferentialGeometry.Analysis.Sobolev.Chart.ChartTransition.ChartPullbackSmooth


noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Chart

variable {E H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

def chartTransitionEuclidRestr (γ α : M) : EuclN → EuclN := by
  classical
  exact (chartOverlapEuclid (I := I) (M := M) γ α).piecewise
    (chartTransitionEuclid (I := I) (M := M) γ α)
    (fun _ : EuclN => 0)

omit [IsManifold I ∞ M] in
lemma chartTransitionEuclidRestr_eqOn_overlap (γ α : M) :
    Set.EqOn (chartTransitionEuclidRestr (I := I) (M := M) γ α)
      (chartTransitionEuclid (I := I) (M := M) γ α)
      (chartOverlapEuclid (I := I) (M := M) γ α) := by
  classical
  intro y hy
  change (chartOverlapEuclid (I := I) (M := M) γ α).piecewise
    (chartTransitionEuclid (I := I) (M := M) γ α) (fun _ : EuclN => 0) y = _
  rw [Set.piecewise_eq_of_mem _ _ _ hy]

omit [IsManifold I ∞ M] in
lemma chartTransitionEuclidRestr_ae_eq_restrict
    [I.Boundaryless] (γ α : M) :
    chartTransitionEuclidRestr (I := I) (M := M) γ α
      =ᵐ[(volume : Measure EuclN).restrict
          (chartOverlapEuclid (I := I) (M := M) γ α)]
      chartTransitionEuclid (I := I) (M := M) γ α := by
  have h_overlap_meas : MeasurableSet (chartOverlapEuclid (I := I) (M := M) γ α) :=
    (chartOverlapEuclid_isOpen (I := I) (M := M) γ α).measurableSet
  refine (ae_restrict_iff' h_overlap_meas).2 ?_
  exact Filter.Eventually.of_forall (fun y hy =>
    chartTransitionEuclidRestr_eqOn_overlap (I := I) (M := M) γ α hy)

lemma chartTransitionEuclidRestr_measurable
    [I.Boundaryless] (γ α : M) :
    Measurable (chartTransitionEuclidRestr (I := I) (M := M) γ α) := by
  classical
  have h_overlap_open : IsOpen (chartOverlapEuclid (I := I) (M := M) γ α) :=
    chartOverlapEuclid_isOpen (I := I) (M := M) γ α
  have h_cont_on : ContinuousOn (chartTransitionEuclid (I := I) (M := M) γ α)
      (chartOverlapEuclid (I := I) (M := M) γ α) :=
    (chartTransitionEuclid_contDiffOn_overlap (I := I) (M := M) γ α).continuousOn
  have h_const_on : ContinuousOn (fun _ : EuclN => (0 : EuclN))
      ((chartOverlapEuclid (I := I) (M := M) γ α)ᶜ) :=
    continuousOn_const
  exact ContinuousOn.measurable_piecewise h_cont_on h_const_on
    h_overlap_open.measurableSet

omit [IsManifold I ∞ M] in
lemma chartTransitionEuclid_preimage_inter_overlap
    [I.Boundaryless] (γ α : M) (s : Set EuclN) :
    chartTransitionEuclid (I := I) (M := M) γ α ⁻¹' s ∩
        chartOverlapEuclid (I := I) (M := M) γ α =
      chartTransitionEuclid (I := I) (M := M) α γ ''
        (s ∩ chartOverlapEuclid (I := I) (M := M) α γ) := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_image]
  constructor
  · rintro ⟨hxs, hxΩ⟩
    refine ⟨chartTransitionEuclid (I := I) (M := M) γ α x, ⟨hxs, ?_⟩, ?_⟩
    · exact chartTransitionEuclid_mapsTo_overlap (I := I) (M := M) γ α hxΩ
    · exact chartTransitionEuclid_left_inv (I := I) (M := M) γ α hxΩ
  · rintro ⟨y, ⟨hys, hyΩ⟩, hxy⟩
    refine ⟨?_, ?_⟩
    · have h_left : chartTransitionEuclid (I := I) (M := M) γ α
          (chartTransitionEuclid (I := I) (M := M) α γ y) = y :=
        chartTransitionEuclid_left_inv (I := I) (M := M) α γ hyΩ
      rw [← hxy, h_left]; exact hys
    · rw [← hxy]
      exact chartTransitionEuclid_mapsTo_overlap (I := I) (M := M) α γ hyΩ

lemma chartTransitionEuclid_preimage_overlap_null
    [I.Boundaryless] (γ α : M)
    {s : Set EuclN} (hs : (volume : Measure EuclN) s = 0) :
    (volume : Measure EuclN)
        (chartTransitionEuclid (I := I) (M := M) γ α ⁻¹' s ∩
          chartOverlapEuclid (I := I) (M := M) γ α) = 0 := by
  rw [chartTransitionEuclid_preimage_inter_overlap (I := I) (M := M) γ α s]
  have h_diffOn : DifferentiableOn ℝ
      (chartTransitionEuclid (I := I) (M := M) α γ)
      (chartOverlapEuclid (I := I) (M := M) α γ) :=
    (chartTransitionEuclid_contDiffOn_overlap (I := I) (M := M) α γ).differentiableOn
      (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)
  have h_diffOn_sub : DifferentiableOn ℝ
      (chartTransitionEuclid (I := I) (M := M) α γ)
      (s ∩ chartOverlapEuclid (I := I) (M := M) α γ) :=
    h_diffOn.mono Set.inter_subset_right
  have h_sub_null : (volume : Measure EuclN)
      (s ∩ chartOverlapEuclid (I := I) (M := M) α γ) = 0 :=
    measure_mono_null Set.inter_subset_left hs
  exact MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
    (volume) h_diffOn_sub h_sub_null

theorem chartTransitionEuclid_quasiMeasurePreserving_restrict
    [I.Boundaryless] (γ α : M) :
    MeasureTheory.Measure.QuasiMeasurePreserving
      (chartTransitionEuclidRestr (I := I) (M := M) γ α)
      ((volume : Measure EuclN).restrict
        (chartOverlapEuclid (I := I) (M := M) γ α))
      (volume : Measure EuclN) := by
  refine ⟨chartTransitionEuclidRestr_measurable (I := I) (M := M) γ α, ?_⟩
  refine MeasureTheory.Measure.AbsolutelyContinuous.mk ?_
  intro s hs_meas hs_zero
  have h_overlap_meas : MeasurableSet (chartOverlapEuclid (I := I) (M := M) γ α) :=
    (chartOverlapEuclid_isOpen (I := I) (M := M) γ α).measurableSet
  have h_pre_meas : MeasurableSet
      (chartTransitionEuclidRestr (I := I) (M := M) γ α ⁻¹' s) :=
    chartTransitionEuclidRestr_measurable (I := I) (M := M) γ α hs_meas
  rw [MeasureTheory.Measure.map_apply
        (chartTransitionEuclidRestr_measurable (I := I) (M := M) γ α) hs_meas,
      MeasureTheory.Measure.restrict_apply h_pre_meas]
  have h_inter_eq :
      chartTransitionEuclidRestr (I := I) (M := M) γ α ⁻¹' s ∩
          chartOverlapEuclid (I := I) (M := M) γ α =
        chartTransitionEuclid (I := I) (M := M) γ α ⁻¹' s ∩
          chartOverlapEuclid (I := I) (M := M) γ α := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_preimage, and_congr_left_iff]
    intro hy
    rw [chartTransitionEuclidRestr_eqOn_overlap (I := I) (M := M) γ α hy]
  rw [h_inter_eq]
  exact chartTransitionEuclid_preimage_overlap_null (I := I) (M := M) γ α hs_zero

theorem chartTransitionEuclidRestr_comp_ae_eq_restrict
    [I.Boundaryless] (γ α : M)
    {f h : EuclN → ℝ}
    (hfh : f =ᵐ[(volume : Measure EuclN).restrict
        (chartOverlapEuclid (I := I) (M := M) α γ)] h) :
    (fun y => f (chartTransitionEuclidRestr (I := I) (M := M) γ α y)) =ᵐ[
        (volume : Measure EuclN).restrict
          (chartOverlapEuclid (I := I) (M := M) γ α)]
      fun y => h (chartTransitionEuclidRestr (I := I) (M := M) γ α y) := by
  have h_qmp_into :
      MeasureTheory.Measure.QuasiMeasurePreserving
        (chartTransitionEuclidRestr (I := I) (M := M) γ α)
        ((volume : Measure EuclN).restrict
          (chartOverlapEuclid (I := I) (M := M) γ α))
        ((volume : Measure EuclN).restrict
          (chartOverlapEuclid (I := I) (M := M) α γ)) := by
    refine ⟨chartTransitionEuclidRestr_measurable (I := I) (M := M) γ α, ?_⟩
    refine MeasureTheory.Measure.AbsolutelyContinuous.mk ?_
    intro s hs_meas hs_zero
    have h_overlap_α_meas :
        MeasurableSet (chartOverlapEuclid (I := I) (M := M) α γ) :=
      (chartOverlapEuclid_isOpen (I := I) (M := M) α γ).measurableSet
    have h_pre_meas : MeasurableSet
        (chartTransitionEuclidRestr (I := I) (M := M) γ α ⁻¹' s) :=
      chartTransitionEuclidRestr_measurable (I := I) (M := M) γ α hs_meas
    rw [MeasureTheory.Measure.restrict_apply hs_meas] at hs_zero
    rw [MeasureTheory.Measure.map_apply
          (chartTransitionEuclidRestr_measurable (I := I) (M := M) γ α) hs_meas,
        MeasureTheory.Measure.restrict_apply h_pre_meas]
    have h_inter_eq :
        chartTransitionEuclidRestr (I := I) (M := M) γ α ⁻¹' s ∩
            chartOverlapEuclid (I := I) (M := M) γ α =
          chartTransitionEuclid (I := I) (M := M) γ α ⁻¹'
              (s ∩ chartOverlapEuclid (I := I) (M := M) α γ) ∩
            chartOverlapEuclid (I := I) (M := M) γ α := by
      ext y
      simp only [Set.mem_inter_iff, Set.mem_preimage]
      constructor
      · rintro ⟨hys, hyΩ⟩
        have hy_eq : chartTransitionEuclidRestr (I := I) (M := M) γ α y =
            chartTransitionEuclid (I := I) (M := M) γ α y :=
          chartTransitionEuclidRestr_eqOn_overlap (I := I) (M := M) γ α hyΩ
        refine ⟨⟨hy_eq ▸ hys, ?_⟩, hyΩ⟩
        exact chartTransitionEuclid_mapsTo_overlap (I := I) (M := M) γ α hyΩ
      · rintro ⟨⟨hys, _⟩, hyΩ⟩
        have hy_eq : chartTransitionEuclidRestr (I := I) (M := M) γ α y =
            chartTransitionEuclid (I := I) (M := M) γ α y :=
          chartTransitionEuclidRestr_eqOn_overlap (I := I) (M := M) γ α hyΩ
        exact ⟨hy_eq ▸ hys, hyΩ⟩
    rw [h_inter_eq]
    exact chartTransitionEuclid_preimage_overlap_null (I := I) (M := M) γ α hs_zero
  exact h_qmp_into.ae_eq hfh

theorem chartTransitionEuclid_comp_ae_eq_restrict
    [I.Boundaryless] (γ α : M)
    {f h : EuclN → ℝ}
    (hfh : f =ᵐ[(volume : Measure EuclN).restrict
        (chartOverlapEuclid (I := I) (M := M) α γ)] h) :
    (fun y => f (chartTransitionEuclid (I := I) (M := M) γ α y)) =ᵐ[
        (volume : Measure EuclN).restrict
          (chartOverlapEuclid (I := I) (M := M) γ α)]
      fun y => h (chartTransitionEuclid (I := I) (M := M) γ α y) := by
  have h_repr := chartTransitionEuclidRestr_ae_eq_restrict (I := I) (M := M) γ α
  have h_f_repr : (fun y => f (chartTransitionEuclid (I := I) (M := M) γ α y))
      =ᵐ[(volume : Measure EuclN).restrict
          (chartOverlapEuclid (I := I) (M := M) γ α)]
      fun y => f (chartTransitionEuclidRestr (I := I) (M := M) γ α y) := by
    filter_upwards [h_repr] with y hy
    rw [hy]
  have h_h_repr : (fun y => h (chartTransitionEuclidRestr (I := I) (M := M) γ α y))
      =ᵐ[(volume : Measure EuclN).restrict
          (chartOverlapEuclid (I := I) (M := M) γ α)]
      fun y => h (chartTransitionEuclid (I := I) (M := M) γ α y) := by
    filter_upwards [h_repr] with y hy
    rw [hy]
  exact (h_f_repr.trans
    (chartTransitionEuclidRestr_comp_ae_eq_restrict (I := I) (M := M) γ α hfh)).trans
    h_h_repr

end Chart
end Sobolev
end Analysis
end DifferentialGeometry
