import DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.Differentiated.DerivedDataConstructor
import DifferentialGeometry.Analysis.Elliptic.Regularity.ChartBilinear.UniformDiffQuotBoundFromDomain
import DifferentialGeometry.Analysis.Elliptic.Regularity.ChartHk.H2NonSmooth
import DifferentialGeometry.Analysis.Sobolev.Approximation.SmoothDensity

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace DerivedChartBilinearH2Interior

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearUniformDiffQuotBoundCanonical
open DifferentialGeometry.Analysis.Laplacian.ChartH2NonSmooth
open DifferentialGeometry.Analysis.Laplacian.DerivedChartBilinearH1ComplDataCanonical
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.Chart

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

private lemma thickening_mono_of_lt
    {α : Type*} [PseudoEMetricSpace α]
    {r r' : ℝ} (hr_lt : r < r') (K : Set α) :
    Metric.thickening r K ⊆ Metric.thickening r' K := by
  intro y hy
  refine Metric.mem_thickening_iff_infEDist_lt.mpr ?_
  have h := Metric.mem_thickening_iff_infEDist_lt.mp hy
  exact lt_of_lt_of_le h
    (ENNReal.ofReal_le_ofReal hr_lt.le)

private lemma self_subset_thickening_of_pos
    {α : Type*} [PseudoEMetricSpace α]
    {r : ℝ} (hr_pos : 0 < r) (K : Set α) :
    K ⊆ Metric.thickening r K :=
  Metric.self_subset_thickening hr_pos K


theorem derivedChartBilinear_memWkp_two_two_interior
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    (l : Fin (Module.finrank ℝ E))
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    ∃ Ω'' : Set EuclN,
      IsOpen Ω'' ∧
      IsCompact (closure Ω'') ∧
      closure Ω'' ⊆ chartTargetEuclid (I := I) (M := M) α ∧
      chartImagePOUTsupport (I := I) (M := M) α ⊆ Ω'' ∧
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 2 2
        ((derivedChartBilinearH1ComplDataUnconditional
          (I := I) (M := M) g α l hu_h).u_chart) Ω'' := by
  classical
  set D : ChartBilinearH1ComplData (I := I) (M := M) g α :=
    derivedChartBilinearH1ComplDataUnconditional (I := I) (M := M) g α l hu_h
    with hD_def
  set K_α : Set EuclN := chartImagePOUTsupport (I := I) (M := M) α with hK_α_def
  have hK_α_compact : IsCompact K_α :=
    chartImagePOUTsupport_isCompact (I := I) (M := M) α
  have hK_α_in_chart : K_α ⊆ chartTargetEuclid (I := I) (M := M) α :=
    chartImagePOUTsupport_subset_target (I := I) (M := M) α
  have h_chart_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α
  obtain ⟨R_α, hR_α_pos, hR_α_subset⟩ :=
    hK_α_compact.exists_cthickening_subset_open h_chart_open hK_α_in_chart
  set ε : ℝ := R_α / 16 with hε_def
  have hε_pos : 0 < ε := by positivity
  set R₀ : ℝ := ε with hR₀_def
  have hR₀_pos : 0 < R₀ := hε_pos
  set Ω'' : Set EuclN := Metric.thickening (2 * ε) K_α with hΩ''_def
  have hΩ''_open : IsOpen Ω'' := Metric.isOpen_thickening
  have h_two_ε_pos : 0 < 2 * ε := by positivity
  have hK_α_in_Ω'' : K_α ⊆ Ω'' :=
    self_subset_thickening_of_pos h_two_ε_pos K_α
  have h_closureΩ''_sub : closure Ω'' ⊆ Metric.cthickening (2 * ε) K_α := by
    refine closure_minimal (Metric.thickening_subset_cthickening _ _)
      Metric.isClosed_cthickening
  have h_cthick_two_ε_in_chart : Metric.cthickening (2 * ε) K_α ⊆
      chartTargetEuclid (I := I) (M := M) α := by
    have hle : (2 * ε) ≤ R_α := by change 2 * (R_α / 16) ≤ R_α; linarith
    have h := Metric.cthickening_mono hle K_α
    exact h.trans hR_α_subset
  have h_closureΩ''_in_chart :
      closure Ω'' ⊆ chartTargetEuclid (I := I) (M := M) α :=
    h_closureΩ''_sub.trans h_cthick_two_ε_in_chart
  have hΩ''_compact_closure : IsCompact (closure Ω'') :=
    hK_α_compact.cthickening.of_isClosed_subset isClosed_closure h_closureΩ''_sub
  have h_room : Metric.cthickening R₀ (closure Ω'') ⊆
      chartTargetEuclid (I := I) (M := M) α := by
    have h1 : Metric.cthickening R₀ (closure Ω'') ⊆
        Metric.cthickening R₀ (Metric.cthickening (2 * ε) K_α) :=
      Metric.cthickening_subset_of_subset _ h_closureΩ''_sub
    have h2 : Metric.cthickening R₀ (Metric.cthickening (2 * ε) K_α) ⊆
        Metric.cthickening (R₀ + 2 * ε) K_α := by
      apply Metric.cthickening_cthickening_subset
      · positivity
      · positivity
    have h3 : Metric.cthickening (R₀ + 2 * ε) K_α ⊆
        Metric.cthickening R_α K_α := by
      have hle : R₀ + 2 * ε ≤ R_α := by
        change R_α / 16 + 2 * (R_α / 16) ≤ R_α; linarith
      exact Metric.cthickening_mono hle K_α
    exact ((h1.trans h2).trans h3).trans hR_α_subset
  set Ω' : Set EuclN := Metric.thickening (8 * ε) K_α with hΩ'_def
  have hΩ'_open : IsOpen Ω' := Metric.isOpen_thickening
  have h_eight_ε_pos : 0 < 8 * ε := by positivity
  have h_closureΩ'_sub : closure Ω' ⊆ Metric.cthickening (8 * ε) K_α := by
    refine closure_minimal (Metric.thickening_subset_cthickening _ _)
      Metric.isClosed_cthickening
  have h_cthick_eight_ε_in_chart : Metric.cthickening (8 * ε) K_α ⊆
      chartTargetEuclid (I := I) (M := M) α := by
    have hle : (8 * ε) ≤ R_α := by change 8 * (R_α / 16) ≤ R_α; linarith
    have h := Metric.cthickening_mono hle K_α
    exact h.trans hR_α_subset
  have h_closureΩ'_in_chart :
      closure Ω' ⊆ chartTargetEuclid (I := I) (M := M) α :=
    h_closureΩ'_sub.trans h_cthick_eight_ε_in_chart
  have hΩ'_compact_closure : IsCompact (closure Ω') :=
    hK_α_compact.cthickening.of_isClosed_subset isClosed_closure h_closureΩ'_sub
  set K_η : Set EuclN := Metric.cthickening (3 * ε) K_α with hK_η_def
  have hK_η_compact : IsCompact K_η := hK_α_compact.cthickening
  set Ω_η : Set EuclN := Metric.thickening (5 * ε) K_α with hΩ_η_def
  have hΩ_η_open : IsOpen Ω_η := Metric.isOpen_thickening
  have hK_η_in_Ω_η : K_η ⊆ Ω_η := by
    refine Metric.cthickening_subset_thickening' (by positivity) (by linarith) K_α
  obtain ⟨δ_η, η, hδ_η_pos, hδ_η_sub_Ωη, hη_smooth, hη_supp, hη_range,
      hη_one_on_cthick_K_η, hη_tsupp_in_Ω_η⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_smooth_cutoff_with_neighborhood
      (d := Module.finrank ℝ E) hK_η_compact hΩ_η_open hK_η_in_Ω_η
  obtain ⟨N, hN_pos, h_fderiv_eta⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Chart.exists_grad_bound_of_compactSupport_smooth
      hη_smooth hη_supp
  have hN_nn : 0 ≤ N := hN_pos.le
  have hη_one_on_K_η : ∀ x ∈ K_η, η x = 1 := by
    intro x hx
    apply hη_one_on_cthick_K_η
    exact Metric.self_subset_cthickening _ hx
  have hΩ''_sub_K_η : Ω'' ⊆ K_η := by
    intro y hy
    have h1 : y ∈ Metric.cthickening (2 * ε) K_α :=
      Metric.thickening_subset_cthickening _ _ hy
    refine Metric.cthickening_mono (by linarith : (2 * ε) ≤ 3 * ε) K_α h1
  have hη_one_on_Ω'' : ∀ x ∈ Ω'', η x = 1 :=
    fun x hx => hη_one_on_K_η x (hΩ''_sub_K_η hx)
  have hη_in_Ω' : tsupport η ⊆ Ω' := by
    refine hη_tsupp_in_Ω_η.trans ?_
    rw [hΩ_η_def, hΩ'_def]
    exact thickening_mono_of_lt (by linarith) K_α
  have hh_supp_in_Ω' : ∀ {h : ℝ}, |h| ≤ R₀ →
      Metric.cthickening |h| (tsupport η) ⊆ Ω' := by
    intro h hh
    have h_tsupp_in_cthick_5ε : tsupport η ⊆ Metric.cthickening (5 * ε) K_α := by
      refine hη_tsupp_in_Ω_η.trans ?_
      rw [hΩ_η_def]
      exact Metric.thickening_subset_cthickening _ _
    by_cases h_abs : |h| ≤ 0
    · have hh_zero : |h| = 0 := le_antisymm h_abs (abs_nonneg _)
      have hcth_zero : Metric.cthickening |h| (tsupport η) = tsupport η := by
        rw [hh_zero, Metric.cthickening_zero]
        exact (isClosed_tsupport η).closure_eq
      rw [hcth_zero]
      exact hη_in_Ω'
    · have h_abs_pos : 0 < |h| := not_le.mp h_abs
      have h1 : Metric.cthickening |h| (tsupport η) ⊆
          Metric.cthickening |h| (Metric.cthickening (5 * ε) K_α) :=
        Metric.cthickening_subset_of_subset _ h_tsupp_in_cthick_5ε
      have h2 : Metric.cthickening |h| (Metric.cthickening (5 * ε) K_α) ⊆
          Metric.cthickening (|h| + 5 * ε) K_α := by
        apply Metric.cthickening_cthickening_subset
        · exact h_abs_pos.le
        · positivity
      have h_le : |h| + 5 * ε < 8 * ε := by
        calc |h| + 5 * ε ≤ R₀ + 5 * ε := by linarith
          _ = ε + 5 * ε := by rw [hR₀_def]
          _ = 6 * ε := by ring
          _ < 8 * ε := by linarith
      have h3 : Metric.cthickening (|h| + 5 * ε) K_α ⊆ Ω' := by
        rw [hΩ'_def]
        exact Metric.cthickening_subset_thickening' (by linarith) h_le K_α
      exact (h1.trans h2).trans h3
  obtain ⟨M_bound, hM_nn, h_uniform_bd⟩ :=
    chartBilinearH1Compl_uniform_diffQuot_bound_of_data
      (I := I) (M := M) (g := g) (α := α) D
      hη_smooth hη_supp hη_range hN_nn h_fderiv_eta
      hΩ'_open h_closureΩ'_in_chart hΩ'_compact_closure
      hη_in_Ω' hR₀_pos hh_supp_in_Ω' hη_one_on_Ω'' hΩ''_open.measurableSet
  have h_h2 :=
    exists_weak_second_partial_of_uniform_diffQuot_bound
      (I := I) (M := M) (g := g) (α := α) D
      hΩ''_open hΩ''_compact_closure hR₀_pos h_room
      hM_nn h_uniform_bd
  have h_uChart_memLp_vol_closureΩ'' :
      MemLp D.u_chart 2 (volume.restrict (closure Ω'')) :=
    memLp_volume_restrict_of_memLp_chartPulledWeightedMeasure (I := I) (M := M)
      D.u_chart_memLp_weighted hΩ''_compact_closure
      hΩ''_compact_closure.isClosed.measurableSet h_closureΩ''_in_chart
  have h_uChart_memLp_vol_Ω'' :
      MemLp D.u_chart 2 (volume.restrict Ω'') :=
    h_uChart_memLp_vol_closureΩ''.mono_measure
      (Measure.restrict_mono subset_closure le_rfl)
  have h_dwp_memLp_Ω'' :
      ∀ i, MemLp (D.weak_partial i) 2 (volume.restrict Ω'') := by
    intro i
    have h := D.weak_partial_locally_memLp i (closure Ω'') hΩ''_compact_closure
      h_closureΩ''_in_chart
    exact h.mono_measure (Measure.restrict_mono subset_closure le_rfl)
  have h_dwp_weak_uChart_Ω'' :
      ∀ i, DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
        (D.weak_partial i) D.u_chart Ω'' := by
    intro i
    have h_full : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
        (D.weak_partial i) D.u_chart
        (chartTargetEuclid (I := I) (M := M) α) :=
      D.weak_partial_isWeakPartial i
    have hΩ''_in_chart : Ω'' ⊆ chartTargetEuclid (I := I) (M := M) α :=
      fun y hy => h_closureΩ''_in_chart (subset_closure hy)
    exact DeGiorgi.HasWeakPartialDeriv.restrict hΩ''_open hΩ''_in_chart h_full
  have h_uChart_memW1p_Ω'' :
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 D.u_chart Ω'' := by
    refine ⟨h_uChart_memLp_vol_Ω'', ?_⟩
    intro i
    exact ⟨D.weak_partial i, h_dwp_memLp_Ω'' i, h_dwp_weak_uChart_Ω'' i⟩
  have h_wp_i_memW1p_Ω'' : ∀ i,
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 (D.weak_partial i) Ω'' := by
    intro i
    refine ⟨h_dwp_memLp_Ω'' i, ?_⟩
    intro k
    obtain ⟨g_ik, hg_ik_memLp, hg_ik_partial, _hg_ik_norm⟩ := h_h2 i k
    exact ⟨g_ik, hg_ik_memLp, hg_ik_partial⟩
  have h_uChart_memWkp_two_Ω'' :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 2 2 D.u_chart Ω'' := by
    refine ⟨h_uChart_memW1p_Ω'', ?_⟩
    intro i
    have h_chosen_partial : DeGiorgi.HasWeakPartialDeriv
        (d := Module.finrank ℝ E) i
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          2 i D.u_chart Ω'') D.u_chart Ω'' :=
      DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_isWeakPartial_of_mem
        h_uChart_memW1p_Ω'' i
    have h_chosen_loc : MeasureTheory.LocallyIntegrable
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          2 i D.u_chart Ω'') (volume.restrict Ω'') :=
      (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_memLp_of_mem
        h_uChart_memW1p_Ω'' i).locallyIntegrable
          (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have h_dwp_loc : MeasureTheory.LocallyIntegrable (D.weak_partial i)
        (volume.restrict Ω'') :=
      (h_dwp_memLp_Ω'' i).locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have h_ae :
        DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          2 i D.u_chart Ω'' =ᵐ[volume.restrict Ω''] D.weak_partial i :=
      DeGiorgi.HasWeakPartialDeriv.ae_eq hΩ''_open h_chosen_partial
        (h_dwp_weak_uChart_Ω'' i) h_chosen_loc h_dwp_loc
    rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.one_iff_memW1p]
    exact (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemW1p_congr_ae
      hΩ''_open h_ae.symm).mp (h_wp_i_memW1p_Ω'' i)
  refine ⟨Ω'', hΩ''_open, hΩ''_compact_closure, h_closureΩ''_in_chart,
    hK_α_in_Ω'', ?_⟩
  exact h_uChart_memWkp_two_Ω''

end DerivedChartBilinearH2Interior
end Laplacian
end Analysis
end DifferentialGeometry

end
