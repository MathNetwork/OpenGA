import DifferentialGeometry.Analysis.Sobolev.Nirenberg.ChartBilinearDischarge.SubstitutionIBP
import DifferentialGeometry.Analysis.Sobolev.Nirenberg.ChartBilinearDischarge.SubstitutionGradTendsto
import DifferentialGeometry.Analysis.Sobolev.Nirenberg.SubstitutionIdentity.ChartBilinearTrivialCases


noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal Pointwise

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace SubstitutionDischargeAssembly

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Laplacian.ChartLocalLaplacian
open DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Sobolev.NirenbergStandardTest
open DifferentialGeometry.Analysis.Sobolev.NirenbergDiffQuotTestFunction
open DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction
open DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeSmoothApprox
open DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeGradTendsto
open DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeIBPExpand
open DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeIBP
open DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeFinal
open DifferentialGeometry.Analysis.Sobolev.SubstitutionNonSmoothChartBilinear

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))


omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] in
private theorem exists_chart_target_cutoff_strong
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {α : M}
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    {R₀ : ℝ} {h : ℝ} (_hh_le : |h| ≤ R₀)
    (h_thick :
      Metric.cthickening |h| K_0 ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ (δ : ℝ) (χ : EuclN → ℝ),
      0 < δ ∧
      ContDiff ℝ (⊤ : ℕ∞) χ ∧
      HasCompactSupport χ ∧
      (∀ x, 0 ≤ χ x) ∧ (∀ x, χ x ≤ 1) ∧
      (∀ x ∈ Metric.cthickening δ (Metric.cthickening |h| K_0), χ x = 1) ∧
      tsupport χ ⊆ chartTargetEuclid (I := I) (M := M) α := by
  classical
  have h_cthick_compact : IsCompact (Metric.cthickening |h| K_0) := by
    have h_bdd : Bornology.IsBounded (Metric.cthickening |h| K_0) :=
      hK_0_compact.isBounded.cthickening
    have h_closed : IsClosed (Metric.cthickening |h| K_0) :=
      Metric.isClosed_cthickening
    exact (Metric.isCompact_iff_isClosed_bounded).mpr ⟨h_closed, h_bdd⟩
  have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  obtain ⟨δ, χ, hδ_pos, _hδΩ, hχ_smooth, hχ_compact, hχ_range, hχ_one,
    hχ_supp⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_smooth_cutoff_with_neighborhood
      (d := Module.finrank ℝ E) h_cthick_compact h_open h_thick
  refine ⟨δ, χ, hδ_pos, hχ_smooth, hχ_compact, ?_, ?_, hχ_one, hχ_supp⟩
  · intro x
    have hx_range : χ x ∈ Set.range χ := Set.mem_range_self x
    exact (hχ_range hx_range).1
  · intro x
    have hx_range : χ x ∈ Set.range χ := Set.mem_range_self x
    exact (hχ_range hx_range).2

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma fderiv_chi_zero_on_cthickening
    {δ : ℝ} (hδ : 0 < δ) {χ : EuclN → ℝ} {h : ℝ} {K_0 : Set EuclN}
    (hχ_one : ∀ x ∈ Metric.cthickening δ (Metric.cthickening |h| K_0), χ x = 1)
    {x : EuclN} (hx : x ∈ Metric.cthickening |h| K_0)
    (i : Fin (Module.finrank ℝ E)) :
    (fderiv ℝ χ x) (EuclideanSpace.single i 1) = 0 :=
  DifferentialGeometry.Analysis.Sobolev.Euclidean.fderiv_cutoff_apply_zero_on_cthickening
    (d := Module.finrank ℝ E) hδ hχ_one hx i


omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma chi_eq_one_on_cthickening
    {δ : ℝ} (_hδ : 0 < δ) {χ : EuclN → ℝ} {h : ℝ} {K_0 : Set EuclN}
    (hχ_one : ∀ x ∈ Metric.cthickening δ (Metric.cthickening |h| K_0), χ x = 1)
    {x : EuclN} (hx : x ∈ Metric.cthickening |h| K_0) : χ x = 1 := by
  have hx_inner : x ∈ Metric.cthickening δ (Metric.cthickening |h| K_0) :=
    Metric.self_subset_cthickening _ hx
  exact hχ_one x hx_inner

private noncomputable def vTestPartialSummand
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (η : EuclN → ℝ) (k : Fin (Module.finrank ℝ E)) (h : ℝ)
    (j : Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  fun z => (η z)^2 *
    DifferentialGeometry.Analysis.Sobolev.diffQuot
      (d := Module.finrank ℝ E) k h (D.weak_partial j) z +
    2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h D.u_chart z

private noncomputable def vTestPartialSummandIndicator
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (η : EuclN → ℝ) (k : Fin (Module.finrank ℝ E)) (h : ℝ) (K_0 : Set EuclN)
    (j : Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  fun z => (η z)^2 *
    DifferentialGeometry.Analysis.Sobolev.diffQuot
      (d := Module.finrank ℝ E) k h
      ((Metric.cthickening |h| K_0).indicator (D.weak_partial j)) z +
    2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h
        ((Metric.cthickening |h| K_0).indicator D.u_chart) z

omit [NeZero (Module.finrank ℝ E)] in
private lemma tF_eq_tFE_on_tsupport
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN}
    {η : EuclN → ℝ}
    (hη_supp_in_K_0 : tsupport η ⊆ K_0)
    (k : Fin (Module.finrank ℝ E)) {h : ℝ}
    (j : Fin (Module.finrank ℝ E))
    {z : EuclN} (hz : z ∈ tsupport η) :
    vTestPartialSummand (I := I) (M := M) D η k h j z =
      vTestPartialSummandIndicator (I := I) (M := M) D η k h K_0 j z := by
  classical
  have hz_K_0 : z ∈ K_0 := hη_supp_in_K_0 hz
  have hz_thick : z ∈ Metric.cthickening |h| K_0 :=
    Metric.self_subset_cthickening _ hz_K_0
  have hz_shift : z + h • EuclideanSpace.single k 1 ∈ Metric.cthickening |h| K_0 := by
    refine Metric.mem_cthickening_of_dist_le _ z |h| K_0 hz_K_0 ?_
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul]
    simp [Real.norm_eq_abs]
  have h_dq_wp : DifferentialGeometry.Analysis.Sobolev.diffQuot
      (d := Module.finrank ℝ E) k h (D.weak_partial j) z =
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h
        ((Metric.cthickening |h| K_0).indicator (D.weak_partial j)) z := by
    by_cases hh : h = 0
    · subst hh
      simp [DifferentialGeometry.Analysis.Sobolev.diffQuot]
    · rw [DifferentialGeometry.Analysis.Sobolev.diffQuot_apply_of_ne
        (d := Module.finrank ℝ E) k hh]
      rw [DifferentialGeometry.Analysis.Sobolev.diffQuot_apply_of_ne
        (d := Module.finrank ℝ E) k hh]
      rw [Set.indicator_of_mem hz_shift, Set.indicator_of_mem hz_thick]
  have h_dq_u : DifferentialGeometry.Analysis.Sobolev.diffQuot
      (d := Module.finrank ℝ E) k h D.u_chart z =
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h
        ((Metric.cthickening |h| K_0).indicator D.u_chart) z := by
    by_cases hh : h = 0
    · subst hh
      simp [DifferentialGeometry.Analysis.Sobolev.diffQuot]
    · rw [DifferentialGeometry.Analysis.Sobolev.diffQuot_apply_of_ne
        (d := Module.finrank ℝ E) k hh]
      rw [DifferentialGeometry.Analysis.Sobolev.diffQuot_apply_of_ne
        (d := Module.finrank ℝ E) k hh]
      rw [Set.indicator_of_mem hz_shift, Set.indicator_of_mem hz_thick]
  unfold vTestPartialSummand vTestPartialSummandIndicator
  rw [h_dq_wp, h_dq_u]

omit [NeZero (Module.finrank ℝ E)] in
private lemma tF_eq_zero_outside_tsupport
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {η : EuclN → ℝ} (k : Fin (Module.finrank ℝ E)) (h : ℝ)
    (j : Fin (Module.finrank ℝ E))
    {z : EuclN} (hz : z ∉ tsupport η) :
    vTestPartialSummand (I := I) (M := M) D η k h j z = 0 := by
  unfold vTestPartialSummand
  have hηz : η z = 0 := image_eq_zero_of_notMem_tsupport hz
  rw [show (η z)^2 = 0 from by rw [hηz]; ring, zero_mul]
  rw [show 2 * η z = 0 from by rw [hηz]; ring]
  ring

omit [NeZero (Module.finrank ℝ E)] in
private lemma tFE_eq_zero_outside_tsupport
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {η : EuclN → ℝ} {h : ℝ} (k : Fin (Module.finrank ℝ E)) (K_0 : Set EuclN)
    (j : Fin (Module.finrank ℝ E))
    {z : EuclN} (hz : z ∉ tsupport η) :
    vTestPartialSummandIndicator (I := I) (M := M) D η k h K_0 j z = 0 := by
  unfold vTestPartialSummandIndicator
  have hηz : η z = 0 := image_eq_zero_of_notMem_tsupport hz
  rw [show (η z)^2 = 0 from by rw [hηz]; ring, zero_mul]
  rw [show 2 * η z = 0 from by rw [hηz]; ring]
  ring

omit [NeZero (Module.finrank ℝ E)] in
private lemma tF_eq_tFE
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN}
    {η : EuclN → ℝ}
    (hη_supp_in_K_0 : tsupport η ⊆ K_0)
    (k : Fin (Module.finrank ℝ E)) {h : ℝ}
    (j : Fin (Module.finrank ℝ E)) :
    vTestPartialSummand (I := I) (M := M) D η k h j =
      vTestPartialSummandIndicator (I := I) (M := M) D η k h K_0 j := by
  funext z
  by_cases hz : z ∈ tsupport η
  · exact tF_eq_tFE_on_tsupport (I := I) (M := M) D
      hη_supp_in_K_0 k j hz
  · rw [tF_eq_zero_outside_tsupport (I := I) (M := M) D k h j hz,
      tFE_eq_zero_outside_tsupport (I := I) (M := M) D k K_0 j hz]

omit [NeZero (Module.finrank ℝ E)] in
private lemma uChart_indicator_memLp
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    {R₀ : ℝ} {h : ℝ} (hh_le : |h| ≤ R₀)
    (h_thick : Metric.cthickening |h| K_0 ⊆
      chartTargetEuclid (I := I) (M := M) α) :
    MemLp ((Metric.cthickening |h| K_0).indicator D.u_chart) 2
      (volume : Measure EuclN) := by
  classical
  have h_thick_compact : IsCompact (Metric.cthickening |h| K_0) :=
    cthickening_K_0_isCompact (E := E) hK_0_compact hh_le
  have h_thick_meas : MeasurableSet (Metric.cthickening |h| K_0) :=
    h_thick_compact.measurableSet
  refine (MeasureTheory.memLp_indicator_iff_restrict h_thick_meas).mpr ?_
  exact memLp_volume_restrict_of_memLp_chartPulledWeightedMeasure (I := I) (M := M)
    D.u_chart_memLp_weighted h_thick_compact h_thick_meas h_thick

omit [NeZero (Module.finrank ℝ E)] in
private lemma weakPartial_indicator_memLp
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    {R₀ : ℝ} {h : ℝ} (hh_le : |h| ≤ R₀)
    (h_thick : Metric.cthickening |h| K_0 ⊆
      chartTargetEuclid (I := I) (M := M) α)
    (j : Fin (Module.finrank ℝ E)) :
    MemLp ((Metric.cthickening |h| K_0).indicator (D.weak_partial j)) 2
      (volume : Measure EuclN) := by
  classical
  have h_thick_compact : IsCompact (Metric.cthickening |h| K_0) :=
    cthickening_K_0_isCompact (E := E) hK_0_compact hh_le
  have h_thick_meas : MeasurableSet (Metric.cthickening |h| K_0) :=
    h_thick_compact.measurableSet
  refine (MeasureTheory.memLp_indicator_iff_restrict h_thick_meas).mpr ?_
  exact D.weak_partial_locally_memLp j (Metric.cthickening |h| K_0)
    h_thick_compact h_thick

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma memLp_diffQuot_of_memLp_local
    {F : EuclN → ℝ} (hF_lp : MemLp F 2 (volume : Measure EuclN))
    (k : Fin (Module.finrank ℝ E)) {h : ℝ} (hh : h ≠ 0) :
    MemLp (DifferentialGeometry.Analysis.Sobolev.diffQuot
      (d := Module.finrank ℝ E) k h F) 2 (volume : Measure EuclN) := by
  classical
  have hF_aesm : AEStronglyMeasurable F (volume : Measure EuclN) :=
    hF_lp.aestronglyMeasurable
  have hdq_aesm : AEStronglyMeasurable
      (DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h F) (volume : Measure EuclN) :=
    DifferentialGeometry.Analysis.Sobolev.aestronglyMeasurable_diffQuot
      (d := Module.finrank ℝ E) k h hF_aesm
  refine ⟨hdq_aesm, ?_⟩
  have h_dq_eq : DifferentialGeometry.Analysis.Sobolev.diffQuot
      (d := Module.finrank ℝ E) k h F =
      h⁻¹ • (DifferentialGeometry.Analysis.Sobolev.translate
        (d := Module.finrank ℝ E) k h F - F) := by
    funext x
    rw [DifferentialGeometry.Analysis.Sobolev.diffQuot_apply_of_ne
      (d := Module.finrank ℝ E) k hh F x]
    simp [Pi.smul_apply, Pi.sub_apply,
      DifferentialGeometry.Analysis.Sobolev.translate, smul_eq_mul]
    field_simp
  rw [h_dq_eq]
  have hτF_lp : MemLp (DifferentialGeometry.Analysis.Sobolev.translate
      (d := Module.finrank ℝ E) k h F) 2 (volume : Measure EuclN) :=
    DifferentialGeometry.Analysis.Sobolev.memLp_translate
      (d := Module.finrank ℝ E) k h hF_lp
  have h_diff_lp : MemLp ((DifferentialGeometry.Analysis.Sobolev.translate
      (d := Module.finrank ℝ E) k h F) - F) 2
      (volume : Measure EuclN) := hτF_lp.sub hF_lp
  have h_smul_lp : MemLp (h⁻¹ • ((DifferentialGeometry.Analysis.Sobolev.translate
      (d := Module.finrank ℝ E) k h F) - F)) 2
      (volume : Measure EuclN) := h_diff_lp.const_smul h⁻¹
  exact h_smul_lp.eLpNorm_lt_top

omit [NeZero (Module.finrank ℝ E)] in
private lemma tFE_memLp_two
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    {η : EuclN → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_supp : HasCompactSupport η)
    (k : Fin (Module.finrank ℝ E))
    {R₀ : ℝ} {h : ℝ} (hh : h ≠ 0) (hh_le : |h| ≤ R₀)
    (h_thick : Metric.cthickening |h| K_0 ⊆
      chartTargetEuclid (I := I) (M := M) α)
    (j : Fin (Module.finrank ℝ E)) :
    MemLp (vTestPartialSummandIndicator (I := I) (M := M) D η k h K_0 j) 2
      (volume : Measure EuclN) := by
  classical
  have hη_cont : Continuous η := hη.continuous
  have h_top_ne_zero : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by decide
  obtain ⟨M_η, hM_η_nn, hM_η_bd⟩ : ∃ M_η : ℝ, 0 ≤ M_η ∧ ∀ x, |η x| ≤ M_η := by
    by_cases hSupp_empty : (tsupport η).Nonempty
    · obtain ⟨xMax, _hxMax_in, hxMax_max⟩ :=
        hη_supp.exists_isMaxOn hSupp_empty hη_cont.abs.continuousOn
      refine ⟨|η xMax|, abs_nonneg _, ?_⟩
      intro x
      by_cases hx : x ∈ tsupport η
      · exact hxMax_max hx
      · have hηx : η x = 0 := image_eq_zero_of_notMem_tsupport hx
        rw [hηx, abs_zero]; exact abs_nonneg _
    · refine ⟨0, le_refl _, ?_⟩
      intro x
      by_cases hx : x ∈ tsupport η
      · exact absurd ⟨x, hx⟩ hSupp_empty
      · have hηx : η x = 0 := image_eq_zero_of_notMem_tsupport hx
        rw [hηx, abs_zero]
  have h_partial_eta_cont : Continuous
      (fun z : EuclN => (fderiv ℝ η z) (EuclideanSpace.single j 1)) :=
    (hη.continuous_fderiv h_top_ne_zero).clm_apply continuous_const
  have h_partial_eta_cs : HasCompactSupport
      (fun z : EuclN => (fderiv ℝ η z) (EuclideanSpace.single j 1)) :=
    hη_supp.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single j 1)
  obtain ⟨M_dη, hM_dη_nn, hM_dη_bd⟩ :
      ∃ M_dη : ℝ, 0 ≤ M_dη ∧
        ∀ x, |(fderiv ℝ η x) (EuclideanSpace.single j 1)| ≤ M_dη := by
    by_cases hSupp_empty : (tsupport (fun z : EuclN => (fderiv ℝ η z)
        (EuclideanSpace.single j 1))).Nonempty
    · obtain ⟨xMax, _hxMax_in, hxMax_max⟩ :=
        h_partial_eta_cs.exists_isMaxOn hSupp_empty
          h_partial_eta_cont.abs.continuousOn
      refine ⟨|(fderiv ℝ η xMax) (EuclideanSpace.single j 1)|, abs_nonneg _, ?_⟩
      intro x
      by_cases hx : x ∈ tsupport (fun z : EuclN => (fderiv ℝ η z)
          (EuclideanSpace.single j 1))
      · exact hxMax_max hx
      · have hpartialx :
            (fun z : EuclN => (fderiv ℝ η z) (EuclideanSpace.single j 1)) x = 0 :=
          image_eq_zero_of_notMem_tsupport
            (f := fun z : EuclN => (fderiv ℝ η z) (EuclideanSpace.single j 1)) hx
        rw [show (fderiv ℝ η x) (EuclideanSpace.single j 1) = 0 from hpartialx,
          abs_zero]
        exact abs_nonneg _
    · refine ⟨0, le_refl _, ?_⟩
      intro x
      by_cases hx : x ∈ tsupport (fun z : EuclN => (fderiv ℝ η z)
          (EuclideanSpace.single j 1))
      · exact absurd ⟨x, hx⟩ hSupp_empty
      · have hpartialx :
            (fun z : EuclN => (fderiv ℝ η z) (EuclideanSpace.single j 1)) x = 0 :=
          image_eq_zero_of_notMem_tsupport
            (f := fun z : EuclN => (fderiv ℝ η z) (EuclideanSpace.single j 1)) hx
        rw [show (fderiv ℝ η x) (EuclideanSpace.single j 1) = 0 from hpartialx,
          abs_zero]
  have hu_ext_lp := uChart_indicator_memLp (I := I) (M := M) D
    hK_0_compact hh_le h_thick
  have hwp_ext_lp := weakPartial_indicator_memLp (I := I) (M := M) D
    hK_0_compact hh_le h_thick j
  have hdq_u_ext_lp : MemLp
      (DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h
        ((Metric.cthickening |h| K_0).indicator D.u_chart)) 2
      (volume : Measure EuclN) :=
    memLp_diffQuot_of_memLp_local hu_ext_lp k hh
  have hdq_wp_ext_lp : MemLp
      (DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h
        ((Metric.cthickening |h| K_0).indicator (D.weak_partial j))) 2
      (volume : Measure EuclN) :=
    memLp_diffQuot_of_memLp_local hwp_ext_lp k hh
  unfold vTestPartialSummandIndicator
  have ht1_pt_bd : ∀ z, ‖(η z)^2 *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h
        ((Metric.cthickening |h| K_0).indicator (D.weak_partial j)) z‖ ≤
      ‖M_η^2 *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h
        ((Metric.cthickening |h| K_0).indicator (D.weak_partial j)) z‖ := by
    intro z
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ M_η^2)]
    have h_eta_sq : |(η z)^2| ≤ M_η^2 := by
      have h_abs : |η z| ≤ M_η := hM_η_bd z
      have h_eq : |(η z)^2| = (η z)^2 := abs_of_nonneg (sq_nonneg _)
      rw [h_eq]
      calc (η z)^2 = (|η z|)^2 := (sq_abs _).symm
        _ ≤ M_η^2 := pow_le_pow_left₀ (abs_nonneg _) h_abs 2
    exact mul_le_mul_of_nonneg_right h_eta_sq (abs_nonneg _)
  have ht1_aesm : AEStronglyMeasurable (fun z => (η z)^2 *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h
        ((Metric.cthickening |h| K_0).indicator (D.weak_partial j)) z)
      (volume : Measure EuclN) :=
    (hη_cont.pow 2).aestronglyMeasurable.mul hdq_wp_ext_lp.aestronglyMeasurable
  have ht1_lp : MemLp (fun z => (η z)^2 *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h
        ((Metric.cthickening |h| K_0).indicator (D.weak_partial j)) z) 2
      (volume : Measure EuclN) :=
    MemLp.mono (hdq_wp_ext_lp.const_mul (M_η^2)) ht1_aesm
      (Filter.Eventually.of_forall ht1_pt_bd)
  have ht2_pt_bd : ∀ z, ‖2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h
        ((Metric.cthickening |h| K_0).indicator D.u_chart) z‖ ≤
      ‖(2 * M_η * M_dη) *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h
          ((Metric.cthickening |h| K_0).indicator D.u_chart) z‖ := by
    intro z
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    have h_lhs_abs : |(2 : ℝ) * η z *
        (fderiv ℝ η z) (EuclideanSpace.single j 1) *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h
          ((Metric.cthickening |h| K_0).indicator D.u_chart) z| =
        (2 * |η z| * |(fderiv ℝ η z) (EuclideanSpace.single j 1)|) *
        |DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h
          ((Metric.cthickening |h| K_0).indicator D.u_chart) z| := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have h_rhs_abs : |(2 * M_η * M_dη) *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h
          ((Metric.cthickening |h| K_0).indicator D.u_chart) z| =
        (2 * M_η * M_dη) *
        |DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h
          ((Metric.cthickening |h| K_0).indicator D.u_chart) z| := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * M_η * M_dη)]
    rw [h_lhs_abs, h_rhs_abs]
    have h_factor : 2 * |η z| * |(fderiv ℝ η z) (EuclideanSpace.single j 1)| ≤
        2 * M_η * M_dη := by
      have h1 : |η z| * |(fderiv ℝ η z) (EuclideanSpace.single j 1)| ≤
          M_η * M_dη :=
        mul_le_mul (hM_η_bd z) (hM_dη_bd z) (abs_nonneg _) hM_η_nn
      calc 2 * |η z| * |(fderiv ℝ η z) (EuclideanSpace.single j 1)|
          = 2 * (|η z| * |(fderiv ℝ η z) (EuclideanSpace.single j 1)|) := by ring
        _ ≤ 2 * (M_η * M_dη) :=
            mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 2)
        _ = 2 * M_η * M_dη := by ring
    exact mul_le_mul_of_nonneg_right h_factor (abs_nonneg _)
  have ht2_aesm : AEStronglyMeasurable (fun z =>
      2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h
          ((Metric.cthickening |h| K_0).indicator D.u_chart) z)
      (volume : Measure EuclN) :=
    (((continuous_const.mul hη_cont).mul h_partial_eta_cont).aestronglyMeasurable).mul
      hdq_u_ext_lp.aestronglyMeasurable
  have ht2_lp : MemLp (fun z =>
      2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h
          ((Metric.cthickening |h| K_0).indicator D.u_chart) z) 2
      (volume : Measure EuclN) :=
    MemLp.mono (hdq_u_ext_lp.const_mul (2 * M_η * M_dη)) ht2_aesm
      (Filter.Eventually.of_forall ht2_pt_bd)
  exact ht1_lp.add ht2_lp

private noncomputable def weakPartial_v_h
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (η : EuclN → ℝ) (k : Fin (Module.finrank ℝ E)) (h : ℝ)
    (j : Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  DifferentialGeometry.Analysis.Sobolev.diffQuot
    (d := Module.finrank ℝ E) k (-h)
    (vTestPartialSummand (I := I) (M := M) D η k h j)

omit [NeZero (Module.finrank ℝ E)] in
private lemma weakPartial_v_h_memLp
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    {η : EuclN → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_supp : HasCompactSupport η)
    (hη_supp_in_K_0 : tsupport η ⊆ K_0)
    (k : Fin (Module.finrank ℝ E))
    {R₀ : ℝ} {h : ℝ} (hh : h ≠ 0) (hh_le : |h| ≤ R₀)
    (h_thick : Metric.cthickening |h| K_0 ⊆
      chartTargetEuclid (I := I) (M := M) α)
    (j : Fin (Module.finrank ℝ E)) :
    MemLp (weakPartial_v_h (I := I) (M := M) D η k h j) 2
      (volume : Measure EuclN) := by
  classical
  unfold weakPartial_v_h
  rw [tF_eq_tFE (I := I) (M := M) D hη_supp_in_K_0 k j]
  have hnh : (-h) ≠ 0 := neg_ne_zero.mpr hh
  exact memLp_diffQuot_of_memLp_local
    (tFE_memLp_two (I := I) (M := M) D hK_0_compact hη hη_supp k hh hh_le h_thick j)
    k hnh

omit [NeZero (Module.finrank ℝ E)] in
private lemma standardNirenbergTest_uChart_memLp_cthickening
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    {η : EuclN → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_supp : HasCompactSupport η)
    (hη_supp_in_K_0 : tsupport η ⊆ K_0)
    (k : Fin (Module.finrank ℝ E))
    {R₀ : ℝ} {h : ℝ} (hh : h ≠ 0) (hh_le : |h| ≤ R₀)
    (h_thick : Metric.cthickening |h| K_0 ⊆
      chartTargetEuclid (I := I) (M := M) α) :
    MemLp (standardNirenbergTest (d := Module.finrank ℝ E) k h η D.u_chart) 2
      ((volume : Measure EuclN).restrict (Metric.cthickening |h| K_0)) := by
  classical
  set F : EuclN → ℝ := fun z =>
    (η z)^2 *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h D.u_chart z with hF_def
  set F_ext : EuclN → ℝ := fun z =>
    (η z)^2 *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h
        ((Metric.cthickening |h| K_0).indicator D.u_chart) z with hF_ext_def
  have hF_eq : F = F_ext := by
    funext z
    by_cases hz : z ∈ tsupport η
    · have hz_K_0 : z ∈ K_0 := hη_supp_in_K_0 hz
      have hz_thick : z ∈ Metric.cthickening |h| K_0 :=
        Metric.self_subset_cthickening _ hz_K_0
      have hz_shift : z + h • EuclideanSpace.single k 1 ∈ Metric.cthickening |h| K_0 := by
        refine Metric.mem_cthickening_of_dist_le _ z |h| K_0 hz_K_0 ?_
        rw [dist_eq_norm, add_sub_cancel_left, norm_smul]
        simp [Real.norm_eq_abs]
      have h_dq_u : DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h D.u_chart z =
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h
            ((Metric.cthickening |h| K_0).indicator D.u_chart) z := by
        by_cases hh_eq : h = 0
        · subst hh_eq
          simp [DifferentialGeometry.Analysis.Sobolev.diffQuot]
        · rw [DifferentialGeometry.Analysis.Sobolev.diffQuot_apply_of_ne
            (d := Module.finrank ℝ E) k hh_eq]
          rw [DifferentialGeometry.Analysis.Sobolev.diffQuot_apply_of_ne
            (d := Module.finrank ℝ E) k hh_eq]
          rw [Set.indicator_of_mem hz_shift, Set.indicator_of_mem hz_thick]
      change (η z)^2 *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h D.u_chart z =
        (η z)^2 *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h
          ((Metric.cthickening |h| K_0).indicator D.u_chart) z
      rw [h_dq_u]
    · have hηz : η z = 0 := image_eq_zero_of_notMem_tsupport hz
      change (η z)^2 *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h D.u_chart z =
        (η z)^2 *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h
          ((Metric.cthickening |h| K_0).indicator D.u_chart) z
      rw [show (η z)^2 = 0 from by rw [hηz]; ring]
      ring
  have hη_cont : Continuous η := hη.continuous
  obtain ⟨M_η, hM_η_nn, hM_η_bd⟩ : ∃ M_η : ℝ, 0 ≤ M_η ∧ ∀ x, |η x| ≤ M_η := by
    by_cases hSupp_empty : (tsupport η).Nonempty
    · obtain ⟨xMax, _hxMax_in, hxMax_max⟩ :=
        hη_supp.exists_isMaxOn hSupp_empty hη_cont.abs.continuousOn
      refine ⟨|η xMax|, abs_nonneg _, ?_⟩
      intro x
      by_cases hx : x ∈ tsupport η
      · exact hxMax_max hx
      · have hηx : η x = 0 := image_eq_zero_of_notMem_tsupport hx
        rw [hηx, abs_zero]; exact abs_nonneg _
    · refine ⟨0, le_refl _, ?_⟩
      intro x
      by_cases hx : x ∈ tsupport η
      · exact absurd ⟨x, hx⟩ hSupp_empty
      · have hηx : η x = 0 := image_eq_zero_of_notMem_tsupport hx
        rw [hηx, abs_zero]
  have hu_ext_lp := uChart_indicator_memLp (I := I) (M := M) D
    hK_0_compact hh_le h_thick
  have hdq_u_ext_lp : MemLp
      (DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h
        ((Metric.cthickening |h| K_0).indicator D.u_chart)) 2
      (volume : Measure EuclN) :=
    memLp_diffQuot_of_memLp_local hu_ext_lp k hh
  have hF_ext_pt_bd : ∀ z, ‖F_ext z‖ ≤
      ‖M_η^2 *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h
          ((Metric.cthickening |h| K_0).indicator D.u_chart) z‖ := by
    intro z
    change ‖(η z)^2 * _‖ ≤ ‖M_η^2 * _‖
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ M_η^2)]
    have h_eta_sq : |(η z)^2| ≤ M_η^2 := by
      have h_abs : |η z| ≤ M_η := hM_η_bd z
      have h_eq : |(η z)^2| = (η z)^2 := abs_of_nonneg (sq_nonneg _)
      rw [h_eq]
      calc (η z)^2 = (|η z|)^2 := (sq_abs _).symm
        _ ≤ M_η^2 := pow_le_pow_left₀ (abs_nonneg _) h_abs 2
    exact mul_le_mul_of_nonneg_right h_eta_sq (abs_nonneg _)
  have hF_ext_aesm : AEStronglyMeasurable F_ext (volume : Measure EuclN) :=
    (hη_cont.pow 2).aestronglyMeasurable.mul hdq_u_ext_lp.aestronglyMeasurable
  have hF_ext_lp : MemLp F_ext 2 (volume : Measure EuclN) :=
    MemLp.mono (hdq_u_ext_lp.const_mul (M_η^2)) hF_ext_aesm
      (Filter.Eventually.of_forall hF_ext_pt_bd)
  have hF_lp : MemLp F 2 (volume : Measure EuclN) := by
    rw [hF_eq]; exact hF_ext_lp
  have hnh : (-h) ≠ 0 := neg_ne_zero.mpr hh
  have h_dq_F_lp : MemLp
      (DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k (-h) F) 2
      (volume : Measure EuclN) :=
    memLp_diffQuot_of_memLp_local hF_lp k hnh
  have h_restrict_lp : MemLp
      (DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k (-h) F) 2
      ((volume : Measure EuclN).restrict (Metric.cthickening |h| K_0)) :=
    h_dq_F_lp.restrict _
  have h_test_eq : standardNirenbergTest (d := Module.finrank ℝ E) k h η D.u_chart =
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k (-h) F := rfl
  rw [h_test_eq]
  exact h_restrict_lp


theorem variational_identity_at_v_h_unconditional
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    (hK_0_in : K_0 ⊆ chartTargetEuclid (I := I) (M := M) α)
    {η : EuclN → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_supp : HasCompactSupport η)
    (hη_supp_in_K_0 : tsupport η ⊆ K_0)
    (k : Fin (Module.finrank ℝ E))
    {R₀ : ℝ} {h : ℝ} (hh : h ≠ 0) (hh_le : |h| ≤ R₀)
    (h_thick : Metric.cthickening |h| K_0 ⊆
      chartTargetEuclid (I := I) (M := M) α) :
    (∫ y in Metric.cthickening |h| K_0,
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramOnEuclid (I := I) g α i j y *
              D.weak_partial i y *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k (-h)
                (fun z => (η z) ^ 2 *
                  DifferentialGeometry.Analysis.Sobolev.diffQuot
                    (d := Module.finrank ℝ E) k h (D.weak_partial j) z +
                  2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) *
                    DifferentialGeometry.Analysis.Sobolev.diffQuot
                      (d := Module.finrank ℝ E) k h D.u_chart z) y)
        ∂(volume : Measure EuclN)) +
      (∫ y in Metric.cthickening |h| K_0,
        densityOnEuclid (I := I) g α y * D.u_chart y *
          standardNirenbergTest (d := Module.finrank ℝ E) k h η D.u_chart y
        ∂(volume : Measure EuclN)) =
      ∫ y in Metric.cthickening |h| K_0,
        densityOnEuclid (I := I) g α y * D.f_chart y *
          standardNirenbergTest (d := Module.finrank ℝ E) k h η D.u_chart y
        ∂(volume : Measure EuclN) := by
  classical
  obtain ⟨δ, χ, hδ_pos, hχ_smooth, hχ_cs, hχ_nn, hχ_le_one,
    hχ_one_strong, hχ_supp⟩ :=
    exists_chart_target_cutoff_strong (I := I) (M := M) (α := α)
      hK_0_compact hh_le h_thick
  have hχ_one : ∀ x ∈ Metric.cthickening |h| K_0, χ x = 1 := fun x hx =>
    chi_eq_one_on_cthickening hδ_pos hχ_one_strong hx
  have hχ_dx_zero : ∀ x ∈ Metric.cthickening |h| K_0, ∀ i,
      (fderiv ℝ χ x) (EuclideanSpace.single i 1) = 0 := fun x hx i =>
    fderiv_chi_zero_on_cthickening hδ_pos hχ_one_strong hx i
  obtain ⟨u_seq, hu_seq_smooth, hu_seq_cs, hu_seq_l2, hu_seq_grad_l2⟩ :=
    exists_smooth_uChart_approx (I := I) (M := M) D
      hχ_smooth hχ_cs hχ_supp
  have h_v_seq_l2 :
      Tendsto (fun n => eLpNorm (fun x =>
        standardNirenbergTest (d := Module.finrank ℝ E) k h η (u_seq n) x -
        standardNirenbergTest (d := Module.finrank ℝ E) k h η D.u_chart x) 2
        ((volume : Measure EuclN).restrict (Metric.cthickening |h| K_0)))
        atTop (𝓝 0) :=
    standardNirenbergTest_seq_tendsto_eLpNorm (I := I) (M := M) D
      hχ_smooth hχ_cs hχ_supp hη hη_supp k hh hh_le hK_0_compact
      hχ_one hη_supp_in_K_0 hu_seq_smooth hu_seq_cs hu_seq_l2
  have h_v_seq_grad_l2 : ∀ j : Fin (Module.finrank ℝ E),
      Tendsto (fun n => eLpNorm
        (fun y => (fderiv ℝ
          (standardNirenbergTest (d := Module.finrank ℝ E) k h η
            (u_seq n)) y) (EuclideanSpace.single j 1) -
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k (-h)
            (fun z => (η z)^2 *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h (D.weak_partial j) z +
              2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) *
                DifferentialGeometry.Analysis.Sobolev.diffQuot
                  (d := Module.finrank ℝ E) k h D.u_chart z) y) 2
        ((volume : Measure EuclN).restrict
          (Metric.cthickening |h| K_0))) atTop (𝓝 0) := by
    intro j
    exact standardNirenbergTest_seq_grad_tendsto_eLpNorm (I := I) (M := M) D
      hχ_smooth hχ_cs hχ_supp hη hη_supp hK_0_compact hχ_one hχ_dx_zero
      hη_supp_in_K_0 k hh hh_le hu_seq_smooth hu_seq_cs hu_seq_l2
      hu_seq_grad_l2 j
  set wpv : Fin (Module.finrank ℝ E) → EuclN → ℝ := fun j y =>
    DifferentialGeometry.Analysis.Sobolev.diffQuot
      (d := Module.finrank ℝ E) k (-h)
      (fun z => (η z)^2 *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h (D.weak_partial j) z +
        2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h D.u_chart z) y with hwpv_def
  have hv_h_lp : MemLp (standardNirenbergTest (d := Module.finrank ℝ E)
      k h η D.u_chart) 2
      ((volume : Measure EuclN).restrict (Metric.cthickening |h| K_0)) :=
    standardNirenbergTest_uChart_memLp_cthickening (I := I) (M := M) D
      hK_0_compact hη hη_supp hη_supp_in_K_0 k hh hh_le h_thick
  have h_wpv_eq_def : ∀ j : Fin (Module.finrank ℝ E),
      wpv j = weakPartial_v_h (I := I) (M := M) D η k h j := by
    intro j
    rfl
  have hv_h_grad_lp : ∀ j : Fin (Module.finrank ℝ E),
      MemLp (wpv j) 2
        ((volume : Measure EuclN).restrict (Metric.cthickening |h| K_0)) := by
    intro j
    rw [h_wpv_eq_def j]
    exact (weakPartial_v_h_memLp (I := I) (M := M) D
      hK_0_compact hη hη_supp hη_supp_in_K_0 k hh hh_le h_thick j).restrict _
  have h_v_seq_supp : ∀ n : ℕ,
      tsupport (standardNirenbergTest (d := Module.finrank ℝ E)
        k h η (u_seq n)) ⊆ Metric.cthickening |h| K_0 := fun n =>
    standardNirenbergTest_tsupport_in_thickening (E := E) k h hη_supp
      hη_supp_in_K_0 (u_seq n)
  exact variational_identity_at_v_h (I := I) (M := M) D
    hK_0_compact hK_0_in hη hη_supp hη_supp_in_K_0 k hh hh_le h_thick
    wpv hv_h_lp hv_h_grad_lp u_seq hu_seq_smooth hu_seq_cs h_v_seq_supp
    h_v_seq_l2 h_v_seq_grad_l2


theorem variational_identity_v_h_expanded_unconditional
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    (hK_0_in : K_0 ⊆ chartTargetEuclid (I := I) (M := M) α)
    {η : EuclN → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_supp : HasCompactSupport η)
    (hη_supp_in_K_0 : tsupport η ⊆ K_0)
    (k : Fin (Module.finrank ℝ E))
    {R₀ : ℝ} {h : ℝ} (hh : h ≠ 0) (hh_le : |h| ≤ R₀)
    (h_thick : Metric.cthickening |h| K_0 ⊆
      chartTargetEuclid (I := I) (M := M) α) :
    (∫ y in Metric.cthickening |h| K_0,
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramOnEuclid (I := I) g α i j y *
              D.weak_partial i y *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k (-h)
                (fun z => (η z) ^ 2 *
                  DifferentialGeometry.Analysis.Sobolev.diffQuot
                    (d := Module.finrank ℝ E) k h (D.weak_partial j) z +
                  2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) *
                    DifferentialGeometry.Analysis.Sobolev.diffQuot
                      (d := Module.finrank ℝ E) k h D.u_chart z) y)
        ∂(volume : Measure EuclN)) +
      (∫ y in Metric.cthickening |h| K_0,
        densityOnEuclid (I := I) g α y * D.u_chart y *
          standardNirenbergTest (d := Module.finrank ℝ E) k h η D.u_chart y
        ∂(volume : Measure EuclN)) =
      ∫ y in Metric.cthickening |h| K_0,
        densityOnEuclid (I := I) g α y * D.f_chart y *
          standardNirenbergTest (d := Module.finrank ℝ E) k h η D.u_chart y
        ∂(volume : Measure EuclN) :=
  variational_identity_at_v_h_unconditional (I := I) (M := M) D
    hK_0_compact hK_0_in hη hη_supp hη_supp_in_K_0 k hh hh_le h_thick

omit [NeZero (Module.finrank ℝ E)] in
private lemma diffQuot_weightedInvGram_weak_partial_expand
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} (α : M)
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (i : Fin (Module.finrank ℝ E)) (k : Fin (Module.finrank ℝ E)) (h : ℝ)
    (j : Fin (Module.finrank ℝ E)) (y : EuclN) :
    DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h
        (fun z => weightedInvGramOnEuclid (I := I) g α i j z *
          D.weak_partial i z) y =
      DifferentialGeometry.Analysis.Sobolev.translate
        (d := Module.finrank ℝ E) k h
        (fun z => weightedInvGramOnEuclid (I := I) g α i j z) y *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h (D.weak_partial i) y +
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h
        (fun z => weightedInvGramOnEuclid (I := I) g α i j z) y *
        D.weak_partial i y :=
  DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.diffQuot_coeff_apply
    (d := Module.finrank ℝ E) k h
    (fun z => weightedInvGramOnEuclid (I := I) g α i j z) (D.weak_partial i) y

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma eta_sq_factor_zero_outside_tsupport
    {η : EuclN → ℝ} (A : EuclN → ℝ) {z : EuclN} (hz : z ∉ tsupport η) :
    (η z)^2 * A z = 0 := by
  have hηz : η z = 0 := image_eq_zero_of_notMem_tsupport hz
  rw [show (η z)^2 = 0 from by rw [hηz]; ring, zero_mul]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma two_eta_partial_factor_zero_outside_tsupport
    {η : EuclN → ℝ} (j : Fin (Module.finrank ℝ E))
    (B A : EuclN → ℝ) {z : EuclN} (hz : z ∉ tsupport η) :
    2 * B z * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) * A z = 0 := by
  have hηz : η z = 0 := image_eq_zero_of_notMem_tsupport hz
  rw [show (η z) = 0 from hηz]
  ring

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma integral_cthickening_eq_integral_K_0
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    {R₀ : ℝ} {h : ℝ} (hh_le : |h| ≤ R₀)
    {η : EuclN → ℝ} (hη_supp_in_K_0 : tsupport η ⊆ K_0)
    {f : EuclN → ℝ}
    (hf_zero_outside_tsupport : ∀ y, y ∉ tsupport η → f y = 0) :
    ∫ y in Metric.cthickening |h| K_0, f y ∂(volume : Measure EuclN) =
      ∫ y in K_0, f y ∂(volume : Measure EuclN) := by
  classical
  have h_thick_compact : IsCompact (Metric.cthickening |h| K_0) :=
    cthickening_K_0_isCompact (E := E) hK_0_compact hh_le
  have h_thick_meas : MeasurableSet (Metric.cthickening |h| K_0) :=
    h_thick_compact.measurableSet
  have hK_0_meas : MeasurableSet K_0 :=
    hK_0_compact.isClosed.measurableSet
  have hK_0_in_thick : K_0 ⊆ Metric.cthickening |h| K_0 :=
    Metric.self_subset_cthickening _
  have h_zero_outside_K_0 : ∀ y, y ∉ K_0 → f y = 0 := by
    intro y hy_not_K_0
    apply hf_zero_outside_tsupport
    intro hy_in_tsupp
    exact hy_not_K_0 (hη_supp_in_K_0 hy_in_tsupp)
  have h_indicator_eq : (Metric.cthickening |h| K_0).indicator f =
      K_0.indicator f := by
    funext y
    by_cases hy_K_0 : y ∈ K_0
    · have hy_thick : y ∈ Metric.cthickening |h| K_0 := hK_0_in_thick hy_K_0
      rw [Set.indicator_of_mem hy_thick, Set.indicator_of_mem hy_K_0]
    · rw [Set.indicator_of_notMem hy_K_0]
      have hfy : f y = 0 := h_zero_outside_K_0 y hy_K_0
      by_cases hy_thick : y ∈ Metric.cthickening |h| K_0
      · rw [Set.indicator_of_mem hy_thick, hfy]
      · rw [Set.indicator_of_notMem hy_thick]
  have h_lhs_eq : ∫ y in Metric.cthickening |h| K_0, f y ∂(volume : Measure EuclN) =
      ∫ y, (Metric.cthickening |h| K_0).indicator f y ∂(volume : Measure EuclN) :=
    (MeasureTheory.integral_indicator h_thick_meas).symm
  have h_rhs_eq : ∫ y in K_0, f y ∂(volume : Measure EuclN) =
      ∫ y, K_0.indicator f y ∂(volume : Measure EuclN) :=
    (MeasureTheory.integral_indicator hK_0_meas).symm
  rw [h_lhs_eq, h_rhs_eq, h_indicator_eq]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma exists_uniform_bound_continuous_compactSupport
    {f : EuclN → ℝ} (hf_cont : Continuous f) (hf_cs : HasCompactSupport f) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |f x| ≤ M := by
  classical
  by_cases hSupp_empty : (tsupport f).Nonempty
  · obtain ⟨xMax, _hxMax_in, hxMax_max⟩ :=
      hf_cs.exists_isMaxOn hSupp_empty hf_cont.abs.continuousOn
    refine ⟨|f xMax|, abs_nonneg _, ?_⟩
    intro x
    by_cases hx : x ∈ tsupport f
    · exact hxMax_max hx
    · have hfx : f x = 0 := image_eq_zero_of_notMem_tsupport hx
      rw [hfx, abs_zero]; exact abs_nonneg _
  · refine ⟨0, le_refl _, ?_⟩
    intro x
    by_cases hx : x ∈ tsupport f
    · exact absurd ⟨x, hx⟩ hSupp_empty
    · have hfx : f x = 0 := image_eq_zero_of_notMem_tsupport hx
      rw [hfx, abs_zero]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma exists_uniform_bound_on_compact
    {f : EuclN → ℝ} {K : Set EuclN} (hf_cont : ContinuousOn f K)
    (hK_compact : IsCompact K) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ K, |f x| ≤ M := by
  classical
  by_cases hK_empty : K = ∅
  · refine ⟨0, le_refl _, ?_⟩
    intro x hx
    rw [hK_empty] at hx
    exact absurd hx (Set.notMem_empty x)
  have hKne : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hK_empty
  have h_abs_cont : ContinuousOn (fun x => |f x|) K := hf_cont.abs
  obtain ⟨xMax, _hxMax_in, h_max_eq⟩ := hK_compact.exists_isMaxOn hKne h_abs_cont
  refine ⟨|f xMax|, abs_nonneg _, fun x hx => h_max_eq hx⟩

omit [NeZero (Module.finrank ℝ E)] in
private lemma weakPartial_memLp_K_0
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (i : Fin (Module.finrank ℝ E))
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    (hK_0_in : K_0 ⊆ chartTargetEuclid (I := I) (M := M) α) :
    MemLp (D.weak_partial i) 2 ((volume : Measure EuclN).restrict K_0) :=
  D.weak_partial_locally_memLp i K_0 hK_0_compact hK_0_in

omit [NeZero (Module.finrank ℝ E)] in
private lemma diffQuot_weakPartial_memLp_K_0
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (i : Fin (Module.finrank ℝ E))
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    (k : Fin (Module.finrank ℝ E))
    {R₀ : ℝ} {h : ℝ} (hh : h ≠ 0) (hh_le : |h| ≤ R₀)
    (h_thick : Metric.cthickening |h| K_0 ⊆
      chartTargetEuclid (I := I) (M := M) α) :
    MemLp (DifferentialGeometry.Analysis.Sobolev.diffQuot
      (d := Module.finrank ℝ E) k h (D.weak_partial i)) 2
      ((volume : Measure EuclN).restrict K_0) := by
  classical
  set wp_i_ext : EuclN → ℝ :=
    (Metric.cthickening |h| K_0).indicator (D.weak_partial i) with hwp_i_ext_def
  have hwp_i_ext_lp : MemLp wp_i_ext 2 (volume : Measure EuclN) :=
    weakPartial_indicator_memLp (I := I) (M := M) D hK_0_compact hh_le h_thick i
  have hdq_wp_i_ext_lp : MemLp
      (DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h wp_i_ext) 2
      (volume : Measure EuclN) :=
    memLp_diffQuot_of_memLp_local hwp_i_ext_lp k hh
  have hdq_wp_i_ext_lp_restrict : MemLp
      (DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h wp_i_ext) 2
      ((volume : Measure EuclN).restrict K_0) :=
    hdq_wp_i_ext_lp.restrict K_0
  have h_pt_eq : ∀ y ∈ K_0,
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h (D.weak_partial i) y =
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h wp_i_ext y := by
    intro y hy_K_0
    have hy_thick : y ∈ Metric.cthickening |h| K_0 :=
      Metric.self_subset_cthickening _ hy_K_0
    have hy_shift : y + h • EuclideanSpace.single k 1 ∈ Metric.cthickening |h| K_0 := by
      refine Metric.mem_cthickening_of_dist_le _ y |h| K_0 hy_K_0 ?_
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul]
      simp [Real.norm_eq_abs]
    rw [DifferentialGeometry.Analysis.Sobolev.diffQuot_apply_of_ne
      (d := Module.finrank ℝ E) k hh]
    rw [DifferentialGeometry.Analysis.Sobolev.diffQuot_apply_of_ne
      (d := Module.finrank ℝ E) k hh]
    change (D.weak_partial i (y + h • EuclideanSpace.single k 1) -
        D.weak_partial i y) / h =
      (wp_i_ext (y + h • EuclideanSpace.single k 1) - wp_i_ext y) / h
    rw [show wp_i_ext (y + h • EuclideanSpace.single k 1) =
        D.weak_partial i (y + h • EuclideanSpace.single k 1) from
        Set.indicator_of_mem hy_shift _,
      show wp_i_ext y = D.weak_partial i y from
        Set.indicator_of_mem hy_thick _]
  have hK_0_meas : MeasurableSet K_0 := hK_0_compact.isClosed.measurableSet
  have h_ae_eq :
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h wp_i_ext =ᵐ[
        (volume : Measure EuclN).restrict K_0]
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h (D.weak_partial i) := by
    refine (MeasureTheory.ae_restrict_iff' hK_0_meas).mpr ?_
    refine Filter.Eventually.of_forall ?_
    intro y hy
    exact (h_pt_eq y hy).symm
  exact MemLp.ae_eq h_ae_eq hdq_wp_i_ext_lp_restrict

omit [NeZero (Module.finrank ℝ E)] in
private lemma diffQuot_uChart_memLp_K_0
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    (k : Fin (Module.finrank ℝ E))
    {R₀ : ℝ} {h : ℝ} (hh : h ≠ 0) (hh_le : |h| ≤ R₀)
    (h_thick : Metric.cthickening |h| K_0 ⊆
      chartTargetEuclid (I := I) (M := M) α) :
    MemLp (DifferentialGeometry.Analysis.Sobolev.diffQuot
      (d := Module.finrank ℝ E) k h D.u_chart) 2
      ((volume : Measure EuclN).restrict K_0) := by
  classical
  set u_ext : EuclN → ℝ :=
    (Metric.cthickening |h| K_0).indicator D.u_chart with hu_ext_def
  have hu_ext_lp : MemLp u_ext 2 (volume : Measure EuclN) :=
    uChart_indicator_memLp (I := I) (M := M) D hK_0_compact hh_le h_thick
  have hdq_u_ext_lp : MemLp
      (DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h u_ext) 2
      (volume : Measure EuclN) :=
    memLp_diffQuot_of_memLp_local hu_ext_lp k hh
  have hdq_u_ext_lp_restrict : MemLp
      (DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h u_ext) 2
      ((volume : Measure EuclN).restrict K_0) :=
    hdq_u_ext_lp.restrict K_0
  have h_pt_eq : ∀ y ∈ K_0,
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h D.u_chart y =
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h u_ext y := by
    intro y hy_K_0
    have hy_thick : y ∈ Metric.cthickening |h| K_0 :=
      Metric.self_subset_cthickening _ hy_K_0
    have hy_shift : y + h • EuclideanSpace.single k 1 ∈ Metric.cthickening |h| K_0 := by
      refine Metric.mem_cthickening_of_dist_le _ y |h| K_0 hy_K_0 ?_
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul]
      simp [Real.norm_eq_abs]
    rw [DifferentialGeometry.Analysis.Sobolev.diffQuot_apply_of_ne
      (d := Module.finrank ℝ E) k hh]
    rw [DifferentialGeometry.Analysis.Sobolev.diffQuot_apply_of_ne
      (d := Module.finrank ℝ E) k hh]
    change (D.u_chart (y + h • EuclideanSpace.single k 1) - D.u_chart y) / h =
      (u_ext (y + h • EuclideanSpace.single k 1) - u_ext y) / h
    rw [show u_ext (y + h • EuclideanSpace.single k 1) =
        D.u_chart (y + h • EuclideanSpace.single k 1) from
        Set.indicator_of_mem hy_shift _,
      show u_ext y = D.u_chart y from
        Set.indicator_of_mem hy_thick _]
  have hK_0_meas : MeasurableSet K_0 := hK_0_compact.isClosed.measurableSet
  have h_ae_eq :
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h u_ext =ᵐ[
        (volume : Measure EuclN).restrict K_0]
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h D.u_chart := by
    refine (MeasureTheory.ae_restrict_iff' hK_0_meas).mpr ?_
    refine Filter.Eventually.of_forall ?_
    intro y hy
    exact (h_pt_eq y hy).symm
  exact MemLp.ae_eq h_ae_eq hdq_u_ext_lp_restrict


omit [NeZero (Module.finrank ℝ E)] in
private lemma translate_weightedInvGramOnEuclid_continuousOn_K_0
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E))
    {K_0 : Set EuclN} (k : Fin (Module.finrank ℝ E))
    {R₀ : ℝ} {h : ℝ} (_hh_le : |h| ≤ R₀)
    (h_thick : Metric.cthickening |h| K_0 ⊆
      chartTargetEuclid (I := I) (M := M) α) :
    ContinuousOn (DifferentialGeometry.Analysis.Sobolev.translate
      (d := Module.finrank ℝ E) k h
      (fun y => weightedInvGramOnEuclid (I := I) g α i j y)) K_0 := by
  classical
  have h_w_cont : ContinuousOn (weightedInvGramOnEuclid (I := I) g α i j)
      (chartTargetEuclid (I := I) (M := M) α) :=
    (weightedInvGramOnEuclid_contDiffOn (I := I) g α i j).continuousOn
  have h_translate_cont : Continuous
      (fun y : EuclN => y + h • EuclideanSpace.single k 1) :=
    continuous_id.add continuous_const
  have h_maps : MapsTo (fun y : EuclN => y + h • EuclideanSpace.single k 1) K_0
      (chartTargetEuclid (I := I) (M := M) α) := by
    intro y hy_K_0
    have h_in_thick : y + h • EuclideanSpace.single k 1 ∈
        Metric.cthickening |h| K_0 := by
      refine Metric.mem_cthickening_of_dist_le _ y |h| K_0 hy_K_0 ?_
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul]
      simp [Real.norm_eq_abs]
    exact h_thick h_in_thick
  exact h_w_cont.comp h_translate_cont.continuousOn h_maps

omit [NeZero (Module.finrank ℝ E)] in
private lemma diffQuot_weightedInvGramOnEuclid_continuousOn_K_0
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E))
    {K_0 : Set EuclN} (k : Fin (Module.finrank ℝ E))
    {R₀ : ℝ} {h : ℝ} (hh_le : |h| ≤ R₀)
    (h_thick : Metric.cthickening |h| K_0 ⊆
      chartTargetEuclid (I := I) (M := M) α) :
    ContinuousOn (DifferentialGeometry.Analysis.Sobolev.diffQuot
      (d := Module.finrank ℝ E) k h
      (fun y => weightedInvGramOnEuclid (I := I) g α i j y)) K_0 := by
  classical
  by_cases hh : h = 0
  · subst hh
    have h_dq_zero : DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k 0
        (fun y => weightedInvGramOnEuclid (I := I) g α i j y) =
        (fun _ : EuclN => (0 : ℝ)) := by
      funext x
      simp [DifferentialGeometry.Analysis.Sobolev.diffQuot]
    rw [h_dq_zero]
    exact continuousOn_const
  have h_dq_eq : DifferentialGeometry.Analysis.Sobolev.diffQuot
      (d := Module.finrank ℝ E) k h
      (fun y => weightedInvGramOnEuclid (I := I) g α i j y) =
      fun y => (weightedInvGramOnEuclid (I := I) g α i j
        (y + h • EuclideanSpace.single k 1) -
        weightedInvGramOnEuclid (I := I) g α i j y) / h := by
    funext y
    rw [DifferentialGeometry.Analysis.Sobolev.diffQuot_apply_of_ne
      (d := Module.finrank ℝ E) k hh]
  rw [h_dq_eq]
  have h_translate_cont :=
    translate_weightedInvGramOnEuclid_continuousOn_K_0 (I := I) (M := M)
      g α i j (k := k) (h := h) hh_le h_thick
  have h_w_cont : ContinuousOn (weightedInvGramOnEuclid (I := I) g α i j)
      (chartTargetEuclid (I := I) (M := M) α) :=
    (weightedInvGramOnEuclid_contDiffOn (I := I) g α i j).continuousOn
  have hK_0_in : K_0 ⊆ chartTargetEuclid (I := I) (M := M) α := by
    intro y hy
    exact h_thick (Metric.self_subset_cthickening _ hy)
  have h_w_cont_K_0 : ContinuousOn (weightedInvGramOnEuclid (I := I) g α i j) K_0 :=
    h_w_cont.mono hK_0_in
  exact (h_translate_cont.sub h_w_cont_K_0).div_const h

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma integrable_bdd_bdd_L2_L2
    {c bdd_factor F1 F2 : EuclN → ℝ}
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    (h_c_cont : ContinuousOn c K_0)
    (h_bdd_cont : Continuous bdd_factor)
    (hF1_lp : MemLp F1 2 ((volume : Measure EuclN).restrict K_0))
    (hF2_lp : MemLp F2 2 ((volume : Measure EuclN).restrict K_0)) :
    Integrable (fun y => c y * bdd_factor y * F1 y * F2 y)
      ((volume : Measure EuclN).restrict K_0) := by
  classical
  haveI : ENNReal.HolderTriple (2 : ℝ≥0∞) 2 1 := by
    constructor
    rw [show (1 : ℝ≥0∞)⁻¹ = 1 from inv_one]
    rw [ENNReal.inv_two_add_inv_two]
  have hK_0_meas : MeasurableSet K_0 := hK_0_compact.isClosed.measurableSet
  obtain ⟨M_c, _hM_c_nn, hM_c_bd⟩ :=
    exists_uniform_bound_on_compact h_c_cont hK_0_compact
  obtain ⟨M_b, _hM_b_nn, hM_b_bd⟩ :=
    exists_uniform_bound_on_compact h_bdd_cont.continuousOn hK_0_compact
  have h_F1F2_int : Integrable (fun y => F1 y * F2 y)
      ((volume : Measure EuclN).restrict K_0) := by
    have h := MemLp.integrable_mul (μ :=
      (volume : Measure EuclN).restrict K_0)
      (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)) hF1_lp hF2_lp
    simpa using h
  have h_bdd_aesm : AEStronglyMeasurable bdd_factor
      ((volume : Measure EuclN).restrict K_0) :=
    h_bdd_cont.aestronglyMeasurable.mono_measure
      (MeasureTheory.Measure.restrict_le_self)
  have h_c_aesm : AEStronglyMeasurable c
      ((volume : Measure EuclN).restrict K_0) :=
    h_c_cont.aestronglyMeasurable_of_isCompact hK_0_compact hK_0_meas
  have h_c_b_aesm : AEStronglyMeasurable (fun y => c y * bdd_factor y)
      ((volume : Measure EuclN).restrict K_0) :=
    h_c_aesm.mul h_bdd_aesm
  have h_c_b_bound : ∀ᵐ y ∂((volume : Measure EuclN).restrict K_0),
      ‖c y * bdd_factor y‖ ≤ M_c * M_b := by
    rw [ae_restrict_iff' hK_0_meas]
    refine Filter.Eventually.of_forall ?_
    intro y hy
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hM_c_bd y hy) (hM_b_bd y (by trivial))
      (abs_nonneg _) (le_trans (abs_nonneg _) (hM_c_bd y hy))
  have h_combine : Integrable (fun y =>
      c y * bdd_factor y * (F1 y * F2 y))
      ((volume : Measure EuclN).restrict K_0) :=
    h_F1F2_int.bdd_mul h_c_b_aesm h_c_b_bound
  have h_eq : (fun y => c y * bdd_factor y * F1 y * F2 y) =
      (fun y => c y * bdd_factor y * (F1 y * F2 y)) := by
    funext y; ring
  rw [h_eq]
  exact h_combine

omit [NeZero (Module.finrank ℝ E)] in
private lemma translatedCoeff_cutoffSq_diffQuotPartial_diffQuotPartial_integrable_K_0
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    {η : EuclN → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (k : Fin (Module.finrank ℝ E))
    {R₀ : ℝ} {h : ℝ} (hh : h ≠ 0) (hh_le : |h| ≤ R₀)
    (h_thick : Metric.cthickening |h| K_0 ⊆
      chartTargetEuclid (I := I) (M := M) α)
    (i j : Fin (Module.finrank ℝ E)) :
    Integrable (fun y =>
      DifferentialGeometry.Analysis.Sobolev.translate
        (d := Module.finrank ℝ E) k h
        (fun z => weightedInvGramOnEuclid (I := I) g α i j z) y *
      (η y) ^ 2 *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h (D.weak_partial i) y *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h (D.weak_partial j) y)
      ((volume : Measure EuclN).restrict K_0) := by
  have h_τw_cont := translate_weightedInvGramOnEuclid_continuousOn_K_0
    (I := I) (M := M) g α i j (k := k) (h := h) hh_le h_thick
  have hη_sq_cont : Continuous (fun y : EuclN => (η y) ^ 2) :=
    hη.continuous.pow 2
  have hdq_wp_i_lp := diffQuot_weakPartial_memLp_K_0 (I := I) (M := M) D i
    hK_0_compact k hh hh_le h_thick
  have hdq_wp_j_lp := diffQuot_weakPartial_memLp_K_0 (I := I) (M := M) D j
    hK_0_compact k hh hh_le h_thick
  exact integrable_bdd_bdd_L2_L2 hK_0_compact h_τw_cont hη_sq_cont
    hdq_wp_i_lp hdq_wp_j_lp

omit [NeZero (Module.finrank ℝ E)] in
private lemma translatedCoeff_cutoffDeriv_diffQuotPartial_diffQuotUChart_integrable_K_0
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    {η : EuclN → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (k : Fin (Module.finrank ℝ E))
    {R₀ : ℝ} {h : ℝ} (hh : h ≠ 0) (hh_le : |h| ≤ R₀)
    (h_thick : Metric.cthickening |h| K_0 ⊆
      chartTargetEuclid (I := I) (M := M) α)
    (i j : Fin (Module.finrank ℝ E)) :
    Integrable (fun y =>
      2 *
      DifferentialGeometry.Analysis.Sobolev.translate
        (d := Module.finrank ℝ E) k h
        (fun z => weightedInvGramOnEuclid (I := I) g α i j z) y *
      η y * ((fderiv ℝ η y) (EuclideanSpace.single j 1)) *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h (D.weak_partial i) y *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h D.u_chart y)
      ((volume : Measure EuclN).restrict K_0) := by
  classical
  have h_τw_cont := translate_weightedInvGramOnEuclid_continuousOn_K_0
    (I := I) (M := M) g α i j (k := k) (h := h) hh_le h_thick
  have h_top_ne_zero : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by decide
  have hη_factor_cont : Continuous (fun y : EuclN =>
      (2 : ℝ) * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1)) :=
    (continuous_const.mul hη.continuous).mul
      ((hη.continuous_fderiv h_top_ne_zero).clm_apply continuous_const)
  have hdq_wp_i_lp := diffQuot_weakPartial_memLp_K_0 (I := I) (M := M) D i
    hK_0_compact k hh hh_le h_thick
  have hdq_u_lp := diffQuot_uChart_memLp_K_0 (I := I) (M := M) D
    hK_0_compact k hh hh_le h_thick
  have h_int := integrable_bdd_bdd_L2_L2 hK_0_compact h_τw_cont hη_factor_cont
    hdq_wp_i_lp hdq_u_lp
  have h_eq : (fun y =>
      DifferentialGeometry.Analysis.Sobolev.translate
        (d := Module.finrank ℝ E) k h
        (fun z => weightedInvGramOnEuclid (I := I) g α i j z) y *
      ((2 : ℝ) * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1)) *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h (D.weak_partial i) y *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h D.u_chart y) =
    (fun y =>
      2 *
      DifferentialGeometry.Analysis.Sobolev.translate
        (d := Module.finrank ℝ E) k h
        (fun z => weightedInvGramOnEuclid (I := I) g α i j z) y *
      η y * ((fderiv ℝ η y) (EuclideanSpace.single j 1)) *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h (D.weak_partial i) y *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h D.u_chart y) := by
    funext y; ring
  rw [← h_eq]
  exact h_int

omit [NeZero (Module.finrank ℝ E)] in
private lemma diffQuotCoeff_cutoffSq_partial_diffQuotPartial_integrable_K_0
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    (hK_0_in : K_0 ⊆ chartTargetEuclid (I := I) (M := M) α)
    {η : EuclN → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (k : Fin (Module.finrank ℝ E))
    {R₀ : ℝ} {h : ℝ} (hh : h ≠ 0) (hh_le : |h| ≤ R₀)
    (h_thick : Metric.cthickening |h| K_0 ⊆
      chartTargetEuclid (I := I) (M := M) α)
    (i j : Fin (Module.finrank ℝ E)) :
    Integrable (fun y =>
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h
        (fun z => weightedInvGramOnEuclid (I := I) g α i j z) y *
      (η y) ^ 2 *
      D.weak_partial i y *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h (D.weak_partial j) y)
      ((volume : Measure EuclN).restrict K_0) := by
  have h_dqw_cont := diffQuot_weightedInvGramOnEuclid_continuousOn_K_0
    (I := I) (M := M) g α i j (k := k) (h := h) hh_le h_thick
  have hη_sq_cont : Continuous (fun y : EuclN => (η y) ^ 2) :=
    hη.continuous.pow 2
  have hwp_i_lp := weakPartial_memLp_K_0 (I := I) (M := M) D i
    hK_0_compact hK_0_in
  have hdq_wp_j_lp := diffQuot_weakPartial_memLp_K_0 (I := I) (M := M) D j
    hK_0_compact k hh hh_le h_thick
  exact integrable_bdd_bdd_L2_L2 hK_0_compact h_dqw_cont hη_sq_cont
    hwp_i_lp hdq_wp_j_lp

omit [NeZero (Module.finrank ℝ E)] in
private lemma diffQuotCoeff_cutoffDeriv_partial_diffQuotUChart_integrable_K_0
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    (hK_0_in : K_0 ⊆ chartTargetEuclid (I := I) (M := M) α)
    {η : EuclN → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (k : Fin (Module.finrank ℝ E))
    {R₀ : ℝ} {h : ℝ} (hh : h ≠ 0) (hh_le : |h| ≤ R₀)
    (h_thick : Metric.cthickening |h| K_0 ⊆
      chartTargetEuclid (I := I) (M := M) α)
    (i j : Fin (Module.finrank ℝ E)) :
    Integrable (fun y =>
      2 *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h
        (fun z => weightedInvGramOnEuclid (I := I) g α i j z) y *
      η y * ((fderiv ℝ η y) (EuclideanSpace.single j 1)) *
      D.weak_partial i y *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h D.u_chart y)
      ((volume : Measure EuclN).restrict K_0) := by
  classical
  have h_dqw_cont := diffQuot_weightedInvGramOnEuclid_continuousOn_K_0
    (I := I) (M := M) g α i j (k := k) (h := h) hh_le h_thick
  have h_top_ne_zero : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by decide
  have hη_factor_cont : Continuous (fun y : EuclN =>
      (2 : ℝ) * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1)) :=
    (continuous_const.mul hη.continuous).mul
      ((hη.continuous_fderiv h_top_ne_zero).clm_apply continuous_const)
  have hwp_i_lp := weakPartial_memLp_K_0 (I := I) (M := M) D i
    hK_0_compact hK_0_in
  have hdq_u_lp := diffQuot_uChart_memLp_K_0 (I := I) (M := M) D
    hK_0_compact k hh hh_le h_thick
  have h_int := integrable_bdd_bdd_L2_L2 hK_0_compact h_dqw_cont hη_factor_cont
    hwp_i_lp hdq_u_lp
  have h_eq : (fun y =>
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h
        (fun z => weightedInvGramOnEuclid (I := I) g α i j z) y *
      ((2 : ℝ) * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1)) *
      D.weak_partial i y *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h D.u_chart y) =
    (fun y =>
      2 *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h
        (fun z => weightedInvGramOnEuclid (I := I) g α i j z) y *
      η y * ((fderiv ℝ η y) (EuclideanSpace.single j 1)) *
      D.weak_partial i y *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h D.u_chart y) := by
    funext y; ring
  rw [← h_eq]
  exact h_int


omit [NeZero (Module.finrank ℝ E)] in
private lemma principal_post_ibp_integral_eq_symbolic
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    (hK_0_in : K_0 ⊆ chartTargetEuclid (I := I) (M := M) α)
    {η : EuclN → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (_hη_supp : HasCompactSupport η)
    (hη_supp_in_K_0 : tsupport η ⊆ K_0)
    (k : Fin (Module.finrank ℝ E))
    {R₀ : ℝ} {h : ℝ} (hh : h ≠ 0) (hh_le : |h| ≤ R₀)
    (h_thick : Metric.cthickening |h| K_0 ⊆
      chartTargetEuclid (I := I) (M := M) α) :
    ∫ y in Metric.cthickening |h| K_0,
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h
              (fun z => weightedInvGramOnEuclid (I := I) g α i j z *
                D.weak_partial i z) y *
            ((η y) ^ 2 *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h (D.weak_partial j) y +
              2 * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1) *
                DifferentialGeometry.Analysis.Sobolev.diffQuot
                  (d := Module.finrank ℝ E) k h D.u_chart y))
        ∂(volume : Measure EuclN) =
      principalTerm_chartBilinear (I := I) (M := M) D K_0 η k h
        + cross_1_term_chartBilinear (I := I) (M := M) D K_0 η k h
        + cross_2_term_chartBilinear (I := I) (M := M) D K_0 η k h
        + cross_3_term_chartBilinear (I := I) (M := M) D K_0 η k h := by
  classical
  set T1 : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → EuclN → ℝ :=
    fun i j y => DifferentialGeometry.Analysis.Sobolev.translate
      (d := Module.finrank ℝ E) k h
      (fun z => weightedInvGramOnEuclid (I := I) g α i j z) y *
      (η y) ^ 2 *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h (D.weak_partial i) y *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h (D.weak_partial j) y with hT1_def
  set T2 : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → EuclN → ℝ :=
    fun i j y => 2 *
      DifferentialGeometry.Analysis.Sobolev.translate
        (d := Module.finrank ℝ E) k h
        (fun z => weightedInvGramOnEuclid (I := I) g α i j z) y *
      η y * ((fderiv ℝ η y) (EuclideanSpace.single j 1)) *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h (D.weak_partial i) y *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h D.u_chart y with hT2_def
  set T3 : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → EuclN → ℝ :=
    fun i j y => DifferentialGeometry.Analysis.Sobolev.diffQuot
      (d := Module.finrank ℝ E) k h
      (fun z => weightedInvGramOnEuclid (I := I) g α i j z) y *
      (η y) ^ 2 *
      D.weak_partial i y *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h (D.weak_partial j) y with hT3_def
  set T4 : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → EuclN → ℝ :=
    fun i j y => 2 *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h
        (fun z => weightedInvGramOnEuclid (I := I) g α i j z) y *
      η y * ((fderiv ℝ η y) (EuclideanSpace.single j 1)) *
      D.weak_partial i y *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h D.u_chart y with hT4_def
  set LHS_ij : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → EuclN → ℝ :=
    fun i j y => DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h
        (fun z => weightedInvGramOnEuclid (I := I) g α i j z *
          D.weak_partial i z) y *
      ((η y) ^ 2 *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h (D.weak_partial j) y +
        2 * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1) *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h D.u_chart y) with hLHS_def
  have h_pointwise_expand : ∀ i j y,
      LHS_ij i j y = T1 i j y + T2 i j y + T3 i j y + T4 i j y := by
    intro i j y
    change DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h
        (fun z => weightedInvGramOnEuclid (I := I) g α i j z *
          D.weak_partial i z) y *
      ((η y) ^ 2 *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h (D.weak_partial j) y +
        2 * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1) *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h D.u_chart y) =
      T1 i j y + T2 i j y + T3 i j y + T4 i j y
    rw [diffQuot_weightedInvGram_weak_partial_expand (I := I) (M := M)
      α D i k h j y]
    change (DifferentialGeometry.Analysis.Sobolev.translate
        (d := Module.finrank ℝ E) k h
        (fun z => weightedInvGramOnEuclid (I := I) g α i j z) y *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h (D.weak_partial i) y +
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h
        (fun z => weightedInvGramOnEuclid (I := I) g α i j z) y *
        D.weak_partial i y) *
      ((η y) ^ 2 *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h (D.weak_partial j) y +
        2 * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1) *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h D.u_chart y) =
      (DifferentialGeometry.Analysis.Sobolev.translate
        (d := Module.finrank ℝ E) k h
        (fun z => weightedInvGramOnEuclid (I := I) g α i j z) y *
      (η y) ^ 2 *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h (D.weak_partial i) y *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h (D.weak_partial j) y) +
      (2 *
      DifferentialGeometry.Analysis.Sobolev.translate
        (d := Module.finrank ℝ E) k h
        (fun z => weightedInvGramOnEuclid (I := I) g α i j z) y *
      η y * ((fderiv ℝ η y) (EuclideanSpace.single j 1)) *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h (D.weak_partial i) y *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h D.u_chart y) +
      (DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h
        (fun z => weightedInvGramOnEuclid (I := I) g α i j z) y *
      (η y) ^ 2 *
      D.weak_partial i y *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h (D.weak_partial j) y) +
      (2 *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h
        (fun z => weightedInvGramOnEuclid (I := I) g α i j z) y *
      η y * ((fderiv ℝ η y) (EuclideanSpace.single j 1)) *
      D.weak_partial i y *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h D.u_chart y)
    ring
  have h_sum_expand : ∀ y, (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E), LHS_ij i j y) =
      (∑ i, ∑ j, T1 i j y) + (∑ i, ∑ j, T2 i j y) +
      (∑ i, ∑ j, T3 i j y) + (∑ i, ∑ j, T4 i j y) := by
    intro y
    have h_per_ij : ∀ i, (∑ j : Fin (Module.finrank ℝ E), LHS_ij i j y) =
        (∑ j, T1 i j y) + (∑ j, T2 i j y) + (∑ j, T3 i j y) + (∑ j, T4 i j y) := by
      intro i
      rw [show (fun (j : Fin (Module.finrank ℝ E)) => LHS_ij i j y) =
          (fun j => T1 i j y + T2 i j y + T3 i j y + T4 i j y) from
          funext (fun j => h_pointwise_expand i j y)]
      simp [Finset.sum_add_distrib]
    rw [show (fun (i : Fin (Module.finrank ℝ E)) =>
        ∑ j : Fin (Module.finrank ℝ E), LHS_ij i j y) =
        (fun i => (∑ j, T1 i j y) + (∑ j, T2 i j y) +
          (∑ j, T3 i j y) + (∑ j, T4 i j y)) from
        funext h_per_ij]
    simp [Finset.sum_add_distrib]
  have h_int_expand :
      ∫ y in Metric.cthickening |h| K_0,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E), LHS_ij i j y)
          ∂(volume : Measure EuclN) =
      ∫ y in Metric.cthickening |h| K_0,
          ((∑ i, ∑ j, T1 i j y) + (∑ i, ∑ j, T2 i j y) +
          (∑ i, ∑ j, T3 i j y) + (∑ i, ∑ j, T4 i j y))
          ∂(volume : Measure EuclN) := by
    refine integral_congr_ae ?_
    refine Filter.Eventually.of_forall ?_
    intro y
    exact h_sum_expand y
  have h_T_zero : ∀ y ∉ tsupport η,
      ((∑ i, ∑ j, T1 i j y) + (∑ i, ∑ j, T2 i j y) +
      (∑ i, ∑ j, T3 i j y) + (∑ i, ∑ j, T4 i j y)) = 0 := by
    intro y hy
    have hηy : η y = 0 := image_eq_zero_of_notMem_tsupport hy
    have h1 : ∀ i j, T1 i j y = 0 := by
      intro i j
      change DifferentialGeometry.Analysis.Sobolev.translate
        (d := Module.finrank ℝ E) k h
        (fun z => weightedInvGramOnEuclid (I := I) g α i j z) y *
      (η y) ^ 2 *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h (D.weak_partial i) y *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h (D.weak_partial j) y = 0
      rw [show (η y) ^ 2 = 0 from by rw [hηy]; ring]
      ring
    have h2 : ∀ i j, T2 i j y = 0 := by
      intro i j
      change 2 *
        DifferentialGeometry.Analysis.Sobolev.translate
          (d := Module.finrank ℝ E) k h
          (fun z => weightedInvGramOnEuclid (I := I) g α i j z) y *
        η y * ((fderiv ℝ η y) (EuclideanSpace.single j 1)) *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h (D.weak_partial i) y *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h D.u_chart y = 0
      rw [show η y = 0 from hηy]
      ring
    have h3 : ∀ i j, T3 i j y = 0 := by
      intro i j
      change DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h
        (fun z => weightedInvGramOnEuclid (I := I) g α i j z) y *
      (η y) ^ 2 *
      D.weak_partial i y *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h (D.weak_partial j) y = 0
      rw [show (η y) ^ 2 = 0 from by rw [hηy]; ring]
      ring
    have h4 : ∀ i j, T4 i j y = 0 := by
      intro i j
      change 2 *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h
          (fun z => weightedInvGramOnEuclid (I := I) g α i j z) y *
        η y * ((fderiv ℝ η y) (EuclideanSpace.single j 1)) *
        D.weak_partial i y *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h D.u_chart y = 0
      rw [show η y = 0 from hηy]
      ring
    rw [show (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E), T1 i j y) = 0 from by
        apply Finset.sum_eq_zero; intros i _
        apply Finset.sum_eq_zero; intros j _
        exact h1 i j]
    rw [show (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E), T2 i j y) = 0 from by
        apply Finset.sum_eq_zero; intros i _
        apply Finset.sum_eq_zero; intros j _
        exact h2 i j]
    rw [show (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E), T3 i j y) = 0 from by
        apply Finset.sum_eq_zero; intros i _
        apply Finset.sum_eq_zero; intros j _
        exact h3 i j]
    rw [show (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E), T4 i j y) = 0 from by
        apply Finset.sum_eq_zero; intros i _
        apply Finset.sum_eq_zero; intros j _
        exact h4 i j]
    ring
  have h_thick_to_K_0 :
      ∫ y in Metric.cthickening |h| K_0,
          ((∑ i, ∑ j, T1 i j y) + (∑ i, ∑ j, T2 i j y) +
          (∑ i, ∑ j, T3 i j y) + (∑ i, ∑ j, T4 i j y))
          ∂(volume : Measure EuclN) =
      ∫ y in K_0,
          ((∑ i, ∑ j, T1 i j y) + (∑ i, ∑ j, T2 i j y) +
          (∑ i, ∑ j, T3 i j y) + (∑ i, ∑ j, T4 i j y))
          ∂(volume : Measure EuclN) :=
    integral_cthickening_eq_integral_K_0 (E := E) hK_0_compact hh_le
      hη_supp_in_K_0 h_T_zero
  have hT1_ij_int : ∀ i j, Integrable (T1 i j)
      ((volume : Measure EuclN).restrict K_0) := fun i j =>
    translatedCoeff_cutoffSq_diffQuotPartial_diffQuotPartial_integrable_K_0 (I := I) (M := M) D hK_0_compact hη k hh hh_le
      h_thick i j
  have hT2_ij_int : ∀ i j, Integrable (T2 i j)
      ((volume : Measure EuclN).restrict K_0) := fun i j =>
    translatedCoeff_cutoffDeriv_diffQuotPartial_diffQuotUChart_integrable_K_0 (I := I) (M := M) D hK_0_compact hη k hh hh_le
      h_thick i j
  have hT3_ij_int : ∀ i j, Integrable (T3 i j)
      ((volume : Measure EuclN).restrict K_0) := fun i j =>
    diffQuotCoeff_cutoffSq_partial_diffQuotPartial_integrable_K_0 (I := I) (M := M) D hK_0_compact hK_0_in hη k hh hh_le
      h_thick i j
  have hT4_ij_int : ∀ i j, Integrable (T4 i j)
      ((volume : Measure EuclN).restrict K_0) := fun i j =>
    diffQuotCoeff_cutoffDeriv_partial_diffQuotUChart_integrable_K_0 (I := I) (M := M) D hK_0_compact hK_0_in hη k hh hh_le
      h_thick i j
  have hT1_sum_int : Integrable (fun y => ∑ i, ∑ j, T1 i j y)
      ((volume : Measure EuclN).restrict K_0) := by
    refine integrable_finset_sum _ ?_
    intro i _
    exact integrable_finset_sum _ (fun j _ => hT1_ij_int i j)
  have hT2_sum_int : Integrable (fun y => ∑ i, ∑ j, T2 i j y)
      ((volume : Measure EuclN).restrict K_0) := by
    refine integrable_finset_sum _ ?_
    intro i _
    exact integrable_finset_sum _ (fun j _ => hT2_ij_int i j)
  have hT3_sum_int : Integrable (fun y => ∑ i, ∑ j, T3 i j y)
      ((volume : Measure EuclN).restrict K_0) := by
    refine integrable_finset_sum _ ?_
    intro i _
    exact integrable_finset_sum _ (fun j _ => hT3_ij_int i j)
  have hT4_sum_int : Integrable (fun y => ∑ i, ∑ j, T4 i j y)
      ((volume : Measure EuclN).restrict K_0) := by
    refine integrable_finset_sum _ ?_
    intro i _
    exact integrable_finset_sum _ (fun j _ => hT4_ij_int i j)
  have h_split :
      ∫ y in K_0,
          ((∑ i, ∑ j, T1 i j y) + (∑ i, ∑ j, T2 i j y) +
          (∑ i, ∑ j, T3 i j y) + (∑ i, ∑ j, T4 i j y))
          ∂(volume : Measure EuclN) =
      ∫ y in K_0, (∑ i, ∑ j, T1 i j y) ∂(volume : Measure EuclN) +
      ∫ y in K_0, (∑ i, ∑ j, T2 i j y) ∂(volume : Measure EuclN) +
      ∫ y in K_0, (∑ i, ∑ j, T3 i j y) ∂(volume : Measure EuclN) +
      ∫ y in K_0, (∑ i, ∑ j, T4 i j y) ∂(volume : Measure EuclN) := by
    have hT12_int : Integrable (fun y => (∑ i, ∑ j, T1 i j y) +
        (∑ i, ∑ j, T2 i j y)) ((volume : Measure EuclN).restrict K_0) :=
      hT1_sum_int.add hT2_sum_int
    have hT123_int : Integrable (fun y => (∑ i, ∑ j, T1 i j y) +
        (∑ i, ∑ j, T2 i j y) + (∑ i, ∑ j, T3 i j y))
        ((volume : Measure EuclN).restrict K_0) :=
      hT12_int.add hT3_sum_int
    rw [integral_add hT123_int hT4_sum_int]
    rw [integral_add hT12_int hT3_sum_int]
    rw [integral_add hT1_sum_int hT2_sum_int]
  have h_principalTerm : ∫ y in K_0, (∑ i, ∑ j, T1 i j y)
      ∂(volume : Measure EuclN) =
      principalTerm_chartBilinear (I := I) (M := M) D K_0 η k h := by
    rfl
  have h_cross1 : ∫ y in K_0, (∑ i, ∑ j, T2 i j y)
      ∂(volume : Measure EuclN) =
      cross_1_term_chartBilinear (I := I) (M := M) D K_0 η k h := by
    rw [show (fun y : EuclN => ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E), T2 i j y) =
        (fun y => ∑ i : Fin (Module.finrank ℝ E),
          (fun y' => ∑ j : Fin (Module.finrank ℝ E), T2 i j y') y) from rfl]
    rw [integral_finset_sum _ (fun i _ =>
      integrable_finset_sum _ (fun j _ => hT2_ij_int i j))]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [show (fun y' : EuclN => ∑ j : Fin (Module.finrank ℝ E), T2 i j y') =
        (fun y' => ∑ j : Fin (Module.finrank ℝ E), (fun y'' => T2 i j y'') y')
        from rfl]
    rw [integral_finset_sum _ (fun j _ => hT2_ij_int i j)]
  have h_cross2 : ∫ y in K_0, (∑ i, ∑ j, T3 i j y)
      ∂(volume : Measure EuclN) =
      cross_2_term_chartBilinear (I := I) (M := M) D K_0 η k h := by
    rw [show (fun y : EuclN => ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E), T3 i j y) =
        (fun y => ∑ i : Fin (Module.finrank ℝ E),
          (fun y' => ∑ j : Fin (Module.finrank ℝ E), T3 i j y') y) from rfl]
    rw [integral_finset_sum _ (fun i _ =>
      integrable_finset_sum _ (fun j _ => hT3_ij_int i j))]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [show (fun y' : EuclN => ∑ j : Fin (Module.finrank ℝ E), T3 i j y') =
        (fun y' => ∑ j : Fin (Module.finrank ℝ E), (fun y'' => T3 i j y'') y')
        from rfl]
    rw [integral_finset_sum _ (fun j _ => hT3_ij_int i j)]
  have h_cross3 : ∫ y in K_0, (∑ i, ∑ j, T4 i j y)
      ∂(volume : Measure EuclN) =
      cross_3_term_chartBilinear (I := I) (M := M) D K_0 η k h := by
    rw [show (fun y : EuclN => ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E), T4 i j y) =
        (fun y => ∑ i : Fin (Module.finrank ℝ E),
          (fun y' => ∑ j : Fin (Module.finrank ℝ E), T4 i j y') y) from rfl]
    rw [integral_finset_sum _ (fun i _ =>
      integrable_finset_sum _ (fun j _ => hT4_ij_int i j))]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [show (fun y' : EuclN => ∑ j : Fin (Module.finrank ℝ E), T4 i j y') =
        (fun y' => ∑ j : Fin (Module.finrank ℝ E), (fun y'' => T4 i j y'') y')
        from rfl]
    rw [integral_finset_sum _ (fun j _ => hT4_ij_int i j)]
  rw [h_int_expand, h_thick_to_K_0, h_split, h_principalTerm, h_cross1,
    h_cross2, h_cross3]


theorem variational_identity_after_product_rule_unconditional
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    (hK_0_in : K_0 ⊆ chartTargetEuclid (I := I) (M := M) α)
    {η : EuclN → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_supp : HasCompactSupport η)
    (hη_supp_in_K_0 : tsupport η ⊆ K_0)
    (k : Fin (Module.finrank ℝ E))
    {R₀ : ℝ} {h : ℝ} (hh : h ≠ 0) (hh_le : |h| ≤ R₀)
    (h_thick : Metric.cthickening |h| K_0 ⊆
      chartTargetEuclid (I := I) (M := M) α) :
    principalTerm_chartBilinear (I := I) (M := M) D K_0 η k h
      + cross_1_term_chartBilinear (I := I) (M := M) D K_0 η k h
      + cross_2_term_chartBilinear (I := I) (M := M) D K_0 η k h
      + cross_3_term_chartBilinear (I := I) (M := M) D K_0 η k h
      + f_term_chartBilinear (I := I) (M := M) D K_0 η k h
      = c_term_chartBilinear (I := I) (M := M) D K_0 η k h := by
  classical
  have h_after_ibp_eq :=
    variational_identity_after_ibp_unconditional (I := I) (M := M) D
      hK_0_compact hK_0_in hη hη_supp hη_supp_in_K_0 k hh hh_le h_thick
      (variational_identity_v_h_expanded_unconditional (I := I) (M := M) D
        hK_0_compact hK_0_in hη hη_supp hη_supp_in_K_0 k hh hh_le h_thick)
  have h_principal_in_K_0_eq :
      ∫ y in Metric.cthickening |h| K_0,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h
                (fun z => weightedInvGramOnEuclid (I := I) g α i j z *
                  D.weak_partial i z) y *
              ((η y) ^ 2 *
                DifferentialGeometry.Analysis.Sobolev.diffQuot
                  (d := Module.finrank ℝ E) k h (D.weak_partial j) y +
                2 * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1) *
                  DifferentialGeometry.Analysis.Sobolev.diffQuot
                    (d := Module.finrank ℝ E) k h D.u_chart y))
          ∂(volume : Measure EuclN) =
      principalTerm_chartBilinear (I := I) (M := M) D K_0 η k h
        + cross_1_term_chartBilinear (I := I) (M := M) D K_0 η k h
        + cross_2_term_chartBilinear (I := I) (M := M) D K_0 η k h
        + cross_3_term_chartBilinear (I := I) (M := M) D K_0 η k h :=
    principal_post_ibp_integral_eq_symbolic (I := I) (M := M) D
      hK_0_compact hK_0_in hη hη_supp hη_supp_in_K_0 k hh hh_le h_thick
  have h_c_term_eq :
      ∫ y in Metric.cthickening |h| K_0,
        densityOnEuclid (I := I) g α y * D.u_chart y *
          standardNirenbergTest (d := Module.finrank ℝ E) k h η D.u_chart y
      ∂(volume : Measure EuclN) =
      c_term_chartBilinear (I := I) (M := M) D K_0 η k h := rfl
  have h_f_term_eq :
      ∫ y in Metric.cthickening |h| K_0,
        densityOnEuclid (I := I) g α y * D.f_chart y *
          standardNirenbergTest (d := Module.finrank ℝ E) k h η D.u_chart y
      ∂(volume : Measure EuclN) =
      f_term_chartBilinear (I := I) (M := M) D K_0 η k h := rfl
  exact variational_identity_after_product_rule (I := I) (M := M) D
    hK_0_compact hK_0_in hη hη_supp hη_supp_in_K_0 k hh hh_le h_thick
    h_after_ibp_eq h_principal_in_K_0_eq h_c_term_eq h_f_term_eq

theorem chartBilinear_substitution_identity_holds
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    (hK_0_in : K_0 ⊆ chartTargetEuclid (I := I) (M := M) α)
    {η : EuclN → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_supp : HasCompactSupport η)
    (hη_supp_in_K_0 : tsupport η ⊆ K_0)
    (k : Fin (Module.finrank ℝ E))
    {R₀ : ℝ} {h : ℝ} (hh : h ≠ 0) (hh_le : |h| ≤ R₀)
    (h_thick : Metric.cthickening |h| K_0 ⊆
      chartTargetEuclid (I := I) (M := M) α) :
    chartBilinear_LHS (I := I) (M := M) D K_0 η k h =
    chartBilinear_RHS (I := I) (M := M) D K_0 η k h := by
  unfold chartBilinear_LHS chartBilinear_RHS
  exact variational_identity_after_product_rule_unconditional (I := I) (M := M) D
    hK_0_compact hK_0_in hη hη_supp hη_supp_in_K_0 k hh hh_le h_thick

theorem nirenberg_substitution_identity_chartBilinear_unconditional
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    (hK_0_in : K_0 ⊆ chartTargetEuclid (I := I) (M := M) α)
    {η : EuclN → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_supp : HasCompactSupport η)
    (hη_supp_in_K_0 : tsupport η ⊆ K_0)
    (k : Fin (Module.finrank ℝ E))
    {R₀ : ℝ} {h : ℝ} (hh : h ≠ 0) (hh_le : |h| ≤ R₀)
    (h_thick : Metric.cthickening |h| K_0 ⊆
      chartTargetEuclid (I := I) (M := M) α) :
    (∫ x in K_0,
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            DifferentialGeometry.Analysis.Sobolev.translate
              (d := Module.finrank ℝ E) k h
              (fun y => weightedInvGramOnEuclid (I := I) g α i j y) x *
            (η x) ^ 2 *
            DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h (D.weak_partial i) x *
            DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h (D.weak_partial j) x
        ∂(volume : Measure EuclN))
    + (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∫ x in K_0,
            2 *
              DifferentialGeometry.Analysis.Sobolev.translate
                (d := Module.finrank ℝ E) k h
                (fun y => weightedInvGramOnEuclid (I := I) g α i j y) x *
              (η x) *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h (D.weak_partial i) x *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h D.u_chart x
            ∂(volume : Measure EuclN))
    + (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∫ x in K_0,
            DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h
              (fun y => weightedInvGramOnEuclid (I := I) g α i j y) x *
            (η x) ^ 2 *
            D.weak_partial i x *
            DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h (D.weak_partial j) x
          ∂(volume : Measure EuclN))
    + (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∫ x in K_0,
            2 *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h
                (fun y => weightedInvGramOnEuclid (I := I) g α i j y) x *
              (η x) *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
              D.weak_partial i x *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h D.u_chart x
            ∂(volume : Measure EuclN))
    + (∫ x in Metric.cthickening |h| K_0,
          densityOnEuclid (I := I) g α x * D.f_chart x *
            standardNirenbergTest
              (d := Module.finrank ℝ E) k h η D.u_chart x
        ∂(volume : Measure EuclN))
    = ∫ x in Metric.cthickening |h| K_0,
          densityOnEuclid (I := I) g α x * D.u_chart x *
            standardNirenbergTest
              (d := Module.finrank ℝ E) k h η D.u_chart x
        ∂(volume : Measure EuclN) := by
  have h := chartBilinear_substitution_identity_holds (I := I) (M := M) D
    hK_0_compact hK_0_in hη hη_supp hη_supp_in_K_0 k hh hh_le h_thick
  unfold chartBilinear_LHS chartBilinear_RHS at h
  unfold principalTerm_chartBilinear cross_1_term_chartBilinear
    cross_2_term_chartBilinear cross_3_term_chartBilinear
    f_term_chartBilinear c_term_chartBilinear at h
  exact h

end SubstitutionDischargeAssembly
end Sobolev
end Analysis
end DifferentialGeometry
