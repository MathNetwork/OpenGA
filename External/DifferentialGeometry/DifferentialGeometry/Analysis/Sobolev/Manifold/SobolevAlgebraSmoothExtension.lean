import DifferentialGeometry.Analysis.Sobolev.Manifold.MorreyManifold
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Multiplication.MultiplyQuant
import DifferentialGeometry.Analysis.Sobolev.Tools.StrictStrongSupport
import DifferentialGeometry.Analysis.Sobolev.Manifold.IteratedSobolevEmbedding
import DifferentialGeometry.Analysis.Sobolev.Approximation.ContMDiffDenseLemmas


noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Chart

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

lemma exists_chart_cutoff
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] (α : M) :
    ∃ b : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ b ∧
      Set.range b ⊆ Set.Icc (0 : ℝ) 1 ∧
      (∀ x ∈ tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU
        I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ), b x = 1) ∧
      tsupport b ⊆ (chartAt H α).source := by
  classical
  obtain ⟨K, hK_compact, hK_chart, h_tsupp_in_int_K⟩ :=
    exists_compact_neighborhood_of_tsupport_pou (I := I) (M := M) α
  obtain ⟨η, hη_smooth, hη_range, _hη_support, hη_one_on_tsupp, hη_tsupport_in_K⟩ :=
    exists_manifold_cutoff_one_on_tsupport_pou (I := I) (M := M) α hK_compact
      h_tsupp_in_int_K
  refine ⟨η, hη_smooth, hη_range, hη_one_on_tsupp, ?_⟩
  exact hη_tsupport_in_K.trans hK_chart

def smoothExtension (α : M) (f : M → ℝ) : EuclN → ℝ := by
  classical
  exact fun y =>
    if (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target then
      f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
    else 0

omit [IsManifold I ∞ M] in
private lemma smoothExtension_apply_of_mem_target
    (α : M) (f : M → ℝ) {y : EuclN}
    (hy : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target) :
    smoothExtension (I := I) (M := M) α f y =
      f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := by
  classical
  change (if (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target then
      f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
    else 0) = f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
  rw [if_pos hy]

omit [IsManifold I ∞ M] in
private lemma smoothExtension_apply_of_notMem_target
    (α : M) (f : M → ℝ) {y : EuclN}
    (hy : (toEuclidean (E := E)).symm y ∉ (extChartAt I α).target) :
    smoothExtension (I := I) (M := M) α f y = 0 := by
  classical
  change (if (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target then
      f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
    else 0) = 0
  rw [if_neg hy]

omit [IsManifold I ∞ M] in
lemma smoothExtension_apply_of_mem_chartTargetEuclid
    (α : M) (f : M → ℝ) {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    smoothExtension (I := I) (M := M) α f y =
      f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := by
  apply smoothExtension_apply_of_mem_target
  rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
  exact hy

omit [IsManifold I ∞ M] in
private lemma smoothExtension_apply_of_notMem_chartTargetEuclid
    (α : M) (f : M → ℝ) {y : EuclN}
    (hy : y ∉ chartTargetEuclid (I := I) (M := M) α) :
    smoothExtension (I := I) (M := M) α f y = 0 := by
  apply smoothExtension_apply_of_notMem_target
  rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
  exact hy

private lemma contDiffOn_smoothExtension_formula
    (α : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    ContDiffOn ℝ ∞
        (fun y : EuclN =>
          f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
        (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have hscalar : ContDiffOn ℝ ∞
      (fun y : E => f ((extChartAt I α).symm y))
      (extChartAt I α).target :=
    DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE_contDiffOn
      (I := I) α hf
  have htoEuc_symm_smooth : ContDiff ℝ ∞ ((toEuclidean (E := E)).symm) :=
    ContinuousLinearEquiv.contDiff _
  have hmaps : Set.MapsTo ((toEuclidean (E := E)).symm)
      (chartTargetEuclid (I := I) (M := M) α) (extChartAt I α).target := by
    intro y hy
    rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
    exact hy
  exact hscalar.comp htoEuc_symm_smooth.contDiffOn hmaps

private lemma contDiffAt_smoothExtension_of_mem_target
    (α : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    [I.Boundaryless] {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    ContDiffAt ℝ ∞ (smoothExtension (I := I) (M := M) α f) y := by
  classical
  have hOpen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hContDiffOn := contDiffOn_smoothExtension_formula (I := I) (M := M) α hf
  have hContDiffAt_formula : ContDiffAt ℝ ∞
      (fun y : EuclN => f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) y := by
    have hwithin : ContDiffWithinAt ℝ ∞
        (fun y : EuclN => f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
        (chartTargetEuclid (I := I) (M := M) α) y := hContDiffOn y hy
    exact hwithin.contDiffAt (hOpen.mem_nhds hy)
  apply hContDiffAt_formula.congr_of_eventuallyEq
  filter_upwards [hOpen.mem_nhds hy] with z hz
  rw [smoothExtension_apply_of_mem_chartTargetEuclid (I := I) (M := M) α f hz]

omit [IsManifold I ∞ M] in
private lemma smoothExtension_eq_zero_off_image_tsupport
    (α : M) {f : M → ℝ}
    (_hf_supp : tsupport f ⊆ (chartAt H α).source) {y : EuclN}
    (hy_off : y ∉ (toEuclidean (E := E)) ''
        ((extChartAt I α) '' (tsupport f))) :
    smoothExtension (I := I) (M := M) α f y = 0 := by
  classical
  by_cases hy_target : y ∈ chartTargetEuclid (I := I) (M := M) α
  · obtain ⟨z, hz_target, hzy⟩ := hy_target
    have hy_target' : y ∈ chartTargetEuclid (I := I) (M := M) α := ⟨z, hz_target, hzy⟩
    have hy_symm : (toEuclidean (E := E)).symm y = z := by
      rw [← hzy]; exact (toEuclidean (E := E)).symm_apply_apply z
    rw [smoothExtension_apply_of_mem_chartTargetEuclid (I := I) (M := M) α f hy_target',
      hy_symm]
    by_contra hne
    apply hy_off
    have hsymm_in_supp : (extChartAt I α).symm z ∈ tsupport f :=
      subset_tsupport _ (Function.mem_support.mpr hne)
    have hz_eq : (extChartAt I α) ((extChartAt I α).symm z) = z :=
      (extChartAt I α).right_inv hz_target
    refine ⟨z, ⟨(extChartAt I α).symm z, hsymm_in_supp, hz_eq⟩, hzy⟩
  · exact smoothExtension_apply_of_notMem_chartTargetEuclid
      (I := I) (M := M) α f hy_target

omit [IsManifold I ∞ M] in
lemma image_extChartAt_tsupport_isCompact
    [CompactSpace M] {f : M → ℝ} {α : M}
    (hf_supp : tsupport f ⊆ (chartAt H α).source) :
    IsCompact ((toEuclidean (E := E)) ''
      ((extChartAt I α) '' (tsupport f))) := by
  have hKE := image_extChartAt_tsupport_compact_subset_target
    (I := I) (M := M) (u := f) (α := α) hf_supp
  exact hKE.1.image (toEuclidean (E := E)).continuous

omit [IsManifold I ∞ M] in
private lemma image_extChartAt_tsupport_subset_chartTarget
    {f : M → ℝ} {α : M}
    (hf_supp : tsupport f ⊆ (chartAt H α).source) :
    (toEuclidean (E := E)) ''
        ((extChartAt I α) '' (tsupport f)) ⊆
      chartTargetEuclid (I := I) (M := M) α :=
  image_toEuclidean_extChartAt_tsupport_subset_chartTargetEuclid
    (I := I) (M := M) (u := f) (α := α) hf_supp

lemma contDiff_smoothExtension
    [CompactSpace M] [I.Boundaryless]
    (α : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hf_supp : tsupport f ⊆ (chartAt H α).source) :
    ContDiff ℝ ∞ (smoothExtension (I := I) (M := M) α f) := by
  classical
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy_target : y ∈ chartTargetEuclid (I := I) (M := M) α
  · exact contDiffAt_smoothExtension_of_mem_target (I := I) (M := M) α hf hy_target
  · have hy_off : y ∉ (toEuclidean (E := E)) ''
        ((extChartAt I α) '' (tsupport f)) := by
      intro hy_in
      apply hy_target
      exact image_extChartAt_tsupport_subset_chartTarget
        (I := I) (M := M) (f := f) (α := α) hf_supp hy_in
    have hK_compact : IsCompact ((toEuclidean (E := E)) ''
        ((extChartAt I α) '' (tsupport f))) :=
      image_extChartAt_tsupport_isCompact
        (I := I) (M := M) (f := f) (α := α) hf_supp
    have hK_compl_open : IsOpen _ := hK_compact.isClosed.isOpen_compl
    apply ContDiffAt.congr_of_eventuallyEq
      (f := fun _ : EuclN => (0 : ℝ)) contDiffAt_const
    filter_upwards [hK_compl_open.mem_nhds hy_off] with z hz
    exact smoothExtension_eq_zero_off_image_tsupport
      (I := I) (M := M) α (f := f) hf_supp hz

omit [IsManifold I ∞ M] in
lemma hasCompactSupport_smoothExtension
    [CompactSpace M] (α : M) {f : M → ℝ}
    (hf_supp : tsupport f ⊆ (chartAt H α).source) :
    HasCompactSupport (smoothExtension (I := I) (M := M) α f) := by
  classical
  set K : Set EuclN :=
    (toEuclidean (E := E)) '' ((extChartAt I α) '' (tsupport f)) with hK_def
  have hK_compact : IsCompact K :=
    image_extChartAt_tsupport_isCompact (I := I) (M := M) (f := f) (α := α) hf_supp
  apply HasCompactSupport.of_support_subset_isCompact hK_compact
  intro y hy_supp
  by_contra hyK
  apply hy_supp
  exact smoothExtension_eq_zero_off_image_tsupport
    (I := I) (M := M) α (f := f) hf_supp hyK

omit [FiniteDimensional ℝ E] in
lemma iteratedFDeriv_bound_of_compactSupport
    {ψ : EuclN → ℝ} (hψ_smooth : ContDiff ℝ ∞ ψ) (hψ_compact : HasCompactSupport ψ)
    (k : ℕ) :
    ∃ Mk : ℝ, 0 ≤ Mk ∧ ∀ y : EuclN, ‖iteratedFDeriv ℝ k ψ y‖ ≤ Mk := by
  classical
  have h_iterCont : Continuous (fun y : EuclN => iteratedFDeriv ℝ k ψ y) :=
    hψ_smooth.continuous_iteratedFDeriv (m := k) (by exact_mod_cast le_top)
  have h_iter_supp : HasCompactSupport (fun y : EuclN => iteratedFDeriv ℝ k ψ y) :=
    hψ_compact.iteratedFDeriv (𝕜 := ℝ) k
  obtain ⟨C, hC⟩ := h_iterCont.bounded_above_of_compact_support h_iter_supp
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro y
  exact (hC y).trans (le_max_left _ _)

lemma smoothExtension_first_order_bound
    [CompactSpace M] [I.Boundaryless]
    (α : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hf_supp : tsupport f ⊆ (chartAt H α).source) :
    ∃ Cf : ℝ, 0 ≤ Cf ∧ ∀ j ≤ 1, ∀ y : EuclN,
      ‖iteratedFDeriv ℝ j (smoothExtension (I := I) (M := M) α f) y‖ ≤ Cf := by
  classical
  have hψ_smooth : ContDiff ℝ ∞ (smoothExtension (I := I) (M := M) α f) :=
    contDiff_smoothExtension (I := I) (M := M) α hf hf_supp
  have hψ_compact : HasCompactSupport (smoothExtension (I := I) (M := M) α f) :=
    hasCompactSupport_smoothExtension (I := I) (M := M) α hf_supp
  obtain ⟨M0, hM0_nn, hM0⟩ :=
    iteratedFDeriv_bound_of_compactSupport hψ_smooth hψ_compact 0
  obtain ⟨M1, hM1_nn, hM1⟩ :=
    iteratedFDeriv_bound_of_compactSupport hψ_smooth hψ_compact 1
  refine ⟨max M0 M1, le_max_of_le_left hM0_nn, ?_⟩
  intro j hj y
  interval_cases j
  · exact (hM0 y).trans (le_max_left _ _)
  · exact (hM1 y).trans (le_max_right _ _)

omit [IsManifold I ∞ M] in
lemma smoothExtension_mul_eq
    (α : M) (f g : M → ℝ) :
    (fun y : EuclN => smoothExtension (I := I) (M := M) α f y *
      smoothExtension (I := I) (M := M) α g y) =
    smoothExtension (I := I) (M := M) α (fun x : M => f x * g x) := by
  classical
  funext y
  by_cases hy : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target
  · rw [smoothExtension_apply_of_mem_target (I := I) (M := M) α f hy,
      smoothExtension_apply_of_mem_target (I := I) (M := M) α g hy,
      smoothExtension_apply_of_mem_target (I := I) (M := M) α (fun x => f x * g x) hy]
  · rw [smoothExtension_apply_of_notMem_target (I := I) (M := M) α f hy,
      smoothExtension_apply_of_notMem_target (I := I) (M := M) α g hy,
      smoothExtension_apply_of_notMem_target (I := I) (M := M) α (fun x => f x * g x) hy,
      mul_zero]

lemma smoothExtension_three_factor
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (α : M) {b u v : M → ℝ}
    (hb_one : ∀ x ∈ tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU
      I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ), b x = 1) :
    smoothExtension (I := I) (M := M) α
        (fun x => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x * v x) =
      (fun y : EuclN =>
        smoothExtension (I := I) (M := M) α
          (fun x => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) x * u x) y *
        smoothExtension (I := I) (M := M) α (fun x => b x * v x) y) := by
  rw [smoothExtension_mul_eq (I := I) (M := M) α
    (fun x => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) x * u x)
    (fun x => b x * v x)]
  congr 1
  funext x
  by_cases hρ : (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
    : C^∞⟮I, M; ℝ⟯) x = 0
  · rw [hρ]; ring
  · have hx_supp : x ∈ tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU
        I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
      subset_tsupport _ (Function.mem_support.mpr hρ)
    have hb_x : b x = 1 := hb_one x hx_supp
    rw [hb_x]; ring

private lemma smoothExtension_three_factor_symm
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (α : M) {b u v : M → ℝ}
    (hb_one : ∀ x ∈ tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU
      I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ), b x = 1) :
    smoothExtension (I := I) (M := M) α
        (fun x => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x * v x) =
      (fun y : EuclN =>
        smoothExtension (I := I) (M := M) α (fun x => b x * u x) y *
        smoothExtension (I := I) (M := M) α
          (fun x => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) x * v x) y) := by
  rw [smoothExtension_mul_eq (I := I) (M := M) α
    (fun x => b x * u x)
    (fun x => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) x * v x)]
  congr 1
  funext x
  by_cases hρ : (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
    : C^∞⟮I, M; ℝ⟯) x = 0
  · rw [hρ]; ring
  · have hx_supp : x ∈ tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU
        I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
      subset_tsupport _ (Function.mem_support.mpr hρ)
    have hb_x : b x = 1 := hb_one x hx_supp
    rw [hb_x]; ring

omit [IsManifold I ∞ M] in
lemma tsupport_smoothExtension_subset_image
    [CompactSpace M] (α : M) {f : M → ℝ}
    (hf_supp : tsupport f ⊆ (chartAt H α).source) :
    tsupport (smoothExtension (I := I) (M := M) α f) ⊆
      (toEuclidean (E := E)) ''
        ((extChartAt I α) '' (tsupport f)) := by
  classical
  set K : Set EuclN :=
    (toEuclidean (E := E)) '' ((extChartAt I α) '' (tsupport f)) with hK_def
  have hK_compact : IsCompact K :=
    image_extChartAt_tsupport_isCompact (I := I) (M := M) (f := f) (α := α) hf_supp
  have hK_closed : IsClosed K := hK_compact.isClosed
  have h_supp_sub : Function.support (smoothExtension (I := I) (M := M) α f) ⊆ K := by
    intro y hy
    by_contra hyK
    apply hy
    exact smoothExtension_eq_zero_off_image_tsupport (I := I) (M := M) α
      (f := f) hf_supp hyK
  rw [tsupport]
  exact hK_closed.closure_subset_iff.mpr h_supp_sub

omit [IsManifold I ∞ M] in
lemma image_tsupport_subset_chartTarget
    {f : M → ℝ} {α : M}
    (hf_supp : tsupport f ⊆ (chartAt H α).source) :
    (toEuclidean (E := E)) ''
        ((extChartAt I α) '' (tsupport f)) ⊆
      chartTargetEuclid (I := I) (M := M) α :=
  image_extChartAt_tsupport_subset_chartTarget (I := I) (M := M) (f := f) (α := α) hf_supp

omit [IsManifold I ∞ M] in
lemma tsupport_smoothExtension_subset_chartTarget
    [CompactSpace M] (α : M) {f : M → ℝ}
    (hf_supp : tsupport f ⊆ (chartAt H α).source) :
    tsupport (smoothExtension (I := I) (M := M) α f) ⊆
      chartTargetEuclid (I := I) (M := M) α :=
  (tsupport_smoothExtension_subset_image (I := I) (M := M) α hf_supp).trans
    (image_tsupport_subset_chartTarget (I := I) (M := M) hf_supp)

end Chart
end Sobolev
end Analysis
end DifferentialGeometry
