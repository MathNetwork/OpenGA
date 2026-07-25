import DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.VariationalIdentity.SuccessorSource
import DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.NirenbergInterior.EffectiveSourceRegularity
import DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.NirenbergInterior.MixedPartials
import DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.Differentiated.CrossTermIBP
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Multiplication.MultiplyQuantK


noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace IteratedFChartEffStepRegularity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainChartData
open DifferentialGeometry.Analysis.Laplacian.IteratedMixedPartials
open DifferentialGeometry.Analysis.Laplacian.IteratedVariationalIdentityStepScaffold
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.DifferentiatedCrossTermIBP
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private abbrev Kα (α : M) : Set EuclN :=
  chartImagePOUTsupport (I := I) (M := M) α

private abbrev Ωα (α : M) : Set EuclN :=
  chartTargetEuclid (I := I) (M := M) α

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma Kα_compact (α : M) :
    IsCompact (Kα (I := I) (M := M) α) :=
  chartImagePOUTsupport_isCompact (I := I) (M := M) α

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma Kα_meas (α : M) :
    MeasurableSet (Kα (I := I) (M := M) α) :=
  (Kα_compact (I := I) (M := M) α).isClosed.measurableSet

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma Kα_subset_Ωα (α : M) :
    Kα (I := I) (M := M) α ⊆ Ωα (I := I) (M := M) α :=
  chartImagePOUTsupport_subset_target (I := I) (M := M) α

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma Ωα_isOpen (α : M) : IsOpen (Ωα (I := I) (M := M) α) :=
  chartTargetEuclid_isOpen (I := I) (M := M) α

omit [NeZero (Module.finrank ℝ E)] in
private lemma chartPushed_u_h_ae_zero_off_Kα
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) :
    chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ)
      =ᵐ[(volume : Measure EuclN).restrict
        (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)]
      (fun _ : EuclN => (0 : ℝ)) := by
  have h_diff_open : IsOpen (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α) :=
    (Ωα_isOpen (I := I) (M := M) α).sdiff
      (Kα_compact (I := I) (M := M) α).isClosed
  refine (ae_restrict_iff' h_diff_open.measurableSet).mpr ?_
  refine Filter.Eventually.of_forall ?_
  intro y hy
  exact chartPushed_eq_zero_off_chartImagePOUTsupport
    (I := I) (M := M) α _ hy.1 hy.2

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma chosenWeakPartial'_ae_zero_on_open_sub_of_ae_zero
    {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω V : Set EuclN}
    (_hΩ : IsOpen Ω) (hV : IsOpen V) (hV_sub : V ⊆ Ω)
    {u : EuclN → ℝ}
    (hu : DeGiorgi.MemW1p (d := Module.finrank ℝ E) p u Ω)
    (hu_ae_zero_V : u =ᵐ[(volume : Measure EuclN).restrict V] (fun _ => (0 : ℝ)))
    (i : Fin (Module.finrank ℝ E)) :
    chosenWeakPartial' (d := Module.finrank ℝ E) p i u Ω
      =ᵐ[(volume : Measure EuclN).restrict V] (fun _ : EuclN => (0 : ℝ)) := by
  classical
  have hu_V : DeGiorgi.MemW1p (d := Module.finrank ℝ E) p u V := by
    refine ⟨?_, ?_⟩
    · exact hu.1.mono_measure
        (MeasureTheory.Measure.restrict_mono_set _ hV_sub)
    · intro j
      obtain ⟨g, hg_memLp, hg_weak⟩ := hu.2 j
      refine ⟨g, ?_, ?_⟩
      · exact hg_memLp.mono_measure
          (MeasureTheory.Measure.restrict_mono_set _ hV_sub)
      · exact DeGiorgi.HasWeakPartialDeriv.restrict hV hV_sub hg_weak
  have h_partial_V : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
      (chosenWeakPartial' (d := Module.finrank ℝ E) p i u V) u V :=
    chosenWeakPartial'_isWeakPartial_of_mem hu_V i
  have h_partial_Ω : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
      (chosenWeakPartial' (d := Module.finrank ℝ E) p i u Ω) u Ω :=
    chosenWeakPartial'_isWeakPartial_of_mem hu i
  have h_partial_Ω_V : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
      (chosenWeakPartial' (d := Module.finrank ℝ E) p i u Ω) u V :=
    DeGiorgi.HasWeakPartialDeriv.restrict hV hV_sub h_partial_Ω
  have h_chosen_V_zero :
      chosenWeakPartial' (d := Module.finrank ℝ E) p i u V
        =ᵐ[(volume : Measure EuclN).restrict V] (fun _ : EuclN => (0 : ℝ)) :=
    chosenWeakPartial'_ae_zero_of_ae_zero (d := Module.finrank ℝ E)
      hp hV hu_ae_zero_V i
  have hg_lp_Ω : MemLp (chosenWeakPartial' (d := Module.finrank ℝ E) p i u Ω) p
      ((volume : Measure EuclN).restrict Ω) :=
    chosenWeakPartial'_memLp_of_mem hu i
  have hg_lp_Ω_V : MemLp (chosenWeakPartial' (d := Module.finrank ℝ E) p i u Ω) p
      ((volume : Measure EuclN).restrict V) :=
    hg_lp_Ω.mono_measure (MeasureTheory.Measure.restrict_mono_set _ hV_sub)
  have hg_loc_Ω_V : LocallyIntegrable
      (chosenWeakPartial' (d := Module.finrank ℝ E) p i u Ω)
      ((volume : Measure EuclN).restrict V) :=
    hg_lp_Ω_V.locallyIntegrable hp
  have hgV_lp : MemLp (chosenWeakPartial' (d := Module.finrank ℝ E) p i u V) p
      ((volume : Measure EuclN).restrict V) :=
    chosenWeakPartial'_memLp_of_mem hu_V i
  have hgV_loc : LocallyIntegrable
      (chosenWeakPartial' (d := Module.finrank ℝ E) p i u V)
      ((volume : Measure EuclN).restrict V) :=
    hgV_lp.locallyIntegrable hp
  have h_unique :
      chosenWeakPartial' (d := Module.finrank ℝ E) p i u Ω
        =ᵐ[(volume : Measure EuclN).restrict V]
        chosenWeakPartial' (d := Module.finrank ℝ E) p i u V :=
    DeGiorgi.HasWeakPartialDeriv.ae_eq hV h_partial_Ω_V h_partial_V
      hg_loc_Ω_V hgV_loc
  exact h_unique.trans h_chosen_V_zero

omit [NeZero (Module.finrank ℝ E)] in
lemma chosenMthMixed_ae_zero_off_Kα
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) (m : ℕ) :
    ∀ (_h_parent : MemWkp (d := Module.finrank ℝ E) m 2
      (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
      (Ωα (I := I) (M := M) α))
    (idx : Fin m → Fin (Module.finrank ℝ E)),
      chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h m idx
        =ᵐ[(volume : Measure EuclN).restrict
          (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)]
        (fun _ : EuclN => (0 : ℝ)) := by
  induction m with
  | zero =>
      intro _h_parent _idx
      simpa [chosenMthMixedPartialChartPushedU_zero] using
        chartPushed_u_h_ae_zero_off_Kα (I := I) (M := M) g α u_h
  | succ m ih =>
      intro h_parent idx
      have h_parent_m : MemWkp (d := Module.finrank ℝ E) m 2
          (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
            ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
          (Ωα (I := I) (M := M) α) := h_parent.le_succ
      have h_inner_ae := ih h_parent_m (Fin.init idx)
      have h_inner_memWkp_1 : MemWkp (d := Module.finrank ℝ E) 1 2
          (chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h m
            (Fin.init idx))
          (Ωα (I := I) (M := M) α) := by
        have h_parent_1_m : MemWkp (d := Module.finrank ℝ E) (1 + m) 2
            (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
              ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
            (Ωα (I := I) (M := M) α) := by
          rw [Nat.add_comm]
          exact h_parent
        exact chosenMthMixedPartialChartPushedU_memWkp_of_chartPushed_memWkp
          (I := I) (M := M) g α u_h m 1 h_parent_1_m (Fin.init idx)
      have h_inner_memW1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
          (chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h m
            (Fin.init idx))
          (Ωα (I := I) (M := M) α) := by
        rw [MemWkp.one_iff_memW1p] at h_inner_memWkp_1
        exact h_inner_memWkp_1
      have h_diff_open : IsOpen
          (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α) :=
        (Ωα_isOpen (I := I) (M := M) α).sdiff
          (Kα_compact (I := I) (M := M) α).isClosed
      have h_diff_subset : Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α ⊆
          Ωα (I := I) (M := M) α := fun _ hy => hy.1
      have h_step :=
        chosenWeakPartial'_ae_zero_on_open_sub_of_ae_zero
          (p := 2) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
          (Ωα_isOpen (I := I) (M := M) α)
          h_diff_open h_diff_subset
          h_inner_memW1p h_inner_ae (idx (Fin.last m))
      rw [chosenMthMixedPartialChartPushedU_succ]
      exact h_step

private structure SmoothExt (α : M) (f : EuclN → ℝ) where

  δ : ℝ

  ext : EuclN → ℝ
  δ_pos : 0 < δ
  cthick_in_target : Metric.cthickening δ (Kα (I := I) (M := M) α) ⊆
    Ωα (I := I) (M := M) α
  ext_smooth : ContDiff ℝ (⊤ : ℕ∞) ext
  ext_eq_on_cthick : ∀ y ∈ Metric.cthickening δ (Kα (I := I) (M := M) α),
    ext y = f y

omit [NeZero (Module.finrank ℝ E)] in
private lemma smoothExt_of_contDiffOn (α : M) {f : EuclN → ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (Ωα (I := I) (M := M) α)) :
    Nonempty (SmoothExt (I := I) (M := M) α f) := by
  obtain ⟨δ, fExt, hδ_pos, hδ_in, hExt_smooth, hExt_eq⟩ :=
    exists_smooth_global_extension (I := I) (M := M) (φ := f) α hf
      (Kα_compact (I := I) (M := M) α)
      (Kα_subset_Ωα (I := I) (M := M) α)
  exact ⟨⟨δ, fExt, hδ_pos, hδ_in, hExt_smooth, hExt_eq⟩⟩

private structure ChartCutoff (α : M) where
  δ : ℝ
  η : EuclN → ℝ
  δ_pos : 0 < δ
  cthick_in_target : Metric.cthickening δ (Kα (I := I) (M := M) α) ⊆
    Ωα (I := I) (M := M) α
  η_smooth : ContDiff ℝ (⊤ : ℕ∞) η
  η_compactSupport : HasCompactSupport η
  η_one_on_cthick : ∀ y ∈ Metric.cthickening δ (Kα (I := I) (M := M) α), η y = 1
  η_tsupp_in_target : tsupport η ⊆ Ωα (I := I) (M := M) α

omit [NeZero (Module.finrank ℝ E)] in
private lemma exists_chartCutoff_nonempty (α : M) :
    Nonempty (ChartCutoff (I := I) (M := M) α) := by
  obtain ⟨δ, η, hδ_pos, hδ_in, hη_smooth, hη_cs, _hη_range, hη_one, hη_tsupp⟩ :=
    exists_smooth_cutoff_with_neighborhood (d := Module.finrank ℝ E)
      (Kα_compact (I := I) (M := M) α)
      (Ωα_isOpen (I := I) (M := M) α)
      (Kα_subset_Ωα (I := I) (M := M) α)
  exact ⟨⟨δ, η, hδ_pos, hδ_in, hη_smooth, hη_cs, hη_one, hη_tsupp⟩⟩

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma memWkp_finset_sum_univ
    {α : M} {K : ℕ} {ι : Type*} (s : Finset ι)
    {f : ι → EuclN → ℝ}
    (hf : ∀ i ∈ s, MemWkp (d := Module.finrank ℝ E) K 2 (f i)
      (Ωα (I := I) (M := M) α)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ∑ i ∈ s, f i y) (Ωα (I := I) (M := M) α) := by
  classical
  have h_open : IsOpen (Ωα (I := I) (M := M) α) := Ωα_isOpen (I := I) (M := M) α
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact MemWkp_zero_fun (d := Module.finrank ℝ E)
        (by norm_num : (1 : ℝ≥0∞) ≤ 2) h_open
  | insert i s his ih =>
      have hi : MemWkp (d := Module.finrank ℝ E) K 2 (f i)
          (Ωα (I := I) (M := M) α) := hf i (Finset.mem_insert_self _ _)
      have his_rest : ∀ j ∈ s, MemWkp (d := Module.finrank ℝ E) K 2 (f j)
          (Ωα (I := I) (M := M) α) :=
        fun j hj => hf j (Finset.mem_insert_of_mem hj)
      have hsum := ih his_rest
      have h_eq : (fun y => ∑ j ∈ insert i s, f j y) =
          (fun y => f i y + ∑ j ∈ s, f j y) := by
        funext y; rw [Finset.sum_insert his]
      rw [h_eq]
      exact MemWkp.add (d := Module.finrank ℝ E)
        (by norm_num : (1 : ℝ≥0∞) ≤ 2) h_open hi hsum

omit [NeZero (Module.finrank ℝ E)] in
private lemma memWkp_coef_mul_factor
    (α : M) (K : ℕ)
    {coef factor : EuclN → ℝ}
    (hcoef_chart : ContDiffOn ℝ (⊤ : ℕ∞) coef (Ωα (I := I) (M := M) α))
    (hfactor_memWkp : MemWkp (d := Module.finrank ℝ E) K 2 factor
      (Ωα (I := I) (M := M) α))
    (hfactor_ae_zero : factor =ᵐ[(volume : Measure EuclN).restrict
      (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)]
      (fun _ => (0 : ℝ))) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => coef y * factor y) (Ωα (I := I) (M := M) α) := by
  classical
  obtain ⟨δ, coef_ext, hδ_pos, hδ_in, hExt_smooth, hExt_eq⟩ :=
    exists_smooth_global_extension (I := I) (M := M) (φ := coef) α hcoef_chart
      (Kα_compact (I := I) (M := M) α)
      (Kα_subset_Ωα (I := I) (M := M) α)
  obtain ⟨ε, χ, hε_pos, hε_in, hχ_smooth, hχ_cs, _hχ_range, hχ_one, hχ_tsupp⟩ :=
    exists_smooth_cutoff_with_neighborhood (d := Module.finrank ℝ E)
      (Kα_compact (I := I) (M := M) α)
      (Ωα_isOpen (I := I) (M := M) α)
      (Kα_subset_Ωα (I := I) (M := M) α)
  have hχ_coef_smooth : ContDiff ℝ (⊤ : ℕ∞) (fun y => χ y * coef_ext y) :=
    hχ_smooth.mul hExt_smooth
  have hχ_coef_cs : HasCompactSupport (fun y => χ y * coef_ext y) :=
    HasCompactSupport.mul_right hχ_cs
  obtain ⟨C, hC_nn, hC_bd⟩ :=
    exists_uniform_iteratedFDeriv_bound_of_smooth_compactSupport
      (d := Module.finrank ℝ E) hχ_coef_smooth hχ_coef_cs K
  have h_prod_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => (χ y * coef_ext y) * factor y) (Ωα (I := I) (M := M) α) :=
    MemWkp.smul_smooth_bounded (d := Module.finrank ℝ E) K
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (Ωα_isOpen (I := I) (M := M) α) hχ_coef_smooth
      (fun j _hj y _hy => hC_bd y j _hj) hfactor_memWkp
  set ρ : ℝ := min δ ε with hρ_def
  have hρ_pos : 0 < ρ := lt_min hδ_pos hε_pos
  have hρ_le_δ : ρ ≤ δ := min_le_left _ _
  have hρ_le_ε : ρ ≤ ε := min_le_right _ _
  set Cρ : Set EuclN := Metric.cthickening ρ (Kα (I := I) (M := M) α) with hCρ_def
  have hCρ_sub_Cδ : Cρ ⊆ Metric.cthickening δ (Kα (I := I) (M := M) α) :=
    Metric.cthickening_mono hρ_le_δ _
  have hCρ_sub_Cε : Cρ ⊆ Metric.cthickening ε (Kα (I := I) (M := M) α) :=
    Metric.cthickening_mono hρ_le_ε _
  have hCρ_in_target : Cρ ⊆ Ωα (I := I) (M := M) α := hCρ_sub_Cδ.trans hδ_in
  have h_ae_eq : (fun y => (χ y * coef_ext y) * factor y) =ᵐ[
      (volume : Measure EuclN).restrict (Ωα (I := I) (M := M) α)]
      (fun y => coef y * factor y) := by
    set Ω : Set EuclN := Ωα (I := I) (M := M) α
    have hΩ_meas : MeasurableSet Ω :=
      (Ωα_isOpen (I := I) (M := M) α).measurableSet
    have hCρ_closed : IsClosed Cρ := Metric.isClosed_cthickening
    have hCρ_meas : MeasurableSet Cρ := hCρ_closed.measurableSet
    have h_eq_on_Cρ : (fun y => (χ y * coef_ext y) * factor y)
        =ᵐ[(volume : Measure EuclN).restrict Cρ]
        (fun y => coef y * factor y) := by
      refine (ae_restrict_iff' hCρ_meas).mpr ?_
      refine Filter.Eventually.of_forall fun y hy => ?_
      have hy_Cδ : y ∈ Metric.cthickening δ (Kα (I := I) (M := M) α) :=
        hCρ_sub_Cδ hy
      have hy_Cε : y ∈ Metric.cthickening ε (Kα (I := I) (M := M) α) :=
        hCρ_sub_Cε hy
      have hχy : χ y = 1 := hχ_one y hy_Cε
      have h_coef : coef_ext y = coef y := hExt_eq y hy_Cδ
      change (χ y * coef_ext y) * factor y = coef y * factor y
      rw [hχy, h_coef]; ring
    have hKα_in_Cρ : Kα (I := I) (M := M) α ⊆ Cρ :=
      Metric.self_subset_cthickening _
    have h_diff_sub : Ω \ Cρ ⊆ Ω \ Kα (I := I) (M := M) α := by
      intro y hy
      exact ⟨hy.1, fun hyK => hy.2 (hKα_in_Cρ hyK)⟩
    have h_factor_ae_zero_diff : factor =ᵐ[(volume : Measure EuclN).restrict
        (Ω \ Cρ)] (fun _ => (0 : ℝ)) := by
      have h_abs : (volume : Measure EuclN).restrict (Ω \ Cρ) ≪
          (volume : Measure EuclN).restrict (Ω \ Kα (I := I) (M := M) α) :=
        MeasureTheory.Measure.absolutelyContinuous_of_le
          (MeasureTheory.Measure.restrict_mono h_diff_sub le_rfl)
      exact h_abs.ae_le hfactor_ae_zero
    have h_eq_on_diff :
        (fun y => (χ y * coef_ext y) * factor y) =ᵐ[
          (volume : Measure EuclN).restrict (Ω \ Cρ)]
        (fun y => coef y * factor y) := by
      filter_upwards [h_factor_ae_zero_diff] with y hy
      show (χ y * coef_ext y) * factor y = coef y * factor y
      rw [hy]; ring
    have h_eq_on_inter : (fun y => (χ y * coef_ext y) * factor y)
        =ᵐ[(volume : Measure EuclN).restrict (Ω ∩ Cρ)]
        (fun y => coef y * factor y) := by
      have h_abs : (volume : Measure EuclN).restrict (Ω ∩ Cρ) ≪
          (volume : Measure EuclN).restrict Cρ :=
        MeasureTheory.Measure.absolutelyContinuous_of_le
          (MeasureTheory.Measure.restrict_mono Set.inter_subset_right le_rfl)
      exact h_abs.ae_le h_eq_on_Cρ
    have h_diff_meas : MeasurableSet (Ω \ Cρ) := hΩ_meas.diff hCρ_meas
    have h_cover : Ω = (Ω ∩ Cρ) ∪ (Ω \ Cρ) := by
      ext y; constructor
      · intro hy
        by_cases h : y ∈ Cρ
        · exact Or.inl ⟨hy, h⟩
        · exact Or.inr ⟨hy, h⟩
      · rintro (⟨hy, _⟩ | ⟨hy, _⟩) <;> exact hy
    have h_disj : Disjoint (Ω ∩ Cρ) (Ω \ Cρ) := by
      refine Set.disjoint_left.mpr ?_
      intro y hy hy'; exact hy'.2 hy.2
    have hΩ_restrict_eq : (volume : Measure EuclN).restrict Ω =
        (volume : Measure EuclN).restrict ((Ω ∩ Cρ) ∪ (Ω \ Cρ)) := by
      rw [← h_cover]
    rw [hΩ_restrict_eq, MeasureTheory.Measure.restrict_union h_disj h_diff_meas]
    exact (MeasureTheory.ae_add_measure_iff).mpr ⟨h_eq_on_inter, h_eq_on_diff⟩
  exact (MemWkp_congr_ae (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) (Ωα_isOpen (I := I) (M := M) α) h_ae_eq).mp
    h_prod_memWkp

omit [NeZero (Module.finrank ℝ E)] in
private lemma layer_A_pair_memWkp
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) (m K : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (l i j : Fin (Module.finrank ℝ E))
    (h_chart_H_succ_K :
      MemWkp (d := Module.finrank ℝ E) ((m + 1) + K) 2
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
        (Ωα (I := I) (M := M) α)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y =>
        (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l) y)
            (EuclideanSpace.single j 1) *
        chosenMthMixedPartialChartPushedU
          (I := I) (M := M) g α u_h (m + 1) (Fin.cons i dirs) y)
      (Ωα (I := I) (M := M) α) := by
  classical
  have h_coef_smooth :
      ContDiffOn ℝ (⊤ : ℕ∞)
        (fun y =>
          (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l) y)
            (EuclideanSpace.single j 1))
        (Ωα (I := I) (M := M) α) := by
    have h_diffOn := weightedInvGramDerivOnEuclid_contDiffOn
      (I := I) (M := M) g α i j l
    have h_open : IsOpen (Ωα (I := I) (M := M) α) :=
      Ωα_isOpen (I := I) (M := M) α
    have h_fderiv :
        ContDiffOn ℝ (⊤ : ℕ∞)
          (fun y => fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l) y)
          (Ωα (I := I) (M := M) α) :=
      ((contDiffOn_infty_iff_fderiv_of_isOpen h_open).1 h_diffOn).2
    have h_eval : ContDiff ℝ (⊤ : ℕ∞)
        (fun (L : EuclN →L[ℝ] ℝ) => L (EuclideanSpace.single j 1)) :=
      (ContinuousLinearMap.apply ℝ ℝ
        (EuclideanSpace.single j (1 : ℝ))).contDiff
    exact h_eval.contDiffOn.comp h_fderiv (mapsTo_univ _ _)
  have h_factor_memWkp :
      MemWkp (d := Module.finrank ℝ E) K 2
        (chosenMthMixedPartialChartPushedU
          (I := I) (M := M) g α u_h (m + 1) (Fin.cons i dirs))
        (Ωα (I := I) (M := M) α) := by
    have h_parent_K_plus :
        MemWkp (d := Module.finrank ℝ E) (K + (m + 1)) 2
          (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
            ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
          (Ωα (I := I) (M := M) α) := by
      have h_eq : K + (m + 1) = (m + 1) + K := by ring
      rw [h_eq]; exact h_chart_H_succ_K
    exact chosenMthMixedPartialChartPushedU_memWkp_of_chartPushed_memWkp
      (I := I) (M := M) g α u_h (m + 1) K h_parent_K_plus (Fin.cons i dirs)
  have h_factor_ae_zero :
      chosenMthMixedPartialChartPushedU
        (I := I) (M := M) g α u_h (m + 1) (Fin.cons i dirs)
        =ᵐ[(volume : Measure EuclN).restrict
          (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)]
        (fun _ => (0 : ℝ)) := by
    have h_parent_m_plus_1 :
        MemWkp (d := Module.finrank ℝ E) (m + 1) 2
          (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
            ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
          (Ωα (I := I) (M := M) α) :=
      h_chart_H_succ_K.le_of_le (by omega)
    exact chosenMthMixed_ae_zero_off_Kα (I := I) (M := M) g α u_h (m + 1)
      h_parent_m_plus_1 (Fin.cons i dirs)
  exact memWkp_coef_mul_factor (I := I) (M := M) α K h_coef_smooth
    h_factor_memWkp h_factor_ae_zero

omit [NeZero (Module.finrank ℝ E)] in
private lemma layer_A_memWkp
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) (m K : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (l : Fin (Module.finrank ℝ E))
    (h_chart_H_succ_K :
      MemWkp (d := Module.finrank ℝ E) ((m + 1) + K) 2
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
        (Ωα (I := I) (M := M) α)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l) y)
              (EuclideanSpace.single j 1) *
            chosenMthMixedPartialChartPushedU
              (I := I) (M := M) g α u_h (m + 1) (Fin.cons i dirs) y)
      (Ωα (I := I) (M := M) α) := by
  classical
  have h_inner_sum : ∀ i : Fin (Module.finrank ℝ E),
      MemWkp (d := Module.finrank ℝ E) K 2
        (fun y => ∑ j : Fin (Module.finrank ℝ E),
          (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l) y)
              (EuclideanSpace.single j 1) *
            chosenMthMixedPartialChartPushedU
              (I := I) (M := M) g α u_h (m + 1) (Fin.cons i dirs) y)
        (Ωα (I := I) (M := M) α) := by
    intro i
    exact memWkp_finset_sum_univ (I := I) (M := M)
      (α := α) (K := K) (s := Finset.univ)
      (f := fun j y =>
        (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l) y)
            (EuclideanSpace.single j 1) *
          chosenMthMixedPartialChartPushedU
            (I := I) (M := M) g α u_h (m + 1) (Fin.cons i dirs) y)
      (fun j _hj =>
        layer_A_pair_memWkp (I := I) (M := M) g α u_h m K dirs l i j
          h_chart_H_succ_K)
  exact memWkp_finset_sum_univ (I := I) (M := M)
    (α := α) (K := K) (s := Finset.univ)
    (f := fun i y => ∑ j : Fin (Module.finrank ℝ E),
      (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l) y)
          (EuclideanSpace.single j 1) *
        chosenMthMixedPartialChartPushedU
          (I := I) (M := M) g α u_h (m + 1) (Fin.cons i dirs) y)
    (fun i _hi => h_inner_sum i)

omit [NeZero (Module.finrank ℝ E)] in
private lemma layer_B_pair_memWkp
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) (m K : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (l i j : Fin (Module.finrank ℝ E))
    (h_chart_H_m_plus_2_K :
      MemWkp (d := Module.finrank ℝ E) ((m + 2) + K) 2
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
        (Ωα (I := I) (M := M) α)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y =>
        weightedInvGramDerivOnEuclid (I := I) g α i j l y *
        chosenMthMixedPartialChartPushedU
          (I := I) (M := M) g α u_h (m + 2)
          (Fin.cons i (Fin.snoc dirs j)) y)
      (Ωα (I := I) (M := M) α) := by
  classical
  have h_coef_smooth :
      ContDiffOn ℝ (⊤ : ℕ∞)
        (weightedInvGramDerivOnEuclid (I := I) g α i j l)
        (Ωα (I := I) (M := M) α) :=
    weightedInvGramDerivOnEuclid_contDiffOn (I := I) (M := M) g α i j l
  have h_factor_memWkp :
      MemWkp (d := Module.finrank ℝ E) K 2
        (chosenMthMixedPartialChartPushedU
          (I := I) (M := M) g α u_h (m + 2)
          (Fin.cons i (Fin.snoc dirs j)))
        (Ωα (I := I) (M := M) α) := by
    have h_parent_K_plus :
        MemWkp (d := Module.finrank ℝ E) (K + (m + 2)) 2
          (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
            ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
          (Ωα (I := I) (M := M) α) := by
      have h_eq : K + (m + 2) = (m + 2) + K := by ring
      rw [h_eq]; exact h_chart_H_m_plus_2_K
    exact chosenMthMixedPartialChartPushedU_memWkp_of_chartPushed_memWkp
      (I := I) (M := M) g α u_h (m + 2) K h_parent_K_plus
      (Fin.cons i (Fin.snoc dirs j))
  have h_factor_ae_zero :
      chosenMthMixedPartialChartPushedU
        (I := I) (M := M) g α u_h (m + 2) (Fin.cons i (Fin.snoc dirs j))
        =ᵐ[(volume : Measure EuclN).restrict
          (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)]
        (fun _ => (0 : ℝ)) := by
    have h_parent_m_plus_2 :
        MemWkp (d := Module.finrank ℝ E) (m + 2) 2
          (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
            ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
          (Ωα (I := I) (M := M) α) :=
      h_chart_H_m_plus_2_K.le_of_le (by omega)
    exact chosenMthMixed_ae_zero_off_Kα (I := I) (M := M) g α u_h (m + 2)
      h_parent_m_plus_2 (Fin.cons i (Fin.snoc dirs j))
  exact memWkp_coef_mul_factor (I := I) (M := M) α K h_coef_smooth
    h_factor_memWkp h_factor_ae_zero

omit [NeZero (Module.finrank ℝ E)] in
private lemma layer_B_memWkp
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) (m K : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (l : Fin (Module.finrank ℝ E))
    (h_chart_H_m_plus_2_K :
      MemWkp (d := Module.finrank ℝ E) ((m + 2) + K) 2
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
        (Ωα (I := I) (M := M) α)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramDerivOnEuclid (I := I) g α i j l y *
            chosenMthMixedPartialChartPushedU
              (I := I) (M := M) g α u_h (m + 2)
              (Fin.cons i (Fin.snoc dirs j)) y)
      (Ωα (I := I) (M := M) α) := by
  classical
  have h_inner_sum : ∀ i : Fin (Module.finrank ℝ E),
      MemWkp (d := Module.finrank ℝ E) K 2
        (fun y => ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramDerivOnEuclid (I := I) g α i j l y *
            chosenMthMixedPartialChartPushedU
              (I := I) (M := M) g α u_h (m + 2)
              (Fin.cons i (Fin.snoc dirs j)) y)
        (Ωα (I := I) (M := M) α) := by
    intro i
    exact memWkp_finset_sum_univ (I := I) (M := M)
      (α := α) (K := K) (s := Finset.univ)
      (f := fun j y =>
        weightedInvGramDerivOnEuclid (I := I) g α i j l y *
          chosenMthMixedPartialChartPushedU
            (I := I) (M := M) g α u_h (m + 2)
            (Fin.cons i (Fin.snoc dirs j)) y)
      (fun j _hj =>
        layer_B_pair_memWkp (I := I) (M := M) g α u_h m K dirs l i j
          h_chart_H_m_plus_2_K)
  exact memWkp_finset_sum_univ (I := I) (M := M)
    (α := α) (K := K) (s := Finset.univ)
    (f := fun i y => ∑ j : Fin (Module.finrank ℝ E),
      weightedInvGramDerivOnEuclid (I := I) g α i j l y *
        chosenMthMixedPartialChartPushedU
          (I := I) (M := M) g α u_h (m + 2)
          (Fin.cons i (Fin.snoc dirs j)) y)
    (fun i _hi => h_inner_sum i)

omit [NeZero (Module.finrank ℝ E)] in
private lemma layer_C_memWkp
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) (m K : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (l : Fin (Module.finrank ℝ E))
    (h_chart_H_m_K :
      MemWkp (d := Module.finrank ℝ E) (m + K) 2
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
        (Ωα (I := I) (M := M) α))
    (h_parent_m :
      MemWkp (d := Module.finrank ℝ E) m 2
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
        (Ωα (I := I) (M := M) α)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y =>
        densityDerivOnEuclid (I := I) g α l y *
        chosenMthMixedPartialChartPushedU
          (I := I) (M := M) g α u_h m dirs y)
      (Ωα (I := I) (M := M) α) := by
  classical
  have h_coef_smooth :
      ContDiffOn ℝ (⊤ : ℕ∞) (densityDerivOnEuclid (I := I) g α l)
        (Ωα (I := I) (M := M) α) :=
    densityDerivOnEuclid_contDiffOn (I := I) (M := M) g α l
  have h_factor_memWkp :
      MemWkp (d := Module.finrank ℝ E) K 2
        (chosenMthMixedPartialChartPushedU
          (I := I) (M := M) g α u_h m dirs)
        (Ωα (I := I) (M := M) α) := by
    have h_parent_K_plus :
        MemWkp (d := Module.finrank ℝ E) (K + m) 2
          (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
            ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
          (Ωα (I := I) (M := M) α) := by
      have h_eq : K + m = m + K := by ring
      rw [h_eq]; exact h_chart_H_m_K
    exact chosenMthMixedPartialChartPushedU_memWkp_of_chartPushed_memWkp
      (I := I) (M := M) g α u_h m K h_parent_K_plus dirs
  have h_factor_ae_zero :
      chosenMthMixedPartialChartPushedU
        (I := I) (M := M) g α u_h m dirs
        =ᵐ[(volume : Measure EuclN).restrict
          (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)]
        (fun _ => (0 : ℝ)) :=
    chosenMthMixed_ae_zero_off_Kα (I := I) (M := M) g α u_h m h_parent_m dirs
  exact memWkp_coef_mul_factor (I := I) (M := M) α K h_coef_smooth
    h_factor_memWkp h_factor_ae_zero

omit [NeZero (Module.finrank ℝ E)] in
private lemma layer_D_memWkp
    (g : SmoothRiemannianMetric I M) (α : M)
    (K : ℕ)
    (l : Fin (Module.finrank ℝ E))
    (prev_fChartEff : EuclN → ℝ)
    (h_prev_memWkp_K :
      MemWkp (d := Module.finrank ℝ E) K 2 prev_fChartEff
        (Ωα (I := I) (M := M) α))
    (h_prev_ae_zero : prev_fChartEff =ᵐ[(volume : Measure EuclN).restrict
      (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)]
      (fun _ => (0 : ℝ))) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => densityDerivOnEuclid (I := I) g α l y * prev_fChartEff y)
      (Ωα (I := I) (M := M) α) := by
  have h_coef_smooth :
      ContDiffOn ℝ (⊤ : ℕ∞) (densityDerivOnEuclid (I := I) g α l)
        (Ωα (I := I) (M := M) α) :=
    densityDerivOnEuclid_contDiffOn (I := I) (M := M) g α l
  exact memWkp_coef_mul_factor (I := I) (M := M) α K h_coef_smooth
    h_prev_memWkp_K h_prev_ae_zero

omit [NeZero (Module.finrank ℝ E)] in
private lemma layer_E_memWkp
    (g : SmoothRiemannianMetric I M) (α : M)
    (K : ℕ)
    (l : Fin (Module.finrank ℝ E))
    (prev_fChartEff : EuclN → ℝ)
    (h_prev_memWkp_succ :
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2 prev_fChartEff
        (Ωα (I := I) (M := M) α))
    (h_prev_ae_zero : prev_fChartEff =ᵐ[(volume : Measure EuclN).restrict
      (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)]
      (fun _ => (0 : ℝ))) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y =>
        densityOnEuclid (I := I) g α y *
        chosenWeakPartial' (d := Module.finrank ℝ E) 2 l prev_fChartEff
          (Ωα (I := I) (M := M) α) y)
      (Ωα (I := I) (M := M) α) := by
  have h_coef_smooth :
      ContDiffOn ℝ (⊤ : ℕ∞) (densityOnEuclid (I := I) g α)
        (Ωα (I := I) (M := M) α) :=
    densityOnEuclid_contDiffOn (I := I) g α
  have h_factor_memWkp :
      MemWkp (d := Module.finrank ℝ E) K 2
        (chosenWeakPartial' (d := Module.finrank ℝ E) 2 l prev_fChartEff
          (Ωα (I := I) (M := M) α))
        (Ωα (I := I) (M := M) α) :=
    h_prev_memWkp_succ.chosenWeakPartial_mem l
  have h_prev_memW1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      prev_fChartEff (Ωα (I := I) (M := M) α) := by
    have h_prev_memWkp_1 : MemWkp (d := Module.finrank ℝ E) 1 2 prev_fChartEff
        (Ωα (I := I) (M := M) α) := h_prev_memWkp_succ.le_of_le (by omega)
    rw [MemWkp.one_iff_memW1p] at h_prev_memWkp_1
    exact h_prev_memWkp_1
  have h_diff_open : IsOpen
      (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α) :=
    (Ωα_isOpen (I := I) (M := M) α).sdiff
      (Kα_compact (I := I) (M := M) α).isClosed
  have h_diff_subset :
      Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α ⊆
        Ωα (I := I) (M := M) α := fun _ hy => hy.1
  have h_factor_ae_zero :
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 l prev_fChartEff
        (Ωα (I := I) (M := M) α)
        =ᵐ[(volume : Measure EuclN).restrict
          (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)]
        (fun _ : EuclN => (0 : ℝ)) :=
    chosenWeakPartial'_ae_zero_on_open_sub_of_ae_zero
      (p := 2) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (Ωα_isOpen (I := I) (M := M) α) h_diff_open h_diff_subset
      h_prev_memW1p h_prev_ae_zero l
  exact memWkp_coef_mul_factor (I := I) (M := M) α K h_coef_smooth
    h_factor_memWkp h_factor_ae_zero

omit [NeZero (Module.finrank ℝ E)] in
private lemma fChartEffStepNumerator_memWkp
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) (m K : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (prev_fChartEff : EuclN → ℝ)
    (l : Fin (Module.finrank ℝ E))
    (h_prev_memWkp_succ :
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2 prev_fChartEff
        (Ωα (I := I) (M := M) α))
    (h_prev_ae_zero : prev_fChartEff =ᵐ[(volume : Measure EuclN).restrict
      (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)]
      (fun _ => (0 : ℝ)))
    (h_chart_H_u : MemWkp (d := Module.finrank ℝ E) (m + 2 + K) 2
      (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
      (Ωα (I := I) (M := M) α)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fChartEffStepNumerator (I := I) (M := M)
        g α u_h m dirs prev_fChartEff l)
      (Ωα (I := I) (M := M) α) := by
  classical
  have h_open : IsOpen (Ωα (I := I) (M := M) α) := Ωα_isOpen (I := I) (M := M) α
  have h_chart_H_m_plus_1_K : MemWkp (d := Module.finrank ℝ E) ((m + 1) + K) 2
      (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
      (Ωα (I := I) (M := M) α) :=
    h_chart_H_u.le_of_le (by omega)
  have h_chart_H_m_K : MemWkp (d := Module.finrank ℝ E) (m + K) 2
      (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
      (Ωα (I := I) (M := M) α) :=
    h_chart_H_u.le_of_le (by omega)
  have h_parent_m : MemWkp (d := Module.finrank ℝ E) m 2
      (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
      (Ωα (I := I) (M := M) α) :=
    h_chart_H_u.le_of_le (by omega)
  have hA := layer_A_memWkp (I := I) (M := M) g α u_h m K dirs l
    h_chart_H_m_plus_1_K
  have hB := layer_B_memWkp (I := I) (M := M) g α u_h m K dirs l
    h_chart_H_u
  have hC := layer_C_memWkp (I := I) (M := M) g α u_h m K dirs l
    h_chart_H_m_K h_parent_m
  have h_prev_memWkp_K : MemWkp (d := Module.finrank ℝ E) K 2 prev_fChartEff
      (Ωα (I := I) (M := M) α) := h_prev_memWkp_succ.le_of_le (by omega)
  have hD := layer_D_memWkp (I := I) (M := M) g α K l prev_fChartEff
    h_prev_memWkp_K h_prev_ae_zero
  have hE := layer_E_memWkp (I := I) (M := M) g α K l prev_fChartEff
    h_prev_memWkp_succ h_prev_ae_zero
  have h_step1 := MemWkp.add (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) h_open hA hB
  have h_step2 := MemWkp.sub (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) h_open h_step1 hC
  have h_step3 := MemWkp.add (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) h_open h_step2 hD
  have h_step4 := MemWkp.add (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) h_open h_step3 hE
  unfold fChartEffStepNumerator
  convert h_step4 using 2 with y

omit [NeZero (Module.finrank ℝ E)] in
private lemma fChartEffStepNumerator_ae_zero_off_Kα
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) (m : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (prev_fChartEff : EuclN → ℝ)
    (l : Fin (Module.finrank ℝ E))
    (h_prev_memW1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      prev_fChartEff (Ωα (I := I) (M := M) α))
    (h_prev_ae_zero : prev_fChartEff =ᵐ[(volume : Measure EuclN).restrict
      (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)]
      (fun _ => (0 : ℝ)))
    (h_chart_H_m_plus_2 :
      MemWkp (d := Module.finrank ℝ E) (m + 2) 2
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
        (Ωα (I := I) (M := M) α)) :
    fChartEffStepNumerator (I := I) (M := M) g α u_h m dirs prev_fChartEff l
      =ᵐ[(volume : Measure EuclN).restrict
        (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)]
      (fun _ : EuclN => (0 : ℝ)) := by
  classical
  have h_parent_m_plus_1 : MemWkp (d := Module.finrank ℝ E) (m + 1) 2
      (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
      (Ωα (I := I) (M := M) α) :=
    h_chart_H_m_plus_2.le_of_le (by omega)
  have h_parent_m : MemWkp (d := Module.finrank ℝ E) m 2
      (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
      (Ωα (I := I) (M := M) α) :=
    h_chart_H_m_plus_2.le_of_le (by omega)
  have hA_ae : ∀ i j : Fin (Module.finrank ℝ E),
      chosenMthMixedPartialChartPushedU
        (I := I) (M := M) g α u_h (m + 1) (Fin.cons i dirs)
        =ᵐ[(volume : Measure EuclN).restrict
          (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)]
        (fun _ => (0 : ℝ)) := fun i j =>
    chosenMthMixed_ae_zero_off_Kα (I := I) (M := M) g α u_h (m + 1)
      h_parent_m_plus_1 (Fin.cons i dirs)
  have hB_ae : ∀ i j : Fin (Module.finrank ℝ E),
      chosenMthMixedPartialChartPushedU
        (I := I) (M := M) g α u_h (m + 2) (Fin.cons i (Fin.snoc dirs j))
        =ᵐ[(volume : Measure EuclN).restrict
          (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)]
        (fun _ => (0 : ℝ)) := fun i j =>
    chosenMthMixed_ae_zero_off_Kα (I := I) (M := M) g α u_h (m + 2)
      h_chart_H_m_plus_2 (Fin.cons i (Fin.snoc dirs j))
  have hC_ae :
      chosenMthMixedPartialChartPushedU
        (I := I) (M := M) g α u_h m dirs
        =ᵐ[(volume : Measure EuclN).restrict
          (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)]
        (fun _ => (0 : ℝ)) :=
    chosenMthMixed_ae_zero_off_Kα (I := I) (M := M) g α u_h m h_parent_m dirs
  have h_diff_open : IsOpen
      (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α) :=
    (Ωα_isOpen (I := I) (M := M) α).sdiff
      (Kα_compact (I := I) (M := M) α).isClosed
  have h_diff_subset :
      Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α ⊆
        Ωα (I := I) (M := M) α := fun _ hy => hy.1
  have hE_ae :
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 l prev_fChartEff
        (Ωα (I := I) (M := M) α)
        =ᵐ[(volume : Measure EuclN).restrict
          (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)]
        (fun _ : EuclN => (0 : ℝ)) :=
    chosenWeakPartial'_ae_zero_on_open_sub_of_ae_zero
      (p := 2) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (Ωα_isOpen (I := I) (M := M) α) h_diff_open h_diff_subset
      h_prev_memW1p h_prev_ae_zero l
  unfold fChartEffStepNumerator
  have hA_sum_ae : (fun y => ∑ i : Fin (Module.finrank ℝ E),
      ∑ j : Fin (Module.finrank ℝ E),
        (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l) y)
            (EuclideanSpace.single j 1) *
          chosenMthMixedPartialChartPushedU
            (I := I) (M := M) g α u_h (m + 1) (Fin.cons i dirs) y)
      =ᵐ[(volume : Measure EuclN).restrict
        (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)]
      (fun _ => (0 : ℝ)) := by
    have h_all : ∀ᵐ y ∂((volume : Measure EuclN).restrict
        (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)),
        ∀ i : Fin (Module.finrank ℝ E), ∀ j : Fin (Module.finrank ℝ E),
          chosenMthMixedPartialChartPushedU
            (I := I) (M := M) g α u_h (m + 1) (Fin.cons i dirs) y = 0 := by
      rw [Filter.eventually_all]
      intro i
      rw [Filter.eventually_all]
      intro j
      exact hA_ae i j
    filter_upwards [h_all] with y hy
    refine Finset.sum_eq_zero ?_
    intro i _
    refine Finset.sum_eq_zero ?_
    intro j _
    change (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l) y)
        (EuclideanSpace.single j 1) *
      chosenMthMixedPartialChartPushedU
        (I := I) (M := M) g α u_h (m + 1) (Fin.cons i dirs) y = 0
    rw [hy i j]; ring
  have hB_sum_ae : (fun y => ∑ i : Fin (Module.finrank ℝ E),
      ∑ j : Fin (Module.finrank ℝ E),
        weightedInvGramDerivOnEuclid (I := I) g α i j l y *
          chosenMthMixedPartialChartPushedU
            (I := I) (M := M) g α u_h (m + 2)
            (Fin.cons i (Fin.snoc dirs j)) y)
      =ᵐ[(volume : Measure EuclN).restrict
        (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)]
      (fun _ => (0 : ℝ)) := by
    have h_all : ∀ᵐ y ∂((volume : Measure EuclN).restrict
        (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)),
        ∀ i : Fin (Module.finrank ℝ E), ∀ j : Fin (Module.finrank ℝ E),
          chosenMthMixedPartialChartPushedU
            (I := I) (M := M) g α u_h (m + 2)
            (Fin.cons i (Fin.snoc dirs j)) y = 0 := by
      rw [Filter.eventually_all]
      intro i
      rw [Filter.eventually_all]
      intro j
      exact hB_ae i j
    filter_upwards [h_all] with y hy
    refine Finset.sum_eq_zero ?_
    intro i _
    refine Finset.sum_eq_zero ?_
    intro j _
    change weightedInvGramDerivOnEuclid (I := I) g α i j l y *
      chosenMthMixedPartialChartPushedU
        (I := I) (M := M) g α u_h (m + 2)
        (Fin.cons i (Fin.snoc dirs j)) y = 0
    rw [hy i j]; ring
  have hC_term_ae : (fun y => densityDerivOnEuclid (I := I) g α l y *
      chosenMthMixedPartialChartPushedU
        (I := I) (M := M) g α u_h m dirs y)
      =ᵐ[(volume : Measure EuclN).restrict
        (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)]
      (fun _ => (0 : ℝ)) := by
    filter_upwards [hC_ae] with y hy
    show densityDerivOnEuclid (I := I) g α l y *
      chosenMthMixedPartialChartPushedU
        (I := I) (M := M) g α u_h m dirs y = 0
    rw [hy]; ring
  have hD_term_ae : (fun y => densityDerivOnEuclid (I := I) g α l y *
      prev_fChartEff y)
      =ᵐ[(volume : Measure EuclN).restrict
        (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)]
      (fun _ => (0 : ℝ)) := by
    filter_upwards [h_prev_ae_zero] with y hy
    show densityDerivOnEuclid (I := I) g α l y * prev_fChartEff y = 0
    rw [hy]; ring
  have hE_term_ae : (fun y => densityOnEuclid (I := I) g α y *
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 l prev_fChartEff
        (Ωα (I := I) (M := M) α) y)
      =ᵐ[(volume : Measure EuclN).restrict
        (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)]
      (fun _ => (0 : ℝ)) := by
    filter_upwards [hE_ae] with y hy
    show densityOnEuclid (I := I) g α y *
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 l prev_fChartEff
        (Ωα (I := I) (M := M) α) y = 0
    rw [hy]; ring
  filter_upwards [hA_sum_ae, hB_sum_ae, hC_term_ae, hD_term_ae, hE_term_ae]
    with y hA hB hC hD hE
  change ((∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l) y)
              (EuclideanSpace.single j 1) *
            chosenMthMixedPartialChartPushedU
              (I := I) (M := M) g α u_h (m + 1) (Fin.cons i dirs) y) +
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramDerivOnEuclid (I := I) g α i j l y *
            chosenMthMixedPartialChartPushedU
              (I := I) (M := M) g α u_h (m + 2)
              (Fin.cons i (Fin.snoc dirs j)) y) -
      densityDerivOnEuclid (I := I) g α l y *
        chosenMthMixedPartialChartPushedU
          (I := I) (M := M) g α u_h m dirs y +
      densityDerivOnEuclid (I := I) g α l y * prev_fChartEff y +
      densityOnEuclid (I := I) g α y *
        chosenWeakPartial' (d := Module.finrank ℝ E) 2 l prev_fChartEff
          (Ωα (I := I) (M := M) α) y) = 0
  rw [hA, hB, hC, hD, hE]; ring

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma one_div_densityOnEuclid_contDiffOn
    (g : SmoothRiemannianMetric I M) (α : M) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y => 1 / densityOnEuclid (I := I) g α y)
      (Ωα (I := I) (M := M) α) := by
  have h_dens_smooth : ContDiffOn ℝ (⊤ : ℕ∞)
      (densityOnEuclid (I := I) g α) (Ωα (I := I) (M := M) α) :=
    densityOnEuclid_contDiffOn (I := I) g α
  have h_ne : ∀ y ∈ Ωα (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y ≠ 0 := fun y hy =>
    (densityOnEuclid_pos (I := I) g α hy).ne'
  have h_const : ContDiffOn ℝ (⊤ : ℕ∞) (fun _ : EuclN => (1 : ℝ))
      (Ωα (I := I) (M := M) α) := contDiffOn_const
  exact h_const.div h_dens_smooth h_ne

omit [NeZero (Module.finrank ℝ E)] in
private lemma fChartEffStepNumerator_div_density_memWkp
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) (m K : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (prev_fChartEff : EuclN → ℝ)
    (l : Fin (Module.finrank ℝ E))
    (h_prev_memWkp_succ :
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2 prev_fChartEff
        (Ωα (I := I) (M := M) α))
    (h_prev_ae_zero : prev_fChartEff =ᵐ[(volume : Measure EuclN).restrict
      (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)]
      (fun _ => (0 : ℝ)))
    (h_chart_H_u : MemWkp (d := Module.finrank ℝ E) (m + 2 + K) 2
      (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
      (Ωα (I := I) (M := M) α)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y =>
        fChartEffStepNumerator (I := I) (M := M) g α u_h m dirs
          prev_fChartEff l y /
        densityOnEuclid (I := I) g α y)
      (Ωα (I := I) (M := M) α) := by
  classical
  have h_eq : (fun y =>
      fChartEffStepNumerator (I := I) (M := M) g α u_h m dirs
        prev_fChartEff l y /
      densityOnEuclid (I := I) g α y) =
      (fun y => (1 / densityOnEuclid (I := I) g α y) *
        fChartEffStepNumerator (I := I) (M := M) g α u_h m dirs
          prev_fChartEff l y) := by
    funext y
    rw [one_div, mul_comm, ← div_eq_mul_inv]
  rw [h_eq]
  have h_num_memWkp :=
    fChartEffStepNumerator_memWkp (I := I) (M := M) g α u_h m K dirs
      prev_fChartEff l h_prev_memWkp_succ h_prev_ae_zero h_chart_H_u
  have h_prev_memW1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      prev_fChartEff (Ωα (I := I) (M := M) α) := by
    have h_prev_memWkp_1 : MemWkp (d := Module.finrank ℝ E) 1 2 prev_fChartEff
        (Ωα (I := I) (M := M) α) := h_prev_memWkp_succ.le_of_le (by omega)
    rw [MemWkp.one_iff_memW1p] at h_prev_memWkp_1
    exact h_prev_memWkp_1
  have h_chart_H_m_plus_2 :
      MemWkp (d := Module.finrank ℝ E) (m + 2) 2
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
        (Ωα (I := I) (M := M) α) :=
    h_chart_H_u.le_of_le (by omega)
  have h_num_ae_zero :=
    fChartEffStepNumerator_ae_zero_off_Kα (I := I) (M := M) g α u_h m dirs
      prev_fChartEff l h_prev_memW1p h_prev_ae_zero h_chart_H_m_plus_2
  exact memWkp_coef_mul_factor (I := I) (M := M) α K
    (one_div_densityOnEuclid_contDiffOn (I := I) (M := M) g α)
    h_num_memWkp h_num_ae_zero

omit [NeZero (Module.finrank ℝ E)] in
theorem fChartEffStep_memWkp_K_two
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) (m K : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (prev_fChartEff : EuclN → ℝ)
    (l : Fin (Module.finrank ℝ E))
    (h_prev_memWkp_succ :
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2 prev_fChartEff
        (chartTargetEuclid (I := I) (M := M) α))
    (h_prev_ae_zero : prev_fChartEff =ᵐ[(volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α \
        chartImagePOUTsupport (I := I) (M := M) α)]
      (fun _ => (0 : ℝ)))
    (h_chart_H_u : MemWkp (d := Module.finrank ℝ E) (m + 2 + K) 2
      (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
      (chartTargetEuclid (I := I) (M := M) α)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fChartEffStep (I := I) (M := M) g α u_h m dirs prev_fChartEff l)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set Q : EuclN → ℝ := fun y =>
    fChartEffStepNumerator (I := I) (M := M) g α u_h m dirs
      prev_fChartEff l y /
    densityOnEuclid (I := I) g α y with hQ_def
  have hQ_memWkp : MemWkp (d := Module.finrank ℝ E) K 2 Q
      (Ωα (I := I) (M := M) α) :=
    fChartEffStepNumerator_div_density_memWkp (I := I) (M := M) g α u_h m K dirs
      prev_fChartEff l h_prev_memWkp_succ h_prev_ae_zero h_chart_H_u
  have h_prev_memW1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      prev_fChartEff (Ωα (I := I) (M := M) α) := by
    have h_prev_memWkp_1 : MemWkp (d := Module.finrank ℝ E) 1 2 prev_fChartEff
        (Ωα (I := I) (M := M) α) := h_prev_memWkp_succ.le_of_le (by omega)
    rw [MemWkp.one_iff_memW1p] at h_prev_memWkp_1
    exact h_prev_memWkp_1
  have h_chart_H_m_plus_2 :
      MemWkp (d := Module.finrank ℝ E) (m + 2) 2
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
        (Ωα (I := I) (M := M) α) :=
    h_chart_H_u.le_of_le (by omega)
  have h_num_ae_zero :=
    fChartEffStepNumerator_ae_zero_off_Kα (I := I) (M := M) g α u_h m dirs
      prev_fChartEff l h_prev_memW1p h_prev_ae_zero h_chart_H_m_plus_2
  have hQ_ae_zero : Q =ᵐ[(volume : Measure EuclN).restrict
      (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)]
      (fun _ => (0 : ℝ)) := by
    filter_upwards [h_num_ae_zero] with y hy
    change fChartEffStepNumerator (I := I) (M := M) g α u_h m dirs
        prev_fChartEff l y / densityOnEuclid (I := I) g α y = 0
    rw [hy]; simp
  have h_fStep_ae_eq_Q :
      fChartEffStep (I := I) (M := M) g α u_h m dirs prev_fChartEff l =ᵐ[
        (volume : Measure EuclN).restrict (Ωα (I := I) (M := M) α)] Q := by
    set Ω : Set EuclN := Ωα (I := I) (M := M) α with hΩ_def
    have hΩ_meas : MeasurableSet Ω :=
      (Ωα_isOpen (I := I) (M := M) α).measurableSet
    have hKα_meas : MeasurableSet (Kα (I := I) (M := M) α) :=
      Kα_meas (I := I) (M := M) α
    have hKα_sub_Ω : Kα (I := I) (M := M) α ⊆ Ω :=
      Kα_subset_Ωα (I := I) (M := M) α
    have h_eq_on_Kα : fChartEffStep (I := I) (M := M) g α u_h m dirs
        prev_fChartEff l =ᵐ[(volume : Measure EuclN).restrict
          (Kα (I := I) (M := M) α)] Q := by
      refine (ae_restrict_iff' hKα_meas).mpr ?_
      refine Filter.Eventually.of_forall fun y hy => ?_
      unfold fChartEffStep
      rw [Set.indicator_of_mem hy]
    have h_diff_meas : MeasurableSet (Ω \ Kα (I := I) (M := M) α) :=
      hΩ_meas.diff hKα_meas
    have h_fStep_ae_zero : fChartEffStep (I := I) (M := M) g α u_h m dirs
        prev_fChartEff l =ᵐ[(volume : Measure EuclN).restrict
          (Ω \ Kα (I := I) (M := M) α)] (fun _ => (0 : ℝ)) := by
      refine (ae_restrict_iff' h_diff_meas).mpr ?_
      refine Filter.Eventually.of_forall fun y hy => ?_
      unfold fChartEffStep
      exact Set.indicator_of_notMem hy.2 _
    have h_eq_on_diff : fChartEffStep (I := I) (M := M) g α u_h m dirs
        prev_fChartEff l =ᵐ[(volume : Measure EuclN).restrict
          (Ω \ Kα (I := I) (M := M) α)] Q := by
      filter_upwards [h_fStep_ae_zero, hQ_ae_zero] with y h0 hQ
      rw [h0, hQ]
    have hKα_inter_Ω : Kα (I := I) (M := M) α = Ω ∩ Kα (I := I) (M := M) α := by
      rw [Set.inter_eq_self_of_subset_right hKα_sub_Ω]
    have h_eq_on_inter : fChartEffStep (I := I) (M := M) g α u_h m dirs
        prev_fChartEff l =ᵐ[(volume : Measure EuclN).restrict
          (Ω ∩ Kα (I := I) (M := M) α)] Q := by
      rw [← hKα_inter_Ω]
      exact h_eq_on_Kα
    have h_cover : Ω = (Ω ∩ Kα (I := I) (M := M) α) ∪
        (Ω \ Kα (I := I) (M := M) α) := by
      ext y; constructor
      · intro hy
        by_cases h : y ∈ Kα (I := I) (M := M) α
        · exact Or.inl ⟨hy, h⟩
        · exact Or.inr ⟨hy, h⟩
      · rintro (⟨hy, _⟩ | ⟨hy, _⟩) <;> exact hy
    have h_disj : Disjoint (Ω ∩ Kα (I := I) (M := M) α)
        (Ω \ Kα (I := I) (M := M) α) := by
      refine Set.disjoint_left.mpr ?_
      intro y hy hy'; exact hy'.2 hy.2
    have hΩ_restrict_eq : (volume : Measure EuclN).restrict Ω =
        (volume : Measure EuclN).restrict ((Ω ∩ Kα (I := I) (M := M) α) ∪
          (Ω \ Kα (I := I) (M := M) α)) := by
      rw [← h_cover]
    rw [hΩ_restrict_eq, MeasureTheory.Measure.restrict_union h_disj h_diff_meas]
    exact (MeasureTheory.ae_add_measure_iff).mpr ⟨h_eq_on_inter, h_eq_on_diff⟩
  exact (MemWkp_congr_ae (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) (Ωα_isOpen (I := I) (M := M) α)
    h_fStep_ae_eq_Q).mpr hQ_memWkp

omit [NeZero (Module.finrank ℝ E)] in
theorem fChartEffStep_memW1p_two
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) (m : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (prev_fChartEff : EuclN → ℝ)
    (l : Fin (Module.finrank ℝ E))
    (h_prev_memWkp_two :
      MemWkp (d := Module.finrank ℝ E) 2 2 prev_fChartEff
        (chartTargetEuclid (I := I) (M := M) α))
    (h_prev_ae_zero : prev_fChartEff =ᵐ[(volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α \
        chartImagePOUTsupport (I := I) (M := M) α)]
      (fun _ => (0 : ℝ)))
    (h_chart_H_u : MemWkp (d := Module.finrank ℝ E) (m + 3) 2
      (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
      (chartTargetEuclid (I := I) (M := M) α)) :
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (fChartEffStep (I := I) (M := M) g α u_h m dirs prev_fChartEff l)
      (chartTargetEuclid (I := I) (M := M) α) := by
  have h_prev_memWkp_succ : MemWkp (d := Module.finrank ℝ E) (1 + 1) 2
      prev_fChartEff (chartTargetEuclid (I := I) (M := M) α) := by
    have h_eq : (1 + 1 : ℕ) = 2 := by norm_num
    rw [h_eq]; exact h_prev_memWkp_two
  have h_chart_H_u' : MemWkp (d := Module.finrank ℝ E) (m + 2 + 1) 2
      (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
      (chartTargetEuclid (I := I) (M := M) α) := by
    have h_eq : m + 2 + 1 = m + 3 := by ring
    rw [h_eq]; exact h_chart_H_u
  have h_mem := fChartEffStep_memWkp_K_two (I := I) (M := M) g α u_h m 1 dirs
    prev_fChartEff l h_prev_memWkp_succ h_prev_ae_zero h_chart_H_u'
  rw [MemWkp.one_iff_memW1p] at h_mem
  exact h_mem

end IteratedFChartEffStepRegularity
end Laplacian
end Analysis
end DifferentialGeometry

end
