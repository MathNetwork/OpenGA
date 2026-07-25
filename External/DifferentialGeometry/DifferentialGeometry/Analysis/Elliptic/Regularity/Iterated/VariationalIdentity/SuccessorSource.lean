import DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.VariationalIdentity.DifferentiatedData
import DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.Differentiated.CrossTermIBP
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Multiplication.SmoothCoefWeakPartialIBP


noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace IteratedVariationalIdentityStepScaffold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.ChartPushedWeakPartialOnVolume
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainChartData
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.IteratedMixedPartials
open DifferentialGeometry.Analysis.Laplacian.IteratedDifferentiatedData
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

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma Kα_compact (α : M) :
    IsCompact (Kα (I := I) (M := M) α) :=
  chartImagePOUTsupport_isCompact (I := I) (M := M) α

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma Kα_meas (α : M) :
    MeasurableSet (Kα (I := I) (M := M) α) :=
  (Kα_compact (I := I) (M := M) α).isClosed.measurableSet

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma Kα_subset_target (α : M) :
    Kα (I := I) (M := M) α ⊆ chartTargetEuclid (I := I) (M := M) α :=
  chartImagePOUTsupport_subset_target (I := I) (M := M) α

omit [NeZero (Module.finrank ℝ E)] in
theorem per_pair_ibp_chosenMthMixed
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g} (m : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (h_chart_regularity :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (m + 1) 2
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
          (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α))
    {φ : EuclN → ℝ}
    (hφ_chart : ContDiffOn ℝ (⊤ : ℕ∞) φ
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α))
    {ψ : EuclN → ℝ} (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆
      DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α)
    (l : Fin (Module.finrank ℝ E)) :
    (∫ y in DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α,
        φ y *
        chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h m dirs y *
        (fderiv ℝ ψ y) (EuclideanSpace.single l 1)
        ∂(volume : Measure EuclN))
    = -((∫ y in DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α,
          (fderiv ℝ φ y) (EuclideanSpace.single l 1) *
          chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h m dirs y *
          ψ y
          ∂(volume : Measure EuclN))
      + (∫ y in DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α,
          φ y *
          chosenMthMixedPartialChartPushedU
            (I := I) (M := M) g α u_h (m + 1) (Fin.snoc dirs l) y *
          ψ y
          ∂(volume : Measure EuclN))) := by
  classical
  set Ω : Set EuclN :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
      (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α
  set v : EuclN → ℝ :=
    chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h m dirs with hv_def
  set w : Fin (Module.finrank ℝ E) → EuclN → ℝ := fun j =>
    chosenMthMixedPartialChartPushedU
      (I := I) (M := M) g α u_h (m + 1) (Fin.snoc dirs j) with hw_def
  have h_v_memW1p :
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 v Ω :=
    chosenMthMixedPartialChartPushedU_memW1p_two
      (I := I) (M := M) g α u_h m h_chart_regularity dirs
  have h_w_eq : ∀ j : Fin (Module.finrank ℝ E),
      w j = DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) 2 j v Ω := by
    intro j
    change chosenMthMixedPartialChartPushedU
        (I := I) (M := M) g α u_h (m + 1) (Fin.snoc dirs j) =
      DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) 2 j v Ω
    rw [chosenMthMixedPartialChartPushedU_succ]
    have h_last : Fin.snoc (α := fun _ => Fin (Module.finrank ℝ E)) dirs j
        (Fin.last m) = j := by simp
    have h_init : Fin.init (Fin.snoc (α := fun _ => Fin (Module.finrank ℝ E))
        dirs j) = dirs := by simp
    rw [h_last, h_init]
  have hw_isWeakPartial : ∀ j : Fin (Module.finrank ℝ E),
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) j (w j) v Ω := by
    intro j
    rw [h_w_eq j]
    exact DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_isWeakPartial_of_mem
      h_v_memW1p j
  have hv_global_memLp : MemLp v 2 ((volume : Measure EuclN).restrict Ω) :=
    h_v_memW1p.1
  have hv_locMemLp : ∀ K' : Set EuclN, IsCompact K' → K' ⊆ Ω →
      MemLp v 2 ((volume : Measure EuclN).restrict K') := by
    intro K' hK'_compact hK'_in
    have hK'_meas : MeasurableSet K' := hK'_compact.isClosed.measurableSet
    have h_eq : ((volume : Measure EuclN).restrict Ω).restrict K' =
        (volume : Measure EuclN).restrict K' := by
      rw [Measure.restrict_restrict hK'_meas]
      congr 1
      exact Set.inter_eq_self_of_subset_left hK'_in
    rw [← h_eq]
    exact hv_global_memLp.restrict K'
  have hw_global_memLp : ∀ j : Fin (Module.finrank ℝ E),
      MemLp (w j) 2 ((volume : Measure EuclN).restrict Ω) := by
    intro j
    rw [h_w_eq j]
    exact DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_memLp_of_mem
      h_v_memW1p j
  have hw_locMemLp : ∀ (j : Fin (Module.finrank ℝ E)) (K' : Set EuclN),
      IsCompact K' → K' ⊆ Ω →
      MemLp (w j) 2 ((volume : Measure EuclN).restrict K') := by
    intro j K' hK'_compact hK'_in
    have hK'_meas : MeasurableSet K' := hK'_compact.isClosed.measurableSet
    have h_eq : ((volume : Measure EuclN).restrict Ω).restrict K' =
        (volume : Measure EuclN).restrict K' := by
      rw [Measure.restrict_restrict hK'_meas]
      congr 1
      exact Set.inter_eq_self_of_subset_left hK'_in
    rw [← h_eq]
    exact (hw_global_memLp j).restrict K'
  set K : Set EuclN := tsupport ψ with hK_def
  have hK_compact : IsCompact K := hψ_cs
  have hK_in : K ⊆ Ω := hψ_supp
  obtain ⟨δ, φExt, hδ_pos, hδ_subset, hφExt_smooth, hφExt_eq⟩ :=
    DifferentialGeometry.Analysis.Laplacian.DifferentiatedCrossTermIBP.exists_smooth_global_extension
      (I := I) (M := M) (φ := φ) α hφ_chart hK_compact hK_in
  have h_ibp_ext :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.integral_smul_weak_partial_eq
      (d := Module.finrank ℝ E) (Ω := Ω) hΩ_open
      (φ := φExt) hφExt_smooth (v := v) (w := w)
      hv_locMemLp hw_locMemLp hw_isWeakPartial l
      (ψ := ψ) hψ_smooth hψ_cs hψ_supp
  have hΩ_meas : MeasurableSet Ω := hΩ_open.measurableSet
  have hcthick_subset : Metric.cthickening δ K ⊆ Ω := hδ_subset
  have hK_in_thickening : K ⊆ Metric.cthickening δ K :=
    Metric.self_subset_cthickening _
  have h_fderiv_zero_outside_K : ∀ x ∉ K, fderiv ℝ ψ x = 0 := by
    intro x hx
    have h_compl_open : IsOpen (Kᶜ) := (isClosed_tsupport _).isOpen_compl
    have hx_in_compl : x ∈ Kᶜ := hx
    have hψ_zero_nbhd : ∀ᶠ y in 𝓝 x, ψ y = 0 := by
      filter_upwards [h_compl_open.mem_nhds hx_in_compl] with y hy
      exact image_eq_zero_of_notMem_tsupport hy
    have hψ_const_zero : fderiv ℝ ψ x = fderiv ℝ (fun _ : EuclN => (0 : ℝ)) x := by
      apply Filter.EventuallyEq.fderiv_eq
      filter_upwards [hψ_zero_nbhd] with y hy
      rw [hy]
    rw [hψ_const_zero]; simp
  have hLHS_eq :
      ∫ y in Ω, φExt y * v y *
          (fderiv ℝ ψ y) (EuclideanSpace.single l 1) ∂(volume : Measure EuclN) =
      ∫ y in Ω, φ y * v y *
          (fderiv ℝ ψ y) (EuclideanSpace.single l 1) ∂(volume : Measure EuclN) := by
    refine setIntegral_congr_fun hΩ_meas (fun y hy => ?_)
    by_cases hy_K : y ∈ K
    · rw [hφExt_eq y (hK_in_thickening hy_K)]
    · rw [h_fderiv_zero_outside_K y hy_K]
      simp
  have h_fderiv_φExt_eq_φ_on_K : ∀ y ∈ K, ∀ j' : Fin (Module.finrank ℝ E),
      (fderiv ℝ φExt y) (EuclideanSpace.single j' 1) =
      (fderiv ℝ φ y) (EuclideanSpace.single j' 1) := by
    intro y hy_K j'
    have hy_thick : y ∈ Metric.cthickening δ K := hK_in_thickening hy_K
    have hy_thick_open : y ∈ Metric.thickening δ K := by
      rw [Metric.mem_thickening_iff]
      refine ⟨y, hy_K, ?_⟩
      simp [hδ_pos]
    have h_thick_open : IsOpen (Metric.thickening δ K) := Metric.isOpen_thickening
    have h_nbhd : Metric.thickening δ K ∈ 𝓝 y := h_thick_open.mem_nhds hy_thick_open
    have h_thick_sub : Metric.thickening δ K ⊆ Metric.cthickening δ K :=
      Metric.thickening_subset_cthickening _ _
    have h_eq_nbhd : φExt =ᶠ[𝓝 y] φ := by
      filter_upwards [h_nbhd] with z hz
      exact hφExt_eq z (h_thick_sub hz)
    have h_fderiv_eq : fderiv ℝ φExt y = fderiv ℝ φ y :=
      Filter.EventuallyEq.fderiv_eq h_eq_nbhd
    rw [h_fderiv_eq]
  have hLeibniz1_eq :
      ∫ y in Ω, (fderiv ℝ φExt y) (EuclideanSpace.single l 1) * v y * ψ y
        ∂(volume : Measure EuclN) =
      ∫ y in Ω, (fderiv ℝ φ y) (EuclideanSpace.single l 1) * v y * ψ y
        ∂(volume : Measure EuclN) := by
    refine setIntegral_congr_fun hΩ_meas (fun y hy => ?_)
    by_cases hy_K : y ∈ K
    · rw [h_fderiv_φExt_eq_φ_on_K y hy_K l]
    · have hψy : ψ y = 0 := image_eq_zero_of_notMem_tsupport hy_K
      rw [hψy]; ring
  have hLeibniz2_eq :
      ∫ y in Ω, φExt y * w l y * ψ y ∂(volume : Measure EuclN) =
      ∫ y in Ω, φ y * w l y * ψ y ∂(volume : Measure EuclN) := by
    refine setIntegral_congr_fun hΩ_meas (fun y hy => ?_)
    by_cases hy_K : y ∈ K
    · rw [hφExt_eq y (hK_in_thickening hy_K)]
    · have hψy : ψ y = 0 := image_eq_zero_of_notMem_tsupport hy_K
      rw [hψy]; ring
  rw [← hLHS_eq, ← hLeibniz1_eq, ← hLeibniz2_eq]
  exact h_ibp_ext

noncomputable def fChartEffStepNumerator
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) (m : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (fChartEffPrev : EuclN → ℝ)
    (l : Fin (Module.finrank ℝ E))
    (y : EuclN) : ℝ :=
  (∑ i : Fin (Module.finrank ℝ E),
    ∑ j : Fin (Module.finrank ℝ E),
      (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l) y)
          (EuclideanSpace.single j 1) *
        chosenMthMixedPartialChartPushedU
          (I := I) (M := M) g α u_h (m + 1) (Fin.cons i dirs) y)
  + (∑ i : Fin (Module.finrank ℝ E),
      ∑ j : Fin (Module.finrank ℝ E),
        weightedInvGramDerivOnEuclid (I := I) g α i j l y *
          chosenMthMixedPartialChartPushedU
            (I := I) (M := M) g α u_h (m + 2)
            (Fin.cons i (Fin.snoc dirs j)) y)
  - densityDerivOnEuclid (I := I) g α l y *
      chosenMthMixedPartialChartPushedU
        (I := I) (M := M) g α u_h m dirs y
  + densityDerivOnEuclid (I := I) g α l y * fChartEffPrev y
  + densityOnEuclid (I := I) g α y *
      DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) 2 l fChartEffPrev
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α) y

noncomputable def fChartEffStep
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) (m : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (fChartEffPrev : EuclN → ℝ)
    (l : Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  Set.indicator (chartImagePOUTsupport (I := I) (M := M) α)
    (fun y => fChartEffStepNumerator
        (I := I) (M := M) g α u_h m dirs fChartEffPrev l y /
      densityOnEuclid (I := I) g α y)

omit [NeZero (Module.finrank ℝ E)] in
theorem fChartEffStep_def_unfold
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) (m : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (fChartEffPrev : EuclN → ℝ)
    (l : Fin (Module.finrank ℝ E))
    (y : EuclN) :
    fChartEffStep (I := I) (M := M) g α u_h m dirs fChartEffPrev l y =
      Set.indicator (chartImagePOUTsupport (I := I) (M := M) α)
        (fun z => fChartEffStepNumerator
          (I := I) (M := M) g α u_h m dirs fChartEffPrev l z /
          densityOnEuclid (I := I) g α z) y := rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem density_mul_fChartEffStep_eq_indicator_numerator
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) (m : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (fChartEffPrev : EuclN → ℝ)
    (l : Fin (Module.finrank ℝ E))
    (y : EuclN)
    (hy : y ∈ DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
      (I := I) (M := M) α) :
    densityOnEuclid (I := I) g α y *
        fChartEffStep (I := I) (M := M) g α u_h m dirs fChartEffPrev l y =
      Set.indicator (chartImagePOUTsupport (I := I) (M := M) α)
        (fun z => fChartEffStepNumerator
          (I := I) (M := M) g α u_h m dirs fChartEffPrev l z) y := by
  classical
  rw [fChartEffStep_def_unfold]
  by_cases hy_K : y ∈ chartImagePOUTsupport (I := I) (M := M) α
  · rw [Set.indicator_of_mem hy_K, Set.indicator_of_mem hy_K]
    have h_pos : 0 < densityOnEuclid (I := I) g α y :=
      densityOnEuclid_pos (I := I) g α hy
    field_simp
  · rw [Set.indicator_of_notMem hy_K, Set.indicator_of_notMem hy_K, mul_zero]

omit [NeZero (Module.finrank ℝ E)] in
theorem fChartEffStep_supported_in_chartImagePOUTsupport
    {g : SmoothRiemannianMetric I M} {α : M}
    {u_h : H1Compl (I := I) (M := M) g} {m : ℕ}
    {dirs : Fin m → Fin (Module.finrank ℝ E)}
    {fChartEffPrev : EuclN → ℝ}
    {l : Fin (Module.finrank ℝ E)} :
    Function.support
        (fChartEffStep (I := I) (M := M) g α u_h m dirs fChartEffPrev l) ⊆
      chartImagePOUTsupport (I := I) (M := M) α := by
  unfold fChartEffStep
  exact Set.support_indicator_subset

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma exists_bound_continuousOn_compact
    {f : EuclN → ℝ} {α : M}
    (hf_contOn :
      ContinuousOn f
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α))
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_in : K ⊆ DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
      (I := I) (M := M) α) :
    ∃ C : ℝ, ∀ y ∈ K, |f y| ≤ C := by
  classical
  by_cases hK_empty : K = ∅
  · refine ⟨0, ?_⟩
    intro y hy
    rw [hK_empty] at hy
    exact absurd hy (Set.notMem_empty y)
  have hK_ne : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hK_empty
  have hf_K : ContinuousOn f K := hf_contOn.mono hK_in
  have h_abs_K : ContinuousOn (fun y => |f y|) K :=
    continuous_abs.comp_continuousOn hf_K
  obtain ⟨y_max, _hy_max_K, h_max⟩ :=
    hK_compact.exists_isMaxOn hK_ne h_abs_K
  exact ⟨|f y_max|, fun y hy => h_max hy⟩

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma memLp_two_of_bounded_mul
    {f h : EuclN → ℝ} {K : Set EuclN}
    (hh_meas : AEStronglyMeasurable h ((volume : Measure EuclN).restrict K))
    {C : ℝ}
    (hh_bd : ∀ᵐ y ∂((volume : Measure EuclN).restrict K), |h y| ≤ C)
    (hf : MemLp f 2 ((volume : Measure EuclN).restrict K)) :
    MemLp (fun y => h y * f y) 2 ((volume : Measure EuclN).restrict K) := by
  classical
  have hh_memLp_top : MemLp h ∞ ((volume : Measure EuclN).restrict K) := by
    refine ⟨hh_meas, ?_⟩
    rw [eLpNorm_exponent_top]
    refine lt_of_le_of_lt ?_
      (show (ENNReal.ofReal (max C 0) : ℝ≥0∞) < ⊤ from
        ENNReal.ofReal_lt_top)
    refine eLpNormEssSup_le_of_ae_enorm_bound (C := ENNReal.ofReal (max C 0)) ?_
    refine hh_bd.mono (fun y hy => ?_)
    rw [Real.enorm_eq_ofReal_abs]
    apply ENNReal.ofReal_le_ofReal
    exact hy.trans (le_max_left _ _)
  exact MemLp.mul' (p := ∞) (q := 2) (r := 2) hf hh_memLp_top

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma memLp_two_continuousOn_mul_on_Kα
    {α : M} {h f : EuclN → ℝ}
    (hh_contOn : ContinuousOn h
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α))
    (hf : MemLp f 2
      ((volume : Measure EuclN).restrict (Kα (I := I) (M := M) α))) :
    MemLp (fun y => h y * f y) 2
      ((volume : Measure EuclN).restrict (Kα (I := I) (M := M) α)) := by
  classical
  obtain ⟨C, hC_bd⟩ :=
    exists_bound_continuousOn_compact (I := I) (M := M) (α := α)
      hh_contOn (Kα_compact (I := I) (M := M) α)
      (Kα_subset_target (I := I) (M := M) α)
  have h_meas :
      AEStronglyMeasurable h
        ((volume : Measure EuclN).restrict (Kα (I := I) (M := M) α)) := by
    have h_K : ContinuousOn h (Kα (I := I) (M := M) α) :=
      hh_contOn.mono (Kα_subset_target (I := I) (M := M) α)
    exact h_K.aestronglyMeasurable (Kα_meas (I := I) (M := M) α)
  have h_ae_bd : ∀ᵐ y ∂((volume : Measure EuclN).restrict
      (Kα (I := I) (M := M) α)),
      |h y| ≤ C := by
    refine (ae_restrict_iff' (Kα_meas (I := I) (M := M) α)).mpr ?_
    refine Filter.Eventually.of_forall ?_
    intro y hy
    exact hC_bd y hy
  exact memLp_two_of_bounded_mul (h := h) h_meas h_ae_bd hf

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma chartPulledWeightedMeasure_restrict_compact_le_volume
    {g : SmoothRiemannianMetric I M} (α : M)
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_meas : MeasurableSet K)
    (hK_in : K ⊆ DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
      (I := I) (M := M) α) :
    ∃ c : ℝ, 0 < c ∧
      (chartPulledWeightedMeasure (I := I) g α).restrict K ≤
        ENNReal.ofReal c • ((volume : Measure EuclN).restrict K) := by
  classical
  obtain ⟨_c_min, c_max, hc_min_pos, hc_le, h_bd⟩ :=
    densityOnEuclid_bounded_on_compact (I := I) (M := M) g α hK_compact hK_in
  refine ⟨c_max, lt_of_lt_of_le hc_min_pos hc_le, ?_⟩
  refine Measure.le_iff.2 ?_
  intro A hA
  rw [Measure.restrict_apply hA, Measure.smul_apply,
    Measure.restrict_apply hA]
  unfold chartPulledWeightedMeasure
  rw [withDensity_apply _ (hA.inter hK_meas)]
  have h_pointwise_bd :
      ∫⁻ y in A ∩ K,
          ENNReal.ofReal (densityOnEuclid (I := I) g α y)
            ∂(volume : Measure EuclN) ≤
      ∫⁻ _y in A ∩ K, ENNReal.ofReal c_max ∂(volume : Measure EuclN) := by
    apply MeasureTheory.setLIntegral_mono_ae'
    · exact hA.inter hK_meas
    · refine Filter.Eventually.of_forall fun y hy => ?_
      apply ENNReal.ofReal_le_ofReal
      exact (h_bd y hy.2).2
  have h_const_eval :
      ∫⁻ _y in A ∩ K, ENNReal.ofReal c_max ∂(volume : Measure EuclN) =
      ENNReal.ofReal c_max * (volume : Measure EuclN) (A ∩ K) := by
    rw [MeasureTheory.setLIntegral_const]
  rw [smul_eq_mul]
  exact h_pointwise_bd.trans (le_of_eq h_const_eval)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma memLp_chartPulledWeighted_restrict_of_volume_restrict
    {g : SmoothRiemannianMetric I M} {α : M} {w : EuclN → ℝ}
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_meas : MeasurableSet K)
    (hK_in : K ⊆ DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
      (I := I) (M := M) α)
    (hw : MemLp w 2 ((volume : Measure EuclN).restrict K)) :
    MemLp w 2 ((chartPulledWeightedMeasure (I := I) g α).restrict K) := by
  obtain ⟨c, _hc_pos, h_le⟩ :=
    chartPulledWeightedMeasure_restrict_compact_le_volume (I := I) (M := M)
      α hK_compact hK_meas hK_in
  exact hw.of_measure_le_smul (c := ENNReal.ofReal c)
    ENNReal.ofReal_ne_top h_le

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma weightedInvGramDerivOnEuclid_partial_continuousOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j l : Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (fun y => (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l) y)
        (EuclideanSpace.single j 1))
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) := by
  have h_open : IsOpen (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
      (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α
  have h_diffOn :
      ContDiffOn ℝ (⊤ : ℕ∞) (weightedInvGramDerivOnEuclid (I := I) g α i j l)
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α) :=
    weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α i j l
  have h_fderiv_diff :
      ContDiffOn ℝ (⊤ : ℕ∞)
        (fun y => fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l) y)
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α) :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen h_open).1 h_diffOn).2
  have h_eval : ContDiff ℝ (⊤ : ℕ∞)
      (fun (L : EuclN →L[ℝ] ℝ) => L (EuclideanSpace.single j 1)) :=
    (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single j (1 : ℝ))).contDiff
  have h := h_eval.contDiffOn.comp h_fderiv_diff (mapsTo_univ _ _)
  exact h.continuousOn

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma memLp_restrict_Kα_of_memLp_chartTarget
    (α : M) {f : EuclN → ℝ}
    (hf : MemLp f 2 ((volume : Measure EuclN).restrict
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α))) :
    MemLp f 2 ((volume : Measure EuclN).restrict (Kα (I := I) (M := M) α)) := by
  have hK_meas : MeasurableSet (Kα (I := I) (M := M) α) :=
    Kα_meas (I := I) (M := M) α
  have h_eq : ((volume : Measure EuclN).restrict
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α)).restrict
        (Kα (I := I) (M := M) α) =
      (volume : Measure EuclN).restrict (Kα (I := I) (M := M) α) := by
    rw [Measure.restrict_restrict hK_meas]
    congr 1
    exact Set.inter_eq_self_of_subset_left
      (Kα_subset_target (I := I) (M := M) α)
  rw [← h_eq]
  exact hf.restrict _

omit [NeZero (Module.finrank ℝ E)] in
private lemma termA_pair_memLp_vol_K
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g} (m : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (h_chart_regularity_1 :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (m + 1) 2
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
          (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α))
    (l : Fin (Module.finrank ℝ E))
    (i j : Fin (Module.finrank ℝ E)) :
    MemLp (fun y =>
        (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l) y)
            (EuclideanSpace.single j 1) *
        chosenMthMixedPartialChartPushedU
          (I := I) (M := M) g α u_h (m + 1) (Fin.cons i dirs) y) 2
      ((volume : Measure EuclN).restrict (Kα (I := I) (M := M) α)) := by
  classical
  have h_factor :
      MemLp (chosenMthMixedPartialChartPushedU
        (I := I) (M := M) g α u_h (m + 1) (Fin.cons i dirs)) 2
        ((volume : Measure EuclN).restrict (Kα (I := I) (M := M) α)) :=
    chosenMthMixedPartialChartPushedU_locally_memLp
      (I := I) (M := M) g α u_h (m + 1) h_chart_regularity_1
      (Fin.cons i dirs)
      (Kα_compact (I := I) (M := M) α)
      (Kα_subset_target (I := I) (M := M) α)
  exact memLp_two_continuousOn_mul_on_Kα (α := α)
    (weightedInvGramDerivOnEuclid_partial_continuousOn
      (I := I) (M := M) g α i j l) h_factor

omit [NeZero (Module.finrank ℝ E)] in
private lemma termB_pair_memLp_vol_K
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g} (m : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (h_chart_regularity_2 :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (m + 2) 2
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
          (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α))
    (l : Fin (Module.finrank ℝ E))
    (i j : Fin (Module.finrank ℝ E)) :
    MemLp (fun y =>
        weightedInvGramDerivOnEuclid (I := I) g α i j l y *
        chosenMthMixedPartialChartPushedU
          (I := I) (M := M) g α u_h (m + 2)
          (Fin.cons i (Fin.snoc dirs j)) y) 2
      ((volume : Measure EuclN).restrict (Kα (I := I) (M := M) α)) := by
  classical
  have h_factor :
      MemLp (chosenMthMixedPartialChartPushedU
        (I := I) (M := M) g α u_h (m + 2)
        (Fin.cons i (Fin.snoc dirs j))) 2
        ((volume : Measure EuclN).restrict (Kα (I := I) (M := M) α)) :=
    chosenMthMixedPartialChartPushedU_locally_memLp
      (I := I) (M := M) g α u_h (m + 2) h_chart_regularity_2
      (Fin.cons i (Fin.snoc dirs j))
      (Kα_compact (I := I) (M := M) α)
      (Kα_subset_target (I := I) (M := M) α)
  exact memLp_two_continuousOn_mul_on_Kα (α := α)
    (weightedInvGramDerivOnEuclid_continuousOn (I := I) g α i j l) h_factor

omit [NeZero (Module.finrank ℝ E)] in
private lemma termC_memLp_vol_K
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g} (m : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (h_chart_regularity_1 :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (m + 1) 2
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
          (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α))
    (l : Fin (Module.finrank ℝ E)) :
    MemLp (fun y =>
        densityDerivOnEuclid (I := I) g α l y *
        chosenMthMixedPartialChartPushedU
          (I := I) (M := M) g α u_h m dirs y) 2
      ((volume : Measure EuclN).restrict (Kα (I := I) (M := M) α)) := by
  classical
  have h_parent_m :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) m 2
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
          (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α) := by
    exact h_chart_regularity_1.le_succ
  have h_factor :
      MemLp (chosenMthMixedPartialChartPushedU
        (I := I) (M := M) g α u_h m dirs) 2
        ((volume : Measure EuclN).restrict (Kα (I := I) (M := M) α)) :=
    chosenMthMixedPartialChartPushedU_locally_memLp
      (I := I) (M := M) g α u_h m h_parent_m dirs
      (Kα_compact (I := I) (M := M) α)
      (Kα_subset_target (I := I) (M := M) α)
  exact memLp_two_continuousOn_mul_on_Kα (α := α)
    (densityDerivOnEuclid_continuousOn (I := I) g α l) h_factor

omit [NeZero (Module.finrank ℝ E)] in
private lemma termD_memLp_vol_K
    {g : SmoothRiemannianMetric I M} {α : M}
    (fChartEffPrev : EuclN → ℝ)
    (h_prev_memLp_weighted :
      MemLp fChartEffPrev 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α)))
    (l : Fin (Module.finrank ℝ E)) :
    MemLp (fun y =>
        densityDerivOnEuclid (I := I) g α l y * fChartEffPrev y) 2
      ((volume : Measure EuclN).restrict (Kα (I := I) (M := M) α)) := by
  classical
  have h_prev_vol_K :
      MemLp fChartEffPrev 2
        ((volume : Measure EuclN).restrict (Kα (I := I) (M := M) α)) :=
    memLp_volume_restrict_of_memLp_chartPulledWeightedMeasure
      (I := I) (M := M) (g := g) (α := α) h_prev_memLp_weighted
      (Kα_compact (I := I) (M := M) α)
      (Kα_meas (I := I) (M := M) α)
      (Kα_subset_target (I := I) (M := M) α)
  exact memLp_two_continuousOn_mul_on_Kα (α := α)
    (densityDerivOnEuclid_continuousOn (I := I) g α l) h_prev_vol_K

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma termE_memLp_vol_K
    (g : SmoothRiemannianMetric I M) (α : M)
    (fChartEffPrev : EuclN → ℝ)
    (l : Fin (Module.finrank ℝ E)) :
    MemLp (fun y =>
        densityOnEuclid (I := I) g α y *
        DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          (d := Module.finrank ℝ E) 2 l fChartEffPrev
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α) y) 2
      ((volume : Measure EuclN).restrict (Kα (I := I) (M := M) α)) := by
  classical
  by_cases h_memW1p :
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 fChartEffPrev
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α)
  · have h_global :
        MemLp (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          (d := Module.finrank ℝ E) 2 l fChartEffPrev
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α)) 2
          ((volume : Measure EuclN).restrict
            (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
              (I := I) (M := M) α)) :=
      DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_memLp_of_mem
        h_memW1p l
    have h_K :
        MemLp (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          (d := Module.finrank ℝ E) 2 l fChartEffPrev
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α)) 2
          ((volume : Measure EuclN).restrict (Kα (I := I) (M := M) α)) :=
      memLp_restrict_Kα_of_memLp_chartTarget (I := I) (M := M) α h_global
    exact memLp_two_continuousOn_mul_on_Kα (α := α)
      (densityOnEuclid_continuousOn (I := I) g α) h_K
  · have h_zero :
        DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          (d := Module.finrank ℝ E) 2 l fChartEffPrev
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α) = 0 :=
      DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_of_not_mem
        h_memW1p l
    have : (fun y => densityOnEuclid (I := I) g α y *
        DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          (d := Module.finrank ℝ E) 2 l fChartEffPrev
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α) y) = (fun _ => 0) := by
      funext y
      rw [h_zero]; simp
    rw [this]
    exact MemLp.zero

omit [NeZero (Module.finrank ℝ E)] in
private lemma fChartEffStepNumerator_memLp_vol_K
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) (m : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (h_chart_regularity_1 :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (m + 1) 2
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
          (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α))
    (h_chart_regularity_2 :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (m + 2) 2
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
          (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α))
    (fChartEffPrev : EuclN → ℝ)
    (h_prev_memLp_weighted :
      MemLp fChartEffPrev 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α)))
    (l : Fin (Module.finrank ℝ E)) :
    MemLp (fChartEffStepNumerator (I := I) (M := M)
        g α u_h m dirs fChartEffPrev l) 2
      ((volume : Measure EuclN).restrict (Kα (I := I) (M := M) α)) := by
  classical
  have hA : MemLp (fun y => (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l) y)
              (EuclideanSpace.single j 1) *
            chosenMthMixedPartialChartPushedU
              (I := I) (M := M) g α u_h (m + 1) (Fin.cons i dirs) y)) 2
        ((volume : Measure EuclN).restrict (Kα (I := I) (M := M) α)) := by
    apply memLp_finset_sum
    intro i _
    apply memLp_finset_sum
    intro j _
    exact termA_pair_memLp_vol_K (I := I) (M := M) g α m dirs
      h_chart_regularity_1 l i j
  have hB : MemLp (fun y => (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramDerivOnEuclid (I := I) g α i j l y *
            chosenMthMixedPartialChartPushedU
              (I := I) (M := M) g α u_h (m + 2)
              (Fin.cons i (Fin.snoc dirs j)) y)) 2
        ((volume : Measure EuclN).restrict (Kα (I := I) (M := M) α)) := by
    apply memLp_finset_sum
    intro i _
    apply memLp_finset_sum
    intro j _
    exact termB_pair_memLp_vol_K (I := I) (M := M) g α m dirs
      h_chart_regularity_2 l i j
  have hC := termC_memLp_vol_K (I := I) (M := M) g α m dirs
    h_chart_regularity_1 l
  have hD := termD_memLp_vol_K (I := I) (M := M) (g := g) (α := α)
    fChartEffPrev h_prev_memLp_weighted l
  have hE := termE_memLp_vol_K (I := I) (M := M) g α
    fChartEffPrev l
  have h_step1 := hA.add hB
  have h_step2 := h_step1.sub hC
  have h_step3 := h_step2.add hD
  have h_step4 := h_step3.add hE
  unfold fChartEffStepNumerator
  convert h_step4 using 2 with y

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma one_div_densityOnEuclid_continuousOn
    (g : SmoothRiemannianMetric I M) (α : M) :
    ContinuousOn (fun y => 1 / densityOnEuclid (I := I) g α y)
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) := by
  have h_cont := densityOnEuclid_continuousOn (I := I) g α
  have h_inv := h_cont.inv₀ (fun y hy =>
    (densityOnEuclid_pos (I := I) g α hy).ne')
  have h_eq : (fun y => 1 / densityOnEuclid (I := I) g α y) =
      (fun y => (densityOnEuclid (I := I) g α y)⁻¹) := by
    funext y; rw [one_div]
  rw [h_eq]
  exact h_inv

omit [NeZero (Module.finrank ℝ E)] in
private lemma fChartEffStepNumerator_div_density_memLp_vol_K
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) (m : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (h_chart_regularity_1 :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (m + 1) 2
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
          (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α))
    (h_chart_regularity_2 :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (m + 2) 2
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
          (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α))
    (fChartEffPrev : EuclN → ℝ)
    (h_prev_memLp_weighted :
      MemLp fChartEffPrev 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α)))
    (l : Fin (Module.finrank ℝ E)) :
    MemLp (fun y => fChartEffStepNumerator
        (I := I) (M := M) g α u_h m dirs fChartEffPrev l y /
        densityOnEuclid (I := I) g α y) 2
      ((volume : Measure EuclN).restrict (Kα (I := I) (M := M) α)) := by
  classical
  have h_num := fChartEffStepNumerator_memLp_vol_K
    (I := I) (M := M) g α u_h m dirs
    h_chart_regularity_1 h_chart_regularity_2 fChartEffPrev
    h_prev_memLp_weighted l
  have h_eq : (fun y => fChartEffStepNumerator
      (I := I) (M := M) g α u_h m dirs fChartEffPrev l y /
      densityOnEuclid (I := I) g α y) =
      fun y => (1 / densityOnEuclid (I := I) g α y) *
        fChartEffStepNumerator
          (I := I) (M := M) g α u_h m dirs fChartEffPrev l y := by
    funext y
    rw [one_div, mul_comm, ← div_eq_mul_inv]
  rw [h_eq]
  exact memLp_two_continuousOn_mul_on_Kα (α := α)
    (one_div_densityOnEuclid_continuousOn (I := I) (M := M) g α) h_num

omit [NeZero (Module.finrank ℝ E)] in
theorem fChartEffStep_memLp_two_weighted
    {g : SmoothRiemannianMetric I M} {α : M}
    {u_h : H1Compl (I := I) (M := M) g} {m : ℕ}
    {dirs : Fin m → Fin (Module.finrank ℝ E)}
    (h_chart_regularity_1 :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (m + 1) 2
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
          (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α))
    (h_chart_regularity_2 :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (m + 2) 2
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
          (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α))
    {fChartEffPrev : EuclN → ℝ}
    (h_prev_memLp_weighted :
      MemLp fChartEffPrev 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α)))
    {l : Fin (Module.finrank ℝ E)} :
    MemLp (fChartEffStep (I := I) (M := M) g α
        u_h m dirs fChartEffPrev l) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α)) := by
  classical
  set K : Set EuclN := Kα (I := I) (M := M) α with hK_def
  set f : EuclN → ℝ := fun y =>
    fChartEffStepNumerator
      (I := I) (M := M) g α u_h m dirs fChartEffPrev l y /
      densityOnEuclid (I := I) g α y with hf_def
  have h_indicator_eq :
      fChartEffStep (I := I) (M := M) g α
          u_h m dirs fChartEffPrev l =
        Set.indicator K f := by
    rfl
  rw [h_indicator_eq]
  have h_chartTarget_meas : MeasurableSet
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) :=
    (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α).measurableSet
  have hK_meas : MeasurableSet K := Kα_meas (I := I) (M := M) α
  have hK_compact : IsCompact K := Kα_compact (I := I) (M := M) α
  have hK_in : K ⊆ DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
      (I := I) (M := M) α :=
    Kα_subset_target (I := I) (M := M) α
  rw [memLp_indicator_iff_restrict hK_meas]
  have h_double_restrict :
      ((chartPulledWeightedMeasure (I := I) g α).restrict
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α)).restrict K =
      (chartPulledWeightedMeasure (I := I) g α).restrict K := by
    rw [Measure.restrict_restrict hK_meas]
    congr 1
    exact Set.inter_eq_self_of_subset_left hK_in
  rw [h_double_restrict]
  refine memLp_chartPulledWeighted_restrict_of_volume_restrict
    (g := g) (α := α) hK_compact hK_meas hK_in ?_
  exact fChartEffStepNumerator_div_density_memLp_vol_K
    (I := I) (M := M) g α u_h m dirs
    h_chart_regularity_1 h_chart_regularity_2 fChartEffPrev
    h_prev_memLp_weighted l

end IteratedVariationalIdentityStepScaffold
end Laplacian
end Analysis
end DifferentialGeometry

end
