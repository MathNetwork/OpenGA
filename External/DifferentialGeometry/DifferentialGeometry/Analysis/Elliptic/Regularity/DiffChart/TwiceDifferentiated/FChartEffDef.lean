import DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.Differentiated.FChartEffDef
import DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.TwiceDifferentiated.BilinearH1Compl
import DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.NirenbergInterior.ThirdMixedPartial


noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace FChartEffTwiceDef

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.ChartPushedWeakPartialOnVolume
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainChartData
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.ChosenThirdMixedPartialChartPushed
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

noncomputable def fChartDeriv2
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (l₁ l₂ : Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
    (d := Module.finrank ℝ E) 2 l₂
    (chosenFChartDeriv (I := I) (M := M) g α hu_h l₁)
    (chartTargetEuclid (I := I) (M := M) α)

noncomputable def effectiveSourceChartSecondOrderNumerator
    (g : SmoothRiemannianMetric I M) (α : M)
    (l₁ l₂ : Fin (Module.finrank ℝ E))
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (y : EuclN) : ℝ :=
  (∑ i : Fin (Module.finrank ℝ E),
    ∑ j : Fin (Module.finrank ℝ E),
      (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l₂) y)
          (EuclideanSpace.single j 1) *
        chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₁ y)
  + (∑ i : Fin (Module.finrank ℝ E),
      ∑ j : Fin (Module.finrank ℝ E),
        weightedInvGramDerivOnEuclid (I := I) g α i j l₂ y *
          chosenThirdMixedPartialChartPushedU (I := I) (M := M) g α u_h i l₁ j y)
  - densityDerivOnEuclid (I := I) g α l₂ y *
      (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
        (laplacianDomainPow_succ_subset_laplacianDomain
          (I := I) (M := M) g 1 hu_h)).weak_partial l₁ y
  + densityDerivOnEuclid (I := I) g α l₂ y *
      chosenFChartDeriv (I := I) (M := M) g α hu_h l₁ y
  + densityOnEuclid (I := I) g α y *
      fChartDeriv2 (I := I) (M := M) g α hu_h l₁ l₂ y
  + (∑ i : Fin (Module.finrank ℝ E),
      ∑ j : Fin (Module.finrank ℝ E),
        (fderiv ℝ (weightedInvGramSecondDerivOnEuclid (I := I) g α i j l₁ l₂) y)
            (EuclideanSpace.single j 1) *
          (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
            (laplacianDomainPow_succ_subset_laplacianDomain
              (I := I) (M := M) g 1 hu_h)).weak_partial i y)
  + (∑ i : Fin (Module.finrank ℝ E),
      ∑ j : Fin (Module.finrank ℝ E),
        weightedInvGramSecondDerivOnEuclid (I := I) g α i j l₁ l₂ y *
          chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i j y)
  + (∑ i : Fin (Module.finrank ℝ E),
      ∑ j : Fin (Module.finrank ℝ E),
        (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l₁) y)
            (EuclideanSpace.single j 1) *
          chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₂ y)
  + (∑ i : Fin (Module.finrank ℝ E),
      ∑ j : Fin (Module.finrank ℝ E),
        weightedInvGramDerivOnEuclid (I := I) g α i j l₁ y *
          chosenThirdMixedPartialChartPushedU (I := I) (M := M) g α u_h i l₂ j y)
  - densitySecondDerivOnEuclid (I := I) g α l₁ l₂ y *
      (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
        (laplacianDomainPow_succ_subset_laplacianDomain
          (I := I) (M := M) g 1 hu_h)).u_chart y
  - densityDerivOnEuclid (I := I) g α l₁ y *
      (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
        (laplacianDomainPow_succ_subset_laplacianDomain
          (I := I) (M := M) g 1 hu_h)).weak_partial l₂ y
  + densitySecondDerivOnEuclid (I := I) g α l₁ l₂ y *
      (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
        (laplacianDomainPow_succ_subset_laplacianDomain
          (I := I) (M := M) g 1 hu_h)).f_chart y
  + densityDerivOnEuclid (I := I) g α l₁ y *
      chosenFChartDeriv (I := I) (M := M) g α hu_h l₂ y

noncomputable def effectiveSourceChartSecondOrder
    (g : SmoothRiemannianMetric I M) (α : M)
    (l₁ l₂ : Fin (Module.finrank ℝ E))
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    EuclN → ℝ :=
  Set.indicator (chartImagePOUTsupport (I := I) (M := M) α)
    (fun y => effectiveSourceChartSecondOrderNumerator (I := I) (M := M) g α l₁ l₂ hu_h y /
      densityOnEuclid (I := I) g α y)

theorem fChartEffTwice_def_unfold
    (g : SmoothRiemannianMetric I M) (α : M)
    (l₁ l₂ : Fin (Module.finrank ℝ E))
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (y : EuclN) :
    effectiveSourceChartSecondOrder (I := I) (M := M) g α l₁ l₂ hu_h y =
      Set.indicator (chartImagePOUTsupport (I := I) (M := M) α)
        (fun z => effectiveSourceChartSecondOrderNumerator (I := I) (M := M) g α l₁ l₂ hu_h z /
          densityOnEuclid (I := I) g α z) y := rfl

theorem density_mul_fChartEffTwice_eq_indicator_numerator
    (g : SmoothRiemannianMetric I M) (α : M)
    (l₁ l₂ : Fin (Module.finrank ℝ E))
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (y : EuclN)
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    densityOnEuclid (I := I) g α y *
        effectiveSourceChartSecondOrder (I := I) (M := M) g α l₁ l₂ hu_h y =
      Set.indicator (chartImagePOUTsupport (I := I) (M := M) α)
        (fun z => effectiveSourceChartSecondOrderNumerator (I := I) (M := M) g α l₁ l₂ hu_h z) y := by
  classical
  rw [fChartEffTwice_def_unfold]
  by_cases hy_K : y ∈ chartImagePOUTsupport (I := I) (M := M) α
  · rw [Set.indicator_of_mem hy_K, Set.indicator_of_mem hy_K]
    have h_pos : 0 < densityOnEuclid (I := I) g α y :=
      densityOnEuclid_pos (I := I) g α hy
    field_simp
  · rw [Set.indicator_of_notMem hy_K, Set.indicator_of_notMem hy_K, mul_zero]

theorem fChartEffTwice_supported_in_chartImagePOUTsupport
    {g : SmoothRiemannianMetric I M} {α : M}
    {l₁ l₂ : Fin (Module.finrank ℝ E)}
    {u_h : H1Compl g} {hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2} :
    Function.support (effectiveSourceChartSecondOrder (I := I) (M := M) g α l₁ l₂ hu_h) ⊆
      chartImagePOUTsupport (I := I) (M := M) α := by
  unfold effectiveSourceChartSecondOrder
  exact Set.support_indicator_subset

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma exists_bound_continuousOn_compact
    {f : EuclN → ℝ} {α : M}
    (hf_contOn :
      ContinuousOn f (chartTargetEuclid (I := I) (M := M) α))
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
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

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma memLp_two_continuousOn_mul_on_Kα
    {α : M} {h f : EuclN → ℝ}
    (hh_contOn : ContinuousOn h (chartTargetEuclid (I := I) (M := M) α))
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
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
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
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α)
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
      (chartTargetEuclid (I := I) (M := M) α) := by
  have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_diffOn :
      ContDiffOn ℝ (⊤ : ℕ∞) (weightedInvGramDerivOnEuclid (I := I) g α i j l)
        (chartTargetEuclid (I := I) (M := M) α) :=
    weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α i j l
  have h_fderiv_diff :
      ContDiffOn ℝ (⊤ : ℕ∞)
        (fun y => fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l) y)
        (chartTargetEuclid (I := I) (M := M) α) :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen h_open).1 h_diffOn).2
  have h_eval : ContDiff ℝ (⊤ : ℕ∞)
      (fun (L : EuclN →L[ℝ] ℝ) => L (EuclideanSpace.single j 1)) :=
    (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single j (1 : ℝ))).contDiff
  have h := h_eval.contDiffOn.comp h_fderiv_diff (mapsTo_univ _ _)
  exact h.continuousOn

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma weightedInvGramSecondDerivOnEuclid_partial_continuousOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j l₁ l₂ : Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (fun y => (fderiv ℝ (weightedInvGramSecondDerivOnEuclid
          (I := I) g α i j l₁ l₂) y)
        (EuclideanSpace.single j 1))
      (chartTargetEuclid (I := I) (M := M) α) := by
  have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_diffOn :
      ContDiffOn ℝ (⊤ : ℕ∞)
        (weightedInvGramSecondDerivOnEuclid (I := I) g α i j l₁ l₂)
        (chartTargetEuclid (I := I) (M := M) α) :=
    weightedInvGramSecondDerivOnEuclid_contDiffOn (I := I) g α i j l₁ l₂
  have h_fderiv_diff :
      ContDiffOn ℝ (⊤ : ℕ∞)
        (fun y => fderiv ℝ
          (weightedInvGramSecondDerivOnEuclid (I := I) g α i j l₁ l₂) y)
        (chartTargetEuclid (I := I) (M := M) α) :=
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
      (chartTargetEuclid (I := I) (M := M) α))) :
    MemLp f 2 ((volume : Measure EuclN).restrict (Kα (I := I) (M := M) α)) := by
  have hK_meas : MeasurableSet (Kα (I := I) (M := M) α) :=
    Kα_meas (I := I) (M := M) α
  have h_eq : ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)).restrict
        (Kα (I := I) (M := M) α) =
      (volume : Measure EuclN).restrict (Kα (I := I) (M := M) α) := by
    rw [Measure.restrict_restrict hK_meas]
    congr 1
    exact Set.inter_eq_self_of_subset_left
      (Kα_subset_target (I := I) (M := M) α)
  rw [← h_eq]
  exact hf.restrict _

private lemma termA1_pair_memLp_vol_K
    (g : SmoothRiemannianMetric I M) (α : M)
    (l₁ l₂ : Fin (Module.finrank ℝ E))
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (i j : Fin (Module.finrank ℝ E)) :
    MemLp (fun y =>
        (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l₂) y)
            (EuclideanSpace.single j 1) *
        chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₁ y) 2
      ((volume : Measure EuclN).restrict (Kα (I := I) (M := M) α)) := by
  classical
  have h_second_K :
      MemLp (chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₁) 2
        ((volume : Measure EuclN).restrict (Kα (I := I) (M := M) α)) :=
    chosenSecondPartialChartPushedU_locally_memLp
      (I := I) (M := M) g α hu_h i l₁
      (Kα_compact (I := I) (M := M) α)
      (Kα_subset_target (I := I) (M := M) α)
  exact memLp_two_continuousOn_mul_on_Kα (α := α)
    (weightedInvGramDerivOnEuclid_partial_continuousOn
      (I := I) (M := M) g α i j l₂) h_second_K

private lemma termA2_pair_memLp_vol_K
    (g : SmoothRiemannianMetric I M) (α : M)
    (l₁ l₂ : Fin (Module.finrank ℝ E))
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (i j : Fin (Module.finrank ℝ E)) :
    MemLp (fun y =>
        weightedInvGramDerivOnEuclid (I := I) g α i j l₂ y *
        chosenThirdMixedPartialChartPushedU (I := I) (M := M) g α u_h i l₁ j y) 2
      ((volume : Measure EuclN).restrict (Kα (I := I) (M := M) α)) := by
  classical
  have h_third_K :
      MemLp (chosenThirdMixedPartialChartPushedU
        (I := I) (M := M) g α u_h i l₁ j) 2
        ((volume : Measure EuclN).restrict (Kα (I := I) (M := M) α)) :=
    chosenThirdMixedPartialChartPushedU_locally_memLp
      (I := I) (M := M) g α hu_h i l₁ j
      (Kα_compact (I := I) (M := M) α)
      (Kα_subset_target (I := I) (M := M) α)
  exact memLp_two_continuousOn_mul_on_Kα (α := α)
    (weightedInvGramDerivOnEuclid_continuousOn (I := I) g α i j l₂) h_third_K

private lemma termA3_memLp_vol_K
    (g : SmoothRiemannianMetric I M) (α : M)
    (l₁ l₂ : Fin (Module.finrank ℝ E))
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    MemLp (fun y => densityDerivOnEuclid (I := I) g α l₂ y *
        (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).weak_partial l₁ y) 2
      ((volume : Measure EuclN).restrict (Kα (I := I) (M := M) α)) := by
  classical
  have h_wp_K :
      MemLp ((chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
            (laplacianDomainPow_succ_subset_laplacianDomain
              (I := I) (M := M) g 1 hu_h)).weak_partial l₁) 2
        ((volume : Measure EuclN).restrict (Kα (I := I) (M := M) α)) :=
    (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
      (laplacianDomainPow_succ_subset_laplacianDomain
        (I := I) (M := M) g 1 hu_h)).weak_partial_locally_memLp l₁
      (Kα (I := I) (M := M) α)
      (Kα_compact (I := I) (M := M) α)
      (Kα_subset_target (I := I) (M := M) α)
  exact memLp_two_continuousOn_mul_on_Kα (α := α)
    (densityDerivOnEuclid_continuousOn (I := I) g α l₂) h_wp_K

private lemma termB1_memLp_vol_K
    (g : SmoothRiemannianMetric I M) (α : M)
    (l₁ l₂ : Fin (Module.finrank ℝ E))
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    MemLp (fun y => densityDerivOnEuclid (I := I) g α l₂ y *
        chosenFChartDeriv (I := I) (M := M) g α hu_h l₁ y) 2
      ((volume : Measure EuclN).restrict (Kα (I := I) (M := M) α)) := by
  classical
  by_cases h_memW1p :
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
        (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).f_chart
        (chartTargetEuclid (I := I) (M := M) α)
  · have h_global :
        MemLp (chosenFChartDeriv (I := I) (M := M) g α hu_h l₁) 2
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)) := by
      unfold chosenFChartDeriv
      exact chosenWeakPartial'_memLp_of_mem h_memW1p l₁
    have h_K :
        MemLp (chosenFChartDeriv (I := I) (M := M) g α hu_h l₁) 2
          ((volume : Measure EuclN).restrict (Kα (I := I) (M := M) α)) :=
      memLp_restrict_Kα_of_memLp_chartTarget (I := I) (M := M) α h_global
    exact memLp_two_continuousOn_mul_on_Kα (α := α)
      (densityDerivOnEuclid_continuousOn (I := I) g α l₂) h_K
  · have h_zero :
        chosenFChartDeriv (I := I) (M := M) g α hu_h l₁ = 0 := by
      unfold chosenFChartDeriv
      exact chosenWeakPartial'_of_not_mem h_memW1p l₁
    have : (fun y => densityDerivOnEuclid (I := I) g α l₂ y *
        chosenFChartDeriv (I := I) (M := M) g α hu_h l₁ y) = (fun _ => 0) := by
      funext y
      rw [h_zero]; simp
    rw [this]
    exact MemLp.zero

private lemma termB2_memLp_vol_K
    (g : SmoothRiemannianMetric I M) (α : M)
    (l₁ l₂ : Fin (Module.finrank ℝ E))
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    MemLp (fun y => densityOnEuclid (I := I) g α y *
        fChartDeriv2 (I := I) (M := M) g α hu_h l₁ l₂ y) 2
      ((volume : Measure EuclN).restrict (Kα (I := I) (M := M) α)) := by
  classical
  by_cases h_memW1p :
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
        (chosenFChartDeriv (I := I) (M := M) g α hu_h l₁)
        (chartTargetEuclid (I := I) (M := M) α)
  · have h_global :
        MemLp (fChartDeriv2 (I := I) (M := M) g α hu_h l₁ l₂) 2
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)) := by
      unfold fChartDeriv2
      exact chosenWeakPartial'_memLp_of_mem h_memW1p l₂
    have h_K :
        MemLp (fChartDeriv2 (I := I) (M := M) g α hu_h l₁ l₂) 2
          ((volume : Measure EuclN).restrict (Kα (I := I) (M := M) α)) :=
      memLp_restrict_Kα_of_memLp_chartTarget (I := I) (M := M) α h_global
    exact memLp_two_continuousOn_mul_on_Kα (α := α)
      (densityOnEuclid_continuousOn (I := I) g α) h_K
  · have h_zero :
        fChartDeriv2 (I := I) (M := M) g α hu_h l₁ l₂ = 0 := by
      unfold fChartDeriv2
      exact chosenWeakPartial'_of_not_mem h_memW1p l₂
    have : (fun y => densityOnEuclid (I := I) g α y *
        fChartDeriv2 (I := I) (M := M) g α hu_h l₁ l₂ y) = (fun _ => 0) := by
      funext y
      rw [h_zero]; simp
    rw [this]
    exact MemLp.zero

private lemma termC1_pair_memLp_vol_K
    (g : SmoothRiemannianMetric I M) (α : M)
    (l₁ l₂ : Fin (Module.finrank ℝ E))
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (i j : Fin (Module.finrank ℝ E)) :
    MemLp (fun y =>
        (fderiv ℝ
            (weightedInvGramSecondDerivOnEuclid (I := I) g α i j l₁ l₂) y)
            (EuclideanSpace.single j 1) *
        (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).weak_partial i y) 2
      ((volume : Measure EuclN).restrict (Kα (I := I) (M := M) α)) := by
  classical
  have h_wp_K :
      MemLp ((chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
            (laplacianDomainPow_succ_subset_laplacianDomain
              (I := I) (M := M) g 1 hu_h)).weak_partial i) 2
        ((volume : Measure EuclN).restrict (Kα (I := I) (M := M) α)) :=
    (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
      (laplacianDomainPow_succ_subset_laplacianDomain
        (I := I) (M := M) g 1 hu_h)).weak_partial_locally_memLp i
      (Kα (I := I) (M := M) α)
      (Kα_compact (I := I) (M := M) α)
      (Kα_subset_target (I := I) (M := M) α)
  exact memLp_two_continuousOn_mul_on_Kα (α := α)
    (weightedInvGramSecondDerivOnEuclid_partial_continuousOn
      (I := I) (M := M) g α i j l₁ l₂) h_wp_K

private lemma termC2_pair_memLp_vol_K
    (g : SmoothRiemannianMetric I M) (α : M)
    (l₁ l₂ : Fin (Module.finrank ℝ E))
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (i j : Fin (Module.finrank ℝ E)) :
    MemLp (fun y =>
        weightedInvGramSecondDerivOnEuclid (I := I) g α i j l₁ l₂ y *
        chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i j y) 2
      ((volume : Measure EuclN).restrict (Kα (I := I) (M := M) α)) := by
  classical
  have h_second_K :
      MemLp (chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i j) 2
        ((volume : Measure EuclN).restrict (Kα (I := I) (M := M) α)) :=
    chosenSecondPartialChartPushedU_locally_memLp
      (I := I) (M := M) g α hu_h i j
      (Kα_compact (I := I) (M := M) α)
      (Kα_subset_target (I := I) (M := M) α)
  exact memLp_two_continuousOn_mul_on_Kα (α := α)
    (weightedInvGramSecondDerivOnEuclid_continuousOn
      (I := I) g α i j l₁ l₂) h_second_K

private lemma termC3_pair_memLp_vol_K
    (g : SmoothRiemannianMetric I M) (α : M)
    (l₁ l₂ : Fin (Module.finrank ℝ E))
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (i j : Fin (Module.finrank ℝ E)) :
    MemLp (fun y =>
        (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l₁) y)
            (EuclideanSpace.single j 1) *
        chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₂ y) 2
      ((volume : Measure EuclN).restrict (Kα (I := I) (M := M) α)) := by
  classical
  have h_second_K :
      MemLp (chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₂) 2
        ((volume : Measure EuclN).restrict (Kα (I := I) (M := M) α)) :=
    chosenSecondPartialChartPushedU_locally_memLp
      (I := I) (M := M) g α hu_h i l₂
      (Kα_compact (I := I) (M := M) α)
      (Kα_subset_target (I := I) (M := M) α)
  exact memLp_two_continuousOn_mul_on_Kα (α := α)
    (weightedInvGramDerivOnEuclid_partial_continuousOn
      (I := I) (M := M) g α i j l₁) h_second_K

private lemma termC4_pair_memLp_vol_K
    (g : SmoothRiemannianMetric I M) (α : M)
    (l₁ l₂ : Fin (Module.finrank ℝ E))
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (i j : Fin (Module.finrank ℝ E)) :
    MemLp (fun y =>
        weightedInvGramDerivOnEuclid (I := I) g α i j l₁ y *
        chosenThirdMixedPartialChartPushedU (I := I) (M := M) g α u_h i l₂ j y) 2
      ((volume : Measure EuclN).restrict (Kα (I := I) (M := M) α)) := by
  classical
  have h_third_K :
      MemLp (chosenThirdMixedPartialChartPushedU
        (I := I) (M := M) g α u_h i l₂ j) 2
        ((volume : Measure EuclN).restrict (Kα (I := I) (M := M) α)) :=
    chosenThirdMixedPartialChartPushedU_locally_memLp
      (I := I) (M := M) g α hu_h i l₂ j
      (Kα_compact (I := I) (M := M) α)
      (Kα_subset_target (I := I) (M := M) α)
  exact memLp_two_continuousOn_mul_on_Kα (α := α)
    (weightedInvGramDerivOnEuclid_continuousOn (I := I) g α i j l₁) h_third_K

private lemma termD1_memLp_vol_K
    (g : SmoothRiemannianMetric I M) (α : M)
    (l₁ l₂ : Fin (Module.finrank ℝ E))
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    MemLp (fun y =>
        densitySecondDerivOnEuclid (I := I) g α l₁ l₂ y *
        (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).u_chart y) 2
      ((volume : Measure EuclN).restrict (Kα (I := I) (M := M) α)) := by
  classical
  have h_uc_K :
      MemLp ((chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
            (laplacianDomainPow_succ_subset_laplacianDomain
              (I := I) (M := M) g 1 hu_h)).u_chart) 2
        ((volume : Measure EuclN).restrict (Kα (I := I) (M := M) α)) :=
    memLp_volume_restrict_of_memLp_chartPulledWeightedMeasure
      (I := I) (M := M) (g := g) (α := α)
      (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
        (laplacianDomainPow_succ_subset_laplacianDomain
          (I := I) (M := M) g 1 hu_h)).u_chart_memLp_weighted
      (Kα_compact (I := I) (M := M) α)
      (Kα_meas (I := I) (M := M) α)
      (Kα_subset_target (I := I) (M := M) α)
  exact memLp_two_continuousOn_mul_on_Kα (α := α)
    (densitySecondDerivOnEuclid_continuousOn (I := I) g α l₁ l₂) h_uc_K

private lemma termD2_memLp_vol_K
    (g : SmoothRiemannianMetric I M) (α : M)
    (l₁ l₂ : Fin (Module.finrank ℝ E))
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    MemLp (fun y =>
        densityDerivOnEuclid (I := I) g α l₁ y *
        (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).weak_partial l₂ y) 2
      ((volume : Measure EuclN).restrict (Kα (I := I) (M := M) α)) := by
  classical
  have h_wp_K :
      MemLp ((chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
            (laplacianDomainPow_succ_subset_laplacianDomain
              (I := I) (M := M) g 1 hu_h)).weak_partial l₂) 2
        ((volume : Measure EuclN).restrict (Kα (I := I) (M := M) α)) :=
    (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
      (laplacianDomainPow_succ_subset_laplacianDomain
        (I := I) (M := M) g 1 hu_h)).weak_partial_locally_memLp l₂
      (Kα (I := I) (M := M) α)
      (Kα_compact (I := I) (M := M) α)
      (Kα_subset_target (I := I) (M := M) α)
  exact memLp_two_continuousOn_mul_on_Kα (α := α)
    (densityDerivOnEuclid_continuousOn (I := I) g α l₁) h_wp_K

private lemma termE1_memLp_vol_K
    (g : SmoothRiemannianMetric I M) (α : M)
    (l₁ l₂ : Fin (Module.finrank ℝ E))
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    MemLp (fun y =>
        densitySecondDerivOnEuclid (I := I) g α l₁ l₂ y *
        (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).f_chart y) 2
      ((volume : Measure EuclN).restrict (Kα (I := I) (M := M) α)) := by
  classical
  have h_fc_K :
      MemLp ((chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
            (laplacianDomainPow_succ_subset_laplacianDomain
              (I := I) (M := M) g 1 hu_h)).f_chart) 2
        ((volume : Measure EuclN).restrict (Kα (I := I) (M := M) α)) :=
    memLp_volume_restrict_of_memLp_chartPulledWeightedMeasure
      (I := I) (M := M) (g := g) (α := α)
      (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
        (laplacianDomainPow_succ_subset_laplacianDomain
          (I := I) (M := M) g 1 hu_h)).f_chart_memLp_weighted
      (Kα_compact (I := I) (M := M) α)
      (Kα_meas (I := I) (M := M) α)
      (Kα_subset_target (I := I) (M := M) α)
  exact memLp_two_continuousOn_mul_on_Kα (α := α)
    (densitySecondDerivOnEuclid_continuousOn (I := I) g α l₁ l₂) h_fc_K

private lemma termE2_memLp_vol_K
    (g : SmoothRiemannianMetric I M) (α : M)
    (l₁ l₂ : Fin (Module.finrank ℝ E))
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    MemLp (fun y =>
        densityDerivOnEuclid (I := I) g α l₁ y *
        chosenFChartDeriv (I := I) (M := M) g α hu_h l₂ y) 2
      ((volume : Measure EuclN).restrict (Kα (I := I) (M := M) α)) := by
  classical
  by_cases h_memW1p :
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
        (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).f_chart
        (chartTargetEuclid (I := I) (M := M) α)
  · have h_global :
        MemLp (chosenFChartDeriv (I := I) (M := M) g α hu_h l₂) 2
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)) := by
      unfold chosenFChartDeriv
      exact chosenWeakPartial'_memLp_of_mem h_memW1p l₂
    have h_K :
        MemLp (chosenFChartDeriv (I := I) (M := M) g α hu_h l₂) 2
          ((volume : Measure EuclN).restrict (Kα (I := I) (M := M) α)) :=
      memLp_restrict_Kα_of_memLp_chartTarget (I := I) (M := M) α h_global
    exact memLp_two_continuousOn_mul_on_Kα (α := α)
      (densityDerivOnEuclid_continuousOn (I := I) g α l₁) h_K
  · have h_zero :
        chosenFChartDeriv (I := I) (M := M) g α hu_h l₂ = 0 := by
      unfold chosenFChartDeriv
      exact chosenWeakPartial'_of_not_mem h_memW1p l₂
    have : (fun y => densityDerivOnEuclid (I := I) g α l₁ y *
        chosenFChartDeriv (I := I) (M := M) g α hu_h l₂ y) = (fun _ => 0) := by
      funext y
      rw [h_zero]; simp
    rw [this]
    exact MemLp.zero

private lemma fChartEffTwiceNumerator_memLp_vol_K
    (g : SmoothRiemannianMetric I M) (α : M)
    (l₁ l₂ : Fin (Module.finrank ℝ E))
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    MemLp (effectiveSourceChartSecondOrderNumerator (I := I) (M := M) g α l₁ l₂ hu_h) 2
      ((volume : Measure EuclN).restrict (Kα (I := I) (M := M) α)) := by
  classical
  have hA1 : MemLp (fun y => (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l₂) y)
              (EuclideanSpace.single j 1) *
            chosenSecondPartialChartPushedU
              (I := I) (M := M) g α u_h i l₁ y)) 2
        ((volume : Measure EuclN).restrict (Kα (I := I) (M := M) α)) := by
    apply memLp_finset_sum
    intro i _
    apply memLp_finset_sum
    intro j _
    exact termA1_pair_memLp_vol_K (I := I) (M := M) g α l₁ l₂ hu_h i j
  have hA2 : MemLp (fun y => (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramDerivOnEuclid (I := I) g α i j l₂ y *
            chosenThirdMixedPartialChartPushedU
              (I := I) (M := M) g α u_h i l₁ j y)) 2
        ((volume : Measure EuclN).restrict (Kα (I := I) (M := M) α)) := by
    apply memLp_finset_sum
    intro i _
    apply memLp_finset_sum
    intro j _
    exact termA2_pair_memLp_vol_K (I := I) (M := M) g α l₁ l₂ hu_h i j
  have hA3 := termA3_memLp_vol_K (I := I) (M := M) g α l₁ l₂ hu_h
  have hB1 := termB1_memLp_vol_K (I := I) (M := M) g α l₁ l₂ hu_h
  have hB2 := termB2_memLp_vol_K (I := I) (M := M) g α l₁ l₂ hu_h
  have hC1 : MemLp (fun y => (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (fderiv ℝ
              (weightedInvGramSecondDerivOnEuclid (I := I) g α i j l₁ l₂) y)
              (EuclideanSpace.single j 1) *
            (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
              (laplacianDomainPow_succ_subset_laplacianDomain
                (I := I) (M := M) g 1 hu_h)).weak_partial i y)) 2
        ((volume : Measure EuclN).restrict (Kα (I := I) (M := M) α)) := by
    apply memLp_finset_sum
    intro i _
    apply memLp_finset_sum
    intro j _
    exact termC1_pair_memLp_vol_K (I := I) (M := M) g α l₁ l₂ hu_h i j
  have hC2 : MemLp (fun y => (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramSecondDerivOnEuclid (I := I) g α i j l₁ l₂ y *
            chosenSecondPartialChartPushedU
              (I := I) (M := M) g α u_h i j y)) 2
        ((volume : Measure EuclN).restrict (Kα (I := I) (M := M) α)) := by
    apply memLp_finset_sum
    intro i _
    apply memLp_finset_sum
    intro j _
    exact termC2_pair_memLp_vol_K (I := I) (M := M) g α l₁ l₂ hu_h i j
  have hC3 : MemLp (fun y => (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l₁) y)
              (EuclideanSpace.single j 1) *
            chosenSecondPartialChartPushedU
              (I := I) (M := M) g α u_h i l₂ y)) 2
        ((volume : Measure EuclN).restrict (Kα (I := I) (M := M) α)) := by
    apply memLp_finset_sum
    intro i _
    apply memLp_finset_sum
    intro j _
    exact termC3_pair_memLp_vol_K (I := I) (M := M) g α l₁ l₂ hu_h i j
  have hC4 : MemLp (fun y => (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramDerivOnEuclid (I := I) g α i j l₁ y *
            chosenThirdMixedPartialChartPushedU
              (I := I) (M := M) g α u_h i l₂ j y)) 2
        ((volume : Measure EuclN).restrict (Kα (I := I) (M := M) α)) := by
    apply memLp_finset_sum
    intro i _
    apply memLp_finset_sum
    intro j _
    exact termC4_pair_memLp_vol_K (I := I) (M := M) g α l₁ l₂ hu_h i j
  have hD1 := termD1_memLp_vol_K (I := I) (M := M) g α l₁ l₂ hu_h
  have hD2 := termD2_memLp_vol_K (I := I) (M := M) g α l₁ l₂ hu_h
  have hE1 := termE1_memLp_vol_K (I := I) (M := M) g α l₁ l₂ hu_h
  have hE2 := termE2_memLp_vol_K (I := I) (M := M) g α l₁ l₂ hu_h
  have h_step1 := hA1.add hA2
  have h_step2 := h_step1.sub hA3
  have h_step3 := h_step2.add hB1
  have h_step4 := h_step3.add hB2
  have h_step5 := h_step4.add hC1
  have h_step6 := h_step5.add hC2
  have h_step7 := h_step6.add hC3
  have h_step8 := h_step7.add hC4
  have h_step9 := h_step8.sub hD1
  have h_step10 := h_step9.sub hD2
  have h_step11 := h_step10.add hE1
  have h_step12 := h_step11.add hE2
  unfold effectiveSourceChartSecondOrderNumerator
  convert h_step12 using 2 with y

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma one_div_densityOnEuclid_continuousOn
    (g : SmoothRiemannianMetric I M) (α : M) :
    ContinuousOn (fun y => 1 / densityOnEuclid (I := I) g α y)
      (chartTargetEuclid (I := I) (M := M) α) := by
  have h_cont := densityOnEuclid_continuousOn (I := I) g α
  have h_inv := h_cont.inv₀ (fun y hy =>
    (densityOnEuclid_pos (I := I) g α hy).ne')
  have h_eq : (fun y => 1 / densityOnEuclid (I := I) g α y) =
      (fun y => (densityOnEuclid (I := I) g α y)⁻¹) := by
    funext y; rw [one_div]
  rw [h_eq]
  exact h_inv

private lemma fChartEffTwiceNumerator_div_density_memLp_vol_K
    (g : SmoothRiemannianMetric I M) (α : M)
    (l₁ l₂ : Fin (Module.finrank ℝ E))
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    MemLp (fun y => effectiveSourceChartSecondOrderNumerator
        (I := I) (M := M) g α l₁ l₂ hu_h y /
        densityOnEuclid (I := I) g α y) 2
      ((volume : Measure EuclN).restrict (Kα (I := I) (M := M) α)) := by
  classical
  have h_num := fChartEffTwiceNumerator_memLp_vol_K
    (I := I) (M := M) g α l₁ l₂ hu_h
  have h_eq : (fun y => effectiveSourceChartSecondOrderNumerator
      (I := I) (M := M) g α l₁ l₂ hu_h y /
      densityOnEuclid (I := I) g α y) =
      fun y => (1 / densityOnEuclid (I := I) g α y) *
        effectiveSourceChartSecondOrderNumerator (I := I) (M := M) g α l₁ l₂ hu_h y := by
    funext y
    rw [one_div, mul_comm, ← div_eq_mul_inv]
  rw [h_eq]
  exact memLp_two_continuousOn_mul_on_Kα (α := α)
    (one_div_densityOnEuclid_continuousOn (I := I) (M := M) g α) h_num

theorem fChartEffTwice_memLp_two_weighted
    {g : SmoothRiemannianMetric I M} {α : M}
    {l₁ l₂ : Fin (Module.finrank ℝ E)}
    {u_h : H1Compl g} {hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2} :
    MemLp (effectiveSourceChartSecondOrder (I := I) (M := M) g α l₁ l₂ hu_h) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  set K : Set EuclN := Kα (I := I) (M := M) α with hK_def
  set f : EuclN → ℝ := fun y =>
    effectiveSourceChartSecondOrderNumerator (I := I) (M := M) g α l₁ l₂ hu_h y /
      densityOnEuclid (I := I) g α y with hf_def
  have h_indicator_eq :
      effectiveSourceChartSecondOrder (I := I) (M := M) g α l₁ l₂ hu_h = Set.indicator K f := by
    rfl
  rw [h_indicator_eq]
  have h_chartTarget_meas : MeasurableSet
      (chartTargetEuclid (I := I) (M := M) α) :=
    (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
  have hK_meas : MeasurableSet K := Kα_meas (I := I) (M := M) α
  have hK_compact : IsCompact K := Kα_compact (I := I) (M := M) α
  have hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α :=
    Kα_subset_target (I := I) (M := M) α
  rw [memLp_indicator_iff_restrict hK_meas]
  have h_double_restrict :
      ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)).restrict K =
      (chartPulledWeightedMeasure (I := I) g α).restrict K := by
    rw [Measure.restrict_restrict hK_meas]
    congr 1
    exact Set.inter_eq_self_of_subset_left hK_in
  rw [h_double_restrict]
  refine memLp_chartPulledWeighted_restrict_of_volume_restrict
    (g := g) (α := α) hK_compact hK_meas hK_in ?_
  exact fChartEffTwiceNumerator_div_density_memLp_vol_K
    (I := I) (M := M) g α l₁ l₂ hu_h

end FChartEffTwiceDef
end Laplacian
end Analysis
end DifferentialGeometry

end
