import DifferentialGeometry.Analysis.Sobolev.Nirenberg.SubstitutionIdentity.SubstitutionNonSmoothChartBilinear
import DifferentialGeometry.Analysis.Sobolev.Nirenberg.TestFunction.Defs
import DifferentialGeometry.Analysis.Sobolev.Solutions.Mollification
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Density
import DifferentialGeometry.External.DeGiorgi.SobolevSpace.Approximation


noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal Pointwise

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace SubstitutionDischargeSmoothApprox

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

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))


omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] in
theorem exists_chart_target_cutoff
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {α : M}
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    {_R₀ : ℝ} {h : ℝ}
    (h_thick :
      Metric.cthickening |h| K_0 ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ χ : EuclN → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧
      (∀ x, 0 ≤ χ x) ∧ (∀ x, χ x ≤ 1) ∧
      (∀ x ∈ Metric.cthickening |h| K_0, χ x = 1) ∧
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
  refine ⟨χ, hχ_smooth, hχ_compact, ?_, ?_, ?_, hχ_supp⟩
  · intro x
    have hx_range : χ x ∈ Set.range χ := Set.mem_range_self x
    have h_in_Icc : χ x ∈ Set.Icc (0 : ℝ) 1 := hχ_range hx_range
    exact h_in_Icc.1
  · intro x
    have hx_range : χ x ∈ Set.range χ := Set.mem_range_self x
    have h_in_Icc : χ x ∈ Set.Icc (0 : ℝ) 1 := hχ_range hx_range
    exact h_in_Icc.2
  · intro x hx
    apply hχ_one
    exact Metric.self_subset_cthickening _ hx

omit [NeZero (Module.finrank ℝ E)] in
lemma cutoff_uChart_memLp_two_univ
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {χ : EuclN → ℝ} (hχ_smooth : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχ_cs : HasCompactSupport χ)
    (hχ_supp_in : tsupport χ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    MemLp (fun x => χ x * D.u_chart x) 2 (volume : Measure EuclN) := by
  classical
  have hχ_cont : Continuous χ := hχ_smooth.continuous
  have hχ_abs_cont : Continuous (fun x => |χ x|) := hχ_cont.abs
  obtain ⟨M_χ, hM_χ_nn, hM_χ_bd⟩ : ∃ M_χ : ℝ, 0 ≤ M_χ ∧ ∀ x, |χ x| ≤ M_χ := by
    by_cases hSupp_empty : (tsupport χ).Nonempty
    · obtain ⟨xMax, hxMax_in, hxMax_max⟩ :=
        hχ_cs.exists_isMaxOn hSupp_empty hχ_abs_cont.continuousOn
      refine ⟨|χ xMax|, abs_nonneg _, ?_⟩
      intro x
      by_cases hx : x ∈ tsupport χ
      · exact hxMax_max hx
      · have hχx : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
        rw [hχx, abs_zero]
        exact abs_nonneg _
    · refine ⟨0, le_refl _, ?_⟩
      intro x
      by_cases hx : x ∈ tsupport χ
      · exact absurd ⟨x, hx⟩ hSupp_empty
      · have hχx : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
        rw [hχx, abs_zero]
  have h_supp_compact : IsCompact (tsupport χ) := hχ_cs
  have h_supp_meas : MeasurableSet (tsupport χ) := (isClosed_tsupport χ).measurableSet
  have hu_l2_supp : MemLp D.u_chart 2
      ((volume : Measure EuclN).restrict (tsupport χ)) :=
    memLp_volume_restrict_of_memLp_chartPulledWeightedMeasure (I := I) (M := M)
      D.u_chart_memLp_weighted h_supp_compact h_supp_meas hχ_supp_in
  have h_u_aesm_restrict : AEStronglyMeasurable D.u_chart
      ((volume : Measure EuclN).restrict (tsupport χ)) :=
    hu_l2_supp.aestronglyMeasurable
  have h_pt_le : ∀ᵐ x ∂((volume : Measure EuclN).restrict (tsupport χ)),
      ‖χ x * D.u_chart x‖ ≤ ‖M_χ * D.u_chart x‖ := by
    refine Filter.Eventually.of_forall ?_
    intro x
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_nonneg hM_χ_nn]
    exact mul_le_mul_of_nonneg_right (hM_χ_bd x) (abs_nonneg _)
  have h_prod_aesm_restrict : AEStronglyMeasurable (fun x => χ x * D.u_chart x)
      ((volume : Measure EuclN).restrict (tsupport χ)) :=
    hχ_cont.aestronglyMeasurable.restrict.mul h_u_aesm_restrict
  have h_restrict_lp : MemLp (fun x => χ x * D.u_chart x) 2
      ((volume : Measure EuclN).restrict (tsupport χ)) :=
    MemLp.mono (hu_l2_supp.const_mul M_χ) h_prod_aesm_restrict h_pt_le
  have h_indicator_eq : (tsupport χ).indicator (fun x => χ x * D.u_chart x) =
      (fun x => χ x * D.u_chart x) := by
    funext x
    by_cases hx : x ∈ tsupport χ
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]
      have hχx : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
      rw [hχx, zero_mul]
  have h_indicator_lp :
      MemLp ((tsupport χ).indicator (fun x => χ x * D.u_chart x)) 2
        (volume : Measure EuclN) :=
    (MeasureTheory.memLp_indicator_iff_restrict h_supp_meas).mpr h_restrict_lp
  rw [h_indicator_eq] at h_indicator_lp
  exact h_indicator_lp

omit [NeZero (Module.finrank ℝ E)] in
lemma cutoff_uChart_partial_memLp_two_univ
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {χ : EuclN → ℝ} (hχ_smooth : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχ_cs : HasCompactSupport χ)
    (hχ_supp_in : tsupport χ ⊆ chartTargetEuclid (I := I) (M := M) α)
    (i : Fin (Module.finrank ℝ E)) :
    MemLp (fun x =>
        (fderiv ℝ χ x) (EuclideanSpace.single i 1) * D.u_chart x +
        χ x * D.weak_partial i x) 2 (volume : Measure EuclN) := by
  classical
  have h_top_ne_zero : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by decide
  have hχ_partial_cont : Continuous
      (fun x => (fderiv ℝ χ x) (EuclideanSpace.single i 1)) :=
    (hχ_smooth.continuous_fderiv h_top_ne_zero).clm_apply continuous_const
  have h_supp_compact : IsCompact (tsupport χ) := hχ_cs
  have h_supp_meas : MeasurableSet (tsupport χ) := (isClosed_tsupport χ).measurableSet
  have hχ_cont : Continuous χ := hχ_smooth.continuous
  have hχ_abs_cont : Continuous (fun x => |χ x|) := hχ_cont.abs
  obtain ⟨M_χ, hM_χ_nn, hM_χ_bd⟩ : ∃ M_χ : ℝ, 0 ≤ M_χ ∧ ∀ x, |χ x| ≤ M_χ := by
    by_cases hSupp_empty : (tsupport χ).Nonempty
    · obtain ⟨xMax, _hxMax_in, hxMax_max⟩ :=
        hχ_cs.exists_isMaxOn hSupp_empty hχ_abs_cont.continuousOn
      refine ⟨|χ xMax|, abs_nonneg _, ?_⟩
      intro x
      by_cases hx : x ∈ tsupport χ
      · exact hxMax_max hx
      · have hχx : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
        rw [hχx, abs_zero]
        exact abs_nonneg _
    · refine ⟨0, le_refl _, ?_⟩
      intro x
      by_cases hx : x ∈ tsupport χ
      · exact absurd ⟨x, hx⟩ hSupp_empty
      · have hχx : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
        rw [hχx, abs_zero]
  have h_partial_χ_supp : HasCompactSupport
      (fun x => (fderiv ℝ χ x) (EuclideanSpace.single i 1)) :=
    hχ_cs.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1)
  have h_partial_χ_supp_subset : tsupport
      (fun x => (fderiv ℝ χ x) (EuclideanSpace.single i 1)) ⊆ tsupport χ :=
    tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)
  obtain ⟨M_dχ, hM_dχ_nn, hM_dχ_bd⟩ : ∃ M_dχ : ℝ, 0 ≤ M_dχ ∧
      ∀ x, |(fderiv ℝ χ x) (EuclideanSpace.single i 1)| ≤ M_dχ := by
    by_cases hSupp_empty :
        (tsupport (fun x => (fderiv ℝ χ x) (EuclideanSpace.single i 1))).Nonempty
    · obtain ⟨xMax, _hxMax_in, hxMax_max⟩ :=
        h_partial_χ_supp.exists_isMaxOn hSupp_empty
          (hχ_partial_cont.abs.continuousOn)
      refine ⟨|(fderiv ℝ χ xMax) (EuclideanSpace.single i 1)|,
        abs_nonneg _, ?_⟩
      intro x
      by_cases hx : x ∈ tsupport
          (fun x => (fderiv ℝ χ x) (EuclideanSpace.single i 1))
      · exact hxMax_max hx
      · have hdχx :
            (fun y : EuclN => (fderiv ℝ χ y) (EuclideanSpace.single i 1)) x = 0 :=
          image_eq_zero_of_notMem_tsupport
            (f := fun y : EuclN => (fderiv ℝ χ y) (EuclideanSpace.single i 1))
            hx
        rw [show (fderiv ℝ χ x) (EuclideanSpace.single i 1) = 0 from hdχx,
          abs_zero]
        exact abs_nonneg _
    · refine ⟨0, le_refl _, ?_⟩
      intro x
      by_cases hx : x ∈ tsupport
          (fun x => (fderiv ℝ χ x) (EuclideanSpace.single i 1))
      · exact absurd ⟨x, hx⟩ hSupp_empty
      · have hdχx :
            (fun y : EuclN => (fderiv ℝ χ y) (EuclideanSpace.single i 1)) x = 0 :=
          image_eq_zero_of_notMem_tsupport
            (f := fun y : EuclN => (fderiv ℝ χ y) (EuclideanSpace.single i 1))
            hx
        rw [show (fderiv ℝ χ x) (EuclideanSpace.single i 1) = 0 from hdχx,
          abs_zero]
  have hu_l2_supp : MemLp D.u_chart 2
      ((volume : Measure EuclN).restrict (tsupport χ)) :=
    memLp_volume_restrict_of_memLp_chartPulledWeightedMeasure (I := I) (M := M)
      D.u_chart_memLp_weighted h_supp_compact h_supp_meas hχ_supp_in
  have hwp_l2_supp : MemLp (D.weak_partial i) 2
      ((volume : Measure EuclN).restrict (tsupport χ)) :=
    D.weak_partial_locally_memLp i (tsupport χ) h_supp_compact hχ_supp_in
  have h_dχ_aesm_restrict : AEStronglyMeasurable
      (fun x => (fderiv ℝ χ x) (EuclideanSpace.single i 1))
      ((volume : Measure EuclN).restrict (tsupport χ)) :=
    hχ_partial_cont.aestronglyMeasurable.restrict
  have h_χ_aesm_restrict : AEStronglyMeasurable χ
      ((volume : Measure EuclN).restrict (tsupport χ)) :=
    hχ_cont.aestronglyMeasurable.restrict
  have h_term1_aesm_restrict : AEStronglyMeasurable
      (fun x => (fderiv ℝ χ x) (EuclideanSpace.single i 1) * D.u_chart x)
      ((volume : Measure EuclN).restrict (tsupport χ)) :=
    h_dχ_aesm_restrict.mul hu_l2_supp.aestronglyMeasurable
  have h_term2_aesm_restrict : AEStronglyMeasurable
      (fun x => χ x * D.weak_partial i x)
      ((volume : Measure EuclN).restrict (tsupport χ)) :=
    h_χ_aesm_restrict.mul hwp_l2_supp.aestronglyMeasurable
  have h_pt_le_1 : ∀ᵐ x ∂((volume : Measure EuclN).restrict (tsupport χ)),
      ‖(fderiv ℝ χ x) (EuclideanSpace.single i 1) * D.u_chart x‖ ≤
        ‖M_dχ * D.u_chart x‖ := by
    refine Filter.Eventually.of_forall ?_
    intro x
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_nonneg hM_dχ_nn]
    exact mul_le_mul_of_nonneg_right (hM_dχ_bd x) (abs_nonneg _)
  have h_term1_lp : MemLp
      (fun x => (fderiv ℝ χ x) (EuclideanSpace.single i 1) * D.u_chart x) 2
      ((volume : Measure EuclN).restrict (tsupport χ)) :=
    MemLp.mono (hu_l2_supp.const_mul M_dχ) h_term1_aesm_restrict h_pt_le_1
  have h_pt_le_2 : ∀ᵐ x ∂((volume : Measure EuclN).restrict (tsupport χ)),
      ‖χ x * D.weak_partial i x‖ ≤ ‖M_χ * D.weak_partial i x‖ := by
    refine Filter.Eventually.of_forall ?_
    intro x
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_nonneg hM_χ_nn]
    exact mul_le_mul_of_nonneg_right (hM_χ_bd x) (abs_nonneg _)
  have h_term2_lp : MemLp
      (fun x => χ x * D.weak_partial i x) 2
      ((volume : Measure EuclN).restrict (tsupport χ)) :=
    MemLp.mono (hwp_l2_supp.const_mul M_χ) h_term2_aesm_restrict h_pt_le_2
  have h_sum_lp : MemLp (fun x =>
      (fderiv ℝ χ x) (EuclideanSpace.single i 1) * D.u_chart x +
      χ x * D.weak_partial i x) 2
      ((volume : Measure EuclN).restrict (tsupport χ)) :=
    h_term1_lp.add h_term2_lp
  have h_indicator_eq : (tsupport χ).indicator
      (fun x => (fderiv ℝ χ x) (EuclideanSpace.single i 1) * D.u_chart x +
        χ x * D.weak_partial i x) =
      (fun x => (fderiv ℝ χ x) (EuclideanSpace.single i 1) * D.u_chart x +
        χ x * D.weak_partial i x) := by
    funext x
    by_cases hx : x ∈ tsupport χ
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]
      have hχx : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
      have hx_notin :
          x ∉ tsupport (fun y : EuclN =>
            (fderiv ℝ χ y) (EuclideanSpace.single i 1)) :=
        fun h => hx (h_partial_χ_supp_subset h)
      have hdχx :
          (fun y : EuclN => (fderiv ℝ χ y) (EuclideanSpace.single i 1)) x = 0 :=
        image_eq_zero_of_notMem_tsupport
          (f := fun y : EuclN => (fderiv ℝ χ y) (EuclideanSpace.single i 1))
          hx_notin
      rw [hχx,
        show (fderiv ℝ χ x) (EuclideanSpace.single i 1) = 0 from hdχx,
        zero_mul, zero_mul, add_zero]
  have h_indicator_lp :
      MemLp ((tsupport χ).indicator (fun x =>
          (fderiv ℝ χ x) (EuclideanSpace.single i 1) * D.u_chart x +
          χ x * D.weak_partial i x)) 2 (volume : Measure EuclN) :=
    (MeasureTheory.memLp_indicator_iff_restrict h_supp_meas).mpr h_sum_lp
  rw [h_indicator_eq] at h_indicator_lp
  exact h_indicator_lp

omit [NeZero (Module.finrank ℝ E)] in
lemma cutoff_uChart_hasWeakPartialDeriv_univ
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {χ : EuclN → ℝ} (hχ_smooth : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχ_cs : HasCompactSupport χ)
    (hχ_supp_in : tsupport χ ⊆ chartTargetEuclid (I := I) (M := M) α)
    (i : Fin (Module.finrank ℝ E)) :
    DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
      (fun x => (fderiv ℝ χ x) (EuclideanSpace.single i 1) * D.u_chart x +
        χ x * D.weak_partial i x)
      (fun x => χ x * D.u_chart x) Set.univ := by
  classical
  intro ψ hψ_smooth hψ_supp _hψ_sub
  set ei : EuclN := EuclideanSpace.single i (1 : ℝ) with hei_def
  have h_chart_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_chart_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    h_chart_open.measurableSet
  have hχψ_smooth : ContDiff ℝ (⊤ : ℕ∞) (fun x => χ x * ψ x) :=
    hχ_smooth.mul hψ_smooth
  have hχψ_cs : HasCompactSupport (fun x => χ x * ψ x) :=
    hχ_cs.mul_right
  have hχψ_supp_in_χ : tsupport (fun x => χ x * ψ x) ⊆ tsupport χ :=
    tsupport_smul_subset_left χ ψ
  have hχψ_supp : tsupport (fun x => χ x * ψ x) ⊆
      chartTargetEuclid (I := I) (M := M) α :=
    hχψ_supp_in_χ.trans hχ_supp_in
  have h_ibp_chart :=
    D.weak_partial_isWeakPartial i (fun y => χ y * ψ y)
      hχψ_smooth hχψ_cs hχψ_supp
  have hχ_diff : Differentiable ℝ χ := hχ_smooth.differentiable (by simp)
  have hψ_diff : Differentiable ℝ ψ := hψ_smooth.differentiable (by simp)
  have h_fderiv_prod : ∀ x : EuclN,
      (fderiv ℝ (fun y => χ y * ψ y) x) ei =
        χ x * (fderiv ℝ ψ x) ei + ψ x * (fderiv ℝ χ x) ei := by
    intro x
    rw [fderiv_fun_mul (hχ_diff.differentiableAt) (hψ_diff.differentiableAt)]
    simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul]
  have hχ_cont : Continuous χ := hχ_smooth.continuous
  have hψ_cont : Continuous ψ := hψ_smooth.continuous
  have h_top_ne_zero : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by decide
  have h_dχ_cont : Continuous (fun y : EuclN => (fderiv ℝ χ y) ei) :=
    (hχ_smooth.continuous_fderiv h_top_ne_zero).clm_apply continuous_const
  have h_dψ_cont : Continuous (fun y : EuclN => (fderiv ℝ ψ y) ei) :=
    (hψ_smooth.continuous_fderiv h_top_ne_zero).clm_apply continuous_const
  set G : EuclN → ℝ := fun x =>
    (fderiv ℝ χ x) ei * D.u_chart x + χ x * D.weak_partial i x with hG_def
  have h_LHS_eq :
      ∫ x in (Set.univ : Set EuclN), χ x * D.u_chart x * (fderiv ℝ ψ x) ei =
      ∫ x in chartTargetEuclid (I := I) (M := M) α,
        χ x * D.u_chart x * (fderiv ℝ ψ x) ei := by
    rw [setIntegral_univ]
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := chartTargetEuclid (I := I) (M := M) α)
      (f := fun x => χ x * D.u_chart x * (fderiv ℝ ψ x) ei)
      (fun x hx => ?_)).symm
    have hx_notin_χ : x ∉ tsupport χ := fun h => hx (hχ_supp_in h)
    have hχx : χ x = 0 := image_eq_zero_of_notMem_tsupport hx_notin_χ
    change χ x * D.u_chart x * (fderiv ℝ ψ x) ei = 0
    simp [hχx]
  have h_RHS_eq :
      ∫ x in (Set.univ : Set EuclN), G x * ψ x =
      ∫ x in chartTargetEuclid (I := I) (M := M) α, G x * ψ x := by
    rw [setIntegral_univ]
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := chartTargetEuclid (I := I) (M := M) α)
      (f := fun x => G x * ψ x) (fun x hx => ?_)).symm
    have hx_notin_χ : x ∉ tsupport χ := fun h => hx (hχ_supp_in h)
    have hχx : χ x = 0 := image_eq_zero_of_notMem_tsupport hx_notin_χ
    have h_partial_χ_supp_subset :
        tsupport (fun y : EuclN => (fderiv ℝ χ y) ei) ⊆ tsupport χ := by
      rw [hei_def]
      exact tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)
    have hx_notin_dχ : x ∉ tsupport (fun y : EuclN => (fderiv ℝ χ y) ei) :=
      fun h => hx_notin_χ (h_partial_χ_supp_subset h)
    have hdχx :
        (fun y : EuclN => (fderiv ℝ χ y) ei) x = 0 :=
      image_eq_zero_of_notMem_tsupport
        (f := fun y : EuclN => (fderiv ℝ χ y) ei) hx_notin_dχ
    have hdχx' : (fderiv ℝ χ x) ei = 0 := hdχx
    simp [hG_def, hχx, hdχx']
  change ∫ x in (Set.univ : Set EuclN), χ x * D.u_chart x * (fderiv ℝ ψ x) ei =
      -∫ x in (Set.univ : Set EuclN), G x * ψ x
  rw [h_LHS_eq, h_RHS_eq]
  have h_supp_compact : IsCompact (tsupport χ) := hχ_cs
  have h_supp_meas : MeasurableSet (tsupport χ) :=
    (isClosed_tsupport χ).measurableSet
  have hu_l2_supp : MemLp D.u_chart 2
      ((volume : Measure EuclN).restrict (tsupport χ)) :=
    memLp_volume_restrict_of_memLp_chartPulledWeightedMeasure (I := I) (M := M)
      D.u_chart_memLp_weighted h_supp_compact h_supp_meas hχ_supp_in
  have hwp_l2_supp : MemLp (D.weak_partial i) 2
      ((volume : Measure EuclN).restrict (tsupport χ)) :=
    D.weak_partial_locally_memLp i (tsupport χ) h_supp_compact hχ_supp_in
  haveI h_finite_meas_fact :
      Fact ((volume : Measure EuclN) (tsupport χ) < (⊤ : ℝ≥0∞)) :=
    Fact.mk h_supp_compact.measure_lt_top
  haveI h_restrict_finite : IsFiniteMeasure
      ((volume : Measure EuclN).restrict (tsupport χ)) :=
    Restrict.isFiniteMeasure (volume : Measure EuclN)
  have hu_l1_supp : Integrable D.u_chart
      ((volume : Measure EuclN).restrict (tsupport χ)) :=
    hu_l2_supp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hwp_l1_supp : Integrable (D.weak_partial i)
      ((volume : Measure EuclN).restrict (tsupport χ)) :=
    hwp_l2_supp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have h_χ_aesm_supp : AEStronglyMeasurable χ
      ((volume : Measure EuclN).restrict (tsupport χ)) :=
    hχ_cont.aestronglyMeasurable.restrict
  have hψ_aesm_supp : AEStronglyMeasurable ψ
      ((volume : Measure EuclN).restrict (tsupport χ)) :=
    hψ_cont.aestronglyMeasurable.restrict
  have h_dχ_aesm_supp : AEStronglyMeasurable (fun x : EuclN => (fderiv ℝ χ x) ei)
      ((volume : Measure EuclN).restrict (tsupport χ)) :=
    h_dχ_cont.aestronglyMeasurable.restrict
  have h_dψ_aesm_supp : AEStronglyMeasurable (fun x : EuclN => (fderiv ℝ ψ x) ei)
      ((volume : Measure EuclN).restrict (tsupport χ)) :=
    h_dψ_cont.aestronglyMeasurable.restrict
  obtain ⟨M_χ, hM_χ_nn, hM_χ_bd⟩ : ∃ M_χ : ℝ, 0 ≤ M_χ ∧ ∀ x, |χ x| ≤ M_χ := by
    by_cases hSupp_empty : (tsupport χ).Nonempty
    · obtain ⟨xMax, _hxMax_in, hxMax_max⟩ :=
        h_supp_compact.exists_isMaxOn hSupp_empty hχ_cont.abs.continuousOn
      refine ⟨|χ xMax|, abs_nonneg _, ?_⟩
      intro x
      by_cases hx : x ∈ tsupport χ
      · exact hxMax_max hx
      · have hχx : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
        rw [hχx, abs_zero]; exact abs_nonneg _
    · refine ⟨0, le_refl _, ?_⟩
      intro x
      by_cases hx : x ∈ tsupport χ
      · exact absurd ⟨x, hx⟩ hSupp_empty
      · have hχx : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
        rw [hχx, abs_zero]
  obtain ⟨M_ψ, hM_ψ_nn, hM_ψ_bd⟩ : ∃ M_ψ : ℝ, 0 ≤ M_ψ ∧
      ∀ x ∈ tsupport χ, |ψ x| ≤ M_ψ := by
    by_cases hSupp_empty : (tsupport χ).Nonempty
    · obtain ⟨xMax, hxMax_in, hxMax_max⟩ :=
        h_supp_compact.exists_isMaxOn hSupp_empty hψ_cont.abs.continuousOn
      refine ⟨|ψ xMax|, abs_nonneg _, ?_⟩
      intro x hx
      exact hxMax_max hx
    · refine ⟨0, le_refl _, ?_⟩
      intro x hx
      exact absurd ⟨x, hx⟩ hSupp_empty
  obtain ⟨M_dψ, hM_dψ_nn, hM_dψ_bd⟩ : ∃ M_dψ : ℝ, 0 ≤ M_dψ ∧
      ∀ x ∈ tsupport χ, |(fderiv ℝ ψ x) ei| ≤ M_dψ := by
    by_cases hSupp_empty : (tsupport χ).Nonempty
    · obtain ⟨xMax, hxMax_in, hxMax_max⟩ :=
        h_supp_compact.exists_isMaxOn hSupp_empty h_dψ_cont.abs.continuousOn
      refine ⟨|(fderiv ℝ ψ xMax) ei|, abs_nonneg _, ?_⟩
      intro x hx
      exact hxMax_max hx
    · refine ⟨0, le_refl _, ?_⟩
      intro x hx
      exact absurd ⟨x, hx⟩ hSupp_empty
  obtain ⟨M_dχ, hM_dχ_nn, hM_dχ_bd⟩ : ∃ M_dχ : ℝ, 0 ≤ M_dχ ∧
      ∀ x ∈ tsupport χ, |(fderiv ℝ χ x) ei| ≤ M_dχ := by
    by_cases hSupp_empty : (tsupport χ).Nonempty
    · obtain ⟨xMax, hxMax_in, hxMax_max⟩ :=
        h_supp_compact.exists_isMaxOn hSupp_empty h_dχ_cont.abs.continuousOn
      refine ⟨|(fderiv ℝ χ xMax) ei|, abs_nonneg _, ?_⟩
      intro x hx
      exact hxMax_max hx
    · refine ⟨0, le_refl _, ?_⟩
      intro x hx
      exact absurd ⟨x, hx⟩ hSupp_empty
  have h_χ_dψ_bdd : ∀ᵐ x ∂((volume : Measure EuclN).restrict (tsupport χ)),
      ‖χ x * (fderiv ℝ ψ x) ei‖ ≤ M_χ * M_dψ := by
    rw [ae_restrict_iff' h_supp_meas]
    refine Filter.Eventually.of_forall ?_
    intro x hx
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hM_χ_bd x) (hM_dψ_bd x hx) (abs_nonneg _) hM_χ_nn
  have h_ψ_dχ_bdd : ∀ᵐ x ∂((volume : Measure EuclN).restrict (tsupport χ)),
      ‖ψ x * (fderiv ℝ χ x) ei‖ ≤ M_ψ * M_dχ := by
    rw [ae_restrict_iff' h_supp_meas]
    refine Filter.Eventually.of_forall ?_
    intro x hx
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hM_ψ_bd x hx) (hM_dχ_bd x hx) (abs_nonneg _) hM_ψ_nn
  have h_χ_ψ_bdd : ∀ᵐ x ∂((volume : Measure EuclN).restrict (tsupport χ)),
      ‖χ x * ψ x‖ ≤ M_χ * M_ψ := by
    rw [ae_restrict_iff' h_supp_meas]
    refine Filter.Eventually.of_forall ?_
    intro x hx
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hM_χ_bd x) (hM_ψ_bd x hx) (abs_nonneg _) hM_χ_nn
  have h_χ_dψ_aesm : AEStronglyMeasurable
      (fun x : EuclN => χ x * (fderiv ℝ ψ x) ei)
      ((volume : Measure EuclN).restrict (tsupport χ)) :=
    h_χ_aesm_supp.mul h_dψ_aesm_supp
  have h_term1_int : Integrable
      (fun x => D.u_chart x * (χ x * (fderiv ℝ ψ x) ei))
      ((volume : Measure EuclN).restrict (tsupport χ)) :=
    hu_l1_supp.mul_bdd h_χ_dψ_aesm h_χ_dψ_bdd
  have h_χ_ψ_aesm : AEStronglyMeasurable
      (fun x : EuclN => χ x * ψ x)
      ((volume : Measure EuclN).restrict (tsupport χ)) :=
    h_χ_aesm_supp.mul hψ_aesm_supp
  have h_term2_int : Integrable
      (fun x => D.weak_partial i x * (χ x * ψ x))
      ((volume : Measure EuclN).restrict (tsupport χ)) :=
    hwp_l1_supp.mul_bdd h_χ_ψ_aesm h_χ_ψ_bdd
  have h_ψ_dχ_aesm : AEStronglyMeasurable
      (fun x : EuclN => ψ x * (fderiv ℝ χ x) ei)
      ((volume : Measure EuclN).restrict (tsupport χ)) :=
    hψ_aesm_supp.mul h_dχ_aesm_supp
  have h_term3_int : Integrable
      (fun x => D.u_chart x * (ψ x * (fderiv ℝ χ x) ei))
      ((volume : Measure EuclN).restrict (tsupport χ)) :=
    hu_l1_supp.mul_bdd h_ψ_dχ_aesm h_ψ_dχ_bdd
  have h_integrand_LHS_zero_outside :
      ∀ x, x ∉ tsupport χ → χ x * D.u_chart x * (fderiv ℝ ψ x) ei = 0 := by
    intro x hx
    have hχx : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
    rw [hχx, zero_mul, zero_mul]
  have h_integrand_term1_zero_outside :
      ∀ x, x ∉ tsupport χ → D.u_chart x * (χ x * (fderiv ℝ ψ x) ei) = 0 := by
    intro x hx
    have hχx : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
    rw [hχx, zero_mul, mul_zero]
  have h_integrand_term3_zero_outside :
      ∀ x, x ∉ tsupport χ → D.u_chart x * (ψ x * (fderiv ℝ χ x) ei) = 0 := by
    intro x hx
    have h_partial_χ_supp_subset :
        tsupport (fun y : EuclN => (fderiv ℝ χ y) ei) ⊆ tsupport χ := by
      rw [hei_def]
      exact tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)
    have hx_notin_dχ : x ∉ tsupport (fun y : EuclN => (fderiv ℝ χ y) ei) :=
      fun h => hx (h_partial_χ_supp_subset h)
    have hdχx :
        (fun y : EuclN => (fderiv ℝ χ y) ei) x = 0 :=
      image_eq_zero_of_notMem_tsupport
        (f := fun y : EuclN => (fderiv ℝ χ y) ei) hx_notin_dχ
    have hdχx' : (fderiv ℝ χ x) ei = 0 := hdχx
    rw [hdχx', mul_zero, mul_zero]
  have h_integrand_term2_zero_outside :
      ∀ x, x ∉ tsupport χ → D.weak_partial i x * (χ x * ψ x) = 0 := by
    intro x hx
    have hχx : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
    rw [hχx, zero_mul, mul_zero]
  have h_integrand_RHS_zero_outside :
      ∀ x, x ∉ tsupport χ → G x * ψ x = 0 := by
    intro x hx
    have hχx : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
    have h_partial_χ_supp_subset :
        tsupport (fun y : EuclN => (fderiv ℝ χ y) ei) ⊆ tsupport χ := by
      rw [hei_def]
      exact tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)
    have hx_notin_dχ : x ∉ tsupport (fun y : EuclN => (fderiv ℝ χ y) ei) :=
      fun h => hx (h_partial_χ_supp_subset h)
    have hdχx :
        (fun y : EuclN => (fderiv ℝ χ y) ei) x = 0 :=
      image_eq_zero_of_notMem_tsupport
        (f := fun y : EuclN => (fderiv ℝ χ y) ei) hx_notin_dχ
    have hdχx' : (fderiv ℝ χ x) ei = 0 := hdχx
    rw [hG_def]
    simp [hχx, hdχx']
  have h_LHS_chart_to_supp :
      ∫ x in chartTargetEuclid (I := I) (M := M) α,
        χ x * D.u_chart x * (fderiv ℝ ψ x) ei =
      ∫ x in tsupport χ, χ x * D.u_chart x * (fderiv ℝ ψ x) ei :=
    setIntegral_eq_of_subset_of_forall_diff_eq_zero
      h_chart_open.measurableSet hχ_supp_in
      (fun x hx => h_integrand_LHS_zero_outside x hx.2)
  have h_RHS_chart_to_supp :
      ∫ x in chartTargetEuclid (I := I) (M := M) α, G x * ψ x =
      ∫ x in tsupport χ, G x * ψ x :=
    setIntegral_eq_of_subset_of_forall_diff_eq_zero
      h_chart_open.measurableSet hχ_supp_in
      (fun x hx => h_integrand_RHS_zero_outside x hx.2)
  have h_term1_chart_to_supp :
      ∫ x in chartTargetEuclid (I := I) (M := M) α,
        D.u_chart x * (χ x * (fderiv ℝ ψ x) ei) =
      ∫ x in tsupport χ, D.u_chart x * (χ x * (fderiv ℝ ψ x) ei) :=
    setIntegral_eq_of_subset_of_forall_diff_eq_zero
      h_chart_open.measurableSet hχ_supp_in
      (fun x hx => h_integrand_term1_zero_outside x hx.2)
  have h_term3_chart_to_supp :
      ∫ x in chartTargetEuclid (I := I) (M := M) α,
        D.u_chart x * (ψ x * (fderiv ℝ χ x) ei) =
      ∫ x in tsupport χ, D.u_chart x * (ψ x * (fderiv ℝ χ x) ei) :=
    setIntegral_eq_of_subset_of_forall_diff_eq_zero
      h_chart_open.measurableSet hχ_supp_in
      (fun x hx => h_integrand_term3_zero_outside x hx.2)
  have h_term2_chart_to_supp :
      ∫ x in chartTargetEuclid (I := I) (M := M) α,
        D.weak_partial i x * (χ x * ψ x) =
      ∫ x in tsupport χ, D.weak_partial i x * (χ x * ψ x) :=
    setIntegral_eq_of_subset_of_forall_diff_eq_zero
      h_chart_open.measurableSet hχ_supp_in
      (fun x hx => h_integrand_term2_zero_outside x hx.2)
  have h_ibp_chart_LHS_split :
      ∫ x in tsupport χ,
        D.u_chart x * (fderiv ℝ (fun y => χ y * ψ y) x) ei =
      (∫ x in tsupport χ, D.u_chart x * (χ x * (fderiv ℝ ψ x) ei)) +
      ∫ x in tsupport χ, D.u_chart x * (ψ x * (fderiv ℝ χ x) ei) := by
    rw [← MeasureTheory.integral_add h_term1_int h_term3_int]
    refine MeasureTheory.integral_congr_ae ?_
    refine Filter.Eventually.of_forall ?_
    intro x
    have h_pt := h_fderiv_prod x
    calc D.u_chart x * (fderiv ℝ (fun y => χ y * ψ y) x) ei
        = D.u_chart x * (χ x * (fderiv ℝ ψ x) ei + ψ x * (fderiv ℝ χ x) ei) := by
          rw [h_pt]
      _ = D.u_chart x * (χ x * (fderiv ℝ ψ x) ei) +
          D.u_chart x * (ψ x * (fderiv ℝ χ x) ei) := by ring
  have h_ibp_chart_LHS_chart_to_supp :
      ∫ x in chartTargetEuclid (I := I) (M := M) α,
        D.u_chart x * (fderiv ℝ (fun y => χ y * ψ y) x) ei =
      ∫ x in tsupport χ,
        D.u_chart x * (fderiv ℝ (fun y => χ y * ψ y) x) ei := by
    refine setIntegral_eq_of_subset_of_forall_diff_eq_zero
      h_chart_open.measurableSet hχ_supp_in (fun x hx => ?_)
    have hx_notin_χψ : x ∉ tsupport (fun y => χ y * ψ y) :=
      fun h => hx.2 (hχψ_supp_in_χ h)
    have hχψ_partial_supp :
        tsupport (fun y : EuclN => (fderiv ℝ (fun z => χ z * ψ z) y) ei) ⊆
          tsupport χ :=
      (tsupport_fderiv_apply_subset ℝ ei).trans hχψ_supp_in_χ
    have hx_notin :
        x ∉ tsupport (fun y : EuclN => (fderiv ℝ (fun z => χ z * ψ z) y) ei) :=
      fun h => hx.2 (hχψ_partial_supp h)
    have hdχψx :
        (fun y : EuclN => (fderiv ℝ (fun z => χ z * ψ z) y) ei) x = 0 :=
      image_eq_zero_of_notMem_tsupport
        (f := fun y : EuclN => (fderiv ℝ (fun z => χ z * ψ z) y) ei) hx_notin
    have hdχψx' : (fderiv ℝ (fun z => χ z * ψ z) x) ei = 0 := hdχψx
    rw [hdχψx', mul_zero]
  rw [h_ibp_chart_LHS_chart_to_supp, h_term2_chart_to_supp] at h_ibp_chart
  rw [h_ibp_chart_LHS_split] at h_ibp_chart
  rw [h_LHS_chart_to_supp, h_RHS_chart_to_supp]
  have h_LHS_pt :
      ∫ x in tsupport χ, χ x * D.u_chart x * (fderiv ℝ ψ x) ei =
      ∫ x in tsupport χ, D.u_chart x * (χ x * (fderiv ℝ ψ x) ei) := by
    refine MeasureTheory.integral_congr_ae ?_
    refine Filter.Eventually.of_forall ?_
    intro x; ring
  have h_RHS_split :
      ∫ x in tsupport χ, G x * ψ x =
      (∫ x in tsupport χ, D.u_chart x * (ψ x * (fderiv ℝ χ x) ei)) +
      ∫ x in tsupport χ, D.weak_partial i x * (χ x * ψ x) := by
    rw [← MeasureTheory.integral_add h_term3_int h_term2_int]
    refine MeasureTheory.integral_congr_ae ?_
    refine Filter.Eventually.of_forall ?_
    intro x
    rw [hG_def]; ring
  rw [h_LHS_pt, h_RHS_split]
  linarith [h_ibp_chart]

omit [NeZero (Module.finrank ℝ E)] in
theorem cutoff_uChart_w1p_witness
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {χ : EuclN → ℝ} (hχ_smooth : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχ_cs : HasCompactSupport χ)
    (hχ_supp_in : tsupport χ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ G : Fin (Module.finrank ℝ E) → EuclN → ℝ,
      (∀ i, MemLp (G i) 2 (volume : Measure EuclN)) ∧
      (∀ i, DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) i (G i)
        (fun x => χ x * D.u_chart x) Set.univ) ∧
      MemLp (fun x => χ x * D.u_chart x) 2 (volume : Measure EuclN) := by
  classical
  refine ⟨fun i x =>
    (fderiv ℝ χ x) (EuclideanSpace.single i 1) * D.u_chart x +
    χ x * D.weak_partial i x, ?_, ?_, ?_⟩
  · intro i
    exact cutoff_uChart_partial_memLp_two_univ (I := I) (M := M) D
      hχ_smooth hχ_cs hχ_supp_in i
  · intro i
    exact cutoff_uChart_hasWeakPartialDeriv_univ (I := I) (M := M) D
      hχ_smooth hχ_cs hχ_supp_in i
  · exact cutoff_uChart_memLp_two_univ (I := I) (M := M) D
      hχ_smooth hχ_cs hχ_supp_in

private noncomputable def cutoff_uChart_witness
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {χ : EuclN → ℝ} (hχ_smooth : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχ_cs : HasCompactSupport χ)
    (hχ_supp_in : tsupport χ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    DeGiorgi.MemW1pWitness (d := Module.finrank ℝ E) (ENNReal.ofReal 2)
      (fun x => χ x * D.u_chart x) Set.univ where
  memLp := by
    have h_lp := cutoff_uChart_memLp_two_univ (I := I) (M := M) D
      hχ_smooth hχ_cs hχ_supp_in
    rw [Measure.restrict_univ]
    have h_two_eq : ENNReal.ofReal 2 = (2 : ℝ≥0∞) := by norm_num
    rw [h_two_eq]
    exact h_lp
  weakGrad := fun x =>
    WithLp.toLp 2 fun i =>
      (fderiv ℝ χ x) (EuclideanSpace.single i 1) * D.u_chart x +
      χ x * D.weak_partial i x
  weakGrad_component_memLp := by
    intro i
    have h_lp := cutoff_uChart_partial_memLp_two_univ (I := I) (M := M) D
      hχ_smooth hχ_cs hχ_supp_in i
    rw [Measure.restrict_univ]
    have h_eq :
        (fun x =>
          (WithLp.toLp 2 fun j =>
            (fderiv ℝ χ x) (EuclideanSpace.single j 1) * D.u_chart x +
            χ x * D.weak_partial j x) i) =
        (fun x =>
          (fderiv ℝ χ x) (EuclideanSpace.single i 1) * D.u_chart x +
          χ x * D.weak_partial i x) := by
      funext x
      simp
    rw [h_eq]
    have h_two_eq : ENNReal.ofReal 2 = (2 : ℝ≥0∞) := by norm_num
    rw [h_two_eq]
    exact h_lp
  isWeakGrad := by
    intro i
    have h_eq :
        (fun x =>
          (WithLp.toLp 2 fun j =>
            (fderiv ℝ χ x) (EuclideanSpace.single j 1) * D.u_chart x +
            χ x * D.weak_partial j x) i) =
        (fun x =>
          (fderiv ℝ χ x) (EuclideanSpace.single i 1) * D.u_chart x +
          χ x * D.weak_partial i x) := by
      funext x
      simp
    rw [h_eq]
    exact cutoff_uChart_hasWeakPartialDeriv_univ (I := I) (M := M) D
      hχ_smooth hχ_cs hχ_supp_in i

theorem exists_smooth_uChart_approx
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {χ : EuclN → ℝ} (hχ_smooth : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχ_cs : HasCompactSupport χ)
    (hχ_supp_in : tsupport χ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ u_seq : ℕ → EuclN → ℝ,
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (u_seq n)) ∧
      (∀ n, HasCompactSupport (u_seq n)) ∧
      Tendsto (fun n => eLpNorm
        (fun x => u_seq n x - χ x * D.u_chart x) 2 (volume : Measure EuclN))
        atTop (𝓝 0) ∧
      ∀ i : Fin (Module.finrank ℝ E),
        Tendsto (fun n => eLpNorm
          (fun x => (fderiv ℝ (u_seq n) x) (EuclideanSpace.single i 1) -
            ((fderiv ℝ χ x) (EuclideanSpace.single i 1) * D.u_chart x +
             χ x * D.weak_partial i x)) 2 (volume : Measure EuclN))
          atTop (𝓝 0) := by
  classical
  let hw :=
    cutoff_uChart_witness (I := I) (M := M) D hχ_smooth hχ_cs hχ_supp_in
  have h_χu_cs : HasCompactSupport (fun x => χ x * D.u_chart x) := by
    refine HasCompactSupport.intro' (K := tsupport χ)
      hχ_cs (isClosed_tsupport χ) ?_
    intro x hx
    have hχx : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
    rw [hχx, zero_mul]
  have hp : (1 : ℝ) < 2 := by norm_num
  obtain ⟨u_seq, hu_smooth, hu_cs, _hu_supp_thicken, hu_tendsto, hu_grad_tendsto⟩ :=
    DeGiorgi.exists_smooth_compactSupport_W1p_approx_univ
      (d := Module.finrank ℝ E) hp hw h_χu_cs
  refine ⟨u_seq, hu_smooth, hu_cs, ?_, ?_⟩
  · have h_two_eq : ENNReal.ofReal 2 = (2 : ℝ≥0∞) := by norm_num
    have h_eq_tendsto :
        (fun n => eLpNorm (fun x => u_seq n x - χ x * D.u_chart x) 2
          (volume : Measure EuclN)) =
        (fun n => eLpNorm (fun x => u_seq n x - χ x * D.u_chart x)
          (ENNReal.ofReal 2) (volume : Measure EuclN)) := by
      funext n
      rw [h_two_eq]
    rw [h_eq_tendsto]
    exact hu_tendsto
  · intro i
    have h_two_eq : ENNReal.ofReal 2 = (2 : ℝ≥0∞) := by norm_num
    have h_eq_tendsto :
        (fun n => eLpNorm
          (fun x => (fderiv ℝ (u_seq n) x) (EuclideanSpace.single i 1) -
            ((fderiv ℝ χ x) (EuclideanSpace.single i 1) * D.u_chart x +
             χ x * D.weak_partial i x)) 2 (volume : Measure EuclN)) =
        (fun n => eLpNorm
          (fun x => (fderiv ℝ (u_seq n) x) (EuclideanSpace.single i 1) -
            hw.weakGrad x i) (ENNReal.ofReal 2) (volume : Measure EuclN)) := by
      funext n
      have h_grad_pt : ∀ x : EuclN, hw.weakGrad x i =
          (fderiv ℝ χ x) (EuclideanSpace.single i 1) * D.u_chart x +
          χ x * D.weak_partial i x := by
        intro x
        change (WithLp.toLp 2 fun j =>
            (fderiv ℝ χ x) (EuclideanSpace.single j 1) * D.u_chart x +
            χ x * D.weak_partial j x) i = _
        simp
      have h_lhs_eq :
          (fun x => (fderiv ℝ (u_seq n) x) (EuclideanSpace.single i 1) -
            ((fderiv ℝ χ x) (EuclideanSpace.single i 1) * D.u_chart x +
             χ x * D.weak_partial i x)) =
          (fun x => (fderiv ℝ (u_seq n) x) (EuclideanSpace.single i 1) -
            hw.weakGrad x i) := by
        funext x
        rw [h_grad_pt x]
      conv_lhs => rw [h_lhs_eq]
      congr 1
      exact h_two_eq.symm
    rw [h_eq_tendsto]
    exact hu_grad_tendsto i

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem standardNirenbergTest_smooth_seq
    {η : EuclN → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_supp : HasCompactSupport η)
    (k : Fin (Module.finrank ℝ E))
    {R₀ : ℝ} {h : ℝ} (hh : h ≠ 0) (_hh_le : |h| ≤ R₀)
    {u_seq : ℕ → EuclN → ℝ}
    (hu_seq_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (u_seq n))
    (_hu_seq_cs : ∀ n, HasCompactSupport (u_seq n)) :
    ∀ n, ContDiff ℝ (⊤ : ℕ∞)
      (standardNirenbergTest (d := Module.finrank ℝ E) k h η (u_seq n)) ∧
        HasCompactSupport
          (standardNirenbergTest (d := Module.finrank ℝ E) k h η
            (u_seq n)) := by
  classical
  intro n
  refine ⟨?_, ?_⟩
  · exact contDiff_nirenbergTestFunction_aux (d := Module.finrank ℝ E)
      hη (hu_seq_smooth n) k hh
  · exact standardNirenbergTest_hasCompactSupport
      (d := Module.finrank ℝ E) k h hη_supp (u_seq n)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma eLpNorm_translate_eq_local (k : Fin (Module.finrank ℝ E)) (h : ℝ)
    (F : EuclN → ℝ) :
    eLpNorm (DifferentialGeometry.Analysis.Sobolev.translate
      (d := Module.finrank ℝ E) k h F) 2 (volume : Measure EuclN) =
      eLpNorm F 2 (volume : Measure EuclN) := by
  set τ : EuclN ≃ₜ EuclN :=
    Homeomorph.addRight (h • EuclideanSpace.single k 1) with hτ_def
  have hMP : MeasurePreserving τ volume volume := by
    rw [show (τ : EuclN → EuclN) = fun x => x + h • EuclideanSpace.single k 1
      from rfl]
    exact measurePreserving_add_right volume _
  have hτ_emb : MeasurableEmbedding τ := τ.measurableEmbedding
  have h_eq :
      DifferentialGeometry.Analysis.Sobolev.translate
        (d := Module.finrank ℝ E) k h F = F ∘ (τ : EuclN → EuclN) := rfl
  rw [h_eq]
  rw [show eLpNorm F 2 (volume : Measure EuclN) =
      eLpNorm F 2 (Measure.map τ volume) from by rw [hMP.map_eq]]
  exact (hτ_emb.eLpNorm_map_measure (g := F) (p := 2)).symm

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma eLpNorm_diffQuot_le_local
    (k : Fin (Module.finrank ℝ E)) {h : ℝ} (hh : h ≠ 0) {F : EuclN → ℝ}
    (hF_aesm : AEStronglyMeasurable F (volume : Measure EuclN)) :
    eLpNorm (DifferentialGeometry.Analysis.Sobolev.diffQuot
      (d := Module.finrank ℝ E) k h F) 2 (volume : Measure EuclN) ≤
      (2 / ENNReal.ofReal |h|) * eLpNorm F 2 (volume : Measure EuclN) := by
  have h_dq_eq : DifferentialGeometry.Analysis.Sobolev.diffQuot
      (d := Module.finrank ℝ E) k h F =
      fun x => h⁻¹ * (DifferentialGeometry.Analysis.Sobolev.translate
        (d := Module.finrank ℝ E) k h F x - F x) := by
    funext x
    rw [DifferentialGeometry.Analysis.Sobolev.diffQuot_apply_of_ne
      (d := Module.finrank ℝ E) k hh F x]
    change (F (x + h • EuclideanSpace.single k 1) - F x) / h =
      h⁻¹ * (F (x + h • EuclideanSpace.single k 1) - F x)
    field_simp
  rw [h_dq_eq]
  have h_eq_pi : (fun x => h⁻¹ * (DifferentialGeometry.Analysis.Sobolev.translate
        (d := Module.finrank ℝ E) k h F x - F x)) =
      h⁻¹ • (DifferentialGeometry.Analysis.Sobolev.translate
        (d := Module.finrank ℝ E) k h F - F) := by
    funext x
    simp [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  rw [h_eq_pi]
  rw [eLpNorm_const_smul h⁻¹]
  have hτF_aesm : AEStronglyMeasurable
      (DifferentialGeometry.Analysis.Sobolev.translate
        (d := Module.finrank ℝ E) k h F) (volume : Measure EuclN) := by
    have hMP : MeasurePreserving
        (fun x : EuclN => x + h • EuclideanSpace.single k 1) volume volume :=
      measurePreserving_add_right volume _
    exact hF_aesm.comp_measurePreserving hMP
  have h_minkowski :
      eLpNorm (DifferentialGeometry.Analysis.Sobolev.translate
        (d := Module.finrank ℝ E) k h F - F) 2 (volume : Measure EuclN) ≤
        eLpNorm (DifferentialGeometry.Analysis.Sobolev.translate
          (d := Module.finrank ℝ E) k h F) 2 (volume : Measure EuclN) +
          eLpNorm F 2 (volume : Measure EuclN) :=
    eLpNorm_sub_le hτF_aesm hF_aesm (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  rw [eLpNorm_translate_eq_local k h F] at h_minkowski
  have h_step : eLpNorm (DifferentialGeometry.Analysis.Sobolev.translate
      (d := Module.finrank ℝ E) k h F - F) 2 (volume : Measure EuclN) ≤
      2 * eLpNorm F 2 (volume : Measure EuclN) := by
    rw [two_mul]; exact h_minkowski
  have h_inv_abs : |h⁻¹| = |h|⁻¹ := abs_inv _
  have habs_h_pos : 0 < |h| := abs_pos.mpr hh
  have h_ofReal_inv :
      ENNReal.ofReal |h⁻¹| = (ENNReal.ofReal |h|)⁻¹ := by
    rw [h_inv_abs]
    exact ENNReal.ofReal_inv_of_pos habs_h_pos
  have h_enorm_abs : (‖(h⁻¹ : ℝ)‖ₑ : ℝ≥0∞) = ENNReal.ofReal |h⁻¹| := by
    rw [Real.enorm_eq_ofReal_abs]
  rw [h_enorm_abs, h_ofReal_inv]
  calc (ENNReal.ofReal |h|)⁻¹ *
        eLpNorm (DifferentialGeometry.Analysis.Sobolev.translate
          (d := Module.finrank ℝ E) k h F - F) 2 (volume : Measure EuclN)
      ≤ (ENNReal.ofReal |h|)⁻¹ *
          (2 * eLpNorm F 2 (volume : Measure EuclN)) := by gcongr
    _ = 2 / ENNReal.ofReal |h| * eLpNorm F 2 (volume : Measure EuclN) := by
        rw [← mul_assoc]
        congr 1
        rw [ENNReal.div_eq_inv_mul]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma standardNirenbergTest_sub
    (k : Fin (Module.finrank ℝ E)) (h : ℝ) (η u₁ u₂ : EuclN → ℝ) :
    (standardNirenbergTest (d := Module.finrank ℝ E) k h η u₁) -
        (standardNirenbergTest (d := Module.finrank ℝ E) k h η u₂) =
      standardNirenbergTest (d := Module.finrank ℝ E) k h η (u₁ - u₂) := by
  unfold standardNirenbergTest
  have h_inner_sub :
      (fun y => (η y)^2 *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h (u₁ - u₂) y) =
      (fun y => (η y)^2 *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h u₁ y) -
      (fun y => (η y)^2 *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h u₂ y) := by
    funext y
    rw [DifferentialGeometry.Analysis.Sobolev.diffQuot_sub
      (d := Module.finrank ℝ E) k h]
    simp [Pi.sub_apply]
    ring
  rw [h_inner_sub]
  rw [DifferentialGeometry.Analysis.Sobolev.diffQuot_sub
    (d := Module.finrank ℝ E) k (-h)]

omit [NeZero (Module.finrank ℝ E)] in
theorem standardNirenbergTest_seq_tendsto_eLpNorm
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {χ : EuclN → ℝ} (hχ_smooth : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχ_cs : HasCompactSupport χ)
    (hχ_supp_in : tsupport χ ⊆ chartTargetEuclid (I := I) (M := M) α)
    {η : EuclN → ℝ} (hη_smooth : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_cs : HasCompactSupport η)
    (k : Fin (Module.finrank ℝ E))
    {R₀ : ℝ} {h : ℝ} (hh : h ≠ 0) (_hh_le : |h| ≤ R₀)
    {K_0 : Set EuclN} (_hK_0_compact : IsCompact K_0)
    (hχ_one : ∀ x ∈ Metric.cthickening |h| K_0, χ x = 1)
    (hη_supp_in_K_0 : tsupport η ⊆ K_0)
    {u_seq : ℕ → EuclN → ℝ}
    (hu_seq_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (u_seq n))
    (_hu_seq_cs : ∀ n, HasCompactSupport (u_seq n))
    (hu_seq_l2_tendsto : Tendsto (fun n => eLpNorm
      (fun x => u_seq n x - χ x * D.u_chart x) 2
      (volume : Measure EuclN)) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm
      (fun x => standardNirenbergTest (d := Module.finrank ℝ E) k h η (u_seq n) x -
        standardNirenbergTest (d := Module.finrank ℝ E) k h η D.u_chart x) 2
      ((volume : Measure EuclN).restrict
        (Metric.cthickening |h| K_0))) atTop (𝓝 0) := by
  classical
  have h_test_eq : standardNirenbergTest (d := Module.finrank ℝ E) k h η
      (fun x => χ x * D.u_chart x) =
      standardNirenbergTest (d := Module.finrank ℝ E) k h η D.u_chart := by
    funext x
    by_cases hh0 : h = 0
    · subst hh0
      simp [standardNirenbergTest, DifferentialGeometry.Analysis.Sobolev.diffQuot]
    have h_test_eq_pointwise : ∀ v : EuclN → ℝ,
        standardNirenbergTest (d := Module.finrank ℝ E) k h η v x =
        ((η (x + (-h) • EuclideanSpace.single k 1))^2 *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h v
            (x + (-h) • EuclideanSpace.single k 1) -
          (η x)^2 * DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h v x) / (-h) := by
      intro v
      exact standardNirenbergTest_apply (d := Module.finrank ℝ E) k h η v x hh0
    rw [h_test_eq_pointwise (fun x => χ x * D.u_chart x),
      h_test_eq_pointwise D.u_chart]
    have h_diff_apply : ∀ v y,
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h v y =
          (v (y + h • EuclideanSpace.single k 1) - v y) / h := fun v y =>
      DifferentialGeometry.Analysis.Sobolev.diffQuot_apply_of_ne
        (d := Module.finrank ℝ E) k hh0 v y
    rw [h_diff_apply, h_diff_apply, h_diff_apply, h_diff_apply]
    by_cases hxK0 : x ∈ Metric.cthickening |h| K_0
    · have h_prod_eq : ∀ z, (η z)^2 * (((χ (z + h • EuclideanSpace.single k 1)) *
            D.u_chart (z + h • EuclideanSpace.single k 1) - χ z * D.u_chart z) / h) =
          (η z)^2 * (((D.u_chart (z + h • EuclideanSpace.single k 1)) -
            D.u_chart z) / h) := by
        intro z
        by_cases hηz : η z = 0
        · rw [show (η z)^2 = 0 from by rw [hηz]; ring, zero_mul, zero_mul]
        have hz_in_supp : z ∈ tsupport η := subset_tsupport η hηz
        have hz_in_K0 : z ∈ K_0 := hη_supp_in_K_0 hz_in_supp
        have hz_in_cthick : z ∈ Metric.cthickening |h| K_0 :=
          Metric.self_subset_cthickening _ hz_in_K0
        have hz_shift_in_cthick : z + h • EuclideanSpace.single k 1 ∈
            Metric.cthickening |h| K_0 := by
          refine Metric.mem_cthickening_of_dist_le _ z |h| K_0 hz_in_K0 ?_
          rw [dist_eq_norm, add_sub_cancel_left, norm_smul]
          simp [Real.norm_eq_abs]
        have hχz : χ z = 1 := hχ_one z hz_in_cthick
        have hχz_shift : χ (z + h • EuclideanSpace.single k 1) = 1 :=
          hχ_one _ hz_shift_in_cthick
        rw [hχz, hχz_shift, one_mul, one_mul]
      rw [h_prod_eq x, h_prod_eq (x + (-h) • EuclideanSpace.single k 1)]
    · have hηx_zero : η x = 0 := by
        by_contra hηx
        have hx_in_supp : x ∈ tsupport η := subset_tsupport η hηx
        have hx_in_K0 : x ∈ K_0 := hη_supp_in_K_0 hx_in_supp
        exact hxK0 (Metric.self_subset_cthickening _ hx_in_K0)
      have hηx_shift_zero : η (x + (-h) • EuclideanSpace.single k 1) = 0 := by
        by_contra hηxs
        have hxs_in_supp : x + (-h) • EuclideanSpace.single k 1 ∈ tsupport η :=
          subset_tsupport η hηxs
        have hxs_in_K0 : x + (-h) • EuclideanSpace.single k 1 ∈ K_0 :=
          hη_supp_in_K_0 hxs_in_supp
        have hx_in_cthick : x ∈ Metric.cthickening |h| K_0 := by
          refine Metric.mem_cthickening_of_dist_le _
            (x + (-h) • EuclideanSpace.single k 1) |h| K_0 hxs_in_K0 ?_
          rw [dist_eq_norm]
          have h_calc : x - (x + (-h) • EuclideanSpace.single k 1) =
              h • EuclideanSpace.single k 1 := by
            rw [sub_add_eq_sub_sub, sub_self, zero_sub, ← neg_smul, neg_neg]
          rw [h_calc, norm_smul]
          simp [Real.norm_eq_abs]
        exact hxK0 hx_in_cthick
      rw [show (η x)^2 = 0 from by rw [hηx_zero]; ring,
        show (η (x + (-h) • EuclideanSpace.single k 1))^2 = 0 from by
          rw [hηx_shift_zero]; ring]
      simp
  have h_diff_eq : ∀ n,
      (fun x => standardNirenbergTest (d := Module.finrank ℝ E) k h η (u_seq n) x -
        standardNirenbergTest (d := Module.finrank ℝ E) k h η D.u_chart x) =
      standardNirenbergTest (d := Module.finrank ℝ E) k h η
        (u_seq n - fun x => χ x * D.u_chart x) := by
    intro n
    rw [← h_test_eq]
    exact standardNirenbergTest_sub k h η (u_seq n)
      (fun x => χ x * D.u_chart x)
  have hη_cont : Continuous η := hη_smooth.continuous
  have hη_abs_cont : Continuous (fun x => |η x|) := hη_cont.abs
  obtain ⟨M_η, hM_η_nn, hM_η_bd⟩ : ∃ M_η : ℝ, 0 ≤ M_η ∧ ∀ x, |η x| ≤ M_η := by
    by_cases hSupp_empty : (tsupport η).Nonempty
    · obtain ⟨xMax, _hxMax_in, hxMax_max⟩ :=
        hη_cs.exists_isMaxOn hSupp_empty hη_abs_cont.continuousOn
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
  have h_univ_tendsto :
      Tendsto (fun n => eLpNorm
        (fun x => standardNirenbergTest (d := Module.finrank ℝ E) k h η (u_seq n) x -
          standardNirenbergTest (d := Module.finrank ℝ E) k h η D.u_chart x) 2
        (volume : Measure EuclN)) atTop (𝓝 0) := by
    have h_eLp_eq : ∀ n,
        eLpNorm (fun x =>
          standardNirenbergTest (d := Module.finrank ℝ E) k h η (u_seq n) x -
          standardNirenbergTest (d := Module.finrank ℝ E) k h η D.u_chart x) 2
        (volume : Measure EuclN) =
        eLpNorm (standardNirenbergTest (d := Module.finrank ℝ E) k h η
          (u_seq n - fun x => χ x * D.u_chart x)) 2
        (volume : Measure EuclN) := by
      intro n
      rw [h_diff_eq n]
    have h_χu_lp : MemLp (fun x => χ x * D.u_chart x) 2
        (volume : Measure EuclN) :=
      cutoff_uChart_memLp_two_univ (I := I) (M := M) D
        hχ_smooth hχ_cs hχ_supp_in
    have h_aesm_diff : ∀ n,
        AEStronglyMeasurable (u_seq n - fun x => χ x * D.u_chart x)
          (volume : Measure EuclN) := by
      intro n
      have h_uSeq_aesm : AEStronglyMeasurable (u_seq n)
          (volume : Measure EuclN) :=
        (hu_seq_smooth n).continuous.aestronglyMeasurable
      exact h_uSeq_aesm.sub h_χu_lp.aestronglyMeasurable
    have h_diff_lp : ∀ n,
        MemLp (u_seq n - fun x => χ x * D.u_chart x) 2
          (volume : Measure EuclN) := by
      intro n
      have h_uSeq_lp : MemLp (u_seq n) 2 (volume : Measure EuclN) :=
        (hu_seq_smooth n).continuous.memLp_of_hasCompactSupport (_hu_seq_cs n)
      exact h_uSeq_lp.sub h_χu_lp
    have h_bound : ∀ n,
        eLpNorm (standardNirenbergTest (d := Module.finrank ℝ E) k h η
          (u_seq n - fun x => χ x * D.u_chart x)) 2
        (volume : Measure EuclN) ≤
        (2 / ENNReal.ofReal |h|) * ENNReal.ofReal (M_η^2) *
          ((2 / ENNReal.ofReal |h|) *
            eLpNorm (u_seq n - fun x => χ x * D.u_chart x) 2
              (volume : Measure EuclN)) := by
      intro n
      have h_test_bound :=
        eLpNorm_standardNirenbergTest_le (d := Module.finrank ℝ E)
          k hh hη_cont (h_aesm_diff n) hM_η_nn hM_η_bd
      have h_dq_bound :=
        eLpNorm_diffQuot_le_local k hh (h_aesm_diff n)
      have h_step1 :
          eLpNorm (standardNirenbergTest (d := Module.finrank ℝ E) k h η
            (u_seq n - fun x => χ x * D.u_chart x)) 2
            (volume : Measure EuclN) ≤
          (2 / ENNReal.ofReal |h|) * ENNReal.ofReal (M_η^2) *
            eLpNorm (DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h
              (u_seq n - fun x => χ x * D.u_chart x)) 2
            (volume : Measure EuclN) := h_test_bound
      have h_step2 :
          (2 / ENNReal.ofReal |h|) * ENNReal.ofReal (M_η^2) *
            eLpNorm (DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h
              (u_seq n - fun x => χ x * D.u_chart x)) 2
            (volume : Measure EuclN) ≤
          (2 / ENNReal.ofReal |h|) * ENNReal.ofReal (M_η^2) *
            ((2 / ENNReal.ofReal |h|) *
              eLpNorm (u_seq n - fun x => χ x * D.u_chart x) 2
                (volume : Measure EuclN)) := by gcongr
      exact h_step1.trans h_step2
    have h_diff_eLp_eq : ∀ n,
        eLpNorm (fun x => u_seq n x - χ x * D.u_chart x) 2
          (volume : Measure EuclN) =
        eLpNorm (u_seq n - fun x => χ x * D.u_chart x) 2
          (volume : Measure EuclN) := by
      intro n; rfl
    have hu_seq_l2_tendsto' :
        Tendsto (fun n => eLpNorm (u_seq n - fun x => χ x * D.u_chart x) 2
          (volume : Measure EuclN)) atTop (𝓝 0) := by
      have h_eq : (fun n => eLpNorm (u_seq n - fun x => χ x * D.u_chart x) 2
            (volume : Measure EuclN)) =
          (fun n => eLpNorm (fun x => u_seq n x - χ x * D.u_chart x) 2
            (volume : Measure EuclN)) := by
        funext n; rfl
      rw [h_eq]
      exact hu_seq_l2_tendsto
    have h_const_tendsto :
        Tendsto (fun n =>
          (2 / ENNReal.ofReal |h|) * ENNReal.ofReal (M_η^2) *
            ((2 / ENNReal.ofReal |h|) *
              eLpNorm (u_seq n - fun x => χ x * D.u_chart x) 2
                (volume : Measure EuclN))) atTop (𝓝 0) := by
      have hh_abs_pos : 0 < |h| := abs_pos.mpr hh
      have h_const_ne_top : (2 / ENNReal.ofReal |h|) * ENNReal.ofReal (M_η^2) *
          (2 / ENNReal.ofReal |h|) ≠ ⊤ := by
        refine ENNReal.mul_ne_top (ENNReal.mul_ne_top ?_ ?_) ?_
        · exact ENNReal.div_ne_top ENNReal.ofNat_ne_top
            (ENNReal.ofReal_pos.mpr hh_abs_pos).ne'
        · exact ENNReal.ofReal_ne_top
        · exact ENNReal.div_ne_top ENNReal.ofNat_ne_top
            (ENNReal.ofReal_pos.mpr hh_abs_pos).ne'
      have h_eq_assoc : ∀ n,
          (2 / ENNReal.ofReal |h|) * ENNReal.ofReal (M_η^2) *
            ((2 / ENNReal.ofReal |h|) *
              eLpNorm (u_seq n - fun x => χ x * D.u_chart x) 2
                (volume : Measure EuclN)) =
          ((2 / ENNReal.ofReal |h|) * ENNReal.ofReal (M_η^2) *
            (2 / ENNReal.ofReal |h|)) *
            eLpNorm (u_seq n - fun x => χ x * D.u_chart x) 2
              (volume : Measure EuclN) := by
        intro n; ring
      simp only [h_eq_assoc]
      have h := ENNReal.Tendsto.const_mul (a :=
          (2 / ENNReal.ofReal |h|) * ENNReal.ofReal (M_η^2) *
            (2 / ENNReal.ofReal |h|)) hu_seq_l2_tendsto' (Or.inr h_const_ne_top)
      simpa using h
    rw [show (fun n => eLpNorm (fun x =>
          standardNirenbergTest (d := Module.finrank ℝ E) k h η (u_seq n) x -
          standardNirenbergTest (d := Module.finrank ℝ E) k h η D.u_chart x) 2
        (volume : Measure EuclN)) = _ from funext h_eLp_eq]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_const_tendsto
      ?_ ?_
    · refine Filter.Eventually.of_forall (fun n => ?_)
      exact zero_le _
    · exact Filter.Eventually.of_forall h_bound
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_univ_tendsto
    ?_ ?_
  · refine Filter.Eventually.of_forall (fun n => ?_)
    exact zero_le _
  · refine Filter.Eventually.of_forall (fun n => ?_)
    exact MeasureTheory.eLpNorm_mono_measure
      (fun x =>
        standardNirenbergTest (d := Module.finrank ℝ E) k h η (u_seq n) x -
        standardNirenbergTest (d := Module.finrank ℝ E) k h η D.u_chart x)
      Measure.restrict_le_self

end SubstitutionDischargeSmoothApprox
end Sobolev
end Analysis
end DifferentialGeometry
