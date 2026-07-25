import DifferentialGeometry.Analysis.Elliptic.Regularity.H1Compl.GradientLipschitz
import DifferentialGeometry.Analysis.Sobolev.Manifold.MeasureBridgeUniform
import DifferentialGeometry.Geometry.Operator.NormGradSq
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic


noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace H1ComplGradientLipschitzBound

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.H1ComplGradientChartBridge
open DifferentialGeometry.Analysis.Laplacian.H1ComplGradientLipschitz
open DifferentialGeometry.Analysis.Laplacian.H1ComplToLpChartBridge
open DifferentialGeometry.Analysis.Sobolev.Chart

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

noncomputable def kPouCompact (α : M) : Set EuclN :=
  (toEuclidean : E ≃L[ℝ] EuclN) ''
    ((extChartAt I α) '' (tsupport (fun x : M =>
      (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x)))

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem kPouCompact_isCompact (α : M) :
    IsCompact (kPouCompact (I := I) (M := M) α) := by
  classical
  unfold kPouCompact
  have h_tsupp_compact : IsCompact (tsupport
      fun x : M => (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x) :=
    isClosed_tsupport _ |>.isCompact
  have h_tsupp_sub_src : tsupport (fun x : M =>
      (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x) ⊆
      (chartAt H α).source :=
    (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M) α
  have h_ext_cont : ContinuousOn (extChartAt I α)
      (tsupport fun x : M => (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x) := by
    have h_src_eq : (chartAt H α).source = (extChartAt I α).source :=
      (DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
        (I := I) (M := M) α).symm
    refine (continuousOn_extChartAt (I := I) α).mono ?_
    rw [← h_src_eq]; exact h_tsupp_sub_src
  have h_ext_image_compact : IsCompact ((extChartAt I α) '' (tsupport
      fun x : M => (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x)) :=
    h_tsupp_compact.image_of_continuousOn h_ext_cont
  exact h_ext_image_compact.image (toEuclidean (E := E)).continuous

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompactSpace M] in
theorem kPouCompact_subset_chartTargetEuclid (α : M) :
    kPouCompact (I := I) (M := M) α ⊆
      DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α := by
  classical
  intro y hy
  rcases hy with ⟨z, hz, hzy⟩
  rcases hz with ⟨x, hx, hxz⟩
  have h_tsupp_sub_src : tsupport (fun x : M =>
      (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x) ⊆
      (chartAt H α).source :=
    (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M) α
  have hxsrc : x ∈ (extChartAt I α).source := by
    rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
      (I := I) (M := M)]
    exact h_tsupp_sub_src hx
  have hz_target : z ∈ (extChartAt I α).target := by
    rw [← hxz]; exact (extChartAt I α).map_source hxsrc
  refine ⟨z, hz_target, hzy⟩

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompactSpace M] in
theorem smoothChartExt_support_subset_kPouCompact
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g) :
    Function.support (smoothChartExt (I := I) (M := M) g α v) ⊆
      kPouCompact (I := I) (M := M) α := by
  classical
  intro y hy
  have hy_ne : smoothChartExt (I := I) (M := M) g α v y ≠ 0 := hy
  by_cases hy_target : y ∈ chartTargetEuclid (I := I) (M := M) α
  · obtain ⟨w, hw_target, hwy⟩ := hy_target
    have h_eq : (toEuclidean (E := E)).symm y = w := by
      rw [← hwy]; exact (toEuclidean (E := E)).symm_apply_apply w
    have h_apply : smoothChartExt (I := I) (M := M) g α v y =
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
            ((extChartAt I α).symm w)) *
          v.toFun ((extChartAt I α).symm w) := by
      rw [smoothChartExt_apply_of_mem_target (I := I) (M := M) g α v
        (h_eq ▸ hw_target)]
      rw [h_eq]
    rw [h_apply] at hy_ne
    by_contra h_notin
    apply hy_ne
    have h_pou_zero : (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) ((extChartAt I α).symm w) = 0 := by
      by_contra h_pou_ne
      apply h_notin
      have h_pou_in_supp : (extChartAt I α).symm w ∈ Function.support
          fun x : M => (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x := h_pou_ne
      have h_pou_in_tsupp : (extChartAt I α).symm w ∈ tsupport
          fun x : M => (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x :=
        subset_tsupport _ h_pou_in_supp
      have h_ext_right : (extChartAt I α) ((extChartAt I α).symm w) = w :=
        (extChartAt I α).right_inv hw_target
      exact ⟨w, ⟨(extChartAt I α).symm w, h_pou_in_tsupp, h_ext_right⟩, hwy⟩
    rw [h_pou_zero]; ring
  · exfalso
    apply hy_ne
    have h_notMem : (toEuclidean (E := E)).symm y ∉ (extChartAt I α).target := by
      intro h_in
      apply hy_target
      refine ⟨(toEuclidean (E := E)).symm y, h_in, ?_⟩
      simp
    exact smoothChartExt_apply_of_notMem_target (I := I) (M := M) g α v h_notMem

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem smoothChartExt_tsupport_subset_kPouCompact
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g) :
    tsupport (smoothChartExt (I := I) (M := M) g α v) ⊆
      kPouCompact (I := I) (M := M) α := by
  refine closure_minimal (smoothChartExt_support_subset_kPouCompact
    (I := I) (M := M) g α v) ?_
  exact (kPouCompact_isCompact (I := I) (M := M) α).isClosed

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem smoothChartExtPartial_tsupport_subset_kPouCompact
    (g : SmoothRiemannianMetric I M) (α : M) (j : Fin (Module.finrank ℝ E))
    (v : SmoothScalar g) :
    tsupport (smoothChartExtPartial (I := I) (M := M) g α j v) ⊆
      kPouCompact (I := I) (M := M) α := by
  have h_fderiv_supp : tsupport (smoothChartExtPartial (I := I) (M := M) g α j v) ⊆
      tsupport (smoothChartExt (I := I) (M := M) g α v) :=
    tsupport_fderiv_apply_subset (𝕜 := ℝ) (EuclideanSpace.single j 1)
  exact h_fderiv_supp.trans
    (smoothChartExt_tsupport_subset_kPouCompact (I := I) (M := M) g α v)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem exists_density_sup_on_kPouCompact
    (g : SmoothRiemannianMetric I M) (α : M) :
    ∃ M_d : ℝ, 0 < M_d ∧
      ∀ y ∈ kPouCompact (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y ≤ M_d := by
  classical
  by_cases hKne : (kPouCompact (I := I) (M := M) α).Nonempty
  · have hK_compact : IsCompact (kPouCompact (I := I) (M := M) α) :=
      kPouCompact_isCompact (I := I) (M := M) α
    have hK_in : kPouCompact (I := I) (M := M) α ⊆
        chartTargetEuclid (I := I) (M := M) α :=
      kPouCompact_subset_chartTargetEuclid (I := I) (M := M) α
    have h_dens_contOn : ContinuousOn (densityOnEuclid (I := I) g α)
        (kPouCompact (I := I) (M := M) α) :=
      (densityOnEuclid_continuousOn (I := I) g α).mono hK_in
    obtain ⟨y₀, hy₀_mem, hy₀_max⟩ :=
      hK_compact.exists_isMaxOn hKne h_dens_contOn
    have h_pos : 0 < densityOnEuclid (I := I) g α y₀ :=
      densityOnEuclid_pos (I := I) g α (hK_in hy₀_mem)
    refine ⟨densityOnEuclid (I := I) g α y₀, h_pos, fun y hy => hy₀_max hy⟩
  · refine ⟨1, by norm_num, ?_⟩
    intro y hy
    rw [Set.not_nonempty_iff_eq_empty] at hKne
    rw [hKne] at hy
    exact absurd hy (Set.notMem_empty y)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem chartPulledWeightedMeasure_kPouCompact_lt_top
    (g : SmoothRiemannianMetric I M) (α : M) :
    (chartPulledWeightedMeasure (I := I) g α) (kPouCompact (I := I) (M := M) α)
      < ⊤ := by
  classical
  have hK_compact : IsCompact (kPouCompact (I := I) (M := M) α) :=
    kPouCompact_isCompact (I := I) (M := M) α
  obtain ⟨M_d, _hM_d_pos, hM_d_bd⟩ :=
    exists_density_sup_on_kPouCompact (I := I) (M := M) g α
  unfold chartPulledWeightedMeasure
  rw [withDensity_apply _ hK_compact.measurableSet]
  have h_int_bd : (∫⁻ y in kPouCompact (I := I) (M := M) α,
      ENNReal.ofReal (densityOnEuclid (I := I) g α y) ∂(volume : Measure EuclN)) ≤
      ENNReal.ofReal M_d *
        (volume : Measure EuclN) (kPouCompact (I := I) (M := M) α) := by
    calc (∫⁻ y in kPouCompact (I := I) (M := M) α,
        ENNReal.ofReal (densityOnEuclid (I := I) g α y) ∂(volume : Measure EuclN))
        ≤ ∫⁻ _y in kPouCompact (I := I) (M := M) α,
            ENNReal.ofReal M_d ∂(volume : Measure EuclN) := by
          refine MeasureTheory.setLIntegral_mono_ae' hK_compact.measurableSet ?_
          refine Filter.Eventually.of_forall (fun y hy => ?_)
          exact ENNReal.ofReal_le_ofReal (hM_d_bd y hy)
      _ = ENNReal.ofReal M_d *
            (volume : Measure EuclN) (kPouCompact (I := I) (M := M) α) := by
          rw [MeasureTheory.setLIntegral_const]
  exact lt_of_le_of_lt h_int_bd
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK_compact.measure_lt_top)

noncomputable def chartPushedPartialLpLin
    (g : SmoothRiemannianMetric I M) (α : M) (j : Fin (Module.finrank ℝ E)) :
    SmoothScalar g →ₗ[ℝ]
      Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) where
  toFun v := chartPushedPartialLp (I := I) (M := M) g α j v
    (chartPushedPartial_memLp (I := I) (M := M) g α j v)
  map_add' v w := by
    classical
    apply MeasureTheory.Lp.ext
    have h1 := MeasureTheory.MemLp.coeFn_toLp
      (chartPushedPartial_memLp (I := I) (M := M) g α j (v + w))
    have h2 := MeasureTheory.MemLp.coeFn_toLp
      (chartPushedPartial_memLp (I := I) (M := M) g α j v)
    have h3 := MeasureTheory.MemLp.coeFn_toLp
      (chartPushedPartial_memLp (I := I) (M := M) g α j w)
    have h_aeEq_vw := chartPushedPartial_aeEq_smoothChartExtPartial
      (I := I) (M := M) g α j (v + w)
    have h_aeEq_v := chartPushedPartial_aeEq_smoothChartExtPartial
      (I := I) (M := M) g α j v
    have h_aeEq_w := chartPushedPartial_aeEq_smoothChartExtPartial
      (I := I) (M := M) g α j w
    have h_smooth_add := smoothChartExtPartial_add (I := I) (M := M) g α j v w
    have h_aeEq_combined :
        chartPushedPartial (I := I) (M := M) g α j (v + w) =ᵐ[
          (chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)]
        fun y => chartPushedPartial (I := I) (M := M) g α j v y +
            chartPushedPartial (I := I) (M := M) g α j w y := by
      filter_upwards [h_aeEq_vw, h_aeEq_v, h_aeEq_w] with y hy_vw hy_v hy_w
      rw [hy_vw, hy_v, hy_w]
      rw [h_smooth_add]
      rfl
    have h_lhs : (chartPushedPartialLp (I := I) (M := M) g α j (v + w)
        (chartPushedPartial_memLp (I := I) (M := M) g α j (v + w)) :
          EuclN → ℝ) =ᵐ[
        (chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
        chartPushedPartial (I := I) (M := M) g α j (v + w) := by
      unfold chartPushedPartialLp
      exact h1
    have h_coeAdd := MeasureTheory.Lp.coeFn_add
      (chartPushedPartialLp (I := I) (M := M) g α j v
        (chartPushedPartial_memLp (I := I) (M := M) g α j v))
      (chartPushedPartialLp (I := I) (M := M) g α j w
        (chartPushedPartial_memLp (I := I) (M := M) g α j w))
    refine h_lhs.trans (h_aeEq_combined.trans ?_)
    refine EventuallyEq.symm ?_
    filter_upwards [h_coeAdd, h2, h3] with y hy_add hy_v hy_w
    have h_v_eq : (chartPushedPartialLp (I := I) (M := M) g α j v
          (chartPushedPartial_memLp (I := I) (M := M) g α j v) :
            EuclN → ℝ) y =
          chartPushedPartial (I := I) (M := M) g α j v y := hy_v
    have h_w_eq : (chartPushedPartialLp (I := I) (M := M) g α j w
          (chartPushedPartial_memLp (I := I) (M := M) g α j w) :
            EuclN → ℝ) y =
          chartPushedPartial (I := I) (M := M) g α j w y := hy_w
    rw [hy_add, Pi.add_apply, h_v_eq, h_w_eq]
  map_smul' c v := by
    classical
    apply MeasureTheory.Lp.ext
    have h1 := MeasureTheory.MemLp.coeFn_toLp
      (chartPushedPartial_memLp (I := I) (M := M) g α j (c • v))
    have h2 := MeasureTheory.MemLp.coeFn_toLp
      (chartPushedPartial_memLp (I := I) (M := M) g α j v)
    have h_aeEq_cv := chartPushedPartial_aeEq_smoothChartExtPartial
      (I := I) (M := M) g α j (c • v)
    have h_aeEq_v := chartPushedPartial_aeEq_smoothChartExtPartial
      (I := I) (M := M) g α j v
    have h_smooth_smul := smoothChartExtPartial_smul (I := I) (M := M) g α j c v
    have h_aeEq_combined :
        chartPushedPartial (I := I) (M := M) g α j (c • v) =ᵐ[
          (chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)]
        fun y => c * chartPushedPartial (I := I) (M := M) g α j v y := by
      filter_upwards [h_aeEq_cv, h_aeEq_v] with y hy_cv hy_v
      rw [hy_cv, hy_v]
      rw [h_smooth_smul]
      rw [Pi.smul_apply, smul_eq_mul]
    have h_lhs : (chartPushedPartialLp (I := I) (M := M) g α j (c • v)
        (chartPushedPartial_memLp (I := I) (M := M) g α j (c • v)) :
          EuclN → ℝ) =ᵐ[
        (chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
        chartPushedPartial (I := I) (M := M) g α j (c • v) := by
      unfold chartPushedPartialLp
      exact h1
    have h_coeSmul := MeasureTheory.Lp.coeFn_smul c
      (chartPushedPartialLp (I := I) (M := M) g α j v
        (chartPushedPartial_memLp (I := I) (M := M) g α j v))
    refine h_lhs.trans (h_aeEq_combined.trans ?_)
    refine EventuallyEq.symm ?_
    filter_upwards [h_coeSmul, h2] with y hy_smul hy_v
    have h_v_eq : (chartPushedPartialLp (I := I) (M := M) g α j v
          (chartPushedPartial_memLp (I := I) (M := M) g α j v) :
            EuclN → ℝ) y =
          chartPushedPartial (I := I) (M := M) g α j v y := hy_v
    change ((c • (chartPushedPartialLp (I := I) (M := M) g α j v
        (chartPushedPartial_memLp (I := I) (M := M) g α j v))) : Lp ℝ 2 _) y =
        c * chartPushedPartial (I := I) (M := M) g α j v y
    rw [hy_smul, Pi.smul_apply, h_v_eq, smul_eq_mul]

omit [NeZero (Module.finrank ℝ E)] in
lemma chartPushedPartialLpLin_apply
    (g : SmoothRiemannianMetric I M) (α : M) (j : Fin (Module.finrank ℝ E))
    (v : SmoothScalar g) :
    chartPushedPartialLpLin (I := I) (M := M) g α j v =
      chartPushedPartialLp (I := I) (M := M) g α j v
        (chartPushedPartial_memLp (I := I) (M := M) g α j v) := rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem norm_chartPushedPartialLpLin
    (g : SmoothRiemannianMetric I M) (α : M) (j : Fin (Module.finrank ℝ E))
    (v : SmoothScalar g) :
    ‖chartPushedPartialLpLin (I := I) (M := M) g α j v‖ =
      (eLpNorm (chartPushedPartial (I := I) (M := M) g α j v) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))).toReal := by
  rw [chartPushedPartialLpLin_apply]
  exact norm_chartPushedPartialLp (I := I) (M := M) g α j v
    (chartPushedPartial_memLp (I := I) (M := M) g α j v)

omit [NeZero (Module.finrank ℝ E)] in
theorem chartPushedPartial_lipschitz_uniform_support
    (g : SmoothRiemannianMetric I M) (α : M) (j : Fin (Module.finrank ℝ E))
    (v : SmoothScalar g) :
    ∃ N : ℝ, 0 ≤ N ∧ (∀ y : EuclN, |smoothChartExtPartial (I := I) (M := M) g α j v y| ≤ N) ∧
    eLpNorm (chartPushedPartial (I := I) (M := M) g α j v) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)) ≤
      ENNReal.ofReal N *
        ((chartPulledWeightedMeasure (I := I) g α)
          (kPouCompact (I := I) (M := M) α)) ^ ((1 : ℝ) / 2) := by
  classical
  have h_cont : Continuous (smoothChartExtPartial (I := I) (M := M) g α j v) :=
    smoothChartExtPartial_continuous (I := I) (M := M) g α j v
  have h_cs : HasCompactSupport (smoothChartExtPartial (I := I) (M := M) g α j v) :=
    smoothChartExtPartial_hasCompactSupport (I := I) (M := M) g α j v
  obtain ⟨N₀, hN₀⟩ := h_cont.bounded_above_of_compact_support h_cs
  set N : ℝ := max N₀ 0 with hN_def
  refine ⟨N, le_max_right _ _, fun y => ?_, ?_⟩
  · exact (hN₀ y).trans (le_max_left _ _)
  have h_aeEq := chartPushedPartial_aeEq_smoothChartExtPartial
    (I := I) (M := M) g α j v
  rw [eLpNorm_congr_ae h_aeEq]
  have hK_compact : IsCompact (kPouCompact (I := I) (M := M) α) :=
    kPouCompact_isCompact (I := I) (M := M) α
  have hK_meas : MeasurableSet (kPouCompact (I := I) (M := M) α) :=
    hK_compact.measurableSet
  set μ_w := (chartPulledWeightedMeasure (I := I) g α).restrict
    (chartTargetEuclid (I := I) (M := M) α) with hμ_w_def
  have hN_nn : 0 ≤ N := le_max_right _ _
  have hN_bd : ∀ y, |smoothChartExtPartial (I := I) (M := M) g α j v y| ≤ N := fun y =>
    (hN₀ y).trans (le_max_left _ _)
  have h_ptbd_sq : ∀ y, ‖smoothChartExtPartial (I := I) (M := M) g α j v y‖ₑ ^ (2 : ℝ) ≤
      ENNReal.ofReal (N^2) *
        Set.indicator (kPouCompact (I := I) (M := M) α) (fun _ => (1 : ℝ≥0∞)) y := by
    intro y
    by_cases hy : y ∈ kPouCompact (I := I) (M := M) α
    · rw [Set.indicator_of_mem hy, mul_one]
      have h_enorm_le : ‖smoothChartExtPartial (I := I) (M := M) g α j v y‖ₑ ≤
          ENNReal.ofReal N := by
        rw [Real.enorm_eq_ofReal_abs]
        exact ENNReal.ofReal_le_ofReal (hN_bd y)
      calc ‖smoothChartExtPartial (I := I) (M := M) g α j v y‖ₑ ^ (2 : ℝ)
          ≤ (ENNReal.ofReal N) ^ (2 : ℝ) := ENNReal.rpow_le_rpow h_enorm_le (by norm_num)
        _ = ENNReal.ofReal (N^2) := by
            rw [show (N^2 : ℝ) = N * N from sq N]
            rw [ENNReal.ofReal_mul hN_nn]
            rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num,
                ENNReal.rpow_natCast, sq]
    · have h_f_zero : smoothChartExtPartial (I := I) (M := M) g α j v y = 0 := by
        by_contra hne
        exact hy (smoothChartExtPartial_tsupport_subset_kPouCompact
          (I := I) (M := M) g α j v (subset_tsupport _ hne))
      rw [h_f_zero, enorm_zero]
      rw [Set.indicator_of_notMem hy, mul_zero]
      rw [ENNReal.zero_rpow_of_pos (by norm_num)]
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal
    (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
  rw [show ((2 : ℝ≥0∞).toReal : ℝ) = 2 from by norm_num]
  have h_lint_bd : ∫⁻ y, ‖smoothChartExtPartial (I := I) (M := M) g α j v y‖ₑ ^ (2 : ℝ)
      ∂μ_w ≤
      ENNReal.ofReal (N^2) *
        (chartPulledWeightedMeasure (I := I) g α)
          (kPouCompact (I := I) (M := M) α) := by
    calc ∫⁻ y, ‖smoothChartExtPartial (I := I) (M := M) g α j v y‖ₑ ^ (2 : ℝ) ∂μ_w
          ≤ ∫⁻ y, ENNReal.ofReal (N^2) *
              Set.indicator (kPouCompact (I := I) (M := M) α) (fun _ => (1 : ℝ≥0∞)) y
              ∂μ_w := MeasureTheory.lintegral_mono_ae (Filter.Eventually.of_forall h_ptbd_sq)
        _ = ENNReal.ofReal (N^2) *
              ∫⁻ y, Set.indicator (kPouCompact (I := I) (M := M) α)
                  (fun _ => (1 : ℝ≥0∞)) y ∂μ_w := by
            rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        _ = ENNReal.ofReal (N^2) * (μ_w (kPouCompact (I := I) (M := M) α)) := by
            congr 1
            rw [MeasureTheory.lintegral_indicator_const hK_meas]
            rw [one_mul]
        _ ≤ ENNReal.ofReal (N^2) *
              (chartPulledWeightedMeasure (I := I) g α)
                (kPouCompact (I := I) (M := M) α) := by
            have h_restrict_le : μ_w (kPouCompact (I := I) (M := M) α) ≤
                (chartPulledWeightedMeasure (I := I) g α)
                  (kPouCompact (I := I) (M := M) α) := by
              rw [hμ_w_def]
              exact MeasureTheory.Measure.restrict_apply_le _ _
            gcongr
  calc (∫⁻ y, ‖smoothChartExtPartial (I := I) (M := M) g α j v y‖ₑ ^ (2 : ℝ) ∂μ_w) ^
        ((1 : ℝ) / 2)
      ≤ (ENNReal.ofReal (N^2) *
          (chartPulledWeightedMeasure (I := I) g α)
            (kPouCompact (I := I) (M := M) α)) ^ ((1 : ℝ) / 2) := by
        apply ENNReal.rpow_le_rpow h_lint_bd
        positivity
    _ = ENNReal.ofReal (N^2) ^ ((1 : ℝ) / 2) *
          ((chartPulledWeightedMeasure (I := I) g α)
            (kPouCompact (I := I) (M := M) α)) ^ ((1 : ℝ) / 2) :=
        ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ 1 / 2)
    _ = ENNReal.ofReal N *
          ((chartPulledWeightedMeasure (I := I) g α)
            (kPouCompact (I := I) (M := M) α)) ^ ((1 : ℝ) / 2) := by
        congr 1
        rw [show (N^2 : ℝ) = N * N from sq N]
        rw [ENNReal.ofReal_mul hN_nn]
        rw [show (ENNReal.ofReal N * ENNReal.ofReal N : ℝ≥0∞) =
            (ENNReal.ofReal N)^(2 : ℝ) from by
          rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num]
          rw [ENNReal.rpow_natCast, sq]]
        rw [← ENNReal.rpow_mul]
        rw [show (2 : ℝ) * (1 / 2) = 1 from by ring]
        rw [ENNReal.rpow_one]

end H1ComplGradientLipschitzBound
end Laplacian
end Analysis
end DifferentialGeometry

end
