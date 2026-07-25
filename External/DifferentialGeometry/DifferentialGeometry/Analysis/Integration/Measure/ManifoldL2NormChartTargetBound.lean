import DifferentialGeometry.Analysis.Integration.Measure.TensorChartPulled
import DifferentialGeometry.Analysis.Integration.Measure.PouDensityChartBound
import DifferentialGeometry.Analysis.Integration.Measure.Family
import DifferentialGeometry.Analysis.Integration.Measure.MeasureBridge
import DifferentialGeometry.Tensor.RSTensor.Defs

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function Tensor0SBundle
open scoped Manifold ContDiff ENNReal NNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" =>
  EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

open DifferentialGeometry.Analysis.Sobolev.Chart

variable (I M) in

noncomputable def chartL2BridgeMα
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M) : ℝ :=
  (exists_pou_chartDensity_bound_on_chartTarget
    (I := I) (M := M) g α).choose

lemma chartL2BridgeMα_nonneg
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M) :
    0 ≤ chartL2BridgeMα (I := I) (M := M) g α :=
  (exists_pou_chartDensity_bound_on_chartTarget
    (I := I) (M := M) g α).choose_spec.1

lemma chartL2BridgeMα_le
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    {y : E} (hy : y ∈ (extChartAt I α).target) :
    (chartAtlasPOU I M α : M → ℝ) ((extChartAt I α).symm y) *
        chartDensity g α ((extChartAt I α).symm y) ≤
      chartL2BridgeMα (I := I) (M := M) g α :=
  (exists_pou_chartDensity_bound_on_chartTarget
    (I := I) (M := M) g α).choose_spec.2 y hy

variable (I M) in

noncomputable def chartTargetL2BridgeConstant
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) : ℝ :=
  (euclideanHaarFactor E : ℝ) *
    ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      (chartL2BridgeMα (I := I) (M := M) g α + 1)

lemma chartTargetL2BridgeConstant_nonneg
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) :
    0 ≤ chartTargetL2BridgeConstant (I := I) (M := M) g := by
  refine mul_nonneg ?_ ?_
  · exact (euclideanHaarFactor_pos (E := E)).le
  · refine Finset.sum_nonneg ?_
    intro α _
    have := chartL2BridgeMα_nonneg (I := I) (M := M) g α
    linarith

private lemma norm_eq_norm_toModel
    {r s : ℕ} {x : M} (T : TensorRSSpace r s I x) :
    ‖T‖ = ‖TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
      (r := r) (s := s) (x := x) T‖ := rfl

private lemma enorm_sq_apply_eq_ofReal_pushedNormSq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : Π b : M, TensorRSSpace r s I b)
    {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    (‖S ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ₑ : ℝ≥0∞) ^ 2
      = ENNReal.ofReal
          (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α S y) := by
  classical
  set x : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hx_def
  have hnorm_eq : ‖S x‖ = ‖TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I)
      (M := M) (r := r) (s := s) (x := x) (S x)‖ :=
    norm_eq_norm_toModel (S x)
  have henorm_eq : ‖S x‖ₑ = ENNReal.ofReal ‖S x‖ := (ofReal_norm _).symm
  have hpush_eq :
      tensorTrivProjPushedNormSq (I := I) (M := M) g r s α S y
        = ‖TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
            (r := r) (s := s) (x := x) (S x)‖ ^ 2 := by
    rw [tensorTrivProjPushedNormSq_apply_of_mem (I := I) (M := M) g r s α S hy]
  rw [henorm_eq, hpush_eq, ← hnorm_eq]
  rw [← ENNReal.ofReal_pow (norm_nonneg _) 2]


theorem manifold_l2_norm_sq_le_finset_sum_chart_target_l2_norm_sq
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : Π b : M, TensorRSSpace r s I b)
    (hS_meas : Measurable (fun x : M => ‖S x‖ ^ 2)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∫⁻ x, (‖S x‖ₑ : ℝ≥0∞) ^ 2
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)
        ≤ ENNReal.ofReal C *
            ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                ENNReal.ofReal
                  (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α S y)
                ∂(volume : Measure EuclN) := by
  classical
  set Sfin : Finset M := chartAtlasPOU_finset (I := I) (M := M) with hSfin_def
  set F : M → ℝ≥0∞ := fun x => (‖S x‖ₑ : ℝ≥0∞) ^ 2 with hF_def
  have hF_meas : Measurable F := by
    have heq : F = fun x : M => ENNReal.ofReal (‖S x‖ ^ 2) := by
      funext x
      have hen : ‖S x‖ₑ = ENNReal.ofReal ‖S x‖ := (ofReal_norm _).symm
      change (‖S x‖ₑ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (‖S x‖ ^ 2)
      rw [hen, ← ENNReal.ofReal_pow (norm_nonneg _) 2]
    rw [heq]
    exact ENNReal.measurable_ofReal.comp hS_meas
  let Mα : M → ℝ := fun α =>
    chartL2BridgeMα (I := I) (M := M) g α
  have hMα_nn : ∀ α : M, 0 ≤ Mα α := fun α =>
    chartL2BridgeMα_nonneg (I := I) (M := M) g α
  have hMα_le : ∀ α : M, ∀ y ∈ (extChartAt I α).target,
      (chartAtlasPOU I M α : M → ℝ) ((extChartAt I α).symm y) *
          chartDensity g α ((extChartAt I α).symm y) ≤ Mα α :=
    fun α y hy => chartL2BridgeMα_le (I := I) (M := M) g α hy
  set cE : ℝ := (euclideanHaarFactor E : ℝ) with hcE_def
  have hcE_nn : 0 ≤ cE := (euclideanHaarFactor_pos (E := E)).le
  set C : ℝ := chartTargetL2BridgeConstant (I := I) (M := M) g
    with hC_def
  have hC_unfold : C = cE * ∑ α ∈ Sfin, (Mα α + 1) := by
    rw [hC_def, hcE_def, hSfin_def]
    rfl
  have hC_nn : 0 ≤ C :=
    chartTargetL2BridgeConstant_nonneg (I := I) (M := M) g
  refine ⟨C, hC_nn, ?_⟩
  rw [riemannianVolumeMeasure_def]
  rw [riemannianMeasure_lintegral_eq (I := I) g (chartAtlasPOU I M) hF_meas]
  have htsum_eq_finsum :
      ∑' β : M, ∫⁻ x, ENNReal.ofReal
              ((chartAtlasPOU I M β : M → ℝ) x) * F x
            ∂(chartLocalMeasure (I := I) g β) =
        ∑ β ∈ Sfin, ∫⁻ x, ENNReal.ofReal
              ((chartAtlasPOU I M β : M → ℝ) x) * F x
            ∂(chartLocalMeasure (I := I) g β) := by
    rw [tsum_eq_sum]
    intro β hβ
    have hρ_zero : ∀ x : M, (chartAtlasPOU I M β : M → ℝ) x = 0 := fun x =>
      chartAtlasPOU_weight_zero_of_notMem (I := I) (M := M) hβ x
    have hint_zero : ∀ x : M, ENNReal.ofReal
        ((chartAtlasPOU I M β : M → ℝ) x) * F x = 0 := by
      intro x
      rw [hρ_zero x]
      simp
    have hintegrand : (fun x : M => ENNReal.ofReal
        ((chartAtlasPOU I M β : M → ℝ) x) * F x) =
        (fun _ : M => (0 : ℝ≥0∞)) := by
      funext x
      exact hint_zero x
    rw [hintegrand]
    simp
  rw [htsum_eq_finsum]
  refine
    le_trans
      (b := ∑ α ∈ Sfin,
        ENNReal.ofReal (cE * (Mα α + 1)) *
          ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal
              (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α S y)
            ∂(volume : Measure EuclN))
      (Finset.sum_le_sum ?_) ?_
  · intro α hα_mem
    have hρα_meas : Measurable (fun x : M =>
        ENNReal.ofReal ((chartAtlasPOU I M α : M → ℝ) x)) :=
      measurable_ofReal_pou_weight (chartAtlasPOU I M) α
    have hgα_meas : Measurable
        (fun x : M => ENNReal.ofReal ((chartAtlasPOU I M α : M → ℝ) x) * F x) :=
      hρα_meas.mul hF_meas
    have hbridge :=
      chartLocalMeasure_lintegral_via_chartTargetEuclid
        (I := I) (M := M) g α (F := fun x : M =>
          ENNReal.ofReal ((chartAtlasPOU I M α : M → ℝ) x) * F x) hgα_meas
    rw [hbridge]
    have hpt_bound : ∀ y, y ∈ chartTargetEuclid (I := I) (M := M) α →
        ENNReal.ofReal
            (chartDensity g α
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
          (ENNReal.ofReal
              ((chartAtlasPOU I M α : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            F ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
        ≤ ENNReal.ofReal (Mα α + 1) *
            ENNReal.ofReal
              (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α S y) := by
      intro y hy
      have hy_target : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
        rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
        exact hy
      have hdens_pos := chartDensity_pos_on_target
        (I := I) (M := M) g α hy_target
      have hdens_nn := hdens_pos.le
      have hρα_nn := (chartAtlasPOU I M).nonneg α
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
      have hprod_le := hMα_le α ((toEuclidean (E := E)).symm y) hy_target
      have hkey :
          ENNReal.ofReal
              (chartDensity g α
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            ENNReal.ofReal
              ((chartAtlasPOU I M α : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
            ≤ ENNReal.ofReal (Mα α + 1) := by
        have hbase :
            chartDensity g α
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
              (chartAtlasPOU I M α : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
              ≤ Mα α + 1 := by
          have hsym : (chartAtlasPOU I M α : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
              chartDensity g α
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
              ≤ Mα α := hprod_le
          have : chartDensity g α
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
              (chartAtlasPOU I M α : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
              ≤ Mα α := by
            rw [mul_comm]; exact hsym
          linarith
        rw [← ENNReal.ofReal_mul hdens_nn]
        exact ENNReal.ofReal_le_ofReal hbase
      have hF_eq :
          F ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) =
            ENNReal.ofReal
              (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α S y) := by
        rw [hF_def]
        exact enorm_sq_apply_eq_ofReal_pushedNormSq
          (I := I) (M := M) g r s α S hy
      calc ENNReal.ofReal
              (chartDensity g α
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            (ENNReal.ofReal
                ((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
              F ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
          = (ENNReal.ofReal
                (chartDensity g α
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
              ENNReal.ofReal
                ((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))) *
              F ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := by
            ring
        _ ≤ ENNReal.ofReal (Mα α + 1) *
              F ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := by
            exact mul_le_mul_left hkey _
        _ = ENNReal.ofReal (Mα α + 1) *
              ENNReal.ofReal
                (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α S y) := by
            rw [hF_eq]
    have hint_le :
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal
              (chartDensity g α
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            (ENNReal.ofReal
                ((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
              F ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
            ∂(volume : Measure EuclN)
          ≤ ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal (Mα α + 1) *
                ENNReal.ofReal
                  (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α S y)
              ∂(volume : Measure EuclN) := by
      exact MeasureTheory.setLIntegral_mono_ae'
        (chartTargetEuclid_measurableSet (I := I) (M := M) α)
        (Filter.Eventually.of_forall hpt_bound)
    have hpull :
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal (Mα α + 1) *
              ENNReal.ofReal
                (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α S y)
            ∂(volume : Measure EuclN)
          = ENNReal.ofReal (Mα α + 1) *
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                ENNReal.ofReal
                  (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α S y)
                ∂(volume : Measure EuclN) := by
      rw [MeasureTheory.lintegral_const_mul']
      exact ENNReal.ofReal_ne_top
    have hfinal_step :
        (euclideanHaarFactor E : ℝ≥0∞) *
          ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal
                (chartDensity g α
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
              (ENNReal.ofReal
                  ((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                F ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
            ∂(volume : Measure EuclN)
          ≤ ENNReal.ofReal (cE * (Mα α + 1)) *
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                ENNReal.ofReal
                  (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α S y)
                ∂(volume : Measure EuclN) := by
      calc (euclideanHaarFactor E : ℝ≥0∞) *
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal
                  (chartDensity g α
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                (ENNReal.ofReal
                    ((chartAtlasPOU I M α : M → ℝ)
                      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                  F ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
              ∂(volume : Measure EuclN)
          ≤ (euclideanHaarFactor E : ℝ≥0∞) *
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                ENNReal.ofReal (Mα α + 1) *
                  ENNReal.ofReal
                    (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α S y)
                ∂(volume : Measure EuclN) := by
            exact mul_le_mul_right hint_le _
        _ = (euclideanHaarFactor E : ℝ≥0∞) *
              (ENNReal.ofReal (Mα α + 1) *
                ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                  ENNReal.ofReal
                    (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α S y)
                  ∂(volume : Measure EuclN)) := by
            rw [hpull]
        _ = ((euclideanHaarFactor E : ℝ≥0∞) *
              ENNReal.ofReal (Mα α + 1)) *
                ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                  ENNReal.ofReal
                    (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α S y)
                  ∂(volume : Measure EuclN) := by
            ring
        _ = ENNReal.ofReal (cE * (Mα α + 1)) *
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                ENNReal.ofReal
                  (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α S y)
                ∂(volume : Measure EuclN) := by
            congr 1
            rw [hcE_def]
            have hMα1_nn : 0 ≤ Mα α + 1 := by have := hMα_nn α; linarith
            rw [ENNReal.ofReal_mul (NNReal.coe_nonneg _)]
            congr 1
            rw [ENNReal.ofReal_coe_nnreal]
    exact hfinal_step
  · have hper_term_le : ∀ α ∈ Sfin,
        ENNReal.ofReal (cE * (Mα α + 1)) ≤ ENNReal.ofReal C := by
      intro α hα_mem
      refine ENNReal.ofReal_le_ofReal ?_
      have h_term_le : Mα α + 1 ≤ ∑ β ∈ Sfin, (Mα β + 1) := by
        have hsum_nn : ∀ β ∈ Sfin, 0 ≤ Mα β + 1 := by
          intro β _; have := hMα_nn β; linarith
        exact Finset.single_le_sum (f := fun β => Mα β + 1) hsum_nn hα_mem
      rw [hC_unfold]
      exact mul_le_mul_of_nonneg_left h_term_le hcE_nn
    have hper_term_bound : ∀ α ∈ Sfin,
        ENNReal.ofReal (cE * (Mα α + 1)) *
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal
                (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α S y)
              ∂(volume : Measure EuclN)
          ≤ ENNReal.ofReal C *
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                ENNReal.ofReal
                  (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α S y)
                ∂(volume : Measure EuclN) := by
      intro α hα_mem
      exact mul_le_mul_left (hper_term_le α hα_mem) _
    have hsum_bound :=
      Finset.sum_le_sum hper_term_bound
    have hpull_out :
        ∑ α ∈ Sfin,
            ENNReal.ofReal C *
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                ENNReal.ofReal
                  (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α S y)
                ∂(volume : Measure EuclN)
          = ENNReal.ofReal C *
              ∑ α ∈ Sfin,
                ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                  ENNReal.ofReal
                    (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α S y)
                  ∂(volume : Measure EuclN) := by
      rw [← Finset.mul_sum]
    rw [← hpull_out]
    exact hsum_bound


theorem uniform_manifold_l2_norm_sq_le_finset_sum_chart_target_l2_norm_sq
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : Π b : M, TensorRSSpace r s I b)
    (hS_meas : Measurable (fun x : M => ‖S x‖ ^ 2)) :
    ∫⁻ x, (‖S x‖ₑ : ℝ≥0∞) ^ 2
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) ≤
      ENNReal.ofReal
          (chartTargetL2BridgeConstant (I := I) (M := M) g) *
        ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
          ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal
              (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α S y)
            ∂(volume : Measure EuclN) := by
  classical
  set Sfin : Finset M := chartAtlasPOU_finset (I := I) (M := M) with hSfin_def
  set F : M → ℝ≥0∞ := fun x => (‖S x‖ₑ : ℝ≥0∞) ^ 2 with hF_def
  have hF_meas : Measurable F := by
    have heq : F = fun x : M => ENNReal.ofReal (‖S x‖ ^ 2) := by
      funext x
      have hen : ‖S x‖ₑ = ENNReal.ofReal ‖S x‖ := (ofReal_norm _).symm
      change (‖S x‖ₑ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (‖S x‖ ^ 2)
      rw [hen, ← ENNReal.ofReal_pow (norm_nonneg _) 2]
    rw [heq]
    exact ENNReal.measurable_ofReal.comp hS_meas
  let Mα : M → ℝ := fun α =>
    chartL2BridgeMα (I := I) (M := M) g α
  have hMα_nn : ∀ α : M, 0 ≤ Mα α := fun α =>
    chartL2BridgeMα_nonneg (I := I) (M := M) g α
  have hMα_le : ∀ α : M, ∀ y ∈ (extChartAt I α).target,
      (chartAtlasPOU I M α : M → ℝ) ((extChartAt I α).symm y) *
          chartDensity g α ((extChartAt I α).symm y) ≤ Mα α :=
    fun α y hy => chartL2BridgeMα_le (I := I) (M := M) g α hy
  set cE : ℝ := (euclideanHaarFactor E : ℝ) with hcE_def
  have hcE_nn : 0 ≤ cE := (euclideanHaarFactor_pos (E := E)).le
  set C : ℝ := chartTargetL2BridgeConstant (I := I) (M := M) g
    with hC_def
  have hC_unfold : C = cE * ∑ α ∈ Sfin, (Mα α + 1) := by
    rw [hC_def, hcE_def, hSfin_def]
    rfl
  rw [riemannianVolumeMeasure_def]
  rw [riemannianMeasure_lintegral_eq (I := I) g (chartAtlasPOU I M) hF_meas]
  have htsum_eq_finsum :
      ∑' β : M, ∫⁻ x, ENNReal.ofReal
              ((chartAtlasPOU I M β : M → ℝ) x) * F x
            ∂(chartLocalMeasure (I := I) g β) =
        ∑ β ∈ Sfin, ∫⁻ x, ENNReal.ofReal
              ((chartAtlasPOU I M β : M → ℝ) x) * F x
            ∂(chartLocalMeasure (I := I) g β) := by
    rw [tsum_eq_sum]
    intro β hβ
    have hρ_zero : ∀ x : M, (chartAtlasPOU I M β : M → ℝ) x = 0 := fun x =>
      chartAtlasPOU_weight_zero_of_notMem (I := I) (M := M) hβ x
    have hint_zero : ∀ x : M, ENNReal.ofReal
        ((chartAtlasPOU I M β : M → ℝ) x) * F x = 0 := by
      intro x
      rw [hρ_zero x]
      simp
    have hintegrand : (fun x : M => ENNReal.ofReal
        ((chartAtlasPOU I M β : M → ℝ) x) * F x) =
        (fun _ : M => (0 : ℝ≥0∞)) := by
      funext x
      exact hint_zero x
    rw [hintegrand]
    simp
  rw [htsum_eq_finsum]
  refine
    le_trans
      (b := ∑ α ∈ Sfin,
        ENNReal.ofReal (cE * (Mα α + 1)) *
          ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal
              (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α S y)
            ∂(volume : Measure EuclN))
      (Finset.sum_le_sum ?_) ?_
  · intro α hα_mem
    have hρα_meas : Measurable (fun x : M =>
        ENNReal.ofReal ((chartAtlasPOU I M α : M → ℝ) x)) :=
      measurable_ofReal_pou_weight (chartAtlasPOU I M) α
    have hgα_meas : Measurable
        (fun x : M => ENNReal.ofReal ((chartAtlasPOU I M α : M → ℝ) x) * F x) :=
      hρα_meas.mul hF_meas
    have hbridge :=
      chartLocalMeasure_lintegral_via_chartTargetEuclid
        (I := I) (M := M) g α (F := fun x : M =>
          ENNReal.ofReal ((chartAtlasPOU I M α : M → ℝ) x) * F x) hgα_meas
    rw [hbridge]
    have hpt_bound : ∀ y, y ∈ chartTargetEuclid (I := I) (M := M) α →
        ENNReal.ofReal
            (chartDensity g α
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
          (ENNReal.ofReal
              ((chartAtlasPOU I M α : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            F ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
        ≤ ENNReal.ofReal (Mα α + 1) *
            ENNReal.ofReal
              (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α S y) := by
      intro y hy
      have hy_target : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
        rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
        exact hy
      have hdens_pos := chartDensity_pos_on_target
        (I := I) (M := M) g α hy_target
      have hdens_nn := hdens_pos.le
      have hρα_nn := (chartAtlasPOU I M).nonneg α
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
      have hprod_le := hMα_le α ((toEuclidean (E := E)).symm y) hy_target
      have hkey :
          ENNReal.ofReal
              (chartDensity g α
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            ENNReal.ofReal
              ((chartAtlasPOU I M α : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
            ≤ ENNReal.ofReal (Mα α + 1) := by
        have hbase :
            chartDensity g α
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
              (chartAtlasPOU I M α : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
              ≤ Mα α + 1 := by
          have hsym : (chartAtlasPOU I M α : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
              chartDensity g α
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
              ≤ Mα α := hprod_le
          have : chartDensity g α
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
              (chartAtlasPOU I M α : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
              ≤ Mα α := by
            rw [mul_comm]; exact hsym
          linarith
        rw [← ENNReal.ofReal_mul hdens_nn]
        exact ENNReal.ofReal_le_ofReal hbase
      have hF_eq :
          F ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) =
            ENNReal.ofReal
              (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α S y) := by
        rw [hF_def]
        exact enorm_sq_apply_eq_ofReal_pushedNormSq
          (I := I) (M := M) g r s α S hy
      calc ENNReal.ofReal
              (chartDensity g α
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            (ENNReal.ofReal
                ((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
              F ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
          = (ENNReal.ofReal
                (chartDensity g α
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
              ENNReal.ofReal
                ((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))) *
              F ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := by
            ring
        _ ≤ ENNReal.ofReal (Mα α + 1) *
              F ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := by
            exact mul_le_mul_left hkey _
        _ = ENNReal.ofReal (Mα α + 1) *
              ENNReal.ofReal
                (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α S y) := by
            rw [hF_eq]
    have hint_le :
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal
              (chartDensity g α
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            (ENNReal.ofReal
                ((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
              F ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
            ∂(volume : Measure EuclN)
          ≤ ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal (Mα α + 1) *
                ENNReal.ofReal
                  (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α S y)
              ∂(volume : Measure EuclN) := by
      exact MeasureTheory.setLIntegral_mono_ae'
        (chartTargetEuclid_measurableSet (I := I) (M := M) α)
        (Filter.Eventually.of_forall hpt_bound)
    have hpull :
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal (Mα α + 1) *
              ENNReal.ofReal
                (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α S y)
            ∂(volume : Measure EuclN)
          = ENNReal.ofReal (Mα α + 1) *
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                ENNReal.ofReal
                  (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α S y)
                ∂(volume : Measure EuclN) := by
      rw [MeasureTheory.lintegral_const_mul']
      exact ENNReal.ofReal_ne_top
    calc (euclideanHaarFactor E : ℝ≥0∞) *
          ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal
                (chartDensity g α
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
              (ENNReal.ofReal
                  ((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                F ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
            ∂(volume : Measure EuclN)
        ≤ (euclideanHaarFactor E : ℝ≥0∞) *
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal (Mα α + 1) *
                ENNReal.ofReal
                  (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α S y)
              ∂(volume : Measure EuclN) := by
          exact mul_le_mul_right hint_le _
      _ = (euclideanHaarFactor E : ℝ≥0∞) *
            (ENNReal.ofReal (Mα α + 1) *
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                ENNReal.ofReal
                  (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α S y)
                ∂(volume : Measure EuclN)) := by
          rw [hpull]
      _ = ((euclideanHaarFactor E : ℝ≥0∞) *
            ENNReal.ofReal (Mα α + 1)) *
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                ENNReal.ofReal
                  (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α S y)
                ∂(volume : Measure EuclN) := by
          ring
      _ = ENNReal.ofReal (cE * (Mα α + 1)) *
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal
                (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α S y)
              ∂(volume : Measure EuclN) := by
          congr 1
          rw [hcE_def]
          have hMα1_nn : 0 ≤ Mα α + 1 := by have := hMα_nn α; linarith
          rw [ENNReal.ofReal_mul (NNReal.coe_nonneg _)]
          congr 1
          rw [ENNReal.ofReal_coe_nnreal]
  · have hper_term_le : ∀ α ∈ Sfin,
        ENNReal.ofReal (cE * (Mα α + 1)) ≤ ENNReal.ofReal C := by
      intro α hα_mem
      refine ENNReal.ofReal_le_ofReal ?_
      have h_term_le : Mα α + 1 ≤ ∑ β ∈ Sfin, (Mα β + 1) := by
        have hsum_nn : ∀ β ∈ Sfin, 0 ≤ Mα β + 1 := by
          intro β _; have := hMα_nn β; linarith
        exact Finset.single_le_sum (f := fun β => Mα β + 1) hsum_nn hα_mem
      rw [hC_unfold]
      exact mul_le_mul_of_nonneg_left h_term_le hcE_nn
    have hper_term_bound : ∀ α ∈ Sfin,
        ENNReal.ofReal (cE * (Mα α + 1)) *
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal
                (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α S y)
              ∂(volume : Measure EuclN)
          ≤ ENNReal.ofReal C *
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                ENNReal.ofReal
                  (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α S y)
                ∂(volume : Measure EuclN) := by
      intro α hα_mem
      exact mul_le_mul_left (hper_term_le α hα_mem) _
    have hsum_bound :=
      Finset.sum_le_sum hper_term_bound
    have hpull_out :
        ∑ α ∈ Sfin,
            ENNReal.ofReal C *
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                ENNReal.ofReal
                  (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α S y)
                ∂(volume : Measure EuclN)
          = ENNReal.ofReal C *
              ∑ α ∈ Sfin,
                ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                  ENNReal.ofReal
                    (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α S y)
                  ∂(volume : Measure EuclN) := by
      rw [← Finset.mul_sum]
    rw [← hpull_out]
    exact hsum_bound

end Measure
end Integral
end DifferentialGeometry

end
