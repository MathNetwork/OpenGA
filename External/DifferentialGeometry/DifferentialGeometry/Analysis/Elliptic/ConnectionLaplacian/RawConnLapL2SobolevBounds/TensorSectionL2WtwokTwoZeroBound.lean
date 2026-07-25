import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RawConnLapL2SobolevBounds.RawTensorConnLapL2WtwokTwoBound
import DifferentialGeometry.Analysis.Spectral.Tensor.TrivProj.ChartTwistIdentity
import DifferentialGeometry.Analysis.Spectral.Tensor.UniformChartBounds.TensorChartTwistUniformBound


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold Set IsManifold ContinuousLinearMap Filter
open MeasureTheory
open scoped Manifold Topology Bundle ContDiff BigOperators ENNReal NNReal

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Tensor
open Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Sobolev.Tensor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

local notation "EuclN" =>
  EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

noncomputable def chartSobolevSectionNormPou
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s) :
    ℝ≥0∞ :=
  ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
    ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
      ENNReal.ofReal
          (((chartAtlasPOU I M α : M → ℝ)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
        ENNReal.ofReal
          (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
            (fun b : M => T.toSection b) y)
      ∂(volume : Measure EuclN)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] in
@[simp] lemma chartSobolevSectionNormPou_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s) :
    chartSobolevSectionNormPou (I := I) (M := M) g r s T =
      ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
            ENNReal.ofReal
              (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                (fun b : M => T.toSection b) y)
          ∂(volume : Measure EuclN) := rfl

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] in
private lemma normSq_section_le_card_mul_sum_pou_sq_mul_normSq
    {r s : ℕ} (T : Π b : M, TensorRSSpace r s I b) (x : M) :
    (‖T x‖ ^ 2 : ℝ) ≤
      ((chartAtlasPOU_finset (I := I) (M := M)).card : ℝ) *
        ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
          ((chartAtlasPOU I M α : M → ℝ) x) ^ 2 *
            ‖T x‖ ^ 2 := by
  classical
  set v : ℝ := ‖T x‖ with hv_def
  set sset : Finset M := chartAtlasPOU_finset (I := I) (M := M) with hs_def
  have hv_nn : 0 ≤ v := norm_nonneg _
  have hv_sq_nn : 0 ≤ v ^ 2 := sq_nonneg _
  have h_sum :=
    chartAtlasPOU_finset_sum_eq_one (I := I) (M := M) x
  have hv_sq_eq :
      v ^ 2 = (∑ α ∈ sset, (chartAtlasPOU I M α : M → ℝ) x * v) ^ 2 := by
    have heq : ∑ α ∈ sset, (chartAtlasPOU I M α : M → ℝ) x * v = v := by
      rw [← Finset.sum_mul, h_sum, one_mul]
    rw [heq]
  have hCS : (∑ α ∈ sset, (chartAtlasPOU I M α : M → ℝ) x * v) ^ 2 ≤
      (sset.card : ℝ) *
        ∑ α ∈ sset, ((chartAtlasPOU I M α : M → ℝ) x * v) ^ 2 := by
    have hbase := Finset.sum_mul_sq_le_sq_mul_sq sset
      (fun _ : M => (1 : ℝ))
      (fun α : M => (chartAtlasPOU I M α : M → ℝ) x * v)
    simp only [one_mul, one_pow] at hbase
    have h_sum_one : (∑ _α ∈ sset, (1 : ℝ)) = (sset.card : ℝ) := by simp
    rw [h_sum_one] at hbase
    convert hbase using 1
  have h_factor_eq : ∑ α ∈ sset, ((chartAtlasPOU I M α : M → ℝ) x * v) ^ 2 =
      ∑ α ∈ sset, ((chartAtlasPOU I M α : M → ℝ) x) ^ 2 * v ^ 2 :=
    Finset.sum_congr rfl (fun α _ => by ring)
  rw [h_factor_eq] at hCS
  calc (‖T x‖ ^ 2 : ℝ)
      = v ^ 2 := rfl
    _ = (∑ α ∈ sset, (chartAtlasPOU I M α : M → ℝ) x * v) ^ 2 := hv_sq_eq
    _ ≤ (sset.card : ℝ) *
          ∑ α ∈ sset, ((chartAtlasPOU I M α : M → ℝ) x) ^ 2 * v ^ 2 := hCS

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] in
private lemma manifold_lintegral_pou_sq_section_normSq_eq_chartTarget
    {r s : ℕ} (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g r s)
    (hsec_meas :
      Measurable (fun x : M => ‖T.toSection x‖ ^ 2))
    (α : M) :
    ∫⁻ x,
        ENNReal.ofReal (((chartAtlasPOU I M α : M → ℝ) x) ^ 2 *
            ‖T.toSection x‖ ^ 2)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      (euclideanHaarFactor E : ℝ≥0∞) *
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal
              (chartDensity g α
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2 *
                ‖T.toSection
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ ^ 2)
          ∂(volume : Measure EuclN) := by
  classical
  set F : M → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (((chartAtlasPOU I M α : M → ℝ) x) ^ 2 *
      ‖T.toSection x‖ ^ 2) with hF_def
  have hρ_cont : Continuous (fun x : M => (chartAtlasPOU I M α : M → ℝ) x) :=
    ((chartAtlasPOU I M α)).contMDiff.continuous
  have hρ_meas : Measurable (fun x : M => (chartAtlasPOU I M α : M → ℝ) x) :=
    hρ_cont.measurable
  have hρ_sq_meas : Measurable (fun x : M => ((chartAtlasPOU I M α : M → ℝ) x) ^ 2) :=
    hρ_meas.pow_const 2
  have hF_meas : Measurable F := by
    rw [hF_def]
    exact ENNReal.measurable_ofReal.comp (hρ_sq_meas.mul hsec_meas)
  have hF_supp : ∀ x : M, x ∉ (chartAt H α).source → F x = 0 := by
    intro x hx
    have hρ_zero : (chartAtlasPOU I M α : M → ℝ) x = 0 := by
      have hsub : tsupport
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) ⊆ (chartAt H α).source :=
        chartAtlasPOU_isSubordinate (I := I) (M := M) α
      have hx_notsupp : x ∉ tsupport
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) := fun hc => hx (hsub hc)
      exact image_eq_zero_of_notMem_tsupport hx_notsupp
    change ENNReal.ofReal (((chartAtlasPOU I M α : M → ℝ) x) ^ 2 *
      ‖T.toSection x‖ ^ 2) = 0
    rw [hρ_zero]
    simp
  rw [show riemannianVolumeMeasure (I := I) (M := M) g =
      riemannianMeasure (I := I) g (chartAtlasPOU I M) from rfl]
  rw [riemannianMeasure_lintegral_eq_chartLocalMeasure_of_supportIn
      (I := I) (M := M) g α hF_meas hF_supp]
  rw [chartLocalMeasure_lintegral_via_chartTargetEuclid
      (I := I) (M := M) g α hF_meas]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma section_normSq_apply_eq_pushedNormSq
    {r s : ℕ} (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g r s)
    (α : M) {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    (‖T.toSection ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ ^ 2
        : ℝ) =
      tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
        (fun b : M => T.toSection b) y := by
  classical
  rw [tensorTrivProjPushedNormSq_apply_of_mem
      (I := I) (M := M) g r s α
      (fun b : M => T.toSection b) hy]
  rfl

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] in
private lemma density_pou_sq_le_section
    (g : SmoothRiemannianMetric I M) (α : M)
    (h_supp_ne :
      (tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)).Nonempty)
    {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    chartDensity g α
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
      (((chartAtlasPOU I M α : M → ℝ)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) ≤
      (chartDensitySupPou (I := I) (M := M) g α + 1) *
      (((chartAtlasPOU I M α : M → ℝ)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) := by
  classical
  set x : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hx_def
  set ρ : ℝ := (chartAtlasPOU I M α : M → ℝ) x with hρ_def
  set dens : ℝ := chartDensity g α x with hdens_def
  have hy_target : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
    rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
    exact hy
  have hρ_nn : 0 ≤ ρ := (chartAtlasPOU I M).nonneg α x
  have hρ_sq_nn : 0 ≤ ρ ^ 2 := sq_nonneg _
  by_cases hρ_zero : ρ = 0
  · rw [show ρ ^ 2 = 0 from by rw [hρ_zero]; ring]
    simp
  · have hx_supp : x ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
      subset_tsupport _ (Function.mem_support.mpr hρ_zero)
    have hy_image : (toEuclidean (E := E)).symm y ∈
        (extChartAt I α) '' (tsupport
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) := by
      refine ⟨x, hx_supp, ?_⟩
      rw [hx_def]
      exact (extChartAt I α).right_inv hy_target
    have hdens_le : dens ≤ chartDensitySupPou (I := I) (M := M) g α := by
      rw [hdens_def, hx_def]
      exact chartDensitySupPou_le (I := I) (M := M) g α h_supp_ne hy_image
    have hbound : dens ≤ chartDensitySupPou (I := I) (M := M) g α + 1 := by
      linarith
    exact mul_le_mul_of_nonneg_right hbound hρ_sq_nn

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] in
theorem tensorSection_L2NormSq_le_chartSobolevSectionNormPou
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : SmoothCcTensor g r s),
        Measurable (fun x : M => ‖T.toSection x‖ ^ 2) →
          ∫⁻ x, (‖T.toSection x‖ₑ : ℝ≥0∞) ^ 2
              ∂(riemannianVolumeMeasure (I := I) (M := M) g) ≤
            ENNReal.ofReal
                (chartSobolevRawNormPouBridgeConstant (I := I) (M := M) g) *
              chartSobolevSectionNormPou (I := I) (M := M) g r s T := by
  classical
  refine ⟨chartSobolevRawNormPouBridgeConstant (I := I) (M := M) g,
    chartSobolevRawNormPouBridgeConstant_nonneg (I := I) (M := M) g, ?_⟩
  intro T hsec_meas
  set Sfin : Finset M := chartAtlasPOU_finset (I := I) (M := M) with hSfin_def
  set N : ℕ := Sfin.card with hN_def
  set cE : ℝ := (euclideanHaarFactor E : ℝ) with hcE_def
  have hcE_nn : 0 ≤ cE := (euclideanHaarFactor_pos (E := E)).le
  set Mα : M → ℝ := fun α => chartDensitySupPou (I := I) (M := M) g α with hMα_def
  have hMα_nn : ∀ α : M, 0 ≤ Mα α := fun α =>
    chartDensitySupPou_nonneg (I := I) (M := M) g α
  set C : ℝ := chartSobolevRawNormPouBridgeConstant (I := I) (M := M) g with hC_def
  have henorm_sq :
      (fun x : M => (‖T.toSection x‖ₑ : ℝ≥0∞) ^ 2) =
        (fun x : M => ENNReal.ofReal (‖T.toSection x‖ ^ 2)) := by
    funext x
    have hen : ‖T.toSection x‖ₑ = ENNReal.ofReal ‖T.toSection x‖ :=
      (ofReal_norm _).symm
    rw [hen, ← ENNReal.ofReal_pow (norm_nonneg _) 2]
  rw [henorm_sq]
  have h_pointwise : ∀ x : M,
      ENNReal.ofReal (‖T.toSection x‖ ^ 2) ≤
        ENNReal.ofReal ((N : ℝ) *
          ∑ α ∈ Sfin,
            ((chartAtlasPOU I M α : M → ℝ) x) ^ 2 *
              ‖T.toSection x‖ ^ 2) := by
    intro x
    have hle := normSq_section_le_card_mul_sum_pou_sq_mul_normSq
      (I := I) (M := M) (r := r) (s := s) (fun b => T.toSection b) x
    refine ENNReal.ofReal_le_ofReal hle
  have h_int_le :
      ∫⁻ x, ENNReal.ofReal (‖T.toSection x‖ ^ 2)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) ≤
        ∫⁻ x, ENNReal.ofReal ((N : ℝ) *
            ∑ α ∈ Sfin,
              ((chartAtlasPOU I M α : M → ℝ) x) ^ 2 *
                ‖T.toSection x‖ ^ 2)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
    MeasureTheory.lintegral_mono h_pointwise
  have h_nn_each : ∀ x : M, ∀ α ∈ Sfin,
      0 ≤ ((chartAtlasPOU I M α : M → ℝ) x) ^ 2 * ‖T.toSection x‖ ^ 2 := by
    intro x α _
    exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have h_nn_sum : ∀ x : M,
      0 ≤ ∑ α ∈ Sfin,
        ((chartAtlasPOU I M α : M → ℝ) x) ^ 2 * ‖T.toSection x‖ ^ 2 := by
    intro x; exact Finset.sum_nonneg (h_nn_each x)
  have hN_nn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
  have h_ofReal_factor : ∀ x : M,
      ENNReal.ofReal ((N : ℝ) *
          ∑ α ∈ Sfin,
            ((chartAtlasPOU I M α : M → ℝ) x) ^ 2 * ‖T.toSection x‖ ^ 2) =
        ENNReal.ofReal (N : ℝ) *
          ENNReal.ofReal (∑ α ∈ Sfin,
            ((chartAtlasPOU I M α : M → ℝ) x) ^ 2 * ‖T.toSection x‖ ^ 2) := fun x =>
    ENNReal.ofReal_mul hN_nn
  have h_ofReal_sum : ∀ x : M,
      ENNReal.ofReal (∑ α ∈ Sfin,
          ((chartAtlasPOU I M α : M → ℝ) x) ^ 2 * ‖T.toSection x‖ ^ 2) =
        ∑ α ∈ Sfin, ENNReal.ofReal
          (((chartAtlasPOU I M α : M → ℝ) x) ^ 2 * ‖T.toSection x‖ ^ 2) := by
    intro x
    rw [ENNReal.ofReal_sum_of_nonneg (h_nn_each x)]
  have h_int_le' :
      ∫⁻ x, ENNReal.ofReal (‖T.toSection x‖ ^ 2)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) ≤
        ENNReal.ofReal (N : ℝ) *
          ∑ α ∈ Sfin,
            ∫⁻ x, ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ) x) ^ 2 * ‖T.toSection x‖ ^ 2)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    calc
      _ ≤ ∫⁻ x, ENNReal.ofReal ((N : ℝ) *
              ∑ α ∈ Sfin,
                ((chartAtlasPOU I M α : M → ℝ) x) ^ 2 * ‖T.toSection x‖ ^ 2)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) := h_int_le
      _ = ∫⁻ x, ENNReal.ofReal (N : ℝ) *
              ENNReal.ofReal (∑ α ∈ Sfin,
                ((chartAtlasPOU I M α : M → ℝ) x) ^ 2 * ‖T.toSection x‖ ^ 2)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
            refine lintegral_congr ?_
            intro x; exact h_ofReal_factor x
      _ = ENNReal.ofReal (N : ℝ) *
            ∫⁻ x, ENNReal.ofReal (∑ α ∈ Sfin,
              ((chartAtlasPOU I M α : M → ℝ) x) ^ 2 * ‖T.toSection x‖ ^ 2)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
            rw [MeasureTheory.lintegral_const_mul']
            exact ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal (N : ℝ) *
            ∫⁻ x, ∑ α ∈ Sfin, ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ) x) ^ 2 * ‖T.toSection x‖ ^ 2)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
            congr 1
            refine lintegral_congr ?_
            intro x; exact h_ofReal_sum x
      _ = ENNReal.ofReal (N : ℝ) *
            ∑ α ∈ Sfin,
              ∫⁻ x, ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ) x) ^ 2 * ‖T.toSection x‖ ^ 2)
                ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
            congr 1
            exact lintegral_finset_sum _ (fun α _ => by
              have hρ_cont :
                  Continuous (fun x : M => (chartAtlasPOU I M α : M → ℝ) x) :=
                ((chartAtlasPOU I M α)).contMDiff.continuous
              have hρ_meas :
                  Measurable (fun x : M => (chartAtlasPOU I M α : M → ℝ) x) :=
                hρ_cont.measurable
              exact ENNReal.measurable_ofReal.comp
                ((hρ_meas.pow_const 2).mul hsec_meas))
  have h_per_alpha : ∀ α ∈ Sfin,
      ∫⁻ x, ENNReal.ofReal
            (((chartAtlasPOU I M α : M → ℝ) x) ^ 2 * ‖T.toSection x‖ ^ 2)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) ≤
        ENNReal.ofReal (cE * (Mα α + 1)) *
          ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
              ENNReal.ofReal
                (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                  (fun b : M => T.toSection b) y)
            ∂(volume : Measure EuclN) := by
    intro α hα_mem
    have h_supp_ne : (tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)).Nonempty := by
      rw [chartAtlasPOU_finset_mem] at hα_mem
      exact hα_mem.mono (subset_tsupport _)
    rw [manifold_lintegral_pou_sq_section_normSq_eq_chartTarget
      (I := I) (M := M) g T hsec_meas α]
    have hpt_bound : ∀ y, y ∈ chartTargetEuclid (I := I) (M := M) α →
        ENNReal.ofReal
            (chartDensity g α
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
          ENNReal.ofReal
            (((chartAtlasPOU I M α : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2 *
              ‖T.toSection
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ ^ 2)
          ≤ ENNReal.ofReal (Mα α + 1) *
              (ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
                ENNReal.ofReal
                  (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                    (fun b : M => T.toSection b) y)) := by
      intro y hy
      have hdens_pou_sq_le := density_pou_sq_le_section
        (I := I) (M := M) g α h_supp_ne hy
      have hdens_nn : 0 ≤ chartDensity g α
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) :=
        Real.sqrt_nonneg _
      have hρ_sq_nn :
          0 ≤ ((chartAtlasPOU I M α : M → ℝ)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2 :=
        sq_nonneg _
      have hnormSq_nn :
          0 ≤ ‖T.toSection
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ ^ 2 :=
        sq_nonneg _
      have h_pushed := section_normSq_apply_eq_pushedNormSq
        (I := I) (M := M) (r := r) (s := s) g T α hy
      have h_dens_pou_sq_nn : 0 ≤
          chartDensity g α
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
            ((chartAtlasPOU I M α : M → ℝ)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2 :=
        mul_nonneg hdens_nn hρ_sq_nn
      have h_ofReal_inner : ENNReal.ofReal
          (((chartAtlasPOU I M α : M → ℝ)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2 *
            ‖T.toSection
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ ^ 2) =
          ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
            ENNReal.ofReal
              (‖T.toSection
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ ^ 2) :=
        ENNReal.ofReal_mul hρ_sq_nn
      rw [h_ofReal_inner]
      have hkey :
          ENNReal.ofReal
              (chartDensity g α
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2)
            ≤ ENNReal.ofReal (Mα α + 1) *
              ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) := by
        have h_Mα1_nn : 0 ≤ Mα α + 1 := by have := hMα_nn α; linarith
        rw [← ENNReal.ofReal_mul hdens_nn,
            ← ENNReal.ofReal_mul h_Mα1_nn]
        exact ENNReal.ofReal_le_ofReal hdens_pou_sq_le
      have h_pushed_eq :
          ENNReal.ofReal
            (‖T.toSection
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ ^ 2) =
          ENNReal.ofReal
            (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
              (fun b : M => T.toSection b) y) := by
        rw [h_pushed]
      calc ENNReal.ofReal
              (chartDensity g α
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            (ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
              ENNReal.ofReal
                (‖T.toSection
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ ^ 2))
          = (ENNReal.ofReal
                (chartDensity g α
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
              ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2)) *
              ENNReal.ofReal
                (‖T.toSection
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ ^ 2) := by
            ring
        _ ≤ (ENNReal.ofReal (Mα α + 1) *
              ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2)) *
              ENNReal.ofReal
                (‖T.toSection
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ ^ 2) := by
            exact mul_le_mul_left hkey _
        _ = ENNReal.ofReal (Mα α + 1) *
              (ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
                ENNReal.ofReal
                  (‖T.toSection
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ ^ 2)) := by
            ring
        _ = ENNReal.ofReal (Mα α + 1) *
              (ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
                ENNReal.ofReal
                  (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                    (fun b : M => T.toSection b) y)) := by
            rw [h_pushed_eq]
    have hset_int_le :
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal
              (chartDensity g α
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2 *
                ‖T.toSection
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ ^ 2)
            ∂(volume : Measure EuclN)
          ≤ ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal (Mα α + 1) *
                (ENNReal.ofReal
                  (((chartAtlasPOU I M α : M → ℝ)
                      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
                  ENNReal.ofReal
                    (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                      (fun b : M => T.toSection b) y))
              ∂(volume : Measure EuclN) :=
      MeasureTheory.setLIntegral_mono_ae'
        (chartTargetEuclid_measurableSet (I := I) (M := M) α)
        (Filter.Eventually.of_forall hpt_bound)
    have hpull :
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal (Mα α + 1) *
            (ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
              ENNReal.ofReal
                (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                  (fun b : M => T.toSection b) y))
            ∂(volume : Measure EuclN)
          = ENNReal.ofReal (Mα α + 1) *
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                ENNReal.ofReal
                  (((chartAtlasPOU I M α : M → ℝ)
                      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
                  ENNReal.ofReal
                    (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                      (fun b : M => T.toSection b) y)
                ∂(volume : Measure EuclN) := by
      rw [MeasureTheory.lintegral_const_mul']
      exact ENNReal.ofReal_ne_top
    calc (euclideanHaarFactor E : ℝ≥0∞) *
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal
                  (chartDensity g α
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                ENNReal.ofReal
                  (((chartAtlasPOU I M α : M → ℝ)
                      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2 *
                    ‖T.toSection
                      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ ^ 2)
              ∂(volume : Measure EuclN)
        ≤ (euclideanHaarFactor E : ℝ≥0∞) *
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal (Mα α + 1) *
                (ENNReal.ofReal
                  (((chartAtlasPOU I M α : M → ℝ)
                      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
                  ENNReal.ofReal
                    (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                      (fun b : M => T.toSection b) y))
              ∂(volume : Measure EuclN) :=
        mul_le_mul_right hset_int_le _
      _ = (euclideanHaarFactor E : ℝ≥0∞) *
            (ENNReal.ofReal (Mα α + 1) *
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                ENNReal.ofReal
                  (((chartAtlasPOU I M α : M → ℝ)
                      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
                  ENNReal.ofReal
                    (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                      (fun b : M => T.toSection b) y)
                ∂(volume : Measure EuclN)) := by rw [hpull]
      _ = ((euclideanHaarFactor E : ℝ≥0∞) * ENNReal.ofReal (Mα α + 1)) *
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
                ENNReal.ofReal
                  (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                    (fun b : M => T.toSection b) y)
              ∂(volume : Measure EuclN) := by ring
      _ = ENNReal.ofReal (cE * (Mα α + 1)) *
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
                ENNReal.ofReal
                  (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                    (fun b : M => T.toSection b) y)
              ∂(volume : Measure EuclN) := by
            congr 1
            rw [hcE_def]
            have hMα1_nn : 0 ≤ Mα α + 1 := by have := hMα_nn α; linarith
            rw [ENNReal.ofReal_mul (NNReal.coe_nonneg _)]
            congr 1
            rw [ENNReal.ofReal_coe_nnreal]
  set Sum_pou : Finset M → ℝ := fun s =>
    ∑ β ∈ s, (Mα β + 1) with hSum_pou_def
  set C_inner : ℝ := cE * Sum_pou Sfin with hC_inner_def
  have hC_inner_nn : 0 ≤ C_inner := by
    refine mul_nonneg hcE_nn ?_
    refine Finset.sum_nonneg ?_
    intro β _; have := hMα_nn β; linarith
  have hC_eq : C = (N : ℝ) * C_inner := by
    rw [hC_def, hN_def, hSfin_def, hC_inner_def, hSum_pou_def, hMα_def, hcE_def]
    rfl
  have hper_term_le : ∀ α ∈ Sfin,
      cE * (Mα α + 1) ≤ C_inner := by
    intro α hα_mem
    have h_term_le : (Mα α + 1) ≤ Sum_pou Sfin := by
      have hsum_nn : ∀ β ∈ Sfin, 0 ≤ Mα β + 1 := by
        intro β _; have := hMα_nn β; linarith
      exact Finset.single_le_sum (f := fun β => Mα β + 1) hsum_nn hα_mem
    rw [hC_inner_def]
    exact mul_le_mul_of_nonneg_left h_term_le hcE_nn
  have hper_alpha_C_inner : ∀ α ∈ Sfin,
      ENNReal.ofReal (cE * (Mα α + 1)) *
          ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
              ENNReal.ofReal
                (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                  (fun b : M => T.toSection b) y)
            ∂(volume : Measure EuclN) ≤
        ENNReal.ofReal C_inner *
          ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
              ENNReal.ofReal
                (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                  (fun b : M => T.toSection b) y)
            ∂(volume : Measure EuclN) := by
    intro α hα_mem
    refine mul_le_mul_left ?_ _
    exact ENNReal.ofReal_le_ofReal (hper_term_le α hα_mem)
  have hsum_per_alpha_le :
      ∑ α ∈ Sfin,
          ∫⁻ x, ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ) x) ^ 2 *
                  ‖T.toSection x‖ ^ 2)
                ∂(riemannianVolumeMeasure (I := I) (M := M) g)
        ≤ ∑ α ∈ Sfin,
            ENNReal.ofReal C_inner *
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                ENNReal.ofReal
                    (((chartAtlasPOU I M α : M → ℝ)
                        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
                  ENNReal.ofReal
                    (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                      (fun b : M => T.toSection b) y)
                ∂(volume : Measure EuclN) := by
    refine Finset.sum_le_sum ?_
    intro α hα_mem
    exact le_trans (h_per_alpha α hα_mem) (hper_alpha_C_inner α hα_mem)
  have hpull_sum :
      ∑ α ∈ Sfin,
          ENNReal.ofReal C_inner *
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal
                  (((chartAtlasPOU I M α : M → ℝ)
                      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
                ENNReal.ofReal
                  (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                    (fun b : M => T.toSection b) y)
              ∂(volume : Measure EuclN)
        = ENNReal.ofReal C_inner *
            ∑ α ∈ Sfin,
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                ENNReal.ofReal
                    (((chartAtlasPOU I M α : M → ℝ)
                        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
                  ENNReal.ofReal
                    (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                      (fun b : M => T.toSection b) y)
                ∂(volume : Measure EuclN) := by
    rw [← Finset.mul_sum]
  have h_combined :
      ENNReal.ofReal (N : ℝ) *
        ∑ α ∈ Sfin,
          ∫⁻ x, ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ) x) ^ 2 * ‖T.toSection x‖ ^ 2)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g) ≤
        ENNReal.ofReal (N : ℝ) *
          (ENNReal.ofReal C_inner *
            chartSobolevSectionNormPou (I := I) (M := M) g r s T) := by
    refine mul_le_mul_right ?_ _
    rw [chartSobolevSectionNormPou_def]
    calc
      ∑ α ∈ Sfin,
          ∫⁻ x, ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ) x) ^ 2 * ‖T.toSection x‖ ^ 2)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g)
        ≤ ∑ α ∈ Sfin,
            ENNReal.ofReal C_inner *
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                ENNReal.ofReal
                    (((chartAtlasPOU I M α : M → ℝ)
                        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
                  ENNReal.ofReal
                    (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                      (fun b : M => T.toSection b) y)
                ∂(volume : Measure EuclN) := hsum_per_alpha_le
      _ = ENNReal.ofReal C_inner *
            ∑ α ∈ Sfin,
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                ENNReal.ofReal
                    (((chartAtlasPOU I M α : M → ℝ)
                        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
                  ENNReal.ofReal
                    (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                      (fun b : M => T.toSection b) y)
                ∂(volume : Measure EuclN) := hpull_sum
  have h_NC_eq : ENNReal.ofReal (N : ℝ) * ENNReal.ofReal C_inner =
      ENNReal.ofReal C := by
    rw [← ENNReal.ofReal_mul hN_nn, ← hC_eq]
  have h_final_eq :
      ENNReal.ofReal (N : ℝ) *
        (ENNReal.ofReal C_inner *
          chartSobolevSectionNormPou (I := I) (M := M) g r s T) =
        ENNReal.ofReal C *
          chartSobolevSectionNormPou (I := I) (M := M) g r s T := by
    rw [← mul_assoc, h_NC_eq]
  exact le_trans h_int_le' (le_trans h_combined (le_of_eq h_final_eq))

end Connection
end Integral
end DifferentialGeometry

end
