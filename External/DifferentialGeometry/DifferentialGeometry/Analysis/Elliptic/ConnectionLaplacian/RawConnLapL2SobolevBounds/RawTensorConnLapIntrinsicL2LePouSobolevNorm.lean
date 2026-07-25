import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RawConnLapPointwiseFiberBounds.RawConnLapPointwisePouSobolevSummandBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartReprDerivativeBounds.CompDataIJChartOnMMeasurable
import DifferentialGeometry.Analysis.Sobolev.Tensor.PouWeightedNorm
import DifferentialGeometry.Analysis.Integration.Measure.MeasureBridge
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.ChartGeometry.GoodSetMeasure
import DifferentialGeometry.Analysis.Integration.Measure.Rellich


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

open Bundle Manifold Set IsManifold ContinuousLinearMap Filter MeasureTheory
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
open DifferentialGeometry.Analysis.Sobolev.Tensor
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" =>
  EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

private noncomputable def tensorPouSobolevNormSqSum_one
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (T : SmoothCcTensor g r s) : ℝ≥0∞ :=
  ∑' α : M,
    ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)),
      ∑ j ∈ Finset.range 3,
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal
            (((chartAtlasPOU I M α : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
              ‖iteratedFDeriv ℝ j
                  (tensorChartComponentRaw (I := I) (M := M) g r s T α IJ.1 IJ.2
                    ∘ (extChartAt I α).symm)
                  ((toEuclidean (E := E)).symm y)‖ ^ 2)
          ∂(volume : Measure EuclN)

omit [NeZero (Module.finrank ℝ E)] in
private lemma tensorPouSobolevNorm_one_sq_eq
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (T : SmoothCcTensor g r s) :
    (tensorPouSobolevNorm (I := I) (M := M) g 1 T) ^ 2 =
      tensorPouSobolevNormSqSum_one (I := I) (M := M) g T := by
  classical
  rw [tensorPouSobolevNorm_eq]
  set BigSum : ℝ≥0∞ :=
    ∑' α : M,
      ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
          (Fin s → Fin (Module.finrank ℝ E)),
        ∑ j ∈ Finset.range (2 * 1 + 1),
          ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                ‖iteratedFDeriv ℝ j
                    (tensorChartComponentRaw (I := I) (M := M) g r s T α IJ.1 IJ.2
                      ∘ (extChartAt I α).symm)
                    ((toEuclidean (E := E)).symm y)‖ ^ 2)
            ∂(volume : Measure EuclN) with hBigSum_def
  have hBigSum_eq : BigSum = tensorPouSobolevNormSqSum_one (I := I) (M := M) g T := by
    rw [hBigSum_def]; simp only [tensorPouSobolevNormSqSum_one]
  have h_pow : (BigSum ^ (1 / 2 : ℝ)) ^ 2 = BigSum := by
    rw [← ENNReal.rpow_natCast (BigSum ^ (1 / 2 : ℝ)) 2, ← ENNReal.rpow_mul]
    have h1 : (1 / 2 : ℝ) * (2 : ℕ) = 1 := by push_cast; ring
    rw [h1]; exact ENNReal.rpow_one BigSum
  rw [h_pow, hBigSum_eq]

omit [NeZero (Module.finrank ℝ E)] in
private lemma tensorPouSobolevNormSqSum_one_eq_finsetSum
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (T : SmoothCcTensor g r s) :
    tensorPouSobolevNormSqSum_one (I := I) (M := M) g T =
      ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
          ∑ j ∈ Finset.range 3,
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                  ‖iteratedFDeriv ℝ j
                      (tensorChartComponentRaw (I := I) (M := M) g r s T α IJ.1 IJ.2
                        ∘ (extChartAt I α).symm)
                      ((toEuclidean (E := E)).symm y)‖ ^ 2)
              ∂(volume : Measure EuclN) := by
  classical
  unfold tensorPouSobolevNormSqSum_one
  rw [tsum_eq_sum (s := chartAtlasPOU_finset (I := I) (M := M))]
  intro α hα
  have hρ_zero : ∀ x : M,
      (chartAtlasPOU I M α : M → ℝ) x = 0 := fun x =>
    chartAtlasPOU_weight_zero_of_notMem (I := I) (M := M) hα x
  refine Finset.sum_eq_zero (fun IJ _ => ?_)
  refine Finset.sum_eq_zero (fun j _ => ?_)
  have h_integrand_zero : ∀ y : EuclN,
      ENNReal.ofReal
        (((chartAtlasPOU I M α : M → ℝ)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
          ‖iteratedFDeriv ℝ j
              (tensorChartComponentRaw (I := I) (M := M) g r s T α IJ.1 IJ.2
                ∘ (extChartAt I α).symm)
              ((toEuclidean (E := E)).symm y)‖ ^ 2) = 0 := by
    intro y; rw [hρ_zero]; simp
  have heq : (fun y : EuclN =>
      ENNReal.ofReal
        (((chartAtlasPOU I M α : M → ℝ)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
          ‖iteratedFDeriv ℝ j
              (tensorChartComponentRaw (I := I) (M := M) g r s T α IJ.1 IJ.2
                ∘ (extChartAt I α).symm)
              ((toEuclidean (E := E)).symm y)‖ ^ 2)) = (fun _ => 0) := by
    funext y; exact h_integrand_zero y
  rw [heq]; simp

variable (I M) in
private noncomputable def perChartDensityCeil
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M) : ℝ :=
  open Classical in
  if h : (tsupport
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)).Nonempty then
    (exists_sup_chartDensity_on_pou_tsupport_image (I := I) (M := M) g α h).choose
  else 0

omit [NeZero (Module.finrank ℝ E)] in
private lemma perChartDensityCeil_nonneg
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M) :
    0 ≤ perChartDensityCeil (I := I) (M := M) g α := by
  classical
  unfold perChartDensityCeil
  by_cases h : (tsupport
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)).Nonempty
  · rw [dif_pos h]
    exact le_of_lt
      (exists_sup_chartDensity_on_pou_tsupport_image (I := I) (M := M) g α h).choose_spec.1
  · rw [dif_neg h]

omit [NeZero (Module.finrank ℝ E)] in
private lemma perChartDensityCeil_bound
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    (h_supp_ne :
      (tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)).Nonempty)
    {y : E}
    (hy_image :
      y ∈ (extChartAt I α) '' (tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ))) :
    chartDensity g α ((extChartAt I α).symm y) ≤
      perChartDensityCeil (I := I) (M := M) g α := by
  classical
  unfold perChartDensityCeil
  rw [dif_pos h_supp_ne]
  exact (exists_sup_chartDensity_on_pou_tsupport_image
    (I := I) (M := M) g α h_supp_ne).choose_spec.2 y hy_image

private noncomputable def compNormSqOnM
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T₀ : SmoothCcTensor g r s)
    (α : M) (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (j : ℕ) : M → ℝ :=
  fun b => ‖iteratedFDeriv ℝ j
    ((tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)
      ∘ (extChartAt I α).symm)
    (extChartAtExt (I := I) α b)‖ ^ 2

omit [NeZero (Module.finrank ℝ E)] in
private lemma compNormSqOnM_measurable
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T₀ : SmoothCcTensor g r s)
    (α : M) (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (j : ℕ) :
    Measurable (compNormSqOnM (I := I) (M := M) g r s T₀ α Idx Jdx j) :=
  measurable_tensorChartComponentRaw_iteratedFDeriv_normSq (I := I) (M := M) g r s T₀ α Idx Jdx j

omit [NeZero (Module.finrank ℝ E)] in
private lemma compNormSqOnM_nonneg
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T₀ : SmoothCcTensor g r s)
    (α : M) (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (j : ℕ) (b : M) :
    0 ≤ compNormSqOnM (I := I) (M := M) g r s T₀ α Idx Jdx j b :=
  sq_nonneg _

omit [NeZero (Module.finrank ℝ E)] in
private lemma compNormSqOnM_eq_of_mem_chartSrc
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T₀ : SmoothCcTensor g r s)
    (α : M) (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (j : ℕ) {b : M} (hb : b ∈ (chartAt H α).source) :
    compNormSqOnM (I := I) (M := M) g r s T₀ α Idx Jdx j b =
      ‖iteratedFDeriv ℝ j
          ((tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)
            ∘ (extChartAt I α).symm)
          ((extChartAt I α) b)‖ ^ 2 := by
  unfold compNormSqOnM
  rw [extChartAtExt_apply_of_mem (I := I) (α := α) hb]

omit [NeZero (Module.finrank ℝ E)] in
private lemma per_alpha_measurable_lintegral_le
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (CB : ℝ) (hCB_nn : 0 ≤ CB) (T₀ : SmoothCcTensor g r s) :
    ∫⁻ b, ENNReal.ofReal
        ((chartAtlasPOU I M α : M → ℝ) b * CB *
          ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              ∑ j ∈ Finset.range 3,
                compNormSqOnM (I := I) (M := M) g r s T₀ α Idx Jdx j b)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) ≤
      ENNReal.ofReal (CB * (euclideanHaarFactor E : ℝ) *
        (perChartDensityCeil (I := I) (M := M) g α + 1)) *
        ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
          ∑ j ∈ Finset.range 3,
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                  ‖iteratedFDeriv ℝ j
                      (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α
                          IJ.1 IJ.2
                        ∘ (extChartAt I α).symm)
                      ((toEuclidean (E := E)).symm y)‖ ^ 2)
              ∂(volume : Measure EuclN) := by
  classical
  set n := Module.finrank ℝ E with hn_def
  set Msup : ℝ := perChartDensityCeil (I := I) (M := M) g α + 1 with hMsup_def
  have hMsup_nn : 0 ≤ Msup := by
    rw [hMsup_def]; linarith [perChartDensityCeil_nonneg (I := I) (M := M) g α]
  set cE : ℝ := (euclideanHaarFactor E : ℝ) with hcE_def
  have hcE_nn : 0 ≤ cE := NNReal.coe_nonneg _
  set rho : M → ℝ := fun b => (chartAtlasPOU I M α : M → ℝ) b with hrho_def
  have hrho_nn : ∀ b, 0 ≤ rho b := fun b => (chartAtlasPOU I M).nonneg α b
  have hrho_meas : Measurable rho :=
    (chartAtlasPOU I M α).contMDiff.continuous.measurable
  have hsub : tsupport rho ⊆ (chartAt H α).source :=
    chartAtlasPOU_isSubordinate (I := I) (M := M) α
  set BigSum_M : M → ℝ := fun b =>
    ∑ Idx : Fin r → Fin n, ∑ Jdx : Fin s → Fin n, ∑ j ∈ Finset.range 3,
      compNormSqOnM (I := I) (M := M) g r s T₀ α Idx Jdx j b with hBigSum_M_def
  have hBigSum_M_meas : Measurable BigSum_M := by
    rw [hBigSum_M_def]
    refine Finset.measurable_sum _ (fun _ _ => ?_)
    refine Finset.measurable_sum _ (fun _ _ => ?_)
    refine Finset.measurable_sum _ (fun _ _ => ?_)
    exact compNormSqOnM_measurable (I := I) (M := M) g r s T₀ α _ _ _
  have hBigSum_M_nn : ∀ b, 0 ≤ BigSum_M b := by
    intro b; rw [hBigSum_M_def]
    refine Finset.sum_nonneg (fun _ _ => ?_)
    refine Finset.sum_nonneg (fun _ _ => ?_)
    refine Finset.sum_nonneg (fun _ _ => ?_)
    exact compNormSqOnM_nonneg (I := I) (M := M) g r s T₀ α _ _ _ _
  have h_distrib_pt : ∀ b : M,
      ENNReal.ofReal (rho b * CB * BigSum_M b) =
        ENNReal.ofReal CB *
          ∑ Idx : Fin r → Fin n, ∑ Jdx : Fin s → Fin n, ∑ j ∈ Finset.range 3,
            ENNReal.ofReal
              (rho b * compNormSqOnM (I := I) (M := M) g r s T₀ α Idx Jdx j b) := by
    intro b
    have h_factor : rho b * CB * BigSum_M b = CB * (rho b * BigSum_M b) := by ring
    rw [h_factor, ENNReal.ofReal_mul hCB_nn]
    congr 1
    have h_mul_distrib : rho b * BigSum_M b =
        ∑ Idx : Fin r → Fin n, ∑ Jdx : Fin s → Fin n, ∑ j ∈ Finset.range 3,
          rho b * compNormSqOnM (I := I) (M := M) g r s T₀ α Idx Jdx j b := by
      rw [hBigSum_M_def, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun Idx _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun Jdx _ => ?_)
      rw [Finset.mul_sum]
    rw [h_mul_distrib, ENNReal.ofReal_sum_of_nonneg]
    · refine Finset.sum_congr rfl (fun Idx _ => ?_)
      rw [ENNReal.ofReal_sum_of_nonneg]
      · refine Finset.sum_congr rfl (fun Jdx _ => ?_)
        rw [ENNReal.ofReal_sum_of_nonneg]
        intro j _; exact mul_nonneg (hrho_nn b)
          (compNormSqOnM_nonneg (I := I) (M := M) g r s T₀ α _ _ _ _)
      · intro Jdx _
        refine Finset.sum_nonneg (fun j _ => ?_)
        exact mul_nonneg (hrho_nn b) (compNormSqOnM_nonneg (I := I) (M := M) g r s T₀ α _ _ _ _)
    · intro Idx _
      refine Finset.sum_nonneg (fun Jdx _ => ?_)
      refine Finset.sum_nonneg (fun j _ => ?_)
      exact mul_nonneg (hrho_nn b) (compNormSqOnM_nonneg (I := I) (M := M) g r s T₀ α _ _ _ _)
  have h_integrand_eq : (fun b : M => ENNReal.ofReal (rho b * CB * BigSum_M b)) =
      fun b : M =>
        ENNReal.ofReal CB *
          ∑ Idx : Fin r → Fin n, ∑ Jdx : Fin s → Fin n, ∑ j ∈ Finset.range 3,
            ENNReal.ofReal
              (rho b * compNormSqOnM (I := I) (M := M) g r s T₀ α Idx Jdx j b) := by
    funext b; exact h_distrib_pt b
  set hμ_g : Measure M := riemannianVolumeMeasure (I := I) (M := M) g
  have hSum_meas : ∀ Idx Jdx j,
      Measurable (fun b : M =>
        ENNReal.ofReal (rho b * compNormSqOnM (I := I) (M := M) g r s T₀ α Idx Jdx j b)) := by
    intro Idx Jdx j
    exact ENNReal.measurable_ofReal.comp
      (hrho_meas.mul (compNormSqOnM_measurable (I := I) (M := M) g r s T₀ α Idx Jdx j))
  have h_int_rw :
      ∫⁻ b, ENNReal.ofReal (rho b * CB * BigSum_M b) ∂hμ_g =
        ENNReal.ofReal CB *
          ∑ Idx : Fin r → Fin n, ∑ Jdx : Fin s → Fin n, ∑ j ∈ Finset.range 3,
            ∫⁻ b, ENNReal.ofReal
                (rho b * compNormSqOnM (I := I) (M := M) g r s T₀ α Idx Jdx j b) ∂hμ_g := by
    rw [h_integrand_eq]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    congr 1
    rw [lintegral_finset_sum _ (fun Idx _ =>
      Finset.measurable_sum _ (fun Jdx _ =>
        Finset.measurable_sum _ (fun j _ => hSum_meas Idx Jdx j)))]
    refine Finset.sum_congr rfl (fun Idx _ => ?_)
    rw [lintegral_finset_sum _ (fun Jdx _ =>
      Finset.measurable_sum _ (fun j _ => hSum_meas Idx Jdx j))]
    refine Finset.sum_congr rfl (fun Jdx _ => ?_)
    exact lintegral_finset_sum _ (fun j _ => hSum_meas Idx Jdx j)
  change ∫⁻ b, ENNReal.ofReal (rho b * CB * BigSum_M b) ∂hμ_g ≤ _
  rw [h_int_rw]
  have hper_summand_le : ∀ Idx Jdx j,
      (∫⁻ b, ENNReal.ofReal
            (rho b * compNormSqOnM (I := I) (M := M) g r s T₀ α Idx Jdx j b) ∂hμ_g) ≤
        ENNReal.ofReal (cE * Msup) *
          ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                ‖iteratedFDeriv ℝ j
                    (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx
                      ∘ (extChartAt I α).symm)
                    ((toEuclidean (E := E)).symm y)‖ ^ 2)
            ∂(volume : Measure EuclN) := by
    intro Idx Jdx j
    set G : M → ℝ≥0∞ := fun b =>
      ENNReal.ofReal (rho b * compNormSqOnM (I := I) (M := M) g r s T₀ α Idx Jdx j b)
      with hG_def
    have hG_meas : Measurable G := hSum_meas Idx Jdx j
    have hG_zero_off : ∀ b, b ∉ (chartAt H α).source → G b = 0 := by
      intro b hb
      have hb_not_tsupp : b ∉ tsupport rho := fun h => hb (hsub h)
      have hrho_b : rho b = 0 := image_eq_zero_of_notMem_tsupport hb_not_tsupp
      change ENNReal.ofReal (rho b * _) = 0
      rw [hrho_b]; simp
    have hrvm_eq : riemannianVolumeMeasure (I := I) (M := M) g =
        riemannianMeasure (I := I) g (chartAtlasPOU I M) :=
      riemannianVolumeMeasure_def (I := I) (M := M) g
    have hpush :
        ∫⁻ b, G b ∂hμ_g = ∫⁻ b, G b ∂(chartLocalMeasure (I := I) g α) := by
      change ∫⁻ b, G b ∂(riemannianVolumeMeasure (I := I) (M := M) g) = _
      rw [hrvm_eq]
      exact riemannianMeasure_lintegral_eq_chartLocalMeasure_of_supportIn
        (I := I) (M := M) g α hG_meas hG_zero_off
    have hbridge_eucl :=
      chartLocalMeasure_lintegral_via_chartTargetEuclid
        (I := I) (M := M) g α (F := G) hG_meas
    have h_on_target :
        ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal
              (chartDensity g α
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            G ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) =
          ENNReal.ofReal
              (chartDensity g α
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                ‖iteratedFDeriv ℝ j
                    (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx
                      ∘ (extChartAt I α).symm)
                    ((toEuclidean (E := E)).symm y)‖ ^ 2) := by
      intro y hy_target
      set b' : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb'_def
      have hb'_src : b' ∈ (chartAt H α).source := by
        rw [hb'_def]
        exact symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) α hy_target
      have hb'_extExt : extChartAtExt (I := I) α b' = (extChartAt I α) b' :=
        extChartAtExt_apply_of_mem (I := I) (α := α) hb'_src
      have h_ext_b' : (extChartAt I α) b' = (toEuclidean (E := E)).symm y := by
        rw [hb'_def]
        have h_in_target : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
          rw [chartTargetEuclid_eq_preimage_symm] at hy_target
          exact hy_target
        exact (extChartAt I α).right_inv h_in_target
      have hG_b' :
          G b' = ENNReal.ofReal
            (rho b' *
              ‖iteratedFDeriv ℝ j
                  ((tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx) ∘
                    (extChartAt I α).symm)
                  ((toEuclidean (E := E)).symm y)‖ ^ 2) := by
        change ENNReal.ofReal (rho b' *
            compNormSqOnM (I := I) (M := M) g r s T₀ α Idx Jdx j b') = _
        congr 1
        unfold compNormSqOnM
        rw [hb'_extExt, h_ext_b']
      rw [hG_b']
    have hpush_eucl :
        ∫⁻ b, G b ∂hμ_g =
          (euclideanHaarFactor E : ℝ≥0∞) *
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal
                  (chartDensity g α
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                ENNReal.ofReal
                  (((chartAtlasPOU I M α : M → ℝ)
                      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                    ‖iteratedFDeriv ℝ j
                        (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx
                          ∘ (extChartAt I α).symm)
                        ((toEuclidean (E := E)).symm y)‖ ^ 2)
              ∂(volume : Measure EuclN) := by
      rw [hpush, hbridge_eucl]
      congr 1
      exact setLIntegral_congr_fun
        (chartTargetEuclid_measurableSet (I := I) (M := M) α) h_on_target
    have h_density_bound :
        ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal
              (chartDensity g α
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                ‖iteratedFDeriv ℝ j
                    (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx
                      ∘ (extChartAt I α).symm)
                    ((toEuclidean (E := E)).symm y)‖ ^ 2) ≤
          ENNReal.ofReal Msup *
            ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                ‖iteratedFDeriv ℝ j
                    (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx
                      ∘ (extChartAt I α).symm)
                    ((toEuclidean (E := E)).symm y)‖ ^ 2) := by
      intro y hy_target
      set ρy : ℝ :=
        (chartAtlasPOU I M α : M → ℝ)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) with hρy_def
      by_cases hρ0 : ρy = 0
      · have h_zero :
            ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                ‖iteratedFDeriv ℝ j
                    (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx
                      ∘ (extChartAt I α).symm)
                    ((toEuclidean (E := E)).symm y)‖ ^ 2) = 0 := by
          rw [← hρy_def, hρ0]; simp
        rw [h_zero]; simp
      · set b' : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb'_def
        have hρ_pos : 0 < ρy :=
          lt_of_le_of_ne ((chartAtlasPOU I M).nonneg α _) (Ne.symm hρ0)
        have hb'_supp_fn : b' ∈ Function.support rho := by
          change (chartAtlasPOU I M α : M → ℝ) b' ≠ 0
          change (chartAtlasPOU I M α : M → ℝ) ((extChartAt I α).symm
              ((toEuclidean (E := E)).symm y)) ≠ 0
          change ρy ≠ 0
          exact hρ0
        have hb'_tsupp : b' ∈ tsupport rho := subset_tsupport _ hb'_supp_fn
        have h_tsupp_ne : (tsupport rho).Nonempty := ⟨b', hb'_tsupp⟩
        have h_tsupp_ne' : (tsupport
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)).Nonempty := h_tsupp_ne
        have h_ext_b' : (extChartAt I α) b' = (toEuclidean (E := E)).symm y := by
          rw [hb'_def]
          have h_in_target : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
            rw [chartTargetEuclid_eq_preimage_symm] at hy_target
            exact hy_target
          exact (extChartAt I α).right_inv h_in_target
        have h_eucl_in_image :
            (toEuclidean (E := E)).symm y ∈
              (extChartAt I α) '' (tsupport rho) :=
          ⟨b', hb'_tsupp, h_ext_b'⟩
        have h_density_le :
            chartDensity g α ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) ≤
              perChartDensityCeil (I := I) (M := M) g α :=
          perChartDensityCeil_bound (I := I) (M := M) g α h_tsupp_ne'
            (y := (toEuclidean (E := E)).symm y) h_eucl_in_image
        have h_density_le_Msup :
            chartDensity g α ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) ≤
              Msup := by rw [hMsup_def]; linarith
        have h_density_le_E :
            ENNReal.ofReal
                (chartDensity g α
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ≤
              ENNReal.ofReal Msup :=
          ENNReal.ofReal_le_ofReal h_density_le_Msup
        exact mul_le_mul_of_nonneg_right h_density_le_E (zero_le _)
    have h_int_density_bound :
        (∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal
                (chartDensity g α
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
              ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                  ‖iteratedFDeriv ℝ j
                      (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx
                        ∘ (extChartAt I α).symm)
                      ((toEuclidean (E := E)).symm y)‖ ^ 2)
            ∂(volume : Measure EuclN)) ≤
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal Msup *
            ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                ‖iteratedFDeriv ℝ j
                    (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx
                      ∘ (extChartAt I α).symm)
                    ((toEuclidean (E := E)).symm y)‖ ^ 2)
          ∂(volume : Measure EuclN) :=
      setLIntegral_mono_ae'
        (chartTargetEuclid_measurableSet (I := I) (M := M) α)
        (Filter.Eventually.of_forall h_density_bound)
    have h_pull_Msup :
        (∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal Msup *
              ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                  ‖iteratedFDeriv ℝ j
                      (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx
                        ∘ (extChartAt I α).symm)
                      ((toEuclidean (E := E)).symm y)‖ ^ 2)
            ∂(volume : Measure EuclN)) =
        ENNReal.ofReal Msup *
          ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                ‖iteratedFDeriv ℝ j
                    (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx
                      ∘ (extChartAt I α).symm)
                    ((toEuclidean (E := E)).symm y)‖ ^ 2)
            ∂(volume : Measure EuclN) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    rw [hpush_eucl]
    refine le_trans (mul_le_mul_right h_int_density_bound _) ?_
    rw [h_pull_Msup]
    rw [← mul_assoc]
    refine mul_le_mul_left ?_ _
    have h_cE_eq : (euclideanHaarFactor E : ℝ≥0∞) = ENNReal.ofReal cE := by
      rw [hcE_def, ENNReal.ofReal_coe_nnreal]
    rw [h_cE_eq, ← ENNReal.ofReal_mul hcE_nn]
  have h_step :
      ∑ Idx : Fin r → Fin n, ∑ Jdx : Fin s → Fin n, ∑ j ∈ Finset.range 3,
          ∫⁻ b, ENNReal.ofReal
              (rho b * compNormSqOnM (I := I) (M := M) g r s T₀ α Idx Jdx j b) ∂hμ_g ≤
        ∑ Idx : Fin r → Fin n, ∑ Jdx : Fin s → Fin n, ∑ j ∈ Finset.range 3,
          ENNReal.ofReal (cE * Msup) *
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                  ‖iteratedFDeriv ℝ j
                      (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx
                        ∘ (extChartAt I α).symm)
                      ((toEuclidean (E := E)).symm y)‖ ^ 2)
              ∂(volume : Measure EuclN) := by
    refine Finset.sum_le_sum (fun Idx _ => ?_)
    refine Finset.sum_le_sum (fun Jdx _ => ?_)
    refine Finset.sum_le_sum (fun j _ => ?_)
    exact hper_summand_le Idx Jdx j
  refine le_trans (mul_le_mul_right h_step _) ?_
  have h_pull :
      ∑ Idx : Fin r → Fin n, ∑ Jdx : Fin s → Fin n, ∑ j ∈ Finset.range 3,
        ENNReal.ofReal (cE * Msup) *
          ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                ‖iteratedFDeriv ℝ j
                    (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx
                      ∘ (extChartAt I α).symm)
                    ((toEuclidean (E := E)).symm y)‖ ^ 2)
            ∂(volume : Measure EuclN) =
      ENNReal.ofReal (cE * Msup) *
        ∑ Idx : Fin r → Fin n, ∑ Jdx : Fin s → Fin n, ∑ j ∈ Finset.range 3,
          ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                ‖iteratedFDeriv ℝ j
                    (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx
                      ∘ (extChartAt I α).symm)
                    ((toEuclidean (E := E)).symm y)‖ ^ 2)
            ∂(volume : Measure EuclN) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun Idx _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun Jdx _ => ?_)
    rw [Finset.mul_sum]
  rw [h_pull]
  rw [← mul_assoc, ← ENNReal.ofReal_mul hCB_nn]
  have h_const_eq : CB * (cE * Msup) = CB * cE * Msup := by ring
  rw [h_const_eq]
  refine mul_le_mul_right ?_ _
  rw [← Finset.sum_product']
  exact le_refl _

theorem rawTensorConnLap_intrinsicL2_le_tensorPouSobolevNorm_sq
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀ (T₀ : SmoothCcTensor g r s),
        ∫⁻ b, ENNReal.ofReal
            (riemannianFiberNormSq (I := I) (M := M) g r s b
              (rawTensorConnLap (I := I) g r s
                (fun z : M => T₀.toSection z) b))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) ≤
        C * (tensorPouSobolevNorm (I := I) (M := M) g 1 T₀) ^ 2 := by
  classical
  set n := Module.finrank ℝ E with hn_def
  set S : Finset M := chartAtlasPOU_finset (I := I) (M := M) with hS_def
  have h_bridge_choose :
      ∀ α : M, ∃ CB : ℝ, 0 ≤ CB ∧
        ∀ T₀' : SmoothCcTensor g r s,
          ∀ {b : M},
            b ∈ tsupport (fun x : M => ((chartAtlasPOU I M α
                : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
              chartLeviCivitaGoodSet (I := I) α →
            riemannianFiberNormSq (I := I) (M := M) g r s b
                (rawTensorConnLap (I := I) g r s
                  (fun z : M => T₀'.toSection z) b) ≤
              CB *
                (∑ Idx : Fin r → Fin n,
                  ∑ Jdx : Fin s → Fin n,
                    ∑ j ∈ Finset.range 3,
                      ‖iteratedFDeriv ℝ j
                          (tensorChartComponentRaw (I := I) (M := M) g r s T₀' α Idx Jdx
                            ∘ (extChartAt I α).symm)
                          ((extChartAt I α) b)‖ ^ 2) := by
    intro α
    exact rawTensorConnLap_riemannianFiberNormSq_le_chartPouSobolevSummand_T0_uniform
      (I := I) (M := M) g r s α
  choose CB hCB_nn hCB_le using h_bridge_choose
  set CB_max : ℝ := if hSne : S.Nonempty then S.sup' hSne CB else 1 with hCB_max_def
  have hCB_max_nn : 0 ≤ CB_max := by
    rw [hCB_max_def]
    by_cases hSne : S.Nonempty
    · rw [dif_pos hSne]
      obtain ⟨α₀, hα₀⟩ := hSne
      exact le_trans (hCB_nn α₀) (Finset.le_sup' CB hα₀)
    · rw [dif_neg hSne]; linarith
  have hCB_le_max : ∀ α ∈ S, CB α ≤ CB_max := by
    intro α hα
    rw [hCB_max_def]
    have hSne : S.Nonempty := ⟨α, hα⟩
    rw [dif_pos hSne]
    exact Finset.le_sup' CB hα
  set D_per_alpha : M → ℝ := fun α =>
    CB_max * (euclideanHaarFactor E : ℝ) *
      (perChartDensityCeil (I := I) (M := M) g α + 1) with hD_per_alpha_def
  have hD_nn : ∀ α, 0 ≤ D_per_alpha α := by
    intro α
    rw [hD_per_alpha_def]
    refine mul_nonneg (mul_nonneg hCB_max_nn (NNReal.coe_nonneg _)) ?_
    linarith [perChartDensityCeil_nonneg (I := I) (M := M) g α]
  set D_max : ℝ := if hSne : S.Nonempty then S.sup' hSne D_per_alpha else 1 with hD_max_def
  have hD_max_nn : 0 ≤ D_max := by
    rw [hD_max_def]
    by_cases hSne : S.Nonempty
    · rw [dif_pos hSne]
      obtain ⟨α₀, hα₀⟩ := hSne
      exact le_trans (hD_nn α₀) (Finset.le_sup' D_per_alpha hα₀)
    · rw [dif_neg hSne]; linarith
  have hD_α_le_max : ∀ α ∈ S, D_per_alpha α ≤ D_max := by
    intro α hα
    rw [hD_max_def]
    have hSne : S.Nonempty := ⟨α, hα⟩
    rw [dif_pos hSne]
    exact Finset.le_sup' D_per_alpha hα
  refine ⟨ENNReal.ofReal D_max, ENNReal.ofReal_ne_top, ?_⟩
  intro T₀
  set F : M → ℝ := fun b =>
    riemannianFiberNormSq (I := I) (M := M) g r s b
      (rawTensorConnLap (I := I) g r s
        (fun z : M => T₀.toSection z) b) with hF_def
  have hF_nn : ∀ b, 0 ≤ F b := fun b =>
    riemannianFiberNormSq_nonneg (I := I) (M := M) g r s b _
  have hpou_sum : ∀ b : M,
      ∑ α ∈ S, (chartAtlasPOU I M α : M → ℝ) b = 1 := by
    intro b
    rw [hS_def]
    exact chartAtlasPOU_finset_sum_eq_one (I := I) (M := M) b
  have hpou_nn : ∀ α b, 0 ≤ (chartAtlasPOU I M α : M → ℝ) b := fun α b =>
    (chartAtlasPOU I M).nonneg α b
  set H_alpha : M → M → ℝ≥0∞ := fun α b =>
    ENNReal.ofReal
      ((chartAtlasPOU I M α : M → ℝ) b * CB_max *
        ∑ Idx : Fin r → Fin n,
          ∑ Jdx : Fin s → Fin n,
            ∑ j ∈ Finset.range 3,
              compNormSqOnM (I := I) (M := M) g r s T₀ α Idx Jdx j b)
    with hH_alpha_def
  have hH_alpha_meas : ∀ α, Measurable (H_alpha α) := by
    intro α
    rw [hH_alpha_def]
    refine ENNReal.measurable_ofReal.comp ?_
    have hp_meas : Measurable (fun b : M => (chartAtlasPOU I M α : M → ℝ) b) :=
      (chartAtlasPOU I M α).contMDiff.continuous.measurable
    refine (hp_meas.mul measurable_const).mul ?_
    refine Finset.measurable_sum _ (fun _ _ => ?_)
    refine Finset.measurable_sum _ (fun _ _ => ?_)
    refine Finset.measurable_sum _ (fun _ _ => ?_)
    exact compNormSqOnM_measurable (I := I) (M := M) g r s T₀ α _ _ _
  have h_pointwise_M : ∀ b : M,
      ENNReal.ofReal (F b) ≤ ∑ α ∈ S, H_alpha α b := by
    intro b
    have h_per_α : ∀ α : M, α ∈ S →
        (chartAtlasPOU I M α : M → ℝ) b * F b ≤
          (chartAtlasPOU I M α : M → ℝ) b * CB_max *
            ∑ Idx : Fin r → Fin n, ∑ Jdx : Fin s → Fin n, ∑ j ∈ Finset.range 3,
              compNormSqOnM (I := I) (M := M) g r s T₀ α Idx Jdx j b := by
      intro α hα_S
      by_cases hb_supp : b ∈ tsupport
          (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)
      · have hb_chartSrc : b ∈ (chartAt H α).source :=
          (chartAtlasPOU_isSubordinate (I := I) (M := M) α) hb_supp
        have hb_extSrc : b ∈ (extChartAt I α).source := by
          rw [extChartAt_source_eq_chartAt_source]; exact hb_chartSrc
        have hgood :
            chartLeviCivitaGoodSet (I := I) α = (extChartAt I α).source :=
          chartLeviCivitaGoodSet_eq_extChartAt_source (I := I) α
        have hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α := by
          rw [hgood]; exact hb_extSrc
        have hb_inter : b ∈ tsupport
              (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
            chartLeviCivitaGoodSet (I := I) α := ⟨hb_supp, hb_good⟩
        have hF_bd : F b ≤ CB α *
            (∑ Idx : Fin r → Fin n, ∑ Jdx : Fin s → Fin n, ∑ j ∈ Finset.range 3,
              ‖iteratedFDeriv ℝ j
                  (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx
                    ∘ (extChartAt I α).symm)
                  ((extChartAt I α) b)‖ ^ 2) := hCB_le α T₀ hb_inter
        have h_sum_align :
            (∑ Idx : Fin r → Fin n, ∑ Jdx : Fin s → Fin n, ∑ j ∈ Finset.range 3,
              ‖iteratedFDeriv ℝ j
                  (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx
                    ∘ (extChartAt I α).symm)
                  ((extChartAt I α) b)‖ ^ 2) =
            ∑ Idx : Fin r → Fin n, ∑ Jdx : Fin s → Fin n, ∑ j ∈ Finset.range 3,
              compNormSqOnM (I := I) (M := M) g r s T₀ α Idx Jdx j b := by
          refine Finset.sum_congr rfl (fun _ _ => ?_)
          refine Finset.sum_congr rfl (fun _ _ => ?_)
          refine Finset.sum_congr rfl (fun _ _ => ?_)
          rw [compNormSqOnM_eq_of_mem_chartSrc (I := I) (M := M)
              g r s T₀ α _ _ _ hb_chartSrc]
        rw [h_sum_align] at hF_bd
        have h_sum_nn :
            0 ≤ ∑ Idx : Fin r → Fin n, ∑ Jdx : Fin s → Fin n, ∑ j ∈ Finset.range 3,
              compNormSqOnM (I := I) (M := M) g r s T₀ α Idx Jdx j b := by
          refine Finset.sum_nonneg (fun _ _ => ?_)
          refine Finset.sum_nonneg (fun _ _ => ?_)
          refine Finset.sum_nonneg (fun _ _ => ?_)
          exact compNormSqOnM_nonneg (I := I) (M := M) g r s T₀ α _ _ _ _
        have hF_bd' : F b ≤ CB_max *
            (∑ Idx : Fin r → Fin n, ∑ Jdx : Fin s → Fin n, ∑ j ∈ Finset.range 3,
              compNormSqOnM (I := I) (M := M) g r s T₀ α Idx Jdx j b) :=
          le_trans hF_bd (mul_le_mul_of_nonneg_right (hCB_le_max α hα_S) h_sum_nn)
        have h_mul := mul_le_mul_of_nonneg_left hF_bd' (hpou_nn α b)
        calc (chartAtlasPOU I M α : M → ℝ) b * F b
            ≤ (chartAtlasPOU I M α : M → ℝ) b * (CB_max *
                ∑ Idx : Fin r → Fin n, ∑ Jdx : Fin s → Fin n, ∑ j ∈ Finset.range 3,
                  compNormSqOnM (I := I) (M := M) g r s T₀ α Idx Jdx j b) := h_mul
          _ = (chartAtlasPOU I M α : M → ℝ) b * CB_max *
                ∑ Idx : Fin r → Fin n, ∑ Jdx : Fin s → Fin n, ∑ j ∈ Finset.range 3,
                  compNormSqOnM (I := I) (M := M) g r s T₀ α Idx Jdx j b := by ring
      · have hp0 : (chartAtlasPOU I M α : M → ℝ) b = 0 :=
          image_eq_zero_of_notMem_tsupport hb_supp
        rw [hp0]
        ring_nf
        have h_sum_nn :
            0 ≤ ∑ Idx : Fin r → Fin n, ∑ Jdx : Fin s → Fin n, ∑ j ∈ Finset.range 3,
              compNormSqOnM (I := I) (M := M) g r s T₀ α Idx Jdx j b := by
          refine Finset.sum_nonneg (fun _ _ => ?_)
          refine Finset.sum_nonneg (fun _ _ => ?_)
          refine Finset.sum_nonneg (fun _ _ => ?_)
          exact compNormSqOnM_nonneg (I := I) (M := M) g r s T₀ α _ _ _ _
        exact le_refl _
    have h_pou_F_eq : F b = ∑ α ∈ S, (chartAtlasPOU I M α : M → ℝ) b * F b := by
      conv_lhs => rw [show F b = 1 * F b from (one_mul _).symm,
                       ← hpou_sum b, Finset.sum_mul]
    have h_pt_real : F b ≤
        ∑ α ∈ S, (chartAtlasPOU I M α : M → ℝ) b * CB_max *
          ∑ Idx : Fin r → Fin n, ∑ Jdx : Fin s → Fin n, ∑ j ∈ Finset.range 3,
            compNormSqOnM (I := I) (M := M) g r s T₀ α Idx Jdx j b := by
      rw [h_pou_F_eq]
      exact Finset.sum_le_sum (fun α hα => h_per_α α hα)
    have h_summand_nn : ∀ α ∈ S,
        0 ≤ (chartAtlasPOU I M α : M → ℝ) b * CB_max *
            ∑ Idx : Fin r → Fin n, ∑ Jdx : Fin s → Fin n, ∑ j ∈ Finset.range 3,
              compNormSqOnM (I := I) (M := M) g r s T₀ α Idx Jdx j b := by
      intro α _
      refine mul_nonneg (mul_nonneg (hpou_nn α b) hCB_max_nn) ?_
      refine Finset.sum_nonneg (fun _ _ => ?_)
      refine Finset.sum_nonneg (fun _ _ => ?_)
      refine Finset.sum_nonneg (fun _ _ => ?_)
      exact compNormSqOnM_nonneg (I := I) (M := M) g r s T₀ α _ _ _ _
    have h_ofReal_le : ENNReal.ofReal (F b) ≤
        ENNReal.ofReal
          (∑ α ∈ S, (chartAtlasPOU I M α : M → ℝ) b * CB_max *
            ∑ Idx : Fin r → Fin n, ∑ Jdx : Fin s → Fin n, ∑ j ∈ Finset.range 3,
              compNormSqOnM (I := I) (M := M) g r s T₀ α Idx Jdx j b) :=
      ENNReal.ofReal_le_ofReal h_pt_real
    have h_distrib : ENNReal.ofReal
        (∑ α ∈ S, (chartAtlasPOU I M α : M → ℝ) b * CB_max *
          ∑ Idx : Fin r → Fin n, ∑ Jdx : Fin s → Fin n, ∑ j ∈ Finset.range 3,
            compNormSqOnM (I := I) (M := M) g r s T₀ α Idx Jdx j b) =
        ∑ α ∈ S, H_alpha α b := by
      rw [ENNReal.ofReal_sum_of_nonneg h_summand_nn]
    rw [h_distrib] at h_ofReal_le
    exact h_ofReal_le
  have h_int_M_le :
      ∫⁻ b, ENNReal.ofReal (F b)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) ≤
      ∫⁻ b, ∑ α ∈ S, H_alpha α b
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
    lintegral_mono h_pointwise_M
  have h_sum_swap :
      ∫⁻ b, ∑ α ∈ S, H_alpha α b
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        ∑ α ∈ S, ∫⁻ b, H_alpha α b
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
    lintegral_finset_sum S (fun α _ => hH_alpha_meas α)
  rw [h_sum_swap] at h_int_M_le
  have h_per_α_int : ∀ α ∈ S,
      ∫⁻ b, H_alpha α b
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) ≤
        ENNReal.ofReal D_max *
          ∑ IJ : (Fin r → Fin n) × (Fin s → Fin n),
            ∑ j ∈ Finset.range 3,
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                ENNReal.ofReal
                  (((chartAtlasPOU I M α : M → ℝ)
                      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                    ‖iteratedFDeriv ℝ j
                        (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α IJ.1 IJ.2
                          ∘ (extChartAt I α).symm)
                        ((toEuclidean (E := E)).symm y)‖ ^ 2)
                ∂(volume : Measure EuclN) := by
    intro α hα
    have h_use := per_alpha_measurable_lintegral_le
      (I := I) (M := M) g r s α CB_max hCB_max_nn T₀
    refine le_trans h_use ?_
    exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (hD_α_le_max α hα)) _
  have h_sum_per_α :
      ∑ α ∈ S, ∫⁻ b, H_alpha α b
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) ≤
      ∑ α ∈ S,
        ENNReal.ofReal D_max *
          ∑ IJ : (Fin r → Fin n) × (Fin s → Fin n),
            ∑ j ∈ Finset.range 3,
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                ENNReal.ofReal
                  (((chartAtlasPOU I M α : M → ℝ)
                      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                    ‖iteratedFDeriv ℝ j
                        (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α IJ.1 IJ.2
                          ∘ (extChartAt I α).symm)
                        ((toEuclidean (E := E)).symm y)‖ ^ 2)
                ∂(volume : Measure EuclN) :=
    Finset.sum_le_sum h_per_α_int
  have h_pull :
      ∑ α ∈ S,
        ENNReal.ofReal D_max *
          ∑ IJ : (Fin r → Fin n) × (Fin s → Fin n),
            ∑ j ∈ Finset.range 3,
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                ENNReal.ofReal
                  (((chartAtlasPOU I M α : M → ℝ)
                      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                    ‖iteratedFDeriv ℝ j
                        (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α IJ.1 IJ.2
                          ∘ (extChartAt I α).symm)
                        ((toEuclidean (E := E)).symm y)‖ ^ 2)
                ∂(volume : Measure EuclN) =
      ENNReal.ofReal D_max *
        ∑ α ∈ S,
          ∑ IJ : (Fin r → Fin n) × (Fin s → Fin n),
            ∑ j ∈ Finset.range 3,
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                ENNReal.ofReal
                  (((chartAtlasPOU I M α : M → ℝ)
                      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                    ‖iteratedFDeriv ℝ j
                        (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α IJ.1 IJ.2
                          ∘ (extChartAt I α).symm)
                        ((toEuclidean (E := E)).symm y)‖ ^ 2)
                ∂(volume : Measure EuclN) := by
    rw [Finset.mul_sum]
  rw [h_pull] at h_sum_per_α
  have h_inner_eq :
      ∑ α ∈ S,
        ∑ IJ : (Fin r → Fin n) × (Fin s → Fin n),
          ∑ j ∈ Finset.range 3,
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                  ‖iteratedFDeriv ℝ j
                      (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α IJ.1 IJ.2
                        ∘ (extChartAt I α).symm)
                      ((toEuclidean (E := E)).symm y)‖ ^ 2)
              ∂(volume : Measure EuclN) =
        (tensorPouSobolevNorm (I := I) (M := M) g 1 T₀) ^ 2 := by
    rw [tensorPouSobolevNorm_one_sq_eq (I := I) (M := M) g T₀]
    rw [tensorPouSobolevNormSqSum_one_eq_finsetSum (I := I) (M := M) g T₀, ← hS_def]
  change ∫⁻ b, ENNReal.ofReal
        (riemannianFiberNormSq (I := I) (M := M) g r s b
          (rawTensorConnLap (I := I) g r s
            (fun z : M => T₀.toSection z) b))
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) ≤
      ENNReal.ofReal D_max * (tensorPouSobolevNorm (I := I) (M := M) g 1 T₀) ^ 2
  have hLHS_eq : (fun b : M => ENNReal.ofReal
        (riemannianFiberNormSq (I := I) (M := M) g r s b
          (rawTensorConnLap (I := I) g r s
            (fun z : M => T₀.toSection z) b))) =
      fun b : M => ENNReal.ofReal (F b) := by
    funext b; rw [hF_def]
  rw [hLHS_eq]
  calc ∫⁻ b, ENNReal.ofReal (F b)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g)
      ≤ ∑ α ∈ S, ∫⁻ b, H_alpha α b
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := h_int_M_le
    _ ≤ ENNReal.ofReal D_max *
        ∑ α ∈ S,
          ∑ IJ : (Fin r → Fin n) × (Fin s → Fin n),
            ∑ j ∈ Finset.range 3,
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                ENNReal.ofReal
                  (((chartAtlasPOU I M α : M → ℝ)
                      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                    ‖iteratedFDeriv ℝ j
                        (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α IJ.1 IJ.2
                          ∘ (extChartAt I α).symm)
                        ((toEuclidean (E := E)).symm y)‖ ^ 2)
                ∂(volume : Measure EuclN) := h_sum_per_α
    _ = ENNReal.ofReal D_max * (tensorPouSobolevNorm (I := I) (M := M) g 1 T₀) ^ 2 := by
        rw [h_inner_eq]

end Connection
end Integral
end DifferentialGeometry

end
