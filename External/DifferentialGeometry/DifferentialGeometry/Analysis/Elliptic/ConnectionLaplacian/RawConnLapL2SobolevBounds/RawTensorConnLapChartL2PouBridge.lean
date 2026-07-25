import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RawConnLapL2SobolevBounds.TensorConnLaplacianL2Bound
import DifferentialGeometry.Analysis.Integration.Measure.Rellich
import DifferentialGeometry.Analysis.Sobolev.Chart.BanachCompleteness.CompletenessLp


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold Set FiberBundle NormedSpace Filter CovariantDerivative
open MeasureTheory
open scoped Manifold Topology ContDiff BigOperators ENNReal NNReal

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Tensor
open Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart

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

noncomputable def chartSobolevRawNormPou
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s) :
    ℝ≥0∞ :=
  ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
    ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
      ENNReal.ofReal
          (((chartAtlasPOU I M α : M → ℝ)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
        ENNReal.ofReal
          (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
            (fun b : M =>
              rawTensorConnLap (I := I) g r s
                (fun z : M => T.toSection z) b)
            y)
      ∂(volume : Measure EuclN)

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma chartSobolevRawNormPou_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s) :
    chartSobolevRawNormPou (I := I) (M := M) g r s T =
      ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
            ENNReal.ofReal
              (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                (fun b : M =>
                  rawTensorConnLap (I := I) g r s
                    (fun z : M => T.toSection z) b)
                y)
          ∂(volume : Measure EuclN) := rfl

variable (I M) in

private noncomputable def chartAtlasPOU_tsupp_nonempty
    (α : M) : Prop :=
  (tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)).Nonempty

variable (I M) in

noncomputable def chartDensitySupPou
    (g : SmoothRiemannianMetric I M) (α : M) : ℝ :=
  open Classical in
  if h : chartAtlasPOU_tsupp_nonempty (I := I) (M := M) α then
    (exists_sup_chartDensity_on_pou_tsupport_image (I := I) (M := M)
      g α h).choose
  else 0

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] in
lemma chartDensitySupPou_nonneg
    (g : SmoothRiemannianMetric I M) (α : M) :
    0 ≤ chartDensitySupPou (I := I) (M := M) g α := by
  classical
  unfold chartDensitySupPou
  by_cases h : chartAtlasPOU_tsupp_nonempty (I := I) (M := M) α
  · rw [dif_pos h]
    exact le_of_lt
      (exists_sup_chartDensity_on_pou_tsupport_image (I := I) (M := M)
        g α h).choose_spec.1
  · rw [dif_neg h]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] in
lemma chartDensitySupPou_le
    (g : SmoothRiemannianMetric I M) (α : M)
    (h_supp_ne :
      (tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)).Nonempty)
    {y : E}
    (hy_image :
      y ∈ (extChartAt I α) '' (tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ))) :
    chartDensity g α ((extChartAt I α).symm y) ≤
      chartDensitySupPou (I := I) (M := M) g α := by
  classical
  have h_pred : chartAtlasPOU_tsupp_nonempty (I := I) (M := M) α := h_supp_ne
  have h := (exists_sup_chartDensity_on_pou_tsupport_image (I := I) (M := M)
    g α h_supp_ne).choose_spec.2 y hy_image
  unfold chartDensitySupPou
  rw [dif_pos h_pred]
  convert h using 2

variable (I M) in

noncomputable def chartSobolevRawNormPouBridgeConstant
    (g : SmoothRiemannianMetric I M) : ℝ :=
  ((chartAtlasPOU_finset (I := I) (M := M)).card : ℝ) *
    ((euclideanHaarFactor E : ℝ) *
      ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        (chartDensitySupPou (I := I) (M := M) g α + 1))

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] in
lemma chartSobolevRawNormPouBridgeConstant_nonneg
    (g : SmoothRiemannianMetric I M) :
    0 ≤ chartSobolevRawNormPouBridgeConstant (I := I) (M := M) g := by
  refine mul_nonneg (Nat.cast_nonneg _) (mul_nonneg ?_ ?_)
  · exact (euclideanHaarFactor_pos (E := E)).le
  · refine Finset.sum_nonneg ?_
    intro α _
    have := chartDensitySupPou_nonneg (I := I) (M := M) g α
    linarith

private lemma sum_finset_sq_le_card_mul_sum_sq
    {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    (∑ i ∈ s, f i) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, (f i) ^ 2 := by
  classical
  by_cases hs : s.card = 0
  · rw [Finset.card_eq_zero] at hs
    subst hs
    simp
  · have h_double_sum : ∑ i ∈ s, ∑ j ∈ s, (f i - f j) ^ 2 =
        2 * ((s.card : ℝ) * (∑ i ∈ s, (f i) ^ 2) - (∑ i ∈ s, f i) ^ 2) := by
      classical
      set S : ℝ := ∑ i ∈ s, f i with hS_def
      set Q : ℝ := ∑ i ∈ s, (f i) ^ 2 with hQ_def
      have h_inner : ∀ i ∈ s, ∑ j ∈ s, (f i - f j) ^ 2 =
          (s.card : ℝ) * (f i) ^ 2 - 2 * (f i) * S + Q := by
        intro i hi
        have hexp : ∀ j, (f i - f j) ^ 2 =
            (f i) ^ 2 - 2 * (f i) * (f j) + (f j) ^ 2 := by
          intro j; ring
        calc ∑ j ∈ s, (f i - f j) ^ 2
            = ∑ j ∈ s, ((f i) ^ 2 - 2 * (f i) * (f j) + (f j) ^ 2) :=
              Finset.sum_congr rfl (fun j _ => hexp j)
          _ = (∑ _j ∈ s, (f i) ^ 2)
                - (∑ j ∈ s, 2 * (f i) * (f j)) + (∑ j ∈ s, (f j) ^ 2) := by
              rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
          _ = (s.card : ℝ) * (f i) ^ 2 - 2 * (f i) * S + Q := by
              rw [Finset.sum_const]
              rw [show (∑ j ∈ s, 2 * (f i) * (f j)) = 2 * (f i) * S from by
                rw [show (fun j => 2 * (f i) * (f j)) =
                  (fun j => (2 * (f i)) * (f j)) from by funext j; ring]
                rw [← Finset.mul_sum, ← hS_def]]
              rw [← hQ_def, nsmul_eq_mul]
      calc ∑ i ∈ s, ∑ j ∈ s, (f i - f j) ^ 2
          = ∑ i ∈ s, ((s.card : ℝ) * (f i) ^ 2 - 2 * (f i) * S + Q) :=
            Finset.sum_congr rfl h_inner
        _ = (∑ i ∈ s, (s.card : ℝ) * (f i) ^ 2)
              - (∑ i ∈ s, 2 * (f i) * S) + (∑ i ∈ s, Q) := by
            rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        _ = (s.card : ℝ) * Q - 2 * S * S + (s.card : ℝ) * Q := by
            rw [show (∑ i ∈ s, (s.card : ℝ) * (f i) ^ 2) =
                (s.card : ℝ) * Q from by
              rw [← Finset.mul_sum, ← hQ_def]]
            rw [show (∑ i ∈ s, 2 * (f i) * S) = 2 * S * S from by
              rw [show (fun i => 2 * (f i) * S) = (fun i => (2 * S) * (f i)) from by
                funext i; ring]
              rw [← Finset.mul_sum, ← hS_def]]
            rw [Finset.sum_const, nsmul_eq_mul]
        _ = 2 * ((s.card : ℝ) * Q - S ^ 2) := by ring
    have h_nn : 0 ≤ ∑ i ∈ s, ∑ j ∈ s, (f i - f j) ^ 2 :=
      Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    rw [h_double_sum] at h_nn
    nlinarith

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma normSq_le_card_mul_sum_pou_sq_mul_normSq
    {r s : ℕ} (g : SmoothRiemannianMetric I M)
    (T₀ : Π b : M, TensorRSSpace r s I b) (x : M) :
    (‖rawTensorConnLap (I := I) g r s T₀ x‖ ^ 2 : ℝ) ≤
      ((chartAtlasPOU_finset (I := I) (M := M)).card : ℝ) *
        ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
          ((chartAtlasPOU I M α : M → ℝ) x) ^ 2 *
            ‖rawTensorConnLap (I := I) g r s T₀ x‖ ^ 2 := by
  classical
  set v : ℝ := ‖rawTensorConnLap (I := I) g r s T₀ x‖ with hv_def
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
  have hCS :=
    sum_finset_sq_le_card_mul_sum_sq sset (fun α => (chartAtlasPOU I M α : M → ℝ) x * v)
  have h_factor_eq : ∑ α ∈ sset, ((chartAtlasPOU I M α : M → ℝ) x * v) ^ 2 =
      ∑ α ∈ sset, ((chartAtlasPOU I M α : M → ℝ) x) ^ 2 * v ^ 2 :=
    Finset.sum_congr rfl (fun α _ => by ring)
  rw [h_factor_eq] at hCS
  calc (‖rawTensorConnLap (I := I) g r s T₀ x‖ ^ 2 : ℝ)
      = v ^ 2 := rfl
    _ = (∑ α ∈ sset, (chartAtlasPOU I M α : M → ℝ) x * v) ^ 2 := hv_sq_eq
    _ ≤ (sset.card : ℝ) *
          ∑ α ∈ sset, ((chartAtlasPOU I M α : M → ℝ) x) ^ 2 * v ^ 2 := hCS

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma manifold_lintegral_pou_sq_normSq_eq_chartTarget
    {r s : ℕ} (g : SmoothRiemannianMetric I M)
    (T₀ : Π b : M, TensorRSSpace r s I b)
    (hraw_meas :
      Measurable (fun x : M => ‖rawTensorConnLap (I := I) g r s T₀ x‖ ^ 2))
    (α : M) :
    ∫⁻ x,
        ENNReal.ofReal (((chartAtlasPOU I M α : M → ℝ) x) ^ 2 *
            ‖rawTensorConnLap (I := I) g r s T₀ x‖ ^ 2)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      (euclideanHaarFactor E : ℝ≥0∞) *
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal
              (chartDensity g α
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2 *
                ‖rawTensorConnLap (I := I) g r s T₀
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ ^ 2)
          ∂(volume : Measure EuclN) := by
  classical
  set F : M → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (((chartAtlasPOU I M α : M → ℝ) x) ^ 2 *
      ‖rawTensorConnLap (I := I) g r s T₀ x‖ ^ 2) with hF_def
  have hρ_cont : Continuous (fun x : M => (chartAtlasPOU I M α : M → ℝ) x) :=
    ((chartAtlasPOU I M α)).contMDiff.continuous
  have hρ_meas : Measurable (fun x : M => (chartAtlasPOU I M α : M → ℝ) x) :=
    hρ_cont.measurable
  have hρ_sq_meas : Measurable (fun x : M => ((chartAtlasPOU I M α : M → ℝ) x) ^ 2) :=
    hρ_meas.pow_const 2
  have hF_meas : Measurable F := by
    rw [hF_def]
    exact ENNReal.measurable_ofReal.comp (hρ_sq_meas.mul hraw_meas)
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
      ‖rawTensorConnLap (I := I) g r s T₀ x‖ ^ 2) = 0
    rw [hρ_zero]
    simp
  rw [show riemannianVolumeMeasure (I := I) (M := M) g =
      riemannianMeasure (I := I) g (chartAtlasPOU I M) from rfl]
  rw [riemannianMeasure_lintegral_eq_chartLocalMeasure_of_supportIn
      (I := I) (M := M) g α hF_meas hF_supp]
  rw [chartLocalMeasure_lintegral_via_chartTargetEuclid
      (I := I) (M := M) g α hF_meas]

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma normSq_apply_eq_pushedNormSq
    {r s : ℕ} (g : SmoothRiemannianMetric I M)
    (T₀ : Π b : M, TensorRSSpace r s I b)
    (α : M) {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    (‖rawTensorConnLap (I := I) g r s T₀
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ ^ 2 : ℝ) =
      tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
        (fun b : M => rawTensorConnLap (I := I) g r s T₀ b) y := by
  classical
  rw [tensorTrivProjPushedNormSq_apply_of_mem
      (I := I) (M := M) g r s α
      (fun b : M => rawTensorConnLap (I := I) g r s T₀ b) hy]
  rfl

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] in
private lemma density_pou_sq_le
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

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma manifold_lintegral_pou_sq_normSq_eq_zero_of_empty
    {r s : ℕ} (g : SmoothRiemannianMetric I M)
    (T₀ : Π b : M, TensorRSSpace r s I b)
    (α : M)
    (h_supp_empty :
      ¬ (tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)).Nonempty) :
    (fun x : M => (chartAtlasPOU I M α : M → ℝ) x ^ 2 *
        ‖rawTensorConnLap (I := I) g r s T₀ x‖ ^ 2) = 0 := by
  classical
  rw [Set.not_nonempty_iff_eq_empty] at h_supp_empty
  funext x
  have hρ_zero : (chartAtlasPOU I M α : M → ℝ) x = 0 := by
    have hx_notsupp : x ∉ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
      rw [h_supp_empty]; exact Set.notMem_empty x
    exact image_eq_zero_of_notMem_tsupport hx_notsupp
  rw [hρ_zero]; simp

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem rawTensorConnLap_L2NormSq_le_chartSobolevRawNormPou
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : SmoothCcTensor g r s),
        Measurable
          (fun x : M =>
            ‖rawTensorConnLap (I := I) g r s
              (fun z : M => T.toSection z) x‖ ^ 2) →
          ∫⁻ x,
              (‖rawTensorConnLap (I := I) g r s
                  (fun z : M => T.toSection z) x‖ₑ : ℝ≥0∞) ^ 2
              ∂(riemannianVolumeMeasure (I := I) (M := M) g) ≤
            ENNReal.ofReal
                (chartSobolevRawNormPouBridgeConstant (I := I) (M := M) g) *
              chartSobolevRawNormPou (I := I) (M := M) g r s T := by
  classical
  refine ⟨chartSobolevRawNormPouBridgeConstant (I := I) (M := M) g,
    chartSobolevRawNormPouBridgeConstant_nonneg (I := I) (M := M) g, ?_⟩
  intro T hraw_meas
  set T₀ : Π b : M, TensorRSSpace r s I b := fun z : M => T.toSection z with hT₀_def
  set Sfin : Finset M := chartAtlasPOU_finset (I := I) (M := M) with hSfin_def
  set N : ℕ := Sfin.card with hN_def
  set cE : ℝ := (euclideanHaarFactor E : ℝ) with hcE_def
  have hcE_nn : 0 ≤ cE := (euclideanHaarFactor_pos (E := E)).le
  set Mα : M → ℝ := fun α => chartDensitySupPou (I := I) (M := M) g α with hMα_def
  have hMα_nn : ∀ α : M, 0 ≤ Mα α := fun α =>
    chartDensitySupPou_nonneg (I := I) (M := M) g α
  set C : ℝ := chartSobolevRawNormPouBridgeConstant (I := I) (M := M) g with hC_def
  have henorm_sq :
      (fun x : M => (‖rawTensorConnLap (I := I) g r s T₀ x‖ₑ : ℝ≥0∞) ^ 2) =
        (fun x : M => ENNReal.ofReal (‖rawTensorConnLap (I := I) g r s T₀ x‖ ^ 2)) := by
    funext x
    have hen : ‖rawTensorConnLap (I := I) g r s T₀ x‖ₑ =
        ENNReal.ofReal ‖rawTensorConnLap (I := I) g r s T₀ x‖ :=
      (ofReal_norm _).symm
    rw [hen, ← ENNReal.ofReal_pow (norm_nonneg _) 2]
  rw [henorm_sq]
  have h_pointwise : ∀ x : M,
      ENNReal.ofReal (‖rawTensorConnLap (I := I) g r s T₀ x‖ ^ 2) ≤
        ENNReal.ofReal ((N : ℝ) *
          ∑ α ∈ Sfin,
            ((chartAtlasPOU I M α : M → ℝ) x) ^ 2 *
              ‖rawTensorConnLap (I := I) g r s T₀ x‖ ^ 2) := by
    intro x
    have hle := normSq_le_card_mul_sum_pou_sq_mul_normSq
      (I := I) (M := M) g (r := r) (s := s) T₀ x
    refine ENNReal.ofReal_le_ofReal hle
  have h_int_le :
      ∫⁻ x, ENNReal.ofReal (‖rawTensorConnLap (I := I) g r s T₀ x‖ ^ 2)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) ≤
        ∫⁻ x, ENNReal.ofReal ((N : ℝ) *
            ∑ α ∈ Sfin,
              ((chartAtlasPOU I M α : M → ℝ) x) ^ 2 *
                ‖rawTensorConnLap (I := I) g r s T₀ x‖ ^ 2)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
    MeasureTheory.lintegral_mono h_pointwise
  have h_nn_each : ∀ x : M, ∀ α ∈ Sfin,
      0 ≤ ((chartAtlasPOU I M α : M → ℝ) x) ^ 2 *
        ‖rawTensorConnLap (I := I) g r s T₀ x‖ ^ 2 := by
    intro x α _
    exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have h_nn_sum : ∀ x : M,
      0 ≤ ∑ α ∈ Sfin,
        ((chartAtlasPOU I M α : M → ℝ) x) ^ 2 *
          ‖rawTensorConnLap (I := I) g r s T₀ x‖ ^ 2 := by
    intro x
    exact Finset.sum_nonneg (h_nn_each x)
  have hN_nn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
  have h_ofReal_factor : ∀ x : M,
      ENNReal.ofReal ((N : ℝ) *
          ∑ α ∈ Sfin,
            ((chartAtlasPOU I M α : M → ℝ) x) ^ 2 *
              ‖rawTensorConnLap (I := I) g r s T₀ x‖ ^ 2) =
        ENNReal.ofReal (N : ℝ) *
          ENNReal.ofReal (∑ α ∈ Sfin,
            ((chartAtlasPOU I M α : M → ℝ) x) ^ 2 *
              ‖rawTensorConnLap (I := I) g r s T₀ x‖ ^ 2) := fun x =>
    ENNReal.ofReal_mul hN_nn
  have h_ofReal_sum : ∀ x : M,
      ENNReal.ofReal (∑ α ∈ Sfin,
          ((chartAtlasPOU I M α : M → ℝ) x) ^ 2 *
            ‖rawTensorConnLap (I := I) g r s T₀ x‖ ^ 2) =
        ∑ α ∈ Sfin, ENNReal.ofReal
          (((chartAtlasPOU I M α : M → ℝ) x) ^ 2 *
            ‖rawTensorConnLap (I := I) g r s T₀ x‖ ^ 2) := by
    intro x
    rw [ENNReal.ofReal_sum_of_nonneg (h_nn_each x)]
  have h_int_le' :
      ∫⁻ x, ENNReal.ofReal (‖rawTensorConnLap (I := I) g r s T₀ x‖ ^ 2)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) ≤
        ENNReal.ofReal (N : ℝ) *
          ∑ α ∈ Sfin,
            ∫⁻ x, ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ) x) ^ 2 *
                  ‖rawTensorConnLap (I := I) g r s T₀ x‖ ^ 2)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    calc
      _ ≤ ∫⁻ x, ENNReal.ofReal ((N : ℝ) *
              ∑ α ∈ Sfin,
                ((chartAtlasPOU I M α : M → ℝ) x) ^ 2 *
                  ‖rawTensorConnLap (I := I) g r s T₀ x‖ ^ 2)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) := h_int_le
      _ = ∫⁻ x, ENNReal.ofReal (N : ℝ) *
              ENNReal.ofReal (∑ α ∈ Sfin,
                ((chartAtlasPOU I M α : M → ℝ) x) ^ 2 *
                  ‖rawTensorConnLap (I := I) g r s T₀ x‖ ^ 2)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
            refine lintegral_congr ?_
            intro x; exact h_ofReal_factor x
      _ = ENNReal.ofReal (N : ℝ) *
            ∫⁻ x, ENNReal.ofReal (∑ α ∈ Sfin,
              ((chartAtlasPOU I M α : M → ℝ) x) ^ 2 *
                ‖rawTensorConnLap (I := I) g r s T₀ x‖ ^ 2)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
            rw [MeasureTheory.lintegral_const_mul']
            exact ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal (N : ℝ) *
            ∫⁻ x, ∑ α ∈ Sfin, ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ) x) ^ 2 *
                ‖rawTensorConnLap (I := I) g r s T₀ x‖ ^ 2)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
            congr 1
            refine lintegral_congr ?_
            intro x; exact h_ofReal_sum x
      _ = ENNReal.ofReal (N : ℝ) *
            ∑ α ∈ Sfin,
              ∫⁻ x, ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ) x) ^ 2 *
                  ‖rawTensorConnLap (I := I) g r s T₀ x‖ ^ 2)
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
                ((hρ_meas.pow_const 2).mul hraw_meas))
  have h_per_alpha : ∀ α ∈ Sfin,
      ∫⁻ x, ENNReal.ofReal
            (((chartAtlasPOU I M α : M → ℝ) x) ^ 2 *
              ‖rawTensorConnLap (I := I) g r s T₀ x‖ ^ 2)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) ≤
        ENNReal.ofReal (cE * (Mα α + 1)) *
          ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
              ENNReal.ofReal
                (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                  (fun b : M => rawTensorConnLap (I := I) g r s T₀ b) y)
            ∂(volume : Measure EuclN) := by
    intro α hα_mem
    have h_supp_ne : (tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)).Nonempty := by
      rw [chartAtlasPOU_finset_mem] at hα_mem
      exact hα_mem.mono (subset_tsupport _)
    rw [manifold_lintegral_pou_sq_normSq_eq_chartTarget
      (I := I) (M := M) g (r := r) (s := s) T₀ hraw_meas α]
    have hpt_bound : ∀ y, y ∈ chartTargetEuclid (I := I) (M := M) α →
        ENNReal.ofReal
            (chartDensity g α
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
          ENNReal.ofReal
            (((chartAtlasPOU I M α : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2 *
              ‖rawTensorConnLap (I := I) g r s T₀
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ ^ 2)
          ≤ ENNReal.ofReal (Mα α + 1) *
              (ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
                ENNReal.ofReal
                  (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                    (fun b : M => rawTensorConnLap (I := I) g r s T₀ b) y)) := by
      intro y hy
      have hdens_pou_sq_le := density_pou_sq_le
        (I := I) (M := M) g α h_supp_ne hy
      have hdens_nn : 0 ≤ chartDensity g α
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) :=
        Real.sqrt_nonneg _
      have hρ_sq_nn :
          0 ≤ ((chartAtlasPOU I M α : M → ℝ)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2 :=
        sq_nonneg _
      have hnormSq_nn :
          0 ≤ ‖rawTensorConnLap (I := I) g r s T₀
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ ^ 2 :=
        sq_nonneg _
      have h_pushed := normSq_apply_eq_pushedNormSq
        (I := I) (M := M) (r := r) (s := s) g T₀ α hy
      have h_dens_pou_sq_nn : 0 ≤
          chartDensity g α
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
            ((chartAtlasPOU I M α : M → ℝ)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2 :=
        mul_nonneg hdens_nn hρ_sq_nn
      have h_ofReal_inner : ENNReal.ofReal
          (((chartAtlasPOU I M α : M → ℝ)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2 *
            ‖rawTensorConnLap (I := I) g r s T₀
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ ^ 2) =
          ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
            ENNReal.ofReal
              (‖rawTensorConnLap (I := I) g r s T₀
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
        have h_real := hdens_pou_sq_le
        have h_bound :
            chartDensity g α
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
              ((chartAtlasPOU I M α : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2 ≤
            (Mα α + 1) *
              ((chartAtlasPOU I M α : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2 := by
          exact h_real
        have h_Mα1_nn : 0 ≤ Mα α + 1 := by have := hMα_nn α; linarith
        rw [← ENNReal.ofReal_mul hdens_nn,
            ← ENNReal.ofReal_mul h_Mα1_nn]
        exact ENNReal.ofReal_le_ofReal h_bound
      have h_pushed_eq :
          ENNReal.ofReal
            (‖rawTensorConnLap (I := I) g r s T₀
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ ^ 2) =
          ENNReal.ofReal
            (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
              (fun b : M => rawTensorConnLap (I := I) g r s T₀ b) y) := by
        rw [h_pushed]
      calc ENNReal.ofReal
              (chartDensity g α
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            (ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
              ENNReal.ofReal
                (‖rawTensorConnLap (I := I) g r s T₀
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ ^ 2))
          = (ENNReal.ofReal
                (chartDensity g α
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
              ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2)) *
              ENNReal.ofReal
                (‖rawTensorConnLap (I := I) g r s T₀
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ ^ 2) := by
            ring
        _ ≤ (ENNReal.ofReal (Mα α + 1) *
              ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2)) *
              ENNReal.ofReal
                (‖rawTensorConnLap (I := I) g r s T₀
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ ^ 2) := by
            exact mul_le_mul_left hkey _
        _ = ENNReal.ofReal (Mα α + 1) *
              (ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
                ENNReal.ofReal
                  (‖rawTensorConnLap (I := I) g r s T₀
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ ^ 2)) := by
            ring
        _ = ENNReal.ofReal (Mα α + 1) *
              (ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
                ENNReal.ofReal
                  (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                    (fun b : M => rawTensorConnLap (I := I) g r s T₀ b) y)) := by
            rw [h_pushed_eq]
    have hset_int_le :
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal
              (chartDensity g α
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2 *
                ‖rawTensorConnLap (I := I) g r s T₀
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ ^ 2)
            ∂(volume : Measure EuclN)
          ≤ ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal (Mα α + 1) *
                (ENNReal.ofReal
                  (((chartAtlasPOU I M α : M → ℝ)
                      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
                  ENNReal.ofReal
                    (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                      (fun b : M => rawTensorConnLap (I := I) g r s T₀ b) y))
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
                  (fun b : M => rawTensorConnLap (I := I) g r s T₀ b) y))
            ∂(volume : Measure EuclN)
          = ENNReal.ofReal (Mα α + 1) *
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                ENNReal.ofReal
                  (((chartAtlasPOU I M α : M → ℝ)
                      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
                  ENNReal.ofReal
                    (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                      (fun b : M => rawTensorConnLap (I := I) g r s T₀ b) y)
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
                    ‖rawTensorConnLap (I := I) g r s T₀
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
                      (fun b : M => rawTensorConnLap (I := I) g r s T₀ b) y))
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
                      (fun b : M => rawTensorConnLap (I := I) g r s T₀ b) y)
                ∂(volume : Measure EuclN)) := by rw [hpull]
      _ = ((euclideanHaarFactor E : ℝ≥0∞) * ENNReal.ofReal (Mα α + 1)) *
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
                ENNReal.ofReal
                  (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                    (fun b : M => rawTensorConnLap (I := I) g r s T₀ b) y)
              ∂(volume : Measure EuclN) := by ring
      _ = ENNReal.ofReal (cE * (Mα α + 1)) *
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
                ENNReal.ofReal
                  (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                    (fun b : M => rawTensorConnLap (I := I) g r s T₀ b) y)
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
                  (fun b : M => rawTensorConnLap (I := I) g r s T₀ b) y)
            ∂(volume : Measure EuclN) ≤
        ENNReal.ofReal C_inner *
          ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
              ENNReal.ofReal
                (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                  (fun b : M => rawTensorConnLap (I := I) g r s T₀ b) y)
            ∂(volume : Measure EuclN) := by
    intro α hα_mem
    refine mul_le_mul_left ?_ _
    exact ENNReal.ofReal_le_ofReal (hper_term_le α hα_mem)
  have hsum_per_alpha_le :
      ∑ α ∈ Sfin,
          ∫⁻ x, ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ) x) ^ 2 *
                  ‖rawTensorConnLap (I := I) g r s T₀ x‖ ^ 2)
                ∂(riemannianVolumeMeasure (I := I) (M := M) g)
        ≤ ∑ α ∈ Sfin,
            ENNReal.ofReal C_inner *
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                ENNReal.ofReal
                    (((chartAtlasPOU I M α : M → ℝ)
                        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
                  ENNReal.ofReal
                    (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                      (fun b : M => rawTensorConnLap (I := I) g r s T₀ b) y)
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
                    (fun b : M => rawTensorConnLap (I := I) g r s T₀ b) y)
              ∂(volume : Measure EuclN)
        = ENNReal.ofReal C_inner *
            ∑ α ∈ Sfin,
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                ENNReal.ofReal
                    (((chartAtlasPOU I M α : M → ℝ)
                        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
                  ENNReal.ofReal
                    (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                      (fun b : M => rawTensorConnLap (I := I) g r s T₀ b) y)
                ∂(volume : Measure EuclN) := by
    rw [← Finset.mul_sum]
  have h_combined :
      ENNReal.ofReal (N : ℝ) *
        ∑ α ∈ Sfin,
          ∫⁻ x, ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ) x) ^ 2 *
                ‖rawTensorConnLap (I := I) g r s T₀ x‖ ^ 2)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g) ≤
        ENNReal.ofReal (N : ℝ) *
          (ENNReal.ofReal C_inner *
            chartSobolevRawNormPou (I := I) (M := M) g r s T) := by
    refine mul_le_mul_right ?_ _
    rw [chartSobolevRawNormPou_def]
    calc
      ∑ α ∈ Sfin,
          ∫⁻ x, ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ) x) ^ 2 *
                ‖rawTensorConnLap (I := I) g r s T₀ x‖ ^ 2)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g)
        ≤ ∑ α ∈ Sfin,
            ENNReal.ofReal C_inner *
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                ENNReal.ofReal
                    (((chartAtlasPOU I M α : M → ℝ)
                        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
                  ENNReal.ofReal
                    (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                      (fun b : M => rawTensorConnLap (I := I) g r s T₀ b) y)
                ∂(volume : Measure EuclN) := hsum_per_alpha_le
      _ = ENNReal.ofReal C_inner *
            ∑ α ∈ Sfin,
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                ENNReal.ofReal
                    (((chartAtlasPOU I M α : M → ℝ)
                        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
                  ENNReal.ofReal
                    (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α
                      (fun b : M => rawTensorConnLap (I := I) g r s T₀ b) y)
                ∂(volume : Measure EuclN) := hpull_sum
  have h_NC_eq : ENNReal.ofReal (N : ℝ) * ENNReal.ofReal C_inner =
      ENNReal.ofReal C := by
    rw [← ENNReal.ofReal_mul hN_nn, ← hC_eq]
  have h_final_eq :
      ENNReal.ofReal (N : ℝ) *
        (ENNReal.ofReal C_inner *
          chartSobolevRawNormPou (I := I) (M := M) g r s T) =
        ENNReal.ofReal C *
          chartSobolevRawNormPou (I := I) (M := M) g r s T := by
    rw [← mul_assoc, h_NC_eq]
  exact le_trans h_int_le' (le_trans h_combined (le_of_eq h_final_eq))

end Connection
end Integral
end DifferentialGeometry

end
