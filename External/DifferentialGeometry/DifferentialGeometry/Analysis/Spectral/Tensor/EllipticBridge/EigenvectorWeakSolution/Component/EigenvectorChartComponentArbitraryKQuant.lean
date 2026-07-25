import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Regularity.EigenvectorArbitraryKRegularity
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.EnergyBound.EigenvectorChartCptResolvBounds
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Component.EigenvectorChartComponentH2EnergyBoundUniform
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.RHS.DifferentiatedRHSEigenvalueBounds.EigenvectorChartRHSDiffWkpNormSharpBoundedExplicit
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Cross.EigenvectorCrossRightBound
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Iterated.EigenvectorIteratedCarrier
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Iterated.EigenvectorIteratedCarrierFChartWkpNorm
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Iterated.EigenvectorIteratedNirenbergWeakenedQuant
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Iterated.EigenvectorIteratedRegularityHigherQuant
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Cutoff.EigenvectorPartialCompCutoffBounds


noncomputable section

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Sobolev.Chart
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Sobolev.Euclidean

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma chartTargetEuclid_eq_local (α : M) :
    (chartTargetEuclid (I := I) (M := M) α : Set EuclN) =
      DifferentialGeometry.Analysis.Laplacian.MetricExtension.chartTargetEuclid
        (I := I) (M := M) α := rfl

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma chartPulledWeightedMeasure_restrict_le_volume_on_chartPouKernel_local
    (g : SmoothRiemannianMetric I M) (α : M) :
    ∃ c : ℝ, 0 ≤ c ∧
      (chartPulledWeightedMeasure (I := I) g α).restrict
          (chartPouKernel (I := I) (M := M) α) ≤
        ENNReal.ofReal c •
          ((volume : Measure EuclN).restrict
            (chartPouKernel (I := I) (M := M) α)) := by
  classical
  set K : Set EuclN := chartPouKernel (I := I) (M := M) α with hK_def
  have hK_compact : IsCompact K := chartPouKernel_isCompact (I := I) (M := M) α
  have hK_meas : MeasurableSet K :=
    chartPouKernel_measurableSet (I := I) (M := M) α
  have hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α :=
    chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
  obtain ⟨_c_min, c_max, hc_min_pos, hc_le, h_bd⟩ :=
    densityOnEuclid_bounded_on_compact (I := I) (M := M) g α hK_compact hK_in
  refine ⟨c_max, le_of_lt (lt_of_lt_of_le hc_min_pos hc_le), ?_⟩
  refine Measure.le_iff.2 ?_
  intro A hA
  rw [Measure.restrict_apply hA, Measure.smul_apply, Measure.restrict_apply hA]
  unfold chartPulledWeightedMeasure
  rw [withDensity_apply _ (hA.inter hK_meas)]
  have h_pointwise_bd :
      ∫⁻ y in A ∩ K,
          ENNReal.ofReal (densityOnEuclid (I := I) g α y)
            ∂(volume : Measure EuclN) ≤
      ∫⁻ _y in A ∩ K, ENNReal.ofReal c_max ∂(volume : Measure EuclN) := by
    refine MeasureTheory.setLIntegral_mono_ae' (hA.inter hK_meas) ?_
    refine Filter.Eventually.of_forall fun y hy => ?_
    exact ENNReal.ofReal_le_ofReal (h_bd y hy.2).2
  have h_const_eval :
      ∫⁻ _y in A ∩ K, ENNReal.ofReal c_max ∂(volume : Measure EuclN) =
      ENNReal.ofReal c_max * (volume : Measure EuclN) (A ∩ K) :=
    MeasureTheory.setLIntegral_const _ _
  rw [smul_eq_mul]
  exact h_pointwise_bd.trans (le_of_eq h_const_eval)

omit [CompleteSpace E] in

omit [NeZero (Module.finrank ℝ E)] in
private lemma eLpNorm_chartPulledWeighted_le_of_ae_zero_off_chartPouKernel_uniform_local
    {ι : Type*} (g : SmoothRiemannianMetric I M) (α : M)
    {f : ι → EuclN → ℝ}
    (hf : ∀ i, f i =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α)] (fun _ : EuclN => (0 : ℝ))) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : ι,
        eLpNorm (f i) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal C *
            eLpNorm (f i) 2
              ((volume : Measure EuclN).restrict
                (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  set K : Set EuclN := chartPouKernel (I := I) (M := M) α with hK_def
  have hK_meas : MeasurableSet K :=
    chartPouKernel_measurableSet (I := I) (M := M) α
  have hK_in : K ⊆ Ω := chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hV_meas : MeasurableSet (Ω \ K) := hΩ_open.measurableSet.diff hK_meas
  obtain ⟨c, hc_nn, hc_le⟩ :=
    chartPulledWeightedMeasure_restrict_le_volume_on_chartPouKernel_local
      (I := I) (M := M) g α
  refine ⟨Real.sqrt c, Real.sqrt_nonneg _, fun i => ?_⟩
  have hf' : ∀ᵐ y ∂((volume : Measure EuclN).restrict Ω),
      y ∉ K → f i y = 0 := by
    have hf_i := hf i
    rw [Filter.EventuallyEq, ae_restrict_iff' hV_meas] at hf_i
    rw [ae_restrict_iff' hΩ_open.measurableSet]
    filter_upwards [hf_i] with y hy hy_Ω hy_K
    exact hy ⟨hy_Ω, hy_K⟩
  have h_abs : (chartPulledWeightedMeasure (I := I) g α).restrict Ω ≪
      (volume : Measure EuclN).restrict Ω := by
    unfold chartPulledWeightedMeasure
    exact (withDensity_absolutelyContinuous (volume : Measure EuclN) _).restrict Ω
  have hf_w : ∀ᵐ y ∂((chartPulledWeightedMeasure (I := I) g α).restrict Ω),
      y ∉ K → f i y = 0 := h_abs.ae_le hf'
  have h_ind_w : f i =ᵐ[(chartPulledWeightedMeasure (I := I) g α).restrict Ω]
      K.indicator (f i) := by
    filter_upwards [hf_w] with y hy
    by_cases hyK : y ∈ K
    · rw [Set.indicator_of_mem hyK]
    · rw [Set.indicator_of_notMem hyK, hy hyK]
  have h_ind_v : f i =ᵐ[(volume : Measure EuclN).restrict Ω] K.indicator (f i) := by
    filter_upwards [hf'] with y hy
    by_cases hyK : y ∈ K
    · rw [Set.indicator_of_mem hyK]
    · rw [Set.indicator_of_notMem hyK, hy hyK]
  rw [eLpNorm_congr_ae h_ind_w, eLpNorm_congr_ae h_ind_v,
    eLpNorm_indicator_eq_eLpNorm_restrict hK_meas,
    eLpNorm_indicator_eq_eLpNorm_restrict hK_meas]
  rw [Measure.restrict_restrict_of_subset hK_in,
    Measure.restrict_restrict_of_subset hK_in]
  have h_mono :
      eLpNorm (f i) 2 ((chartPulledWeightedMeasure (I := I) g α).restrict K)
        ≤ eLpNorm (f i) 2
            (ENNReal.ofReal c • ((volume : Measure EuclN).restrict K)) :=
    eLpNorm_mono_measure (f i) hc_le
  refine h_mono.trans ?_
  rw [eLpNorm_smul_measure_of_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
  have h_toReal : ((1 / 2 : ℝ≥0∞).toReal : ℝ) = (1 : ℝ) / 2 := by
    rw [show (1 / 2 : ℝ≥0∞) = (1 : ℝ≥0∞) / 2 from rfl]; simp
  rw [h_toReal]
  have h_pow_eq : ENNReal.ofReal c ^ ((1 : ℝ) / 2) =
      ENNReal.ofReal (Real.sqrt c) := by
    rw [Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_nonneg hc_nn (by positivity)]
  rw [h_pow_eq, smul_eq_mul]

section Unconditional

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

omit [CompleteSpace E] in
private lemma wkpNorm_eigenvectorChartComponentFun_eq_zero_of_notMem
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    {α : M} (hα : α ∉ chartAtlasPOU_activeFinset I M)
    (P₀ : TensorCompIdx (E := E) r s) (K' : ℕ) :
    iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
        (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
          g r s i α P₀)
        (chartTargetEuclid (I := I) (M := M) α) = 0 := by
  classical
  have h_chart_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_kernel_empty :
      chartPouKernel (I := I) (M := M) α = (∅ : Set EuclN) := by
    have h_zero : ∀ x : M,
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 0 :=
      chartAtlasPOU_eq_zero_of_notMem_activeFinset (I := I) (M := M) hα
    have h_supp_empty :
        Function.support (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) = ∅ := by
      ext x; simp [Function.mem_support, h_zero x]
    have h_tsupp_empty :
        tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) = ∅ := by
      unfold tsupport; rw [h_supp_empty]; exact closure_empty
    unfold chartPouKernel
    rw [h_tsupp_empty, Set.image_empty, Set.image_empty]
  have h_ae_off :=
    eigenvectorChartComponentFun_ae_zero_off_chartPouKernel
      (I := I) (M := M) g r s i α P₀
  have h_target_eq :
      DifferentialGeometry.Analysis.Laplacian.MetricExtension.chartTargetEuclid
            (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α =
        chartTargetEuclid (I := I) (M := M) α := by
    rw [h_kernel_empty, Set.diff_empty]
  rw [h_target_eq] at h_ae_off
  have h_swap :
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
          (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
            g r s i α P₀)
          (chartTargetEuclid (I := I) (M := M) α) =
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
          (fun _ : EuclN => (0 : ℝ))
          (chartTargetEuclid (I := I) (M := M) α) :=
    wkpNorm_congr_ae (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) h_chart_open h_ae_off
  rw [h_swap]
  exact wkpNorm_zero_fun_zero (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) h_chart_open

omit [CompleteSpace E] in
private lemma resolventChartComponent_memWkp_arbitrary_local
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) (K' : ℕ)
    (β : M) (Q : TensorCompIdx (E := E) r s) :
    MemWkp (d := Module.finrank ℝ E) K' 2
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s i))
          β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
      (chartTargetEuclid (I := I) (M := M) β) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) β with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) β
  have h_eigen : MemWkp (d := Module.finrank ℝ E) K' 2
      (eigenvectorChartComponentFun (I := I) (M := M)
        g r s i β Q) Ω :=
    eigenvector_chartComponent_memWkp_arbitrary
      (I := I) (M := M) g r s i K' β Q
  have h_chart_eq := eigenvector_chartComponent_eq
    (I := I) (M := M) g r s i β Q
  have h_ae :
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s i))
          β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
          EuclN → ℝ) y)
        =ᵐ[(volume : Measure EuclN).restrict Ω]
      (fun y => i.fst.val *
        eigenvectorChartComponentFun (I := I) (M := M)
          g r s i β Q y) := by
    have h_smul := Lp.coeFn_smul i.fst.val
      (tensorL2ChartComponent (I := I) (M := M) g r s
        (tensorResolventEigenbasisVec (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M)
            g r s) i) β Q)
    have hμ_ne : i.fst.val ≠ 0 := i.fst.val_ne_zero
    have h_back :
        i.fst.val •
            tensorL2ChartComponent (I := I) (M := M) g r s
              (tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i) β Q =
          tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q := by
      rw [h_chart_eq, smul_smul, mul_inv_cancel₀ hμ_ne, one_smul]
    rw [h_back] at h_smul
    filter_upwards [h_smul] with y hy
    rw [hy, Pi.smul_apply, smul_eq_mul]; rfl
  exact (MemWkp_congr_ae (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae).mpr
    (MemWkp.const_smul (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_eigen i.fst.val)

omit [CompleteSpace E] in
private lemma sharpDiff_eigen_inv_nonneg
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (0 : ℝ) ≤ (i.fst.val)⁻¹ :=
  le_trans zero_le_one (sharpDiff_eigen_inv_one_le
    (I := I) (M := M) g r s i)

omit [CompleteSpace E] in
private lemma sharpDiff_eigen_inv_pow_le_inv_pow_succ
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) (e : ℕ) :
    (i.fst.val)⁻¹ ^ e ≤ (i.fst.val)⁻¹ ^ (e + 1) := by
  have h1 : (1 : ℝ) ≤ (i.fst.val)⁻¹ :=
    sharpDiff_eigen_inv_one_le (I := I) (M := M) g r s i
  exact pow_le_pow_right₀ h1 (by omega)

omit [CompleteSpace E] in
private lemma eigenvector_chartComponent_wkpNorm_step_perPair
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (m : ℕ) (C_IH : ℝ) (hC_IH_nn : 0 ≤ C_IH)
    (hC_IH_bd : ∀ (α' : M) (P₀' : TensorCompIdx (E := E) r s)
        (i : TensorEigenIdx (I := I) (M := M) g r s),
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (m + 2) 2
            (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
              g r s i α' P₀')
            (chartTargetEuclid (I := I) (M := M) α')
          ≤ ENNReal.ofReal (C_IH * (i.fst.val)⁻¹ ^ (m + 1)) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec
                (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (i : TensorEigenIdx (I := I) (M := M) g r s),
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) ((m + 1) + 2) 2
            (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
              g r s i α P₀)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal (C * (i.fst.val)⁻¹ ^ (m + 2)) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec
                (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖ := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn_def
  have h_pou_resolv :
      ∀ (i : TensorEigenIdx (I := I) (M := M) g r s) (K' : ℕ)
        (β : M) (Q : TensorCompIdx (E := E) r s), K' ≤ 0 + (m + 1) + 1 →
      MemWkp (d := Module.finrank ℝ E) K' 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
            EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β) := fun i K' β Q _ =>
    resolventChartComponent_memWkp_arbitrary_local
      (I := I) (M := M) g r s i K' β Q
  have h_IH_bd_at : ∀ (α' : M) (P₀' : TensorCompIdx (E := E) r s)
      (i : TensorEigenIdx (I := I) (M := M) g r s),
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (0 + (m + 1) + 1) 2
          (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
            g r s i α' P₀')
          (chartTargetEuclid (I := I) (M := M) α')
        ≤ ENNReal.ofReal (C_IH * (i.fst.val)⁻¹ ^ (m + 1)) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖ := by
    intro α' P₀' i
    have h_arith : 0 + (m + 1) + 1 = m + 2 := by omega
    rw [h_arith]
    exact hC_IH_bd α' P₀' i
  set C_cR_data :=
    eigenvector_crossRightLimit_perK_from_uniform_β_unconditional
      (I := I) (M := M) g r s (0 + (m + 1) + 1) C_IH hC_IH_nn
      (m + 1) h_IH_bd_at h_pou_resolv α with hC_cR_data_def
  set C_cut_per : TensorCompIdx (E := E) r s → ℕ → ℝ := fun P K' =>
    (eigenvector_cutoffPartialLpLimit_perK_from_uniform_β_unconditional
      (I := I) (M := M) g r s (0 + (m + 1) + 1) C_IH hC_IH_nn
      (m + 1) h_IH_bd_at h_pou_resolv α P).choose K' with hC_cut_per_def
  set C_cut : ℕ → ℝ := fun K' =>
    ∑ P : TensorCompIdx (E := E) r s, C_cut_per P K' with hC_cut_def
  set H : eigenvectorChartRHSDiffSharpWkpBoundsUpToOrder (I := I) (M := M) g r s α P₀
      (0 + (m + 1) + 1) :=
    { h_pou_resolv := fun i K' β Q hK' => h_pou_resolv i K' β Q hK'
      Ceig := fun _ => C_IH
      eEig := fun _ => m + 1
      hCeig_nn := fun _ => hC_IH_nn
      hCeig_bd := fun i K' hK' =>
        eigenvector_chartComponent_perK_from_uniform_β_unconditional
          (I := I) (M := M) g r s (0 + (m + 1) + 1) C_IH hC_IH_nn
          (m + 1) h_IH_bd_at α P₀ K' hK' i
      CresH := fun _ => C_IH
      eResH := fun _ => m + 1
      hCresH_nn := fun _ => hC_IH_nn
      hCresH_bd := fun i β Q K' hK' =>
        eigenvector_resolventHigh_perK_from_uniform_β_unconditional
          (I := I) (M := M) g r s (0 + (m + 1) + 1) C_IH hC_IH_nn
          (m + 1) h_IH_bd_at
          (fun i' K'' β' Q' _ =>
            resolventChartComponent_memWkp_arbitrary_local
              (I := I) (M := M) g r s i' (K'' + 1) β' Q')
          K' hK' i β Q
      CresL := fun _ => C_IH
      eResL := fun _ => m + 1
      hCresL_nn := fun _ => hC_IH_nn
      hCresL_bd := fun i β Q K' hK' =>
        eigenvector_resolventLow_perK_from_uniform_β_unconditional
          (I := I) (M := M) g r s (0 + (m + 1) + 1) C_IH hC_IH_nn
          (m + 1) h_IH_bd_at h_pou_resolv K' hK' i β Q
      Cpar := fun _ => C_IH
      ePar := fun _ => m + 1
      hCpar_nn := fun _ => hC_IH_nn
      hCpar_bd := fun i P k K' hK' =>
        eigenvector_partialLpLimit_perK_from_uniform_β_unconditional
          (I := I) (M := M) g r s (0 + (m + 1) + 1) C_IH hC_IH_nn
          (m + 1) h_IH_bd_at h_pou_resolv α K' hK' i P k
      Ccom := fun _ => C_IH
      eCom := fun _ => m + 1
      hCcom_nn := fun _ => hC_IH_nn
      hCcom_bd := fun i P K' hK' =>
        eigenvector_componentLpLimit_perK_from_uniform_β_unconditional
          (I := I) (M := M) g r s (0 + (m + 1) + 1) C_IH hC_IH_nn
          (m + 1) h_IH_bd_at h_pou_resolv α K' hK' i P
      CcR := C_cR_data.choose
      eCcR := fun _ => m + 1
      hCcR_nn := C_cR_data.choose_spec.1
      hCcR_bd := fun i P K' hK' => C_cR_data.choose_spec.2 K' hK' i P
      Ccut := C_cut
      eCcut := fun _ => m + 1
      hCcut_nn := fun K' => Finset.sum_nonneg fun P _ =>
        (eigenvector_cutoffPartialLpLimit_perK_from_uniform_β_unconditional
          (I := I) (M := M) g r s (0 + (m + 1) + 1) C_IH hC_IH_nn
          (m + 1) h_IH_bd_at h_pou_resolv α P).choose_spec.1 K'
      hCcut_bd := fun i P l K' hK' => by
        have h_per :=
          (eigenvector_cutoffPartialLpLimit_perK_from_uniform_β_unconditional
            (I := I) (M := M) g r s (0 + (m + 1) + 1) C_IH hC_IH_nn
            (m + 1) h_IH_bd_at h_pou_resolv α P).choose_spec.2 K' hK' i l
        have h_per_nn : ∀ P, 0 ≤ C_cut_per P K' := fun P =>
          (eigenvector_cutoffPartialLpLimit_perK_from_uniform_β_unconditional
            (I := I) (M := M) g r s (0 + (m + 1) + 1) C_IH hC_IH_nn
            (m + 1) h_IH_bd_at h_pou_resolv α P).choose_spec.1 K'
        have h_dom_real : C_cut_per P K' ≤ C_cut K' :=
          Finset.single_le_sum (f := fun P' => C_cut_per P' K')
            (fun P' _ => h_per_nn P') (Finset.mem_univ P)
        have hμ_inv_nn : (0 : ℝ) ≤ (i.fst.val)⁻¹ :=
          le_trans zero_le_one (sharpDiff_eigen_inv_one_le
            (I := I) (M := M) g r s i)
        have h_dom_pow : C_cut_per P K' * (i.fst.val)⁻¹ ^ (m + 1) ≤
            C_cut K' * (i.fst.val)⁻¹ ^ (m + 1) :=
          mul_le_mul_of_nonneg_right h_dom_real (pow_nonneg hμ_inv_nn _)
        have h_const_le :
            ENNReal.ofReal (C_cut_per P K' * (i.fst.val)⁻¹ ^ (m + 1)) ≤
              ENNReal.ofReal (C_cut K' * (i.fst.val)⁻¹ ^ (m + 1)) :=
          ENNReal.ofReal_le_ofReal h_dom_pow
        exact h_per.trans (mul_le_mul_of_nonneg_right h_const_le
          (zero_le _)) }
  have h_eAtomMax : ∀ K', K' ≤ 0 + (m + 1) + 1 →
      H.eEig K' ≤ m + 1 ∧ H.eResH K' ≤ m + 1 ∧
        H.eResL K' ≤ m + 1 ∧ H.ePar K' ≤ m + 1 ∧
        H.eCom K' ≤ m + 1 ∧ H.eCcR K' ≤ m + 1 ∧
        H.eCcut K' ≤ m + 1 := fun K' _ =>
    ⟨le_refl _, le_refl _, le_refl _, le_refl _,
      le_refl _, le_refl _, le_refl _⟩
  set C_p5 : (Fin (m + 1) → Fin n) → ℝ := fun directions =>
    (eigenvectorChartRHSDiff_wkpNorm_le_chartcpt_sharp_bdd_explicit
      (I := I) (M := M) g r s α P₀ (m + 1) 0
      directions H (m + 1) h_eAtomMax).choose with hC_p5_def
  have hC_p5_nn : ∀ directions, 0 ≤ C_p5 directions := fun _ =>
    (eigenvectorChartRHSDiff_wkpNorm_le_chartcpt_sharp_bdd_explicit
      (I := I) (M := M) g r s α P₀ (m + 1) 0 _ H (m + 1)
      h_eAtomMax).choose_spec.1
  have hC_p5_bd : ∀ directions
      (i : TensorEigenIdx (I := I) (M := M) g r s),
      iteratedWeakSobolevNorm (d := n) 0 2
          (eigenvectorChartRHSDiff (I := I) (M := M)
            g r s i α P₀ (m + 1) directions)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (C_p5 directions * (i.fst.val)⁻¹ ^ (m + 2)) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec
              (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖ := fun directions =>
    (eigenvectorChartRHSDiff_wkpNorm_le_chartcpt_sharp_bdd_explicit
      (I := I) (M := M) g r s α P₀ (m + 1) 0 directions H (m + 1)
      h_eAtomMax).choose_spec.2
  obtain ⟨C_W2, hC_W2_pos, hC_W2_bd⟩ :=
    eigenvectorChartIteratedPartial_wkpNorm_two_two_le_uniform
      (I := I) (M := M) g r s α P₀ (m := m + 1)
  obtain ⟨C_OR, hC_OR_pos, hC_OR_bd⟩ :=
    eigenvectorChartComponent_wkpNorm_m_plus_two_of_iterated_le_uniform
      (I := I) (M := M) g r s α P₀ (m + 1)
  obtain ⟨C_cmp, hC_cmp_nn, hC_cmp_bd⟩ :=
    eLpNorm_chartPulledWeighted_le_of_ae_zero_off_chartPouKernel_uniform_local
      (I := I) (M := M)
      (ι := TensorEigenIdx (I := I) (M := M) g r s ×
        (Fin (m + 1) → Fin n))
      g α (f := fun p => eigenvectorChartRHSDiff (I := I) (M := M)
        g r s p.1 α P₀ (m + 1) p.2)
      (fun p => eigenvectorChartRHSDiff_ae_zero_off_chartPouKernel
        (I := I) (M := M) g r s p.1 α P₀ (m + 1) p.2)
  set Sum_p5 : ℝ := ∑ directions : Fin (m + 1) → Fin n, C_p5 directions
    with hSum_p5_def
  have hSum_p5_nn : 0 ≤ Sum_p5 :=
    Finset.sum_nonneg (fun directions _ => hC_p5_nn directions)
  set DirCard : ℕ :=
    (Finset.univ : Finset (Fin (m + 1) → Fin n)).card with hDirCard_def
  have hDirCard_nn : (0 : ℝ) ≤ (DirCard : ℝ) := Nat.cast_nonneg _
  set W1Card : ℕ := ∑ j ∈ Finset.range ((m + 1) + 1),
    (Finset.univ : Finset (Fin j → Fin n)).card with hW1Card_def
  have hW1Card_nn : (0 : ℝ) ≤ (W1Card : ℝ) := Nat.cast_nonneg _
  set C : ℝ := C_OR * ((W1Card : ℝ) * C_IH + C_W2 *
    ((DirCard : ℝ) * C_IH + C_cmp * Sum_p5)) with hC_def
  have h_W2_inner_nn : 0 ≤ (DirCard : ℝ) * C_IH + C_cmp * Sum_p5 :=
    add_nonneg (mul_nonneg hDirCard_nn hC_IH_nn)
      (mul_nonneg hC_cmp_nn hSum_p5_nn)
  have h_inner_nn : 0 ≤ (W1Card : ℝ) * C_IH + C_W2 *
      ((DirCard : ℝ) * C_IH + C_cmp * Sum_p5) :=
    add_nonneg (mul_nonneg hW1Card_nn hC_IH_nn)
      (mul_nonneg hC_W2_pos.le h_W2_inner_nn)
  have hC_nn : 0 ≤ C := mul_nonneg hC_OR_pos.le h_inner_nn
  refine ⟨C, hC_nn, ?_⟩
  intro i
  have hμ_inv_nn : (0 : ℝ) ≤ (i.fst.val)⁻¹ :=
    sharpDiff_eigen_inv_nonneg (I := I) (M := M) g r s i
  have hμ_inv_pow_le := sharpDiff_eigen_inv_pow_le_inv_pow_succ
    (I := I) (M := M) g r s i (m + 1)
  have h_intermediate_w1p : ∀ (j : ℕ), j ≤ m + 1 →
      ∀ (idx : Fin j → Fin n),
        MemWkp (d := n) 1 2
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ j idx)
          (chartTargetEuclid (I := I) (M := M) α) := by
    intro j _ idx
    have h_parent : MemWkp (d := n) (1 + j) 2
        (eigenvectorChartComponentFun (I := I) (M := M)
          g r s i α P₀)
        (chartTargetEuclid (I := I) (M := M) α) :=
      eigenvector_chartComponent_memWkp_arbitrary
        (I := I) (M := M) g r s i (1 + j) α P₀
    exact eigenvectorChartIteratedPartial_memWkp_of_memWkp
      (I := I) (M := M) g r s i α P₀ j 1 h_parent idx
  have h_top_memWkp_two : ∀ (idx : Fin (m + 1) → Fin n),
      MemWkp (d := n) 2 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ (m + 1) idx)
        (chartTargetEuclid (I := I) (M := M) α) := by
    intro idx
    have h_parent : MemWkp (d := n) (2 + (m + 1)) 2
        (eigenvectorChartComponentFun (I := I) (M := M)
          g r s i α P₀)
        (chartTargetEuclid (I := I) (M := M) α) :=
      eigenvector_chartComponent_memWkp_arbitrary
        (I := I) (M := M) g r s i (2 + (m + 1)) α P₀
    exact eigenvectorChartIteratedPartial_memWkp_of_memWkp
      (I := I) (M := M) g r s i α P₀ (m + 1) 2 h_parent idx
  obtain ⟨_, h_raiser⟩ := hC_OR_bd i h_intermediate_w1p h_top_memWkp_two
  have h_parent_succ_arb : ∀ (j : ℕ),
      MemWkp (d := n) (j + 1) 2
        (eigenvectorChartComponentFun (I := I) (M := M)
          g r s i α P₀)
        (chartTargetEuclid (I := I) (M := M) α) := fun j =>
    eigenvector_chartComponent_memWkp_arbitrary
      (I := I) (M := M) g r s i (j + 1) α P₀
  have h_W1_per_summand : ∀ (j : ℕ) (hj : j ≤ m + 1)
      (idx : Fin j → Fin n),
      iteratedWeakSobolevNorm (d := n) 1 2
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ j idx)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (C_IH * (i.fst.val)⁻¹ ^ (m + 1)) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec
              (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖ := by
    intro j hj idx
    have h_w1_slot := (eigenvectorChartIteratedPartial_wkpNorm_one_two_le
      (I := I) (M := M) g r s i α P₀ j idx
      (h_parent_succ_arb j)).2
    have h_mono : iteratedWeakSobolevNorm (d := n) (j + 1) 2
        (eigenvectorChartComponentFun (I := I) (M := M)
          g r s i α P₀)
        (chartTargetEuclid (I := I) (M := M) α)
          ≤ iteratedWeakSobolevNorm (d := n) (m + 2) 2
        (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
          g r s i α P₀)
        (chartTargetEuclid (I := I) (M := M) α) :=
      wkpNorm_mono_order (d := n) (by omega : j + 1 ≤ m + 2) _ _
    exact h_w1_slot.trans (h_mono.trans (hC_IH_bd α P₀ i))
  have h_W1_sum : eigenvectorIteratedW1Aggregate (I := I) (M := M)
      g r s i α P₀ (m + 1)
        ≤ ENNReal.ofReal ((W1Card : ℝ) *
            (C_IH * (i.fst.val)⁻¹ ^ (m + 1))) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec
              (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖ := by
    unfold eigenvectorIteratedW1Aggregate
    have h_inner : ∀ j ∈ Finset.range ((m + 1) + 1),
        ∑ idx : Fin j → Fin n,
          iteratedWeakSobolevNorm (d := n) 1 2
              (eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s i α P₀ j idx)
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal
                ((Finset.univ : Finset (Fin j → Fin n)).card : ℝ) *
              (ENNReal.ofReal (C_IH * (i.fst.val)⁻¹ ^ (m + 1)) *
                ENNReal.ofReal
                  ‖tensorResolventEigenbasisVec
                    (I := I) (M := M)
                    (tensorResolventL2_isCompactOperator
                      (I := I) (M := M) g r s) i‖) := by
      intro j hj
      rw [Finset.mem_range] at hj
      have h_each : ∀ idx ∈ (Finset.univ : Finset (Fin j → Fin n)),
          iteratedWeakSobolevNorm (d := n) 1 2
              (eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s i α P₀ j idx)
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal (C_IH * (i.fst.val)⁻¹ ^ (m + 1)) *
              ENNReal.ofReal
                ‖tensorResolventEigenbasisVec
                  (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator
                    (I := I) (M := M) g r s) i‖ := fun idx _ =>
        h_W1_per_summand j (by omega) idx
      calc ∑ idx : Fin j → Fin n,
              iteratedWeakSobolevNorm (d := n) 1 2
                (eigenvectorChartIteratedPartial (I := I) (M := M)
                  g r s i α P₀ j idx)
                (chartTargetEuclid (I := I) (M := M) α)
            ≤ ∑ _idx : Fin j → Fin n,
                (ENNReal.ofReal (C_IH * (i.fst.val)⁻¹ ^ (m + 1)) *
                  ENNReal.ofReal
                    ‖tensorResolventEigenbasisVec
                      (I := I) (M := M)
                      (tensorResolventL2_isCompactOperator
                        (I := I) (M := M) g r s) i‖) :=
              Finset.sum_le_sum h_each
        _ = ENNReal.ofReal
                ((Finset.univ : Finset (Fin j → Fin n)).card : ℝ) *
              (ENNReal.ofReal (C_IH * (i.fst.val)⁻¹ ^ (m + 1)) *
                ENNReal.ofReal
                  ‖tensorResolventEigenbasisVec
                    (I := I) (M := M)
                    (tensorResolventL2_isCompactOperator
                      (I := I) (M := M) g r s) i‖) := by
            rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_natCast]
    have h_outer := Finset.sum_le_sum h_inner
    refine h_outer.trans ?_
    rw [← Finset.sum_mul]
    have h_card_eq :
        (∑ j ∈ Finset.range ((m + 1) + 1),
          ENNReal.ofReal
            ((Finset.univ : Finset (Fin j → Fin n)).card : ℝ)) =
          ENNReal.ofReal (W1Card : ℝ) := by
      rw [hW1Card_def]
      rw [← ENNReal.ofReal_sum_of_nonneg
        (fun j _ => Nat.cast_nonneg _)]
      congr 1
      push_cast
      rfl
    rw [h_card_eq]
    rw [show ENNReal.ofReal ((W1Card : ℝ) *
        (C_IH * (i.fst.val)⁻¹ ^ (m + 1))) =
        ENNReal.ofReal (W1Card : ℝ) *
        ENNReal.ofReal (C_IH * (i.fst.val)⁻¹ ^ (m + 1)) by
      rw [ENNReal.ofReal_mul hW1Card_nn]]
    rw [mul_assoc]
  have h_parent_m2 : MemWkp (d := n) ((m + 1) + 1) 2
      (eigenvectorChartComponentFun (I := I) (M := M)
        g r s i α P₀)
      (chartTargetEuclid (I := I) (M := M) α) :=
    eigenvector_chartComponent_memWkp_arbitrary
      (I := I) (M := M) g r s i ((m + 1) + 1) α P₀
  have h_pou_qual : ∀ (j : ℕ), j < m + 1 → ∀ (β : M)
      (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := n) (j + 2) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
            EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β) := fun j _ β Q =>
    resolventChartComponent_memWkp_arbitrary_local
      (I := I) (M := M) g r s i (j + 2) β Q
  have h_W2_per_summand : ∀ (idx : Fin (m + 1) → Fin n),
      iteratedWeakSobolevNorm (d := n) 2 2
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ (m + 1) idx)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (C_W2 *
            (C_IH + C_cmp * C_p5 idx) * (i.fst.val)⁻¹ ^ (m + 2)) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec
              (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖ := by
    intro idx
    obtain ⟨D_m, hD_m_dirs, hD_m_fChartEff⟩ :=
      exists_eigenvectorIteratedCarrier
        (I := I) (M := M) g r s i α P₀ (m + 1) idx h_pou_qual
    obtain ⟨_, h_w2_slot⟩ := hC_W2_bd i idx D_m hD_m_dirs h_parent_m2
    have h_w1_of_idx := (eigenvectorChartIteratedPartial_wkpNorm_one_two_le
      (I := I) (M := M) g r s i α P₀ (m + 1) idx h_parent_m2).2
    have h_w1_le : iteratedWeakSobolevNorm (d := n) 1 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ (m + 1) idx)
        (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal (C_IH * (i.fst.val)⁻¹ ^ (m + 1)) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec
                (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖ :=
      h_w1_of_idx.trans (hC_IH_bd α P₀ i)
    have h_f_chart_eq :
        (eigenvectorIteratedTensorChartBilinearData_toData
            (I := I) (M := M) g r s i α P₀ D_m h_parent_m2).f_chart =
          eigenvectorChartRHSDiff (I := I) (M := M)
            g r s i α P₀ (m + 1) idx := by
      change D_m.diffChartForcing = eigenvectorChartRHSDiff (I := I) (M := M)
        g r s i α P₀ (m + 1) idx
      exact hD_m_fChartEff
    have h_eLp_vol_eq_wkp_zero := wkpNorm_zero (d := n) 2
      (eigenvectorChartRHSDiff (I := I) (M := M)
        g r s i α P₀ (m + 1) idx)
      (chartTargetEuclid (I := I) (M := M) α)
    have h_eLp_vol_bd : eLpNorm
          (eigenvectorChartRHSDiff (I := I) (M := M)
            g r s i α P₀ (m + 1) idx) 2
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal (C_p5 idx * (i.fst.val)⁻¹ ^ (m + 2)) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec
              (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖ := by
      rw [← h_eLp_vol_eq_wkp_zero]
      exact hC_p5_bd idx i
    have h_eLp_weighted_bd :
        eLpNorm
            ((eigenvectorIteratedTensorChartBilinearData_toData
                (I := I) (M := M) g r s i α P₀ D_m h_parent_m2).f_chart)
            2 ((chartPulledWeightedMeasure (I := I) g α).restrict
                (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal (C_cmp * C_p5 idx *
            (i.fst.val)⁻¹ ^ (m + 2)) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec
                (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖ := by
      rw [h_f_chart_eq]
      refine (hC_cmp_bd (i, idx)).trans ?_
      refine le_trans (mul_le_mul_of_nonneg_left h_eLp_vol_bd (zero_le _)) ?_
      rw [← mul_assoc, ← ENNReal.ofReal_mul hC_cmp_nn]
      rw [show C_cmp * (C_p5 idx * (i.fst.val)⁻¹ ^ (m + 2)) =
        C_cmp * C_p5 idx * (i.fst.val)⁻¹ ^ (m + 2) by ring]
    refine h_w2_slot.trans ?_
    refine le_trans (mul_le_mul_of_nonneg_left
      (add_le_add h_w1_le h_eLp_weighted_bd) (zero_le _)) ?_
    have h_pow_le_real : C_IH * (i.fst.val)⁻¹ ^ (m + 1) ≤
        C_IH * (i.fst.val)⁻¹ ^ (m + 2) :=
      mul_le_mul_of_nonneg_left hμ_inv_pow_le hC_IH_nn
    have h_eNN_pow_le :
        ENNReal.ofReal (C_IH * (i.fst.val)⁻¹ ^ (m + 1)) ≤
          ENNReal.ofReal (C_IH * (i.fst.val)⁻¹ ^ (m + 2)) :=
      ENNReal.ofReal_le_ofReal h_pow_le_real
    have h_lhs_le :
        ENNReal.ofReal (C_IH * (i.fst.val)⁻¹ ^ (m + 1)) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec
              (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖ +
        ENNReal.ofReal (C_cmp * C_p5 idx * (i.fst.val)⁻¹ ^ (m + 2)) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec
              (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖ ≤
        ENNReal.ofReal (C_IH * (i.fst.val)⁻¹ ^ (m + 2)) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec
              (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖ +
        ENNReal.ofReal (C_cmp * C_p5 idx * (i.fst.val)⁻¹ ^ (m + 2)) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec
              (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖ :=
      add_le_add (mul_le_mul_of_nonneg_right h_eNN_pow_le (zero_le _))
        (le_refl _)
    refine le_trans (mul_le_mul_of_nonneg_left h_lhs_le (zero_le _)) ?_
    have h_nn_1 : 0 ≤ C_IH * (i.fst.val)⁻¹ ^ (m + 2) :=
      mul_nonneg hC_IH_nn (pow_nonneg hμ_inv_nn _)
    have h_nn_2 : 0 ≤ C_cmp * C_p5 idx * (i.fst.val)⁻¹ ^ (m + 2) :=
      mul_nonneg (mul_nonneg hC_cmp_nn (hC_p5_nn idx))
        (pow_nonneg hμ_inv_nn _)
    have h_eq_factor :
        ENNReal.ofReal (C_IH * (i.fst.val)⁻¹ ^ (m + 2)) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec
              (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖ +
        ENNReal.ofReal (C_cmp * C_p5 idx * (i.fst.val)⁻¹ ^ (m + 2)) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec
              (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖ =
        ENNReal.ofReal ((C_IH + C_cmp * C_p5 idx) *
          (i.fst.val)⁻¹ ^ (m + 2)) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec
              (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖ := by
      rw [← add_mul, ← ENNReal.ofReal_add h_nn_1 h_nn_2]
      congr 2; ring
    rw [h_eq_factor]
    rw [← mul_assoc, ← ENNReal.ofReal_mul hC_W2_pos.le]
    rw [show C_W2 * ((C_IH + C_cmp * C_p5 idx) * (i.fst.val)⁻¹ ^ (m + 2)) =
        C_W2 * (C_IH + C_cmp * C_p5 idx) * (i.fst.val)⁻¹ ^ (m + 2) by ring]
  have h_W2_sum : eigenvectorIteratedW2Aggregate (I := I) (M := M)
      g r s i α P₀ (m + 1)
        ≤ ENNReal.ofReal (C_W2 * ((DirCard : ℝ) * C_IH + C_cmp * Sum_p5) *
            (i.fst.val)⁻¹ ^ (m + 2)) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec
              (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖ := by
    unfold eigenvectorIteratedW2Aggregate
    have h_sum_le : ∑ idx : Fin (m + 1) → Fin n,
        iteratedWeakSobolevNorm (d := n) 2 2
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s i α P₀ (m + 1) idx)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ∑ idx : Fin (m + 1) → Fin n,
              ENNReal.ofReal (C_W2 *
                  (C_IH + C_cmp * C_p5 idx) * (i.fst.val)⁻¹ ^ (m + 2)) *
                ENNReal.ofReal
                  ‖tensorResolventEigenbasisVec
                    (I := I) (M := M)
                    (tensorResolventL2_isCompactOperator
                      (I := I) (M := M) g r s) i‖ :=
      Finset.sum_le_sum (fun idx _ => h_W2_per_summand idx)
    refine h_sum_le.trans ?_
    have h_term_nn : ∀ idx : Fin (m + 1) → Fin n,
        0 ≤ C_W2 * (C_IH + C_cmp * C_p5 idx) * (i.fst.val)⁻¹ ^ (m + 2) := by
      intro idx
      exact mul_nonneg (mul_nonneg hC_W2_pos.le
        (add_nonneg hC_IH_nn (mul_nonneg hC_cmp_nn (hC_p5_nn idx))))
        (pow_nonneg hμ_inv_nn _)
    have h_pull_out :
        ∑ idx : Fin (m + 1) → Fin n,
          ENNReal.ofReal (C_W2 * (C_IH + C_cmp * C_p5 idx) *
            (i.fst.val)⁻¹ ^ (m + 2)) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec
                (I := I) (M := M)
                (tensorResolventL2_isCompactOperator
                  (I := I) (M := M) g r s) i‖ =
        (∑ idx : Fin (m + 1) → Fin n,
          ENNReal.ofReal (C_W2 * (C_IH + C_cmp * C_p5 idx) *
            (i.fst.val)⁻¹ ^ (m + 2))) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec
              (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖ := by
      rw [Finset.sum_mul]
    rw [h_pull_out]
    refine mul_le_mul_of_nonneg_right ?_ (zero_le _)
    have h_combine :
        ∑ idx : Fin (m + 1) → Fin n,
          ENNReal.ofReal (C_W2 * (C_IH + C_cmp * C_p5 idx) *
            (i.fst.val)⁻¹ ^ (m + 2)) =
          ENNReal.ofReal (∑ idx : Fin (m + 1) → Fin n,
            C_W2 * (C_IH + C_cmp * C_p5 idx) * (i.fst.val)⁻¹ ^ (m + 2)) := by
      rw [← ENNReal.ofReal_sum_of_nonneg]
      intro idx _
      exact h_term_nn idx
    rw [h_combine]
    refine ENNReal.ofReal_le_ofReal ?_
    have h_real_sum :
        ∑ idx : Fin (m + 1) → Fin n,
          C_W2 * (C_IH + C_cmp * C_p5 idx) * (i.fst.val)⁻¹ ^ (m + 2)
          = C_W2 * ((DirCard : ℝ) * C_IH + C_cmp * Sum_p5) *
            (i.fst.val)⁻¹ ^ (m + 2) := by
      have h_step1 :
          ∑ idx : Fin (m + 1) → Fin n,
            C_W2 * (C_IH + C_cmp * C_p5 idx) * (i.fst.val)⁻¹ ^ (m + 2) =
          (∑ idx : Fin (m + 1) → Fin n,
            C_W2 * (C_IH + C_cmp * C_p5 idx)) * (i.fst.val)⁻¹ ^ (m + 2) := by
        rw [← Finset.sum_mul]
      rw [h_step1]
      congr 1
      have h_step2 :
          ∑ idx : Fin (m + 1) → Fin n,
            C_W2 * (C_IH + C_cmp * C_p5 idx) =
            ∑ idx : Fin (m + 1) → Fin n,
              (C_W2 * C_IH + C_W2 * (C_cmp * C_p5 idx)) := by
        apply Finset.sum_congr rfl
        intro idx _
        ring
      rw [h_step2, Finset.sum_add_distrib]
      rw [Finset.sum_const]
      simp only [nsmul_eq_mul, hDirCard_def, hSum_p5_def]
      have h_factor : ∑ x : Fin (m + 1) → Fin n,
          C_W2 * (C_cmp * C_p5 x) =
          C_W2 * C_cmp * ∑ x : Fin (m + 1) → Fin n, C_p5 x := by
        rw [← Finset.mul_sum]
        rw [← Finset.mul_sum]
        ring
      rw [h_factor]
      ring
    rw [h_real_sum]
  have h_W1_W2_sum :
      eigenvectorIteratedW1Aggregate (I := I) (M := M)
          g r s i α P₀ (m + 1) +
        eigenvectorIteratedW2Aggregate (I := I) (M := M)
          g r s i α P₀ (m + 1)
        ≤ ENNReal.ofReal (((W1Card : ℝ) * C_IH + C_W2 *
            ((DirCard : ℝ) * C_IH + C_cmp * Sum_p5)) *
            (i.fst.val)⁻¹ ^ (m + 2)) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec
              (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖ := by
    have h_W1_dom : eigenvectorIteratedW1Aggregate (I := I) (M := M)
        g r s i α P₀ (m + 1)
          ≤ ENNReal.ofReal ((W1Card : ℝ) * C_IH *
              (i.fst.val)⁻¹ ^ (m + 2)) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec
                (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖ := by
      refine h_W1_sum.trans ?_
      refine mul_le_mul_of_nonneg_right ?_ (zero_le _)
      refine ENNReal.ofReal_le_ofReal ?_
      rw [show (W1Card : ℝ) * (C_IH * (i.fst.val)⁻¹ ^ (m + 1)) =
          (W1Card : ℝ) * C_IH * (i.fst.val)⁻¹ ^ (m + 1) by ring]
      exact mul_le_mul_of_nonneg_left hμ_inv_pow_le
        (mul_nonneg hW1Card_nn hC_IH_nn)
    have h_add_le := add_le_add h_W1_dom h_W2_sum
    refine h_add_le.trans ?_
    have h_nn_w1 : 0 ≤ (W1Card : ℝ) * C_IH * (i.fst.val)⁻¹ ^ (m + 2) :=
      mul_nonneg (mul_nonneg hW1Card_nn hC_IH_nn)
        (pow_nonneg hμ_inv_nn _)
    have h_nn_w2 : 0 ≤ C_W2 * ((DirCard : ℝ) * C_IH + C_cmp * Sum_p5) *
        (i.fst.val)⁻¹ ^ (m + 2) :=
      mul_nonneg (mul_nonneg hC_W2_pos.le h_W2_inner_nn)
        (pow_nonneg hμ_inv_nn _)
    rw [show ENNReal.ofReal ((W1Card : ℝ) * C_IH *
            (i.fst.val)⁻¹ ^ (m + 2)) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec
              (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖ +
          ENNReal.ofReal (C_W2 * ((DirCard : ℝ) * C_IH + C_cmp * Sum_p5) *
            (i.fst.val)⁻¹ ^ (m + 2)) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec
              (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖ =
          ENNReal.ofReal (((W1Card : ℝ) * C_IH + C_W2 *
            ((DirCard : ℝ) * C_IH + C_cmp * Sum_p5)) *
            (i.fst.val)⁻¹ ^ (m + 2)) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec
              (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖ by
      rw [← add_mul, ← ENNReal.ofReal_add h_nn_w1 h_nn_w2]
      congr 2; ring]
  refine h_raiser.trans ?_
  refine le_trans (mul_le_mul_of_nonneg_left h_W1_W2_sum (zero_le _)) ?_
  rw [← mul_assoc, ← ENNReal.ofReal_mul hC_OR_pos.le]
  rw [show C_OR * (((W1Card : ℝ) * C_IH + C_W2 *
      ((DirCard : ℝ) * C_IH + C_cmp * Sum_p5)) * (i.fst.val)⁻¹ ^ (m + 2)) =
      C * (i.fst.val)⁻¹ ^ (m + 2) by rw [hC_def]; ring]

omit [CompleteSpace E] in
private theorem eigenvector_chartComponent_wkpNorm_pm_uniform_β_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (α : M) (P₀ : TensorCompIdx (E := E) r s)
        (i : TensorEigenIdx (I := I) (M := M) g r s),
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (m + 2) 2
            (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
              g r s i α P₀)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal (C * (i.fst.val)⁻¹ ^ (m + 1)) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec
                (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖ := by
  classical
  induction m with
  | zero =>
      simpa using
        eigenvector_chartComponent_wkpNorm_two_energy_le_uniform_β_unconditional
          (I := I) (M := M) g r s
  | succ m ih =>
      obtain ⟨C_IH, hC_IH_nn, hC_IH_bd⟩ := ih
      set C_step : M → TensorCompIdx (E := E) r s → ℝ := fun α P₀ =>
        (eigenvector_chartComponent_wkpNorm_step_perPair
          (I := I) (M := M) g r s m C_IH hC_IH_nn hC_IH_bd α P₀).choose
        with hC_step_def
      have hC_step_nn : ∀ α P₀, 0 ≤ C_step α P₀ := fun α P₀ =>
        (eigenvector_chartComponent_wkpNorm_step_perPair
          (I := I) (M := M) g r s m C_IH hC_IH_nn hC_IH_bd
            α P₀).choose_spec.1
      have hC_step_bd : ∀ α P₀ i,
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) ((m + 1) + 2) 2
              (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
                g r s i α P₀)
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal (C_step α P₀ * (i.fst.val)⁻¹ ^ (m + 2)) *
              ENNReal.ofReal
                ‖tensorResolventEigenbasisVec
                  (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator
                    (I := I) (M := M) g r s) i‖ := fun α P₀ =>
        (eigenvector_chartComponent_wkpNorm_step_perPair
          (I := I) (M := M) g r s m C_IH hC_IH_nn hC_IH_bd
            α P₀).choose_spec.2
      refine ⟨∑ α ∈ chartAtlasPOU_activeFinset I M,
        ∑ P₀ : TensorCompIdx (E := E) r s, C_step α P₀, ?_, ?_⟩
      · exact Finset.sum_nonneg fun α _ =>
          Finset.sum_nonneg fun P₀ _ => hC_step_nn α P₀
      intro α P₀ i
      by_cases hα : α ∈ chartAtlasPOU_activeFinset I M
      · have hμ_inv_nn : (0 : ℝ) ≤ (i.fst.val)⁻¹ :=
          sharpDiff_eigen_inv_nonneg (I := I) (M := M) g r s i
        have h_step_le : C_step α P₀ ≤
            ∑ α' ∈ chartAtlasPOU_activeFinset I M,
              ∑ P₀' : TensorCompIdx (E := E) r s, C_step α' P₀' := by
          have h1 : C_step α P₀ ≤ ∑ P₀' : TensorCompIdx (E := E) r s,
              C_step α P₀' :=
            Finset.single_le_sum (f := fun P₀' => C_step α P₀')
              (fun P₀' _ => hC_step_nn α P₀') (Finset.mem_univ P₀)
          have h2 : (∑ P₀' : TensorCompIdx (E := E) r s, C_step α P₀') ≤
              ∑ α' ∈ chartAtlasPOU_activeFinset I M,
                ∑ P₀' : TensorCompIdx (E := E) r s, C_step α' P₀' :=
            Finset.single_le_sum
              (f := fun α' => ∑ P₀' : TensorCompIdx (E := E) r s,
                C_step α' P₀')
              (fun α' _ => Finset.sum_nonneg
                (fun P₀' _ => hC_step_nn α' P₀')) hα
          exact h1.trans h2
        have h_real_le : C_step α P₀ * (i.fst.val)⁻¹ ^ (m + 2) ≤
            (∑ α' ∈ chartAtlasPOU_activeFinset I M,
              ∑ P₀' : TensorCompIdx (E := E) r s, C_step α' P₀') *
              (i.fst.val)⁻¹ ^ (m + 2) :=
          mul_le_mul_of_nonneg_right h_step_le (pow_nonneg hμ_inv_nn _)
        have h_const_le :
            ENNReal.ofReal (C_step α P₀ * (i.fst.val)⁻¹ ^ (m + 2)) ≤
              ENNReal.ofReal
                ((∑ α' ∈ chartAtlasPOU_activeFinset I M,
                  ∑ P₀' : TensorCompIdx (E := E) r s, C_step α' P₀') *
                  (i.fst.val)⁻¹ ^ (m + 2)) :=
          ENNReal.ofReal_le_ofReal h_real_le
        exact (hC_step_bd α P₀ i).trans
          (mul_le_mul_of_nonneg_right h_const_le (zero_le _))
      · rw [wkpNorm_eigenvectorChartComponentFun_eq_zero_of_notMem
          (I := I) (M := M) g r s i hα P₀ ((m + 1) + 2)]
        exact zero_le _

omit [CompleteSpace E] in
theorem eigenvector_chartComponent_wkpNorm_arbitrary
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (k : ℕ) (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (i : TensorEigenIdx (I := I) (M := M) g r s),
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) k 2
            (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
              g r s i α P₀)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal (C * (i.fst.val)⁻¹ ^ (k + 1)) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec
                (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖ := by
  classical
  obtain ⟨C, hC_nn, hC_bd⟩ :=
    eigenvector_chartComponent_wkpNorm_pm_uniform_β_unconditional
      (I := I) (M := M) g r s k
  refine ⟨C, hC_nn, fun i => ?_⟩
  have h_mono : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) k 2
      (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
        g r s i α P₀)
      (chartTargetEuclid (I := I) (M := M) α)
        ≤ iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (k + 2) 2
      (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
        g r s i α P₀)
      (chartTargetEuclid (I := I) (M := M) α) :=
    wkpNorm_mono_order (d := Module.finrank ℝ E) (by omega : k ≤ k + 2) _ _
  exact h_mono.trans (hC_bd α P₀ i)

end Unconditional

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
