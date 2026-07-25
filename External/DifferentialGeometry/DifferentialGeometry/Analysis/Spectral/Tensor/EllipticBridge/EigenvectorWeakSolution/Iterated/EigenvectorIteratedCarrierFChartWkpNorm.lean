import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.RHS.DifferentiatedRHS.EigenvectorChartRHSDiffWkpNorm
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Iterated.EigenvectorIteratedNirenbergWeakenedQuant
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Iterated.EigenvectorIteratedCarrier
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.RHS.ChartRHSBounds.EigenvectorChartRHSMemWkp
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.EnergyBound.EigenvectorChartWeightedMemLp

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators
  RealInnerProductSpace InnerProductSpace

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
open DifferentialGeometry.Tensor.TensorRSRiemannian
open TensorRSNabla
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma chartPulledWeightedMeasure_restrict_le_volume_on_chartPouKernel
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
private lemma eLpNorm_chartPulledWeighted_le_of_ae_zero_off_chartPouKernel
    (g : SmoothRiemannianMetric I M) (α : M) {f : EuclN → ℝ}
    (hf : f =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α)] (fun _ : EuclN => (0 : ℝ))) :
    ∃ C : ℝ, 0 ≤ C ∧
      eLpNorm f 2
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal C *
          eLpNorm f 2
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
  have hf' : ∀ᵐ y ∂((volume : Measure EuclN).restrict Ω),
      y ∉ K → f y = 0 := by
    rw [Filter.EventuallyEq, ae_restrict_iff' hV_meas] at hf
    rw [ae_restrict_iff' hΩ_open.measurableSet]
    filter_upwards [hf] with y hy hy_Ω hy_K
    exact hy ⟨hy_Ω, hy_K⟩
  obtain ⟨c, hc_nn, hc_le⟩ :=
    chartPulledWeightedMeasure_restrict_le_volume_on_chartPouKernel
      (I := I) (M := M) g α
  refine ⟨Real.sqrt c, Real.sqrt_nonneg _, ?_⟩
  have h_abs : (chartPulledWeightedMeasure (I := I) g α).restrict Ω ≪
      (volume : Measure EuclN).restrict Ω := by
    unfold chartPulledWeightedMeasure
    exact (withDensity_absolutelyContinuous (volume : Measure EuclN) _).restrict Ω
  have hf_w : ∀ᵐ y ∂((chartPulledWeightedMeasure (I := I) g α).restrict Ω),
      y ∉ K → f y = 0 := h_abs.ae_le hf'
  have h_ind_w : f =ᵐ[(chartPulledWeightedMeasure (I := I) g α).restrict Ω]
      K.indicator f := by
    filter_upwards [hf_w] with y hy
    by_cases hyK : y ∈ K
    · rw [Set.indicator_of_mem hyK]
    · rw [Set.indicator_of_notMem hyK, hy hyK]
  have h_ind_v : f =ᵐ[(volume : Measure EuclN).restrict Ω] K.indicator f := by
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
      eLpNorm f 2 ((chartPulledWeightedMeasure (I := I) g α).restrict K)
        ≤ eLpNorm f 2
            (ENNReal.ofReal c • ((volume : Measure EuclN).restrict K)) :=
    eLpNorm_mono_measure f hc_le
  refine h_mono.trans ?_
  rw [eLpNorm_smul_measure_of_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
  have h_toReal : ((1 / 2 : ℝ≥0∞).toReal : ℝ) = (1 : ℝ) / 2 := by
    rw [show (1 / 2 : ℝ≥0∞) = (1 : ℝ≥0∞) / 2 from rfl]; simp
  rw [h_toReal]
  have h_pow_eq : ENNReal.ofReal c ^ ((1 : ℝ) / 2) =
      ENNReal.ofReal (Real.sqrt c) := by
    rw [Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_nonneg hc_nn (by positivity)]
  rw [h_pow_eq, smul_eq_mul]

omit [CompleteSpace E] in

omit [NeZero (Module.finrank ℝ E)] in
private lemma eLpNorm_chartPulledWeighted_le_of_ae_zero_off_chartPouKernel_uniform
    {ι : Type*} (g : SmoothRiemannianMetric I M) (α : M) {f : ι → EuclN → ℝ}
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
    chartPulledWeightedMeasure_restrict_le_volume_on_chartPouKernel
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

section MainBoundUnconditional

omit [CompleteSpace E] in
theorem eigenvectorIteratedCarrier_fChartEff_eLpNorm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) {m : ℕ}
    (directions : Fin m → Fin (Module.finrank ℝ E))
    (D_m : eigenvectorIteratedTensorChartBilinearData (I := I) (M := M)
      g r s i α P₀ m)
    (h_fChartEff : D_m.diffChartForcing =
      eigenvectorChartRHSDiff (I := I) (M := M)
        g r s i α P₀ m directions)
    (h_parent : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (m + 1) 2
      (eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀)
      (chartTargetEuclid (I := I) (M := M) α))
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (m + 1 + 0) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    ∃ C : ℝ, 0 ≤ C ∧
      eLpNorm
          ((eigenvectorIteratedTensorChartBilinearData_toData
              (I := I) (M := M) g r s i α P₀ D_m h_parent).f_chart)
          2 ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * C) *
          diffRHSAggregate (I := I) (M := M)
            g r s i α P₀ m 0 directions := by
  classical
  have h_f_chart_eq :
      (eigenvectorIteratedTensorChartBilinearData_toData
          (I := I) (M := M) g r s i α P₀ D_m h_parent).f_chart =
        eigenvectorChartRHSDiff (I := I) (M := M)
          g r s i α P₀ m directions := by
    change D_m.diffChartForcing =
      eigenvectorChartRHSDiff (I := I) (M := M)
        g r s i α P₀ m directions
    exact h_fChartEff
  rw [h_f_chart_eq]
  have h_ae_zero :
      eigenvectorChartRHSDiff (I := I) (M := M)
          g r s i α P₀ m directions
        =ᵐ[(volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α \
            chartPouKernel (I := I) (M := M) α)] (fun _ : EuclN => (0 : ℝ)) :=
    rhsDiff_ae_zero_off_chartPouKernel (I := I) (M := M)
      g r s i α P₀ m directions
  obtain ⟨Ccmp, hCcmp_nn, hCcmp_bd⟩ :=
    eLpNorm_chartPulledWeighted_le_of_ae_zero_off_chartPouKernel
      (I := I) (M := M) g α h_ae_zero
  obtain ⟨Cvol, hCvol_nn, hCvol_bd⟩ :=
    eigenvectorChartRHSDiff_eLpNorm_le (I := I) (M := M)
      g r s i α P₀ m directions h_pou
  refine ⟨Ccmp * Cvol, mul_nonneg hCcmp_nn hCvol_nn, ?_⟩
  calc
    eLpNorm (eigenvectorChartRHSDiff (I := I) (M := M)
            g r s i α P₀ m directions) 2
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal Ccmp *
          eLpNorm (eigenvectorChartRHSDiff (I := I) (M := M)
              g r s i α P₀ m directions) 2
            ((volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α)) := hCcmp_bd
    _ ≤ ENNReal.ofReal Ccmp *
          (ENNReal.ofReal ((i.fst.val)⁻¹ * Cvol) *
            diffRHSAggregate (I := I) (M := M)
              g r s i α P₀ m 0 directions) :=
          mul_le_mul' (le_refl _) hCvol_bd
    _ = ENNReal.ofReal ((i.fst.val)⁻¹ * (Ccmp * Cvol)) *
          diffRHSAggregate (I := I) (M := M)
            g r s i α P₀ m 0 directions := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hCcmp_nn]
          congr 2
          ring

omit [CompleteSpace E] in
theorem eigenvectorIteratedCarrier_fChartEff_eLpNorm_le_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) {m : ℕ}
    (directions : Fin m → Fin (Module.finrank ℝ E))
    (h_pou : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (m + 1 + 0) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
        (D_m : eigenvectorIteratedTensorChartBilinearData
          (I := I) (M := M) g r s i α P₀ m)
        (_h_fChartEff : D_m.diffChartForcing =
          eigenvectorChartRHSDiff (I := I) (M := M)
            g r s i α P₀ m directions)
        (h_parent : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) (m + 1) 2
          (eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)),
        eLpNorm
            ((eigenvectorIteratedTensorChartBilinearData_toData
                (I := I) (M := M) g r s i α P₀ D_m h_parent).f_chart)
            2 ((chartPulledWeightedMeasure (I := I) g α).restrict
                (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * C) *
            diffRHSAggregate (I := I) (M := M)
              g r s i α P₀ m 0 directions := by
  classical
  have h_ae_zero :
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eigenvectorChartRHSDiff (I := I) (M := M)
            g r s i α P₀ m directions
          =ᵐ[(volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α \
              chartPouKernel (I := I) (M := M) α)] (fun _ : EuclN => (0 : ℝ)) :=
    fun i => rhsDiff_ae_zero_off_chartPouKernel (I := I) (M := M)
      g r s i α P₀ m directions
  obtain ⟨Ccmp, hCcmp_nn, hCcmp_bd⟩ :=
    eLpNorm_chartPulledWeighted_le_of_ae_zero_off_chartPouKernel_uniform
      (I := I) (M := M)
      (ι := TensorEigenIdx (I := I) (M := M) g r s) g α h_ae_zero
  obtain ⟨Cvol, hCvol_nn, hCvol_bd⟩ :=
    eigenvectorChartRHSDiff_eLpNorm_le_uniform (I := I) (M := M)
      g r s α P₀ m directions h_pou
  refine ⟨Ccmp * Cvol, mul_nonneg hCcmp_nn hCvol_nn, ?_⟩
  intro i D_m h_fChartEff h_parent
  have h_f_chart_eq :
      (eigenvectorIteratedTensorChartBilinearData_toData
          (I := I) (M := M) g r s i α P₀ D_m h_parent).f_chart =
        eigenvectorChartRHSDiff (I := I) (M := M)
          g r s i α P₀ m directions := by
    change D_m.diffChartForcing =
      eigenvectorChartRHSDiff (I := I) (M := M)
        g r s i α P₀ m directions
    exact h_fChartEff
  rw [h_f_chart_eq]
  calc
    eLpNorm (eigenvectorChartRHSDiff (I := I) (M := M)
            g r s i α P₀ m directions) 2
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal Ccmp *
          eLpNorm (eigenvectorChartRHSDiff (I := I) (M := M)
              g r s i α P₀ m directions) 2
            ((volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α)) := hCcmp_bd i
    _ ≤ ENNReal.ofReal Ccmp *
          (ENNReal.ofReal ((i.fst.val)⁻¹ * Cvol) *
            diffRHSAggregate (I := I) (M := M)
              g r s i α P₀ m 0 directions) :=
          mul_le_mul' (le_refl _) (hCvol_bd i)
    _ = ENNReal.ofReal ((i.fst.val)⁻¹ * (Ccmp * Cvol)) *
          diffRHSAggregate (I := I) (M := M)
            g r s i α P₀ m 0 directions := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hCcmp_nn]
          congr 2
          ring

end MainBoundUnconditional

omit [CompleteSpace E] in
private lemma diffRHSHead_ne_top
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E)) :
    diffRHSHead (I := I) (M := M) g r s i α P₀ m K l
      ≠ (⊤ : ℝ≥0∞) := by
  classical
  have h_iter : ∀ (N j : ℕ) (idx : Fin j → Fin (Module.finrank ℝ E)),
      MemWkp (d := Module.finrank ℝ E) N 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ j idx)
        (chartTargetEuclid (I := I) (M := M) α) := by
    intro N j idx
    have h_comp : MemWkp (d := Module.finrank ℝ E) (N + j) 2
        (eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀)
        (chartTargetEuclid (I := I) (M := M) α) :=
      eigenvector_chartComponent_memWkp_arbitrary (I := I) (M := M)
        g r s i (N + j) α P₀
    exact eigenvectorChartIteratedPartial_memWkp_of_memWkp
      (I := I) (M := M) g r s i α P₀ j N h_comp idx
  rw [diffRHSHead]
  refine ENNReal.add_ne_top.mpr ⟨?_, ?_⟩
  · refine ne_of_lt (ENNReal.sum_lt_top.mpr (fun a _ => ?_))
    exact wkpNorm_lt_top_of_memWkp (d := Module.finrank ℝ E)
      (h_iter (2 + K) (m + 1) (Fin.cons a (Fin.init l)))
  · exact ne_of_lt (wkpNorm_lt_top_of_memWkp (d := Module.finrank ℝ E)
      (h_iter (2 + K) m (Fin.init l)))

omit [CompleteSpace E] in
private lemma rhsZeroAggregate_ne_top
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (K : ℕ)
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    rhsZeroAggregate (I := I) (M := M) g r s i α P₀ K
      ≠ (⊤ : ℝ≥0∞) := by
  classical
  rw [rhsZeroAggregate]
  refine ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr
    ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr
      ⟨ENNReal.add_ne_top.mpr ⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · exact ne_of_lt (wkpNorm_lt_top_of_memWkp (d := Module.finrank ℝ E)
      (eigenvector_chartComponent_memWkp_arbitrary (I := I) (M := M)
        g r s i K α P₀))
  · refine ne_of_lt (ENNReal.sum_lt_top.mpr (fun β _ =>
      ENNReal.add_lt_top.mpr ⟨ENNReal.sum_lt_top.mpr (fun Q _ => ?_),
        ENNReal.sum_lt_top.mpr (fun β' _ =>
          ENNReal.sum_lt_top.mpr (fun Q _ => ?_))⟩))
    · exact wkpNorm_lt_top_of_memWkp (d := Module.finrank ℝ E) (h_pou β Q)
    · exact wkpNorm_lt_top_of_memWkp (d := Module.finrank ℝ E) (h_pou β' Q)
  · refine ne_of_lt (ENNReal.sum_lt_top.mpr (fun β _ =>
      ENNReal.sum_lt_top.mpr (fun Q _ => ?_)))
    exact wkpNorm_lt_top_of_memWkp (d := Module.finrank ℝ E)
      (MemWkp.le_of_le (d := Module.finrank ℝ E)
        (by omega : K ≤ K + 1) (h_pou β Q))
  · refine ne_of_lt (ENNReal.sum_lt_top.mpr (fun P _ =>
      ENNReal.sum_lt_top.mpr (fun k _ => ?_)))
    exact wkpNorm_lt_top_of_memWkp (d := Module.finrank ℝ E)
      (partialLpLimit_memWkp (I := I) (M := M)
        g r s i α P k K h_pou)
  · refine ne_of_lt (ENNReal.sum_lt_top.mpr (fun p _ => ?_))
    exact wkpNorm_lt_top_of_memWkp (d := Module.finrank ℝ E)
      (componentLpLimit_memWkp (I := I) (M := M)
        g r s i α p K h_pou)
  · refine ne_of_lt (ENNReal.sum_lt_top.mpr (fun P _ => ?_))
    exact wkpNorm_lt_top_of_memWkp (d := Module.finrank ℝ E)
      (crossRightLimitComponent_memWkp (I := I) (M := M)
        g r s i α P K h_pou)
  · refine ne_of_lt (ENNReal.sum_lt_top.mpr (fun P _ =>
      ENNReal.sum_lt_top.mpr (fun l _ => ?_)))
    exact wkpNorm_lt_top_of_memWkp (d := Module.finrank ℝ E)
      (cutoffPartialLpLimit_memWkp (I := I) (M := M)
        g r s i α P l K h_pou)

omit [CompleteSpace E] in
theorem diffRHSAggregate_ne_top
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin m → Fin (Module.finrank ℝ E))
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (m + 1 + K) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    diffRHSAggregate (I := I) (M := M) g r s i α P₀ m K l
      ≠ (⊤ : ℝ≥0∞) := by
  classical
  induction m generalizing K with
  | zero =>
      rw [show diffRHSAggregate (I := I) (M := M)
          g r s i α P₀ 0 K l =
        rhsZeroAggregate (I := I) (M := M) g r s i α P₀ K from rfl]
      have h_pou' : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
          MemWkp (d := Module.finrank ℝ E) (K + 1) 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent (I := I) (M := M)
                    g r s i))
                β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β) := by
        intro β Q
        have h_idx : (0 : ℕ) + 1 + K = K + 1 := by omega
        rw [← h_idx]
        exact h_pou β Q
      exact rhsZeroAggregate_ne_top (I := I) (M := M)
        g r s i α P₀ K h_pou'
  | succ m ih =>
      rw [show diffRHSAggregate (I := I) (M := M)
            g r s i α P₀ (m + 1) K l =
          diffRHSHead (I := I) (M := M) g r s i α P₀ m K l +
            diffRHSAggregate (I := I) (M := M)
              g r s i α P₀ m (K + 1) (Fin.init l) from rfl]
      refine ENNReal.add_ne_top.mpr ⟨?_, ?_⟩
      · exact diffRHSHead_ne_top (I := I) (M := M)
          g r s i α P₀ m K l
      · have h_pou_prev : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
            MemWkp (d := Module.finrank ℝ E) (m + 1 + (K + 1)) 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent (I := I) (M := M)
                      g r s i))
                  β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β) := by
          intro β Q
          have h_idx : m + 1 + (K + 1) = m + 1 + 1 + K := by omega
          rw [h_idx]
          exact h_pou β Q
        exact ih (K + 1) (Fin.init l) h_pou_prev

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
