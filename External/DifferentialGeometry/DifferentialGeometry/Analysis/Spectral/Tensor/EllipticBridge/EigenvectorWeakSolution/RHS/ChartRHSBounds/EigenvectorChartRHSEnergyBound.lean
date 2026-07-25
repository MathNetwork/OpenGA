import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.RHS.ChartRHSBounds.EigenvectorChartRHSEpNorm
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.EnergyBound.EigenvectorChartLimitEnergyBounds
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.RHS.ChartRHSBounds.EigenvectorChartRHSMemWkp


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
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Analysis.Laplacian.MetricExtension hiding chartTargetEuclid
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in

omit [CompleteSpace E] in
private lemma eigenvalue_mem_Ioc
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    0 < i.fst.val ∧ i.fst.val ≤ 1 :=
  tensorResolvent_eigenvalue_mem_unit_interval (I := I) (M := M) g r s
    (tensorResolventEigenbasisVec_mem (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s) i)
    (by
      intro h_zero
      have h_norm :
          ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖ = 1 :=
        (tensorResolventEigenbasisVec_orthonormal (I := I) (M := M)
          (g := g) (r := r) (s := s)
          (tensorResolventL2_isCompactOperator (I := I) (M := M)
            g r s)).norm_eq_one i
      rw [h_zero, norm_zero] at h_norm
      exact one_ne_zero h_norm.symm)

omit [CompleteSpace E] in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma eLpNorm_chartPulledWeighted_le_of_ae_zero_off_compact
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ f : EuclN → ℝ,
        f =ᵐ[(volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α \ K)]
            (fun _ : EuclN => (0 : ℝ)) →
        eLpNorm f 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal C *
            eLpNorm f 2
              ((volume : Measure EuclN).restrict
                (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hK_meas : MeasurableSet K := hK_compact.isClosed.measurableSet
  have hΩ_open : IsOpen Ω :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α
  have hV_meas : MeasurableSet (Ω \ K) := hΩ_open.measurableSet.diff hK_meas
  obtain ⟨_c_min, c_max, hc_min_pos, hc_le, h_dens_bd⟩ :=
    densityOnEuclid_bounded_on_compact (I := I) (M := M) g α hK_compact hK_in
  have hc_max_pos : 0 < c_max := lt_of_lt_of_le hc_min_pos hc_le
  have hc_le_meas : (chartPulledWeightedMeasure (I := I) g α).restrict K ≤
      ENNReal.ofReal c_max • ((volume : Measure EuclN).restrict K) := by
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
      exact ENNReal.ofReal_le_ofReal (h_dens_bd y hy.2).2
    have h_const_eval :
        ∫⁻ _y in A ∩ K, ENNReal.ofReal c_max ∂(volume : Measure EuclN) =
        ENNReal.ofReal c_max * (volume : Measure EuclN) (A ∩ K) :=
      MeasureTheory.setLIntegral_const _ _
    rw [smul_eq_mul]
    exact h_pointwise_bd.trans (le_of_eq h_const_eval)
  refine ⟨Real.sqrt c_max, Real.sqrt_nonneg _, fun f hf => ?_⟩
  have hf' : ∀ᵐ y ∂((volume : Measure EuclN).restrict Ω), y ∉ K → f y = 0 := by
    rw [Filter.EventuallyEq, ae_restrict_iff' hV_meas] at hf
    rw [ae_restrict_iff' hΩ_open.measurableSet]
    filter_upwards [hf] with y hy hy_Ω hy_K
    exact hy ⟨hy_Ω, hy_K⟩
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
    eLpNorm_indicator_eq_eLpNorm_restrict hK_meas,
    Measure.restrict_restrict_of_subset hK_in,
    Measure.restrict_restrict_of_subset hK_in]
  have h_mono :
      eLpNorm f 2 ((chartPulledWeightedMeasure (I := I) g α).restrict K)
        ≤ eLpNorm f 2
            (ENNReal.ofReal c_max • ((volume : Measure EuclN).restrict K)) :=
    eLpNorm_mono_measure f hc_le_meas
  refine h_mono.trans ?_
  rw [eLpNorm_smul_measure_of_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
  have h_toReal : ((1 / 2 : ℝ≥0∞).toReal : ℝ) = (1 : ℝ) / 2 := by
    rw [show (1 / 2 : ℝ≥0∞) = (1 : ℝ≥0∞) / 2 from rfl]; simp
  rw [h_toReal]
  have h_pow_eq : ENNReal.ofReal c_max ^ ((1 : ℝ) / 2) =
      ENNReal.ofReal (Real.sqrt c_max) := by
    rw [Real.sqrt_eq_rpow,
      ← ENNReal.ofReal_rpow_of_nonneg hc_max_pos.le (by positivity)]
  rw [h_pow_eq, smul_eq_mul]

omit [CompleteSpace E] in

omit [NeZero (Module.finrank ℝ E)] in
private lemma tensorL2ChartComponent_aeEq_zero_off_chartPouKernel
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (u : TensorL2 r s g) (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    (fun y => (tensorL2ChartComponent (I := I) (M := M) g r s u α P₀ :
        EuclN → ℝ) y)
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α)] (fun _ : EuclN => (0 : ℝ)) := by
  classical
  have hK_meas : MeasurableSet (chartPouKernel (I := I) (M := M) α) :=
    chartPouKernel_measurableSet (I := I) (M := M) α
  have hΩ_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α).measurableSet
  have hV_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α \
      chartPouKernel (I := I) (M := M) α) := hΩ_meas.diff hK_meas
  have h_ae := tensorL2ChartComponent_ae_zero_off_chartPouKernel
    (I := I) (M := M) g r s u α P₀
  have h_ae_v : ∀ᵐ y ∂(volume : Measure EuclN), y ∈
        chartTargetEuclid (I := I) (M := M) α →
      y ∉ chartPouKernel (I := I) (M := M) α →
        (tensorL2ChartComponent (I := I) (M := M) g r s u α P₀ :
          EuclN → ℝ) y = 0 :=
    (ae_restrict_iff' hΩ_meas).mp h_ae
  rw [Filter.EventuallyEq, ae_restrict_iff' hV_meas]
  filter_upwards [h_ae_v] with y hy hy_mem
  exact hy hy_mem.1 hy_mem.2

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 800000 in

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem eLpNorm_tensorL2ChartComponent_le_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : TensorL2 r s g,
        eLpNorm ((tensorL2ChartComponent (I := I) (M := M) g r s u α P₀ :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal C * ENNReal.ofReal ‖u‖ := by
  classical
  obtain ⟨Ccmp, hCcmp_nn, hCcmp_bd⟩ :=
    eLpNorm_chartPulledWeighted_le_of_ae_zero_off_compact (I := I) (M := M) g α
      (chartPouKernel_isCompact (I := I) (M := M) α)
      (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
  set Cop : ℝ := ‖tensorL2ChartComponentCLM (I := I) (M := M) g r s α P₀‖
    with hCop_def
  have hCop_nn : 0 ≤ Cop :=
    norm_nonneg (tensorL2ChartComponentCLM (I := I) (M := M) g r s α P₀)
  refine ⟨Ccmp * Cop, mul_nonneg hCcmp_nn hCop_nn, fun u => ?_⟩
  have h_off := tensorL2ChartComponent_aeEq_zero_off_chartPouKernel
    (I := I) (M := M) g r s u α P₀
  have h_eLp_eq :
      eLpNorm ((tensorL2ChartComponent (I := I) (M := M) g r s u α P₀ :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)) =
        ENNReal.ofReal ‖tensorL2ChartComponent (I := I) (M := M) g r s u α P₀‖ := by
    rw [show (volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α) =
        chartL2Measure (I := I) (M := M) α from rfl,
      Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]
  have h_op : ‖tensorL2ChartComponent (I := I) (M := M) g r s u α P₀‖ ≤
      Cop * ‖u‖ := by
    rw [hCop_def,
      ← tensorL2ChartComponentCLM_apply (I := I) (M := M) g r s α P₀ u]
    exact (tensorL2ChartComponentCLM (I := I) (M := M) g r s α P₀).le_opNorm u
  calc eLpNorm ((tensorL2ChartComponent (I := I) (M := M) g r s u α P₀ :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))
      ≤ ENNReal.ofReal Ccmp *
          eLpNorm ((tensorL2ChartComponent (I := I) (M := M) g r s u α P₀ :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
            ((volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α)) :=
        hCcmp_bd _ h_off
    _ = ENNReal.ofReal Ccmp *
          ENNReal.ofReal
            ‖tensorL2ChartComponent (I := I) (M := M) g r s u α P₀‖ := by
        rw [h_eLp_eq]
    _ ≤ ENNReal.ofReal Ccmp * ENNReal.ofReal (Cop * ‖u‖) := by
        gcongr
    _ = ENNReal.ofReal (Ccmp * Cop) * ENNReal.ofReal ‖u‖ := by
        rw [ENNReal.ofReal_mul hCop_nn, ENNReal.ofReal_mul hCcmp_nn, mul_assoc]

section AtomBoundsUnconditional

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

omit [CompleteSpace E] in
private lemma eigenvectorChartComponentFun_eLpNorm_le_energy
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
            g r s i α P₀) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal C *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖ := by
  obtain ⟨C, hC_nn, hC_bd⟩ := eLpNorm_tensorL2ChartComponent_le_uniform
    (I := I) (M := M) g r s α P₀
  exact ⟨C, hC_nn, fun i => hC_bd
    (tensorResolventEigenbasisVec (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s) i)⟩

omit [CompleteSpace E] in
private lemma crossLeftLimitComponent_eLpNorm_le_energy
    (α : M) (P : TensorCompIdx (E := E) r (s + 1)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm ((crossLeftLimitComponent (I := I) (M := M)
            g r s i α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal (C * Real.sqrt i.fst.val) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖ := by
  obtain ⟨C, hC_nn, hC_bd⟩ := eLpNorm_crossLeftLimitComponent_le_uniform
    (I := I) (M := M) g r s α P
  refine ⟨C, hC_nn, fun i => ?_⟩
  refine (hC_bd i).trans ?_
  rw [ENNReal.ofReal_mul hC_nn]
  refine le_trans (mul_le_mul' (le_refl _)
    (ENNReal.ofReal_le_ofReal
      (tensorCovGradL2Compl_eigenvectorResolvent_l2Norm_le
        (I := I) (M := M) g r s i))) ?_
  rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _), ← mul_assoc]

omit [CompleteSpace E] in
private lemma crossRightLimitComponent_eLpNorm_le_energy
    (α : M) (P : TensorCompIdx (E := E) r s) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm ((crossRightLimitComponent (I := I) (M := M)
            g r s i α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal (C * i.fst.val) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖ := by
  obtain ⟨C, hC_nn, hC_bd⟩ := eLpNorm_crossRightLimitComponent_le_uniform
    (I := I) (M := M) g r s α P
  refine ⟨C, hC_nn, fun i => ?_⟩
  have hμ_nn : 0 ≤ i.fst.val :=
    le_of_lt (eigenvalue_mem_Ioc (I := I) (M := M) g r s i).1
  have h_l2 : TensorH1ComplToTensorL2 (I := I) (M := M) g r s
      (eigenvectorResolvent (I := I) (M := M) g r s i) =
      i.fst.val •
        tensorResolventEigenbasisVec (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M)
            g r s) i := by
    rw [eigenvectorResolvent,
      ← tensorResolventL2_apply (I := I) (M := M) g r s]
    exact (mem_tensorResolventEigenspace_iff (I := I) (M := M) g r s i.fst.val
        (tensorResolventEigenbasisVec (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M)
            g r s) i)).mp
      (tensorResolventEigenbasisVec_mem (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M)
          g r s) i)
  have h_norm : ‖TensorH1ComplToTensorL2 (I := I) (M := M) g r s
        (eigenvectorResolvent (I := I) (M := M) g r s i)‖ =
      i.fst.val *
        ‖tensorResolventEigenbasisVec (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M)
            g r s) i‖ := by
    rw [h_l2, norm_smul, Real.norm_eq_abs, abs_of_nonneg hμ_nn]
  refine (hC_bd i).trans ?_
  rw [h_norm, ENNReal.ofReal_mul hC_nn, ENNReal.ofReal_mul hμ_nn, mul_assoc]

omit [CompleteSpace E] in
private lemma partialLpLimit_eLpNorm_le_energy
    (α : M) (P : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm ((partialLpLimit (I := I) (M := M)
            g r s i α P k :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal (C * Real.sqrt i.fst.val) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖ := by
  classical
  obtain ⟨Ccmp, hCcmp_nn, hCcmp_bd⟩ :=
    eLpNorm_chartPulledWeighted_le_of_ae_zero_off_compact (I := I) (M := M) g α
      (chartPouKernel_isCompact (I := I) (M := M) α)
      (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
  obtain ⟨Cvol, hCvol_nn, hCvol_bd⟩ :=
    partialLpLimit_eLpNorm_le (I := I) (M := M) g r s α P k
  refine ⟨Ccmp * Cvol, mul_nonneg hCcmp_nn hCvol_nn, fun i => ?_⟩
  have h_off : (fun y => ((partialLpLimit (I := I) (M := M)
        g r s i α P k :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α)] (fun _ : EuclN => (0 : ℝ)) := by
    have h_smul : (fun y => ((partialLpLimit (I := I) (M := M)
          g r s i α P k :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
        =ᵐ[(volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α \
            chartPouKernel (I := I) (M := M) α)]
        (fun y => i.fst.val •
          eigenvectorChartWeakPartial (I := I) (M := M)
            g r s i α P k y) := by
      have h_ac : (volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α \
            chartPouKernel (I := I) (M := M) α) ≪
          chartL2Measure (I := I) (M := M) α := by
        rw [show chartL2Measure (I := I) (M := M) α =
            (volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α) from rfl]
        exact Measure.absolutelyContinuous_of_le
          (Measure.restrict_mono Set.diff_subset le_rfl)
      refine h_ac.ae_eq ?_
      rw [partialLpLimit, eigenvectorChartWeakPartial]
      exact Lp.coeFn_smul i.fst.val _
    have h_weak := eigenvectorChartWeakPartial_ae_zero_off_chartPouKernel
      (I := I) (M := M) g r s i α P k
    filter_upwards [h_smul, h_weak] with y hy hy_zero
    rw [hy, hy_zero, smul_zero]
  refine le_trans (hCcmp_bd _ h_off) ?_
  refine le_trans (mul_le_mul' (le_refl _) (hCvol_bd i)) (le_of_eq ?_)
  rw [← mul_assoc, ← ENNReal.ofReal_mul hCcmp_nn,
    show Ccmp * (Cvol * Real.sqrt i.fst.val) =
      Ccmp * Cvol * Real.sqrt i.fst.val from (mul_assoc _ _ _).symm]

omit [CompleteSpace E] in
private lemma componentLpLimit_eLpNorm_le_energy
    (α : M) (P : TensorCompIdx (E := E) r s) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm ((componentLpLimit (I := I) (M := M)
            g r s i α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal (C * i.fst.val) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖ := by
  classical
  obtain ⟨C, hC_nn, hC_bd⟩ := eLpNorm_tensorL2ChartComponent_le_uniform
    (I := I) (M := M) g r s α P
  refine ⟨C, hC_nn, fun i => ?_⟩
  set μw : Measure EuclN :=
    (chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α) with hμw_def
  have hμ_nn : 0 ≤ i.fst.val :=
    le_of_lt (eigenvalue_mem_Ioc (I := I) (M := M) g r s i).1
  have h_smul : (fun y => ((componentLpLimit (I := I) (M := M)
        g r s i α P :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      =ᵐ[μw]
      i.fst.val •
        (((tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M)
              g r s) i) α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ)) := by
    have h_ac : μw ≪ chartL2Measure (I := I) (M := M) α := by
      rw [hμw_def]
      exact chartPulledWeightedMeasure_restrict_absolutelyContinuous
        (I := I) (M := M) g α
    refine h_ac.ae_eq ?_
    rw [componentLpLimit]
    exact Lp.coeFn_smul i.fst.val _
  rw [eLpNorm_congr_ae h_smul]
  rw [eLpNorm_const_smul (μ := μw) (p := 2) i.fst.val
    (((tensorL2ChartComponent (I := I) (M := M) g r s
        (tensorResolventEigenbasisVec (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M)
            g r s) i) α P :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ)),
    Real.enorm_of_nonneg hμ_nn]
  refine le_trans (mul_le_mul' (le_refl _) (hC_bd
    (tensorResolventEigenbasisVec (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M)
        g r s) i))) (le_of_eq ?_)
  rw [← mul_assoc, ← ENNReal.ofReal_mul hμ_nn, mul_comm i.fst.val C]

omit [CompleteSpace E] in
private lemma cutoffPartialLpLimit_eLpNorm_le_energy
    (α : M) (P : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm ((cutoffPartialLpLimit (I := I) (M := M)
            g r s i α P k :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal (C * Real.sqrt i.fst.val) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖ := by
  classical
  obtain ⟨Ccmp, hCcmp_nn, hCcmp_bd⟩ :=
    eLpNorm_chartPulledWeighted_le_of_ae_zero_off_compact (I := I) (M := M) g α
      (cutoffChartKernelEuclid_isCompact (I := I) (M := M) α)
      (cutoffChartKernelEuclid_subset_chartTargetEuclid (I := I) (M := M) α)
  obtain ⟨Cvol, hCvol_nn, hCvol_bd⟩ :=
    cutoffPartialLpLimit_eLpNorm_le (I := I) (M := M) g r s α P k
  refine ⟨Ccmp * Cvol, mul_nonneg hCcmp_nn hCvol_nn, fun i => ?_⟩
  have h_off : (fun y => ((cutoffPartialLpLimit (I := I) (M := M)
        g r s i α P k :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          cutoffChartKernelEuclid (I := I) (M := M) α)]
        (fun _ : EuclN => (0 : ℝ)) := by
    have hKc_meas : MeasurableSet (cutoffChartKernelEuclid (I := I) (M := M) α) :=
      cutoffChartKernelEuclid_measurableSet (I := I) (M := M) α
    have hΩ_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
        (I := I) (M := M) α).measurableSet
    have hV_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α \
        cutoffChartKernelEuclid (I := I) (M := M) α) := hΩ_meas.diff hKc_meas
    have h_ae := cutoffPartialLpLimit_ae_zero_off_cutoffChartKernelEuclid
      (I := I) (M := M) g r s i α P k
    have h_ae_v : ∀ᵐ y ∂(volume : Measure EuclN), y ∈
          chartTargetEuclid (I := I) (M := M) α →
        y ∉ cutoffChartKernelEuclid (I := I) (M := M) α →
          ((cutoffPartialLpLimit (I := I) (M := M)
              g r s i α P k :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y = 0 :=
      (ae_restrict_iff' hΩ_meas).mp h_ae
    rw [Filter.EventuallyEq, ae_restrict_iff' hV_meas]
    filter_upwards [h_ae_v] with y hy hy_mem
    exact hy hy_mem.1 hy_mem.2
  refine le_trans (hCcmp_bd _ h_off) ?_
  refine le_trans (mul_le_mul' (le_refl _) (hCvol_bd i)) (le_of_eq ?_)
  rw [← mul_assoc, ← ENNReal.ofReal_mul hCcmp_nn,
    show Ccmp * (Cvol * Real.sqrt i.fst.val) =
      Ccmp * Cvol * Real.sqrt i.fst.val from (mul_assoc _ _ _).symm]

end AtomBoundsUnconditional

private lemma ofReal_mul_muPow_le_ofReal {C μ : ℝ} (hC : 0 ≤ C)
    (hμ_le : μ ≤ 1) :
    ENNReal.ofReal (C * Real.sqrt μ) ≤ ENNReal.ofReal C ∧
      ENNReal.ofReal (C * μ) ≤ ENNReal.ofReal C := by
  have h_sqrt_le : Real.sqrt μ ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_le_sqrt hμ_le
  refine ⟨ENNReal.ofReal_le_ofReal ?_, ENNReal.ofReal_le_ofReal ?_⟩
  · calc C * Real.sqrt μ ≤ C * 1 :=
          mul_le_mul_of_nonneg_left h_sqrt_le hC
      _ = C := mul_one C
  · calc C * μ ≤ C * 1 := mul_le_mul_of_nonneg_left hμ_le hC
      _ = C := mul_one C

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1600000 in
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in

omit [CompleteSpace E] in
theorem eigenvectorChartRHS_eLpNorm_le_energy
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm (eigenvectorChartRHS (I := I) (M := M)
            g r s i α P₀) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal (C * (i.fst.val)⁻¹) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖ := by
  classical
  obtain ⟨Crhs, hCrhs_nn, hCrhs_bd⟩ :=
    eigenvectorChartRHS_eLpNorm_le_uniform_unconditional (I := I) (M := M)
      g r s α P₀
  obtain ⟨C1, hC1_nn, hC1_bd⟩ :=
    eigenvectorChartComponentFun_eLpNorm_le_energy
      (I := I) (M := M) g r s α P₀
  choose C2 hC2_nn hC2_bd using fun P : TensorCompIdx (E := E) r (s + 1) =>
    crossLeftLimitComponent_eLpNorm_le_energy (I := I) (M := M)
      g r s α P
  choose C3 hC3_nn hC3_bd using fun P : TensorCompIdx (E := E) r s =>
    crossRightLimitComponent_eLpNorm_le_energy (I := I) (M := M)
      g r s α P
  choose C4 hC4_nn hC4_bd using
    fun (P : TensorCompIdx (E := E) r s) (k : Fin (Module.finrank ℝ E)) =>
      partialLpLimit_eLpNorm_le_energy (I := I) (M := M)
        g r s α P k
  choose C5 hC5_nn hC5_bd using fun P : TensorCompIdx (E := E) r s =>
    componentLpLimit_eLpNorm_le_energy (I := I) (M := M)
      g r s α P
  choose C6 hC6_nn hC6_bd using
    fun (P : TensorCompIdx (E := E) r s) (l : Fin (Module.finrank ℝ E)) =>
      cutoffPartialLpLimit_eLpNorm_le_energy (I := I) (M := M)
        g r s α P l
  set Cagg : ℝ :=
    C1
      + ∑ P : TensorCompIdx (E := E) r (s + 1), C2 P
      + ∑ P : TensorCompIdx (E := E) r s, C3 P
      + ∑ P : TensorCompIdx (E := E) r s, ∑ k : Fin (Module.finrank ℝ E), C4 P k
      + ∑ P : TensorCompIdx (E := E) r s, C5 P
      + ∑ P : TensorCompIdx (E := E) r s, ∑ l : Fin (Module.finrank ℝ E), C6 P l
    with hCagg_def
  have hCagg_nn : 0 ≤ Cagg := by
    rw [hCagg_def]
    have h2 : 0 ≤ ∑ P : TensorCompIdx (E := E) r (s + 1), C2 P :=
      Finset.sum_nonneg (fun P _ => hC2_nn P)
    have h3 : 0 ≤ ∑ P : TensorCompIdx (E := E) r s, C3 P :=
      Finset.sum_nonneg (fun P _ => hC3_nn P)
    have h4 : 0 ≤ ∑ P : TensorCompIdx (E := E) r s,
        ∑ k : Fin (Module.finrank ℝ E), C4 P k :=
      Finset.sum_nonneg (fun P _ => Finset.sum_nonneg (fun k _ => hC4_nn P k))
    have h5 : 0 ≤ ∑ P : TensorCompIdx (E := E) r s, C5 P :=
      Finset.sum_nonneg (fun P _ => hC5_nn P)
    have h6 : 0 ≤ ∑ P : TensorCompIdx (E := E) r s,
        ∑ l : Fin (Module.finrank ℝ E), C6 P l :=
      Finset.sum_nonneg (fun P _ => Finset.sum_nonneg (fun l _ => hC6_nn P l))
    positivity
  refine ⟨Crhs * Cagg, mul_nonneg hCrhs_nn hCagg_nn, fun i => ?_⟩
  set μw : Measure EuclN :=
    (chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α) with hμw_def
  obtain ⟨hμ_pos, hμ_le⟩ :=
    eigenvalue_mem_Ioc (I := I) (M := M) g r s i
  have hμ_inv_nn : 0 ≤ (i.fst.val)⁻¹ := le_of_lt (inv_pos.mpr hμ_pos)
  set φnorm : ℝ :=
    ‖tensorResolventEigenbasisVec (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M)
        g r s) i‖ with hφnorm_def
  have hφnorm_nn : 0 ≤ φnorm := norm_nonneg _
  set Rhs : ℝ≥0∞ := ENNReal.ofReal φnorm with hRhs_def
  have hA1 :
      eLpNorm (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
          g r s i α P₀) 2 μw
        ≤ ENNReal.ofReal C1 * Rhs := hC1_bd i
  have hfold := fun {C : ℝ} (hC : 0 ≤ C) =>
    ofReal_mul_muPow_le_ofReal (C := C) (μ := i.fst.val) hC hμ_le
  have hA2 : ∀ P : TensorCompIdx (E := E) r (s + 1),
      eLpNorm ((crossLeftLimitComponent (I := I) (M := M)
          g r s i α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2 μw
        ≤ ENNReal.ofReal (C2 P) * Rhs := fun P =>
    le_trans (hC2_bd P i)
      (mul_le_mul' (hfold (hC2_nn P)).1 (le_refl _))
  have hA3 : ∀ P : TensorCompIdx (E := E) r s,
      eLpNorm ((crossRightLimitComponent (I := I) (M := M)
          g r s i α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2 μw
        ≤ ENNReal.ofReal (C3 P) * Rhs := fun P =>
    le_trans (hC3_bd P i)
      (mul_le_mul' (hfold (hC3_nn P)).2 (le_refl _))
  have hA4 : ∀ (P : TensorCompIdx (E := E) r s)
      (k : Fin (Module.finrank ℝ E)),
      eLpNorm ((partialLpLimit (I := I) (M := M)
          g r s i α P k :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2 μw
        ≤ ENNReal.ofReal (C4 P k) * Rhs := fun P k =>
    le_trans (hC4_bd P k i)
      (mul_le_mul' (hfold (hC4_nn P k)).1 (le_refl _))
  have hA5 : ∀ P : TensorCompIdx (E := E) r s,
      eLpNorm ((componentLpLimit (I := I) (M := M)
          g r s i α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2 μw
        ≤ ENNReal.ofReal (C5 P) * Rhs := fun P =>
    le_trans (hC5_bd P i)
      (mul_le_mul' (hfold (hC5_nn P)).2 (le_refl _))
  have hA6 : ∀ (P : TensorCompIdx (E := E) r s)
      (l : Fin (Module.finrank ℝ E)),
      eLpNorm ((cutoffPartialLpLimit (I := I) (M := M)
          g r s i α P l :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2 μw
        ≤ ENNReal.ofReal (C6 P l) * Rhs := fun P l =>
    le_trans (hC6_bd P l i)
      (mul_le_mul' (hfold (hC6_nn P l)).1 (le_refl _))
  have h_sum2 : (∑ P : TensorCompIdx (E := E) r (s + 1),
        eLpNorm ((crossLeftLimitComponent (I := I) (M := M)
          g r s i α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2 μw)
      ≤ ENNReal.ofReal (∑ P : TensorCompIdx (E := E) r (s + 1), C2 P) * Rhs := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun P _ => hC2_nn P), Finset.sum_mul]
    exact Finset.sum_le_sum (fun P _ => hA2 P)
  have h_sum3 : (∑ P : TensorCompIdx (E := E) r s,
        eLpNorm ((crossRightLimitComponent (I := I) (M := M)
          g r s i α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2 μw)
      ≤ ENNReal.ofReal (∑ P : TensorCompIdx (E := E) r s, C3 P) * Rhs := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun P _ => hC3_nn P), Finset.sum_mul]
    exact Finset.sum_le_sum (fun P _ => hA3 P)
  have h_sum4 : (∑ P : TensorCompIdx (E := E) r s,
        ∑ k : Fin (Module.finrank ℝ E),
          eLpNorm ((partialLpLimit (I := I) (M := M)
            g r s i α P k :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2 μw)
      ≤ ENNReal.ofReal (∑ P : TensorCompIdx (E := E) r s,
          ∑ k : Fin (Module.finrank ℝ E), C4 P k) * Rhs := by
    rw [ENNReal.ofReal_sum_of_nonneg
        (fun P _ => Finset.sum_nonneg (fun k _ => hC4_nn P k)), Finset.sum_mul]
    refine Finset.sum_le_sum (fun P _ => ?_)
    rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => hC4_nn P k), Finset.sum_mul]
    exact Finset.sum_le_sum (fun k _ => hA4 P k)
  have h_sum5 : (∑ P : TensorCompIdx (E := E) r s,
        eLpNorm ((componentLpLimit (I := I) (M := M)
          g r s i α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2 μw)
      ≤ ENNReal.ofReal (∑ P : TensorCompIdx (E := E) r s, C5 P) * Rhs := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun P _ => hC5_nn P), Finset.sum_mul]
    exact Finset.sum_le_sum (fun P _ => hA5 P)
  have h_sum6 : (∑ P : TensorCompIdx (E := E) r s,
        ∑ l : Fin (Module.finrank ℝ E),
          eLpNorm ((cutoffPartialLpLimit (I := I) (M := M)
            g r s i α P l :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2 μw)
      ≤ ENNReal.ofReal (∑ P : TensorCompIdx (E := E) r s,
          ∑ l : Fin (Module.finrank ℝ E), C6 P l) * Rhs := by
    rw [ENNReal.ofReal_sum_of_nonneg
        (fun P _ => Finset.sum_nonneg (fun l _ => hC6_nn P l)), Finset.sum_mul]
    refine Finset.sum_le_sum (fun P _ => ?_)
    rw [ENNReal.ofReal_sum_of_nonneg (fun l _ => hC6_nn P l), Finset.sum_mul]
    exact Finset.sum_le_sum (fun l _ => hA6 P l)
  have h_aggr :
      eLpNorm (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
            g r s i α P₀) 2 μw
          + (∑ P : TensorCompIdx (E := E) r (s + 1),
              eLpNorm ((crossLeftLimitComponent (I := I) (M := M)
                g r s i α P :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2 μw)
          + (∑ P : TensorCompIdx (E := E) r s,
              eLpNorm ((crossRightLimitComponent (I := I) (M := M)
                g r s i α P :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2 μw)
          + (∑ P : TensorCompIdx (E := E) r s,
              ∑ k : Fin (Module.finrank ℝ E),
                eLpNorm ((partialLpLimit (I := I) (M := M)
                  g r s i α P k :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                  EuclN → ℝ) 2 μw)
          + (∑ P : TensorCompIdx (E := E) r s,
              eLpNorm ((componentLpLimit (I := I) (M := M)
                g r s i α P :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2 μw)
          + (∑ P : TensorCompIdx (E := E) r s,
              ∑ l : Fin (Module.finrank ℝ E),
                eLpNorm ((cutoffPartialLpLimit (I := I) (M := M)
                  g r s i α P l :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                  EuclN → ℝ) 2 μw)
        ≤ ENNReal.ofReal Cagg * Rhs := by
    have hS2 : 0 ≤ ∑ P : TensorCompIdx (E := E) r (s + 1), C2 P :=
      Finset.sum_nonneg (fun P _ => hC2_nn P)
    have hS3 : 0 ≤ ∑ P : TensorCompIdx (E := E) r s, C3 P :=
      Finset.sum_nonneg (fun P _ => hC3_nn P)
    have hS4 : 0 ≤ ∑ P : TensorCompIdx (E := E) r s,
        ∑ k : Fin (Module.finrank ℝ E), C4 P k :=
      Finset.sum_nonneg (fun P _ => Finset.sum_nonneg (fun k _ => hC4_nn P k))
    have hS5 : 0 ≤ ∑ P : TensorCompIdx (E := E) r s, C5 P :=
      Finset.sum_nonneg (fun P _ => hC5_nn P)
    have hS6 : 0 ≤ ∑ P : TensorCompIdx (E := E) r s,
        ∑ l : Fin (Module.finrank ℝ E), C6 P l :=
      Finset.sum_nonneg (fun P _ => Finset.sum_nonneg (fun l _ => hC6_nn P l))
    rw [hCagg_def]
    rw [ENNReal.ofReal_add (by positivity) hS6,
      ENNReal.ofReal_add (by positivity) hS5,
      ENNReal.ofReal_add (by positivity) hS4,
      ENNReal.ofReal_add (by positivity) hS3,
      ENNReal.ofReal_add hC1_nn hS2]
    rw [add_mul, add_mul, add_mul, add_mul, add_mul]
    refine add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
      ?_ h_sum2) h_sum3) h_sum4) h_sum5) h_sum6
    exact hA1
  refine le_trans (hCrhs_bd i) ?_
  refine le_trans (mul_le_mul' (le_refl _) h_aggr) (le_of_eq ?_)
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), hRhs_def, hφnorm_def,
    show (i.fst.val)⁻¹ * Crhs * Cagg = Crhs * Cagg * (i.fst.val)⁻¹ by ring]

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
