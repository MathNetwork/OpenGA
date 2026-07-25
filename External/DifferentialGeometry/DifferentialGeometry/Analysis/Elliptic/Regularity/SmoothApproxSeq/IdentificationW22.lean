import DifferentialGeometry.Analysis.Elliptic.Regularity.SmoothApproxSeq.CauchyW22
import DifferentialGeometry.Analysis.Elliptic.Regularity.SmoothApproxSeq.H1ComplTendsto
import DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.ResidualRegularity.BilinearH1ComplResidual


noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace SmoothApproxSeqIdentificationW22

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainChartData
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplResidual
open DifferentialGeometry.Analysis.Laplacian.SmoothApproxSeqCauchyW22
open DifferentialGeometry.Analysis.Laplacian.SmoothApproxSeqH1ComplTendsto
open DifferentialGeometry.Analysis.Sobolev.Chart

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
private lemma wkpNormChart_one_le_three
    (g : SmoothRiemannianMetric I M) (u : M → ℝ) :
    wkpNormChart (I := I) (M := M) g 1 2 u ≤
      wkpNormChart (I := I) (M := M) g 3 2 u := by
  calc wkpNormChart (I := I) (M := M) g 1 2 u
      ≤ wkpNormChart (I := I) (M := M) g 2 2 u :=
        wkpNormChart_le_succ (I := I) (M := M) g 1 2 u
    _ ≤ wkpNormChart (I := I) (M := M) g 3 2 u :=
        wkpNormChart_le_succ (I := I) (M := M) g 2 2 u

private theorem smoothApproxSeqWkpThree_cauchy_smoothScalar
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    CauchySeq (fun n =>
      smoothApproxSeqWkpThree (I := I) (M := M) g hu_h n) := by
  classical
  obtain ⟨C, hC_nn, hC_bnd⟩ :=
    norm_smoothScalar_le_const_mul_wkpNormChart_one (I := I) (M := M) g
  rw [Metric.cauchySeq_iff]
  intro ε hε_pos
  set Cp1 : ℝ := C + 1 with hCp1_def
  have hCp1_pos : 0 < Cp1 := by linarith
  set ε' : ℝ := ε / (2 * Cp1) with hε'_def
  have hε'_pos : 0 < ε' := by positivity
  obtain ⟨N0, hN0_real⟩ := exists_nat_gt (1 / ε' - 1)
  have hN1_pos : (0 : ℝ) < (N0 : ℝ) + 1 := by
    have h_pos : 0 < 1 / ε' := by positivity
    linarith
  have hN0_inv_le : (1 : ℝ) / ((N0 : ℝ) + 1) ≤ ε' := by
    rw [div_le_iff₀ hN1_pos]
    have h1 : (1 : ℝ) = ε' * (1 / ε') := by
      rw [mul_one_div, div_self hε'_pos.ne']
    rw [h1]
    apply mul_le_mul_of_nonneg_left _ hε'_pos.le
    linarith
  refine ⟨N0, ?_⟩
  intro m hm n hn
  set vm : SmoothScalar g := smoothApproxSeqWkpThree (I := I) (M := M) g hu_h m
    with hvm_def
  set vn : SmoothScalar g := smoothApproxSeqWkpThree (I := I) (M := M) g hu_h n
    with hvn_def
  rw [dist_eq_norm]
  set vdiff : SmoothScalar g := vm - vn with hvdiff_def
  have hvdiff_toFun : vdiff.toFun = fun x => vm.toFun x - vn.toFun x := by
    rw [hvdiff_def]; rfl
  have h_wkpNormChart_finite :
      wkpNormChart (I := I) (M := M) g 1 2 vdiff.toFun ≠ ⊤ := by
    rw [hvdiff_toFun]
    exact wkpNormChart_one_two_smoothScalar_diff_ne_top (I := I) (M := M) g vm vn
  have h_norm_bd : ‖vdiff‖ ≤ C *
      (wkpNormChart (I := I) (M := M) g 1 2 vdiff.toFun).toReal :=
    hC_bnd vdiff h_wkpNormChart_finite
  have h_wkp_chart_3_2 :
      wkpNormChart (I := I) (M := M) g 3 2 vdiff.toFun ≤
        ENNReal.ofReal (1 / ((m : ℝ) + 1)) +
          ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
    rw [hvdiff_toFun]
    exact smoothApproxSeqWkpThree_wkpNormChart_diff_le (I := I) (M := M) g hu_h m n
  have h_wkp_chart_1_2 :
      wkpNormChart (I := I) (M := M) g 1 2 vdiff.toFun ≤
        ENNReal.ofReal (1 / ((m : ℝ) + 1)) +
          ENNReal.ofReal (1 / ((n : ℝ) + 1)) :=
    (wkpNormChart_one_le_three (I := I) (M := M) g vdiff.toFun).trans h_wkp_chart_3_2
  have h_sum_finite :
      ENNReal.ofReal (1 / ((m : ℝ) + 1)) +
        ENNReal.ofReal (1 / ((n : ℝ) + 1)) ≠ ⊤ := by
    apply ENNReal.add_ne_top.mpr
    exact ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩
  have h_inv_m_nn : (0 : ℝ) ≤ 1 / ((m : ℝ) + 1) := by positivity
  have h_inv_n_nn : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) := by positivity
  have h_sum_toReal :
      (ENNReal.ofReal (1 / ((m : ℝ) + 1)) +
            ENNReal.ofReal (1 / ((n : ℝ) + 1))).toReal =
        1 / ((m : ℝ) + 1) + 1 / ((n : ℝ) + 1) := by
    rw [ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top]
    rw [ENNReal.toReal_ofReal h_inv_m_nn, ENNReal.toReal_ofReal h_inv_n_nn]
  have h_wkp_toReal_le :
      (wkpNormChart (I := I) (M := M) g 1 2 vdiff.toFun).toReal ≤
        1 / ((m : ℝ) + 1) + 1 / ((n : ℝ) + 1) := by
    have h_mono := ENNReal.toReal_mono h_sum_finite h_wkp_chart_1_2
    rwa [h_sum_toReal] at h_mono
  have hN0m : (N0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hN0n : (N0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hm1_pos : (0 : ℝ) < (m : ℝ) + 1 := by linarith
  have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have hm_inv_le : (1 : ℝ) / ((m : ℝ) + 1) ≤ (1 : ℝ) / ((N0 : ℝ) + 1) := by
    apply div_le_div_of_nonneg_left zero_le_one hN1_pos
    linarith
  have hn_inv_le : (1 : ℝ) / ((n : ℝ) + 1) ≤ (1 : ℝ) / ((N0 : ℝ) + 1) := by
    apply div_le_div_of_nonneg_left zero_le_one hN1_pos
    linarith
  have h_sum_le : 1 / ((m : ℝ) + 1) + 1 / ((n : ℝ) + 1) ≤ 2 * (1 / ((N0 : ℝ) + 1)) := by
    linarith
  have h_wkp_toReal_le_2N : (wkpNormChart (I := I) (M := M) g 1 2 vdiff.toFun).toReal ≤
        2 * (1 / ((N0 : ℝ) + 1)) :=
    h_wkp_toReal_le.trans h_sum_le
  have h_final : C * (wkpNormChart (I := I) (M := M) g 1 2 vdiff.toFun).toReal ≤
      C * (2 * (1 / ((N0 : ℝ) + 1))) := by
    apply mul_le_mul_of_nonneg_left h_wkp_toReal_le_2N hC_nn
  have h_2N_le : 2 * (1 / ((N0 : ℝ) + 1)) ≤ 2 * ε' := by
    apply mul_le_mul_of_nonneg_left hN0_inv_le (by norm_num : (0 : ℝ) ≤ 2)
  have h_step1 : C * (wkpNormChart (I := I) (M := M) g 1 2 vdiff.toFun).toReal ≤
      C * (2 * ε') := by
    refine h_final.trans ?_
    exact mul_le_mul_of_nonneg_left h_2N_le hC_nn
  refine lt_of_le_of_lt (h_norm_bd.trans h_step1) ?_
  rw [hε'_def]
  have h1 : C * (2 * (ε / (2 * Cp1))) = C * ε / Cp1 := by
    field_simp
  rw [h1]
  rw [div_lt_iff₀ hCp1_pos]
  have hC_lt_Cp1 : C < Cp1 := by rw [hCp1_def]; linarith
  nlinarith [hε_pos]

private theorem smoothToH1Compl_smoothApproxSeqWkpThree_cauchy
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    CauchySeq (fun n =>
      smoothToH1Compl (I := I) (M := M) g
        (smoothApproxSeqWkpThree (I := I) (M := M) g hu_h n)) := by
  have h_cauchy_smooth :=
    smoothApproxSeqWkpThree_cauchy_smoothScalar (I := I) (M := M) g hu_h
  exact h_cauchy_smooth.map
    (smoothToH1Compl (I := I) (M := M) g).uniformContinuous

private theorem smoothToH1Compl_smoothApproxSeqWkpThree_has_limit
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    ∃ u_star : H1Compl g,
      Tendsto (fun n => smoothToH1Compl (I := I) (M := M) g
        (smoothApproxSeqWkpThree (I := I) (M := M) g hu_h n)) atTop (𝓝 u_star) :=
  cauchySeq_tendsto_of_complete
    (smoothToH1Compl_smoothApproxSeqWkpThree_cauchy (I := I) (M := M) g hu_h)

private theorem eLpNorm_diff_smoothApproxSeqWkpThree_tendsto_zero
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    Tendsto (fun n => eLpNorm (fun x =>
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x -
          (smoothApproxSeqWkpThree (I := I) (M := M) g hu_h n).toFun x) 2
        (riemannianVolumeMeasure (I := I) (M := M) g))
      atTop (𝓝 0) := by
  classical
  obtain ⟨C, hC_nn, hC_bnd⟩ :=
    DifferentialGeometry.Analysis.Sobolev.EquivalenceFull.eLpNorm_riemannianVolumeMeasure_le_const_mul_wkpNormChart_uniform
      (I := I) (M := M) g (p := 2) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  set u : M → ℝ := ((H1ComplToLp (I := I) (M := M) g u_h :
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) with hu_def
  have hu_meas : Measurable u := by
    rw [hu_def]
    exact (Lp.stronglyMeasurable _).measurable
  rw [ENNReal.tendsto_atTop_zero]
  intro ε hε_pos
  by_cases hC_zero : C = 0
  · refine ⟨0, ?_⟩
    intro n _
    have h_bnd := hC_bnd
        (u := fun x => u x -
          (smoothApproxSeqWkpThree (I := I) (M := M) g hu_h n).toFun x)
        (hu_meas.sub
          (smoothApproxSeqWkpThree (I := I) (M := M) g hu_h n).smooth.continuous.measurable)
    rw [hC_zero, ENNReal.ofReal_zero, zero_mul] at h_bnd
    exact h_bnd.trans (zero_le _)
  have hC_pos : 0 < C := lt_of_le_of_ne hC_nn (Ne.symm hC_zero)
  by_cases hε_top : ε = ⊤
  · refine ⟨0, ?_⟩
    intro n _
    rw [hε_top]
    exact le_top
  have hε_real_pos : 0 < ε.toReal := ENNReal.toReal_pos hε_pos.ne' hε_top
  set ε_C : ℝ := ε.toReal / C with hε_C_def
  have hε_C_pos : 0 < ε_C := by positivity
  obtain ⟨N, hN_real⟩ := exists_nat_gt (1 / ε_C - 1)
  have hN1_pos : (0 : ℝ) < (N : ℝ) + 1 := by
    have h_pos : 0 < 1 / ε_C := by positivity
    linarith
  have hN_inv_le : (1 : ℝ) / ((N : ℝ) + 1) ≤ ε_C := by
    rw [div_le_iff₀ hN1_pos]
    have h1 : (1 : ℝ) = ε_C * (1 / ε_C) := by
      rw [mul_one_div, div_self hε_C_pos.ne']
    rw [h1]
    apply mul_le_mul_of_nonneg_left _ hε_C_pos.le
    linarith
  refine ⟨N, ?_⟩
  intro n hn
  have h_meas : Measurable (fun x : M => u x -
      (smoothApproxSeqWkpThree (I := I) (M := M) g hu_h n).toFun x) :=
    hu_meas.sub
      (smoothApproxSeqWkpThree (I := I) (M := M) g hu_h n).smooth.continuous.measurable
  have h_bnd := hC_bnd h_meas
  have h_chart_3_2 :
      wkpNormChart (I := I) (M := M) g 3 2
          (fun x : M => u x -
            (smoothApproxSeqWkpThree (I := I) (M := M) g hu_h n).toFun x) ≤
        ENNReal.ofReal (1 / ((n : ℝ) + 1)) :=
    smoothApproxSeqWkpThree_wkpNormChart_le (I := I) (M := M) g hu_h n
  have h_chart_1_2 :
      wkpNormChart (I := I) (M := M) g 1 2
          (fun x : M => u x -
            (smoothApproxSeqWkpThree (I := I) (M := M) g hu_h n).toFun x) ≤
        ENNReal.ofReal (1 / ((n : ℝ) + 1)) :=
    (wkpNormChart_one_le_three (I := I) (M := M) g _).trans h_chart_3_2
  have h_chain : eLpNorm
        (fun x => u x -
          (smoothApproxSeqWkpThree (I := I) (M := M) g hu_h n).toFun x) 2
        (riemannianVolumeMeasure (I := I) (M := M) g) ≤
      ENNReal.ofReal C * ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
    refine h_bnd.trans ?_
    gcongr
  refine h_chain.trans ?_
  have h_inv_n_nn : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) := by positivity
  have h_prod_eq : ENNReal.ofReal C * ENNReal.ofReal (1 / ((n : ℝ) + 1)) =
      ENNReal.ofReal (C * (1 / ((n : ℝ) + 1))) := by
    rw [← ENNReal.ofReal_mul hC_nn]
  rw [h_prod_eq]
  have hNn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have hn_inv_le_N_inv : (1 : ℝ) / ((n : ℝ) + 1) ≤ (1 : ℝ) / ((N : ℝ) + 1) := by
    apply div_le_div_of_nonneg_left zero_le_one hN1_pos
    linarith
  have h_C_step : C * (1 / ((n : ℝ) + 1)) ≤ C * (1 / ((N : ℝ) + 1)) :=
    mul_le_mul_of_nonneg_left hn_inv_le_N_inv hC_nn
  have h_C_ε_C : C * (1 / ((N : ℝ) + 1)) ≤ C * ε_C :=
    mul_le_mul_of_nonneg_left hN_inv_le hC_nn
  have h_C_ε_C_eq : C * ε_C = ε.toReal := by
    rw [hε_C_def]
    field_simp
  have h_final_real : C * (1 / ((n : ℝ) + 1)) ≤ ε.toReal := by
    calc C * (1 / ((n : ℝ) + 1))
        ≤ C * (1 / ((N : ℝ) + 1)) := h_C_step
      _ ≤ C * ε_C := h_C_ε_C
      _ = ε.toReal := h_C_ε_C_eq
  have h_ε_eq : ε = ENNReal.ofReal ε.toReal := (ENNReal.ofReal_toReal hε_top).symm
  rw [h_ε_eq]
  exact ENNReal.ofReal_le_ofReal h_final_real

set_option maxHeartbeats 1600000 in
private theorem smoothToLp_smoothApproxSeqWkpThree_tendsto
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    Tendsto (fun n => smoothToLp (I := I) (M := M) g
        (smoothApproxSeqWkpThree (I := I) (M := M) g hu_h n))
      atTop (𝓝 (H1ComplToLp (I := I) (M := M) g u_h)) := by
  classical
  rw [Metric.tendsto_atTop]
  intro ε hε_pos
  have h_eLpNorm_tendsto :=
    eLpNorm_diff_smoothApproxSeqWkpThree_tendsto_zero (I := I) (M := M) g hu_h
  rw [ENNReal.tendsto_atTop_zero] at h_eLpNorm_tendsto
  have hε_half_pos : 0 < ε / 2 := by linarith
  obtain ⟨N, hN⟩ := h_eLpNorm_tendsto (ENNReal.ofReal (ε / 2))
    (ENNReal.ofReal_pos.mpr hε_half_pos)
  refine ⟨N, ?_⟩
  intro n hn
  have h_eLpNorm_le := hN n hn
  set u : M → ℝ := ((H1ComplToLp (I := I) (M := M) g u_h :
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) with hu_def
  rw [dist_eq_norm]
  have h_norm_sub_comm :
      ‖smoothToLp (I := I) (M := M) g
            (smoothApproxSeqWkpThree (I := I) (M := M) g hu_h n) -
          H1ComplToLp (I := I) (M := M) g u_h‖ =
      ‖H1ComplToLp (I := I) (M := M) g u_h -
          smoothToLp (I := I) (M := M) g
            (smoothApproxSeqWkpThree (I := I) (M := M) g hu_h n)‖ :=
    norm_sub_rev _ _
  rw [h_norm_sub_comm]
  set Δ : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
    H1ComplToLp (I := I) (M := M) g u_h -
      smoothToLp (I := I) (M := M) g
        (smoothApproxSeqWkpThree (I := I) (M := M) g hu_h n) with hΔ_def
  have h_Δ_coe_ae : (Δ : M → ℝ) =ᵐ[
      riemannianVolumeMeasure (I := I) (M := M) g]
      (fun x => u x -
        (smoothApproxSeqWkpThree (I := I) (M := M) g hu_h n).toFun x) := by
    have h_sub := MeasureTheory.Lp.coeFn_sub
      (H1ComplToLp (I := I) (M := M) g u_h)
      (smoothToLp (I := I) (M := M) g
        (smoothApproxSeqWkpThree (I := I) (M := M) g hu_h n))
    have h_smoothToLp_coe :
        (smoothToLp (I := I) (M := M) g
            (smoothApproxSeqWkpThree (I := I) (M := M) g hu_h n) :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) =ᵐ[
          riemannianVolumeMeasure (I := I) (M := M) g]
        (smoothApproxSeqWkpThree (I := I) (M := M) g hu_h n).toFun :=
      MemLp.coeFn_toLp
        (smoothApproxSeqWkpThree (I := I) (M := M) g hu_h n).memLp_two
    filter_upwards [h_sub, h_smoothToLp_coe] with x hx_sub hx_smoothToLp
    rw [hΔ_def, hx_sub, Pi.sub_apply, hx_smoothToLp]
  have h_norm_Δ : ‖Δ‖ = (eLpNorm (fun x => u x -
        (smoothApproxSeqWkpThree (I := I) (M := M) g hu_h n).toFun x) 2
        (riemannianVolumeMeasure (I := I) (M := M) g)).toReal := by
    rw [Lp.norm_def]
    rw [eLpNorm_congr_ae h_Δ_coe_ae]
  rw [h_norm_Δ]
  have h_eLpNorm_finite : eLpNorm (fun x => u x -
      (smoothApproxSeqWkpThree (I := I) (M := M) g hu_h n).toFun x) 2
      (riemannianVolumeMeasure (I := I) (M := M) g) ≠ ⊤ := by
    have h_le_half : eLpNorm (fun x => u x -
        (smoothApproxSeqWkpThree (I := I) (M := M) g hu_h n).toFun x) 2
        (riemannianVolumeMeasure (I := I) (M := M) g) ≤
        ENNReal.ofReal (ε / 2) := h_eLpNorm_le
    refine ne_of_lt ?_
    exact lt_of_le_of_lt h_le_half ENNReal.ofReal_lt_top
  have h_toReal_le : (eLpNorm (fun x => u x -
      (smoothApproxSeqWkpThree (I := I) (M := M) g hu_h n).toFun x) 2
      (riemannianVolumeMeasure (I := I) (M := M) g)).toReal ≤ ε / 2 := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h_eLpNorm_le
    rw [ENNReal.toReal_ofReal hε_half_pos.le] at this
    exact this
  linarith

set_option maxHeartbeats 800000 in
private lemma inner_smoothToH1Compl_limit_eq_u_h_wkpThree
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    {u_star : H1Compl g}
    (h_tendsto_star : Tendsto (fun n => smoothToH1Compl (I := I) (M := M) g
        (smoothApproxSeqWkpThree (I := I) (M := M) g hu_h n)) atTop (𝓝 u_star))
    (f : SmoothScalar g) :
    ⟪smoothToH1Compl (I := I) (M := M) g f, u_star⟫_ℝ =
      ⟪smoothToH1Compl (I := I) (M := M) g f, u_h⟫_ℝ := by
  classical
  have h_inner_star_lim : Tendsto (fun n =>
      ⟪smoothToH1Compl (I := I) (M := M) g f,
        smoothToH1Compl (I := I) (M := M) g
          (smoothApproxSeqWkpThree (I := I) (M := M) g hu_h n)⟫_ℝ) atTop
        (𝓝 ⟪smoothToH1Compl (I := I) (M := M) g f, u_star⟫_ℝ) :=
    Tendsto.inner tendsto_const_nhds h_tendsto_star
  have h_rewrite : ∀ n,
      ⟪smoothToH1Compl (I := I) (M := M) g f,
        smoothToH1Compl (I := I) (M := M) g
          (smoothApproxSeqWkpThree (I := I) (M := M) g hu_h n)⟫_ℝ =
      ⟪smoothToLp (I := I) (M := M) g f.oneSubLapClassical,
        smoothToLp (I := I) (M := M) g
          (smoothApproxSeqWkpThree (I := I) (M := M) g hu_h n)⟫_ℝ := by
    intro n
    rw [inner_smoothToH1Compl_smoothToH1Compl]
    rw [smoothScalarH1Inner_symm]
    exact smoothScalarH1Inner_eq_lpInner_oneSubLap_right (I := I) (M := M) g
      (smoothApproxSeqWkpThree (I := I) (M := M) g hu_h n) f
  have h_lp_tendsto :=
    smoothToLp_smoothApproxSeqWkpThree_tendsto (I := I) (M := M) g hu_h
  have h_inner_lp_lim : Tendsto (fun n =>
      ⟪smoothToLp (I := I) (M := M) g f.oneSubLapClassical,
        smoothToLp (I := I) (M := M) g
          (smoothApproxSeqWkpThree (I := I) (M := M) g hu_h n)⟫_ℝ) atTop
        (𝓝 ⟪smoothToLp (I := I) (M := M) g f.oneSubLapClassical,
          H1ComplToLp (I := I) (M := M) g u_h⟫_ℝ) :=
    Tendsto.inner tendsto_const_nhds h_lp_tendsto
  have h_rewrite_func : (fun n =>
      ⟪smoothToH1Compl (I := I) (M := M) g f,
        smoothToH1Compl (I := I) (M := M) g
          (smoothApproxSeqWkpThree (I := I) (M := M) g hu_h n)⟫_ℝ) =
      (fun n =>
        ⟪smoothToLp (I := I) (M := M) g f.oneSubLapClassical,
          smoothToLp (I := I) (M := M) g
            (smoothApproxSeqWkpThree (I := I) (M := M) g hu_h n)⟫_ℝ) := by
    funext n; exact h_rewrite n
  rw [h_rewrite_func] at h_inner_star_lim
  have h_LHS_eq : ⟪smoothToH1Compl (I := I) (M := M) g f, u_star⟫_ℝ =
      ⟪smoothToLp (I := I) (M := M) g f.oneSubLapClassical,
        H1ComplToLp (I := I) (M := M) g u_h⟫_ℝ :=
    tendsto_nhds_unique h_inner_star_lim h_inner_lp_lim
  have h_RHS_eq : ⟪smoothToH1Compl (I := I) (M := M) g f, u_h⟫_ℝ =
      ⟪smoothToLp (I := I) (M := M) g f.oneSubLapClassical,
        H1ComplToLp (I := I) (M := M) g u_h⟫_ℝ := by
    have h_uh_f := inner_h1Compl_smoothToH1Compl_eq_lpInner (I := I) (M := M) g u_h f
    rw [← h_uh_f]
    exact real_inner_comm _ _
  rw [h_LHS_eq, h_RHS_eq]

theorem smoothApproxSeqWkpThree_tendsto_h1Compl
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    Tendsto (fun n =>
      smoothToH1Compl (I := I) (M := M) g
        (smoothApproxSeqWkpThree (I := I) (M := M) g hu_h n))
      atTop (𝓝 u_h) := by
  classical
  obtain ⟨u_star, h_tendsto_star⟩ :=
    smoothToH1Compl_smoothApproxSeqWkpThree_has_limit (I := I) (M := M) g hu_h
  suffices h_eq : u_star = u_h by
    convert h_tendsto_star using 2
    exact h_eq.symm
  apply ext_inner_left ℝ
  intro w
  have hL_cont : Continuous (fun w => ⟪w, u_star⟫_ℝ) :=
    ((innerSL ℝ (E := H1Compl g)).flip u_star).continuous
  have hR_cont : Continuous (fun w => ⟪w, u_h⟫_ℝ) :=
    ((innerSL ℝ (E := H1Compl g)).flip u_h).continuous
  have hLR_smooth :
      (fun w => ⟪w, u_star⟫_ℝ) ∘ (smoothToH1Compl (I := I) (M := M) g) =
        (fun w => ⟪w, u_h⟫_ℝ) ∘ (smoothToH1Compl (I := I) (M := M) g) := by
    funext f
    exact inner_smoothToH1Compl_limit_eq_u_h_wkpThree (I := I) (M := M) g hu_h
      h_tendsto_star f
  exact congrFun
    ((denseRange_smoothToH1Compl (I := I) (M := M) g).equalizer
      hL_cont hR_cont hLR_smooth) w

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma eLpNorm_le_wkpNorm_two_two
    (u : EuclN → ℝ) (Ω : Set EuclN) :
    eLpNorm u 2 ((volume : Measure EuclN).restrict Ω) ≤
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 2 2 u Ω := by
  classical
  have h_iter_eq :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial
        (d := Module.finrank ℝ E) (p := 2) 0 (fun i : Fin 0 => i.elim0) u Ω = u :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial_zero
      (d := Module.finrank ℝ E) (p := 2) (fun i : Fin 0 => i.elim0) u Ω
  have h_zero_le :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.eLpNorm_iterWeakPartial_le_wkpNorm
      (d := Module.finrank ℝ E) (k := 2) (p := 2) u Ω 0 (by norm_num : (0 : ℕ) ≤ 2)
      (fun i : Fin 0 => i.elim0)
  rw [h_iter_eq] at h_zero_le
  exact h_zero_le

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma eLpNorm_tendsto_zero_of_wkpNorm_two_two_tendsto_zero
    {u : ℕ → EuclN → ℝ} {F_lim : EuclN → ℝ} {Ω : Set EuclN}
    (h_tendsto : Tendsto (fun n =>
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) 2 2
          (fun y => u n y - F_lim y) Ω)
      atTop (𝓝 0)) :
    Tendsto (fun n =>
      eLpNorm (fun y => u n y - F_lim y) 2
        ((volume : Measure EuclN).restrict Ω))
      atTop (𝓝 0) := by
  classical
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    (g := fun _ => (0 : ℝ≥0∞)) (h := fun n =>
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 2 2
        (fun y => u n y - F_lim y) Ω)
    tendsto_const_nhds h_tendsto
    (fun _ => zero_le _)
    (fun n => eLpNorm_le_wkpNorm_two_two (fun y => u n y - F_lim y) Ω)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma volume_restrict_chartTarget_absolutelyContinuous_weighted
    (g : SmoothRiemannianMetric I M) (α : M) :
    (volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α) ≪
      (chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  intro A hA
  have h_chartTarget_meas : MeasurableSet
      (chartTargetEuclid (I := I) (M := M) α) :=
    (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
  unfold chartPulledWeightedMeasure at hA
  rw [show ((volume : Measure EuclN).withDensity
        (fun y => ENNReal.ofReal (densityOnEuclid (I := I) g α y))).restrict
        (chartTargetEuclid (I := I) (M := M) α) =
      ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)).withDensity
        (fun y => ENNReal.ofReal (densityOnEuclid (I := I) g α y))
    from MeasureTheory.restrict_withDensity h_chartTarget_meas _] at hA
  rw [MeasureTheory.withDensity_apply_eq_zero'
    (μ := (volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α))
    (f := fun y : EuclN => ENNReal.ofReal (densityOnEuclid (I := I) g α y))
    (ENNReal.measurable_ofReal.comp_aemeasurable
      ((densityOnEuclid_continuousOn (I := I) g α).aemeasurable h_chartTarget_meas))]
    at hA
  rw [Measure.restrict_apply' h_chartTarget_meas]
  rw [Measure.restrict_apply' h_chartTarget_meas] at hA
  refine MeasureTheory.measure_mono_null ?_ hA
  intro y ⟨hy_A, hy_chart⟩
  refine ⟨⟨?_, hy_A⟩, hy_chart⟩
  have h_pos : 0 < densityOnEuclid (I := I) g α y :=
    densityOnEuclid_pos (I := I) g α hy_chart
  exact (ENNReal.ofReal_pos.mpr h_pos).ne'

omit [NeZero (Module.finrank ℝ E)] in
private lemma smoothFChartResidual_aestronglyMeasurable
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g)
    (μ : Measure EuclN) :
    AEStronglyMeasurable
      (smoothFChartResidual (I := I) (M := M) g α v) μ := by
  unfold smoothFChartResidual fChartResidual
  exact (Lp.stronglyMeasurable _).aestronglyMeasurable.mono_measure (le_refl _)

omit [NeZero (Module.finrank ℝ E)] in
private lemma fChartResidual_aestronglyMeasurable
    (g : SmoothRiemannianMetric I M) (α : M) (u_h : H1Compl (I := I) (M := M) g)
    (μ : Measure EuclN) :
    AEStronglyMeasurable
      (DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fChartResidual
        (I := I) (M := M) g α u_h) μ := by
  unfold fChartResidual
  exact (Lp.stronglyMeasurable _).aestronglyMeasurable.mono_measure (le_refl _)

omit [NeZero (Module.finrank ℝ E)] in
private lemma exists_subseq_ae_volume_restrict
    (g : SmoothRiemannianMetric I M) (α : M)
    {v : ℕ → SmoothScalar g} {F_lim : EuclN → ℝ}
    (hF_aesm : AEStronglyMeasurable F_lim
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)))
    (h_tendsto : Tendsto (fun n =>
      eLpNorm (fun y =>
          smoothFChartResidual (I := I) (M := M) g α (v n) y - F_lim y) 2
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)))
      atTop (𝓝 0)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∀ᵐ y ∂((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)),
        Tendsto (fun n =>
          smoothFChartResidual (I := I) (M := M) g α (v (σ n)) y) atTop
          (𝓝 (F_lim y)) := by
  classical
  have h_aesm_n : ∀ n, AEStronglyMeasurable
      (smoothFChartResidual (I := I) (M := M) g α (v n))
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := fun n =>
    smoothFChartResidual_aestronglyMeasurable (I := I) (M := M) g α (v n) _
  have h_tim : TendstoInMeasure
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α))
      (fun n => smoothFChartResidual (I := I) (M := M) g α (v n))
      atTop F_lim :=
    MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm
      (μ := (volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α))
      (p := 2) (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      h_aesm_n hF_aesm h_tendsto
  exact h_tim.exists_seq_tendsto_ae

omit [NeZero (Module.finrank ℝ E)] in
private lemma exists_subseq_ae_weighted_restrict
    (g : SmoothRiemannianMetric I M) (α : M)
    {v : ℕ → SmoothScalar g} {F : EuclN → ℝ}
    (hF_aesm : AEStronglyMeasurable F
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)))
    (h_tendsto : Tendsto (fun n =>
      eLpNorm (fun y =>
          smoothFChartResidual (I := I) (M := M) g α (v n) y - F y) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)))
      atTop (𝓝 0)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∀ᵐ y ∂((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)),
        Tendsto (fun n =>
          smoothFChartResidual (I := I) (M := M) g α (v (σ n)) y) atTop
          (𝓝 (F y)) := by
  classical
  have h_aesm_n : ∀ n, AEStronglyMeasurable
      (smoothFChartResidual (I := I) (M := M) g α (v n))
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := fun n =>
    smoothFChartResidual_aestronglyMeasurable (I := I) (M := M) g α (v n) _
  have h_tim : TendstoInMeasure
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α))
      (fun n => smoothFChartResidual (I := I) (M := M) g α (v n))
      atTop F :=
    MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm
      (μ := (chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α))
      (p := 2) (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      h_aesm_n hF_aesm h_tendsto
  exact h_tim.exists_seq_tendsto_ae

theorem smoothApproxSeqWkpThree_smoothFChartResidual_limit_eq_fChartResidual_w22
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    ∀ F_lim : EuclN → ℝ,
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 2 2 F_lim
        (chartTargetEuclid (I := I) (M := M) α) →
      Tendsto (fun n =>
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) 2 2
          (fun y =>
            smoothFChartResidual (I := I) (M := M) g α
              (smoothApproxSeqWkpThree (I := I) (M := M) g hu_h n) y -
            F_lim y)
          (chartTargetEuclid (I := I) (M := M) α))
        atTop (𝓝 0) →
      F_lim =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)]
        DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fChartResidual
          (I := I) (M := M) g α u_h := by
  classical
  intro F_lim h_F_lim_w2p h_wkp_tendsto
  set v : ℕ → SmoothScalar g := fun n =>
    smoothApproxSeqWkpThree (I := I) (M := M) g hu_h n with hv_def
  have hF_lim_W1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 F_lim
      (chartTargetEuclid (I := I) (M := M) α) := h_F_lim_w2p.memW1p
  have hF_lim_memLp : MemLp F_lim 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := hF_lim_W1p.1
  have hF_lim_aesm_volume : AEStronglyMeasurable F_lim
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
    hF_lim_memLp.aestronglyMeasurable
  have hF_res_aesm_weighted :
      AEStronglyMeasurable
        (DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fChartResidual
          (I := I) (M := M) g α u_h)
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
    fChartResidual_aestronglyMeasurable (I := I) (M := M) g α u_h _
  have h_eLpNorm_volume_tendsto :
      Tendsto (fun n =>
        eLpNorm (fun y =>
            smoothFChartResidual (I := I) (M := M) g α (v n) y - F_lim y) 2
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)))
        atTop (𝓝 0) :=
    eLpNorm_tendsto_zero_of_wkpNorm_two_two_tendsto_zero
      (u := fun n => smoothFChartResidual (I := I) (M := M) g α (v n))
      (F_lim := F_lim)
      (Ω := chartTargetEuclid (I := I) (M := M) α)
      h_wkp_tendsto
  have h_h1Compl_tendsto : Tendsto (fun n =>
      smoothToH1Compl (I := I) (M := M) g (v n))
      atTop (𝓝 u_h) :=
    smoothApproxSeqWkpThree_tendsto_h1Compl (I := I) (M := M) g hu_h
  have h_eLpNorm_weighted_tendsto :
      Tendsto (fun n =>
        eLpNorm (fun y =>
            smoothFChartResidual (I := I) (M := M) g α (v n) y -
            DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fChartResidual
              (I := I) (M := M) g α u_h y) 2
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)))
        atTop (𝓝 0) :=
    smoothFChartResidual_tendsto_fChartResidual_lp_weighted
      (I := I) (M := M) g α v h_h1Compl_tendsto
  obtain ⟨σ, hσ_strict, hσ_ae⟩ :=
    exists_subseq_ae_volume_restrict (I := I) (M := M) g α
      (v := v) (F_lim := F_lim) hF_lim_aesm_volume h_eLpNorm_volume_tendsto
  have h_eLpNorm_weighted_subseq :
      Tendsto (fun n =>
        eLpNorm (fun y =>
            smoothFChartResidual (I := I) (M := M) g α (v (σ n)) y -
            DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fChartResidual
              (I := I) (M := M) g α u_h y) 2
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)))
        atTop (𝓝 0) :=
    h_eLpNorm_weighted_tendsto.comp hσ_strict.tendsto_atTop
  obtain ⟨τ, hτ_strict, hτ_ae⟩ :=
    exists_subseq_ae_weighted_restrict (I := I) (M := M) g α
      (v := fun n => v (σ n))
      (F := DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fChartResidual
        (I := I) (M := M) g α u_h)
      hF_res_aesm_weighted h_eLpNorm_weighted_subseq
  have h_volume_ae_σ_τ :
      ∀ᵐ y ∂((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)),
        Tendsto (fun n =>
          smoothFChartResidual (I := I) (M := M) g α (v (σ (τ n))) y) atTop
          (𝓝 (F_lim y)) := by
    filter_upwards [hσ_ae] with y hy
    exact hy.comp hτ_strict.tendsto_atTop
  have h_vol_abs : (volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α) ≪
      (chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α) :=
    volume_restrict_chartTarget_absolutelyContinuous_weighted
      (I := I) (M := M) g α
  have h_volume_ae_σ_τ_fChart :
      ∀ᵐ y ∂((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)),
        Tendsto (fun n =>
          smoothFChartResidual (I := I) (M := M) g α (v (σ (τ n))) y) atTop
          (𝓝 ((DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fChartResidual
              (I := I) (M := M) g α u_h) y)) :=
    h_vol_abs.ae_le hτ_ae
  filter_upwards [h_volume_ae_σ_τ, h_volume_ae_σ_τ_fChart]
    with y h_to_Flim h_to_fChart
  exact tendsto_nhds_unique h_to_Flim h_to_fChart

end SmoothApproxSeqIdentificationW22
end Laplacian
end Analysis
end DifferentialGeometry

end
