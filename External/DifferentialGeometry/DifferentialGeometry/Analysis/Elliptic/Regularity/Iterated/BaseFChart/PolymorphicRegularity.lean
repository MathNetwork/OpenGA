import DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.BaseFChart.BilinearRegularity
import DifferentialGeometry.Analysis.Elliptic.Regularity.SmoothApproxSeq.H1ComplTendsto
import DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.ResidualRegularity.BilinearH1ComplFromDomainPow
import DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.BaseFChart.MemWkpTwoTwo
import DifferentialGeometry.Analysis.Sobolev.Approximation.ContMDiffDenseHigherOrder


noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace IteratedBaseFChartRegularityB

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
open DifferentialGeometry.Analysis.Laplacian.IteratedBaseFChartRegularity
open DifferentialGeometry.Analysis.Laplacian.SmoothFChartResidualLinearity
open DifferentialGeometry.Analysis.Laplacian.SmoothApproxSeqH1ComplTendsto
open DifferentialGeometry.Analysis.Sobolev.Chart

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private noncomputable def smoothScalarSub
    {g : SmoothRiemannianMetric I M}
    (v₁ v₂ : SmoothScalar g) : SmoothScalar g :=
  { toFun := fun x => v₁.toFun x - v₂.toFun x
    smooth := v₁.smooth.sub v₂.smooth }

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma smoothScalarSub_toFun
    {g : SmoothRiemannianMetric I M}
    (v₁ v₂ : SmoothScalar g) :
    (smoothScalarSub v₁ v₂).toFun = fun x => v₁.toFun x - v₂.toFun x := rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
private lemma wkpNormChart_one_le_succ
    (g : SmoothRiemannianMetric I M) (m : ℕ) (u : M → ℝ) :
    wkpNormChart (I := I) (M := M) g 1 2 u ≤
      wkpNormChart (I := I) (M := M) g (m + 1) 2 u := by
  classical
  induction m with
  | zero => exact le_refl _
  | succ k ih =>
      have h_step : wkpNormChart (I := I) (M := M) g (k + 1) 2 u ≤
          wkpNormChart (I := I) (M := M) g (k + 1 + 1) 2 u :=
        wkpNormChart_le_succ (I := I) (M := M) g (k + 1) 2 u
      exact ih.trans h_step

theorem exists_smoothApprox_chartWmSucc
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    {u : M → ℝ} (hu : MemWkpChart (I := I) (M := M) g (m + 1) 2 u)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ v : SmoothScalar g, wkpNormChart (I := I) (M := M) g (m + 1) 2
      (fun x => u x - v.toFun x) ≤ ENNReal.ofReal ε := by
  classical
  obtain ⟨w, hw_smooth, hw_le⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Chart.contMDiff_dense_in_WkpChart_k
      (I := I) (M := M) g (m + 1) (p := 2) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hu hε
  refine ⟨⟨w, hw_smooth⟩, ?_⟩
  exact hw_le

noncomputable def smoothApproxSeqWkpM
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    {u : M → ℝ} (hu : MemWkpChart (I := I) (M := M) g (m + 1) 2 u)
    (n : ℕ) : SmoothScalar g :=
  (exists_smoothApprox_chartWmSucc (I := I) (M := M) g m hu
    (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1))).choose

theorem smoothApproxSeqWkpM_wkpNormChart_le
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    {u : M → ℝ} (hu : MemWkpChart (I := I) (M := M) g (m + 1) 2 u)
    (n : ℕ) :
    wkpNormChart (I := I) (M := M) g (m + 1) 2
      (fun x => u x - (smoothApproxSeqWkpM (I := I) (M := M) g m hu n).toFun x) ≤
      ENNReal.ofReal (1 / ((n : ℝ) + 1)) :=
  (exists_smoothApprox_chartWmSucc (I := I) (M := M) g m hu
    (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1))).choose_spec

theorem smoothApproxSeqWkpM_wkpNormChart_diff_le
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    {u : M → ℝ} (hu : MemWkpChart (I := I) (M := M) g (m + 1) 2 u)
    (a b : ℕ) :
    wkpNormChart (I := I) (M := M) g (m + 1) 2
      (fun x => (smoothApproxSeqWkpM (I := I) (M := M) g m hu a).toFun x -
        (smoothApproxSeqWkpM (I := I) (M := M) g m hu b).toFun x) ≤
      ENNReal.ofReal (1 / ((a : ℝ) + 1)) + ENNReal.ofReal (1 / ((b : ℝ) + 1)) := by
  classical
  set va : SmoothScalar g := smoothApproxSeqWkpM (I := I) (M := M) g m hu a
  set vb : SmoothScalar g := smoothApproxSeqWkpM (I := I) (M := M) g m hu b
  have h_decomp : (fun x => va.toFun x - vb.toFun x) =
      (fun x => (u x - vb.toFun x) - (u x - va.toFun x)) := by
    funext x; ring
  rw [h_decomp]
  have hp_one : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have h_smooth_va : MemWkpChart (I := I) (M := M) g (m + 1) 2 va.toFun :=
    DifferentialGeometry.Analysis.Sobolev.Chart.memWkpChart_of_contMDiff_k
      (I := I) (M := M) g hp_one (m + 1) va.smooth
  have h_smooth_vb : MemWkpChart (I := I) (M := M) g (m + 1) 2 vb.toFun :=
    DifferentialGeometry.Analysis.Sobolev.Chart.memWkpChart_of_contMDiff_k
      (I := I) (M := M) g hp_one (m + 1) vb.smooth
  have h_u_diff_va : MemWkpChart (I := I) (M := M) g (m + 1) 2
      (fun x => u x - va.toFun x) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart_sub
      (I := I) (M := M) g hp_one hu h_smooth_va
  have h_u_diff_vb : MemWkpChart (I := I) (M := M) g (m + 1) 2
      (fun x => u x - vb.toFun x) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart_sub
      (I := I) (M := M) g hp_one hu h_smooth_vb
  have h_split : (fun x : M => (u x - vb.toFun x) - (u x - va.toFun x)) =
      (fun x : M => (u x - vb.toFun x) + (-1 : ℝ) * (u x - va.toFun x)) := by
    funext x; ring
  rw [h_split]
  have h_neg_smul :
      wkpNormChart (I := I) (M := M) g (m + 1) 2
        (fun x => (-1 : ℝ) * (u x - va.toFun x)) =
      ‖(-1 : ℝ)‖ₑ *
        wkpNormChart (I := I) (M := M) g (m + 1) 2 (fun x => u x - va.toFun x) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart_const_smul
      (I := I) (M := M) g hp_one (-1 : ℝ) h_u_diff_va
  have h_neg_one_norm : ‖(-1 : ℝ)‖ₑ = 1 := by
    simp [enorm]
  rw [h_neg_one_norm, one_mul] at h_neg_smul
  have h_u_diff_va_neg : MemWkpChart (I := I) (M := M) g (m + 1) 2
      (fun x => (-1 : ℝ) * (u x - va.toFun x)) := by
    have h_eq : (fun x : M => (-1 : ℝ) * (u x - va.toFun x)) =
        (fun x => -(u x - va.toFun x)) := by funext x; ring
    rw [h_eq]
    exact DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart_neg
      (I := I) (M := M) g hp_one h_u_diff_va
  have h_add :=
    DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart_add_le (I := I) (M := M)
      g (k := m + 1) (p := 2) hp_one h_u_diff_vb h_u_diff_va_neg
  rw [h_neg_smul] at h_add
  have h_bound1 :
      wkpNormChart (I := I) (M := M) g (m + 1) 2 (fun x => u x - vb.toFun x) +
        wkpNormChart (I := I) (M := M) g (m + 1) 2 (fun x => u x - va.toFun x) ≤
      ENNReal.ofReal (1 / ((b : ℝ) + 1)) + ENNReal.ofReal (1 / ((a : ℝ) + 1)) :=
    add_le_add
      (smoothApproxSeqWkpM_wkpNormChart_le (I := I) (M := M) g m hu b)
      (smoothApproxSeqWkpM_wkpNormChart_le (I := I) (M := M) g m hu a)
  have h_comm :
      ENNReal.ofReal (1 / ((b : ℝ) + 1)) + ENNReal.ofReal (1 / ((a : ℝ) + 1)) =
      ENNReal.ofReal (1 / ((a : ℝ) + 1)) + ENNReal.ofReal (1 / ((b : ℝ) + 1)) := by
    rw [add_comm]
  exact le_trans h_add (le_of_le_of_eq h_bound1 h_comm)

theorem smoothApproxSeq_smoothFChartResidual_wkpNorm_cauchy_wkpM
    (g : SmoothRiemannianMetric I M) (α : M) (m : ℕ)
    {u : M → ℝ} (hu : MemWkpChart (I := I) (M := M) g (m + 1) 2 u) :
    ∀ ε > 0, ∃ N, ∀ a b, N ≤ a → N ≤ b →
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) m 2
        (fun y =>
          DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplResidual.smoothFChartResidual
            (I := I) (M := M) g α
            (smoothApproxSeqWkpM (I := I) (M := M) g m hu a) y -
          DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplResidual.smoothFChartResidual
            (I := I) (M := M) g α
            (smoothApproxSeqWkpM (I := I) (M := M) g m hu b) y)
        (chartTargetEuclid (I := I) (M := M) α) ≤ ENNReal.ofReal ε := by
  classical
  intro ε hε
  obtain ⟨C, hC_pos, hC_bound⟩ :=
    wkpNorm_smoothFChartResidual_le_wkpNormChart_wkpM (I := I) (M := M) g α m
  have hε_C_pos : 0 < ε / (2 * C) := by positivity
  obtain ⟨N0, hN0_real⟩ := exists_nat_gt (1 / (ε / (2 * C)) - 1)
  have hN1_pos : (0 : ℝ) < (N0 : ℝ) + 1 := by
    have h_pos : 0 < 1 / (ε / (2 * C)) := by positivity
    linarith
  have hN0_inv_real : (1 : ℝ) / ((N0 : ℝ) + 1) ≤ ε / (2 * C) := by
    rw [div_le_iff₀ hN1_pos]
    have h1 : (1 : ℝ) = (ε / (2 * C)) * (1 / (ε / (2 * C))) := by
      rw [mul_one_div, div_self hε_C_pos.ne']
    rw [h1]
    apply mul_le_mul_of_nonneg_left _ hε_C_pos.le
    linarith
  refine ⟨N0, ?_⟩
  intro a b ha hb
  set va : SmoothScalar g := smoothApproxSeqWkpM (I := I) (M := M) g m hu a
  set vb : SmoothScalar g := smoothApproxSeqWkpM (I := I) (M := M) g m hu b
  set vdiff : SmoothScalar g := smoothScalarSub va vb with hvdiff_def
  have hvdiff_toFun :
      vdiff.toFun = fun x => va.toFun x - vb.toFun x :=
    smoothScalarSub_toFun va vb
  have h_ae_sub :=
    smoothFChartResidual_ae_sub (I := I) (M := M) g α va vb vdiff hvdiff_toFun
  have h_wkp_eq :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) m 2
        (fun y =>
          DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplResidual.smoothFChartResidual
            (I := I) (M := M) g α va y -
          DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplResidual.smoothFChartResidual
            (I := I) (M := M) g α vb y)
        (chartTargetEuclid (I := I) (M := M) α) =
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) m 2
        (DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplResidual.smoothFChartResidual
          (I := I) (M := M) g α vdiff)
        (chartTargetEuclid (I := I) (M := M) α) := by
    refine DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_congr_ae
      (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (chartTargetEuclid_isOpen (I := I) (M := M) α) ?_
    exact h_ae_sub.symm
  rw [h_wkp_eq]
  have h_bilinear := hC_bound vdiff
  have h_chartWm1_cauchy :
      wkpNormChart (I := I) (M := M) g (m + 1) 2 vdiff.toFun ≤
        ENNReal.ofReal ((1 : ℝ) / ((a : ℝ) + 1)) +
          ENNReal.ofReal ((1 : ℝ) / ((b : ℝ) + 1)) := by
    rw [hvdiff_toFun]
    exact smoothApproxSeqWkpM_wkpNormChart_diff_le (I := I) (M := M) g m hu a b
  have h_step :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) m 2
        (DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplResidual.smoothFChartResidual
          (I := I) (M := M) g α vdiff)
        (chartTargetEuclid (I := I) (M := M) α) ≤
      ENNReal.ofReal C *
        (ENNReal.ofReal ((1 : ℝ) / ((a : ℝ) + 1)) +
          ENNReal.ofReal ((1 : ℝ) / ((b : ℝ) + 1))) := by
    refine h_bilinear.trans ?_
    exact mul_le_mul_of_nonneg_left h_chartWm1_cauchy (zero_le _)
  refine h_step.trans ?_
  have hN0a : (N0 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hN0b : (N0 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have ha1_pos : (0 : ℝ) < (a : ℝ) + 1 := by linarith
  have hb1_pos : (0 : ℝ) < (b : ℝ) + 1 := by linarith
  have ha_inv_le : (1 : ℝ) / ((a : ℝ) + 1) ≤ (1 : ℝ) / ((N0 : ℝ) + 1) := by
    apply div_le_div_of_nonneg_left zero_le_one hN1_pos
    linarith
  have hb_inv_le : (1 : ℝ) / ((b : ℝ) + 1) ≤ (1 : ℝ) / ((N0 : ℝ) + 1) := by
    apply div_le_div_of_nonneg_left zero_le_one hN1_pos
    linarith
  have ha_ofReal_le :
      ENNReal.ofReal ((1 : ℝ) / ((a : ℝ) + 1)) ≤
        ENNReal.ofReal ((1 : ℝ) / ((N0 : ℝ) + 1)) :=
    ENNReal.ofReal_le_ofReal ha_inv_le
  have hb_ofReal_le :
      ENNReal.ofReal ((1 : ℝ) / ((b : ℝ) + 1)) ≤
        ENNReal.ofReal ((1 : ℝ) / ((N0 : ℝ) + 1)) :=
    ENNReal.ofReal_le_ofReal hb_inv_le
  have hsum_le :
      ENNReal.ofReal ((1 : ℝ) / ((a : ℝ) + 1)) +
        ENNReal.ofReal ((1 : ℝ) / ((b : ℝ) + 1)) ≤
      ENNReal.ofReal ((1 : ℝ) / ((N0 : ℝ) + 1)) +
        ENNReal.ofReal ((1 : ℝ) / ((N0 : ℝ) + 1)) :=
    add_le_add ha_ofReal_le hb_ofReal_le
  have hC_step :
      ENNReal.ofReal C *
        (ENNReal.ofReal ((1 : ℝ) / ((a : ℝ) + 1)) +
          ENNReal.ofReal ((1 : ℝ) / ((b : ℝ) + 1))) ≤
      ENNReal.ofReal C *
        (ENNReal.ofReal ((1 : ℝ) / ((N0 : ℝ) + 1)) +
          ENNReal.ofReal ((1 : ℝ) / ((N0 : ℝ) + 1))) :=
    mul_le_mul_of_nonneg_left hsum_le (zero_le _)
  refine hC_step.trans ?_
  have hN0_inv_nn : (0 : ℝ) ≤ (1 : ℝ) / ((N0 : ℝ) + 1) := by positivity
  have h_add :
      ENNReal.ofReal ((1 : ℝ) / ((N0 : ℝ) + 1)) +
        ENNReal.ofReal ((1 : ℝ) / ((N0 : ℝ) + 1)) =
      ENNReal.ofReal (2 * ((1 : ℝ) / ((N0 : ℝ) + 1))) := by
    rw [show (2 : ℝ) * ((1 : ℝ) / ((N0 : ℝ) + 1)) =
        ((1 : ℝ) / ((N0 : ℝ) + 1)) + ((1 : ℝ) / ((N0 : ℝ) + 1)) by ring,
      ENNReal.ofReal_add hN0_inv_nn hN0_inv_nn]
  rw [h_add]
  have hprod_eq :
      ENNReal.ofReal C * ENNReal.ofReal (2 * ((1 : ℝ) / ((N0 : ℝ) + 1))) =
      ENNReal.ofReal (C * (2 * ((1 : ℝ) / ((N0 : ℝ) + 1)))) := by
    rw [← ENNReal.ofReal_mul hC_pos.le]
  rw [hprod_eq]
  refine ENNReal.ofReal_le_ofReal ?_
  have h_step_real :
      C * (2 * ((1 : ℝ) / ((N0 : ℝ) + 1))) ≤
      C * (2 * (ε / (2 * C))) := by
    apply mul_le_mul_of_nonneg_left _ hC_pos.le
    apply mul_le_mul_of_nonneg_left hN0_inv_real (by norm_num : (0 : ℝ) ≤ 2)
  refine h_step_real.trans ?_
  have h_simp : C * (2 * (ε / (2 * C))) = ε := by
    field_simp
  rw [h_simp]

private theorem smoothApproxSeqWkpM_cauchy_smoothScalar
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    {u : M → ℝ} (hu : MemWkpChart (I := I) (M := M) g (m + 1) 2 u) :
    CauchySeq (fun n =>
      smoothApproxSeqWkpM (I := I) (M := M) g m hu n) := by
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
  intro a ha b hb
  set va : SmoothScalar g := smoothApproxSeqWkpM (I := I) (M := M) g m hu a
    with hva_def
  set vb : SmoothScalar g := smoothApproxSeqWkpM (I := I) (M := M) g m hu b
    with hvb_def
  rw [dist_eq_norm]
  set vdiff : SmoothScalar g := va - vb with hvdiff_def
  have hvdiff_toFun : vdiff.toFun = fun x => va.toFun x - vb.toFun x := by
    rw [hvdiff_def]; rfl
  have h_wkpNormChart_finite :
      wkpNormChart (I := I) (M := M) g 1 2 vdiff.toFun ≠ ⊤ := by
    rw [hvdiff_toFun]
    exact wkpNormChart_one_two_smoothScalar_diff_ne_top (I := I) (M := M) g va vb
  have h_norm_bd : ‖vdiff‖ ≤ C *
      (wkpNormChart (I := I) (M := M) g 1 2 vdiff.toFun).toReal :=
    hC_bnd vdiff h_wkpNormChart_finite
  have h_wkp_chart_succ :
      wkpNormChart (I := I) (M := M) g (m + 1) 2 vdiff.toFun ≤
        ENNReal.ofReal (1 / ((a : ℝ) + 1)) +
          ENNReal.ofReal (1 / ((b : ℝ) + 1)) := by
    rw [hvdiff_toFun]
    exact smoothApproxSeqWkpM_wkpNormChart_diff_le (I := I) (M := M) g m hu a b
  have h_wkp_chart_1_2 :
      wkpNormChart (I := I) (M := M) g 1 2 vdiff.toFun ≤
        ENNReal.ofReal (1 / ((a : ℝ) + 1)) +
          ENNReal.ofReal (1 / ((b : ℝ) + 1)) :=
    (wkpNormChart_one_le_succ (I := I) (M := M) g m vdiff.toFun).trans h_wkp_chart_succ
  have h_sum_finite :
      ENNReal.ofReal (1 / ((a : ℝ) + 1)) +
        ENNReal.ofReal (1 / ((b : ℝ) + 1)) ≠ ⊤ := by
    apply ENNReal.add_ne_top.mpr
    exact ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩
  have h_inv_a_nn : (0 : ℝ) ≤ 1 / ((a : ℝ) + 1) := by positivity
  have h_inv_b_nn : (0 : ℝ) ≤ 1 / ((b : ℝ) + 1) := by positivity
  have h_sum_toReal :
      (ENNReal.ofReal (1 / ((a : ℝ) + 1)) +
            ENNReal.ofReal (1 / ((b : ℝ) + 1))).toReal =
        1 / ((a : ℝ) + 1) + 1 / ((b : ℝ) + 1) := by
    rw [ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top]
    rw [ENNReal.toReal_ofReal h_inv_a_nn, ENNReal.toReal_ofReal h_inv_b_nn]
  have h_wkp_toReal_le :
      (wkpNormChart (I := I) (M := M) g 1 2 vdiff.toFun).toReal ≤
        1 / ((a : ℝ) + 1) + 1 / ((b : ℝ) + 1) := by
    have h_mono := ENNReal.toReal_mono h_sum_finite h_wkp_chart_1_2
    rwa [h_sum_toReal] at h_mono
  have hN0a : (N0 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hN0b : (N0 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have ha1_pos : (0 : ℝ) < (a : ℝ) + 1 := by linarith
  have hb1_pos : (0 : ℝ) < (b : ℝ) + 1 := by linarith
  have ha_inv_le : (1 : ℝ) / ((a : ℝ) + 1) ≤ (1 : ℝ) / ((N0 : ℝ) + 1) := by
    apply div_le_div_of_nonneg_left zero_le_one hN1_pos
    linarith
  have hb_inv_le : (1 : ℝ) / ((b : ℝ) + 1) ≤ (1 : ℝ) / ((N0 : ℝ) + 1) := by
    apply div_le_div_of_nonneg_left zero_le_one hN1_pos
    linarith
  have h_sum_le : 1 / ((a : ℝ) + 1) + 1 / ((b : ℝ) + 1) ≤
      2 * (1 / ((N0 : ℝ) + 1)) := by
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

private theorem smoothToH1Compl_smoothApproxSeqWkpM_cauchy
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    {u : M → ℝ} (hu : MemWkpChart (I := I) (M := M) g (m + 1) 2 u) :
    CauchySeq (fun n =>
      smoothToH1Compl (I := I) (M := M) g
        (smoothApproxSeqWkpM (I := I) (M := M) g m hu n)) := by
  have h_cauchy_smooth :=
    smoothApproxSeqWkpM_cauchy_smoothScalar (I := I) (M := M) g m hu
  exact h_cauchy_smooth.map
    (smoothToH1Compl (I := I) (M := M) g).uniformContinuous

private theorem smoothToH1Compl_smoothApproxSeqWkpM_has_limit
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    {u : M → ℝ} (hu : MemWkpChart (I := I) (M := M) g (m + 1) 2 u) :
    ∃ u_star : H1Compl g,
      Tendsto (fun n => smoothToH1Compl (I := I) (M := M) g
        (smoothApproxSeqWkpM (I := I) (M := M) g m hu n)) atTop (𝓝 u_star) :=
  cauchySeq_tendsto_of_complete
    (smoothToH1Compl_smoothApproxSeqWkpM_cauchy (I := I) (M := M) g m hu)

private theorem eLpNorm_diff_smoothApproxSeqWkpM_tendsto_zero
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_chart : MemWkpChart (I := I) (M := M) g (m + 1) 2
      ((H1ComplToLp (I := I) (M := M) g u_h : Lp ℝ 2
        (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) :
    Tendsto (fun n => eLpNorm (fun x =>
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x -
          (smoothApproxSeqWkpM (I := I) (M := M) g m hu_chart n).toFun x) 2
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
          (smoothApproxSeqWkpM (I := I) (M := M) g m hu_chart n).toFun x)
        (hu_meas.sub
          (smoothApproxSeqWkpM (I := I) (M := M) g m hu_chart n).smooth.continuous.measurable)
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
      (smoothApproxSeqWkpM (I := I) (M := M) g m hu_chart n).toFun x) :=
    hu_meas.sub
      (smoothApproxSeqWkpM (I := I) (M := M) g m hu_chart n).smooth.continuous.measurable
  have h_bnd := hC_bnd h_meas
  have h_chart_succ :
      wkpNormChart (I := I) (M := M) g (m + 1) 2
          (fun x : M => u x -
            (smoothApproxSeqWkpM (I := I) (M := M) g m hu_chart n).toFun x) ≤
        ENNReal.ofReal (1 / ((n : ℝ) + 1)) :=
    smoothApproxSeqWkpM_wkpNormChart_le (I := I) (M := M) g m hu_chart n
  have h_chart_1_2 :
      wkpNormChart (I := I) (M := M) g 1 2
          (fun x : M => u x -
            (smoothApproxSeqWkpM (I := I) (M := M) g m hu_chart n).toFun x) ≤
        ENNReal.ofReal (1 / ((n : ℝ) + 1)) :=
    (wkpNormChart_one_le_succ (I := I) (M := M) g m _).trans h_chart_succ
  have h_chain : eLpNorm
        (fun x => u x -
          (smoothApproxSeqWkpM (I := I) (M := M) g m hu_chart n).toFun x) 2
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
    rw [hε_C_def]; field_simp
  have h_final_real : C * (1 / ((n : ℝ) + 1)) ≤ ε.toReal := by
    calc C * (1 / ((n : ℝ) + 1))
        ≤ C * (1 / ((N : ℝ) + 1)) := h_C_step
      _ ≤ C * ε_C := h_C_ε_C
      _ = ε.toReal := h_C_ε_C_eq
  have h_ε_eq : ε = ENNReal.ofReal ε.toReal := (ENNReal.ofReal_toReal hε_top).symm
  rw [h_ε_eq]
  exact ENNReal.ofReal_le_ofReal h_final_real

private theorem smoothToLp_smoothApproxSeqWkpM_tendsto
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_chart : MemWkpChart (I := I) (M := M) g (m + 1) 2
      ((H1ComplToLp (I := I) (M := M) g u_h : Lp ℝ 2
        (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) :
    Tendsto (fun n => smoothToLp (I := I) (M := M) g
        (smoothApproxSeqWkpM (I := I) (M := M) g m hu_chart n))
      atTop (𝓝 (H1ComplToLp (I := I) (M := M) g u_h)) := by
  classical
  rw [Metric.tendsto_atTop]
  intro ε hε_pos
  have h_eLpNorm_tendsto :=
    eLpNorm_diff_smoothApproxSeqWkpM_tendsto_zero (I := I) (M := M) g m hu_chart
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
            (smoothApproxSeqWkpM (I := I) (M := M) g m hu_chart n) -
          H1ComplToLp (I := I) (M := M) g u_h‖ =
      ‖H1ComplToLp (I := I) (M := M) g u_h -
          smoothToLp (I := I) (M := M) g
            (smoothApproxSeqWkpM (I := I) (M := M) g m hu_chart n)‖ :=
    norm_sub_rev _ _
  rw [h_norm_sub_comm]
  set Δ : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
    H1ComplToLp (I := I) (M := M) g u_h -
      smoothToLp (I := I) (M := M) g
        (smoothApproxSeqWkpM (I := I) (M := M) g m hu_chart n) with hΔ_def
  have h_Δ_coe_ae : (Δ : M → ℝ) =ᵐ[
      riemannianVolumeMeasure (I := I) (M := M) g]
      (fun x => u x -
        (smoothApproxSeqWkpM (I := I) (M := M) g m hu_chart n).toFun x) := by
    have h_sub := MeasureTheory.Lp.coeFn_sub
      (H1ComplToLp (I := I) (M := M) g u_h)
      (smoothToLp (I := I) (M := M) g
        (smoothApproxSeqWkpM (I := I) (M := M) g m hu_chart n))
    have h_smoothToLp_coe :
        (smoothToLp (I := I) (M := M) g
            (smoothApproxSeqWkpM (I := I) (M := M) g m hu_chart n) :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) =ᵐ[
          riemannianVolumeMeasure (I := I) (M := M) g]
        (smoothApproxSeqWkpM (I := I) (M := M) g m hu_chart n).toFun :=
      MemLp.coeFn_toLp
        (smoothApproxSeqWkpM (I := I) (M := M) g m hu_chart n).memLp_two
    filter_upwards [h_sub, h_smoothToLp_coe] with x hx_sub hx_smoothToLp
    rw [hΔ_def, hx_sub, Pi.sub_apply, hx_smoothToLp]
  have h_norm_Δ : ‖Δ‖ = (eLpNorm (fun x => u x -
        (smoothApproxSeqWkpM (I := I) (M := M) g m hu_chart n).toFun x) 2
        (riemannianVolumeMeasure (I := I) (M := M) g)).toReal := by
    rw [Lp.norm_def]
    rw [eLpNorm_congr_ae h_Δ_coe_ae]
  rw [h_norm_Δ]
  have h_eLpNorm_finite : eLpNorm (fun x => u x -
      (smoothApproxSeqWkpM (I := I) (M := M) g m hu_chart n).toFun x) 2
      (riemannianVolumeMeasure (I := I) (M := M) g) ≠ ⊤ := by
    have h_le_half : eLpNorm (fun x => u x -
        (smoothApproxSeqWkpM (I := I) (M := M) g m hu_chart n).toFun x) 2
        (riemannianVolumeMeasure (I := I) (M := M) g) ≤
        ENNReal.ofReal (ε / 2) := h_eLpNorm_le
    refine ne_of_lt ?_
    exact lt_of_le_of_lt h_le_half ENNReal.ofReal_lt_top
  have h_toReal_le : (eLpNorm (fun x => u x -
      (smoothApproxSeqWkpM (I := I) (M := M) g m hu_chart n).toFun x) 2
      (riemannianVolumeMeasure (I := I) (M := M) g)).toReal ≤ ε / 2 := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h_eLpNorm_le
    rw [ENNReal.toReal_ofReal hε_half_pos.le] at this
    exact this
  linarith

set_option maxHeartbeats 800000 in
private lemma inner_smoothToH1Compl_limit_eq_u_h_wkpM
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_chart : MemWkpChart (I := I) (M := M) g (m + 1) 2
      ((H1ComplToLp (I := I) (M := M) g u_h : Lp ℝ 2
        (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
    {u_star : H1Compl g}
    (h_tendsto_star : Tendsto (fun n => smoothToH1Compl (I := I) (M := M) g
        (smoothApproxSeqWkpM (I := I) (M := M) g m hu_chart n)) atTop (𝓝 u_star))
    (f : SmoothScalar g) :
    ⟪smoothToH1Compl (I := I) (M := M) g f, u_star⟫_ℝ =
      ⟪smoothToH1Compl (I := I) (M := M) g f, u_h⟫_ℝ := by
  classical
  have h_inner_star_lim : Tendsto (fun n =>
      ⟪smoothToH1Compl (I := I) (M := M) g f,
        smoothToH1Compl (I := I) (M := M) g
          (smoothApproxSeqWkpM (I := I) (M := M) g m hu_chart n)⟫_ℝ) atTop
        (𝓝 ⟪smoothToH1Compl (I := I) (M := M) g f, u_star⟫_ℝ) :=
    Tendsto.inner tendsto_const_nhds h_tendsto_star
  have h_rewrite : ∀ n,
      ⟪smoothToH1Compl (I := I) (M := M) g f,
        smoothToH1Compl (I := I) (M := M) g
          (smoothApproxSeqWkpM (I := I) (M := M) g m hu_chart n)⟫_ℝ =
      ⟪smoothToLp (I := I) (M := M) g f.oneSubLapClassical,
        smoothToLp (I := I) (M := M) g
          (smoothApproxSeqWkpM (I := I) (M := M) g m hu_chart n)⟫_ℝ := by
    intro n
    rw [inner_smoothToH1Compl_smoothToH1Compl]
    rw [smoothScalarH1Inner_symm]
    exact smoothScalarH1Inner_eq_lpInner_oneSubLap_right (I := I) (M := M) g
      (smoothApproxSeqWkpM (I := I) (M := M) g m hu_chart n) f
  have h_lp_tendsto :=
    smoothToLp_smoothApproxSeqWkpM_tendsto (I := I) (M := M) g m hu_chart
  have h_inner_lp_lim : Tendsto (fun n =>
      ⟪smoothToLp (I := I) (M := M) g f.oneSubLapClassical,
        smoothToLp (I := I) (M := M) g
          (smoothApproxSeqWkpM (I := I) (M := M) g m hu_chart n)⟫_ℝ) atTop
        (𝓝 ⟪smoothToLp (I := I) (M := M) g f.oneSubLapClassical,
          H1ComplToLp (I := I) (M := M) g u_h⟫_ℝ) :=
    Tendsto.inner tendsto_const_nhds h_lp_tendsto
  have h_rewrite_func : (fun n =>
      ⟪smoothToH1Compl (I := I) (M := M) g f,
        smoothToH1Compl (I := I) (M := M) g
          (smoothApproxSeqWkpM (I := I) (M := M) g m hu_chart n)⟫_ℝ) =
      (fun n =>
        ⟪smoothToLp (I := I) (M := M) g f.oneSubLapClassical,
          smoothToLp (I := I) (M := M) g
            (smoothApproxSeqWkpM (I := I) (M := M) g m hu_chart n)⟫_ℝ) := by
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

theorem smoothApproxSeqWkpM_tendsto_h1Compl
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_chart : MemWkpChart (I := I) (M := M) g (m + 1) 2
      ((H1ComplToLp (I := I) (M := M) g u_h : Lp ℝ 2
        (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) :
    Tendsto (fun n =>
      smoothToH1Compl (I := I) (M := M) g
        (smoothApproxSeqWkpM (I := I) (M := M) g m hu_chart n))
      atTop (𝓝 u_h) := by
  classical
  obtain ⟨u_star, h_tendsto_star⟩ :=
    smoothToH1Compl_smoothApproxSeqWkpM_has_limit (I := I) (M := M) g m hu_chart
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
    exact inner_smoothToH1Compl_limit_eq_u_h_wkpM (I := I) (M := M) g m hu_chart
      h_tendsto_star f
  exact congrFun
    ((denseRange_smoothToH1Compl (I := I) (M := M) g).equalizer
      hL_cont hR_cont hLR_smooth) w

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma eLpNorm_le_wkpNorm_m_two
    (m : ℕ) (u : EuclN → ℝ) (Ω : Set EuclN) :
    eLpNorm u 2 ((volume : Measure EuclN).restrict Ω) ≤
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) m 2 u Ω := by
  classical
  have h_iter_eq :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial
        (d := Module.finrank ℝ E) (p := 2) 0 (fun i : Fin 0 => i.elim0) u Ω = u :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial_zero
      (d := Module.finrank ℝ E) (p := 2) (fun i : Fin 0 => i.elim0) u Ω
  have h_zero_le :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.eLpNorm_iterWeakPartial_le_wkpNorm
      (d := Module.finrank ℝ E) (k := m) (p := 2) u Ω 0 (Nat.zero_le m)
      (fun i : Fin 0 => i.elim0)
  rw [h_iter_eq] at h_zero_le
  exact h_zero_le

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma eLpNorm_tendsto_zero_of_wkpNorm_m_two_tendsto_zero
    (m : ℕ) {u : ℕ → EuclN → ℝ} {F_lim : EuclN → ℝ} {Ω : Set EuclN}
    (h_tendsto : Tendsto (fun n =>
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) m 2
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
        (d := Module.finrank ℝ E) m 2
        (fun y => u n y - F_lim y) Ω)
    tendsto_const_nhds h_tendsto
    (fun _ => zero_le _)
    (fun n => eLpNorm_le_wkpNorm_m_two m (fun y => u n y - F_lim y) Ω)

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
      (DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplResidual.smoothFChartResidual
        (I := I) (M := M) g α v) μ := by
  unfold DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplResidual.smoothFChartResidual
    DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fChartResidual
  exact (Lp.stronglyMeasurable _).aestronglyMeasurable.mono_measure (le_refl _)

omit [NeZero (Module.finrank ℝ E)] in
private lemma fChartResidual_aestronglyMeasurable
    (g : SmoothRiemannianMetric I M) (α : M) (u_h : H1Compl (I := I) (M := M) g)
    (μ : Measure EuclN) :
    AEStronglyMeasurable
      (DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fChartResidual
        (I := I) (M := M) g α u_h) μ := by
  unfold DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fChartResidual
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
          DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplResidual.smoothFChartResidual
            (I := I) (M := M) g α (v n) y - F_lim y) 2
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)))
      atTop (𝓝 0)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∀ᵐ y ∂((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)),
        Tendsto (fun n =>
          DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplResidual.smoothFChartResidual
            (I := I) (M := M) g α (v (σ n)) y) atTop
          (𝓝 (F_lim y)) := by
  classical
  have h_aesm_n : ∀ n, AEStronglyMeasurable
      (DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplResidual.smoothFChartResidual
        (I := I) (M := M) g α (v n))
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := fun n =>
    smoothFChartResidual_aestronglyMeasurable (I := I) (M := M) g α (v n) _
  have h_tim : TendstoInMeasure
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α))
      (fun n =>
        DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplResidual.smoothFChartResidual
          (I := I) (M := M) g α (v n))
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
          DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplResidual.smoothFChartResidual
            (I := I) (M := M) g α (v n) y - F y) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)))
      atTop (𝓝 0)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∀ᵐ y ∂((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)),
        Tendsto (fun n =>
          DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplResidual.smoothFChartResidual
            (I := I) (M := M) g α (v (σ n)) y) atTop
          (𝓝 (F y)) := by
  classical
  have h_aesm_n : ∀ n, AEStronglyMeasurable
      (DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplResidual.smoothFChartResidual
        (I := I) (M := M) g α (v n))
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := fun n =>
    smoothFChartResidual_aestronglyMeasurable (I := I) (M := M) g α (v n) _
  have h_tim : TendstoInMeasure
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α))
      (fun n =>
        DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplResidual.smoothFChartResidual
          (I := I) (M := M) g α (v n))
      atTop F :=
    MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm
      (μ := (chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α))
      (p := 2) (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      h_aesm_n hF_aesm h_tendsto
  exact h_tim.exists_seq_tendsto_ae

theorem smoothApproxSeqWkpM_smoothFChartResidual_limit_eq_fChartResidual_wkpM
    (g : SmoothRiemannianMetric I M) (α : M) (m : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_chart : MemWkpChart (I := I) (M := M) g (m + 1) 2
      ((H1ComplToLp (I := I) (M := M) g u_h : Lp ℝ 2
        (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) :
    ∀ F_lim : EuclN → ℝ,
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) m 2 F_lim
        (chartTargetEuclid (I := I) (M := M) α) →
      Tendsto (fun n =>
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) m 2
          (fun y =>
            DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplResidual.smoothFChartResidual
              (I := I) (M := M) g α
              (smoothApproxSeqWkpM (I := I) (M := M) g m hu_chart n) y -
            F_lim y)
          (chartTargetEuclid (I := I) (M := M) α))
        atTop (𝓝 0) →
      F_lim =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)]
        DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fChartResidual
          (I := I) (M := M) g α u_h := by
  classical
  intro F_lim h_F_lim_memWkp h_wkp_tendsto
  set v : ℕ → SmoothScalar g := fun n =>
    smoothApproxSeqWkpM (I := I) (M := M) g m hu_chart n with hv_def
  have hF_lim_memLp : MemLp F_lim 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.memLp h_F_lim_memWkp
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
            DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplResidual.smoothFChartResidual
              (I := I) (M := M) g α (v n) y - F_lim y) 2
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)))
        atTop (𝓝 0) :=
    eLpNorm_tendsto_zero_of_wkpNorm_m_two_tendsto_zero m
      (u := fun n =>
        DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplResidual.smoothFChartResidual
          (I := I) (M := M) g α (v n))
      (F_lim := F_lim)
      (Ω := chartTargetEuclid (I := I) (M := M) α)
      h_wkp_tendsto
  have h_h1Compl_tendsto : Tendsto (fun n =>
      smoothToH1Compl (I := I) (M := M) g (v n))
      atTop (𝓝 u_h) :=
    smoothApproxSeqWkpM_tendsto_h1Compl (I := I) (M := M) g m hu_chart
  have h_eLpNorm_weighted_tendsto :
      Tendsto (fun n =>
        eLpNorm (fun y =>
            DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplResidual.smoothFChartResidual
              (I := I) (M := M) g α (v n) y -
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
            DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplResidual.smoothFChartResidual
              (I := I) (M := M) g α (v (σ n)) y -
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
          DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplResidual.smoothFChartResidual
            (I := I) (M := M) g α (v (σ (τ n))) y) atTop
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
          DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplResidual.smoothFChartResidual
            (I := I) (M := M) g α (v (σ (τ n))) y) atTop
          (𝓝 ((DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fChartResidual
              (I := I) (M := M) g α u_h) y)) :=
    h_vol_abs.ae_le hτ_ae
  filter_upwards [h_volume_ae_σ_τ, h_volume_ae_σ_τ_fChart]
    with y h_to_Flim h_to_fChart
  exact tendsto_nhds_unique h_to_Flim h_to_fChart

theorem fChartResidual_memWkp_m
    (g : SmoothRiemannianMetric I M) (α : M) (m : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_chart : MemWkpChart (I := I) (M := M) g (m + 1) 2
      ((H1ComplToLp (I := I) (M := M) g u_h : Lp ℝ 2
        (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) m 2
      (DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fChartResidual
        (I := I) (M := M) g α u_h)
      (chartTargetEuclid (I := I) (M := M) α) :=
  memWkp_fChartResidual_of_wkpNorm_cauchy_identification_wkpM
    (I := I) (M := M) g α m u_h
    (fun n => smoothApproxSeqWkpM (I := I) (M := M) g m hu_chart n)
    (smoothApproxSeq_smoothFChartResidual_wkpNorm_cauchy_wkpM
      (I := I) (M := M) g α m hu_chart)
    (smoothApproxSeqWkpM_smoothFChartResidual_limit_eq_fChartResidual_wkpM
      (I := I) (M := M) g α m hu_chart)

noncomputable def fChartPiecePreimageGeneral
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h_lapdom : u_h ∈ laplacianDomain (I := I) (M := M) g) : EuclN → ℝ :=
  DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
    (I := I) (M := M) (chartAtlasPOU I M) α
    ((laplacianDomain.preimage (I := I) (M := M) g ⟨u_h, hu_h_lapdom⟩ :
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)

private noncomputable def smoothMulLpRhoPreimageGeneral
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h_lapdom : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  smoothMulLp (I := I) (M := M) g (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
    (laplacianDomain.preimage (I := I) (M := M) g ⟨u_h, hu_h_lapdom⟩)

omit [NeZero (Module.finrank ℝ E)] in
private lemma fHLeibniz_eq_piecePreimage_add_residual_general
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h_lapdom : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    leibnizCompensatedSource (I := I) (M := M) g α u_h hu_h_lapdom =
      smoothMulLpRhoPreimageGeneral (I := I) (M := M) g α hu_h_lapdom +
        fHLeibnizResidualLp (I := I) (M := M) g α u_h := by
  classical
  unfold smoothMulLpRhoPreimageGeneral fHLeibnizResidualLp
  rw [fHLeibniz_def]
  have h_diff_eq :
      H1ComplToLp (I := I) (M := M) g u_h -
        laplacianOp (I := I) (M := M) g ⟨u_h, hu_h_lapdom⟩ =
      laplacianDomain.preimage (I := I) (M := M) g ⟨u_h, hu_h_lapdom⟩ := by
    rw [laplacianOp_apply]
    abel
  rw [h_diff_eq]
  abel

omit [NeZero (Module.finrank ℝ E)] in
private lemma chartPushedRawLpFromLp_smoothMulLpRhoPreimageGeneral_coeFn_aeEq
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h_lapdom : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    ((chartPushedRawLpFromLp (I := I) (M := M) g α
        (smoothMulLpRhoPreimageGeneral (I := I) (M := M) g α hu_h_lapdom) :
        Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ)
      =ᵐ[(chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      fChartPiecePreimageGeneral (I := I) (M := M) g α hu_h_lapdom := by
  classical
  have h_coeFn := chartPushedRawLpFromLp_coeFn (I := I) (M := M) g α
    (smoothMulLpRhoPreimageGeneral (I := I) (M := M) g α hu_h_lapdom)
  have h_smoothMulLp_ae : (smoothMulLpRhoPreimageGeneral (I := I) (M := M) g α hu_h_lapdom :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      (fun x : M => (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x *
        ((laplacianDomain.preimage (I := I) (M := M) g ⟨u_h, hu_h_lapdom⟩ :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x) := by
    unfold smoothMulLpRhoPreimageGeneral
    exact smoothMulLp_apply_coeFn (I := I) (M := M) g _ _
  have h_smoothMul_meas :
      Measurable ((smoothMulLpRhoPreimageGeneral (I := I) (M := M) g α hu_h_lapdom :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) :=
    (Lp.stronglyMeasurable _).measurable
  have h_prod_meas :
      Measurable (fun x : M => (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x *
        ((laplacianDomain.preimage (I := I) (M := M) g ⟨u_h, hu_h_lapdom⟩ :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x) := by
    refine Measurable.mul ?_ ?_
    · exact ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff.continuous).measurable
    · exact (Lp.stronglyMeasurable _).measurable
  have h_chartPushedRaw_ae :
      DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw (I := I) α
        ((smoothMulLpRhoPreimageGeneral (I := I) (M := M) g α hu_h_lapdom :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =ᵐ[
        (chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw (I := I) α
        (fun x : M => (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x *
          ((laplacianDomain.preimage (I := I) (M := M) g ⟨u_h, hu_h_lapdom⟩ :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x) :=
    DifferentialGeometry.Analysis.Laplacian.LaplacianDomainChartData.chartPushedRaw_aeEq_of_aeEq
      (I := I) (M := M) g α h_smoothMul_meas h_prod_meas h_smoothMulLp_ae
  have h_chartTarget_meas : MeasurableSet
      (chartTargetEuclid (I := I) (M := M) α) :=
    (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
  have h_weighted_restrict_self :
      ∀ᵐ y ∂((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)),
      y ∈ chartTargetEuclid (I := I) (M := M) α := by
    rw [ae_restrict_iff' h_chartTarget_meas]
    exact Filter.Eventually.of_forall (fun _ h => h)
  filter_upwards [h_coeFn, h_chartPushedRaw_ae, h_weighted_restrict_self]
    with y hy_coeFn hy_chart hy_in
  rw [hy_coeFn, hy_chart]
  unfold fChartPiecePreimageGeneral
  exact (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed_eq_chartPushedRaw_pou_mul_on_target
    (I := I) (M := M) (chartAtlasPOU I M) α
    ((laplacianDomain.preimage (I := I) (M := M) g ⟨u_h, hu_h_lapdom⟩ :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) hy_in).symm

private lemma base_f_chart_ae_eq_piecePreimage_add_residual_general_weighted
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h_lapdom : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
      hu_h_lapdom).f_chart
      =ᵐ[(chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)]
      (fun y => fChartPiecePreimageGeneral (I := I) (M := M) g α hu_h_lapdom y +
        DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fChartResidual
          (I := I) (M := M) g α u_h y) := by
  classical
  have h_base_def := chartBilinearH1ComplData_of_laplacianDomain_f_chart_def
    (I := I) (M := M) g α hu_h_lapdom
  have h_fHLeibniz_decomp := fHLeibniz_eq_piecePreimage_add_residual_general
    (I := I) (M := M) g α hu_h_lapdom
  have h_chartPushedRaw_add_ae :
      ((chartPushedRawLpFromLp (I := I) (M := M) g α
          (smoothMulLpRhoPreimageGeneral (I := I) (M := M) g α hu_h_lapdom +
            fHLeibnizResidualLp (I := I) (M := M) g α u_h) :
          Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ)
        =ᵐ[(chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)]
        (fun y =>
          ((chartPushedRawLpFromLp (I := I) (M := M) g α
              (smoothMulLpRhoPreimageGeneral (I := I) (M := M) g α hu_h_lapdom) :
              Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
                (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y +
          ((chartPushedRawLpFromLp (I := I) (M := M) g α
              (fHLeibnizResidualLp (I := I) (M := M) g α u_h) :
              Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
                (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y) := by
    have h_FG_coeFn := chartPushedRawLpFromLp_coeFn (I := I) (M := M) g α
      (smoothMulLpRhoPreimageGeneral (I := I) (M := M) g α hu_h_lapdom +
        fHLeibnizResidualLp (I := I) (M := M) g α u_h)
    have h_F_coeFn := chartPushedRawLpFromLp_coeFn (I := I) (M := M) g α
      (smoothMulLpRhoPreimageGeneral (I := I) (M := M) g α hu_h_lapdom)
    have h_G_coeFn := chartPushedRawLpFromLp_coeFn (I := I) (M := M) g α
      (fHLeibnizResidualLp (I := I) (M := M) g α u_h)
    set F : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
      smoothMulLpRhoPreimageGeneral (I := I) (M := M) g α hu_h_lapdom with hF_def
    set G : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
      fHLeibnizResidualLp (I := I) (M := M) g α u_h with hG_def
    set sumFun : M → ℝ := fun x =>
      ((F : Lp ℝ 2 _) : M → ℝ) x + ((G : Lp ℝ 2 _) : M → ℝ) x with hsumFun_def
    have h_sum_coe : ((F + G : Lp ℝ 2 _) : M → ℝ) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g] sumFun :=
      MeasureTheory.Lp.coeFn_add F G
    have h_FG_meas : Measurable ((F + G : Lp ℝ 2 _) : M → ℝ) :=
      (Lp.stronglyMeasurable (F + G)).measurable
    have hF_meas : Measurable ((F : Lp ℝ 2 _) : M → ℝ) :=
      (Lp.stronglyMeasurable F).measurable
    have hG_meas : Measurable ((G : Lp ℝ 2 _) : M → ℝ) :=
      (Lp.stronglyMeasurable G).measurable
    have hsum_meas : Measurable sumFun := hF_meas.add hG_meas
    have h_chartPushedRaw_FG :
        DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw (I := I) α
          ((F + G : Lp ℝ 2 _) : M → ℝ) =ᵐ[
          (chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)]
        DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw (I := I) α
          sumFun :=
      DifferentialGeometry.Analysis.Laplacian.LaplacianDomainChartData.chartPushedRaw_aeEq_of_aeEq
        (I := I) (M := M) g α h_FG_meas hsum_meas h_sum_coe
    have h_chartPushedRaw_sum_pointwise :
        ∀ y : EuclN,
          DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw (I := I) α
            sumFun y =
          DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw (I := I) α
            ((F : Lp ℝ 2 _) : M → ℝ) y +
          DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw (I := I) α
            ((G : Lp ℝ 2 _) : M → ℝ) y := by
      intro y
      by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
      · rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_mem
          (I := I) (M := M) (α := α) sumFun hy,
          DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_mem
            (I := I) (M := M) (α := α) ((F : Lp ℝ 2 _) : M → ℝ) hy,
          DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_mem
            (I := I) (M := M) (α := α) ((G : Lp ℝ 2 _) : M → ℝ) hy]
      · rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_notMem
          (I := I) (M := M) (α := α) sumFun hy,
          DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_notMem
            (I := I) (M := M) (α := α) ((F : Lp ℝ 2 _) : M → ℝ) hy,
          DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_notMem
            (I := I) (M := M) (α := α) ((G : Lp ℝ 2 _) : M → ℝ) hy]
        ring
    filter_upwards [h_FG_coeFn, h_F_coeFn, h_G_coeFn, h_chartPushedRaw_FG]
      with y hy_FG hy_F hy_G hy_chart
    rw [hy_FG, hy_chart, h_chartPushedRaw_sum_pointwise y]
    rw [← hy_F, ← hy_G]
  have h_piece1 := chartPushedRawLpFromLp_smoothMulLpRhoPreimageGeneral_coeFn_aeEq
    (I := I) (M := M) g α hu_h_lapdom
  rw [h_base_def, h_fHLeibniz_decomp]
  filter_upwards [h_chartPushedRaw_add_ae, h_piece1] with y hy_add hy_piece1
  rw [hy_add, hy_piece1]
  rfl

lemma base_f_chart_ae_eq_piecePreimage_add_residual_general
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h_lapdom : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
      hu_h_lapdom).f_chart
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)]
      (fun y => fChartPiecePreimageGeneral (I := I) (M := M) g α hu_h_lapdom y +
        DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fChartResidual
          (I := I) (M := M) g α u_h y) := by
  classical
  exact (volume_restrict_chartTarget_absolutelyContinuous_weighted
    (I := I) (M := M) g α).ae_le
    (base_f_chart_ae_eq_piecePreimage_add_residual_general_weighted
      (I := I) (M := M) g α hu_h_lapdom)

omit [NeZero (Module.finrank ℝ E)] in
lemma fChartPiecePreimageGeneral_memWkp_of_memWkpChart
    (g : SmoothRiemannianMetric I M) (α : M) (m : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h_lapdom : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (h_rhs : MemWkpChart (I := I) (M := M) g m 2
      ((laplacianDomain.preimage (I := I) (M := M) g ⟨u_h, hu_h_lapdom⟩ :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) m 2
      (fChartPiecePreimageGeneral (I := I) (M := M) g α hu_h_lapdom)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  unfold fChartPiecePreimageGeneral
  exact h_rhs α

theorem base_f_chart_memWkp_m
    (g : SmoothRiemannianMetric I M) (α : M) (m : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h_lapdom : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (h_chart_H_m_plus_1_u :
      MemWkpChart (I := I) (M := M) g (m + 1) 2
        ((H1ComplToLp (I := I) (M := M) g u_h : Lp ℝ 2
          (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
    (h_chart_H_m_RHS :
      MemWkpChart (I := I) (M := M) g m 2
        ((laplacianDomain.preimage (I := I) (M := M) g ⟨u_h, hu_h_lapdom⟩ :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) m 2
      (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
        hu_h_lapdom).f_chart
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have h_decomp := base_f_chart_ae_eq_piecePreimage_add_residual_general
    (I := I) (M := M) g α hu_h_lapdom
  have h_piece1_memWkp := fChartPiecePreimageGeneral_memWkp_of_memWkpChart
    (I := I) (M := M) g α m hu_h_lapdom h_chart_H_m_RHS
  have h_residual_memWkp := fChartResidual_memWkp_m
    (I := I) (M := M) g α m h_chart_H_m_plus_1_u
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hp_one : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have h_sum_memWkp :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) m 2
        (fun y => fChartPiecePreimageGeneral (I := I) (M := M) g α hu_h_lapdom y +
          DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fChartResidual
            (I := I) (M := M) g α u_h y)
        (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.add hp_one hΩ_open
      h_piece1_memWkp h_residual_memWkp
  exact (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_congr_ae
    hp_one hΩ_open h_decomp.symm).mp h_sum_memWkp

end IteratedBaseFChartRegularityB
end Laplacian
end Analysis
end DifferentialGeometry

end
