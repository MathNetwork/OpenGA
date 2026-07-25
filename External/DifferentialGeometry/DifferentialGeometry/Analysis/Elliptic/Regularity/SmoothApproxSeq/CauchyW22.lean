import DifferentialGeometry.Analysis.Elliptic.Regularity.FChartResidual.MemW1pResidualFull
import DifferentialGeometry.Analysis.Elliptic.Regularity.SmoothFChartResidual.BilinearBoundW22
import DifferentialGeometry.Analysis.Elliptic.Regularity.SmoothFChartResidual.Linearity
import DifferentialGeometry.Analysis.Elliptic.Regularity.ChartPushed.MemWkpThreeSmooth


noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace SmoothApproxSeqCauchyW22

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainChartData
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplResidual
open DifferentialGeometry.Analysis.Laplacian.SmoothFChartResidualBilinearBoundW22
open DifferentialGeometry.Analysis.Laplacian.SmoothFChartResidualLinearity
open DifferentialGeometry.Analysis.Laplacian.ChartPushedMemWkpThreeSmooth
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

theorem H1ComplToLp_memWkpChart_three_two
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    MemWkpChart (I := I) (M := M) g 3 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) := by
  intro α
  exact chartPushed_memWkp_three_two_of_laplacianDomainPow_two
    (I := I) (M := M) g α hu_h

theorem exists_smoothApprox_chartW32
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ v : SmoothScalar g, wkpNormChart (I := I) (M := M) g 3 2
      (fun x => ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x -
        v.toFun x) ≤ ENNReal.ofReal ε := by
  classical
  set u : M → ℝ := ((H1ComplToLp (I := I) (M := M) g u_h :
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) with hu_def
  have h_u_mem : MemWkpChart (I := I) (M := M) g 3 2 u :=
    H1ComplToLp_memWkpChart_three_two (I := I) (M := M) g hu_h
  obtain ⟨w, hw_smooth, hw_le⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Chart.contMDiff_dense_in_WkpChart_k
      (I := I) (M := M) g 3 (p := 2) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) h_u_mem hε
  refine ⟨⟨w, hw_smooth⟩, ?_⟩
  exact hw_le

noncomputable def smoothApproxSeqWkpThree
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (n : ℕ) : SmoothScalar g :=
  (exists_smoothApprox_chartW32 (I := I) (M := M) g hu_h
    (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1))).choose

theorem smoothApproxSeqWkpThree_wkpNormChart_le
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (n : ℕ) :
    wkpNormChart (I := I) (M := M) g 3 2
      (fun x => ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x -
        (smoothApproxSeqWkpThree (I := I) (M := M) g hu_h n).toFun x) ≤
      ENNReal.ofReal (1 / ((n : ℝ) + 1)) :=
  (exists_smoothApprox_chartW32 (I := I) (M := M) g hu_h
    (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1))).choose_spec

theorem smoothApproxSeqWkpThree_wkpNormChart_diff_le
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (m n : ℕ) :
    wkpNormChart (I := I) (M := M) g 3 2
      (fun x => (smoothApproxSeqWkpThree (I := I) (M := M) g hu_h m).toFun x -
        (smoothApproxSeqWkpThree (I := I) (M := M) g hu_h n).toFun x) ≤
      ENNReal.ofReal (1 / ((m : ℝ) + 1)) + ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
  classical
  set u : M → ℝ := ((H1ComplToLp (I := I) (M := M) g u_h :
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) with hu_def
  set vm : SmoothScalar g := smoothApproxSeqWkpThree (I := I) (M := M) g hu_h m
  set vn : SmoothScalar g := smoothApproxSeqWkpThree (I := I) (M := M) g hu_h n
  have h_decomp : (fun x => vm.toFun x - vn.toFun x) =
      (fun x => (u x - vn.toFun x) - (u x - vm.toFun x)) := by
    funext x; ring
  rw [h_decomp]
  have h_u_mem : MemWkpChart (I := I) (M := M) g 3 2 u :=
    H1ComplToLp_memWkpChart_three_two (I := I) (M := M) g hu_h
  have hp_one : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have h_smooth_vm : MemWkpChart (I := I) (M := M) g 3 2 vm.toFun :=
    DifferentialGeometry.Analysis.Sobolev.Chart.memWkpChart_of_contMDiff_k
      (I := I) (M := M) g hp_one 3 vm.smooth
  have h_smooth_vn : MemWkpChart (I := I) (M := M) g 3 2 vn.toFun :=
    DifferentialGeometry.Analysis.Sobolev.Chart.memWkpChart_of_contMDiff_k
      (I := I) (M := M) g hp_one 3 vn.smooth
  have h_u_diff_vm : MemWkpChart (I := I) (M := M) g 3 2 (fun x => u x - vm.toFun x) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart_sub
      (I := I) (M := M) g hp_one h_u_mem h_smooth_vm
  have h_u_diff_vn : MemWkpChart (I := I) (M := M) g 3 2 (fun x => u x - vn.toFun x) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart_sub
      (I := I) (M := M) g hp_one h_u_mem h_smooth_vn
  have h_split : (fun x : M => (u x - vn.toFun x) - (u x - vm.toFun x)) =
      (fun x : M => (u x - vn.toFun x) + (-1 : ℝ) * (u x - vm.toFun x)) := by
    funext x; ring
  rw [h_split]
  have h_neg_smul :
      wkpNormChart (I := I) (M := M) g 3 2
        (fun x => (-1 : ℝ) * (u x - vm.toFun x)) =
      ‖(-1 : ℝ)‖ₑ * wkpNormChart (I := I) (M := M) g 3 2 (fun x => u x - vm.toFun x) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart_const_smul
      (I := I) (M := M) g hp_one (-1 : ℝ) h_u_diff_vm
  have h_neg_one_norm : ‖(-1 : ℝ)‖ₑ = 1 := by
    simp [enorm]
  rw [h_neg_one_norm, one_mul] at h_neg_smul
  have h_u_diff_vm_neg : MemWkpChart (I := I) (M := M) g 3 2
      (fun x => (-1 : ℝ) * (u x - vm.toFun x)) := by
    have h_eq : (fun x : M => (-1 : ℝ) * (u x - vm.toFun x)) =
        (fun x => -(u x - vm.toFun x)) := by funext x; ring
    rw [h_eq]
    exact DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart_neg
      (I := I) (M := M) g hp_one h_u_diff_vm
  have h_add :=
    DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart_add_le (I := I) (M := M)
      g (k := 3) (p := 2) hp_one h_u_diff_vn h_u_diff_vm_neg
  rw [h_neg_smul] at h_add
  have h_bound1 : wkpNormChart (I := I) (M := M) g 3 2 (fun x => u x - vn.toFun x) +
        wkpNormChart (I := I) (M := M) g 3 2 (fun x => u x - vm.toFun x) ≤
      ENNReal.ofReal (1 / ((n : ℝ) + 1)) + ENNReal.ofReal (1 / ((m : ℝ) + 1)) :=
    add_le_add
      (smoothApproxSeqWkpThree_wkpNormChart_le (I := I) (M := M) g hu_h n)
      (smoothApproxSeqWkpThree_wkpNormChart_le (I := I) (M := M) g hu_h m)
  have h_comm : ENNReal.ofReal (1 / ((n : ℝ) + 1)) + ENNReal.ofReal (1 / ((m : ℝ) + 1)) =
      ENNReal.ofReal (1 / ((m : ℝ) + 1)) + ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
    rw [add_comm]
  exact le_trans h_add (le_of_le_of_eq h_bound1 h_comm)

theorem smoothApproxSeq_smoothFChartResidual_wkpNorm_cauchy_w22
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    ∀ ε > 0, ∃ N, ∀ m n, N ≤ m → N ≤ n →
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 2 2
        (fun y =>
          DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplResidual.smoothFChartResidual
            (I := I) (M := M) g α
            (smoothApproxSeqWkpThree (I := I) (M := M) g hu_h m) y -
          DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplResidual.smoothFChartResidual
            (I := I) (M := M) g α
            (smoothApproxSeqWkpThree (I := I) (M := M) g hu_h n) y)
        (chartTargetEuclid (I := I) (M := M) α) ≤ ENNReal.ofReal ε := by
  classical
  intro ε hε
  obtain ⟨C, hC_pos, hC_bound⟩ :=
    wkpNorm_smoothFChartResidual_le_wkpNormChart_w22 (I := I) (M := M) g α
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
  intro m n hm hn
  set vm : SmoothScalar g := smoothApproxSeqWkpThree (I := I) (M := M) g hu_h m
    with hvm_def
  set vn : SmoothScalar g := smoothApproxSeqWkpThree (I := I) (M := M) g hu_h n
    with hvn_def
  set vdiff : SmoothScalar g := smoothScalarSub vm vn with hvdiff_def
  have hvdiff_toFun :
      vdiff.toFun = fun x => vm.toFun x - vn.toFun x :=
    smoothScalarSub_toFun vm vn
  have h_ae_sub :=
    smoothFChartResidual_ae_sub (I := I) (M := M) g α vm vn vdiff hvdiff_toFun
  have h_wkp_eq :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 2 2
        (fun y =>
          DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplResidual.smoothFChartResidual
            (I := I) (M := M) g α vm y -
          DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplResidual.smoothFChartResidual
            (I := I) (M := M) g α vn y)
        (chartTargetEuclid (I := I) (M := M) α) =
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 2 2
        (DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplResidual.smoothFChartResidual
          (I := I) (M := M) g α vdiff)
        (chartTargetEuclid (I := I) (M := M) α) := by
    refine DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_congr_ae
      (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (chartTargetEuclid_isOpen (I := I) (M := M) α) ?_
    exact h_ae_sub.symm
  rw [h_wkp_eq]
  have h_bilinear := hC_bound vdiff
  have h_chartW32_cauchy :
      wkpNormChart (I := I) (M := M) g 3 2 vdiff.toFun ≤
        ENNReal.ofReal ((1 : ℝ) / ((m : ℝ) + 1)) +
          ENNReal.ofReal ((1 : ℝ) / ((n : ℝ) + 1)) := by
    rw [hvdiff_toFun]
    exact smoothApproxSeqWkpThree_wkpNormChart_diff_le (I := I) (M := M) g hu_h m n
  have h_step :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 2 2
        (DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplResidual.smoothFChartResidual
          (I := I) (M := M) g α vdiff)
        (chartTargetEuclid (I := I) (M := M) α) ≤
      ENNReal.ofReal C *
        (ENNReal.ofReal ((1 : ℝ) / ((m : ℝ) + 1)) +
          ENNReal.ofReal ((1 : ℝ) / ((n : ℝ) + 1))) := by
    refine h_bilinear.trans ?_
    exact mul_le_mul_of_nonneg_left h_chartW32_cauchy (zero_le _)
  refine h_step.trans ?_
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
  have hm_ofReal_le :
      ENNReal.ofReal ((1 : ℝ) / ((m : ℝ) + 1)) ≤
        ENNReal.ofReal ((1 : ℝ) / ((N0 : ℝ) + 1)) :=
    ENNReal.ofReal_le_ofReal hm_inv_le
  have hn_ofReal_le :
      ENNReal.ofReal ((1 : ℝ) / ((n : ℝ) + 1)) ≤
        ENNReal.ofReal ((1 : ℝ) / ((N0 : ℝ) + 1)) :=
    ENNReal.ofReal_le_ofReal hn_inv_le
  have hsum_le :
      ENNReal.ofReal ((1 : ℝ) / ((m : ℝ) + 1)) +
        ENNReal.ofReal ((1 : ℝ) / ((n : ℝ) + 1)) ≤
      ENNReal.ofReal ((1 : ℝ) / ((N0 : ℝ) + 1)) +
        ENNReal.ofReal ((1 : ℝ) / ((N0 : ℝ) + 1)) :=
    add_le_add hm_ofReal_le hn_ofReal_le
  have hC_step :
      ENNReal.ofReal C *
        (ENNReal.ofReal ((1 : ℝ) / ((m : ℝ) + 1)) +
          ENNReal.ofReal ((1 : ℝ) / ((n : ℝ) + 1))) ≤
      ENNReal.ofReal C *
        (ENNReal.ofReal ((1 : ℝ) / ((N0 : ℝ) + 1)) +
          ENNReal.ofReal ((1 : ℝ) / ((N0 : ℝ) + 1))) :=
    mul_le_mul_of_nonneg_left hsum_le (zero_le _)
  refine hC_step.trans ?_
  have hN0_inv_pos : (0 : ℝ) ≤ (1 : ℝ) / ((N0 : ℝ) + 1) := by positivity
  have h_add :
      ENNReal.ofReal ((1 : ℝ) / ((N0 : ℝ) + 1)) +
        ENNReal.ofReal ((1 : ℝ) / ((N0 : ℝ) + 1)) =
      ENNReal.ofReal (2 * ((1 : ℝ) / ((N0 : ℝ) + 1))) := by
    rw [show (2 : ℝ) * ((1 : ℝ) / ((N0 : ℝ) + 1)) =
        ((1 : ℝ) / ((N0 : ℝ) + 1)) + ((1 : ℝ) / ((N0 : ℝ) + 1)) by ring,
      ENNReal.ofReal_add hN0_inv_pos hN0_inv_pos]
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

end SmoothApproxSeqCauchyW22
end Laplacian
end Analysis
end DifferentialGeometry

end
