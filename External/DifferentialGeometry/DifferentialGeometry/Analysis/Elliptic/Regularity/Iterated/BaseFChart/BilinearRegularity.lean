import DifferentialGeometry.Analysis.Elliptic.Regularity.SmoothFChartResidual.BilinearBound
import DifferentialGeometry.Analysis.Elliptic.Regularity.SmoothFChartResidual.BilinearBoundW22
import DifferentialGeometry.Analysis.Elliptic.Regularity.SmoothFChartResidual.Linearity
import DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.ResidualRegularity.BilinearH1ComplFromDomainPow
import DifferentialGeometry.Analysis.Elliptic.Regularity.SmoothApproxSeq.H1ComplTendsto
import DifferentialGeometry.Analysis.Sobolev.Chart.SmoothDensity.StrictCutoffPushforwardBound
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Multiplication.MultiplyQuantK
import DifferentialGeometry.Analysis.Sobolev.Manifold.IteratedSobolevEmbedding


noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace IteratedBaseFChartRegularity

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
open DifferentialGeometry.Analysis.Laplacian.GradInnerCLMChartFormula
open DifferentialGeometry.Analysis.Laplacian.SmoothFChartResidualBilinearBound
open DifferentialGeometry.Analysis.Sobolev.Chart

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] in
private lemma memWkp_chartPushedRaw_etaTimesV_succ
    (g : SmoothRiemannianMetric I M) (α : M) (m : ℕ) (v : SmoothScalar g) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (m + 1) 2
      (chartPushedRaw (I := I) (M := M) α
        (etaTimesV (I := I) (M := M) α v.toFun))
      (chartTargetEuclid (I := I) (M := M) α) := by
  have hηv_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (etaTimesV (I := I) (M := M) α v.toFun) :=
    etaTimesV_smooth (I := I) (M := M) α v.smooth
  have hηv_supp : tsupport (etaTimesV (I := I) (M := M) α v.toFun) ⊆
      (chartAt H α).source :=
    tsupport_etaTimesV_subset (I := I) (M := M) α v.toFun
  have hCP_smooth : ContDiff ℝ ∞
      (chartPushedRaw (I := I) (M := M) α
        (etaTimesV (I := I) (M := M) α v.toFun)) :=
    chartPushedRaw_contDiff (I := I) (M := M) hηv_smooth hηv_supp
  have hCP_cpt : HasCompactSupport
      (chartPushedRaw (I := I) (M := M) α
        (etaTimesV (I := I) (M := M) α v.toFun)) :=
    chartPushedRaw_smooth_hasCompactSupport_local (I := I) (M := M) hηv_supp
  have hCP_tsupp : tsupport (chartPushedRaw (I := I) (M := M) α
        (etaTimesV (I := I) (M := M) α v.toFun)) ⊆
      chartTargetEuclid (I := I) (M := M) α :=
    tsupport_chartPushedRaw_subset_chartTargetEuclid (I := I) (M := M) hηv_supp
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_of_smooth_compactSupport
    (d := Module.finrank ℝ E)
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    hCP_smooth hCP_cpt hCP_tsupp (by norm_num : (1 : ℝ≥0∞) ≤ 2) (m + 1)

omit [NeZero (Module.finrank ℝ E)] in
private lemma memWkp_chartPushedRaw_etaTimesV
    (g : SmoothRiemannianMetric I M) (α : M) (m : ℕ) (v : SmoothScalar g) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) m 2
      (chartPushedRaw (I := I) (M := M) α
        (etaTimesV (I := I) (M := M) α v.toFun))
      (chartTargetEuclid (I := I) (M := M) α) := by
  have hηv_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (etaTimesV (I := I) (M := M) α v.toFun) :=
    etaTimesV_smooth (I := I) (M := M) α v.smooth
  have hηv_supp : tsupport (etaTimesV (I := I) (M := M) α v.toFun) ⊆
      (chartAt H α).source :=
    tsupport_etaTimesV_subset (I := I) (M := M) α v.toFun
  have hCP_smooth : ContDiff ℝ ∞
      (chartPushedRaw (I := I) (M := M) α
        (etaTimesV (I := I) (M := M) α v.toFun)) :=
    chartPushedRaw_contDiff (I := I) (M := M) hηv_smooth hηv_supp
  have hCP_cpt : HasCompactSupport
      (chartPushedRaw (I := I) (M := M) α
        (etaTimesV (I := I) (M := M) α v.toFun)) :=
    chartPushedRaw_smooth_hasCompactSupport_local (I := I) (M := M) hηv_supp
  have hCP_tsupp : tsupport (chartPushedRaw (I := I) (M := M) α
        (etaTimesV (I := I) (M := M) α v.toFun)) ⊆
      chartTargetEuclid (I := I) (M := M) α :=
    tsupport_chartPushedRaw_subset_chartTargetEuclid (I := I) (M := M) hηv_supp
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_of_smooth_compactSupport
    (d := Module.finrank ℝ E)
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    hCP_smooth hCP_cpt hCP_tsupp (by norm_num : (1 : ℝ≥0∞) ≤ 2) m

omit [NeZero (Module.finrank ℝ E)] in
private lemma memWkp_partialDerivOnEuclid_etaTimesV
    (g : SmoothRiemannianMetric I M) (α : M) (m : ℕ) (v : SmoothScalar g)
    (i : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) m 2
      (partialDerivOnEuclid (I := I) (M := M) α i
        (etaTimesV (I := I) (M := M) α v.toFun))
      (chartTargetEuclid (I := I) (M := M) α) := by
  have hηv_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (etaTimesV (I := I) (M := M) α v.toFun) :=
    etaTimesV_smooth (I := I) (M := M) α v.smooth
  have hηv_supp : tsupport (etaTimesV (I := I) (M := M) α v.toFun) ⊆
      (chartAt H α).source :=
    tsupport_etaTimesV_subset (I := I) (M := M) α v.toFun
  have h_chartPushed_succ := memWkp_chartPushedRaw_etaTimesV_succ
    (I := I) (M := M) g α m v
  have h_chosen_mem :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) m 2
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          (d := Module.finrank ℝ E) 2 i
          (chartPushedRaw (I := I) (M := M) α
            (etaTimesV (I := I) (M := M) α v.toFun))
          (chartTargetEuclid (I := I) (M := M) α))
        (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.chosenWeakPartial_mem
      h_chartPushed_succ i
  have h_ae := partialDerivOnEuclid_ae_eq_chosenWeakPartial
    (I := I) (M := M) (α := α) (i := i) hηv_smooth hηv_supp
    (p := (2 : ℝ≥0∞)) (by norm_num)
  exact (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_congr_ae
    (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    (chartTargetEuclid_isOpen (I := I) (M := M) α) h_ae).mpr h_chosen_mem

private lemma wkpNorm_chartPushedRaw_etaTimesV_le_succ
    (g : SmoothRiemannianMetric I M) (α : M) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : SmoothScalar g,
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) (m + 1) 2
        (chartPushedRaw (I := I) (M := M) α
          (etaTimesV (I := I) (M := M) α v.toFun))
        (chartTargetEuclid (I := I) (M := M) α) ≤
      ENNReal.ofReal C * wkpNormChart (I := I) (M := M) g (m + 1) 2
        (fun x : M => v.toFun x) := by
  classical
  obtain ⟨C, hC_pos, hC_bound⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Chart.wkpNorm_chartPushedRaw_strictCutoff_mul_le
      (I := I) (M := M) g α (m + 1) (p := 2) (by norm_num) (by norm_num)
  refine ⟨C, hC_pos, ?_⟩
  intro v
  have h_v_MemWkpChart : MemWkpChart (I := I) (M := M) g (m + 1) 2 v.toFun :=
    memWkpChart_of_contMDiff_k (I := I) (M := M) g (by norm_num) (m + 1) v.smooth
  have h_funext : etaTimesV (I := I) (M := M) α v.toFun =
      fun x : M => chartStrictCutoff (I := I) (M := M) α x * v.toFun x := by
    funext x; rfl
  rw [h_funext]
  exact hC_bound h_v_MemWkpChart

private lemma wkpNorm_chartPushedRaw_etaTimesV_le_self
    (g : SmoothRiemannianMetric I M) (α : M) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : SmoothScalar g,
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) m 2
        (chartPushedRaw (I := I) (M := M) α
          (etaTimesV (I := I) (M := M) α v.toFun))
        (chartTargetEuclid (I := I) (M := M) α) ≤
      ENNReal.ofReal C * wkpNormChart (I := I) (M := M) g m 2
        (fun x : M => v.toFun x) := by
  classical
  obtain ⟨C, hC_pos, hC_bound⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Chart.wkpNorm_chartPushedRaw_strictCutoff_mul_le
      (I := I) (M := M) g α m (p := 2) (by norm_num) (by norm_num)
  refine ⟨C, hC_pos, ?_⟩
  intro v
  have h_v_MemWkpChart : MemWkpChart (I := I) (M := M) g m 2 v.toFun :=
    memWkpChart_of_contMDiff_k (I := I) (M := M) g (by norm_num) m v.smooth
  have h_funext : etaTimesV (I := I) (M := M) α v.toFun =
      fun x : M => chartStrictCutoff (I := I) (M := M) α x * v.toFun x := by
    funext x; rfl
  rw [h_funext]
  exact hC_bound h_v_MemWkpChart

private lemma wkpNorm_partialDerivOnEuclid_etaTimesV_le_m
    (g : SmoothRiemannianMetric I M) (α : M) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : SmoothScalar g,
      ∀ i : Fin (Module.finrank ℝ E),
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) m 2
          (partialDerivOnEuclid (I := I) (M := M) α i
            (etaTimesV (I := I) (M := M) α v.toFun))
          (chartTargetEuclid (I := I) (M := M) α) ≤
        ENNReal.ofReal C * wkpNormChart (I := I) (M := M) g (m + 1) 2
          (fun x : M => v.toFun x) := by
  classical
  have h_per_i_partial : ∀ i : Fin (Module.finrank ℝ E), ∃ C_p : ℝ, 0 < C_p ∧
      ∀ {u : M → ℝ}, ContMDiff I 𝓘(ℝ, ℝ) ∞ u → tsupport u ⊆ (chartAt H α).source →
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) m 2
          (partialDerivOnEuclid (I := I) (M := M) α i u)
          (chartTargetEuclid (I := I) (M := M) α) ≤
        ENNReal.ofReal C_p *
          DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := Module.finrank ℝ E) (m + 1) 2
            (chartPushedRaw (I := I) (M := M) α u)
            (chartTargetEuclid (I := I) (M := M) α) := fun i =>
    wkpNorm_partialDerivOnEuclid_le_wkpNorm_chartPushedRaw_succ
      (I := I) (M := M) α i m (p := 2) (by norm_num) (by norm_num)
  let Cp : Fin (Module.finrank ℝ E) → ℝ := fun i => (h_per_i_partial i).choose
  have hCp_pos : ∀ i, 0 < Cp i := fun i => (h_per_i_partial i).choose_spec.1
  have hCp_bound : ∀ i : Fin (Module.finrank ℝ E),
      ∀ {u : M → ℝ}, ContMDiff I 𝓘(ℝ, ℝ) ∞ u → tsupport u ⊆ (chartAt H α).source →
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) m 2
          (partialDerivOnEuclid (I := I) (M := M) α i u)
          (chartTargetEuclid (I := I) (M := M) α) ≤
        ENNReal.ofReal (Cp i) *
          DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := Module.finrank ℝ E) (m + 1) 2
            (chartPushedRaw (I := I) (M := M) α u)
            (chartTargetEuclid (I := I) (M := M) α) := fun i =>
    (h_per_i_partial i).choose_spec.2
  obtain ⟨C_strict, hC_strict_pos, hC_strict_bound⟩ :=
    wkpNorm_chartPushedRaw_etaTimesV_le_succ (I := I) (M := M) g α m
  have h_fin_pos : 0 < Module.finrank ℝ E := Nat.pos_of_ne_zero (NeZero.ne _)
  haveI h_nonempty : Nonempty (Fin (Module.finrank ℝ E)) := ⟨⟨0, h_fin_pos⟩⟩
  set Cmax : ℝ := Finset.univ.sup' (Finset.univ_nonempty (α := Fin _)) Cp
  have hCmax_ge : ∀ i, Cp i ≤ Cmax := fun i => Finset.le_sup' Cp (Finset.mem_univ i)
  have hCmax_pos : 0 < Cmax :=
    lt_of_lt_of_le (hCp_pos h_nonempty.some) (hCmax_ge h_nonempty.some)
  set C_total : ℝ := Cmax * C_strict with hC_total_def
  have hC_total_pos : 0 < C_total := mul_pos hCmax_pos hC_strict_pos
  refine ⟨C_total, hC_total_pos, ?_⟩
  intro v i
  have hηv_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (etaTimesV (I := I) (M := M) α v.toFun) :=
    etaTimesV_smooth (I := I) (M := M) α v.smooth
  have hηv_supp : tsupport (etaTimesV (I := I) (M := M) α v.toFun) ⊆
      (chartAt H α).source :=
    tsupport_etaTimesV_subset (I := I) (M := M) α v.toFun
  have h_partial_bound := hCp_bound i hηv_smooth hηv_supp
  have h_strict_bound := hC_strict_bound v
  calc DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) m 2
        (partialDerivOnEuclid (I := I) (M := M) α i
          (etaTimesV (I := I) (M := M) α v.toFun))
        (chartTargetEuclid (I := I) (M := M) α)
      ≤ ENNReal.ofReal (Cp i) *
          DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := Module.finrank ℝ E) (m + 1) 2
            (chartPushedRaw (I := I) (M := M) α
              (etaTimesV (I := I) (M := M) α v.toFun))
            (chartTargetEuclid (I := I) (M := M) α) := h_partial_bound
    _ ≤ ENNReal.ofReal (Cp i) *
            (ENNReal.ofReal C_strict * wkpNormChart (I := I) (M := M) g (m + 1) 2 v.toFun) :=
            mul_le_mul_of_nonneg_left h_strict_bound (zero_le _)
    _ = ENNReal.ofReal (Cp i * C_strict) *
            wkpNormChart (I := I) (M := M) g (m + 1) 2 v.toFun := by
            rw [← mul_assoc, ENNReal.ofReal_mul (hCp_pos i).le]
    _ ≤ ENNReal.ofReal C_total *
            wkpNormChart (I := I) (M := M) g (m + 1) 2 v.toFun := by
            refine mul_le_mul_of_nonneg_right ?_ (zero_le _)
            refine ENNReal.ofReal_le_ofReal ?_
            rw [hC_total_def]
            exact mul_le_mul_of_nonneg_right (hCmax_ge i) hC_strict_pos.le

private lemma wkpNorm_chartPushedRaw_gradInnerPiece_le
    (g : SmoothRiemannianMetric I M) (α : M) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : SmoothScalar g,
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) m 2
        (chartPushedRaw (I := I) (M := M) α
          (gradInnerPiece (I := I) (M := M) g α v.toFun))
        (chartTargetEuclid (I := I) (M := M) α) ≤
      ENNReal.ofReal C * wkpNormChart (I := I) (M := M) g (m + 1) 2
        (fun x : M => v.toFun x) := by
  classical
  have h_per_i_smul : ∀ i : Fin (Module.finrank ℝ E), ∃ K : ℝ, 0 < K ∧
      ∀ {u : EuclN → ℝ},
        DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) m 2 u
          (chartTargetEuclid (I := I) (M := M) α) →
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) m 2
          (fun y => Λgrad (I := I) (M := M) g α i y * u y)
          (chartTargetEuclid (I := I) (M := M) α) ≤
        ENNReal.ofReal K *
          DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := Module.finrank ℝ E) m 2 u
            (chartTargetEuclid (I := I) (M := M) α) := by
    intro i
    obtain ⟨C_Λ, hC_Λ_nn, hC_Λ_bound⟩ :=
      DifferentialGeometry.Analysis.Sobolev.Chart.smoothExtensionScalar_iteratedFDeriv_bound
        (I := I) (M := M) α
        (gradInnerCoefI_M_smooth (I := I) (M := M) g α i)
        (tsupport_gradInnerCoefI_M_subset (I := I) (M := M) g α i) m
    exact DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_smul_smooth_bounded_le
      (d := Module.finrank ℝ E) m (p := 2) (by norm_num) (by norm_num)
      (chartTargetEuclid_isOpen (I := I) (M := M) α)
      (Λgrad_contDiff (I := I) (M := M) g α i)
      hC_Λ_nn (fun j hj y _ => hC_Λ_bound j hj y)
  let K : Fin (Module.finrank ℝ E) → ℝ := fun i => (h_per_i_smul i).choose
  have hK_pos : ∀ i, 0 < K i := fun i => (h_per_i_smul i).choose_spec.1
  have hK_bound : ∀ i : Fin (Module.finrank ℝ E),
      ∀ {u : EuclN → ℝ},
        DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) m 2 u
          (chartTargetEuclid (I := I) (M := M) α) →
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) m 2
          (fun y => Λgrad (I := I) (M := M) g α i y * u y)
          (chartTargetEuclid (I := I) (M := M) α) ≤
        ENNReal.ofReal (K i) *
          DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := Module.finrank ℝ E) m 2 u
            (chartTargetEuclid (I := I) (M := M) α) := fun i =>
    (h_per_i_smul i).choose_spec.2
  obtain ⟨C_partial, hC_partial_pos, hC_partial_bound⟩ :=
    wkpNorm_partialDerivOnEuclid_etaTimesV_le_m (I := I) (M := M) g α m
  set sumK : ℝ := ∑ i : Fin (Module.finrank ℝ E), K i with hsumK_def
  have hsumK_nn : 0 ≤ sumK :=
    Finset.sum_nonneg (fun i _ => (hK_pos i).le)
  set Cfinal : ℝ := 2 * (sumK * C_partial) + 1 with hCfinal_def
  have h_Cfinal_pos : 0 < Cfinal := by
    rw [hCfinal_def]; linarith [mul_nonneg hsumK_nn hC_partial_pos.le]
  refine ⟨Cfinal, h_Cfinal_pos, ?_⟩
  intro v
  have h_pointwise : ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
      chartPushedRaw (I := I) (M := M) α
          (gradInnerPiece (I := I) (M := M) g α v.toFun) y =
        (2 : ℝ) * ∑ i : Fin (Module.finrank ℝ E),
          Λgrad (I := I) (M := M) g α i y *
            partialDerivOnEuclid (I := I) (M := M) α i
              (etaTimesV (I := I) (M := M) α v.toFun) y := fun y hy =>
    chartPushedRaw_gradInnerPiece_eq_sum (I := I) (M := M) g α v hy
  have h_ae : (chartPushedRaw (I := I) (M := M) α
        (gradInnerPiece (I := I) (M := M) g α v.toFun)) =ᵐ[
        volume.restrict (chartTargetEuclid (I := I) (M := M) α)]
      fun y => (2 : ℝ) * ∑ i : Fin (Module.finrank ℝ E),
        Λgrad (I := I) (M := M) g α i y *
          partialDerivOnEuclid (I := I) (M := M) α i
            (etaTimesV (I := I) (M := M) α v.toFun) y := by
    refine (MeasureTheory.ae_restrict_iff'
      (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet).mpr ?_
    refine Filter.Eventually.of_forall ?_
    intro y hy; exact h_pointwise y hy
  rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_congr_ae
        (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
        (chartTargetEuclid_isOpen (I := I) (M := M) α) h_ae]
  have h_partial_mem : ∀ i : Fin (Module.finrank ℝ E),
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) m 2
        (partialDerivOnEuclid (I := I) (M := M) α i
          (etaTimesV (I := I) (M := M) α v.toFun))
        (chartTargetEuclid (I := I) (M := M) α) := fun i =>
    memWkp_partialDerivOnEuclid_etaTimesV (I := I) (M := M) g α m v i
  have h_summand_mem : ∀ i : Fin (Module.finrank ℝ E),
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) m 2
        (fun y : EuclN => Λgrad (I := I) (M := M) g α i y *
          partialDerivOnEuclid (I := I) (M := M) α i
            (etaTimesV (I := I) (M := M) α v.toFun) y)
        (chartTargetEuclid (I := I) (M := M) α) := by
    intro i
    obtain ⟨C_Λ, hC_Λ_nn, hC_Λ_bound⟩ :=
      DifferentialGeometry.Analysis.Sobolev.Chart.smoothExtensionScalar_iteratedFDeriv_bound
        (I := I) (M := M) α
        (gradInnerCoefI_M_smooth (I := I) (M := M) g α i)
        (tsupport_gradInnerCoefI_M_subset (I := I) (M := M) g α i) m
    exact DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.smul_smooth_bounded
      (d := Module.finrank ℝ E) m (p := 2) (by norm_num)
      (chartTargetEuclid_isOpen (I := I) (M := M) α)
      (Λgrad_contDiff (I := I) (M := M) g α i)
      (fun j hj y _ => hC_Λ_bound j hj y)
      (h_partial_mem i)
  have h_sum_mem_gen : ∀ (S : Finset (Fin (Module.finrank ℝ E))),
      (∀ ε ∈ S, DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) m 2
        (fun y : EuclN => Λgrad (I := I) (M := M) g α ε y *
          partialDerivOnEuclid (I := I) (M := M) α ε
            (etaTimesV (I := I) (M := M) α v.toFun) y)
        (chartTargetEuclid (I := I) (M := M) α)) →
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) m 2
        (fun y : EuclN => ∑ ε ∈ S,
          Λgrad (I := I) (M := M) g α ε y *
            partialDerivOnEuclid (I := I) (M := M) α ε
              (etaTimesV (I := I) (M := M) α v.toFun) y)
        (chartTargetEuclid (I := I) (M := M) α) := by
    intro S
    induction S using Finset.induction with
    | empty =>
        intro _
        simp only [Finset.sum_empty]
        exact DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_zero_fun
          (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
          (chartTargetEuclid_isOpen (I := I) (M := M) α)
    | insert δ S' hδ ih2 =>
        intro hf
        have hf_δ := hf δ (Finset.mem_insert_self δ S')
        have hf_S' : ∀ ε ∈ S', _ := fun ε hε =>
          hf ε (Finset.mem_insert_of_mem hε)
        have hsum := ih2 hf_S'
        have h_eq : (fun y : EuclN => ∑ ε ∈ insert δ S',
            Λgrad (I := I) (M := M) g α ε y *
              partialDerivOnEuclid (I := I) (M := M) α ε
                (etaTimesV (I := I) (M := M) α v.toFun) y) =
            fun y : EuclN =>
              (Λgrad (I := I) (M := M) g α δ y *
                partialDerivOnEuclid (I := I) (M := M) α δ
                  (etaTimesV (I := I) (M := M) α v.toFun) y) +
              ∑ ε ∈ S', Λgrad (I := I) (M := M) g α ε y *
                partialDerivOnEuclid (I := I) (M := M) α ε
                  (etaTimesV (I := I) (M := M) α v.toFun) y := by
          funext y; exact Finset.sum_insert hδ
        rw [h_eq]
        exact DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.add
          (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
          (chartTargetEuclid_isOpen (I := I) (M := M) α) hf_δ hsum
  have h_sum_mem :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) m 2
        (fun y : EuclN => ∑ i : Fin (Module.finrank ℝ E),
          Λgrad (I := I) (M := M) g α i y *
            partialDerivOnEuclid (I := I) (M := M) α i
              (etaTimesV (I := I) (M := M) α v.toFun) y)
        (chartTargetEuclid (I := I) (M := M) α) :=
    h_sum_mem_gen Finset.univ (fun i _ => h_summand_mem i)
  have h_const2 :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) m 2
        (fun y => (2 : ℝ) * ∑ i : Fin (Module.finrank ℝ E),
          Λgrad (I := I) (M := M) g α i y *
            partialDerivOnEuclid (I := I) (M := M) α i
              (etaTimesV (I := I) (M := M) α v.toFun) y)
        (chartTargetEuclid (I := I) (M := M) α) =
      ‖(2 : ℝ)‖ₑ *
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) m 2
          (fun y : EuclN => ∑ i : Fin (Module.finrank ℝ E),
            Λgrad (I := I) (M := M) g α i y *
              partialDerivOnEuclid (I := I) (M := M) α i
                (etaTimesV (I := I) (M := M) α v.toFun) y)
          (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_const_smul
      (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (chartTargetEuclid_isOpen (I := I) (M := M) α) h_sum_mem (2 : ℝ)
  rw [h_const2]
  have h_triangle :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) m 2
        (fun y : EuclN => ∑ i : Fin (Module.finrank ℝ E),
          Λgrad (I := I) (M := M) g α i y *
            partialDerivOnEuclid (I := I) (M := M) α i
              (etaTimesV (I := I) (M := M) α v.toFun) y)
        (chartTargetEuclid (I := I) (M := M) α) ≤
      ∑ i : Fin (Module.finrank ℝ E),
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) m 2
          (fun y : EuclN => Λgrad (I := I) (M := M) g α i y *
            partialDerivOnEuclid (I := I) (M := M) α i
              (etaTimesV (I := I) (M := M) α v.toFun) y)
          (chartTargetEuclid (I := I) (M := M) α) := by
    have h_gen : ∀ (T : Finset (Fin (Module.finrank ℝ E))),
        (∀ i ∈ T, DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) m 2
          (fun y : EuclN => Λgrad (I := I) (M := M) g α i y *
            partialDerivOnEuclid (I := I) (M := M) α i
              (etaTimesV (I := I) (M := M) α v.toFun) y)
          (chartTargetEuclid (I := I) (M := M) α)) →
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) m 2
          (fun y : EuclN => ∑ i ∈ T,
            Λgrad (I := I) (M := M) g α i y *
              partialDerivOnEuclid (I := I) (M := M) α i
                (etaTimesV (I := I) (M := M) α v.toFun) y)
          (chartTargetEuclid (I := I) (M := M) α) ≤
        ∑ i ∈ T,
          DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := Module.finrank ℝ E) m 2
            (fun y : EuclN => Λgrad (I := I) (M := M) g α i y *
              partialDerivOnEuclid (I := I) (M := M) α i
                (etaTimesV (I := I) (M := M) α v.toFun) y)
            (chartTargetEuclid (I := I) (M := M) α) := by
      intro T
      induction T using Finset.induction with
      | empty =>
          intro _
          simp only [Finset.sum_empty]
          rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_zero_fun_zero
            (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
            (chartTargetEuclid_isOpen (I := I) (M := M) α)]
      | insert γ T hγ ih =>
          intro hf_mem
          have hf_γ_mem := hf_mem γ (Finset.mem_insert_self γ T)
          have hf_T_mem : ∀ ε ∈ T,
              DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
                (d := Module.finrank ℝ E) m 2
                (fun y : EuclN => Λgrad (I := I) (M := M) g α ε y *
                  partialDerivOnEuclid (I := I) (M := M) α ε
                    (etaTimesV (I := I) (M := M) α v.toFun) y)
                (chartTargetEuclid (I := I) (M := M) α) := fun ε hε =>
            hf_mem ε (Finset.mem_insert_of_mem hε)
          have h_sumT_mem : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
              (d := Module.finrank ℝ E) m 2
              (fun y : EuclN => ∑ ε ∈ T,
                Λgrad (I := I) (M := M) g α ε y *
                  partialDerivOnEuclid (I := I) (M := M) α ε
                    (etaTimesV (I := I) (M := M) α v.toFun) y)
              (chartTargetEuclid (I := I) (M := M) α) := h_sum_mem_gen T hf_T_mem
          have h_eq : (fun y : EuclN => ∑ ε ∈ insert γ T,
              Λgrad (I := I) (M := M) g α ε y *
                partialDerivOnEuclid (I := I) (M := M) α ε
                  (etaTimesV (I := I) (M := M) α v.toFun) y) =
              fun y : EuclN =>
                (Λgrad (I := I) (M := M) g α γ y *
                  partialDerivOnEuclid (I := I) (M := M) α γ
                    (etaTimesV (I := I) (M := M) α v.toFun) y) +
                ∑ ε ∈ T, Λgrad (I := I) (M := M) g α ε y *
                  partialDerivOnEuclid (I := I) (M := M) α ε
                    (etaTimesV (I := I) (M := M) α v.toFun) y := by
            funext y; exact Finset.sum_insert hγ
          rw [h_eq, Finset.sum_insert hγ]
          have h_triangle_step :=
            DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_add_le
              (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
              (chartTargetEuclid_isOpen (I := I) (M := M) α) hf_γ_mem h_sumT_mem
          have h_ih := ih hf_T_mem
          refine h_triangle_step.trans ?_
          exact add_le_add le_rfl h_ih
    exact h_gen Finset.univ (fun i _ => h_summand_mem i)
  have h_two_norm : ‖(2 : ℝ)‖ₑ = ENNReal.ofReal 2 := by
    rw [Real.enorm_eq_ofReal (by norm_num : (0 : ℝ) ≤ 2)]
  rw [h_two_norm]
  refine le_trans (mul_le_mul_of_nonneg_left h_triangle (zero_le _)) ?_
  have h_each_bound : ∀ i : Fin (Module.finrank ℝ E),
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) m 2
        (fun y : EuclN => Λgrad (I := I) (M := M) g α i y *
          partialDerivOnEuclid (I := I) (M := M) α i
            (etaTimesV (I := I) (M := M) α v.toFun) y)
        (chartTargetEuclid (I := I) (M := M) α) ≤
      ENNReal.ofReal (K i * C_partial) *
        wkpNormChart (I := I) (M := M) g (m + 1) 2 v.toFun := by
    intro i
    have h_step1 := hK_bound i (h_partial_mem i)
    have h_step2 := hC_partial_bound v i
    calc DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) m 2
          (fun y => Λgrad (I := I) (M := M) g α i y *
            partialDerivOnEuclid (I := I) (M := M) α i
              (etaTimesV (I := I) (M := M) α v.toFun) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (K i) *
            DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
              (d := Module.finrank ℝ E) m 2
              (partialDerivOnEuclid (I := I) (M := M) α i
                (etaTimesV (I := I) (M := M) α v.toFun))
              (chartTargetEuclid (I := I) (M := M) α) := h_step1
      _ ≤ ENNReal.ofReal (K i) *
              (ENNReal.ofReal C_partial * wkpNormChart (I := I) (M := M) g (m + 1) 2 v.toFun) :=
            mul_le_mul_of_nonneg_left h_step2 (zero_le _)
      _ = ENNReal.ofReal (K i * C_partial) *
              wkpNormChart (I := I) (M := M) g (m + 1) 2 v.toFun := by
            rw [← mul_assoc, ENNReal.ofReal_mul (hK_pos i).le]
  have h_sum_bound : ∑ i : Fin (Module.finrank ℝ E),
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) m 2
        (fun y : EuclN => Λgrad (I := I) (M := M) g α i y *
          partialDerivOnEuclid (I := I) (M := M) α i
            (etaTimesV (I := I) (M := M) α v.toFun) y)
        (chartTargetEuclid (I := I) (M := M) α) ≤
      ∑ i : Fin (Module.finrank ℝ E),
        ENNReal.ofReal (K i * C_partial) *
          wkpNormChart (I := I) (M := M) g (m + 1) 2 v.toFun :=
    Finset.sum_le_sum (fun i _ => h_each_bound i)
  refine le_trans (mul_le_mul_of_nonneg_left h_sum_bound (zero_le _)) ?_
  rw [← Finset.sum_mul]
  rw [show ∑ i : Fin (Module.finrank ℝ E), ENNReal.ofReal (K i * C_partial) =
      ENNReal.ofReal (∑ i : Fin (Module.finrank ℝ E), K i * C_partial) from by
        rw [ENNReal.ofReal_sum_of_nonneg]
        intro i _
        exact mul_nonneg (hK_pos i).le hC_partial_pos.le]
  rw [show ∑ i : Fin (Module.finrank ℝ E), K i * C_partial = sumK * C_partial from by
        rw [hsumK_def, Finset.sum_mul]]
  rw [← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (zero_le _)
  rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [hCfinal_def]; linarith [mul_nonneg hsumK_nn hC_partial_pos.le]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
private lemma wkpNormChart_le_of_le
    (g : SmoothRiemannianMetric I M) (j k : ℕ) (hjk : j ≤ k)
    (p : ℝ≥0∞) (u : M → ℝ) :
    wkpNormChart (I := I) (M := M) g j p u ≤
      wkpNormChart (I := I) (M := M) g k p u := by
  classical
  unfold wkpNormChart
  refine ENNReal.tsum_le_tsum (fun α => ?_)
  exact DifferentialGeometry.Analysis.Sobolev.Chart.EuclideanIterated.wkpNorm_mono_order
    (d := Module.finrank ℝ E) (j := j) (k := k) hjk

private lemma wkpNorm_chartPushedRaw_lapPiece_le
    (g : SmoothRiemannianMetric I M) (α : M) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : SmoothScalar g,
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) m 2
        (chartPushedRaw (I := I) (M := M) α
          (lapPiece (I := I) (M := M) g α v.toFun))
        (chartTargetEuclid (I := I) (M := M) α) ≤
      ENNReal.ofReal C * wkpNormChart (I := I) (M := M) g (m + 1) 2
        (fun x : M => v.toFun x) := by
  classical
  obtain ⟨b, hb_smooth, _, hb_one_on_tsupp, hb_supp⟩ :=
    exists_chart_cutoff_M (I := I) (M := M) α
  set bΔρα : M → ℝ := fun x : M =>
    b x * (laplacianOfChartPOU (I := I) (M := M) g α : M → ℝ) x with hbΔρα_def
  have hbΔρα_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ bΔρα :=
    hb_smooth.mul (laplacianOfChartPOU (I := I) (M := M) g α).contMDiff
  have hbΔρα_supp : tsupport bΔρα ⊆ (chartAt H α).source := by
    have h_eq : bΔρα = (fun x : M => b x •
      (laplacianOfChartPOU (I := I) (M := M) g α : M → ℝ) x) := by
      funext x; rfl
    rw [h_eq]
    exact (tsupport_smul_subset_left (f := b)
      (g := ((laplacianOfChartPOU (I := I) (M := M) g α : C^∞⟮I, M; ℝ⟯) : M → ℝ))).trans
      hb_supp
  obtain ⟨CΛ, hCΛ_nn, hCΛ_bound⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Chart.smoothExtensionScalar_iteratedFDeriv_bound
      (I := I) (M := M) α hbΔρα_smooth hbΔρα_supp m
  set Λ : EuclN → ℝ := smoothExtensionScalar (I := I) (M := M) α bΔρα with hΛ_def
  have hΛ_smooth : ContDiff ℝ (⊤ : ℕ∞) Λ :=
    contDiff_smoothExtensionScalar (I := I) (M := M) α hbΔρα_smooth hbΔρα_supp
  have hΛ_bound : ∀ j ≤ m, ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
      ‖iteratedFDeriv ℝ j Λ y‖ ≤ CΛ := fun j hj y _ => hCΛ_bound j hj y
  obtain ⟨K, hK_pos, hK_bound⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_smul_smooth_bounded_le
      (d := Module.finrank ℝ E) m (p := 2) (by norm_num) (by norm_num)
      (chartTargetEuclid_isOpen (I := I) (M := M) α)
      hΛ_smooth hCΛ_nn hΛ_bound
  obtain ⟨C_strict, hC_strict_pos, hC_strict_bound⟩ :=
    wkpNorm_chartPushedRaw_etaTimesV_le_self (I := I) (M := M) g α m
  set Cfinal : ℝ := K * C_strict with hCfinal_def
  have h_Cfinal_pos : 0 < Cfinal := mul_pos hK_pos hC_strict_pos
  refine ⟨Cfinal, h_Cfinal_pos, ?_⟩
  intro v
  have h_factor : (fun y : EuclN => chartPushedRaw (I := I) (M := M) α
        (lapPiece (I := I) (M := M) g α v.toFun) y) =ᵐ[
        volume.restrict (chartTargetEuclid (I := I) (M := M) α)]
      fun y : EuclN => Λ y * chartPushedRaw (I := I) (M := M) α
        (etaTimesV (I := I) (M := M) α v.toFun) y := by
    refine (MeasureTheory.ae_restrict_iff'
      (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet).mpr ?_
    refine Filter.Eventually.of_forall (fun y hy => ?_)
    exact chartPushedRaw_lapPiece_factor (I := I) (M := M) g α v.toFun
      hb_one_on_tsupp hy
  have h_norm_eq :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) m 2
        (chartPushedRaw (I := I) (M := M) α
          (lapPiece (I := I) (M := M) g α v.toFun))
        (chartTargetEuclid (I := I) (M := M) α) =
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) m 2
        (fun y : EuclN => Λ y * chartPushedRaw (I := I) (M := M) α
          (etaTimesV (I := I) (M := M) α v.toFun) y)
        (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_congr_ae
      (d := Module.finrank ℝ E) (by norm_num)
      (chartTargetEuclid_isOpen (I := I) (M := M) α) h_factor
  rw [h_norm_eq]
  have hH_Wm2 : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) m 2
      (chartPushedRaw (I := I) (M := M) α
        (etaTimesV (I := I) (M := M) α v.toFun))
      (chartTargetEuclid (I := I) (M := M) α) :=
    memWkp_chartPushedRaw_etaTimesV (I := I) (M := M) g α m v
  have h_mono : wkpNormChart (I := I) (M := M) g m 2 v.toFun ≤
      wkpNormChart (I := I) (M := M) g (m + 1) 2 v.toFun :=
    wkpNormChart_le_of_le (I := I) (M := M) g m (m + 1)
      (Nat.le_succ _) 2 v.toFun
  calc DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) m 2
        (fun y => Λ y * chartPushedRaw (I := I) (M := M) α
          (etaTimesV (I := I) (M := M) α v.toFun) y)
        (chartTargetEuclid (I := I) (M := M) α)
      ≤ ENNReal.ofReal K *
          DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := Module.finrank ℝ E) m 2
            (chartPushedRaw (I := I) (M := M) α
              (etaTimesV (I := I) (M := M) α v.toFun))
            (chartTargetEuclid (I := I) (M := M) α) := hK_bound hH_Wm2
    _ ≤ ENNReal.ofReal K *
            (ENNReal.ofReal C_strict * wkpNormChart (I := I) (M := M) g m 2 v.toFun) :=
          mul_le_mul_of_nonneg_left (hC_strict_bound v) (zero_le _)
    _ ≤ ENNReal.ofReal K *
            (ENNReal.ofReal C_strict * wkpNormChart (I := I) (M := M) g (m + 1) 2 v.toFun) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left h_mono (zero_le _)) (zero_le _)
    _ = ENNReal.ofReal (K * C_strict) *
            wkpNormChart (I := I) (M := M) g (m + 1) 2 v.toFun := by
          rw [← mul_assoc, ENNReal.ofReal_mul hK_pos.le]
    _ = ENNReal.ofReal Cfinal *
            wkpNormChart (I := I) (M := M) g (m + 1) 2 v.toFun := by
          rw [hCfinal_def]

theorem wkpNorm_smoothFChartResidual_le_wkpNormChart_wkpM
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (α : M) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : SmoothScalar g,
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) m 2
        (DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplResidual.smoothFChartResidual
          (I := I) (M := M) g α v)
        (chartTargetEuclid (I := I) (M := M) α)
      ≤ ENNReal.ofReal C * wkpNormChart (I := I) (M := M) g (m + 1) 2 v.toFun := by
  classical
  obtain ⟨C_grad, hC_grad_pos, hC_grad_bound⟩ :=
    wkpNorm_chartPushedRaw_gradInnerPiece_le (I := I) (M := M) g α m
  obtain ⟨C_lap, hC_lap_pos, hC_lap_bound⟩ :=
    wkpNorm_chartPushedRaw_lapPiece_le (I := I) (M := M) g α m
  refine ⟨C_grad + C_lap, by linarith, ?_⟩
  intro v
  have h_ae := smoothFChartResidual_ae_eq_chartPushedRaw_smoothRep
    (I := I) (M := M) g α v
  rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_congr_ae
        (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
        (chartTargetEuclid_isOpen (I := I) (M := M) α) h_ae]
  have h_ptwise : chartPushedRaw (I := I) (M := M) α
        (smoothRep (I := I) (M := M) g α v) =
      fun y => -chartPushedRaw (I := I) (M := M) α
          (gradInnerPiece (I := I) (M := M) g α v.toFun) y -
        chartPushedRaw (I := I) (M := M) α
          (lapPiece (I := I) (M := M) g α v.toFun) y := by
    funext y
    exact chartPushedRaw_smoothRep_eq (I := I) (M := M) g α v y
  rw [h_ptwise]
  have hP_grad : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) m 2
      (chartPushedRaw (I := I) (M := M) α
        (gradInnerPiece (I := I) (M := M) g α v.toFun))
      (chartTargetEuclid (I := I) (M := M) α) := by
    have h_smooth := gradInnerPiece_smooth (I := I) (M := M) g α v
    have h_supp := tsupport_gradInnerPiece_subset_source
      (I := I) (M := M) g α v.toFun
    have hCP_smooth : ContDiff ℝ ∞
        (chartPushedRaw (I := I) (M := M) α
          (gradInnerPiece (I := I) (M := M) g α v.toFun)) :=
      chartPushedRaw_contDiff (I := I) (M := M) h_smooth h_supp
    have hCP_cpt : HasCompactSupport
        (chartPushedRaw (I := I) (M := M) α
          (gradInnerPiece (I := I) (M := M) g α v.toFun)) :=
      chartPushedRaw_smooth_hasCompactSupport_local (I := I) (M := M) h_supp
    have hCP_tsupp : tsupport (chartPushedRaw (I := I) (M := M) α
          (gradInnerPiece (I := I) (M := M) g α v.toFun)) ⊆
        chartTargetEuclid (I := I) (M := M) α :=
      tsupport_chartPushedRaw_subset_chartTargetEuclid (I := I) (M := M) h_supp
    exact DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_of_smooth_compactSupport
      (d := Module.finrank ℝ E)
      (chartTargetEuclid_isOpen (I := I) (M := M) α)
      hCP_smooth hCP_cpt hCP_tsupp (by norm_num : (1 : ℝ≥0∞) ≤ 2) m
  have hP_lap : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) m 2
      (chartPushedRaw (I := I) (M := M) α
        (lapPiece (I := I) (M := M) g α v.toFun))
      (chartTargetEuclid (I := I) (M := M) α) := by
    have h_smooth := lapPiece_smooth (I := I) (M := M) g α v
    have h_supp := tsupport_lapPiece_subset_source
      (I := I) (M := M) g α v.toFun
    have hCP_smooth : ContDiff ℝ ∞
        (chartPushedRaw (I := I) (M := M) α
          (lapPiece (I := I) (M := M) g α v.toFun)) :=
      chartPushedRaw_contDiff (I := I) (M := M) h_smooth h_supp
    have hCP_cpt : HasCompactSupport
        (chartPushedRaw (I := I) (M := M) α
          (lapPiece (I := I) (M := M) g α v.toFun)) :=
      chartPushedRaw_smooth_hasCompactSupport_local (I := I) (M := M) h_supp
    have hCP_tsupp : tsupport (chartPushedRaw (I := I) (M := M) α
          (lapPiece (I := I) (M := M) g α v.toFun)) ⊆
        chartTargetEuclid (I := I) (M := M) α :=
      tsupport_chartPushedRaw_subset_chartTargetEuclid (I := I) (M := M) h_supp
    exact DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_of_smooth_compactSupport
      (d := Module.finrank ℝ E)
      (chartTargetEuclid_isOpen (I := I) (M := M) α)
      hCP_smooth hCP_cpt hCP_tsupp (by norm_num : (1 : ℝ≥0∞) ≤ 2) m
  have h_rewrite : (fun y : EuclN => -chartPushedRaw (I := I) (M := M) α
          (gradInnerPiece (I := I) (M := M) g α v.toFun) y -
        chartPushedRaw (I := I) (M := M) α
          (lapPiece (I := I) (M := M) g α v.toFun) y) =
      (fun y => (-1 : ℝ) * chartPushedRaw (I := I) (M := M) α
          (gradInnerPiece (I := I) (M := M) g α v.toFun) y +
        ((-1 : ℝ) * chartPushedRaw (I := I) (M := M) α
          (lapPiece (I := I) (M := M) g α v.toFun) y)) := by
    funext y; ring
  rw [h_rewrite]
  have hP_negA : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) m 2
      (fun y => (-1 : ℝ) * chartPushedRaw (I := I) (M := M) α
        (gradInnerPiece (I := I) (M := M) g α v.toFun) y)
      (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.const_smul
      (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (chartTargetEuclid_isOpen (I := I) (M := M) α) hP_grad (-1 : ℝ)
  have hP_negB : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) m 2
      (fun y => (-1 : ℝ) * chartPushedRaw (I := I) (M := M) α
        (lapPiece (I := I) (M := M) g α v.toFun) y)
      (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.const_smul
      (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (chartTargetEuclid_isOpen (I := I) (M := M) α) hP_lap (-1 : ℝ)
  have h_triangle :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_add_le
      (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (chartTargetEuclid_isOpen (I := I) (M := M) α) hP_negA hP_negB
  refine le_trans h_triangle ?_
  have h_neg_norm_grad :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) m 2
        (fun y => (-1 : ℝ) * chartPushedRaw (I := I) (M := M) α
          (gradInnerPiece (I := I) (M := M) g α v.toFun) y)
        (chartTargetEuclid (I := I) (M := M) α) =
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) m 2
        (chartPushedRaw (I := I) (M := M) α
          (gradInnerPiece (I := I) (M := M) g α v.toFun))
        (chartTargetEuclid (I := I) (M := M) α) := by
    rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_const_smul
        (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
        (chartTargetEuclid_isOpen (I := I) (M := M) α) hP_grad (-1 : ℝ)]
    have : ‖(-1 : ℝ)‖ₑ = 1 := by
      rw [Real.enorm_eq_ofReal_abs]
      simp
    rw [this, one_mul]
  have h_neg_norm_lap :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) m 2
        (fun y => (-1 : ℝ) * chartPushedRaw (I := I) (M := M) α
          (lapPiece (I := I) (M := M) g α v.toFun) y)
        (chartTargetEuclid (I := I) (M := M) α) =
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) m 2
        (chartPushedRaw (I := I) (M := M) α
          (lapPiece (I := I) (M := M) g α v.toFun))
        (chartTargetEuclid (I := I) (M := M) α) := by
    rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_const_smul
        (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
        (chartTargetEuclid_isOpen (I := I) (M := M) α) hP_lap (-1 : ℝ)]
    have : ‖(-1 : ℝ)‖ₑ = 1 := by
      rw [Real.enorm_eq_ofReal_abs]
      simp
    rw [this, one_mul]
  rw [h_neg_norm_grad, h_neg_norm_lap]
  calc DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) m 2
        (chartPushedRaw (I := I) (M := M) α
          (gradInnerPiece (I := I) (M := M) g α v.toFun))
        (chartTargetEuclid (I := I) (M := M) α) +
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) m 2
        (chartPushedRaw (I := I) (M := M) α
          (lapPiece (I := I) (M := M) g α v.toFun))
        (chartTargetEuclid (I := I) (M := M) α)
      ≤ ENNReal.ofReal C_grad * wkpNormChart (I := I) (M := M) g (m + 1) 2 v.toFun +
        ENNReal.ofReal C_lap * wkpNormChart (I := I) (M := M) g (m + 1) 2 v.toFun := by
            exact add_le_add (hC_grad_bound v) (hC_lap_bound v)
    _ = (ENNReal.ofReal C_grad + ENNReal.ofReal C_lap) *
        wkpNormChart (I := I) (M := M) g (m + 1) 2 v.toFun := by
            rw [add_mul]
    _ = ENNReal.ofReal (C_grad + C_lap) *
        wkpNormChart (I := I) (M := M) g (m + 1) 2 v.toFun := by
            rw [ENNReal.ofReal_add hC_grad_pos.le hC_lap_pos.le]

omit [NeZero (Module.finrank ℝ E)] in
lemma smoothFChartResidual_memWkp_m
    (g : SmoothRiemannianMetric I M) (α : M) (m : ℕ) (v : SmoothScalar g) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) m 2
      (smoothFChartResidual (I := I) (M := M) g α v)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have h_ae := smoothFChartResidual_ae_eq_chartPushedRaw_smoothRep
    (I := I) (M := M) g α v
  have h_ptwise : chartPushedRaw (I := I) (M := M) α
        (smoothRep (I := I) (M := M) g α v) =
      fun y => -chartPushedRaw (I := I) (M := M) α
          (gradInnerPiece (I := I) (M := M) g α v.toFun) y -
        chartPushedRaw (I := I) (M := M) α
          (lapPiece (I := I) (M := M) g α v.toFun) y := by
    funext y
    exact chartPushedRaw_smoothRep_eq (I := I) (M := M) g α v y
  have hP_grad : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) m 2
      (chartPushedRaw (I := I) (M := M) α
        (gradInnerPiece (I := I) (M := M) g α v.toFun))
      (chartTargetEuclid (I := I) (M := M) α) := by
    have h_smooth := gradInnerPiece_smooth (I := I) (M := M) g α v
    have h_supp := tsupport_gradInnerPiece_subset_source
      (I := I) (M := M) g α v.toFun
    have hCP_smooth : ContDiff ℝ ∞
        (chartPushedRaw (I := I) (M := M) α
          (gradInnerPiece (I := I) (M := M) g α v.toFun)) :=
      chartPushedRaw_contDiff (I := I) (M := M) h_smooth h_supp
    have hCP_cpt : HasCompactSupport
        (chartPushedRaw (I := I) (M := M) α
          (gradInnerPiece (I := I) (M := M) g α v.toFun)) :=
      chartPushedRaw_smooth_hasCompactSupport_local (I := I) (M := M) h_supp
    have hCP_tsupp : tsupport (chartPushedRaw (I := I) (M := M) α
          (gradInnerPiece (I := I) (M := M) g α v.toFun)) ⊆
        chartTargetEuclid (I := I) (M := M) α :=
      tsupport_chartPushedRaw_subset_chartTargetEuclid (I := I) (M := M) h_supp
    exact DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_of_smooth_compactSupport
      (d := Module.finrank ℝ E)
      (chartTargetEuclid_isOpen (I := I) (M := M) α)
      hCP_smooth hCP_cpt hCP_tsupp (by norm_num : (1 : ℝ≥0∞) ≤ 2) m
  have hP_lap : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) m 2
      (chartPushedRaw (I := I) (M := M) α
        (lapPiece (I := I) (M := M) g α v.toFun))
      (chartTargetEuclid (I := I) (M := M) α) := by
    have h_smooth := lapPiece_smooth (I := I) (M := M) g α v
    have h_supp := tsupport_lapPiece_subset_source
      (I := I) (M := M) g α v.toFun
    have hCP_smooth : ContDiff ℝ ∞
        (chartPushedRaw (I := I) (M := M) α
          (lapPiece (I := I) (M := M) g α v.toFun)) :=
      chartPushedRaw_contDiff (I := I) (M := M) h_smooth h_supp
    have hCP_cpt : HasCompactSupport
        (chartPushedRaw (I := I) (M := M) α
          (lapPiece (I := I) (M := M) g α v.toFun)) :=
      chartPushedRaw_smooth_hasCompactSupport_local (I := I) (M := M) h_supp
    have hCP_tsupp : tsupport (chartPushedRaw (I := I) (M := M) α
          (lapPiece (I := I) (M := M) g α v.toFun)) ⊆
        chartTargetEuclid (I := I) (M := M) α :=
      tsupport_chartPushedRaw_subset_chartTargetEuclid (I := I) (M := M) h_supp
    exact DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_of_smooth_compactSupport
      (d := Module.finrank ℝ E)
      (chartTargetEuclid_isOpen (I := I) (M := M) α)
      hCP_smooth hCP_cpt hCP_tsupp (by norm_num : (1 : ℝ≥0∞) ≤ 2) m
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hp_one : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have hP_negA : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) m 2
      (fun y => (-1 : ℝ) * chartPushedRaw (I := I) (M := M) α
        (gradInnerPiece (I := I) (M := M) g α v.toFun) y)
      (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.const_smul
      (d := Module.finrank ℝ E) hp_one hΩ_open hP_grad (-1 : ℝ)
  have hP_negB : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) m 2
      (fun y => (-1 : ℝ) * chartPushedRaw (I := I) (M := M) α
        (lapPiece (I := I) (M := M) g α v.toFun) y)
      (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.const_smul
      (d := Module.finrank ℝ E) hp_one hΩ_open hP_lap (-1 : ℝ)
  have hP_sum : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) m 2
      (fun y => (-1 : ℝ) * chartPushedRaw (I := I) (M := M) α
        (gradInnerPiece (I := I) (M := M) g α v.toFun) y +
        (-1 : ℝ) * chartPushedRaw (I := I) (M := M) α
          (lapPiece (I := I) (M := M) g α v.toFun) y)
      (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.add hp_one hΩ_open
      hP_negA hP_negB
  have h_eq_sum :
      (fun y : EuclN => (-1 : ℝ) * chartPushedRaw (I := I) (M := M) α
          (gradInnerPiece (I := I) (M := M) g α v.toFun) y +
        (-1 : ℝ) * chartPushedRaw (I := I) (M := M) α
          (lapPiece (I := I) (M := M) g α v.toFun) y) =
      chartPushedRaw (I := I) (M := M) α
        (smoothRep (I := I) (M := M) g α v) := by
    funext y
    rw [h_ptwise]
    ring
  rw [h_eq_sum] at hP_sum
  exact (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_congr_ae
    hp_one hΩ_open h_ae.symm).mp hP_sum

theorem memWkp_fChartResidual_of_wkpNorm_cauchy_identification_wkpM
    (g : SmoothRiemannianMetric I M) (α : M) (m : ℕ)
    (u_h : H1Compl (I := I) (M := M) g)
    (v : ℕ → SmoothScalar g)
    (h_cauchy : ∀ ε > 0, ∃ N, ∀ a b, N ≤ a → N ≤ b →
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) m 2
        (fun y => smoothFChartResidual (I := I) (M := M) g α (v a) y -
          smoothFChartResidual (I := I) (M := M) g α (v b) y)
        (chartTargetEuclid (I := I) (M := M) α) ≤ ENNReal.ofReal ε)
    (h_identification : ∀ F_lim : EuclN → ℝ,
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) m 2 F_lim
        (chartTargetEuclid (I := I) (M := M) α) →
      Tendsto (fun n =>
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) m 2
          (fun y => smoothFChartResidual (I := I) (M := M) g α (v n) y - F_lim y)
          (chartTargetEuclid (I := I) (M := M) α))
        atTop (𝓝 0) →
      F_lim =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)]
        DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fChartResidual
          (I := I) (M := M) g α u_h) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) m 2
      (DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fChartResidual
        (I := I) (M := M) g α u_h)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have h_smooth_Wmp : ∀ n,
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) m 2
        (smoothFChartResidual (I := I) (M := M) g α (v n))
        (chartTargetEuclid (I := I) (M := M) α) := fun n =>
    smoothFChartResidual_memWkp_m (I := I) (M := M) g α m (v n)
  obtain ⟨F_lim, hF_lim_memWkp, hF_lim_tendsto⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.exists_limit_of_wkpNorm_cauchy
      (hΩ_open := chartTargetEuclid_isOpen (I := I) (M := M) α)
      (k := m) (p := 2) (hp_one := by norm_num) (hp_top := by norm_num)
      (u := fun n => smoothFChartResidual (I := I) (M := M) g α (v n))
      h_smooth_Wmp h_cauchy
  have hF_lim_aeEq := h_identification F_lim hF_lim_memWkp hF_lim_tendsto
  exact (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_congr_ae
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    hF_lim_aeEq).mp hF_lim_memWkp

theorem base_f_chart_memWkp_m_of_hypotheses
    (g : SmoothRiemannianMetric I M) (α : M) (m : ℕ)
    (u_h : H1Compl (I := I) (M := M) g)
    (F_base f_piece1 : EuclN → ℝ)
    (h_piece1_memWkp :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) m 2 f_piece1
        (chartTargetEuclid (I := I) (M := M) α))
    (h_decomp_ae : F_base =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)]
      fun y => f_piece1 y +
        DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fChartResidual
          (I := I) (M := M) g α u_h y)
    (v : ℕ → SmoothScalar g)
    (h_cauchy : ∀ ε > 0, ∃ N, ∀ a b, N ≤ a → N ≤ b →
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) m 2
        (fun y => smoothFChartResidual (I := I) (M := M) g α (v a) y -
          smoothFChartResidual (I := I) (M := M) g α (v b) y)
        (chartTargetEuclid (I := I) (M := M) α) ≤ ENNReal.ofReal ε)
    (h_identification : ∀ F_lim : EuclN → ℝ,
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) m 2 F_lim
        (chartTargetEuclid (I := I) (M := M) α) →
      Tendsto (fun n =>
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) m 2
          (fun y => smoothFChartResidual (I := I) (M := M) g α (v n) y - F_lim y)
          (chartTargetEuclid (I := I) (M := M) α))
        atTop (𝓝 0) →
      F_lim =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)]
        DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fChartResidual
          (I := I) (M := M) g α u_h) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) m 2 F_base
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have h_residual_memWkp :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) m 2
        (DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fChartResidual
          (I := I) (M := M) g α u_h)
        (chartTargetEuclid (I := I) (M := M) α) :=
    memWkp_fChartResidual_of_wkpNorm_cauchy_identification_wkpM
      (I := I) (M := M) g α m u_h v h_cauchy h_identification
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hp_one : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have h_sum_memWkp :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) m 2
        (fun y => f_piece1 y +
          DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fChartResidual
            (I := I) (M := M) g α u_h y)
        (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.add hp_one hΩ_open
      h_piece1_memWkp h_residual_memWkp
  exact (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_congr_ae
    hp_one hΩ_open h_decomp_ae.symm).mp h_sum_memWkp

end IteratedBaseFChartRegularity
end Laplacian
end Analysis
end DifferentialGeometry

end
