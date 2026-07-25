import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.RHS.ChartRHSBounds.EigenvectorChartRHSMemWkp
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Cross.EigenvectorChartCrossRotationWkpNormBounds
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.LowerOrder.EigenvectorChartLowerOrderWkpNormBounds
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Cross.EigenvectorChartCrossRightDivWkpNormBound
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.RHS.DifferentiatedRHS.EigenvectorDifferentiatedRHS
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.RHS.ChartRHSBounds.EigenvectorChartRHSWkpNormProductBounds
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.RHS.ChartRHSBounds.EigenvectorChartRHSWkpNormTermAggregate
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.RHS.ChartRHSBounds.EigenvectorChartRHSWkpNormUniformBounds


noncomputable section

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

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

section MainBound


omit [CompleteSpace E] in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma eigenIdx_val_pos
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    0 < i.fst.val := by
  obtain ⟨u, hu_mem, hu_ne⟩ := i.fst.hasEigenvalue.exists_hasEigenvector
  have hu_in : u ∈ tensorResolventEigenspace
      (I := I) (M := M) g r s i.fst.val := hu_mem
  exact (tensorResolvent_eigenvalue_mem_unit_interval
    (I := I) (M := M) g r s hu_in hu_ne).1

end MainBound

section Unconditional
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

section TermBoundsUnconditional

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (i : TensorEigenIdx (I := I) (M := M) g r s)
  (α : M) (P₀ : TensorCompIdx (E := E) r s) (K : ℕ)


omit [CompleteSpace E] in
private lemma rhsTerm1_wkpNorm_le :
    ∃ C : ℝ, 0 ≤ C ∧
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (rhsTerm1 (I := I) (M := M) g r s i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal C *
          wkpRhsAggregate (I := I) (M := M) g r s i α P₀ K := by
  refine ⟨1, by norm_num, ?_⟩
  rw [ENNReal.ofReal_one, one_mul]
  exact le_trans (le_of_eq rfl)
    (aggrUchart_le (I := I) (M := M) g r s i α P₀ K)

omit [CompleteSpace E] in
private lemma rhsTerm2_wkpNorm_le
    (h_pou : eigenvectorResolventChartWkpRegularity (I := I) (M := M) g r s i K) :
    ∃ C : ℝ, 0 ≤ C ∧
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (rhsTerm2 (I := I) (M := M) g r s i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal C *
          wkpRhsAggregate (I := I) (M := M) g r s i α P₀ K := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  set F : (TensorCompIdx (E := E) r (s + 1) ×
      TensorCompIdx (E := E) r (s + 1)) → EuclN → ℝ :=
    fun x y => (covChartMetricGram (I := I) (M := M) g r (s + 1) α x.1 x.2 y *
        crossLeftTestCoeff (I := I) (M := M) g r s α P₀ x.2 y) *
      ((crossLeftLimitComponent (I := I) (M := M) g r s i α x.1 :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hF_def
  have h_data : ∀ x : TensorCompIdx (E := E) r (s + 1) ×
      TensorCompIdx (E := E) r (s + 1),
      MemWkp (d := Module.finrank ℝ E) K 2 (F x) Ω ∧
        ∃ C : ℝ, 0 ≤ C ∧
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (F x) Ω
            ≤ ENNReal.ofReal C *
              wkpRhsAggregate (I := I) (M := M)
                g r s i α P₀ K := by
    intro x
    have h_factor : MemWkp (d := Module.finrank ℝ E) K 2
        (fun y => ((crossLeftLimitComponent (I := I) (M := M)
            g r s i α x.1 :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω :=
      crossLeftLimitComponent_memWkp (I := I) (M := M)
        g r s i α x.1 K h_pou
    have hcoef_chart : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun y => covChartMetricGram (I := I) (M := M) g r (s + 1) α x.1 x.2 y *
          crossLeftTestCoeff (I := I) (M := M) g r s α P₀ x.2 y) Ω :=
      (covChartMetricGram_contDiffOn (I := I) (M := M)
          g r (s + 1) α x.1 x.2).mul
        (crossLeftTestCoeff_contDiffOn (I := I) (M := M) g r s α P₀ x.2)
    have h_factor_ae_zero : ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
        y ∉ cutoffChartKernelEuclid (I := I) (M := M) α →
          ((crossLeftLimitComponent (I := I) (M := M)
              g r s i α x.1 :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y = 0 := by
      rw [crossLeftLimitComponent]
      exact tensorL2ChartComponentCutoff_ae_zero_off_cutoffChartKernelEuclid
        (I := I) (M := M) g r (s + 1)
        (tensorCovGradL2Compl (I := I) (M := M) g r s
          (eigenvectorResolvent (I := I) (M := M) g r s i)) α x.1
    obtain ⟨h_summand_memWkp, C, hC_nn, hC_bd⟩ :=
      wkpNorm_smoothCoef_mul_aeZeroFactor_le
        (I := I) (M := M) α K
        (cutoffChartKernelEuclid_isCompact (I := I) (M := M) α)
        (cutoffChartKernelEuclid_subset_chartTargetEuclid (I := I) (M := M) α)
        hcoef_chart h_factor h_factor_ae_zero
    refine ⟨?_, ?_⟩
    · rw [hF_def]; exact h_summand_memWkp
    obtain ⟨C', hC'_nn, hC'_bd⟩ := wkpNorm_crossLeftLimitComponent_le
      (I := I) (M := M) g r s i K h_pou α x.1
    refine ⟨C * C', by positivity, ?_⟩
    rw [hF_def]
    have h_aggr_eq :
        (∑ β ∈ transportChartCenters (I := I) (M := M) α,
            ((∑ Q : TensorCompIdx (E := E) r s,
                iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K + 1) 2
                  (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                      (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                        (eigenvectorResolvent (I := I) (M := M)
                          g r s i))
                      β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                      EuclN → ℝ) y)
                  (chartTargetEuclid (I := I) (M := M) β))
              + ∑ β' ∈ transportChartCenters (I := I) (M := M) β,
                  ∑ Q : TensorCompIdx (E := E) r s,
                    iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K + 1) 2
                      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                            (eigenvectorResolvent (I := I) (M := M)
                              g r s i))
                          β' Q :
                          Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) :
                          EuclN → ℝ) y)
                      (chartTargetEuclid (I := I) (M := M) β')))
          = aggrCrossLeft (I := I) (M := M) g r s i α K := by
      rw [aggrCrossLeft]; rfl
    calc
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (fun y => (covChartMetricGram (I := I) (M := M)
              g r (s + 1) α x.1 x.2 y *
            crossLeftTestCoeff (I := I) (M := M) g r s α P₀ x.2 y) *
          ((crossLeftLimitComponent (I := I) (M := M)
              g r s i α x.1 :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω
          ≤ ENNReal.ofReal C *
              iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
                (fun y => ((crossLeftLimitComponent (I := I) (M := M)
                    g r s i α x.1 :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                  EuclN → ℝ) y) Ω := hC_bd
      _ ≤ ENNReal.ofReal C *
            (ENNReal.ofReal C' *
              wkpRhsAggregate (I := I) (M := M)
                g r s i α P₀ K) := by
          gcongr
          rw [hΩ_def]
          refine hC'_bd.trans ?_
          rw [h_aggr_eq]
          gcongr
          exact aggrCrossLeft_le (I := I) (M := M)
            g r s i α P₀ K
      _ = ENNReal.ofReal (C * C') *
            wkpRhsAggregate (I := I) (M := M)
              g r s i α P₀ K := by
          rw [ENNReal.ofReal_mul hC_nn, mul_assoc]
  obtain ⟨C, hC_nn, hC_bd⟩ := wkpNorm_sum_le_const_mul_aggregate
    (Ω := Ω) hΩ_open F
    (wkpRhsAggregate (I := I) (M := M) g r s i α P₀ K)
    (fun x => (h_data x).1) (fun x => (h_data x).2)
  refine ⟨C, hC_nn, ?_⟩
  have h_eq : rhsTerm2 (I := I) (M := M) g r s i α P₀
      = fun y => ∑ x : TensorCompIdx (E := E) r (s + 1) ×
          TensorCompIdx (E := E) r (s + 1), F x y := by
    funext y
    simp only [rhsTerm2, hF_def, Fintype.sum_prod_type]
  rw [h_eq, hΩ_def]
  exact hC_bd

omit [CompleteSpace E] in
private lemma rhsTerm3_wkpNorm_le
    (h_pou : eigenvectorResolventChartWkpRegularity (I := I) (M := M) g r s i K) :
    ∃ C : ℝ, 0 ≤ C ∧
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (rhsTerm3 (I := I) (M := M) g r s i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal C *
          wkpRhsAggregate (I := I) (M := M) g r s i α P₀ K := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  set F : (TensorCompIdx (E := E) r s ×
      TensorCompIdx (E := E) r s) → EuclN → ℝ :=
    fun x y => (covChartMetricGram (I := I) (M := M) g r s α x.1 x.2 y *
        crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ x.2 y) *
      ((crossRightLimitComponent (I := I) (M := M) g r s i α x.1 :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hF_def
  have h_data : ∀ x : TensorCompIdx (E := E) r s ×
      TensorCompIdx (E := E) r s,
      MemWkp (d := Module.finrank ℝ E) K 2 (F x) Ω ∧
        ∃ C : ℝ, 0 ≤ C ∧
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (F x) Ω
            ≤ ENNReal.ofReal C *
              wkpRhsAggregate (I := I) (M := M)
                g r s i α P₀ K := by
    intro x
    have h_factor : MemWkp (d := Module.finrank ℝ E) K 2
        (fun y => ((crossRightLimitComponent (I := I) (M := M)
            g r s i α x.1 :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω :=
      crossRightLimitComponent_memWkp (I := I) (M := M)
        g r s i α x.1 K h_pou
    have hcoef_chart : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun y => covChartMetricGram (I := I) (M := M) g r s α x.1 x.2 y *
          crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ x.2 y) Ω :=
      (covChartMetricGram_contDiffOn (I := I) (M := M) g r s α x.1 x.2).mul
        (crossRightTestValueCoeff_contDiffOn (I := I) (M := M) g r s α P₀ x.2)
    have h_factor_ae_zero : ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
        y ∉ cutoffChartKernelEuclid (I := I) (M := M) α →
          ((crossRightLimitComponent (I := I) (M := M)
              g r s i α x.1 :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y = 0 := by
      rw [crossRightLimitComponent]
      exact tensorL2ChartComponentCutoff_ae_zero_off_cutoffChartKernelEuclid
        (I := I) (M := M) g r s
        (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
          (eigenvectorResolvent (I := I) (M := M) g r s i)) α x.1
    obtain ⟨h_summand_memWkp, C, hC_nn, hC_bd⟩ :=
      wkpNorm_smoothCoef_mul_aeZeroFactor_le
        (I := I) (M := M) α K
        (cutoffChartKernelEuclid_isCompact (I := I) (M := M) α)
        (cutoffChartKernelEuclid_subset_chartTargetEuclid (I := I) (M := M) α)
        hcoef_chart h_factor h_factor_ae_zero
    refine ⟨?_, ?_⟩
    · rw [hF_def]; exact h_summand_memWkp
    obtain ⟨C', hC'_nn, hC'_bd⟩ := wkpNorm_crossRightLimitComponent_le
      (I := I) (M := M) g r s i K
      (fun β Q => (h_pou β Q).le_of_le (Nat.le_succ K)) α x.1
    refine ⟨C * C', by positivity, ?_⟩
    rw [hF_def]
    have h_aggr_eq :
        (∑ β ∈ transportChartCenters (I := I) (M := M) α,
            ∑ Q : TensorCompIdx (E := E) r s,
              iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
                (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                    (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                      (eigenvectorResolvent (I := I) (M := M)
                        g r s i))
                    β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                    EuclN → ℝ) y)
                (chartTargetEuclid (I := I) (M := M) β))
          = aggrCrossRight (I := I) (M := M) g r s i α K := by
      rw [aggrCrossRight]; rfl
    calc
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (fun y => (covChartMetricGram (I := I) (M := M) g r s α x.1 x.2 y *
            crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ x.2 y) *
          ((crossRightLimitComponent (I := I) (M := M)
              g r s i α x.1 :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω
          ≤ ENNReal.ofReal C *
              iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
                (fun y => ((crossRightLimitComponent (I := I) (M := M)
                    g r s i α x.1 :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                  EuclN → ℝ) y) Ω := hC_bd
      _ ≤ ENNReal.ofReal C *
            (ENNReal.ofReal C' *
              wkpRhsAggregate (I := I) (M := M)
                g r s i α P₀ K) := by
          gcongr
          rw [hΩ_def]
          refine hC'_bd.trans ?_
          rw [h_aggr_eq]
          gcongr
          exact aggrCrossRight_le (I := I) (M := M)
            g r s i α P₀ K
      _ = ENNReal.ofReal (C * C') *
            wkpRhsAggregate (I := I) (M := M)
              g r s i α P₀ K := by
          rw [ENNReal.ofReal_mul hC_nn, mul_assoc]
  obtain ⟨C, hC_nn, hC_bd⟩ := wkpNorm_sum_le_const_mul_aggregate
    (Ω := Ω) hΩ_open F
    (wkpRhsAggregate (I := I) (M := M) g r s i α P₀ K)
    (fun x => (h_data x).1) (fun x => (h_data x).2)
  refine ⟨C, hC_nn, ?_⟩
  have h_eq : rhsTerm3 (I := I) (M := M) g r s i α P₀
      = fun y => ∑ x : TensorCompIdx (E := E) r s ×
          TensorCompIdx (E := E) r s, F x y := by
    funext y
    simp only [rhsTerm3, hF_def, Fintype.sum_prod_type]
  rw [h_eq, hΩ_def]
  exact hC_bd

omit [CompleteSpace E] in
private lemma rhsTerm4_wkpNorm_le
    (h_pou : eigenvectorResolventChartWkpRegularity (I := I) (M := M) g r s i K) :
    ∃ C : ℝ, 0 ≤ C ∧
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (rhsTerm4 (I := I) (M := M) g r s i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal C *
          wkpRhsAggregate (I := I) (M := M) g r s i α P₀ K := by
  obtain ⟨C, hC_nn, hC_bd⟩ :=
    wkpNorm_covPrincipalRotationCoeffLimit_le_unconditional
      (I := I) (M := M) g r s i K α P₀ (fun β Q => h_pou β Q)
  refine ⟨C, hC_nn, ?_⟩
  rw [rhsTerm4]
  refine le_trans hC_bd ?_
  gcongr
  exact aggrPartial_le (I := I) (M := M) g r s i α P₀ K

omit [CompleteSpace E] in
private lemma rhsTerm5_wkpNorm_le
    (h_pou : eigenvectorResolventChartWkpRegularity (I := I) (M := M) g r s i K) :
    ∃ C : ℝ, 0 ≤ C ∧
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (rhsTerm5 (I := I) (M := M) g r s i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal C *
          wkpRhsAggregate (I := I) (M := M) g r s i α P₀ K := by
  obtain ⟨C, hC_nn, hC_bd⟩ :=
    wkpNorm_covLowerOrderRotationValueCoeffLimit_le_unconditional
      (I := I) (M := M) g r s i K α P₀ (fun β Q => h_pou β Q)
  refine ⟨2 * C, by positivity, ?_⟩
  rw [rhsTerm5]
  have h_sum_le :
      aggrPartial (I := I) (M := M) g r s i α K
          + aggrComponent (I := I) (M := M) g r s i α K
        ≤ 2 * wkpRhsAggregate (I := I) (M := M)
            g r s i α P₀ K := by
    rw [two_mul]
    exact add_le_add
      (aggrPartial_le (I := I) (M := M) g r s i α P₀ K)
      (aggrComponent_le (I := I) (M := M) g r s i α P₀ K)
  refine le_trans hC_bd ?_
  calc
    ENNReal.ofReal C *
        (aggrPartial (I := I) (M := M) g r s i α K
          + aggrComponent (I := I) (M := M) g r s i α K)
        ≤ ENNReal.ofReal C *
            (2 * wkpRhsAggregate (I := I) (M := M)
              g r s i α P₀ K) := by
          gcongr
    _ = ENNReal.ofReal (2 * C) *
          wkpRhsAggregate (I := I) (M := M)
            g r s i α P₀ K := by
        rw [← ofReal_two, ← mul_assoc, ← ENNReal.ofReal_mul hC_nn, mul_comm C 2]

omit [CompleteSpace E] in
private lemma weightedGradCoeffDivLimit_sum_wkpNorm_le
    (h_pou : eigenvectorResolventChartWkpRegularity (I := I) (M := M) g r s i K) :
    ∃ C : ℝ, 0 ≤ C ∧
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (fun y => ∑ l : Fin (Module.finrank ℝ E),
            weightedGradCoeffDivLimit (I := I) (M := M)
              g r s i α P₀ l y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal C *
          wkpRhsAggregate (I := I) (M := M) g r s i α P₀ K := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_data : ∀ l : Fin (Module.finrank ℝ E),
      MemWkp (d := Module.finrank ℝ E) K 2
          (weightedGradCoeffDivLimit (I := I) (M := M)
            g r s i α P₀ l) Ω ∧
        ∃ C : ℝ, 0 ≤ C ∧
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (weightedGradCoeffDivLimit (I := I) (M := M)
                g r s i α P₀ l) Ω
            ≤ ENNReal.ofReal C *
              wkpRhsAggregate (I := I) (M := M)
                g r s i α P₀ K := by
    intro l
    refine ⟨?_, ?_⟩
    · rw [hΩ_def]
      exact weightedGradCoeffDivLimit_memWkp (I := I) (M := M)
        g r s i α P₀ l K (fun β Q => h_pou β Q)
    obtain ⟨C, hC_nn, hC_bd⟩ := wkpNorm_weightedGradCoeffDivLimit_le_unconditional
      (I := I) (M := M) g r s i K α P₀ l (fun β Q => h_pou β Q)
    refine ⟨2 * C, by positivity, ?_⟩
    rw [hΩ_def]
    refine le_trans hC_bd ?_
    have h_sum_le :
        aggrComponent (I := I) (M := M) g r s i α K
            + aggrPartial (I := I) (M := M) g r s i α K
          ≤ 2 * wkpRhsAggregate (I := I) (M := M)
              g r s i α P₀ K := by
      rw [two_mul]
      exact add_le_add
        (aggrComponent_le (I := I) (M := M) g r s i α P₀ K)
        (aggrPartial_le (I := I) (M := M) g r s i α P₀ K)
    calc
      ENNReal.ofReal C *
          (aggrComponent (I := I) (M := M) g r s i α K
            + aggrPartial (I := I) (M := M) g r s i α K)
          ≤ ENNReal.ofReal C *
              (2 * wkpRhsAggregate (I := I) (M := M)
                g r s i α P₀ K) := by
            gcongr
      _ = ENNReal.ofReal (2 * C) *
            wkpRhsAggregate (I := I) (M := M)
              g r s i α P₀ K := by
          rw [← ofReal_two, ← mul_assoc, ← ENNReal.ofReal_mul hC_nn,
            mul_comm C 2]
  exact wkpNorm_sum_le_const_mul_aggregate (Ω := Ω) hΩ_open
    (fun l => weightedGradCoeffDivLimit (I := I) (M := M)
      g r s i α P₀ l)
    (wkpRhsAggregate (I := I) (M := M) g r s i α P₀ K)
    (fun l => (h_data l).1) (fun l => (h_data l).2)

omit [CompleteSpace E] in
private lemma rhsTerm6_wkpNorm_le
    (h_pou : eigenvectorResolventChartWkpRegularity (I := I) (M := M) g r s i K) :
    ∃ C : ℝ, 0 ≤ C ∧
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (rhsTerm6 (I := I) (M := M) g r s i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal C *
          wkpRhsAggregate (I := I) (M := M) g r s i α P₀ K := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_sum_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ∑ l : Fin (Module.finrank ℝ E),
        weightedGradCoeffDivLimit (I := I) (M := M)
          g r s i α P₀ l y) Ω :=
    memWkpFinsetSum hΩ_open
      (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
      (fun l => weightedGradCoeffDivLimit (I := I) (M := M)
        g r s i α P₀ l)
      (fun l _ => weightedGradCoeffDivLimit_memWkp (I := I) (M := M)
        g r s i α P₀ l K (fun β Q => h_pou β Q))
  have h_sum_ae_zero : ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
      y ∉ chartPouKernel (I := I) (M := M) α →
        (∑ l : Fin (Module.finrank ℝ E),
          weightedGradCoeffDivLimit (I := I) (M := M)
            g r s i α P₀ l y) = 0 :=
    Filter.Eventually.of_forall (fun _y hy =>
      Finset.sum_eq_zero (fun l _ =>
        weightedGradCoeffDivLimit_eq_zero_off_chartPouKernel_unconditional
          (I := I) (M := M) g r s i α P₀ l hy))
  obtain ⟨_, C₁, hC₁_nn, hC₁_bd⟩ := wkpNorm_smoothCoef_mul_aeZeroFactor_le
    (I := I) (M := M) α K
    (chartPouKernel_isCompact (I := I) (M := M) α)
    (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
    (one_div_densityOnEuclid_contDiffOn (I := I) (M := M) g α)
    h_sum_memWkp h_sum_ae_zero
  obtain ⟨C₂, hC₂_nn, hC₂_bd⟩ :=
    weightedGradCoeffDivLimit_sum_wkpNorm_le
      (I := I) (M := M) g r s i α P₀ K h_pou
  refine ⟨C₁ * C₂, by positivity, ?_⟩
  have h_term6_eq : rhsTerm6 (I := I) (M := M) g r s i α P₀
      = fun y => (1 / densityOnEuclid (I := I) g α y) *
          (∑ l : Fin (Module.finrank ℝ E),
            weightedGradCoeffDivLimit (I := I) (M := M)
              g r s i α P₀ l y) := rfl
  rw [h_term6_eq]
  calc
    iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
        (fun y => (1 / densityOnEuclid (I := I) g α y) *
          (∑ l : Fin (Module.finrank ℝ E),
            weightedGradCoeffDivLimit (I := I) (M := M)
              g r s i α P₀ l y)) Ω
        ≤ ENNReal.ofReal C₁ *
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (fun y => ∑ l : Fin (Module.finrank ℝ E),
                weightedGradCoeffDivLimit (I := I) (M := M)
                  g r s i α P₀ l y) Ω := hC₁_bd
    _ ≤ ENNReal.ofReal C₁ *
          (ENNReal.ofReal C₂ *
            wkpRhsAggregate (I := I) (M := M)
              g r s i α P₀ K) := by
        gcongr
    _ = ENNReal.ofReal (C₁ * C₂) *
          wkpRhsAggregate (I := I) (M := M)
            g r s i α P₀ K := by
        rw [ENNReal.ofReal_mul hC₁_nn, mul_assoc]

omit [CompleteSpace E] in
private lemma rhsTerm7_wkpNorm_le
    (h_pou : eigenvectorResolventChartWkpRegularity (I := I) (M := M) g r s i K) :
    ∃ C : ℝ, 0 ≤ C ∧
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (rhsTerm7 (I := I) (M := M) g r s i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal C *
          wkpRhsAggregate (I := I) (M := M) g r s i α P₀ K := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have h_div_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (crossRightGradCoeffDivLimit (I := I) (M := M)
        g r s i α P₀) Ω :=
    crossRightGradCoeffDivLimit_memWkp_local (I := I) (M := M)
      g r s i α P₀ K h_pou
  have h_div_ae_zero : ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
      y ∉ chartPouKernel (I := I) (M := M) α →
        crossRightGradCoeffDivLimit (I := I) (M := M)
          g r s i α P₀ y = 0 :=
    Filter.Eventually.of_forall (fun y hy_imp =>
      crossRightGradCoeffDivLimit_eq_zero_off_chartPouKernel
        (I := I) (M := M) g r s i α P₀ hy_imp)
  obtain ⟨_, C₁, hC₁_nn, hC₁_bd⟩ := wkpNorm_smoothCoef_mul_aeZeroFactor_le
    (I := I) (M := M) α K
    (chartPouKernel_isCompact (I := I) (M := M) α)
    (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
    (one_div_densityOnEuclid_contDiffOn (I := I) (M := M) g α)
    h_div_memWkp h_div_ae_zero
  obtain ⟨C₂, hC₂_nn, hC₂_bd⟩ :=
    wkpNorm_crossRightGradCoeffDivLimit_le
      (I := I) (M := M) g r s i α P₀ K (fun β Q => h_pou β Q)
  refine ⟨C₁ * (2 * C₂), by positivity, ?_⟩
  have h_term7_eq : rhsTerm7 (I := I) (M := M) g r s i α P₀
      = fun y => (1 / densityOnEuclid (I := I) g α y) *
          crossRightGradCoeffDivLimit (I := I) (M := M)
            g r s i α P₀ y := rfl
  rw [h_term7_eq]
  have h_sum_le :
      aggrCrossRightLimit (I := I) (M := M) g r s i α K
          + aggrCutoffPartial (I := I) (M := M) g r s i α K
        ≤ 2 * wkpRhsAggregate (I := I) (M := M)
            g r s i α P₀ K := by
    rw [two_mul]
    exact add_le_add
      (aggrCrossRightLimit_le (I := I) (M := M) g r s i α P₀ K)
      (aggrCutoffPartial_le (I := I) (M := M) g r s i α P₀ K)
  calc
    iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
        (fun y => (1 / densityOnEuclid (I := I) g α y) *
          crossRightGradCoeffDivLimit (I := I) (M := M)
            g r s i α P₀ y) Ω
        ≤ ENNReal.ofReal C₁ *
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (crossRightGradCoeffDivLimit (I := I) (M := M)
                g r s i α P₀) Ω := hC₁_bd
    _ ≤ ENNReal.ofReal C₁ *
          (ENNReal.ofReal C₂ *
            (2 * wkpRhsAggregate (I := I) (M := M)
              g r s i α P₀ K)) := by
        rw [hΩ_def]
        gcongr
        refine le_trans hC₂_bd ?_
        gcongr
        exact h_sum_le
    _ = ENNReal.ofReal (C₁ * (2 * C₂)) *
          wkpRhsAggregate (I := I) (M := M)
            g r s i α P₀ K := by
        rw [ENNReal.ofReal_mul hC₁_nn,
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ofReal_two]
        ring

end TermBoundsUnconditional

section BracketBoundUnconditional

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (i : TensorEigenIdx (I := I) (M := M) g r s)
  (α : M) (P₀ : TensorCompIdx (E := E) r s) (K : ℕ)

omit [CompleteSpace E] in
private lemma rhsBracket_wkpNorm_le
    (h_pou : eigenvectorResolventChartWkpRegularity (I := I) (M := M) g r s i K) :
    ∃ C : ℝ, 0 ≤ C ∧
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (rhsBracket (I := I) (M := M) g r s i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal C *
          wkpRhsAggregate (I := I) (M := M) g r s i α P₀ K := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hM1 := rhsTerm1_memWkp (I := I) (M := M)
    g r s i α P₀ K h_pou
  have hM2 := rhsTerm2_memWkp (I := I) (M := M)
    g r s i α P₀ K h_pou
  have hM3 := rhsTerm3_memWkp (I := I) (M := M)
    g r s i α P₀ K h_pou
  have hM4 := rhsTerm4_memWkp (I := I) (M := M)
    g r s i α P₀ K h_pou
  have hM5 := rhsTerm5_memWkp (I := I) (M := M)
    g r s i α P₀ K h_pou
  have hM6 := rhsTerm6_memWkp (I := I) (M := M)
    g r s i α P₀ K h_pou
  have hM7 := rhsTerm7_memWkp (I := I) (M := M)
    g r s i α P₀ K h_pou
  rw [← hΩ_def] at hM1 hM2 hM3 hM4 hM5 hM6 hM7
  have hp2 : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have hB12 : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => rhsTerm1 (I := I) (M := M) g r s i α P₀ y
        - rhsTerm2 (I := I) (M := M) g r s i α P₀ y) Ω :=
    MemWkp.sub (d := Module.finrank ℝ E) hp2 hΩ_open hM1 hM2
  have hB123 : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => (rhsTerm1 (I := I) (M := M) g r s i α P₀ y
          - rhsTerm2 (I := I) (M := M) g r s i α P₀ y)
        + rhsTerm3 (I := I) (M := M) g r s i α P₀ y) Ω :=
    MemWkp.add (d := Module.finrank ℝ E) hp2 hΩ_open hB12 hM3
  have hB1234 : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ((rhsTerm1 (I := I) (M := M) g r s i α P₀ y
            - rhsTerm2 (I := I) (M := M) g r s i α P₀ y)
          + rhsTerm3 (I := I) (M := M) g r s i α P₀ y)
        - rhsTerm4 (I := I) (M := M) g r s i α P₀ y) Ω :=
    MemWkp.sub (d := Module.finrank ℝ E) hp2 hΩ_open hB123 hM4
  have hB12345 : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => (((rhsTerm1 (I := I) (M := M) g r s i α P₀ y
              - rhsTerm2 (I := I) (M := M) g r s i α P₀ y)
            + rhsTerm3 (I := I) (M := M) g r s i α P₀ y)
          - rhsTerm4 (I := I) (M := M) g r s i α P₀ y)
        - rhsTerm5 (I := I) (M := M) g r s i α P₀ y) Ω :=
    MemWkp.sub (d := Module.finrank ℝ E) hp2 hΩ_open hB1234 hM5
  have hB123456 : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ((((rhsTerm1 (I := I) (M := M) g r s i α P₀ y
                - rhsTerm2 (I := I) (M := M) g r s i α P₀ y)
              + rhsTerm3 (I := I) (M := M) g r s i α P₀ y)
            - rhsTerm4 (I := I) (M := M) g r s i α P₀ y)
          - rhsTerm5 (I := I) (M := M) g r s i α P₀ y)
        + rhsTerm6 (I := I) (M := M) g r s i α P₀ y) Ω :=
    MemWkp.add (d := Module.finrank ℝ E) hp2 hΩ_open hB12345 hM6
  obtain ⟨D1, hD1_nn, hD1⟩ := rhsTerm1_wkpNorm_le
    (I := I) (M := M) g r s i α P₀ K
  obtain ⟨D2, hD2_nn, hD2⟩ := rhsTerm2_wkpNorm_le
    (I := I) (M := M) g r s i α P₀ K h_pou
  obtain ⟨D3, hD3_nn, hD3⟩ := rhsTerm3_wkpNorm_le
    (I := I) (M := M) g r s i α P₀ K h_pou
  obtain ⟨D4, hD4_nn, hD4⟩ := rhsTerm4_wkpNorm_le
    (I := I) (M := M) g r s i α P₀ K h_pou
  obtain ⟨D5, hD5_nn, hD5⟩ := rhsTerm5_wkpNorm_le
    (I := I) (M := M) g r s i α P₀ K h_pou
  obtain ⟨D6, hD6_nn, hD6⟩ := rhsTerm6_wkpNorm_le
    (I := I) (M := M) g r s i α P₀ K h_pou
  obtain ⟨D7, hD7_nn, hD7⟩ := rhsTerm7_wkpNorm_le
    (I := I) (M := M) g r s i α P₀ K h_pou
  rw [← hΩ_def] at hD1 hD2 hD3 hD4 hD5 hD6 hD7
  refine ⟨D1 + D2 + D3 + D4 + D5 + D6 + D7, by positivity, ?_⟩
  have h_tri :
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (rhsBracket (I := I) (M := M) g r s i α P₀) Ω
        ≤ iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (rhsTerm1 (I := I) (M := M) g r s i α P₀) Ω
          + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (rhsTerm2 (I := I) (M := M) g r s i α P₀) Ω
          + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (rhsTerm3 (I := I) (M := M) g r s i α P₀) Ω
          + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (rhsTerm4 (I := I) (M := M) g r s i α P₀) Ω
          + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (rhsTerm5 (I := I) (M := M) g r s i α P₀) Ω
          + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (rhsTerm6 (I := I) (M := M) g r s i α P₀) Ω
          + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (rhsTerm7 (I := I) (M := M) g r s i α P₀) Ω := by
    have h_bracket_eq :
        rhsBracket (I := I) (M := M) g r s i α P₀
        = fun y =>
            (((((rhsTerm1 (I := I) (M := M) g r s i α P₀ y
                  - rhsTerm2 (I := I) (M := M) g r s i α P₀ y)
                + rhsTerm3 (I := I) (M := M) g r s i α P₀ y)
              - rhsTerm4 (I := I) (M := M) g r s i α P₀ y)
            - rhsTerm5 (I := I) (M := M) g r s i α P₀ y)
          + rhsTerm6 (I := I) (M := M) g r s i α P₀ y)
          - rhsTerm7 (I := I) (M := M) g r s i α P₀ y := by
      funext y
      simp only [rhsBracket, Pi.sub_apply, Pi.add_apply]
    rw [h_bracket_eq]
    refine le_trans (wkpNorm_sub_le (K := K) hΩ_open hB123456 hM7) ?_
    refine add_le_add ?_ (le_refl _)
    refine le_trans (wkpNorm_add_le (d := Module.finrank ℝ E)
      (by norm_num) hΩ_open hB12345 hM6) ?_
    refine add_le_add ?_ (le_refl _)
    refine le_trans (wkpNorm_sub_le (K := K) hΩ_open hB1234 hM5) ?_
    refine add_le_add ?_ (le_refl _)
    refine le_trans (wkpNorm_sub_le (K := K) hΩ_open hB123 hM4) ?_
    refine add_le_add ?_ (le_refl _)
    refine le_trans (wkpNorm_add_le (d := Module.finrank ℝ E)
      (by norm_num) hΩ_open hB12 hM3) ?_
    refine add_le_add ?_ (le_refl _)
    exact wkpNorm_sub_le (K := K) hΩ_open hM1 hM2
  refine le_trans h_tri ?_
  have h_seven :
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (rhsTerm1 (I := I) (M := M) g r s i α P₀) Ω
        + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (rhsTerm2 (I := I) (M := M) g r s i α P₀) Ω
        + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (rhsTerm3 (I := I) (M := M) g r s i α P₀) Ω
        + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (rhsTerm4 (I := I) (M := M) g r s i α P₀) Ω
        + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (rhsTerm5 (I := I) (M := M) g r s i α P₀) Ω
        + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (rhsTerm6 (I := I) (M := M) g r s i α P₀) Ω
        + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (rhsTerm7 (I := I) (M := M) g r s i α P₀) Ω
      ≤ ENNReal.ofReal D1 *
            wkpRhsAggregate (I := I) (M := M) g r s i α P₀ K
          + ENNReal.ofReal D2 *
            wkpRhsAggregate (I := I) (M := M) g r s i α P₀ K
          + ENNReal.ofReal D3 *
            wkpRhsAggregate (I := I) (M := M) g r s i α P₀ K
          + ENNReal.ofReal D4 *
            wkpRhsAggregate (I := I) (M := M) g r s i α P₀ K
          + ENNReal.ofReal D5 *
            wkpRhsAggregate (I := I) (M := M) g r s i α P₀ K
          + ENNReal.ofReal D6 *
            wkpRhsAggregate (I := I) (M := M) g r s i α P₀ K
          + ENNReal.ofReal D7 *
            wkpRhsAggregate (I := I) (M := M) g r s i α P₀ K :=
    add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
      (add_le_add hD1 hD2) hD3) hD4) hD5) hD6) hD7
  refine le_trans h_seven ?_
  rw [ENNReal.ofReal_add (by positivity) hD7_nn,
    ENNReal.ofReal_add (by positivity) hD6_nn,
    ENNReal.ofReal_add (by positivity) hD5_nn,
    ENNReal.ofReal_add (by positivity) hD4_nn,
    ENNReal.ofReal_add (by positivity) hD3_nn,
    ENNReal.ofReal_add hD1_nn hD2_nn]
  rw [add_mul, add_mul, add_mul, add_mul, add_mul, add_mul]

end BracketBoundUnconditional

section MainBoundUnconditional

omit [CompleteSpace E] in
theorem eigenvectorChartRHS_wkpNorm_le
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
    ∃ C : ℝ, 0 ≤ C ∧
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (eigenvectorChartRHS (I := I) (M := M) g r s i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * C) *
          (iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (tensorResolventEigenbasisVec (I := I) (M := M)
                    (tensorResolventL2_isCompactOperator (I := I)
                      (M := M) g r s) i) α P₀ :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) α)
            + (∑ β ∈ transportChartCenters (I := I) (M := M) α,
                ((∑ Q : TensorCompIdx (E := E) r s,
                    iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K + 1) 2
                      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                            (eigenvectorResolvent (I := I) (M := M)
                              g r s i))
                          β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                          EuclN → ℝ) y)
                      (chartTargetEuclid (I := I) (M := M) β))
                  + ∑ β' ∈ transportChartCenters (I := I) (M := M) β,
                      ∑ Q : TensorCompIdx (E := E) r s,
                        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K + 1) 2
                          (fun y => ((tensorL2ChartComponent (I := I) (M := M)
                              g r s
                              (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                                (eigenvectorResolvent (I := I)
                                  (M := M) g r s i))
                              β' Q :
                              Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) :
                              EuclN → ℝ) y)
                          (chartTargetEuclid (I := I) (M := M) β')))
            + (∑ β ∈ transportChartCenters (I := I) (M := M) α,
                ∑ Q : TensorCompIdx (E := E) r s,
                  iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
                    (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                        (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                          (eigenvectorResolvent (I := I) (M := M)
                            g r s i))
                        β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                        EuclN → ℝ) y)
                    (chartTargetEuclid (I := I) (M := M) β))
            + (∑ P : TensorCompIdx (E := E) r s,
                ∑ k : Fin (Module.finrank ℝ E),
                  iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
                    (fun y => ((partialLpLimit (I := I) (M := M)
                        g r s i α P k :
                      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                      EuclN → ℝ) y)
                    (chartTargetEuclid (I := I) (M := M) α))
            + (∑ p : TensorCompIdx (E := E) r s,
                iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
                  (fun y => ((componentLpLimit (I := I) (M := M)
                      g r s i α p :
                    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                    EuclN → ℝ) y)
                  (chartTargetEuclid (I := I) (M := M) α))
            + (∑ P : TensorCompIdx (E := E) r s,
                iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
                  (fun y => ((crossRightLimitComponent (I := I)
                      (M := M) g r s i α P :
                    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                    EuclN → ℝ) y)
                  (chartTargetEuclid (I := I) (M := M) α))
            + (∑ P : TensorCompIdx (E := E) r s,
                ∑ l : Fin (Module.finrank ℝ E),
                  iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
                    (fun y => ((cutoffPartialLpLimit (I := I)
                        (M := M) g r s i α P l :
                      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                      EuclN → ℝ) y)
                    (chartTargetEuclid (I := I) (M := M) α))) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hμ_pos : 0 < i.fst.val := eigenIdx_val_pos (I := I) (M := M) g r s i
  have hμ_inv_nn : 0 ≤ (i.fst.val)⁻¹ := le_of_lt (inv_pos.mpr hμ_pos)
  have h_bracket_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (rhsBracket (I := I) (M := M) g r s i α P₀) Ω := by
    have hM1 := rhsTerm1_memWkp (I := I) (M := M)
      g r s i α P₀ K h_pou
    have hM2 := rhsTerm2_memWkp (I := I) (M := M)
      g r s i α P₀ K h_pou
    have hM3 := rhsTerm3_memWkp (I := I) (M := M)
      g r s i α P₀ K h_pou
    have hM4 := rhsTerm4_memWkp (I := I) (M := M)
      g r s i α P₀ K h_pou
    have hM5 := rhsTerm5_memWkp (I := I) (M := M)
      g r s i α P₀ K h_pou
    have hM6 := rhsTerm6_memWkp (I := I) (M := M)
      g r s i α P₀ K h_pou
    have hM7 := rhsTerm7_memWkp (I := I) (M := M)
      g r s i α P₀ K h_pou
    rw [← hΩ_def] at hM1 hM2 hM3 hM4 hM5 hM6 hM7
    have hp2 : (1 : ℝ≥0∞) ≤ 2 := by norm_num
    have h_bracket_eq :
        rhsBracket (I := I) (M := M) g r s i α P₀
        = fun y =>
            (((((rhsTerm1 (I := I) (M := M) g r s i α P₀ y
                  - rhsTerm2 (I := I) (M := M) g r s i α P₀ y)
                + rhsTerm3 (I := I) (M := M) g r s i α P₀ y)
              - rhsTerm4 (I := I) (M := M) g r s i α P₀ y)
            - rhsTerm5 (I := I) (M := M) g r s i α P₀ y)
          + rhsTerm6 (I := I) (M := M) g r s i α P₀ y)
          - rhsTerm7 (I := I) (M := M) g r s i α P₀ y := by
      funext y
      simp only [rhsBracket, Pi.sub_apply, Pi.add_apply]
    rw [h_bracket_eq]
    exact MemWkp.sub (d := Module.finrank ℝ E) hp2 hΩ_open
      (MemWkp.add (d := Module.finrank ℝ E) hp2 hΩ_open
        (MemWkp.sub (d := Module.finrank ℝ E) hp2 hΩ_open
          (MemWkp.sub (d := Module.finrank ℝ E) hp2 hΩ_open
            (MemWkp.add (d := Module.finrank ℝ E) hp2 hΩ_open
              (MemWkp.sub (d := Module.finrank ℝ E) hp2 hΩ_open hM1 hM2) hM3)
            hM4) hM5) hM6) hM7
  obtain ⟨C, hC_nn, hC_bd⟩ := rhsBracket_wkpNorm_le
    (I := I) (M := M) g r s i α P₀ K h_pou
  rw [← hΩ_def] at hC_bd
  refine ⟨C, hC_nn, ?_⟩
  have h_smul_eq :
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (eigenvectorChartRHS (I := I) (M := M)
            g r s i α P₀) Ω
        = ENNReal.ofReal (i.fst.val)⁻¹ *
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (rhsBracket (I := I) (M := M) g r s i α P₀) Ω := by
    rw [eigenvectorChartRHS_eq_smul_bracket (I := I) (M := M)
      g r s i α P₀]
    have h := wkpNorm_const_smul (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_bracket_memWkp (i.fst.val)⁻¹
    rw [h, Real.enorm_of_nonneg hμ_inv_nn]
  rw [h_smul_eq]
  have h_step :
      ENNReal.ofReal (i.fst.val)⁻¹ *
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (rhsBracket (I := I) (M := M) g r s i α P₀) Ω
        ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * C) *
          wkpRhsAggregate (I := I) (M := M) g r s i α P₀ K := by
    rw [ENNReal.ofReal_mul hμ_inv_nn, mul_assoc]
    gcongr
  refine le_trans h_step (le_of_eq ?_)
  simp only [hΩ_def, wkpRhsAggregate, aggrUchart,
    aggrCrossLeft, aggrCrossRight,
    aggrPartial, aggrComponent,
    aggrCrossRightLimit, aggrCutoffPartial,
    resolventH1ComplChartWkpNorm]

end MainBoundUnconditional

section UniformMainBoundUnconditional

omit [CompleteSpace E] in
theorem eigenvectorChartRHS_wkpNorm_le_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (K : ℕ)
    (h_pou : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (eigenvectorChartRHS (I := I) (M := M) g r s i α P₀)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * C) *
            (iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
                (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                    (tensorResolventEigenbasisVec (I := I) (M := M)
                      (tensorResolventL2_isCompactOperator (I := I)
                        (M := M) g r s) i) α P₀ :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
                (chartTargetEuclid (I := I) (M := M) α)
              + (∑ β ∈ transportChartCenters (I := I) (M := M) α,
                  ((∑ Q : TensorCompIdx (E := E) r s,
                      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K + 1) 2
                        (fun y => ((tensorL2ChartComponent (I := I) (M := M)
                            g r s
                            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                              (eigenvectorResolvent (I := I)
                                (M := M) g r s i))
                            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                            EuclN → ℝ) y)
                        (chartTargetEuclid (I := I) (M := M) β))
                    + ∑ β' ∈ transportChartCenters (I := I) (M := M) β,
                        ∑ Q : TensorCompIdx (E := E) r s,
                          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K + 1) 2
                            (fun y => ((tensorL2ChartComponent (I := I) (M := M)
                                g r s
                                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                                  (eigenvectorResolvent (I := I)
                                    (M := M) g r s i))
                                β' Q :
                                Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) :
                                EuclN → ℝ) y)
                            (chartTargetEuclid (I := I) (M := M) β')))
              + (∑ β ∈ transportChartCenters (I := I) (M := M) α,
                  ∑ Q : TensorCompIdx (E := E) r s,
                    iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
                      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                            (eigenvectorResolvent (I := I) (M := M)
                              g r s i))
                          β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                          EuclN → ℝ) y)
                      (chartTargetEuclid (I := I) (M := M) β))
              + (∑ P : TensorCompIdx (E := E) r s,
                  ∑ k : Fin (Module.finrank ℝ E),
                    iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
                      (fun y => ((partialLpLimit (I := I) (M := M)
                          g r s i α P k :
                        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                        EuclN → ℝ) y)
                      (chartTargetEuclid (I := I) (M := M) α))
              + (∑ p : TensorCompIdx (E := E) r s,
                  iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
                    (fun y => ((componentLpLimit (I := I) (M := M)
                        g r s i α p :
                      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                      EuclN → ℝ) y)
                    (chartTargetEuclid (I := I) (M := M) α))
              + (∑ P : TensorCompIdx (E := E) r s,
                  iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
                    (fun y => ((crossRightLimitComponent (I := I)
                        (M := M) g r s i α P :
                      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                      EuclN → ℝ) y)
                    (chartTargetEuclid (I := I) (M := M) α))
              + (∑ P : TensorCompIdx (E := E) r s,
                  ∑ l : Fin (Module.finrank ℝ E),
                    iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
                      (fun y => ((cutoffPartialLpLimit (I := I)
                          (M := M) g r s i α P l :
                        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                        EuclN → ℝ) y)
                      (chartTargetEuclid (I := I) (M := M) α))) := by
  classical
  obtain ⟨C, hC_nn, hC_bd⟩ := rhsBracket_wkpNorm_le_uniform
    (I := I) (M := M) g r s α P₀ K h_pou
  refine ⟨C, hC_nn, fun i => ?_⟩
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hμ_pos : 0 < i.fst.val := eigenIdx_val_pos (I := I) (M := M) g r s i
  have hμ_inv_nn : 0 ≤ (i.fst.val)⁻¹ := le_of_lt (inv_pos.mpr hμ_pos)
  have h_bracket_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (rhsBracket (I := I) (M := M) g r s i α P₀) Ω := by
    have hM1 := rhsTerm1_memWkp (I := I) (M := M)
      g r s i α P₀ K (h_pou i)
    have hM2 := rhsTerm2_memWkp (I := I) (M := M)
      g r s i α P₀ K (h_pou i)
    have hM3 := rhsTerm3_memWkp (I := I) (M := M)
      g r s i α P₀ K (h_pou i)
    have hM4 := rhsTerm4_memWkp (I := I) (M := M)
      g r s i α P₀ K (h_pou i)
    have hM5 := rhsTerm5_memWkp (I := I) (M := M)
      g r s i α P₀ K (h_pou i)
    have hM6 := rhsTerm6_memWkp (I := I) (M := M)
      g r s i α P₀ K (h_pou i)
    have hM7 := rhsTerm7_memWkp (I := I) (M := M)
      g r s i α P₀ K (h_pou i)
    rw [← hΩ_def] at hM1 hM2 hM3 hM4 hM5 hM6 hM7
    have hp2 : (1 : ℝ≥0∞) ≤ 2 := by norm_num
    have h_bracket_eq :
        rhsBracket (I := I) (M := M) g r s i α P₀
        = fun y =>
            (((((rhsTerm1 (I := I) (M := M) g r s i α P₀ y
                  - rhsTerm2 (I := I) (M := M) g r s i α P₀ y)
                + rhsTerm3 (I := I) (M := M) g r s i α P₀ y)
              - rhsTerm4 (I := I) (M := M) g r s i α P₀ y)
            - rhsTerm5 (I := I) (M := M) g r s i α P₀ y)
          + rhsTerm6 (I := I) (M := M) g r s i α P₀ y)
          - rhsTerm7 (I := I) (M := M) g r s i α P₀ y := by
      funext y
      simp only [rhsBracket, Pi.sub_apply, Pi.add_apply]
    rw [h_bracket_eq]
    exact MemWkp.sub (d := Module.finrank ℝ E) hp2 hΩ_open
      (MemWkp.add (d := Module.finrank ℝ E) hp2 hΩ_open
        (MemWkp.sub (d := Module.finrank ℝ E) hp2 hΩ_open
          (MemWkp.sub (d := Module.finrank ℝ E) hp2 hΩ_open
            (MemWkp.add (d := Module.finrank ℝ E) hp2 hΩ_open
              (MemWkp.sub (d := Module.finrank ℝ E) hp2 hΩ_open hM1 hM2) hM3)
            hM4) hM5) hM6) hM7
  have hC_bd_i := hC_bd i
  have h_smul_eq :
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (eigenvectorChartRHS (I := I) (M := M)
            g r s i α P₀) Ω
        = ENNReal.ofReal (i.fst.val)⁻¹ *
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (rhsBracket (I := I) (M := M) g r s i α P₀) Ω := by
    rw [eigenvectorChartRHS_eq_smul_bracket (I := I) (M := M)
      g r s i α P₀]
    have h := wkpNorm_const_smul (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_bracket_memWkp (i.fst.val)⁻¹
    rw [h, Real.enorm_of_nonneg hμ_inv_nn]
  rw [h_smul_eq]
  have h_step :
      ENNReal.ofReal (i.fst.val)⁻¹ *
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (rhsBracket (I := I) (M := M) g r s i α P₀) Ω
        ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * C) *
          wkpRhsAggregate (I := I) (M := M) g r s i α P₀ K := by
    rw [ENNReal.ofReal_mul hμ_inv_nn, mul_assoc]
    gcongr
  refine le_trans h_step (le_of_eq ?_)
  simp only [hΩ_def, wkpRhsAggregate, aggrUchart,
    aggrCrossLeft, aggrCrossRight,
    aggrPartial, aggrComponent,
    aggrCrossRightLimit, aggrCutoffPartial,
    resolventH1ComplChartWkpNorm]

end UniformMainBoundUnconditional

end Unconditional

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
