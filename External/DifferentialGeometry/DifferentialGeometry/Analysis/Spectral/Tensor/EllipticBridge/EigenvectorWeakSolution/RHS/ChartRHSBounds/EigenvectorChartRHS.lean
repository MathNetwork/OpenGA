import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Smooth.SmoothApprox
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Component.EigenvectorChartComponentL2
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.EnergyBound.EigenvectorChartWeightedMemLp
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.VariationalIdentity.EigenvectorChartTestDecoupling
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Cross.EigenvectorChartCrossRightDiv


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
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Analysis.Laplacian.MetricExtension hiding chartTargetEuclid
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in

noncomputable def eigenvectorChartRHS
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) : EuclN → ℝ :=
  fun y =>
    (i.fst.val)⁻¹ *
      (
        ((tensorL2ChartComponent (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i) α P₀ :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
        - (∑ P : TensorCompIdx (E := E) r (s + 1),
            ∑ Q : TensorCompIdx (E := E) r (s + 1),
              (covChartMetricGram (I := I) (M := M) g r (s + 1) α P Q y *
                  crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y) *
                ((crossLeftLimitComponent (I := I) (M := M)
                  g r s i α P :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
        + (∑ P : TensorCompIdx (E := E) r s,
            ∑ Q : TensorCompIdx (E := E) r s,
              (covChartMetricGram (I := I) (M := M) g r s α P Q y *
                  crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y) *
                ((crossRightLimitComponent (I := I) (M := M)
                  g r s i α P :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
        - covPrincipalRotationCoeffLimit (I := I) (M := M)
            g r s i α P₀ y
        - covLowerOrderRotationValueCoeffLimit (I := I) (M := M)
            g r s i α P₀ y
        + (1 / densityOnEuclid (I := I) g α y) *
            (∑ l : Fin (Module.finrank ℝ E),
              weightedGradCoeffDivLimit (I := I) (M := M)
                g r s i α P₀ l y)
        - (1 / densityOnEuclid (I := I) g α y) *
            crossRightGradCoeffDivLimit (I := I) (M := M)
              g r s i α P₀ y)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma one_div_densityOnEuclid_contDiffOn
    (g : SmoothRiemannianMetric I M) (α : M) :
    ContDiffOn ℝ ∞ (fun y => 1 / densityOnEuclid (I := I) g α y)
      (chartTargetEuclid (I := I) (M := M) α) :=
  contDiffOn_const.div (densityOnEuclid_contDiffOn (I := I) g α)
    (fun _ hy => (densityOnEuclid_pos (I := I) g α hy).ne')

omit [CompleteSpace E] in
lemma crossRightGradCoeffDivLimit_eq_zero_off_chartPouKernel
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    {y : EuclN} (hy : y ∉ chartPouKernel (I := I) (M := M) α) :
    crossRightGradCoeffDivLimit (I := I) (M := M)
        g r s i α P₀ y = 0 := by
  classical
  rw [crossRightGradCoeffDivLimit,
    Finset.sum_eq_zero (fun l _ => Finset.sum_eq_zero (fun P _ =>
      Finset.sum_eq_zero (fun Q _ => by
        rw [Set.indicator_of_notMem hy, zero_mul]))),
    Finset.sum_eq_zero (fun l _ => Finset.sum_eq_zero (fun P _ =>
      Finset.sum_eq_zero (fun Q _ => by
        rw [Set.indicator_of_notMem hy, zero_mul]))),
    add_zero]

omit [CompleteSpace E] in
private lemma crossRightGradCoeffDivLimit_memLp_weighted
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    MemLp (crossRightGradCoeffDivLimit (I := I) (M := M)
        g r s i α P₀) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  have h_plain : MemLp (crossRightGradCoeffDivLimit (I := I) (M := M)
      g r s i α P₀) 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
    crossRightGradCoeffDivLimit_memLp (I := I) (M := M)
      g r s i α P₀
  exact memLp_chartPulledWeightedMeasure_of_memLp_volume_of_ae_zero_off_compact
    (I := I) (M := M) g α
    (chartPouKernel_isCompact (I := I) (M := M) α)
    (chartPouKernel_measurableSet (I := I) (M := M) α)
    (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
    (Filter.Eventually.of_forall (fun y hy =>
      crossRightGradCoeffDivLimit_eq_zero_off_chartPouKernel
        (I := I) (M := M) g r s i α P₀ hy))
    h_plain

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in

omit [CompleteSpace E] in
theorem eigenvectorChartRHS_memLp_weighted
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    MemLp (eigenvectorChartRHS (I := I) (M := M) g r s i α P₀) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  set μw : Measure EuclN :=
    (chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α) with hμw_def
  have h_uchart : MemLp
      (fun y =>
        ((tensorL2ChartComponent (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i) α P₀ :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) 2 μw := by
    rw [hμw_def]
    exact tensorL2ChartComponent_memLp_weighted (I := I) (M := M) g r s
      (tensorResolventEigenbasisVec (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M)
          g r s) i) α P₀
  have h_crossLeft : ∀ (P Q : TensorCompIdx (E := E) r (s + 1)),
      MemLp
        (fun y => (covChartMetricGram (I := I) (M := M) g r (s + 1) α P Q y *
            crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y) *
          ((crossLeftLimitComponent (I := I) (M := M)
            g r s i α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) 2 μw := by
    intro P Q
    rw [hμw_def]
    have h_aezero :
        ∀ᵐ y ∂((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)),
          y ∉ cutoffChartKernelEuclid (I := I) (M := M) α →
            ((crossLeftLimitComponent (I := I) (M := M)
              g r s i α P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y = 0 := by
      rw [crossLeftLimitComponent]
      exact tensorL2ChartComponentCutoff_ae_zero_off_cutoffChartKernelEuclid_weighted
        (I := I) (M := M) g r (s + 1)
        (tensorCovGradL2Compl (I := I) (M := M) g r s
          (eigenvectorResolvent (I := I) (M := M) g r s i)) α P
    exact memLp_weighted_contDiffOn_mul (I := I) (M := M) g α
      ((covChartMetricGram_contDiffOn (I := I) (M := M) g r (s + 1) α P Q).mul
        (crossLeftTestCoeff_contDiffOn (I := I) (M := M) g r s α P₀ Q))
      (cutoffChartKernelEuclid_isCompact (I := I) (M := M) α)
      (cutoffChartKernelEuclid_measurableSet (I := I) (M := M) α)
      (cutoffChartKernelEuclid_subset_chartTargetEuclid (I := I) (M := M) α)
      (crossLeftLimitComponent_memLp_weighted_unconditional (I := I) (M := M)
        g r s i α P)
      h_aezero
  have h_crossRight : ∀ (P Q : TensorCompIdx (E := E) r s),
      MemLp
        (fun y => (covChartMetricGram (I := I) (M := M) g r s α P Q y *
            crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y) *
          ((crossRightLimitComponent (I := I) (M := M)
            g r s i α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) 2 μw := by
    intro P Q
    rw [hμw_def]
    have h_aezero :
        ∀ᵐ y ∂((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)),
          y ∉ cutoffChartKernelEuclid (I := I) (M := M) α →
            ((crossRightLimitComponent (I := I) (M := M)
              g r s i α P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y = 0 := by
      rw [crossRightLimitComponent]
      exact tensorL2ChartComponentCutoff_ae_zero_off_cutoffChartKernelEuclid_weighted
        (I := I) (M := M) g r s
        (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
          (eigenvectorResolvent (I := I) (M := M) g r s i)) α P
    exact memLp_weighted_contDiffOn_mul (I := I) (M := M) g α
      ((covChartMetricGram_contDiffOn (I := I) (M := M) g r s α P Q).mul
        (crossRightTestValueCoeff_contDiffOn (I := I) (M := M) g r s α P₀ Q))
      (cutoffChartKernelEuclid_isCompact (I := I) (M := M) α)
      (cutoffChartKernelEuclid_measurableSet (I := I) (M := M) α)
      (cutoffChartKernelEuclid_subset_chartTargetEuclid (I := I) (M := M) α)
      (crossRightLimitComponent_memLp_weighted_unconditional (I := I) (M := M)
        g r s i α P)
      h_aezero
  have h_prc : MemLp (covPrincipalRotationCoeffLimit (I := I) (M := M)
      g r s i α P₀) 2 μw := by
    rw [hμw_def]
    exact covPrincipalRotationCoeffLimit_memLp_weighted_unconditional
      (I := I) (M := M) g r s i α P₀
  have h_lov : MemLp (covLowerOrderRotationValueCoeffLimit
      (I := I) (M := M) g r s i α P₀) 2 μw := by
    rw [hμw_def]
    exact covLowerOrderRotationValueCoeffLimit_memLp_weighted_unconditional
      (I := I) (M := M) g r s i α P₀
  have h_gradDiv : MemLp
      (fun y => (1 / densityOnEuclid (I := I) g α y) *
        (∑ l : Fin (Module.finrank ℝ E),
          weightedGradCoeffDivLimit (I := I) (M := M)
            g r s i α P₀ l y)) 2 μw := by
    rw [hμw_def]
    have h_div_sum : MemLp
        (fun y => ∑ l : Fin (Module.finrank ℝ E),
          weightedGradCoeffDivLimit (I := I) (M := M)
            g r s i α P₀ l y) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
      memLp_finset_sum (μ := (chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))
        (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
        (fun l _ => weightedGradCoeffDivLimit_memLp_weighted_unconditional
          (I := I) (M := M) g r s i α P₀ l)
    have h_aezero :
        ∀ᵐ y ∂((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)),
          y ∉ chartPouKernel (I := I) (M := M) α →
            (∑ l : Fin (Module.finrank ℝ E),
              weightedGradCoeffDivLimit (I := I) (M := M)
                g r s i α P₀ l y) = 0 :=
      Filter.Eventually.of_forall (fun y hy =>
        Finset.sum_eq_zero (fun l _ =>
          weightedGradCoeffDivLimit_eq_zero_off_chartPouKernel_unconditional
            (I := I) (M := M) g r s i α P₀ l hy))
    exact memLp_weighted_contDiffOn_mul (I := I) (M := M) g α
      (one_div_densityOnEuclid_contDiffOn (I := I) (M := M) g α)
      (chartPouKernel_isCompact (I := I) (M := M) α)
      (chartPouKernel_measurableSet (I := I) (M := M) α)
      (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
      h_div_sum h_aezero
  have h_crossRightDiv : MemLp
      (fun y => (1 / densityOnEuclid (I := I) g α y) *
        crossRightGradCoeffDivLimit (I := I) (M := M)
          g r s i α P₀ y) 2 μw := by
    rw [hμw_def]
    have h_aezero :
        ∀ᵐ y ∂((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)),
          y ∉ chartPouKernel (I := I) (M := M) α →
            crossRightGradCoeffDivLimit (I := I) (M := M)
              g r s i α P₀ y = 0 :=
      Filter.Eventually.of_forall (fun y hy =>
        crossRightGradCoeffDivLimit_eq_zero_off_chartPouKernel
          (I := I) (M := M) g r s i α P₀ hy)
    exact memLp_weighted_contDiffOn_mul (I := I) (M := M) g α
      (one_div_densityOnEuclid_contDiffOn (I := I) (M := M) g α)
      (chartPouKernel_isCompact (I := I) (M := M) α)
      (chartPouKernel_measurableSet (I := I) (M := M) α)
      (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
      (crossRightGradCoeffDivLimit_memLp_weighted (I := I) (M := M)
        g r s i α P₀)
      h_aezero
  have h_crossLeft_sum : MemLp
      (fun y => ∑ P : TensorCompIdx (E := E) r (s + 1),
        ∑ Q : TensorCompIdx (E := E) r (s + 1),
          (covChartMetricGram (I := I) (M := M) g r (s + 1) α P Q y *
              crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y) *
            ((crossLeftLimitComponent (I := I) (M := M)
              g r s i α P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      2 μw :=
    memLp_finset_sum (μ := μw)
      (Finset.univ : Finset (TensorCompIdx (E := E) r (s + 1)))
      (fun P _ => memLp_finset_sum (μ := μw)
        (Finset.univ : Finset (TensorCompIdx (E := E) r (s + 1)))
        (fun Q _ => h_crossLeft P Q))
  have h_crossRight_sum : MemLp
      (fun y => ∑ P : TensorCompIdx (E := E) r s,
        ∑ Q : TensorCompIdx (E := E) r s,
          (covChartMetricGram (I := I) (M := M) g r s α P Q y *
              crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y) *
            ((crossRightLimitComponent (I := I) (M := M)
              g r s i α P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      2 μw :=
    memLp_finset_sum (μ := μw)
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun P _ => memLp_finset_sum (μ := μw)
        (Finset.univ : Finset (TensorCompIdx (E := E) r s))
        (fun Q _ => h_crossRight P Q))
  have h_total :
      MemLp (eigenvectorChartRHS (I := I) (M := M) g r s i α P₀) 2
        μw := by
    have h_bracket :=
      ((((((h_uchart.sub h_crossLeft_sum).add h_crossRight_sum).sub h_prc).sub
        h_lov).add h_gradDiv).sub h_crossRightDiv)
    have h_assembled := h_bracket.const_mul (i.fst.val)⁻¹
    refine h_assembled.ae_eq ?_
    refine Filter.Eventually.of_forall (fun y => ?_)
    simp only [eigenvectorChartRHS, Pi.add_apply, Pi.sub_apply]
  rw [hμw_def] at h_total
  exact h_total

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
