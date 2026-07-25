import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.RHS.ChartRHSBounds.EigenvectorChartRHS
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Cross.EigenvectorChartCrossLimits
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Cross.EigenvectorChartCrossRightLimit
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Cross.EigenvectorChartCrossRightDiv
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.LowerOrder.EigenvectorChartLowerOrderLimits
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.VariationalIdentity.EigenvectorChartTestDecoupling
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Component.EigenvectorChartComponentL2
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.ChartPartial.EigenvectorChartPartialL2
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.EnergyBound.EigenvectorChartWeightedMemLp
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.ChartPartial.EigenvectorWeakPartials
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.VariationalIdentity.TensorChartBilinearData
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.AbstractChartPull
import DifferentialGeometry.Analysis.Elliptic.TensorRegularity.WeakSolution.WeakSolutionDirichlet
import DifferentialGeometry.Analysis.Elliptic.TensorRegularity.Bootstrap.BootstrapSource
import DifferentialGeometry.Analysis.Elliptic.TensorRegularity.DirichletForm.RotatedTestSection
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovariantLeibniz
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.VariationalIdentity.EigenvectorPouApproxRegularity

noncomputable section

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators
  RealInnerProductSpace InnerProductSpace Matrix

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
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
open DifferentialGeometry.Analysis.Laplacian.ChartLocalLaplacian

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [CompleteSpace E] in
theorem covPrincipalRotationCoeff_source_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    Filter.Tendsto
      (fun n => ∫ y, densityOnEuclid (I := I) g α y *
          covPrincipalRotationCoeff (I := I) (M := M) g r s
            (eigenvectorPouApprox (I := I) (M := M) g r s i α n)
            α P₀ y * ψ y ∂(volume : Measure EuclN))
      atTop
      (𝓝 (∫ y, densityOnEuclid (I := I) g α y *
          covPrincipalRotationCoeffLimit (I := I) (M := M)
            g r s i α P₀ y * ψ y ∂(volume : Measure EuclN))) := by
  classical
  set μch : Measure EuclN := chartL2Measure (I := I) (M := M) α with hμch_def
  set m : Lp ℝ 2 μch :=
    (densityOnEuclid_mul_test_memLp (I := I) (M := M) g α hψ hψ_cs hψ_supp).toLp _
    with hm_def
  set glim : Lp ℝ 2 μch :=
    (covPrincipalRotationCoeffLimit_memLp (I := I) (M := M)
      g r s i α P₀).toLp _ with hglim_def
  set gseq : ℕ → Lp ℝ 2 μch := fun n =>
    (covPrincipalRotationCoeff_pouSmul_memLp (I := I) (M := M)
      g r s i α P₀ n).toLp _ with hgseq_def
  have h_int_n : ∀ n : ℕ,
      ∫ y, (m : EuclN → ℝ) y * (gseq n : EuclN → ℝ) y ∂μch =
        ∫ y, densityOnEuclid (I := I) g α y *
          covPrincipalRotationCoeff (I := I) (M := M) g r s
            (eigenvectorPouApprox (I := I) (M := M) g r s i α n)
            α P₀ y * ψ y ∂(volume : Measure EuclN) := by
    intro n
    have h_m_ae : (m : EuclN → ℝ) =ᵐ[μch]
        fun y => densityOnEuclid (I := I) g α y * ψ y := by
      rw [hm_def]; exact MemLp.coeFn_toLp _
    have h_g_ae : (gseq n : EuclN → ℝ) =ᵐ[μch]
        covPrincipalRotationCoeff (I := I) (M := M) g r s
          (eigenvectorPouApprox (I := I) (M := M) g r s i α n)
          α P₀ := by
      rw [hgseq_def]; exact MemLp.coeFn_toLp _
    have h_ae_prod : (fun y => (m : EuclN → ℝ) y * (gseq n : EuclN → ℝ) y)
        =ᵐ[μch]
        fun y => densityOnEuclid (I := I) g α y *
          covPrincipalRotationCoeff (I := I) (M := M) g r s
            (eigenvectorPouApprox (I := I) (M := M) g r s i α n)
            α P₀ y * ψ y := by
      filter_upwards [h_m_ae, h_g_ae] with y hy_m hy_g
      rw [hy_m, hy_g]; ring
    rw [integral_congr_ae h_ae_prod, hμch_def, chartL2Measure]
    refine MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero ?_
    intro y hy
    rw [image_eq_zero_of_notMem_tsupport (fun h => hy (hψ_supp h)), mul_zero]
  have h_int_lim :
      ∫ y, (m : EuclN → ℝ) y * (glim : EuclN → ℝ) y ∂μch =
        ∫ y, densityOnEuclid (I := I) g α y *
          covPrincipalRotationCoeffLimit (I := I) (M := M)
            g r s i α P₀ y * ψ y ∂(volume : Measure EuclN) := by
    have h_m_ae : (m : EuclN → ℝ) =ᵐ[μch]
        fun y => densityOnEuclid (I := I) g α y * ψ y := by
      rw [hm_def]; exact MemLp.coeFn_toLp _
    have h_g_ae : (glim : EuclN → ℝ) =ᵐ[μch]
        covPrincipalRotationCoeffLimit (I := I) (M := M)
          g r s i α P₀ := by
      rw [hglim_def]; exact MemLp.coeFn_toLp _
    have h_ae_prod : (fun y => (m : EuclN → ℝ) y * (glim : EuclN → ℝ) y)
        =ᵐ[μch]
        fun y => densityOnEuclid (I := I) g α y *
          covPrincipalRotationCoeffLimit (I := I) (M := M)
            g r s i α P₀ y * ψ y := by
      filter_upwards [h_m_ae, h_g_ae] with y hy_m hy_g
      rw [hy_m, hy_g]; ring
    rw [integral_congr_ae h_ae_prod, hμch_def, chartL2Measure]
    refine MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero ?_
    intro y hy
    rw [image_eq_zero_of_notMem_tsupport (fun h => hy (hψ_supp h)), mul_zero]
  have h_tendsto_lp : Filter.Tendsto gseq atTop (𝓝 glim) := by
    rw [hgseq_def, hglim_def]
    exact covPrincipalRotationCoeff_tendsto (I := I) (M := M)
      g r s i α P₀
  have h_main := tendsto_lp_inner_integral (μ := μch) m h_tendsto_lp
  rw [h_int_lim] at h_main
  exact h_main.congr (fun n => h_int_n n)

omit [CompleteSpace E] in
theorem covLowerOrderRotationValueCoeff_source_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    Filter.Tendsto
      (fun n => ∫ y, densityOnEuclid (I := I) g α y *
          covLowerOrderRotationValueCoeff (I := I) (M := M) g r s
            (eigenvectorPouApprox (I := I) (M := M) g r s i α n)
            α P₀ y * ψ y ∂(volume : Measure EuclN))
      atTop
      (𝓝 (∫ y, densityOnEuclid (I := I) g α y *
          covLowerOrderRotationValueCoeffLimit (I := I) (M := M)
            g r s i α P₀ y * ψ y ∂(volume : Measure EuclN))) := by
  classical
  set μch : Measure EuclN := chartL2Measure (I := I) (M := M) α with hμch_def
  set m : Lp ℝ 2 μch :=
    (densityOnEuclid_mul_test_memLp (I := I) (M := M) g α hψ hψ_cs hψ_supp).toLp _
    with hm_def
  set glim : Lp ℝ 2 μch :=
    (covLowerOrderRotationValueCoeffLimit_memLp (I := I) (M := M)
      g r s i α P₀).toLp _ with hglim_def
  set gseq : ℕ → Lp ℝ 2 μch := fun n =>
    (covLowerOrderRotationValueCoeff_pouSmul_memLp (I := I) (M := M)
      g r s i α P₀ n).toLp _ with hgseq_def
  have h_int_n : ∀ n : ℕ,
      ∫ y, (m : EuclN → ℝ) y * (gseq n : EuclN → ℝ) y ∂μch =
        ∫ y, densityOnEuclid (I := I) g α y *
          covLowerOrderRotationValueCoeff (I := I) (M := M) g r s
            (eigenvectorPouApprox (I := I) (M := M) g r s i α n)
            α P₀ y * ψ y ∂(volume : Measure EuclN) := by
    intro n
    have h_m_ae : (m : EuclN → ℝ) =ᵐ[μch]
        fun y => densityOnEuclid (I := I) g α y * ψ y := by
      rw [hm_def]; exact MemLp.coeFn_toLp _
    have h_g_ae : (gseq n : EuclN → ℝ) =ᵐ[μch]
        covLowerOrderRotationValueCoeff (I := I) (M := M) g r s
          (eigenvectorPouApprox (I := I) (M := M) g r s i α n)
          α P₀ := by
      rw [hgseq_def]; exact MemLp.coeFn_toLp _
    have h_ae_prod : (fun y => (m : EuclN → ℝ) y * (gseq n : EuclN → ℝ) y)
        =ᵐ[μch]
        fun y => densityOnEuclid (I := I) g α y *
          covLowerOrderRotationValueCoeff (I := I) (M := M) g r s
            (eigenvectorPouApprox (I := I) (M := M) g r s i α n)
            α P₀ y * ψ y := by
      filter_upwards [h_m_ae, h_g_ae] with y hy_m hy_g
      rw [hy_m, hy_g]; ring
    rw [integral_congr_ae h_ae_prod, hμch_def, chartL2Measure]
    refine MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero ?_
    intro y hy
    rw [image_eq_zero_of_notMem_tsupport (fun h => hy (hψ_supp h)), mul_zero]
  have h_int_lim :
      ∫ y, (m : EuclN → ℝ) y * (glim : EuclN → ℝ) y ∂μch =
        ∫ y, densityOnEuclid (I := I) g α y *
          covLowerOrderRotationValueCoeffLimit (I := I) (M := M)
            g r s i α P₀ y * ψ y ∂(volume : Measure EuclN) := by
    have h_m_ae : (m : EuclN → ℝ) =ᵐ[μch]
        fun y => densityOnEuclid (I := I) g α y * ψ y := by
      rw [hm_def]; exact MemLp.coeFn_toLp _
    have h_g_ae : (glim : EuclN → ℝ) =ᵐ[μch]
        covLowerOrderRotationValueCoeffLimit (I := I) (M := M)
          g r s i α P₀ := by
      rw [hglim_def]; exact MemLp.coeFn_toLp _
    have h_ae_prod : (fun y => (m : EuclN → ℝ) y * (glim : EuclN → ℝ) y)
        =ᵐ[μch]
        fun y => densityOnEuclid (I := I) g α y *
          covLowerOrderRotationValueCoeffLimit (I := I) (M := M)
            g r s i α P₀ y * ψ y := by
      filter_upwards [h_m_ae, h_g_ae] with y hy_m hy_g
      rw [hy_m, hy_g]; ring
    rw [integral_congr_ae h_ae_prod, hμch_def, chartL2Measure]
    refine MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero ?_
    intro y hy
    rw [image_eq_zero_of_notMem_tsupport (fun h => hy (hψ_supp h)), mul_zero]
  have h_tendsto_lp : Filter.Tendsto gseq atTop (𝓝 glim) := by
    rw [hgseq_def, hglim_def]
    exact covLowerOrderRotationValueCoeff_tendsto (I := I) (M := M)
      g r s i α P₀
  have h_main := tendsto_lp_inner_integral (μ := μch) m h_tendsto_lp
  rw [h_int_lim] at h_main
  exact h_main.congr (fun n => h_int_n n)

omit [CompleteSpace E] in
theorem weightedGradCoeffDivSum_source_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    Filter.Tendsto
      (fun n => ∫ y, (∑ l : Fin (Module.finrank ℝ E),
          euclidPartial (E := E) l
            (weightedGradCoeff (I := I) (M := M) g r s
              (eigenvectorPouApprox (I := I) (M := M) g r s i α n)
              α P₀ l) y) * ψ y ∂(volume : Measure EuclN))
      atTop
      (𝓝 (∫ y, (∑ l : Fin (Module.finrank ℝ E),
          weightedGradCoeffDivLimit (I := I) (M := M)
            g r s i α P₀ l y) * ψ y ∂(volume : Measure EuclN))) := by
  classical
  set m : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) :=
    (test_memLp (I := I) (M := M) α hψ hψ_cs).toLp _ with hm_def
  set gseq : ℕ → Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) := fun n =>
    ∑ l : Fin (Module.finrank ℝ E),
      (euclidPartial_weightedGradCoeff_pouSmul_memLp (I := I) (M := M)
        g r s i α P₀ l n).toLp _ with hgseq_def
  set glim : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) :=
    ∑ l : Fin (Module.finrank ℝ E),
      (weightedGradCoeffDivLimit_memLp (I := I) (M := M)
        g r s i α P₀ l).toLp _ with hglim_def
  have h_m_ae : (m : EuclN → ℝ) =ᵐ[chartL2Measure (I := I) (M := M) α] ψ := by
    rw [hm_def]; exact MemLp.coeFn_toLp _
  have h_gseq_ae : ∀ n : ℕ, (gseq n : EuclN → ℝ)
      =ᵐ[chartL2Measure (I := I) (M := M) α]
      fun y => ∑ l : Fin (Module.finrank ℝ E),
        euclidPartial (E := E) l
          (weightedGradCoeff (I := I) (M := M) g r s
            (eigenvectorPouApprox (I := I) (M := M) g r s i α n)
            α P₀ l) y := fun n => by
    rw [hgseq_def]
    exact coeFn_finsetSum_toLp (I := I) (M := M) α
      (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
      (fun l => euclidPartial_weightedGradCoeff_pouSmul_memLp
        (I := I) (M := M) g r s i α P₀ l n)
  have h_glim_ae : (glim : EuclN → ℝ)
      =ᵐ[chartL2Measure (I := I) (M := M) α]
      fun y => ∑ l : Fin (Module.finrank ℝ E),
        weightedGradCoeffDivLimit (I := I) (M := M)
          g r s i α P₀ l y := by
    rw [hglim_def]
    exact coeFn_finsetSum_toLp (I := I) (M := M) α
      (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
      (fun l => weightedGradCoeffDivLimit_memLp (I := I) (M := M)
        g r s i α P₀ l)
  have h_int_n : ∀ n : ℕ,
      ∫ y, (m : EuclN → ℝ) y * (gseq n : EuclN → ℝ) y
          ∂(chartL2Measure (I := I) (M := M) α) =
        ∫ y, (∑ l : Fin (Module.finrank ℝ E),
            euclidPartial (E := E) l
              (weightedGradCoeff (I := I) (M := M) g r s
                (eigenvectorPouApprox (I := I) (M := M)
                  g r s i α n)
                α P₀ l) y) * ψ y ∂(volume : Measure EuclN) := by
    intro n
    have h_ae_prod : (fun y => (m : EuclN → ℝ) y * (gseq n : EuclN → ℝ) y)
        =ᵐ[chartL2Measure (I := I) (M := M) α]
        fun y => (∑ l : Fin (Module.finrank ℝ E),
          euclidPartial (E := E) l
            (weightedGradCoeff (I := I) (M := M) g r s
              (eigenvectorPouApprox (I := I) (M := M) g r s i α n)
              α P₀ l) y) * ψ y := by
      filter_upwards [h_m_ae, h_gseq_ae n] with y hy_m hy_g
      rw [hy_m, hy_g]; ring
    rw [integral_congr_ae h_ae_prod, chartL2Measure]
    refine MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero ?_
    intro y hy
    rw [image_eq_zero_of_notMem_tsupport (fun h => hy (hψ_supp h)), mul_zero]
  have h_int_lim :
      ∫ y, (m : EuclN → ℝ) y * (glim : EuclN → ℝ) y
          ∂(chartL2Measure (I := I) (M := M) α) =
        ∫ y, (∑ l : Fin (Module.finrank ℝ E),
            weightedGradCoeffDivLimit (I := I) (M := M)
              g r s i α P₀ l y) * ψ y ∂(volume : Measure EuclN) := by
    have h_ae_prod : (fun y => (m : EuclN → ℝ) y * (glim : EuclN → ℝ) y)
        =ᵐ[chartL2Measure (I := I) (M := M) α]
        fun y => (∑ l : Fin (Module.finrank ℝ E),
          weightedGradCoeffDivLimit (I := I) (M := M)
            g r s i α P₀ l y) * ψ y := by
      filter_upwards [h_m_ae, h_glim_ae] with y hy_m hy_g
      rw [hy_m, hy_g]; ring
    rw [integral_congr_ae h_ae_prod, chartL2Measure]
    refine MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero ?_
    intro y hy
    rw [image_eq_zero_of_notMem_tsupport (fun h => hy (hψ_supp h)), mul_zero]
  have h_tendsto_lp : Filter.Tendsto gseq atTop (𝓝 glim) :=
    weightedGradCoeffDivSum_tendsto (I := I) (M := M)
      g r s i α P₀
  have h_main := tendsto_lp_inner_integral
    (μ := chartL2Measure (I := I) (M := M) α) m h_tendsto_lp
  rw [h_int_lim] at h_main
  exact h_main.congr (fun n => h_int_n n)

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
