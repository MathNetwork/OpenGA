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
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.VariationalIdentity.EigenvectorSourceRotationCoeffLimits
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.VariationalIdentity.EigenvectorRotatedTestCrossTerms

noncomputable section

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000
set_option backward.isDefEq.respectTransparency false

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

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in

omit [CompleteSpace E] in
theorem eigenvectorChartVariationalIdentity
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      (∑ i' : Fin (Module.finrank ℝ E),
        ∑ j' : Fin (Module.finrank ℝ E),
          weightedInvGramOnEuclid (I := I) g α i' j' y *
            eigenvectorChartWeakPartial (I := I) (M := M)
              g r s i α P₀ i' y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j' 1))
      ∂(volume : Measure EuclN)) +
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y *
        ((tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M)
              g r s) i) α P₀ :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y * ψ y
      ∂(volume : Measure EuclN)) =
    ∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y *
        eigenvectorChartRHS (I := I) (M := M) g r s i α P₀ y * ψ y
      ∂(volume : Measure EuclN) := by
  classical
  set μ : ℝ := i.fst.val with hμ_def
  have hμ_ne : μ ≠ 0 := i.fst.val_ne_zero
  set φ : TensorL2 r s g :=
    tensorResolventEigenbasisVec (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s) i
    with hφ_def
  set P : ℝ := ∫ y in chartTargetEuclid (I := I) (M := M) α,
    (∑ i' : Fin (Module.finrank ℝ E),
      ∑ j' : Fin (Module.finrank ℝ E),
        weightedInvGramOnEuclid (I := I) g α i' j' y *
          eigenvectorChartWeakPartial (I := I) (M := M)
            g r s i α P₀ i' y *
          (fderiv ℝ ψ y) (EuclideanSpace.single j' 1))
    ∂(volume : Measure EuclN) with hP_def
  set U : ℝ := ∫ y in chartTargetEuclid (I := I) (M := M) α,
    densityOnEuclid (I := I) g α y *
      ((tensorL2ChartComponent (I := I) (M := M) g r s φ α P₀ :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y * ψ y
    ∂(volume : Measure EuclN) with hU_def
  set CL : ℝ := ∫ y in chartTargetEuclid (I := I) (M := M) α,
    densityOnEuclid (I := I) g α y *
      (∑ P' : TensorCompIdx (E := E) r (s + 1),
        ∑ Q : TensorCompIdx (E := E) r (s + 1),
          covChartMetricGram (I := I) (M := M) g r (s + 1) α P' Q y *
              crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y *
            ((crossLeftLimitComponent (I := I) (M := M)
              g r s i α P' :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) *
      ψ y ∂(volume : Measure EuclN) with hCL_def
  set CRV : ℝ := ∫ y in chartTargetEuclid (I := I) (M := M) α,
    densityOnEuclid (I := I) g α y *
      (∑ P' : TensorCompIdx (E := E) r s,
        ∑ Q : TensorCompIdx (E := E) r s,
          covChartMetricGram (I := I) (M := M) g r s α P' Q y *
              crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y *
            ((crossRightLimitComponent (I := I) (M := M)
              g r s i α P' :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) *
      ψ y ∂(volume : Measure EuclN) with hCRV_def
  set CRGdiv : ℝ := ∫ y in chartTargetEuclid (I := I) (M := M) α,
    crossRightGradCoeffDivLimit (I := I) (M := M)
      g r s i α P₀ y * ψ y ∂(volume : Measure EuclN) with hCRGdiv_def
  set PRC : ℝ := ∫ y, densityOnEuclid (I := I) g α y *
      covPrincipalRotationCoeffLimit (I := I) (M := M)
        g r s i α P₀ y * ψ y ∂(volume : Measure EuclN) with hPRC_def
  set LOV : ℝ := ∫ y, densityOnEuclid (I := I) g α y *
      covLowerOrderRotationValueCoeffLimit (I := I) (M := M)
        g r s i α P₀ y * ψ y ∂(volume : Measure EuclN) with hLOV_def
  set GD : ℝ := ∫ y, (∑ l : Fin (Module.finrank ℝ E),
      weightedGradCoeffDivLimit (I := I) (M := M)
        g r s i α P₀ l y) * ψ y
    ∂(volume : Measure EuclN) with hGD_def
  have hcTE_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_measurableSet (I := I) (M := M) α
  have h_per_n : ∀ n : ℕ,
      (tensorPrincipalForm (I := I) (M := M) g α
          (chartPouKernel_isCompact (I := I) (M := M) α)
          (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)).bilin
        (tensorComponentEuclid (I := I) (M := M) g r s
          (eigenvectorPouApprox (I := I) (M := M)
            g r s i α n) α P₀)
        ψ =
      ((∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor
          (pouSmul (I := I) (M := M) g r s α
            (eigenvectorRotatedTestSection (I := I) (M := M) g r s α P₀
              hψ hψ_cs hψ_supp)) x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) -
      (∫ x, tensorCovDerivCrossLeft (I := I) (M := M) g r s
          (chartAtlasPOU I M α)
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor
          (eigenvectorRotatedTestSection (I := I) (M := M) g r s α P₀
            hψ hψ_cs hψ_supp) x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) +
      ((∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          (∑ P' : TensorCompIdx (E := E) r s,
            ∑ Q : TensorCompIdx (E := E) r s,
              covChartMetricGram (I := I) (M := M) g r s α P' Q y *
                  crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y *
                ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
                  (((eigenvectorSmoothApprox (I := I) (M := M)
                      g r s i n).toCcTensor) : TensorL2 r s g)
                  α P' :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) *
          ψ y ∂(volume : Measure EuclN)) +
      ∑ l : Fin (Module.finrank ℝ E),
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
              crossRightTestGradTerm (I := I) (M := M) g r s
                (eigenvectorSmoothApprox (I := I) (M := M)
                  g r s i n).toCcTensor α P₀ l y *
            euclidPartial (E := E) l ψ y ∂(volume : Measure EuclN))) -
      (∫ y, densityOnEuclid (I := I) g α y *
          covPrincipalRotationCoeff (I := I) (M := M) g r s
            (eigenvectorPouApprox (I := I) (M := M)
              g r s i α n)
            α P₀ y * ψ y ∂(volume : Measure EuclN)) -
      (∫ y, densityOnEuclid (I := I) g α y *
          covLowerOrderRotationValueCoeff (I := I) (M := M) g r s
            (eigenvectorPouApprox (I := I) (M := M)
              g r s i α n)
            α P₀ y * ψ y ∂(volume : Measure EuclN)) +
      ∫ y, (∑ l : Fin (Module.finrank ℝ E),
          euclidPartial (E := E) l
            (weightedGradCoeff (I := I) (M := M) g r s
              (eigenvectorPouApprox (I := I) (M := M)
                g r s i α n)
              α P₀ l) y) * ψ y ∂(volume : Measure EuclN) := by
    intro n
    rw [tensorComponent_chartBilinIdentity_of_dirichlet (I := I) (M := M) g r s
      (eigenvectorPouApprox (I := I) (M := M) g r s i α n) α
      (chartPouKernel_isCompact (I := I) (M := M) α)
      (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α) P₀
      (eigenvectorPouApprox_tsupport_subset_source (I := I) (M := M)
        g r s i α n)
      (eigenvectorPouApprox_component_tsupport_subset (I := I) (M := M)
        g r s i α P₀ n) hψ hψ_cs hψ_supp]
    rw [show (∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r s
            (eigenvectorPouApprox (I := I) (M := M) g r s i α n)
            (rotatedTestSection (I := I) (M := M) g r s α P₀
              (chartTestPullback (I := I) (M := M) α ψ)
              (chartTestPullback_contMDiffOn (I := I) (M := M) α hψ)
              (chartTestPullback_tsupport_subset_source (I := I) (M := M) α
                hψ_cs hψ_supp)) x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
        ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r s
            (eigenvectorPouApprox (I := I) (M := M) g r s i α n)
            (eigenvectorRotatedTestSection (I := I) (M := M) g r s α P₀
              hψ hψ_cs hψ_supp) x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) from rfl]
    rw [eigenvectorSource_integral_split (I := I) (M := M) g r s i
      α P₀ hψ hψ_cs hψ_supp n,
      eigenvectorCrossRight_integral_eq_value_plus_grad (I := I) (M := M)
        g r s i α P₀ hψ hψ_cs hψ_supp n]
  set L : ℝ := ((1 - μ) * U - CL + (CRV + -CRGdiv) - PRC - LOV + GD) with hL_def
  have h_rhs_tendsto : Filter.Tendsto
      (fun n => ((∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M)
              g r s i n).toCcTensor
            (pouSmul (I := I) (M := M) g r s α
              (eigenvectorRotatedTestSection (I := I) (M := M) g r s α P₀
                hψ hψ_cs hψ_supp)) x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) -
        (∫ x, tensorCovDerivCrossLeft (I := I) (M := M) g r s
            (chartAtlasPOU I M α)
            (eigenvectorSmoothApprox (I := I) (M := M)
              g r s i n).toCcTensor
            (eigenvectorRotatedTestSection (I := I) (M := M) g r s α P₀
              hψ hψ_cs hψ_supp) x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) +
        ((∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            (∑ P' : TensorCompIdx (E := E) r s,
              ∑ Q : TensorCompIdx (E := E) r s,
                covChartMetricGram (I := I) (M := M) g r s α P' Q y *
                    crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y *
                  ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
                    (((eigenvectorSmoothApprox (I := I) (M := M)
                        g r s i n).toCcTensor) : TensorL2 r s g)
                    α P' :
                    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                    EuclN → ℝ) y) *
            ψ y ∂(volume : Measure EuclN)) +
        ∑ l : Fin (Module.finrank ℝ E),
          ∫ y in chartTargetEuclid (I := I) (M := M) α,
            densityOnEuclid (I := I) g α y *
                crossRightTestGradTerm (I := I) (M := M) g r s
                  (eigenvectorSmoothApprox (I := I) (M := M)
                    g r s i n).toCcTensor α P₀ l y *
              euclidPartial (E := E) l ψ y ∂(volume : Measure EuclN))) -
        (∫ y, densityOnEuclid (I := I) g α y *
            covPrincipalRotationCoeff (I := I) (M := M) g r s
              (eigenvectorPouApprox (I := I) (M := M)
                g r s i α n)
              α P₀ y * ψ y ∂(volume : Measure EuclN)) -
        (∫ y, densityOnEuclid (I := I) g α y *
            covLowerOrderRotationValueCoeff (I := I) (M := M) g r s
              (eigenvectorPouApprox (I := I) (M := M)
                g r s i α n)
              α P₀ y * ψ y ∂(volume : Measure EuclN)) +
        ∫ y, (∑ l : Fin (Module.finrank ℝ E),
            euclidPartial (E := E) l
              (weightedGradCoeff (I := I) (M := M) g r s
                (eigenvectorPouApprox (I := I) (M := M)
                  g r s i α n)
                α P₀ l) y) * ψ y ∂(volume : Measure EuclN))
      atTop (𝓝 L) := by
    rw [hL_def]
    have h_md := eigenvectorMainDir_tendsto (I := I) (M := M) g r s i
      α P₀ hψ hψ_cs hψ_supp
    refine (((((h_md.sub
      (eigenvectorCrossLeft_tendsto (I := I) (M := M) g r s i
        α P₀ hψ hψ_cs hψ_supp)).add
      ((eigenvectorCrossRight_tendsto (I := I) (M := M) g r s i
        α P₀ hψ hψ_cs hψ_supp).add
        (eigenvectorCrossRightGrad_tendsto (I := I) (M := M) g r s i
          α P₀ hψ hψ_cs hψ_supp))).sub
      (covPrincipalRotationCoeff_source_tendsto (I := I) (M := M) g r s
        i α P₀ hψ hψ_cs hψ_supp)).sub
      (covLowerOrderRotationValueCoeff_source_tendsto (I := I) (M := M)
        g r s i α P₀ hψ hψ_cs hψ_supp)).add
      (weightedGradCoeffDivSum_source_tendsto (I := I) (M := M) g r s
        i α P₀ hψ hψ_cs hψ_supp)).congr ?_
    intro n
    rfl
  have h_lhs_tendsto : Filter.Tendsto
      (fun n => (tensorPrincipalForm (I := I) (M := M) g α
          (chartPouKernel_isCompact (I := I) (M := M) α)
          (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)).bilin
        (tensorComponentEuclid (I := I) (M := M) g r s
          (eigenvectorPouApprox (I := I) (M := M)
            g r s i α n) α P₀)
        ψ)
      atTop (𝓝 (μ * P)) := by
    rw [hμ_def, hP_def]
    exact bilin_eigenvectorPouApprox_tendsto (I := I) (M := M) g r s i
      α P₀ hψ hψ_cs hψ_supp
  have h_mu_P : μ * P = L := by
    refine tendsto_nhds_unique (h_lhs_tendsto.congr ?_) h_rhs_tendsto
    intro n
    exact h_per_n n
  have h_one_div_density : ContDiffOn ℝ ∞
      (fun y => 1 / densityOnEuclid (I := I) g α y)
      (chartTargetEuclid (I := I) (M := M) α) :=
    contDiffOn_const.div (densityOnEuclid_contDiffOn (I := I) g α)
      (fun _ hy => (densityOnEuclid_pos (I := I) g α hy).ne')
  have h_rhs_integral :
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          eigenvectorChartRHS (I := I) (M := M) g r s i α P₀ y * ψ y
        ∂(volume : Measure EuclN)) =
      μ⁻¹ * (U - CL + CRV - PRC - LOV + GD - CRGdiv) := by
    have hint_U : Integrable (fun y => densityOnEuclid (I := I) g α y *
        ((tensorL2ChartComponent (I := I) (M := M) g r s φ α P₀ :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y * ψ y)
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
      density_memLp2_test_integrable (I := I) (M := M) g α
        (Lp.memLp (tensorL2ChartComponent (I := I) (M := M) g r s φ α P₀))
        hψ hψ_cs hψ_supp
    have hint_CLsum : Integrable (fun y => densityOnEuclid (I := I) g α y *
        (∑ P' : TensorCompIdx (E := E) r (s + 1),
          ∑ Q : TensorCompIdx (E := E) r (s + 1),
            covChartMetricGram (I := I) (M := M) g r (s + 1) α P' Q y *
                crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y *
              ((crossLeftLimitComponent (I := I) (M := M)
                g r s i α P' :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) *
        ψ y)
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) := by
      have h_sum : Integrable (fun y => ∑ P' : TensorCompIdx (E := E) r (s + 1),
        ∑ Q : TensorCompIdx (E := E) r (s + 1),
          densityOnEuclid (I := I) g α y *
            (covChartMetricGram (I := I) (M := M) g r (s + 1) α P' Q y *
                crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y *
              ((crossLeftLimitComponent (I := I) (M := M)
                g r s i α P' :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) *
            ψ y)
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)) :=
        MeasureTheory.integrable_finset_sum _ (fun P' _ =>
          MeasureTheory.integrable_finset_sum _ (fun Q _ =>
            crossLeftLimitPairing_integrable (I := I) (M := M) g r s i
              α P₀ P' Q hψ hψ_cs hψ_supp))
      refine h_sum.congr (Filter.Eventually.of_forall (fun y => ?_))
      simp only [Finset.mul_sum, Finset.sum_mul]
    have hint_CRVsum : Integrable (fun y => densityOnEuclid (I := I) g α y *
        (∑ P' : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            covChartMetricGram (I := I) (M := M) g r s α P' Q y *
                crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y *
              ((crossRightLimitComponent (I := I) (M := M)
                g r s i α P' :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) *
        ψ y)
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) := by
      have h_sum : Integrable (fun y => ∑ P' : TensorCompIdx (E := E) r s,
        ∑ Q : TensorCompIdx (E := E) r s,
          densityOnEuclid (I := I) g α y *
            (covChartMetricGram (I := I) (M := M) g r s α P' Q y *
                crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y *
              ((crossRightLimitComponent (I := I) (M := M)
                g r s i α P' :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) *
            ψ y)
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)) :=
        MeasureTheory.integrable_finset_sum _ (fun P' _ =>
          MeasureTheory.integrable_finset_sum _ (fun Q _ =>
            crossRightValueLimitPairing_integrable (I := I) (M := M)
              g r s i α P₀ P' Q hψ hψ_cs hψ_supp))
      refine h_sum.congr (Filter.Eventually.of_forall (fun y => ?_))
      simp only [Finset.mul_sum, Finset.sum_mul]
    have hint_PRC : Integrable (fun y => densityOnEuclid (I := I) g α y *
        covPrincipalRotationCoeffLimit (I := I) (M := M)
          g r s i α P₀ y * ψ y)
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
      density_memLp2_test_integrable (I := I) (M := M) g α
        (covPrincipalRotationCoeffLimit_memLp (I := I) (M := M)
          g r s i α P₀)
        hψ hψ_cs hψ_supp
    have hint_LOV : Integrable (fun y => densityOnEuclid (I := I) g α y *
        covLowerOrderRotationValueCoeffLimit (I := I) (M := M)
          g r s i α P₀ y * ψ y)
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
      density_memLp2_test_integrable (I := I) (M := M) g α
        (covLowerOrderRotationValueCoeffLimit_memLp (I := I) (M := M)
          g r s i α P₀)
        hψ hψ_cs hψ_supp
    have hint_GD : Integrable (fun y => densityOnEuclid (I := I) g α y *
        ((1 / densityOnEuclid (I := I) g α y) *
          ∑ l : Fin (Module.finrank ℝ E),
            weightedGradCoeffDivLimit (I := I) (M := M)
              g r s i α P₀ l y) * ψ y)
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
      density_coeff_memLp2_test_integrable (I := I) (M := M) g α
        h_one_div_density
        (memLp_finset_sum (μ := (volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α))
          (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
          (fun l _ => weightedGradCoeffDivLimit_memLp (I := I) (M := M)
            g r s i α P₀ l))
        hψ hψ_cs hψ_supp
    have hint_CRGD : Integrable (fun y => densityOnEuclid (I := I) g α y *
        ((1 / densityOnEuclid (I := I) g α y) *
          crossRightGradCoeffDivLimit (I := I) (M := M)
            g r s i α P₀ y) * ψ y)
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
      density_coeff_memLp2_test_integrable (I := I) (M := M) g α
        h_one_div_density
        (crossRightGradCoeffDivLimit_memLp (I := I) (M := M)
          g r s i α P₀)
        hψ hψ_cs hψ_supp
    have h_integrand : Set.EqOn
        (fun y => densityOnEuclid (I := I) g α y *
          eigenvectorChartRHS (I := I) (M := M) g r s i α P₀ y * ψ y)
        (fun y => μ⁻¹ *
          ((densityOnEuclid (I := I) g α y *
              ((tensorL2ChartComponent (I := I) (M := M) g r s φ α P₀ :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                EuclN → ℝ) y * ψ y) -
            densityOnEuclid (I := I) g α y *
              (∑ P' : TensorCompIdx (E := E) r (s + 1),
                ∑ Q : TensorCompIdx (E := E) r (s + 1),
                  covChartMetricGram (I := I) (M := M) g r (s + 1) α P' Q y *
                      crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y *
                    ((crossLeftLimitComponent (I := I) (M := M)
                      g r s i α P' :
                      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                      EuclN → ℝ) y) * ψ y +
            densityOnEuclid (I := I) g α y *
              (∑ P' : TensorCompIdx (E := E) r s,
                ∑ Q : TensorCompIdx (E := E) r s,
                  covChartMetricGram (I := I) (M := M) g r s α P' Q y *
                      crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y *
                    ((crossRightLimitComponent (I := I) (M := M)
                      g r s i α P' :
                      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                      EuclN → ℝ) y) * ψ y -
            densityOnEuclid (I := I) g α y *
              covPrincipalRotationCoeffLimit (I := I) (M := M)
                g r s i α P₀ y * ψ y -
            densityOnEuclid (I := I) g α y *
              covLowerOrderRotationValueCoeffLimit (I := I) (M := M)
                g r s i α P₀ y * ψ y +
            densityOnEuclid (I := I) g α y *
              ((1 / densityOnEuclid (I := I) g α y) *
                ∑ l : Fin (Module.finrank ℝ E),
                  weightedGradCoeffDivLimit (I := I) (M := M)
                    g r s i α P₀ l y) * ψ y -
            densityOnEuclid (I := I) g α y *
              ((1 / densityOnEuclid (I := I) g α y) *
                crossRightGradCoeffDivLimit (I := I) (M := M)
                  g r s i α P₀ y) * ψ y))
        (chartTargetEuclid (I := I) (M := M) α) := by
      intro y _hy
      simp only [eigenvectorChartRHS, hφ_def]
      ring
    rw [MeasureTheory.setIntegral_congr_fun hcTE_meas h_integrand]
    rw [MeasureTheory.integral_const_mul]
    congr 1
    have hψ_zero : ∀ y, y ∉ chartTargetEuclid (I := I) (M := M) α → ψ y = 0 :=
      fun y hy => image_eq_zero_of_notMem_tsupport (fun h => hy (hψ_supp h))
    have hD4 : (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            covPrincipalRotationCoeffLimit (I := I) (M := M)
              g r s i α P₀ y * ψ y ∂(volume : Measure EuclN)) = PRC := by
      rw [hPRC_def]
      exact MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun y hy => by rw [hψ_zero y hy, mul_zero])
    have hD5 : (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            covLowerOrderRotationValueCoeffLimit (I := I) (M := M)
              g r s i α P₀ y * ψ y ∂(volume : Measure EuclN)) = LOV := by
      rw [hLOV_def]
      exact MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun y hy => by rw [hψ_zero y hy, mul_zero])
    have hD6 : (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            ((1 / densityOnEuclid (I := I) g α y) *
              ∑ l : Fin (Module.finrank ℝ E),
                weightedGradCoeffDivLimit (I := I) (M := M)
                  g r s i α P₀ l y) * ψ y
          ∂(volume : Measure EuclN)) = GD := by
      rw [hGD_def]
      rw [show (∫ y, (∑ l : Fin (Module.finrank ℝ E),
              weightedGradCoeffDivLimit (I := I) (M := M)
                g r s i α P₀ l y) * ψ y ∂(volume : Measure EuclN)) =
          ∫ y in chartTargetEuclid (I := I) (M := M) α,
            (∑ l : Fin (Module.finrank ℝ E),
              weightedGradCoeffDivLimit (I := I) (M := M)
                g r s i α P₀ l y) * ψ y ∂(volume : Measure EuclN)
        from (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
          (fun y hy => by rw [hψ_zero y hy, mul_zero])).symm]
      refine MeasureTheory.setIntegral_congr_fun hcTE_meas (fun y hy => ?_)
      rw [show densityOnEuclid (I := I) g α y *
            ((1 / densityOnEuclid (I := I) g α y) *
              ∑ l : Fin (Module.finrank ℝ E),
                weightedGradCoeffDivLimit (I := I) (M := M)
                  g r s i α P₀ l y) * ψ y =
          (densityOnEuclid (I := I) g α y *
              (1 / densityOnEuclid (I := I) g α y)) *
            ((∑ l : Fin (Module.finrank ℝ E),
              weightedGradCoeffDivLimit (I := I) (M := M)
                g r s i α P₀ l y) * ψ y) from by ring]
      rw [mul_one_div, div_self (densityOnEuclid_pos (I := I) g α hy).ne',
        one_mul]
    have hD7 : (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            ((1 / densityOnEuclid (I := I) g α y) *
              crossRightGradCoeffDivLimit (I := I) (M := M)
                g r s i α P₀ y) * ψ y
          ∂(volume : Measure EuclN)) = CRGdiv := by
      rw [hCRGdiv_def]
      refine MeasureTheory.setIntegral_congr_fun hcTE_meas (fun y hy => ?_)
      rw [show densityOnEuclid (I := I) g α y *
            ((1 / densityOnEuclid (I := I) g α y) *
              crossRightGradCoeffDivLimit (I := I) (M := M)
                g r s i α P₀ y) * ψ y =
          (densityOnEuclid (I := I) g α y *
              (1 / densityOnEuclid (I := I) g α y)) *
            (crossRightGradCoeffDivLimit (I := I) (M := M)
              g r s i α P₀ y * ψ y) from by ring]
      rw [mul_one_div, div_self (densityOnEuclid_pos (I := I) g α hy).ne',
        one_mul]
    set fU : EuclN → ℝ := fun y => densityOnEuclid (I := I) g α y *
      ((tensorL2ChartComponent (I := I) (M := M) g r s φ α P₀ :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y * ψ y
      with hfU_def
    set fCL : EuclN → ℝ := fun y => densityOnEuclid (I := I) g α y *
      (∑ P' : TensorCompIdx (E := E) r (s + 1),
        ∑ Q : TensorCompIdx (E := E) r (s + 1),
          covChartMetricGram (I := I) (M := M) g r (s + 1) α P' Q y *
              crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y *
            ((crossLeftLimitComponent (I := I) (M := M)
              g r s i α P' :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) * ψ y
      with hfCL_def
    set fCRV : EuclN → ℝ := fun y => densityOnEuclid (I := I) g α y *
      (∑ P' : TensorCompIdx (E := E) r s,
        ∑ Q : TensorCompIdx (E := E) r s,
          covChartMetricGram (I := I) (M := M) g r s α P' Q y *
              crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y *
            ((crossRightLimitComponent (I := I) (M := M)
              g r s i α P' :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) * ψ y
      with hfCRV_def
    set fPRC : EuclN → ℝ := fun y => densityOnEuclid (I := I) g α y *
      covPrincipalRotationCoeffLimit (I := I) (M := M)
        g r s i α P₀ y * ψ y with hfPRC_def
    set fLOV : EuclN → ℝ := fun y => densityOnEuclid (I := I) g α y *
      covLowerOrderRotationValueCoeffLimit (I := I) (M := M)
        g r s i α P₀ y * ψ y with hfLOV_def
    set fGD : EuclN → ℝ := fun y => densityOnEuclid (I := I) g α y *
      ((1 / densityOnEuclid (I := I) g α y) *
        ∑ l : Fin (Module.finrank ℝ E),
          weightedGradCoeffDivLimit (I := I) (M := M)
            g r s i α P₀ l y) * ψ y with hfGD_def
    set fCRGD : EuclN → ℝ := fun y => densityOnEuclid (I := I) g α y *
      ((1 / densityOnEuclid (I := I) g α y) *
        crossRightGradCoeffDivLimit (I := I) (M := M)
          g r s i α P₀ y) * ψ y with hfCRGD_def
    have e1 : (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (fU y - fCL y + fCRV y - fPRC y - fLOV y + fGD y - fCRGD y)
          ∂(volume : Measure EuclN)) =
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (fU y - fCL y + fCRV y - fPRC y - fLOV y + fGD y)
          ∂(volume : Measure EuclN)) -
        ∫ y in chartTargetEuclid (I := I) (M := M) α, fCRGD y
          ∂(volume : Measure EuclN) :=
      MeasureTheory.integral_sub
        (((((hint_U.sub hint_CLsum).add hint_CRVsum).sub hint_PRC).sub
          hint_LOV).add hint_GD) hint_CRGD
    have e2 : (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (fU y - fCL y + fCRV y - fPRC y - fLOV y + fGD y)
          ∂(volume : Measure EuclN)) =
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (fU y - fCL y + fCRV y - fPRC y - fLOV y)
          ∂(volume : Measure EuclN)) +
        ∫ y in chartTargetEuclid (I := I) (M := M) α, fGD y
          ∂(volume : Measure EuclN) :=
      MeasureTheory.integral_add
        ((((hint_U.sub hint_CLsum).add hint_CRVsum).sub hint_PRC).sub hint_LOV)
        hint_GD
    have e3 : (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (fU y - fCL y + fCRV y - fPRC y - fLOV y)
          ∂(volume : Measure EuclN)) =
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (fU y - fCL y + fCRV y - fPRC y)
          ∂(volume : Measure EuclN)) -
        ∫ y in chartTargetEuclid (I := I) (M := M) α, fLOV y
          ∂(volume : Measure EuclN) :=
      MeasureTheory.integral_sub
        (((hint_U.sub hint_CLsum).add hint_CRVsum).sub hint_PRC) hint_LOV
    have e4 : (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (fU y - fCL y + fCRV y - fPRC y)
          ∂(volume : Measure EuclN)) =
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (fU y - fCL y + fCRV y)
          ∂(volume : Measure EuclN)) -
        ∫ y in chartTargetEuclid (I := I) (M := M) α, fPRC y
          ∂(volume : Measure EuclN) :=
      MeasureTheory.integral_sub
        ((hint_U.sub hint_CLsum).add hint_CRVsum) hint_PRC
    have e5 : (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (fU y - fCL y + fCRV y)
          ∂(volume : Measure EuclN)) =
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (fU y - fCL y)
          ∂(volume : Measure EuclN)) +
        ∫ y in chartTargetEuclid (I := I) (M := M) α, fCRV y
          ∂(volume : Measure EuclN) :=
      MeasureTheory.integral_add (hint_U.sub hint_CLsum) hint_CRVsum
    have e6 : (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (fU y - fCL y)
          ∂(volume : Measure EuclN)) =
        (∫ y in chartTargetEuclid (I := I) (M := M) α, fU y
          ∂(volume : Measure EuclN)) -
        ∫ y in chartTargetEuclid (I := I) (M := M) α, fCL y
          ∂(volume : Measure EuclN) :=
      MeasureTheory.integral_sub hint_U hint_CLsum
    rw [e1, e2, e3, e4, e5, e6, ← hU_def, ← hCL_def, ← hCRV_def,
      hD4, hD5, hD6, hD7]
  rw [hP_def, hU_def, h_rhs_integral, ← hU_def]
  rw [show U - CL + CRV - PRC - LOV + GD - CRGdiv =
      L + μ * U from by rw [hL_def]; ring]
  rw [← h_mu_P]
  rw [show μ⁻¹ * (μ * P + μ * U) = P + U from by
    rw [mul_add, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hμ_ne, one_mul,
      one_mul]]

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in

def eigenvectorTensorChartBilinearData
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    TensorChartBilinearH1ComplData (I := I) (M := M) g r s α P₀ :=
  ⟨{ u_chart := fun y =>
        ((tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M)
              g r s) i) α P₀ :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
     f_chart := eigenvectorChartRHS (I := I) (M := M) g r s i α P₀
     weak_partial := eigenvectorChartWeakPartial (I := I) (M := M)
       g r s i α P₀
     u_chart_memLp_weighted :=
       tensorL2ChartComponent_memLp_weighted (I := I) (M := M) g r s
         (tensorResolventEigenbasisVec (I := I) (M := M)
           (tensorResolventL2_isCompactOperator (I := I) (M := M)
             g r s) i) α P₀
     f_chart_memLp_weighted :=
       eigenvectorChartRHS_memLp_weighted (I := I) (M := M)
         g r s i α P₀
     weak_partial_locally_memLp := fun k _K hK hK_in =>
       eigenvectorChartWeakPartial_locally_memLp (I := I) (M := M)
         g r s i α P₀ k hK hK_in
     weak_partial_isWeakPartial := fun k =>
       eigenvectorChartWeakPartial_hasWeakPartialDeriv (I := I) (M := M)
         g r s i α P₀ k
     variational_identity := fun _ψ hψ hψ_cs hψ_supp =>
       eigenvectorChartVariationalIdentity (I := I) (M := M)
         g r s i α P₀ hψ hψ_cs hψ_supp }⟩

section ElaborationTests

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (i : TensorEigenIdx (I := I) (M := M) g r s)

end ElaborationTests

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
