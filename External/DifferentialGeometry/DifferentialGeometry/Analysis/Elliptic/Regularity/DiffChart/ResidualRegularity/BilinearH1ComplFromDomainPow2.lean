import DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.ResidualRegularity.BilinearH1ComplFromDomainPow
import DifferentialGeometry.Analysis.Elliptic.Regularity.GradInner.CLM.Leibniz
import DifferentialGeometry.Analysis.Elliptic.Regularity.LaplacianDomain.PerChart
import DifferentialGeometry.Analysis.Elliptic.Regularity.LaplacianDomain.SmoothMulH1Compl
import DifferentialGeometry.Analysis.Sobolev.Chart.SmoothDensity.SmoothMul

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace DiffChartBilinearH1Compl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.ChartPushedWeakPartialOnVolume
open DifferentialGeometry.Analysis.Laplacian.H1ComplGradientH1LipschitzBound
open DifferentialGeometry.Analysis.Laplacian.H1ComplWeakPartialLimit
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainChartData
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainVariationalIdentityIntegralForm
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPerChartWitness
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

theorem memWkpChart_two_two_smooth_mul_laplacianDomain
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g 2 2
      (fun x : M => (φ : M → ℝ) x *
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x) := by
  have h_uh := (laplacianDomain_memWkpChart_two_unconditional
    (I := I) (M := M) g hu_h).1
  exact DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart_smooth_mul
    (I := I) (M := M) g (by norm_num : (1 : ℝ≥0∞) ≤ 2) φ h_uh

theorem memWkpChart_two_two_smoothMulLp_laplacianDomain_coeFn
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g 2 2
      ((smoothMulLp (I := I) (M := M) g φ
        (H1ComplToLp (I := I) (M := M) g u_h) :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) := by
  classical
  have h_phase3 := smoothMulH1Compl_mem_laplacianDomain
    (I := I) (M := M) g φ hu_h
  have h_cstep := (laplacianDomain_memWkpChart_two_unconditional
    (I := I) (M := M) g h_phase3).1
  have h_phase2 := H1ComplToLp_smoothMulH1Compl (I := I) (M := M) g φ u_h
  rw [h_phase2] at h_cstep
  exact h_cstep

theorem memWkpChart_two_two_smoothMulLp_preimage_coeFn
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g 2 2
      ((smoothMulLp (I := I) (M := M) g φ
        (laplacianDomain.preimage (I := I) (M := M) g
          ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h⟩) :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) := by
  classical
  obtain ⟨w_h, hw_h_dom, hw_h_eq⟩ :=
    laplacianDomainPow_two_preimage_eq (I := I) (M := M) g hu_h
  have h_phase3 := smoothMulH1Compl_mem_laplacianDomain
    (I := I) (M := M) g φ hw_h_dom
  have h_cstep := (laplacianDomain_memWkpChart_two_unconditional
    (I := I) (M := M) g h_phase3).1
  have h_phase2 := H1ComplToLp_smoothMulH1Compl (I := I) (M := M) g φ w_h
  rw [h_phase2, hw_h_eq] at h_cstep
  exact h_cstep

noncomputable def diffChartBilinearH1ComplData_of_laplacianDomainPow_two_unconditional
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (direction : Fin (Module.finrank ℝ E))
    (h_residual_memW1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (fChartResidual (I := I) (M := M) g α u_h)
      (chartTargetEuclid (I := I) (M := M) α))
    (h_identity :
      ∀ ψ : EuclN → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α →
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                (chosenSecondPartialChartPushedU
                  (I := I) (M := M) g α u_h i direction) y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN)) +
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
              (laplacianDomainPow_succ_subset_laplacianDomain
                (I := I) (M := M) g 1 hu_h)).weak_partial direction y * ψ y
          ∂(volume : Measure EuclN)) =
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            chosenFChartDeriv (I := I) (M := M) g α hu_h direction y * ψ y
          ∂(volume : Measure EuclN)) -
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramDerivOnEuclid (I := I) g α i j direction y *
                (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
                  (laplacianDomainPow_succ_subset_laplacianDomain
                    (I := I) (M := M) g 1 hu_h)).weak_partial i y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN)) -
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityDerivOnEuclid (I := I) g α direction y *
            (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
              (laplacianDomainPow_succ_subset_laplacianDomain
                (I := I) (M := M) g 1 hu_h)).u_chart y * ψ y
          ∂(volume : Measure EuclN)) +
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityDerivOnEuclid (I := I) g α direction y *
            (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
              (laplacianDomainPow_succ_subset_laplacianDomain
                (I := I) (M := M) g 1 hu_h)).f_chart y * ψ y
          ∂(volume : Measure EuclN))) :
    DiffChartBilinearH1ComplData (I := I) (M := M) g α :=
  diffChartBilinearH1ComplData_of_laplacianDomainPow_two_via_residual
    (I := I) (M := M) g α hu_h direction h_residual_memW1p h_identity

end DiffChartBilinearH1Compl
end Laplacian
end Analysis
end DifferentialGeometry

end
