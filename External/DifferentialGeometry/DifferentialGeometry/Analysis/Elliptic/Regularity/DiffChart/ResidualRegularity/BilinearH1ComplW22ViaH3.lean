import DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.ResidualRegularity.BilinearH1ComplViaH3


noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace DiffChartBilinearH1ComplH3Direct

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.ChartPushedWeakPartialOnVolume
open DifferentialGeometry.Analysis.Laplacian.H1ComplGradientH1LipschitzBound
open DifferentialGeometry.Analysis.Laplacian.H1ComplWeakPartialLimit
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainChartData
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplH3
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] in
theorem chartPushedChosenFirstPartial_memWkp_two_of_memWkp_three
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (h_chartPushed_memWkp32 :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 3 2
        (chartPushed (I := I) (M := M)
          (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
        (chartTargetEuclid (I := I) (M := M) α))
    (l₁ : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 2 2
      (chartPushedChosenFirstPartial (I := I) (M := M) g α u_h l₁)
      (chartTargetEuclid (I := I) (M := M) α) := by
  exact h_chartPushed_memWkp32.chosenWeakPartial_mem l₁

theorem diffChartBilinearH1Compl_u_chart_deriv_memWkp_two
    (g : SmoothRiemannianMetric I M) (α : M)
    (l₁ : Fin (Module.finrank ℝ E))
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_base_f_chart_memW1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
        (laplacianDomainPow_succ_subset_laplacianDomain
          (I := I) (M := M) g 1 hu_h)).f_chart
      (chartTargetEuclid (I := I) (M := M) α))
    (h_once_identity :
      ∀ ψ : EuclN → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α →
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                (chosenSecondPartialChartPushedU
                  (I := I) (M := M) g α u_h i l₁) y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN)) +
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
              (laplacianDomainPow_succ_subset_laplacianDomain
                (I := I) (M := M) g 1 hu_h)).weak_partial l₁ y * ψ y
          ∂(volume : Measure EuclN)) =
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            chosenFChartDeriv (I := I) (M := M) g α hu_h l₁ y * ψ y
          ∂(volume : Measure EuclN)) -
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramDerivOnEuclid (I := I) g α i j l₁ y *
                (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
                  (laplacianDomainPow_succ_subset_laplacianDomain
                    (I := I) (M := M) g 1 hu_h)).weak_partial i y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN)) -
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityDerivOnEuclid (I := I) g α l₁ y *
            (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
              (laplacianDomainPow_succ_subset_laplacianDomain
                (I := I) (M := M) g 1 hu_h)).u_chart y * ψ y
          ∂(volume : Measure EuclN)) +
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityDerivOnEuclid (I := I) g α l₁ y *
            (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
              (laplacianDomainPow_succ_subset_laplacianDomain
                (I := I) (M := M) g 1 hu_h)).f_chart y * ψ y
          ∂(volume : Measure EuclN)))
    (h_chartPushed_memWkp32 :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 3 2
        (chartPushed (I := I) (M := M)
          (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
        (chartTargetEuclid (I := I) (M := M) α)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 2 2
      (diffChartBilinearH1ComplData_of_laplacianDomainPow_two
        (I := I) (M := M) g α hu_h l₁
        h_base_f_chart_memW1p h_once_identity).u_chart_deriv
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  change DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
    (d := Module.finrank ℝ E) 2 2
    (((chartPushedWeakPartialLp (I := I) (M := M) g α l₁
      (chartPushedPartialLipschitz_canonical (I := I) (M := M) g α l₁) u_h
     ) : EuclN → ℝ))
    (chartTargetEuclid (I := I) (M := M) α)
  have h_chosenFirst_memWkp_two :=
    chartPushedChosenFirstPartial_memWkp_two_of_memWkp_three
      (I := I) (M := M) g α h_chartPushed_memWkp32 l₁
  have h_ae := chartPushedWeakPartialLp_ae_eq_chosenFirstPartial_on_chartTarget
    (I := I) (M := M) g α hu_h l₁
  exact (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_congr_ae
    (k := 2) (p := 2) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    (chartTargetEuclid_isOpen (I := I) (M := M) α) h_ae.symm).mp
    h_chosenFirst_memWkp_two

end DiffChartBilinearH1ComplH3Direct
end Laplacian
end Analysis
end DifferentialGeometry

end
