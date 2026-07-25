import DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.BaseFChart.MemWkpTwoTwo
import DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.ResidualRegularity.ChosenFChartDerivMemW1p
import DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.TwiceDifferentiated.VariationalIdentity
import DifferentialGeometry.Analysis.Elliptic.Regularity.ChartPushed.MemWkpFourSmooth
import DifferentialGeometry.Analysis.Elliptic.Regularity.LaplacianDomain.PowH2kBridge
import DifferentialGeometry.Analysis.Elliptic.Regularity.LaplacianDomain.PowH4Bridge

noncomputable section

open Bundle Manifold MeasureTheory Set Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace ChartPushedMemWkpFour

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.ChosenThirdMixedPartialChartPushed
open DifferentialGeometry.Analysis.Laplacian.FChartEffTwiceDef
open DifferentialGeometry.Analysis.Laplacian.BaseFChartMemW22
open DifferentialGeometry.Analysis.Laplacian.ChosenFChartDerivMemW1p
open DifferentialGeometry.Analysis.Laplacian.TwiceDifferentiatedVariationalIdentity
open DifferentialGeometry.Analysis.Laplacian.ChartPushedMemWkpFourSmooth
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private lemma twice_diff_identities_at
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    ∀ l₁ l₂ : Fin (Module.finrank ℝ E),
      ∀ ψ : EuclN → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α →
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                chosenThirdMixedPartialChartPushedU
                  (I := I) (M := M) g α u_h i l₁ l₂ y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN))
        + (∫ y in chartTargetEuclid (I := I) (M := M) α,
            densityOnEuclid (I := I) g α y *
              chosenSecondPartialChartPushedU
                (I := I) (M := M) g α u_h l₁ l₂ y * ψ y
            ∂(volume : Measure EuclN)) =
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            effectiveSourceChartSecondOrder (I := I) (M := M) g α l₁ l₂ hu_h y * ψ y
          ∂(volume : Measure EuclN) := by
  intro l₁ l₂ ψ hψ_smooth hψ_cs hψ_supp
  have h_base_f_chart_memWkp22 :=
    base_f_chart_memWkp_two_two
      (I := I) (M := M) g α hu_h
  have h_chosenFChartDeriv_memW1p :=
    chosenFChartDeriv_memW1p_truly_unconditional
      (I := I) (M := M) g α hu_h l₁ h_base_f_chart_memWkp22
  exact twice_differentiated_variational_identity_holds
    (I := I) (M := M) g α hu_h l₁ l₂ h_chosenFChartDeriv_memW1p
    hψ_smooth hψ_cs hψ_supp

theorem chartPushed_memWkp_four_two_of_laplacianDomainPow_two
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 4 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
        (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) :=
  chartPushed_memWkp_four_two_of_laplacianDomainPow_two_of_twice_diff_identities
    (I := I) (M := M) g α hu_h
    (twice_diff_identities_at (I := I) (M := M) g α hu_h)

theorem chartSideH2kBridge_two_of_laplacianDomainPow_two
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    ChartSideH2kBridge (I := I) (M := M) g 2
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) :=
  chartSideH2kBridge_two_of_twice_diff_identities
    (I := I) (M := M) g hu_h
    (fun α => twice_diff_identities_at (I := I) (M := M) g α hu_h)

theorem laplacianDomainPow_memWkpChart_four_two_of_laplacianDomainPow_two
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g 4 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) ∧
    DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart
      (I := I) (M := M) g 4 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) < ⊤ :=
  laplacianDomainPow_memWkpChart_four_two_of_twice_diff_identities
    (I := I) (M := M) g hu_h
    (fun α => twice_diff_identities_at (I := I) (M := M) g α hu_h)

theorem chartSideH4Bridge_of_laplacianDomainPow_two
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH4Bridge.ChartSideH4Bridge
      (I := I) (M := M) g
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) :=
  chartSideH4Bridge_of_chartSideH2kBridge_two (I := I) (M := M) g
    (chartSideH2kBridge_two_of_laplacianDomainPow_two
      (I := I) (M := M) g hu_h)

end ChartPushedMemWkpFour
end Laplacian
end Analysis
end DifferentialGeometry

end
