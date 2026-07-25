import DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.ResidualRegularity.BilinearH1ComplFromDomainPow
import DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.ResidualRegularity.BilinearH1ComplViaH3
import DifferentialGeometry.Analysis.Elliptic.Regularity.ChartPushed.MemWkpThreeSmooth
import DifferentialGeometry.Analysis.Elliptic.Regularity.FChartResidual.ResidualMemW1p
import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.IteratedSobolev

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace ChosenFChartDerivMemW1p

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplH3
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainChartData

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

theorem chosenFChartDeriv_memW1p_of_base_memWkp22
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (direction : Fin (Module.finrank ℝ E))
    (h_base_f_chart_memWkp22 :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 2 2
        (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).f_chart
        (chartTargetEuclid (I := I) (M := M) α)) :
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (chosenFChartDeriv (I := I) (M := M) g α hu_h direction)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  unfold chosenFChartDeriv
  have h_step := h_base_f_chart_memWkp22.chosenWeakPartial_mem direction
  rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.one_iff_memW1p]
    at h_step
  exact h_step

theorem chosenFChartDeriv_memW1p_truly_unconditional
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (l₁ : Fin (Module.finrank ℝ E))
    (h_base_f_chart_memWkp22 :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 2 2
        (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).f_chart
        (chartTargetEuclid (I := I) (M := M) α)) :
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (chosenFChartDeriv (I := I) (M := M) g α hu_h l₁)
      (chartTargetEuclid (I := I) (M := M) α) :=
  chosenFChartDeriv_memW1p_of_base_memWkp22 (I := I) (M := M) g α hu_h l₁
    h_base_f_chart_memWkp22

theorem chosenFChartDeriv_memW1p_of_base_f_chart_memWkp22
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (l₁ : Fin (Module.finrank ℝ E))
    (h_base_f_chart_memWkp22 :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 2 2
        (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).f_chart
        (chartTargetEuclid (I := I) (M := M) α)) :
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (chosenFChartDeriv (I := I) (M := M) g α hu_h l₁)
      (chartTargetEuclid (I := I) (M := M) α) :=
  chosenFChartDeriv_memW1p_truly_unconditional (I := I) (M := M) g α hu_h l₁
    h_base_f_chart_memWkp22

end ChosenFChartDerivMemW1p
end Laplacian
end Analysis
end DifferentialGeometry

end
