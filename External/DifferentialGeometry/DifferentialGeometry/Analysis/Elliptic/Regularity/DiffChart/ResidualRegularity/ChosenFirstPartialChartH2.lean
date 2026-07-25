import DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.ResidualRegularity.BilinearH1ComplW22ViaH3
import DifferentialGeometry.Analysis.Elliptic.Regularity.ChartPushed.MemWkpThree
import DifferentialGeometry.Analysis.Elliptic.Regularity.LaplacianDomain.PerChart
import DifferentialGeometry.Analysis.Elliptic.Regularity.ChartBilinear.UniformDiffQuotBoundFromDomain
import DifferentialGeometry.Analysis.Elliptic.Regularity.ChartHk.H2NonSmooth
import DifferentialGeometry.Analysis.Sobolev.Approximation.SmoothDensity
import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.IteratedSobolev


noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace ChosenFirstPartialChartH2

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
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainChartData
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplH3
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplH3Direct
open DifferentialGeometry.Analysis.Laplacian.ChartPushedMemWkpThree
open DifferentialGeometry.Analysis.Sobolev.Chart

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

noncomputable def chosenMixedSecondPartial
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g)
    (l i : Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
    (d := Module.finrank ℝ E) 2 i
    (chartPushedChosenFirstPartial (I := I) (M := M) g α u_h l)
    (chartTargetEuclid (I := I) (M := M) α)

omit [NeZero (Module.finrank ℝ E)] in
theorem target_iff_per_direction
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) (l : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 2 2
      (chartPushedChosenFirstPartial (I := I) (M := M) g α u_h l)
      (chartTargetEuclid (I := I) (M := M) α) ↔
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (chartPushedChosenFirstPartial (I := I) (M := M) g α u_h l)
      (chartTargetEuclid (I := I) (M := M) α) ∧
    ∀ i : Fin (Module.finrank ℝ E),
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
        (chosenMixedSecondPartial (I := I) (M := M) g α u_h l i)
        (chartTargetEuclid (I := I) (M := M) α) := by
  constructor
  · intro h
    rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_succ] at h
    refine ⟨h.1, ?_⟩
    intro i
    have h_step := h.2 i
    rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.one_iff_memW1p]
      at h_step
    exact h_step
  · rintro ⟨h_first, h_second⟩
    rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_succ]
    refine ⟨h_first, ?_⟩
    intro i
    rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.one_iff_memW1p]
    exact h_second i

omit [NeZero (Module.finrank ℝ E)] in
theorem chosenMixedSecondPartial_memW1p_of_chartPushed_memWkp_three
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g)
    (h_chartPushed_memWkp_three :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 3 2
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
          (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
        (chartTargetEuclid (I := I) (M := M) α))
    (l i : Fin (Module.finrank ℝ E)) :
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (chosenMixedSecondPartial (I := I) (M := M) g α u_h l i)
      (chartTargetEuclid (I := I) (M := M) α) := by
  have h_first : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 2 2
      (chartPushedChosenFirstPartial (I := I) (M := M) g α u_h l)
      (chartTargetEuclid (I := I) (M := M) α) :=
    h_chartPushed_memWkp_three.chosenWeakPartial_mem l
  have h_second := h_first.chosenWeakPartial_mem i
  rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.one_iff_memW1p]
    at h_second
  exact h_second

theorem chartPushedChosenFirstPartial_memWkp_two_of_chartPushed_memWkp_three
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_chartPushed_memWkp_three :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 3 2
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
          (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
        (chartTargetEuclid (I := I) (M := M) α))
    (l : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 2 2
      (chartPushedChosenFirstPartial (I := I) (M := M) g α u_h l)
      (chartTargetEuclid (I := I) (M := M) α) := by
  rw [target_iff_per_direction (I := I) (M := M) g α u_h l]
  refine ⟨chartPushedChosenFirstPartial_memW1p_two
    (I := I) (M := M) g α hu_h l, ?_⟩
  intro i
  exact chosenMixedSecondPartial_memW1p_of_chartPushed_memWkp_three
    (I := I) (M := M) g α u_h h_chartPushed_memWkp_three l i

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem chartPushed_chosenFirstPartial_memWkp_two_two_of_laplacianDomainPow_two_via_chartPushed_memWkp_three
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_chartPushed_memWkp_three :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 3 2
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
          (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
        (chartTargetEuclid (I := I) (M := M) α))
    (l : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 2 2
      (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) 2 l
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
          (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α))
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) := by
  change DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
    (d := Module.finrank ℝ E) 2 2
    (chartPushedChosenFirstPartial (I := I) (M := M) g α u_h l)
    (chartTargetEuclid (I := I) (M := M) α)
  exact chartPushedChosenFirstPartial_memWkp_two_of_chartPushed_memWkp_three
    (I := I) (M := M) g α hu_h h_chartPushed_memWkp_three l

end ChosenFirstPartialChartH2
end Laplacian
end Analysis
end DifferentialGeometry

end
