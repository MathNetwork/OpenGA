import DifferentialGeometry.Analysis.Elliptic.Regularity.ManifoldH2.NonSmooth
import DifferentialGeometry.Analysis.Elliptic.Regularity.LaplacianDomain.ChartData
import DifferentialGeometry.Analysis.Sobolev.Nirenberg.SubstitutionIdentity.ChartBilinearVariationalIdentity

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace LaplacianDomainH2FromSmooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Laplacian.ChartLocalLaplacian
open DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainChartData
open DifferentialGeometry.Analysis.Laplacian.ManifoldH2NonSmooth
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
open DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [NeZero (Module.finrank ℝ E)] in
theorem laplacianDomain_memWkpChart_two
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (h_witness : ∀ α : M, ChartH2NonSmoothPOUWitness (I := I) (M := M) g
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) α) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g 2 2
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) ∧
    DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart
      (I := I) (M := M) g 2 2
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) < ⊤ := by
  change DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
    (I := I) (M := M) g 2 2
    (laplacianDomain.lpRep (I := I) (M := M) g u_h) ∧
    DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart
      (I := I) (M := M) g 2 2
      (laplacianDomain.lpRep (I := I) (M := M) g u_h) < ⊤
  have h_witness' : ∀ α : M, ChartH2NonSmoothPOUWitness (I := I) (M := M) g
      (laplacianDomain.lpRep (I := I) (M := M) g u_h) α := h_witness
  exact memWkpChart_two_of_laplacianDomain_canonical (I := I) (M := M) g u_h hu_h h_witness'

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_laplacianDomain_memWkpChart_two
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (h_witness : ∀ α : M, ChartH2NonSmoothPOUWitness (I := I) (M := M) g
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) α) :
    ∃ u : M → ℝ,
      u = ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) ∧
      DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
        (I := I) (M := M) g 2 2 u ∧
      DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart
        (I := I) (M := M) g 2 2 u < ⊤ := by
  refine ⟨((H1ComplToLp (I := I) (M := M) g u_h :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ), rfl, ?_, ?_⟩
  · exact (laplacianDomain_memWkpChart_two (I := I) (M := M) g hu_h h_witness).1
  · exact (laplacianDomain_memWkpChart_two (I := I) (M := M) g hu_h h_witness).2

omit [NeZero (Module.finrank ℝ E)] in
theorem laplacianDomain_memWkpChart_two_bridgeData
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (h_bridge : ∀ α : M, ChartH2NonSmoothBridgeData (I := I) (M := M) g
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) α) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g 2 2
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) ∧
    DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart
      (I := I) (M := M) g 2 2
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) < ⊤ := by
  exact memWkpChart_two_of_laplacianDomain_bridgeData (I := I) (M := M) g u_h hu_h
    (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) h_bridge

omit [NeZero (Module.finrank ℝ E)] in
theorem laplacianDomain_memWkpChart_one
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (h_witness : ∀ α : M, ChartH2NonSmoothPOUWitness (I := I) (M := M) g
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) α) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g 1 2
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) :=
  (laplacianDomain_memWkpChart_two (I := I) (M := M) g hu_h h_witness).1.le_succ

end LaplacianDomainH2FromSmooth
end Laplacian
end Analysis
end DifferentialGeometry
