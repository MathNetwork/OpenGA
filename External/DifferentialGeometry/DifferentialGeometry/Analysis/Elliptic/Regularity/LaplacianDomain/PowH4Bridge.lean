import DifferentialGeometry.Analysis.Elliptic.Regularity.LaplacianDomain.PowH4
import DifferentialGeometry.Analysis.Elliptic.Regularity.ChartHk.H4NonSmooth
import DifferentialGeometry.Analysis.Elliptic.Regularity.LaplacianDomain.ChartData

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace LaplacianDomainPowH4Bridge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.Chart

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompactSpace M] in
theorem chartH4NonSmoothPOUWitness_of_memWkp_four
    (g : SmoothRiemannianMetric I M) {u : M → ℝ} {α : M}
    (h : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 4 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
        (chartAtlasPOU I M) α u)
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α)) :
    ChartH4NonSmoothPOUWitness (I := I) (M := M) g u α :=
  ChartH4NonSmoothPOUWitness.mk' (g := g) h

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompactSpace M] in
theorem chartH4NonSmoothPOUWitness_iff_memWkp_four
    (g : SmoothRiemannianMetric I M) (u : M → ℝ) (α : M) :
    ChartH4NonSmoothPOUWitness (I := I) (M := M) g u α ↔
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 4 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
        (chartAtlasPOU I M) α u)
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) :=
  ⟨fun h => h.memWkp_four,
   fun h => chartH4NonSmoothPOUWitness_of_memWkp_four g (u := u) (α := α) h⟩

def ChartSideH4Bridge (_g : SmoothRiemannianMetric I M) (u : M → ℝ) : Prop :=
  ∀ α : M,
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 4 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
        (chartAtlasPOU I M) α u)
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompactSpace M] in
theorem chartH4NonSmoothPOUWitness_of_chartSideH4Bridge
    (g : SmoothRiemannianMetric I M) {u : M → ℝ}
    (h_bridge : ChartSideH4Bridge (I := I) (M := M) g u) :
    ∀ α : M, ChartH4NonSmoothPOUWitness (I := I) (M := M) g u α :=
  fun α => chartH4NonSmoothPOUWitness_of_memWkp_four g (u := u) (α := α)
    (h_bridge α)

omit [NeZero (Module.finrank ℝ E)] in
theorem laplacianDomainPow_memWkpChart_four_of_chartSideH4Bridge
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_bridge : ChartSideH4Bridge (I := I) (M := M) g
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g 4 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) ∧
    DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart
      (I := I) (M := M) g 4 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) < ⊤ :=
  laplacianDomainPow_memWkpChart_four (I := I) (M := M) g hu_h
    (chartH4NonSmoothPOUWitness_of_chartSideH4Bridge g h_bridge)

omit [NeZero (Module.finrank ℝ E)] in
theorem laplacianDomainPow_memWkpChart_four_two_sided_of_chartSideBridges
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_bridge_u : ChartSideH4Bridge (I := I) (M := M) g
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)))
    (h_bridge_rhs : ChartSideH4Bridge (I := I) (M := M) g
      (((laplacianDomain.preimage (I := I) (M := M) g
          ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h⟩ :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))) :
    (DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
        (I := I) (M := M) g 4 2
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) ∧
      DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart
        (I := I) (M := M) g 4 2
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) < ⊤) ∧
    (DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
        (I := I) (M := M) g 4 2
        ((laplacianDomain.preimage (I := I) (M := M) g
            ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
              (I := I) (M := M) g 1 hu_h⟩ :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) ∧
      DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart
        (I := I) (M := M) g 4 2
        ((laplacianDomain.preimage (I := I) (M := M) g
            ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
              (I := I) (M := M) g 1 hu_h⟩ :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) < ⊤) :=
  laplacianDomainPow_memWkpChart_four_two_sided (I := I) (M := M) g hu_h
    (chartH4NonSmoothPOUWitness_of_chartSideH4Bridge g h_bridge_u)
    (chartH4NonSmoothPOUWitness_of_chartSideH4Bridge g h_bridge_rhs)

end LaplacianDomainPowH4Bridge
end Laplacian
end Analysis
end DifferentialGeometry

end
