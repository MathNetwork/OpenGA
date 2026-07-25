import DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.Bootstrap.H2RegularitySuccessor
import DifferentialGeometry.Analysis.Elliptic.Regularity.ManifoldH2.NonSmooth
import DifferentialGeometry.Analysis.Sobolev.Chart.SmoothDensity.SmoothMul


noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian

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

structure ChartH4NonSmoothPOUWitness
    (g : SmoothRiemannianMetric I M) (u : M → ℝ) (α : M) : Prop where

  memWkp_four : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
    (d := Module.finrank ℝ E) 4 2
    (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
      (chartAtlasPOU I M) α u)
    (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
      (I := I) (M := M) α)

namespace ChartH4NonSmoothPOUWitness

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompactSpace M] in
theorem mk' {g : SmoothRiemannianMetric I M} {u : M → ℝ} {α : M}
    (h : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 4 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
        (chartAtlasPOU I M) α u)
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α)) :
    ChartH4NonSmoothPOUWitness (I := I) (M := M) g u α :=
  ⟨h⟩

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompactSpace M] in
theorem memWkp_four_eq {g : SmoothRiemannianMetric I M} {u : M → ℝ} {α : M}
    (h : ChartH4NonSmoothPOUWitness (I := I) (M := M) g u α) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 4 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
        (chartAtlasPOU I M) α u)
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) :=
  h.memWkp_four

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompactSpace M] in
theorem memWkp_three {g : SmoothRiemannianMetric I M} {u : M → ℝ} {α : M}
    (h : ChartH4NonSmoothPOUWitness (I := I) (M := M) g u α) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 3 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
        (chartAtlasPOU I M) α u)
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) :=
  DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.le_succ h.memWkp_four

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompactSpace M] in
theorem memWkp_two {g : SmoothRiemannianMetric I M} {u : M → ℝ} {α : M}
    (h : ChartH4NonSmoothPOUWitness (I := I) (M := M) g u α) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 2 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
        (chartAtlasPOU I M) α u)
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) :=
  DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.le_of_le
    (by norm_num : (2 : ℕ) ≤ 4) h.memWkp_four

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompactSpace M] in
theorem memWkp_one {g : SmoothRiemannianMetric I M} {u : M → ℝ} {α : M}
    (h : ChartH4NonSmoothPOUWitness (I := I) (M := M) g u α) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 1 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
        (chartAtlasPOU I M) α u)
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) :=
  DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.le_of_le
    (by norm_num : (1 : ℕ) ≤ 4) h.memWkp_four

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompactSpace M] in
theorem memLp_two {g : SmoothRiemannianMetric I M} {u : M → ℝ} {α : M}
    (h : ChartH4NonSmoothPOUWitness (I := I) (M := M) g u α) :
    MemLp
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
        (chartAtlasPOU I M) α u) 2
      ((volume : Measure EuclN).restrict
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α)) :=
  DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.memLp h.memWkp_four

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem toH2 {g : SmoothRiemannianMetric I M} {u : M → ℝ} {α : M}
    (h : ChartH4NonSmoothPOUWitness (I := I) (M := M) g u α) :
    DifferentialGeometry.Analysis.Laplacian.ManifoldH2NonSmooth.ChartH2NonSmoothPOUWitness
      (I := I) (M := M) g u α :=
  ⟨h.memWkp_two⟩

end ChartH4NonSmoothPOUWitness

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem memWkpChart_four_of_chartPOUWitnesses
    (g : SmoothRiemannianMetric I M) {u : M → ℝ}
    (h_witness : ∀ α : M, ChartH4NonSmoothPOUWitness (I := I) (M := M) g u α) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g 4 2 u := by
  intro α
  exact (h_witness α).memWkp_four

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem memWkpChart_three_of_chartPOUWitnesses
    (g : SmoothRiemannianMetric I M) {u : M → ℝ}
    (h_witness : ∀ α : M, ChartH4NonSmoothPOUWitness (I := I) (M := M) g u α) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g 3 2 u :=
  (memWkpChart_four_of_chartPOUWitnesses (I := I) (M := M) g h_witness).le_succ

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem memWkpChart_two_of_chartH4POUWitnesses
    (g : SmoothRiemannianMetric I M) {u : M → ℝ}
    (h_witness : ∀ α : M, ChartH4NonSmoothPOUWitness (I := I) (M := M) g u α) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g 2 2 u :=
  DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart.le_of_le
    (by norm_num : (2 : ℕ) ≤ 4)
    (memWkpChart_four_of_chartPOUWitnesses (I := I) (M := M) g h_witness)

omit [NeZero (Module.finrank ℝ E)] in
theorem wkpNormChart_four_lt_top_of_chartPOUWitnesses
    (g : SmoothRiemannianMetric I M) {u : M → ℝ}
    (h_witness : ∀ α : M, ChartH4NonSmoothPOUWitness (I := I) (M := M) g u α) :
    DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart
      (I := I) (M := M) g 4 2 u < ⊤ :=
  DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart_lt_top_of_memWkpChart
    (I := I) (M := M) g (k := 4) (p := 2) (by norm_num)
    (memWkpChart_four_of_chartPOUWitnesses (I := I) (M := M) g h_witness)

omit [NeZero (Module.finrank ℝ E)] in
theorem laplacianDomainPow_memWkpChart_four
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_witness : ∀ α : M, ChartH4NonSmoothPOUWitness (I := I) (M := M) g
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) α) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g 4 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) ∧
    DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart
      (I := I) (M := M) g 4 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) < ⊤ := by
  let _ := hu_h
  refine ⟨?_, ?_⟩
  · exact memWkpChart_four_of_chartPOUWitnesses (I := I) (M := M) g h_witness
  · exact wkpNormChart_four_lt_top_of_chartPOUWitnesses
      (I := I) (M := M) g h_witness

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_laplacianDomainPow_memWkpChart_four
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_witness : ∀ α : M, ChartH4NonSmoothPOUWitness (I := I) (M := M) g
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) α) :
    ∃ u : M → ℝ,
      u = ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) ∧
      DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
        (I := I) (M := M) g 4 2 u ∧
      DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart
        (I := I) (M := M) g 4 2 u < ⊤ := by
  refine ⟨((H1ComplToLp (I := I) (M := M) g u_h :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ), rfl, ?_, ?_⟩
  · exact (laplacianDomainPow_memWkpChart_four (I := I) (M := M) g hu_h h_witness).1
  · exact (laplacianDomainPow_memWkpChart_four (I := I) (M := M) g hu_h h_witness).2

omit [NeZero (Module.finrank ℝ E)] in
theorem laplacianDomainPow_memWkpChart_four_two_sided
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_witness_u : ∀ α : M, ChartH4NonSmoothPOUWitness (I := I) (M := M) g
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) α)
    (h_witness_rhs : ∀ α : M, ChartH4NonSmoothPOUWitness (I := I) (M := M) g
      (((laplacianDomain.preimage (I := I) (M := M) g
          ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h⟩ :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) α) :
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
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) < ⊤) := by
  refine ⟨laplacianDomainPow_memWkpChart_four (I := I) (M := M) g hu_h h_witness_u, ?_⟩
  refine ⟨memWkpChart_four_of_chartPOUWitnesses (I := I) (M := M) g h_witness_rhs, ?_⟩
  exact wkpNormChart_four_lt_top_of_chartPOUWitnesses (I := I) (M := M) g h_witness_rhs

omit [NeZero (Module.finrank ℝ E)] in
theorem memWkpChart_two_of_h4_witnesses_laplacianDomainPow_two
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_witness : ∀ α : M, ChartH4NonSmoothPOUWitness (I := I) (M := M) g
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) α) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g 2 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) := by
  let _ := hu_h
  exact memWkpChart_two_of_chartH4POUWitnesses
    (I := I) (M := M) g h_witness

theorem laplacianDomainPow_two_h2_via_h4_witnesses
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (_h_witness : ∀ α : M, ChartH4NonSmoothPOUWitness (I := I) (M := M) g
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) α) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g 2 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) := by
  exact (laplacianDomainPow_two_h2_plus_rhs_h2
    (I := I) (M := M) g hu_h).1.1

end Laplacian
end Analysis
end DifferentialGeometry

end
