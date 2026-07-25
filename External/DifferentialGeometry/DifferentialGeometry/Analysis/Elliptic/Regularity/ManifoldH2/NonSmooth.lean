import DifferentialGeometry.Analysis.Elliptic.Regularity.ChartBilinear.H1Compl
import DifferentialGeometry.Analysis.Elliptic.Regularity.ChartBilinear.H1ComplFromDom
import DifferentialGeometry.Analysis.Elliptic.Regularity.ChartHk.H2NonSmooth
import DifferentialGeometry.Analysis.Elliptic.Regularity.ManifoldH2.Smooth
import DifferentialGeometry.Analysis.Elliptic.Operator.VariationalLaplacian
import DifferentialGeometry.Analysis.Sobolev.Chart.Defs
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic


noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace ManifoldH2NonSmooth

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
open DifferentialGeometry.Analysis.Laplacian.ChartH2NonSmooth
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

structure ChartH2NonSmoothPOUWitness
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (u : M → ℝ) (α : M) : Prop where

  memWkp_two : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
    (d := Module.finrank ℝ E) 2 2
    (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
      (chartAtlasPOU I M) α u)
    (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α)

namespace ChartH2NonSmoothPOUWitness

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] in
theorem mk' {g : SmoothRiemannianMetric I M} {u : M → ℝ} {α : M}
    (h : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 2 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
        (chartAtlasPOU I M) α u)
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α)) :
    ChartH2NonSmoothPOUWitness (I := I) (M := M) g u α :=
  ⟨h⟩

omit [NeZero (Module.finrank ℝ E)] in
theorem memWkp_two_eq {g : SmoothRiemannianMetric I M} {u : M → ℝ} {α : M}
    (h : ChartH2NonSmoothPOUWitness (I := I) (M := M) g u α) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 2 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
        (chartAtlasPOU I M) α u)
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α) :=
  h.memWkp_two

omit [NeZero (Module.finrank ℝ E)] in
theorem memWkp_one {g : SmoothRiemannianMetric I M} {u : M → ℝ} {α : M}
    (h : ChartH2NonSmoothPOUWitness (I := I) (M := M) g u α) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 1 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
        (chartAtlasPOU I M) α u)
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α) :=
  DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.le_succ h.memWkp_two

omit [NeZero (Module.finrank ℝ E)] in
theorem memLp_two {g : SmoothRiemannianMetric I M} {u : M → ℝ} {α : M}
    (h : ChartH2NonSmoothPOUWitness (I := I) (M := M) g u α) :
    MemLp
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
        (chartAtlasPOU I M) α u) 2
      ((volume : Measure EuclN).restrict
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α)) :=
  DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.memLp h.memWkp_two

end ChartH2NonSmoothPOUWitness

omit [NeZero (Module.finrank ℝ E)] in
theorem memWkpChart_two_of_chartPOUWitnesses
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) {u : M → ℝ}
    (h_witness : ∀ α : M, ChartH2NonSmoothPOUWitness (I := I) (M := M) g u α) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g 2 2 u := by
  intro α
  exact (h_witness α).memWkp_two

omit [NeZero (Module.finrank ℝ E)] in
theorem memWkpChart_one_of_chartPOUWitnesses
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) {u : M → ℝ}
    (h_witness : ∀ α : M, ChartH2NonSmoothPOUWitness (I := I) (M := M) g u α) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g 1 2 u :=
  (memWkpChart_two_of_chartPOUWitnesses (I := I) (M := M) g h_witness).le_succ

omit [NeZero (Module.finrank ℝ E)] in
theorem wkpNormChart_two_eq_tsum
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (u : M → ℝ) :
    DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart
      (I := I) (M := M) g 2 2 u =
      ∑' α : M,
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) 2 2
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
            (I := I) (M := M) (chartAtlasPOU I M) α u)
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α) :=
  DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart_eq_tsum
    (I := I) (M := M) g 2 2 u

omit [NeZero (Module.finrank ℝ E)] in
theorem wkpNormChart_two_lt_top_of_chartPOUWitnesses
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) {u : M → ℝ}
    (h_witness : ∀ α : M, ChartH2NonSmoothPOUWitness (I := I) (M := M) g u α) :
    DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart
      (I := I) (M := M) g 2 2 u < ⊤ :=
  DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart_lt_top_of_memWkpChart
    (I := I) (M := M) g (k := 2) (p := 2) (by norm_num)
    (memWkpChart_two_of_chartPOUWitnesses (I := I) (M := M) g h_witness)

omit [NeZero (Module.finrank ℝ E)] in
theorem wkpNormChart_two_le_tsum_chart_norms
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (u : M → ℝ) :
    DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart
      (I := I) (M := M) g 2 2 u ≤
      ∑' α : M,
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) 2 2
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
            (I := I) (M := M) (chartAtlasPOU I M) α u)
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α) :=
  le_of_eq (wkpNormChart_two_eq_tsum (I := I) (M := M) g u)

structure ChartH2NonSmoothBridgeData
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (u : M → ℝ) (α : M) where

  D : ChartBilinearH1ComplData (I := I) (M := M) g α

  Omega'' : Set EuclN
  Omega''_open : IsOpen Omega''
  Omega''_compact_closure : IsCompact (closure Omega'')

  h0 : ℝ
  h0_pos : 0 < h0
  room :
    Metric.cthickening h0 (closure Omega'') ⊆
      DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α

  M_bound : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ
  M_bound_nn : ∀ i k, 0 ≤ M_bound i k
  uniform_diffQuot_bound :
    ∀ (i : Fin (Module.finrank ℝ E)) (k : Fin (Module.finrank ℝ E))
      (h : ℝ), 0 < |h| → |h| ≤ h0 →
        eLpNorm
            (DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h (D.weak_partial i)) 2
            ((volume : Measure EuclN).restrict Omega'')
          ≤ ENNReal.ofReal (M_bound i k)

  memWkp_two_chartPushed :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 2 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
        (chartAtlasPOU I M) α u)
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α)

namespace ChartH2NonSmoothBridgeData

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

omit [NeZero (Module.finrank ℝ E)] in
theorem loc_chart_of_chartH2NonSmoothBridgeData
    {g : SmoothRiemannianMetric I M} {u : M → ℝ} {α : M}
    (h : ChartH2NonSmoothBridgeData (I := I) (M := M) g u α) :
    ∀ i k : Fin (Module.finrank ℝ E),
    ∃ g_ik : EuclN → ℝ,
      MemLp g_ik 2 ((volume : Measure EuclN).restrict h.Omega'') ∧
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k g_ik
        (h.D.weak_partial i) h.Omega'' ∧
      eLpNorm g_ik 2 ((volume : Measure EuclN).restrict h.Omega'') ≤
        ENNReal.ofReal (h.M_bound i k) := by
  exact exists_weak_second_partial_of_uniform_diffQuot_bound (I := I) (M := M) (g := g) (α := α)
    h.D h.Omega''_open h.Omega''_compact_closure h.h0_pos h.room
    h.M_bound_nn h.uniform_diffQuot_bound

omit [NeZero (Module.finrank ℝ E)] in
theorem chartH2NonSmoothPOUWitness_of_bridgeData
    {g : SmoothRiemannianMetric I M} {u : M → ℝ} {α : M}
    (h : ChartH2NonSmoothBridgeData (I := I) (M := M) g u α) :
    ChartH2NonSmoothPOUWitness (I := I) (M := M) g u α :=
  ⟨h.memWkp_two_chartPushed⟩

end ChartH2NonSmoothBridgeData

omit [NeZero (Module.finrank ℝ E)] in
theorem memWkpChart_two_of_chartH2NonSmoothBridgeData
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) {u : M → ℝ}
    (h_bridge : ∀ α : M, ChartH2NonSmoothBridgeData (I := I) (M := M) g u α) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g 2 2 u :=
  memWkpChart_two_of_chartPOUWitnesses (I := I) (M := M) g
    (fun α => (h_bridge α).chartH2NonSmoothPOUWitness_of_bridgeData)

omit [NeZero (Module.finrank ℝ E)] in
theorem wkpNormChart_two_lt_top_of_chartH2NonSmoothBridgeData
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) {u : M → ℝ}
    (h_bridge : ∀ α : M, ChartH2NonSmoothBridgeData (I := I) (M := M) g u α) :
    DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart
      (I := I) (M := M) g 2 2 u < ⊤ :=
  wkpNormChart_two_lt_top_of_chartPOUWitnesses (I := I) (M := M) g
    (fun α => (h_bridge α).chartH2NonSmoothPOUWitness_of_bridgeData)

omit [NeZero (Module.finrank ℝ E)] in
theorem memWkpChart_two_of_laplacianDomain
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (u_h : H1Compl g) (_hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (u : M → ℝ)
    (h_witness : ∀ α : M, ChartH2NonSmoothPOUWitness (I := I) (M := M) g u α) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g 2 2 u ∧
    DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart
      (I := I) (M := M) g 2 2 u < ⊤ := by
  refine ⟨?_, ?_⟩
  · exact memWkpChart_two_of_chartPOUWitnesses (I := I) (M := M) g h_witness
  · exact wkpNormChart_two_lt_top_of_chartPOUWitnesses (I := I) (M := M) g h_witness

omit [NeZero (Module.finrank ℝ E)] in
theorem memWkpChart_two_of_laplacianDomain_with_norm
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (u_h : H1Compl g) (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (u : M → ℝ)
    (h_witness : ∀ α : M, ChartH2NonSmoothPOUWitness (I := I) (M := M) g u α) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g 2 2 u ∧
    DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart
      (I := I) (M := M) g 2 2 u =
      ∑' α : M,
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) 2 2
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
            (I := I) (M := M) (chartAtlasPOU I M) α u)
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α) := by
  refine ⟨?_, ?_⟩
  · exact (memWkpChart_two_of_laplacianDomain (I := I) (M := M) g u_h hu_h u h_witness).1
  · exact wkpNormChart_two_eq_tsum (I := I) (M := M) g u

omit [NeZero (Module.finrank ℝ E)] in
theorem memWkpChart_two_of_laplacianDomain_bridgeData
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (u_h : H1Compl g) (_hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (u : M → ℝ)
    (h_bridge : ∀ α : M, ChartH2NonSmoothBridgeData (I := I) (M := M) g u α) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g 2 2 u ∧
    DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart
      (I := I) (M := M) g 2 2 u < ⊤ := by
  refine ⟨?_, ?_⟩
  · exact memWkpChart_two_of_chartH2NonSmoothBridgeData (I := I) (M := M) g h_bridge
  · exact wkpNormChart_two_lt_top_of_chartH2NonSmoothBridgeData (I := I) (M := M) g h_bridge

def laplacianDomain.lpRep
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (u_h : H1Compl g) : M → ℝ :=
  ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ)

omit [NeZero (Module.finrank ℝ E)] in
theorem laplacianDomain.lpRep_aeEq_coeFn
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (u_h : H1Compl g) :
    laplacianDomain.lpRep (I := I) (M := M) g u_h =
      ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ) := rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem memWkpChart_two_of_laplacianDomain_canonical
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (u_h : H1Compl g) (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (h_witness : ∀ α : M, ChartH2NonSmoothPOUWitness (I := I) (M := M) g
      (laplacianDomain.lpRep (I := I) (M := M) g u_h) α) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g 2 2
      (laplacianDomain.lpRep (I := I) (M := M) g u_h) ∧
    DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart
      (I := I) (M := M) g 2 2
      (laplacianDomain.lpRep (I := I) (M := M) g u_h) < ⊤ :=
  memWkpChart_two_of_laplacianDomain (I := I) (M := M) g u_h hu_h
    (laplacianDomain.lpRep (I := I) (M := M) g u_h) h_witness

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_memWkpChart_two_of_laplacianDomain
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (u_h : H1Compl g) (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (u : M → ℝ)
    (h_witness : ∀ α : M, ChartH2NonSmoothPOUWitness (I := I) (M := M) g u α) :
    ∃ v : M → ℝ,
      DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
        (I := I) (M := M) g 2 2 v ∧
      DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart
        (I := I) (M := M) g 2 2 v < ⊤ := by
  refine ⟨u, ?_⟩
  exact memWkpChart_two_of_laplacianDomain (I := I) (M := M) g u_h hu_h u h_witness

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_memWkpChart_two_of_laplacianDomain_canonical
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (u_h : H1Compl g) (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (h_witness : ∀ α : M, ChartH2NonSmoothPOUWitness (I := I) (M := M) g
      (laplacianDomain.lpRep (I := I) (M := M) g u_h) α) :
    ∃ v : M → ℝ,
      v = laplacianDomain.lpRep (I := I) (M := M) g u_h ∧
      DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
        (I := I) (M := M) g 2 2 v ∧
      DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart
        (I := I) (M := M) g 2 2 v < ⊤ := by
  refine ⟨laplacianDomain.lpRep (I := I) (M := M) g u_h, rfl, ?_⟩
  exact memWkpChart_two_of_laplacianDomain_canonical (I := I) (M := M) g u_h hu_h h_witness

end ManifoldH2NonSmooth
end Laplacian
end Analysis
end DifferentialGeometry
