import DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.Bootstrap.ChartHm
import DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.Bootstrap.ChartHmPolymorphic
import DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.Bootstrap.ChartHmDomainPow
import DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.NirenbergInterior.InteriorH2
import DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.NirenbergInterior.EffectiveSourceRegularity
import DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.NirenbergInterior.EffectiveSourceSuccessorRegularity
import DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.BaseFChart.PolymorphicRegularity
import DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.VariationalIdentity.DifferentiatedData
import DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.VariationalIdentity.InductiveSuccessor
import DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.NirenbergInterior.MixedPartials
import DifferentialGeometry.Analysis.Elliptic.Regularity.LaplacianDomain.PowH2kBridge
import DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.Bootstrap.H2Regularity
import DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.Bootstrap.H2RegularitySuccessor
import DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.Defs
import DifferentialGeometry.Analysis.Elliptic.Regularity.ChartPushed.MemWkpFour


noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace IteratedChartHmBootstrapStrongInduction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Laplacian.IteratedMixedPartials
open DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrap
open DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapFinal
open DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapCanonical
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge
open DifferentialGeometry.Analysis.Laplacian.ChartPushedMemWkpFour

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem chartSideH2kBridge_mono_of_le
    (g : SmoothRiemannianMetric I M) {k j : ℕ} (hjk : j ≤ k)
    {u : M → ℝ}
    (h_bridge : ChartSideH2kBridge (I := I) (M := M) g k u) :
    ChartSideH2kBridge (I := I) (M := M) g j u := by
  intro α
  have h := h_bridge α
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.le_of_le
    (by omega : 2 * j ≤ 2 * k) h

omit [NeZero (Module.finrank ℝ E)] in
theorem chartPushed_memWkp_j_of_chartSideH2kBridge_at
    (g : SmoothRiemannianMetric I M) (α : M) {k j : ℕ} (hjk : j ≤ 2 * k)
    {u_h : H1Compl (I := I) (M := M) g}
    (h_bridge : ChartSideH2kBridge (I := I) (M := M) g k
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) j 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
        (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) :=
  DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.le_of_le hjk
    (h_bridge α)

omit [NeZero (Module.finrank ℝ E)] in
theorem chosenMthMixed_memWkp_two_two_of_chartSideH2kBridge
    (g : SmoothRiemannianMetric I M) (α : M) {k m : ℕ} (hm : m + 2 ≤ 2 * k)
    {u_h : H1Compl (I := I) (M := M) g}
    (h_bridge : ChartSideH2kBridge (I := I) (M := M) g k
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)))
    (idx : Fin m → Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 2 2
      (chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h m idx)
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) := by
  classical
  have h_parent : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (m + 2) 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
        (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) :=
    chartPushed_memWkp_j_of_chartSideH2kBridge_at
      (I := I) (M := M) g α (k := k) (j := m + 2) hm h_bridge
  have h_parent' : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (2 + m) 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
        (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) := by
    have h_eq : 2 + m = m + 2 := Nat.add_comm 2 m
    rw [h_eq]
    exact h_parent
  exact chosenMthMixedPartialChartPushedU_memWkp_of_chartPushed_memWkp
    (I := I) (M := M) g α u_h m 2 h_parent' idx

omit [NeZero (Module.finrank ℝ E)] in
theorem chartPushed_memWkp_two_k_of_laplacianDomainPow_bridge
    (g : SmoothRiemannianMetric I M) (α : M) (k : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g k)
    (h_bridge : ChartSideH2kBridge (I := I) (M := M) g k
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (2 * k) 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
        (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) := by
  let _ := hu_h
  exact h_bridge α

omit [NeZero (Module.finrank ℝ E)] in
theorem chartPushed_memWkp_two_k_of_laplacianDomainPow
    (g : SmoothRiemannianMetric I M) (α : M) (k : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g k)
    (h_bridge : ChartSideH2kBridge (I := I) (M := M) g k
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (2 * k) 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
        (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) :=
  chartPushed_memWkp_two_k_of_laplacianDomainPow_bridge
    (I := I) (M := M) g α k hu_h h_bridge

omit [NeZero (Module.finrank ℝ E)] in
theorem memWkpChart_two_k_of_laplacianDomainPow_bridge
    (g : SmoothRiemannianMetric I M) (k : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g k)
    (h_bridge : ChartSideH2kBridge (I := I) (M := M) g k
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g (2 * k) 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) := by
  intro α
  exact chartPushed_memWkp_two_k_of_laplacianDomainPow_bridge
    (I := I) (M := M) g α k hu_h h_bridge

theorem chartPushed_memWkp_two_k_unconditional_of_le_two
    (g : SmoothRiemannianMetric I M) (α : M) {k : ℕ} (hk : k ≤ 2)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g k) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (2 * k) 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
        (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) := by
  have h_bridge :=
    chartSideH2kBridge_unconditional_of_laplacianDomainPow_le_two
      (I := I) (M := M) g hk hu_h
  exact chartPushed_memWkp_two_k_of_laplacianDomainPow_bridge
    (I := I) (M := M) g α k hu_h h_bridge

theorem memWkpChart_two_k_unconditional_of_le_two
    (g : SmoothRiemannianMetric I M) {k : ℕ} (hk : k ≤ 2)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g k) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g (2 * k) 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) := by
  intro α
  exact chartPushed_memWkp_two_k_unconditional_of_le_two
    (I := I) (M := M) g α hk hu_h

theorem chartPushed_memWkp_two_min_k_two
    (g : SmoothRiemannianMetric I M) (α : M) (k : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g k) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (2 * min k 2) 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
        (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) := by
  classical
  have h_min_le_2 : min k 2 ≤ 2 := min_le_right _ _
  have hu_h_min : u_h ∈ laplacianDomainPow (I := I) (M := M) g (min k 2) :=
    laplacianDomainPow_le_of_le (I := I) (M := M) g (min_le_left _ _) hu_h
  exact chartPushed_memWkp_two_k_unconditional_of_le_two
    (I := I) (M := M) g α h_min_le_2 hu_h_min

theorem memWkpChart_two_min_k_two
    (g : SmoothRiemannianMetric I M) (k : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g k) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g (2 * min k 2) 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) := by
  intro α
  exact chartPushed_memWkp_two_min_k_two
    (I := I) (M := M) g α k hu_h

omit [NeZero (Module.finrank ℝ E)] in
theorem chartPushed_memWkp_succ_step_of_chartSideH2kBridge
    (g : SmoothRiemannianMetric I M) (α : M) {k m : ℕ} (hm : m + 2 ≤ 2 * k)
    {u_h : H1Compl (I := I) (M := M) g}
    (h_bridge : ChartSideH2kBridge (I := I) (M := M) g k
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (m + 2) 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
        (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) := by
  have h_chart_H_m_plus_1 : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (m + 1) 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
        (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) :=
    chartPushed_memWkp_j_of_chartSideH2kBridge_at
      (I := I) (M := M) g α (k := k) (j := m + 1) (by omega) h_bridge
  have h_top_memWkp_two : ∀ (idx : Fin m → Fin (Module.finrank ℝ E)),
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 2 2
        (chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h m idx)
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α) :=
    fun idx => chosenMthMixed_memWkp_two_two_of_chartSideH2kBridge
      (I := I) (M := M) g α (k := k) (m := m) hm h_bridge idx
  exact chartPushed_memWkp_m_plus_two_step
    (I := I) (M := M) g α u_h m h_chart_H_m_plus_1 h_top_memWkp_two

omit [NeZero (Module.finrank ℝ E)] in
theorem chartPushed_memWkp_two_k_plus_two_two_sided_of_chartSideBridges
    (g : SmoothRiemannianMetric I M) (α : M) (k : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g (k + 1))
    (h_bridge_u : ChartSideH2kBridge (I := I) (M := M) g (k + 1)
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)))
    (h_bridge_rhs : ChartSideH2kBridge (I := I) (M := M) g (k + 1)
      (((laplacianDomain.preimage (I := I) (M := M) g
          ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g k hu_h⟩ :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))) :
    (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (2 * (k + 1)) 2
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
          (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α)) ∧
    (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (2 * (k + 1)) 2
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
          (I := I) (M := M) (chartAtlasPOU I M) α
          ((laplacianDomain.preimage (I := I) (M := M) g
              ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
                (I := I) (M := M) g k hu_h⟩ :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α)) := by
  refine ⟨?_, ?_⟩
  · exact chartPushed_memWkp_two_k_of_laplacianDomainPow_bridge
      (I := I) (M := M) g α (k + 1) hu_h h_bridge_u
  · exact h_bridge_rhs α

omit [NeZero (Module.finrank ℝ E)] in
theorem memWkpChart_two_k_of_preimage_chartSideBridge
    (g : SmoothRiemannianMetric I M) (k : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g (k + 1))
    (h_bridge_rhs : ChartSideH2kBridge (I := I) (M := M) g k
      (((laplacianDomain.preimage (I := I) (M := M) g
          ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g k hu_h⟩ :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g (2 * k) 2
      ((laplacianDomain.preimage (I := I) (M := M) g
          ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g k hu_h⟩ :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) := by
  intro α
  exact h_bridge_rhs α

end IteratedChartHmBootstrapStrongInduction
end Laplacian
end Analysis
end DifferentialGeometry

end
