import DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.NirenbergInterior.EffectiveSourceRegularity
import DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.NirenbergInterior.InteriorH2
import DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.Bootstrap.ChartHm
import DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.Bootstrap.H2RegularitySuccessor
import DifferentialGeometry.Analysis.Elliptic.Regularity.LaplacianDomain.PowH2kBridge
import DifferentialGeometry.Analysis.Elliptic.Regularity.ChartPushed.MemWkpFour


noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace IteratedChartHmBootstrapFinal

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
open DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrap
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge
open DifferentialGeometry.Analysis.Laplacian.ChartPushedMemWkpFour

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

theorem chartPushed_memWkp_unconditional_of_laplacianDomainPow_le_two
    (g : SmoothRiemannianMetric I M) (α : M) {k : ℕ} (hk : k ≤ 2)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g k) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (2 * k) 2
      (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  interval_cases k
  · have h_zero := iteratedH2Regularity_zero (I := I) (M := M) g u_h α
    have h_eq : (2 : ℕ) * 0 = 0 := by norm_num
    rw [h_eq]
    exact h_zero
  · have h_one := (iteratedH2Regularity_one (I := I) (M := M) g hu_h).1 α
    have h_eq : (2 : ℕ) * 1 = 2 := by norm_num
    rw [h_eq]
    exact h_one
  · have h_two := chartPushed_memWkp_four_two_of_laplacianDomainPow_two
      (I := I) (M := M) g α hu_h
    have h_eq : (2 : ℕ) * 2 = 4 := by norm_num
    rw [h_eq]
    exact h_two

theorem chartSideH2kBridge_unconditional_of_laplacianDomainPow_le_two
    (g : SmoothRiemannianMetric I M) {k : ℕ} (hk : k ≤ 2)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g k) :
    ChartSideH2kBridge (I := I) (M := M) g k
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) := by
  intro α
  exact chartPushed_memWkp_unconditional_of_laplacianDomainPow_le_two
    (I := I) (M := M) g α hk hu_h

theorem memWkpChart_unconditional_of_laplacianDomainPow_le_two
    (g : SmoothRiemannianMetric I M) {k : ℕ} (hk : k ≤ 2)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g k) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g (2 * k) 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) := by
  intro α
  exact chartPushed_memWkp_unconditional_of_laplacianDomainPow_le_two
    (I := I) (M := M) g α hk hu_h

omit [NeZero (Module.finrank ℝ E)] in
theorem chartPushed_memWkp_unconditional_of_laplacianDomainPow
    (g : SmoothRiemannianMetric I M) (α : M) (k : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (_hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g k)
    (h_bridge : ChartSideH2kBridge (I := I) (M := M) g k
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (2 * k) 2
      (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
      (chartTargetEuclid (I := I) (M := M) α) :=
  h_bridge α

omit [NeZero (Module.finrank ℝ E)] in
theorem chartPushed_memWkp_j_of_chartSideH2kBridge
    (g : SmoothRiemannianMetric I M) (α : M) {k j : ℕ} (hjk : j ≤ 2 * k)
    {u_h : H1Compl (I := I) (M := M) g}
    (h_bridge : ChartSideH2kBridge (I := I) (M := M) g k
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) j 2
      (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
      (chartTargetEuclid (I := I) (M := M) α) :=
  DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.le_of_le hjk
    (h_bridge α)

omit [NeZero (Module.finrank ℝ E)] in
theorem chartPushed_memWkp_succ_step
    (g : SmoothRiemannianMetric I M) (α : M) (m : ℕ)
    (u_h : H1Compl (I := I) (M := M) g)
    (h_chart_H_m_plus_1 :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (m + 1) 2
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
        (chartTargetEuclid (I := I) (M := M) α))
    (h_top_memWkp_two :
      ∀ (idx : Fin m → Fin (Module.finrank ℝ E)),
        DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) 2 2
          (DifferentialGeometry.Analysis.Laplacian.IteratedMixedPartials.chosenMthMixedPartialChartPushedU
            (I := I) (M := M) g α u_h m idx)
          (chartTargetEuclid (I := I) (M := M) α)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (m + 2) 2
      (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
      (chartTargetEuclid (I := I) (M := M) α) :=
  chartPushed_memWkp_m_plus_two_step (I := I) (M := M) g α u_h m
    h_chart_H_m_plus_1 h_top_memWkp_two

omit [NeZero (Module.finrank ℝ E)] in
theorem memWkpChart_2k_of_chartSideH2kBridge_polymorphic
    (g : SmoothRiemannianMetric I M) (k : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (h_bridge : ChartSideH2kBridge (I := I) (M := M) g k
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g (2 * k) 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) :=
  fun α => h_bridge α

theorem chartPushed_memWkp_two_sided_succ_le_two
    (g : SmoothRiemannianMetric I M) (α : M) {k : ℕ} (hk : k + 1 ≤ 2)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g (k + 1)) :
    (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (2 * (k + 1)) 2
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
        (chartTargetEuclid (I := I) (M := M) α)) ∧
    (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (2 * k) 2
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          ((laplacianDomain.preimage (I := I) (M := M) g
              ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
                (I := I) (M := M) g k hu_h⟩ :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  refine ⟨?_, ?_⟩
  · exact chartPushed_memWkp_unconditional_of_laplacianDomainPow_le_two
      (I := I) (M := M) g α hk hu_h
  · have hk_le_one : k ≤ 1 := by omega
    interval_cases k
    · have h_eq : (2 : ℕ) * 0 = 0 := by norm_num
      rw [h_eq]
      have h_lp := memWkpChart_zero_of_lp (I := I) (M := M) g
        (laplacianDomain.preimage (I := I) (M := M) g
          ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 0 hu_h⟩) α
      exact h_lp
    · have h := laplacianDomainPow_two_iterated_h2 (I := I) (M := M) g hu_h
      have h_eq : (2 : ℕ) * 1 = 2 := by norm_num
      rw [h_eq]
      exact h.2 α

omit [NeZero (Module.finrank ℝ E)] in
theorem chartPushed_memWkp_of_laplacianDomainPow_via_bridge
    (g : SmoothRiemannianMetric I M) (α : M) (k : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g k)
    (h_bridge : ChartSideH2kBridge (I := I) (M := M) g k
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (2 * k) 2
      (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
      (chartTargetEuclid (I := I) (M := M) α) :=
  chartPushed_memWkp_unconditional_of_laplacianDomainPow
    (I := I) (M := M) g α k hu_h h_bridge

end IteratedChartHmBootstrapFinal
end Laplacian
end Analysis
end DifferentialGeometry

end
