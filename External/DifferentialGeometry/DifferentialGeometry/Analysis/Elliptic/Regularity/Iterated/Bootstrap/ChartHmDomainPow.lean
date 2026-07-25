import DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.Bootstrap.ChartHmPolymorphic
import DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.NirenbergInterior.EffectiveSourceSuccessorRegularity
import DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.NirenbergInterior.EffectiveSourceRegularity
import DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.NirenbergInterior.InteriorH2
import DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.BaseFChart.PolymorphicRegularity
import DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.Bootstrap.H2RegularitySuccessor


noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace IteratedChartHmBootstrapCanonical

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
open DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapFinal
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge
open DifferentialGeometry.Analysis.Laplacian.ChartPushedMemWkpFour

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] in
theorem laplacianDomainPow_le_of_le
    (g : SmoothRiemannianMetric I M) {k j : ℕ} (hjk : j ≤ k)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g k) :
    u_h ∈ laplacianDomainPow (I := I) (M := M) g j := by
  classical
  obtain ⟨d, hd⟩ : ∃ d : ℕ, k = j + d := Nat.exists_eq_add_of_le hjk
  subst hd
  clear hjk
  induction d with
  | zero =>
      simpa using hu_h
  | succ d ih =>
      have h_succ_eq : j + (d + 1) = (j + d) + 1 := by ring
      rw [h_succ_eq] at hu_h
      have hu_h_jd : u_h ∈ laplacianDomainPow (I := I) (M := M) g (j + d) := by
        rw [DifferentialGeometry.Analysis.Laplacian.laplacianDomainPow_succ_mem_iff] at hu_h
        obtain ⟨f, hf⟩ := hu_h
        by_cases h_jd_zero : j + d = 0
        · rw [h_jd_zero]
          rw [DifferentialGeometry.Analysis.Laplacian.laplacianDomainPow_zero]
          exact Submodule.mem_top
        · obtain ⟨n, hn⟩ : ∃ n : ℕ, j + d = n + 1 :=
            Nat.exists_eq_succ_of_ne_zero h_jd_zero
          rw [hn] at hf ⊢
          rw [DifferentialGeometry.Analysis.Laplacian.iteratedResolventL2_succ_apply] at hf
          rw [DifferentialGeometry.Analysis.Laplacian.laplacianDomainPow_succ_mem_iff]
          refine ⟨DifferentialGeometry.Analysis.Laplacian.resolventL2
            (I := I) (M := M) g f, ?_⟩
          rw [hf]
          congr 1
          have h1 : DifferentialGeometry.Analysis.Laplacian.iteratedResolventL2
              (I := I) (M := M) g n
              (DifferentialGeometry.Analysis.Laplacian.resolventL2
                (I := I) (M := M) g f) =
            DifferentialGeometry.Analysis.Laplacian.iteratedResolventL2
              (I := I) (M := M) g (n + 1) f := by
            rw [DifferentialGeometry.Analysis.Laplacian.iteratedResolventL2_add]
            rfl
          have h2 : DifferentialGeometry.Analysis.Laplacian.resolventL2
              (I := I) (M := M) g
              (DifferentialGeometry.Analysis.Laplacian.iteratedResolventL2
                (I := I) (M := M) g n f) =
            DifferentialGeometry.Analysis.Laplacian.iteratedResolventL2
              (I := I) (M := M) g (n + 1) f := by
            rw [DifferentialGeometry.Analysis.Laplacian.iteratedResolventL2_succ_apply]
          rw [h1, h2]
      exact ih hu_h_jd

theorem chartPushed_memWkp_two_k_of_laplacianDomainPow_le_two
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
        (I := I) (M := M) α) :=
  chartPushed_memWkp_unconditional_of_laplacianDomainPow_le_two
    (I := I) (M := M) g α hk hu_h

theorem chartSideH2kBridge_of_laplacianDomainPow_le_two
    (g : SmoothRiemannianMetric I M) {k : ℕ} (hk : k ≤ 2)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g k) :
    ChartSideH2kBridge (I := I) (M := M) g k
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) :=
  chartSideH2kBridge_unconditional_of_laplacianDomainPow_le_two
    (I := I) (M := M) g hk hu_h

theorem memWkpChart_two_k_of_laplacianDomainPow_le_two
    (g : SmoothRiemannianMetric I M) {k : ℕ} (hk : k ≤ 2)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g k) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g (2 * k) 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) :=
  memWkpChart_unconditional_of_laplacianDomainPow_le_two
    (I := I) (M := M) g hk hu_h

theorem chartPushed_memWkp_two_k_of_laplacianDomainPow_min_two
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
  have hu_h_min : u_h ∈ laplacianDomainPow (I := I) (M := M) g (min k 2) :=
    laplacianDomainPow_le_of_le (I := I) (M := M) g (min_le_left _ _) hu_h
  have h_min_le_2 : min k 2 ≤ 2 := min_le_right _ _
  exact chartPushed_memWkp_two_k_of_laplacianDomainPow_le_two
    (I := I) (M := M) g α h_min_le_2 hu_h_min

theorem chartSideH2kBridge_of_laplacianDomainPow_min_two
    (g : SmoothRiemannianMetric I M) (k : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g k) :
    ChartSideH2kBridge (I := I) (M := M) g (min k 2)
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) := by
  classical
  have hu_h_min : u_h ∈ laplacianDomainPow (I := I) (M := M) g (min k 2) :=
    laplacianDomainPow_le_of_le (I := I) (M := M) g (min_le_left _ _) hu_h
  have h_min_le_2 : min k 2 ≤ 2 := min_le_right _ _
  exact chartSideH2kBridge_of_laplacianDomainPow_le_two
    (I := I) (M := M) g h_min_le_2 hu_h_min

theorem memWkpChart_two_k_of_laplacianDomainPow_min_two
    (g : SmoothRiemannianMetric I M) (k : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g k) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g (2 * min k 2) 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) := by
  classical
  have hu_h_min : u_h ∈ laplacianDomainPow (I := I) (M := M) g (min k 2) :=
    laplacianDomainPow_le_of_le (I := I) (M := M) g (min_le_left _ _) hu_h
  have h_min_le_2 : min k 2 ≤ 2 := min_le_right _ _
  exact memWkpChart_two_k_of_laplacianDomainPow_le_two
    (I := I) (M := M) g h_min_le_2 hu_h_min

theorem laplacianDomainPow_memWkpChart_two_k
    (g : SmoothRiemannianMetric I M) (k : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g k) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g (2 * min k 2) 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) ∧
    DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart
      (I := I) (M := M) g (2 * min k 2) 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) < ⊤ := by
  classical
  have h_mem := memWkpChart_two_k_of_laplacianDomainPow_min_two
    (I := I) (M := M) g k hu_h
  refine ⟨h_mem, ?_⟩
  exact DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart_lt_top_of_memWkpChart
    (I := I) (M := M) g (k := 2 * min k 2) (p := 2) (by norm_num) h_mem

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
  chartPushed_memWkp_unconditional_of_laplacianDomainPow
    (I := I) (M := M) g α k hu_h h_bridge

omit [NeZero (Module.finrank ℝ E)] in
theorem memWkpChart_two_k_of_laplacianDomainPow
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
  let _ := hu_h
  exact memWkpChart_2k_of_chartSideH2kBridge_polymorphic
    (I := I) (M := M) g k h_bridge

omit [NeZero (Module.finrank ℝ E)] in
theorem chartSideH2kBridge_of_laplacianDomainPow
    (g : SmoothRiemannianMetric I M) (k : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (_hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g k)
    (h_bridge : ChartSideH2kBridge (I := I) (M := M) g k
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))) :
    ChartSideH2kBridge (I := I) (M := M) g k
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) :=
  h_bridge

end IteratedChartHmBootstrapCanonical
end Laplacian
end Analysis
end DifferentialGeometry

end
