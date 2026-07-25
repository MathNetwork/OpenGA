import DifferentialGeometry.Analysis.Elliptic.Regularity.LaplacianDomain.PowH4Bridge
import DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.Bootstrap.H2Regularity


noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace LaplacianDomainPowH2kBridge

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

def ChartSideH2kBridge (_g : SmoothRiemannianMetric I M) (k : ℕ) (u : M → ℝ) : Prop :=
  ∀ α : M,
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (2 * k) 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
        (chartAtlasPOU I M) α u)
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem memWkpChart_2k_of_chartSideH2kBridge
    (g : SmoothRiemannianMetric I M) (k : ℕ) {u : M → ℝ}
    (h_bridge : ChartSideH2kBridge (I := I) (M := M) g k u) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g (2 * k) 2 u := by
  intro α
  exact h_bridge α

omit [NeZero (Module.finrank ℝ E)] in
theorem wkpNormChart_2k_lt_top_of_chartSideH2kBridge
    (g : SmoothRiemannianMetric I M) (k : ℕ) {u : M → ℝ}
    (h_bridge : ChartSideH2kBridge (I := I) (M := M) g k u) :
    DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart
      (I := I) (M := M) g (2 * k) 2 u < ⊤ :=
  DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart_lt_top_of_memWkpChart
    (I := I) (M := M) g (k := 2 * k) (p := 2) (by norm_num)
    (memWkpChart_2k_of_chartSideH2kBridge (I := I) (M := M) g k h_bridge)

omit [NeZero (Module.finrank ℝ E)] in
theorem laplacianDomainPow_memWkpChart_2k_of_chartSideH2kBridge
    (g : SmoothRiemannianMetric I M) (k : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g k)
    (h_bridge : ChartSideH2kBridge (I := I) (M := M) g k
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g (2 * k) 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) ∧
    DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart
      (I := I) (M := M) g (2 * k) 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) < ⊤ := by
  let _ := hu_h
  refine ⟨?_, ?_⟩
  · exact memWkpChart_2k_of_chartSideH2kBridge (I := I) (M := M) g k h_bridge
  · exact wkpNormChart_2k_lt_top_of_chartSideH2kBridge
      (I := I) (M := M) g k h_bridge

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_laplacianDomainPow_memWkpChart_2k_of_chartSideH2kBridge
    (g : SmoothRiemannianMetric I M) (k : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g k)
    (h_bridge : ChartSideH2kBridge (I := I) (M := M) g k
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))) :
    ∃ u : M → ℝ,
      u = ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) ∧
      DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
        (I := I) (M := M) g (2 * k) 2 u ∧
      DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart
        (I := I) (M := M) g (2 * k) 2 u < ⊤ := by
  refine ⟨((H1ComplToLp (I := I) (M := M) g u_h :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ), rfl, ?_, ?_⟩
  · exact (laplacianDomainPow_memWkpChart_2k_of_chartSideH2kBridge
      (I := I) (M := M) g k hu_h h_bridge).1
  · exact (laplacianDomainPow_memWkpChart_2k_of_chartSideH2kBridge
      (I := I) (M := M) g k hu_h h_bridge).2

omit [NeZero (Module.finrank ℝ E)] in
theorem laplacianDomainPow_memWkpChart_2k_two_sided_of_chartSideBridges
    (g : SmoothRiemannianMetric I M) (k : ℕ)
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
    (DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
        (I := I) (M := M) g (2 * (k + 1)) 2
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) ∧
      DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart
        (I := I) (M := M) g (2 * (k + 1)) 2
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) < ⊤) ∧
    (DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
        (I := I) (M := M) g (2 * (k + 1)) 2
        ((laplacianDomain.preimage (I := I) (M := M) g
            ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
              (I := I) (M := M) g k hu_h⟩ :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) ∧
      DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart
        (I := I) (M := M) g (2 * (k + 1)) 2
        ((laplacianDomain.preimage (I := I) (M := M) g
            ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
              (I := I) (M := M) g k hu_h⟩ :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) < ⊤) := by
  refine ⟨laplacianDomainPow_memWkpChart_2k_of_chartSideH2kBridge
    (I := I) (M := M) g (k + 1) hu_h h_bridge_u, ?_⟩
  refine ⟨memWkpChart_2k_of_chartSideH2kBridge (I := I) (M := M) g (k + 1)
    h_bridge_rhs, ?_⟩
  exact wkpNormChart_2k_lt_top_of_chartSideH2kBridge
    (I := I) (M := M) g (k + 1) h_bridge_rhs

omit [NeZero (Module.finrank ℝ E)] in
theorem chartSideH2kBridge_zero
    (g : SmoothRiemannianMetric I M)
    (u_h : H1Compl (I := I) (M := M) g) :
    ChartSideH2kBridge (I := I) (M := M) g 0
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) := by
  intro α
  have h := iteratedH2Regularity_zero (I := I) (M := M) g u_h
  have h_eq : (2 : ℕ) * 0 = 0 := by norm_num
  rw [h_eq]
  exact h α

omit [NeZero (Module.finrank ℝ E)] in
theorem laplacianDomainPow_memWkpChart_2k_of_chartSideH2kBridge_zero
    (g : SmoothRiemannianMetric I M)
    (u_h : H1Compl (I := I) (M := M) g) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g 0 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) ∧
    DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart
      (I := I) (M := M) g 0 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) < ⊤ := by
  have hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 0 := by
    rw [laplacianDomainPow_zero]
    exact Submodule.mem_top
  have h_bridge := chartSideH2kBridge_zero (I := I) (M := M) g u_h
  have h_eq : (2 : ℕ) * 0 = 0 := by norm_num
  have := laplacianDomainPow_memWkpChart_2k_of_chartSideH2kBridge
    (I := I) (M := M) g 0 hu_h h_bridge
  rw [h_eq] at this
  exact this

theorem chartSideH2kBridge_one
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 1) :
    ChartSideH2kBridge (I := I) (M := M) g 1
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) := by
  intro α
  have h := (iteratedH2Regularity_one (I := I) (M := M) g hu_h).1
  have h_eq : (2 : ℕ) * 1 = 2 := by norm_num
  rw [h_eq]
  exact h α

theorem laplacianDomainPow_memWkpChart_2k_of_chartSideH2kBridge_one
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 1) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g 2 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) ∧
    DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart
      (I := I) (M := M) g 2 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) < ⊤ :=
  iteratedH2Regularity_one (I := I) (M := M) g hu_h

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompactSpace M] in
theorem chartSideH4Bridge_iff_chartSideH2kBridge_two
    (g : SmoothRiemannianMetric I M) (u : M → ℝ) :
    DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH4Bridge.ChartSideH4Bridge
      (I := I) (M := M) g u ↔
    ChartSideH2kBridge (I := I) (M := M) g 2 u := by
  unfold DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH4Bridge.ChartSideH4Bridge
    ChartSideH2kBridge
  have h_eq : (2 : ℕ) * 2 = 4 := by norm_num
  rw [h_eq]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompactSpace M] in
theorem chartSideH2kBridge_two_of_chartSideH4Bridge
    (g : SmoothRiemannianMetric I M) {u : M → ℝ}
    (h : DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH4Bridge.ChartSideH4Bridge
      (I := I) (M := M) g u) :
    ChartSideH2kBridge (I := I) (M := M) g 2 u :=
  (chartSideH4Bridge_iff_chartSideH2kBridge_two (I := I) (M := M) g u).mp h

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompactSpace M] in
theorem chartSideH4Bridge_of_chartSideH2kBridge_two
    (g : SmoothRiemannianMetric I M) {u : M → ℝ}
    (h : ChartSideH2kBridge (I := I) (M := M) g 2 u) :
    DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH4Bridge.ChartSideH4Bridge
      (I := I) (M := M) g u :=
  (chartSideH4Bridge_iff_chartSideH2kBridge_two (I := I) (M := M) g u).mpr h

omit [NeZero (Module.finrank ℝ E)] in
theorem laplacianDomainPow_memWkpChart_2k_of_chartSideH4Bridge
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_bridge : DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH4Bridge.ChartSideH4Bridge
      (I := I) (M := M) g
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g 4 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) ∧
    DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart
      (I := I) (M := M) g 4 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) < ⊤ := by
  have h_bridge_2k := chartSideH2kBridge_two_of_chartSideH4Bridge
    (I := I) (M := M) g h_bridge
  have h := laplacianDomainPow_memWkpChart_2k_of_chartSideH2kBridge
    (I := I) (M := M) g 2 hu_h h_bridge_2k
  have h_eq : (2 : ℕ) * 2 = 4 := by norm_num
  rw [h_eq] at h
  exact h

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompactSpace M] in
theorem chartSideH2kBridge_le_of_le
    (g : SmoothRiemannianMetric I M)
    {k j : ℕ} (hkj : j ≤ k) {u : M → ℝ}
    (h : ChartSideH2kBridge (I := I) (M := M) g k u) :
    ChartSideH2kBridge (I := I) (M := M) g j u := by
  intro α
  have h_le : 2 * j ≤ 2 * k := Nat.mul_le_mul_left 2 hkj
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.le_of_le h_le (h α)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompactSpace M] in
theorem chartSideH2kBridge_pred
    (g : SmoothRiemannianMetric I M)
    (k : ℕ) {u : M → ℝ}
    (h : ChartSideH2kBridge (I := I) (M := M) g (k + 1) u) :
    ChartSideH2kBridge (I := I) (M := M) g k u :=
  chartSideH2kBridge_le_of_le (I := I) (M := M) g (Nat.le_succ k) h

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem chartSideH2kBridge_add
    (g : SmoothRiemannianMetric I M) (k : ℕ)
    {u v : M → ℝ}
    (hu : ChartSideH2kBridge (I := I) (M := M) g k u)
    (hv : ChartSideH2kBridge (I := I) (M := M) g k v) :
    ChartSideH2kBridge (I := I) (M := M) g k (fun x => u x + v x) := by
  intro α
  rw [chartPushed_add]
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.add
    (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    (hu α) (hv α)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem chartSideH2kBridge_const_smul
    (g : SmoothRiemannianMetric I M) (k : ℕ)
    (c : ℝ) {u : M → ℝ}
    (hu : ChartSideH2kBridge (I := I) (M := M) g k u) :
    ChartSideH2kBridge (I := I) (M := M) g k (fun x => c * u x) := by
  intro α
  rw [chartPushed_const_smul]
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.const_smul
    (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    (hu α) c

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem chartSideH2kBridge_neg
    (g : SmoothRiemannianMetric I M) (k : ℕ)
    {u : M → ℝ}
    (hu : ChartSideH2kBridge (I := I) (M := M) g k u) :
    ChartSideH2kBridge (I := I) (M := M) g k (fun x => -u x) := by
  have h := chartSideH2kBridge_const_smul (I := I) (M := M) g k (-1) hu
  have hEq : (fun x : M => (-1 : ℝ) * u x) = (fun x : M => -u x) := by
    funext x; ring
  rw [hEq] at h
  exact h

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem chartSideH2kBridge_sub
    (g : SmoothRiemannianMetric I M) (k : ℕ)
    {u v : M → ℝ}
    (hu : ChartSideH2kBridge (I := I) (M := M) g k u)
    (hv : ChartSideH2kBridge (I := I) (M := M) g k v) :
    ChartSideH2kBridge (I := I) (M := M) g k (fun x => u x - v x) := by
  have hneg := chartSideH2kBridge_neg (I := I) (M := M) g k hv
  have h := chartSideH2kBridge_add (I := I) (M := M) g k hu hneg
  have hEq : (fun x : M => u x + -v x) = (fun x : M => u x - v x) := by
    funext x; ring
  rw [hEq] at h
  exact h

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem memWkpChart_2j_of_chartSideH2kBridge
    (g : SmoothRiemannianMetric I M)
    {k j : ℕ} (hkj : j ≤ k) {u : M → ℝ}
    (h_bridge : ChartSideH2kBridge (I := I) (M := M) g k u) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g (2 * j) 2 u := by
  have h_full := memWkpChart_2k_of_chartSideH2kBridge
    (I := I) (M := M) g k h_bridge
  exact DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart.le_of_le
    (Nat.mul_le_mul_left 2 hkj) h_full

omit [NeZero (Module.finrank ℝ E)] in
theorem laplacianDomainPow_memWkpChart_2j_of_chartSideH2kBridge
    (g : SmoothRiemannianMetric I M)
    {k j : ℕ} (hkj : j ≤ k)
    {u_h : H1Compl (I := I) (M := M) g}
    (_hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g k)
    (h_bridge : ChartSideH2kBridge (I := I) (M := M) g k
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g (2 * j) 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) :=
  memWkpChart_2j_of_chartSideH2kBridge (I := I) (M := M) g hkj h_bridge

omit [NeZero (Module.finrank ℝ E)] in
theorem laplacianDomainPow_memWkpChart_2k_unified
    (g : SmoothRiemannianMetric I M) (k : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g k)
    (h_bridge : ChartSideH2kBridge (I := I) (M := M) g k
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g (2 * k) 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) :=
  (laplacianDomainPow_memWkpChart_2k_of_chartSideH2kBridge
    (I := I) (M := M) g k hu_h h_bridge).1

end LaplacianDomainPowH2kBridge
end Laplacian
end Analysis
end DifferentialGeometry

end
