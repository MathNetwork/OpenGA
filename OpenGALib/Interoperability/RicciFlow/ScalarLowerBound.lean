import DifferentialGeometry.Geometry.Flow.RicciFlow.Preservation.ScalarLowerBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Regularity

/-!
# Scalar curvature lower bounds for geometric Ricci flows

The scalar field is the scalar curvature of the metric in `SolutionOn`.
The evolution equation and maximum-principle regularity are derived from
`IsSolutionOn`, rather than supplied as conclusions to this interface.
Only an initial scalar-curvature lower bound is required.

The comparison theorem is reused from DifferentialGeometry. The local
trace-norm argument and assembly of the maximum-principle inputs adapt
`Geometry/Flow/RicciFlow/Estimates/FiniteTime/Solution.lean`.
Upstream: qinz1yang/differential-geometry, Apache-2.0, v0.1.2,
commit 1b535dd102b94cc42b107cca27059687888f08b3.
Copyright 2026 The DifferentialGeometry contributors.

Reference: Colding-Minicozzi, *Width and finite extinction time of Ricci flow*,
arXiv:0707.0108, Section 1.5. This file concerns smooth time intervals;
it does not construct a flow or prove compatibility with surgery.
-/

noncomputable section

open Set Bundle
open scoped Manifold ContDiff
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor.Coordinates

namespace OpenGA.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]

/-- The pointwise three-dimensional trace inequality for the actual Ricci tensor. -/
theorem scalar_sq_div_three_le_ricciNorm
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hdim : Module.finrank ℝ E = 3) (t : ℝ) (x : M) :
    (1 / 3 : ℝ) * (S.scalar t x) ^ 2 ≤ ricciNorm S t x := by
  classical
  let : Nonempty (CoordinateIdx (𝕜 := ℝ) E) := ⟨⟨0, by simp [hdim]⟩⟩
  let basis := coordinateFrameAtToBasis (I := I) x
  let gInv := fun k l : CoordinateIdx (𝕜 := ℝ) E =>
    inverseMetricFlatModelInChartComponent
      (I := I) (S.family.metric t) x k l (extChartAt I x x)
  have hinv : MetricInverseInBasisGen (I := I) (S.family.metric t) x basis gInv := by
    simpa [basis, gInv] using
      inverseMetricFlatModelInChart_metricInverseInBasis_center
        (I := I) (S.family.metric t) x
  have h := DifferentialGeometry.Geometry.Operator.metricTracePair0SAt_sq_div_rank_le_normSq0S
    (I := I) (g := S.family.metric t) (basis := basis)
    (gInv := gInv) hinv (S.ricciAt t x)
  rw [SolutionOn.scalar_eq_metricTrace]
  simpa [SolutionOn.scalar, SolutionFamily.scalar, ricciNorm, CoordinateIdx, hdim] using h

/-- A nonpositive initial scalar bound propagates by the Ricci-flow barrier.
The time slab includes its endpoints, and positive times must be regular. -/
theorem scalar_lower_barrier
    [CompactSpace M] [I.Boundaryless]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) (hdim : Module.finrank ℝ E = 3)
    {T c₀ : ℝ} (hT : 0 < T) (hc₀ : c₀ ≤ 0)
    (hslab : Icc 0 T ⊆ D.carrier)
    (hregular : ∀ t ∈ Icc 0 T, 0 < t → t ∈ D.regular)
    (hinitial : ∀ x : M, c₀ ≤ S.scalar 0 x) :
    ∀ t ∈ Icc 0 T, ∀ x : M,
      c₀ / (1 - (2 / 3 : ℝ) * c₀ * t) ≤ S.scalar t x := by
  classical
  let G := flowG S
  have hSmooth := smoothOfSol (I := I) S hS
  have hden : ∀ t ∈ Icc 0 T, 0 < 1 - (2 / 3 : ℝ) * c₀ * t := by
    intro t ht
    have := mul_nonpos_of_nonpos_of_nonneg hc₀ ht.1
    nlinarith
  have hbar : ContinuousOn (scalarLowerBarrier 3 c₀) (Icc 0 T) := by
    exact continuousOn_const.div
      (by fun_prop) (fun t ht => (hden t ht).ne')
  have hcont : ContinuousOn (fun p : ℝ × M => S.scalar p.1 p.2)
      (DifferentialGeometry.Integral.Connection.spacetimeSlab (M := M) T) := by
    exact hS.scalarCont.mono (fun p hp => ⟨hslab hp.1, hp.2⟩)
  have hcompact := DifferentialGeometry.Integral.Connection.scalarWMPValueSet_isCompact
    (M := M) T S.scalar (scalarLowerBarrier 3 c₀) hcont hbar
  obtain ⟨K, hK⟩ := exists_scalarLowerReaction_lipschitzOn_valueSet
    (M := M) 3 T S.scalar (scalarLowerBarrier 3 c₀) hcompact
  have hreg := scalarRegOfSmooth (I := I) S hSmooth G T 3 c₀ K
    (fun t ht => hslab ht) (by intro t ht; rfl)
    (fun t ht => (hden t ht).ne')
  exact scalar_curvature_lower_bound_of_scalarEvolution_of_regularity
    (I := I) (D := D) G T 3 c₀ hT (by norm_num)
    S.scalar (fun t x => laplacianAt G t (S.scalar t) x) (ricciNorm S) K
    hslab hregular hden hreg (scalar_curvature_evolution S hS)
    (ScalarLaplacianRealizesHeatOperatorOn.of_laplacianAt (by intro t ht x; rfl))
    (fun t ht x => scalar_sq_div_three_le_ricciNorm S hdim t x) hinitial hK

/-- The Colding-Minicozzi lower bound, with one fixed initial constant `C`. -/
theorem scalar_lower_bound
    [CompactSpace M] [I.Boundaryless]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) (hdim : Module.finrank ℝ E = 3)
    {T C : ℝ} (hT : 0 < T) (hC : 0 < C)
    (hslab : Icc 0 T ⊆ D.carrier)
    (hregular : ∀ t ∈ Icc 0 T, 0 < t → t ∈ D.regular)
    (hinitial : ∀ x : M, -(3 : ℝ) / (2 * C) ≤ S.scalar 0 x) :
    ∀ t ∈ Icc 0 T, ∀ x : M, -(3 : ℝ) / (2 * (t + C)) ≤ S.scalar t x := by
  have hc₀ : -(3 : ℝ) / (2 * C) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity)
  have h := scalar_lower_barrier S hS hdim hT hc₀ hslab hregular hinitial
  intro t ht x
  have hCt : t + C ≠ 0 := (add_pos_of_nonneg_of_pos ht.1 hC).ne'
  have hid : (-(3 : ℝ) / (2 * C)) / (1 - (2 / 3 : ℝ) * (-(3 : ℝ) / (2 * C)) * t) =
      -(3 : ℝ) / (2 * (t + C)) := by
    have hden : 1 - (2 / 3 : ℝ) * (-(3 : ℝ) / (2 * C)) * t = (t + C) / C := by
      field_simp
      ring
    rw [hden]
    field_simp [hC.ne', hCt]
  rw [← hid]
  exact h t ht x

/-- The normalization used by the existing OpenGA extinction trace. -/
theorem scalar_lower_bound_normalized
    [CompactSpace M] [I.Boundaryless]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) (hdim : Module.finrank ℝ E = 3)
    {T : ℝ} (hT : 0 < T)
    (hslab : Icc 0 T ⊆ D.carrier)
    (hregular : ∀ t ∈ Icc 0 T, 0 < t → t ∈ D.regular)
    (hinitial : ∀ x : M, -6 ≤ S.scalar 0 x) :
    ∀ t ∈ Icc 0 T, ∀ x : M, -(6 : ℝ) / (1 + 4 * t) ≤ S.scalar t x := by
  have h := scalar_lower_barrier S hS hdim hT (by norm_num : (-6 : ℝ) ≤ 0)
    hslab hregular hinitial
  intro t ht x
  have hden : 1 - (2 / 3 : ℝ) * (-6) * t = 1 + 4 * t := by ring
  simpa only [hden] using h t ht x

/-- The infimum of the actual scalar-curvature range. Compactness and
nonemptiness ensure it is attained; no arbitrary scalar profile is introduced. -/
def scalarMinimum {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (t : ℝ) : ℝ := sInf (range (S.scalar t))

/-- On a nonempty closed manifold, `scalarMinimum` is attained. -/
theorem exists_scalar_eq_minimum [CompactSpace M] [Nonempty M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (t : ℝ) :
    ∃ x : M, S.scalar t x = scalarMinimum S t := by
  obtain ⟨x, hx, hmin⟩ := isCompact_univ.exists_isMinOn
    (Set.univ_nonempty : (univ : Set M).Nonempty)
    (scalarSmoothOfSol S t).continuous.continuousOn
  refine ⟨x, le_antisymm ?_ ?_⟩
  · exact le_csInf (range_nonempty _) (by rintro y ⟨z, rfl⟩; exact hmin (mem_univ z))
  · exact csInf_le ⟨S.scalar t x, by rintro y ⟨z, rfl⟩; exact hmin (mem_univ z)⟩
      (mem_range_self x)

/-- The same lower bound holds for the geometric scalar minimum. -/
theorem scalarMinimum_lower_bound
    [CompactSpace M] [Nonempty M] [I.Boundaryless]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) (hdim : Module.finrank ℝ E = 3)
    {T C : ℝ} (hT : 0 < T) (hC : 0 < C)
    (hslab : Icc 0 T ⊆ D.carrier)
    (hregular : ∀ t ∈ Icc 0 T, 0 < t → t ∈ D.regular)
    (hinitial : ∀ x : M, -(3 : ℝ) / (2 * C) ≤ S.scalar 0 x) :
    ∀ t ∈ Icc 0 T, -(3 : ℝ) / (2 * (t + C)) ≤ scalarMinimum S t := by
  intro t ht
  obtain ⟨x, hx⟩ := exists_scalar_eq_minimum S t
  rw [← hx]
  exact scalar_lower_bound S hS hdim hT hC hslab hregular hinitial t ht x

end OpenGA.RicciFlow
