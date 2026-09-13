import OpenGALib.Interoperability.RicciFlow.ScalarLowerBound
import OpenGALib.Analysis.WidthComparison
import OpenGALib.Analysis.WidthExtinction

/-!
# The geometric scalar bound in the width comparison argument

The scalar input is now the actual minimum of a Ricci flow's scalar curvature.
The sweepout comparison data remain explicit hypotheses: these theorems do not
construct sweepouts, minimal spheres, or surgery. They connect that remaining
geometric input to the already proved analytic lifetime bound.

Reference: Colding-Minicozzi, arXiv:0707.0108, Section 1.5.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature

namespace OpenGA.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [CompactSpace M] [Nonempty M] [I.Boundaryless]

/-- The CM slope bound from geometric scalar curvature and comparison data. -/
theorem eventually_width_slope_lt
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) (hdim : Module.finrank ℝ E = 3)
    {T C : ℝ} (hT : 0 < T) (hC : 0 < C)
    (hslab : Icc 0 T ⊆ D.carrier)
    (hregular : ∀ t ∈ Icc 0 T, 0 < t → t ∈ D.regular)
    (hinitial : ∀ x : M, -(3 : ℝ) / (2 * C) ≤ S.scalar 0 x)
    {width : ℝ → ℝ} {t : ℝ} (ht : t ∈ Icc 0 T)
    (data : WidthComparisonData width t (scalarMinimum S t))
    {q : ℝ} (hq : -(4 * Real.pi) + 3 / (4 * (t + C)) * width t < q) :
    ∀ᶠ s in 𝓝[>] t, slope width t s < q := by
  have hscalar := scalarMinimum_lower_bound S hS hdim hT hC hslab hregular hinitial t ht
  have hw : 0 ≤ width t := by
    rw [← data.realized_energy]
    exact integral_nonneg (fun x => energyDensity_nonneg _ _)
  apply eventually_width_slope_lt_of_comparison data q
  have hmul := mul_le_mul_of_nonneg_right hscalar hw
  have hid : (-(3 : ℝ) / (2 * (t + C))) * width t / 2 =
      -(3 / (4 * (t + C)) * width t) := by
    have hCt : t + C ≠ 0 := (add_pos_of_nonneg_of_pos ht.1 hC).ne'
    field_simp
    ring
  nlinarith

/-- A smooth Ricci-flow interval with CM comparison families obeys the
existing width deadline. The families are still the unproved geometric input. -/
theorem lifetime_le_of_width_comparison
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) (hdim : Module.finrank ℝ E = 3)
    {T C : ℝ} (hT : 0 < T) (hC : 0 < C)
    (hslab : Icc 0 T ⊆ D.carrier)
    (hregular : ∀ t ∈ Icc 0 T, 0 < t → t ∈ D.regular)
    (hinitial : ∀ x : M, -(3 : ℝ) / (2 * C) ≤ S.scalar 0 x)
    {width : ℝ → ℝ} (hcont : ContinuousOn width (Icc 0 T))
    (hfinal : 0 ≤ width T)
    (hcomparison : ∀ t ∈ Ico 0 T,
      Nonempty (WidthComparisonData width t (scalarMinimum S t))) :
    T ≤ widthExtinctionTime C (width 0) := by
  apply le_widthExtinctionTime_of_slope_le hC hT.le hfinal hcont
  intro t ht q hq
  obtain ⟨data⟩ := hcomparison t ht
  exact (eventually_width_slope_lt S hS hdim hT hC hslab hregular hinitial
    (Ico_subset_Icc_self ht) data hq).frequently

end OpenGA.RicciFlow
