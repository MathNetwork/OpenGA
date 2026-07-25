import DifferentialGeometry.Integration.Volume.ChartDensity
import DifferentialGeometry.Analysis.Integration.Measure.RiemannianMeasure
import DifferentialGeometry.Integration.Volume.ChartDensity
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import DifferentialGeometry.Integration.Volume.Invariance
import DifferentialGeometry.Analysis.Integration.Measure.Properties
import DifferentialGeometry.Integration.Volume.ChartDensity
import DifferentialGeometry.Analysis.Integration.Measure.RiemannianMeasure
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import DifferentialGeometry.Integration.Volume.Invariance
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Topology.Compactness.LocallyFinite
import Mathlib.Topology.Algebra.Support
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Geometry.Manifold.Metrizable
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Topology.Compactness.LocallyFinite
import DifferentialGeometry.Analysis.Integration.Measure.FamilyDecomposition
import DifferentialGeometry.Analysis.Integration.Measure.FamilyDefs
import DifferentialGeometry.Analysis.Integration.Measure.JacobiFormula

set_option autoImplicit false


































noncomputable section

open Bundle Manifold Set MeasureTheory Matrix
open scoped Manifold Topology ContDiff ENNReal Matrix BigOperators

namespace DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]






private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩



theorem continuousOn_deriv_of_hasDerivAt_eq_continuousOn
    {α : Type*} [TopologicalSpace α]
    {S : Set (ℝ × α)} {f D : ℝ → α → ℝ}
    (hderiv :
      ∀ p ∈ S, HasDerivAt (fun t : ℝ => f t p.2) (D p.1 p.2) p.1)
    (hD : ContinuousOn (fun p : ℝ × α => D p.1 p.2) S) :
    ContinuousOn
      (fun p : ℝ × α => deriv (fun t : ℝ => f t p.2) p.1)
      S := by
  have h_eq : Set.EqOn
      (fun p : ℝ × α => deriv (fun t : ℝ => f t p.2) p.1)
      (fun p : ℝ × α => D p.1 p.2) S := by
    intro p hp
    exact (hderiv p hp).deriv
  exact hD.congr h_eq



theorem MetricFamilyRegularAt.of_chartGram_timeDeriv
    {g_fam : ℝ → SmoothRiemannianMetric I M} {t₀ : ℝ}
    (h :
      ∀ x₀ i j, ∃ D : ℝ → M → ℝ,
        (∀ t x,
          x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet →
            HasDerivAt
              (fun s : ℝ => chartGramMatrix (I := I) (g_fam s) x₀ x i j)
              (D t x) t) ∧
        ContinuousOn
          (fun p : ℝ × M =>
            chartGramMatrix (I := I) (g_fam p.1) x₀ p.2 i j)
          (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) ∧
        ContinuousOn
          (fun p : ℝ × M => D p.1 p.2)
          (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    MetricFamilyRegularAt (I := I) g_fam t₀ := by
  refine
    { hasDerivAt_chartGramMatrix := ?_
      continuousOn_chartGramMatrix := ?_
      continuousOn_deriv_chartGramMatrix := ?_ }
  · intro x₀ i j x hx t
    rcases h x₀ i j with ⟨D, hD_deriv, -, -⟩
    have hderiv := hD_deriv t x hx
    exact hderiv.congr_deriv hderiv.deriv.symm
  · intro x₀ i j
    rcases h x₀ i j with ⟨D, -, hG_cont, -⟩
    exact hG_cont
  · intro x₀ i j
    rcases h x₀ i j with ⟨D, hD_deriv, -, hD_cont⟩
    refine continuousOn_deriv_of_hasDerivAt_eq_continuousOn
      (S := Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)
      (f := fun t x => chartGramMatrix (I := I) (g_fam t) x₀ x i j)
      (D := D) ?_ hD_cont
    intro p hp
    exact hD_deriv p.1 p.2 hp.2

theorem FunctionRegularAt_const (c : ℝ) (t₀ : ℝ) :
    FunctionRegularAt (fun _ : ℝ => fun _ : M => c) t₀ := by
  refine
    { hasDerivAt_time := ?_
      continuous_joint := ?_
      continuous_deriv_joint := ?_ }
  · intro _ t
    have hderiv : deriv (fun _ : ℝ => c) t = 0 :=
      (hasDerivAt_const (x := t) (c := c)).deriv
    simpa [hderiv] using (hasDerivAt_const (x := t) (c := c))
  · simpa using (continuous_const : Continuous (fun _ : ℝ × M => c))
  · have hfun :
        (fun p : ℝ × M => deriv (fun _ : ℝ => c) p.1) =
          fun _ : ℝ × M => (0 : ℝ) := by
      funext p
      exact (hasDerivAt_const (x := p.1) (c := c)).deriv
    simpa [hfun] using (continuous_const : Continuous (fun _ : ℝ × M => (0 : ℝ)))



theorem FunctionRegularAt_one (t₀ : ℝ) :
    FunctionRegularAt (fun _ : ℝ => fun _ : M => (1 : ℝ)) t₀ :=
  FunctionRegularAt_const (M := M) 1 t₀













section Jacobi

variable {n : Type*} [Fintype n] [DecidableEq n]


end Jacobi








section ChartDensityFamily

variable {g_fam : ℝ → SmoothRiemannianMetric I M}





end ChartDensityFamily
















section ChartInvarianceOfTraceTimeDeriv


end ChartInvarianceOfTraceTimeDeriv



end DifferentialGeometry.Integral.Measure
