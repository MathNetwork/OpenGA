import Theorems.Thm_DifferentialGeometry_Integral_Measure_trace_chartGramMatrix_inv_deriv_chart_independent
import Theorems.Thm_DifferentialGeometry_Integral_Measure_hasDerivAt_chartDensityFamily_eq_half_trace_inv_mul
import Definitions.Def_ClosedSurface_DifferentialGeometry_Analysis_Integration_Measure_ChartDensity
import Definitions.Def_ClosedSurface_DifferentialGeometry_Analysis_Integration_Measure_Family
import Definitions.Def_ClosedSurface_DifferentialGeometry_Analysis_Integration_Measure_FamilyDecomposition
import Definitions.Def_ClosedSurface_DifferentialGeometry_Analysis_Integration_Measure_FamilyDefs
import Definitions.Def_ClosedSurface_DifferentialGeometry_Analysis_Integration_Measure_Invariance
import Definitions.Def_ClosedSurface_DifferentialGeometry_Analysis_Integration_Measure_Properties
import Definitions.Def_ClosedSurface_DifferentialGeometry_Analysis_Integration_Measure_RiemannianMeasure
import Definitions.Def_ClosedSurface_DifferentialGeometry_Bundle_TangentSpace
import Definitions.Def_ClosedSurface_DifferentialGeometry_Geometry_Metric_ChartGram
import Definitions.Def_OpenGA_ImmersedMetric
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Matrix.Mul
import Mathlib.Geometry.Manifold.Algebra.Monoid
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.ContMDiffMap
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.Metrizable
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Compactness.LocallyFinite


section

noncomputable section

open Bundle Manifold Set MeasureTheory Matrix

open scoped Manifold Topology ContDiff ENNReal Matrix BigOperators

namespace DifferentialGeometry

namespace Integral

namespace Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [local instance] _root_.OpenGAExport.DifferentialGeometry.Analysis.Integration.Measure.FamilyDefs.instance_30

attribute [local instance] _root_.OpenGAExport.DifferentialGeometry.Analysis.Integration.Measure.FamilyDefs.instance_31

attribute [local instance] _root_.OpenGAExport.DifferentialGeometry.Analysis.Integration.Measure.FamilyDefs.instance_32

attribute [local instance] _root_.OpenGAExport.DifferentialGeometry.Analysis.Integration.Measure.FamilyDefs.instance_33

lemma traceTimeDerivMetric_eq
    (g_fam : ℝ → SmoothRiemannianMetric I M) (t : ℝ) (x : M) :
    traceTimeDerivMetric (I := I) g_fam t x =
      Matrix.trace ((chartGramMatrix (I := I) (g_fam t) x x)⁻¹ *
        (Matrix.of fun i j =>
          deriv (fun s => chartGramMatrix (I := I) (g_fam s) x x i j) t)) := rfl

end Measure

end Integral

end DifferentialGeometry

end

end

section

noncomputable section

open Bundle Manifold Set MeasureTheory Matrix

open scoped Manifold Topology ContDiff ENNReal Matrix BigOperators

namespace DifferentialGeometry

namespace Integral

namespace Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [local instance] _root_.OpenGAExport.DifferentialGeometry.Analysis.Integration.Measure.FamilyDecomposition.instance_29

attribute [local instance] _root_.OpenGAExport.DifferentialGeometry.Analysis.Integration.Measure.FamilyDecomposition.instance_30

attribute [local instance] _root_.OpenGAExport.DifferentialGeometry.Analysis.Integration.Measure.FamilyDecomposition.instance_31

attribute [local instance] _root_.OpenGAExport.DifferentialGeometry.Analysis.Integration.Measure.FamilyDecomposition.instance_32

lemma hasDerivAt_chartGramMatrix_entry
    {g_fam : ℝ → SmoothRiemannianMetric I M} {t₀ : ℝ}
    (hreg : MetricFamilyRegularAt (I := I) g_fam t₀)
    (x₀ : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (i j : Fin (Module.finrank ℝ E)) (t : ℝ) :
    HasDerivAt (fun s => chartGramMatrix (I := I) (g_fam s) x₀ x i j)
      (deriv (fun s => chartGramMatrix (I := I) (g_fam s) x₀ x i j) t) t :=
  hreg.hasDerivAt_chartGramMatrix x₀ i j hx t

lemma traceTimeDerivMetric_eq_trace_chartGramMatrix
    {g_fam : ℝ → SmoothRiemannianMetric I M} {t : ℝ}
    (hreg : MetricFamilyRegularAt (I := I) g_fam t)
    (α : M) {x : M}
    (hxα : x ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    traceTimeDerivMetric (I := I) g_fam t x
    = Matrix.trace ((chartGramMatrix (I := I) (g_fam t) α x)⁻¹ *
      (Matrix.of fun i j : Fin (Module.finrank ℝ E) =>
        deriv (fun s => chartGramMatrix (I := I) (g_fam s) α x i j) t)) := by
  have hxx : x ∈ (trivializationAt E (TangentSpace I) x).baseSet := by
    change x ∈ (chartAt H x).source
    exact mem_chart_source _ _
  rw [traceTimeDerivMetric_eq]
  exact trace_chartGramMatrix_inv_deriv_chart_independent
    (I := I) (M := M) hreg x α hxx hxα

end Measure

end Integral

end DifferentialGeometry

end

end

noncomputable section

open Bundle Manifold Set MeasureTheory Matrix

open scoped Manifold Topology ContDiff ENNReal Matrix BigOperators

namespace DifferentialGeometry
end DifferentialGeometry
open _root_.DifferentialGeometry

namespace DifferentialGeometry.Integral
end DifferentialGeometry.Integral
open _root_.DifferentialGeometry
open _root_.DifferentialGeometry.Integral

namespace DifferentialGeometry.Integral.Measure
end DifferentialGeometry.Integral.Measure
open _root_.DifferentialGeometry
open _root_.DifferentialGeometry.Integral
open _root_.DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [local instance] _root_.OpenGAExport.DifferentialGeometry.Analysis.Integration.Measure.Family.instance_30

attribute [local instance] _root_.OpenGAExport.DifferentialGeometry.Analysis.Integration.Measure.Family.instance_31

attribute [local instance] _root_.OpenGAExport.DifferentialGeometry.Analysis.Integration.Measure.Family.instance_32

attribute [local instance] _root_.OpenGAExport.DifferentialGeometry.Analysis.Integration.Measure.Family.instance_33

variable {g_fam : ℝ → SmoothRiemannianMetric I M}

namespace DifferentialGeometry.Integral.Measure
end DifferentialGeometry.Integral.Measure
open _root_.DifferentialGeometry.Integral.Measure

lemma solution
    {g_fam : ℝ → SmoothRiemannianMetric I M} {t : ℝ}
    (hreg : MetricFamilyRegularAt (I := I) g_fam t)
    (α : M) {x : M}
    (hxα : x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (f : ℝ → M → ℝ) (ρ : M → ℝ)
    (hf : HasDerivAt (fun s : ℝ => f s x) (deriv (fun s : ℝ => f s x) t) t) :
    HasDerivAt
      (fun s : ℝ => f s x * ρ x *
        chartDensity (I := I) (g_fam s) α x)
      ((deriv (fun s : ℝ => f s x) t +
          (1/2) * traceTimeDerivMetric (I := I) g_fam t x * f t x) * ρ x *
        chartDensity (I := I) (g_fam t) α x) t := by
  classical
  set n := Fin (Module.finrank ℝ E) with hn_def
  have hG : ∀ i j : n,
      HasDerivAt (fun s => chartGramMatrixFamily (I := I) g_fam α x s i j)
        (deriv (fun s => chartGramMatrixFamily (I := I) g_fam α x s i j) t) t := by
    intro i j
    exact hasDerivAt_chartGramMatrix_entry (I := I) (M := M) hreg α hxα i j t
  have hdensity_deriv :
      HasDerivAt
        (fun s : ℝ => chartDensity (I := I) (g_fam s) α x)
        ((1 / 2) *
          Matrix.trace ((chartGramMatrixFamily (I := I) g_fam α x t)⁻¹ *
            (Matrix.of fun i j : n =>
              deriv (fun s => chartGramMatrixFamily (I := I) g_fam α x s i j) t)) *
          Real.sqrt (chartGramMatrixFamily (I := I) g_fam α x t).det) t := by
    have := hasDerivAt_chartDensityFamily_eq_half_trace_inv_mul
      (I := I) (M := M) g_fam α t (x := x) hxα
      (Matrix.of fun i j : n =>
        deriv (fun s => chartGramMatrixFamily (I := I) g_fam α x s i j) t)
      (by
        intro i j
        exact hG i j)
    change HasDerivAt (fun s => chartDensity (I := I) (g_fam s) α x) _ t
    exact this
  have htrace :
      Matrix.trace ((chartGramMatrixFamily (I := I) g_fam α x t)⁻¹ *
        (Matrix.of fun i j : n =>
          deriv (fun s => chartGramMatrixFamily (I := I) g_fam α x s i j) t))
        = traceTimeDerivMetric (I := I) g_fam t x := by
    change Matrix.trace ((chartGramMatrix (I := I) (g_fam t) α x)⁻¹ *
        (Matrix.of fun i j : n =>
          deriv (fun s => chartGramMatrix (I := I) (g_fam s) α x i j) t))
      = traceTimeDerivMetric (I := I) g_fam t x
    rw [traceTimeDerivMetric_eq_trace_chartGramMatrix
      (I := I) (M := M) hreg α hxα]
  have hdensity_val :
      chartDensity (I := I) (g_fam t) α x
        = Real.sqrt (chartGramMatrixFamily (I := I) g_fam α x t).det := by
    rfl
  have hdensity_deriv' :
      HasDerivAt
        (fun s : ℝ => chartDensity (I := I) (g_fam s) α x)
        ((1 / 2) * traceTimeDerivMetric (I := I) g_fam t x *
          chartDensity (I := I) (g_fam t) α x) t := by
    rw [hdensity_val]
    have := hdensity_deriv
    rw [htrace] at this
    exact this
  have hfρ : HasDerivAt (fun s : ℝ => f s x * ρ x)
      (deriv (fun s : ℝ => f s x) t * ρ x) t :=
    hf.mul_const (ρ x)
  have hprod := hfρ.mul hdensity_deriv'
  have halgebra :
      (deriv (fun s : ℝ => f s x) t * ρ x) *
          chartDensity (I := I) (g_fam t) α x
        + (f t x * ρ x) *
          ((1 / 2) * traceTimeDerivMetric (I := I) g_fam t x *
            chartDensity (I := I) (g_fam t) α x)
      = (deriv (fun s : ℝ => f s x) t +
          (1/2) * traceTimeDerivMetric (I := I) g_fam t x * f t x) * ρ x *
          chartDensity (I := I) (g_fam t) α x := by
    ring
  rw [← halgebra]
  exact hprod
