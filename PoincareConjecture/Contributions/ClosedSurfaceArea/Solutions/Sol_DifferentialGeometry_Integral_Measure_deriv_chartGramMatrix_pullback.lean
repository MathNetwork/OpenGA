import Theorems.Thm_DifferentialGeometry_Integral_Measure_chartGramMatrix_pullback_eq_sum
import Definitions.Def_ClosedSurface_DifferentialGeometry_Analysis_Integration_Measure_ChartDensity
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

attribute [local instance] _root_.OpenGAExport.DifferentialGeometry.Analysis.Integration.Measure.FamilyDecomposition.instance_29

attribute [local instance] _root_.OpenGAExport.DifferentialGeometry.Analysis.Integration.Measure.FamilyDecomposition.instance_30

attribute [local instance] _root_.OpenGAExport.DifferentialGeometry.Analysis.Integration.Measure.FamilyDecomposition.instance_31

attribute [local instance] _root_.OpenGAExport.DifferentialGeometry.Analysis.Integration.Measure.FamilyDecomposition.instance_32

namespace DifferentialGeometry.Integral.Measure
end DifferentialGeometry.Integral.Measure
open _root_.DifferentialGeometry.Integral.Measure

lemma solution
    {g_fam : ℝ → SmoothRiemannianMetric I M} {t : ℝ}
    (hreg : MetricFamilyRegularAt (I := I) g_fam t)
    (x₀ x₁ : M) {x : M}
    (hx0 : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (hx1 : x ∈ (trivializationAt E (TangentSpace I) x₁).baseSet) :
    (Matrix.of fun i j : Fin (Module.finrank ℝ E) =>
        deriv (fun s => chartGramMatrix (I := I) (g_fam s) x₁ x i j) t)
      = (transitionMatrix (I := I) x₀ x₁ x)ᵀ *
          (Matrix.of fun i j : Fin (Module.finrank ℝ E) =>
            deriv (fun s => chartGramMatrix (I := I) (g_fam s) x₀ x i j) t) *
          transitionMatrix (I := I) x₀ x₁ x := by
  classical
  set n := Fin (Module.finrank ℝ E) with hn_def
  set J : Matrix n n ℝ := transitionMatrix (I := I) x₀ x₁ x with hJ_def
  have hentry : ∀ (t₀ : ℝ) (i j : n),
      chartGramMatrix (I := I) (g_fam t₀) x₁ x i j
        = ∑ k, ∑ l, J k i * J l j *
            chartGramMatrix (I := I) (g_fam t₀) x₀ x k l := by
    intro t₀ i j
    exact chartGramMatrix_pullback_eq_sum (I := I) (g_fam t₀) x₀ x₁ hx0 hx1 i j
  ext i j
  have hG0_entry : ∀ k l : n,
      HasDerivAt (fun s => chartGramMatrix (I := I) (g_fam s) x₀ x k l)
        (deriv (fun s => chartGramMatrix (I := I) (g_fam s) x₀ x k l) t) t := by
    intro k l
    exact hasDerivAt_chartGramMatrix_entry (I := I) (M := M) hreg x₀ hx0 k l t
  have hsum_hasDeriv :
      HasDerivAt
        (fun s => ∑ k : n, ∑ l : n, J k i * J l j *
            chartGramMatrix (I := I) (g_fam s) x₀ x k l)
        (∑ k : n, ∑ l : n, J k i * J l j *
            deriv (fun s => chartGramMatrix (I := I) (g_fam s) x₀ x k l) t) t := by
    refine HasDerivAt.fun_sum (fun k _ => ?_)
    refine HasDerivAt.fun_sum (fun l _ => ?_)
    have hcm := (hG0_entry k l).const_mul (J k i * J l j)
    exact hcm
  have hfun_eq :
      (fun s => chartGramMatrix (I := I) (g_fam s) x₁ x i j)
        = (fun s => ∑ k : n, ∑ l : n, J k i * J l j *
            chartGramMatrix (I := I) (g_fam s) x₀ x k l) := by
    funext s
    exact hentry s i j
  have hderiv_eq :
      deriv (fun s => chartGramMatrix (I := I) (g_fam s) x₁ x i j) t
        = ∑ k : n, ∑ l : n, J k i * J l j *
            deriv (fun s => chartGramMatrix (I := I) (g_fam s) x₀ x k l) t := by
    rw [hfun_eq]
    exact hsum_hasDeriv.deriv
  change deriv (fun s => chartGramMatrix (I := I) (g_fam s) x₁ x i j) t
      = (Jᵀ *
          (Matrix.of fun i j : n =>
            deriv (fun s => chartGramMatrix (I := I) (g_fam s) x₀ x i j) t) *
          J) i j
  rw [hderiv_eq]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  ring
