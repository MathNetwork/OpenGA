import Theorems.Thm_DifferentialGeometry_Integral_Measure_deriv_chartGramMatrix_pullback
import Theorems.Thm_DifferentialGeometry_Integral_Measure_transitionMatrix_mul_reverse
import Theorems.Thm_DifferentialGeometry_Integral_Measure_chartGramMatrix_pullback_eq_sum
import Theorems.Thm_DifferentialGeometry_Integral_Measure_chartGramMatrix_posDef
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

open Bundle Manifold Set MeasureTheory

open scoped Manifold Topology ContDiff Matrix

namespace DifferentialGeometry

namespace Integral

namespace Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [local instance] _root_.OpenGAExport.DifferentialGeometry.Geometry.Metric.ChartGram.instance_40

attribute [local instance] _root_.OpenGAExport.DifferentialGeometry.Geometry.Metric.ChartGram.instance_41

attribute [local instance] _root_.OpenGAExport.DifferentialGeometry.Geometry.Metric.ChartGram.instance_42

attribute [local instance] _root_.OpenGAExport.DifferentialGeometry.Geometry.Metric.ChartGram.instance_43

export DifferentialGeometry (SmoothRiemannianMetric)

lemma chartGramMatrix_det_pos
    (g : SmoothRiemannianMetric I M) (x₀ : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    0 < (chartGramMatrix g x₀ x).det :=
  (chartGramMatrix_posDef (I := I) g x₀ hx).det_pos

end Measure

end Integral

end DifferentialGeometry

end

end

section

noncomputable section

open Bundle Manifold Set MeasureTheory

open scoped Manifold Topology ContDiff ENNReal Matrix

namespace DifferentialGeometry

namespace Integral

namespace Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [local instance] _root_.OpenGAExport.DifferentialGeometry.Analysis.Integration.Measure.Invariance.instance_28

attribute [local instance] _root_.OpenGAExport.DifferentialGeometry.Analysis.Integration.Measure.Invariance.instance_29

attribute [local instance] _root_.OpenGAExport.DifferentialGeometry.Analysis.Integration.Measure.Invariance.instance_30

attribute [local instance] _root_.OpenGAExport.DifferentialGeometry.Analysis.Integration.Measure.Invariance.instance_31

lemma chartGramMatrix_pullback_eq_mul
    (g : SmoothRiemannianMetric I M) (x₀ x₁ : M) {x : M}
    (hx0 : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (hx1 : x ∈ (trivializationAt E (TangentSpace I) x₁).baseSet) :
    chartGramMatrix g x₁ x =
      (transitionMatrix (I := I) x₀ x₁ x)ᵀ *
        chartGramMatrix g x₀ x *
        transitionMatrix (I := I) x₀ x₁ x := by
  ext i j
  rw [chartGramMatrix_pullback_eq_sum (I := I) g x₀ x₁ hx0 hx1 i j]
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro l _
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro k _
  ring

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

section ChartInvarianceOfTraceTimeDeriv

lemma transitionMatrix_isUnit
    (x₀ x₁ : M) {x : M}
    (hx0 : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (hx1 : x ∈ (trivializationAt E (TangentSpace I) x₁).baseSet) :
    IsUnit (transitionMatrix (I := I) x₀ x₁ x) := by
  have hleft : transitionMatrix (I := I) x₁ x₀ x *
      transitionMatrix (I := I) x₀ x₁ x = 1 :=
    transitionMatrix_mul_reverse (I := I) x₁ x₀ hx1 hx0
  have hdet : (transitionMatrix (I := I) x₀ x₁ x).det *
      (transitionMatrix (I := I) x₁ x₀ x).det = 1 := by
    rw [mul_comm, ← Matrix.det_mul, hleft, Matrix.det_one]
  exact (Matrix.isUnit_iff_isUnit_det _).mpr
    (IsUnit.of_mul_eq_one _ hdet)

end ChartInvarianceOfTraceTimeDeriv

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
    Matrix.trace ((chartGramMatrix (I := I) (g_fam t) x₀ x)⁻¹ *
      (Matrix.of fun i j : Fin (Module.finrank ℝ E) =>
        deriv (fun s => chartGramMatrix (I := I) (g_fam s) x₀ x i j) t))
    = Matrix.trace ((chartGramMatrix (I := I) (g_fam t) x₁ x)⁻¹ *
      (Matrix.of fun i j : Fin (Module.finrank ℝ E) =>
        deriv (fun s => chartGramMatrix (I := I) (g_fam s) x₁ x i j) t)) := by
  classical
  set n := Fin (Module.finrank ℝ E) with hn_def
  set J : Matrix n n ℝ := transitionMatrix (I := I) x₀ x₁ x with hJ_def
  set G₀ : Matrix n n ℝ := chartGramMatrix (I := I) (g_fam t) x₀ x with hG0_def
  set G₁ : Matrix n n ℝ := chartGramMatrix (I := I) (g_fam t) x₁ x with hG1_def
  set dG₀ : Matrix n n ℝ := Matrix.of fun i j : n =>
      deriv (fun s => chartGramMatrix (I := I) (g_fam s) x₀ x i j) t with hdG0_def
  set dG₁ : Matrix n n ℝ := Matrix.of fun i j : n =>
      deriv (fun s => chartGramMatrix (I := I) (g_fam s) x₁ x i j) t with hdG1_def
  have hG1_eq : G₁ = Jᵀ * G₀ * J :=
    chartGramMatrix_pullback_eq_mul (I := I) (g_fam t) x₀ x₁ hx0 hx1
  have hdG1_eq : dG₁ = Jᵀ * dG₀ * J :=
    deriv_chartGramMatrix_pullback (I := I) (M := M) hreg x₀ x₁ hx0 hx1
  have hJ_unit : IsUnit J :=
    transitionMatrix_isUnit (I := I) x₀ x₁ hx0 hx1
  have hG0_unit : IsUnit G₀ := by
    rw [Matrix.isUnit_iff_isUnit_det]
    have hpos : 0 < G₀.det := chartGramMatrix_det_pos (I := I) (g_fam t) x₀ hx0
    exact (ne_of_gt hpos).isUnit
  have hJT_unit : IsUnit Jᵀ := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose]
    exact (Matrix.isUnit_iff_isUnit_det _).mp hJ_unit
  have hJ_det : IsUnit J.det := (Matrix.isUnit_iff_isUnit_det _).mp hJ_unit
  have hJT_det : IsUnit (Jᵀ).det := by
    rw [Matrix.det_transpose]; exact hJ_det
  have hinv : G₁⁻¹ = J⁻¹ * G₀⁻¹ * (Jᵀ)⁻¹ := by
    rw [hG1_eq]
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev]
    simp only [Matrix.mul_assoc]
  have hJTinv : (Jᵀ)⁻¹ * Jᵀ = 1 := Matrix.nonsing_inv_mul _ hJT_det
  have hJinvJ : J * J⁻¹ = 1 := Matrix.mul_nonsing_inv _ hJ_det
  have hgoal :
      Matrix.trace (G₁⁻¹ * dG₁) = Matrix.trace (G₀⁻¹ * dG₀) := by
    rw [hinv, hdG1_eq]
    have hrw1 :
        (J⁻¹ * G₀⁻¹ * (Jᵀ)⁻¹) * (Jᵀ * dG₀ * J)
          = J⁻¹ * G₀⁻¹ * ((Jᵀ)⁻¹ * Jᵀ) * dG₀ * J := by
      simp only [Matrix.mul_assoc]
    rw [hrw1]
    rw [hJTinv]
    rw [Matrix.mul_one]
    rw [show J⁻¹ * G₀⁻¹ * dG₀ * J = (J⁻¹ * G₀⁻¹ * dG₀) * J from by
      simp only [Matrix.mul_assoc]]
    rw [Matrix.trace_mul_comm]
    rw [show J * (J⁻¹ * G₀⁻¹ * dG₀) = (J * J⁻¹) * G₀⁻¹ * dG₀ from by
      simp only [← Matrix.mul_assoc]]
    rw [hJinvJ]
    rw [Matrix.one_mul]
  linarith [hgoal]
