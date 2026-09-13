import Theorems.Thm_DifferentialGeometry_Integral_Measure_chartBasisVecFiber_pullback
import Definitions.Def_ClosedSurface_DifferentialGeometry_Analysis_Integration_Measure_ChartDensity
import Definitions.Def_ClosedSurface_DifferentialGeometry_Analysis_Integration_Measure_Invariance
import Definitions.Def_ClosedSurface_DifferentialGeometry_Analysis_Integration_Measure_RiemannianMeasure
import Definitions.Def_ClosedSurface_DifferentialGeometry_Bundle_TangentSpace
import Definitions.Def_ClosedSurface_DifferentialGeometry_Geometry_Metric_ChartGram
import Definitions.Def_OpenGA_ImmersedMetric
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Matrix.Mul
import Mathlib.Geometry.Manifold.Algebra.Monoid
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Topology.Algebra.Module.Equiv


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

@[simp] lemma chartGramMatrix_apply
    (g : SmoothRiemannianMetric I M) (x₀ : M) (x : M)
    (i j : Fin (Module.finrank ℝ E)) :
    chartGramMatrix g x₀ x i j =
      g.inner x
        (chartBasisVecFiber (I := I) x₀ i x)
        (chartBasisVecFiber (I := I) x₀ j x) := rfl

end Measure

end Integral

end DifferentialGeometry

end

end

noncomputable section

open Bundle Manifold Set MeasureTheory

open scoped Manifold Topology ContDiff ENNReal Matrix

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

attribute [local instance] _root_.OpenGAExport.DifferentialGeometry.Analysis.Integration.Measure.Invariance.instance_28

attribute [local instance] _root_.OpenGAExport.DifferentialGeometry.Analysis.Integration.Measure.Invariance.instance_29

attribute [local instance] _root_.OpenGAExport.DifferentialGeometry.Analysis.Integration.Measure.Invariance.instance_30

attribute [local instance] _root_.OpenGAExport.DifferentialGeometry.Analysis.Integration.Measure.Invariance.instance_31

namespace DifferentialGeometry.Integral.Measure
end DifferentialGeometry.Integral.Measure
open _root_.DifferentialGeometry.Integral.Measure

lemma solution
    (g : SmoothRiemannianMetric I M) (x₀ x₁ : M) {x : M}
    (hx0 : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (hx1 : x ∈ (trivializationAt E (TangentSpace I) x₁).baseSet)
    (i j : Fin (Module.finrank ℝ E)) :
    chartGramMatrix g x₁ x i j =
      ∑ k, ∑ l,
        (transitionMatrix (I := I) x₀ x₁ x k i) *
        (transitionMatrix (I := I) x₀ x₁ x l j) *
        chartGramMatrix g x₀ x k l := by
  have hlhs :
      chartGramMatrix g x₁ x i j =
        g.inner x
          (chartBasisVecFiber (I := I) x₁ i x)
          (chartBasisVecFiber (I := I) x₁ j x) := rfl
  rw [hlhs]
  rw [chartBasisVecFiber_pullback (I := I) x₀ x₁ hx0 hx1 i]
  rw [chartBasisVecFiber_pullback (I := I) x₀ x₁ hx0 hx1 j]
  have hL :
      g.inner x
          (∑ k, transitionMatrix (I := I) x₀ x₁ x k i •
            chartBasisVecFiber (I := I) x₀ k x)
        = ∑ k, transitionMatrix (I := I) x₀ x₁ x k i •
            g.inner x (chartBasisVecFiber (I := I) x₀ k x) := by
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [map_smul]
  rw [hL]
  rw [sum_apply]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [smul_apply]
  have hR :
      g.inner x (chartBasisVecFiber (I := I) x₀ k x)
          (∑ l, transitionMatrix (I := I) x₀ x₁ x l j •
            chartBasisVecFiber (I := I) x₀ l x)
        = ∑ l, transitionMatrix (I := I) x₀ x₁ x l j *
            g.inner x (chartBasisVecFiber (I := I) x₀ k x)
              (chartBasisVecFiber (I := I) x₀ l x) := by
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro l _
    rw [map_smul]
    rw [smul_eq_mul]
  rw [hR, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro l _
  rw [chartGramMatrix_apply]
  ring
