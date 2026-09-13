import Theorems.Thm_DifferentialGeometry_Integral_Measure_chartGramMatrix_dotProduct_mulVec
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
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Map
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

lemma chartBasisFamily_apply (x₀ : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (i : Fin (Module.finrank ℝ E)) :
    chartBasisFamily (I := I) x₀ hx i =
      chartBasisVecFiber (I := I) x₀ i x := by
  unfold chartBasisFamily chartBasisVecFiber
  rw [Module.Basis.map_apply]
  exact congrFun ((trivializationAt E (TangentSpace I) x₀).symm_continuousLinearEquivAt_eq hx)
    ((chartModelBasis E) i)

lemma chartBasisFamily_linearIndependent (x₀ : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    LinearIndependent ℝ
      (fun i : Fin (Module.finrank ℝ E) =>
        chartBasisVecFiber (I := I) x₀ i x) := by
  have h := (chartBasisFamily (I := I) x₀ hx).linearIndependent
  have hcongr : (chartBasisFamily (I := I) x₀ hx : Fin (Module.finrank ℝ E) → TangentSpace I x)
      = fun i => chartBasisVecFiber (I := I) x₀ i x := by
    funext i
    exact chartBasisFamily_apply (I := I) x₀ hx i
  rw [← hcongr]
  exact h

@[simp] lemma chartGramMatrix_apply
    (g : SmoothRiemannianMetric I M) (x₀ : M) (x : M)
    (i j : Fin (Module.finrank ℝ E)) :
    chartGramMatrix g x₀ x i j =
      g.inner x
        (chartBasisVecFiber (I := I) x₀ i x)
        (chartBasisVecFiber (I := I) x₀ j x) := rfl

lemma chartGramMatrix_isHermitian
    (g : SmoothRiemannianMetric I M) (x₀ : M) (x : M) :
    (chartGramMatrix g x₀ x).IsHermitian := by
  refine Matrix.IsHermitian.ext ?_
  intro i j
  show star (chartGramMatrix g x₀ x j i) = chartGramMatrix g x₀ x i j
  rw [chartGramMatrix_apply, chartGramMatrix_apply, star_trivial]
  exact g.symm x
    (chartBasisVecFiber (I := I) x₀ j x)
    (chartBasisVecFiber (I := I) x₀ i x)

end Measure

end Integral

end DifferentialGeometry

end

end

noncomputable section

open Bundle Manifold Set MeasureTheory

open scoped Manifold Topology ContDiff Matrix

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

attribute [local instance] _root_.OpenGAExport.DifferentialGeometry.Geometry.Metric.ChartGram.instance_40

attribute [local instance] _root_.OpenGAExport.DifferentialGeometry.Geometry.Metric.ChartGram.instance_41

attribute [local instance] _root_.OpenGAExport.DifferentialGeometry.Geometry.Metric.ChartGram.instance_42

attribute [local instance] _root_.OpenGAExport.DifferentialGeometry.Geometry.Metric.ChartGram.instance_43

export DifferentialGeometry (SmoothRiemannianMetric)

namespace DifferentialGeometry.Integral.Measure
end DifferentialGeometry.Integral.Measure
open _root_.DifferentialGeometry.Integral.Measure

lemma solution
    (g : SmoothRiemannianMetric I M) (x₀ : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    (chartGramMatrix g x₀ x).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos
    (chartGramMatrix_isHermitian (I := I) g x₀ x) ?_
  intro c hc
  set w : TangentSpace I x :=
    ∑ i, c i • chartBasisVecFiber (I := I) x₀ i x with hw_def
  have heq := chartGramMatrix_dotProduct_mulVec (I := I) g x₀ x c
  rw [heq]
  have hwnz : w ≠ 0 := by
    intro hw0
    have hli := chartBasisFamily_linearIndependent (I := I) x₀ hx
    rw [Fintype.linearIndependent_iff] at hli
    have : c = 0 := funext (hli c hw0)
    exact hc this
  exact g.pos x w hwnz
