
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

lemma trivializationAt_chartBasisVec_snd
    (x₀ : M) (i : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    (trivializationAt E (TangentSpace I) x₀
        ⟨x, chartBasisVecFiber (I := I) x₀ i x⟩).2
      = (chartModelBasis E) i := by
  have h := (trivializationAt E (TangentSpace I) x₀).apply_mk_symm hx
    ((chartModelBasis E) i)
  rw [chartBasisVecFiber, Trivialization.symmL_apply _ hx]
  exact congrArg Prod.snd h

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
    (x₀ : M) (i : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (chartBasisVec (I := I) x₀ i)
      (trivializationAt E (TangentSpace I) x₀).baseSet := by
  have hiff :=
    ((trivializationAt E (TangentSpace I) x₀)).contMDiffOn_section_baseSet_iff
      (IB := I) (n := ∞) (s := fun x => chartBasisVecFiber (I := I) x₀ i x)
  refine hiff.mpr ?_
  have hconst : ContMDiffOn I 𝓘(ℝ, E) ∞
      (fun _ : M => (chartModelBasis E) i)
      (trivializationAt E (TangentSpace I) x₀).baseSet :=
    contMDiffOn_const
  refine hconst.congr ?_
  intro x hx
  exact (trivializationAt_chartBasisVec_snd (I := I) x₀ i hx)
