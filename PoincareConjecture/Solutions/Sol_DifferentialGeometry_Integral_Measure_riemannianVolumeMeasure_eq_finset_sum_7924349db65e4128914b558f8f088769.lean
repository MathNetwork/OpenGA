
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

open scoped Manifold Topology ContDiff ENNReal

namespace DifferentialGeometry

namespace Integral

namespace Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [local instance] _root_.OpenGAExport.DifferentialGeometry.Analysis.Integration.Measure.RiemannianMeasure.instance_21

attribute [local instance] _root_.OpenGAExport.DifferentialGeometry.Analysis.Integration.Measure.RiemannianMeasure.instance_22

attribute [local instance] _root_.OpenGAExport.DifferentialGeometry.Analysis.Integration.Measure.RiemannianMeasure.instance_23

attribute [local instance] _root_.OpenGAExport.DifferentialGeometry.Analysis.Integration.Measure.RiemannianMeasure.instance_24

lemma riemannianMeasure_def
    (g : SmoothRiemannianMetric I M)
    (ρ : SmoothPartitionOfUnity M I M univ) :
    riemannianMeasure (I := I) g ρ =
      MeasureTheory.Measure.sum (fun α : M =>
        (chartLocalMeasure (I := I) g α).withDensity
          (fun x : M => ENNReal.ofReal (ρ α x))) := rfl

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

lemma riemannianVolumeMeasure_def
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) :
    riemannianVolumeMeasure (I := I) (M := M) g =
      riemannianMeasure (I := I) g (chartAtlasPOU I M) := rfl

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

lemma chartAtlasPOU_finset_mem
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] {α : M} :
    α ∈ chartAtlasPOUFinset (I := I) (M := M) ↔
      (Function.support ((chartAtlasPOU I M) α)).Nonempty := by
  unfold chartAtlasPOUFinset
  rw [Set.Finite.mem_toFinset]
  rfl

lemma chartAtlasPOU_weight_zero_of_notMem
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {α : M} (hα : α ∉ chartAtlasPOUFinset (I := I) (M := M)) (x : M) :
    (chartAtlasPOU I M) α x = 0 := by
  rw [chartAtlasPOU_finset_mem] at hα
  rw [Set.not_nonempty_iff_eq_empty] at hα
  by_contra hne
  have hx : x ∈ Function.support ((chartAtlasPOU I M) α) := hne
  rw [hα] at hx
  exact (Set.notMem_empty _) hx

lemma chartAtlasPOU_withDensity_zero_of_notMem
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {α : M} (hα : α ∉ chartAtlasPOUFinset (I := I) (M := M)) :
    (chartLocalMeasure (I := I) g α).withDensity
        (fun x : M => ENNReal.ofReal ((chartAtlasPOU I M) α x)) = 0 := by
  have hzero : (fun x : M => ENNReal.ofReal ((chartAtlasPOU I M) α x)) = 0 := by
    funext x
    rw [chartAtlasPOU_weight_zero_of_notMem (I := I) (M := M) hα x]
    simp
  rw [hzero, MeasureTheory.withDensity_zero]

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

theorem solution
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) :
    riemannianVolumeMeasure (I := I) (M := M) g =
      ∑ α ∈ chartAtlasPOUFinset (I := I) (M := M),
        (chartLocalMeasure (I := I) g α).withDensity
          (fun x : M => ENNReal.ofReal ((chartAtlasPOU I M) α x)) := by
  rw [riemannianVolumeMeasure_def, riemannianMeasure_def]
  set S : Finset M := chartAtlasPOUFinset (I := I) (M := M) with hS
  set f : M → MeasureTheory.Measure M := fun α =>
      (chartLocalMeasure (I := I) g α).withDensity
        (fun x : M => ENNReal.ofReal ((chartAtlasPOU I M) α x)) with hf
  have hsplit : ((MeasureTheory.Measure.sum fun i : (S : Set M) => f i) +
      MeasureTheory.Measure.sum (fun i : ↥((S : Set M)ᶜ) => f i)) =
      MeasureTheory.Measure.sum f :=
    MeasureTheory.Measure.sum_add_sum_compl (S : Set M) f
  have hcompl : MeasureTheory.Measure.sum (fun i : ↥((S : Set M)ᶜ) => f i) = 0 := by
    have hzero : ∀ i : ↥((S : Set M)ᶜ), f i = 0 := by
      intro i
      have hi : (i : M) ∉ S := i.2
      exact chartAtlasPOU_withDensity_zero_of_notMem (I := I) (M := M) g hi
    ext t ht
    rw [MeasureTheory.Measure.sum_apply _ ht]
    simp [hzero]
  rw [← hsplit, hcompl, add_zero]
  exact MeasureTheory.Measure.sum_coe_finset S f
