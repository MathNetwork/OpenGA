
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

lemma chartModelBasis_repr_sum
    (L : E →L[ℝ] E) (i : Fin (Module.finrank ℝ E)) :
    L ((chartModelBasis E) i) =
      ∑ k, ((chartModelBasis E).repr (L ((chartModelBasis E) i)) k)
            • (chartModelBasis E) k :=
  (((chartModelBasis E).sum_repr (L ((chartModelBasis E) i)))).symm

@[simp] lemma transitionMatrix_apply (x₀ x₁ : M) (x : M)
    (k i : Fin (Module.finrank ℝ E)) :
    transitionMatrix (I := I) x₀ x₁ x k i =
      (chartModelBasis E).repr
        ((tangentCoordChange I x₁ x₀ x) ((chartModelBasis E) i)) k := rfl

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
    (x₀ x₁ : M) {x : M}
    (hx0 : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (hx1 : x ∈ (trivializationAt E (TangentSpace I) x₁).baseSet) :
    transitionMatrix (I := I) x₀ x₁ x * transitionMatrix (I := I) x₁ x₀ x = 1 := by
  classical
  ext i j
  have hx0' : x ∈ (extChartAt I x₀).source := by
    rw [extChartAt_source]
    exact hx0
  have hx1' : x ∈ (extChartAt I x₁).source := by
    rw [extChartAt_source]
    exact hx1
  have hmem : x ∈ (extChartAt I x₀).source ∩ (extChartAt I x₁).source ∩
      (extChartAt I x₀).source := ⟨⟨hx0', hx1'⟩, hx0'⟩
  have hcomp : ∀ i : Fin (Module.finrank ℝ E),
      (tangentCoordChange I x₁ x₀ x) ((tangentCoordChange I x₀ x₁ x)
          ((chartModelBasis E) i))
        = (chartModelBasis E) i := by
    intro i
    have := tangentCoordChange_comp (I := I) (𝕜 := ℝ) (E := E) (H := H) (M := M)
        (w := x₀) (x := x₁) (y := x₀) (z := x)
        (v := (chartModelBasis E) i) hmem
    rw [this]
    have hself := tangentCoordChange_self (I := I) (x := x₀) (z := x)
      (v := (chartModelBasis E) i) hx0'
    exact hself
  change (transitionMatrix (I := I) x₀ x₁ x *
      transitionMatrix (I := I) x₁ x₀ x) i j = (1 : Matrix _ _ _) i j
  simp only [Matrix.mul_apply, transitionMatrix_apply, Matrix.one_apply]
  have hexp :
      (tangentCoordChange I x₀ x₁ x) ((chartModelBasis E) j)
        = ∑ k, (chartModelBasis E).repr
            ((tangentCoordChange I x₀ x₁ x) ((chartModelBasis E) j)) k
          • (chartModelBasis E) k :=
    chartModelBasis_repr_sum (tangentCoordChange I x₀ x₁ x) j
  have hlin :
      (tangentCoordChange I x₁ x₀ x)
          (∑ k, (chartModelBasis E).repr
              ((tangentCoordChange I x₀ x₁ x) ((chartModelBasis E) j)) k
            • (chartModelBasis E) k)
        = ∑ k, (chartModelBasis E).repr
              ((tangentCoordChange I x₀ x₁ x) ((chartModelBasis E) j)) k
            • (tangentCoordChange I x₁ x₀ x) ((chartModelBasis E) k) := by
    rw [map_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [ContinuousLinearMap.map_smul]
  have heval : (tangentCoordChange I x₁ x₀ x) ((tangentCoordChange I x₀ x₁ x)
      ((chartModelBasis E) j))
      = (chartModelBasis E) j := hcomp j
  have heval' :
      ∑ k, (chartModelBasis E).repr
            ((tangentCoordChange I x₀ x₁ x) ((chartModelBasis E) j)) k
          • (tangentCoordChange I x₁ x₀ x) ((chartModelBasis E) k)
        = (chartModelBasis E) j := by
    rw [← hlin, ← hexp]; exact heval
  have happ := congrArg ((chartModelBasis E).repr · i) heval'
  simp only [map_sum, Finsupp.coe_finsetSum, Finset.sum_apply,
    map_smul, Finsupp.smul_apply, smul_eq_mul] at happ
  have hrhs : ((chartModelBasis E).repr ((chartModelBasis E) j)) i
                = if i = j then (1 : ℝ) else 0 := by
    rw [(chartModelBasis E).repr_self, Finsupp.single_apply]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij, Ne.symm hij]
  rw [← hrhs]
  rw [← happ]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  exact mul_comm _ _
