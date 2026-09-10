import Theorems.Thm_DifferentialGeometry_Integral_Measure_integral_riemannianVolumeMeasure_eq_finset_sum
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

attribute [local instance] _root_.OpenGAExport.DifferentialGeometry.Analysis.Integration.Measure.FamilyDefs.instance_30

attribute [local instance] _root_.OpenGAExport.DifferentialGeometry.Analysis.Integration.Measure.FamilyDefs.instance_31

attribute [local instance] _root_.OpenGAExport.DifferentialGeometry.Analysis.Integration.Measure.FamilyDefs.instance_32

attribute [local instance] _root_.OpenGAExport.DifferentialGeometry.Analysis.Integration.Measure.FamilyDefs.instance_33

lemma riemannianMeasureFamily_def
    {P : Type*}
    [T2Space M] [SigmaCompactSpace M]
    (g_fam : P → SmoothRiemannianMetric I M) (t : P) :
    riemannianMeasureFamily (I := I) (M := M) g_fam t =
      riemannianVolumeMeasure (I := I) (M := M) (g_fam t) := rfl

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

theorem volume_variation_formula_from_chart_derivs
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (f : ℝ → M → ℝ) (t : ℝ)
    (Iα : M → ℝ)
    (Iglobal : ℝ)
    (hα_deriv : ∀ α ∈ chartAtlasPOUFinset (I := I) (M := M),
      HasDerivAt
        (fun s : ℝ => ∫ x, f s x
          ∂((chartLocalMeasure (I := I) (g_fam s) α).withDensity
              (fun y : M => ENNReal.ofReal ((chartAtlasPOU I M) α y))))
        (Iα α) t)
    (hα_sum_val : ∑ α ∈ chartAtlasPOUFinset (I := I) (M := M), Iα α = Iglobal) :
    HasDerivAt
      (fun s : ℝ => ∑ α ∈ chartAtlasPOUFinset (I := I) (M := M),
        ∫ x, f s x
          ∂((chartLocalMeasure (I := I) (g_fam s) α).withDensity
              (fun y : M => ENNReal.ofReal ((chartAtlasPOU I M) α y))))
      Iglobal t := by
  rw [← hα_sum_val]
  exact HasDerivAt.fun_sum hα_deriv

theorem integral_riemannianMeasureFamily_eq_finset_sum
    {P : Type*}
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g_fam : P → SmoothRiemannianMetric I M)
    (f : P → M → ℝ) (t : P)
    (hf_cont : Continuous (f t)) :
    ∫ x, f t x ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t)
      = ∑ α ∈ chartAtlasPOUFinset (I := I) (M := M),
          ∫ x, f t x
            ∂((chartLocalMeasure (I := I) (g_fam t) α).withDensity
              (fun y : M => ENNReal.ofReal ((chartAtlasPOU I M) α y))) := by
  rw [riemannianMeasureFamily_def]
  exact integral_riemannianVolumeMeasure_eq_finset_sum (I := I) (M := M)
    (g_fam t) (f t) hf_cont

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
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (f : ℝ → M → ℝ) (t : ℝ)
    (Iα : M → ℝ) (Iglobal : ℝ)
    (hf_cont : ∀ᶠ s in 𝓝 t, Continuous (f s))
    (hα_deriv : ∀ α ∈ chartAtlasPOUFinset (I := I) (M := M),
      HasDerivAt
        (fun s : ℝ => ∫ x, f s x
          ∂((chartLocalMeasure (I := I) (g_fam s) α).withDensity
              (fun y : M => ENNReal.ofReal ((chartAtlasPOU I M) α y))))
        (Iα α) t)
    (hα_sum_val : ∑ α ∈ chartAtlasPOUFinset (I := I) (M := M), Iα α = Iglobal) :
    HasDerivAt
      (fun s : ℝ =>
        ∫ x, f s x ∂(riemannianMeasureFamily (I := I) (M := M) g_fam s))
      Iglobal t := by
  have hfun :
      (fun s : ℝ =>
          ∫ x, f s x ∂(riemannianMeasureFamily (I := I) (M := M) g_fam s))
        =ᶠ[𝓝 t]
      (fun s : ℝ => ∑ α ∈ chartAtlasPOUFinset (I := I) (M := M),
        ∫ x, f s x
          ∂((chartLocalMeasure (I := I) (g_fam s) α).withDensity
              (fun y : M => ENNReal.ofReal ((chartAtlasPOU I M) α y)))) := by
    filter_upwards [hf_cont] with s hs
    exact integral_riemannianMeasureFamily_eq_finset_sum (I := I) (M := M)
      g_fam f s hs
  refine HasDerivAt.congr_of_eventuallyEq ?_ hfun
  exact volume_variation_formula_from_chart_derivs (I := I) (M := M)
    g_fam f t Iα Iglobal hα_deriv hα_sum_val
