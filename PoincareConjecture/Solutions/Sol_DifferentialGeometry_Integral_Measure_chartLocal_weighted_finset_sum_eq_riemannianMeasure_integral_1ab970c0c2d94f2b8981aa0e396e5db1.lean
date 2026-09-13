import Theorems.Thm_DifferentialGeometry_Integral_Measure_integral_riemannianVolumeMeasure_eq_finset_sum
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

theorem solution
    [T2Space M] [CompactSpace M]
    (g_fam : ℝ → SmoothRiemannianMetric I M) (t : ℝ)
    (h : M → ℝ) (hh_cont : Continuous h) :
    ∑ α ∈ chartAtlasPOUFinset (I := I) (M := M),
        ∫ x, h x * (chartAtlasPOU I M) α x
          ∂(chartLocalMeasure (I := I) (g_fam t) α)
      = ∫ x, h x ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t) := by
  classical
  rw [riemannianMeasureFamily_def]
  rw [integral_riemannianVolumeMeasure_eq_finset_sum (I := I) (M := M)
      (g_fam t) h hh_cont]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  set ρ : M → ℝ := fun x => (chartAtlasPOU I M) α x with hρ_def
  have hρ_cont : Continuous ρ := ((chartAtlasPOU I M) α).contMDiff.continuous
  have hρ_nonneg : ∀ x, 0 ≤ ρ x := fun x => (chartAtlasPOU I M).nonneg _ _
  have hρ_ae : AEMeasurable (fun x : M => ENNReal.ofReal (ρ x))
      (chartLocalMeasure (I := I) (g_fam t) α) := by
    exact (ENNReal.measurable_ofReal.comp hρ_cont.measurable).aemeasurable
  have hρ_lt_top : ∀ᵐ x ∂(chartLocalMeasure (I := I) (g_fam t) α),
      ENNReal.ofReal (ρ x) < ⊤ :=
    Filter.Eventually.of_forall (fun _ => by simp)
  have hswap :
      ∫ x, h x
          ∂((chartLocalMeasure (I := I) (g_fam t) α).withDensity
              (fun y : M => ENNReal.ofReal (ρ y)))
        = ∫ x, (ENNReal.ofReal (ρ x)).toReal • h x
            ∂(chartLocalMeasure (I := I) (g_fam t) α) :=
    integral_withDensity_eq_integral_toReal_smul₀
      (μ := chartLocalMeasure (I := I) (g_fam t) α)
      (f := fun y : M => ENNReal.ofReal (ρ y)) hρ_ae hρ_lt_top
      (g := h)
  have htoReal : ∀ x, (ENNReal.ofReal (ρ x)).toReal = ρ x := fun x =>
    ENNReal.toReal_ofReal (hρ_nonneg x)
  have hsmul : ∀ x, (ENNReal.ofReal (ρ x)).toReal • h x = h x * ρ x := fun x => by
    rw [htoReal x, smul_eq_mul, mul_comm]
  have hintegrand_eq :
      (fun x : M => (ENNReal.ofReal (ρ x)).toReal • h x)
        = fun x : M => h x * ρ x := by
    funext x; exact hsmul x
  rw [hswap, hintegrand_eq]
