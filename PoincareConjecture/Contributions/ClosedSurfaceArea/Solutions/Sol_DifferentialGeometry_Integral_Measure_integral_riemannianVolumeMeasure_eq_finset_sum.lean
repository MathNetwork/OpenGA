import Theorems.Thm_DifferentialGeometry_Integral_Measure_riemannianVolumeMeasure_eq_finset_sum
import Theorems.Thm_DifferentialGeometry_Integral_Measure_riemannianMeasure_compact_lt_top
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

variable (I M) in
lemma chartAtlasPOU_isSubordinate [T2Space M] [SigmaCompactSpace M] :
    (chartAtlasPOU I M).IsSubordinate (fun x : M => (chartAt H x).source) :=
  (SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source I M).choose_spec

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

open Bundle Manifold Set MeasureTheory Function

open scoped Manifold Topology ContDiff ENNReal

namespace DifferentialGeometry

namespace Integral

namespace Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [local instance] _root_.OpenGAExport.DifferentialGeometry.Analysis.Integration.Measure.Properties.instance_46

attribute [local instance] _root_.OpenGAExport.DifferentialGeometry.Analysis.Integration.Measure.Properties.instance_47

attribute [local instance] _root_.OpenGAExport.DifferentialGeometry.Analysis.Integration.Measure.Properties.instance_48

attribute [local instance] _root_.OpenGAExport.DifferentialGeometry.Analysis.Integration.Measure.Properties.instance_49

theorem riemannianMeasure_isFiniteMeasureOnCompacts
    [T2Space M] (g : SmoothRiemannianMetric I M)
    (ρ : SmoothPartitionOfUnity M I M univ)
    (hρ : ρ.IsSubordinate (fun α : M => (chartAt H α).source)) :
    IsFiniteMeasureOnCompacts (riemannianMeasure (I := I) g ρ) :=
  ⟨fun _K hK => riemannianMeasure_compact_lt_top (I := I) (M := M) g ρ hρ hK⟩

theorem riemannianMeasure_isFiniteMeasure_of_compactSpace
    [T2Space M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (ρ : SmoothPartitionOfUnity M I M univ)
    (hρ : ρ.IsSubordinate (fun α : M => (chartAt H α).source)) :
    IsFiniteMeasure (riemannianMeasure (I := I) g ρ) := by
  have : IsFiniteMeasureOnCompacts (riemannianMeasure (I := I) g ρ) :=
    riemannianMeasure_isFiniteMeasureOnCompacts (I := I) (M := M) g ρ hρ
  infer_instance

theorem riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) :
    IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) := by
  rw [riemannianVolumeMeasure_def]
  exact riemannianMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
    (chartAtlasPOU I M) (chartAtlasPOU_isSubordinate I M)

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
    (g : SmoothRiemannianMetric I M)
    (h : M → ℝ)
    (hh_cont : Continuous h) :
    ∫ x, h x ∂(riemannianVolumeMeasure (I := I) (M := M) g)
      = ∑ α ∈ chartAtlasPOUFinset (I := I) (M := M),
          ∫ x, h x
            ∂((chartLocalMeasure (I := I) g α).withDensity
              (fun y : M => ENNReal.ofReal ((chartAtlasPOU I M) α y))) := by
  classical
  have hVol_eq :=
    riemannianVolumeMeasure_eq_finset_sum (I := I) (M := M) g
  have hFin :
      MeasureTheory.IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  obtain ⟨C, hC⟩ : ∃ C, ∀ x, ‖h x‖ ≤ C := by
    have hCpt := (isCompact_univ (X := M)).image hh_cont.norm
    obtain ⟨C, hCmem⟩ := hCpt.bddAbove
    refine ⟨C, fun x => hCmem ⟨x, Set.mem_univ _, rfl⟩⟩
  have hh_int : Integrable h (riemannianVolumeMeasure (I := I) (M := M) g) :=
    (integrable_const C).mono' hh_cont.aestronglyMeasurable
      (Filter.Eventually.of_forall hC)
  have hsummand_int : ∀ α ∈ chartAtlasPOUFinset (I := I) (M := M),
      Integrable h
        ((chartLocalMeasure (I := I) g α).withDensity
          (fun y : M => ENNReal.ofReal ((chartAtlasPOU I M) α y))) := by
    intro α hα
    refine hh_int.mono_measure ?_
    rw [hVol_eq]
    exact Finset.single_le_sum
      (f := fun β : M => (chartLocalMeasure (I := I) g β).withDensity
        (fun y : M => ENNReal.ofReal ((chartAtlasPOU I M) β y)))
      (s := chartAtlasPOUFinset (I := I) (M := M))
      (fun _ _ => Measure.zero_le _) hα
  conv_lhs => rw [hVol_eq]
  exact integral_finsetSum_measure hsummand_int
