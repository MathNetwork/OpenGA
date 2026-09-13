import Theorems.Thm_DifferentialGeometry_Integral_Measure_aemeasurable_chartDensity_symm_pullback
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

open scoped Manifold Topology ContDiff Matrix

namespace DifferentialGeometry

namespace Integral

namespace Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [local instance] _root_.OpenGAExport.DifferentialGeometry.Analysis.Integration.Measure.ChartDensity.instance_39

attribute [local instance] _root_.OpenGAExport.DifferentialGeometry.Analysis.Integration.Measure.ChartDensity.instance_40

attribute [local instance] _root_.OpenGAExport.DifferentialGeometry.Analysis.Integration.Measure.ChartDensity.instance_41

attribute [local instance] _root_.OpenGAExport.DifferentialGeometry.Analysis.Integration.Measure.ChartDensity.instance_42

lemma chartDensity_pos
    (g : SmoothRiemannianMetric I M) (x₀ : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    0 < chartDensity g x₀ x :=
  Real.sqrt_pos.mpr (chartGramMatrix_det_pos (I := I) g x₀ hx)

attribute [local instance] _root_.DifferentialGeometry.Integral.Measure.modelHaar_isAddHaarMeasure

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

omit [Module.Finite ℝ E] [IsManifold I ∞ M] in
lemma measurableSet_extChartAt_target (x₀ : M) :
    MeasurableSet (extChartAt I x₀).target := by
  rw [extChartAt_target (I := I)]
  refine MeasurableSet.inter ?_ ?_
  · exact (I.continuous_symm.isOpen_preimage _ (chartAt H x₀).open_target).measurableSet
  · exact I.isClosed_range.measurableSet

omit [Module.Finite ℝ E] [IsManifold I ∞ M] in
lemma extChartAt_source_eq_chartAt_source (x₀ : M) :
    (extChartAt I x₀).source = (chartAt H x₀).source := by
  rw [extChartAt_source]

omit [IsManifold I ∞ M] in
lemma aemeasurable_extChartAt_symm_restrict_target
    (x₀ : M) :
    AEMeasurable ((extChartAt I x₀).symm)
      ((modelHaar (E := E)).restrict (extChartAt I x₀).target) := by
  have htarget_meas : MeasurableSet (extChartAt I x₀).target :=
    measurableSet_extChartAt_target (I := I) x₀
  exact (continuousOn_extChartAt_symm (I := I) x₀).aemeasurable htarget_meas

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
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (h : M → ℝ)
    (hh_meas : AEStronglyMeasurable h (chartLocalMeasure (I := I) g x₀)) :
    ∫ x, h x ∂(chartLocalMeasure (I := I) g x₀)
      = ∫ y in (extChartAt I x₀).target,
          chartDensity g x₀ ((extChartAt I x₀).symm y) *
            h ((extChartAt I x₀).symm y)
          ∂(modelHaar (E := E)) := by
  have htarget_meas : MeasurableSet (extChartAt I x₀).target :=
    measurableSet_extChartAt_target (I := I) x₀
  set μ₀ : MeasureTheory.Measure E :=
    (modelHaar (E := E)).restrict (extChartAt I x₀).target with hμ₀
  set w : E → ℝ≥0∞ :=
    fun y => ENNReal.ofReal
      (chartDensity g x₀ ((extChartAt I x₀).symm y)) with hw
  set μ₁ : MeasureTheory.Measure E := μ₀.withDensity w with hμ₁
  have h_unfold :
      chartLocalMeasure (I := I) g x₀ =
        MeasureTheory.Measure.map (extChartAt I x₀).symm μ₁ := rfl
  have hh_map : AEStronglyMeasurable h
      (MeasureTheory.Measure.map (extChartAt I x₀).symm μ₁) := by
    rw [← h_unfold]
    exact hh_meas
  rw [h_unfold]
  have haem_symm : AEMeasurable ((extChartAt I x₀).symm) μ₁ := by
    have haem_base : AEMeasurable ((extChartAt I x₀).symm) μ₀ :=
      aemeasurable_extChartAt_symm_restrict_target (I := I) (E := E) x₀
    have hac : μ₁ ≪ μ₀ := by
      simpa [hμ₁] using MeasureTheory.withDensity_absolutelyContinuous (μ := μ₀) w
    exact haem_base.mono_ac hac
  have h_integral_map :
      ∫ x, h x ∂(MeasureTheory.Measure.map (extChartAt I x₀).symm μ₁)
        = ∫ y, h ((extChartAt I x₀).symm y) ∂μ₁ := by
    exact MeasureTheory.integral_map haem_symm hh_map
  rw [h_integral_map]
  have hwd_aem : AEMeasurable w μ₀ :=
    aemeasurable_chartDensity_symm_pullback (I := I) g x₀
  have hw_lt_top : ∀ᵐ y ∂μ₀, w y < (⊤ : ℝ≥0∞) := by
    refine Filter.Eventually.of_forall (fun y => ?_)
    simp [hw]
  have h_withDensity :
      ∫ y, h ((extChartAt I x₀).symm y) ∂μ₁
        = ∫ y, (w y).toReal • h ((extChartAt I x₀).symm y) ∂μ₀ := by
    simpa [hμ₁] using
      integral_withDensity_eq_integral_toReal_smul₀ (μ := μ₀)
        (f := w) hwd_aem hw_lt_top
        (g := fun y : E => h ((extChartAt I x₀).symm y))
  rw [h_withDensity]
  have hw_toReal : ∀ y ∈ (extChartAt I x₀).target,
      (w y).toReal = chartDensity g x₀ ((extChartAt I x₀).symm y) := by
    intro y hy
    have hsource : (extChartAt I x₀).symm y ∈ (chartAt H x₀).source := by
      have := (extChartAt I x₀).map_target hy
      rw [extChartAt_source_eq_chartAt_source (I := I)] at this
      exact this
    have hbase : (extChartAt I x₀).symm y ∈
        (trivializationAt E (TangentSpace I) x₀).baseSet := hsource
    have hpos : 0 < chartDensity g x₀ ((extChartAt I x₀).symm y) :=
      chartDensity_pos (I := I) g x₀ hbase
    change (ENNReal.ofReal (chartDensity g x₀ ((extChartAt I x₀).symm y))).toReal
        = chartDensity g x₀ ((extChartAt I x₀).symm y)
    exact ENNReal.toReal_ofReal hpos.le
  have h_restrict :
      ∫ y, (w y).toReal • h ((extChartAt I x₀).symm y) ∂μ₀
        = ∫ y in (extChartAt I x₀).target,
            (w y).toReal • h ((extChartAt I x₀).symm y)
          ∂(modelHaar (E := E)) := by
    simp [hμ₀]
  rw [h_restrict]
  refine setIntegral_congr_fun htarget_meas (fun y hy => ?_)
  rw [hw_toReal y hy, smul_eq_mul]
