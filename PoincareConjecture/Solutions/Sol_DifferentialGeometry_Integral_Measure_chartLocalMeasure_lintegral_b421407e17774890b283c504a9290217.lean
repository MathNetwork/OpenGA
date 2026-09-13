import Theorems.Thm_DifferentialGeometry_Integral_Measure_aemeasurable_chartDensity_symm_pullback
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

theorem solution
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    {F : M → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x, F x ∂(chartLocalMeasure (I := I) g x₀) =
      ∫⁻ y in (extChartAt I x₀).target,
        ENNReal.ofReal (chartDensity g x₀ ((extChartAt I x₀).symm y)) *
          F ((extChartAt I x₀).symm y) ∂ (modelHaar (E := E)) := by
  unfold chartLocalMeasure
  have htarget_meas : MeasurableSet (extChartAt I x₀).target :=
    measurableSet_extChartAt_target (I := I) x₀
  have haem_base : AEMeasurable (extChartAt I x₀).symm
      ((modelHaar (E := E)).restrict (extChartAt I x₀).target) :=
    aemeasurable_extChartAt_symm_restrict_target (I := I) (E := E) x₀
  have hw_aem : AEMeasurable
      (fun y : E =>
        ENNReal.ofReal (chartDensity g x₀ ((extChartAt I x₀).symm y)))
      ((modelHaar (E := E)).restrict (extChartAt I x₀).target) :=
    aemeasurable_chartDensity_symm_pullback (I := I) g x₀
  have hwd_ac :
      (((modelHaar (E := E)).restrict (extChartAt I x₀).target).withDensity
          (fun y : E =>
            ENNReal.ofReal (chartDensity g x₀ ((extChartAt I x₀).symm y))))
        ≪ (modelHaar (E := E)).restrict (extChartAt I x₀).target :=
    MeasureTheory.withDensity_absolutelyContinuous _ _
  have haem : AEMeasurable (extChartAt I x₀).symm
      (((modelHaar (E := E)).restrict (extChartAt I x₀).target).withDensity
        (fun y : E =>
          ENNReal.ofReal (chartDensity g x₀ ((extChartAt I x₀).symm y)))) :=
    haem_base.mono_ac hwd_ac
  rw [MeasureTheory.lintegral_map' hF.aemeasurable haem]
  have hcomp :=
    MeasureTheory.lintegral_withDensity_eq_lintegral_mul₀
      (μ := (modelHaar (E := E)).restrict (extChartAt I x₀).target) hw_aem
      (g := fun y : E => F ((extChartAt I x₀).symm y))
      (hF.aemeasurable.comp_aemeasurable haem_base)
  simp only [Pi.mul_apply] at hcomp
  rw [hcomp]
