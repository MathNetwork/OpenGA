import Theorems.Thm_DifferentialGeometry_Integral_Measure_chartLocalMeasure_lintegral
import Theorems.Thm_DifferentialGeometry_Integral_Measure_chartGramMatrix_posDef
import Theorems.Thm_DifferentialGeometry_Integral_Measure_chartGramMatrix_det_contMDiffOn
import Definitions.Def_ClosedSurface_DifferentialGeometry_Analysis_Integration_Measure_ChartDensity
import Definitions.Def_ClosedSurface_DifferentialGeometry_Analysis_Integration_Measure_Invariance
import Definitions.Def_ClosedSurface_DifferentialGeometry_Analysis_Integration_Measure_Properties
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
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.Metrizable
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

lemma chartDensity_contMDiffOn
    (g : SmoothRiemannianMetric I M) (x₀ : M) :
    ContMDiffOn I 𝓘(ℝ) ∞ (chartDensity g x₀)
      (trivializationAt E (TangentSpace I) x₀).baseSet := by
  intro x hx
  have hdet := chartGramMatrix_det_contMDiffOn (I := I) g x₀ x hx
  have hpos_ne : (chartGramMatrix (I := I) g x₀ x).det ≠ 0 :=
    ne_of_gt (chartGramMatrix_det_pos (I := I) g x₀ hx)
  have hsqrt : ContDiffAt ℝ ∞ Real.sqrt
      (chartGramMatrix (I := I) g x₀ x).det :=
    Real.contDiffAt_sqrt hpos_ne
  have := hsqrt.comp_contMDiffWithinAt (f :=
      fun y : M => (chartGramMatrix (I := I) g x₀ y).det) hdet
  exact this

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

lemma chartDensity_continuousOn
    (g : SmoothRiemannianMetric I M) (x₀ : M) :
    ContinuousOn (chartDensity g x₀)
      (trivializationAt E (TangentSpace I) x₀).baseSet :=
  (chartDensity_contMDiffOn (I := I) g x₀).continuousOn

end Measure

end Integral

end DifferentialGeometry

end

end

noncomputable section

open Bundle Manifold Set MeasureTheory Function

open scoped Manifold Topology ContDiff ENNReal

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

attribute [local instance] _root_.OpenGAExport.DifferentialGeometry.Analysis.Integration.Measure.Properties.instance_46

attribute [local instance] _root_.OpenGAExport.DifferentialGeometry.Analysis.Integration.Measure.Properties.instance_47

attribute [local instance] _root_.OpenGAExport.DifferentialGeometry.Analysis.Integration.Measure.Properties.instance_48

attribute [local instance] _root_.OpenGAExport.DifferentialGeometry.Analysis.Integration.Measure.Properties.instance_49

namespace DifferentialGeometry.Integral.Measure
end DifferentialGeometry.Integral.Measure
open _root_.DifferentialGeometry.Integral.Measure

theorem solution
    [T2Space M]
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    {K : Set M} (hK : IsCompact K) (hKsub : K ⊆ (chartAt H x₀).source) :
    chartLocalMeasure (I := I) g x₀ K < (⊤ : ℝ≥0∞) := by
  classical
  have hKmeas : MeasurableSet K := hK.isClosed.measurableSet
  have hind_meas : Measurable (fun x : M => K.indicator (fun _ => (1 : ℝ≥0∞)) x) :=
    (measurable_const).indicator hKmeas
  have hlint := chartLocalMeasure_lintegral (I := I) (M := M) g x₀ hind_meas
  have hmeas_eq : chartLocalMeasure (I := I) g x₀ K =
      ∫⁻ x, K.indicator (fun _ => (1 : ℝ≥0∞)) x ∂ chartLocalMeasure (I := I) g x₀ := by
    rw [lintegral_indicator hKmeas, setLIntegral_const,
        one_mul]
  rw [hmeas_eq, hlint]
  set T : Set E := (extChartAt I x₀).target with hT_def
  set KE : Set E := (extChartAt I x₀) '' K with hKE_def
  have hT_meas : MeasurableSet T := measurableSet_extChartAt_target (I := I) x₀
  have hKsub' : K ⊆ (extChartAt I x₀).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    exact hKsub
  have hcontOn_ext : ContinuousOn (extChartAt I x₀) (extChartAt I x₀).source :=
    continuousOn_extChartAt (I := I) x₀
  have hKE_compact : IsCompact KE :=
    hK.image_of_continuousOn (hcontOn_ext.mono hKsub')
  have hKE_closed : IsClosed KE := hKE_compact.isClosed
  have hKE_meas : MeasurableSet KE := hKE_closed.measurableSet
  have hKE_sub_T : KE ⊆ T := by
    intro y hy
    rcases hy with ⟨x, hxK, hxy⟩
    have hxsrc : x ∈ (extChartAt I x₀).source := hKsub' hxK
    have : (extChartAt I x₀) x ∈ (extChartAt I x₀).target :=
      (extChartAt I x₀).map_source hxsrc
    rw [hxy] at this
    exact this
  have hcontDensity_source : ContinuousOn (chartDensity g x₀) (chartAt H x₀).source :=
    chartDensity_continuousOn (I := I) g x₀
  have hcontDensity_K : ContinuousOn (chartDensity g x₀) K :=
    hcontDensity_source.mono hKsub
  have hbddAbove : BddAbove (chartDensity g x₀ '' K) :=
    (hK.image_of_continuousOn hcontDensity_K).bddAbove
  rcases hbddAbove with ⟨C, hC⟩
  have hsymm_in_K_iff : ∀ y ∈ T, ((extChartAt I x₀).symm y ∈ K ↔ y ∈ KE) := by
    intro y hyT
    constructor
    · intro hsymmK
      refine ⟨(extChartAt I x₀).symm y, hsymmK, ?_⟩
      exact (extChartAt I x₀).right_inv hyT
    · intro hyKE
      rcases hyKE with ⟨x, hxK, hxy⟩
      have hxsrc : x ∈ (extChartAt I x₀).source := hKsub' hxK
      have : (extChartAt I x₀).symm y = x := by
        rw [← hxy]
        exact (extChartAt I x₀).left_inv hxsrc
      rw [this]; exact hxK
  have hbound_pt : ∀ y ∈ T,
      ENNReal.ofReal (chartDensity g x₀ ((extChartAt I x₀).symm y)) *
          K.indicator (fun _ => (1 : ℝ≥0∞)) ((extChartAt I x₀).symm y) ≤
        ENNReal.ofReal C * KE.indicator (fun _ => (1 : ℝ≥0∞)) y := by
    intro y hyT
    by_cases hy : y ∈ KE
    · have hsymmK : (extChartAt I x₀).symm y ∈ K := (hsymm_in_K_iff y hyT).mpr hy
      rcases hy with ⟨x, hxK, hxy⟩
      have hxsrc : x ∈ (extChartAt I x₀).source := hKsub' hxK
      have hleft : (extChartAt I x₀).symm y = x := by
        rw [← hxy]
        exact (extChartAt I x₀).left_inv hxsrc
      rw [Set.indicator_of_mem hsymmK, Set.indicator_of_mem (show y ∈ KE from ⟨x, hxK, hxy⟩),
          hleft, mul_one, mul_one]
      have hle : chartDensity g x₀ x ≤ C := hC (Set.mem_image_of_mem _ hxK)
      exact ENNReal.ofReal_le_ofReal hle
    · have hsymm_notin : (extChartAt I x₀).symm y ∉ K := by
        intro hmem
        exact hy ((hsymm_in_K_iff y hyT).mp hmem)
      rw [Set.indicator_of_notMem hsymm_notin, Set.indicator_of_notMem hy,
          mul_zero, mul_zero]
  have hrhs_meas : Measurable
      (fun y : E => ENNReal.ofReal C * KE.indicator (fun _ => (1 : ℝ≥0∞)) y) :=
    (measurable_const).mul ((measurable_const).indicator hKE_meas)
  calc
    ∫⁻ y in T, ENNReal.ofReal (chartDensity g x₀ ((extChartAt I x₀).symm y)) *
          K.indicator (fun _ => (1 : ℝ≥0∞)) ((extChartAt I x₀).symm y)
            ∂(modelHaar (E := E))
        ≤ ∫⁻ y in T, ENNReal.ofReal C *
            KE.indicator (fun _ => (1 : ℝ≥0∞)) y ∂(modelHaar (E := E)) := by
          refine MeasureTheory.setLIntegral_mono_ae hrhs_meas.aemeasurable ?_
          exact Filter.Eventually.of_forall (fun y hyT => hbound_pt y hyT)
      _ = ENNReal.ofReal C *
            ∫⁻ y in T, KE.indicator (fun _ => (1 : ℝ≥0∞)) y ∂(modelHaar (E := E)) := by
          rw [lintegral_const_mul _ ((measurable_const).indicator hKE_meas)]
      _ = ENNReal.ofReal C * (modelHaar (E := E)) (KE ∩ T) := by
          rw [lintegral_indicator hKE_meas, setLIntegral_const, one_mul,
              Measure.restrict_apply hKE_meas]
      _ ≤ ENNReal.ofReal C * (modelHaar (E := E)) KE := by
          gcongr
          exact Set.inter_subset_left
      _ < (⊤ : ℝ≥0∞) := by
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hKE_compact.measure_lt_top
