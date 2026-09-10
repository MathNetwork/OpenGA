import Theorems.Thm_DifferentialGeometry_Integral_Measure_continuousOn_traceTimeDerivMetric_on_base
import Theorems.Thm_DifferentialGeometry_Integral_Measure_traceTimeDerivMetric_continuous
import Theorems.Thm_DifferentialGeometry_Integral_Measure_per_chart_integrand_hasDerivAt
import Theorems.Thm_DifferentialGeometry_Integral_Measure_continuousOn_chartDensity_family
import Theorems.Thm_DifferentialGeometry_Integral_Measure_hasDerivAt_setIntegral_model
import Theorems.Thm_DifferentialGeometry_Integral_Measure_integral_chart_ae
import Theorems.Thm_DifferentialGeometry_Integral_Measure_trace_chartGramMatrix_inv_deriv_chart_independent
import Theorems.Thm_DifferentialGeometry_Integral_Measure_chartGramMatrix_posDef
import Theorems.Thm_DifferentialGeometry_Integral_Measure_chartGramMatrix_det_contMDiffOn
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

lemma MetricFamilyRegularAt.at_any
    {g_fam : ℝ → SmoothRiemannianMetric I M} {t : ℝ}
    (hreg : MetricFamilyRegularAt (I := I) g_fam t) (s : ℝ) :
    MetricFamilyRegularAt (I := I) g_fam s :=
  { hasDerivAt_chartGramMatrix := hreg.hasDerivAt_chartGramMatrix
    continuousOn_chartGramMatrix := hreg.continuousOn_chartGramMatrix
    continuousOn_deriv_chartGramMatrix := hreg.continuousOn_deriv_chartGramMatrix }

lemma traceTimeDerivMetric_eq
    (g_fam : ℝ → SmoothRiemannianMetric I M) (t : ℝ) (x : M) :
    traceTimeDerivMetric (I := I) g_fam t x =
      Matrix.trace ((chartGramMatrix (I := I) (g_fam t) x x)⁻¹ *
        (Matrix.of fun i j =>
          deriv (fun s => chartGramMatrix (I := I) (g_fam s) x x i j) t)) := rfl

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

theorem integral_chartLocalMeasure
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (h : M → ℝ) (hh_meas : Measurable h) :
    ∫ x, h x ∂(chartLocalMeasure (I := I) g x₀)
      = ∫ y in (extChartAt I x₀).target,
          chartDensity g x₀ ((extChartAt I x₀).symm y) *
            h ((extChartAt I x₀).symm y)
          ∂(modelHaar (E := E)) :=
  integral_chart_ae (I := I) g x₀ h hh_meas.aestronglyMeasurable

lemma traceTimeDerivMetric_eq_trace_chartGramMatrix
    {g_fam : ℝ → SmoothRiemannianMetric I M} {t : ℝ}
    (hreg : MetricFamilyRegularAt (I := I) g_fam t)
    (α : M) {x : M}
    (hxα : x ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    traceTimeDerivMetric (I := I) g_fam t x
    = Matrix.trace ((chartGramMatrix (I := I) (g_fam t) α x)⁻¹ *
      (Matrix.of fun i j : Fin (Module.finrank ℝ E) =>
        deriv (fun s => chartGramMatrix (I := I) (g_fam s) α x i j) t)) := by
  have hxx : x ∈ (trivializationAt E (TangentSpace I) x).baseSet := by
    change x ∈ (chartAt H x).source
    exact mem_chart_source _ _
  rw [traceTimeDerivMetric_eq]
  exact trace_chartGramMatrix_inv_deriv_chart_independent
    (I := I) (M := M) hreg x α hxx hxα

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

attribute [local instance] _root_.OpenGAExport.DifferentialGeometry.Analysis.Integration.Measure.Family.instance_30

attribute [local instance] _root_.OpenGAExport.DifferentialGeometry.Analysis.Integration.Measure.Family.instance_31

attribute [local instance] _root_.OpenGAExport.DifferentialGeometry.Analysis.Integration.Measure.Family.instance_32

attribute [local instance] _root_.OpenGAExport.DifferentialGeometry.Analysis.Integration.Measure.Family.instance_33

section CleanVolumeVariation

variable {g_fam : ℝ → SmoothRiemannianMetric I M}

section TraceTimeDerivMetricContinuous

lemma continuousOn_chartTrace_form_of_base_pullback
    {g_fam : ℝ → SmoothRiemannianMetric I M} {t : ℝ}
    (hreg : MetricFamilyRegularAt (I := I) g_fam t) (α : M)
    {S : Set (ℝ × E)} (sym : E → M)
    (hsym_cont : ContinuousOn (fun p : ℝ × E => (p.1, sym p.2)) S)
    (hsym_maps : Set.MapsTo (fun p : ℝ × E => ((p.1, sym p.2) : ℝ × M)) S
      (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet)) :
    ContinuousOn
      (fun p : ℝ × E => Matrix.trace
        ((chartGramMatrix (I := I) (g_fam p.1) α (sym p.2))⁻¹ *
          (Matrix.of fun i j : Fin (Module.finrank ℝ E) =>
            deriv (fun s => chartGramMatrix (I := I) (g_fam s) α (sym p.2) i j) p.1)))
      S := by
  have h_base := continuousOn_traceTimeDerivMetric_on_base (I := I) (M := M) hreg α
  have h_comp : ContinuousOn
      ((fun p : ℝ × M => Matrix.trace
          ((chartGramMatrix (I := I) (g_fam p.1) α p.2)⁻¹ *
            (Matrix.of fun i j : Fin (Module.finrank ℝ E) =>
              deriv (fun s => chartGramMatrix (I := I) (g_fam s) α p.2 i j) p.1)))
        ∘ (fun p : ℝ × E => ((p.1, sym p.2) : ℝ × M))) S :=
    h_base.comp hsym_cont hsym_maps
  exact h_comp

end TraceTimeDerivMetricContinuous

end CleanVolumeVariation

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

variable {g_fam : ℝ → SmoothRiemannianMetric I M}

namespace DifferentialGeometry.Integral.Measure
end DifferentialGeometry.Integral.Measure
open _root_.DifferentialGeometry.Integral.Measure

lemma solution
    [T2Space M] [CompactSpace M]
    {g_fam : ℝ → SmoothRiemannianMetric I M} {f : ℝ → M → ℝ} {t : ℝ}
    (hreg : MetricFamilyRegularAt (I := I) g_fam t)
    (hf : FunctionRegularAt f t)
    (α : M) :
    HasDerivAt
      (fun s : ℝ => ∫ x, f s x
        ∂((chartLocalMeasure (I := I) (g_fam s) α).withDensity
            (fun y : M => ENNReal.ofReal ((chartAtlasPOU I M) α y))))
      (∫ x, (deriv (fun s : ℝ => f s x) t
              + (1/2) * traceTimeDerivMetric (I := I) g_fam t x * f t x) *
            (chartAtlasPOU I M) α x
          ∂(chartLocalMeasure (I := I) (g_fam t) α)) t := by
  classical
  set n := Fin (Module.finrank ℝ E) with hn_def
  set ρα : M → ℝ := fun x => (chartAtlasPOU I M) α x with hρα_def
  set μₐ : MeasureTheory.Measure M := chartLocalMeasure (I := I) (g_fam t) α with hμα_def
  set target : Set E := (extChartAt I α).target with htarget_def
  set symm : E → M := fun y => (extChartAt I α).symm y with hsymm_def
  have htarget_meas : MeasurableSet target :=
    measurableSet_extChartAt_target (I := I) α
  have hρα_cont : Continuous ρα := ((chartAtlasPOU I M) α).contMDiff.continuous
  have hρα_nonneg : ∀ x, 0 ≤ ρα x := fun x => (chartAtlasPOU I M).nonneg _ _
  have hρα_le_one : ∀ x, ρα x ≤ 1 := fun x => (chartAtlasPOU I M).le_one _ _
  have hρα_subord : tsupport ρα ⊆ (chartAt H α).source :=
    (chartAtlasPOU_isSubordinate I M) α
  have hρα_tsupport_compact : IsCompact (tsupport ρα) := isClosed_tsupport ρα |>.isCompact
  have hf_cont_joint : Continuous (fun p : ℝ × M => f p.1 p.2) := hf.continuous_joint
  have hft_cont : Continuous (f t) := by
    have : Continuous ((fun p : ℝ × M => f p.1 p.2) ∘ (fun x : M => (t, x))) := by
      refine hf_cont_joint.comp ?_
      exact continuous_const.prodMk continuous_id
    exact this
  have h_deriv_cont_joint_M : Continuous
      (fun p : ℝ × M => deriv (fun s : ℝ => f s p.2) p.1) :=
    hf.continuous_deriv_joint
  have h_deriv_cont : Continuous (fun x : M => deriv (fun s : ℝ => f s x) t) := by
    have : Continuous ((fun p : ℝ × M => deriv (fun s : ℝ => f s p.2) p.1)
        ∘ (fun x : M => (t, x))) :=
      h_deriv_cont_joint_M.comp (continuous_const.prodMk continuous_id)
    exact this
  have h_tr_cont : Continuous (fun x : M => traceTimeDerivMetric (I := I) g_fam t x) :=
    traceTimeDerivMetric_continuous (I := I) (M := M) hreg
  have h_density_contOn : ContinuousOn
      (fun x : M => chartDensity (I := I) (g_fam t) α x)
      (trivializationAt E (TangentSpace I) α).baseSet :=
    chartDensity_continuousOn (I := I) (g_fam t) α
  have h_symm_contOn : ContinuousOn symm target :=
    continuousOn_extChartAt_symm (I := I) α
  have h_symm_maps : ∀ y ∈ target, symm y ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    intro y hy
    have hsrc : symm y ∈ (extChartAt I α).source := (extChartAt I α).map_target hy
    rw [extChartAt_source_eq_chartAt_source (I := I)] at hsrc
    exact hsrc
  obtain ⟨Cf, hCf⟩ : ∃ C, ∀ x, ‖f t x‖ ≤ C := by
    have hIm := (isCompact_univ (X := M)).image hft_cont.norm
    obtain ⟨C, hC⟩ := hIm.bddAbove
    exact ⟨C, fun x => hC ⟨x, Set.mem_univ _, rfl⟩⟩
  set Fmdl : ℝ → E → ℝ := fun s y =>
    f s (symm y) * ρα (symm y) * chartDensity (I := I) (g_fam s) α (symm y)
  set Fprim : ℝ → E → ℝ := fun s y =>
    (deriv (fun r : ℝ => f r (symm y)) s +
      (1/2) * traceTimeDerivMetric (I := I) g_fam s (symm y) *
        f s (symm y)) * ρα (symm y) *
      chartDensity (I := I) (g_fam s) α (symm y)
  have hH'_deriv : ∀ᵐ y ∂((modelHaar (E := E)).restrict target),
      ∀ s ∈ (Set.univ : Set ℝ), HasDerivAt (fun r => Fmdl r y) (Fprim s y) s := by
    refine (MeasureTheory.ae_restrict_iff' htarget_meas).mpr ?_
    refine Filter.Eventually.of_forall (fun y hy => ?_)
    intro s _
    have hsym_base : symm y ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
      h_symm_maps y hy
    have hslice : HasDerivAt (fun r : ℝ => f r (symm y))
        (deriv (fun r : ℝ => f r (symm y)) s) s :=
      hf.hasDerivAt_time (symm y) s
    have hpcd := per_chart_integrand_hasDerivAt
      (I := I) (M := M) (t := s) (hreg.at_any s) α (x := symm y) hsym_base f ρα hslice
    exact hpcd
  set K : Set M := tsupport ρα
  set K' : Set E := (extChartAt I α) '' K
  have hK_compact : IsCompact K := hρα_tsupport_compact
  have hK'_compact : IsCompact K' :=
    hK_compact.image_of_continuousOn (continuousOn_extChartAt (I := I) α |>.mono (by
      intro y hy
      have : y ∈ (chartAt H α).source := hρα_subord hy
      rw [← extChartAt_source_eq_chartAt_source (I := I)] at this
      exact this))
  have hK'_meas : MeasurableSet K' := hK'_compact.measurableSet
  have hK'_meas_lt_top : (modelHaar (E := E)) K' < ⊤ :=
    hK'_compact.measure_lt_top
  have h_deriv_cont_joint : Continuous
      (fun p : ℝ × M => deriv (fun s : ℝ => f s p.2) p.1) :=
    hf.continuous_deriv_joint
  set I₁ : Set ℝ := Set.Icc (t - 1) (t + 1)
  have hI₁_compact : IsCompact I₁ := isCompact_Icc
  have ht_interior : t ∈ Set.Ioo (t - 1 : ℝ) (t + 1) := by
    refine ⟨?_, ?_⟩ <;> linarith
  have ht_in_I₁ : t ∈ I₁ := ⟨by linarith, by linarith⟩
  set ball_s : Set ℝ := Metric.ball t 1
  have hballs_nhd : ball_s ∈ 𝓝 t := Metric.ball_mem_nhds _ one_pos
  have hballs_sub_I₁ : ball_s ⊆ I₁ := by
    intro s hs
    have hs' : |s - t| < 1 := by
      change dist s t < 1 at hs
      simpa [Real.dist_eq, Real.norm_eq_abs] using hs
    refine ⟨?_, ?_⟩
    · have := (abs_lt.mp hs').1; linarith
    · have := (abs_lt.mp hs').2; linarith
  set Ω : Set (ℝ × E) := I₁ ×ˢ K'
  have hΩ_compact : IsCompact Ω := hI₁_compact.prod hK'_compact
  have hK'_sub_target : K' ⊆ target := by
    intro y hy
    obtain ⟨x, hxK, hx_eq⟩ := hy
    have hx_src : x ∈ (extChartAt I α).source := by
      have : x ∈ (chartAt H α).source := hρα_subord hxK
      rw [← extChartAt_source_eq_chartAt_source (I := I)] at this
      exact this
    rw [← hx_eq]
    exact (extChartAt I α).map_source hx_src
  have h_Fprim_continuousOn_Ω :
      ContinuousOn (fun p : ℝ × E => Fprim p.1 p.2) (I₁ ×ˢ K') := by
    have h_symm_contOn_K' : ContinuousOn symm K' := h_symm_contOn.mono hK'_sub_target
    have h_symm_pair_contOn :
        ContinuousOn (fun p : ℝ × E => (p.1, symm p.2)) (I₁ ×ˢ K') := by
      refine ContinuousOn.prodMk continuousOn_fst ?_
      refine h_symm_contOn_K'.comp continuousOn_snd ?_
      intro p hp
      exact hp.2
    have hf_comp : ContinuousOn (fun p : ℝ × E => f p.1 (symm p.2)) (I₁ ×ˢ K') := by
      exact hf_cont_joint.continuousOn.comp h_symm_pair_contOn (fun _ _ => Set.mem_univ _)
    have hρα_comp : ContinuousOn (fun p : ℝ × E => ρα (symm p.2)) (I₁ ×ˢ K') := by
      have : ContinuousOn (fun y : E => ρα (symm y)) K' := by
        exact hρα_cont.continuousOn.comp h_symm_contOn_K' (fun _ _ => Set.mem_univ _)
      exact (this.comp continuousOn_snd (fun _ hp => hp.2))
    have hdensity_comp : ContinuousOn
        (fun p : ℝ × E => chartDensity (I := I) (g_fam p.1) α (symm p.2))
        (I₁ ×ˢ K') := by
      have h_joint_cont : ContinuousOn
          (fun p : ℝ × M => chartDensity (I := I) (g_fam p.1) α p.2)
          (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) :=
        continuousOn_chartDensity_family (I := I) (M := M) hreg α
      have hmaps : Set.MapsTo (fun p : ℝ × E => ((p.1, symm p.2) : ℝ × M))
          (I₁ ×ˢ K')
          (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) := by
        intro p hp
        refine ⟨Set.mem_univ _, ?_⟩
        exact h_symm_maps p.2 (hK'_sub_target hp.2)
      have h := h_joint_cont.comp h_symm_pair_contOn hmaps
      exact h
    have h_deriv_comp : ContinuousOn
        (fun p : ℝ × E => deriv (fun r : ℝ => f r (symm p.2)) p.1) (I₁ ×ˢ K') := by
      have h := h_deriv_cont_joint.continuousOn.comp h_symm_pair_contOn
        (fun _ _ => Set.mem_univ _)
      exact h
    have h_symm_pair_mapsTo : Set.MapsTo (fun p : ℝ × E => ((p.1, symm p.2) : ℝ × M))
        (I₁ ×ˢ K')
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) := fun p hp =>
      ⟨Set.mem_univ _, h_symm_maps p.2 (hK'_sub_target hp.2)⟩
    have h_tr_base_pb :
        ContinuousOn (fun p : ℝ × E => Matrix.trace
          ((chartGramMatrix (I := I) (g_fam p.1) α (symm p.2))⁻¹ *
            (Matrix.of fun i j : Fin (Module.finrank ℝ E) =>
              deriv (fun s => chartGramMatrix (I := I) (g_fam s) α (symm p.2) i j) p.1)))
        (I₁ ×ˢ K') :=
      continuousOn_chartTrace_form_of_base_pullback (I := I) (M := M) hreg α
        (sym := symm) h_symm_pair_contOn h_symm_pair_mapsTo
    have h_tr_comp : ContinuousOn
        (fun p : ℝ × E => traceTimeDerivMetric (I := I) g_fam p.1 (symm p.2))
        (I₁ ×ˢ K') := by
      refine h_tr_base_pb.congr ?_
      intro p hp
      have hsym_base : symm p.2 ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
        h_symm_maps p.2 (hK'_sub_target hp.2)
      exact traceTimeDerivMetric_eq_trace_chartGramMatrix
        (I := I) (M := M) (t := p.1) (hreg.at_any p.1) α hsym_base
    change ContinuousOn (fun p : ℝ × E =>
        (deriv (fun r : ℝ => f r (symm p.2)) p.1 +
            (1/2) * traceTimeDerivMetric (I := I) g_fam p.1 (symm p.2) *
              f p.1 (symm p.2)) * ρα (symm p.2) *
          chartDensity (I := I) (g_fam p.1) α (symm p.2)) (I₁ ×ˢ K')
    refine ContinuousOn.mul (ContinuousOn.mul ?_ hρα_comp) hdensity_comp
    refine ContinuousOn.add h_deriv_comp ?_
    refine ContinuousOn.mul ?_ hf_comp
    refine ContinuousOn.mul continuousOn_const ?_
    exact h_tr_comp
  obtain ⟨CH, hCH⟩ : ∃ C, ∀ p ∈ (I₁ ×ˢ K'), |Fprim p.1 p.2| ≤ C := by
    classical
    by_cases hne' : (I₁ ×ˢ K' : Set (ℝ × E)).Nonempty
    · have hΩne : Ω.Nonempty := hne'
      have h_abs_cont : ContinuousOn (fun p : ℝ × E => |Fprim p.1 p.2|) Ω :=
        h_Fprim_continuousOn_Ω.abs
      have hbdd := hΩ_compact.bddAbove_image h_abs_cont
      obtain ⟨C, hC⟩ := hbdd
      refine ⟨C, fun p hp => ?_⟩
      exact hC ⟨p, hp, rfl⟩
    · refine ⟨0, fun p hp => ?_⟩
      exact (hne' ⟨p, hp⟩).elim
  set C₀ : ℝ := |CH|
  set b : E → ℝ := fun y => C₀ * (K'.indicator (fun _ : E => (1 : ℝ))) y with hb_def
  have hb_nonneg : ∀ y, 0 ≤ b y := by
    intro y
    have h_ind_nonneg : 0 ≤ K'.indicator (fun _ : E => (1 : ℝ)) y :=
      Set.indicator_nonneg (fun _ _ => zero_le_one) _
    exact mul_nonneg (abs_nonneg _) h_ind_nonneg
  have hb_integrable : Integrable b ((modelHaar (E := E)).restrict target) := by
    have h_ind_int : Integrable (K'.indicator (fun _ : E => (1 : ℝ)))
        ((modelHaar (E := E)).restrict target) := by
      have h_rest_int : Integrable (K'.indicator (fun _ : E => (1 : ℝ))) (modelHaar (E := E)) := by
        rw [integrable_indicator_iff hK'_meas]
        exact integrableOn_const (hs := ne_of_lt hK'_meas_lt_top)
      exact h_rest_int.restrict
    have := h_ind_int.const_mul C₀
    simpa [b, smul_eq_mul] using this
  have h_bound_prop : ∀ᵐ y ∂((modelHaar (E := E)).restrict target),
      ∀ s ∈ ball_s, ‖Fprim s y‖ ≤ b y := by
    refine (MeasureTheory.ae_restrict_iff' htarget_meas).mpr ?_
    refine Filter.Eventually.of_forall (fun y hy => ?_)
    intro s hs
    by_cases hyK' : y ∈ K'
    · have hp : (s, y) ∈ (I₁ ×ˢ K' : Set (ℝ × E)) := ⟨hballs_sub_I₁ hs, hyK'⟩
      have hbound := hCH (s, y) hp
      have hby : b y = C₀ := by
        simp [b, Set.indicator_of_mem hyK']
      rw [Real.norm_eq_abs, hby]
      have : |Fprim s y| ≤ CH := hbound
      refine this.trans ?_
      exact le_abs_self _
    · have h_symm_y_not_in : symm y ∉ K := by
        intro hsymInK
        exact hyK' ⟨symm y, hsymInK, by
          exact (extChartAt I α).right_inv hy⟩
      have hρ_zero : ρα (symm y) = 0 := by
        by_contra h
        have : symm y ∈ Function.support ρα := h
        exact h_symm_y_not_in (subset_tsupport _ this)
      have hH'_zero : Fprim s y = 0 := by
        change (deriv (fun r : ℝ => f r (symm y)) s +
            (1/2) * traceTimeDerivMetric (I := I) g_fam s (symm y) *
              f s (symm y)) * ρα (symm y) *
            chartDensity (I := I) (g_fam s) α (symm y) = 0
        rw [hρ_zero, mul_zero, zero_mul]
      rw [hH'_zero]
      have hby_nonneg : 0 ≤ b y := hb_nonneg y
      simpa using hby_nonneg
  have hH_meas_at_t : ∀ᶠ s in 𝓝 t,
      AEStronglyMeasurable (Fmdl s) ((modelHaar (E := E)).restrict target) := by
    refine Filter.Eventually.of_forall (fun s => ?_)
    have h_symm_contOn_target : ContinuousOn symm target := h_symm_contOn
    have h_f_s_comp_contOn : ContinuousOn (fun y : E => f s (symm y)) target := by
      have hf_s_cont : Continuous (f s) := by
        have : Continuous ((fun p : ℝ × M => f p.1 p.2) ∘ (fun x : M => (s, x))) := by
          refine hf_cont_joint.comp ?_
          exact continuous_const.prodMk continuous_id
        exact this
      exact hf_s_cont.continuousOn.comp h_symm_contOn_target
        (fun _ _ => Set.mem_univ _)
    have h_ρα_comp_contOn : ContinuousOn (fun y : E => ρα (symm y)) target :=
      hρα_cont.continuousOn.comp h_symm_contOn_target (fun _ _ => Set.mem_univ _)
    have h_density_comp_contOn : ContinuousOn
        (fun y : E => chartDensity (I := I) (g_fam s) α (symm y)) target := by
      have h_density_s : ContinuousOn
          (fun x : M => chartDensity (I := I) (g_fam s) α x)
          (trivializationAt E (TangentSpace I) α).baseSet :=
        chartDensity_continuousOn (I := I) (g_fam s) α
      exact h_density_s.comp h_symm_contOn_target h_symm_maps
    have h_H_s_contOn : ContinuousOn (Fmdl s) target := by
      exact (h_f_s_comp_contOn.mul h_ρα_comp_contOn).mul h_density_comp_contOn
    exact (h_H_s_contOn.aestronglyMeasurable htarget_meas)
  have hH_int_at_t : Integrable (Fmdl t) ((modelHaar (E := E)).restrict target) := by
    have h_Ht_cont_K' : ContinuousOn (Fmdl t) K' := by
      have h_symm_contOn_K' : ContinuousOn symm K' := h_symm_contOn.mono hK'_sub_target
      have hf_cont : Continuous (f t) := by
        have : Continuous ((fun p : ℝ × M => f p.1 p.2) ∘ (fun x : M => (t, x))) := by
          refine hf_cont_joint.comp ?_
          exact continuous_const.prodMk continuous_id
        exact this
      have h_f_comp : ContinuousOn (fun y : E => f t (symm y)) K' :=
        hf_cont.continuousOn.comp h_symm_contOn_K' (fun _ _ => Set.mem_univ _)
      have h_ρα_comp : ContinuousOn (fun y : E => ρα (symm y)) K' :=
        hρα_cont.continuousOn.comp h_symm_contOn_K' (fun _ _ => Set.mem_univ _)
      have h_density_comp : ContinuousOn
          (fun y : E => chartDensity (I := I) (g_fam t) α (symm y)) K' := by
        refine h_density_contOn.comp h_symm_contOn_K' ?_
        intro y hy
        exact h_symm_maps y (hK'_sub_target hy)
      exact (h_f_comp.mul h_ρα_comp).mul h_density_comp
    obtain ⟨C_Fmdl, hC_H⟩ : ∃ C, ∀ y ∈ K', |Fmdl t y| ≤ C := by
      by_cases hK'_ne : K'.Nonempty
      · have h_abs_cont : ContinuousOn (fun y : E => |Fmdl t y|) K' := h_Ht_cont_K'.abs
        obtain ⟨C, hC⟩ := hK'_compact.bddAbove_image h_abs_cont
        refine ⟨C, fun y hy => ?_⟩
        exact hC ⟨y, hy, rfl⟩
      · refine ⟨0, fun y hy => ?_⟩
        exact absurd ⟨y, hy⟩ hK'_ne
    have hH_t_vanish : ∀ y ∈ target, y ∉ K' → Fmdl t y = 0 := by
      intro y hy_tg hy_not
      have : symm y ∉ K := by
        intro h
        have hsrc : symm y ∈ (chartAt H α).source := hρα_subord h
        have hsrc' : symm y ∈ (extChartAt I α).source := by
          rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hsrc
        apply hy_not
        refine ⟨symm y, h, ?_⟩
        exact (extChartAt I α).right_inv hy_tg
      have hρ_zero : ρα (symm y) = 0 := by
        by_contra h
        exact this (subset_tsupport _ (show symm y ∈ Function.support ρα from h))
      change f t (symm y) * ρα (symm y) * chartDensity (I := I) (g_fam t) α (symm y) = 0
      rw [hρ_zero, mul_zero, zero_mul]
    set C_Fprim : ℝ := max C_Fmdl 0
    have hC_Fprim_nonneg : 0 ≤ C_Fprim := le_max_right _ _
    have h_domHt : ∀ᵐ y ∂((modelHaar (E := E)).restrict target),
        ‖Fmdl t y‖ ≤ C_Fprim * K'.indicator (fun _ : E => (1 : ℝ)) y := by
      refine (MeasureTheory.ae_restrict_iff' htarget_meas).mpr ?_
      refine Filter.Eventually.of_forall (fun y hy => ?_)
      by_cases hyK' : y ∈ K'
      · rw [Set.indicator_of_mem hyK', mul_one, Real.norm_eq_abs]
        calc |Fmdl t y| ≤ C_Fmdl := hC_H y hyK'
          _ ≤ C_Fprim := le_max_left _ _
      · rw [hH_t_vanish y hy hyK']
        rw [Set.indicator_of_notMem hyK', mul_zero, norm_zero]
    have h_bound_int' : Integrable
        (fun y : E => C_Fprim * K'.indicator (fun _ : E => (1 : ℝ)) y)
        ((modelHaar (E := E)).restrict target) := by
      have h_ind_int : Integrable (K'.indicator (fun _ : E => (1 : ℝ)))
          ((modelHaar (E := E)).restrict target) := by
        have h_rest_int : Integrable (K'.indicator (fun _ : E => (1 : ℝ)))
            (modelHaar (E := E)) := by
          rw [integrable_indicator_iff hK'_meas]
          exact integrableOn_const (hs := ne_of_lt hK'_meas_lt_top)
        exact h_rest_int.restrict
      simpa [smul_eq_mul] using h_ind_int.const_mul C_Fprim
    have h_meas_Ht : AEStronglyMeasurable (Fmdl t) ((modelHaar (E := E)).restrict target) := by
      have h_symm_contOn_target : ContinuousOn symm target := h_symm_contOn
      have hf_cont : Continuous (f t) := by
        have : Continuous ((fun p : ℝ × M => f p.1 p.2) ∘ (fun x : M => (t, x))) := by
          refine hf_cont_joint.comp ?_
          exact continuous_const.prodMk continuous_id
        exact this
      have h_f_cont : ContinuousOn (fun y : E => f t (symm y)) target :=
        hf_cont.continuousOn.comp h_symm_contOn_target (fun _ _ => Set.mem_univ _)
      have h_ρ_cont : ContinuousOn (fun y : E => ρα (symm y)) target :=
        hρα_cont.continuousOn.comp h_symm_contOn_target (fun _ _ => Set.mem_univ _)
      have h_d_cont : ContinuousOn
          (fun y : E => chartDensity (I := I) (g_fam t) α (symm y)) target :=
        h_density_contOn.comp h_symm_contOn_target h_symm_maps
      exact ((h_f_cont.mul h_ρ_cont).mul h_d_cont).aestronglyMeasurable htarget_meas
    exact h_bound_int'.mono' h_meas_Ht h_domHt
  have hH'_meas_at_t : AEStronglyMeasurable (Fprim t)
      ((modelHaar (E := E)).restrict target) := by
    have h_t_in_I₁ : t ∈ I₁ := ht_in_I₁
    have h_Ht'_cont_K' : ContinuousOn (fun y : E => Fprim t y) K' := by
      have := h_Fprim_continuousOn_Ω
      have : ContinuousOn (fun p : ℝ × E => Fprim p.1 p.2) (I₁ ×ˢ K') := this
      intro y hy
      have hp : (t, y) ∈ (I₁ ×ˢ K') := ⟨h_t_in_I₁, hy⟩
      have hat : ContinuousWithinAt (fun p : ℝ × E => Fprim p.1 p.2) (I₁ ×ˢ K') (t, y) :=
        this (t, y) hp
      have hincl_cont : Continuous (fun e : E => (t, e)) :=
        continuous_const.prodMk continuous_id
      have hincl_mapsTo : Set.MapsTo (fun e : E => (t, e)) K' (I₁ ×ˢ K') :=
        fun e he => ⟨h_t_in_I₁, he⟩
      exact hat.comp hincl_cont.continuousWithinAt hincl_mapsTo
    have h_Ht'_zero_off : ∀ y ∈ target, y ∉ K' → Fprim t y = 0 := by
      intro y hy hyK'
      have h_symm_y_not_K : symm y ∉ K := by
        intro h
        apply hyK'
        refine ⟨symm y, h, ?_⟩
        exact (extChartAt I α).right_inv hy
      have hρ_zero : ρα (symm y) = 0 := by
        by_contra h
        exact h_symm_y_not_K (subset_tsupport _
          (show symm y ∈ Function.support ρα from h))
      change (deriv (fun r : ℝ => f r (symm y)) t +
          (1/2) * traceTimeDerivMetric (I := I) g_fam t (symm y) *
            f t (symm y)) * ρα (symm y) *
          chartDensity (I := I) (g_fam t) α (symm y) = 0
      rw [hρ_zero, mul_zero, zero_mul]
    have h_ind_Ht : Fprim t =ᵐ[(modelHaar (E := E)).restrict target]
        K'.indicator (fun y => Fprim t y) := by
      refine (MeasureTheory.ae_restrict_iff' htarget_meas).mpr ?_
      refine Filter.Eventually.of_forall (fun y hy => ?_)
      by_cases hyK' : y ∈ K'
      · rw [Set.indicator_of_mem hyK']
      · rw [Set.indicator_of_notMem hyK']
        exact h_Ht'_zero_off y hy hyK'
    refine AEStronglyMeasurable.congr ?_ h_ind_Ht.symm
    have h_ind_meas : AEStronglyMeasurable
        (K'.indicator (fun y : E => Fprim t y))
        ((modelHaar (E := E)).restrict target) := by
      have h_restrict : AEStronglyMeasurable (fun y : E => Fprim t y)
          ((modelHaar (E := E)).restrict K') := by
        exact h_Ht'_cont_K'.aestronglyMeasurable hK'_meas
      have : AEStronglyMeasurable (K'.indicator (fun y : E => Fprim t y))
          (modelHaar (E := E)) := by
        refine (aestronglyMeasurable_indicator_iff hK'_meas).mpr ?_
        exact h_restrict
      exact this.restrict
    exact h_ind_meas
  have h_s_mem : ball_s ∈ 𝓝 t := hballs_nhd
  have h_diff_ballsupersed : ∀ᵐ y ∂((modelHaar (E := E)).restrict target),
      ∀ s ∈ ball_s, HasDerivAt (fun r => Fmdl r y) (Fprim s y) s := by
    filter_upwards [hH'_deriv] with y hy
    intro s' _
    exact hy s' (Set.mem_univ _)
  have h_setInt := hasDerivAt_setIntegral_model (E := E) target
    (F := Fmdl) (F' := Fprim) (b := b) t (s := ball_s) h_s_mem hH_meas_at_t hH_int_at_t
    hH'_meas_at_t h_bound_prop hb_integrable h_diff_ballsupersed
  obtain ⟨_, h_inner⟩ := h_setInt
  have h_lhs_eq : ∀ s : ℝ,
      (∫ y in target, Fmdl s y ∂(modelHaar (E := E)))
        = ∫ x, f s x
            ∂((chartLocalMeasure (I := I) (g_fam s) α).withDensity
                (fun y : M => ENNReal.ofReal (ρα y))) := by
    intro s
    have hρα_meas : AEMeasurable (fun y : M => ENNReal.ofReal (ρα y))
        (chartLocalMeasure (I := I) (g_fam s) α) :=
      (ENNReal.measurable_ofReal.comp hρα_cont.measurable).aemeasurable
    have hρα_lt_top : ∀ᵐ y ∂(chartLocalMeasure (I := I) (g_fam s) α),
        ENNReal.ofReal (ρα y) < ⊤ := Filter.Eventually.of_forall (fun _ => by simp)
    have h_withD :
        ∫ x, f s x
          ∂((chartLocalMeasure (I := I) (g_fam s) α).withDensity
              (fun y : M => ENNReal.ofReal (ρα y)))
          = ∫ x, (ENNReal.ofReal (ρα x)).toReal • f s x
              ∂(chartLocalMeasure (I := I) (g_fam s) α) :=
      integral_withDensity_eq_integral_toReal_smul₀
        (μ := chartLocalMeasure (I := I) (g_fam s) α)
        (f := fun y : M => ENNReal.ofReal (ρα y)) hρα_meas hρα_lt_top
        (g := f s)
    have h_smul_eq : (fun x : M =>
        (ENNReal.ofReal (ρα x)).toReal • f s x) = fun x : M => f s x * ρα x := by
      funext x
      rw [ENNReal.toReal_ofReal (hρα_nonneg x), smul_eq_mul, mul_comm]
    have hfs_cont : Continuous (f s) := by
      have : Continuous ((fun p : ℝ × M => f p.1 p.2) ∘ (fun x : M => (s, x))) := by
        refine hf_cont_joint.comp ?_
        exact continuous_const.prodMk continuous_id
      exact this
    have h_fρ_meas : Measurable (fun x : M => f s x * ρα x) :=
      (hfs_cont.mul hρα_cont).measurable
    have h_ICLM := integral_chartLocalMeasure (I := I) (M := M) (g_fam s) α
      (fun x => f s x * ρα x) h_fρ_meas
    rw [h_withD, h_smul_eq, h_ICLM]
    have h_integrand_eq : (fun y : E =>
        chartDensity (I := I) (g_fam s) α (symm y) * (f s (symm y) * ρα (symm y)))
          = fun y : E => Fmdl s y := by
      funext y
      change chartDensity (I := I) (g_fam s) α ((extChartAt I α).symm y) *
            (f s ((extChartAt I α).symm y) * ρα ((extChartAt I α).symm y))
        = f s ((extChartAt I α).symm y) * ρα ((extChartAt I α).symm y) *
            chartDensity (I := I) (g_fam s) α ((extChartAt I α).symm y)
      ring
    rw [h_integrand_eq]
  have h_rhs_eq :
      (∫ y in target, Fprim t y ∂(modelHaar (E := E)))
        = ∫ x, (deriv (fun s : ℝ => f s x) t
              + (1/2) * traceTimeDerivMetric (I := I) g_fam t x * f t x) *
              ρα x
            ∂(chartLocalMeasure (I := I) (g_fam t) α) := by
    set gFn : M → ℝ := fun x =>
      (deriv (fun s : ℝ => f s x) t +
        (1/2) * traceTimeDerivMetric (I := I) g_fam t x * f t x) * ρα x
    have hg_cont : Continuous gFn := by
      refine Continuous.mul ?_ hρα_cont
      refine h_deriv_cont.add ?_
      refine Continuous.mul ?_ hft_cont
      exact (continuous_const.mul h_tr_cont)
    have hg_meas : Measurable gFn := hg_cont.measurable
    have h_ICLM := integral_chartLocalMeasure (I := I) (M := M) (g_fam t) α gFn hg_meas
    rw [h_ICLM]
    refine MeasureTheory.setIntegral_congr_ae htarget_meas ?_
    refine Filter.Eventually.of_forall (fun y hy => ?_)
    change (deriv (fun r : ℝ => f r (symm y)) t +
            (1/2) * traceTimeDerivMetric (I := I) g_fam t (symm y) *
              f t (symm y)) * ρα (symm y) *
            chartDensity (I := I) (g_fam t) α (symm y)
      = chartDensity (I := I) (g_fam t) α ((extChartAt I α).symm y) *
          gFn ((extChartAt I α).symm y)
    change _ = chartDensity (I := I) (g_fam t) α (symm y) * gFn (symm y)
    change _ = chartDensity (I := I) (g_fam t) α (symm y) *
        ((deriv (fun r : ℝ => f r (symm y)) t +
          (1/2) * traceTimeDerivMetric (I := I) g_fam t (symm y) *
            f t (symm y)) * ρα (symm y))
    ring
  rw [show (fun s : ℝ => ∫ x, f s x
        ∂((chartLocalMeasure (I := I) (g_fam s) α).withDensity
            (fun y : M => ENNReal.ofReal (ρα y))))
      = fun s : ℝ => ∫ y in target, Fmdl s y ∂(modelHaar (E := E)) from ?_]
  · rw [h_rhs_eq.symm]
    exact h_inner
  · funext s
    exact (h_lhs_eq s).symm
