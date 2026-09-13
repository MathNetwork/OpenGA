import Theorems.Thm_DifferentialGeometry_Integral_Measure_chartLocalMeasure_compact_lt_top
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

omit [Module.Finite ℝ E] [IsManifold I ∞ M] in
lemma measurable_ofReal_pou_weight
    (ρ : SmoothPartitionOfUnity M I M univ) (α : M) :
    Measurable (fun x : M => ENNReal.ofReal (ρ α x)) := by
  have hcont : Continuous (fun x : M => ρ α x) :=
    (ρ α).contMDiff.continuous
  exact ENNReal.measurable_ofReal.comp hcont.measurable

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

 lemma _root_.DifferentialGeometry.Integral.Measure.pou_term_zero_of_tsupport_disjoint_closedSurface_DifferentialGeometry_Analysis_Integration_Measure_Properties
    (g : SmoothRiemannianMetric I M)
    (ρ : SmoothPartitionOfUnity M I M univ)
    {K : Set M} (hK : MeasurableSet K) (α : M)
    (hdisj : Disjoint K (tsupport (ρ α))) :
    ((chartLocalMeasure (I := I) g α).withDensity
        (fun x : M => ENNReal.ofReal (ρ α x))) K = 0 := by
  have hfmeas : Measurable (fun x : M => ENNReal.ofReal (ρ α x)) :=
    measurable_ofReal_pou_weight (I := I) (M := M) ρ α
  rw [withDensity_apply _ hK]
  refine MeasureTheory.setLIntegral_eq_zero hK (fun x hxK => ?_)
  have hxK_ts : x ∉ tsupport (ρ α) := by
    intro hx
    exact (Set.disjoint_left.mp hdisj hxK) hx
  have : ρ α x = 0 := by
    by_contra hne
    exact hxK_ts (subset_tsupport _ hne)
  simp [this]

 lemma _root_.DifferentialGeometry.Integral.Measure.pou_term_le_chartLocalMeasure_closedSurface_DifferentialGeometry_Analysis_Integration_Measure_Properties
    (g : SmoothRiemannianMetric I M)
    (ρ : SmoothPartitionOfUnity M I M univ)
    {K : Set M} (hK : MeasurableSet K) (α : M) :
    ((chartLocalMeasure (I := I) g α).withDensity
        (fun x : M => ENNReal.ofReal (ρ α x))) K ≤
      chartLocalMeasure (I := I) g α (K ∩ tsupport (ρ α)) := by
  have htsup_closed : IsClosed (tsupport (ρ α)) := isClosed_tsupport _
  have htsup_meas : MeasurableSet (tsupport (ρ α)) := htsup_closed.measurableSet
  have hKts_meas : MeasurableSet (K ∩ tsupport (ρ α)) := hK.inter htsup_meas
  have hle_one : ∀ x : M, ENNReal.ofReal (ρ α x) ≤ (1 : ℝ≥0∞) := by
    intro x
    calc ENNReal.ofReal (ρ α x) ≤ ENNReal.ofReal 1 :=
          ENNReal.ofReal_le_ofReal (ρ.le_one α x)
      _ = 1 := ENNReal.ofReal_one
  have hρ_zero_off : ∀ x, x ∉ tsupport (ρ α) → ρ α x = 0 := by
    intro x hx
    by_contra hne
    exact hx (subset_tsupport _ hne)
  rw [withDensity_apply _ hK]
  have hpt : ∀ x : M,
      ENNReal.ofReal (ρ α x) ≤ (tsupport (ρ α)).indicator (fun _ => (1 : ℝ≥0∞)) x := by
    intro x
    by_cases hx : x ∈ tsupport (ρ α)
    · rw [Set.indicator_of_mem hx]; exact hle_one x
    · rw [Set.indicator_of_notMem hx, hρ_zero_off x hx, ENNReal.ofReal_zero]
  calc
    ∫⁻ x in K, ENNReal.ofReal (ρ α x) ∂ chartLocalMeasure (I := I) g α
        ≤ ∫⁻ x in K, (tsupport (ρ α)).indicator (fun _ => (1 : ℝ≥0∞)) x
            ∂ chartLocalMeasure (I := I) g α := by
          refine MeasureTheory.setLIntegral_mono_ae
            ((measurable_const).indicator htsup_meas).aemeasurable ?_
          exact Filter.Eventually.of_forall (fun x _ => hpt x)
      _ = chartLocalMeasure (I := I) g α (K ∩ tsupport (ρ α)) := by
          rw [lintegral_indicator htsup_meas, Measure.restrict_restrict htsup_meas,
              setLIntegral_const, one_mul, Set.inter_comm]

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
    (g : SmoothRiemannianMetric I M)
    (ρ : SmoothPartitionOfUnity M I M univ)
    (hρ : ρ.IsSubordinate (fun α : M => (chartAt H α).source))
    {K : Set M} (hK : IsCompact K) :
    riemannianMeasure (I := I) g ρ K < (⊤ : ℝ≥0∞) := by
  classical
  have hKmeas : MeasurableSet K := hK.isClosed.measurableSet
  have hdecomp : riemannianMeasure (I := I) g ρ K =
      ∑' α : M, ((chartLocalMeasure (I := I) g α).withDensity
          (fun x : M => ENNReal.ofReal (ρ α x))) K := by
    rw [riemannianMeasure_def, Measure.sum_apply _ hKmeas]
  rw [hdecomp]
  set S : Set M := {α | (tsupport (ρ α) ∩ K).Nonempty} with hS_def
  have hlf_ts : LocallyFinite (fun α : M => tsupport (ρ α)) := ρ.locallyFinite.closure
  have hS_fin : S.Finite := hlf_ts.finite_nonempty_inter_compact hK
  have hzero_off : ∀ α, α ∉ S →
      ((chartLocalMeasure (I := I) g α).withDensity
          (fun x : M => ENNReal.ofReal (ρ α x))) K = 0 := by
    intro α hα
    have hdisj : Disjoint K (tsupport (ρ α)) := by
      rw [Set.disjoint_iff_inter_eq_empty, Set.inter_comm]
      simp only [hS_def, Set.mem_ofPred_eq, Set.not_nonempty_iff_eq_empty] at hα
      exact hα
    exact _root_.DifferentialGeometry.Integral.Measure.pou_term_zero_of_tsupport_disjoint_closedSurface_DifferentialGeometry_Analysis_Integration_Measure_Properties (I := I) (M := M) g ρ hKmeas α hdisj
  have htsum_eq : ∑' α : M, ((chartLocalMeasure (I := I) g α).withDensity
          (fun x : M => ENNReal.ofReal (ρ α x))) K =
        ∑ α ∈ hS_fin.toFinset, ((chartLocalMeasure (I := I) g α).withDensity
          (fun x : M => ENNReal.ofReal (ρ α x))) K := by
    refine tsum_eq_sum (s := hS_fin.toFinset) ?_
    intro α hα
    refine hzero_off α ?_
    intro hαS
    exact hα (hS_fin.mem_toFinset.mpr hαS)
  rw [htsum_eq]
  refine ENNReal.sum_lt_top.mpr ?_
  intro α _
  have hKts_compact : IsCompact (K ∩ tsupport (ρ α)) :=
    hK.inter_right (isClosed_tsupport _)
  have hKts_sub : K ∩ tsupport (ρ α) ⊆ (chartAt H α).source := by
    intro x hx
    exact hρ α hx.2
  have hbound := _root_.DifferentialGeometry.Integral.Measure.pou_term_le_chartLocalMeasure_closedSurface_DifferentialGeometry_Analysis_Integration_Measure_Properties
    (I := I) (M := M) g ρ hKmeas α
  exact lt_of_le_of_lt hbound
    (chartLocalMeasure_compact_lt_top (I := I) (M := M) g α hKts_compact hKts_sub)
