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
import Verified.ClosedSurface_DifferentialGeometry_Analysis_Integration_Measure_ChartDensity
import Verified.ClosedSurface_DifferentialGeometry_Analysis_Integration_Measure_Invariance
import Verified.ClosedSurface_DifferentialGeometry_Analysis_Integration_Measure_RiemannianMeasure
import Verified.ClosedSurface_DifferentialGeometry_Bundle_TangentSpace
import Verified.ClosedSurface_DifferentialGeometry_Geometry_Metric_ChartGram

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

 local instance _root_.OpenGAExport.DifferentialGeometry.Analysis.Integration.Measure.Properties.instance_46 : MeasurableSpace E := borel E

 local instance _root_.OpenGAExport.DifferentialGeometry.Analysis.Integration.Measure.Properties.instance_47 : BorelSpace E := ⟨rfl⟩

 local instance _root_.OpenGAExport.DifferentialGeometry.Analysis.Integration.Measure.Properties.instance_48 : MeasurableSpace M := borel M

 local instance _root_.OpenGAExport.DifferentialGeometry.Analysis.Integration.Measure.Properties.instance_49 : BorelSpace M := ⟨rfl⟩

theorem chartLocalMeasure_compact_lt_top
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

theorem riemannianMeasure_compact_lt_top
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
