import DifferentialGeometry.Analysis.Integration.Measure.MeasureBridge
import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.Defs
import DifferentialGeometry.Tensor.RSTensor.Defs

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function Tensor0SBundle
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry
namespace Integral
namespace Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" =>
  EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

open DifferentialGeometry.Analysis.Sobolev.Chart

variable (I) in

def tensorTrivProjPushedNormSq
    (_g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : Π b : M, TensorRSSpace r s I b) : EuclN → ℝ := by
  classical
  exact fun y =>
    if y ∈ chartTargetEuclid (I := I) (M := M) α then
      ‖TensorRSSpace.toModel
        (S ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))‖ ^ 2
    else 0

@[simp]
lemma tensorTrivProjPushedNormSq_apply_of_mem
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : Π b : M, TensorRSSpace r s I b)
    {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    tensorTrivProjPushedNormSq (I := I) (M := M) g r s α S y =
      ‖TensorRSSpace.toModel
        (S ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))‖ ^ 2 := by
  classical
  unfold tensorTrivProjPushedNormSq
  simp [hy]

@[simp]
lemma tensorTrivProjPushedNormSq_apply_of_notMem
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : Π b : M, TensorRSSpace r s I b)
    {y : EuclN}
    (hy : y ∉ chartTargetEuclid (I := I) (M := M) α) :
    tensorTrivProjPushedNormSq (I := I) (M := M) g r s α S y = 0 := by
  classical
  unfold tensorTrivProjPushedNormSq
  simp [hy]

lemma tensorTrivProjPushedNormSq_eq_zero_off_chartTargetEuclid
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : Π b : M, TensorRSSpace r s I b)
    (y : EuclN)
    (hy : y ∉ chartTargetEuclid (I := I) (M := M) α) :
    tensorTrivProjPushedNormSq (I := I) (M := M) g r s α S y = 0 :=
  tensorTrivProjPushedNormSq_apply_of_notMem (I := I) (M := M) g r s α S hy

lemma tensorTrivProjPushedNormSq_nonneg
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : Π b : M, TensorRSSpace r s I b)
    (y : EuclN) :
    0 ≤ tensorTrivProjPushedNormSq (I := I) (M := M) g r s α S y := by
  classical
  unfold tensorTrivProjPushedNormSq
  split_ifs with hy
  · exact sq_nonneg _
  · exact le_rfl

theorem tensorTrivProjPushedNormSq_continuousOn_chartTarget
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : Π b : M, TensorRSSpace r s I b)
    (hS : ContinuousOn
      (fun x : M => ‖TensorRSSpace.toModel (S x)‖ ^ 2)
      ((chartAt H α).source)) :
    ContinuousOn (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α S)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have hcomp : ContinuousOn
      (fun y : EuclN =>
        ‖TensorRSSpace.toModel
          (S ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))‖ ^ 2)
      (chartTargetEuclid (I := I) (M := M) α) := by
    have hmaps : MapsTo
        (fun y : EuclN =>
          (extChartAt I α).symm ((toEuclidean (E := E)).symm y))
        (chartTargetEuclid (I := I) (M := M) α)
        ((chartAt H α).source) := by
      intro y hy
      exact symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) α hy
    have hcont :=
      continuousOn_symm_toEuclideanSymm (I := I) (M := M) (α := α)
    exact hS.comp hcont hmaps
  refine ContinuousOn.congr hcomp ?_
  intro y hy
  exact tensorTrivProjPushedNormSq_apply_of_mem (I := I) (M := M) g r s α S hy

private lemma tensorTrivProjPushedNormSq_eq_zero_off_image_tsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : Π b : M, TensorRSSpace r s I b)
    {y : EuclN}
    (hy_target : y ∈ chartTargetEuclid (I := I) (M := M) α)
    (hy_off :
      y ∉ toEuclidean ''
        ((extChartAt I α) '' (tsupport
          (fun x : M => ‖TensorRSSpace.toModel (S x)‖ ^ 2)))) :
    tensorTrivProjPushedNormSq (I := I) (M := M) g r s α S y = 0 := by
  classical
  rw [tensorTrivProjPushedNormSq_apply_of_mem (I := I) (M := M) g r s α S hy_target]
  set x : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hx_def
  by_contra hne
  apply hy_off
  obtain ⟨z, hz_target, hzy⟩ := hy_target
  have hsym_eq : (toEuclidean (E := E)).symm y = z := by
    rw [← hzy]; exact (toEuclidean (E := E)).symm_apply_apply z
  have hxz : x = (extChartAt I α).symm z := by
    rw [hx_def, hsym_eq]
  have hx_supp :
      x ∈ tsupport (fun x : M => ‖TensorRSSpace.toModel (S x)‖ ^ 2) :=
    subset_tsupport _ (Function.mem_support.mpr hne)
  refine ⟨z, ⟨x, hx_supp, ?_⟩, hzy⟩
  rw [hxz]
  exact (extChartAt I α).right_inv hz_target

theorem tensorTrivProjPushedNormSq_hasCompactSupport
    [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : Π b : M, TensorRSSpace r s I b)
    (hS_supp :
      tsupport (fun x : M => ‖TensorRSSpace.toModel (S x)‖ ^ 2) ⊆
        (chartAt H α).source) :
    HasCompactSupport
      (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α S) := by
  classical
  set u : M → ℝ := fun x => ‖TensorRSSpace.toModel (S x)‖ ^ 2 with hu_def
  obtain ⟨hcompact_image, hsub_target⟩ :=
    image_extChartAt_tsupport_compact_subset_target
      (I := I) (M := M) (u := u) (α := α) hS_supp
  set K : Set EuclN := toEuclidean '' ((extChartAt I α) '' (tsupport u)) with hK_def
  have hK_compact : IsCompact K :=
    hcompact_image.image (toEuclidean (E := E)).continuous
  refine HasCompactSupport.of_support_subset_isCompact hK_compact ?_
  intro y hy_supp
  by_contra hy_notK
  apply hy_supp
  by_cases hy_target : y ∈ chartTargetEuclid (I := I) (M := M) α
  · exact tensorTrivProjPushedNormSq_eq_zero_off_image_tsupport
      (I := I) (M := M) g r s α S hy_target hy_notK
  · exact tensorTrivProjPushedNormSq_apply_of_notMem
      (I := I) (M := M) g r s α S hy_target

omit [IsManifold I ∞ M] in
private lemma chartTargetEuclid_measurableSet'
    (α : M) :
    MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
  chartTargetEuclid_measurableSet (I := I) (M := M) α

theorem tensorTrivProjPushedNormSq_measurable
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : Π b : M, TensorRSSpace r s I b)
    (hS_meas :
      Measurable (fun x : M => ‖TensorRSSpace.toModel (S x)‖ ^ 2)) :
    Measurable (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α S) := by
  classical
  set u : M → ℝ := fun x => ‖TensorRSSpace.toModel (S x)‖ ^ 2 with hu_def
  have hsymm_glob_meas :
      Measurable (fun y : E =>
        ((extChartAt I α).target.piecewise
          (fun y : E => (extChartAt I α).symm y)
          (fun _ : E => α)) y) := by
    refine ContinuousOn.measurable_piecewise
      (continuousOn_extChartAt_symm (I := I) α) continuousOn_const ?_
    exact DifferentialGeometry.Integral.Measure.measurableSet_extChartAt_target
      (I := I) (M := M) α
  have hu_pull :
      Measurable (fun y : E =>
        u (((extChartAt I α).target.piecewise
              (fun y : E => (extChartAt I α).symm y)
              (fun _ : E => α)) y)) :=
    hS_meas.comp hsymm_glob_meas
  have htoEucl :
      Measurable ((toEuclidean (E := E)).symm : EuclN → E) :=
    (toEuclidean (E := E)).symm.continuous.measurable
  have hu_pull' :
      Measurable (fun z : EuclN =>
        u (((extChartAt I α).target.piecewise
              (fun y : E => (extChartAt I α).symm y)
              (fun _ : E => α)) ((toEuclidean (E := E)).symm z))) :=
    hu_pull.comp htoEucl
  have hindic_meas :
      Measurable ((chartTargetEuclid (I := I) (M := M) α).indicator
        (fun z : EuclN =>
          u (((extChartAt I α).target.piecewise
                (fun y : E => (extChartAt I α).symm y)
                (fun _ : E => α)) ((toEuclidean (E := E)).symm z)))) :=
    hu_pull'.indicator (chartTargetEuclid_measurableSet' (I := I) (M := M) α)
  have heq :
      tensorTrivProjPushedNormSq (I := I) (M := M) g r s α S =
        (chartTargetEuclid (I := I) (M := M) α).indicator
          (fun z : EuclN =>
            u (((extChartAt I α).target.piecewise
                  (fun y : E => (extChartAt I α).symm y)
                  (fun _ : E => α)) ((toEuclidean (E := E)).symm z))) := by
    funext y
    by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
    · rw [tensorTrivProjPushedNormSq_apply_of_mem
            (I := I) (M := M) g r s α S hy]
      rw [Set.indicator_of_mem hy]
      have hy_target : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
        have hpre :
            chartTargetEuclid (I := I) (M := M) α =
              (toEuclidean (E := E)).symm ⁻¹' (extChartAt I α).target :=
          chartTargetEuclid_eq_preimage_symm (I := I) (M := M) (α := α)
        rw [hpre] at hy; exact hy
      rw [Set.piecewise_eq_of_mem _ _ _ hy_target]
    · rw [tensorTrivProjPushedNormSq_apply_of_notMem
            (I := I) (M := M) g r s α S hy]
      rw [Set.indicator_of_notMem hy]
  rw [heq]
  exact hindic_meas

theorem tensorTrivProjPushedNormSq_integrableOn
    [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : Π b : M, TensorRSSpace r s I b)
    (hS_meas :
      Measurable (fun x : M => ‖TensorRSSpace.toModel (S x)‖ ^ 2))
    (hS_supp :
      tsupport (fun x : M => ‖TensorRSSpace.toModel (S x)‖ ^ 2) ⊆
        (chartAt H α).source)
    (hS_cont :
      ContinuousOn
        (fun x : M => ‖TensorRSSpace.toModel (S x)‖ ^ 2)
        ((chartAt H α).source)) :
    IntegrableOn (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α S)
      (chartTargetEuclid (I := I) (M := M) α)
      (volume : MeasureTheory.Measure EuclN) := by
  classical
  have hmeas :
      Measurable (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α S) :=
    tensorTrivProjPushedNormSq_measurable
      (I := I) (M := M) g r s α S hS_meas
  have hcont_target :
      ContinuousOn (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α S)
        (chartTargetEuclid (I := I) (M := M) α) :=
    tensorTrivProjPushedNormSq_continuousOn_chartTarget
      (I := I) (M := M) g r s α S hS_cont
  set u : M → ℝ := fun x => ‖TensorRSSpace.toModel (S x)‖ ^ 2 with hu_def
  obtain ⟨hK_compact_image, _hK_sub_target⟩ :=
    image_extChartAt_tsupport_compact_subset_target
      (I := I) (M := M) (u := u) (α := α) hS_supp
  set K : Set EuclN := toEuclidean '' ((extChartAt I α) '' (tsupport u)) with hK_def
  have hK_compact : IsCompact K :=
    hK_compact_image.image (toEuclidean (E := E)).continuous
  have hK_sub :
      K ⊆ chartTargetEuclid (I := I) (M := M) α :=
    image_toEuclidean_extChartAt_tsupport_subset_chartTargetEuclid
      (I := I) (M := M) (u := u) (α := α) hS_supp
  have hcont_K :
      ContinuousOn (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α S) K :=
    hcont_target.mono hK_sub
  have hint_K :
      IntegrableOn (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α S) K
        (volume : MeasureTheory.Measure EuclN) :=
    ContinuousOn.integrableOn_compact hK_compact hcont_K
  have hzero_off_K : ∀ y, y ∉ K →
      tensorTrivProjPushedNormSq (I := I) (M := M) g r s α S y = 0 := by
    intro y hy_notK
    by_cases hy_target : y ∈ chartTargetEuclid (I := I) (M := M) α
    · exact tensorTrivProjPushedNormSq_eq_zero_off_image_tsupport
        (I := I) (M := M) g r s α S hy_target hy_notK
    · exact tensorTrivProjPushedNormSq_apply_of_notMem
        (I := I) (M := M) g r s α S hy_target
  have hf_integrable :
      Integrable (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α S)
        (volume : MeasureTheory.Measure EuclN) := by
    have hindic_eq :
        tensorTrivProjPushedNormSq (I := I) (M := M) g r s α S =
          K.indicator (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α S) := by
      funext y
      by_cases hy_K : y ∈ K
      · rw [Set.indicator_of_mem hy_K]
      · rw [Set.indicator_of_notMem hy_K, hzero_off_K y hy_K]
    rw [hindic_eq]
    exact hint_K.integrable_indicator hK_compact.measurableSet
  exact hf_integrable.integrableOn

end Measure
end Integral
end DifferentialGeometry

end
