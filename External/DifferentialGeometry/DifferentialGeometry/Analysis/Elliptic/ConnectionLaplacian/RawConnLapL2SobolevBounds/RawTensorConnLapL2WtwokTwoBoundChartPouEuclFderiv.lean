import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartReprDerivativeBounds.ChartPulledCovDerivChartCompBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartReprDerivativeBounds.IteratedFDerivTensorReprChartCompBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RawConnLapPointwiseFiberBounds.RawTensorConnLapChartTargetSqBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RawConnLapL2SobolevBounds.RawTensorConnLapChartL2PouBridge
import DifferentialGeometry.Analysis.Sobolev.Tensor.Defs
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Embedding.FderivToWkpNormBridge
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Embedding.IteratedFderivToWkpNormBridge
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.ChartGeometry.GoodSetMeasure
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.ChartTransition.TensorChartTransition
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.CovApplyAndSlotCorrectionBounds.SlotCorrectionChartFderivBound


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold Set IsManifold ContinuousLinearMap Filter
open MeasureTheory
open scoped Manifold Topology Bundle ContDiff BigOperators ENNReal NNReal

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Tensor
open Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Sobolev.Tensor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

local notation "EuclN" =>
  EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

noncomputable def chartPouEucl (α : M) : EuclN → ℝ := by
  classical
  exact fun y =>
    if y ∈ chartTargetEuclid (I := I) (M := M) α then
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
    else 0

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
private lemma chartPouEucl_apply_of_mem (α : M) {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    chartPouEucl (I := I) (M := M) α y =
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := by
  classical
  unfold chartPouEucl; exact if_pos hy

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
private lemma chartPouEucl_apply_of_notMem (α : M) {y : EuclN}
    (hy : y ∉ chartTargetEuclid (I := I) (M := M) α) :
    chartPouEucl (I := I) (M := M) α y = 0 := by
  classical
  unfold chartPouEucl; exact if_neg hy

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
lemma chartPouEucl_contDiff (α : M) :
    ContDiff ℝ ∞ (chartPouEucl (I := I) (M := M) α) := by
  classical
  set f : M → ℝ := fun x : M =>
    ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x with hf_def
  have hf_smooth : ContMDiff I (𝓘(ℝ, ℝ)) ∞ f :=
    (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff
  have hf_supp : tsupport f ⊆ (chartAt H α).source :=
    chartAtlasPOU_isSubordinate I M α
  set K : Set EuclN :=
    (toEuclidean (E := E)) '' ((extChartAt I α) '' (tsupport f)) with hK_def
  have hf_compact : IsCompact (tsupport f) := (isClosed_tsupport _).isCompact
  have hsub_target : tsupport f ⊆ (extChartAt I α).source := by
    intro x hx
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    exact hf_supp hx
  have hcont_chart : ContinuousOn (extChartAt I α) (tsupport f) :=
    (continuousOn_extChartAt α).mono hsub_target
  have hK_compact_M : IsCompact ((extChartAt I α) '' (tsupport f)) :=
    hf_compact.image_of_continuousOn hcont_chart
  have hK_compact : IsCompact K :=
    hK_compact_M.image (toEuclidean (E := E)).continuous
  have hK_closed : IsClosed K := hK_compact.isClosed
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy_target :
      y ∈ chartTargetEuclid (I := I) (M := M) α
  · have hOpen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
      chartTargetEuclid_isOpen (I := I) (M := M) α
    have hformula_smooth :
        ContDiffOn ℝ ∞
          (fun z : EuclN =>
            f ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)))
          (chartTargetEuclid (I := I) (M := M) α) := by
      have hscalar : ContDiffOn ℝ ∞
          (fun z : E => f ((extChartAt I α).symm z))
          (extChartAt I α).target :=
        DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE_contDiffOn
          (I := I) α hf_smooth
      have htoEuc_symm_smooth : ContDiff ℝ ∞ ((toEuclidean (E := E)).symm) :=
        ContinuousLinearEquiv.contDiff _
      have hmaps : Set.MapsTo ((toEuclidean (E := E)).symm)
          (chartTargetEuclid (I := I) (M := M) α)
          (extChartAt I α).target := by
        intro z hz
        rcases hz with ⟨w, hw_target, hwz⟩
        have h_eq : (toEuclidean (E := E)).symm z = w := by
          rw [← hwz]; exact (toEuclidean (E := E)).symm_apply_apply w
        rw [h_eq]; exact hw_target
      exact hscalar.comp htoEuc_symm_smooth.contDiffOn hmaps
    have hwithin : ContDiffWithinAt ℝ ∞
        (fun z : EuclN =>
          f ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)))
        (chartTargetEuclid (I := I) (M := M) α) y := hformula_smooth y hy_target
    have hformula_at : ContDiffAt ℝ ∞
        (fun z : EuclN =>
          f ((extChartAt I α).symm ((toEuclidean (E := E)).symm z))) y :=
      hwithin.contDiffAt (hOpen.mem_nhds hy_target)
    refine hformula_at.congr_of_eventuallyEq ?_
    filter_upwards [hOpen.mem_nhds hy_target] with z hz
    exact (chartPouEucl_apply_of_mem (I := I) (M := M) α hz)
  · have hcarrier_subset_target :
        K ⊆ chartTargetEuclid (I := I) (M := M) α := by
      intro z hz_carrier
      rcases hz_carrier with ⟨w, ⟨x, hx_supp, hxw⟩, hwz⟩
      have hx_src : x ∈ (extChartAt I α).source := hsub_target hx_supp
      have hw_target : w ∈ (extChartAt I α).target := by
        rw [← hxw]; exact (extChartAt I α).map_source hx_src
      exact ⟨w, hw_target, hwz⟩
    have hy_off : y ∉ K := fun hy_in =>
      hy_target (hcarrier_subset_target hy_in)
    have hK_compl_open : IsOpen Kᶜ := hK_closed.isOpen_compl
    apply ContDiffAt.congr_of_eventuallyEq
      (f := fun _ : EuclN => (0 : ℝ)) contDiffAt_const
    filter_upwards [hK_compl_open.mem_nhds hy_off] with z hz
    by_cases hz_target :
        z ∈ chartTargetEuclid (I := I) (M := M) α
    · obtain ⟨w, hw_target, hwz⟩ := hz_target
      have hz_target' :
          z ∈ chartTargetEuclid (I := I) (M := M) α := ⟨w, hw_target, hwz⟩
      have h_eq : (toEuclidean (E := E)).symm z = w := by
        rw [← hwz]; exact (toEuclidean (E := E)).symm_apply_apply w
      rw [chartPouEucl_apply_of_mem (I := I) (M := M) α hz_target']
      by_contra hne_f
      apply hz
      have hin_supp : (extChartAt I α).symm ((toEuclidean (E := E)).symm z) ∈
          tsupport f := subset_tsupport _ hne_f
      rw [h_eq] at hin_supp
      have hext_right : (extChartAt I α) ((extChartAt I α).symm w) = w :=
        (extChartAt I α).right_inv hw_target
      refine ⟨w, ⟨(extChartAt I α).symm w, hin_supp, hext_right⟩, hwz⟩
    · exact chartPouEucl_apply_of_notMem (I := I) (M := M) α hz_target

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] in
lemma chartPouEucl_hasCompactSupport (α : M) :
    HasCompactSupport (chartPouEucl (I := I) (M := M) α) := by
  classical
  set f : M → ℝ := fun x : M =>
    ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x with hf_def
  have hf_supp : tsupport f ⊆ (chartAt H α).source :=
    chartAtlasPOU_isSubordinate I M α
  set K : Set EuclN :=
    (toEuclidean (E := E)) '' ((extChartAt I α) '' (tsupport f)) with hK_def
  have hf_compact : IsCompact (tsupport f) := (isClosed_tsupport _).isCompact
  have hsub_target : tsupport f ⊆ (extChartAt I α).source := by
    intro x hx
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    exact hf_supp hx
  have hcont_chart : ContinuousOn (extChartAt I α) (tsupport f) :=
    (continuousOn_extChartAt α).mono hsub_target
  have hK_compact_M : IsCompact ((extChartAt I α) '' (tsupport f)) :=
    hf_compact.image_of_continuousOn hcont_chart
  have hK_compact : IsCompact K :=
    hK_compact_M.image (toEuclidean (E := E)).continuous
  have hK_closed : IsClosed K := hK_compact.isClosed
  apply HasCompactSupport.intro (K := K) hK_compact
  intro y hy_notK
  by_cases hy_target :
      y ∈ chartTargetEuclid (I := I) (M := M) α
  · obtain ⟨w, hw_target, hwy⟩ := hy_target
    have h_eq : (toEuclidean (E := E)).symm y = w := by
      rw [← hwy]; exact (toEuclidean (E := E)).symm_apply_apply w
    rw [chartPouEucl_apply_of_mem (I := I) (M := M) α
        ⟨w, hw_target, hwy⟩]
    by_contra hne_f
    apply hy_notK
    have hin_supp : (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∈
        tsupport f := subset_tsupport _ hne_f
    rw [h_eq] at hin_supp
    have hext_right : (extChartAt I α) ((extChartAt I α).symm w) = w :=
      (extChartAt I α).right_inv hw_target
    refine ⟨w, ⟨(extChartAt I α).symm w, hin_supp, hext_right⟩, hwy⟩
  · exact chartPouEucl_apply_of_notMem (I := I) (M := M) α hy_target

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private lemma exists_chartPouEucl_fderiv_uniform_bound (α : M) :
    ∃ K_pou : ℝ, 0 ≤ K_pou ∧
      ∀ y : EuclN, ‖fderiv ℝ (chartPouEucl (I := I) (M := M) α) y‖ ≤ K_pou := by
  classical
  have hCD : ContDiff ℝ ∞ (chartPouEucl (I := I) (M := M) α) :=
    chartPouEucl_contDiff (I := I) (M := M) α
  have hHCS : HasCompactSupport (chartPouEucl (I := I) (M := M) α) :=
    chartPouEucl_hasCompactSupport (I := I) (M := M) α
  have h_fderiv_cont : Continuous (fun y : EuclN =>
      fderiv ℝ (chartPouEucl (I := I) (M := M) α) y) :=
    hCD.continuous_fderiv (by norm_num)
  have h_fderiv_compactSupport : HasCompactSupport (fun y : EuclN =>
      fderiv ℝ (chartPouEucl (I := I) (M := M) α) y) :=
    hHCS.fderiv ℝ
  obtain ⟨K_raw, hK_bound⟩ := h_fderiv_cont.bounded_above_of_compact_support
    h_fderiv_compactSupport
  refine ⟨max K_raw 0, le_max_right _ _, ?_⟩
  intro y
  exact le_trans (hK_bound y) (le_max_left _ _)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma tensorChartComponentRaw_symm_contDiffOn_target
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
        (extChartAt I α).symm) ((extChartAt I α).target) := by
  classical
  have hsmooth_on := tensorChartComponentRaw_contMDiffOn_chart_source
    (I := I) (M := M) g r s T α Idx Jdx
  have hsymm : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I α).symm
      (extChartAt I α).target := contMDiffOn_extChartAt_symm (I := I) α
  have hmaps : Set.MapsTo (extChartAt I α).symm (extChartAt I α).target
      (chartAt H α).source := by
    intro e he_tgt
    have hsrc : (extChartAt I α).symm e ∈ (extChartAt I α).source :=
      (extChartAt I α).map_target he_tgt
    rwa [extChartAt_source] at hsrc
  have hcomp : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞
      (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
        (extChartAt I α).symm) (extChartAt I α).target :=
    hsmooth_on.comp hsymm hmaps
  exact hcomp.contDiffOn

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
lemma chartAtlasPOU_symm_contDiffOn_target (α : M) :
    ContDiffOn ℝ ∞
      ((fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∘
        (extChartAt I α).symm) ((extChartAt I α).target) := by
  classical
  have hf_smooth : ContMDiff I (𝓘(ℝ, ℝ)) ∞
      (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) :=
    (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff
  exact DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE_contDiffOn
    (I := I) α hf_smooth

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] in
lemma chartAtlasPOU_symm_differentiableAt
    (α : M) {e : E} (he : e ∈ (extChartAt I α).target) :
    DifferentiableAt ℝ
      ((fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∘
        (extChartAt I α).symm) e := by
  have hcd := chartAtlasPOU_symm_contDiffOn_target (I := I) (M := M) α
  have h_open : IsOpen (extChartAt I α).target := isOpen_extChartAt_target (I := I) α
  have hwithin : DifferentiableWithinAt ℝ
      ((fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∘
        (extChartAt I α).symm) ((extChartAt I α).target) e :=
    (hcd _ he).differentiableWithinAt (by norm_num)
  exact hwithin.differentiableAt (h_open.mem_nhds he)

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
lemma tensorChartComponentRaw_symm_differentiableAt
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {e : E} (he : e ∈ (extChartAt I α).target) :
    DifferentiableAt ℝ
      (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
        (extChartAt I α).symm) e := by
  have hcd := tensorChartComponentRaw_symm_contDiffOn_target
    (I := I) (M := M) g r s T α Idx Jdx
  have h_open : IsOpen (extChartAt I α).target := isOpen_extChartAt_target (I := I) α
  have hwithin : DifferentiableWithinAt ℝ
      (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
        (extChartAt I α).symm) ((extChartAt I α).target) e :=
    (hcd _ he).differentiableWithinAt (by norm_num)
  exact hwithin.differentiableAt (h_open.mem_nhds he)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
private lemma tensorChartComp_eq_pou_mul_raw_pulled
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    tensorChartComp (I := I) (M := M) g r s T α Idx Jdx y =
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
        tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := by
  rw [tensorChartComp_apply_of_mem (I := I) (M := M) g r s T α Idx Jdx hy]
  unfold tensorChartComponentPou
  rfl

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma tensorChartComp_toEuclidean_eq_pou_mul_raw
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {e : E} (he : e ∈ (extChartAt I α).target) :
    tensorChartComp (I := I) (M := M) g r s T α Idx Jdx
        ((toEuclidean (E := E)) e) =
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
          ((extChartAt I α).symm e) *
        tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
          ((extChartAt I α).symm e) := by
  have hy : (toEuclidean (E := E)) e ∈ chartTargetEuclid (I := I) (M := M) α :=
    ⟨e, he, rfl⟩
  have h_eq : (toEuclidean (E := E)).symm ((toEuclidean (E := E)) e) = e :=
    (toEuclidean (E := E)).symm_apply_apply e
  rw [tensorChartComp_eq_pou_mul_raw_pulled
    (I := I) (M := M) g r s T α Idx Jdx hy, h_eq]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma pou_mul_raw_eq_tensorChartComp_toEuclidean
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {e : E} (he : e ∈ (extChartAt I α).target) :
    ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
          ((extChartAt I α).symm e) *
        tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
          ((extChartAt I α).symm e) =
      tensorChartComp (I := I) (M := M) g r s T α Idx Jdx
        ((toEuclidean (E := E)) e) :=
  (tensorChartComp_toEuclidean_eq_pou_mul_raw
    (I := I) (M := M) g r s T α Idx Jdx he).symm

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
private lemma chartPouEucl_toEuclidean_eq_pou_symm
    (α : M) {e : E} (he : e ∈ (extChartAt I α).target) :
    chartPouEucl (I := I) (M := M) α ((toEuclidean (E := E)) e) =
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
          ((extChartAt I α).symm e) := by
  have hy : (toEuclidean (E := E)) e ∈ chartTargetEuclid (I := I) (M := M) α :=
    ⟨e, he, rfl⟩
  have h_eq : (toEuclidean (E := E)).symm ((toEuclidean (E := E)) e) = e :=
    (toEuclidean (E := E)).symm_apply_apply e
  rw [chartPouEucl_apply_of_mem (I := I) (M := M) α hy, h_eq]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
private lemma pou_mul_raw_symm_eventuallyEq_tensorChartComp_toEuclidean
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {e : E} (he : e ∈ (extChartAt I α).target) :
    (fun e' : E =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
          ((extChartAt I α).symm e') *
        tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
          ((extChartAt I α).symm e'))
      =ᶠ[𝓝 e]
      (fun e' : E => tensorChartComp (I := I) (M := M) g r s T α Idx Jdx
        ((toEuclidean (E := E)) e')) := by
  have h_open : IsOpen (extChartAt I α).target := isOpen_extChartAt_target (I := I) α
  filter_upwards [h_open.mem_nhds he] with e' he'
  exact pou_mul_raw_eq_tensorChartComp_toEuclidean
    (I := I) (M := M) g r s T α Idx Jdx he'

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
lemma fderiv_pou_mul_raw_symm_eq_fderiv_tensorChartComp_toEuclidean
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {e : E} (he : e ∈ (extChartAt I α).target) :
    fderiv ℝ
        (fun e' : E =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
            ((extChartAt I α).symm e') *
          tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
            ((extChartAt I α).symm e')) e =
      fderiv ℝ
        (fun e' : E => tensorChartComp (I := I) (M := M) g r s T α Idx Jdx
          ((toEuclidean (E := E)) e')) e :=
  (pou_mul_raw_symm_eventuallyEq_tensorChartComp_toEuclidean
    (I := I) (M := M) g r s T α Idx Jdx he).fderiv_eq

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
lemma fderiv_tensorChartComp_toEuclidean
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) (e : E) :
    fderiv ℝ
        (fun e' : E => tensorChartComp (I := I) (M := M) g r s T α Idx Jdx
          ((toEuclidean (E := E)) e')) e =
      (fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
          ((toEuclidean (E := E)) e)).comp
        (toEuclidean (E := E) : E →L[ℝ] EuclN) := by
  classical
  have htoE_smooth : ContDiff ℝ ∞ ((toEuclidean (E := E)) : E → EuclN) :=
    ContinuousLinearEquiv.contDiff _
  have hcomp_smooth : ContDiff ℝ ∞
      (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx) :=
    tensorChartComp_contDiff (I := I) (M := M) g r s T α Idx Jdx
  have h_chain : fderiv ℝ
      ((tensorChartComp (I := I) (M := M) g r s T α Idx Jdx) ∘
        ((toEuclidean (E := E)) : E → EuclN)) e =
      (fderiv ℝ (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
          (((toEuclidean (E := E)) : E → EuclN) e)).comp
        (fderiv ℝ ((toEuclidean (E := E)) : E → EuclN) e) := by
    apply fderiv_comp e
    · exact (hcomp_smooth.differentiable (by norm_num)).differentiableAt
    · exact (htoE_smooth.differentiable (by norm_num)).differentiableAt
  rw [show (fun e' : E => tensorChartComp (I := I) (M := M) g r s T α Idx Jdx
        ((toEuclidean (E := E)) e')) =
      (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx) ∘
        ((toEuclidean (E := E)) : E → EuclN) from rfl]
  rw [h_chain]
  congr 1
  exact (toEuclidean (E := E)).fderiv

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private lemma fderiv_chartPouEucl_toEuclidean (α : M) (e : E) :
    fderiv ℝ
        (fun e' : E => chartPouEucl (I := I) (M := M) α
          ((toEuclidean (E := E)) e')) e =
      (fderiv ℝ (chartPouEucl (I := I) (M := M) α)
          ((toEuclidean (E := E)) e)).comp
        (toEuclidean (E := E) : E →L[ℝ] EuclN) := by
  classical
  have htoE_smooth : ContDiff ℝ ∞ ((toEuclidean (E := E)) : E → EuclN) :=
    ContinuousLinearEquiv.contDiff _
  have hpou_smooth : ContDiff ℝ ∞ (chartPouEucl (I := I) (M := M) α) :=
    chartPouEucl_contDiff (I := I) (M := M) α
  have h_chain : fderiv ℝ
      ((chartPouEucl (I := I) (M := M) α) ∘
        ((toEuclidean (E := E)) : E → EuclN)) e =
      (fderiv ℝ (chartPouEucl (I := I) (M := M) α)
          (((toEuclidean (E := E)) : E → EuclN) e)).comp
        (fderiv ℝ ((toEuclidean (E := E)) : E → EuclN) e) := by
    apply fderiv_comp e
    · exact (hpou_smooth.differentiable (by norm_num)).differentiableAt
    · exact (htoE_smooth.differentiable (by norm_num)).differentiableAt
  rw [show (fun e' : E => chartPouEucl (I := I) (M := M) α
        ((toEuclidean (E := E)) e')) =
      (chartPouEucl (I := I) (M := M) α) ∘
        ((toEuclidean (E := E)) : E → EuclN) from rfl]
  rw [h_chain]
  congr 1
  exact (toEuclidean (E := E)).fderiv

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] in
lemma pou_symm_eventuallyEq_chartPouEucl_toEuclidean
    (α : M) {e : E} (he : e ∈ (extChartAt I α).target) :
    (fun e' : E => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
        ((extChartAt I α).symm e'))
      =ᶠ[𝓝 e]
      (fun e' : E => chartPouEucl (I := I) (M := M) α
        ((toEuclidean (E := E)) e')) := by
  have h_open : IsOpen (extChartAt I α).target := isOpen_extChartAt_target (I := I) α
  filter_upwards [h_open.mem_nhds he] with e' he'
  exact (chartPouEucl_toEuclidean_eq_pou_symm (I := I) (M := M) α he').symm

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private lemma fderiv_pou_symm_eq
    (α : M) {e : E} (he : e ∈ (extChartAt I α).target) :
    fderiv ℝ
        (fun e' : E => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
          ((extChartAt I α).symm e')) e =
      (fderiv ℝ (chartPouEucl (I := I) (M := M) α)
          ((toEuclidean (E := E)) e)).comp
        (toEuclidean (E := E) : E →L[ℝ] EuclN) := by
  rw [(pou_symm_eventuallyEq_chartPouEucl_toEuclidean
    (I := I) (M := M) α he).fderiv_eq]
  exact fderiv_chartPouEucl_toEuclidean (I := I) (M := M) α e

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
lemma exists_pou_symm_fderiv_uniform_bound (α : M) :
    ∃ K_pou : ℝ, 0 ≤ K_pou ∧
      ∀ e ∈ (extChartAt I α).target,
        ‖fderiv ℝ
          (fun e' : E => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
            ((extChartAt I α).symm e')) e‖ ≤ K_pou := by
  classical
  obtain ⟨K_eucl, hK_nn, hK_bound⟩ :=
    exists_chartPouEucl_fderiv_uniform_bound (I := I) (M := M) α
  set NtoE : ℝ := ‖(toEuclidean (E := E) : E →L[ℝ] EuclN)‖ with hNtoE_def
  have hNtoE_nn : 0 ≤ NtoE := norm_nonneg _
  refine ⟨K_eucl * NtoE, mul_nonneg hK_nn hNtoE_nn, ?_⟩
  intro e he
  rw [fderiv_pou_symm_eq (I := I) (M := M) α he]
  have hbound : ‖(fderiv ℝ (chartPouEucl (I := I) (M := M) α)
        ((toEuclidean (E := E)) e)).comp
        (toEuclidean (E := E) : E →L[ℝ] EuclN)‖ ≤
      ‖fderiv ℝ (chartPouEucl (I := I) (M := M) α)
        ((toEuclidean (E := E)) e)‖ *
      ‖(toEuclidean (E := E) : E →L[ℝ] EuclN)‖ :=
    ContinuousLinearMap.opNorm_comp_le _ _
  refine le_trans hbound ?_
  exact mul_le_mul_of_nonneg_right (hK_bound _) hNtoE_nn

end Connection
end Integral
end DifferentialGeometry

end
