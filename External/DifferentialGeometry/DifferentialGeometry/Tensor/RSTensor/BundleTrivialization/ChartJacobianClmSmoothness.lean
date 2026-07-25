import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Tangent
import Mathlib.Geometry.Manifold.MFDeriv.UniqueDifferential
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Dimension.Free


noncomputable section

open Bundle Set IsManifold ContinuousLinearMap
open scoped Manifold Topology Bundle ContDiff

namespace DifferentialGeometry
namespace Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [Module.Finite ℝ E] in
theorem contMDiffAt_tangentTrivialization_coordChangeL_alpha_to_b0
    (α : M) {b₀ : M} (hb₀ : b₀ ∈ (chartAt H α).source) :
    ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E) ∞
      (fun b : M =>
        ((trivializationAt E (TangentSpace I) b₀).continuousLinearMapAt ℝ b ∘L
          (trivializationAt E (TangentSpace I) α).symmL ℝ b
            : E →L[ℝ] E))
      b₀ := by
  classical
  have hα_src : b₀ ∈ (chartAt H α).source := hb₀
  set u := (extChartAt I α).target with hu_def
  have hf_on : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I α).symm u :=
    contMDiffOn_extChartAt_symm α
  have hyb₀ : extChartAt I α b₀ ∈ u := by
    have : extChartAt I α b₀ ∈ (extChartAt I α).target :=
      (extChartAt I α).map_source (by simpa [extChartAt_source] using hα_src)
    simpa [u] using this
  have hf_at : ContMDiffWithinAt 𝓘(ℝ, E) I ∞
      (extChartAt I α).symm u (extChartAt I α b₀) := hf_on _ hyb₀
  have hu_uniq : UniqueMDiffOn 𝓘(ℝ, E) u := by
    have hroot : UniqueMDiffOn 𝓘(ℝ, E)
        ((extChartAt I α).target ∩ (extChartAt I α).symm ⁻¹' (univ : Set M)) :=
      UniqueMDiffOn.uniqueMDiffOn_target_inter
        (uniqueMDiffOn_univ : UniqueMDiffOn I (univ : Set M)) α
    have hset_eq : (extChartAt I α).target ∩ (extChartAt I α).symm ⁻¹' univ
        = (extChartAt I α).target := by
      simp
    rw [hset_eq] at hroot
    exact hroot
  have hmfderiv :
      ContMDiffWithinAt 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] E) ∞
        (inTangentCoordinates 𝓘(ℝ, E) I id (extChartAt I α).symm
          (mfderivWithin 𝓘(ℝ, E) I (extChartAt I α).symm u) (extChartAt I α b₀))
        u (extChartAt I α b₀) := by
    have := ContMDiffWithinAt.mfderivWithin_const (I := 𝓘(ℝ, E)) (I' := I)
      (n := ∞) (m := ∞) (f := (extChartAt I α).symm) (s := u)
      hf_at (le_refl _) hyb₀ hu_uniq
    simpa using this
  have hg : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α) (chartAt H α).source :=
    contMDiffOn_extChartAt
  have hg_at : ContMDiffWithinAt I 𝓘(ℝ, E) ∞
      (extChartAt I α) (chartAt H α).source b₀ := hg _ hα_src
  have hg_at' : ContMDiffAt I 𝓘(ℝ, E) ∞
      (extChartAt I α) b₀ :=
    hg_at.contMDiffAt ((chartAt H α).open_source.mem_nhds hα_src)
  have hg_maps : MapsTo (extChartAt I α) (chartAt H α).source u := by
    intro x hx
    have : extChartAt I α x ∈ (extChartAt I α).target :=
      (extChartAt I α).map_source (by simpa [extChartAt_source] using hx)
    simpa [u] using this
  have hcomp_within :
      ContMDiffWithinAt I 𝓘(ℝ, E →L[ℝ] E) ∞
        (fun b : M =>
          inTangentCoordinates 𝓘(ℝ, E) I id (extChartAt I α).symm
            (mfderivWithin 𝓘(ℝ, E) I (extChartAt I α).symm u)
            (extChartAt I α b₀) (extChartAt I α b))
        (chartAt H α).source b₀ :=
    hmfderiv.comp b₀ hg_at hg_maps
  have hcomp : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E) ∞
      (fun b : M =>
        inTangentCoordinates 𝓘(ℝ, E) I id (extChartAt I α).symm
          (mfderivWithin 𝓘(ℝ, E) I (extChartAt I α).symm u)
          (extChartAt I α b₀) (extChartAt I α b))
      b₀ :=
    hcomp_within.contMDiffAt ((chartAt H α).open_source.mem_nhds hα_src)
  refine hcomp.congr_of_eventuallyEq ?_
  have hα_open : IsOpen (chartAt H α).source := (chartAt H α).open_source
  have hb₀_open : IsOpen (chartAt H b₀).source := (chartAt H b₀).open_source
  filter_upwards [hα_open.mem_nhds hα_src,
    hb₀_open.mem_nhds (mem_chart_source H b₀)] with b hb hb₀'
  have hb_src : b ∈ (chartAt H α).source := hb
  have hb_src_b₀ : b ∈ (chartAt H b₀).source := hb₀'
  have hxs : (id (extChartAt I α b)) ∈
      (chartAt (H := E) (id ((extChartAt I α b₀) : E))).source := by
    simp
  have hys : (extChartAt I α).symm (extChartAt I α b) ∈
      (chartAt H ((extChartAt I α).symm (extChartAt I α b₀))).source := by
    have hb' : (extChartAt I α).symm (extChartAt I α b) = b :=
      (extChartAt I α).left_inv (by simpa [extChartAt_source] using hb_src)
    have hb₀' : (extChartAt I α).symm (extChartAt I α b₀) = b₀ :=
      (extChartAt I α).left_inv (by simpa [extChartAt_source] using hα_src)
    rw [hb', hb₀']
    exact hb_src_b₀
  rw [inTangentCoordinates_eq (I := 𝓘(ℝ, E)) (I' := I) id (extChartAt I α).symm _ hxs hys]
  have hsrc_id :
      (tangentBundleCore 𝓘(ℝ, E) E).coordChange (achart E (id (extChartAt I α b₀)))
          (achart E (id (extChartAt I α b)))
          (id (extChartAt I α b)) = ContinuousLinearMap.id ℝ E :=
    tangentBundleCore_coordChange_model_space _ _ _
  have htarget_eq :
      (tangentBundleCore I M).coordChange
          (achart H ((extChartAt I α).symm (extChartAt I α b)))
          (achart H ((extChartAt I α).symm (extChartAt I α b₀)))
          ((extChartAt I α).symm (extChartAt I α b)) =
        (trivializationAt E (TangentSpace I) b₀).continuousLinearMapAt ℝ b := by
    have hb' : (extChartAt I α).symm (extChartAt I α b) = b :=
      (extChartAt I α).left_inv (by simpa [extChartAt_source] using hb_src)
    have hb₀' : (extChartAt I α).symm (extChartAt I α b₀) = b₀ :=
      (extChartAt I α).left_inv (by simpa [extChartAt_source] using hα_src)
    rw [hb', hb₀']
    exact (TangentBundle.continuousLinearMapAt_trivializationAt_eq_core
      (b₀ := b₀) (b := b) hb_src_b₀).symm
  have hmfderiv_eq :
      mfderivWithin 𝓘(ℝ, E) I (extChartAt I α).symm u (extChartAt I α b) =
        (trivializationAt E (TangentSpace I) α).symmL ℝ b := by
    have h1 : (trivializationAt E (TangentSpace I) α).symmL ℝ b =
        mfderivWithin 𝓘(ℝ, E) I (extChartAt I α).symm (range I)
          (extChartAt I α b) :=
      TangentBundle.symmL_trivializationAt hb_src
    have h2 : mfderivWithin 𝓘(ℝ, E) I (extChartAt I α).symm u
          (extChartAt I α b) =
        mfderivWithin 𝓘(ℝ, E) I (extChartAt I α).symm (range I)
          (extChartAt I α b) := by
      have hb_target : extChartAt I α b ∈ u := hg_maps hb_src
      have hb_target' : extChartAt I α b ∈ (extChartAt I α).target := by
        simpa [u] using hb_target
      have hsubset : u ⊆ range I := by
        intro x hx
        exact extChartAt_target_subset_range α (by simpa [u] using hx)
      have h_super : range I ∈ nhdsWithin (extChartAt I α b) u :=
        Filter.mem_of_superset self_mem_nhdsWithin hsubset
      have hmdiff : MDifferentiableWithinAt 𝓘(ℝ, E) I
          (extChartAt I α).symm (range I) (extChartAt I α b) :=
        mdifferentiableWithinAt_extChartAt_symm hb_target'
      exact hmdiff.mfderivWithin_mono_of_mem_nhdsWithin
        (hu_uniq _ hb_target) h_super
    rw [h2, ← h1]
  rw [hsrc_id, hmfderiv_eq, htarget_eq, ContinuousLinearMap.comp_id]
  rfl

omit [Module.Finite ℝ E] in
theorem contMDiffAt_tangentTrivialization_coordChangeL_b0_to_alpha
    (α : M) {b₀ : M} (hb₀ : b₀ ∈ (chartAt H α).source) :
    ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E) ∞
      (fun b : M =>
        ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b ∘L
          (trivializationAt E (TangentSpace I) b₀).symmL ℝ b
            : E →L[ℝ] E))
      b₀ := by
  classical
  have hα_src : b₀ ∈ (chartAt H α).source := hb₀
  have hf_at : ContMDiffAt I 𝓘(ℝ, E) ∞ (extChartAt I α) b₀ :=
    contMDiffAt_extChartAt' hα_src
  have hmfderiv :
      ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E) ∞
        (inTangentCoordinates I 𝓘(ℝ, E) id (extChartAt I α)
          (mfderiv I 𝓘(ℝ, E) (extChartAt I α)) b₀) b₀ :=
    ContMDiffAt.mfderiv_const (n := ∞) (m := ∞) hf_at (le_refl _)
  refine hmfderiv.congr_of_eventuallyEq ?_
  have hα_open : IsOpen (chartAt H α).source := (chartAt H α).open_source
  have hb₀_open : IsOpen (chartAt H b₀).source := (chartAt H b₀).open_source
  filter_upwards [hα_open.mem_nhds hα_src,
    hb₀_open.mem_nhds (mem_chart_source H b₀)] with b hb hb₀'
  have hb_src : b ∈ (chartAt H α).source := hb
  have hb_src_b₀ : b ∈ (chartAt H b₀).source := hb₀'
  have hxs : (id b) ∈ (chartAt H ((id) b₀)).source := hb_src_b₀
  have hys : (extChartAt I α b) ∈
      (chartAt (H := E) ((extChartAt I α b₀) : E)).source := by simp
  rw [inTangentCoordinates_eq (I := I) (I' := 𝓘(ℝ, E)) id (extChartAt I α)
    _ hxs hys]
  have hsrc_eq :
      (tangentBundleCore I M).coordChange (achart H (id b₀)) (achart H (id b)) (id b) =
        (trivializationAt E (TangentSpace I) b₀).symmL ℝ b :=
    (TangentBundle.symmL_trivializationAt_eq_core hb_src_b₀).symm
  have htarget_id :
      (tangentBundleCore 𝓘(ℝ, E) E).coordChange
          (achart E ((extChartAt I α) b)) (achart E ((extChartAt I α) b₀))
          ((extChartAt I α) b) = ContinuousLinearMap.id ℝ E :=
    tangentBundleCore_coordChange_model_space _ _ _
  have hmfd_eq :
      mfderiv I 𝓘(ℝ, E) (extChartAt I α) b =
        (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b :=
    (TangentBundle.continuousLinearMapAt_trivializationAt hb_src).symm
  rw [htarget_id, hmfd_eq, hsrc_eq, ContinuousLinearMap.id_comp]
  rfl

end Tensor
end DifferentialGeometry

end
