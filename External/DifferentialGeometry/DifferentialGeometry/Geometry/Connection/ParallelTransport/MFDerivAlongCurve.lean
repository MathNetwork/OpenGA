import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Analysis.Calculus.ContDiff.Comp


noncomputable section

open Set Function Filter Bundle
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace MFDerivAlongCurve

theorem chartCoord_mfderiv_along_curve_eq_fderiv
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (α : M) {t : ℝ} (ht : γ t ∈ (chartAt H α).source) :
    ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ (γ t))
        ((mfderiv 𝓘(ℝ, ℝ) I γ t : ℝ →L[ℝ] _) (1 : ℝ)) =
      (fderiv ℝ ((extChartAt I α) ∘ γ) t : ℝ →L[ℝ] E) (1 : ℝ) := by
  rw [TangentBundle.continuousLinearMapAt_trivializationAt (I := I)
        (x₀ := α) (x := γ t) ht]
  have hγ_mdiff : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t :=
    (hγ.contMDiffAt).mdifferentiableAt (by simp)
  have hφ_mdiff : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I α) (γ t) :=
    mdifferentiableAt_extChartAt (I := I) (x := α) ht
  have hchain :
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ((extChartAt I α) ∘ γ) t =
        (mfderiv I 𝓘(ℝ, E) (extChartAt I α) (γ t)).comp
          (mfderiv 𝓘(ℝ, ℝ) I γ t) :=
    mfderiv_comp t hφ_mdiff hγ_mdiff
  have hmf_eq_f :
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ((extChartAt I α) ∘ γ) t =
        fderiv ℝ ((extChartAt I α) ∘ γ) t :=
    mfderiv_eq_fderiv (𝕜 := ℝ) (f := (extChartAt I α) ∘ γ) (x := t)
  have hRHS :
      (fderiv ℝ ((extChartAt I α) ∘ γ) t : ℝ →L[ℝ] E) (1 : ℝ) =
        ((mfderiv I 𝓘(ℝ, E) (extChartAt I α) (γ t)).comp
            (mfderiv 𝓘(ℝ, ℝ) I γ t)) (1 : ℝ) := by
    rw [← hmf_eq_f, hchain]; rfl
  rw [hRHS]; rfl

theorem chartCoord_mfderiv_along_curve_eq_fderiv_of_mdifferentiableAt
    {γ : ℝ → M} {t : ℝ} (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t)
    (α : M) (ht : γ t ∈ (chartAt H α).source) :
    ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ (γ t))
        ((mfderiv 𝓘(ℝ, ℝ) I γ t : ℝ →L[ℝ] _) (1 : ℝ)) =
      (fderiv ℝ ((extChartAt I α) ∘ γ) t : ℝ →L[ℝ] E) (1 : ℝ) := by
  rw [TangentBundle.continuousLinearMapAt_trivializationAt (I := I)
        (x₀ := α) (x := γ t) ht]
  have hφ_mdiff : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I α) (γ t) :=
    mdifferentiableAt_extChartAt (I := I) (x := α) ht
  have hchain :
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ((extChartAt I α) ∘ γ) t =
        (mfderiv I 𝓘(ℝ, E) (extChartAt I α) (γ t)).comp
          (mfderiv 𝓘(ℝ, ℝ) I γ t) :=
    mfderiv_comp t hφ_mdiff hγ
  have hmf_eq_f :
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ((extChartAt I α) ∘ γ) t =
        fderiv ℝ ((extChartAt I α) ∘ γ) t :=
    mfderiv_eq_fderiv (𝕜 := ℝ) (f := (extChartAt I α) ∘ γ) (x := t)
  have hRHS :
      (fderiv ℝ ((extChartAt I α) ∘ γ) t : ℝ →L[ℝ] E) (1 : ℝ) =
        ((mfderiv I 𝓘(ℝ, E) (extChartAt I α) (γ t)).comp
            (mfderiv 𝓘(ℝ, ℝ) I γ t)) (1 : ℝ) := by
    rw [← hmf_eq_f, hchain]; rfl
  rw [hRHS]; rfl

theorem continuousOn_fderiv_extChartAt_comp_curve
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) (α : M) :
    ContinuousOn
      (fun t : ℝ => (fderiv ℝ ((extChartAt I α) ∘ γ) t : ℝ → E) (1 : ℝ))
      (γ ⁻¹' (chartAt H α).source) := by
  classical
  set U : Set ℝ := γ ⁻¹' (chartAt H α).source with hU_def
  have hU_open : IsOpen U := by
    have : IsOpen (chartAt H α).source := by
      rw [← extChartAt_source (I := I)]
      exact isOpen_extChartAt_source (I := I) α
    exact hγ.continuous.isOpen_preimage _ this
  have h_comp_mdiff :
      ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ ((extChartAt I α) ∘ γ) U := by
    have hφ : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α)
        (chartAt H α).source :=
      contMDiffOn_extChartAt (I := I) (n := ∞) (x := α)
    have hγU : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ U := hγ.contMDiffOn
    have hmaps : MapsTo γ U (chartAt H α).source := fun _ ht => ht
    exact hφ.comp hγU hmaps
  have h_comp_diff :
      ContDiffOn ℝ ∞ ((extChartAt I α) ∘ γ) U :=
    contMDiffOn_iff_contDiffOn.mp h_comp_mdiff
  have h1le : (1 : ℕ∞) ≤ (∞ : WithTop ℕ∞) := by
    exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤)
  have h_fdW :
      ContinuousOn (fderivWithin ℝ ((extChartAt I α) ∘ γ) U) U :=
    h_comp_diff.continuousOn_fderivWithin hU_open.uniqueDiffOn h1le
  have h_fderiv_cont :
      ContinuousOn (fun t : ℝ => fderiv ℝ ((extChartAt I α) ∘ γ) t) U := by
    refine h_fdW.congr ?_
    intro t ht
    exact (fderivWithin_of_isOpen hU_open ht).symm
  exact h_fderiv_cont.clm_apply continuousOn_const

theorem continuousOn_chartCoord_mfderiv_along_curve
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) (α : M) :
    ContinuousOn
      (fun t : ℝ =>
        (((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ (γ t))
          ((mfderiv 𝓘(ℝ, ℝ) I γ t : ℝ →L[ℝ] _) (1 : ℝ)) : E))
      (γ ⁻¹' (chartAt H α).source) := by
  refine ContinuousOn.congr
    (continuousOn_fderiv_extChartAt_comp_curve (I := I) (M := M) (γ := γ) hγ α) ?_
  intro t ht
  exact (chartCoord_mfderiv_along_curve_eq_fderiv (I := I) (M := M) (γ := γ) hγ
    α (t := t) ht)

theorem chartCoord_mfderiv_along_curve_continuousOn
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) (α : M)
    {s : Set ℝ} (_hs : IsCompact s)
    (hs_sub : s ⊆ γ ⁻¹' (chartAt H α).source) :
    ContinuousOn
      (fun t : ℝ =>
        (((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ (γ t))
          ((mfderiv 𝓘(ℝ, ℝ) I γ t : ℝ →L[ℝ] _) (1 : ℝ)) : E)) s := by
  exact (continuousOn_chartCoord_mfderiv_along_curve (I := I) (M := M)
    (γ := γ) hγ α).mono hs_sub

theorem raw_mfderiv_eq_symmL_apply_fderiv
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (α : M) {t : ℝ} (ht : γ t ∈ (chartAt H α).source) :
    ((mfderiv 𝓘(ℝ, ℝ) I γ t : ℝ →L[ℝ] _) (1 : ℝ) : E) =
      ((trivializationAt E (TangentSpace I) α).symmL ℝ (γ t))
        ((fderiv ℝ ((extChartAt I α) ∘ γ) t : ℝ →L[ℝ] E) (1 : ℝ)) := by
  have hCC : ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ (γ t))
      ((mfderiv 𝓘(ℝ, ℝ) I γ t : ℝ →L[ℝ] _) (1 : ℝ)) =
        (fderiv ℝ ((extChartAt I α) ∘ γ) t : ℝ →L[ℝ] E) (1 : ℝ) :=
    chartCoord_mfderiv_along_curve_eq_fderiv (I := I) (M := M) (γ := γ) hγ α ht
  have hbaseSet : γ t ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact ht
  have hround :
      ((trivializationAt E (TangentSpace I) α).symmL ℝ (γ t))
          (((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ (γ t))
            ((mfderiv 𝓘(ℝ, ℝ) I γ t : ℝ →L[ℝ] _) (1 : ℝ))) =
        ((mfderiv 𝓘(ℝ, ℝ) I γ t : ℝ →L[ℝ] _) (1 : ℝ)) :=
    (trivializationAt E (TangentSpace I) α).symmL_continuousLinearMapAt
      (R := ℝ) hbaseSet _
  calc ((mfderiv 𝓘(ℝ, ℝ) I γ t : ℝ →L[ℝ] _) (1 : ℝ) : E)
      = ((trivializationAt E (TangentSpace I) α).symmL ℝ (γ t))
          (((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ (γ t))
            ((mfderiv 𝓘(ℝ, ℝ) I γ t : ℝ →L[ℝ] _) (1 : ℝ))) := hround.symm
    _ = ((trivializationAt E (TangentSpace I) α).symmL ℝ (γ t))
          ((fderiv ℝ ((extChartAt I α) ∘ γ) t : ℝ →L[ℝ] E) (1 : ℝ)) := by rw [hCC]

theorem raw_mfderiv_eq_symmL_apply_fderiv_of_mdifferentiableAt
    {γ : ℝ → M} {t : ℝ} (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t)
    (α : M) (ht : γ t ∈ (chartAt H α).source) :
    ((mfderiv 𝓘(ℝ, ℝ) I γ t : ℝ →L[ℝ] _) (1 : ℝ) : E) =
      ((trivializationAt E (TangentSpace I) α).symmL ℝ (γ t))
        ((fderiv ℝ ((extChartAt I α) ∘ γ) t : ℝ →L[ℝ] E) (1 : ℝ)) := by
  have hCC : ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ (γ t))
      ((mfderiv 𝓘(ℝ, ℝ) I γ t : ℝ →L[ℝ] _) (1 : ℝ)) =
        (fderiv ℝ ((extChartAt I α) ∘ γ) t : ℝ →L[ℝ] E) (1 : ℝ) :=
    chartCoord_mfderiv_along_curve_eq_fderiv_of_mdifferentiableAt
      (I := I) (M := M) (γ := γ) hγ α ht
  have hbaseSet : γ t ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact ht
  have hround :
      ((trivializationAt E (TangentSpace I) α).symmL ℝ (γ t))
          (((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ (γ t))
            ((mfderiv 𝓘(ℝ, ℝ) I γ t : ℝ →L[ℝ] _) (1 : ℝ))) =
        ((mfderiv 𝓘(ℝ, ℝ) I γ t : ℝ →L[ℝ] _) (1 : ℝ)) :=
    (trivializationAt E (TangentSpace I) α).symmL_continuousLinearMapAt
      (R := ℝ) hbaseSet _
  calc ((mfderiv 𝓘(ℝ, ℝ) I γ t : ℝ →L[ℝ] _) (1 : ℝ) : E)
      = ((trivializationAt E (TangentSpace I) α).symmL ℝ (γ t))
          (((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ (γ t))
            ((mfderiv 𝓘(ℝ, ℝ) I γ t : ℝ →L[ℝ] _) (1 : ℝ))) := hround.symm
    _ = ((trivializationAt E (TangentSpace I) α).symmL ℝ (γ t))
          ((fderiv ℝ ((extChartAt I α) ∘ γ) t : ℝ →L[ℝ] E) (1 : ℝ)) := by rw [hCC]

theorem continuous_tangentMap_unitLift
    {γ : ℝ → M} {n : WithTop ℕ∞} (hn : 1 ≤ n) (hγ : ContMDiff 𝓘(ℝ, ℝ) I n γ) :
    Continuous (fun t : ℝ =>
      tangentMap 𝓘(ℝ, ℝ) I γ (⟨t, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) := by
  have h_tan_cont : Continuous (tangentMap 𝓘(ℝ, ℝ) I γ) :=
    hγ.continuous_tangentMap hn
  have h_input_cont :
      Continuous (fun t : ℝ =>
        (⟨t, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) := by
    have h_homeo :
        Continuous ((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm :
          ModelProd ℝ ℝ → TangentBundle 𝓘(ℝ, ℝ) ℝ) :=
      (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm.continuous
    have h_pair : Continuous (fun t : ℝ => (t, (1 : ℝ))) :=
      continuous_id.prodMk continuous_const
    exact h_homeo.comp h_pair
  exact h_tan_cont.comp h_input_cont

theorem mem_chartPullback_self {γ : ℝ → M} (t : ℝ) :
    t ∈ γ ⁻¹' (chartAt H (γ t)).source := by
  exact mem_chart_source H (γ t)

omit [IsManifold I ∞ M] in
theorem chartPullback_cover_compact
    {γ : ℝ → M} (_hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) {s : Set ℝ} (_hs : IsCompact s) :
    s ⊆ ⋃ t₀ ∈ s, γ ⁻¹' (chartAt H (γ t₀)).source := by
  intro t ht
  refine mem_iUnion_of_mem t ?_
  refine mem_iUnion_of_mem ht ?_
  exact mem_chart_source H (γ t)

omit [IsManifold I ∞ M] in
theorem exists_finite_chartPullback_subcover
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    {s : Set ℝ} (hs : IsCompact s) :
    ∃ T : Set ℝ, T ⊆ s ∧ Set.Finite T ∧
      s ⊆ ⋃ t₀ ∈ T, γ ⁻¹' (chartAt H (γ t₀)).source := by
  classical
  have hopen : ∀ t₀ : ℝ, t₀ ∈ s → IsOpen (γ ⁻¹' (chartAt H (γ t₀)).source) := by
    intro t₀ _
    have : IsOpen (chartAt H (γ t₀)).source := by
      rw [← extChartAt_source (I := I)]
      exact isOpen_extChartAt_source (I := I) (γ t₀)
    exact hγ.continuous.isOpen_preimage _ this
  have hcover : s ⊆ ⋃ t₀ ∈ s, γ ⁻¹' (chartAt H (γ t₀)).source :=
    chartPullback_cover_compact (I := I) (M := M) (γ := γ) hγ hs
  exact hs.elim_finite_subcover_image hopen hcover

end MFDerivAlongCurve

end Riemannian
end Geometry
end DifferentialGeometry
