import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.LocalFormula
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.ChartCoeffPullback
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.LineDeriv.Basic


noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff Matrix

namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure

def tangentSectionAction
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (f : M → ℝ) : M → ℝ :=
  fun x => mfderiv I 𝓘(ℝ) f x (X x)

omit [Module.Finite ℝ E] in
@[simp] lemma tangentSectionAction_def
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (f : M → ℝ) (x : M) :
    tangentSectionAction (I := I) X f x = mfderiv I 𝓘(ℝ) f x (X x) := rfl

def scalarOnE (α : M) (f : M → ℝ) : E → ℝ :=
  fun y => f ((extChartAt I α).symm y)

omit [Module.Finite ℝ E] [IsManifold I ∞ M] in
@[simp] lemma scalarOnE_def (α : M) (f : M → ℝ) (y : E) :
    scalarOnE (I := I) α f y = f ((extChartAt I α).symm y) := rfl

omit [Module.Finite ℝ E] [IsManifold I ∞ M] in
lemma scalarOnE_extChartAt (α : M) (f : M → ℝ) {x : M}
    (hx : x ∈ (extChartAt I α).source) :
    scalarOnE (I := I) α f (extChartAt I α x) = f x := by
  change f ((extChartAt I α).symm (extChartAt I α x)) = f x
  rw [(extChartAt I α).left_inv hx]

omit [Module.Finite ℝ E] in
lemma scalarOnE_contDiffOn (α : M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) :
    ContDiffOn ℝ ∞ (scalarOnE (I := I) α f) (extChartAt I α).target := by
  have hsymm : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I α).symm
      (extChartAt I α).target := contMDiffOn_extChartAt_symm (I := I) α
  have hf_on : ContMDiffOn I 𝓘(ℝ) ∞ f univ := hf.contMDiffOn
  have hcomp : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞ (f ∘ (extChartAt I α).symm)
      (extChartAt I α).target :=
    hf_on.comp hsymm (fun _ _ => mem_univ _)
  exact hcomp.contDiffOn

omit [Module.Finite ℝ E] in
lemma scalarOnE_contDiffWithinAt
    (α : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) {y : E}
    (hy : y ∈ (extChartAt I α).target) :
    ContDiffWithinAt ℝ ∞ (scalarOnE (I := I) α f) (extChartAt I α).target y :=
  scalarOnE_contDiffOn (I := I) α hf y hy

lemma mfderiv_chartBasisVecFiber (α : M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    {x : M} (hx : x ∈ (chartAt H α).source)
    (hx_int : extChartAt I α x ∈ interior (extChartAt I α).target)
    (i : Fin (Module.finrank ℝ E)) :
    mfderiv I 𝓘(ℝ) f x
        (chartBasisVecFiber (I := I) α i x)
      = partialDeriv (E := E) i (scalarOnE (I := I) α f) (extChartAt I α x) := by
  classical
  set φ := extChartAt I α
  have hxsrc : x ∈ φ.source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hx
  have hbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]; exact hx
  have hf_mdiff_at : MDifferentiableAt I 𝓘(ℝ) f x := hf.mdifferentiableAt (by simp)
  have hscalar_smooth :=
    scalarOnE_contDiffOn (I := I) α hf
  have hint_open : IsOpen (interior φ.target) := isOpen_interior
  have hsubset : interior φ.target ⊆ φ.target := interior_subset
  have hscalar_at : ContDiffAt ℝ ∞ (scalarOnE (I := I) α f) (φ x) := by
    have h_within : ContDiffWithinAt ℝ ∞
        (scalarOnE (I := I) α f) φ.target (φ x) := hscalar_smooth (φ x) (hsubset hx_int)
    exact h_within.contDiffAt (mem_nhds_iff.mpr ⟨interior φ.target, hsubset, hint_open, hx_int⟩)
  have hscalar_diff : DifferentiableAt ℝ (scalarOnE (I := I) α f) (φ x) :=
    hscalar_at.differentiableAt (by simp)
  have hcomp_eq : ∀ᶠ y in 𝓝 x, f y = (scalarOnE (I := I) α f) (φ y) := by
    have hsrc_nhd : φ.source ∈ 𝓝 x :=
      (isOpen_extChartAt_source (I := I) α).mem_nhds hxsrc
    filter_upwards [hsrc_nhd] with y hy
    rw [scalarOnE_def, φ.left_inv hy]
  set L : E →L[ℝ] ℝ := fderiv ℝ (scalarOnE (I := I) α f) (φ x)
  have hf_mfderiv := hf_mdiff_at.mfderiv
  have hcong : f =ᶠ[𝓝 x] (scalarOnE (I := I) α f) ∘ (extChartAt I α) := hcomp_eq
  have hmfderiv_cong : mfderiv I 𝓘(ℝ) f x =
      mfderiv I 𝓘(ℝ) ((scalarOnE (I := I) α f) ∘ (extChartAt I α)) x :=
    Filter.EventuallyEq.mfderiv_eq hcong
  rw [hmfderiv_cong]
  have hphi_diff : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I α) x :=
    mdifferentiableAt_extChartAt (I := I) (x := α) hx
  have hg_diff : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ) (scalarOnE (I := I) α f) (φ x) :=
    hscalar_diff.mdifferentiableAt
  have hchain :
      mfderiv I 𝓘(ℝ) ((scalarOnE (I := I) α f) ∘ (extChartAt I α)) x =
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ) (scalarOnE (I := I) α f) (φ x)).comp
          (mfderiv I 𝓘(ℝ, E) (extChartAt I α) x) :=
    mfderiv_comp x hg_diff hphi_diff
  rw [hchain]
  rw [show mfderiv 𝓘(ℝ, E) 𝓘(ℝ) (scalarOnE (I := I) α f) (φ x)
      = fderiv ℝ (scalarOnE (I := I) α f) (φ x) from
        mfderiv_eq_fderiv (𝕜 := ℝ) (f := scalarOnE (I := I) α f)]
  have hmfderiv_chartBasis :
      mfderiv I 𝓘(ℝ, E) (extChartAt I α) x
          (chartBasisVecFiber (I := I) α i x)
        = (chartModelBasis E) i := by
    rw [← TangentBundle.continuousLinearMapAt_trivializationAt (𝕜 := ℝ) (I := I)
      (x₀ := α) (x := x) hx]
    set T : Bundle.Trivialization E (π E (TangentSpace I : M → Type _)) :=
      trivializationAt E (TangentSpace I) α
    have heq : chartBasisVecFiber (I := I) α i x = T.symm x ((chartModelBasis E) i) :=
      rfl
    rw [heq]
    have h_apply :
        T.continuousLinearMapAt ℝ x (T.symm x ((chartModelBasis E) i))
          = (chartModelBasis E) i := by
      have : T.symm x ((chartModelBasis E) i)
            = T.symmL ℝ x ((chartModelBasis E) i) := by
        rw [Trivialization.symmL_apply]
      rw [this, Trivialization.continuousLinearMapAt_symmL T (b := x) hbase]
    exact h_apply
  change fderiv ℝ (scalarOnE (I := I) α f) (φ x)
        (mfderiv I 𝓘(ℝ, E) (extChartAt I α) x (chartBasisVecFiber (I := I) α i x))
      = partialDeriv (E := E) i (scalarOnE (I := I) α f) (φ x)
  rw [hmfderiv_chartBasis]
  rfl

theorem tangentSectionAction_chartLocal
    (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    {x : M} (hx : x ∈ (chartAt H α).source)
    (hx_int : extChartAt I α x ∈ interior (extChartAt I α).target) :
    tangentSectionAction (I := I) X f x =
      ∑ i : Fin (Module.finrank ℝ E),
        chartCoeff (I := I) α X i x *
          partialDeriv (E := E) i (scalarOnE (I := I) α f) (extChartAt I α x) := by
  classical
  have hbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]; exact hx
  have hXrecomp : X x = ∑ i, chartCoeff (I := I) α X i x •
        chartBasisVecFiber (I := I) α i x :=
    chartCoeff_recompose (I := I) α X hbase
  rw [tangentSectionAction_def, hXrecomp]
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [map_smul]
  rw [mfderiv_chartBasisVecFiber (I := I) α hf hx hx_int i]
  exact smul_eq_mul ..

omit [Module.Finite ℝ E] [IsManifold I ∞ M] in
lemma extChartAt_target_subset_interior_of_boundaryless [I.Boundaryless] (α : M) :
    (extChartAt I α).target ⊆ interior (extChartAt I α).target := by
  intro y hy
  exact (isOpen_extChartAt_target (I := I) α).interior_eq.symm ▸ hy

theorem tangentSectionAction_chartLocal_of_boundaryless [I.Boundaryless]
    (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    {x : M} (hx : x ∈ (chartAt H α).source) :
    tangentSectionAction (I := I) X f x =
      ∑ i : Fin (Module.finrank ℝ E),
        chartCoeff (I := I) α X i x *
          partialDeriv (E := E) i (scalarOnE (I := I) α f) (extChartAt I α x) := by
  have hxsrc : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hx
  have hx_target : extChartAt I α x ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source hxsrc
  have hx_int : extChartAt I α x ∈ interior (extChartAt I α).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α hx_target
  exact tangentSectionAction_chartLocal (I := I) α X hf hx hx_int

private lemma partialDeriv_scalarOnE_contDiffOn_interior
    (α : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (i : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (partialDeriv (E := E) i (scalarOnE (I := I) α f))
      (interior (extChartAt I α).target) := by
  have hbase : ContDiffOn ℝ ∞
      (scalarOnE (I := I) α f) (extChartAt I α).target :=
    scalarOnE_contDiffOn (I := I) α hf
  have hbase_int : ContDiffOn ℝ ∞ (scalarOnE (I := I) α f)
      (interior (extChartAt I α).target) := hbase.mono interior_subset
  have hfderiv : ContDiffOn ℝ ∞ (fderiv ℝ (scalarOnE (I := I) α f))
      (interior (extChartAt I α).target) :=
    hbase_int.fderiv_of_isOpen isOpen_interior (by rw [ENat.coe_top_add_one])
  have hconst : ContDiffOn ℝ ∞ (fun _ : E => (chartModelBasis E) i)
      (interior (extChartAt I α).target) := contDiffOn_const
  exact hfderiv.clm_apply hconst

private lemma partialDeriv_scalarOnE_comp_extChartAt_contMDiffOn
    (α : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (i : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun x : M =>
        partialDeriv (E := E) i (scalarOnE (I := I) α f) (extChartAt I α x))
      ((extChartAt I α).source ∩
        (extChartAt I α) ⁻¹' interior (extChartAt I α).target) := by
  classical
  have hpartial : ContDiffOn ℝ ∞
      (partialDeriv (E := E) i (scalarOnE (I := I) α f))
      (interior (extChartAt I α).target) :=
    partialDeriv_scalarOnE_contDiffOn_interior (I := I) α hf i
  have hpartialM : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞
      (partialDeriv (E := E) i (scalarOnE (I := I) α f))
      (interior (extChartAt I α).target) := hpartial.contMDiffOn
  have hchart : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α : M → E)
      (chartAt H α).source := contMDiffOn_extChartAt
  have hchart' : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α : M → E)
      ((extChartAt I α).source ∩
        (extChartAt I α) ⁻¹' interior (extChartAt I α).target) := by
    refine hchart.mono ?_
    intro x hx
    have h1 : x ∈ (extChartAt I α).source := hx.1
    rw [extChartAt_source_eq_chartAt_source (I := I)] at h1
    exact h1
  have hsubset : (extChartAt I α).source ∩
      (extChartAt I α) ⁻¹' interior (extChartAt I α).target ⊆
        (extChartAt I α : M → E) ⁻¹' interior (extChartAt I α).target :=
    fun _ hx => hx.2
  exact hpartialM.comp hchart' hsubset

theorem tangentSectionAction_contMDiffOn
    (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) :
    ContMDiffOn I 𝓘(ℝ) ∞ (tangentSectionAction (I := I) X f)
      ((extChartAt I α).source ∩
        (extChartAt I α) ⁻¹' interior (extChartAt I α).target) := by
  set U : Set M := (extChartAt I α).source ∩
      (extChartAt I α) ⁻¹' interior (extChartAt I α).target with hU_def
  have hcongr : ∀ x ∈ U,
      tangentSectionAction (I := I) X f x =
        ∑ i : Fin (Module.finrank ℝ E),
          chartCoeff (I := I) α X i x *
            partialDeriv (E := E) i (scalarOnE (I := I) α f) (extChartAt I α x) := by
    intro x hx
    have hx_chart : x ∈ (chartAt H α).source := by
      have := hx.1
      rw [extChartAt_source_eq_chartAt_source (I := I)] at this
      exact this
    exact tangentSectionAction_chartLocal (I := I) α X hf hx_chart hx.2
  refine ContMDiffOn.congr ?_ hcongr
  refine contMDiffOn_finset_sum (fun i _ => ?_)
  refine ContMDiffOn.mul ?_ ?_
  · have h1 : ContMDiffOn I 𝓘(ℝ) ∞ (chartCoeff (I := I) α X i)
        (trivializationAt E (TangentSpace I) α).baseSet :=
      chartCoeff_contMDiffOn (I := I) α X i
    refine h1.mono ?_
    intro x hx
    rw [trivializationAt_baseSet_eq_chartAt_source]
    have := hx.1
    rw [extChartAt_source_eq_chartAt_source (I := I)] at this
    exact this
  · exact partialDeriv_scalarOnE_comp_extChartAt_contMDiffOn (I := I) α hf i

theorem tangentSectionAction_contMDiffOn_baseSet [I.Boundaryless]
    (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) :
    ContMDiffOn I 𝓘(ℝ) ∞ (tangentSectionAction (I := I) X f)
      (chartAt H α).source := by
  refine (tangentSectionAction_contMDiffOn (I := I) α X hf).mono ?_
  intro x hx
  refine ⟨?_, ?_⟩
  · rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hx
  · rw [show (extChartAt I α : M → E) ⁻¹' interior (extChartAt I α).target =
          (extChartAt I α : M → E) ⁻¹' (extChartAt I α).target from ?_]
    · exact (extChartAt I α).map_source
        (by rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hx)
    · congr 1
      exact (isOpen_extChartAt_target (I := I) α).interior_eq

theorem tangentSectionAction_contMDiff [I.Boundaryless]
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) :
    ContMDiff I 𝓘(ℝ) ∞ (tangentSectionAction (I := I) X f) := by
  intro x
  have hx_src : x ∈ (chartAt H x).source := mem_chart_source H x
  have hsrc_open : IsOpen ((chartAt H x).source) := (chartAt H x).open_source
  have hsmooth : ContMDiffOn I 𝓘(ℝ) ∞ (tangentSectionAction (I := I) X f)
      (chartAt H x).source :=
    tangentSectionAction_contMDiffOn_baseSet (I := I) x X hf
  exact (hsmooth x hx_src).contMDiffAt (hsrc_open.mem_nhds hx_src)

end DivergenceTheorem
end Integral
end DifferentialGeometry
