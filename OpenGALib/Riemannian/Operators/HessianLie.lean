import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.VectorField.LieBracket
import Mathlib.Geometry.Manifold.VectorField.Pullback
import OpenGALib.Riemannian.TangentBundle.TangentSmooth

/-!
# Scalar Hessian–Lie identity

For a $C^2$ scalar / vector-valued function $f : M \to F$ and $C^1$
vector fields $V, W$,
$$D_V(D_W f) - D_W(D_V f) = D_{[V, W]} f.$$

This is the algebraic content of the Lie bracket as a derivation on
$C^\infty(M, F)$. Used by `Riemannian.Curvature` to close
`riemannCurvature_inner_self_zero` (skew-symmetry of the Riemann
endomorphism), which in turn feeds `ricci_symm` via Bianchi I.

## Main results

* `flat_hessianLie_apply`, `flat_hessianLieWithin_apply` —
  flat (normed-space) versions of the identity.
* `mfderiv_iterate_sub_eq_mlieBracket_apply` — the manifold version,
  obtained from the flat version via chart pullback.

The chart-bridge helpers (`Helper #1, #2, #3`) and the bundle-section ↔
flat smoothness conversions are `private` engineering.

Reference: do Carmo, *Riemannian Geometry*, §0 Lemma 5.2; Lee,
*Smooth Manifolds*, Proposition 8.30.
-/

open Bundle VectorField
open scoped ContDiff Manifold Topology Riemannian

namespace Riemannian

/-! ## Flat (normed-space) version -/

section Flat

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- $D_V(D_W f) - D_W(D_V f) = D_{[V, W]} f$ on a normed space (univ). -/
theorem flat_hessianLie_apply
    {f : E → F} {V W : E → E} {x : E}
    (hf : ContDiffAt ℝ 2 f x)
    (hV : DifferentiableAt ℝ V x) (hW : DifferentiableAt ℝ W x) :
    fderiv ℝ (fun y => fderiv ℝ f y (W y)) x (V x)
    - fderiv ℝ (fun y => fderiv ℝ f y (V y)) x (W x)
    = fderiv ℝ f x (lieBracket ℝ V W x) := by
  have hf'_diff : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((hf.of_le (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).fderiv_right
      (le_refl _)).differentiableAt (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  have h1 : fderiv ℝ (fun y => fderiv ℝ f y (V y)) x
          = (fderiv ℝ (fderiv ℝ f) x).flip (V x)
            + (fderiv ℝ f x).comp (fderiv ℝ V x) := by
    rw [fderiv_clm_apply hf'_diff hV, add_comm]
  have h2 : fderiv ℝ (fun y => fderiv ℝ f y (W y)) x
          = (fderiv ℝ (fderiv ℝ f) x).flip (W x)
            + (fderiv ℝ f x).comp (fderiv ℝ W x) := by
    rw [fderiv_clm_apply hf'_diff hW, add_comm]
  rw [h2, h1]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.coe_comp', Function.comp_apply]
  rw [(hf.isSymmSndFDerivAt (by simp) (V x) (W x)).symm,
      lieBracket_eq, (fderiv ℝ f x).map_sub]
  abel

/-- Within form on a unique-diff set `s` (used for chart-pullback). -/
theorem flat_hessianLieWithin_apply
    {f : E → F} {V W : E → E} {s : Set E} {x : E}
    (hs : UniqueDiffOn ℝ s) (hx : x ∈ s)
    (h_interior : x ∈ closure (interior s))
    (hf : ContDiffWithinAt ℝ 2 f s x)
    (hV : DifferentiableWithinAt ℝ V s x)
    (hW : DifferentiableWithinAt ℝ W s x) :
    fderivWithin ℝ (fun y => fderivWithin ℝ f s y (W y)) s x (V x)
    - fderivWithin ℝ (fun y => fderivWithin ℝ f s y (V y)) s x (W x)
    = fderivWithin ℝ f s x (lieBracketWithin ℝ V W s x) := by
  have hsx : UniqueDiffWithinAt ℝ s x := hs x hx
  have hf'_diff : DifferentiableWithinAt ℝ (fderivWithin ℝ f s) s x :=
    ((hf.of_le (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).fderivWithin_right hs
      (by norm_num) hx).differentiableWithinAt
        (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  have h1 : fderivWithin ℝ (fun y => fderivWithin ℝ f s y (V y)) s x
          = (fderivWithin ℝ (fderivWithin ℝ f s) s x).flip (V x)
            + (fderivWithin ℝ f s x).comp (fderivWithin ℝ V s x) := by
    rw [fderivWithin_clm_apply hsx hf'_diff hV, add_comm]
  have h2 : fderivWithin ℝ (fun y => fderivWithin ℝ f s y (W y)) s x
          = (fderivWithin ℝ (fderivWithin ℝ f s) s x).flip (W x)
            + (fderivWithin ℝ f s x).comp (fderivWithin ℝ W s x) := by
    rw [fderivWithin_clm_apply hsx hf'_diff hW, add_comm]
  rw [h2, h1]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.coe_comp', Function.comp_apply]
  rw [(hf.isSymmSndFDerivWithinAt (by simp) hs h_interior hx (V x) (W x)).symm,
      lieBracketWithin_eq, (fderivWithin ℝ f s x).map_sub]
  abel

end Flat

/-! ## Chart-bridge helpers (private engineering) -/

variable {H : Type*} [TopologicalSpace H]
  {E_M : Type*} [NormedAddCommGroup E_M] [NormedSpace ℝ E_M]
  {I : ModelWithCorners ℝ E_M H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

section ChartHelpers

variable [IsLocallyConstantChartedSpace H M]

/-- `mfderiv (extChartAt I x) y` is identity in a nbhd of `x`. -/
private theorem mfderiv_extChartAt_eq_id_eventually
    [IsManifold I 1 M] (x : M) :
    ∀ᶠ y in 𝓝 x, mfderiv I 𝓘(ℝ, E_M) (extChartAt I x) y
                = ContinuousLinearMap.id ℝ E_M := by
  have h_chart_eq : ∀ᶠ y in 𝓝 x, chartAt H y = chartAt H x :=
    chartAt_eventually_eq_of_locallyConstant x
  have h_chart_src : (chartAt H x).source ∈ 𝓝 x :=
    (chartAt H x).open_source.mem_nhds (mem_chart_source H x)
  filter_upwards [h_chart_eq, h_chart_src] with y hy_eq hy_src
  rw [← TangentBundle.continuousLinearMapAt_trivializationAt hy_src,
      TangentBundle.continuousLinearMapAt_trivializationAt_eq_core hy_src,
      show achart H y = achart H x from Subtype.ext hy_eq]
  ext v
  exact (tangentBundleCore I M).coordChange_self (achart H x) y
    (by simpa [tangentBundleCore_baseSet] using hy_src) v

private theorem mfderivWithin_extChartAt_symm_eq_id_eventually
    [IsManifold I 1 M] (x : M) :
    ∀ᶠ e in 𝓝[Set.range I] (extChartAt I x x),
      mfderivWithin 𝓘(ℝ, E_M) I (extChartAt I x).symm (Set.range I) e
      = ContinuousLinearMap.id ℝ E_M := by
  have h_target : (extChartAt I x).target ∈ 𝓝[Set.range I] (extChartAt I x x) :=
    extChartAt_target_mem_nhdsWithin x
  have h_symm_tendsto : Filter.Tendsto (extChartAt I x).symm
      (𝓝[Set.range I] (extChartAt I x x)) (𝓝 x) := by
    have h_cont : ContinuousWithinAt (extChartAt I x).symm
        (extChartAt I x).target (extChartAt I x x) :=
      (continuousOn_extChartAt_symm x) _ (mem_extChartAt_target x)
    have h_symm_at_x : (extChartAt I x).symm (extChartAt I x x) = x :=
      (extChartAt I x).left_inv (mem_extChartAt_source x)
    have h_tendsto : Filter.Tendsto (extChartAt I x).symm
        (𝓝[(extChartAt I x).target] (extChartAt I x x)) (𝓝 x) := by
      have := h_cont.tendsto
      rwa [h_symm_at_x] at this
    refine h_tendsto.mono_left ?_
    rw [nhdsWithin]
    exact le_inf inf_le_left (Filter.le_principal_iff.mpr h_target)
  have h_chart_eq_e : ∀ᶠ e in 𝓝[Set.range I] (extChartAt I x x),
      chartAt H ((extChartAt I x).symm e) = chartAt H x :=
    h_symm_tendsto (chartAt_eventually_eq_of_locallyConstant x)
  filter_upwards [h_target, h_chart_eq_e] with e he_target hy_eq
  have h_symm_e_src : (extChartAt I x).symm e ∈ (chartAt H x).source := by
    have := (extChartAt I x).map_target he_target
    rwa [extChartAt_source] at this
  have h_comp := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm
    (I := I) (M := M) (x := x) he_target
  have h_id_at_symm : mfderiv I 𝓘(ℝ, E_M) (extChartAt I x) ((extChartAt I x).symm e)
                    = ContinuousLinearMap.id ℝ E_M := by
    rw [← TangentBundle.continuousLinearMapAt_trivializationAt h_symm_e_src,
        TangentBundle.continuousLinearMapAt_trivializationAt_eq_core h_symm_e_src,
        show achart H ((extChartAt I x).symm e) = achart H x from Subtype.ext hy_eq]
    ext v
    exact (tangentBundleCore I M).coordChange_self (achart H x) ((extChartAt I x).symm e)
      (by simpa [tangentBundleCore_baseSet] using h_symm_e_src) v
  rw [h_id_at_symm] at h_comp
  simpa using h_comp

end ChartHelpers

/-- Chain-rule bridge: $\mathrm{d}(g \circ \mathrm{chart})_x = \mathrm{d}^I g_{\mathrm{chart}\,x}$
on $\mathrm{range}\, I$. -/
private theorem mfderiv_chart_compose_apply
    [IsManifold I 1 M] (x : M)
    (g : E_M → F)
    (hg : DifferentiableWithinAt ℝ g (Set.range I) (extChartAt I x x))
    (v : TangentSpace I x) :
    mfderiv I 𝓘(ℝ, F) (fun y => g (extChartAt I x y)) x v
    = fderivWithin ℝ g (Set.range I) (extChartAt I x x) v := by
  have h_maps : Set.MapsTo (extChartAt I x) (chartAt H x).source (Set.range I) := by
    intro y _
    rw [extChartAt_coe]
    exact Set.mem_range_self _
  have h_comp : MDifferentiableAt I 𝓘(ℝ, F)
      (fun y => g (extChartAt I x y)) x :=
    (hg.comp_mdifferentiableWithinAt
      (mdifferentiableAt_extChartAt (mem_chart_source H x)).mdifferentiableWithinAt
      h_maps).mdifferentiableAt
        ((chartAt H x).open_source.mem_nhds (mem_chart_source H x))
  rw [h_comp.mfderiv]
  have h_eqOn : (extChartAt I x).target.EqOn
      (writtenInExtChartAt I 𝓘(ℝ, F) x (fun y => g (extChartAt I x y))) g := by
    intro e he
    show (extChartAt 𝓘(ℝ, F) (g (extChartAt I x x)))
         (g (extChartAt I x ((extChartAt I x).symm e))) = g e
    rw [(extChartAt I x).right_inv he]; rfl
  have h_eventually :
      (writtenInExtChartAt I 𝓘(ℝ, F) x (fun y => g (extChartAt I x y)))
      =ᶠ[𝓝[Set.range I] (extChartAt I x x)] g := by
    filter_upwards [extChartAt_target_mem_nhdsWithin x] with e he
    exact h_eqOn he
  rw [h_eventually.fderivWithin_eq (h_eqOn (mem_extChartAt_target x))]
  rfl

/-! ## Manifold version -/

variable [IsLocallyConstantChartedSpace H M]

/-- $F$-typed `mfderiv` wrapper sidestepping basepoint-dependent `HSub`
synthesis on iterated forms. Definitionally equal to `mfderiv I 𝓘(ℝ,F) f x v`. -/
@[reducible] noncomputable def mDirDeriv
    (f : M → F) (x : M) (v : TangentSpace I x) : F :=
  mfderiv I 𝓘(ℝ, F) f x v

omit [IsLocallyConstantChartedSpace H M] in
private theorem mDirDeriv_chart_compose_apply
    [IsManifold I 1 M] (x : M)
    (g : E_M → F)
    (hg : DifferentiableWithinAt ℝ g (Set.range I) (extChartAt I x x))
    (v : TangentSpace I x) :
    mDirDeriv (fun y => g (extChartAt I x y)) x v
    = fderivWithin ℝ g (Set.range I) (extChartAt I x x) v :=
  mfderiv_chart_compose_apply x g hg v

variable [IsManifold I 1 M]

private theorem MDifferentiableAt_of_tangent_bundle_section
    (V : VectorFieldSection I M) {x : M}
    (hV : MDifferentiableAt I (I.prod 𝓘(ℝ, E_M))
          (fun y => (⟨y, V y⟩ : TotalSpace E_M (TangentSpace I))) x) :
    MDifferentiableAt I 𝓘(ℝ, E_M) V x := by
  have hV_chart : MDifferentiableAt I 𝓘(ℝ, E_M)
      (fun y => ((trivializationAt E_M (TangentSpace I) x) ⟨y, V y⟩).2) x := by
    rw [mdifferentiableAt_totalSpace] at hV
    exact hV.2
  have h_eq : (fun y => ((trivializationAt E_M (TangentSpace I) x) ⟨y, V y⟩).2)
              =ᶠ[𝓝 x] V := by
    have h_base : (trivializationAt E_M (TangentSpace I) x).baseSet ∈ 𝓝 x :=
      (trivializationAt E_M (TangentSpace I) x).open_baseSet.mem_nhds
        (FiberBundle.mem_baseSet_trivializationAt' x)
    have h_chart_src : (chartAt H x).source ∈ 𝓝 x :=
      (chartAt H x).open_source.mem_nhds (mem_chart_source H x)
    have h_chart_eq : ∀ᶠ y in 𝓝 x, chartAt H y = chartAt H x :=
      chartAt_eventually_eq_of_locallyConstant x
    filter_upwards [h_base, h_chart_src, h_chart_eq] with y hy_base hy_src hy_eq
    show ((trivializationAt E_M (TangentSpace I) x) ⟨y, V y⟩).2 = V y
    rw [← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) _ hy_base,
        TangentBundle.continuousLinearMapAt_trivializationAt_eq_core hy_src,
        show achart H y = achart H x from Subtype.ext hy_eq]
    show (tangentBundleCore I M).coordChange (achart H x) (achart H x) y (V y) = V y
    exact (tangentBundleCore I M).coordChange_self (achart H x) y
      (by simpa [tangentBundleCore_baseSet] using hy_src) (V y)
  exact hV_chart.congr_of_eventuallyEq h_eq.symm

private theorem DifferentiableWithinAt_chart_pullback_of_section
    (V : VectorFieldSection I M) (x : M)
    (hV : MDifferentiableAt I (I.prod 𝓘(ℝ, E_M))
          (fun y => (⟨y, V y⟩ : TotalSpace E_M (TangentSpace I))) x) :
    DifferentiableWithinAt ℝ (fun e => V ((extChartAt I x).symm e))
      (Set.range I) (extChartAt I x x) := by
  have hV_plain : MDifferentiableAt I 𝓘(ℝ, E_M) V x :=
    MDifferentiableAt_of_tangent_bundle_section V hV
  have h := MDifferentiableWithinAt.differentiableWithinAt_comp_extChartAt_symm
    (s := Set.univ) hV_plain.mdifferentiableWithinAt
  convert h using 2
  simp [Set.preimage_univ, Set.univ_inter]

omit [IsManifold I 1 M] in
private theorem mfderiv_inner_eq_fderivWithin_eventually
    {f : M → F} {V : VectorFieldSection I M} {x : M}
    (hf_nbhd : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, F) f y) :
    (fun y => mfderiv I 𝓘(ℝ, F) f y (V y))
    =ᶠ[𝓝 x] (fun y => fderivWithin ℝ (f ∘ (extChartAt I x).symm) (Set.range I)
                        (extChartAt I x y) (V y)) := by
  have h_chart_eq : ∀ᶠ y in 𝓝 x, chartAt H y = chartAt H x :=
    chartAt_eventually_eq_of_locallyConstant x
  have h_ext_eq : ∀ᶠ y in 𝓝 x, extChartAt I y = extChartAt I x := by
    filter_upwards [h_chart_eq] with y hy
    rw [extChartAt, extChartAt, hy]
  filter_upwards [hf_nbhd, h_ext_eq] with y hy_diff hy_ext
  have h_written : writtenInExtChartAt I 𝓘(ℝ, F) y f
                 = f ∘ (extChartAt I x).symm := by
    ext e
    show (extChartAt 𝓘(ℝ, F) (f y)) (f ((extChartAt I y).symm e))
       = (f ∘ (extChartAt I x).symm) e
    rw [hy_ext]; rfl
  rw [hy_diff.mfderiv, h_written]
  show fderivWithin ℝ (f ∘ (extChartAt I x).symm) (Set.range I) ((extChartAt I y) y) (V y)
     = fderivWithin ℝ (f ∘ (extChartAt I x).symm) (Set.range I) ((extChartAt I x) y) (V y)
  rw [hy_ext]

private theorem mpullbackWithin_extChartAt_symm_eq_eventually
    (V : VectorFieldSection I M) (x : M) :
    mpullbackWithin 𝓘(ℝ, E_M) I (extChartAt I x).symm V (Set.range I)
    =ᶠ[𝓝[Set.range I] (extChartAt I x x)]
    fun e => V ((extChartAt I x).symm e) := by
  filter_upwards [mfderivWithin_extChartAt_symm_eq_id_eventually (I := I) (M := M) x]
    with e h_id_e
  show (mfderivWithin 𝓘(ℝ, E_M) I (extChartAt I x).symm (Set.range I) e).inverse
        (V ((extChartAt I x).symm e))
     = V ((extChartAt I x).symm e)
  rw [h_id_e]
  show (ContinuousLinearMap.id ℝ E_M).inverse (V ((extChartAt I x).symm e))
     = V ((extChartAt I x).symm e)
  rw [ContinuousLinearMap.inverse_id]
  rfl

private theorem mlieBracket_eq_lieBracketWithin_chart_pullback
    (V W : VectorFieldSection I M) (x : M) :
    mlieBracket I V W x
    = lieBracketWithin ℝ (fun e => V ((extChartAt I x).symm e))
        (fun e => W ((extChartAt I x).symm e)) (Set.range I) (extChartAt I x x) := by
  rw [show mlieBracket I V W x = mlieBracketWithin I V W Set.univ x from rfl,
      VectorField.mlieBracketWithin_apply]
  have h_id : mfderiv I 𝓘(ℝ, E_M) (extChartAt I x) x = ContinuousLinearMap.id ℝ E_M :=
    (mfderiv_extChartAt_eq_id_eventually (I := I) (M := M) x).self_of_nhds
  rw [h_id]
  show (ContinuousLinearMap.id ℝ E_M).inverse
        (lieBracketWithin ℝ
          (mpullbackWithin 𝓘(ℝ, E_M) I (extChartAt I x).symm V (Set.range I))
          (mpullbackWithin 𝓘(ℝ, E_M) I (extChartAt I x).symm W (Set.range I))
          ((extChartAt I x).symm ⁻¹' Set.univ ∩ Set.range I) (extChartAt I x x))
      = lieBracketWithin ℝ (fun e => V ((extChartAt I x).symm e))
          (fun e => W ((extChartAt I x).symm e)) (Set.range I) (extChartAt I x x)
  rw [ContinuousLinearMap.inverse_id]
  simp only [Set.preimage_univ, Set.univ_inter]
  show lieBracketWithin ℝ (mpullbackWithin 𝓘(ℝ, E_M) I (extChartAt I x).symm V (Set.range I))
        (mpullbackWithin 𝓘(ℝ, E_M) I (extChartAt I x).symm W (Set.range I))
        (Set.range I) (extChartAt I x x)
      = lieBracketWithin ℝ (fun e => V ((extChartAt I x).symm e))
          (fun e => W ((extChartAt I x).symm e)) (Set.range I) (extChartAt I x x)
  exact (mpullbackWithin_extChartAt_symm_eq_eventually V x).lieBracketWithin_vectorField_eq_of_mem
    (mpullbackWithin_extChartAt_symm_eq_eventually W x)
    (extChartAt_target_subset_range x (mem_extChartAt_target x))

set_option backward.isDefEq.respectTransparency false in
/-- **Manifold scalar Hessian–Lie identity**:
$D_V(D_W f) - D_W(D_V f) = D_{[V,W]} f$ at $x \in M$, where $D_V f$
denotes `mfderiv f · (V ·)` and `mlieBracket I V W` is the manifold
Lie bracket. Requires $f$ of class $C^2$, $V, W$ of class $C^1$, and
$\mathrm{chart}\, x$ in the closure of the interior of $\mathrm{range}\, I$. -/
theorem mfderiv_iterate_sub_eq_mlieBracket_apply
    [IsManifold I 2 M]
    (f : M → F) (V W : VectorFieldSection I M) (x : M)
    (h_interior : extChartAt I x x ∈ closure (interior (Set.range I)))
    (hf : ContMDiffAt I 𝓘(ℝ, F) 2 f x)
    (hV : ContMDiffAt I (I.prod 𝓘(ℝ, E_M)) 1
      (fun y => (⟨y, V y⟩ : TotalSpace E_M (TangentSpace I))) x)
    (hW : ContMDiffAt I (I.prod 𝓘(ℝ, E_M)) 1
      (fun y => (⟨y, W y⟩ : TotalSpace E_M (TangentSpace I))) x) :
    mDirDeriv (fun y => mDirDeriv f y (W y)) x (V x)
    - mDirDeriv (fun y => mDirDeriv f y (V y)) x (W x)
    = mDirDeriv f x (mlieBracket I V W x) := by
  unfold mDirDeriv
  set phi := extChartAt I x
  set s : Set E_M := Set.range I
  set f_loc : E_M → F := f ∘ phi.symm
  set V_loc : E_M → E_M := fun e => V (phi.symm e)
  set W_loc : E_M → E_M := fun e => W (phi.symm e)
  have hf_nbhd : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, F) f y := by
    filter_upwards [(contMDiffAt_iff_contMDiffAt_nhds (by decide : (2 : ℕ∞ω) ≠ ∞)).mp hf]
      with y hy using hy.mdifferentiableAt (by norm_num : (2 : ℕ∞ω) ≠ 0)
  have h_f_loc_C2 : ContDiffWithinAt ℝ 2 f_loc s (phi x) :=
    (contMDiffAt_iff.mp hf).2
  have hV_pt : MDifferentiableAt I (I.prod 𝓘(ℝ, E_M))
      (fun y => (⟨y, V y⟩ : TotalSpace E_M (TangentSpace I))) x :=
    hV.mdifferentiableAt (by norm_num : (1 : ℕ∞ω) ≠ 0)
  have hW_pt : MDifferentiableAt I (I.prod 𝓘(ℝ, E_M))
      (fun y => (⟨y, W y⟩ : TotalSpace E_M (TangentSpace I))) x :=
    hW.mdifferentiableAt (by norm_num : (1 : ℕ∞ω) ≠ 0)
  have h_V_loc_diff : DifferentiableWithinAt ℝ V_loc s (phi x) :=
    DifferentiableWithinAt_chart_pullback_of_section V x hV_pt
  have h_W_loc_diff : DifferentiableWithinAt ℝ W_loc s (phi x) :=
    DifferentiableWithinAt_chart_pullback_of_section W x hW_pt
  have h_s_unique : UniqueDiffOn ℝ s := I.uniqueDiffOn
  have h_phi_x_in_s : phi x ∈ s :=
    extChartAt_target_subset_range x (mem_extChartAt_target x)
  have h_f_loc_diff : DifferentiableWithinAt ℝ f_loc s (phi x) :=
    (h_f_loc_C2.of_le (by norm_num : (1 : ℕ∞ω) ≤ 2)).differentiableWithinAt
      (by norm_num : (1 : ℕ∞ω) ≠ 0)
  have h_fderiv_f_loc_diff : DifferentiableWithinAt ℝ (fderivWithin ℝ f_loc s) s (phi x) :=
    (h_f_loc_C2.fderivWithin_right h_s_unique
      (by norm_num : ((1 : ℕ∞ω)) + 1 ≤ 2) h_phi_x_in_s).differentiableWithinAt
        (by norm_num : (1 : ℕ∞ω) ≠ 0)
  have h_inner_W := mfderiv_inner_eq_fderivWithin_eventually (V := W) (f := f) hf_nbhd
  have h_inner_V := mfderiv_inner_eq_fderivWithin_eventually (V := V) (f := f) hf_nbhd
  rw [Filter.EventuallyEq.mfderiv_eq h_inner_W,
      Filter.EventuallyEq.mfderiv_eq h_inner_V]
  have h_outer (V_aux : VectorFieldSection I M) :
      (fun y => fderivWithin ℝ f_loc s (phi y) (V_aux y))
      =ᶠ[𝓝 x] (fun y => fderivWithin ℝ f_loc s (phi y)
        (V_aux ((extChartAt I x).symm (phi y)))) := by
    have h_chart_src : (chartAt H x).source ∈ 𝓝 x :=
      (chartAt H x).open_source.mem_nhds (mem_chart_source H x)
    filter_upwards [h_chart_src] with y hy_src
    have : (extChartAt I x).symm (phi y) = y :=
      (extChartAt I x).left_inv (by rwa [extChartAt_source])
    rw [this]
  rw [Filter.EventuallyEq.mfderiv_eq (h_outer W),
      Filter.EventuallyEq.mfderiv_eq (h_outer V)]
  show mDirDeriv (fun y => fderivWithin ℝ f_loc s (phi y) (W_loc (phi y))) x (V x)
       - mDirDeriv (fun y => fderivWithin ℝ f_loc s (phi y) (V_loc (phi y))) x (W x)
       = mDirDeriv f x (mlieBracket I V W x)
  have h_g_chart_W_diff : DifferentiableWithinAt ℝ
      (fun e => fderivWithin ℝ f_loc s e (W_loc e)) s (phi x) :=
    h_fderiv_f_loc_diff.clm_apply h_W_loc_diff
  have h_g_chart_V_diff : DifferentiableWithinAt ℝ
      (fun e => fderivWithin ℝ f_loc s e (V_loc e)) s (phi x) :=
    h_fderiv_f_loc_diff.clm_apply h_V_loc_diff
  rw [mDirDeriv_chart_compose_apply x _ h_g_chart_W_diff (V x),
      mDirDeriv_chart_compose_apply x _ h_g_chart_V_diff (W x)]
  have h_VW_at_x (V_aux : VectorFieldSection I M) :
      V_aux x = (fun e => V_aux ((extChartAt I x).symm e)) (phi x) := by
    show V_aux x = V_aux ((extChartAt I x).symm (phi x))
    rw [(extChartAt I x).left_inv (mem_extChartAt_source x)]
  rw [h_VW_at_x V, h_VW_at_x W]
  rw [flat_hessianLieWithin_apply h_s_unique h_phi_x_in_s h_interior
        h_f_loc_C2 h_V_loc_diff h_W_loc_diff]
  have h_f_outer : (fun y : M => f y) =ᶠ[𝓝 x] (fun y => f_loc (phi y)) := by
    have h_chart_src : (chartAt H x).source ∈ 𝓝 x :=
      (chartAt H x).open_source.mem_nhds (mem_chart_source H x)
    filter_upwards [h_chart_src] with y hy_src
    show f y = f (phi.symm (phi y))
    rw [(extChartAt I x).left_inv (by rwa [extChartAt_source])]
  show fderivWithin ℝ f_loc s (phi x) (lieBracketWithin ℝ V_loc W_loc s (phi x))
     = mfderiv I 𝓘(ℝ, F) f x (mlieBracket I V W x)
  rw [Filter.EventuallyEq.mfderiv_eq h_f_outer,
      ← mlieBracket_eq_lieBracketWithin_chart_pullback V W x]
  exact (mfderiv_chart_compose_apply x f_loc h_f_loc_diff (mlieBracket I V W x)).symm

set_option linter.unusedSectionVars false in
/-- **Manifold Lie bracket of two constant tangent sections vanishes.**
Chart-pullback (`mlieBracket_eq_lieBracketWithin_chart_pullback`) reduces
`mlieBracket I (fun _ => v) (fun _ => w) x` to a `lieBracketWithin` in the
model space `E_M` of two constant functions; `fderivWithin` of a constant
is zero, so the bracket vanishes at every $x \in M$. -/
theorem mlieBracket_const_const_apply_zero
    (v w : E_M) (x : M) :
    mlieBracket I (fun _ : M => v) (fun _ : M => w) x = 0 := by
  rw [mlieBracket_eq_lieBracketWithin_chart_pullback]
  -- Goal (after β-reduction): `lieBracketWithin ℝ (fun _ => v) (fun _ => w) (range I)
  --   (extChartAt I x x) = 0`. Unfold `lieBracketWithin`; both `fderivWithin` terms
  -- are zero (`fderivWithin_const_apply`).
  show fderivWithin ℝ (fun _ : E_M => w) (Set.range I) (extChartAt I x x)
          ((fun _ : E_M => v) (extChartAt I x x))
        - fderivWithin ℝ (fun _ : E_M => v) (Set.range I) (extChartAt I x x)
            ((fun _ : E_M => w) (extChartAt I x x)) = 0
  rw [fderivWithin_const_apply, fderivWithin_const_apply]
  simp

end Riemannian
