import Mathlib.Geometry.Manifold.VectorField.LieBracket
import Mathlib.Geometry.Manifold.VectorField.Pullback
import Riemannian.Foundations.HessianLie.Flat
import Riemannian.Foundations.HessianLie.ChartHelpers

/-!
# Scalar Hessian–Lie identity — manifold version

The flat scalar Hessian–Lie identity (`Flat.lean`) lifted to a smooth
manifold via chart pullback. For `f : M → F` of class `C^2` and `V, W`
smooth vector fields,

  $$D_V (D_W f) - D_W (D_V f) = D_{[V,W]} f$$

at every point, where `mfderiv` and `mlieBracket` are the manifold
analogs.

## Strategy

Pull back through `extChartAt I x`. With `IsLocallyConstantChartedSpace`,
the chart is identity-like in a nbhd; combined with the chart helpers
(`ChartHelpers.lean`), every `mfderiv` reduces to `fderivWithin (range I)`
and every `mlieBracket` reduces to `lieBracketWithin (range I)`. The
flat identity (`flat_hessianLieWithin_apply`) closes the chart-side
algebraic content.

## Helper lemmas

* `tangentSection_mdifferentiableAt_of_smooth_chart` — bundle-section
  smoothness ⇒ plain `MDifferentiableAt I 𝓘(ℝ,E_M) V x` via chart
  trivialization (using Helper #1's chart-coherence).
* `mpullbackWithin_eq_chart_pullback_eventually` — `mpullbackWithin V`
  agrees with `V ∘ phi.symm` eventually within `range I` (uses Helper #3).
* `mfderiv_inner_eq_fderivWithin_eventually` — for f differentiable
  in a nbhd, `y ↦ mfderiv f y (V y)` agrees eventually with
  `y ↦ fderivWithin f_loc s (phi y) (V y)`.

## Main theorem

* `mfderiv_iterate_sub_eq_mlieBracket_apply` — the manifold scalar
  Hessian–Lie identity.

**Ground truth**: do Carmo 1992 §0 Lemma 5.2; Lee 2013 *Smooth
Manifolds* Proposition 8.30. -/

open Bundle VectorField
open scoped ContDiff Manifold Topology

namespace Riemannian

variable {H : Type*} [TopologicalSpace H]
  {E_M : Type*} [NormedAddCommGroup E_M] [NormedSpace ℝ E_M]
  {I : ModelWithCorners ℝ E_M H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsLocallyConstantChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ## Helper: F-typed reified `mfderiv`

A `@[reducible]` def whose return type is `F` (not `TangentSpace 𝓘(ℝ,F) (f x)`).
Sidesteps `HSub` instance synthesis on basepoint-dependent types in iterated
forms. Definitionally equal to `mfderiv I 𝓘(ℝ, F) f x v`. -/

@[reducible] noncomputable def mDirDeriv
    (f : M → F) (x : M) (v : TangentSpace I x) : F :=
  mfderiv I 𝓘(ℝ, F) f x v

omit [IsLocallyConstantChartedSpace H M] in
theorem mDirDeriv_chart_compose_apply
    [IsManifold I 1 M] (x : M)
    (g : E_M → F)
    (hg : DifferentiableWithinAt ℝ g (Set.range I) (extChartAt I x x))
    (v : TangentSpace I x) :
    mDirDeriv (fun y => g (extChartAt I x y)) x v
    = fderivWithin ℝ g (Set.range I) (extChartAt I x x) v :=
  mfderiv_chart_compose_apply x g hg v

/-! ## Bundle-section ↔ flat smoothness bridge -/

variable [IsManifold I 1 M]

/-- **Bundle-section MDifferentiableAt → plain MDifferentiableAt** via
chart trivialization. Uses `IsLocallyConstantChartedSpace` to reduce
the chart's `cLMA` to identity in a nbhd, so the trivialized form
equals the section's value. -/
theorem MDifferentiableAt_of_tangent_bundle_section
    (V : Π y : M, TangentSpace I y) {x : M}
    (hV : MDifferentiableAt I (I.prod 𝓘(ℝ, E_M))
          (fun y => (⟨y, V y⟩ : TotalSpace E_M (TangentSpace I))) x) :
    MDifferentiableAt I 𝓘(ℝ, E_M) V x := by
  have hV_chart : MDifferentiableAt I 𝓘(ℝ, E_M)
      (fun y => ((trivializationAt E_M (TangentSpace I) x) ⟨y, V y⟩).2) x := by
    rw [mdifferentiableAt_totalSpace] at hV
    exact hV.2
  -- Show the trivialized form equals V eventually near x.
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

/-- Specialization: `DifferentiableWithinAt` flat-form for `V ∘ phi.symm`. -/
theorem DifferentiableWithinAt_chart_pullback_of_section
    (V : Π y : M, TangentSpace I y) (x : M)
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

/-! ## Chart-pullback bridges for the iterated `mfderiv` -/

omit [IsManifold I 1 M] in
/-- For `f` differentiable in a nbhd of `x`, the inner directional derivative
`y ↦ mfderiv f y (V y)` agrees eventually with the chart-pullback form
`y ↦ fderivWithin (f ∘ phi.symm) (range I) (phi y) (V y)`. -/
theorem mfderiv_inner_eq_fderivWithin_eventually
    {f : M → F} {V : Π y : M, TangentSpace I y} {x : M}
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

/-- The Mathlib `mpullbackWithin` of a vector field via chart inverse equals
the simple chart-pullback `V ∘ phi.symm` eventually within `range I`. -/
theorem mpullbackWithin_extChartAt_symm_eq_eventually
    (V : Π y : M, TangentSpace I y) (x : M) :
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

/-- `mlieBracket I V W x` reduces to `lieBracketWithin (V ∘ phi.symm) (W ∘ phi.symm)
(range I) (phi x)` via chart pullback (Helper #1 + Helper #3). -/
theorem mlieBracket_eq_lieBracketWithin_chart_pullback
    (V W : Π y : M, TangentSpace I y) (x : M) :
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

/-! ## Main theorem -/

set_option backward.isDefEq.respectTransparency false in
/-- **Manifold scalar Hessian–Lie identity.**
    `D_V(D_W f) - D_W(D_V f) = D_{[V,W]} f` at `x ∈ M`,
where `D_V f := mfderiv I 𝓘(ℝ,F) f · (V ·)`, `mlieBracket` is the
manifold Lie bracket, and `f : M → F` is `C^2` while `V, W` are `C^1`
smooth vector fields.

The `mDirDeriv` form (F-typed) sidesteps basepoint-dependent type issues
in iterated forms. -/
theorem mfderiv_iterate_sub_eq_mlieBracket_apply
    [IsManifold I 2 M]
    (f : M → F) (V W : Π y : M, TangentSpace I y) (x : M)
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
  -- Chart pullback abbreviations.
  set phi := extChartAt I x
  set s : Set E_M := Set.range I
  set f_loc : E_M → F := f ∘ phi.symm
  set V_loc : E_M → E_M := fun e => V (phi.symm e)
  set W_loc : E_M → E_M := fun e => W (phi.symm e)
  -- (1) Smoothness facts.
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
  -- (2) Inner locality: rewrite each inner mfderiv to chart-pullback fderivWithin form.
  have h_inner_W := mfderiv_inner_eq_fderivWithin_eventually (V := W) (f := f) hf_nbhd
  have h_inner_V := mfderiv_inner_eq_fderivWithin_eventually (V := V) (f := f) hf_nbhd
  rw [Filter.EventuallyEq.mfderiv_eq h_inner_W,
      Filter.EventuallyEq.mfderiv_eq h_inner_V]
  -- (3) Outer locality: rewrite outer functions to `g_chart ∘ phi` form.
  have h_outer (V_aux : Π y : M, TangentSpace I y) :
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
  -- (4) Re-fold to mDirDeriv form (F-typed; sidesteps basepoint HSub issue).
  show mDirDeriv (fun y => fderivWithin ℝ f_loc s (phi y) (W_loc (phi y))) x (V x)
       - mDirDeriv (fun y => fderivWithin ℝ f_loc s (phi y) (V_loc (phi y))) x (W x)
       = mDirDeriv f x (mlieBracket I V W x)
  -- Apply mDirDeriv-form Helper #2 to LHS terms.
  have h_g_chart_W_diff : DifferentiableWithinAt ℝ
      (fun e => fderivWithin ℝ f_loc s e (W_loc e)) s (phi x) :=
    h_fderiv_f_loc_diff.clm_apply h_W_loc_diff
  have h_g_chart_V_diff : DifferentiableWithinAt ℝ
      (fun e => fderivWithin ℝ f_loc s e (V_loc e)) s (phi x) :=
    h_fderiv_f_loc_diff.clm_apply h_V_loc_diff
  rw [mDirDeriv_chart_compose_apply x _ h_g_chart_W_diff (V x),
      mDirDeriv_chart_compose_apply x _ h_g_chart_V_diff (W x)]
  -- (5) Substitute V x = V_loc (phi x), W x = W_loc (phi x).
  have h_VW_at_x (V_aux : Π y : M, TangentSpace I y) :
      V_aux x = (fun e => V_aux ((extChartAt I x).symm e)) (phi x) := by
    show V_aux x = V_aux ((extChartAt I x).symm (phi x))
    rw [(extChartAt I x).left_inv (mem_extChartAt_source x)]
  rw [h_VW_at_x V, h_VW_at_x W]
  -- (6) Apply flat Hessian-Lie identity.
  rw [flat_hessianLieWithin_apply h_s_unique h_phi_x_in_s h_interior
        h_f_loc_C2 h_V_loc_diff h_W_loc_diff]
  -- (7) RHS bridge: rewrite manifold mfderiv f via chart pullback + mlieBracket via Helper.
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

end Riemannian
