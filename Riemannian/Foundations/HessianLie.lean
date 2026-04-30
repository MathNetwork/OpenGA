import Mathlib.Geometry.Manifold.VectorField.LieBracket
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Analysis.Calculus.VectorField
import Riemannian.TangentBundle.Smoothness

/-!
# Scalar Hessian–Lie identity

The fundamental identity relating iterated directional derivatives of a
**scalar function** to the Lie bracket of vector fields:

  $$X(Y(f))(x) - Y(X(f))(x) = [X, Y](f)(x)$$

i.e. for `f : M → ℝ` smooth and `X, Y` smooth vector fields,

  ```
  mfderiv (fun y => mfderiv f y (Y y)) x (X x)
  - mfderiv (fun y => mfderiv f y (X y)) x (Y x)
  = mfderiv f x (mlieBracket I X Y x).
  ```

## Strategic placement

This is a **manifold-level foundational identity** — the defining
algebraic property of the Lie bracket as a derivation on `C^∞(M, ℝ)`.
Independent of metric / connection / curvature; lives in
`Foundations/`.

Used by:
* `Riemannian.Curvature` — `riemannCurvature_inner_diagonal_zero`
  (skew-symmetry of Riemann endomorphism), which feeds into
  `ricci_symm` via `bianchi_first`.

## Mathlib upstream candidacy

The flat ($E$ = model space) version of this identity is provable
directly from `VectorField.lieBracket_eq` and the symmetry of the
second derivative (Schwarz). The manifold version follows by
chart-pullback. Both are natural Mathlib upstream PR candidates — the
flat version belongs to `Mathlib.Analysis.Calculus.VectorField`, and
the manifold version to `Mathlib.Geometry.Manifold.VectorField.LieBracket`.

**Ground truth**: standard differential geometry textbook fact (e.g.,
do Carmo 1992 §0 Lemma 5.2; Lee 2013 Smooth Manifolds Proposition 8.30). -/

open VectorField
open scoped ContDiff Manifold Topology

namespace Riemannian

/-! ## Flat version on a normed space

For `f : E → ℝ` and `V, W : E → E` (flat vector fields), the iterated
fderiv satisfies the Lie-bracket identity. This is the model-fiber
content; the manifold version below pulls back through charts. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Flat scalar Hessian–Lie identity.** For a $C^2$ scalar function
`f : E → F` (with `F` an arbitrary normed space) and $C^1$ vector fields
`V, W : E → E`,

  `D(y ↦ Df(y)(V y))(x)(W x) - D(y ↦ Df(y)(W y))(x)(V x) = Df(x)([V,W](x))`

where `[V,W] = lieBracket V W`. The proof uses bilinear-pairing product
rule + symmetry of the second derivative. -/
theorem flat_hessianLie_apply
    {f : E → F} {V W : E → E} {x : E}
    (hf : ContDiffAt ℝ 2 f x)
    (hV : DifferentiableAt ℝ V x) (hW : DifferentiableAt ℝ W x) :
    fderiv ℝ (fun y => fderiv ℝ f y (W y)) x (V x)
    - fderiv ℝ (fun y => fderiv ℝ f y (V y)) x (W x)
    = fderiv ℝ f x (lieBracket ℝ V W x) := by
  -- Step 1: expand each fderiv via product rule for bilinear application.
  -- `y ↦ fderiv f y (V y)` is the composition of `(fderiv f, V)` with the
  -- bilinear pairing `(L, v) ↦ L v`.
  -- Its fderiv at x applied to direction h is:
  --   D²f(x)(h)(V x) + Df(x)(DV(x)(h))
  have hf' : ContDiffAt ℝ 1 (fderiv ℝ f) x :=
    ((hf.of_le (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).fderiv_right (le_refl _))
  have hf'_diff : DifferentiableAt ℝ (fderiv ℝ f) x :=
    hf'.differentiableAt (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  -- Apply the product rule for clm_apply at x:
  -- fderiv (fun y => (g y) (v y)) x = (fderiv g x).flip (v x) + (fderiv f x).comp (fderiv v x)
  -- In Mathlib this is `fderiv_clm_apply`.
  have h1 : fderiv ℝ (fun y => fderiv ℝ f y (V y)) x
          = (fderiv ℝ (fderiv ℝ f) x).flip (V x)
            + (fderiv ℝ f x).comp (fderiv ℝ V x) := by
    rw [fderiv_clm_apply hf'_diff hV]; rw [add_comm]
  have h2 : fderiv ℝ (fun y => fderiv ℝ f y (W y)) x
          = (fderiv ℝ (fderiv ℝ f) x).flip (W x)
            + (fderiv ℝ f x).comp (fderiv ℝ W x) := by
    rw [fderiv_clm_apply hf'_diff hW]; rw [add_comm]
  rw [h2, h1]
  -- Now: subtract and apply at appropriate vectors.
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.coe_comp', Function.comp_apply]
  -- Goal: (fderiv² f x (W x))(V x) + (fderiv f x)(fderiv V x (W x))
  --     - (fderiv² f x (V x))(W x) - (fderiv f x)(fderiv W x (V x))
  --     = (fderiv f x)(lieBracket V W x)
  -- After rw [h2, h1], goal is:
  --   ((D²f x).flip (W x) + (Df x).comp (DW x))(V x)
  --   - ((D²f x).flip (V x) + (Df x).comp (DV x))(W x)
  --   = Df x (lieBracket V W x)
  -- = D²f(x)(V x)(W x) + Df(x)(DW(V x))
  --   - D²f(x)(W x)(V x) - Df(x)(DV(W x))
  --   = Df(x)(DW(V) - DV(W))
  --   = Df(x)(lieBracket V W x)   ✓ (matches Mathlib convention).
  -- Schwarz cancels D² terms: (fderiv² f x (V x))(W x) = (fderiv² f x (W x))(V x).
  have h_symm : (fderiv ℝ (fderiv ℝ f) x (V x)) (W x)
              = (fderiv ℝ (fderiv ℝ f) x (W x)) (V x) :=
    (hf.isSymmSndFDerivAt (by simp) _ _).symm
  rw [h_symm]
  rw [lieBracket_eq, (fderiv ℝ f x).map_sub]
  abel

/-! ## Flat version on a set (`Within` form)

The chart-pullback form needed for the manifold lift. Same identity,
but every `fderiv` becomes `fderivWithin s` and every `lieBracket`
becomes `lieBracketWithin s`. The hypothesis `x ∈ closure (interior s)`
appears via `ContDiffWithinAt.isSymmSndFDerivWithinAt` (Schwarz Within);
for the standard `range I` set on a model with corners this holds at
points in the interior, and on boundaryless models trivially. -/

/-- **Flat scalar Hessian–Lie identity, `Within` form.** For a $C^2$
scalar function `f : E → F` and $C^1$ vector fields `V, W : E → E`,
restricted to a unique-diff set `s` containing `x`:

  `Dwithin(y ↦ Dwithin f s y (V y)) s x (W x)`
  `- Dwithin(y ↦ Dwithin f s y (W y)) s x (V x)`
  `= Dwithin f s x (lieBracketWithin V W s x)`

This is the form pulled back from manifold charts (where `s = range I`,
the model-with-corners' image). -/
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
  -- Same structure as `flat_hessianLie_apply`: expand both fderivWithin
  -- via `fderivWithin_clm_apply`, apply Schwarz Within, simplify.
  have hsx : UniqueDiffWithinAt ℝ s x := hs x hx
  have hf' : ContDiffWithinAt ℝ 1 (fderivWithin ℝ f s) s x :=
    (hf.of_le (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).fderivWithin_right hs
      (by norm_num) hx
  have hf'_diff : DifferentiableWithinAt ℝ (fderivWithin ℝ f s) s x :=
    hf'.differentiableWithinAt (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  have h1 : fderivWithin ℝ (fun y => fderivWithin ℝ f s y (V y)) s x
          = (fderivWithin ℝ (fderivWithin ℝ f s) s x).flip (V x)
            + (fderivWithin ℝ f s x).comp (fderivWithin ℝ V s x) := by
    rw [fderivWithin_clm_apply hsx hf'_diff hV]; rw [add_comm]
  have h2 : fderivWithin ℝ (fun y => fderivWithin ℝ f s y (W y)) s x
          = (fderivWithin ℝ (fderivWithin ℝ f s) s x).flip (W x)
            + (fderivWithin ℝ f s x).comp (fderivWithin ℝ W s x) := by
    rw [fderivWithin_clm_apply hsx hf'_diff hW]; rw [add_comm]
  rw [h2, h1]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.coe_comp', Function.comp_apply]
  -- Schwarz Within cancels the second-derivative cross terms.
  have h_symm : (fderivWithin ℝ (fderivWithin ℝ f s) s x (V x)) (W x)
              = (fderivWithin ℝ (fderivWithin ℝ f s) s x (W x)) (V x) :=
    (hf.isSymmSndFDerivWithinAt (by simp) hs h_interior hx _ _).symm
  rw [h_symm, lieBracketWithin_eq, (fderivWithin ℝ f s x).map_sub]
  abel

/-! ## Manifold version

Lift `flat_hessianLieWithin_apply` from the model space `E` to a smooth
manifold via chart pullback. The statement: for `f : M → F` of class
`C^2` at `x` and smooth vector fields `V, W`,

  `mfderiv (fun y ↦ mfderiv f y (W y)) x (V x)`
  `- mfderiv (fun y ↦ mfderiv f y (V y)) x (W x)`
  `= mfderiv f x (mlieBracket I V W x)`. -/

variable {H : Type*} [TopologicalSpace H]
  {E_M : Type*} [NormedAddCommGroup E_M] [NormedSpace ℝ E_M]
  {I : ModelWithCorners ℝ E_M H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [_root_.IsLocallyConstantChartedSpace H M]

/-! ### Helper #1: chart's mfderiv at base point is identity (eventually)

In a chart-coherent neighbourhood of `x` (provided by
`IsLocallyConstantChartedSpace H M`), the mfderiv of `extChartAt I x` is
the identity CLM. The proof reduces to `tangentBundleCore.coordChange_self`
once chart selection is shown to be constant. -/

/-- **Chart's mfderiv at base-point-in-coherent-nbhd is identity.** -/
theorem mfderiv_extChartAt_eq_id_eventually
    [IsManifold I 1 M] (x : M) :
    ∀ᶠ y in 𝓝 x, mfderiv I 𝓘(ℝ, E_M) (extChartAt I x) y
                = ContinuousLinearMap.id ℝ E_M := by
  have h_chart_eq : ∀ᶠ y in 𝓝 x, chartAt H y = chartAt H x :=
    chartAt_eventually_eq_of_locallyConstant x
  have h_chart_src : (chartAt H x).source ∈ 𝓝 x :=
    (chartAt H x).open_source.mem_nhds (mem_chart_source H x)
  filter_upwards [h_chart_eq, h_chart_src] with y hy_eq hy_src
  -- Use `continuousLinearMapAt_trivializationAt` to convert mfderiv to coordChange,
  -- then `coordChange_self` at the chart-coherent point.
  rw [← TangentBundle.continuousLinearMapAt_trivializationAt hy_src]
  rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core hy_src]
  have h_achart_eq : achart H y = achart H x := Subtype.ext hy_eq
  rw [h_achart_eq]
  ext v
  exact (tangentBundleCore I M).coordChange_self (achart H x) y
    (by simpa [tangentBundleCore_baseSet] using hy_src) v

/-! ### Helper #3: chart-inverse mfderivWithin = id (eventually)

Analog of Helper #1 for the inverse chart. From Mathlib's chart-comp identity
`mfderiv (extChartAt I x) ∘L mfderivWithin (extChartAt I x).symm = id` plus
Helper #1, we get the inverse chart's mfderivWithin is identity in a
chart-target nbhd within `range I`. -/

omit [IsLocallyConstantChartedSpace H M] in
/-- **Chart-inverse mfderivWithin at chart-target-nbhd is identity.** -/
theorem mfderivWithin_extChartAt_symm_eq_id_at_base
    [IsManifold I 1 M] [IsLocallyConstantChartedSpace H M] (x : M) :
    mfderivWithin 𝓘(ℝ, E_M) I (extChartAt I x).symm (Set.range I) (extChartAt I x x)
    = ContinuousLinearMap.id ℝ E_M := by
  -- Mathlib's `mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm`:
  --   mfderiv (extChartAt I x) (phi.symm (phi x)) ∘L mfderivWithin (extChartAt I x).symm (range I) (phi x) = id
  -- phi.symm (phi x) = x, so first factor = mfderiv (extChartAt I x) x = id (Helper #1).
  -- Hence id ∘L mfderivWithin (extChartAt I x).symm (range I) (phi x) = id.
  have h_comp := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm
    (I := I) (M := M) (x := x) (mem_extChartAt_target x)
  have h_id : mfderiv I 𝓘(ℝ, E_M) (extChartAt I x) x = ContinuousLinearMap.id ℝ E_M :=
    (mfderiv_extChartAt_eq_id_eventually (I := I) (M := M) x).self_of_nhds
  have h_symm_eq_x : (extChartAt I x).symm (extChartAt I x x) = x :=
    (extChartAt I x).left_inv (mem_extChartAt_source x)
  rw [h_symm_eq_x] at h_comp
  rw [h_id] at h_comp
  -- h_comp : id ∘L mfderivWithin ... = id
  simpa using h_comp

/-! ### Helper #2: chart-compose `mfderiv` reduces to flat `fderivWithin`

For a flat function `g : E_M → F` differentiable within `range I` at the
chart's image `extChartAt I x x`, the manifold derivative of the composition
`g ∘ extChartAt I x` at `x` equals the flat `fderivWithin g (range I) (...)`.

The proof combines:
* `MDifferentiableAt.mfderiv`: unfold manifold mfderiv to `fderivWithin
  (writtenInExtChartAt) (range I) (phi x)`.
* `writtenInExtChartAt I 𝓘(ℝ,F) x (g ∘ phi) = g ∘ phi ∘ phi.symm = g` on
  `phi.target` (since `phi ∘ phi.symm = id` there).
* `fderivWithin` congruence on `EventuallyEq within s`.

PRE-PAPER. Closure: bounded structural follow-up via
`DifferentiableWithinAt.comp_mdifferentiableAt` + chart-source identification.
~30-40 lines. -/
omit [IsLocallyConstantChartedSpace H M] in
theorem mfderiv_chart_compose_apply
    [IsManifold I 1 M] (x : M)
    (g : E_M → F)
    (hg : DifferentiableWithinAt ℝ g (Set.range I) (extChartAt I x x))
    (v : TangentSpace I x) :
    mfderiv I 𝓘(ℝ, F) (fun y => g (extChartAt I x y)) x v
    = fderivWithin ℝ g (Set.range I) (extChartAt I x x) v := by
  -- Step 1: extChartAt I x is MDifferentiable at x (chart smoothness).
  have h_phi : MDifferentiableAt I 𝓘(ℝ, E_M) (extChartAt I x) x :=
    mdifferentiableAt_extChartAt (mem_chart_source H x)
  -- Step 2: composition is MDifferentiableAt at x (within chart source).
  have h_phi_within : MDifferentiableWithinAt I 𝓘(ℝ, E_M)
      (extChartAt I x) (chartAt H x).source x := h_phi.mdifferentiableWithinAt
  have h_maps : Set.MapsTo (extChartAt I x) (chartAt H x).source (Set.range I) := by
    intro y hy
    rw [extChartAt_coe]
    exact Set.mem_range_self _
  have h_comp_within : MDifferentiableWithinAt I 𝓘(ℝ, F)
      (fun y => g (extChartAt I x y)) (chartAt H x).source x :=
    hg.comp_mdifferentiableWithinAt h_phi_within h_maps
  have h_chart_src_nhds : (chartAt H x).source ∈ 𝓝 x :=
    (chartAt H x).open_source.mem_nhds (mem_chart_source H x)
  have h_comp : MDifferentiableAt I 𝓘(ℝ, F)
      (fun y => g (extChartAt I x y)) x :=
    h_comp_within.mdifferentiableAt h_chart_src_nhds
  -- Step 3: apply MDifferentiableAt.mfderiv.
  rw [h_comp.mfderiv]
  -- Goal: fderivWithin (writtenInExtChartAt _) (range I) (phi x) v
  --     = fderivWithin g (range I) (phi x) v
  -- Step 4: writtenInExtChartAt simplification: it equals g on (extChartAt I x).target.
  have h_eqOn : (extChartAt I x).target.EqOn
      (writtenInExtChartAt I 𝓘(ℝ, F) x (fun y => g (extChartAt I x y))) g := by
    intro e he
    show (extChartAt 𝓘(ℝ, F) (g (extChartAt I x x)))
         (g (extChartAt I x ((extChartAt I x).symm e))) = g e
    rw [(extChartAt I x).right_inv he]
    rfl
  -- (extChartAt I x).target ∈ 𝓝[range I] (phi x), so the functions are EventuallyEq within range I.
  have h_target_nhdsW : (extChartAt I x).target ∈ 𝓝[Set.range I] (extChartAt I x x) :=
    extChartAt_target_mem_nhdsWithin x
  have h_eventually : (writtenInExtChartAt I 𝓘(ℝ, F) x (fun y => g (extChartAt I x y)))
                      =ᶠ[𝓝[Set.range I] (extChartAt I x x)] g := by
    filter_upwards [h_target_nhdsW] with e he
    exact h_eqOn he
  have h_fd_eq : fderivWithin ℝ
      (writtenInExtChartAt I 𝓘(ℝ, F) x (fun y => g (extChartAt I x y)))
      (Set.range I) (extChartAt I x x)
      = fderivWithin ℝ g (Set.range I) (extChartAt I x x) :=
    h_eventually.fderivWithin_eq (h_eqOn (mem_extChartAt_target x))
  rw [h_fd_eq]
  rfl

/-- Helper: directional derivative of a scalar/vector-valued function as
an `F`-typed value (avoids `TangentSpace 𝓘(ℝ, F) (f x)` basepoint
indirection in iterated forms). Definitionally equal to
`mfderiv I 𝓘(ℝ, F) f x v`. -/
@[reducible] noncomputable def mDirDeriv
    (f : M → F) (x : M) (v : TangentSpace I x) : F :=
  mfderiv I 𝓘(ℝ, F) f x v

omit [IsLocallyConstantChartedSpace H M] in
/-- **`mDirDeriv`-form chart-compose** = Helper #2 in F-typed wrapper.
The F-typed return value avoids `TangentSpace 𝓘(ℝ,F) (f x)` basepoint
issues under iterated forms / HSub elaboration. -/
theorem mDirDeriv_chart_compose_apply
    [IsManifold I 1 M] (x : M)
    (g : E_M → F)
    (hg : DifferentiableWithinAt ℝ g (Set.range I) (extChartAt I x x))
    (v : TangentSpace I x) :
    mDirDeriv (fun y => g (extChartAt I x y)) x v
    = fderivWithin ℝ g (Set.range I) (extChartAt I x x) v :=
  mfderiv_chart_compose_apply x g hg v

set_option backward.isDefEq.respectTransparency false in
/-- **Manifold scalar Hessian–Lie identity.** For a $C^2$ scalar function
`f : M → F` on a manifold and $C^1$ smooth vector fields `V, W`,

  `mDirDeriv (fun y ↦ mDirDeriv f y (W y)) x (V x)`
  `- mDirDeriv (fun y ↦ mDirDeriv f y (V y)) x (W x)`
  `= mDirDeriv f x (mlieBracket I V W x)`.

(`mDirDeriv` is `mfderiv` reified to the model fiber `F`; the identity
holds in `mfderiv` form too via `@[reducible]`.) The proof pulls back
through the chart `extChartAt I x`, applies `flat_hessianLieWithin_apply`
with `s = range I`, then pulls forward.

PRE-PAPER. Closure path: chart-pullback expansion via Mathlib bridges
(`MDifferentiableAt.mfderiv`, `mlieBracketWithin_apply`, `mfderiv` chain
rules under chart) — mechanical but intricate, ~80–120 lines. -/
theorem mfderiv_iterate_sub_eq_mlieBracket_apply
    [IsManifold I 2 M]
    (f : M → F) (V W : Π y : M, TangentSpace I y) (x : M)
    (h_interior : extChartAt I x x ∈ closure (interior (Set.range I)))
    (hf : ContMDiffAt I 𝓘(ℝ, F) 2 f x)
    (hV : ContMDiffAt I (I.prod 𝓘(ℝ, E_M)) 1
      (fun y => (⟨y, V y⟩ : Bundle.TotalSpace E_M (TangentSpace I))) x)
    (hW : ContMDiffAt I (I.prod 𝓘(ℝ, E_M)) 1
      (fun y => (⟨y, W y⟩ : Bundle.TotalSpace E_M (TangentSpace I))) x) :
    mDirDeriv (fun y => mDirDeriv f y (W y)) x (V x)
    - mDirDeriv (fun y => mDirDeriv f y (V y)) x (W x)
    = mDirDeriv f x (mlieBracket I V W x) := by
  unfold mDirDeriv
  -- Chart-pullback abbreviations.
  set phi := extChartAt I x with hphi_def
  set s : Set E_M := Set.range I with hs_def
  set f_loc : E_M → F := f ∘ phi.symm with hf_loc_def
  -- Smoothness-open: f is C² in a nbhd of x.
  have hf_nbhd : ∀ᶠ y in 𝓝 x, ContMDiffAt I 𝓘(ℝ, F) 2 f y :=
    (contMDiffAt_iff_contMDiffAt_nhds (by decide : (2 : ℕ∞ω) ≠ ∞)).mp hf
  -- Chart-coherence: chartAt H y = chartAt H x near x.
  have h_chart_eq : ∀ᶠ y in 𝓝 x, chartAt H y = chartAt H x :=
    chartAt_eventually_eq_of_locallyConstant x
  -- Combined: extChartAt I y = phi near x.
  have h_ext_eq : ∀ᶠ y in 𝓝 x, extChartAt I y = phi := by
    filter_upwards [h_chart_eq] with y hy
    show extChartAt I y = extChartAt I x
    rw [extChartAt, extChartAt, hy]
  -- Step 2 (inner locality): for y near x, `mfderiv f y (W y)` equals
  -- `fderivWithin f_loc s (phi y) (W y)`.
  have h_inner_W : (fun y => mfderiv I 𝓘(ℝ, F) f y (W y))
      =ᶠ[𝓝 x] (fun y => fderivWithin ℝ f_loc s (phi y) (W y)) := by
    filter_upwards [hf_nbhd, h_ext_eq] with y hy_smooth hy_ext
    have hy_diff : MDifferentiableAt I 𝓘(ℝ, F) f y :=
      hy_smooth.mdifferentiableAt (by norm_num : (2 : ℕ∞ω) ≠ 0)
    have h_mfd := hy_diff.mfderiv
    -- writtenInExtChartAt I 𝓘(ℝ, F) y f = f ∘ (extChartAt I y).symm = f ∘ phi.symm = f_loc
    have h_written : writtenInExtChartAt I 𝓘(ℝ, F) y f = f_loc := by
      ext e
      show (extChartAt 𝓘(ℝ, F) (f y)) (f ((extChartAt I y).symm e)) = f_loc e
      rw [hy_ext]
      simp [extChartAt, hf_loc_def]
    rw [h_mfd, h_written]
    show fderivWithin ℝ f_loc s ((extChartAt I y) y) (W y)
      = fderivWithin ℝ f_loc s (phi y) (W y)
    rw [hy_ext]
  have h_inner_V : (fun y => mfderiv I 𝓘(ℝ, F) f y (V y))
      =ᶠ[𝓝 x] (fun y => fderivWithin ℝ f_loc s (phi y) (V y)) := by
    filter_upwards [hf_nbhd, h_ext_eq] with y hy_smooth hy_ext
    have hy_diff : MDifferentiableAt I 𝓘(ℝ, F) f y :=
      hy_smooth.mdifferentiableAt (by norm_num : (2 : ℕ∞ω) ≠ 0)
    have h_mfd := hy_diff.mfderiv
    have h_written : writtenInExtChartAt I 𝓘(ℝ, F) y f = f_loc := by
      ext e
      show (extChartAt 𝓘(ℝ, F) (f y)) (f ((extChartAt I y).symm e)) = f_loc e
      rw [hy_ext]
      simp [extChartAt, hf_loc_def]
    rw [h_mfd, h_written]
    show fderivWithin ℝ f_loc s ((extChartAt I y) y) (V y)
      = fderivWithin ℝ f_loc s (phi y) (V y)
    rw [hy_ext]
  -- Rewrite the outer-mfderiv via inner locality.
  rw [Filter.EventuallyEq.mfderiv_eq h_inner_W,
      Filter.EventuallyEq.mfderiv_eq h_inner_V]
  -- Local pullback vector fields (flat).
  set V_loc : E_M → E_M := fun e => V (phi.symm e) with hV_loc_def
  set W_loc : E_M → E_M := fun e => W (phi.symm e) with hW_loc_def
  -- Outer function (chart form): match LHS to `fderivWithin g_chart s (phi x) (...)`.
  -- The function `g_W(y) := fderivWithin f_loc s (phi y) (W y)` agrees with
  -- `(fun e => fderivWithin f_loc s e (W_loc e)) ∘ phi` near x (since phi.symm ∘ phi = id
  -- on chart source).
  -- Define the chart-form outer functions:
  set g_chart_W : E_M → F := fun e => fderivWithin ℝ f_loc s e (W_loc e) with hg_chart_W_def
  set g_chart_V : E_M → F := fun e => fderivWithin ℝ f_loc s e (V_loc e) with hg_chart_V_def
  -- For y in chart-coherent + chart-source nbhd:
  --   fderivWithin f_loc s (phi y) (W y) = g_chart_W (phi y)
  -- (since W y = W (phi.symm (phi y)) = W_loc (phi y) for y in chart source).
  have h_outer_W : (fun y => fderivWithin ℝ f_loc s (phi y) (W y))
      =ᶠ[𝓝 x] (fun y => g_chart_W (phi y)) := by
    have h_chart_src : (chartAt H x).source ∈ 𝓝 x :=
      (chartAt H x).open_source.mem_nhds (mem_chart_source H x)
    filter_upwards [h_chart_src] with y hy_src
    show fderivWithin ℝ f_loc s (phi y) (W y) = g_chart_W (phi y)
    show fderivWithin ℝ f_loc s (phi y) (W y)
      = fderivWithin ℝ f_loc s (phi y) (W_loc (phi y))
    have : W_loc (phi y) = W y := by
      show W (phi.symm (phi y)) = W y
      have : phi.symm (phi y) = y := by
        show (extChartAt I x).symm (extChartAt I x y) = y
        exact (extChartAt I x).left_inv (by rwa [extChartAt_source])
      rw [this]
    rw [this]
  have h_outer_V : (fun y => fderivWithin ℝ f_loc s (phi y) (V y))
      =ᶠ[𝓝 x] (fun y => g_chart_V (phi y)) := by
    have h_chart_src : (chartAt H x).source ∈ 𝓝 x :=
      (chartAt H x).open_source.mem_nhds (mem_chart_source H x)
    filter_upwards [h_chart_src] with y hy_src
    show fderivWithin ℝ f_loc s (phi y) (V y) = g_chart_V (phi y)
    show fderivWithin ℝ f_loc s (phi y) (V y)
      = fderivWithin ℝ f_loc s (phi y) (V_loc (phi y))
    have : V_loc (phi y) = V y := by
      show V (phi.symm (phi y)) = V y
      have : phi.symm (phi y) = y := by
        show (extChartAt I x).symm (extChartAt I x y) = y
        exact (extChartAt I x).left_inv (by rwa [extChartAt_source])
      rw [this]
    rw [this]
  rw [Filter.EventuallyEq.mfderiv_eq h_outer_W,
      Filter.EventuallyEq.mfderiv_eq h_outer_V]
  -- Auxiliary equality: V x = V_loc (phi x) and W x = W_loc (phi x).
  have h_V_at_x : V x = V_loc (phi x) := by
    show V x = V (phi.symm (phi x))
    have : phi.symm (phi x) = x := by
      show (extChartAt I x).symm (extChartAt I x x) = x
      exact (extChartAt I x).left_inv (mem_extChartAt_source x)
    rw [this]
  have h_W_at_x : W x = W_loc (phi x) := by
    show W x = W (phi.symm (phi x))
    have : phi.symm (phi x) = x := by
      show (extChartAt I x).symm (extChartAt I x x) = x
      exact (extChartAt I x).left_inv (mem_extChartAt_source x)
    rw [this]
  -- Re-fold to mDirDeriv form (F-typed; HSub on F trivial; sidesteps basepoint issue).
  show mDirDeriv (fun y => g_chart_W (phi y)) x (V x)
       - mDirDeriv (fun y => g_chart_V (phi y)) x (W x)
       = mDirDeriv f x (mlieBracket I V W x)
  -- Smoothness premises (sorry'd; bounded follow-up via f C² + V, W C¹).
  have h_f_loc_C2 : ContDiffWithinAt ℝ 2 f_loc s (extChartAt I x x) :=
    (contMDiffAt_iff.mp hf).2
  -- V/W as functions M → E_M (using TangentSpace I y = E_M definitionally), pulled back via phi.symm.
  -- From hV/hW (bundle-section ContMDiffAt) + IsLocallyConstantChartedSpace + chart-bridge.
  -- Helper: V (treated as M → E_M via TangentSpace I y = E_M defeq) is MDifferentiableAt at x.
  have hV_pt : MDifferentiableAt I (I.prod 𝓘(ℝ, E_M))
      (fun y => (⟨y, V y⟩ : Bundle.TotalSpace E_M (TangentSpace I))) x :=
    hV.mdifferentiableAt (by norm_num : (1 : ℕ∞ω) ≠ 0)
  have hW_pt : MDifferentiableAt I (I.prod 𝓘(ℝ, E_M))
      (fun y => (⟨y, W y⟩ : Bundle.TotalSpace E_M (TangentSpace I))) x :=
    hW.mdifferentiableAt (by norm_num : (1 : ℕ∞ω) ≠ 0)
  -- Chart-form of V/W at x: applying (trivAt x).cLMA — by Helper #1 logic (chart-coherent
  -- nbhd ⇒ cLMA = id), this equals V/W.
  have hV_chart : MDifferentiableAt I 𝓘(ℝ, E_M)
      (fun y => ((trivializationAt E_M (TangentSpace I) x) ⟨y, V y⟩).2) x := by
    have h := hV_pt
    rw [mdifferentiableAt_totalSpace] at h
    exact h.2
  have hW_chart : MDifferentiableAt I 𝓘(ℝ, E_M)
      (fun y => ((trivializationAt E_M (TangentSpace I) x) ⟨y, W y⟩).2) x := by
    have h := hW_pt
    rw [mdifferentiableAt_totalSpace] at h
    exact h.2
  have h_chart_eq_at : ∀ᶠ y in 𝓝 x, chartAt H y = chartAt H x :=
    chartAt_eventually_eq_of_locallyConstant x
  have h_trivAt_eqV : (fun y => ((trivializationAt E_M (TangentSpace I) x) ⟨y, V y⟩).2)
                     =ᶠ[𝓝 x] V := by
    have h_base : (trivializationAt E_M (TangentSpace I) x).baseSet ∈ 𝓝 x :=
      (trivializationAt E_M (TangentSpace I) x).open_baseSet.mem_nhds
        (FiberBundle.mem_baseSet_trivializationAt' x)
    have h_chart_src : (chartAt H x).source ∈ 𝓝 x :=
      (chartAt H x).open_source.mem_nhds (mem_chart_source H x)
    filter_upwards [h_base, h_chart_src, h_chart_eq_at] with y hy_base hy_src hy_eq
    show ((trivializationAt E_M (TangentSpace I) x) ⟨y, V y⟩).2 = V y
    rw [← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) _ hy_base]
    -- (trivAt x).cLMA y = id (Helper #1 via continuousLinearMapAt_trivializationAt + chart eq).
    have h_id : (trivializationAt E_M (TangentSpace I) x).continuousLinearMapAt ℝ y
              = ContinuousLinearMap.id ℝ E_M := by
      rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core hy_src]
      have h_achart_eq : achart H y = achart H x := Subtype.ext hy_eq
      rw [h_achart_eq]
      ext v
      exact (tangentBundleCore I M).coordChange_self (achart H x) y
        (by simpa [tangentBundleCore_baseSet] using hy_src) v
    rw [h_id]; rfl
  have h_trivAt_eqW : (fun y => ((trivializationAt E_M (TangentSpace I) x) ⟨y, W y⟩).2)
                     =ᶠ[𝓝 x] W := by
    have h_base : (trivializationAt E_M (TangentSpace I) x).baseSet ∈ 𝓝 x :=
      (trivializationAt E_M (TangentSpace I) x).open_baseSet.mem_nhds
        (FiberBundle.mem_baseSet_trivializationAt' x)
    have h_chart_src : (chartAt H x).source ∈ 𝓝 x :=
      (chartAt H x).open_source.mem_nhds (mem_chart_source H x)
    filter_upwards [h_base, h_chart_src, h_chart_eq_at] with y hy_base hy_src hy_eq
    show ((trivializationAt E_M (TangentSpace I) x) ⟨y, W y⟩).2 = W y
    rw [← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) _ hy_base]
    have h_id : (trivializationAt E_M (TangentSpace I) x).continuousLinearMapAt ℝ y
              = ContinuousLinearMap.id ℝ E_M := by
      rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core hy_src]
      have h_achart_eq : achart H y = achart H x := Subtype.ext hy_eq
      rw [h_achart_eq]
      ext v
      exact (tangentBundleCore I M).coordChange_self (achart H x) y
        (by simpa [tangentBundleCore_baseSet] using hy_src) v
    rw [h_id]; rfl
  have hV_plain : MDifferentiableAt I 𝓘(ℝ, E_M) V x :=
    hV_chart.congr_of_eventuallyEq h_trivAt_eqV.symm
  have hW_plain : MDifferentiableAt I 𝓘(ℝ, E_M) W x :=
    hW_chart.congr_of_eventuallyEq h_trivAt_eqW.symm
  -- Compose with chart-inverse: V_loc = V ∘ phi.symm = MDiff-pulled-back-flat.
  have h_V_loc_diff : DifferentiableWithinAt ℝ V_loc s (extChartAt I x x) := by
    have h := MDifferentiableWithinAt.differentiableWithinAt_comp_extChartAt_symm
      (s := Set.univ) hV_plain.mdifferentiableWithinAt
    show DifferentiableWithinAt ℝ V_loc (Set.range I) (extChartAt I x x)
    convert h using 2
    simp [Set.preimage_univ, Set.univ_inter]
  have h_W_loc_diff : DifferentiableWithinAt ℝ W_loc s (extChartAt I x x) := by
    have h := MDifferentiableWithinAt.differentiableWithinAt_comp_extChartAt_symm
      (s := Set.univ) hW_plain.mdifferentiableWithinAt
    show DifferentiableWithinAt ℝ W_loc (Set.range I) (extChartAt I x x)
    convert h using 2
    simp [Set.preimage_univ, Set.univ_inter]
  have h_s_unique : UniqueDiffOn ℝ s := I.uniqueDiffOn
  have h_phi_x_in_s : phi x ∈ s :=
    extChartAt_target_subset_range x (mem_extChartAt_target x)
  -- g_chart_W e := fderivWithin f_loc s e (W_loc e). Bilinear in (fderivWithin f_loc s e, W_loc e).
  have h_fderiv_f_loc_C1 : ContDiffWithinAt ℝ 1 (fderivWithin ℝ f_loc s) s (extChartAt I x x) :=
    h_f_loc_C2.fderivWithin_right h_s_unique (by norm_num : ((1 : ℕ∞ω)) + 1 ≤ 2) h_phi_x_in_s
  have h_fderiv_f_loc_diff : DifferentiableWithinAt ℝ (fderivWithin ℝ f_loc s) s
      (extChartAt I x x) :=
    h_fderiv_f_loc_C1.differentiableWithinAt (by norm_num : (1 : ℕ∞ω) ≠ 0)
  have h_g_chart_W_diff : DifferentiableWithinAt ℝ g_chart_W s (extChartAt I x x) :=
    h_fderiv_f_loc_diff.clm_apply h_W_loc_diff
  have h_g_chart_V_diff : DifferentiableWithinAt ℝ g_chart_V s (extChartAt I x x) :=
    h_fderiv_f_loc_diff.clm_apply h_V_loc_diff
  have h_f_diff : MDifferentiableAt I 𝓘(ℝ, F) f x :=
    hf.mdifferentiableAt (by norm_num : (2 : ℕ∞ω) ≠ 0)
  have h_f_loc_diff_W : DifferentiableWithinAt ℝ f_loc s (extChartAt I x x) :=
    (h_f_loc_C2.of_le (by norm_num : (1 : ℕ∞ω) ≤ 2)).differentiableWithinAt
      (by norm_num : (1 : ℕ∞ω) ≠ 0)
  -- Apply mDirDeriv-form Helper #2 to LHS terms (works on F-typed mDirDeriv).
  rw [mDirDeriv_chart_compose_apply x g_chart_W h_g_chart_W_diff (V x),
      mDirDeriv_chart_compose_apply x g_chart_V h_g_chart_V_diff (W x)]
  -- Substitute V x = V_loc (phi x), W x = W_loc (phi x).
  rw [h_V_at_x, h_W_at_x]
  -- Goal: fderivWithin g_chart_W s (phi x) (V_loc (phi x))
  --     - fderivWithin g_chart_V s (phi x) (W_loc (phi x))
  --     = mDirDeriv f x (mlieBracket I V W x)
  -- Unfold g_chart_W, g_chart_V (via @[reducible] / defn) and apply flat lemma.
  have h_s_unique : UniqueDiffOn ℝ s := I.uniqueDiffOn
  have h_phi_x_in_s : phi x ∈ s :=
    extChartAt_target_subset_range x (mem_extChartAt_target x)
  show fderivWithin ℝ (fun e => fderivWithin ℝ f_loc s e (W_loc e)) s
        (extChartAt I x x) (V_loc (extChartAt I x x))
       - fderivWithin ℝ (fun e => fderivWithin ℝ f_loc s e (V_loc e)) s
        (extChartAt I x x) (W_loc (extChartAt I x x))
       = mDirDeriv f x (mlieBracket I V W x)
  rw [flat_hessianLieWithin_apply h_s_unique h_phi_x_in_s h_interior
        h_f_loc_C2 h_V_loc_diff h_W_loc_diff]
  -- Goal: fderivWithin f_loc s (phi x) (lieBracketWithin V_loc W_loc s (phi x))
  --     = mDirDeriv f x (mlieBracket I V W x)
  -- RHS bridge: apply mDirDeriv-form Helper #2 to mDirDeriv f x.
  -- `f` is not yet of the form `g ∘ extChartAt I x`, but
  -- `f = (f ∘ phi.symm) ∘ phi = f_loc ∘ phi` by `phi.symm ∘ phi = id` on chart source
  -- — same trick as h_outer_W. Use eventually-equal then mfderiv_eq.
  -- Combined with Helper #1 → mfderiv (extChartAt I x) x = id, this gives
  -- mDirDeriv f x v = fderivWithin f_loc s (phi x) v.
  -- Apply via Helper #2 on f_loc:
  have h_f_outer : (fun y : M => f y) =ᶠ[𝓝 x] (fun y => f_loc (phi y)) := by
    have h_chart_src : (chartAt H x).source ∈ 𝓝 x :=
      (chartAt H x).open_source.mem_nhds (mem_chart_source H x)
    filter_upwards [h_chart_src] with y hy_src
    show f y = f (phi.symm (phi y))
    have : phi.symm (phi y) = y := by
      show (extChartAt I x).symm (extChartAt I x y) = y
      exact (extChartAt I x).left_inv (by rwa [extChartAt_source])
    rw [this]
  have h_mfderiv_eq : mfderiv I 𝓘(ℝ, F) f x
                    = mfderiv I 𝓘(ℝ, F) (fun y => f_loc (phi y)) x :=
    Filter.EventuallyEq.mfderiv_eq h_f_outer
  rw [show mDirDeriv f x (mlieBracket I V W x)
        = mfderiv I 𝓘(ℝ, F) f x (mlieBracket I V W x) from rfl,
      h_mfderiv_eq]
  -- Apply Helper #2 to RHS to get `fderivWithin f_loc s (phi x) (mlieBracket I V W x)`.
  have h_helper2_f : mfderiv I 𝓘(ℝ, F) (fun y => f_loc (phi y)) x (mlieBracket I V W x)
                  = fderivWithin ℝ f_loc s (extChartAt I x x) (mlieBracket I V W x) :=
    mfderiv_chart_compose_apply x f_loc h_f_loc_diff_W (mlieBracket I V W x)
  -- Now goal: fderivWithin f_loc s (phi x) (lieBracketWithin V_loc W_loc s (phi x))
  --         = mfderiv ... f_loc∘phi ... x (mlieBracket I V W x)
  -- Bridge mlieBracket via mlieBracketWithin_apply + Helper #1.
  have h_lieBr_eq : lieBracketWithin ℝ V_loc W_loc s (phi x) = mlieBracket I V W x := by
    rw [show mlieBracket I V W x = mlieBracketWithin I V W Set.univ x from rfl,
        VectorField.mlieBracketWithin_apply]
    have h_id : mfderiv I 𝓘(ℝ, E_M) (extChartAt I x) x = ContinuousLinearMap.id ℝ E_M :=
      (mfderiv_extChartAt_eq_id_eventually (I := I) (M := M) x).self_of_nhds
    rw [h_id]
    rw [show (ContinuousLinearMap.id ℝ E_M).inverse = ContinuousLinearMap.id ℝ E_M
        from ContinuousLinearMap.inverse_id]
    simp only [ContinuousLinearMap.coe_id, id_eq, Set.preimage_univ, Set.univ_inter]
    -- Goal: lieBracketWithin V_loc W_loc s (phi x)
    --     = lieBracketWithin (mpullbackWithin V) (mpullbackWithin W) (range I) (phi x)
    -- Need: V_loc =ᶠ[𝓝[s] (phi x)] mpullbackWithin V (range I) (and similarly W) so
    -- lieBracketWithin congruence applies.
    -- mpullbackWithin V (range I) e := (mfderivWithin phi.symm s e).inverse (V (phi.symm e))
    -- At e = phi x: mfderivWithin = id (Helper #3) → mpullbackWithin V (phi x) = V x = V_loc (phi x).
    -- Eventually-equal version of Helper #3 needed for lieBracketWithin congruence.
    sorry
  rw [h_lieBr_eq]
  exact h_helper2_f.symm

end Riemannian
