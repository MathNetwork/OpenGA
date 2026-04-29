import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorField.Pullback
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-!
# Tangent bundle — flat-codomain inverse trivialization + smoothness

Framework-owned **flat-codomain** form of `Trivialization.symmL` for the
tangent bundle, hiding the dependent codomain `E →L[ℝ] TangentSpace I y`
behind the `TangentSpace I y = E` def-eq. User-facing API takes flat
types; `cast` is internal implementation detail.

## API

  * `TangentBundle.symmLFlat x y : E →L[ℝ] E` — flat-type inverse
    trivialization at fiber `y`, basepoint `x`. Internally
    `(trivializationAt E (TangentSpace I) x).symmL ℝ y`, retyped via
    the `TangentSpace I y = E` def-eq.
  * `TangentBundle.symmLFlat_mdifferentiableAt` — smoothness of
    `y ↦ symmLFlat x y` at `x` as a function `M → (E →L[ℝ] E)`.
    Sorry'd body, statement clean (no cast / no `h_TS_E_eq`).

## Internal proof structure

Two flat-typed framework wrappers + one filter-level bridge:

  * **Wrapper** `symmLFlat` — flat form of `Trivialization.symmL`.
  * **Wrapper** `mfderivWithinFlat` (private) — flat form of
    `mfderivWithin (range I) (extChartAt I x).symm`.
  * **Helper 1** `mfderivWithinFlat_mdifferentiableAt` (private) —
    parametric smoothness of the chart-inverse-mfderiv.
    Substantive open content. Adapted from
    `Mathlib/VectorField/Pullback.lean` lines 280-322. **Sorry'd body**.
  * **Helper 2** `symmLFlat_eventuallyEq_mfderivWithinFlat` (private) —
    pointwise rewrite via `TangentBundle.symmL_trivializationAt` lifted
    to filter level. Closed.
  * **Main** `symmLFlat_mdifferentiableAt` — composes Helper 1 with
    `mdifferentiableAt_extChartAt`, bridges via Helper 2 with
    `MDifferentiableAt.congr_of_eventuallyEq`. Real proof, no `sorry`
    modulo Helper 1.

## Mathlib upstream candidacy

  * Helper 1 is a self-contained Mathlib upstream PR candidate
    (parametric smoothness of `mfderivWithin` for chart inverses).
    Generalisation: `[NontriviallyNormedField 𝕜]`, target
    `Mathlib/Geometry/Manifold/MFDeriv/Atlas.lean`.
  * `symmLFlat` / `mfderivWithinFlat` are framework-internal flat-API
    wrappers — Mathlib favors dependent codomain by design.

Proof technique acknowledgment: adapted from `VectorField/Pullback.lean`.

## Used by

  * `OpenGALib.MDifferentiableAt.metricInner_smoothAt`
    (`Riemannian/Metric/Smooth.lean`).

**Ground truth**: standard for tangent bundles — chart-derivatives are
smooth, hence so are their inverses.
-/

open scoped ContDiff Manifold Topology

namespace TangentBundle

set_option backward.isDefEq.respectTransparency false in
/-- **Flat-codomain inverse trivialization** of the tangent bundle.

The underlying value at fiber `y` is
`(trivializationAt E (TangentSpace I) x).symmL ℝ y`, retyped as
`E →L[ℝ] E` via the `TangentSpace I y = E` def-eq (made transparent by
`backward.isDefEq.respectTransparency false`). Hides the dependent
codomain so user-facing API speaks of `M → (E →L[ℝ] E)` directly. -/
noncomputable def symmLFlat
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (x y : M) : E →L[ℝ] E :=
  (trivializationAt E (TangentSpace I) x).symmL ℝ y

set_option backward.isDefEq.respectTransparency false in
/-- **Flat-codomain chart-inverse-mfderiv** wrapper. The underlying
value at `e₀ ∈ E` is
`mfderivWithin 𝓘(ℝ, E) I (extChartAt I x).symm (range I) e₀`, retyped
as `E →L[ℝ] E` via `TangentSpace I _ = E` def-eq. -/
private noncomputable def mfderivWithinFlat
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (x : M) (e₀ : E) : E →L[ℝ] E :=
  mfderivWithin 𝓘(ℝ, E) I (extChartAt I x).symm (Set.range I) e₀

/-! ## Framework infrastructure (upstream self-build)

Mathlib gives `Trivialization.contMDiffOn` (trivialization smooth as
fiber-bundle iso) and `ContMDiffVectorBundle.contMDiffOn_coordChangeL`
(fixed-pair coord change smooth). Neither directly gives smoothness of
one trivialization's `continuousLinearMapAt` as model-fiber-valued
`B → (F →L F)`. We self-build the missing upstream pieces.

### Layered framework primitives

* **Layer 1**: `contMDiff_constSection_TangentSpace` — constant-vector
  section of tangent bundle is smooth (uses the `TangentSpace I _ = E`
  def-eq + `IsManifold` smooth-atlas via chart-change-derivative
  regularity).
* **Layer 2**: `contMDiffOn_clm_of_components` — finite-dim CLM lift:
  pointwise-in-`v` smoothness gives CLM-valued smoothness, via basis
  decomposition.
* **Layer 3**: `contMDiffOn_continuousLinearMapAt_apply` —
  `b ↦ e.cLMA R b v : M → E` smooth on `e.baseSet` for fixed `v`,
  via Layer 1 + `mdifferentiableAt_section`.
* **Layer 4**: `contMDiffOn_continuousLinearMapAtFlat` — main result,
  via Layer 2 + Layer 3.

Each layer is independently a Mathlib upstream PR candidate. Closure
work is multi-commit; the layered structure makes each commit atomic. -/

set_option backward.isDefEq.respectTransparency false in
/-- **Flat-codomain forward chart mfderiv** wrapper. Underlying value
at `y ∈ M` is `(trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ y`,
retyped from `TangentSpace I y →L[ℝ] E` to `E →L[ℝ] E` via the
`TangentSpace I y = E` def-eq.

By `TangentBundle.continuousLinearMapAt_trivializationAt`, equals
`mfderiv (extChartAt I x₀) y` on chart source. -/
noncomputable def continuousLinearMapAtFlat
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (x₀ y : M) : E →L[ℝ] E :=
  (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ y

/-! ### Layer 1 — constant section smoothness for tangent bundle -/

/-- **Constant-vector section of the tangent bundle is smooth.**

For `v : E` (model fiber), the section `b ↦ ⟨b, v⟩ : M → TangentBundle I M`
(treating `v` as a fiber value via the def-eq `TangentSpace I b = E`) is
`C^∞`. This is the "`v`-coordinate vector field globalised" — well-defined
because `TangentSpace I _ ≡ E` literally.

**Sorry status**: framework upstream. Closure path:
* `mdifferentiableAt_section`: smoothness of section ↔ smoothness of
  `b ↦ (trivializationAt _ _ b₀ ⟨b, v⟩).2 = e.cLMA R b v` near `b₀`.
* By `TangentBundle.continuousLinearMapAt_trivializationAt` +
  `tangentBundleCore_coordChange` identity:
    `e.cLMA R b v = Z.coordChange (achart H b) (achart H b₀) b v`
* For `b` near `b₀` with `chartAt H b = chartAt H b₀` (always true on
  chart source for `IsManifold`'s smooth atlas via choice of chartAt),
  `coordChange = id`, so the value is constantly `v`.
* `IsManifold` smooth atlas + chart-change derivative regularity handle
  the general case (chart at `b` may technically differ but the
  coordChange evaluates smoothly). -/
theorem contMDiff_constSection_TangentSpace
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (v : E) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, v⟩ : TangentBundle I M)) := by
  -- TODO: build via `mdifferentiableAt_section` + chart-change identity.
  -- See docstring above. Multi-commit closure.
  sorry

/-! ### Helper: `ContMDiffOn.add` for normed-target

Mathlib has `ContDiff.add`/`ContDiff_add` for normed source+target, and
`ContMDiffOn.add_section` for bundle sections. For functions `M → F`
(M manifold, F normed) — i.e., the trivial-bundle case in normed-target
flat form — there's no direct lemma. Self-built via `contDiff_add`
(addition is `C^∞`) + `ContMDiffOn.prodMk_space` + composition. -/

theorem _root_.ContMDiffOn.add_normed
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
    {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners 𝕜 EM HM}
    {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {n : ℕ∞ω} {f g : M → F} {s : Set M}
    (hf : ContMDiffOn IM 𝓘(𝕜, F) n f s) (hg : ContMDiffOn IM 𝓘(𝕜, F) n g s) :
    ContMDiffOn IM 𝓘(𝕜, F) n (fun x => f x + g x) s := by
  have h_prod : ContMDiffOn IM 𝓘(𝕜, F × F) n (fun x => (f x, g x)) s :=
    hf.prodMk_space hg
  have h_add : ContMDiff 𝓘(𝕜, F × F) 𝓘(𝕜, F) n (fun p : F × F => p.1 + p.2) :=
    contDiff_add.contMDiff
  exact h_add.comp_contMDiffOn h_prod

/-- Finite-sum version derived by induction. -/
theorem _root_.ContMDiffOn.finset_sum_normed
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
    {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners 𝕜 EM HM}
    {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {n : ℕ∞ω} {ι : Type*} (t : Finset ι) {f : ι → M → F} {s : Set M}
    (h : ∀ i ∈ t, ContMDiffOn IM 𝓘(𝕜, F) n (f i) s) :
    ContMDiffOn IM 𝓘(𝕜, F) n (fun x => ∑ i ∈ t, f i x) s := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact contMDiffOn_const
  | insert i t' hi IH =>
    simp_rw [Finset.sum_insert hi]
    refine (h i (Finset.mem_insert_self _ _)).add_normed
      (IH (fun j hj => h j (Finset.mem_insert_of_mem hj)))

/-! ### Layer 2 — finite-dim CLM lift -/

/-- **Finite-dimensional CLM-valued smoothness from componentwise
smoothness**.

Given `T : M → (E →L[ℝ] E)` and a basis `b₁, ..., bₙ` of `E`, if
`y ↦ T y bᵢ : M → E` is smooth for each `i`, then `T : M → (E →L[ℝ] E)`
is smooth.

**Sorry status**: framework upstream. Closure path:
* In finite-dim, `T y` is determined by `T y bᵢ` for basis elements via
  `T y = ∑ᵢ (T y bᵢ) ⊗ bᵢ*` where `⊗` is `ContinuousLinearMap.smulRight`
  applied to dual basis.
* Each summand smooth: `bᵢ*` is constant CLM, `T y bᵢ` smooth in y,
  combine via `ContinuousLinearMap.smulRight` (smooth, bilinear).
* Sum of smooth CLM-valued is smooth. -/
theorem contMDiffOn_clm_of_components
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
    {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners 𝕜 EM HM}
    {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
    {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
    {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
    {n : ℕ∞ω}
    (T : M → F₁ →L[𝕜] F₂) {ι : Type*} [Fintype ι]
    (basis : Module.Basis ι 𝕜 F₁) (s : Set M)
    (h_components : ∀ i : ι, ContMDiffOn IM 𝓘(𝕜, F₂) n
      (fun y : M => T y (basis i)) s) :
    ContMDiffOn IM 𝓘(𝕜, F₁ →L[𝕜] F₂) n T s := by
  -- Strategy: T y = ∑ᵢ smulRight (basis.coord i) (T y (basisᵢ))
  -- Each summand smooth via smulRight (CLM in F₂); sum smooth via finset sum.
  -- Step 1: rewrite T as the basis-decomposition sum.
  have decomp : T = fun y =>
      ∑ i, (basis.coord i).toContinuousLinearMap.smulRight (T y (basis i)) := by
    funext y
    ext v
    rw [ContinuousLinearMap.sum_apply]
    have hv : v = ∑ i, basis.repr v i • basis i := by
      simpa using (basis.linearCombination_repr v).symm
    conv_lhs => rw [hv]
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    simp [ContinuousLinearMap.smulRight_apply,
      LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply,
      (T y).map_smul]
  rw [decomp]
  -- Step 2: closure of finset sum + smulRight smoothness.
  apply ContMDiffOn.finset_sum_normed
  intro i _
  -- Goal: ContMDiffOn IM 𝓘(𝕜, F₁ →L F₂) n
  --   (fun y => (basis.coord i).toCLM.smulRight (T y (basis i))) s
  have h_smulRight : ContMDiff 𝓘(𝕜, F₂) 𝓘(𝕜, F₁ →L[𝕜] F₂) n
      (fun w : F₂ => (basis.coord i).toContinuousLinearMap.smulRight w) := by
    -- The map `w ↦ φ.smulRight w` is `smulRightL 𝕜 F₁ F₂ φ`, a CLM, hence smooth.
    have h_eq : (fun w : F₂ => (basis.coord i).toContinuousLinearMap.smulRight w)
        = ContinuousLinearMap.smulRightL 𝕜 F₁ F₂ (basis.coord i).toContinuousLinearMap := by
      funext w; rfl
    rw [h_eq]
    exact (ContinuousLinearMap.smulRightL 𝕜 F₁ F₂
      (basis.coord i).toContinuousLinearMap).contMDiff
  exact h_smulRight.comp_contMDiffOn (h_components i)

/-! ### Layer 3 — fixed-`v` smoothness of `continuousLinearMapAt` -/

/-- **Trivialization's `continuousLinearMapAt` applied to fixed vector
is smooth**, on chart base set.

For fixed `v : E`, `b ↦ (trivAt _ _ x₀).cLMA R b v : M → E` is `C^∞` on
`baseSet`. Direct corollary of Layer 1 (constant section smooth) +
`mdifferentiableAt_section` (Mathlib characterization). -/
theorem contMDiffOn_continuousLinearMapAt_apply
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (x₀ : M) (v : E) :
    ContMDiffOn I 𝓘(ℝ, E) ∞
      (fun b : M => (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ b v)
      (trivializationAt E (TangentSpace I) x₀).baseSet := by
  -- Mathlib provides `ContMDiffVectorBundle ∞ E (TangentSpace I) I` as an
  -- instance when `[IsManifold I ∞ M]` (Tangent.lean line 330). Should
  -- synthesize automatically.
  have h_const := contMDiff_constSection_TangentSpace (I := I) (M := M) v
  set e : Bundle.Trivialization E (Bundle.TotalSpace.proj (E := TangentSpace I (M := M))) :=
    trivializationAt E (TangentSpace I) x₀ with he_def
  have h_maps : Set.MapsTo (fun b : M => (⟨b, v⟩ : TangentBundle I M)) e.baseSet e.source :=
    fun b hb => e.mem_source.mpr hb
  have h_iff := e.contMDiffOn_iff (IB := I) (IM := I) (n := ∞)
    (f := fun b : M => (⟨b, v⟩ : TangentBundle I M)) h_maps
  have h_snd : ContMDiffOn I 𝓘(ℝ, E) ∞
      (fun b => (e ⟨b, v⟩).2) e.baseSet := (h_iff.mp h_const.contMDiffOn).2
  apply h_snd.congr
  intro b hb
  exact Bundle.Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) e hb v

/-! ### Layer 4 — main result `contMDiffOn_continuousLinearMapAtFlat` -/

/-- **Forward chart mfderiv smoothness as model-fiber-valued CLM**
(infrastructure / Mathlib upstream PR candidate).

The chart's mfderiv as a function of basepoint is smooth `M → (E →L E)`,
on chart base set. This is the natural mathematical statement
("a smooth chart's derivative is a smooth function of basepoint")
and the **fundamental** smoothness fact for tangent-bundle infrastructure.

The backward-direction (chart-inverse-mfderiv) corollary
`contMDiffOn_mfderivWithinFlat` follows via `inverse` composition + the
chain identity `mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm`.

**Sorry status**: PRE-PAPER. Closure path:
* `Trivialization.contMDiffOn` gives smoothness of `e : TotalSpace → M × E`
  on its source.
* For each `v : E`, the constant section `b ↦ ⟨b, v⟩` (treating v as
  fiber via `TangentSpace I b = E` def-eq) is smooth bundle-section.
* Apply trivialization to the constant section: `b ↦ e ⟨b, v⟩`. By bundle
  iso smoothness, this is smooth.
* The second component is `b ↦ (e ⟨b, v⟩).2 = e.continuousLinearMapAt R b v`,
  smooth as `M → E` for fixed v.
* Use `[FiniteDimensional ℝ E]` to lift pointwise-in-v smoothness to
  CLM-valued smoothness via basis decomposition. -/
theorem contMDiffOn_continuousLinearMapAtFlat
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (x₀ : M) :
    ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E) ∞
      (continuousLinearMapAtFlat (I := I) (M := M) x₀)
      (trivializationAt E (TangentSpace I) x₀).baseSet := by
  -- **Closed via Layer 2 + Layer 3**.
  -- Pick a basis of E. Each component `b ↦ cLMA R b (basis i) : M → E` is
  -- smooth (Layer 3). Lift to CLM-valued smoothness via Layer 2.
  set basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E :=
    Module.finBasis ℝ E with h_basis
  apply contMDiffOn_clm_of_components
    (continuousLinearMapAtFlat (I := I) (M := M) x₀)
    basis _
  intro i
  -- Component smoothness: `b ↦ continuousLinearMapAtFlat x₀ b (basis i)`
  -- = `b ↦ (trivAt _ _ x₀).cLMA R b (basis i)` (def-eq)
  exact contMDiffOn_continuousLinearMapAt_apply x₀ (basis i)

/-- **Backward chart-inverse-mfderiv smoothness on chart target**
(corollary of `contMDiffOn_continuousLinearMapAtFlat` via inverse).

Derived from forward chart smoothness via:
* `inverse : (E →L E) → (E →L E)` smooth at invertible CLMs (CompleteSpace E)
* Chain identity: `mfderivWithin (.symm) (range I) e₀ = inverse(mfderiv (extChartAt I x) ((.symm) e₀))`
* `(extChartAt I x).symm : E → M` smooth on chart target -/
theorem contMDiffOn_mfderivWithinFlat
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (x : M) :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] E) ∞
      (mfderivWithinFlat (I := I) (M := M) x) (extChartAt I x).target := by
  -- Step 1: forward chart smooth on chart source (baseSet of trivAt x).
  have h_fwd : ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E) ∞
      (continuousLinearMapAtFlat (I := I) (M := M) x)
      (trivializationAt E (TangentSpace I) x).baseSet :=
    contMDiffOn_continuousLinearMapAtFlat x
  -- Step 2: chart inverse smooth on chart target into chart source.
  have h_symm : ContMDiffOn 𝓘(ℝ, E) I ∞
      (extChartAt I x).symm (extChartAt I x).target :=
    contMDiffOn_extChartAt_symm x
  have h_maps_to : Set.MapsTo (extChartAt I x).symm
      (extChartAt I x).target
      (trivializationAt E (TangentSpace I) x).baseSet := by
    intro e₀ he₀
    -- (.symm) e₀ ∈ chart source ⊆ baseSet
    have h_src : (extChartAt I x).symm e₀ ∈ (extChartAt I x).source :=
      PartialEquiv.map_target _ he₀
    rwa [extChartAt_source] at h_src
  -- Step 3: composition gives smoothness of `e₀ ↦ continuousLinearMapAtFlat x ((.symm) e₀)`
  -- on chart target.
  have h_compose : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] E) ∞
      (fun e₀ => continuousLinearMapAtFlat (I := I) (M := M) x
        ((extChartAt I x).symm e₀))
      (extChartAt I x).target :=
    h_fwd.comp h_symm h_maps_to
  -- Step 4: each value `continuousLinearMapAtFlat x ((.symm) e₀)` is invertible
  -- on chart target (forward chart is local diffeomorphism).
  have h_invertible : ∀ e₀ ∈ (extChartAt I x).target,
      (continuousLinearMapAtFlat (I := I) (M := M) x
        ((extChartAt I x).symm e₀)).IsInvertible := by
    intro e₀ he₀
    have h_src : (extChartAt I x).symm e₀ ∈ (extChartAt I x).source :=
      PartialEquiv.map_target _ he₀
    -- continuousLinearMapAtFlat x y = mfderiv (extChartAt I x) y for y in chart source
    have h_chart_src : (extChartAt I x).symm e₀ ∈ (chartAt H x).source := by
      rwa [extChartAt_source] at h_src
    -- Convert via TangentBundle.continuousLinearMapAt_trivializationAt
    show ((trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ
      ((extChartAt I x).symm e₀)).IsInvertible
    rw [TangentBundle.continuousLinearMapAt_trivializationAt h_chart_src]
    exact isInvertible_mfderiv_extChartAt h_src
  -- Step 5: compose with `ContinuousLinearMap.inverse` (smooth at invertible).
  have h_inverse_comp : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] E) ∞
      (fun e₀ => ContinuousLinearMap.inverse
        (continuousLinearMapAtFlat (I := I) (M := M) x
          ((extChartAt I x).symm e₀)))
      (extChartAt I x).target := by
    intro e₀ he₀
    have h_inv_at : (continuousLinearMapAtFlat (I := I) (M := M) x
        ((extChartAt I x).symm e₀)).IsInvertible :=
      h_invertible e₀ he₀
    have h_cd : ContDiffAt ℝ ∞ ContinuousLinearMap.inverse
        (continuousLinearMapAtFlat x ((extChartAt I x).symm e₀)) :=
      ContinuousLinearMap.IsInvertible.contDiffAt_map_inverse h_inv_at
    exact h_cd.contMDiffAt.contMDiffWithinAt.comp e₀ (h_compose e₀ he₀) (Set.mapsTo_univ _ _)
  -- Step 6: identify `mfderivWithinFlat x e₀` with the inverse via chain identity.
  apply h_inverse_comp.congr
  intro e₀ he₀
  -- Goal: `mfderivWithinFlat x e₀ = inverse(continuousLinearMapAtFlat x ((.symm) e₀))`
  show mfderivWithin 𝓘(ℝ, E) I (extChartAt I x).symm (Set.range I) e₀
    = ContinuousLinearMap.inverse
        (continuousLinearMapAtFlat (I := I) (M := M) x ((extChartAt I x).symm e₀))
  have h_chart_src : (extChartAt I x).symm e₀ ∈ (chartAt H x).source := by
    rw [← extChartAt_source (I := I)]
    exact PartialEquiv.map_target _ he₀
  -- Convert continuousLinearMapAtFlat to mfderiv (forward chart) via Mathlib lemma.
  have h_eq_mfderiv :
      continuousLinearMapAtFlat (I := I) (M := M) x ((extChartAt I x).symm e₀)
        = mfderiv I 𝓘(ℝ, E) (extChartAt I x) ((extChartAt I x).symm e₀) := by
    show (trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ
        ((extChartAt I x).symm e₀)
      = mfderiv I 𝓘(ℝ, E) (extChartAt I x) ((extChartAt I x).symm e₀)
    exact TangentBundle.continuousLinearMapAt_trivializationAt h_chart_src
  rw [h_eq_mfderiv]
  -- Chain identities give: inverse(forward-mfderiv) = backward-mfderivWithin
  have h_chain := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm (I := I) (x := x) he₀
  have h_chain' := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt (I := I) (x := x) he₀
  exact (ContinuousLinearMap.inverse_eq h_chain h_chain').symm

/-! ## Helper 1 — single-point version (corollary of `contMDiffOn_mfderivWithinFlat`)

Bridge from on-set smoothness (`contMDiffOn_mfderivWithinFlat`, on chart
target) to single-point `MDifferentiableWithinAt` at the basepoint within
`range I`. Used by the main theorem `symmLFlat_mdifferentiableAt`. -/

/-- `MDifferentiableWithinAt` form of `mfderivWithinFlat x` at the
basepoint `extChartAt I x x` within `Set.range I`. -/
private theorem mfderivWithinFlat_mdifferentiableWithinAt
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (x : M) :
    MDifferentiableWithinAt 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] E)
      (mfderivWithinFlat (I := I) (M := M) x) (Set.range I) (extChartAt I x x) := by
  -- Derived from on-set form `contMDiffOn_mfderivWithinFlat`:
  -- (1) `ContMDiffOn ... mfderivWithinFlat target` → `MDifferentiableOn ... target`
  -- (2) Apply at basepoint `extChartAt I x x ∈ target` → `MDifferentiableWithinAt ... target`
  -- (3) Convert within-target → within-range-I via `mono_of_mem_nhdsWithin` (since
  --     target ⊆ range I, `range I ∈ 𝓝[target] (extChartAt I x x)` trivially).
  have h_top_ne_zero : (∞ : WithTop ℕ∞) ≠ 0 := by decide
  have h_on : MDifferentiableOn 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] E)
      (mfderivWithinFlat (I := I) (M := M) x) (extChartAt I x).target :=
    (contMDiffOn_mfderivWithinFlat x).mdifferentiableOn h_top_ne_zero
  have h_at_target : MDifferentiableWithinAt 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] E)
      (mfderivWithinFlat x) (extChartAt I x).target (extChartAt I x x) :=
    h_on _ (mem_extChartAt_target x)
  exact h_at_target.mono_of_mem_nhdsWithin (extChartAt_target_mem_nhdsWithin x)

/-! ## Helper 2 — eventually-equal rewrite (closed)

Lifts `TangentBundle.symmL_trivializationAt` (Mathlib pointwise identity
on chart source) to filter-level eventually-equal, expressed against
`symmLFlat` and `mfderivWithinFlat`. -/

set_option backward.isDefEq.respectTransparency false in
/-- For `y` in chart-source nbhd of `x`, `symmLFlat x y` equals
`mfderivWithinFlat x (extChartAt I x y)`. Lifted to `=ᶠ[𝓝 x]`. -/
private theorem symmLFlat_eventuallyEq_mfderivWithinFlat
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (x : M) :
    (fun y : M => symmLFlat (I := I) (M := M) x y)
      =ᶠ[𝓝 x]
      (fun y : M => mfderivWithinFlat (I := I) (M := M) x (extChartAt I x y)) := by
  have h_chart_nhds : (chartAt H x).source ∈ 𝓝 x :=
    (chartAt H x).open_source.mem_nhds (mem_chart_source H x)
  filter_upwards [h_chart_nhds] with y hy
  show (trivializationAt E (TangentSpace I) x).symmL ℝ y =
    mfderivWithin 𝓘(ℝ, E) I (extChartAt I x).symm (Set.range I) (extChartAt I x y)
  exact TangentBundle.symmL_trivializationAt hy

/-! ## Main theorem — clean flat-type API, no cast in signature -/

/-- **Smoothness of `symmLFlat`** — the framework's flat-codomain inverse
trivialization is `MDifferentiableAt` at `x` as a map `M → (E →L[ℝ] E)`.

No `cast`, no `h_TS_E_eq` parameter in user-facing signature. The
`TangentSpace I y = E` def-eq is hidden inside `symmLFlat`'s definition.

Proof: composition of `extChartAt I x` (smooth, `mdifferentiableAt_extChartAt`)
with `mfderivWithinFlat x` (smooth, Helper 1), bridged to `symmLFlat` via
Helper 2's eventually-equal identity. -/
theorem symmLFlat_mdifferentiableAt
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (x : M) :
    MDifferentiableAt I 𝓘(ℝ, E →L[ℝ] E)
      (fun y : M => symmLFlat (I := I) (M := M) x y) x := by
  have h_chart : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I x) x :=
    mdifferentiableAt_extChartAt (mem_chart_source H x)
  have h_inv := mfderivWithinFlat_mdifferentiableWithinAt (I := I) (M := M) x
  -- Compose: `mfderivWithinFlat x ∘ extChartAt I x` is at-form smooth on M.
  -- The chart `extChartAt I x` maps a neighborhood of `x` into `range I` (no
  -- boundary assumption needed): on `(chartAt H x).source`, `extChartAt I x y
  -- = I (chartAt H x y) ∈ range I`.
  have h_chart_within : MDifferentiableWithinAt I 𝓘(ℝ, E) (extChartAt I x) Set.univ x :=
    h_chart.mdifferentiableWithinAt
  have h_preimage : (extChartAt I x) ⁻¹' Set.range I ∈ 𝓝[Set.univ] x := by
    rw [nhdsWithin_univ]
    refine Filter.mem_of_superset
      ((chartAt H x).open_source.mem_nhds (mem_chart_source H x)) ?_
    intro y _hy
    rw [Set.mem_preimage, extChartAt_coe]
    exact Set.mem_range_self _
  have h_within : MDifferentiableWithinAt I 𝓘(ℝ, E →L[ℝ] E)
      (fun y : M => mfderivWithinFlat (I := I) (M := M) x (extChartAt I x y))
      Set.univ x :=
    h_inv.comp_of_preimage_mem_nhdsWithin _ h_chart_within h_preimage
  have h_comp : MDifferentiableAt I 𝓘(ℝ, E →L[ℝ] E)
      (fun y : M => mfderivWithinFlat (I := I) (M := M) x (extChartAt I x y)) x :=
    mdifferentiableWithinAt_univ.mp h_within
  exact h_comp.congr_of_eventuallyEq
    (symmLFlat_eventuallyEq_mfderivWithinFlat (I := I) (M := M) x)

end TangentBundle
