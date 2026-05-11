import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorField.Pullback
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-!
# Tangent bundle smoothness API

Smoothness of tangent vector fields and chart-frame derivatives.

This file is the single verifiable-object presentation of the framework's
tangent-bundle smoothness layer:

1. Chart-coherence typeclass `IsLocallyConstantChartedSpace`.
2. Smoothness predicate `TangentSmoothAt` and its closure under the
   $C^\infty(M)$-module operations, plus the `tangent_smooth` tactic.
3. Chart-frame inverse/forward trivialization in flat-codomain form
   (`symmLFlat`, `continuousLinearMapAtFlat`) and their smoothness.
4. Bundled smooth vector fields `SmoothVectorField`.
5. Chart-frame `mfderiv` smoothness theorems.

## Main definitions

* `IsLocallyConstantChartedSpace H M` — typeclass: `chartAt H` is locally
  constant. Required for parametric chart-mfderiv smoothness.
* `TangentSmoothAt V x` — smoothness of a tangent section at a point.
* `TangentBundle.symmLFlat x y : E →L[ℝ] E` — flat-typed chart-inverse.
* `TangentBundle.continuousLinearMapAtFlat x y : E →L[ℝ] E` — flat-typed
  chart-forward.
* `Riemannian.SmoothVectorField I M` — bundled smooth tangent section.

## Main results

* `TangentSmoothAt.{zero, add, neg, sub, smul}` — algebra closure.
* `tangent_smooth` tactic — discharges goals of the form
  `TangentSmoothAt V x` for `V` built from smooth-section algebra.
* `TangentBundle.symmLFlat_mdifferentiableAt`,
  `TangentBundle.continuousLinearMapAtFlat_contMDiffAt` — flat chart
  derivatives are smooth in the basepoint.
* `mfderiv_const_dir_smoothAt`, `mfderiv_smoothDir_smoothAt` — for a
  smooth scalar $f$ and (constant or smoothly-varying) direction $V$,
  $y \mapsto \mathrm{d}f_y(V(y))$ is smooth.

Reference: Lee, *Smooth Manifolds*, Ch. 8 (smooth vector fields) and
Ch. 11 (chart-derivative smoothness).
-/

open scoped ContDiff Manifold Topology

/-! ## Chart selection coherence

The `IsManifold I ∞ M` typeclass requires only smoothness of chart
*transitions*, not local constancy of the chart-selection function
`chartAt H : M → PartialHomeomorph M H`. Without local constancy, the
parametric chart-derivative `b ↦ (trivAt b₀).cLMA R b` is not
generally smooth.

`IsLocallyConstantChartedSpace` adds the missing structure: in every
neighborhood of every basepoint, `chartAt H` is constant. Standard
Mathlib examples (Euclidean spaces, single-chart-per-region atlases)
satisfy this.
-/

class IsLocallyConstantChartedSpace
    (H : Type*) [TopologicalSpace H]
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] : Prop where
  /-- `chartAt H b = chartAt H b₀` eventually as `b → b₀`. -/
  chartAt_eventually_eq : ∀ b₀ : M, ∀ᶠ b in 𝓝 b₀, chartAt H b = chartAt H b₀

theorem chartAt_eventually_eq_of_locallyConstant
    {H : Type*} [TopologicalSpace H]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsLocallyConstantChartedSpace H M] (b₀ : M) :
    ∀ᶠ b in 𝓝 b₀, chartAt H b = chartAt H b₀ :=
  IsLocallyConstantChartedSpace.chartAt_eventually_eq b₀

/-- `H` over itself satisfies the typeclass (charts are constantly
`PartialHomeomorph.refl H`). -/
instance instIsLocallyConstantChartedSpace_self
    (H : Type*) [TopologicalSpace H] :
    IsLocallyConstantChartedSpace H H where
  chartAt_eventually_eq _ := Filter.Eventually.of_forall (fun _ => rfl)

/-! ## Tangent vector field smoothness predicate

`TangentSmoothAt V x` is the framework's canonical smoothness predicate
for tangent sections, equivalent to the bundle-form
`MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (fun y ↦ ⟨y, V y⟩) x` but
opaque to elaborator unfolding for tactic-search performance.
-/

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The tangent section `y ↦ ⟨y, V y⟩` is `MDifferentiableAt` at `x`
as a map `M → TangentBundle I M`. -/
def TangentSmoothAt (V : (y : M) → TangentSpace I y) (x : M) : Prop :=
  MDifferentiableAt I (I.prod 𝓘(ℝ, E))
    (fun y => (⟨y, V y⟩ : TangentBundle I M)) x

namespace TangentSmoothAt

theorem mk {V : (y : M) → TangentSpace I y} {x : M}
    (h : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, V y⟩ : TangentBundle I M)) x) :
    TangentSmoothAt V x := h

theorem toBundleSection {V : (y : M) → TangentSpace I y} {x : M}
    (h : TangentSmoothAt V x) :
    MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, V y⟩ : TangentBundle I M)) x := h

/-- Chart-coordinate form: `y ↦ (trivAt x ⟨y, V y⟩).2 : M → E` is smooth. -/
theorem coordSmoothAt {V : (y : M) → TangentSpace I y} {x : M}
    (hV : TangentSmoothAt V x) :
    MDifferentiableAt I 𝓘(ℝ, E)
      (fun y => ((trivializationAt E (TangentSpace I) x) ⟨y, V y⟩).2) x := by
  have h := hV.toBundleSection
  rw [mdifferentiableAt_totalSpace] at h
  exact h.2

theorem iff_coord {V : (y : M) → TangentSpace I y} {x : M} :
    TangentSmoothAt V x ↔
      MDifferentiableAt I 𝓘(ℝ, E)
        (fun y => ((trivializationAt E (TangentSpace I) x) ⟨y, V y⟩).2) x := by
  unfold TangentSmoothAt
  rw [mdifferentiableAt_totalSpace]
  exact ⟨And.right, fun h => ⟨mdifferentiableAt_id, h⟩⟩

/-- The zero vector field is smooth. -/
theorem zero (x : M) : TangentSmoothAt (fun y : M => (0 : TangentSpace I y)) x := by
  rw [TangentSmoothAt.iff_coord]
  set e := trivializationAt E (TangentSpace I) x
  apply (mdifferentiableAt_const (c := (0 : E))).congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds
    (FiberBundle.mem_baseSet_trivializationAt' x)] with y hy
  show (e ⟨y, (0 : TangentSpace I y)⟩).2 = (0 : E)
  rw [← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) e hy]
  exact map_zero _

theorem add {Y Z : (y : M) → TangentSpace I y} {x : M}
    (hY : TangentSmoothAt Y x) (hZ : TangentSmoothAt Z x) :
    TangentSmoothAt (Y + Z) x := by
  rw [TangentSmoothAt.iff_coord]
  set e := trivializationAt E (TangentSpace I) x
  have hY' := hY.coordSmoothAt
  have hZ' := hZ.coordSmoothAt
  apply (hY'.add hZ').congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds
    (FiberBundle.mem_baseSet_trivializationAt' x)] with y hy
  show (e ⟨y, (Y + Z) y⟩).2 = (e ⟨y, Y y⟩).2 + (e ⟨y, Z y⟩).2
  rw [← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) e hy,
      ← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) e hy,
      ← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) e hy]
  show (e.continuousLinearMapAt ℝ y) ((Y + Z) y)
      = (e.continuousLinearMapAt ℝ y) (Y y) + (e.continuousLinearMapAt ℝ y) (Z y)
  show (e.continuousLinearMapAt ℝ y) (Y y + Z y)
      = (e.continuousLinearMapAt ℝ y) (Y y) + (e.continuousLinearMapAt ℝ y) (Z y)
  exact ContinuousLinearMap.map_add _ _ _

theorem neg {V : (y : M) → TangentSpace I y} {x : M}
    (hV : TangentSmoothAt V x) :
    TangentSmoothAt (-V) x := by
  rw [TangentSmoothAt.iff_coord]
  set e := trivializationAt E (TangentSpace I) x
  have hV' := hV.coordSmoothAt
  apply hV'.neg.congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds
    (FiberBundle.mem_baseSet_trivializationAt' x)] with y hy
  show (e ⟨y, (-V) y⟩).2 = -(e ⟨y, V y⟩).2
  rw [← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) e hy,
      ← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) e hy]
  show (e.continuousLinearMapAt ℝ y) ((-V) y) = -(e.continuousLinearMapAt ℝ y) (V y)
  show (e.continuousLinearMapAt ℝ y) (-V y) = -(e.continuousLinearMapAt ℝ y) (V y)
  exact ContinuousLinearMap.map_neg _ _

theorem sub {Y Z : (y : M) → TangentSpace I y} {x : M}
    (hY : TangentSmoothAt Y x) (hZ : TangentSmoothAt Z x) :
    TangentSmoothAt (Y - Z) x := by
  have h_eq : (Y - Z : (y : M) → TangentSpace I y) = Y + (-Z) := by
    funext y
    show Y y - Z y = Y y + -Z y
    exact sub_eq_add_neg _ _
  rw [h_eq]
  exact hY.add hZ.neg

theorem smul {f : M → ℝ} {V : (y : M) → TangentSpace I y} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x) (hV : TangentSmoothAt V x) :
    TangentSmoothAt (fun y => f y • V y) x := by
  rw [TangentSmoothAt.iff_coord]
  set e := trivializationAt E (TangentSpace I) x
  have hV' := hV.coordSmoothAt
  apply (hf.smul hV').congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds
    (FiberBundle.mem_baseSet_trivializationAt' x)] with y hy
  show (e ⟨y, f y • V y⟩).2 = f y • (e ⟨y, V y⟩).2
  rw [← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) e hy,
      ← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) e hy]
  show (e.continuousLinearMapAt ℝ y) (f y • V y)
      = f y • (e.continuousLinearMapAt ℝ y) (V y)
  exact ContinuousLinearMap.map_smul _ _ _

end TangentSmoothAt

/-- Closes any `TangentSmoothAt V x` goal where `V` is built from
hypotheses by zero / add / sub / neg / smul. -/
syntax "tangent_smooth" : tactic

macro_rules
  | `(tactic| tangent_smooth) => `(tactic|
      repeat first
        | assumption
        | exact TangentSmoothAt.zero _
        | apply TangentSmoothAt.add
        | apply TangentSmoothAt.sub
        | apply TangentSmoothAt.neg
        | apply TangentSmoothAt.smul)

end Riemannian

/-! ## Chart-frame infrastructure

Flat-codomain (type-erased) chart-derivative wrappers, plus the
framework's parametric chart-mfderiv smoothness theorems.

The flat-typed wrappers retype the dependent codomain
`E →L[ℝ] TangentSpace I y` (which Mathlib uses) to `E →L[ℝ] E` via the
def-eq `TangentSpace I y = E`, hiding the cast. Smoothness statements
on `M → (E →L[ℝ] E)` are the user-facing API; clients never see the
def-eq bridge.

Most helpers are `private` (Layer 1-4 framework infrastructure for
constant-section smoothness, finite-dim CLM lift, and chart-inverse
smoothness via `inverse` composition). The four public theorems are
`continuousLinearMapAtFlat_contMDiffAt`, `symmLFlat_mdifferentiableAt`,
`contMDiff_constSection_TangentSpace` (used by `SmoothVectorField.const`).
-/

namespace TangentBundle

set_option backward.isDefEq.respectTransparency false in
/-- Flat-codomain inverse trivialization: `(trivAt x).symmL ℝ y` retyped
as `E →L[ℝ] E` via `TangentSpace I y = E`. -/
noncomputable def symmLFlat
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (x y : M) : E →L[ℝ] E :=
  (trivializationAt E (TangentSpace I) x).symmL ℝ y

set_option backward.isDefEq.respectTransparency false in
/-- Flat-codomain forward chart-mfderiv:
`(trivAt x₀).continuousLinearMapAt ℝ y` retyped as `E →L[ℝ] E`. -/
noncomputable def continuousLinearMapAtFlat
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (x₀ y : M) : E →L[ℝ] E :=
  (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ y

set_option backward.isDefEq.respectTransparency false in
/-- Flat-codomain `mfderivWithin (range I) (extChartAt I x).symm e₀`. -/
private noncomputable def mfderivWithinFlat
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (x : M) (e₀ : E) : E →L[ℝ] E :=
  mfderivWithin 𝓘(ℝ, E) I (extChartAt I x).symm (Set.range I) e₀

/-! ### Layer 1 — constant-section smoothness for the tangent bundle -/

/-- Forward chart-mfderiv as a CLM-valued function of basepoint, smooth
at `b₀`. With `IsLocallyConstantChartedSpace`, locally constant on
`chartAt H b₀ = chartAt H b₀`'s neighborhood and equals the identity
CLM via `coordChange_self`. -/
theorem continuousLinearMapAtFlat_contMDiffAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [IsLocallyConstantChartedSpace H M]
    (b₀ : M) :
    ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E) ∞
      (continuousLinearMapAtFlat (I := I) (M := M) b₀) b₀ := by
  refine (contMDiffAt_const (c := ContinuousLinearMap.id ℝ E)).congr_of_eventuallyEq ?_
  have h_chart_eq : ∀ᶠ b in 𝓝 b₀, chartAt H b = chartAt H b₀ :=
    chartAt_eventually_eq_of_locallyConstant b₀
  have h_chart_src : (chartAt H b₀).source ∈ 𝓝 b₀ :=
    (chartAt H b₀).open_source.mem_nhds (mem_chart_source H b₀)
  filter_upwards [h_chart_eq, h_chart_src] with b hb_eq hb_src
  show continuousLinearMapAtFlat (I := I) (M := M) b₀ b = ContinuousLinearMap.id ℝ E
  show (trivializationAt E (TangentSpace I) b₀).continuousLinearMapAt ℝ b
    = ContinuousLinearMap.id ℝ E
  rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core hb_src]
  have h_achart_eq : achart H b = achart H b₀ := Subtype.ext hb_eq
  rw [h_achart_eq]
  ext v
  exact (tangentBundleCore I M).coordChange_self (achart H b₀) b
    (by simpa [tangentBundleCore_baseSet] using hb_src) v

private theorem mfderiv_extChartAt_apply_smoothAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [IsLocallyConstantChartedSpace H M]
    (b₀ : M) (v : E) :
    ContMDiffAt I 𝓘(ℝ, E) ∞
      (fun b : M => mfderiv I 𝓘(ℝ, E) (extChartAt I b₀) b v) b₀ := by
  have h_cLMA := continuousLinearMapAtFlat_contMDiffAt (I := I) (M := M) b₀
  have h_apply : ContMDiffAt I 𝓘(ℝ, E) ∞
      (fun b : M => continuousLinearMapAtFlat (I := I) (M := M) b₀ b v) b₀ :=
    h_cLMA.clm_apply contMDiffAt_const
  have h_base : (chartAt H b₀).source ∈ 𝓝 b₀ :=
    (chartAt H b₀).open_source.mem_nhds (mem_chart_source H b₀)
  have h_eq : (fun b : M => continuousLinearMapAtFlat (I := I) (M := M) b₀ b v)
      =ᶠ[𝓝 b₀] (fun b : M => mfderiv I 𝓘(ℝ, E) (extChartAt I b₀) b v) := by
    filter_upwards [h_base] with b hb
    show (trivializationAt E (TangentSpace I) b₀).continuousLinearMapAt ℝ b v
      = mfderiv I 𝓘(ℝ, E) (extChartAt I b₀) b v
    rw [TangentBundle.continuousLinearMapAt_trivializationAt hb]
    rfl
  exact h_apply.congr_of_eventuallyEq h_eq.symm

/-- Constant-vector tangent section is smooth. For `v : E`, the section
`b ↦ ⟨b, v⟩` (with `v` viewed as fiber via `TangentSpace I b = E`) is
$C^\infty$. Used by `SmoothVectorField.const`. -/
theorem contMDiff_constSection_TangentSpace
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [IsLocallyConstantChartedSpace H M]
    (v : E) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, v⟩ : TangentBundle I M)) := by
  intro b₀
  set e := trivializationAt E (TangentSpace I) b₀ with he_def
  have h_he : (Bundle.TotalSpace.mk b₀ v : TangentBundle I M) ∈ e.source := by
    rw [Bundle.Trivialization.mem_source]
    exact FiberBundle.mem_baseSet_trivializationAt' (F := E) b₀
  refine (Bundle.Trivialization.contMDiffAt_iff (IM := I) (IB := I) (e := e)
    (f := fun b : M => (Bundle.TotalSpace.mk b v : TangentBundle I M)) (n := ∞) h_he).mpr ?_
  refine ⟨contMDiffAt_id, ?_⟩
  have h_base : e.baseSet ∈ 𝓝 b₀ :=
    e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' b₀)
  have h_eqOn : (fun b : M => (e ⟨b, v⟩).2)
      =ᶠ[𝓝 b₀] (fun b : M => mfderiv I 𝓘(ℝ, E) (extChartAt I b₀) b v) := by
    filter_upwards [h_base] with b hb
    have hb' : b ∈ (chartAt H b₀).source := by
      rwa [TangentBundle.trivializationAt_baseSet] at hb
    show (e ⟨b, v⟩).2 = mfderiv I 𝓘(ℝ, E) (extChartAt I b₀) b v
    rw [(Bundle.Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) e hb v).symm,
        TangentBundle.continuousLinearMapAt_trivializationAt hb']
    rfl
  exact (mfderiv_extChartAt_apply_smoothAt (I := I) (M := M) b₀ v).congr_of_eventuallyEq
    h_eqOn

/-! ### Layer 2 — finite-dim CLM lift -/

private theorem _root_.ContMDiffOn.add_normed
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

private theorem _root_.ContMDiffOn.finset_sum_normed
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

/-- Componentwise smoothness `(y ↦ T y bᵢ) : M → F₂` lifts to CLM-valued
smoothness `T : M → (F₁ →L[𝕜] F₂)` via basis decomposition. -/
private theorem contMDiffOn_clm_of_components
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
  have decomp : T = fun y =>
      ∑ i, (basis.coord i).toContinuousLinearMap.smulRight (T y (basis i)) := by
    funext y
    ext v
    rw [ContinuousLinearMap.sum_apply]
    have hv : v = ∑ i, basis.repr v i • basis i := by simp
    conv_lhs => rw [hv]
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    simp [ContinuousLinearMap.smulRight_apply,
      LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply,
      (T y).map_smul]
  rw [decomp]
  apply ContMDiffOn.finset_sum_normed
  intro i _
  have h_smulRight : ContMDiff 𝓘(𝕜, F₂) 𝓘(𝕜, F₁ →L[𝕜] F₂) n
      (fun w : F₂ => (basis.coord i).toContinuousLinearMap.smulRight w) := by
    have h_eq : (fun w : F₂ => (basis.coord i).toContinuousLinearMap.smulRight w)
        = ContinuousLinearMap.smulRightL 𝕜 F₁ F₂ (basis.coord i).toContinuousLinearMap := by
      funext w; rfl
    rw [h_eq]
    exact (ContinuousLinearMap.smulRightL 𝕜 F₁ F₂
      (basis.coord i).toContinuousLinearMap).contMDiff
  exact h_smulRight.comp_contMDiffOn (h_components i)

/-! ### Layer 3-4 — chart-mfderiv smoothness on `baseSet` -/

private theorem contMDiffOn_continuousLinearMapAt_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [IsLocallyConstantChartedSpace H M]
    (x₀ : M) (v : E) :
    ContMDiffOn I 𝓘(ℝ, E) ∞
      (fun b : M => (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ b v)
      (trivializationAt E (TangentSpace I) x₀).baseSet := by
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

private theorem contMDiffOn_continuousLinearMapAtFlat
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [IsLocallyConstantChartedSpace H M]
    (x₀ : M) :
    ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E) ∞
      (continuousLinearMapAtFlat (I := I) (M := M) x₀)
      (trivializationAt E (TangentSpace I) x₀).baseSet := by
  set basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E :=
    Module.finBasis ℝ E with h_basis
  apply contMDiffOn_clm_of_components
    (continuousLinearMapAtFlat (I := I) (M := M) x₀)
    basis _
  intro i
  exact contMDiffOn_continuousLinearMapAt_apply x₀ (basis i)

private theorem contMDiffOn_mfderivWithinFlat
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [IsLocallyConstantChartedSpace H M]
    (x : M) :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] E) ∞
      (mfderivWithinFlat (I := I) (M := M) x) (extChartAt I x).target := by
  have h_fwd : ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E) ∞
      (continuousLinearMapAtFlat (I := I) (M := M) x)
      (trivializationAt E (TangentSpace I) x).baseSet :=
    contMDiffOn_continuousLinearMapAtFlat x
  have h_symm : ContMDiffOn 𝓘(ℝ, E) I ∞
      (extChartAt I x).symm (extChartAt I x).target :=
    contMDiffOn_extChartAt_symm x
  have h_maps_to : Set.MapsTo (extChartAt I x).symm
      (extChartAt I x).target
      (trivializationAt E (TangentSpace I) x).baseSet := by
    intro e₀ he₀
    have h_src : (extChartAt I x).symm e₀ ∈ (extChartAt I x).source :=
      PartialEquiv.map_target _ he₀
    rwa [extChartAt_source] at h_src
  have h_compose : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] E) ∞
      (fun e₀ => continuousLinearMapAtFlat (I := I) (M := M) x
        ((extChartAt I x).symm e₀))
      (extChartAt I x).target :=
    h_fwd.comp h_symm h_maps_to
  have h_invertible : ∀ e₀ ∈ (extChartAt I x).target,
      (continuousLinearMapAtFlat (I := I) (M := M) x
        ((extChartAt I x).symm e₀)).IsInvertible := by
    intro e₀ he₀
    have h_src : (extChartAt I x).symm e₀ ∈ (extChartAt I x).source :=
      PartialEquiv.map_target _ he₀
    have h_chart_src : (extChartAt I x).symm e₀ ∈ (chartAt H x).source := by
      rwa [extChartAt_source] at h_src
    show ((trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ
      ((extChartAt I x).symm e₀)).IsInvertible
    rw [TangentBundle.continuousLinearMapAt_trivializationAt h_chart_src]
    exact isInvertible_mfderiv_extChartAt h_src
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
  apply h_inverse_comp.congr
  intro e₀ he₀
  show mfderivWithin 𝓘(ℝ, E) I (extChartAt I x).symm (Set.range I) e₀
    = ContinuousLinearMap.inverse
        (continuousLinearMapAtFlat (I := I) (M := M) x ((extChartAt I x).symm e₀))
  have h_chart_src : (extChartAt I x).symm e₀ ∈ (chartAt H x).source := by
    rw [← extChartAt_source (I := I)]
    exact PartialEquiv.map_target _ he₀
  have h_eq_mfderiv :
      continuousLinearMapAtFlat (I := I) (M := M) x ((extChartAt I x).symm e₀)
        = mfderiv I 𝓘(ℝ, E) (extChartAt I x) ((extChartAt I x).symm e₀) := by
    show (trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ
        ((extChartAt I x).symm e₀)
      = mfderiv I 𝓘(ℝ, E) (extChartAt I x) ((extChartAt I x).symm e₀)
    exact TangentBundle.continuousLinearMapAt_trivializationAt h_chart_src
  rw [h_eq_mfderiv]
  have h_chain := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm (I := I) (x := x) he₀
  have h_chain' := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt (I := I) (x := x) he₀
  exact (ContinuousLinearMap.inverse_eq h_chain h_chain').symm

private theorem mfderivWithinFlat_mdifferentiableWithinAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [IsLocallyConstantChartedSpace H M]
    (x : M) :
    MDifferentiableWithinAt 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] E)
      (mfderivWithinFlat (I := I) (M := M) x) (Set.range I) (extChartAt I x x) := by
  have h_top_ne_zero : (∞ : WithTop ℕ∞) ≠ 0 := by decide
  have h_on : MDifferentiableOn 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] E)
      (mfderivWithinFlat (I := I) (M := M) x) (extChartAt I x).target :=
    (contMDiffOn_mfderivWithinFlat x).mdifferentiableOn h_top_ne_zero
  have h_at_target : MDifferentiableWithinAt 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] E)
      (mfderivWithinFlat x) (extChartAt I x).target (extChartAt I x x) :=
    h_on _ (mem_extChartAt_target x)
  exact h_at_target.mono_of_mem_nhdsWithin (extChartAt_target_mem_nhdsWithin x)

set_option backward.isDefEq.respectTransparency false in
private theorem symmLFlat_eventuallyEq_mfderivWithinFlat
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
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

/-- Smoothness of `symmLFlat` as a map `M → (E →L[ℝ] E)`. The
`TangentSpace I y = E` def-eq is hidden inside the definition. -/
theorem symmLFlat_mdifferentiableAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [IsLocallyConstantChartedSpace H M]
    (x : M) :
    MDifferentiableAt I 𝓘(ℝ, E →L[ℝ] E)
      (fun y : M => symmLFlat (I := I) (M := M) x y) x := by
  have h_chart : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I x) x :=
    mdifferentiableAt_extChartAt (mem_chart_source H x)
  have h_inv := mfderivWithinFlat_mdifferentiableWithinAt (I := I) (M := M) x
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

/-! ## Bundled smooth vector fields

`SmoothVectorField I M` packages a tangent section with its $C^\infty$
smoothness witness. Algebraic operations (zero, add, sub, neg, smul,
constant section) are defined; clients use the bundled type to avoid
threading `ContMDiff` premises through every theorem.
-/

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- A smooth tangent vector field on `M`. -/
structure SmoothVectorField (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] where
  /-- Underlying tangent section. -/
  toFun : Π y : M, TangentSpace I y
  /-- Smoothness of the bundle section. -/
  smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
    (fun y => (⟨y, toFun y⟩ : TangentBundle I M))

namespace SmoothVectorField

instance : CoeFun (SmoothVectorField I M) fun _ => Π y : M, TangentSpace I y :=
  ⟨toFun⟩

@[simp] lemma coe_mk (f : Π y : M, TangentSpace I y) (h) :
    ⇑(⟨f, h⟩ : SmoothVectorField I M) = f := rfl

theorem smoothAt (X : SmoothVectorField I M) (x : M) : TangentSmoothAt X x :=
  TangentSmoothAt.mk ((X.smooth x).mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0))

noncomputable def zero : SmoothVectorField I M where
  toFun := fun _ => 0
  smooth := Bundle.contMDiff_zeroSection ℝ (TangentSpace I (M := M)) (n := ∞)

noncomputable instance : Zero (SmoothVectorField I M) := ⟨zero⟩

@[simp] lemma zero_apply (y : M) : (0 : SmoothVectorField I M) y = 0 := rfl

noncomputable def add (X Y : SmoothVectorField I M) : SmoothVectorField I M where
  toFun := fun y => X y + Y y
  smooth := ContMDiff.add_section X.smooth Y.smooth

noncomputable instance : Add (SmoothVectorField I M) := ⟨add⟩

@[simp] lemma add_apply (X Y : SmoothVectorField I M) (y : M) :
    (X + Y) y = X y + Y y := rfl

noncomputable def neg (X : SmoothVectorField I M) : SmoothVectorField I M where
  toFun := fun y => -X y
  smooth := ContMDiff.neg_section X.smooth

noncomputable instance : Neg (SmoothVectorField I M) := ⟨neg⟩

@[simp] lemma neg_apply (X : SmoothVectorField I M) (y : M) :
    (-X) y = -X y := rfl

noncomputable def sub (X Y : SmoothVectorField I M) : SmoothVectorField I M where
  toFun := fun y => X y - Y y
  smooth := ContMDiff.sub_section X.smooth Y.smooth

noncomputable instance : Sub (SmoothVectorField I M) := ⟨sub⟩

@[simp] lemma sub_apply (X Y : SmoothVectorField I M) (y : M) :
    (X - Y) y = X y - Y y := rfl

noncomputable def constSMul (a : ℝ) (X : SmoothVectorField I M) : SmoothVectorField I M where
  toFun := fun y => a • X y
  smooth := ContMDiff.const_smul_section (a := a) X.smooth

noncomputable instance : SMul ℝ (SmoothVectorField I M) := ⟨constSMul⟩

@[simp] lemma constSMul_apply (a : ℝ) (X : SmoothVectorField I M) (y : M) :
    (a • X) y = a • X y := by
  show (constSMul a X) y = a • X y; rfl

/-- Smooth-scalar-function multiplication `f • X` for `f : M → ℝ` smooth. -/
noncomputable def smul (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (X : SmoothVectorField I M) : SmoothVectorField I M where
  toFun := fun y => f y • X y
  smooth := ContMDiff.smul_section hf X.smooth

@[simp] lemma smul_apply (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (X : SmoothVectorField I M) (y : M) :
    (smul f hf X) y = f y • X y := rfl

/-- Constant `E`-valued section as a `SmoothVectorField`. -/
noncomputable def const [_root_.IsLocallyConstantChartedSpace H M] (v : E) :
    SmoothVectorField I M where
  toFun := fun _ => v
  smooth := TangentBundle.contMDiff_constSection_TangentSpace v

@[simp] lemma const_apply [_root_.IsLocallyConstantChartedSpace H M] (v : E) (y : M) :
    (const (I := I) v) y = v := rfl

end SmoothVectorField

end Riemannian

/-! ## `mfderiv` smoothness in chart-frame directions

For a globally smooth scalar $f : M \to \mathbb{R}$ and either a
constant direction $v : E$ or a smoothly-varying direction $V : M \to E$,
the function $y \mapsto \mathrm{d}f_y(V(y))$ is smooth at every point.

These are boundary-agnostic: the chart-pullback formula
$\mathrm{d}f_y = \mathrm{fderivWithin}_{\mathrm{range}\, I}(f \circ
\mathrm{chart.symm})$ combined with `IsLocallyConstantChartedSpace`
(which makes `extChartAt I y = extChartAt I x` constant on a
neighborhood of `x`) lifts $C^\infty$ regularity from the chart side
to the manifold side via `comp_of_preimage_mem_nhdsWithin`.
-/

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [IsLocallyConstantChartedSpace H M]

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
set_option backward.isDefEq.respectTransparency false in
/-- Smoothness of $y \mapsto \mathrm{d}f_y(v)$ for chart-frame-constant $v$. -/
theorem mfderiv_const_dir_smoothAt
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) (v : E) :
    MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y : M => mfderiv I 𝓘(ℝ, ℝ) f y v) x := by
  have h_symm_within : ContMDiffWithinAt 𝓘(ℝ, E) I ∞ (extChartAt I x).symm
      (Set.range I) (extChartAt I x x) :=
    contMDiffWithinAt_extChartAt_symm_range x (mem_extChartAt_target x)
  have h_eqx : (extChartAt I x).symm (extChartAt I x x) = x := by simp
  have h_comp_within : ContMDiffWithinAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞
      (f ∘ (extChartAt I x).symm) (Set.range I) (extChartAt I x x) :=
    (hf x).comp_contMDiffWithinAt_of_eq h_symm_within h_eqx
  have h_f_hat : ContDiffWithinAt ℝ ∞ (f ∘ (extChartAt I x).symm) (Set.range I)
      (extChartAt I x x) :=
    h_comp_within.contDiffWithinAt
  have h_unique : UniqueDiffOn ℝ (Set.range (I : H → E)) := I.uniqueDiffOn
  have h_mem : extChartAt I x x ∈ Set.range (I : H → E) := Set.mem_range_self _
  have h_fderiv_within : ContDiffWithinAt ℝ ∞
      (fderivWithin ℝ (f ∘ (extChartAt I x).symm) (Set.range I))
      (Set.range I) (extChartAt I x x) :=
    h_f_hat.fderivWithin_right h_unique (le_refl _) h_mem
  have h_fderiv_apply_within : ContDiffWithinAt ℝ ∞
      (fun e₀ : E => fderivWithin ℝ (f ∘ (extChartAt I x).symm) (Set.range I) e₀ v)
      (Set.range I) (extChartAt I x x) :=
    (ContinuousLinearMap.apply ℝ ℝ v).contDiff.contDiffAt.contDiffWithinAt.comp
      (extChartAt I x x) h_fderiv_within (Set.mapsTo_univ _ _)
  have h_fderiv_mdiff_within : MDifferentiableWithinAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ)
      (fun e₀ : E => fderivWithin ℝ (f ∘ (extChartAt I x).symm) (Set.range I) e₀ v)
      (Set.range I) (extChartAt I x x) :=
    h_fderiv_apply_within.contMDiffWithinAt.mdifferentiableWithinAt (by decide)
  have h_chart_mdiff : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I x : M → E) x :=
    mdifferentiableAt_extChartAt (mem_chart_source H x)
  have h_chart_within : MDifferentiableWithinAt I 𝓘(ℝ, E)
      (extChartAt I x) Set.univ x :=
    h_chart_mdiff.mdifferentiableWithinAt
  have h_preimage : (extChartAt I x) ⁻¹' Set.range I ∈ 𝓝[Set.univ] x := by
    rw [nhdsWithin_univ]
    refine Filter.mem_of_superset
      ((chartAt H x).open_source.mem_nhds (mem_chart_source H x)) ?_
    intro y _hy
    rw [Set.mem_preimage, extChartAt_coe]
    exact Set.mem_range_self _
  have h_fderiv_compose_within : MDifferentiableWithinAt I 𝓘(ℝ, ℝ)
      (fun y : M => fderivWithin ℝ (f ∘ (extChartAt I x).symm) (Set.range I)
        ((extChartAt I x) y) v)
      Set.univ x :=
    h_fderiv_mdiff_within.comp_of_preimage_mem_nhdsWithin _ h_chart_within h_preimage
  have h_fderiv_at : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y : M => fderivWithin ℝ (f ∘ (extChartAt I x).symm) (Set.range I)
        ((extChartAt I x) y) v) x :=
    mdifferentiableWithinAt_univ.mp h_fderiv_compose_within
  apply h_fderiv_at.congr_of_eventuallyEq
  have h_chart_eq : ∀ᶠ y in 𝓝 x, chartAt H y = chartAt H x :=
    chartAt_eventually_eq_of_locallyConstant x
  have h_chart_src : (chartAt H x).source ∈ 𝓝 x :=
    (chartAt H x).open_source.mem_nhds (mem_chart_source H x)
  have h_top_ne : (∞ : ℕ∞ω) ≠ 0 := by decide
  filter_upwards [h_chart_eq, h_chart_src] with y hy_chart hy_src
  have hf_at_y : MDifferentiableAt I 𝓘(ℝ, ℝ) f y :=
    (hf y).mdifferentiableAt h_top_ne
  have h_extChart_eq : extChartAt I y = extChartAt I x := by
    show (chartAt H y).extend I = (chartAt H x).extend I
    rw [hy_chart]
  show mfderiv I 𝓘(ℝ, ℝ) f y v
      = fderivWithin ℝ (f ∘ (extChartAt I x).symm) (Set.range I)
          ((extChartAt I x) y) v
  rw [hf_at_y.mfderiv]
  have h_written :
      writtenInExtChartAt I 𝓘(ℝ, ℝ) y f = f ∘ (extChartAt I x).symm := by
    funext z
    show (extChartAt 𝓘(ℝ, ℝ) (f y)) (f ((extChartAt I y).symm z))
        = f ((extChartAt I x).symm z)
    rw [h_extChart_eq]
    rfl
  rw [h_written, h_extChart_eq]
  rfl

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
set_option backward.isDefEq.respectTransparency false in
/-- Smoothness of $y \mapsto \mathrm{d}f_y(V(y))$ for smoothly-varying $V : M \to E$. -/
theorem mfderiv_smoothDir_smoothAt
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {x : M}
    {V : M → E} (hV : ContMDiffAt I 𝓘(ℝ, E) ∞ V x) :
    MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y : M => mfderiv I 𝓘(ℝ, ℝ) f y (V y)) x := by
  have h_symm_within : ContMDiffWithinAt 𝓘(ℝ, E) I ∞ (extChartAt I x).symm
      (Set.range I) (extChartAt I x x) :=
    contMDiffWithinAt_extChartAt_symm_range x (mem_extChartAt_target x)
  have h_eqx : (extChartAt I x).symm (extChartAt I x x) = x := by simp
  have h_comp_within : ContMDiffWithinAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞
      (f ∘ (extChartAt I x).symm) (Set.range I) (extChartAt I x x) :=
    (hf x).comp_contMDiffWithinAt_of_eq h_symm_within h_eqx
  have h_f_hat : ContDiffWithinAt ℝ ∞ (f ∘ (extChartAt I x).symm) (Set.range I)
      (extChartAt I x x) :=
    h_comp_within.contDiffWithinAt
  have h_unique : UniqueDiffOn ℝ (Set.range (I : H → E)) := I.uniqueDiffOn
  have h_mem : extChartAt I x x ∈ Set.range (I : H → E) := Set.mem_range_self _
  have h_fderiv_within : ContDiffWithinAt ℝ ∞
      (fderivWithin ℝ (f ∘ (extChartAt I x).symm) (Set.range I))
      (Set.range I) (extChartAt I x x) :=
    h_f_hat.fderivWithin_right h_unique (le_refl _) h_mem
  have h_fderiv_mdiff_within : MDifferentiableWithinAt 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] ℝ)
      (fderivWithin ℝ (f ∘ (extChartAt I x).symm) (Set.range I))
      (Set.range I) (extChartAt I x x) :=
    h_fderiv_within.contMDiffWithinAt.mdifferentiableWithinAt (by decide)
  have h_chart_mdiff : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I x : M → E) x :=
    mdifferentiableAt_extChartAt (mem_chart_source H x)
  have h_chart_within : MDifferentiableWithinAt I 𝓘(ℝ, E)
      (extChartAt I x) Set.univ x :=
    h_chart_mdiff.mdifferentiableWithinAt
  have h_preimage : (extChartAt I x) ⁻¹' Set.range I ∈ 𝓝[Set.univ] x := by
    rw [nhdsWithin_univ]
    refine Filter.mem_of_superset
      ((chartAt H x).open_source.mem_nhds (mem_chart_source H x)) ?_
    intro y _hy
    rw [Set.mem_preimage, extChartAt_coe]
    exact Set.mem_range_self _
  have h_fderiv_compose_within : MDifferentiableWithinAt I 𝓘(ℝ, E →L[ℝ] ℝ)
      (fun y : M => fderivWithin ℝ (f ∘ (extChartAt I x).symm) (Set.range I)
        ((extChartAt I x) y))
      Set.univ x :=
    h_fderiv_mdiff_within.comp_of_preimage_mem_nhdsWithin _ h_chart_within h_preimage
  have h_fderiv_at : MDifferentiableAt I 𝓘(ℝ, E →L[ℝ] ℝ)
      (fun y : M => fderivWithin ℝ (f ∘ (extChartAt I x).symm) (Set.range I)
        ((extChartAt I x) y)) x :=
    mdifferentiableWithinAt_univ.mp h_fderiv_compose_within
  have hV_mdiff : MDifferentiableAt I 𝓘(ℝ, E) V x :=
    hV.mdifferentiableAt (by decide)
  have h_compose : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y : M => fderivWithin ℝ (f ∘ (extChartAt I x).symm) (Set.range I)
        ((extChartAt I x) y) (V y)) x :=
    h_fderiv_at.clm_apply hV_mdiff
  apply h_compose.congr_of_eventuallyEq
  have h_chart_eq : ∀ᶠ y in 𝓝 x, chartAt H y = chartAt H x :=
    chartAt_eventually_eq_of_locallyConstant x
  have h_chart_src : (chartAt H x).source ∈ 𝓝 x :=
    (chartAt H x).open_source.mem_nhds (mem_chart_source H x)
  have h_top_ne : (∞ : ℕ∞ω) ≠ 0 := by decide
  filter_upwards [h_chart_eq, h_chart_src] with y hy_chart hy_src
  have hf_at_y : MDifferentiableAt I 𝓘(ℝ, ℝ) f y :=
    (hf y).mdifferentiableAt h_top_ne
  have h_extChart_eq : extChartAt I y = extChartAt I x := by
    show (chartAt H y).extend I = (chartAt H x).extend I
    rw [hy_chart]
  show mfderiv I 𝓘(ℝ, ℝ) f y (V y)
      = fderivWithin ℝ (f ∘ (extChartAt I x).symm) (Set.range I)
          ((extChartAt I x) y) (V y)
  rw [hf_at_y.mfderiv]
  have h_written :
      writtenInExtChartAt I 𝓘(ℝ, ℝ) y f = f ∘ (extChartAt I x).symm := by
    funext z
    show (extChartAt 𝓘(ℝ, ℝ) (f y)) (f ((extChartAt I y).symm z))
        = f ((extChartAt I x).symm z)
    rw [h_extChart_eq]
    rfl
  rw [h_written, h_extChart_eq]
  rfl

end Riemannian
