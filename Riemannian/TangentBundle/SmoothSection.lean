import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Tangent vector field smoothness predicate

`TangentSmoothAt V x` says the tangent vector field
`V : (y : M) → TangentSpace I y` is smooth at `x`. First-class predicate
for the smoothness algebra of bundle sections.

## Design rationale

Downstream Riemannian smoothness arguments repeatedly need "smoothness
of $f$ built from smooth bundle sections $V_1, \ldots, V_n$". Mathlib's
`MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (fun y => ⟨y, V y⟩) x` form is
syntactically heavy and confuses tactic search.

`TangentSmoothAt` makes vector field smoothness a **first-class concept**:

  * Clean API: `metricInner_smoothAt : TangentSmoothAt Y x → TangentSmoothAt Z x → ...`
  * Algebraic closure (Phase A.1): `(hY.add hZ).smul hf` etc.
  * Tactic dispatch (Phase A.2): future `tangent_smooth` tactic searches
    over `TangentSmoothAt`-tagged lemmas without descending into chart
    machinery — performance critical.

## Performance choice: `def` over `abbrev`

We define `TangentSmoothAt` as a regular `def`, not `abbrev`. This keeps
the predicate **opaque** to elaborator unfolding, so:

  * Instance synthesis on `IsManifold` etc. happens once at definition,
    not at every call site that mentions the verbose form.
  * Future `tangent_smooth` tactic matches on `TangentSmoothAt`
    syntactically, avoiding repeated unfolds during goal traversal.
  * Error messages reference `TangentSmoothAt V x`, not the verbose
    bundle-section `MDifferentiableAt` form.

Conversion to/from the underlying form is via `mk` / `toBundleSection`.
Lean 4's `def` is semi-reducible, so direct application typically still
works at typecheck level; explicit conversions are available when
elaboration needs nudging.

## API

  * `TangentSmoothAt V x` — predicate (this file)
  * `TangentSmoothAt.mk` / `.toBundleSection` — conversion to/from
    underlying `MDifferentiableAt` form
  * `TangentSmoothAt.coordSmoothAt` — extract chart-coordinate
    smoothness (`fun y => (e ⟨y, V y⟩).2`)
  * **Algebra closure** (Phase A.1): `.zero`, `.add`, `.sub`, `.neg`,
    `.smul` — closure of `TangentSmoothAt` under the standard
    operations on smooth vector fields.

**Ground truth**: Lee, *Smooth Manifolds*, Ch. 8 (smooth vector fields
form a `C^∞(M)`-module under pointwise addition and scalar multiplication).
-/

open scoped ContDiff Manifold Topology

namespace OpenGALib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Smoothness of a tangent vector field at a point**: the bundle
section `y ↦ ⟨y, V y⟩` is `MDifferentiableAt` at `x` as a map
`M → TangentBundle I M`. -/
def TangentSmoothAt (V : (y : M) → TangentSpace I y) (x : M) : Prop :=
  MDifferentiableAt I (I.prod 𝓘(ℝ, E))
    (fun y => (⟨y, V y⟩ : TangentBundle I M)) x

namespace TangentSmoothAt

/-- Construct a `TangentSmoothAt` from the underlying bundle-section
`MDifferentiableAt` form. -/
theorem mk {V : (y : M) → TangentSpace I y} {x : M}
    (h : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, V y⟩ : TangentBundle I M)) x) :
    TangentSmoothAt V x := h

/-- Unfold a `TangentSmoothAt` to the underlying bundle-section
`MDifferentiableAt` form. -/
theorem toBundleSection {V : (y : M) → TangentSpace I y} {x : M}
    (h : TangentSmoothAt V x) :
    MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, V y⟩ : TangentBundle I M)) x := h

/-- The chart-coordinate form of a smooth bundle section, via the
trivialization at `x`, is smooth as a function `M → E`. -/
theorem coordSmoothAt {V : (y : M) → TangentSpace I y} {x : M}
    (hV : TangentSmoothAt V x) :
    MDifferentiableAt I 𝓘(ℝ, E)
      (fun y => ((trivializationAt E (TangentSpace I) x) ⟨y, V y⟩).2) x := by
  have h := hV.toBundleSection
  rw [mdifferentiableAt_totalSpace] at h
  exact h.2

/-- **Iff bridge**: `TangentSmoothAt V x` is equivalent to chart-coord
smoothness at `x`. The projection conjunct of `mdifferentiableAt_totalSpace`
is discharged by `mdifferentiableAt_id`. -/
theorem iff_coord {V : (y : M) → TangentSpace I y} {x : M} :
    TangentSmoothAt V x ↔
      MDifferentiableAt I 𝓘(ℝ, E)
        (fun y => ((trivializationAt E (TangentSpace I) x) ⟨y, V y⟩).2) x := by
  unfold TangentSmoothAt
  rw [mdifferentiableAt_totalSpace]
  exact ⟨And.right, fun h => ⟨mdifferentiableAt_id, h⟩⟩

/-! ## Algebra closure -/

/-- The zero vector field is smooth at every point. -/
theorem zero (x : M) : TangentSmoothAt (fun y : M => (0 : TangentSpace I y)) x := by
  rw [TangentSmoothAt.iff_coord]
  set e := trivializationAt E (TangentSpace I) x
  apply (mdifferentiableAt_const (c := (0 : E))).congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds
    (FiberBundle.mem_baseSet_trivializationAt' x)] with y hy
  show (e ⟨y, (0 : TangentSpace I y)⟩).2 = (0 : E)
  rw [← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) e hy]
  exact map_zero _

/-- Sum of smooth vector fields is smooth. -/
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

/-- Negation of a smooth vector field is smooth. -/
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

/-- Difference of smooth vector fields is smooth. -/
theorem sub {Y Z : (y : M) → TangentSpace I y} {x : M}
    (hY : TangentSmoothAt Y x) (hZ : TangentSmoothAt Z x) :
    TangentSmoothAt (Y - Z) x := by
  have h_eq : (Y - Z : (y : M) → TangentSpace I y) = Y + (-Z) := by
    funext y
    show Y y - Z y = Y y + -Z y
    exact sub_eq_add_neg _ _
  rw [h_eq]
  exact hY.add hZ.neg

/-- Smooth scalar function times smooth vector field is smooth. -/
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

/-! ## Tactic — `tangent_smooth`

Recursively applies `TangentSmoothAt.{zero, add, sub, neg, smul}` and
`assumption`. Closes any goal of the form `TangentSmoothAt V x` where
`V` is built from hypotheses by smooth-vector-field algebra.

**Performance**: each rule is deterministic `apply` against the goal
head — no backtracking, no metavariable explosion. `assumption` is the
leaf-case discharger. -/

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

end OpenGALib

/-! ## UX test — `tangent_smooth` regression guard -/

section TangentSmoothTest

open OpenGALib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Sum of two smooth fields — closes via `add` + `assumption`. -/
example {Y Z : (y : M) → TangentSpace I y} {x : M}
    (hY : TangentSmoothAt Y x) (hZ : TangentSmoothAt Z x) :
    TangentSmoothAt (Y + Z) x := by tangent_smooth

/-- Difference + negation — closes via `sub`, `neg`, `assumption`. -/
example {Y Z : (y : M) → TangentSpace I y} {x : M}
    (hY : TangentSmoothAt Y x) (hZ : TangentSmoothAt Z x) :
    TangentSmoothAt (Y - (-Z)) x := by tangent_smooth

/-- Smooth-scalar smul — closes via `smul` + 2 assumptions. -/
example {Y : (y : M) → TangentSpace I y} {f : M → ℝ} {x : M}
    (hY : TangentSmoothAt Y x) (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x) :
    TangentSmoothAt (fun y => f y • Y y) x := by tangent_smooth

/-- Compound: `f • Y - Z + W` — exercises full algebra recursion. -/
example {Y Z W : (y : M) → TangentSpace I y} {f : M → ℝ} {x : M}
    (hY : TangentSmoothAt Y x) (hZ : TangentSmoothAt Z x) (hW : TangentSmoothAt W x)
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x) :
    TangentSmoothAt ((fun y => f y • Y y) - Z + W) x := by tangent_smooth

end TangentSmoothTest
