import OpenGALib.Riemannian.Operators.Bochner

/-!
# Per-summand chain of the heart-of-Bochner identity

This file ports the per-summand chain that drives the unconditional
discharge of the heart-of-Bochner inner-product identity
(`hInner_discharge` in external `differential-geometry`).

For a smooth scalar `f : M → ℝ`, smooth `B, W : SmoothVectorField I M`,
and `x : M` in the strict interior of `range I`:

* `bochner_per_summand_swap` — Hess-sym swap form (step (d) of the textbook
  derivation):
  $$g_x(\nabla_{B} \nabla_B \nabla f, W) - g_x(\nabla_{\nabla_B B} \nabla f, W)
     = g_x(\nabla_{B} \nabla_W \nabla f, B) - g_x(\nabla_{\nabla_B W} \nabla f, B).$$

Closure path: two applications of `leviCivitaConnection_metric_compatible`
on the section pairs `(Q := ∇_B ∇f, W)` and `(P := ∇_W ∇f, B)` along the
direction `B x`, combined with the section-level Hessian symmetry
`hessianBilin_section_eventually_symm_of_strict_interior` to equate
the two mfderiv values at `x`, and pointwise `hessianBilin_symm` at `x`
to identify the cross-Christoffel terms.

This is the OpenGALib analog of external's `bochner_per_summand_swap`
(lines 2828–2966 of `external/differential-geometry/.../Bochner.lean`).
The structural difference is that the section-level Hess-sym is stated
as `=ᶠ[𝓝 x]` (relying on strict-interior nbhd propagation from
`extChartAt_self_eventually_mem_closure_interior_range`) rather than
the global `=` form (which requires `[I.Boundaryless]`).

## References
* Petersen, *Riemannian Geometry*, Ch. 7 §1 Proposition 33
* do Carmo, *Riemannian Geometry*, §6 (curvature commutators)
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle
open scoped ContDiff Manifold Bundle Riemannian InnerProductSpace Topology

namespace Riemannian
namespace Operators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [IsLocallyConstantChartedSpace H M]
  [hm : HasMetric I M]

/-- **Per-summand swap form** (Hess-sym swap, step (d) of Petersen Ch 7 §1
Prop 33).

Given smooth `B, W : SmoothVectorField I M` and `f : M → ℝ` smooth with
smooth gradient bundle section, at any point `x` mapping into the strict
interior of `range I`:

$$g_x(\nabla_B \nabla_B \nabla f, W) - g_x(\nabla_{\nabla_B B} \nabla f, W)
   = g_x(\nabla_B \nabla_W \nabla f, B) - g_x(\nabla_{\nabla_B W} \nabla f, B).$$

The proof combines:
* Two `leviCivitaConnection_metric_compatible` applications on the section
  pairs `(Q, W)` and `(P, B)` where `Q := ∇_B ∇f`, `P := ∇_W ∇f`.
* `hessianBilin_section_eventually_symm_of_strict_interior` to obtain
  the section-level Hess sym `(b ↦ g(Q, W)) =ᶠ (b ↦ g(P, B))`.
* `Filter.EventuallyEq.mfderiv_eq` to lift the section-level equality to
  equality of mfderiv values at `x` along direction `B x`.
* `hessianBilin_symm` at `x` to identify the cross-Christoffel inner
  products `g(Q x, ∇_B W) = g(∇_{∇_B W} ∇f, B)` and symmetric counterpart.

External reference: `bochner_per_summand_swap` in
`differential-geometry/.../Bochner.lean:2828–2966`. -/
theorem bochner_per_summand_swap
    [IsManifold I 2 M]
    (f : M → ℝ) (B W : SmoothVectorField I M) (x : M)
    (h_strict : extChartAt I x x ∈ interior (Set.range I))
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (h_grad : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
              (fun y => (⟨y, manifoldGradient (I := I) f y⟩ : TangentBundle I M))) :
    metricInner x
        (covDeriv B.toFun
          (fun y => covDeriv B.toFun (manifoldGradient (I := I) f) y) x)
        (W.toFun x)
      - metricInner x
          (covDerivAt (manifoldGradient (I := I) f) x
            (covDeriv B.toFun B.toFun x))
          (W.toFun x)
    = metricInner x
        (covDeriv B.toFun
          (fun y => covDeriv W.toFun (manifoldGradient (I := I) f) y) x)
        (B.toFun x)
      - metricInner x
          (covDerivAt (manifoldGradient (I := I) f) x
            (covDeriv B.toFun W.toFun x))
          (B.toFun x) := by
  classical
  -- Wrap `manifoldGradient f` as a `SmoothVectorField`.
  let gradF : SmoothVectorField I M :=
    { toFun := manifoldGradient (I := I) f, smooth := h_grad }
  -- Smoothness sections used downstream.
  set Q : Π y : M, TangentSpace I y :=
    fun y => covDeriv B.toFun gradF.toFun y with hQ_def
  set P : Π y : M, TangentSpace I y :=
    fun y => covDeriv W.toFun gradF.toFun y with hP_def
  have hQ_smooth : ∀ y, TangentSmoothAt Q y :=
    fun y => covDeriv_smoothVF_smoothAt B gradF y
  have hP_smooth : ∀ y, TangentSmoothAt P y :=
    fun y => covDeriv_smoothVF_smoothAt W gradF y
  -- Step (a): metric compat on `(Q, W)` along direction `B x` at `x`.
  have h_compat_QW := leviCivitaConnection_metric_compatible
    B.toFun Q W.toFun x (B.smoothAt x) (hQ_smooth x) (W.smoothAt x)
  -- Step (b): section-level Hess sym `(b ↦ g(Q b, W b)) =ᶠ (b ↦ g(P b, B b))`.
  -- Equivalent (def-eq) to the section-level form of
  -- `hessianBilin_section_eventually_symm_of_strict_interior` with X := B, Y := W.
  have h_section_sym :
      (fun y : M => metricInner y (Q y) (W.toFun y))
        =ᶠ[𝓝 x] (fun y : M => metricInner y (P y) (B.toFun y)) :=
    hessianBilin_section_eventually_symm_of_strict_interior
      (I := I) f B.toFun W.toFun x h_strict hf h_grad
  -- Step (c): metric compat on `(P, B)` along direction `B x` at `x`.
  have h_compat_PB := leviCivitaConnection_metric_compatible
    B.toFun P B.toFun x (B.smoothAt x) (hP_smooth x) (B.smoothAt x)
  -- Step (d): differentiate `h_section_sym` at `x` along `B x` via `EventuallyEq.mfderiv_eq`.
  have h_mfderiv_eq :
      mfderiv I 𝓘(ℝ, ℝ)
          (fun y : M => metricInner y (Q y) (W.toFun y)) x (B.toFun x)
        = mfderiv I 𝓘(ℝ, ℝ)
          (fun y : M => metricInner y (P y) (B.toFun y)) x (B.toFun x) := by
    rw [Filter.EventuallyEq.mfderiv_eq h_section_sym]
    rfl
  -- `h_mfderiv_eq : mfderiv (...g(Q, W)) x (B x) = mfderiv (...g(P, B)) x (B x)`.
  -- Combine `h_compat_QW`, `h_compat_PB`, `h_mfderiv_eq`:
  -- g(LC Q x (B x), W x) + g(Q x, LC W x (B x))
  --   = mfderiv (b ↦ g(Q, W)) x (B x)   [h_compat_QW symm]
  --   = mfderiv (b ↦ g(P, B)) x (B x)   [h_mfderiv_eq]
  --   = g(LC P x (B x), B x) + g(P x, LC B x (B x))  [h_compat_PB]
  have h_combined :
      metricInner x ((leviCivitaConnection (I := I) (M := M)).toFun Q x (B.toFun x))
          (W.toFun x)
        + metricInner x (Q x)
            ((leviCivitaConnection (I := I) (M := M)).toFun W.toFun x (B.toFun x))
      = metricInner x ((leviCivitaConnection (I := I) (M := M)).toFun P x (B.toFun x))
          (B.toFun x)
        + metricInner x (P x)
            ((leviCivitaConnection (I := I) (M := M)).toFun B.toFun x (B.toFun x)) := by
    rw [← h_compat_QW, h_mfderiv_eq, h_compat_PB]
  -- Step (e): identify `g(Q x, LC W x (B x))` via `hessianBilin_symm` at `x`.
  -- `Q x = LC ∇f x (B x)`, so `g(Q x, LC W x (B x)) = hessianBilin f x (B x) (LC W x (B x))`.
  -- By hessianBilin_symm = `hessianBilin f x (LC W x (B x)) (B x) = g(LC ∇f x (LC W x (B x)), B x)`.
  have hf_2 : ContMDiffAt I 𝓘(ℝ, ℝ) 2 f x :=
    (hf x).of_le (by
      show ((2 : ℕ∞) : ℕ∞ω) ≤ ∞
      exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤))
  have h_grad_at_x : TangentSmoothAt (manifoldGradient (I := I) f) x :=
    (h_grad x).mdifferentiableAt (by simp)
  -- Convert `h_strict` (strict interior) to `h_interior` (closure interior) at `x` only.
  have h_interior : extChartAt I x x ∈ closure (interior (Set.range I)) :=
    subset_closure h_strict
  -- `hessianBilin_symm` at `x`.
  have h_hess_sym : ∀ a b : TangentSpace I x,
      hessianBilin (I := I) f x a b = hessianBilin (I := I) f x b a :=
    fun a b => hessianBilin_symm (I := I) f x h_interior hf_2 h_grad_at_x a b
  -- Apply to (B x, LC W x (B x)) and (W x, LC B x (B x)).
  have h_sym_BW :
      hessianBilin (I := I) f x (B.toFun x)
          ((leviCivitaConnection (I := I) (M := M)).toFun W.toFun x (B.toFun x))
        = hessianBilin (I := I) f x
            ((leviCivitaConnection (I := I) (M := M)).toFun W.toFun x (B.toFun x))
            (B.toFun x) :=
    h_hess_sym _ _
  have h_sym_WB :
      hessianBilin (I := I) f x (W.toFun x)
          ((leviCivitaConnection (I := I) (M := M)).toFun B.toFun x (B.toFun x))
        = hessianBilin (I := I) f x
            ((leviCivitaConnection (I := I) (M := M)).toFun B.toFun x (B.toFun x))
            (W.toFun x) :=
    h_hess_sym _ _
  -- Unfold `hessianBilin f x a b = metricInner x (covDerivAt ∇f x a) b` (rfl).
  -- LHS of h_sym_BW : `metricInner x (Q x) (LC W x (B x)) = metricInner x (LC ∇f x (LC W x (B x))) (B x)`.
  -- LHS of h_sym_WB : `metricInner x (P x) (LC B x (B x)) = metricInner x (LC ∇f x (LC B x (B x))) (W x)`.
  -- Note Q x = LC ∇f x (B x) and P x = LC ∇f x (W x) (def-eq).
  -- We need `metricInner x (Q x) (LC W x (B x))` form on LHS of h_sym_BW.
  -- `hessianBilin f x (B x) v = metricInner x (covDerivAt ∇f x (B x)) v = metricInner x (Q x) v`
  -- by def (covDerivAt ∇f x (B x) = (lcc ∇f) x (B x) = Q x def-eq).
  have h_QcovBW : metricInner x (Q x)
        ((leviCivitaConnection (I := I) (M := M)).toFun W.toFun x (B.toFun x))
      = metricInner x ((leviCivitaConnection (I := I) (M := M)).toFun gradF.toFun x
          ((leviCivitaConnection (I := I) (M := M)).toFun W.toFun x (B.toFun x)))
          (B.toFun x) := h_sym_BW
  have h_PcovBB : metricInner x (P x)
        ((leviCivitaConnection (I := I) (M := M)).toFun B.toFun x (B.toFun x))
      = metricInner x ((leviCivitaConnection (I := I) (M := M)).toFun gradF.toFun x
          ((leviCivitaConnection (I := I) (M := M)).toFun B.toFun x (B.toFun x)))
          (W.toFun x) := h_sym_WB
  rw [h_QcovBW, h_PcovBB] at h_combined
  -- Rearrange to match the goal: LHS - LCBB term = RHS - LCWB term.
  -- The goal uses `covDerivAt ∇f x v` form rather than `lcc.toFun ∇f x v`.
  -- These are definitionally equal: `covDerivAt Y x v := (lcc.toFun Y x) v`.
  show metricInner x ((leviCivitaConnection (I := I) (M := M)).toFun Q x (B.toFun x))
          (W.toFun x)
        - metricInner x
            ((leviCivitaConnection (I := I) (M := M)).toFun gradF.toFun x
              ((leviCivitaConnection (I := I) (M := M)).toFun B.toFun x (B.toFun x)))
            (W.toFun x)
      = metricInner x ((leviCivitaConnection (I := I) (M := M)).toFun P x (B.toFun x))
          (B.toFun x)
        - metricInner x
            ((leviCivitaConnection (I := I) (M := M)).toFun gradF.toFun x
              ((leviCivitaConnection (I := I) (M := M)).toFun W.toFun x (B.toFun x)))
            (B.toFun x)
  linarith [h_combined]

/-- **Per-summand riemann form** (step (e) of Petersen Ch 7 §1 Prop 33,
torsion-free curvature expansion).

For smooth `B, W : SmoothVectorField I M` and `f : M → ℝ` smooth at `x`:

$$g_x(\nabla_B \nabla_W \nabla f, B) - g_x(\nabla_{\nabla_B W} \nabla f, B)
   = g_x(R(B, W) \nabla f, B) + g_x(\nabla_W \nabla_B \nabla f, B)
     - g_x(\nabla_{\nabla_W B} \nabla f, B).$$

Algebraic identity: unfolds `riemannCurvature` via
$R(B, W) \nabla f = \nabla_B \nabla_W \nabla f - \nabla_W \nabla_B \nabla f
- \nabla_{[B, W]} \nabla f$, applies torsion-freeness
$[B, W] = \nabla_B W - \nabla_W B$, and the ℝ-linearity of
$\nabla_\cdot \nabla f$ in its direction argument to split
$\nabla_{[B,W]} \nabla f = \nabla_{\nabla_B W} \nabla f -
\nabla_{\nabla_W B} \nabla f$.

External reference: `bochner_per_summand_riemann_form` in
`differential-geometry/.../Bochner.lean:2978–3076`. -/
theorem bochner_per_summand_riemann_form
    (f : M → ℝ) (B W : SmoothVectorField I M) (x : M) :
    metricInner x
        (covDeriv B.toFun
          (fun y => covDeriv W.toFun (manifoldGradient (I := I) f) y) x)
        (B.toFun x)
      - metricInner x
          (covDerivAt (manifoldGradient (I := I) f) x
            (covDeriv B.toFun W.toFun x))
          (B.toFun x)
    = metricInner x
        (riemannCurvature B.toFun W.toFun (manifoldGradient (I := I) f) x)
        (B.toFun x)
      + metricInner x
          (covDeriv W.toFun
            (fun y => covDeriv B.toFun (manifoldGradient (I := I) f) y) x)
          (B.toFun x)
      - metricInner x
          (covDerivAt (manifoldGradient (I := I) f) x
            (covDeriv W.toFun B.toFun x))
          (B.toFun x) := by
  classical
  -- Unfold `riemannCurvature` via def.
  -- riemannCurvature B W ∇f x = ∇_B (∇_W ∇f) x - ∇_W (∇_B ∇f) x - ∇_{[B,W]} ∇f x
  have h_riem :
      riemannCurvature B.toFun W.toFun (manifoldGradient (I := I) f) x
        = covDeriv B.toFun
            (fun y => covDeriv W.toFun (manifoldGradient (I := I) f) y) x
          - covDeriv W.toFun
            (fun y => covDeriv B.toFun (manifoldGradient (I := I) f) y) x
          - covDeriv (VectorField.mlieBracket I B.toFun W.toFun)
              (manifoldGradient (I := I) f) x :=
    riemannCurvature_def B.toFun W.toFun (manifoldGradient (I := I) f) x
  -- Torsion-free at x: `[B, W] x = ∇_B W x - ∇_W B x`. Use
  -- `covDeriv_sub_swap_eq_mlieBracket B W x (B.smoothAt x) (W.smoothAt x)`:
  -- (∇_B W) x - (∇_W B) x = [B, W] x.
  have h_torsion :
      covDeriv B.toFun W.toFun x - covDeriv W.toFun B.toFun x
        = VectorField.mlieBracket I B.toFun W.toFun x :=
    covDeriv_sub_swap_eq_mlieBracket B.toFun W.toFun x (B.smoothAt x) (W.smoothAt x)
  -- `covDeriv U Z x = lcc.toFun Z x (U x)`; in particular, depends ℝ-linearly on `U x`.
  -- So `covDeriv (mlieBracket I B W) ∇f x = lcc.toFun ∇f x ((mlieBracket I B W) x)`
  --                                        = lcc.toFun ∇f x ((∇_B W - ∇_W B) x)
  --                                        = lcc.toFun ∇f x ((∇_B W) x) - lcc.toFun ∇f x ((∇_W B) x)
  --                                        = covDerivAt ∇f x (∇_B W x) - covDerivAt ∇f x (∇_W B x).
  have h_lieb_dir :
      covDeriv (VectorField.mlieBracket I B.toFun W.toFun)
          (manifoldGradient (I := I) f) x
        = covDerivAt (manifoldGradient (I := I) f) x
            (covDeriv B.toFun W.toFun x)
          - covDerivAt (manifoldGradient (I := I) f) x
            (covDeriv W.toFun B.toFun x) := by
    -- Replace `(mlieBracket I B W) x` with `∇_B W x - ∇_W B x` via h_torsion.
    show (leviCivitaConnection (I := I) (M := M)).toFun
            (manifoldGradient (I := I) f) x
            (VectorField.mlieBracket I B.toFun W.toFun x)
        = (leviCivitaConnection (I := I) (M := M)).toFun
            (manifoldGradient (I := I) f) x
            (covDeriv B.toFun W.toFun x)
          - (leviCivitaConnection (I := I) (M := M)).toFun
              (manifoldGradient (I := I) f) x
              (covDeriv W.toFun B.toFun x)
    rw [← h_torsion]
    exact ContinuousLinearMap.map_sub _ _ _
  -- Substitute and rearrange.
  rw [h_riem, h_lieb_dir]
  -- Now: g(∇_B ∇_W ∇f - ∇_W ∇_B ∇f - (covDeriv ∇f (∇_B W) - covDeriv ∇f (∇_W B)), B x)
  --     = g(∇_B ∇_W ∇f, B) - g(∇_W ∇_B ∇f, B) - g(covDeriv ∇f (∇_B W), B) + g(covDeriv ∇f (∇_W B), B)
  -- (by metricInner_sub_left distribution × 2 + metricInner_add_left for the inner +).
  -- Goal becomes pure algebra; linarith with metricInner-sub distribution closes.
  rw [metricInner_sub_left, metricInner_sub_left, metricInner_sub_left]
  linarith

/-- **Per-summand assembled form** (step (f) of Petersen Ch 7 §1 Prop 33,
final per-summand assembly).

For smooth `B, W : SmoothVectorField I M` and `f : M → ℝ` smooth, at
strict-interior `x`:

$$g_x(\nabla_B \nabla_B \nabla f, W) - g_x(\nabla_{\nabla_B B} \nabla f, W)
   = g_x(R(B, W) \nabla f, B)
     + \mathrm{d}\left(b \mapsto \mathrm{Hess}\,f(B, B)\right)(x)\cdot W
     - 2\,\mathrm{Hess}\,f(B, \nabla_W B)(x).$$

Composes:
* `bochner_per_summand_swap` (step d) — Hess-sym swap form.
* `bochner_per_summand_riemann_form` (step e) — torsion-free curvature
  expansion.
* A third `leviCivitaConnection_metric_compatible` on the section pair
  `(Q := ∇_B ∇f, B)` along direction `W x` at `x`, identifying
  `g(∇_W Q, B)` as `mfderiv (b ↦ g(Q b, B b)) x (W x) - g(Q x, ∇_W B x)`.
* `hessianBilin_symm` at `x` to identify both Christoffel-correction
  inner products as the single quantity
  `hessianBilin f x (B x) (∇_W B x)`.

External reference: `bochner_per_summand_assembled` in
`differential-geometry/.../Bochner.lean:3088–3239`. -/
theorem bochner_per_summand_assembled
    [IsManifold I 2 M]
    (f : M → ℝ) (B W : SmoothVectorField I M) (x : M)
    (h_strict : extChartAt I x x ∈ interior (Set.range I))
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (h_grad : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
              (fun y => (⟨y, manifoldGradient (I := I) f y⟩ : TangentBundle I M))) :
    metricInner x
        (covDeriv B.toFun
          (fun y => covDeriv B.toFun (manifoldGradient (I := I) f) y) x)
        (W.toFun x)
      - metricInner x
          (covDerivAt (manifoldGradient (I := I) f) x
            (covDeriv B.toFun B.toFun x))
          (W.toFun x)
    = metricInner x
        (riemannCurvature B.toFun W.toFun (manifoldGradient (I := I) f) x)
        (B.toFun x)
      + (show ℝ from mfderiv I 𝓘(ℝ, ℝ)
          (fun y : M => hessianBilin (I := I) f y (B.toFun y) (B.toFun y))
          x (W.toFun x))
      - 2 * hessianBilin (I := I) f x (B.toFun x)
              (covDeriv W.toFun B.toFun x) := by
  classical
  -- Wrap ∇f as SmoothVectorField.
  let gradF : SmoothVectorField I M :=
    { toFun := manifoldGradient (I := I) f, smooth := h_grad }
  set Q : Π y : M, TangentSpace I y :=
    fun y => covDeriv B.toFun gradF.toFun y with hQ_def
  -- Step 1: chain `bochner_per_summand_swap` + `bochner_per_summand_riemann_form`.
  -- Get LHS = R-term + g(LC Q x (W x), B x) - g(LC Gf x (LC B x (W x))) (B x).
  have h_swap := bochner_per_summand_swap (I := I) f B W x h_strict hf h_grad
  have h_riem := bochner_per_summand_riemann_form (I := I) f B W x
  -- Step 2: third metric compat on (Q, B) along direction W x at x.
  have hQ_smooth : TangentSmoothAt Q x :=
    covDeriv_smoothVF_smoothAt B gradF x
  have h_compat_QB := leviCivitaConnection_metric_compatible
    W.toFun Q B.toFun x (W.smoothAt x) hQ_smooth (B.smoothAt x)
  -- Identify `(fun y => metricInner y (Q y) (B y)) = (fun y => hessianBilin f y (B y) (B y))`.
  have h_QB_section :
      (fun y : M => metricInner y (Q y) (B.toFun y))
        = (fun y : M => hessianBilin (I := I) f y (B.toFun y) (B.toFun y)) := by
    funext y
    -- hessianBilin f y v w = metricInner y (covDerivAt ∇f y v) w (def).
    -- Q y = covDeriv B ∇f y = covDerivAt ∇f y (B y) (def).
    rfl
  rw [h_QB_section] at h_compat_QB
  -- h_compat_QB : mfderiv (b ↦ Hess(B b, B b)) x (W x)
  --             = g(LC Q x (W x), B x) + g(Q x, LC B x (W x))
  -- Step 3: identify `g(Q x, LC B x (W x))` via `hessianBilin_symm` at `x`.
  -- Q x = covDerivAt ∇f x (B x), LC B x (W x) = covDeriv W B x.
  -- So g(Q x, covDeriv W B x) = hessianBilin f x (B x) (covDeriv W B x).
  -- Identical to RHS's third term (the `2 *` factor will come from combining with
  -- the swap's RHS third term, which equals hessianBilin f x (covDeriv W B x) (B x)
  -- via def, and then by hessianBilin_symm at x, also equals hessianBilin f x (B x) (covDeriv W B x)).
  have hf_2 : ContMDiffAt I 𝓘(ℝ, ℝ) 2 f x :=
    (hf x).of_le (by
      show ((2 : ℕ∞) : ℕ∞ω) ≤ ∞
      exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤))
  have h_grad_at_x : TangentSmoothAt (manifoldGradient (I := I) f) x :=
    (h_grad x).mdifferentiableAt (by simp)
  have h_interior : extChartAt I x x ∈ closure (interior (Set.range I)) :=
    subset_closure h_strict
  have h_hess_sym : ∀ a b : TangentSpace I x,
      hessianBilin (I := I) f x a b = hessianBilin (I := I) f x b a :=
    fun a b => hessianBilin_symm (I := I) f x h_interior hf_2 h_grad_at_x a b
  -- Use h_hess_sym at (covDeriv W B x, B x) to fold the second Christoffel.
  have h_sym_WB : hessianBilin (I := I) f x (covDeriv W.toFun B.toFun x) (B.toFun x)
                = hessianBilin (I := I) f x (B.toFun x) (covDeriv W.toFun B.toFun x) :=
    h_hess_sym _ _
  -- Compose h_swap (LHS = swap RHS) and h_riem (swap RHS = riemann RHS):
  -- LHS = g(R(B, W) ∇f, B x) + g(LC Q x (W x), B x) - g(LC Gf x (LC B x (W x))) (B x)
  -- where `LC Q x (W x) = covDeriv W Q x` (a CLM eval at W x of the section ∇_Q),
  -- but actually here it's `lcc.toFun Q x (W x)` = `covDeriv W.toFun (fun y => covDeriv B.toFun ∇f y) x`.
  rw [h_swap, h_riem]
  -- Now goal:
  -- g(R(B,W) ∇f, B) + g(LC Q x (W x), B) - g(LC Gf x (LC B x (W x))) (B)
  --   = g(R(B,W) ∇f, B) + mfderiv (b ↦ Hess(B,B)) x (W x) - 2 * Hess(x, B x, ∇_W B)
  -- Substitute g(LC Q x (W x), B) via h_compat_QB:
  --   g(LC Q x (W x), B) = mfderiv (...) - g(Q x, LC B x (W x))
  --                       = mfderiv (...) - hessianBilin f x (B x) (LC B x (W x))
  -- and g(LC Gf x (LC B x (W x))) (B) = hessianBilin f x (LC B x (W x)) (B x)
  --   (def: hessianBilin f x v w = metricInner x (covDerivAt ∇f x v) w; here v = LC B x (W x) = ∇_W B x, w = B x)
  --   = hessianBilin f x (B x) (LC B x (W x))   [by h_sym_WB]
  -- So the cancellation:
  --   g(R + g(LC Q W, B) - Hess(LC B W, B)
  --   = R + (mfderiv - Hess(B, LC B W)) - Hess(B, LC B W)   [via h_sym_WB on last]
  --   = R + mfderiv - 2 * Hess(B, LC B W).
  -- We rewrite the goal's last subtraction using h_sym_WB to get a `2 *` factor.
  -- Cast the mfderiv result to `ℝ` via a `let`-binding `mf_val` so that
  -- subsequent arithmetic tactics don't have to traverse `show ℝ from ...`.
  set mf_val : ℝ := mfderiv I 𝓘(ℝ, ℝ)
      (fun y : M => hessianBilin (I := I) f y (B.toFun y) (B.toFun y))
      x (W.toFun x) with hmf_val
  -- Rewrite h_compat_QB in terms of mf_val.
  have h_compat_QB' :
      mf_val
        = metricInner x ((leviCivitaConnection (I := I) (M := M)).toFun Q x (W.toFun x))
            (B.toFun x)
          + metricInner x (Q x)
              ((leviCivitaConnection (I := I) (M := M)).toFun B.toFun x (W.toFun x)) :=
    h_compat_QB
  have h_id_LCQW :
      metricInner x
          ((leviCivitaConnection (I := I) (M := M)).toFun Q x (W.toFun x))
          (B.toFun x)
        = mf_val - hessianBilin (I := I) f x (B.toFun x)
            (covDeriv W.toFun B.toFun x) := by
    have h_id_Q_LCBW :
        metricInner x (Q x)
            ((leviCivitaConnection (I := I) (M := M)).toFun B.toFun x (W.toFun x))
          = hessianBilin (I := I) f x (B.toFun x)
              (covDeriv W.toFun B.toFun x) := rfl
    linarith [h_compat_QB', h_id_Q_LCBW]
  -- Identification of the LHS's third term as `hessianBilin (... ) (B x)`,
  -- folded via h_sym_WB into the `(B x) (...)` form.
  have h_id_LCBW :
      metricInner x
          (covDerivAt (manifoldGradient (I := I) f) x
            (covDeriv W.toFun B.toFun x))
          (B.toFun x)
        = hessianBilin (I := I) f x (B.toFun x)
            (covDeriv W.toFun B.toFun x) := by
    show hessianBilin (I := I) f x (covDeriv W.toFun B.toFun x) (B.toFun x)
        = hessianBilin (I := I) f x (B.toFun x) (covDeriv W.toFun B.toFun x)
    exact h_sym_WB
  -- The goal's `covDeriv W.toFun (fun y => covDeriv B.toFun ∇f y) x` is exactly
  -- `lcc.toFun Q x (W.toFun x)` (def-eq).
  have h_id_outer :
      covDeriv W.toFun (fun y => covDeriv B.toFun
            (manifoldGradient (I := I) f) y) x
        = (leviCivitaConnection (I := I) (M := M)).toFun Q x (W.toFun x) := rfl
  rw [h_id_outer]
  rw [h_id_LCQW, h_id_LCBW]
  -- Goal: R + (mfderiv - Hess(B, ∇_W B)) - Hess(B, ∇_W B) = R + mfderiv - 2 * Hess(B, ∇_W B)
  ring

/-! ### Diagonal tensoriality bridge (Hadamard)

For `Z, V : SmoothVectorField I M`, the section-form $(\nabla^2 Z)(V, V)(x)$
equals the constant-form $(\nabla^2 Z)(V x, V x)$. Proof via Hadamard
decomposition `V - const(V x) = ∑_j u_j • const e_j` with `u_j(x) = 0`. -/

/-- `TangentSmoothAt` propagates over `Finset.sum`. -/
private lemma tangentSmoothAt_finset_sum
    {ι : Type*} (s : Finset ι) {x : M}
    (Y : ι → Π b : M, TangentSpace I b)
    (hY : ∀ i ∈ s, TangentSmoothAt (Y i) x) :
    TangentSmoothAt (fun b : M => ∑ i ∈ s, Y i b) x := by
  classical
  induction s using Finset.induction with
  | empty =>
    show TangentSmoothAt (fun _ : M => (0 : TangentSpace I x)) x
    exact (SmoothVectorField.const (I := I) (M := M) (0 : E)).smoothAt x
  | insert j t hjt ih =>
    have hYj : TangentSmoothAt (Y j) x := hY j (Finset.mem_insert_self j t)
    have hYrest : ∀ i ∈ t, TangentSmoothAt (Y i) x :=
      fun i hi => hY i (Finset.mem_insert_of_mem hi)
    have hrest : TangentSmoothAt (fun b : M => ∑ i ∈ t, Y i b) x := ih hYrest
    have h_eq : (fun b : M => ∑ i ∈ insert j t, Y i b)
        = (fun b : M => Y j b + ∑ i ∈ t, Y i b) := by
      funext b; rw [Finset.sum_insert hjt]
    rw [h_eq]; exact hYj.add hrest

/-- `covDeriv` distributes over `Finset.sum` in the differentiated field. -/
private lemma covDeriv_finset_sum_field
    {ι : Type*} (s : Finset ι)
    (X : Π b : M, TangentSpace I b)
    (Y : ι → Π b : M, TangentSpace I b) (x : M)
    (hY : ∀ i ∈ s, TangentSmoothAt (Y i) x) :
    (∇[X] (fun b => ∑ i ∈ s, Y i b)) x = ∑ i ∈ s, (∇[X] (Y i)) x := by
  classical
  induction s using Finset.induction with
  | empty =>
    show ((leviCivitaConnection (I := I) (M := M)).toFun
            (fun b : M => ∑ i ∈ (∅ : Finset ι), Y i b)) x (X x) = 0
    have h_zero : (fun b : M => ∑ i ∈ (∅ : Finset ι), Y i b)
        = (0 : Π b : M, TangentSpace I b) := by
      funext b; simp
    rw [h_zero, CovariantDerivative.zero]; rfl
  | insert j t hjt ih =>
    have hYj : TangentSmoothAt (Y j) x := hY j (Finset.mem_insert_self j t)
    have hYrest : ∀ i ∈ t, TangentSmoothAt (Y i) x :=
      fun i hi => hY i (Finset.mem_insert_of_mem hi)
    have hrest_smooth : TangentSmoothAt (fun b : M => ∑ i ∈ t, Y i b) x :=
      tangentSmoothAt_finset_sum t Y hYrest
    have h_pi_eq : (fun b : M => ∑ i ∈ insert j t, Y i b)
        = ((Y j) + (fun b : M => ∑ i ∈ t, Y i b)) := by
      funext b
      show ∑ i ∈ insert j t, Y i b = Y j b + ∑ i ∈ t, Y i b
      rw [Finset.sum_insert hjt]
    rw [h_pi_eq,
        covDeriv_add_field X (Y j) (fun b => ∑ i ∈ t, Y i b) x hYj hrest_smooth,
        ih hYrest, Finset.sum_insert hjt]

/-- **Hadamard bridge** at a vanishing section: for `Z, U : SmoothVectorField I M`
with `U x = 0`, $\nabla_v (b \mapsto \nabla_{U(b)} Z(b))(x) = \nabla_{(\nabla_v U)} Z(x)$.

Proof via Hadamard expansion `U b = ∑_j u_j b • basis j` against
`stdOrthonormalBasis ℝ E`; scalar coefficients vanish at `x` so Leibniz
products lose their first term. -/
private theorem covDeriv_apply_smooth_section_at_zero
    [IsManifold I 2 M]
    (Z U : SmoothVectorField I M) (x : M) (v : E)
    (hU0 : U.toFun x = (0 : TangentSpace I x)) :
    covDerivAt (I := I) (M := M)
        (fun b : M => covDerivAt (I := I) (M := M) Z.toFun b (U.toFun b)) x v
      = covDerivAt (I := I) (M := M) Z.toFun x
          (covDerivAt (I := I) (M := M) U.toFun x v) := by
  sorry

/-- **Diagonal tensoriality bridge**: for `Z, V : SmoothVectorField I M`,
$(\nabla^2 Z)(V, V)(x) = (\nabla^2 Z)(V x, V x)$ at `x`. -/
private theorem secondCovDerivSection_diagonal_eq_secondCovDerivAt
    [IsManifold I 2 M]
    (Z V : SmoothVectorField I M) (x : M) :
    secondCovDerivSection (I := I) (M := M) Z.toFun V.toFun V.toFun x
      = secondCovDerivAt (I := I) (M := M) Z.toFun x (V.toFun x) (V.toFun x) := by
  let constV : SmoothVectorField I M :=
    SmoothVectorField.const (I := I) (M := M) (V.toFun x : E)
  let U : SmoothVectorField I M := V - constV
  have hU0 : U.toFun x = (0 : TangentSpace I x) := by
    show V.toFun x - constV.toFun x = (0 : TangentSpace I x)
    have h_constV : constV.toFun x = V.toFun x := rfl
    rw [h_constV]; exact sub_self _
  have hV_smooth : TangentSmoothAt V.toFun x := V.smoothAt x
  have hConstV_smooth : TangentSmoothAt constV.toFun x := constV.smoothAt x
  have hZV_smooth : TangentSmoothAt
      (fun b : M => covDerivAt (I := I) (M := M) Z.toFun b (V.toFun b)) x :=
    leviCivitaConnection_smoothAt_smoothVF_dir V Z x
  have hZv_smooth : TangentSmoothAt
      (fun b : M => covDerivAt (I := I) (M := M) Z.toFun b (constV.toFun b)) x :=
    leviCivitaConnection_smoothAt_smoothVF_dir constV Z x
  have h_bridge :=
    covDeriv_apply_smooth_section_at_zero (I := I) (M := M) Z U x (V.toFun x : E) hU0
  have h_pi_section :
      ((fun b : M => covDerivAt Z.toFun b (V.toFun b))
        - (fun b : M => covDerivAt Z.toFun b (constV.toFun b)))
        = (fun b : M => covDerivAt Z.toFun b (U.toFun b)) := by
    funext b
    show covDerivAt Z.toFun b (V.toFun b) - covDerivAt Z.toFun b (constV.toFun b)
        = covDerivAt Z.toFun b (U.toFun b)
    rw [show U.toFun b = V.toFun b - constV.toFun b from rfl,
        (covDerivAt Z.toFun b).map_sub]
  have h_pi_U : V.toFun - constV.toFun = U.toFun := by
    funext b; rfl
  have h_section_diff :
      covDerivAt (fun b : M => covDerivAt Z.toFun b (V.toFun b)) x (V.toFun x)
        - covDerivAt (fun b : M => covDerivAt Z.toFun b (constV.toFun b)) x
            (V.toFun x)
        = covDerivAt (fun b : M => covDerivAt Z.toFun b (U.toFun b)) x
            (V.toFun x) := by
    have h := covDeriv_sub_field (fun _ : M => V.toFun x)
      (fun b : M => covDerivAt Z.toFun b (V.toFun b))
      (fun b : M => covDerivAt Z.toFun b (constV.toFun b)) x
      hZV_smooth hZv_smooth
    rw [h_pi_section] at h
    exact h.symm
  have h_dir_diff :
      covDerivAt V.toFun x (V.toFun x) - covDerivAt constV.toFun x (V.toFun x)
        = covDerivAt U.toFun x (V.toFun x) := by
    have h := covDeriv_sub_field (fun _ : M => V.toFun x) V.toFun constV.toFun x
      hV_smooth hConstV_smooth
    rw [h_pi_U] at h
    exact h.symm
  have hCLM_sub :
      covDerivAt Z.toFun x (covDerivAt V.toFun x (V.toFun x))
        - covDerivAt Z.toFun x (covDerivAt constV.toFun x (V.toFun x))
        = covDerivAt Z.toFun x (covDerivAt U.toFun x (V.toFun x)) := by
    rw [← (covDerivAt Z.toFun x).map_sub, h_dir_diff]
  show covDerivAt (fun b : M => covDerivAt Z.toFun b (V.toFun b)) x (V.toFun x)
        - covDerivAt Z.toFun x (covDerivAt V.toFun x (V.toFun x))
      = covDerivAt (fun b : M => covDerivAt Z.toFun b (constV.toFun b)) x
            (V.toFun x)
        - covDerivAt Z.toFun x (covDerivAt constV.toFun x (V.toFun x))
  have h_zero :
      covDerivAt (fun b : M => covDerivAt Z.toFun b (U.toFun b)) x (V.toFun x)
        - covDerivAt Z.toFun x (covDerivAt U.toFun x (V.toFun x)) = 0 := by
    rw [h_bridge]; exact sub_self _
  have key :
      (covDerivAt (fun b : M => covDerivAt Z.toFun b (V.toFun b)) x (V.toFun x)
          - covDerivAt Z.toFun x (covDerivAt V.toFun x (V.toFun x)))
      - (covDerivAt (fun b : M => covDerivAt Z.toFun b (constV.toFun b)) x
            (V.toFun x)
          - covDerivAt Z.toFun x (covDerivAt constV.toFun x (V.toFun x))) = 0 := by
    have h_rearrange :
        (covDerivAt (fun b : M => covDerivAt Z.toFun b (V.toFun b)) x (V.toFun x)
            - covDerivAt Z.toFun x (covDerivAt V.toFun x (V.toFun x)))
        - (covDerivAt (fun b : M => covDerivAt Z.toFun b (constV.toFun b)) x
              (V.toFun x)
            - covDerivAt Z.toFun x (covDerivAt constV.toFun x (V.toFun x)))
        = (covDerivAt (fun b : M => covDerivAt Z.toFun b (V.toFun b)) x (V.toFun x)
            - covDerivAt (fun b : M => covDerivAt Z.toFun b (constV.toFun b)) x
                (V.toFun x))
          - (covDerivAt Z.toFun x (covDerivAt V.toFun x (V.toFun x))
            - covDerivAt Z.toFun x (covDerivAt constV.toFun x (V.toFun x))) := by
      abel
    rw [h_rearrange, h_section_diff, hCLM_sub]; exact h_zero
  exact sub_eq_zero.mp key

/-! ### Heart-of-Bochner sum identity (final assembly)

Closes the narrowed PRE-PAPER sorry `sum_inner_secondCovDerivAt_grad_smoothOrthoFrame`
in `Bochner.lean` (downstream version with `h_strict` hypothesis), via:
* diagonal bridge → `secondCovDerivSection` form,
* per-summand assembled identity (`bochner_per_summand_assembled`),
* sum over `i` distributing into R-term (Ricci), mfderiv-Hess-term
  (gradient of the scalar Laplacian), and cov-Hess-term (vanishes). -/

/-- **Heart-of-Bochner sum identity** (unconditional, requires strict
interior). Diagonal of the second covariant derivative against
`smoothOrthoFrame · x`, contracted with `∇f`, equals
`g(∇f, ∇(Δ_g f)) + Ric(∇f, ∇f)`. -/
theorem sum_inner_secondCovDerivAt_grad_smoothOrthoFrame_unconditional
    [IsManifold I 2 M] [T2Space M]
    (f : M → ℝ) (x : M)
    (h_strict : extChartAt I x x ∈ interior (Set.range I))
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (h_grad : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
              (fun y => (⟨y, manifoldGradient (I := I) f y⟩ : TangentBundle I M))) :
    ∑ i, metricInner x
        (secondCovDerivAt (I := I) (M := M) (manifoldGradient (I := I) f) x
          (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x i x)
          (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x i x))
        (manifoldGradient (I := I) f x)
      = metricInner x (manifoldGradient (I := I) f x)
            (manifoldGradient (I := I) (Δ_g[I] f) x)
        + Ric_g((manifoldGradient (I := I) f x),
                (manifoldGradient (I := I) f x)) x := by
  classical
  let gradF : SmoothVectorField I M :=
    { toFun := manifoldGradient (I := I) f, smooth := h_grad }
  let Bi : Fin (Module.finrank ℝ E) → SmoothVectorField I M := fun i =>
    { toFun := Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x i
      smooth := Riemannian.Tensor.smoothOrthoFrame_smooth (I := I) hm.metric x i }
  have h_interior : extChartAt I x x ∈ closure (interior (Set.range I)) :=
    subset_closure h_strict
  -- Abbreviations.
  set Rterm : Fin (Module.finrank ℝ E) → ℝ := fun i =>
    metricInner x
      (riemannCurvature (Bi i).toFun gradF.toFun gradF.toFun x)
      ((Bi i).toFun x) with hRterm_def
  set Mterm : Fin (Module.finrank ℝ E) → ℝ := fun i =>
    mfderiv I 𝓘(ℝ, ℝ)
      (fun y : M => hessianBilin (I := I) f y ((Bi i).toFun y)
        ((Bi i).toFun y)) x (gradF.toFun x) with hMterm_def
  set Hterm : Fin (Module.finrank ℝ E) → ℝ := fun i =>
    hessianBilin (I := I) f x ((Bi i).toFun x)
      (covDeriv gradF.toFun (Bi i).toFun x) with hHterm_def
  -- Per-summand: bridge → secondCovDerivSection → bochner_per_summand_assembled.
  have h_per_summand : ∀ i,
      metricInner x
          (secondCovDerivAt gradF.toFun x ((Bi i).toFun x) ((Bi i).toFun x))
          (gradF.toFun x)
        = Rterm i + Mterm i - 2 * Hterm i := by
    intro i
    rw [show (secondCovDerivAt gradF.toFun x ((Bi i).toFun x) ((Bi i).toFun x))
        = secondCovDerivSection gradF.toFun (Bi i).toFun (Bi i).toFun x from
        (secondCovDerivSection_diagonal_eq_secondCovDerivAt gradF (Bi i) x).symm]
    show metricInner x
          (covDeriv (Bi i).toFun (covDeriv (Bi i).toFun gradF.toFun) x
            - covDerivAt gradF.toFun x (covDeriv (Bi i).toFun (Bi i).toFun x))
          (gradF.toFun x) = _
    rw [metricInner_sub_left]
    show _ = Rterm i + Mterm i - 2 * Hterm i
    rw [hRterm_def, hMterm_def, hHterm_def]
    exact bochner_per_summand_assembled (I := I) f (Bi i) gradF x h_strict hf h_grad
  -- Sum the per-summand identity.
  have h_sum_eq :
      (∑ i, metricInner x
          (secondCovDerivAt gradF.toFun x ((Bi i).toFun x) ((Bi i).toFun x))
          (gradF.toFun x))
        = (∑ i, Rterm i) + (∑ i, Mterm i) - 2 * (∑ i, Hterm i) := by
    calc (∑ i, metricInner x
            (secondCovDerivAt gradF.toFun x ((Bi i).toFun x) ((Bi i).toFun x))
            (gradF.toFun x))
        = ∑ i, (Rterm i + Mterm i - 2 * Hterm i) :=
          Finset.sum_congr rfl (fun i _ => h_per_summand i)
      _ = (∑ i, (Rterm i + Mterm i)) - ∑ i, (2 * Hterm i) := by
          rw [Finset.sum_sub_distrib]
      _ = ((∑ i, Rterm i) + ∑ i, Mterm i) - ∑ i, (2 * Hterm i) := by
          rw [Finset.sum_add_distrib]
      _ = ((∑ i, Rterm i) + ∑ i, Mterm i) - 2 * (∑ i, Hterm i) := by
          rw [← Finset.mul_sum]
  rw [h_sum_eq]
  -- Identify ∑ Rterm = Ric.
  have h_R_eq : (∑ i, Rterm i) = Ric_g(manifoldGradient (I := I) f x, gradF.toFun x) x :=
    heart_curvature_orthonormal_sum_eq_ricci (I := I) f gradF x h_interior h_grad
  -- Identify ∑ Hterm = 0.
  have h_H_eq : (∑ i, Hterm i) = 0 :=
    sum_hessianBilin_smoothOrthoFrame_cov_eq_zero (I := I) f gradF x
      h_interior hf h_grad
  -- Identify ∑ Mterm = mfderiv (Δ_g f) x (∇f x) = g(∇(Δ_g f), ∇f x).
  -- Smoothness of each summand `b ↦ Hess f(Bᵢ b, Bᵢ b)` at x.
  have h_each_hess_smooth : ∀ i,
      MDifferentiableAt I 𝓘(ℝ, ℝ)
          (fun y : M => hessianBilin (I := I) f y ((Bi i).toFun y)
            ((Bi i).toFun y)) x := by
    intro i; sorry
  have h_M_factor :
      (∑ i, Mterm i)
        = (mfderiv I 𝓘(ℝ, ℝ)
            (fun b : M => ∑ i, hessianBilin (I := I) f b ((Bi i).toFun b)
              ((Bi i).toFun b)) x (gradF.toFun x) : ℝ) := by
    rw [hMterm_def]
    exact (mfderiv_finset_sum_apply Finset.univ
      (fun i b => hessianBilin (I := I) f b ((Bi i).toFun b) ((Bi i).toFun b)) x
      (gradF.toFun x) (fun i _ => h_each_hess_smooth i)).symm
  have h_eventuallyEq :
      (fun b : M => ∑ i, hessianBilin (I := I) f b ((Bi i).toFun b)
            ((Bi i).toFun b))
        =ᶠ[𝓝 x] (fun b : M => Operators.scalarLaplacian (I := I) (M := M) f b) :=
    sum_hessianBilin_smoothOrthoFrame_eventuallyEq_laplacian (I := I) f x
  have h_M_to_lap :
      (mfderiv I 𝓘(ℝ, ℝ)
          (fun b : M => ∑ i, hessianBilin (I := I) f b ((Bi i).toFun b)
            ((Bi i).toFun b)) x (gradF.toFun x) : ℝ)
        = (mfderiv I 𝓘(ℝ, ℝ) (Δ_g[I] f : M → ℝ) x (gradF.toFun x) : ℝ) := by
    congr 1
    exact Filter.EventuallyEq.mfderiv_eq h_eventuallyEq
  -- Gradient-mfderiv duality: `mfderiv g x v = ⟨∇g x, v⟩_g`.
  have h_grad_dual :
      (mfderiv I 𝓘(ℝ, ℝ) (Δ_g[I] f : M → ℝ) x (gradF.toFun x) : ℝ)
        = metricInner x (manifoldGradient (I := I) (Δ_g[I] f) x) (gradF.toFun x) :=
    (manifoldGradient_inner_eq (Δ_g[I] f) x (gradF.toFun x)).symm
  -- Combine.
  rw [h_R_eq, h_H_eq, h_M_factor, h_M_to_lap, h_grad_dual,
      metricInner_comm x (manifoldGradient (I := I) (Δ_g[I] f) x)]
  ring

/-- **G — heart-of-Bochner reduction (unconditional, strict interior)**:
$\langle \Delta_\nabla \nabla f, \nabla f\rangle_g
= \langle \nabla f, \nabla(\Delta_g f)\rangle_g + \mathrm{Ric}(\nabla f, \nabla f)$.

Unconditional version of `connectionLaplacian_grad_eq_grad_laplacian_add_ricci`
(which is conditional on the narrowed PRE-PAPER sorry in `Bochner.lean`),
proved via `sum_inner_secondCovDerivAt_grad_smoothOrthoFrame_unconditional`
+ existing outer assembly. Requires strict interior (vs closure interior). -/
theorem connectionLaplacian_grad_eq_grad_laplacian_add_ricci_unconditional
    [IsManifold I 2 M] [T2Space M]
    (f : M → ℝ) (x : M)
    (h_strict : extChartAt I x x ∈ interior (Set.range I))
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (h_grad : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
              (fun y => (⟨y, manifoldGradient (I := I) f y⟩ : TangentBundle I M))) :
    ⟪connectionLaplacian (grad_g[I] f) x, (grad_g[I] f) x⟫_g
      = ⟪(grad_g[I] f) x, (grad_g[I] (Δ_g[I] f)) x⟫_g
        + Ric_g((grad_g[I] f) x, (grad_g[I] f) x) x := by
  have h_interior : extChartAt I x x ∈ closure (interior (Set.range I)) :=
    subset_closure h_strict
  show metricInner x
        (connectionLaplacian (I := I) (M := M) (manifoldGradient (I := I) f) x)
        (manifoldGradient (I := I) f x)
      = metricInner x (manifoldGradient (I := I) f x)
          (manifoldGradient (I := I) (Δ_g[I] f) x)
        + Ric_g((manifoldGradient (I := I) f x),
                (manifoldGradient (I := I) f x)) x
  rw [connectionLaplacian_eq_sum_secondCovDerivAt]
  -- The trace identification at `x` only depends on the basis at `x`, and
  -- `smoothOrthoFrame · x` is g-orthonormal at `x` (Stage 5). Use the
  -- stored bilinear form `B` to apply `Tensor.sum_diagonal_smoothOrthoFrame_eq_std`.
  let h_const_dir : ∀ w : TangentSpace I x,
      TangentSmoothAt
        (fun y : M => covDerivAt (manifoldGradient (I := I) f) y w) x :=
    fun w => leviCivitaConnection_smoothAt_const_dir
      ⟨manifoldGradient (I := I) f, h_grad⟩ (w : E) x
  set B' : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ
      (fun v w => metricInner x
        (secondCovDerivAt (I := I) (M := M)
          (manifoldGradient (I := I) f) x v w)
        (manifoldGradient (I := I) f x))
      (fun v₁ v₂ w => by
        show metricInner x
            (secondCovDerivAt (manifoldGradient (I := I) f) x (v₁ + v₂) w)
            (manifoldGradient (I := I) f x)
          = metricInner x
              (secondCovDerivAt (manifoldGradient (I := I) f) x v₁ w)
              (manifoldGradient (I := I) f x)
            + metricInner x
                (secondCovDerivAt (manifoldGradient (I := I) f) x v₂ w)
                (manifoldGradient (I := I) f x)
        rw [secondCovDerivAt_add_left, metricInner_add_left])
      (fun c v w => by
        show metricInner x
            (secondCovDerivAt (manifoldGradient (I := I) f) x (c • v) w)
            (manifoldGradient (I := I) f x)
          = c • metricInner x
              (secondCovDerivAt (manifoldGradient (I := I) f) x v w)
              (manifoldGradient (I := I) f x)
        rw [secondCovDerivAt_smul_left, metricInner_smul_left]; rfl)
      (fun v w₁ w₂ => by
        show metricInner x
            (secondCovDerivAt (manifoldGradient (I := I) f) x v (w₁ + w₂))
            (manifoldGradient (I := I) f x)
          = metricInner x
              (secondCovDerivAt (manifoldGradient (I := I) f) x v w₁)
              (manifoldGradient (I := I) f x)
            + metricInner x
                (secondCovDerivAt (manifoldGradient (I := I) f) x v w₂)
                (manifoldGradient (I := I) f x)
        rw [secondCovDerivAt_add_right (h_smooth_dir := h_const_dir),
            metricInner_add_left])
      (fun c v w => by
        show metricInner x
            (secondCovDerivAt (manifoldGradient (I := I) f) x v (c • w))
            (manifoldGradient (I := I) f x)
          = c • metricInner x
              (secondCovDerivAt (manifoldGradient (I := I) f) x v w)
              (manifoldGradient (I := I) f x)
        rw [secondCovDerivAt_smul_right
              (h_smooth_dir := h_const_dir w),
            metricInner_smul_left]; rfl) with hB'_def
  have h_basis_swap :=
    Riemannian.Tensor.sum_diagonal_smoothOrthoFrame_eq_std (I := I) x B'
  rw [hB'_def] at h_basis_swap
  simp only [LinearMap.mk₂_apply] at h_basis_swap
  -- `h_basis_swap : ∑_i metricInner x (secondCovDerivAt ... (smoothOrthoFrame i x))
  --                                    ... ∇f x
  --              = ∑_i metricInner x (secondCovDerivAt ... (e_std i)) ... ∇f x`.
  -- Pull sum out of `metricInner` (= `⟪·,·⟫_ℝ` def-eq + `sum_inner`).
  have h_pull :
      metricInner x
          (∑ i, secondCovDerivAt (I := I) (M := M)
            (manifoldGradient (I := I) f) x
            ((stdOrthonormalBasis ℝ (TangentSpace I x)) i)
            ((stdOrthonormalBasis ℝ (TangentSpace I x)) i))
          (manifoldGradient (I := I) f x)
        = ∑ i, metricInner x
            (secondCovDerivAt (I := I) (M := M)
              (manifoldGradient (I := I) f) x
              ((stdOrthonormalBasis ℝ (TangentSpace I x)) i)
              ((stdOrthonormalBasis ℝ (TangentSpace I x)) i))
            (manifoldGradient (I := I) f x) := by
    exact sum_inner Finset.univ
      (fun i => secondCovDerivAt (I := I) (M := M)
        (manifoldGradient (I := I) f) x
        ((stdOrthonormalBasis ℝ (TangentSpace I x)) i)
        ((stdOrthonormalBasis ℝ (TangentSpace I x)) i))
      (manifoldGradient (I := I) f x)
  -- Convert goal from `⟪·,·⟫_g` notation to `metricInner` form, then apply `h_pull`.
  show metricInner x
        (∑ i, secondCovDerivAt (I := I) (M := M)
          (manifoldGradient (I := I) f) x
          ((stdOrthonormalBasis ℝ (TangentSpace I x)) i)
          ((stdOrthonormalBasis ℝ (TangentSpace I x)) i))
        (manifoldGradient (I := I) f x)
      = metricInner x (manifoldGradient (I := I) f x)
          (manifoldGradient (I := I) (Δ_g[I] f) x)
        + Ric_g((manifoldGradient (I := I) f x),
                (manifoldGradient (I := I) f x)) x
  rw [h_pull]
  -- Convert `∑_i ... e_std i ...` to `∑_i ... smoothOrthoFrame i x ...`.
  rw [← h_basis_swap]
  exact sum_inner_secondCovDerivAt_grad_smoothOrthoFrame_unconditional
    f x h_strict hf h_grad

/-- **Bochner–Weitzenböck identity (unconditional, strict interior)**.
Unconditional version of `bochner_weitzenboeck` in `Bochner.lean`
(which is conditional on the narrowed PRE-PAPER sorry).

$$\tfrac{1}{2}\,\Delta_g\,|\nabla f|_g^2
  = |\nabla^2 f|_g^2
    + \langle \nabla f, \nabla\,\Delta_g f\rangle_g
    + \mathrm{Ric}(\nabla f, \nabla f).$$ -/
theorem bochner_weitzenboeck_unconditional
    [IsManifold I 2 M] [T2Space M]
    (f : M → ℝ) (x : M)
    (h_strict : extChartAt I x x ∈ interior (Set.range I))
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (h_grad : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
              (fun y => (⟨y, manifoldGradient (I := I) f y⟩ : TangentBundle I M))) :
    (1 / 2 : ℝ) * (Δ_g[I] ‖grad_g[I] f‖²_g) x =
      ‖hess_g[I] f‖²_g x
      + ⟪(grad_g[I] f) x, (grad_g[I] (Δ_g[I] f)) x⟫_g
      + Ric_g((grad_g[I] f) x, (grad_g[I] f) x) x := by
  rw [leibniz_trace_reduction f x h_grad,
      connectionLaplacian_grad_eq_grad_laplacian_add_ricci_unconditional
        f x h_strict hf h_grad]
  abel

end Operators
end Riemannian
