import OpenGALib.Riemannian.Operators.Bochner

/-!
# Per-summand chain of the heart-of-Bochner identity

This file ports the per-summand chain that drives the unconditional
discharge of the heart-of-Bochner inner-product identity
(`hInner_discharge` in external `differential-geometry`).

For a smooth scalar `f : M → ℝ`, smooth `B, W : SmoothVectorField I M`,
and `x : M` in the strict interior of `range I`:

* `heart_per_summand_swap` — Hess-sym swap form (step (d) of the textbook
  derivation):
  $$g_x(\nabla_{B} \nabla_B \nabla f, W) - g_x(\nabla_{\nabla_B B} \nabla f, W)
     = g_x(\nabla_{B} \nabla_W \nabla f, B) - g_x(\nabla_{\nabla_B W} \nabla f, B).$$

Closure path: two applications of `leviCivitaConnection_metric_compatible`
on the section pairs `(Q := ∇_B ∇f, W)` and `(P := ∇_W ∇f, B)` along the
direction `B x`, combined with the section-level Hessian symmetry
`hessianBilin_section_eventually_symm_of_strict_interior` to equate
the two mfderiv values at `x`, and pointwise `hessianBilin_symm` at `x`
to identify the cross-Christoffel terms.

This is the OpenGALib analog of external's `heart_per_summand_swap`
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

External reference: `heart_per_summand_swap` in
`differential-geometry/.../Bochner.lean:2828–2966`. -/
theorem heart_per_summand_swap
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

External reference: `heart_per_summand_riemann_form` in
`differential-geometry/.../Bochner.lean:2978–3076`. -/
theorem heart_per_summand_riemann_form
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

end Operators
end Riemannian
