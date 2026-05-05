import Mathlib.Analysis.Calculus.VectorField

/-!
# Scalar Hessian–Lie identity — flat version

For a $C^2$ vector-valued function `f : E → F` and $C^1$ vector fields
`V, W : E → E` on a normed space `E`, the iterated directional
derivatives satisfy

  $$D_{V}(D_{W}f) - D_{W}(D_{V}f) = D_{[V,W]}f$$

with `[V,W]` the flat Lie bracket of vector fields.

## Conventions

`fderiv ℝ f x v` denotes $D_v f(x)$ (Mathlib convention). The function
`y ↦ fderiv ℝ f y (V y)` is $D_V f$ as a function of basepoint.

## Variants

* `Riemannian.flat_hessianLie_apply` — `fderiv` form, on full nbhds.
* `Riemannian.flat_hessianLieWithin_apply` — `fderivWithin s` form,
  for chart-pullback to `s = range I`.

## Proof technique

Bilinear-pairing product rule (`fderiv_clm_apply`) expresses each
iterated `fderiv` as `(fderiv² f) ∘L V + (fderiv f) ∘L (fderiv V)`.
Symmetry of the second derivative (Schwarz, `isSymmSndFDerivAt`) cancels
the cross terms, leaving `fderiv f x` applied to
`fderiv W x (V x) - fderiv V x (W x) = lieBracket V W x`.

**Ground truth**: do Carmo 1992 §0 Lemma 5.2; Lee 2013 *Smooth
Manifolds* Proposition 8.30. -/

open VectorField
open scoped ContDiff

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Flat scalar Hessian–Lie identity** (univ form).
    `D_V(D_W f) - D_W(D_V f) = D_{[V,W]} f` at `x`. -/
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
  -- Bilinear-pairing product rule applied to both iterated derivatives.
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
  -- Schwarz cancels the cross-D² terms.
  rw [(hf.isSymmSndFDerivAt (by simp) (V x) (W x)).symm,
      lieBracket_eq, (fderiv ℝ f x).map_sub]
  abel

/-- **Flat scalar Hessian–Lie identity, `Within` form** on a unique-diff
set `s` (used for chart-pullback with `s = range I`). -/
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

end Riemannian
