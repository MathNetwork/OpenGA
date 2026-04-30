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

/-- Helper: directional derivative of a scalar/vector-valued function as
an `F`-typed value (avoids `TangentSpace 𝓘(ℝ, F) (f x)` basepoint
indirection in iterated forms). Definitionally equal to
`mfderiv I 𝓘(ℝ, F) f x v`. -/
@[reducible] noncomputable def mDirDeriv
    (f : M → F) (x : M) (v : TangentSpace I x) : F :=
  mfderiv I 𝓘(ℝ, F) f x v

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
  -- Goal: mfderiv I 𝓘(ℝ, F) (fun y => mfderiv I 𝓘(ℝ, F) f y (W y)) x (V x)
  --     - mfderiv I 𝓘(ℝ, F) (fun y => mfderiv I 𝓘(ℝ, F) f y (V y)) x (W x)
  --     = mfderiv I 𝓘(ℝ, F) f x (mlieBracket I V W x)
  sorry

end Riemannian
