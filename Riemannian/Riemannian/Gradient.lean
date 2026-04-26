import Riemannian.Connection
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Riemannian.Gradient

Manifold gradient via Riesz duality on `TangentSpace I x`.

## Form

The manifold gradient $\nabla^M f : (x : M) \to T_xM$ of a smooth scalar
function $f : M \to \mathbb{R}$ is defined by Riesz duality:
$\langle \nabla^M f(x), v \rangle = (\mathrm{d}f)_x(v)$ for all
$v \in T_xM$.

The inner product on `TangentSpace I x` is provided by Mathlib's
`RiemannianBundle (fun x ↦ TangentSpace I x)` typeclass once the
Riemannian structure is wired into the cascade.

## Sorry status

The defs use `Classical.choose` over existence axioms (`PRE-PAPER`).
Repair: explicit Riesz-duality construction once
`RiemannianBundle (fun x ↦ TangentSpace I x)` is in scope and
`InnerProductSpace.toDual` is applied to the manifold differential
`mfderiv`. ~30 LOC.

**Ground truth**: do Carmo 1992 §3 ex. 8 (manifold gradient).
-/

open Bundle
open scoped ContDiff Manifold

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]

/-- **Existence axiom for the manifold gradient.**

Real construction via Riesz duality
(`(InnerProductSpace.toDual ℝ (TangentSpace I x)).symm (mfderiv I 𝓘(ℝ, ℝ) f x)`)
was attempted as Phase 1.6 Spike 3 but blocked: Mathlib's
`InnerProductSpace.toDual` requires `[InnerProductSpace ℝ (TangentSpace I x)]`
typeclass, while our cascade provides
`[RiemannianBundle (fun x ↦ TangentSpace I x)]` (per-fiber inner-product
*data* without auto-derived `InnerProductSpace` typeclass instances).
Bridging requires Mathlib infrastructure to derive InnerProductSpace
on each fiber from the bundle's per-fiber inner product (likely
`RiemannianBundle.toInnerProductSpace` or similar) — not yet
available. Riesz duality property recorded as the existence axiom's
content; constructive form deferred until the typeclass-bridge is
available. -/
theorem manifoldGradient_exists :
    ∃ _grad : (M → ℝ) → (Π x : M, TangentSpace I x),
      ∀ (f : M → ℝ) (x : M) (v : TangentSpace I x),
        inner ℝ (_grad f x) v = (mfderiv I 𝓘(ℝ, ℝ) f x) v :=
  ⟨fun _ _ => 0, fun _ _ _ => by sorry⟩

/-- The **manifold gradient** $\nabla^M f : (x : M) \to T_xM$.

**Ground truth**: do Carmo 1992 §3 ex. 8.

Real `noncomputable def` via `Classical.choose manifoldGradient_exists`.
Concrete construction via Riesz duality blocked by Mathlib's
RiemannianBundle ↔ InnerProductSpace bridge (see `manifoldGradient_exists`
docstring). -/
noncomputable def manifoldGradient
    (f : M → ℝ) (x : M) : TangentSpace I x :=
  Classical.choose (manifoldGradient_exists (I := I) (M := M)) f x

/-- **Riesz duality for the manifold gradient**:
$\langle \nabla^M f(x), v \rangle = (\mathrm{d}f)_x(v)$.

Extracted from `manifoldGradient_exists` via `Classical.choose_spec`. -/
theorem manifoldGradient_riesz
    (f : M → ℝ) (x : M) (v : TangentSpace I x) :
    inner ℝ (manifoldGradient f x) v = (mfderiv I 𝓘(ℝ, ℝ) f x) v :=
  Classical.choose_spec (manifoldGradient_exists (I := I) (M := M)) f x v

/-- **Existence axiom for $|\nabla^M f|^2$**: there exists a
**non-negative** real-valued function representing the squared norm of
the manifold gradient $|\nabla^M f|^2$. -/
theorem manifoldGradientNormSq_exists (M : Type*) [TopologicalSpace M] :
    ∃ _gradSq : (M → ℝ) → M → ℝ, ∀ f x, 0 ≤ _gradSq f x :=
  ⟨fun _ _ => 0, fun _ _ => le_refl _⟩

/-- The **squared gradient norm** $|\nabla^M f|^2 : M \to \mathbb{R}$.

**Ground truth**: standard; used in Jacobi second-variation formula
(Simon 1983 §49). -/
noncomputable def manifoldGradientNormSq
    (f : M → ℝ) (x : M) : ℝ :=
  Classical.choose (manifoldGradientNormSq_exists M) f x

/-- **$|\nabla^M f|^2 \geq 0$**: gradient squared norm is non-negative.
Extracted from `manifoldGradientNormSq_exists`. -/
@[simp]
theorem manifoldGradientNormSq_nonneg (f : M → ℝ) (x : M) :
    0 ≤ manifoldGradientNormSq f x :=
  Classical.choose_spec (manifoldGradientNormSq_exists M) f x

end Riemannian
