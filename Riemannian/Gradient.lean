import Riemannian.Connection
import Riemannian.InnerProductBridge
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
open scoped ContDiff Manifold Bundle

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]

/-- The **manifold gradient** $\nabla^M f : (x : M) \to T_xM$, defined
via **Riesz duality** on the tangent space.

Concretely: $\nabla^M f(x)$ is the unique $v \in T_xM$ such that
$\langle v, w \rangle = (\mathrm{d}f)_x(w)$ for all $w \in T_xM$.
Implemented via Mathlib's `InnerProductSpace.toDual.symm` applied to
the manifold differential `mfderiv I 𝓘(ℝ, ℝ) f x`.

The `[InnerProductSpace ℝ (TangentSpace I x)]` typeclass is provided
by `Riemannian.InnerProductBridge.instInnerProductSpaceTangentSpace`,
the framework's self-built bridge from
`[RiemannianBundle (fun x ↦ TangentSpace I x)]`.

**Ground truth**: do Carmo 1992 §3 ex. 8.

Real `noncomputable def` (no `Classical.choose` over an existence
axiom) — Riesz duality is a constructive bijection in Mathlib. -/
noncomputable def manifoldGradient
    (f : M → ℝ) (x : M) : TangentSpace I x :=
  (InnerProductSpace.toDual ℝ (TangentSpace I x)).symm (mfderiv I 𝓘(ℝ, ℝ) f x)

/-- **Riesz duality for the manifold gradient**:
$\langle \nabla^M f(x), v \rangle = (\mathrm{d}f)_x(v)$.

Holds by construction of `manifoldGradient` via
`InnerProductSpace.toDual.symm`. -/
theorem manifoldGradient_riesz
    (f : M → ℝ) (x : M) (v : TangentSpace I x) :
    inner ℝ (manifoldGradient f x) v = (mfderiv I 𝓘(ℝ, ℝ) f x) v := by
  rw [manifoldGradient, InnerProductSpace.toDual_symm_apply]
  rfl

/-- The **squared gradient norm** $|\nabla^M f|^2 : M \to \mathbb{R}$,
defined as $\|\nabla^M f(x)\|^2$ using the inner-product norm on
`TangentSpace I x` (provided by the bridge instances in
`Riemannian.InnerProductBridge`).

**Ground truth**: standard; used in Jacobi second-variation formula
(Simon 1983 §49).

Real `noncomputable def` (no `Classical.choose`) — direct
constructive form via `‖_‖^2`. -/
noncomputable def manifoldGradientNormSq
    (I' : ModelWithCorners ℝ E H)
    [ChartedSpace H M] [IsManifold I' ∞ M]
    [Bundle.RiemannianBundle (fun x : M => TangentSpace I' x)]
    (f : M → ℝ) (x : M) : ℝ :=
  ‖(manifoldGradient (I := I') f x : TangentSpace I' x)‖ ^ 2

/-- **$|\nabla^M f|^2 \geq 0$**: gradient squared norm is non-negative.
Direct from `sq_nonneg` on `‖manifoldGradient f x‖`. -/
@[simp]
theorem manifoldGradientNormSq_nonneg
    (I' : ModelWithCorners ℝ E H)
    [ChartedSpace H M] [IsManifold I' ∞ M]
    [Bundle.RiemannianBundle (fun x : M => TangentSpace I' x)]
    (f : M → ℝ) (x : M) :
    0 ≤ manifoldGradientNormSq I' f x :=
  sq_nonneg _

end Riemannian
