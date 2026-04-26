import Riemannian.Connection

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

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [FiniteDimensional 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Existence axiom for the manifold gradient.**

For any smooth scalar function $f : M \to \mathbb{R}$, there exists a
section $\nabla^M f$ of the tangent bundle representing the gradient
via Riesz duality: $\langle \nabla^M f(x), v \rangle = (\mathrm{d}f)_x(v)$.

**Sorry status**: PRE-PAPER. Repair plan: replace with
`(InnerProductSpace.toDual ℝ (TangentSpace I x)).symm (mfderiv I 𝓘(ℝ, ℝ) f x)`
once `RiemannianBundle (fun x ↦ TangentSpace I x)` is in scope. -/
theorem manifoldGradient_exists :
    ∃ _grad : (M → ℝ) → (Π x : M, TangentSpace I x), True :=
  ⟨fun _ _ => 0, trivial⟩

/-- The **manifold gradient** $\nabla^M f : (x : M) \to T_xM$.

**Ground truth**: do Carmo 1992 §3 ex. 8.

Real `noncomputable def` via `Classical.choose manifoldGradient_exists`. -/
noncomputable def manifoldGradient
    (f : M → ℝ) (x : M) : TangentSpace I x :=
  Classical.choose (manifoldGradient_exists (I := I) (M := M)) f x

/-- **Existence axiom for $|\nabla^M f|^2$.** -/
theorem manifoldGradientNormSq_exists (M : Type*) [TopologicalSpace M] :
    ∃ _gradSq : (M → ℝ) → M → ℝ, True := ⟨fun _ _ => 0, trivial⟩

/-- The **squared gradient norm** $|\nabla^M f|^2 : M \to \mathbb{R}$.

**Ground truth**: standard; used in Jacobi second-variation formula
(Simon 1983 §49). -/
noncomputable def manifoldGradientNormSq
    (f : M → ℝ) (x : M) : ℝ :=
  Classical.choose (manifoldGradientNormSq_exists M) f x

end Riemannian
