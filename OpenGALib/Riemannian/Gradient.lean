import OpenGALib.Riemannian.Connection

/-!
# Manifold gradient

For a smooth scalar function $f : M \to \mathbb{R}$ on a Riemannian manifold
$(M, g)$, the **gradient** $\nabla^M f : (x : M) \to T_xM$ is the unique vector
field characterised by Riesz duality:
$$\langle \nabla^M f(x), v \rangle_g = (\mathrm{d}f)_x(v) \quad \forall v \in T_xM.$$

## Main definitions

* `manifoldGradient f x` — the gradient $\nabla^M f(x) \in T_xM$.

For the squared gradient norm $|\nabla^M f|^2$ as a scalar function on
$M$, use the polymorphic `‖grad_g[I] f‖²_g` (the section-level instance
of `Riemannian.MetricNormSq`).

## Main results

* `manifoldGradient_inner_eq` — the defining Riesz identity.

Reference: do Carmo §3 ex. 8.
-/

open Bundle
open scoped ContDiff Manifold Bundle Riemannian

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [hm : HasMetric I M]

/-- The **manifold gradient** $\nabla^M f(x) \in T_xM$, defined via Riesz duality
on the tangent space: the unique $v$ with $\langle v, w \rangle_g = (\mathrm{d}f)_x(w)$
for all $w$. -/
noncomputable def manifoldGradient
    (f : M → ℝ) (x : M) : TangentSpace I x :=
  metricRiesz x (mfderiv I 𝓘(ℝ, ℝ) f x)

/-- The manifold gradient `grad_g[I] f` as a section `x ↦ ∇^M f(x)`.
`I` is bracketed because `f : M → ℝ` does not expose the model with
corners to typeclass synthesis. -/
scoped[Riemannian] notation:max "grad_g[" I "] " f:max =>
  manifoldGradient (I := I) f

omit [CompleteSpace E] in
/-- $\langle \nabla^M f(x), v \rangle_g = (\mathrm{d}f)_x(v)$. -/
theorem manifoldGradient_inner_eq
    (f : M → ℝ) (x : M) (v : TangentSpace I x) :
    metricInner x (grad_g[I] f x) v = (mfderiv I 𝓘(ℝ, ℝ) f x) v :=
  metricRiesz_inner x (mfderiv I 𝓘(ℝ, ℝ) f x) v

end Riemannian
