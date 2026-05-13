import OpenGALib.Riemannian.Connection
import OpenGALib.Riemannian.Tensor.MusicalIso

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

omit [CompleteSpace E] in
/-- **Gradient smoothness propagation**: if a scalar function `g : M → ℝ`
is $C^\infty$, then its manifold gradient $\nabla^M g$ is $C^\infty$ as a
tangent bundle section.

Mathematically trivial in standard differential geometry — the gradient
is the composition of the smooth differential `mfderiv g` with the
smooth Riesz isomorphism (smooth because the Riemannian metric itself is
smooth). Used to discharge the automatic-by-textbook smoothness of the
gradient in headline theorems such as the Bochner–Weitzenböck identity
(`OpenGALib.Riemannian.Operators.Bochner`).

Closed via `Riemannian.Tensor.metricRiesz_section_contMDiffAt` (the framework
primitive from `Riemannian/Tensor/MusicalIso.lean`) applied at each point
with $\Phi := \mathrm{d}g$. The covector-section hypothesis (`mfderiv g y`
applied to chart-basis vectors is smooth on the base set) is discharged by
`Riemannian.Tensor.mfderiv_chartBasisVec_apply_contMDiffOn`, which uses the
chart-pullback identity $\mathrm{d}g(e_j) = \partial_j (g \circ \varphi^{-1}) \circ \varphi$
together with `[I.Boundaryless]` to make the smoothness domain equal the chart
base set (without `[I.Boundaryless]`, the identity holds only on the strict
interior of the chart target). -/
theorem manifoldGradient_smooth_of_smooth
    [InnerProductSpace ℝ E] [I.Boundaryless] [NeZero (Module.finrank ℝ E)]
    (g : M → ℝ) (hg : ContMDiff I 𝓘(ℝ, ℝ) ∞ g) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => (⟨y, manifoldGradient (I := I) g y⟩ : TangentBundle I M)) := by
  intro x
  have hx_base : x ∈ (trivializationAt E (TangentSpace I) x).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet (𝕜 := ℝ) (I := I) x]
    exact mem_chart_source H x
  have hΦ : ∀ j : Fin (Module.finrank ℝ E),
      ContMDiffOn I 𝓘(ℝ) ∞
        (fun y => (mfderiv I 𝓘(ℝ, ℝ) g y)
          (Riemannian.Tensor.chartBasisVecFiber (I := I) x j y))
        (trivializationAt E (TangentSpace I) x).baseSet := by
    intro j
    exact Riemannian.Tensor.mfderiv_chartBasisVec_apply_contMDiffOn
      (I := I) x hg j
  exact Riemannian.Tensor.metricRiesz_section_contMDiffAt
    (I := I) hm.metric x hx_base (Φ := fun y => mfderiv I 𝓘(ℝ, ℝ) g y) hΦ

end Riemannian
