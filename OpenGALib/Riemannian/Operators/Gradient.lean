import OpenGALib.Riemannian.Connection.LeviCivita
import OpenGALib.Riemannian.TensorBundle.MusicalIso
import OpenGALib.Riemannian.Util.Tangent.MfderivApplySection

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

/-- **Math.** The **manifold gradient** $\nabla^M f(x) \in T_xM$ via
Riesz duality: the unique $v$ with $\langle v, w \rangle_g = (\mathrm{d}f)_x(w)$
for all $w$. -/
noncomputable def manifoldGradient
    (g : RiemannianMetric I M)
    (f : M → ℝ) (x : M) : TangentSpace I x :=
  g.metricRiesz x (mfderiv I 𝓘(ℝ, ℝ) f x)

omit [CompleteSpace E] in
/-- **Math.** $\langle \nabla^M f(x), v \rangle_g = (\mathrm{d}f)_x(v)$. -/
theorem manifoldGradient_inner_eq
    (g : RiemannianMetric I M)
    (f : M → ℝ) (x : M) (v : TangentSpace I x) :
    g.metricInner x (manifoldGradient g f x) v = (mfderiv I 𝓘(ℝ, ℝ) f x) v :=
  g.metricRiesz_inner x (mfderiv I 𝓘(ℝ, ℝ) f x) v

omit [CompleteSpace E] in
/-- **Math.** **Gradient smoothness propagation**: $C^\infty$ scalar $g$
gives $C^\infty$ manifold gradient $\nabla^M g$. The gradient is the
composition of `mfderiv g` with the smooth Riesz isomorphism.

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
    (g : RiemannianMetric I M)
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => (⟨y, manifoldGradient (I := I) g f y⟩ : TangentBundle I M)) := by
  intro x
  have hx_base : x ∈ (trivializationAt E (TangentSpace I) x).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet (𝕜 := ℝ) (I := I) x]
    exact mem_chart_source H x
  have hΦ : ∀ j : Fin (Module.finrank ℝ E),
      ContMDiffOn I 𝓘(ℝ) ∞
        (fun y => (mfderiv I 𝓘(ℝ, ℝ) f y)
          (Riemannian.Tensor.chartBasisVecFiber (I := I) x j y))
        (trivializationAt E (TangentSpace I) x).baseSet := by
    intro j
    exact Riemannian.Tensor.mfderiv_chartBasisVec_apply_contMDiffOn
      (I := I) x hf j
  exact Riemannian.Tensor.metricRiesz_section_contMDiffAt
    (I := I) g x hx_base (Φ := fun y => mfderiv I 𝓘(ℝ, ℝ) f y) hΦ

end Riemannian
