import OpenGALib.Riemannian.Connection.LeviCivita
import OpenGALib.Riemannian.TensorBundle.SmoothOrthoFrame

/-!
# Divergence of a vector field

For a smooth tangent vector field $X$ on a Riemannian manifold $(M, g)$,
the **divergence** is the $g$-trace of the $(1,1)$-tensor $\nabla X$
(the covariant derivative seen as an endomorphism $Y \mapsto \nabla_Y X$):
$$\operatorname{div}_g X (x) \;=\; \mathrm{tr}_g(\nabla X)(x)
   \;=\; \sum_i g_x\bigl(\nabla_{B_i} X(x),\, B_i(x)\bigr),$$
where $\{B_i\} = \operatorname{smoothOrthoFrame} g\,x$ is the smooth
$g$-orthonormal frame at $x$ (Gram-Schmidt of the chart frame, bumped
to a global section). The trace is basis-independent (basis-invariance
of trace under change of orthonormal frame), so the choice of frame is
irrelevant.

This file is the vector-field-side analog of `scalarLaplacian` in
`Operators/Laplacian.lean`: both are $g$-traces of differential
operators, the latter on $(0,2)$-Hessian, the former on $(1,1)$-cov-deriv.

Reference: do Carmo §3.6; Petersen Ch. 2 §1.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle
open scoped ContDiff Manifold Bundle Riemannian InnerProductSpace

namespace Riemannian
namespace Operators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [IsLocallyConstantChartedSpace H M]
  [hm : HasMetric I M]

/-- **Math.** **Divergence** of a tangent vector field $X$ at $x$:
$$\operatorname{div}_g X (x) \;=\; \sum_i g_x\bigl(\nabla_{B_i} X(x),\,
                                                 B_i(x)\bigr),$$
where $\{B_i\}$ is the smooth $g$-orthonormal frame at $x$
(`Riemannian.Tensor.smoothOrthoFrame`).

Basis-form definition: trace of the $(1,1)$-tensor $\nabla X$, evaluated
against a $g$-orthonormal basis of $T_xM$. The result is basis-invariant
(though this fact is not used in the definition itself; the canonical
`smoothOrthoFrame` is picked as the working basis). -/
noncomputable def divergence
    (X : VectorFieldSection I M) (x : M) : ℝ :=
  ∑ i, metricInner x
    ((∇[Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x i] X) x)
    (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x i x)

/-- **Math.** Notation `div_g[I] X` for the divergence as a function
`M → ℝ`; `(div_g[I] X) x` is the value at `x`. -/
scoped[Riemannian] notation:max "div_g[" I "]" =>
  Operators.divergence (I := I)

/-- **Math.** The divergence of the zero vector field is zero. -/
@[simp] theorem divergence_zero (x : M) :
    divergence (I := I) (M := M) (0 : VectorFieldSection I M) x = 0 := by
  show ∑ i, metricInner x
        ((∇[Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x i]
            (0 : VectorFieldSection I M)) x)
        (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x i x) = 0
  refine Finset.sum_eq_zero ?_
  intro i _
  -- ∇_{B_i} 0 at x = 0 via continuous linear map-zero of `leviCivitaConnection.toFun 0 x`.
  have h_zero : (∇[Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x i]
        (0 : VectorFieldSection I M)) x = 0 := by
    show ((leviCivitaConnection (I := I) (M := M) HasMetric.metric).toFun 0 x)
        (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x i x) = 0
    rw [CovariantDerivative.zero]
    rfl
  rw [h_zero]
  show ⟪(0 : TangentSpace I x), _⟫_ℝ = 0
  exact inner_zero_left _

end Operators
end Riemannian

end
