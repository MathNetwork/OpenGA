import OpenGALib.Riemannian.Connection
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Connection Laplacian on tangent vector fields

For a tangent vector field $Z : \Pi x : M, T_x M$ on a Riemannian manifold
$(M, g)$, the **connection Laplacian** (also called the rough or Bochner
Laplacian) is the metric trace of the second covariant derivative,
$$\Delta_\nabla Z \;=\; \mathrm{tr}_g(\nabla\nabla Z).$$
In a $g$-orthonormal frame $\{\varepsilon_i\}$ of $T_xM$ this evaluates to
$$(\Delta_\nabla Z)(x) \;=\; \sum_i
   \bigl(\nabla_{\varepsilon_i}\nabla_{\varepsilon_i} Z
        - \nabla_{(\nabla_{\varepsilon_i}\varepsilon_i)} Z\bigr)(x).$$

The frame is `stdOrthonormalBasis ℝ (TangentSpace I x)`, viewed as a
constant chart-frame extension via `[IsLocallyConstantChartedSpace H M]`
(under which `TangentSpace I _ = E` definitionally on all of $M$).

The connection Laplacian on tangent fields is the linear operator at the
heart of the Bochner–Weitzenböck identity:
$\Delta_\nabla(\nabla f) = \nabla(\Delta_g f) + \mathrm{Ric}^\sharp(\nabla f)$.

## Main definitions

* `connectionLaplacian Z x` — the connection Laplacian on a tangent vector
  field, evaluated at `x` against `stdOrthonormalBasis ℝ (TangentSpace I x)`.

Reference: Petersen, *Riemannian Geometry*, Ch. 7 §1; do Carmo §6.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle
open scoped ContDiff Manifold Bundle Riemannian

namespace Riemannian
namespace Operators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [IsLocallyConstantChartedSpace H M]
  [hm : HasMetric I M]

set_option backward.isDefEq.respectTransparency false in
/-- The **connection Laplacian** $\Delta_\nabla Z$ on a tangent vector
field $Z : \Pi x : M, T_x M$, computed against the $g$-orthonormal frame
`stdOrthonormalBasis ℝ (TangentSpace I x)` extended as a constant
chart-frame section:
$$(\Delta_\nabla Z)(x) \;=\; \sum_i \bigl(\nabla_{\varepsilon_i}
   \nabla_{\varepsilon_i} Z - \nabla_{(\nabla_{\varepsilon_i}\varepsilon_i)} Z\bigr)(x).$$

The constant chart-frame extension is $g$-orthonormal at $x$ (where
`stdOrthonormalBasis` is constructed); in general it is *not* $g$-orthonormal
at other points, but the trace identification at $x$ depends only on the
frame at $x$, so this gives the correct geometric trace of $\nabla\nabla Z$
at $x$ — basis-independent among $g$-orthonormal frames of $T_xM$.

**Ground truth**: Petersen, *Riemannian Geometry*, Ch. 7 §1 Proposition 33
(Bochner identity); do Carmo §6 ex. 12. -/
noncomputable def connectionLaplacian
    (Z : Π x : M, TangentSpace I x) (x : M) : TangentSpace I x :=
  let e : OrthonormalBasis _ ℝ (TangentSpace I x) :=
    stdOrthonormalBasis ℝ (TangentSpace I x)
  ∑ i, (covDerivAt (fun y : M => covDerivAt Z y (e i : TangentSpace I x)) x
          (e i : TangentSpace I x)
        - covDerivAt Z x
            (covDerivAt (fun _ : M => (e i : TangentSpace I x)) x
              (e i : TangentSpace I x)))

@[simp] lemma connectionLaplacian_def
    (Z : Π x : M, TangentSpace I x) (x : M) :
    connectionLaplacian (I := I) (M := M) Z x =
      ∑ i, (covDerivAt (fun y : M =>
                covDerivAt Z y
                  ((stdOrthonormalBasis ℝ (TangentSpace I x)) i
                    : TangentSpace I x)) x
              ((stdOrthonormalBasis ℝ (TangentSpace I x)) i : TangentSpace I x)
            - covDerivAt Z x
                (covDerivAt (fun _ : M =>
                  ((stdOrthonormalBasis ℝ (TangentSpace I x)) i
                    : TangentSpace I x)) x
                  ((stdOrthonormalBasis ℝ (TangentSpace I x)) i
                    : TangentSpace I x))) :=
  rfl

end Operators
end Riemannian
