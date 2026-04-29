import Riemannian.Metric.Basic
import Riemannian.Connection.LeviCivita
import Riemannian.Curvature

/-!
# Riemannian notation

Textbook-style notation for the framework's primary operations on
tangent vectors. All notations are `scoped` to the `Riemannian` scope —
open it via `open scoped Riemannian` to use them.

  * `⟪V, W⟫_g` — `metricInner _ V W` (basepoint inferred from
    `V W : TangentSpace I x` types)
  * `‖V‖²_g` — `metricInner _ V V` (squared norm via the metric)
  * `∇[X] Y` — `covDeriv X Y` as a function `M → TangentSpace I _`,
    so `(∇[X] Y) x = covDeriv X Y x` is $(\nabla_X Y)(x)$.
  * `Riem(X, Y) Z` — `riemannCurvature X Y Z` as a function, so
    `(Riem(X, Y) Z) x = riemannCurvature X Y Z x` is $R(X, Y) Z (x)$.

The notation follows do Carmo's convention: subscripts on inner products
indicate the metric (`_g`), and ∇ binds tightly with its direction
argument.

**Ground truth**: do Carmo 1992 §1.2 (inner product notation),
§2 (covariant derivative notation), §4 (Riemann curvature notation).
-/

namespace OpenGALib

/-- The metric inner product $\langle V, W \rangle_g$ on tangent vectors,
with the basepoint inferred from the type of `V`, `W`. -/
scoped notation:max "⟪" V ", " W "⟫_g" => metricInner _ V W

/-- The squared norm $\|V\|^2_g$ of a tangent vector under the metric. -/
scoped notation:max "‖" V "‖²_g" => metricInner _ V V

end OpenGALib

namespace Riemannian

/-- The covariant derivative $\nabla_X Y$ as a section: applied to $x$,
gives $(\nabla_X Y)(x) = $ `covDeriv X Y x`. -/
scoped notation:max "∇[" X "] " Y => fun x => covDeriv X Y x

/-- The Riemann curvature $R(X, Y) Z$ as a section: applied to $x$,
gives $(R(X, Y) Z)(x) = $ `riemannCurvature X Y Z x`. -/
scoped notation:max "Riem(" X ", " Y ") " Z =>
  fun x => riemannCurvature X Y Z x

end Riemannian
