import OpenGALib.Riemannian.Curvature
import OpenGALib.Riemannian.Gradient
import OpenGALib.Riemannian.SecondFundamentalForm

/-!
# Riemannian notation

Textbook-style notation for the framework's primary operations on
tangent vectors. All notations are `scoped` to the `Riemannian` scope —
open it via `open scoped Riemannian` to use them.

  * `⟪V, W⟫_g` — `metricInner _ V W` (basepoint inferred from
    `V W : TangentSpace I x` types)
  * `‖V‖²_g` — `metricInner _ V V` (squared norm via the metric)
  * `∇[X] Y`, `⟦X, Y⟧`, `Riem(X, Y) Z` — defined alongside their
    underlying primitives in `Connection/Bianchi.lean` (covariant
    derivative, Lie bracket section, Riemann curvature). All scoped
    to `Riemannian`.
  * `Ric(X, Y)` — `ricci X Y` as a function $M \to \mathbb{R}$.
  * `scal_g` — `scalarCurvature` as a function $M \to \mathbb{R}$.
  * `grad_g f` — `manifoldGradient f` as a section
    $x \mapsto \nabla^M f(x) \in T_x M$.
  * `II(X, Y)` — `secondFundamentalFormScalar X Y` (codim-1, function form).
  * `H_g` — `meanCurvature` as a scalar function $M \to \mathbb{R}$.

The notation follows do Carmo's convention: subscripts on inner products
indicate the metric (`_g`), and ∇ binds tightly with its direction
argument.

**Ground truth**: do Carmo 1992 §1.2 (inner product notation),
§2 (covariant derivative notation), §4 (Riemann curvature notation),
§4 ex. 1 (Ricci), §6.2 (second fundamental form, mean curvature).
-/

namespace OpenGALib

/-- The metric inner product $\langle V, W \rangle_g$ on tangent vectors,
with the basepoint inferred from the type of `V`, `W`. -/
scoped notation:max "⟪" V ", " W "⟫_g" => metricInner _ V W

/-- The squared norm $\|V\|^2_g$ of a tangent vector under the metric. -/
scoped notation:max "‖" V "‖²_g" => metricInner _ V V

end OpenGALib

namespace Riemannian

-- ∇[X] Y, ⟦X, Y⟧, Riem(X, Y) Z are defined in Connection/Bianchi.lean
-- alongside their underlying primitives (covDeriv, mlieBracket,
-- riemannCurvature) to avoid circular import.

/-- The Ricci curvature $\mathrm{Ric}(X, Y)$ as a scalar function on
the manifold: applied to $x$, gives $\mathrm{Ric}(X, Y)(x) = $
`ricci X Y x`. -/
scoped notation:max "Ric(" X ", " Y ")" => fun x => ricci X Y x

/-- The scalar curvature $\mathrm{scal}_g : M \to \mathbb{R}$. -/
scoped notation "scal_g" => scalarCurvature

/-- The codim-1 second fundamental form scalar $\mathrm{II}(X, Y) :
M \to \mathbb{R}$. -/
scoped notation:max "II(" X ", " Y ")" =>
  fun x => secondFundamentalFormScalar X Y x

/-- The mean curvature $H_g : M \to \mathbb{R}$. -/
scoped notation "H_g" => meanCurvature

/-- The manifold gradient $\mathrm{grad}_g f$ as a section
$x \mapsto \nabla^M f(x)$. The model `I` is taken from the ambient
typeclass context. -/
scoped notation:max "grad_g " f => fun x => manifoldGradient f x

end Riemannian
