import OpenGALib.Riemannian.Connection.LeviCivita
import OpenGALib.Riemannian.Metric.Basic

/-!
# Riemannian notation — pre-Bianchi tier

Notations for connection-level and metric-level primitives. Imported by
`Connection/Bianchi.lean` so the Riemann curvature def can read in
math notation; imported by all downstream theorem code that uses
`∇`, `⟦,⟧`, `⟪,⟫_g`.

  * `⟪V, W⟫_g` — `metricInner _ V W` (basepoint inferred)
  * `‖V‖²_g`   — `metricInner _ V V` (squared norm)
  * `∇[X] Y`   — `covDeriv X Y` as a section `M → TangentSpace I _`
  * `⟦X, Y⟧`   — `VectorField.mlieBracket _ X Y` as a section

All `scoped` to `Riemannian` (or `OpenGALib` for metric inner). Activate
via `open scoped Riemannian OpenGALib`.

Eta-reduced form (no `fun x => ... x` wrapping) so notation aligns with
simp's beta-reduced normal form. `(∇[X] Y) x` elaborates directly to
`covDeriv X Y x` without a residual lambda.

**Ground truth**: do Carmo 1992 §1.2 (inner product), §2 (covariant
derivative).
-/

namespace OpenGALib

/-- The metric inner product $\langle V, W \rangle_g$ on tangent vectors,
with the basepoint inferred from the type of `V`, `W`. -/
scoped notation:max "⟪" V ", " W "⟫_g" => metricInner _ V W

/-- The squared norm $\|V\|^2_g$ of a tangent vector under the metric. -/
scoped notation:max "‖" V "‖²_g" => metricInner _ V V

end OpenGALib

namespace Riemannian

/-- The covariant derivative $\nabla_X Y$ as a section. Pointwise:
$(∇[X] Y)(x) = (\nabla_X Y)(x) = $ `covDeriv X Y x`. -/
scoped notation:max "∇[" X "] " Y:max => covDeriv X Y

/-- The manifold Lie bracket $[X, Y]$ as a section. Model `I` inferred
from types. Pointwise: $(⟦X, Y⟧)(x) = $ `mlieBracket _ X Y x`. -/
scoped notation:max "⟦" X ", " Y "⟧" => VectorField.mlieBracket _ X Y

end Riemannian
