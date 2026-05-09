import OpenGALib.Util.Notation.Connection
import OpenGALib.Util.Notation.Riemann
import OpenGALib.Util.Notation.Curvature

/-!
# Notation — umbrella

Single import point for OpenGALib's full Riemannian notational
surface. Re-exports three dep-tier-split notation files:

  * `Util/Notation/Connection.lean` — pre-Bianchi tier:
    `⟪V, W⟫_g`, `‖V‖²_g`, `∇[X] Y`, `⟦X, Y⟧`
  * `Util/Notation/Riemann.lean`    — Riemann-curvature tier:
    `Riem(X, Y) Z`
  * `Util/Notation/Curvature.lean`  — post-Curvature tier:
    `Ric(X, Y)`, `scal_g`, `II(X, Y)`, `H_g`, `grad_g f`

Activate via `open scoped Riemannian OpenGALib`.

The tier split is necessary because `Connection/Bianchi.lean` itself
uses the pre-Bianchi notation in `riemannCurvature`'s def body — so
that tier must be defined before Bianchi. The Riemann-tier defines
`Riem(X, Y) Z` post-Bianchi (after `riemannCurvature` is in scope).
The post-Curvature tier defines notation for `ricci`, `scalarCurvature`,
etc., which must come after `Curvature.lean`.

End users typically only need this umbrella. Internal files import
the specific tier they depend on, to avoid circular imports.
-/
