import OpenGALib.Riemannian.Connection.LeviCivita
import OpenGALib.Riemannian.Curvature.RiemannCurvature
import OpenGALib.Riemannian.Operators.Gradient
import OpenGALib.Riemannian.Operators.SecondFundamentalForm
import OpenGALib.Riemannian.Operators.Hessian
import OpenGALib.Riemannian.Operators.Laplacian

/-!
# OpenGALib notation — facade

Single import point for OpenGALib's Riemannian notational surface. This
file does not define notation itself; each notation lives next to the
`def` it abbreviates (Mathlib convention). Consumers:

```
import OpenGALib.Util.Notation
open scoped Riemannian
```

Remaining scoped notation:

  * `⟦X, Y⟧`  — manifold Lie bracket `VectorField.mlieBracket _ X Y`
    (metric-independent; kept post-9g)

Previously hosted typeclass-dispatched `_g` notations
(`∇[X] Y`, `Riem(X, Y) Z`, `Ric(X, Y)`, `Ric_g`, `scal_g[I]`, `II(X, Y)`,
`H_g[I]`, `grad_g[I] f`, `Δ_g[I] f`, `hess_g[I] f`, `K_g[I](X, Y)`,
`(∇R)[X](Y, Z) W`, `⟪V, W⟫_g`, `‖V‖²_g`) were dropped in 9g
(umbrella #9) in favor of explicit `HasMetric.metric`/`g` forms, so that
multiple metrics (Ricci flow, conformal change, comparison geometry)
can coexist on the same manifold.
-/
