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

Notation summary (each definition file has the canonical comment):

  * `∇[X] Y`, `⟦X, Y⟧`, `Riem(X, Y) Z`         — connection / curvature
  * `⟪V, W⟫_g`, `‖V‖²_g`                       — polymorphic inner / sq norm
  * `Ric(X, Y)`, `Ric_g(v, w) x`, `scal_g[I]`  — Ricci, scalar curvature
  * `II(X, Y)`, `H_g[I]`                       — second fundamental form, mean curvature
  * `grad_g[I] f`, `Δ_g[I] f`, `hess_g[I] f`   — gradient, Laplacian, Hessian

Bracketed `[I]` is required where bare `M` does not expose the model with
corners to typeclass synthesis.
-/
