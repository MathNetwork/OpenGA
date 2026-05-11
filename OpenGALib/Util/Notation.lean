import OpenGALib.Riemannian.Connection
import OpenGALib.Riemannian.Curvature
import OpenGALib.Riemannian.Gradient
import OpenGALib.Riemannian.SecondFundamentalForm
import OpenGALib.Riemannian.Operators.Hessian
import OpenGALib.Riemannian.Operators.Laplacian

/-!
# OpenGALib notation — facade

Single import point for OpenGALib's full Riemannian notational surface.
This file does not define any notation itself; instead it imports the
operational files where each notation lives next to the `def` it
abbreviates (Mathlib convention). Consumers should:

```
import OpenGALib.Util.Notation
open scoped Riemannian
```

and then write theorems in math-first form.

## Notation provided

### Connection tier (defined in `Riemannian/Connection.lean`)

  * `∇[X] Y`           — `covDeriv X Y` as a section.
  * `⟦X, Y⟧`           — `VectorField.mlieBracket _ X Y` as a section.
  * `Riem(X, Y) Z`     — `riemannCurvature X Y Z` as a section.

### Metric tier (defined in `Riemannian/Manifold.lean`)

  * `⟪V, W⟫_g`         — polymorphic inner product
                         (tangent → `ℝ`, section → `M → ℝ`)
                         via `MetricInnerHom` typeclass.
  * `‖V‖²_g`           — polymorphic squared norm
                         via `MetricNormSq` typeclass.

### Curvature tier (defined in `Riemannian/Curvature.lean`)

  * `Ric(X, Y)`        — `ricci X Y` as a section.
  * `Ric_g(v, w) x`    — `ricciTensor x v w` (pointwise).
  * `scal_g[I]`        — `scalarCurvature (I := I)` (`M → ℝ`).

### Codim-1 tier (defined in `Riemannian/SecondFundamentalForm.lean`)

  * `II(X, Y)`         — `secondFundamentalFormScalar X Y`.
  * `H_g[I]`           — `meanCurvature (I := I)`.

### Operator tier

  * `grad_g[I] f`      — `manifoldGradient (I := I) f` (`Riemannian/Gradient.lean`).
  * `Δ_g[I] f`         — `Operators.scalarLaplacian (I := I) f`
                         (`Riemannian/Operators/Laplacian.lean`).
  * `hess_g[I] f`      — `Operators.hessianBilin (I := I) f`
                         (`Riemannian/Operators/Hessian.lean`).
  * `‖·‖²_g` on `Bilin` sections → Frobenius squared norm
    (`Riemannian/Operators/Hessian.lean`).

Eta-reduced where applicable so notation aligns with simp's beta-reduced
normal form. Bracketed `I` is required for notations on `f : M → ℝ` (or
similar) where bare `M` does not expose the model with corners to
typeclass synthesis.

**Ground truth**: do Carmo 1992 §§1.2, 2, 4, 6.2; Lee, *Smooth Manifolds*.
-/
