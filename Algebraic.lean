import Algebraic.BilinearForm.Basic
import Algebraic.Instances.RatVector

/-!
# Algebraic — field-generic computable algebraic core

A namespace for fully computable, field-generic algebraic structures.
Currently provides:

- `Algebraic/BilinearForm/Basic.lean` — symmetric bilinear forms and
  their inner-product API, parameterised over any `Field 𝕜`. Algebra
  lemmas (zero / neg / sub / add / smul) are field-generic.
- `Algebraic/Instances/RatVector.lean` — the standard symmetric
  bilinear form on `Fin n → ℚ`, with `#eval` demonstrations producing
  actual rational numbers and `native_decide`-verified concrete
  equalities.

## Layering

This namespace is **independent of `Riemannian/`**: it provides the
algebraic substrate. The Riemannian module specialises this content to
`𝕜 = ℝ` and adds smoothness; on a computable field like `ℚ`, the same
algebraic content runs as a program.

```
Algebraic/  (𝕜-generic, computable)
    ↑
Riemannian/  (𝕜 = ℝ + smoothness)
```

## Reusability

`Algebraic/` is reusable across contexts that need bilinear forms
without a smooth-manifold structure: quadratic forms in algebra,
positive-definite forms in optimization, matrix calculus, Hermitian
forms when 𝕜 = ℂ, etc.
-/
