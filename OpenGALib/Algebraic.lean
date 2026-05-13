import OpenGALib.Algebraic.Auxiliary.Basis
import OpenGALib.Algebraic.Auxiliary.Fin
import OpenGALib.Algebraic.Auxiliary.LIContDiff
import OpenGALib.Algebraic.Auxiliary.MultiKroneckerDelta
import OpenGALib.Algebraic.Auxiliary.Perm
import OpenGALib.Algebraic.Auxiliary.ShuffleDecomposition
import OpenGALib.Algebraic.Auxiliary.ShuffleDeriv
import OpenGALib.Algebraic.Auxiliary.ShuffleSplit
import OpenGALib.Algebraic.BilinearForm.Basic
import OpenGALib.Algebraic.Instances.RatVector

/-!
# Algebraic — field-generic computable algebraic core

Fully computable, field-generic algebraic structures: symmetric bilinear
forms parameterised over any `Field 𝕜` (algebra lemmas field-generic),
plus a concrete `Fin n → ℚ` instance with `native_decide`-verified
equalities.

Independent of `Riemannian/`. The Riemannian module specialises to
`𝕜 = ℝ` and adds smoothness; on a computable field like `ℚ`, the same
algebraic content runs as a program. Reusable for quadratic forms in
algebra, positive-definite forms in optimization, Hermitian forms when
`𝕜 = ℂ`.
-/
