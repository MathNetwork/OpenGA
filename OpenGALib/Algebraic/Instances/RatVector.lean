import OpenGALib.Algebraic.BilinearForm.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Concrete instance: rational vectors

A fully `#eval`-able `BilinearForm` on `Fin n → ℚ`. `#eval inner`
produces a `Rat`; `native_decide` closes concrete equalities like
`inner ![1,2,3] ![4,5,6] = 32`. The same operations on the abstract
`Form ℚ V` API give the same numerical results, demonstrating
algebraic-core ↔ concrete-instance consistency.

Specialising to `𝕜 = ℝ` + smoothness reproduces the Riemannian module's
`metricInner` (with the usual `noncomputable` cascade).

**Ground truth**: $\langle v, w \rangle = \sum_i v_i w_i$ on
$\mathbb{Q}^n$.
-/

namespace RatVector

open BilinearForm

/-- The standard symmetric bilinear form on $\mathrm{Fin}\,n \to \mathbb{Q}$:
$B(v, w) = \sum_i v_i w_i$. As a `LinearMap.BilinForm`-style
`V →ₗ[ℚ] V →ₗ[ℚ] ℚ`. -/
def stdForm (n : ℕ) : Form ℚ (Fin n → ℚ) where
  toFun v :=
    { toFun := fun w => ∑ i, v i * w i
      map_add' := fun w₁ w₂ => by
        simp [Finset.sum_add_distrib, mul_add]
      map_smul' := fun c w => by
        simp [Finset.mul_sum, mul_left_comm] }
  map_add' v₁ v₂ := by
    ext w
    simp [Finset.sum_add_distrib, add_mul]
  map_smul' c v := by
    ext w
    simp [Finset.mul_sum, mul_assoc]

/-- Standard inner product specialised to ℚ: `inner v w = ∑ i, v i * w i`. -/
@[simp]
theorem stdForm_apply (n : ℕ) (v w : Fin n → ℚ) :
    stdForm n v w = ∑ i, v i * w i :=
  rfl

/-- `inner` via the standard form on $\mathbb{Q}^n$ also reduces to the
sum: `inner (stdForm n) v w = ∑ i, v i * w i`. -/
theorem inner_stdForm (n : ℕ) (v w : Fin n → ℚ) :
    inner (stdForm n) v w = ∑ i, v i * w i :=
  rfl

end RatVector

/-! ## `#eval` demonstrations — math runs

Below `#eval` commands genuinely execute at elaboration time and
produce rational numbers. Sample output (lhs is what `#eval` prints):

```
inner (stdForm 3) ![1, 2, 3] ![4, 5, 6]   =  32
inner (stdForm 2) ![3, 4] ![3, 4]         =  25
inner (stdForm 3) ![1, 0, 0] ![0, 1, 0]   =  0
inner (stdForm 3) ![1, 0, 0] ![1, 0, 0]   =  1
```
-/

open BilinearForm RatVector

#eval inner (stdForm 3) ![1, 2, 3] ![4, 5, 6]    -- 32

#eval inner (stdForm 2) ![3, 4] ![3, 4]          -- 25

#eval inner (stdForm 3) ![1, 0, 0] ![0, 1, 0]    -- 0

#eval inner (stdForm 3) ![1, 0, 0] ![1, 0, 0]    -- 1

/-! ## `native_decide`-closed equalities — proof by execution

The same equations that `#eval` produces are closed as theorems via
`native_decide`, which compiles the term to native code and uses the
result as a proof. -/

example : inner (stdForm 3) ![1, 2, 3] ![4, 5, 6] = 32 := by native_decide

example : inner (stdForm 2) ![3, 4] ![3, 4] = 25 := by native_decide

example : inner (stdForm 3) ![1, 0, 0] ![0, 1, 0] = 0 := by native_decide

example : inner (stdForm 3) ![1, 0, 0] ![1, 0, 0] = 1 := by native_decide

/-- Cauchy–Schwarz on a concrete pair, verified by execution. -/
example :
    let v : Fin 3 → ℚ := ![1, 2, 3]
    let w : Fin 3 → ℚ := ![4, 5, 6]
    (inner (stdForm 3) v w) ^ 2
      ≤ inner (stdForm 3) v v * inner (stdForm 3) w w := by
  native_decide
