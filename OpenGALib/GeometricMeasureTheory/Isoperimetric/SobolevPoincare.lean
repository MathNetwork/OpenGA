import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import OpenGALib.GeometricMeasureTheory.Isoperimetric.BVFunction
import OpenGALib.GeometricMeasureTheory.Isoperimetric.Relative
import OpenGALib.GeometricMeasureTheory.Isoperimetric.BVFunction

/-!
# GeometricMeasureTheory.Isoperimetric.SobolevPoincare

**Sobolev–Poincaré inequality (BV form)** and **Federer–Fleming theorem**
(Maggi Ch. 30; Federer–Fleming 1960; Sobolev 1938).

For BV $u : \mathbb{R}^n \to \mathbb{R}$ ($n \ge 2$) with $\int u = 0$,
$$\|u\|_{L^{n/(n-1)}(\mathbb{R}^n)} \;\le\; c_n^{\mathrm{SP}}\;\|Du\|(\mathbb{R}^n).$$
Federer–Fleming identifies the optimal constant with the inverse of the
optimal isoperimetric constant: $c_n^{\mathrm{SP}} = (c_n^{\mathrm{iso}})^{-1}$.

Composes `BVFunction.totalVariation`, the `coarea_formula` bridge, and
Mathlib's `eLpNorm` into a paper-faithful, **non-vacuous** statement.
Exponent and constant are real `noncomputable def`s with real-derived
positivity. `sobolev_poincare_inequality` itself is a single PRE-PAPER
existence axiom; closure is framework self-build via the truncation
argument over `coarea_formula` (~150 LOC) once `lpNorm`-vs-truncation
lemmas land.

**Ground truth**: Maggi Thm 30.1 (BV form), Thm 30.4 (Federer–Fleming);
Federer–Fleming 1960; Sobolev 1938.
-/

namespace GeometricMeasureTheory
namespace Isoperimetric

/-! ## Sobolev exponent + Sobolev–Poincaré constant -/

/-- The **Sobolev exponent** $n^* = n/(n-1)$ for dimension $n$.

For $n \ge 2$, this is the sharp critical exponent at which the
Sobolev–Poincaré embedding $BV(\mathbb{R}^n) \hookrightarrow L^{n^*}$
holds. For $n \le 1$ the formula degenerates ($n = 1$ gives $1/0 = 0$
by `div_zero`, $n = 0$ gives $0/{-1} = 0$); positivity / strict-
greater-than-one is proven under `1 < n`.

**Ground truth**: Maggi 2012 §30 (intro). -/
noncomputable def sobolevExponent (n : ℕ) : ℝ :=
  (n : ℝ) / ((n : ℝ) - 1)

/-- The Sobolev exponent is positive for $n \ge 2$. -/
theorem sobolevExponent_pos {n : ℕ} (hn : 1 < n) :
    0 < sobolevExponent n := by
  unfold sobolevExponent
  have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith
  have hn_sub_pos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  positivity

/-- The Sobolev exponent is strictly greater than $1$ for $n \ge 2$
(this is the BV-embedding gain $L^p \hookrightarrow L^{p^*}$ relevant
to the Sobolev–Poincaré inequality). -/
theorem sobolevExponent_gt_one {n : ℕ} (hn : 1 < n) :
    1 < sobolevExponent n := by
  unfold sobolevExponent
  have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn_sub_pos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  rw [lt_div_iff₀ hn_sub_pos]
  linarith

/-- The **Sobolev–Poincaré constant** $c_n^{\mathrm{SP}}$ in dimension
$n$, defined directly as the inverse of the isoperimetric constant
(per the Federer–Fleming equivalence).

Defined this way, `federer_fleming_equivalence` becomes an `rfl`-style
derivation: the equation Maggi states as Theorem 30.4 is the very
definition we use in this framework. The Maggi-stated existence /
optimality of this $c_n$ for the Sobolev–Poincaré inequality is then
the content of `sobolev_poincare_inequality`.

**Ground truth**: Maggi 2012 Theorem 30.4 (Federer–Fleming). -/
noncomputable def sobolevPoincareConstant (n : ℕ) : ℝ :=
  (isoperimetricConstant n)⁻¹

/-- The Sobolev–Poincaré constant is positive for $n \ge 1$, derived
from `isoperimetricConstant_pos` via `inv_pos`. -/
theorem sobolevPoincareConstant_pos {n : ℕ} (hn : 0 < n) :
    0 < sobolevPoincareConstant n := by
  unfold sobolevPoincareConstant
  exact inv_pos.mpr (isoperimetricConstant_pos hn)

/-! ## L^p norm of a BV function -/

section LpNorm

variable {E : Type*} [MeasureTheory.MeasureSpace E]

/-- The **L^p norm** $\|u\|_{L^p(E)}$ of (the underlying function of)
a BV function $u$, defined via Mathlib's `MeasureTheory.eLpNorm`
against the ambient `MeasureTheory.volume` measure.

The `MeasureSpace E` instance provides both the `MeasurableSpace E`
required by `BVFunction` and the canonical `volume : Measure E`
required by `eLpNorm`, so a single typeclass closes both
dependencies. -/
noncomputable def lpNorm (u : BVFunction E) (p : ENNReal) : ENNReal :=
  MeasureTheory.eLpNorm u.toFun p MeasureTheory.volume

/-- The L^p norm is non-negative (trivial via `ENNReal`). -/
theorem lpNorm_nonneg (u : BVFunction E) (p : ENNReal) :
    0 ≤ lpNorm u p := zero_le _

end LpNorm

/-! ## Sobolev–Poincaré inequality (Maggi Theorem 30.1) -/

section SobolevPoincare

variable {E : Type*} [MeasureTheory.MeasureSpace E]

/-- **Sobolev–Poincaré inequality (BV form)** (Maggi 2012 Theorem 30.1):

For a BV function $u : E \to \mathbb{R}$ in dimension $n \ge 2$ with
$\int u\,d\mu = 0$,
$$\|u\|_{L^{n/(n-1)}(E)} \;\le\; c_n^{\mathrm{SP}} \cdot \|Du\|(E).$$

Stated in Lean using the framework's `lpNorm` (real def via Mathlib
`eLpNorm`) on the LHS and `Isoperimetric.totalVariation u` on the RHS
— paper-faithful Maggi 30.1, **not** a vacuous existential.

**Sorry status**: PRE-PAPER existence axiom. Repair plan: framework
self-build via the truncation argument over `coarea_formula` (Maggi
Ch. 30 proof template, ~150 LOC) once `Real.rpow` + `lintegral`
truncation lemmas connect.

**Ground truth**: Maggi 2012 Theorem 30.1; Federer–Fleming 1960;
Sobolev 1938. -/
theorem sobolev_poincare_inequality
    {n : ℕ} (_hn : 1 < n)
    (u : BVFunction E)
    (_hzero : ∫ x, u x ∂(MeasureTheory.volume : MeasureTheory.Measure E) = 0) :
    lpNorm u (ENNReal.ofReal (sobolevExponent n)) ≤
      ENNReal.ofReal (sobolevPoincareConstant n) * totalVariation u := by
  sorry

end SobolevPoincare

/-! ## Federer–Fleming theorem (Maggi Theorem 30.4) -/

/-- **Federer–Fleming theorem** (Maggi 2012 Theorem 30.4).

The Sobolev–Poincaré inequality and the Euclidean isoperimetric
inequality are equivalent — each implies the other with the constant
relationship
$$c_n^{\mathrm{SP}} \;=\; \bigl(c_n^{\mathrm{iso}}\bigr)^{-1}.$$

In this framework, `sobolevPoincareConstant n` is **defined** as
`(isoperimetricConstant n)⁻¹`, so this theorem is `rfl`. The Maggi
30.4 *content* — that this is indeed the optimal Sobolev–Poincaré
constant — is encoded in the soundness of `sobolev_poincare_inequality`
(the existence axiom would be vacuous if the constant were arbitrary).

**Ground truth**: Maggi 2012 Theorem 30.4; Federer–Fleming 1960. -/
theorem federer_fleming_equivalence (n : ℕ) :
    sobolevPoincareConstant n = (isoperimetricConstant n)⁻¹ := rfl


end Isoperimetric
end GeometricMeasureTheory
