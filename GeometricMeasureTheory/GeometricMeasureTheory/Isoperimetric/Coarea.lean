import GeometricMeasureTheory.Isoperimetric.BVFunction
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-!
# GeometricMeasureTheory.Isoperimetric.Coarea

The **coarea formula** (Maggi 2012 Theorem 18.1; Federer 1969 §3.2.22).

For a BV function $u : E \to \mathbb{R}$, the total variation $\|Du\|(E)$
equals the integral of the perimeters of the super-level sets:
$$\|Du\|(E) \;=\; \int_{\mathbb{R}} \mathrm{Per}(\{u > t\})\,dt.$$

This is the foundational tool for converting BV-functional inequalities
into level-set perimeter inequalities. Phase 3.6 (Sobolev–Poincaré +
Federer–Fleming) consumes the coarea formula directly.

## Form

The Phase 3.4 (revised) `BVFunction` primitive provides
`Isoperimetric.totalVariation u : ℝ≥0∞`. The framework's
`FinitePerimeter` exposes the perimeter as the measure-on-the-whole-
space `Ω.perimMeasure Set.univ : ℝ≥0∞` (matching Maggi's
$|D\chi_\Omega|(E) = \mathrm{Per}(\Omega)$ identity from
`totalVariation_ofFinitePerimeter`). The coarea formula is therefore
stated as the equality of two `ℝ≥0∞` quantities under
`MeasureTheory.lintegral` against the Lebesgue measure on $\mathbb{R}$
— **not** a vacuous existential, but a real paper-faithful equation.

## Sorry status

Both core results are PRE-PAPER existence axioms:
  * `levelSet_finitePerimeter_exists` — Maggi 2012 Proposition 13.1
  * `coarea_formula` — Maggi 2012 Theorem 18.1

Repair plan: framework self-build of Federer's slicing argument
(Federer 1969 §3.2.22; ~250 LOC including the BV-derivative-via-
finite-difference quotient) once a `BVDistributionalDerivative`
primitive lands, or wait for Mathlib upstream.

**Ground truth**: Maggi 2012 Theorem 18.1; Federer 1969 §3.2.22;
Federer 1959 (original).
-/

open MeasureTheory

namespace GeometricMeasureTheory
namespace Isoperimetric

/-! ## Level-set finite-perimeter existence (Maggi Proposition 13.1) -/

variable {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]

/-- **Level-set finite-perimeter existence** (Maggi 2012 Proposition 13.1):

For any BV function $u : E \to \mathbb{R}$, there exists a family of
finite-perimeter sets $\{u > t\}_{t \in \mathbb{R}}$ such that, for
Lebesgue-a.e. $t \in \mathbb{R}$, the carrier of the $t$-th set
coincides with $\{x : u(x) > t\}$.

The family is obtained by a single existential `Classical.choose` over
$t$, packaging the level-set construction as a function
`ℝ → FinitePerimeter E`.

**Sorry status**: PRE-PAPER existence axiom. Repair plan: framework
self-build via Federer slicing once a `BVDistributionalDerivative`
primitive is available (~80 LOC), or wait for Mathlib upstream BV
infrastructure.

**Ground truth**: Maggi 2012 Proposition 13.1. -/
theorem levelSet_finitePerimeter_exists (u : BVFunction E) :
    ∃ levelSet : ℝ → FinitePerimeter E,
      ∀ᵐ t ∂(MeasureTheory.volume : Measure ℝ), ∀ x : E, x ∈ (levelSet t).carrier ↔ u x > t := by
  sorry

/-- The **level set** $\{u > t\}$ as a `FinitePerimeter E`,
extracted from `levelSet_finitePerimeter_exists` via
`Classical.choose`. -/
noncomputable def levelSet (u : BVFunction E) : ℝ → FinitePerimeter E :=
  Classical.choose (levelSet_finitePerimeter_exists u)

/-- The level-set carrier characterization: for a.e. $t$, $x$ is in
the carrier of $\{u > t\}$ iff $u(x) > t$. -/
theorem levelSet_carrier_iff (u : BVFunction E) :
    ∀ᵐ t ∂(MeasureTheory.volume : Measure ℝ),
      ∀ x : E, x ∈ (levelSet u t).carrier ↔ u x > t :=
  Classical.choose_spec (levelSet_finitePerimeter_exists u)

/-! ## Coarea formula (Maggi Theorem 18.1) -/

/-- **Coarea formula** (Maggi 2012 Theorem 18.1; Federer 1969 §3.2.22).

For a BV function $u : E \to \mathbb{R}$, the total variation $\|Du\|(E)$
equals the Lebesgue integral over $\mathbb{R}$ of the perimeters of the
super-level sets:
$$\|Du\|(E) \;=\; \int_{\mathbb{R}} |D\chi_{\{u > t\}}|(E)\,dt.$$

Stated using the framework's `Isoperimetric.totalVariation` (LHS) and
the perimeter-measure-on-whole-space `(levelSet u t).perimMeasure Set.univ`
(RHS) — both `ℝ≥0∞`, integrated by `MeasureTheory.lintegral` against
the standard Lebesgue measure on $\mathbb{R}$.

**Sorry status**: PRE-PAPER existence axiom. Repair plan: framework
self-build via Federer's slicing argument (Federer 1969 §3.2.22)
when a `BVDistributionalDerivative` primitive matures (~250 LOC), or
wait for Mathlib upstream.

**Ground truth**: Maggi 2012 Theorem 18.1; Federer 1969 §3.2.22;
Federer 1959 (original).

**Paper-faithful, non-vacuous**: the LHS depends on $u$ via
`totalVariation u`, the RHS depends on $u$ via `levelSet u t`, both
threaded through real `noncomputable def`s — unlike a generic
`∃ x : ℝ≥0∞, x = …` form which would be trivially provable. -/
theorem coarea_formula (u : BVFunction E) :
    totalVariation u =
      ∫⁻ t, (levelSet u t).perimMeasure Set.univ ∂(MeasureTheory.volume : Measure ℝ) := by
  sorry

/-- **Coarea-derived finiteness**: the level-set-perimeter integral is
finite, since it equals the (finite) BV total variation.

Phase 3.4 BV finiteness `totalVariation_lt_top'` combined with
`coarea_formula` gives the lintegral finiteness directly. -/
@[simp] theorem coarea_formula_finite (u : BVFunction E) :
    ∫⁻ t, (levelSet u t).perimMeasure Set.univ ∂(MeasureTheory.volume : Measure ℝ) < ⊤ := by
  rw [← coarea_formula u]
  exact totalVariation_lt_top' u

/-! ## UXTest: typeclass + simp self-test -/

section CoareaTest

/-- Self-test: `coarea_formula` is callable and packs the BV-to-
level-set-perimeter equality. -/
example (u : BVFunction E) :
    totalVariation u =
      ∫⁻ t, (levelSet u t).perimMeasure Set.univ ∂(MeasureTheory.volume : Measure ℝ) :=
  coarea_formula u

/-- Self-test: derived finiteness simp closes. -/
example (u : BVFunction E) :
    ∫⁻ t, (levelSet u t).perimMeasure Set.univ ∂(MeasureTheory.volume : Measure ℝ) < ⊤ := by
  simp

end CoareaTest

end Isoperimetric
end GeometricMeasureTheory
