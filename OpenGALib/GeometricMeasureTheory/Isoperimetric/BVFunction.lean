import OpenGALib.GeometricMeasureTheory.FinitePerimeter

/-!
# GeometricMeasureTheory.Isoperimetric.BVFunction

A function $u : E \to \mathbb{R}$ is **BV (bounded variation)** if its
distributional gradient is a vector-valued Radon measure of finite
total variation:
$$\|Du\|(E) = \sup\left\{\int u \, \mathrm{div}\,\varphi \, dx :
  \varphi \in C^1_c(E; E),\; \|\varphi\|_\infty \le 1\right\} < \infty.$$

`BVFunction` bundles the measurable function with its total-variation
witness as a single algebraic object (Maggi §13). Foundational
primitive for the downstream coarea formula and Sobolev–Poincaré /
Federer–Fleming statements — without `totalVariation`, those would
degenerate to vacuous existence quantifiers.

A **bridge primitive** in the spirit of `InnerProductBridge`: a thin
algebraic carrier whose introduction unblocks multiple downstream
statements, since Mathlib's BV infrastructure on metric measure spaces
is not yet sufficient.

**Ground truth**: Maggi 2012 Ch. 13; De Giorgi 1954; Federer 1969 §3.
-/

namespace GeometricMeasureTheory
namespace Isoperimetric

/-! ## BVFunction structure -/

/-- A **BV (bounded variation) function** $u : E \to \mathbb{R}$.

Bundles the underlying measurable function with a total-variation
witness $\|Du\|(E) < \infty$. The total variation is left abstract
at this layer; downstream consumers may either treat it as the
supremum of test-field integrals
$\sup_\varphi \int u\,\mathrm{div}\,\varphi$ (paper-faithful Maggi 13.1)
or as the distributional-derivative norm.

**Ground truth**: Maggi 2012 Chapter 13. -/
structure BVFunction (E : Type*) [MeasurableSpace E] where
  /-- Underlying real-valued function. -/
  toFun : E → ℝ
  /-- Measurability of the underlying function. -/
  measurable : Measurable toFun
  /-- Total variation $\|Du\|(E) \in [0, \infty]$. -/
  totalVariation : ENNReal
  /-- Total variation is finite (the BV-membership constraint). -/
  totalVariation_lt_top : totalVariation < ⊤

namespace BVFunction

variable {E : Type*} [MeasurableSpace E]

/-- BV functions coerce to underlying functions. -/
instance : CoeFun (BVFunction E) (fun _ => E → ℝ) := ⟨BVFunction.toFun⟩

end BVFunction

/-! ## Total-variation accessor + derived simp lemmas -/

variable {E : Type*} [MeasurableSpace E]

/-- The **total variation** of a BV function $u$, exposed under the
`Isoperimetric` namespace as a clean concept-level accessor (paper-
faithful $\|Du\|(E)$ notation). -/
noncomputable def totalVariation (u : BVFunction E) : ENNReal := u.totalVariation

/-- Total variation of any BV function is finite (the BV-membership
constraint repackaged as a derived fact under the `Isoperimetric`
namespace). -/
@[simp] theorem totalVariation_lt_top' (u : BVFunction E) :
    totalVariation u < ⊤ := u.totalVariation_lt_top

/-- Total variation is non-negative (trivial via `ENNReal`). -/
theorem totalVariation_nonneg (u : BVFunction E) :
    0 ≤ totalVariation u := zero_le _

/-! ## BV ↔ finite-perimeter set bridge (Maggi Proposition 13.1) -/

section CharacteristicIsBV

variable {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]

/-- **Characteristic function of a finite-perimeter set is BV**
(Maggi 2012 Proposition 13.1).

For a finite-perimeter set $\Omega \subseteq E$, the characteristic
function $\chi_\Omega : E \to \mathbb{R}$ is BV with total variation
equal to the perimeter measure on the whole space:
$$\|D\chi_\Omega\|(E) \;=\; \mathrm{Per}(\Omega) \;=\; |D\chi_\Omega|(E).$$

**Sorry status**: PRE-PAPER existence axiom. Repair plan: framework
self-build of Maggi 13.1 when a `BVDistributionalDerivative` primitive
matures (~80 LOC), or wait for Mathlib upstream BV infrastructure on
charted manifolds.

**Ground truth**: Maggi 2012 Proposition 13.1; De Giorgi 1954. -/
theorem characteristic_isBV (Ω : FinitePerimeter E) :
    ∃ u : BVFunction E,
      (∀ x, u x = Ω.carrier.indicator (fun _ => (1 : ℝ)) x) ∧
      totalVariation u = Ω.perimMeasure Set.univ := by
  sorry

/-- The **BV function from a finite-perimeter set**: characteristic
function $\chi_\Omega$ as a `BVFunction`. Real `noncomputable def`
via `Classical.choose` over the existence axiom
`characteristic_isBV`. -/
noncomputable def ofFinitePerimeter (Ω : FinitePerimeter E) : BVFunction E :=
  Classical.choose (characteristic_isBV Ω)

/-- The underlying function of `ofFinitePerimeter Ω` is exactly the
indicator function of $\Omega$'s carrier (using
`Set.indicator` to avoid a `Decidable (x ∈ Ω.carrier)` typeclass
side condition; equivalent to $\chi_\Omega(x) = 1$ if $x \in \Omega$,
else $0$). -/
theorem ofFinitePerimeter_eq_indicator (Ω : FinitePerimeter E) (x : E) :
    (ofFinitePerimeter Ω) x = Ω.carrier.indicator (fun _ => (1 : ℝ)) x :=
  (Classical.choose_spec (characteristic_isBV Ω)).1 x

/-- The total variation of $\chi_\Omega$ as a BV function equals the
perimeter measure on the whole space: $\|D\chi_\Omega\|(E) = |D\chi_\Omega|(E)$
(Maggi 2012 Proposition 13.1). -/
@[simp] theorem totalVariation_ofFinitePerimeter (Ω : FinitePerimeter E) :
    totalVariation (ofFinitePerimeter Ω) = Ω.perimMeasure Set.univ :=
  (Classical.choose_spec (characteristic_isBV Ω)).2

end CharacteristicIsBV


end Isoperimetric
end GeometricMeasureTheory
