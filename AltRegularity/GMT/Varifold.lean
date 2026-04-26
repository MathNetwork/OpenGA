import AltRegularity.Basic

/-!
# AltRegularity.GMT.Varifold

Varifolds in a metric measurable space.

Mathlib does not yet contain a codimension-1 varifold framework, so we
declare the type and its main operations as opaque, with structural facts
recorded as `theorem ... := by sorry`. A foundational definition (Radon
measures on $M \times \mathrm{Gr}(n, T_pM)$) is deferred to future work.

This is part of Section 2 (Preliminaries) of the paper.
-/

namespace AltRegularity

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]

/-- An $n$-varifold in $M$ (with $n+1 = \dim M$). -/
opaque Varifold (M : Type*)
    [MetricSpace M] [MeasurableSpace M] [BorelSpace M] : Type

/-- The type of $n$-varifolds in $M$ is non-empty: e.g., the zero varifold.
This is asserted as a sorry'd instance because `Varifold` is opaque; once
`Varifold` is defined as a Radon measure on $M \times \mathrm{Gr}(n, T_pM)$,
the zero measure provides a concrete witness. -/
instance Varifold.instNonempty :
    Nonempty (Varifold M) := by sorry

namespace Varifold

/-- Total mass $\|V\|(M)$. -/
opaque mass : Varifold M → ℝ

/-- Localized mass $\|V\|(U)$ on a Borel set $U \subset M$. -/
opaque massOn : Varifold M → Set M → ℝ

/-- Topological support $\mathrm{spt}\|V\|$. -/
opaque support : Varifold M → Set M

/-- Pointwise density $\Theta(\|V\|, p) := \lim_{r \to 0} \|V\|(B_r(p))/(\omega_n r^n)$. -/
opaque density : Varifold M → M → ℝ

/-- Densities are non-negative. -/
theorem density_nonneg (V : Varifold M) (p : M) : 0 ≤ density V p := by sorry

/-- Total mass is non-negative. -/
theorem mass_nonneg (V : Varifold M) : 0 ≤ mass V := by sorry

/-- Localized mass is non-negative. -/
theorem massOn_nonneg (V : Varifold M) (U : Set M) : 0 ≤ massOn V U := by sorry

/-- Localized mass is monotone in the set. -/
theorem massOn_mono (V : Varifold M) {U W : Set M} (h : U ⊆ W) :
    massOn V U ≤ massOn V W := by sorry

/-- The total mass equals the localized mass on the whole space. -/
theorem massOn_univ (V : Varifold M) : massOn V Set.univ = mass V := by sorry

/-- $p \in \mathrm{spt}\|V\|$ iff every open ball around $p$ has positive
local mass. -/
theorem mem_support_iff (V : Varifold M) (p : M) :
    p ∈ support V ↔ ∀ r > 0, 0 < massOn V (Metric.ball p r) := by sorry

end Varifold

end AltRegularity
