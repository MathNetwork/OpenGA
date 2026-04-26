import AltRegularity.Basic

/-!
# AltRegularity.GMT.FinitePerimeter

Sets of finite perimeter in a metric measurable space (also known in the
GMT literature as Caccioppoli sets).

A finite-perimeter set is recorded as a Borel-measurable subset of $M$
together with its total perimeter. The reduced boundary $\partial^*\Omega$
and the localized perimeter $\mathrm{Per}(\Omega, U)$ are declared as
opaque, deferring their definition through the BV theory of indicator
functions to a future refinement.

This is part of Section 2 (Preliminaries) of the paper.
-/

namespace AltRegularity

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]

/-- A set of finite perimeter in $M$. -/
structure FinitePerimeter (M : Type*)
    [MetricSpace M] [MeasurableSpace M] [BorelSpace M] where
  /-- The underlying carrier set $\Omega \subset M$. -/
  carrier : Set M
  /-- The carrier is Borel-measurable. -/
  isMeasurable : MeasurableSet carrier
  /-- The total perimeter $\mathrm{Per}(\Omega) \in [0, \infty)$. -/
  perim : NNReal

namespace FinitePerimeter

/-- Topological closure $\overline{\Omega}$. -/
def topClosure (Ω : FinitePerimeter M) : Set M := closure Ω.carrier

/-- Topological interior $\mathrm{int}(\Omega)$. -/
def topInterior (Ω : FinitePerimeter M) : Set M := interior Ω.carrier

/-- The reduced boundary $\partial^*\Omega$ as a subset of $M$.
A foundational definition through BV/indicator functions is deferred. -/
opaque rbdy : FinitePerimeter M → Set M

/-- Localized perimeter $\mathrm{Per}(\Omega, U) = |D\chi_\Omega|(U)$
on a Borel set $U \subset M$. -/
opaque perimOn : FinitePerimeter M → Set M → ℝ

/-- The total perimeter is non-negative as a real number. -/
theorem perim_nonneg (Ω : FinitePerimeter M) : (0 : ℝ) ≤ Ω.perim :=
  NNReal.coe_nonneg _

/-- Localized perimeter is non-negative. -/
theorem perimOn_nonneg (Ω : FinitePerimeter M) (U : Set M) :
    0 ≤ perimOn Ω U := by sorry

/-- Localized perimeter on the whole space recovers the total perimeter. -/
theorem perimOn_univ (Ω : FinitePerimeter M) :
    perimOn Ω Set.univ = (Ω.perim : ℝ) := by sorry

/-- The reduced boundary is a subset of the topological closure. -/
theorem rbdy_subset_topClosure (Ω : FinitePerimeter M) :
    rbdy Ω ⊆ Ω.topClosure := by sorry

/-- Every point of $M$ stands in exactly one of three relations to a
finite-perimeter set $\Omega$: outside the closure, on the reduced
boundary, or in the topological interior. -/
theorem trichotomy (Ω : FinitePerimeter M) (p : M) :
    p ∉ Ω.topClosure ∨ p ∈ rbdy Ω ∨ p ∈ Ω.topInterior := by sorry

end FinitePerimeter

end AltRegularity
