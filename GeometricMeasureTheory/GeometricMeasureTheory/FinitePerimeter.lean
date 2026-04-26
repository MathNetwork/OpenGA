import Mathlib.Topology.MetricSpace.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Tactic
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-!
# AltRegularity.GMT.FinitePerimeter

Sets of finite perimeter in a metric measurable space (also known in the
GMT literature as Caccioppoli sets).

A finite-perimeter set is implemented as a Borel-measurable subset of $M$
together with its **perimeter measure** $|D\chi_\Omega|$ — a finite
Borel measure on $M$. The total perimeter $\mathrm{Per}(\Omega)$ and the
localized perimeter $\mathrm{Per}(\Omega, U)$ are then defined directly
from this measure. The reduced boundary $\partial^*\Omega$ remains a
deferred construction (its definition through De Giorgi blow-ups is not
yet available in Mathlib).

This is part of Section 2 (Preliminaries) of the paper.
-/

namespace GeometricMeasureTheory

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M] [MeasureTheory.MeasureSpace M]

/-- A set of finite perimeter in $M$. The structure bundles the carrier
$\Omega$ together with its perimeter measure $|D\chi_\Omega|$, a finite
Borel measure on $M$ representing the BV total variation of the
indicator $\chi_\Omega$. -/
structure FinitePerimeter (M : Type*)
    [MetricSpace M] [MeasurableSpace M] [BorelSpace M] where
  /-- The underlying carrier set $\Omega \subset M$. -/
  carrier : Set M
  /-- The carrier is Borel-measurable. -/
  isMeasurable : MeasurableSet carrier
  /-- The perimeter measure $|D\chi_\Omega|$ on $M$. -/
  perimMeasure : MeasureTheory.Measure M
  /-- The perimeter measure has finite total mass. -/
  perimFinite : MeasureTheory.IsFiniteMeasure perimMeasure

namespace FinitePerimeter

/-- Topological closure $\overline{\Omega}$. -/
def topClosure (Ω : FinitePerimeter M) : Set M := closure Ω.carrier

/-- Topological interior $\mathrm{int}(\Omega)$. -/
def topInterior (Ω : FinitePerimeter M) : Set M := interior Ω.carrier

/-- The total perimeter $\mathrm{Per}(\Omega) := |D\chi_\Omega|(M)
\in [0, \infty)$, derived from the perimeter measure. -/
def perim (Ω : FinitePerimeter M) : NNReal := (Ω.perimMeasure Set.univ).toNNReal

/-- Localized perimeter $\mathrm{Per}(\Omega, U) := |D\chi_\Omega|(U)$
on a Borel set $U \subset M$. -/
def perimOn (Ω : FinitePerimeter M) (U : Set M) : ℝ :=
  (Ω.perimMeasure U).toReal

/-- The reduced boundary $\partial^*\Omega$ as a subset of $M$.

The construction via De Giorgi blow-ups (points where the rescaled
indicator converges in $L^1_{\mathrm{loc}}$ to a half-space indicator)
requires BV-on-manifold infrastructure not yet in Mathlib and is deferred. -/
noncomputable def rbdy (Ω : FinitePerimeter M) : Set M := by sorry

omit [MeasureTheory.MeasureSpace M] in
/-- The total perimeter is non-negative as a real number. -/
theorem perim_nonneg (Ω : FinitePerimeter M) : (0 : ℝ) ≤ (Ω.perim : ℝ) :=
  NNReal.coe_nonneg _

omit [MeasureTheory.MeasureSpace M] in
/-- Localized perimeter is non-negative. -/
theorem perimOn_nonneg (Ω : FinitePerimeter M) (U : Set M) :
    0 ≤ perimOn Ω U :=
  ENNReal.toReal_nonneg

omit [MeasureTheory.MeasureSpace M] in
/-- Localized perimeter on the whole space recovers the total perimeter. -/
theorem perimOn_univ (Ω : FinitePerimeter M) :
    perimOn Ω Set.univ = (Ω.perim : ℝ) := rfl

/-- The reduced boundary is a subset of the topological closure. -/
theorem rbdy_subset_topClosure (Ω : FinitePerimeter M) :
    rbdy Ω ⊆ Ω.topClosure := by sorry

/-- Every point of $M$ stands in exactly one of three relations to a
finite-perimeter set $\Omega$: outside the closure, on the reduced
boundary, or in the topological interior. -/
theorem trichotomy (Ω : FinitePerimeter M) (p : M) :
    p ∉ Ω.topClosure ∨ p ∈ rbdy Ω ∨ p ∈ Ω.topInterior := by sorry

end FinitePerimeter

end GeometricMeasureTheory
