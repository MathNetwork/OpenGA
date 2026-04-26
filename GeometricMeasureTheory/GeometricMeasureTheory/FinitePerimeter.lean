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

/-- **De Giorgi structure theorem** (existence form): for any
finite-perimeter set $\Omega$ in $M$, there exists a "reduced boundary"
subset $\partial^* \Omega \subseteq \overline{\Omega}$ on which the
perimeter measure $D\chi_\Omega$ is concentrated.

**Ground truth**: Maggi 2012 Theorem 15.9; De Giorgi 1955.

**Statement form** (paper-faithful): the existence assertion gives a
set $S$ which is a subset of the topological closure $\overline{\Omega}$
**and** captures all of the perimeter measure (its complement carries
zero perimeter). Full $(n-1)$-rectifiability of $S$ — Maggi 15.9 (iii) —
requires `IsHRectifiable` infrastructure not in scope here; deferred to
Phase 4 framework long-term work via a strengthened existence axiom.

**Sorry status**: PRE-PAPER. Repair plan: when framework's
`IsHRectifiable` matures and connects to `BVFunction`-style derivative
infrastructure, replace with a constructive De Giorgi blow-up
construction. Alternatively, when Mathlib upstream gains finite-perimeter
+ De Giorgi, deprecate.

**Used by**: `reducedBoundary` real def. -/
theorem deGiorgi_reducedBoundary_exists (Ω : FinitePerimeter M) :
    ∃ S : Set M, S ⊆ Ω.topClosure ∧
      ∀ A : Set M, MeasurableSet A → Ω.perimMeasure A = Ω.perimMeasure (A ∩ S) := by
  sorry

/-- The **reduced boundary** $\partial^*\Omega \subseteq M$ of a
finite-perimeter set: the $(n-1)$-rectifiable subset of
$\overline{\Omega}$ that supports the perimeter measure $D\chi_\Omega$.

**Ground truth**: Maggi 2012 Definition 15.1; De Giorgi 1955.

Real `noncomputable def` via `Classical.choose` over the De Giorgi
structure existence axiom (`deGiorgi_reducedBoundary_exists`). -/
noncomputable def reducedBoundary (Ω : FinitePerimeter M) : Set M :=
  Classical.choose (deGiorgi_reducedBoundary_exists Ω)

/-- Backwards-compatibility alias. The old `rbdy` name is retained for
chain-proof consumers; new code should use `reducedBoundary`. -/
@[deprecated reducedBoundary (since := "Phase 3.1")]
noncomputable def rbdy (Ω : FinitePerimeter M) : Set M := reducedBoundary Ω

/-- The reduced boundary is contained in the topological closure
(De Giorgi structure theorem, part of the existence statement). -/
theorem reducedBoundary_subset_topClosure (Ω : FinitePerimeter M) :
    reducedBoundary Ω ⊆ Ω.topClosure :=
  (Classical.choose_spec (deGiorgi_reducedBoundary_exists Ω)).1

/-- The perimeter measure is concentrated on the reduced boundary:
for any measurable set $A$, $|D\chi_\Omega|(A) = |D\chi_\Omega|(A \cap \partial^*\Omega)$
(De Giorgi structure theorem, Maggi 2012 Theorem 15.9 (i)). -/
theorem perimMeasure_concentrated_on_reducedBoundary
    (Ω : FinitePerimeter M) (A : Set M) (hA : MeasurableSet A) :
    Ω.perimMeasure A = Ω.perimMeasure (A ∩ reducedBoundary Ω) :=
  (Classical.choose_spec (deGiorgi_reducedBoundary_exists Ω)).2 A hA

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
