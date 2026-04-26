import AltRegularity.Basic
import AltRegularity.GMT.FinitePerimeter
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-!
# AltRegularity.GMT.Varifold

Varifolds in a metric measurable space.

A full $n$-varifold framework requires Radon measures on
$M \times \mathrm{Gr}(n, T_pM)$ which is not yet in Mathlib. As a
provisional implementation sufficient for this formalization's chain
proofs, we model an $n$-varifold by its mass measure $\|V\|$ alone — a
finite Borel measure on $M$ — deferring tangent-plane data to a
subsequent refinement.

This is part of Section 2 (Preliminaries) of the paper.
-/

namespace AltRegularity

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]

/-- An $n$-varifold in $M$ (with $n+1 = \dim M$), modeled provisionally
by its mass measure $\|V\|$ as a finite Borel measure on $M$. The full
varifold structure with tangent-plane data on $M \times \mathrm{Gr}(n,
T_pM)$ is deferred. -/
structure Varifold (M : Type*)
    [MetricSpace M] [MeasurableSpace M] [BorelSpace M] where
  /-- The mass measure $\|V\|$ as a Borel measure on $M$. -/
  massMeasure : MeasureTheory.Measure M
  /-- The mass measure has finite total mass. -/
  isFiniteMeasure : MeasureTheory.IsFiniteMeasure massMeasure

/-- The type of $n$-varifolds in $M$ is non-empty: the zero varifold
provides a concrete witness. -/
instance Varifold.instNonempty : Nonempty (Varifold M) :=
  ⟨{ massMeasure := 0
     isFiniteMeasure := ⟨by simp⟩ }⟩

namespace Varifold

/-- Total mass $\|V\|(M)$. -/
def mass (V : Varifold M) : ℝ := (V.massMeasure Set.univ).toReal

/-- Localized mass $\|V\|(U)$ on a Borel set $U \subset M$. -/
def massOn (V : Varifold M) (U : Set M) : ℝ := (V.massMeasure U).toReal

/-- Topological support $\mathrm{spt}\|V\|$: points such that every
neighborhood has positive mass. -/
def support (V : Varifold M) : Set M :=
  {p | ∀ U ∈ nhds p, V.massMeasure U ≠ 0}

/-- Pointwise density $\Theta(\|V\|, p) := \lim_{r \to 0} \|V\|(B_r(p))/(\omega_n r^n)$.

The construction requires Mathlib infrastructure for the monotonicity-formula
limit (Hausdorff $n$-measure, ratio limits) and is deferred to a later
refinement. -/
noncomputable def density (V : Varifold M) (p : M) : ℝ := by sorry

/-- Densities are non-negative. -/
theorem density_nonneg (V : Varifold M) (p : M) : 0 ≤ density V p := by sorry

/-- Total mass is non-negative. -/
theorem mass_nonneg (V : Varifold M) : 0 ≤ mass V :=
  ENNReal.toReal_nonneg

/-- Localized mass is non-negative. -/
theorem massOn_nonneg (V : Varifold M) (U : Set M) : 0 ≤ massOn V U :=
  ENNReal.toReal_nonneg

/-- Localized mass is monotone in the set. -/
theorem massOn_mono (V : Varifold M) {U W : Set M} (h : U ⊆ W) :
    massOn V U ≤ massOn V W := by
  haveI := V.isFiniteMeasure
  exact ENNReal.toReal_mono (MeasureTheory.measure_lt_top V.massMeasure W).ne
    (MeasureTheory.measure_mono h)

/-- The total mass equals the localized mass on the whole space. -/
theorem massOn_univ (V : Varifold M) : massOn V Set.univ = mass V := rfl

/-- $p \in \mathrm{spt}\|V\|$ iff every open ball around $p$ has positive
local mass. -/
theorem mem_support_iff (V : Varifold M) (p : M) :
    p ∈ support V ↔ ∀ r > 0, 0 < massOn V (Metric.ball p r) := by sorry

/-- **Weak varifold convergence** of a sequence $V_i \to V$.

Encoded as an opaque leaf primitive: in full generality, weak convergence
of varifolds means convergence of the underlying Radon measures on the
Grassmann bundle $G_n(M)$ when paired against compactly supported
continuous test functions. -/
opaque VarifoldConverge : (ℕ → Varifold M) → Varifold M → Prop

/-- The **regular set** $\mathrm{reg}\,V$ of a varifold: the largest
open subset of $\mathrm{spt}\|V\|$ on which the support is locally a
smooth embedded hypersurface.

Encoded as an opaque leaf primitive pending Mathlib's smooth-manifold
infrastructure. -/
opaque regular : Varifold M → Set M

/-- The **singular set** $\mathrm{sing}\,V := \mathrm{spt}\|V\| \setminus
\mathrm{reg}\,V$ — points of the support that are not regular.

Defined explicitly so the structure "support minus regular part" is
visible to the Lean kernel. -/
def sing (V : Varifold M) : Set M := support V \ regular V

/-- The **boundary varifold** $|\partial^*\Omega|$ associated to a
finite-perimeter set: the rectifiable $n$-varifold supported on the
reduced boundary $\partial^*\Omega$ with multiplicity 1. -/
noncomputable opaque ofBoundary : FinitePerimeter M → Varifold M

end Varifold

end AltRegularity
