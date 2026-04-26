import Mathlib.Topology.MetricSpace.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Tactic
import GeometricMeasureTheory.FinitePerimeter
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

namespace GeometricMeasureTheory

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M] [MeasureTheory.MeasureSpace M]

/-- An $n$-varifold in $M$ (with $n+1 = \dim M$), modeled provisionally
by its mass measure $\|V\|$ as a finite Borel measure on $M$ together
with its intrinsic dimension $n$. The full varifold structure with
tangent-plane data on $M \times \mathrm{Gr}(n, T_pM)$ is deferred. -/
structure Varifold (M : Type*)
    [MetricSpace M] [MeasurableSpace M] [BorelSpace M] where
  /-- Intrinsic dimension $n$ of the varifold. -/
  dim : ℕ
  /-- The mass measure $\|V\|$ as a Borel measure on $M$. -/
  massMeasure : MeasureTheory.Measure M
  /-- The mass measure has finite total mass. -/
  isFiniteMeasure : MeasureTheory.IsFiniteMeasure massMeasure

/-- The type of $n$-varifolds in $M$ is non-empty: the zero varifold
(at dimension $0$) provides a concrete witness. -/
instance Varifold.instNonempty : Nonempty (Varifold M) :=
  ⟨{ dim := 0
     massMeasure := 0
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

/-- Pointwise density $\Theta(\|V\|, p) := \lim_{r \to 0} \|V\|(B_r(p))/(\omega_n r^n)$
where $n = V.\mathrm{dim}$.

Defined as the `Filter.limsup` of `‖V‖(B_r(p)) / r^n` as $r \to 0^+$,
omitting the unit-ball-volume constant $\omega_n$ (the constant is
non-zero, so it cancels in sign-comparison statements like $\Theta > 0$;
exact-value statements like $\Theta = k$ are interpreted modulo the
$\omega_n$ normalization).

**Ground truth**: Simon 1983 §17 (monotonicity formula for stationary
varifolds; existence of density at every point); §10–§11 (general
density-of-measure theory).

For non-stationary varifolds the limit may not exist; `limsup` is the
canonical convention (existence of the limit follows for stationary
varifolds via Simon §17 monotonicity, but the framework returns
`limsup` unconditionally to avoid existence hypotheses on callers). -/
noncomputable def density (V : Varifold M) (p : M) : ℝ :=
  Filter.limsup
    (fun r : ℝ => (V.massMeasure (Metric.ball p r)).toReal / r ^ V.dim)
    (nhdsWithin (0 : ℝ) (Set.Ioi 0))

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

/-- **Weak varifold convergence** $V_i \to V$.

Defined via pairing of mass measures against compactly supported
continuous test functions on $M$:
$$\int_M \varphi \, d\|V_i\| \to \int_M \varphi \, d\|V\|, \quad
\forall \varphi \in C_c(M; \mathbb{R}).$$

This is the **mass measure** weak-convergence form, not the full
varifold weak-* convergence on the Grassmann bundle $G_n(M)$. The
Grassmann form requires upgrading `Varifold` to carry a measure on
$M \times G_n(M)$ instead of just the mass measure on $M$, deferred
to a future round. The mass-measure form suffices for paper §6
applications (which only use mass measure / support information).

**Ground truth**: Simon 1983 §38 (varifold convergence as weak-*
convergence of Radon measures on the Grassmann bundle, paired against
compactly supported continuous test functions); Allard 1972 §3.

**Used by**: `Sweepout.MinMaxLimit` def (`Sweepout/MinMaxLimit.lean`). -/
def VarifoldConverge (Vᵢ : ℕ → Varifold M) (V : Varifold M) : Prop :=
  ∀ φ : M → ℝ, Continuous φ → HasCompactSupport φ →
    Filter.Tendsto
      (fun i => ∫ x, φ x ∂(Vᵢ i).massMeasure)
      Filter.atTop
      (nhds (∫ x, φ x ∂V.massMeasure))

/-- The **regular set** $\mathrm{reg}\,V$ of a varifold: the largest
open subset of $\mathrm{spt}\|V\|$ on which the support is locally a
smooth embedded hypersurface.

**Ground truth**: Simon 1983 §41 (regular vs singular set for stationary
integral varifolds); Wickramasekera 2014 §2 (definition of $\mathrm{reg}\,V$
in the manifold setting).

**Why opaque**: a paper-faithful `def` would require Mathlib's
smooth-manifold-with-corners infrastructure (`IsManifold` typeclass,
which presupposes `[NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
[NormedSpace 𝕜 E] [ChartedSpace E M] (I : ModelWithCorners 𝕜 E E)
[IsManifold I n M]`) plus a notion of "embedded hypersurface" (not in
Mathlib). The typeclass propagation alone would cascade through ~27
framework files and substantively change the ambient typeclass profile.
A "sub-primitive" workaround (introducing an opaque `IsLocallyHypersurface`
predicate) achieves only net-zero opaque-count reduction.

**Used by**: `Varifold.sing` def (in this file). -/
opaque regular : Varifold M → Set M

/-- The **singular set** $\mathrm{sing}\,V := \mathrm{spt}\|V\| \setminus
\mathrm{reg}\,V$ — points of the support that are not regular.

Defined explicitly so the structure "support minus regular part" is
visible to the Lean kernel. -/
def sing (V : Varifold M) : Set M := support V \ regular V

/-- The **boundary varifold** $|\partial^*\Omega|$ associated to a
finite-perimeter set: the rectifiable $n$-varifold supported on the
reduced boundary $\partial^*\Omega$ with multiplicity 1.

**Ground truth**: Simon 1983 §27 (BV / finite-perimeter sets) + §38
(associated varifold of an integer-rectifiable current); De Giorgi
structure theorem (Maggi 2012, Ch. 15) for the reduced boundary as a
rectifiable set.

**Used by**: `Sweepout.MinMaxLimit` def (`Sweepout/MinMaxLimit.lean`),
`dlt_criterion` (`Integrality/PerimeterConvergence.lean`). -/
noncomputable opaque ofBoundary : FinitePerimeter M → Varifold M

end Varifold

end GeometricMeasureTheory
