import Sweepout.MinMaxLimit

open GeometricMeasureTheory

namespace Sweepout

/-!
# AltRegularity.Sweepout.MassCancellation

Mass cancellation at a critical parameter (Definition 3.5 of the paper).

A min-max sequence $t_i \to t_0$ with $|\partial^*\Omega_{t_i}| \to V$
exhibits **mass cancellation** at $t_0$ if the perimeter of the limit
slice $\Omega_{t_0}$ is strictly less than the width $W$:
$$\mathrm{Per}(\Omega_{t_0}) < W.$$
The complementary case is the **no-mass-cancellation** case
$\mathrm{Per}(\Omega_{t_0}) = W$, which is treated by the De Lellis–Tasnady
integrality criterion.

This file establishes:
  * The two cases form a **dichotomy** (`mass_cancellation_or_no`):
    every parameter is in exactly one of them.
  * The two cases are **mutually exclusive**
    (`not_both_mass_cancellation_and_no`).
  * In the degenerate case `width Φ = 0`, every slice has zero perimeter
    (`perim_eq_zero_of_width_eq_zero`).

The dichotomy and exclusivity are proved formally from the coherence
axiom `perim_slice_le_width`, which captures the definitional content of
$W(\Phi) = \sup_t \mathrm{Per}(\Phi(t))$.
-/



variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M] [MeasureTheory.MeasureSpace M]


/-- Mass cancellation at $t_0$ in $\Phi$: the perimeter of the limit slice
is strictly less than the width. -/
def MassCancellation (Φ : Sweepout M) (t₀ : ℝ) : Prop :=
  ((Φ.slice t₀).perim : ℝ) < width Φ

/-- No mass cancellation: the perimeter of the limit slice equals the width. -/
def NoMassCancellation (Φ : Sweepout M) (t₀ : ℝ) : Prop :=
  ((Φ.slice t₀).perim : ℝ) = width Φ

/-- **Coherence axiom for the width.** Every slice has perimeter at most the
width of the sweepout. This is the definitional content of $W(\Phi)$ as a
supremum and the only fact about `width` needed to establish the dichotomy.

In a future refinement that gives `width` an explicit definition (e.g., as
`⨆ t ∈ Set.Icc 0 1, (Φ.slice t).perim`), this becomes a `theorem` proved
by the supremum bound. -/
theorem perim_slice_le_width (Φ : Sweepout M) (t : ℝ) :
    ((Φ.slice t).perim : ℝ) ≤ width Φ := by sorry

/-- **Dichotomy of mass cancellation.** Every parameter $t_0$ falls in
exactly one of the two cases: either mass cancellation
($\mathrm{Per}(\Phi(t_0)) < W$) or no mass cancellation
($\mathrm{Per}(\Phi(t_0)) = W$). -/
theorem mass_cancellation_or_no (Φ : Sweepout M) (t₀ : ℝ) :
    MassCancellation Φ t₀ ∨ NoMassCancellation Φ t₀ :=
  lt_or_eq_of_le (perim_slice_le_width Φ t₀)

/-- The two cases are mutually exclusive. -/
theorem not_both_mass_cancellation_and_no (Φ : Sweepout M) (t₀ : ℝ) :
    ¬ (MassCancellation Φ t₀ ∧ NoMassCancellation Φ t₀) := by
  rintro ⟨h_lt, h_eq⟩
  exact (lt_iff_le_and_ne.mp h_lt).2 h_eq

/-- If the width vanishes, every slice has zero perimeter. -/
theorem perim_eq_zero_of_width_eq_zero
    (Φ : Sweepout M) (h : width Φ = 0) (t : ℝ) :
    ((Φ.slice t).perim : ℝ) = 0 := by
  have h_le : ((Φ.slice t).perim : ℝ) ≤ 0 := h ▸ perim_slice_le_width Φ t
  exact le_antisymm h_le (Φ.slice t).perim_nonneg

/-- **(c) of paper §6.1 Theorem 6.3: No mass cancellation → perimeter
convergence.** The no-mass-cancellation hypothesis is exactly the
statement that perimeters of the min-max sequence converge to the
perimeter of the limit slice:
$\mathrm{Per}(\Omega(t_i)) = \mathbf{M}(\Phi(t_i)) \to W = \mathbf{M}(\Phi(t_0))
= \mathrm{Per}(\Omega(t_0))$.

The 4-step equality chain in the paper proof:
  (1) $\mathrm{Per}(\Omega(t_i)) = \mathbf{M}(\Phi(t_i))$ — perimeter
      equals current mass for a Caccioppoli boundary varifold (definitional).
  (2) $\mathbf{M}(\Phi(t_i)) \to W$ — definition of min-max sequence;
      packaged in our framework as `minmax_mass_eq_width` applied to any
      varifold limit of the sequence.
  (3) $W = \mathbf{M}(\Phi(t_0))$ — `NoMassCancellation` (definition).
  (4) $\mathbf{M}(\Phi(t_0)) = \mathrm{Per}(\Omega(t_0))$ — same as (1)
      at the limit parameter (definitional).

The two equality steps (1) and (4) are folded into the `(Φ.slice t₀).perim`
notation; step (2) is `minmax_mass_eq_width`; step (3) is the input
hypothesis `hno`. -/
theorem perimeterConvergence_of_noMassCancellation
    {Φ : Sweepout M} {t₀ : ℝ} {V : Varifold M}
    (_hlim : MinMaxLimit Φ t₀ V) (hno : NoMassCancellation Φ t₀) :
    PerimeterConverge Φ t₀ := by
  -- Unfold the def: take any min-max varifold limit V'.
  intro V' hlim'
  -- (2) min-max ⟹ Varifold.mass V' = width Φ.
  rw [minmax_mass_eq_width hlim']
  -- (3) NoMassCancellation: (Φ.slice t₀).perim = width Φ; symm gives goal.
  exact hno.symm



end Sweepout
