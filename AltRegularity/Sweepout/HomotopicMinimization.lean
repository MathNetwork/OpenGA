import AltRegularity.Sweepout.NonExcessive
import AltRegularity.Sweepout.MinMaxLimit

/-!
# AltRegularity.Sweepout.HomotopicMinimization

One-sided homotopic minimization (Definition 3.X / Proposition 7.2 in the
paper). For a non-excessive ONVP sweepout, the slices at a critical
parameter $t_0$ have a homotopic-minimizer property: any one-sided
ambient isotopy of $\partial^*\Omega_{t_0}$ that does not increase $t$
beyond $t_0$ is bounded below by the original perimeter.

This property substitutes for the classical almost-minimizing condition
of Schoen–Simon (1981) and provides the stability needed for the smooth
regularity theorem (`AltRegularity.Regularity.SmoothRegularity`).

The **set of non-homotopic-minimizing points** $\mathfrak{h}_{\mathrm{nm}}(V)$
of the limit varifold and its finiteness from
[CLS22, Proposition 3.1] are also recorded here as the input to the
stability proof in `AltRegularity.Regularity.StabilityVerification`.
-/

namespace AltRegularity

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]

namespace Sweepout

/-- $\Phi$ at $t_0$ has the **one-sided homotopic-minimizer** property
on the inner side: the slice $\Omega_{t_0}$ is a homotopic perimeter
minimizer among ambient isotopies that do not enlarge it. -/
opaque InnerHomotopicMinimizer : Sweepout M → ℝ → Prop

/-- Outer homotopic-minimizer property (the symmetric version). -/
opaque OuterHomotopicMinimizer : Sweepout M → ℝ → Prop

/-- **Non-excessive ⟹ one-sided homotopic minimization.**
The non-excessive property at a critical $t_0$ implies the inner (and
outer) homotopic-minimizer property of the slice $\Omega_{t_0}$. -/
theorem innerHomotopicMinimizer_of_nonExcessive
    {Φ : Sweepout M} (h : NonExcessive Φ) (t₀ : ℝ) (hcrit : Critical Φ t₀) :
    InnerHomotopicMinimizer Φ t₀ := by sorry

/-- The outer companion of `innerHomotopicMinimizer_of_nonExcessive`. -/
theorem outerHomotopicMinimizer_of_nonExcessive
    {Φ : Sweepout M} (h : NonExcessive Φ) (t₀ : ℝ) (hcrit : Critical Φ t₀) :
    OuterHomotopicMinimizer Φ t₀ := by sorry

/-! ## Non-homotopic-minimizing points and their finiteness -/

/-- The **set of non-homotopic-minimizing points** $\mathfrak{h}_{\mathrm{nm}}(V)$
of the limit varifold $V$: points $P \in \mathrm{spt}\|V\|$ at which $V$
fails to be one-sided homotopic minimizing in any neighborhood. -/
opaque hnm : Varifold M → Set M

/-- **Finiteness of $\mathfrak{h}_{\mathrm{nm}}(V)$** ([CLS22, Proposition 3.1]).
For the limit varifold of a non-excessive ONVP sweepout, the set of
non-homotopic-minimizing points is finite. The finiteness uses both the
non-excessive property and the nestedness of the sweepout. -/
theorem hnm_finite_of_nonExcessive
    {Φ : Sweepout M} {t₀ : ℝ} {V : Varifold M}
    (hne : NonExcessive Φ) (hcrit : Critical Φ t₀)
    (hlim : MinMaxLimit Φ t₀ V) :
    (hnm V).Finite := by sorry

end Sweepout

end AltRegularity
