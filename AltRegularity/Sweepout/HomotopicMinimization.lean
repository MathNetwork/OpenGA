import AltRegularity.Sweepout.NonExcessive

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

end Sweepout

end AltRegularity
