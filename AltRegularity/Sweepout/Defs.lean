import AltRegularity.GMT.FinitePerimeter

/-!
# AltRegularity.Sweepout.Defs

The basic notion of a sweepout: a 1-parameter family of sets of finite perimeter
indexed by $[0,1]$, together with the width $W(\Phi)$. This is the input
to the CLS22 framework developed in Section 3 of the paper.
-/

namespace AltRegularity

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]

/-- A 1-parameter family of sets of finite perimeter in $M$, indexed by $\mathbb{R}$
(in practice the interval $[0,1]$). -/
structure Sweepout (M : Type*)
    [MetricSpace M] [MeasurableSpace M] [BorelSpace M] where
  /-- The slice $\Phi(t)$ at parameter $t$. -/
  slice : ℝ → FinitePerimeter M

namespace Sweepout

/-- Width $W(\Phi) := \sup_{t \in [0,1]} \mathrm{Per}(\Phi(t))$. -/
opaque width : Sweepout M → ℝ

end Sweepout

end AltRegularity
