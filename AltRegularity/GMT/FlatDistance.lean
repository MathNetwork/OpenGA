import AltRegularity.GMT.FinitePerimeter
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

/-!
# AltRegularity.GMT.FlatDistance

For two Caccioppoli sets $\Omega_1, \Omega_2 \subset M$, the **flat
distance** is $\mathcal{F}(\Omega_1, \Omega_2) := \mathrm{Vol}(\Omega_1
\,\triangle\, \Omega_2)$. This is the pseudometric used in paper
Definition 3.1 to define $\mathcal{F}$-continuity of a sweepout.

Defined explicitly in terms of `MeasureTheory.volume` (Mathlib's
`[MeasureSpace M]` default measure). For the framework's manifold
ambient $M$, the reference volume is the Riemannian volume form;
formalized as the `MeasureSpace` typeclass instance to be supplied
downstream.
-/

namespace AltRegularity

namespace FinitePerimeter

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasureTheory.MeasureSpace M]

/-- The **flat distance** between two finite-perimeter sets:
$\mathcal{F}(\Omega_1, \Omega_2) := \mathrm{Vol}(\Omega_1
\,\triangle\, \Omega_2)$.

Specialization of the flat norm on integral $n$-currents to indicator
functions of Caccioppoli sets, where boundary-minimization in the
general flat norm collapses to the symmetric-difference volume.

**Ground truth**: Simon 1983 §31; specialization Maggi 2012 §15.

**Used by**: `Sweepout.FContinuous` def (`Sweepout/Defs.lean`). -/
noncomputable def flatDist (Ω₁ Ω₂ : FinitePerimeter M) : ℝ :=
  (MeasureTheory.volume (symmDiff Ω₁.carrier Ω₂.carrier)).toReal

end FinitePerimeter

end AltRegularity
