import AltRegularity.GMT.FinitePerimeter

/-!
# AltRegularity.GMT.FlatDistance

Flat distance pseudometric on finite-perimeter sets.

For two Caccioppoli sets $\Omega_1, \Omega_2 \subset M$, the **flat
distance** is $\mathcal{F}(\Omega_1, \Omega_2) := \mathrm{Vol}(\Omega_1
\triangle \Omega_2)$. This is the pseudometric used in paper
Definition 3.1 to define $\mathcal{F}$-continuity of a sweepout.

The leaf-level definition $\mathrm{Vol}(\Omega_1 \triangle \Omega_2)$
requires a reference volume measure on $M$ and is left as a sorry'd
opaque primitive pending Mathlib's volume-form-on-manifold infrastructure.
-/

namespace AltRegularity

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]

namespace FinitePerimeter

/-- The **flat distance** $\mathcal{F}(\Omega_1, \Omega_2) :=
\mathrm{Vol}(\Omega_1 \triangle \Omega_2)$.

Encoded as an opaque leaf primitive pending a reference volume measure
on $M$. -/
opaque flatDist : FinitePerimeter M → FinitePerimeter M → ℝ

end FinitePerimeter

end AltRegularity
