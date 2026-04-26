import AltRegularity.Sweepout.Defs

/-!
# AltRegularity.Sweepout.ONVP

The Optimal Nested Volume-Parametrized (ONVP) property of a sweepout
(Definition 3.2 in the paper): the slices are ordered by inclusion in $t$
and parametrized so that $\mathrm{Vol}(\Phi(t)) = t \cdot \mathrm{Vol}(M)$.

The defining content is recorded structurally; only the consequence
`onvp_nested` is needed downstream.
-/

namespace AltRegularity

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]

namespace Sweepout

/-- $\Phi$ is Optimal Nested Volume-Parametrized: ascending nested in $t$
and volume-parametrized by $t \mapsto t \cdot \mathrm{Vol}(M)$. -/
opaque ONVP : Sweepout M → Prop

/-- For an ONVP sweepout, slices are nested ascending: $s \le t$ implies
$\Omega_s \subseteq \Omega_t$ on carriers. -/
theorem onvp_nested {Φ : Sweepout M} (h : ONVP Φ) {s t : ℝ} (hst : s ≤ t) :
    (Φ.slice s).carrier ⊆ (Φ.slice t).carrier := by sorry

end Sweepout

end AltRegularity
