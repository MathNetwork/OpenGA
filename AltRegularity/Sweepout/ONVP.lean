import AltRegularity.Sweepout.Defs

/-!
# AltRegularity.Sweepout.ONVP

The Optimal Nested Volume-Parametrized (ONVP) property of a sweepout
(paper Definition 3.2, [CLS22, Def 1.2]).

A sweepout $\{\Phi(x) = \partial \Omega(x)\}$ is called:
  * **optimal** if $\sup_x \mathbf{M}(\Phi(x)) = W$ (the global width
    over all sweepouts);
  * **nested** if $\Omega(x_1) \subset \Omega(x_2)$ for all $0 \leq x_1
    \leq x_2 \leq 1$;
  * **volume parametrized** if $\mathrm{Vol}(\Omega(x)) = x \cdot
    \mathrm{Vol}(M)$ for every $x \in [0,1]$.

## Definition style

`Sweepout.IsOptimal` and `Sweepout.IsVolumeParametrized` are leaf
primitives: optimality requires a global infimum over the class
$\mathcal{S}$ of all sweepouts, and volume parametrization requires a
reference volume measure on $M$ — both pending Mathlib-level
infrastructure.

`Sweepout.ONVP` is an explicit `def` conjoining the three conditions,
so that nesting can be extracted directly via `onvp_nested`.
-/

namespace AltRegularity

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]

namespace Sweepout

/-- $\Phi$ is **optimal** (paper Def 3.2 first bullet): $\sup_t
\mathbf{M}(\Phi(t))$ equals the global width $W = \inf_{\Phi'}
\sup_t \mathbf{M}(\Phi'(t))$ over all sweepouts.

Encoded as an opaque leaf primitive pending a quantification over
$\mathcal{S}$ in the framework. -/
opaque IsOptimal : Sweepout M → Prop

/-- $\Phi$ is **volume-parametrized** (paper Def 3.2 third bullet):
$\mathrm{Vol}(\Omega(t)) = t \cdot \mathrm{Vol}(M)$ for every $t \in
[0,1]$.

Encoded as an opaque leaf primitive pending a reference volume measure
on $M$. -/
opaque IsVolumeParametrized : Sweepout M → Prop

/-- $\Phi$ is **Optimal Nested Volume-Parametrized** (paper Def 3.2 /
[CLS22, Def 1.2]): optimal, nested in $t$, and parametrized by
$\mathrm{Vol}(\Omega(t)) = t \cdot \mathrm{Vol}(M)$.

Defined explicitly as the conjunction of the three properties so that
each component is extractable. -/
def ONVP (Φ : Sweepout M) : Prop :=
  IsOptimal Φ ∧
  (∀ s t : ℝ, s ≤ t → (Φ.slice s).carrier ⊆ (Φ.slice t).carrier) ∧
  IsVolumeParametrized Φ

/-- For an ONVP sweepout, slices are nested ascending: $s \le t$ implies
$\Omega_s \subseteq \Omega_t$ on carriers. -/
theorem onvp_nested {Φ : Sweepout M} (h : ONVP Φ) {s t : ℝ} (hst : s ≤ t) :
    (Φ.slice s).carrier ⊆ (Φ.slice t).carrier :=
  h.2.1 s t hst

end Sweepout

end AltRegularity
