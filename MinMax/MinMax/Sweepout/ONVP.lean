import MinMax.Sweepout.Defs

open GeometricMeasureTheory
open MinMax

namespace MinMax.Sweepout

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



variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M] [MeasureTheory.MeasureSpace M]


/-- $\Phi$ is **optimal** (paper Def 3.2 first bullet): no other sweepout
has strictly smaller width. Equivalently, $\Phi$ realizes the infimum
$W = \inf_{\Phi'} \sup_t \mathbf{M}(\Phi'(t))$ over all sweepouts of $M$.

Defined explicitly as a universally-quantified inequality
$\forall \Phi', \mathrm{width}\,\Phi \le \mathrm{width}\,\Phi'$, which
is equivalent to "$\mathrm{width}\,\Phi$ realizes the infimum" without
requiring `InfSet` or non-emptyness machinery on `Sweepout M`.

**Ground truth**: sweepout-specific concept (no direct Pitts/Simon
analog); CLS22 §2 line 805 + paper §3 Def 3.1. -/
def IsOptimal (Φ : Sweepout M) : Prop :=
  ∀ Φ' : Sweepout M, width Φ ≤ width Φ'

/-- $\Phi$ is **volume-parametrized** (paper §3 Def 3.2 third bullet,
verbatim "$\mathrm{Vol}(\Omega(x)) = x \cdot \mathrm{Vol}(M)$ for every
$x \in [0,1]$").

Defined explicitly via `MeasureTheory.volume` (the default measure
provided by `[MeasureSpace M]`).

**Ground truth**: sweepout-specific concept; CLS22 §2 (Def 1.2) +
paper §3 Def 3.2. Volume measure on $M$ is Simon 1983 §3 (Lebesgue
on $\mathbb{R}^{n+1}$) / standard Riemannian volume form, supplied as
the `[MeasureSpace M]` instance. -/
def IsVolumeParametrized (Φ : Sweepout M) : Prop :=
  ∀ t ∈ Set.Icc (0 : ℝ) 1,
    (MeasureTheory.volume (Φ.slice t).carrier).toReal =
      t * (MeasureTheory.volume (Set.univ : Set M)).toReal

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



end MinMax.Sweepout
