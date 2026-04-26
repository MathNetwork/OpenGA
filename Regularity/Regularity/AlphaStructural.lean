import GeometricMeasureTheory.Stationary
import GeometricMeasureTheory.SecondVariation
import GeometricMeasureTheory.TangentCone

open GeometricMeasureTheory GeometricMeasureTheory.Varifold

/-!
# AltRegularity.Regularity.AlphaStructural

The $\alpha$-structural hypothesis and the class $\mathcal{S}_\alpha$
(paper §4 Definition 4.1, [Wickramasekera 2014, Section 2]).

A stable codimension-1 integral varifold $V$ on an open subset of a
Riemannian manifold belongs to $\mathcal{S}_\alpha$ iff it satisfies:

  ($\mathcal{S}1$) **Stationarity:** $\delta V = 0$.
  ($\mathcal{S}2$) **Stability:** the second variation
       $\delta^2 V(\varphi, \varphi) \ge 0$ for every smooth scalar
       normal deformation $\varphi$ supported in
       $\mathrm{spt}\|V\| \setminus \mathrm{sing}\,V$.
  ($\mathcal{S}3$) **$\alpha$-structural hypothesis:** at each singular
       point $Z$, no neighborhood of $Z$ in $\mathrm{spt}\|V\|$ equals a
       finite union of $C^{1,\alpha}$ hypersurfaces-with-boundary all
       sharing a common $C^{1,\alpha}$ boundary containing $Z$.

These conditions are the input to the smooth regularity theorem
(`AltRegularity.Regularity.SmoothRegularity`).

## Definition style

`IsStable` is an explicit `def` in terms of the leaf primitive
`Varifold.secondVariation`. `AlphaStructural` is an explicit `def` in
terms of the leaf primitive `Varifold.HasAlphaJunctionAt`. The
`InClassSAlpha` structure conjoins ($\mathcal{S}1$)–($\mathcal{S}3$)
along with integrality.
-/

namespace Regularity

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M] [MeasureTheory.MeasureSpace M]

namespace Varifold

/-- The varifold is **integral**: its density takes integer values
$\|V\|$-almost everywhere.

Defined explicitly as an a.e. integrality condition on the density
$\Theta(\|V\|, p)$, so the structural content of "integer multiplicity"
is visible to the Lean kernel. -/
def IsIntegral (V : Varifold M) : Prop :=
  ∀ᵐ p ∂V.massMeasure, ∃ k : ℕ, density V p = (k : ℝ)

/-- $V$ is **stable** ($\mathcal{S}2$, paper §4 Def 4.1):
$\delta^2 V(\varphi, \varphi) \ge 0$ for every smooth scalar normal
deformation $\varphi$ compactly supported away from $\mathrm{sing}\,V$.

Defined explicitly as a universally-quantified non-negativity statement
so that its content is visible to the Lean kernel. -/
def IsStable (V : Varifold M) : Prop :=
  ∀ φ : M → ℝ, Function.support φ ⊆ (sing V)ᶜ →
    0 ≤ secondVariation V φ

/-- The varifold has an **$\alpha$-junction at $Z$**: there exists
$\rho > 0$ such that $\mathrm{spt}\|V\| \cap B_\rho(Z)$ equals a finite
union of $C^{1,\alpha}$ hypersurfaces-with-boundary all having a common
$C^{1,\alpha}$ boundary containing $Z$, with no two of them
intersecting except along this common boundary.

**Ground truth**: Wickramasekera 2014 §2 ($\alpha$-structural hypothesis
$(\mathcal{S}3)$); the $C^{1,\alpha}$ regularity of hypersurfaces-with-
boundary is paper-internal to Wic14 and not in Pitts/Simon.

This is the configuration excluded by ($\mathcal{S}3$), encoded as an
opaque leaf primitive pending Mathlib's $C^{1,\alpha}$-hypersurface
infrastructure.

**Used by**: `Varifold.AlphaStructural` def (in this file). -/
opaque HasAlphaJunctionAt : Varifold M → M → ℝ → Prop

/-- $C$ is a **junction cone**: a stationary integral cone supported on
$N \ge 3$ distinct half-hyperplanes $P_1^+, \ldots, P_N^+$ meeting along
a common $(n-1)$-dimensional edge $L$, with the stationary balance
condition $\sum_{j=1}^N m_j \nu_j = 0$ on the outward conormals.

**Ground truth**: Simon 1983 §42 (regularity of stationary integral
cones, classification of tangent cones); Wickramasekera 2014 §3
(Sheeting Theorem and Minimum Distance Theorem give the equivalence
with the $\alpha$-structural hypothesis).

Encoded as an opaque leaf primitive pending Mathlib's
half-hyperplane / cone infrastructure. Lives in `Regularity` rather
than `GeometricMeasureTheory` because the junction-cone configuration
is regularity-theory-specific (Wickramasekera α-structural), not a
general GMT primitive.

**Used by**: `Varifold.HasJunction` def (in this file). -/
opaque IsJunctionCone : Varifold M → Prop

/-- The varifold $V$ has a **junction** at the point $Z$ (paper §6.2,
Step 1; Remark 3.5(ii)): the tangent cone to $\|V\|$ at $Z$ is a
junction cone — supported on $N \ge 3$ distinct half-hyperplanes
meeting along a common $(n-1)$-dimensional edge with the stationary
balancing condition $\sum_j m_j \nu_j = 0$ on the outward conormals.
This is the configuration excluded by $(\mathcal{S}3)$.

Defined explicitly via the GMT primitive `tangentCone` and the
regularity-side primitive `IsJunctionCone`. -/
def HasJunction (V : Varifold M) (Z : M) : Prop :=
  IsJunctionCone (tangentCone V Z)

/-- $V$ satisfies the **$\alpha$-structural hypothesis** ($\mathcal{S}3$,
paper §4 Def 4.1): no singular point of $V$ admits an $\alpha$-junction.

Defined explicitly as a universally-quantified negation, so the structure
"no singular point is a junction" is visible to the Lean kernel. -/
def AlphaStructural (V : Varifold M) (α : ℝ) : Prop :=
  ∀ Z ∈ sing V, ¬ HasAlphaJunctionAt V Z α

/-- The class $\mathcal{S}_\alpha$ (paper §4 Def 4.1, [Wickramasekera
2014, Section 2]): integral, stationary, stable, and satisfies the
$\alpha$-structural hypothesis. -/
structure InClassSAlpha (V : Varifold M) (α : ℝ) : Prop where
  /-- ($\mathcal{S}1$) The varifold is stationary: $\delta V = 0$. -/
  stationary : IsStationary V
  /-- The varifold has integer multiplicity. -/
  integral : IsIntegral V
  /-- ($\mathcal{S}2$) The second variation is non-negative on the
  regular part. -/
  stable : IsStable V
  /-- ($\mathcal{S}3$) The $\alpha$-structural hypothesis at each
  singular point. -/
  alphaStructural : AlphaStructural V α

end Varifold

end Regularity
