import GeometricMeasureTheory.Stationary
import GeometricMeasureTheory.SecondVariation
import GeometricMeasureTheory.Stable
import GeometricMeasureTheory.TangentCone
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.Topology.VectorBundle.Riemannian

open GeometricMeasureTheory GeometricMeasureTheory.Varifold Bundle
open scoped ContDiff Manifold

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

-- `IsStable` (paper §4 Def 4.1 (S2)) was moved to
-- `GeometricMeasureTheory/Stable.lean` as a GMT-level concept (Phase 1.5
-- Commit D). It is re-imported here unchanged; downstream usage is
-- unaffected.

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

/-- **Structural carrier for a junction cone** on a measure $\mu$ on the
model normed space $E$, centered at a point $p \in E$.

A junction cone (Wic14 §3) is a stationary integral cone supported on
$N \ge 3$ distinct half-hyperplanes meeting along a common
$(n-1)$-dim edge through $p$. This carrier records the structural
skeleton: $N \ge 3$ distinct closed sheets through $p$, with the mass
measure concentrated on their union. The half-hyperplane structure
(each sheet is a closed half of an $n$-dim affine subspace),
the common $(n-1)$-dim edge, and the stationary balance condition
$\sum_j m_j \nu_j = 0$ are **deferred** as Wic14-internal refinements
(see TODO comments in fields).

**Ground truth**: Simon 1983 §42; Wickramasekera 2014 §3.

**Used by**: `IsJunctionCone`. -/
structure IsJunctionConeData
    {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    (μ : MeasureTheory.Measure E) (p : E) where
  /-- Number of sheets in the cone. -/
  N : ℕ
  /-- At least three sheets — the defining condition of a junction. -/
  N_ge_3 : 3 ≤ N
  /-- The N closed sheets, each a subset of $E$. -/
  sheet : Fin N → Set E
  /-- Each sheet is closed. -/
  sheet_closed : ∀ j, IsClosed (sheet j)
  /-- Each sheet contains the common point $p$ (the cone vertex /
  edge intersects $p$). -/
  sheet_contains_p : ∀ j, p ∈ sheet j
  /-- Sheets are pairwise distinct. -/
  sheets_distinct : Function.Injective sheet
  /-- Multiplicity of each sheet — positive natural numbers. -/
  mult : Fin N → ℕ
  /-- Each multiplicity is positive. -/
  mult_pos : ∀ j, 0 < mult j
  /-- Mass measure is concentrated on the union of sheets:
  the complement of $\bigcup_j$ sheet $j$ has $\mu$-measure zero. -/
  measure_concentrated : μ (⋃ j, sheet j)ᶜ = 0
  -- TODO (Wic14-internal refinement, deferred):
  --   * each sheet is a closed half of an $n$-dim affine subspace
  --     (codim-1 hyperplane in $E$);
  --   * common $(n-1)$-dim edge $L$ through $p$ (intersection of all
  --     carrier hyperplanes);
  --   * stationary balance condition $\sum_j$ mult $j$ • $\nu_j = 0$
  --     on outward conormals $\nu_j$ at the edge — requires
  --     `[InnerProductSpace ℝ E]` cascade upgrade.

/-- $V$ is a **junction cone centered at $Z$** (paper §6.2 Step 1;
Wic14 §3): the chart-pushforward of $V$.massMeasure to $E$ via the chart
at $Z$ admits the structural skeleton of a junction cone (`IsJunctionConeData`)
based at the chart image of $Z$.

**Layer B C-7 真填**: real `def` via `Nonempty (IsJunctionConeData ...)`
on the chart-pushforward, mirroring the
`Manifold.IsSmoothEmbedding` ⇒ `LocalSmoothEmbeddingWitness` ⇒
`Nonempty` pattern (Layer B C-5). The structural carrier records
$N \ge 3$ closed sheets, distinctness, multiplicities, and measure
concentration; the half-hyperplane / edge / balance refinements are
documented as deferred Wic14-internal structure (gap analogous to
`secondVariation`'s curvature placeholder).

**Ground truth**: Simon 1983 §42; Wickramasekera 2014 §3.

Lives in `Regularity` rather than `GeometricMeasureTheory` because the
junction-cone configuration is regularity-theory-specific (Wickramasekera
$\alpha$-structural), not a general GMT primitive.

**Used by**: `Varifold.HasJunction` def (in this file). -/
def IsJunctionCone
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    [ChartedSpace H M] [IsManifold I ∞ M]
    (V : Varifold M) (Z : M) : Prop :=
  Nonempty (IsJunctionConeData
    (V.massMeasure.map (extChartAt I Z))
    ((extChartAt I Z) Z))

/-- The varifold $V$ has a **junction** at the point $Z$ (paper §6.2,
Step 1; Remark 3.5(ii)): the tangent cone to $\|V\|$ at $Z$ is a
junction cone — supported on $N \ge 3$ distinct half-hyperplanes
meeting along a common $(n-1)$-dimensional edge with the stationary
balancing condition $\sum_j m_j \nu_j = 0$ on the outward conormals.
This is the configuration excluded by $(\mathcal{S}3)$.

Defined explicitly via the GMT primitive `tangentCone` and the
regularity-side primitive `IsJunctionCone`. -/
def HasJunction
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    [ChartedSpace H M] [IsManifold I ∞ M]
    (V : Varifold M) (Z : M) : Prop :=
  IsJunctionCone I (tangentCone I V Z) Z

/-- $V$ satisfies the **$\alpha$-structural hypothesis** ($\mathcal{S}3$,
paper §4 Def 4.1): no singular point of $V$ admits an $\alpha$-junction.

Defined explicitly as a universally-quantified negation, so the structure
"no singular point is a junction" is visible to the Lean kernel.

Carries the smooth-manifold typeclass cascade because `sing I V`
requires it. -/
def AlphaStructural
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    [ChartedSpace H M] [IsManifold I ∞ M]
    (V : Varifold M) (α : ℝ) : Prop :=
  ∀ Z ∈ sing I V, ¬ HasAlphaJunctionAt V Z α

/-- The class $\mathcal{S}_\alpha$ (paper §4 Def 4.1, [Wickramasekera
2014, Section 2]): integral, stationary, stable, and satisfies the
$\alpha$-structural hypothesis.

Carries the smooth-manifold typeclass cascade because `IsStable I V`
and `AlphaStructural I V α` reference `sing I V`. -/
structure InClassSAlpha
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    [ChartedSpace H M] [IsManifold I ∞ M]
    [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
    [OpenGALib.RiemannianMetric I M]
    (V : Varifold M) [Varifold.HasNormal I V]
    (α : ℝ) : Prop where
  /-- ($\mathcal{S}1$) The varifold is stationary: $\delta V = 0$. -/
  stationary : IsStationary V
  /-- The varifold has integer multiplicity. -/
  integral : IsIntegral V
  /-- ($\mathcal{S}2$) The second variation is non-negative on the
  regular part. -/
  stable : IsStable I V
  /-- ($\mathcal{S}3$) The $\alpha$-structural hypothesis at each
  singular point. -/
  alphaStructural : AlphaStructural I V α

end Varifold

end Regularity
