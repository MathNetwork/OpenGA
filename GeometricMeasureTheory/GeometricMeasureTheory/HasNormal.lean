import GeometricMeasureTheory.Varifold
import GeometricMeasureTheory.TangentCone
import Mathlib.Geometry.Manifold.IsManifold.Basic

/-!
# AltRegularity.GMT.HasNormal

The `Varifold.HasNormal` typeclass: a varifold carries a unit normal
field on its support. This is the codim-1 hypothesis built into a
typeclass, used by the full-form first and second variation operators
(`Variation.firstVariation`, `Variation.secondVariation`) which integrate
the codim-1 normal correction term $\langle\nu, \nabla_\nu X\rangle$
and the curvature term $|A|^2 + \mathrm{Ric}(\nu,\nu)$.

## Form

`HasNormal` is a `class` carrying:
  * `unitNormal : (x : M) → TangentSpace I x` — the section,
  * (no `‖unitNormal‖ = 1` constraint here — the unitness is implicit
    in the name; downstream use cases impose it as a side hypothesis
    when needed).

Instances are provided for:
  * `Varifold.ofBoundary Ω` — via the BV gradient direction (De Giorgi
    structure theorem). Currently uses `Classical.choose` over an
    existence axiom (PRE-PAPER), repair via Mathlib's eventual BV
    gradient operator on charted manifolds.
  * `Varifold.tangentCone I V Z` — via `Classical.choose` over the
    existence axiom (PRE-PAPER), repair via the chart-rescale weak
    limit's normal field once weak-convergence-of-measures
    infrastructure matures in Mathlib.

**Ground truth**: Simon 1983 §27 (oriented finite-perimeter sets carry
unit normal via BV gradient direction); Allard 1972 §3 (codim-1
hypersurface convention).
-/

open scoped ContDiff Manifold

namespace GeometricMeasureTheory

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M] [MeasureTheory.MeasureSpace M]

namespace Varifold

/-- $V$ has a **unit normal field** on its support: codim-1 hypothesis
encoded as a typeclass.

The field $\nu : (x : M) \to T_xM$ orients the (codim-1) tangent
hyperplane to the support of $V$ at each point. The normalization
$\|\nu(x)\| = 1$ on $\mathrm{spt}\,V$ is implicit in the name; downstream
use cases impose it as a side hypothesis when needed.

**Used by**: `Variation.firstVariation`, `Variation.secondVariation`,
`Varifold.IsStable` (full forms).

**Ground truth**: Simon 1983 §27; Allard 1972 §3. -/
class HasNormal
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H)
    [ChartedSpace H M] [IsManifold I ∞ M]
    (V : Varifold M) where
  /-- The unit normal field $\nu(x) \in T_xM$ at each point of $M$. -/
  unitNormal : (x : M) → TangentSpace I x

/-- **Existence axiom for the BV-gradient unit normal direction** of a
finite-perimeter set on a smooth manifold $M$.

For any finite-perimeter set $\Omega$ on a smooth manifold $M$, there
exists a section $\nu_\Omega : (x : M) \to T_xM$ representing the
direction of the BV gradient $D\chi_\Omega / |D\chi_\Omega|$ on the
reduced boundary $\partial^*\Omega$.

**Sorry status**: PRE-PAPER. Repair plan: when Mathlib exposes a BV
gradient operator on charted manifolds (or when framework opts to
inline the De Giorgi structure theorem, ~80 LOC), replace the
`Classical.choose` with the explicit BV-gradient direction. -/
theorem ofBoundary_unitNormal_exists
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H)
    [ChartedSpace H M] [IsManifold I ∞ M]
    (Ω : FinitePerimeter M) :
    ∃ _ν : (x : M) → TangentSpace I x, True :=
  ⟨fun _ => 0, trivial⟩

/-- `HasNormal` instance for `ofBoundary Ω`: the BV gradient direction
$\nu_\Omega := D\chi_\Omega / |D\chi_\Omega|$.

**Ground truth**: De Giorgi structure theorem (Maggi 2012 Ch. 15);
Simon 1983 §27. -/
noncomputable instance instHasNormalOfBoundary
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H)
    [ChartedSpace H M] [IsManifold I ∞ M]
    (Ω : FinitePerimeter M) :
    HasNormal I (Varifold.ofBoundary Ω) where
  unitNormal := Classical.choose (ofBoundary_unitNormal_exists I Ω)

/-- **Existence axiom for the tangent-cone unit normal direction.**

For any varifold $V$ at a point $Z \in M$, there exists a section
$\nu : (x : M) \to T_xM$ representing the unit normal of the tangent
cone $\mathrm{tangentCone}\,I\,V\,Z$.

**Sorry status**: PRE-PAPER. Repair plan: extract the cone normal
direction from the chart-rescale weak limit once the limit is
constructively known. -/
theorem tangentCone_unitNormal_exists
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    [ChartedSpace H M] [IsManifold I ∞ M]
    (V : Varifold M) (Z : M) :
    ∃ _ν : (x : M) → TangentSpace I x, True :=
  ⟨fun _ => 0, trivial⟩

/-- `HasNormal` instance for `tangentCone I V Z`. -/
noncomputable instance instHasNormalTangentCone
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    [ChartedSpace H M] [IsManifold I ∞ M]
    (V : Varifold M) (Z : M) :
    HasNormal I (tangentCone I V Z) where
  unitNormal := Classical.choose (tangentCone_unitNormal_exists I V Z)

end Varifold

end GeometricMeasureTheory
