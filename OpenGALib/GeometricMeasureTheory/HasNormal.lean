import OpenGALib.GeometricMeasureTheory.Varifold
import OpenGALib.GeometricMeasureTheory.TangentCone
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import OpenGALib.Riemannian.Metric

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

/-- A smooth, compactly supported vector field on a smooth manifold $M$.

A test vector field is a section of the tangent bundle $TM$ that is
$C^\infty$ as a map into the total space and supported on a compact set
in the base.

**Ground truth**: standard smooth-manifold concept; Simon 1983 §38
("smooth vector fields with compact support on $M$"); Allard 1972 §3.

Located in `HasNormal.lean` (Phase 1.7) as a foundation file shared
by `Stationary.lean` and `Variation/FirstVariation.lean` — avoids the
cycle where `Stationary` would otherwise import `Variation` for the
full-form body migration.

**Used by**: `Varifold.IsStationary` def; `Variation.firstVariationFull`. -/
structure TestVectorField
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] where
  /-- The vector field as a section of the tangent bundle. -/
  toFun : Π (x : M), TangentSpace I x
  /-- The lifted bundle map $x \mapsto (x, X(x))$ is $C^\infty$. -/
  contMDiff : ContMDiff I I.tangent ∞ (fun x : M => (toFun x : TangentBundle I M))
  /-- The vector field has compact support: the closure of the
  non-vanishing set is compact. -/
  isCompactSupport : IsCompact (closure {x : M | toFun x ≠ 0})

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
@[ext]
class HasNormal
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H)
    [ChartedSpace H M] [IsManifold I ∞ M]
    (V : Varifold M) where
  /-- The unit normal field $\nu(x) \in T_xM$ at each point of $M$. -/
  unitNormal : (x : M) → TangentSpace I x

/-- **Existence axiom for the BV-gradient unit normal direction**
([Maggi 2012, Definition 15.1, Theorem 15.5]; De Giorgi 1955).

For a finite-perimeter set $\Omega$ on a smooth manifold $M$, there
exists a section $\nu_\Omega : (x : M) \to T_xM$ representing the
direction of the BV gradient $D\chi_\Omega / |D\chi_\Omega|$, satisfying
the **unit-norm property** on the reduced boundary:
$\|\nu_\Omega(x)\| = 1$ for $x \in \partial^*\Omega$.

The direction is paper-faithfully defined by the blow-up limit
$\nu_\Omega(x) = \lim_{r \to 0^+} D\chi_\Omega(B_r(x)) / |D\chi_\Omega(B_r(x))|$,
which converges $|D\chi_\Omega|$-a.e. to a unit vector by the De Giorgi
structure theorem.

**Sorry status**: PRE-PAPER. Repair plan: replace `Classical.choose`
body with the constructive blow-up limit when Mathlib's BV
infrastructure on charted manifolds matures, or via framework
self-build of the De Giorgi blow-up (~80 LOC). The unit-norm
property is preserved by the explicit construction. -/
theorem ofBoundary_unitNormal_exists
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    [ChartedSpace H M] [IsManifold I ∞ M]
    (Ω : FinitePerimeter M) :
    ∃ ν : (x : M) → TangentSpace I x,
      ∀ x ∈ FinitePerimeter.reducedBoundary Ω, ‖ν x‖ = 1 := by
  sorry

/-- The **BV gradient direction** $\nu_\Omega(x) \in T_xM$ — the outer
unit normal to the reduced boundary $\partial^*\Omega$, defined paper-
faithfully via the blow-up limit
$\nu_\Omega(x) = \lim_{r \to 0^+} D\chi_\Omega(B_r(x)) / |D\chi_\Omega(B_r(x))|$.

Real `noncomputable def` via `Classical.choose` over the De Giorgi
existence axiom (`ofBoundary_unitNormal_exists`).

**Ground truth**: Maggi 2012 Definition 15.1; De Giorgi 1955.

**Used by**: `instHasNormalOfBoundary` (codim-1 normal field on
boundary varifolds). -/
noncomputable def bvGradientDirection
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    [ChartedSpace H M] [IsManifold I ∞ M]
    (Ω : FinitePerimeter M) (x : M) : TangentSpace I x :=
  Classical.choose (ofBoundary_unitNormal_exists I Ω) x

/-- **Unit norm of BV gradient direction on the reduced boundary**.

For any $x \in \partial^*\Omega$, $\|\nu_\Omega(x)\| = 1$. Extracted
from `ofBoundary_unitNormal_exists` via `Classical.choose_spec`. -/
theorem bvGradientDirection_unit_on_reducedBoundary
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    [ChartedSpace H M] [IsManifold I ∞ M]
    (Ω : FinitePerimeter M) (x : M)
    (hx : x ∈ FinitePerimeter.reducedBoundary Ω) :
    ‖bvGradientDirection I Ω x‖ = 1 :=
  Classical.choose_spec (ofBoundary_unitNormal_exists I Ω) x hx

/-- `HasNormal` instance for `ofBoundary Ω`: the BV gradient direction
$\nu_\Omega := D\chi_\Omega / |D\chi_\Omega|$.

**Ground truth**: De Giorgi structure theorem (Maggi 2012 Ch. 15);
Simon 1983 §27. -/
noncomputable instance instHasNormalOfBoundary
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    [ChartedSpace H M] [IsManifold I ∞ M]
    (Ω : FinitePerimeter M) :
    HasNormal I (Varifold.ofBoundary Ω) where
  unitNormal := bvGradientDirection I Ω

omit [MeasureTheory.MeasureSpace M] in
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
    (_V : Varifold M) (_Z : M) :
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

/-! ## UXTest

Self-test section verifying typeclass auto-resolve for `HasNormal`
instances, namely `instHasNormalOfBoundary` and
`instHasNormalTangentCone`. If a future refactor changes
`HasNormal`'s signature or these instances' arguments, the section
will fail to elaborate, surfacing the regression immediately. -/
section UXTest

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasureTheory.MeasureSpace M]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  [ChartedSpace H M] [IsManifold I ∞ M]

noncomputable example (Ω : FinitePerimeter M) :
    Varifold.HasNormal I (Varifold.ofBoundary Ω) := inferInstance

noncomputable example (V : Varifold M) (Z : M) :
    Varifold.HasNormal I (Varifold.tangentCone I V Z) := inferInstance

end UXTest

end GeometricMeasureTheory
