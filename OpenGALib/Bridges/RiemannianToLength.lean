import Mathlib.Geometry.Manifold.Riemannian.Basic
import OpenGALib.MetricGeometry.LengthSpace

/-!
# Bridge: Riemannian manifolds are length spaces

This file installs the instance `LengthSpace M` for every space `M` carrying
Mathlib's `IsRiemannianManifold I M` predicate. The bridge sits in Layer 5
(`OpenGALib/Bridges/`) per the OpenGA layer hierarchy — it consumes both the
Layer 1 length-space definition and the Layer 3a Riemannian primitives, and
expresses that the metric-side and Riemannian-side notions of "geodesic
distance" coincide.

## Mathematical content

The instance is a direct consequence of `IsRiemannianManifold.out`, which
already records the equation `edist x y = riemannianEDist I x y` (Mathlib's
Riemannian-side definition of the infimum of `C¹`-path lengths). Combined
with `eVariationOn.edist_le` (the triangle-inequality direction, free for
every pseudo-extended-metric space), the only remaining content is the
comparison between OpenGA's metric-variation `pathLength` (= `eVariationOn`
over the unit interval) and Mathlib's tangent-integral `Manifold.pathELength`
for `C¹` paths.

## Ground truth

Burago–Burago–Ivanov §2.7.1 (the length structure induced by a Riemannian
metric agrees with the Riemannian length); do Carmo, *Riemannian Geometry*,
Ch. 7 §2 (the distance function is the infimum of lengths of piecewise
differentiable curves).
-/

open Bundle Set Topology
open scoped ENNReal Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [PseudoEMetricSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- **Math.** Every Riemannian manifold is a length space: the extended
distance equals the infimum of `pathLength` over continuous paths.

Ground truth: Burago–Burago–Ivanov §2.7.1; do Carmo, *Riemannian Geometry*,
Ch. 7 §2. The Riemannian distance between two points equals the infimum of
the lengths of paths joining them.

Eng note (proof body, not statement): the proof bridges OpenGA's
metric-variation `pathLength` (Layer 1, wrapping `eVariationOn`) with
Mathlib's tangent-integral `Manifold.pathELength` (Layer 3a, used to define
`IsRiemannianManifold`). The `≥` direction is the unconditional
triangle-inequality bound `edist_le_pathLength`. The `≤` direction is
sorry-marked PRE-PAPER (see repair plan below).

PRE-PAPER. **Sorry repair plan.** The remaining obligation is:
for every `C¹` path `γ : ℝ → M` smooth on `[0, 1]`, the metric-side
e-variation of `γ ∘ Subtype.val : I → M` is bounded by the tangent-integral
`Manifold.pathELength I γ 0 1`. This is the standard partition-telescoping
argument:

* for each monotone partition `u : ℕ → I`, each segment-distance
  `edist (γ ↑u(i+1)) (γ ↑u(i))` is bounded by `riemannianEDist` (via
  `IsRiemannianManifold.out`), which in turn is bounded by
  `Manifold.pathELength I γ ↑u(i) ↑u(i+1)` (via
  `Manifold.riemannianEDist_le_pathELength`);
* telescoping via `Manifold.pathELength_add` and monotonicity via
  `Manifold.pathELength_mono` collapses the sum to
  `Manifold.pathELength I γ 0 1`.

The proof is approximately 60–100 LOC of bookkeeping. It is not landed here
because it would expand Stage I's scope; the dependency on this bridge in
downstream files is currently only via the `LengthSpace M` instance head
(not the `iInf` equation), so the sorry does not flow into Riemannian /
GMT headline theorems.

**Repair trigger.** First downstream consumer that destructures the `iInf`
equation (e.g. a theorem that needs an explicit length-minimizing sequence
of paths on a Riemannian manifold). At that point, prove the
`eVariationOn ≤ Manifold.pathELength` bridge lemma in
`OpenGALib/Bridges/Util/EVariationOnLePathELength.lean` and replace the
sorry by `iInf_le_of_le γ_path (eVariationOn_le_pathELength γ γ̃_smooth)`.

## Why a `def`, not an `instance`

The model-with-corners `I : ModelWithCorners ℝ E H` is data, not a typeclass,
so Lean's synthesis algorithm cannot recover it from the conclusion
`LengthSpace M`. The bridge is therefore exposed as a `def`; concrete
`LengthSpace` instances are installed in `Core/Examples/` for each specific
choice of model (inner-product spaces, products, Lie groups, …) by
applying the bridge with the canonical model for that family. -/
@[reducible]
def IsRiemannianManifold.toLengthSpace
    [IsRiemannianManifold I M] : OpenGA.LengthSpace M where
  edist_eq_iInf_pathLength x y := by
    apply le_antisymm
    · -- edist x y ≤ ⨅ γ, pathLength γ — unconditional triangle inequality.
      exact le_iInf fun γ ↦ OpenGA.LengthSpace.edist_le_pathLength γ
    · -- ⨅ γ, pathLength γ ≤ edist x y — needs the metric-variation /
      -- tangent-integral comparison on C¹ paths. See PRE-PAPER block above.
      sorry

/-- **Math.** Every real inner product space is a length space: applying
`IsRiemannianManifold.toLengthSpace` to Mathlib's canonical Riemannian
metric on a vector space (`riemannianMetricVectorSpace`, automatic instance
`IsRiemannianManifold 𝓘(ℝ, F) F`). -/
noncomputable instance (priority := 100) OpenGA.instLengthSpaceOfInnerProductSpace
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] :
    OpenGA.LengthSpace F :=
  IsRiemannianManifold.toLengthSpace (I := 𝓘(ℝ, F))
