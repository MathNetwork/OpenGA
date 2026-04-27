import Mathlib.Topology.MetricSpace.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Tactic
import GeometricMeasureTheory.FinitePerimeter
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.Geometry.Manifold.IsManifold.Basic

open scoped ContDiff

/-!
# AltRegularity.GMT.Varifold

Varifolds in a metric measurable space.

A full $n$-varifold framework requires Radon measures on
$M \times \mathrm{Gr}(n, T_pM)$ which is not yet in Mathlib. As a
provisional implementation sufficient for this formalization's chain
proofs, we model an $n$-varifold by its mass measure $\|V\|$ alone — a
finite Borel measure on $M$ — deferring tangent-plane data to a
subsequent refinement.

This is part of Section 2 (Preliminaries) of the paper.
-/

namespace GeometricMeasureTheory

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M] [MeasureTheory.MeasureSpace M]

/-- An $n$-varifold in $M$ (with $n+1 = \dim M$), modeled provisionally
by its mass measure $\|V\|$ as a finite Borel measure on $M$ together
with its intrinsic dimension $n$. The full varifold structure with
tangent-plane data on $M \times \mathrm{Gr}(n, T_pM)$ is deferred. -/
structure Varifold (M : Type*)
    [MetricSpace M] [MeasurableSpace M] [BorelSpace M] where
  /-- Intrinsic dimension $n$ of the varifold. -/
  dim : ℕ
  /-- The mass measure $\|V\|$ as a Borel measure on $M$. -/
  massMeasure : MeasureTheory.Measure M
  /-- The mass measure has finite total mass. -/
  isFiniteMeasure : MeasureTheory.IsFiniteMeasure massMeasure

/-- The type of $n$-varifolds in $M$ is non-empty: the zero varifold
(at dimension $0$) provides a concrete witness. -/
instance Varifold.instNonempty : Nonempty (Varifold M) :=
  ⟨{ dim := 0
     massMeasure := 0
     isFiniteMeasure := ⟨by simp⟩ }⟩

namespace Varifold

/-- Total mass $\|V\|(M)$. -/
def mass (V : Varifold M) : ℝ := (V.massMeasure Set.univ).toReal

/-- Localized mass $\|V\|(U)$ on a Borel set $U \subset M$. -/
def massOn (V : Varifold M) (U : Set M) : ℝ := (V.massMeasure U).toReal

/-- Topological support $\mathrm{spt}\|V\|$: points such that every
neighborhood has positive mass. -/
def support (V : Varifold M) : Set M :=
  {p | ∀ U ∈ nhds p, V.massMeasure U ≠ 0}

/-- Pointwise density $\Theta(\|V\|, p) := \lim_{r \to 0} \|V\|(B_r(p))/(\omega_n r^n)$
where $n = V.\mathrm{dim}$.

Defined as the `Filter.limsup` of `‖V‖(B_r(p)) / r^n` as $r \to 0^+$,
omitting the unit-ball-volume constant $\omega_n$ (the constant is
non-zero, so it cancels in sign-comparison statements like $\Theta > 0$;
exact-value statements like $\Theta = k$ are interpreted modulo the
$\omega_n$ normalization).

**Ground truth**: Simon 1983 §17 (monotonicity formula for stationary
varifolds; existence of density at every point); §10–§11 (general
density-of-measure theory).

For non-stationary varifolds the limit may not exist; `limsup` is the
canonical convention (existence of the limit follows for stationary
varifolds via Simon §17 monotonicity, but the framework returns
`limsup` unconditionally to avoid existence hypotheses on callers). -/
noncomputable def density (V : Varifold M) (p : M) : ℝ :=
  Filter.limsup
    (fun r : ℝ => (V.massMeasure (Metric.ball p r)).toReal / r ^ V.dim)
    (nhdsWithin (0 : ℝ) (Set.Ioi 0))

/-- Densities are non-negative. -/
theorem density_nonneg (V : Varifold M) (p : M) : 0 ≤ density V p := by sorry

omit [MeasureTheory.MeasureSpace M] in
/-- Total mass is non-negative. -/
theorem mass_nonneg (V : Varifold M) : 0 ≤ mass V :=
  ENNReal.toReal_nonneg

omit [MeasureTheory.MeasureSpace M] in
/-- Localized mass is non-negative. -/
theorem massOn_nonneg (V : Varifold M) (U : Set M) : 0 ≤ massOn V U :=
  ENNReal.toReal_nonneg

omit [MeasureTheory.MeasureSpace M] in
/-- Localized mass is monotone in the set. -/
theorem massOn_mono (V : Varifold M) {U W : Set M} (h : U ⊆ W) :
    massOn V U ≤ massOn V W := by
  haveI := V.isFiniteMeasure
  exact ENNReal.toReal_mono (MeasureTheory.measure_lt_top V.massMeasure W).ne
    (MeasureTheory.measure_mono h)

omit [MeasureTheory.MeasureSpace M] in
/-- The total mass equals the localized mass on the whole space. -/
theorem massOn_univ (V : Varifold M) : massOn V Set.univ = mass V := rfl

/-- $p \in \mathrm{spt}\|V\|$ iff every open ball around $p$ has positive
local mass. -/
theorem mem_support_iff (V : Varifold M) (p : M) :
    p ∈ support V ↔ ∀ r > 0, 0 < massOn V (Metric.ball p r) := by sorry

/-- **Weak varifold convergence** $V_i \to V$.

Defined via pairing of mass measures against compactly supported
continuous test functions on $M$:
$$\int_M \varphi \, d\|V_i\| \to \int_M \varphi \, d\|V\|, \quad
\forall \varphi \in C_c(M; \mathbb{R}).$$

This is the **mass measure** weak-convergence form, not the full
varifold weak-* convergence on the Grassmann bundle $G_n(M)$. The
Grassmann form requires upgrading `Varifold` to carry a measure on
$M \times G_n(M)$ instead of just the mass measure on $M$, deferred
to a future round. The mass-measure form suffices for paper §6
applications (which only use mass measure / support information).

**Ground truth**: Simon 1983 §38 (varifold convergence as weak-*
convergence of Radon measures on the Grassmann bundle, paired against
compactly supported continuous test functions); Allard 1972 §3.

**Used by**: `Sweepout.MinMaxLimit` def (`Sweepout/MinMaxLimit.lean`). -/
def VarifoldConverge (Vᵢ : ℕ → Varifold M) (V : Varifold M) : Prop :=
  ∀ φ : M → ℝ, Continuous φ → HasCompactSupport φ →
    Filter.Tendsto
      (fun i => ∫ x, φ x ∂(Vᵢ i).massMeasure)
      Filter.atTop
      (nhds (∫ x, φ x ∂V.massMeasure))

section Smooth

/-- A **local smooth chart** for a subset $T \subseteq M$: witness that
$T$ is the image of a smooth embedding from some smooth manifold $S$
into $M$.

The witness bundles all the typeclass infrastructure (norm structure on
the model space, charted-space + manifold structure on $S$, smooth
embedding $f$) into a single structure carried by `regular`. Using a
structure rather than a chain of existentials lets the typeclass
instances be *fields with `[]` brackets*, which is how Lean propagates
them at the use site `Manifold.IsSmoothEmbedding J I ⊤ f`.

**Ground truth**: Simon 1983 §41 + §11; the "image of a smooth
embedding from a manifold" formulation matches Wickramasekera 2014 §2's
notion of regular point.

**Used by**: `Varifold.regular` def (in this file). -/
structure LocalSmoothEmbeddingWitness
    (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (T : Set M) where
  /-- Model normed space for the source manifold. -/
  E' : Type
  [normedAddCommGroup_E' : NormedAddCommGroup E']
  [normedSpace_E' : NormedSpace 𝕜 E']
  /-- Model topological space for the source manifold. -/
  H' : Type
  [topologicalSpace_H' : TopologicalSpace H']
  /-- Model with corners for the source manifold. -/
  J : ModelWithCorners 𝕜 E' H'
  /-- Source manifold whose smooth-embedding image is $T$. -/
  S : Type
  [topologicalSpace_S : TopologicalSpace S]
  [chartedSpace_S : ChartedSpace H' S]
  [isManifold_S : IsManifold J ∞ S]
  /-- The smooth embedding $f : S \to M$ with image $T$. -/
  f : S → M
  /-- $f$ is a $C^\infty$ embedding (`Manifold.IsSmoothEmbedding`). -/
  isEmbedding : Manifold.IsSmoothEmbedding J I ∞ f
  /-- $f$ has range exactly $T$. -/
  rangeEq : Set.range f = T

/-- The **regular set** $\mathrm{reg}\,V$ of a varifold (with respect
to the smooth-manifold structure $I$ on $M$): the set of support points
$p$ admitting an open neighborhood $U$ such that $U \cap \mathrm{spt}\|V\|$
is the image of a smooth embedding from some smooth manifold.

Defined explicitly via the structure
`LocalSmoothEmbeddingWitness` carrying a `Manifold.IsSmoothEmbedding`
witness. This replaces the previous `opaque` placeholder with a
paper-faithful def grounded against Mathlib's smooth-manifold API.

**Ground truth**: Simon 1983 §41 (regular vs singular set for stationary
integral varifolds); Wickramasekera 2014 §2 (regular set in the manifold
setting).

**Codimension**: the def admits any codimension; the codim-1 hypersurface
specialization (paper §4) is enforced at the call site by the relation
between `V.dim` and the source manifold's dimension. The def itself does
not constrain `V.dim`.

**Used by**: `Varifold.sing` def (in this file). -/
def regular
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (V : Varifold M) : Set M :=
  {p | p ∈ support V ∧ ∃ U : Set M, IsOpen U ∧ p ∈ U ∧
    Nonempty (LocalSmoothEmbeddingWitness 𝕜 I M (U ∩ support V))}

/-- The **singular set** $\mathrm{sing}\,V := \mathrm{spt}\|V\| \setminus
\mathrm{reg}\,V$ — points of the support that are not regular.

Defined explicitly so the structure "support minus regular part" is
visible to the Lean kernel. -/
def sing
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (V : Varifold M) : Set M := support V \ regular I V

end Smooth

/-- The **boundary varifold** $|\partial^*\Omega|$ associated to a
finite-perimeter set: the rectifiable codimension-1 varifold supported
on the reduced boundary $\partial^*\Omega$ with multiplicity 1.

Mass measure is `Ω.perimMeasure` (the BV total variation $|D\chi_\Omega|$,
already a finite Borel measure on $M$ via `Ω.perimFinite`). Dimension
is set to the placeholder $0$: a paper-faithful value would be
$(\text{ambient dim of } M) - 1$, but the framework's `M` does not yet
carry an ambient-dimension typeclass; chain proofs do not depend on the
exact value of `(ofBoundary Ω).dim`.

**Ground truth**: Simon 1983 §27 (BV / finite-perimeter sets) + §38
(associated varifold of an integer-rectifiable current); De Giorgi
structure theorem (Maggi 2012, Ch. 15) for the reduced boundary as a
rectifiable set.

**Used by**: `Sweepout.MinMaxLimit` def (`MinMax/Sweepout/MinMaxLimit.lean`),
`dlt_criterion` (`AltRegularity/Integrality/PerimeterConvergence.lean`). -/
noncomputable def ofBoundary (Ω : FinitePerimeter M) : Varifold M where
  dim := 0
  massMeasure := Ω.perimMeasure
  isFiniteMeasure := Ω.perimFinite

end Varifold

end GeometricMeasureTheory
