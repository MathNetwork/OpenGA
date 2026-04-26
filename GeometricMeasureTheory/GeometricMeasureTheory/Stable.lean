import GeometricMeasureTheory.Varifold
import GeometricMeasureTheory.SecondVariation
import Mathlib.Geometry.Manifold.IsManifold.Basic

/-!
# AltRegularity.GMT.Stable

Stability and Morse-index concepts for varifolds — GMT-level
classification primitives.

## Phase 1.5 (D): file-relocation

`IsStable` previously lived in `Regularity/AlphaStructural.lean`. It is
moved here because it is a GMT-level concept (a universal quantification
over test functions of `secondVariation`-non-negativity) rather than a
regularity-theory-specific construct. `Regularity/AlphaStructural.lean`
re-imports.

## Sibling concepts

  * `IsStable V` — $\delta^2 V \ge 0$ for all test functions
    compactly supported away from $\mathrm{sing}\,V$;
  * `IsUnstable V` — there exists a test function with $\delta^2 V < 0$;
  * `MorseIndex V` — dimension of the negative eigenspace of the
    Jacobi operator (stub for future development).

Each carries the smooth-manifold typeclass cascade
`(I : ModelWithCorners ℝ E H) [ChartedSpace H M] [IsManifold I ∞ M]`
because `sing I V` requires it.

**Ground truth**: Simon 1983 §49; Schoen-Simon 1981 §1; Wickramasekera
2014 §2 — stability appears as condition (S2) of the class
$\mathcal{S}_\alpha$.
-/

open scoped ContDiff Manifold

namespace GeometricMeasureTheory

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasureTheory.MeasureSpace M]

namespace Varifold

/-- $V$ is **stable** (paper §4 Definition 4.1 (S2)):
$\delta^2 V(\varphi, \varphi) \ge 0$ for every smooth scalar normal
deformation $\varphi$ compactly supported away from $\mathrm{sing}\,V$.

Carries the smooth-manifold typeclass cascade
`(I : ModelWithCorners) [ChartedSpace H M] [IsManifold I ∞ M]`
because `sing I V` requires it. -/
def IsStable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    [ChartedSpace H M] [IsManifold I ∞ M]
    (V : Varifold M) : Prop :=
  ∀ φ : M → ℝ, Function.support φ ⊆ (sing I V)ᶜ →
    0 ≤ secondVariation I V φ

/-- $V$ is **unstable**: there exists a test direction with negative
second variation. -/
def IsUnstable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    [ChartedSpace H M] [IsManifold I ∞ M]
    (V : Varifold M) : Prop :=
  ∃ φ : M → ℝ,
    Function.support φ ⊆ (sing I V)ᶜ ∧
    secondVariation I V φ < 0

/-- The **Morse index** of $V$: dimension of the negative eigenspace
of the Jacobi operator (stub).

**Ground truth**: Simon 1983 §49 (eigenvalue problem for the Jacobi
operator). Stub returning 0; future development will replace with the
actual eigencount via spectral decomposition. -/
def MorseIndex (_V : Varifold M) : ℕ := 0

end Varifold

end GeometricMeasureTheory
