import GeometricMeasureTheory.Isoperimetric.Basic
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# GeometricMeasureTheory.Isoperimetric.Euclidean

The **classical Euclidean isoperimetric inequality** (Maggi 2012 Ch. 14).

For any finite-perimeter set $\Omega \subseteq \mathbb{R}^n$ with finite
volume,
$$P(\Omega) \;\ge\; n\,\omega_n^{1/n}\,|\Omega|^{(n-1)/n},$$
where $\omega_n = \pi^{n/2} / \Gamma(n/2+1)$ is the volume of the unit
ball in $\mathbb{R}^n$ and $c_n := n\,\omega_n^{1/n}$ is the
**isoperimetric constant**.

Equality (almost everywhere) characterizes balls.

**Ground truth**: Maggi 2012 *Sets of Finite Perimeter and Geometric
Variational Problems*, Theorem 14.1 (inequality) and Theorem 14.4
(equality case). Original results: De Giorgi 1958 (modern proof);
Federer 1959 (sharp form via symmetrization).

## Form

The inequality and equality case are stated as **existence axioms**
(`sorry`, PRE-PAPER classification): the constructive proofs go via
Brunn–Minkowski / Steiner symmetrization (Maggi Ch. 9, Ch. 14), which
require BV symmetrization infrastructure beyond the framework's
current scope. Repair plan: framework self-build of Brunn–Minkowski
+ symmetrization (~400 LOC, Phase 4 long-term work) or wait for
Mathlib upstream.

## Used by

- §6 paper regularity arguments do not formally consume this in the
  current chain proof — the Maggi 14.1 inequality is part of the
  background convention but not threaded through `main_theorem_*`
  (paper §5 cancellation argument is commented-out at the formal level).
- Future framework consumers (relative isoperimetric inequality,
  Allard density bounds, Caffarelli compactness) will consume these
  primitives.
-/

open Real MeasureTheory

namespace GeometricMeasureTheory
namespace Isoperimetric

/-! ## The isoperimetric constant -/

/-- The **isoperimetric constant** in dimension $n$:
$$c_n \;:=\; n \cdot \omega_n^{1/n},
\quad \omega_n = \frac{\pi^{n/2}}{\Gamma(n/2+1)}.$$

The unit ball volume $\omega_n$ matches Mathlib's
`EuclideanSpace.volume_ball` formula
($\sqrt{\pi}^{n} / \Gamma(n/2+1)$, since $\sqrt{\pi}^{n} = \pi^{n/2}$).

**Ground truth**: Maggi 2012 §14.1 (the constant $n \omega_n^{1/n}$
appears as the leading factor of Theorem 14.1's right-hand side). -/
noncomputable def isoperimetricConstant (n : ℕ) : ℝ :=
  (n : ℝ) * (Real.pi ^ ((n : ℝ) / 2) / Real.Gamma ((n : ℝ) / 2 + 1)) ^ ((1 : ℝ) / n)

/-- The isoperimetric constant is positive for all $n \ge 1$.

Both factors are positive: $n \ge 1$, and the unit ball volume
$\omega_n = \pi^{n/2} / \Gamma(n/2+1)$ is positive (positivity of
$\pi^{n/2}$ via `Real.rpow_pos_of_pos` and positivity of
$\Gamma(n/2+1)$ via `Real.Gamma_pos_of_pos`). -/
theorem isoperimetricConstant_pos {n : ℕ} (hn : 0 < n) :
    0 < isoperimetricConstant n := by
  unfold isoperimetricConstant
  have hπ : 0 < Real.pi := Real.pi_pos
  have hΓ : 0 < Real.Gamma ((n : ℝ) / 2 + 1) := by
    apply Real.Gamma_pos_of_pos
    have : (0 : ℝ) ≤ (n : ℝ) / 2 := by positivity
    linarith
  have hω : 0 < Real.pi ^ ((n : ℝ) / 2) / Real.Gamma ((n : ℝ) / 2 + 1) := by
    apply div_pos
    · exact Real.rpow_pos_of_pos hπ _
    · exact hΓ
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hpow : 0 < (Real.pi ^ ((n : ℝ) / 2) / Real.Gamma ((n : ℝ) / 2 + 1)) ^ ((1 : ℝ) / n) :=
    Real.rpow_pos_of_pos hω _
  exact mul_pos hn' hpow

/-! ## The classical isoperimetric inequality (Maggi 2012 Theorem 14.1) -/

/-- **Classical Euclidean isoperimetric inequality** (Maggi 2012
Theorem 14.1; De Giorgi 1958; Federer 1959).

For any finite-perimeter set $\Omega \subseteq \mathbb{R}^n$ ($n \ge 1$)
with finite volume,
$$c_n \cdot |\Omega|^{(n-1)/n} \;\le\; P(\Omega),$$
where $c_n = n\,\omega_n^{1/n}$ is the isoperimetric constant.

**Sorry status**: PRE-PAPER existence axiom. Repair plan: replace by
the constructive proof via Steiner symmetrization (Maggi Ch. 14
~400 LOC, framework self-build) or via Mathlib upstream when its
isoperimetric library lands.

**Ground truth**: Maggi 2012 Theorem 14.1. -/
theorem classical_isoperimetric_inequality
    {n : ℕ} (hn : 0 < n)
    (Ω : FinitePerimeter (EuclideanSpace ℝ (Fin n)))
    (_hvol : volume Ω < ⊤) :
    isoperimetricConstant n * (volume Ω).toReal ^ ((n - 1 : ℝ) / n) ≤
      (Ω.perim : ℝ) := by
  sorry

/-! ## Equality case (Maggi 2012 Theorem 14.4) -/

/-- **Equality case** (Maggi 2012 Theorem 14.4).

The classical isoperimetric inequality holds with equality iff $\Omega$
is (almost everywhere) a ball.

**Sorry status**: PRE-PAPER existence axiom. Repair plan: same as
`classical_isoperimetric_inequality`, the equality case is established
in Maggi Ch. 14 alongside the inequality via the same symmetrization
argument with rigidity analysis (Maggi 14.4).

**Ground truth**: Maggi 2012 Theorem 14.4. -/
theorem isoperimetric_equality_iff_ball
    {n : ℕ} (hn : 0 < n)
    (Ω : FinitePerimeter (EuclideanSpace ℝ (Fin n)))
    (_hvol : volume Ω < ⊤) (_hvol_pos : 0 < volume Ω) :
    isoperimetricConstant n * (volume Ω).toReal ^ ((n - 1 : ℝ) / n) =
        (Ω.perim : ℝ)
      ↔
    ∃ (c : EuclideanSpace ℝ (Fin n)) (r : ℝ), 0 < r ∧
      Ω.carrier =ᵐ[MeasureTheory.volume] Metric.ball c r := by
  sorry

/-! ## UXTest: typeclass synthesis self-test -/

section UXTest

/-- Self-test: typeclass synthesis fires at the call site for
`volume Ω` when `Ω : FinitePerimeter (EuclideanSpace ℝ (Fin n))`. -/
example {n : ℕ} (Ω : FinitePerimeter (EuclideanSpace ℝ (Fin n))) :
    0 ≤ volume Ω := volume_nonneg Ω

/-- Self-test: `isoperimetricConstant_pos` resolves with explicit
positivity hypothesis. -/
example {n : ℕ} (hn : 0 < n) : 0 < isoperimetricConstant n :=
  isoperimetricConstant_pos hn

end UXTest

end Isoperimetric
end GeometricMeasureTheory
