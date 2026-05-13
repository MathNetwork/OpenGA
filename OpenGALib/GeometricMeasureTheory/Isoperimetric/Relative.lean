import OpenGALib.GeometricMeasureTheory.Isoperimetric.Basic
import OpenGALib.GeometricMeasureTheory.Isoperimetric.Euclidean

/-!
# GeometricMeasureTheory.Isoperimetric.Relative

The **relative isoperimetric inequality** on a closed Riemannian
manifold (Maggi 12.37; Federer §3.2.43). For a Caccioppoli set
$\Omega \subseteq M^{n+1}$ and a geodesic ball $B_\rho(p)$ with
$\rho < r_1$,
$$\min\bigl(|\Omega \cap B_\rho(p)|,\, |B_\rho(p) \setminus \Omega|\bigr)^{n/(n+1)}
   \;\le\; C_I \cdot \mathrm{Per}(\Omega, B_\rho(p)),$$
where $r_1, C_I > 0$ depend only on $(M, g, n)$.

Constants and inequality are bundled into a single existence theorem
`relative_isoperimetric_inequality_exists` (paper §2's bundled form,
avoiding leakage of Riemannian-geometric quantities like injectivity
radius or sectional-curvature bound to consumers). Body is PRE-PAPER
existence axiom; closure is framework self-build or Mathlib upstream.

**Ground truth**: Maggi 2012 Prop 12.37; Federer 1969 §3.2.43.
-/

namespace GeometricMeasureTheory
namespace Isoperimetric

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasureTheory.MeasureSpace M] [CompactSpace M]

/-! ## The relative isoperimetric inequality -/

/-- **Relative isoperimetric inequality** (Maggi 2012 Proposition 12.37;
paper §2 Proposition `prop:relative-isoperimetric`).

For a closed Riemannian manifold $(M^{n+1}, g)$, there exist constants
$r_1 > 0$ and $C_I > 0$ depending only on $(M, g, n)$ such that for
every Caccioppoli set $\Omega \subseteq M$, every $p \in M$, and every
$\rho < r_1$,
$$\min\bigl(|\Omega \cap B_\rho(p)|,\, |B_\rho(p) \setminus \Omega|\bigr)^{n/(n+1)}
   \;\le\; C_I \cdot \mathrm{Per}(\Omega, B_\rho(p)).$$

The dimension parameter is paper convention: $M^{n+1}$ is the
$(n+1)$-dimensional manifold, $n$ is the codimension-1 hypersurface
dimension; the exponent $n/(n+1)$ is the standard relative
isoperimetric exponent.

Volumes use the framework's `Isoperimetric.volume` primitive applied
to the relevant intersections; perimeter uses `FinitePerimeter.perimOn`
(localized perimeter on a Borel set).

**Sorry status**: PRE-PAPER existence axiom. Repair plan: framework
self-build of Federer 1969 §3.2.43 + Maggi 12.37 covering argument
(~200 LOC) or wait for Mathlib upstream's relative-isoperimetric
library.

**Ground truth**: Maggi 2012 Proposition 12.37; Federer 1969 §3.2.43.

**Paper alignment**: paper §2 Proposition `prop:relative-isoperimetric`,
verbatim. -/
theorem relative_isoperimetric_inequality_exists (n : ℕ) (_hn : 0 < n) :
    ∃ r₁ : ℝ, 0 < r₁ ∧ ∃ C_I : ℝ, 0 < C_I ∧
      ∀ (Ω : FinitePerimeter M) (p : M) (ρ : ℝ), ρ < r₁ →
        min (MeasureTheory.volume (Ω.carrier ∩ Metric.ball p ρ)).toReal
            (MeasureTheory.volume (Metric.ball p ρ \ Ω.carrier)).toReal
          ^ ((n : ℝ) / (n + 1)) ≤
          C_I * Ω.perimOn (Metric.ball p ρ) := by
  sorry

/-- **Relative isoperimetric constants** (Maggi 2012 Proposition 12.37):
the pair $(r_1, C_I)$ extracted from the existence theorem via
`Classical.choose`.

Used downstream when callers need the pair as an explicit object;
most callers should use `relative_isoperimetric_inequality_exists`
directly, since the constants depend on $(M, g, n)$ and threading
them is paper-faithful only up to the existence quantifier.

**Ground truth**: Maggi 2012 Proposition 12.37; paper §2. -/
noncomputable def relativeIsoperimetricCriticalRadius
    (M : Type*) [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
    [MeasureTheory.MeasureSpace M] [CompactSpace M]
    (n : ℕ) (hn : 0 < n) : ℝ :=
  Classical.choose (relative_isoperimetric_inequality_exists (M := M) n hn)

/-- The critical radius from `relative_isoperimetric_inequality_exists`
is positive. -/
theorem relativeIsoperimetricCriticalRadius_pos
    (n : ℕ) (hn : 0 < n) :
    0 < relativeIsoperimetricCriticalRadius M n hn :=
  (Classical.choose_spec (relative_isoperimetric_inequality_exists (M := M) n hn)).1


end Isoperimetric
end GeometricMeasureTheory
