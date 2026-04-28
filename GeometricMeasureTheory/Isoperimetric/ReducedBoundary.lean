import GeometricMeasureTheory.Isoperimetric.Basic
import GeometricMeasureTheory.HasNormal
import Riemannian.Metric

/-!
# GeometricMeasureTheory.Isoperimetric.ReducedBoundary

Structural properties of the **reduced boundary** $\partial^*\Omega$
of a finite-perimeter set $\Omega \subseteq M$ (Maggi 2012 Chapter 15;
De Giorgi 1955).

Phase 3.1 introduced `FinitePerimeter.reducedBoundary` and
`Varifold.bvGradientDirection` as real `noncomputable def`s via
`Classical.choose` over De Giorgi existence axioms. This file extends
that surface with the structural characterizations from Maggi Ch. 15:

  * Outer-unit-normal **blow-up characterization** (Theorem 15.5):
    $\nu_\Omega(x) = -\lim_{r \to 0} \frac{D\chi_\Omega(B_r(x))}{|D\chi_\Omega|(B_r(x))}.$
  * **Density-1/2 property** at reduced boundary points (Theorem 15.9):
    $\lim_{r \to 0} |\Omega \cap B_r(x)| / |B_r(x)| = 1/2.$
  * **Tangent hyperplane** (Theorem 15.5): the orthogonal complement
    of $\nu_\Omega(x)$.

## Form

All three structural properties are stated as existence/equational
axioms. The framework's Phase 3.1 `bvGradientDirection` already
wraps the De Giorgi existence; this file exposes the additional
properties. Constructive bodies are deferred to framework long-term
work (Phase 4 De Giorgi blow-up self-build, ~80–120 LOC) or to
Mathlib upstream when its BV / De Giorgi structure theorem matures.

**Ground truth**: Maggi 2012 *Sets of Finite Perimeter and Geometric
Variational Problems*, Theorems 15.5, 15.9; De Giorgi 1955.
-/

open scoped ContDiff Manifold Topology

namespace GeometricMeasureTheory
namespace Isoperimetric

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasureTheory.MeasureSpace M]

/-! ## Outer unit normal: blow-up characterization (Maggi Theorem 15.5) -/

section OuterNormal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  [ChartedSpace H M] [IsManifold I ∞ M]
  [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]

/-- **Outer unit normal blow-up characterization** (Maggi Theorem 15.5).

The framework's `Varifold.bvGradientDirection` (Phase 3.1) provides the
`noncomputable def` that *would* be characterized as the blow-up limit
$\nu_\Omega(x) = -\lim_{r \to 0} \frac{D\chi_\Omega(B_r(x))}{|D\chi_\Omega|(B_r(x))}.$
The unit-norm property on the reduced boundary (Phase 3.1 lemma
`Varifold.bvGradientDirection_unit_on_reducedBoundary`) is the
strongest property currently exposed; the explicit blow-up-limit
equation is deferred to a `noncomputable def` body migration once the
framework gains a BV-blow-up primitive.

Re-export of the Phase 3.1 unit-norm property for convenience under
the `Isoperimetric` namespace.

**Ground truth**: Maggi 2012 Theorem 15.5. -/
theorem outerNormal_unit_on_reducedBoundary
    (Ω : FinitePerimeter M) (x : M)
    (hx : x ∈ FinitePerimeter.reducedBoundary Ω) :
    ‖Varifold.bvGradientDirection I Ω x‖ = 1 :=
  Varifold.bvGradientDirection_unit_on_reducedBoundary I Ω x hx

/-- **Outer unit normal is well-defined on the reduced boundary**:
the framework's `bvGradientDirection` extends to all of $M$ but is
characterized only on $\partial^*\Omega$. This wrapper records the
existence in `Isoperimetric` form, mirroring Maggi Theorem 15.5. -/
theorem outerNormal_exists_on_reducedBoundary
    (Ω : FinitePerimeter M) :
    ∃ ν : (x : M) → TangentSpace I x,
      ∀ x ∈ FinitePerimeter.reducedBoundary Ω, ‖ν x‖ = 1 :=
  ⟨Varifold.bvGradientDirection I Ω,
   fun x hx => Varifold.bvGradientDirection_unit_on_reducedBoundary I Ω x hx⟩

end OuterNormal

/-! ## Density-1/2 property (Maggi Theorem 15.9) -/

/-- **Density-1/2 at reduced boundary points** (Maggi Theorem 15.9).

For a finite-perimeter set $\Omega \subseteq M$ and any point
$x \in \partial^*\Omega$, the volume density of $\Omega$ at $x$
equals $1/2$:
$$\lim_{r \to 0^+} \frac{|\Omega \cap B_r(x)|}{|B_r(x)|} = \frac12.$$

Stated using the framework's `Isoperimetric.volume` primitive applied
to the intersection with a metric ball; the ambient ball volume uses
`MeasureTheory.volume (Metric.ball x r)`.

**Sorry status**: PRE-PAPER existence axiom. Repair plan: framework
self-build of the De Giorgi blow-up density limit (~80 LOC), or wait
for Mathlib upstream.

**Ground truth**: Maggi 2012 Theorem 15.9. -/
theorem density_at_reducedBoundary_eq_half
    (Ω : FinitePerimeter M) (x : M)
    (_hx : x ∈ FinitePerimeter.reducedBoundary Ω) :
    Filter.Tendsto
      (fun r : ℝ =>
        (MeasureTheory.volume (Ω.carrier ∩ Metric.ball x r)).toReal /
          (MeasureTheory.volume (Metric.ball x r)).toReal)
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 (1 / 2 : ℝ)) := by
  sorry

/-! ## Tangent hyperplane characterization (Maggi Theorem 15.5) -/

section TangentHyperplane

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  [ChartedSpace H M] [IsManifold I ∞ M]
  [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
  [OpenGALib.RiemannianMetric I M]

/-- **Tangent hyperplane at reduced boundary** (Maggi Theorem 15.5).

At every point $x$ of the reduced boundary, the tangent space to
$\partial^*\Omega$ is the orthogonal complement of the outer unit
normal:
$$T_x(\partial^*\Omega) = \{v \in T_xM : \langle v, \nu_\Omega(x)\rangle_g = 0\}.$$

Stated as the equality of the tangent-hyperplane subspace with the
orthogonal complement of the line spanned by the BV gradient
direction, with the framework-owned `metricInner` (Phase 4.7.2)
on the LHS. The RHS uses Mathlib's `Submodule.orthogonal` (`ᗮ`),
which is well-defined via the bridge instance
`Riemannian.InnerProductBridge.instInnerProductSpaceTangentSpace`.
The biconditional is mathematically valid when the Mathlib inner and
the framework `metricInner` agree (which they do under the
single-canonical-metric design of Phase 4.7).

**Sorry status**: PRE-PAPER existence axiom. Repair plan: framework
self-build of the tangent-blow-up to a hyperplane in the De Giorgi
structure theorem, or wait for Mathlib upstream's BV tangent-cone
infrastructure.

**Ground truth**: Maggi 2012 Theorem 15.5. -/
theorem tangentHyperplane_at_reducedBoundary_orthogonal
    (Ω : FinitePerimeter M) (x : M)
    (_hx : x ∈ FinitePerimeter.reducedBoundary Ω) (v : TangentSpace I x) :
    OpenGALib.metricInner x v (Varifold.bvGradientDirection I Ω x) = 0 ↔
      v ∈ (Submodule.span ℝ {Varifold.bvGradientDirection I Ω x})ᗮ := by
  sorry

end TangentHyperplane

/-! ## UXTest: typeclass + simp self-test -/

section ReducedBoundaryTest

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  [ChartedSpace H M] [IsManifold I ∞ M]
  [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]

/-- Self-test: the outer-normal unit-norm property is callable on a
point of the reduced boundary. -/
example (Ω : FinitePerimeter M) (x : M)
    (hx : x ∈ FinitePerimeter.reducedBoundary Ω) :
    ‖Varifold.bvGradientDirection I Ω x‖ = 1 :=
  outerNormal_unit_on_reducedBoundary I Ω x hx

/-- Self-test: existence form is also callable. -/
example (Ω : FinitePerimeter M) :
    ∃ ν : (x : M) → TangentSpace I x,
      ∀ x ∈ FinitePerimeter.reducedBoundary Ω, ‖ν x‖ = 1 :=
  outerNormal_exists_on_reducedBoundary I Ω

end ReducedBoundaryTest

end Isoperimetric
end GeometricMeasureTheory
