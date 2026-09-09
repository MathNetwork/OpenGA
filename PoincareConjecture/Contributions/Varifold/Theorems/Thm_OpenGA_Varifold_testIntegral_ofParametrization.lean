import Definitions.Def_OpenGA_ParametrizedVarifold



/-!
# Varifolds of parametrized surfaces in Euclidean space

The Jacobian is the actual `normDet` of the Frechet derivative. A measurable
tangent lift must agree with its range wherever the Jacobian is nonzero.
Using Lebesgue measure on the two-dimensional parameter space, restricted to
the parameter domain, we construct the finite-area varifold and prove that it
is independent of the tangent-plane extension on the zero-Jacobian set.

The measurable tangent lift is explicit input: this file does not yet construct
it automatically for every `C^1` map. Nor does it glue manifold charts or supply
the weak derivative for Sobolev surface maps. The definition already uses the
actual derivative, rather than an unconstrained surrogate for it.

References: Simon, *Introduction to Geometric Measure Theory*, 2018, Chapters 2
and 8; Colding-Minicozzi, arXiv:0707.0108, Section 1.3, p. 5.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal CompactlySupported

namespace OpenGA.Varifold

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]


















theorem testIntegral_ofParametrization (f : EuclideanSpace ℝ (Fin 2) → E)
    (hf : ContDiff ℝ 1 f) (Ω : Set (EuclideanSpace ℝ (Fin 2)))
    (P : SurfaceTangentLift f)
    (hfinite : (∫⁻ x in Ω, (surfaceJacobian f x : ℝ≥0∞)) < ∞)
    (φ : C_c(E × Grassmannian E 2, ℝ)) :
    (ofParametrization f hf Ω P hfinite).testIntegral φ =
      ∫ x in Ω, (surfaceJacobian f x : ℝ) * φ (f x, P.plane x) := by sorry



end OpenGA.Varifold

