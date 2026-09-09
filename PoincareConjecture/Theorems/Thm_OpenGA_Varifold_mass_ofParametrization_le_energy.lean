import Definitions.Def_OpenGA_ParametrizedVarifold
import Definitions.Def_OpenGA_ParametrizedVarifold



/-!
# Area-energy control of a parametrized varifold

For a `C^1` map from a Euclidean two-dimensional parameter domain, the mass of
its induced varifold is bounded by its Dirichlet energy. The derivative and
Jacobian are the actual ones, and the tangent lift is the one required by
`ofParametrization`. This connects the varifold construction to the existing
finite-energy comparison theorem used by the width route.

Reference: Colding-Minicozzi, arXiv:0707.0108, equation (1.4), p. 3, and
Section 1.3, p. 5. This is the Euclidean parameter-domain version; it does not
assert a global frame on a sphere or construct a Sobolev derivative.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace OpenGA.Varifold

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]


theorem mass_ofParametrization_le_energy (f : EuclideanSpace ℝ (Fin 2) → E)
    (hf : ContDiff ℝ 1 f) (Ω : Set (EuclideanSpace ℝ (Fin 2)))
    (P : SurfaceTangentLift f)
    (hfinite : (∫⁻ x in Ω, (surfaceJacobian f x : ℝ≥0∞)) < ∞)
    (b : OrthonormalBasis (Fin 2) ℝ (EuclideanSpace ℝ (Fin 2)))
    (henergy : IntegrableOn (fun x =>
      energyDensity (fderiv ℝ f x (b 0)) (fderiv ℝ f x (b 1))) Ω volume) :
    (ofParametrization f hf Ω P hfinite).mass ≤ ENNReal.ofReal
      (∫ x in Ω, energyDensity (fderiv ℝ f x (b 0)) (fderiv ℝ f x (b 1))) := by sorry

end OpenGA.Varifold

