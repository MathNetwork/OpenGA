import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Green
import DifferentialGeometry.Analysis.Integration.Measure.ChartDensity
import DifferentialGeometry.Analysis.Integration.Measure.VolumeVariation
import DifferentialGeometry.Integration.DivergenceTheorem.LocalFormula
import DifferentialGeometry.Integration.DivergenceTheorem.Gradient
import DifferentialGeometry.Tensor.RSTensor.MetricTrace.Higher
import DifferentialGeometry.Tensor.RSTensor.Basis
import DifferentialGeometry.Tensor.RSTensor.Coordinates.Components
import DifferentialGeometry.Tensor.RSTensor.Coordinates.CoordinateBasis
import DifferentialGeometry.Tensor.RSTensor.Coordinates.Field
import DifferentialGeometry.Geometry.Coordinates.NablaComponents.TensorRS.ApplyInput
import DifferentialGeometry.Geometry.Coordinates.MetricCompatibility.Covariant
import DifferentialGeometry.Geometry.Coordinates.MetricCompatibility.Inverse
import DifferentialGeometry.Geometry.Coordinates.CoordinateFrame
import DifferentialGeometry.Geometry.Connection.Chart.Christoffel
import DifferentialGeometry.Geometry.Connection.LeviCivita.LeviCivitaLogDensity
import DifferentialGeometry.Geometry.Connection.LeviCivita.Variation.RicciCoord
import DifferentialGeometry.Geometry.Connection.LeviCivita.Basic
import DifferentialGeometry.Bundle.PartialMfderiv.FixedBase

set_option autoImplicit false

namespace DifferentialGeometry.PDE.RicciFlow.Entropy

noncomputable section

open Filter MeasureTheory
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Coordinates
open Tensor0SBundle
open scoped Manifold ContDiff

variable {M : Type*}








open Tensor0SBundle
open scoped Manifold ContDiff

variable {M : Type*}




def expNegPotentialDensity (potential : M -> Real) : M -> Real :=
  fun x => Real.exp (-(potential x))


def expNegPotentialWeightedMeasure [MeasurableSpace M] (mu : Measure M)
    (potential : M -> Real) : Measure M :=
  mu.withDensity fun x => ENNReal.ofReal (expNegPotentialDensity potential x)




theorem expNegPotentialWeightedMeasure_integral_eq_base
    [MeasurableSpace M] (mu : Measure M) (potential integrand : M -> Real)
    (hmeas :
      AEMeasurable
        (fun x : M => ENNReal.ofReal (expNegPotentialDensity potential x))
        mu) :
    (∫ x, integrand x ∂(expNegPotentialWeightedMeasure mu potential)) =
      ∫ x, expNegPotentialDensity potential x * integrand x ∂mu := by
  rw [expNegPotentialWeightedMeasure]
  rw [integral_withDensity_eq_integral_toReal_smul₀
    (μ := mu)
    (f := fun x : M => ENNReal.ofReal (expNegPotentialDensity potential x))
    hmeas
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)
    integrand]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall ?_
  intro x
  have hnonneg : 0 ≤ expNegPotentialDensity potential x :=
    le_of_lt (Real.exp_pos _)
  simp [ENNReal.toReal_ofReal hnonneg, smul_eq_mul]




theorem expWeightedIBP_of_baseIntegral_zero [MeasurableSpace M]
    (mu : Measure M) (potential lapPotential gradPotentialNormSq : M -> Real)
    (hmeas :
      AEMeasurable
        (fun x : M => ENNReal.ofReal (expNegPotentialDensity potential x))
        mu)
    (hbase :
      ∫ x,
        expNegPotentialDensity potential x *
          (lapPotential x - gradPotentialNormSq x)
        ∂mu = 0) :
    ∫ x, (lapPotential x - gradPotentialNormSq x)
      ∂(expNegPotentialWeightedMeasure mu potential) = 0 := by
  rw [expNegPotentialWeightedMeasure_integral_eq_base
    (mu := mu) (potential := potential)
    (integrand := fun x : M => lapPotential x - gradPotentialNormSq x)
    hmeas]
  exact hbase


def fFunctionalBracket (scalarCurvature gradPotentialNormSq : M -> Real) :
    M -> Real :=
  fun x => scalarCurvature x + gradPotentialNormSq x



def fFunctionalClosedBracket (scalarCurvature lapPotential : M -> Real) :
    M -> Real :=
  fun x => scalarCurvature x + lapPotential x


def fFunctionalClosedBracketVariation
    (scalarCurvatureVariation lapPotentialVariation : M -> Real) :
    M -> Real :=
  fun x => scalarCurvatureVariation x + lapPotentialVariation x


def fFunctional [MeasurableSpace M] (mu : Measure M)
    (scalarCurvature gradPotentialNormSq potential : M -> Real) : Real :=
  ∫ x, fFunctionalBracket scalarCurvature gradPotentialNormSq x
    ∂(expNegPotentialWeightedMeasure mu potential)


theorem fFunctional_eq_integral [MeasurableSpace M] (mu : Measure M)
    (scalarCurvature gradPotentialNormSq potential : M -> Real) :
    fFunctional mu scalarCurvature gradPotentialNormSq potential =
      ∫ x, fFunctionalBracket scalarCurvature gradPotentialNormSq x
        ∂(expNegPotentialWeightedMeasure mu potential) := rfl


def fFunctionalAlong [MeasurableSpace M] (mu : Real -> Measure M)
    (scalarCurvature gradPotentialNormSq potential : Real -> M -> Real) :
    Real -> Real :=
  fun s => fFunctional (mu s) (scalarCurvature s) (gradPotentialNormSq s)
    (potential s)


def FFunctionalHasFirstVariationAt [MeasurableSpace M]
    (mu : Real -> Measure M)
    (scalarCurvature gradPotentialNormSq potential : Real -> M -> Real)
    (s0 firstVariation : Real) : Prop :=
  HasDerivAt (fFunctionalAlong mu scalarCurvature gradPotentialNormSq potential)
    firstVariation s0


def fFunctionalFirstVariation [MeasurableSpace M]
    (mu : Real -> Measure M)
    (scalarCurvature gradPotentialNormSq potential : Real -> M -> Real)
    (s0 : Real) : Real :=
  deriv (fFunctionalAlong mu scalarCurvature gradPotentialNormSq potential) s0

theorem fFunctionalFirstVariation_eq_of_hasFirstVariationAt [MeasurableSpace M]
    {mu : Real -> Measure M}
    {scalarCurvature gradPotentialNormSq potential : Real -> M -> Real}
    {s0 firstVariation : Real}
    (h :
      FFunctionalHasFirstVariationAt mu scalarCurvature gradPotentialNormSq
        potential s0 firstVariation) :
    fFunctionalFirstVariation mu scalarCurvature gradPotentialNormSq potential s0 =
      firstVariation := by
  unfold fFunctionalFirstVariation FFunctionalHasFirstVariationAt at *
  exact h.deriv



theorem expNegPotentialDensity_hasDerivAt
    {potentialPath : Real -> M -> Real} {s0 : Real}
    {potentialVariation : M -> Real}
    (hpotential_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => potentialPath s x)
          (potentialVariation x) s0)
    (x : M) :
    HasDerivAt
      (fun s : Real => expNegPotentialDensity (potentialPath s) x)
      (-(potentialVariation x) *
        expNegPotentialDensity (potentialPath s0) x)
      s0 := by
  have h := (hpotential_deriv x).neg.exp
  simpa [expNegPotentialDensity, mul_comm, mul_left_comm, mul_assoc] using h



def expWeightedMeasureVariationFactor
    (potentialVariation metricVariationTrace : M -> Real) : M -> Real :=
  fun x => metricVariationTrace x / 2 - potentialVariation x



def expWeightedIntegralVariationIntegrand
    (potential potentialVariation metricVariationTrace phi phiVariation :
      M -> Real) :
    M -> Real :=
  fun x =>
    expNegPotentialDensity potential x *
      (phiVariation x +
        phi x *
          expWeightedMeasureVariationFactor potentialVariation
            metricVariationTrace x)


end

end DifferentialGeometry.PDE.RicciFlow.Entropy
