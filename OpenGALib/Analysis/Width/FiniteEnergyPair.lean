import OpenGALib.Analysis.WidthComparison

/-!
# Constructors for finite-energy pairs

The geometric part of the sweepout formalization supplies two measurable
vector fields in a fixed inner-product target and proves energy integrability.
This constructor packages exactly those hypotheses into the analytic object
used by the width comparison layer.
-/

noncomputable section

open MeasureTheory

namespace OpenGA

variable {X F : Type} [MeasurableSpace X]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {μ : Measure X} {v w : X → F}

/-- Build a finite-energy pair from measurable vector fields with integrable
Dirichlet energy. -/
def FiniteEnergyPair.ofFields
    (hv : AEStronglyMeasurable v μ) (hw : AEStronglyMeasurable w μ)
    (henergy : Integrable (fun x => energyDensity (v x) (w x)) μ) :
    FiniteEnergyPair :=
  { domain := X
    target := F
    measure := μ
    first := v
    second := w
    first_measurable := hv
    second_measurable := hw
    energy_integrable := henergy }

theorem FiniteEnergyPair.ofFields_area
    (hv : AEStronglyMeasurable v μ) (hw : AEStronglyMeasurable w μ)
    (henergy : Integrable (fun x => energyDensity (v x) (w x)) μ) :
    (FiniteEnergyPair.ofFields hv hw henergy).area =
      ∫ x, areaDensity (v x) (w x) ∂μ := by
  rfl

theorem FiniteEnergyPair.ofFields_energy
    (hv : AEStronglyMeasurable v μ) (hw : AEStronglyMeasurable w μ)
    (henergy : Integrable (fun x => energyDensity (v x) (w x)) μ) :
    (FiniteEnergyPair.ofFields hv hw henergy).energy =
      ∫ x, energyDensity (v x) (w x) ∂μ := by
  rfl

end OpenGA
