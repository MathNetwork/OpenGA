import OpenGALib.Analysis.Width.FiniteEnergyPair
import OpenGALib.GeometricMeasureTheory.Varifold.Parametrization

/-!
# Energy pair of a parametrized surface

For a `C¹` map from a Euclidean two-dimensional parameter domain, the two
columns of the Fréchet derivative in an orthonormal basis form the concrete
finite-energy pair used by the area-energy comparison. This is the local
parameter-domain construction; passing from manifold charts to a global
sweepout remains a separate gluing problem.
-/

noncomputable section

open MeasureTheory Set
open scoped InnerProductSpace

namespace OpenGA

variable {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

structure ParametrizedSurfaceEnergy where
  map : EuclideanSpace ℝ (Fin 2) → F
  smooth : ContDiff ℝ 1 map
  region : Set (EuclideanSpace ℝ (Fin 2))
  basis : OrthonormalBasis (Fin 2) ℝ (EuclideanSpace ℝ (Fin 2))
  energy_integrable : IntegrableOn (fun x =>
    energyDensity (fderiv ℝ map x (basis 0)) (fderiv ℝ map x (basis 1))) region volume

namespace ParametrizedSurfaceEnergy

private theorem derivative_measurable (P : ParametrizedSurfaceEnergy (F := F))
    (i : Fin 2) :
    AEStronglyMeasurable (fun x => fderiv ℝ P.map x (P.basis i))
      (volume.restrict P.region) := by
  have hcont : Continuous (fun x => fderiv ℝ P.map x (P.basis i)) :=
    (P.smooth.continuous_fderiv (by norm_num)).clm_apply continuous_const
  exact hcont.aestronglyMeasurable

/-- The finite-energy pair formed by the two derivative columns. -/
def pair (P : ParametrizedSurfaceEnergy (F := F)) : FiniteEnergyPair :=
  FiniteEnergyPair.ofFields
    (derivative_measurable P 0) (derivative_measurable P 1) P.energy_integrable

@[simp] theorem pair_first (P : ParametrizedSurfaceEnergy (F := F)) :
    (P.pair).first = fun x => fderiv ℝ P.map x (P.basis 0) := rfl

@[simp] theorem pair_second (P : ParametrizedSurfaceEnergy (F := F)) :
    (P.pair).second = fun x => fderiv ℝ P.map x (P.basis 1) := rfl

theorem pair_energy (P : ParametrizedSurfaceEnergy (F := F)) :
    P.pair.energy = ∫ x in P.region, energyDensity
      (fderiv ℝ P.map x (P.basis 0)) (fderiv ℝ P.map x (P.basis 1)) := by
  exact FiniteEnergyPair.ofFields_energy
    (derivative_measurable P 0) (derivative_measurable P 1) P.energy_integrable

end ParametrizedSurfaceEnergy
end OpenGA
