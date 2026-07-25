import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.PotentialGeometry

set_option autoImplicit false









namespace DifferentialGeometry.PDE.RicciFlow.Entropy

noncomputable section

open MeasureTheory
open DifferentialGeometry.Integral.Connection
open scoped Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩




theorem w_square_form
    (mu : Measure M) (g : SmoothRiemannianMetric I M) (n : Nat)
    {tau : Real} (htau : 0 < tau) (scalarCurvature : M -> Real)
    {v : M -> Real} (hv : ContMDiff I 𝓘(Real, Real) ∞ v)
    (hpos : ∀ x : M, 0 < v x) :
    wFunctional mu n tau scalarCurvature
        (fun x =>
          g.inner x
            (gradientFun (I := I) g
              (perelmanPotential n tau (fun y => v y * v y)) x)
            (gradientFun (I := I) g
              (perelmanPotential n tau (fun y => v y * v y)) x))
        (perelmanPotential n tau (fun y => v y * v y)) =
      ∫ x,
        4 * tau * g.inner x
            (gradientFun (I := I) g v x)
            (gradientFun (I := I) g v x) +
          tau * scalarCurvature x * (v x * v x) -
          (v x * v x) * Real.log (v x * v x) +
          (Real.log (perelmanDensityPrefactor n tau) - (n : Real)) *
            (v x * v x) ∂mu := by
  let density : M -> Real := fun x => v x * v x
  let potential : M -> Real := perelmanPotential n tau density
  let gradSq : M -> Real := fun x =>
    g.inner x
      (gradientFun (I := I) g potential x)
      (gradientFun (I := I) g potential x)
  have hdensity : perelmanDensity n tau potential = density := by
    exact density_potential n density htau fun x => mul_pos (hpos x) (hpos x)
  have hmeas :
      AEMeasurable
        (fun x : M => ENNReal.ofReal (perelmanDensity n tau potential x)) mu := by
    rw [hdensity]
    exact (ENNReal.continuous_ofReal.comp (hv.mul hv).continuous).aemeasurable
  rw [show
    wFunctional mu n tau scalarCurvature
        (fun x =>
          g.inner x
            (gradientFun (I := I) g
              (perelmanPotential n tau (fun y => v y * v y)) x)
            (gradientFun (I := I) g
              (perelmanPotential n tau (fun y => v y * v y)) x))
        (perelmanPotential n tau (fun y => v y * v y)) =
      wFunctional mu n tau scalarCurvature gradSq potential by rfl]
  rw [wFunctional_base mu n tau scalarCurvature gradSq potential htau.le hmeas]
  apply integral_congr_ae
  filter_upwards with x
  rw [congrFun hdensity x]
  change
    (v x * v x) *
        (tau * (scalarCurvature x + gradSq x) + potential x - (n : Real)) = _
  rw [show potential x =
      -Real.log (v x * v x) + Real.log (perelmanDensityPrefactor n tau) by
    exact potential_square n hpos htau x]
  have henergy :
      (v x * v x) * gradSq x =
        4 * g.inner x
          (gradientFun (I := I) g v x)
          (gradientFun (I := I) g v x) := by
    exact square_pot_energy (I := I) g n hv hpos htau x
  linear_combination tau * henergy

end

end DifferentialGeometry.PDE.RicciFlow.Entropy
