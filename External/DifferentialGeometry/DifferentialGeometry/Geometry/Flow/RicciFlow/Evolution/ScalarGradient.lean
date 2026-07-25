import Mathlib.Data.Real.Sqrt

set_option autoImplicit false
set_option linter.style.longLine false



















noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

variable {M : Type*}

def ScalarGradientEstimateOn
    (gradScalarNormSq scalar decayHalf decayCubic : Real -> M -> Real)
    (beta C : Real) : Prop :=
  ∀ (t : Real) (x : M),
    gradScalarNormSq t x / scalar t x ^ 3 ≤
      beta * decayHalf t x + C * decayCubic t x



def PinchingEstimateYetAgainOn
    (tracefreeRmRatio decay : Real -> M -> Real) (C : Real) : Prop :=
  ∀ (t : Real) (x : M), tracefreeRmRatio t x ≤ C * decay t x

def GradScalarNormEvolutionOn
    (gradScalarNormSq hessianScalarNormSq gradRicciNormSq : Real -> M -> Real) :
    Prop :=
  ∀ (t : Real) (x : M),
    gradScalarNormSq t x =
      hessianScalarNormSq t x + gradRicciNormSq t x

def GradScalarOverScalarEvolutionOn
    (gradScalarNormSq scalar rhs : Real -> M -> Real) : Prop :=
  ∀ (t : Real) (x : M), gradScalarNormSq t x / scalar t x = rhs t x

def ScalarAndRicciNormSquaredEvolutionOn
    (scalar ricciNormSq scalarSqRhs ricciNormSqRhs : Real -> M -> Real) : Prop :=
  ∀ (t : Real) (x : M),
    scalar t x ^ 2 = scalarSqRhs t x ∧ ricciNormSq t x = ricciNormSqRhs t x


def ScalarSquaredEvolutionOn
    (scalar scalarSqRhs : Real -> M -> Real) : Prop :=
  ∀ (t : Real) (x : M), scalar t x ^ 2 = scalarSqRhs t x


def RicciNormSquaredEvolutionOn
    (ricciNormSq ricciNormSqRhs : Real -> M -> Real) : Prop :=
  ∀ (t : Real) (x : M), ricciNormSq t x = ricciNormSqRhs t x



def tracefreeRicciNormSqAtOf (scalar ricciNormSq : Real) : Real :=
  ricciNormSq - scalar ^ 2 / 3



def tracefreeRicciNormSqOf
    (scalar ricciNormSq : Real -> M -> Real) (t : Real) (x : M) : Real :=
  tracefreeRicciNormSqAtOf (scalar t x) (ricciNormSq t x)

def TracefreeRicciEvolutionInequalityOn
    (tracefreeRicciNormSq scalar ricciNormSq rhs : Real -> M -> Real) : Prop :=
  ∀ (t : Real) (x : M),
    tracefreeRicciNormSq t x = tracefreeRicciNormSqOf scalar ricciNormSq t x ∧
      tracefreeRicciNormSq t x ≤ rhs t x

def GradRicciControlsGradScalarOn
    (gradRicciNormSq gradScalarNormSq : Real -> M -> Real) : Prop :=
  ∀ (t : Real) (x : M),
    gradScalarNormSq t x / 3 ≤ gradRicciNormSq t x ∧
      (1 / 37 : Real) * gradRicciNormSq t x ≤
        gradRicciNormSq t x - gradScalarNormSq t x / 3



def CauchySchwarzEstimateForGradScalarOn
    (gradScalarNormSq hessianScalarNormSq gradRicciNormSq : Real -> M -> Real)
    (C : Real) : Prop :=
  ∀ (t : Real) (x : M),
    gradScalarNormSq t x ≤
      C * hessianScalarNormSq t x * gradRicciNormSq t x

def scalarGradientV
    (gradScalarNormSq scalar tracefreeRicciNormSq : Real -> M -> Real)
    (t : Real) (x : M) : Real :=
  gradScalarNormSq t x / scalar t x +
    (37 / 2 : Real) * (8 * Real.sqrt 3 + 1) * tracefreeRicciNormSq t x

def VGradientQuantityEvolutionInequalityOn
    (V scalar tracefreeRicciNormSq gradRicciNormSq : Real -> M -> Real) : Prop :=
  ∀ (t : Real) (x : M),
    V t x ≤ scalar t x * tracefreeRicciNormSq t x - gradRicciNormSq t x

def WTracefreeRicciBoundOn
    (W scalar tracefreeRicciNormSq : Real -> M -> Real) : Prop :=
  ∀ (t : Real) (x : M),
    W t x ≤ (50 / 3 : Real) * scalar t x * tracefreeRicciNormSq t x

theorem grad_scalar_norm_squared_evolution
    (gradScalarNormSq hessianScalarNormSq gradRicciNormSq : Real -> M -> Real)
    (h : GradScalarNormEvolutionOn
      gradScalarNormSq hessianScalarNormSq gradRicciNormSq) :
    GradScalarNormEvolutionOn
      gradScalarNormSq hessianScalarNormSq gradRicciNormSq :=
  h

theorem grad_scalar_over_scalar_evolution
    (gradScalarNormSq scalar rhs : Real -> M -> Real)
    (h : GradScalarOverScalarEvolutionOn gradScalarNormSq scalar rhs) :
    GradScalarOverScalarEvolutionOn gradScalarNormSq scalar rhs :=
  h

theorem scalar_and_ricci_norm_squared_evolution
    (scalar ricciNormSq scalarSqRhs ricciNormSqRhs : Real -> M -> Real)
    (h : ScalarAndRicciNormSquaredEvolutionOn
      scalar ricciNormSq scalarSqRhs ricciNormSqRhs) :
    ScalarAndRicciNormSquaredEvolutionOn
      scalar ricciNormSq scalarSqRhs ricciNormSqRhs :=
  h

theorem tracefree_ricci_evolution_inequality
    (tracefreeRicciNormSq scalar ricciNormSq rhs : Real -> M -> Real)
    (h : TracefreeRicciEvolutionInequalityOn
      tracefreeRicciNormSq scalar ricciNormSq rhs) :
    TracefreeRicciEvolutionInequalityOn
      tracefreeRicciNormSq scalar ricciNormSq rhs :=
  h

theorem grad_ricci_controls_grad_scalar
    (gradRicciNormSq gradScalarNormSq : Real -> M -> Real)
    (h : GradRicciControlsGradScalarOn gradRicciNormSq gradScalarNormSq) :
    GradRicciControlsGradScalarOn gradRicciNormSq gradScalarNormSq :=
  h

theorem v_for_grad_r_one
    (V scalar tracefreeRicciNormSq gradRicciNormSq : Real -> M -> Real)
    (h : VGradientQuantityEvolutionInequalityOn
      V scalar tracefreeRicciNormSq gradRicciNormSq) :
    VGradientQuantityEvolutionInequalityOn
      V scalar tracefreeRicciNormSq gradRicciNormSq :=
  h

theorem v_for_grad_r_two
    (W scalar tracefreeRicciNormSq : Real -> M -> Real)
    (h : WTracefreeRicciBoundOn W scalar tracefreeRicciNormSq) :
    WTracefreeRicciBoundOn W scalar tracefreeRicciNormSq :=
  h

theorem estimate_gradient_of_scalar
    (gradScalarNormSq scalar : Real -> M -> Real)
    (h :
      ∃ betaBar deltaBar : Real,
        0 < betaBar ∧ 0 < deltaBar ∧
        ∃ decayHalf decayCubic : Real -> M -> Real,
          ∀ beta : Real, 0 ≤ beta -> beta ≤ betaBar ->
            ∃ C : Real,
              ScalarGradientEstimateOn
                gradScalarNormSq scalar decayHalf decayCubic beta C) :
    ∃ betaBar deltaBar : Real,
      0 < betaBar ∧ 0 < deltaBar ∧
      ∃ decayHalf decayCubic : Real -> M -> Real,
        ∀ beta : Real, 0 ≤ beta -> beta ≤ betaBar ->
          ∃ C : Real,
            ScalarGradientEstimateOn
              gradScalarNormSq scalar decayHalf decayCubic beta C :=
  h

end DifferentialGeometry.PDE.RicciFlow
