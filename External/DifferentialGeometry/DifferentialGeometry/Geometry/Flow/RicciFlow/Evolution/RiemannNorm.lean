import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedFintypeInType false











noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

local instance : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
  simpa using (inferInstance : IsManifold I (∞ : WithTop ℕ∞) M)

section Components

variable {Idx : Type*} [Fintype Idx]



def raisedRm04CompInFrame
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (a b c d : Idx) : Real :=
  ∑ p : Idx, ∑ q : Idx, ∑ r : Idx, ∑ s : Idx,
    gInv t x a p * gInv t x b q * gInv t x c r * gInv t x d s *
      DifferentialGeometry.Integral.Connection.rm04Comp (I := I) (Rm04 t) frame x p q r s

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem raisedRm04CompInFrame_apply
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (a b c d : Idx) :
    raisedRm04CompInFrame (I := I) Rm04 gInv frame t x a b c d =
      ∑ p : Idx, ∑ q : Idx, ∑ r : Idx, ∑ s : Idx,
        gInv t x a p * gInv t x b q * gInv t x c r * gInv t x d s *
          DifferentialGeometry.Integral.Connection.rm04Comp (I := I) (Rm04 t) frame x p q r s := by
  rfl



def rm04NormSqInFrame
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) :
    Real -> M -> Real :=
  fun t x =>
    ∑ a : Idx, ∑ b : Idx, ∑ c : Idx, ∑ d : Idx,
      DifferentialGeometry.Integral.Connection.rm04Comp (I := I) (Rm04 t) frame x a b c d *
        raisedRm04CompInFrame (I := I) Rm04 gInv frame t x a b c d

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem rm04NormSqInFrame_apply
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) :
    rm04NormSqInFrame (I := I) Rm04 gInv frame t x =
      ∑ a : Idx, ∑ b : Idx, ∑ c : Idx, ∑ d : Idx,
        DifferentialGeometry.Integral.Connection.rm04Comp (I := I) (Rm04 t) frame x a b c d *
          raisedRm04CompInFrame (I := I) Rm04 gInv frame t x a b c d := by
  rfl



private def derivProduct5RHS
    (u v w y z du dv dw dy dz : Real) : Real :=
  ((((du * v + u * dv) * w + (u * v) * dw) * y + ((u * v) * w) * dy) * z +
    (((u * v) * w) * y) * dz)



def raisedRm04DerivRHSInFrame
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (rm04Dt : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (a b c d : Idx) : Real :=
  ∑ p : Idx, ∑ q : Idx, ∑ r : Idx, ∑ s : Idx,
    derivProduct5RHS
      (gInv t x a p)
      (gInv t x b q)
      (gInv t x c r)
      (gInv t x d s)
      (DifferentialGeometry.Integral.Connection.rm04Comp (I := I) (Rm04 t) frame x p q r s)
      (inverseMetricEvolutionRHSInFrame (I := I) S gInv frame t x a p)
      (inverseMetricEvolutionRHSInFrame (I := I) S gInv frame t x b q)
      (inverseMetricEvolutionRHSInFrame (I := I) S gInv frame t x c r)
      (inverseMetricEvolutionRHSInFrame (I := I) S gInv frame t x d s)
      (rm04Dt t x p q r s)


def rm04NormDerivRHSInFrame
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (rm04Dt : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) : Real :=
  ∑ a : Idx, ∑ b : Idx, ∑ c : Idx, ∑ d : Idx,
    (rm04Dt t x a b c d *
        raisedRm04CompInFrame (I := I) Rm04 gInv frame t x a b c d +
      DifferentialGeometry.Integral.Connection.rm04Comp (I := I) (Rm04 t) frame x a b c d *
        raisedRm04DerivRHSInFrame (I := I) S Rm04 gInv frame rm04Dt
          t x a b c d)




def Rm04NormRawDerivativeEquationOn
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (rm04Dt : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real) : Prop :=
  ∀ (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
    HasDerivWithinAt
      (fun s : Real => rm04NormSqInFrame (I := I) Rm04 gInv frame s x)
      (rm04NormDerivRHSInFrame (I := I) S Rm04 gInv frame rm04Dt
        (t : Real) x)
      D.carrier
      (t : Real)


def roughLapRm04InnerInFrame
    (roughLapRm04 : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) :
    Real -> M -> Real :=
  fun t x =>
    ∑ a : Idx, ∑ b : Idx, ∑ c : Idx, ∑ d : Idx,
      roughLapRm04 t x a b c d *
        raisedRm04CompInFrame (I := I) Rm04 gInv frame t x a b c d


def nablaRm04NormSqInFrame
    (nablaRm04 : Real -> M -> Idx -> Idx -> Idx -> Idx -> Idx -> Real)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx) :
    Real -> M -> Real :=
  fun t x =>
    ∑ a : Idx, ∑ b : Idx,
    ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
    ∑ p : Idx, ∑ q : Idx, ∑ r : Idx, ∑ s : Idx,
      gInv t x a b *
        gInv t x i p * gInv t x j q * gInv t x k r * gInv t x l s *
          nablaRm04 t x a i j k l * nablaRm04 t x b p q r s





def Rm04NormDerivativeSimplifiesInFrame
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (rm04Dt : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (roughLapInner reaction : Real -> M -> Real) : Prop :=
  ∀ (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
    rm04NormDerivRHSInFrame (I := I) S Rm04 gInv frame rm04Dt
        (t : Real) x =
      2 * roughLapInner (t : Real) x + reaction (t : Real) x


def Rm04NormTimeDerivativeComponentsOn
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (rmNormSq roughLapInner reaction : Real -> M -> Real) : Prop :=
  ∀ (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
    HasDerivWithinAt
      (fun s : Real => rmNormSq s x)
      (2 * roughLapInner (t : Real) x + reaction (t : Real) x)
      D.carrier
      (t : Real)



omit [SigmaCompactSpace M] [T2Space M] in
theorem rm04NormTimeDerivativeComponentsOn_of_rawDerivative
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (rm04Dt : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (roughLapInner reaction : Real -> M -> Real)
    (h_raw : Rm04NormRawDerivativeEquationOn
      (I := I) S Rm04 gInv frame rm04Dt)
    (h_simplify : Rm04NormDerivativeSimplifiesInFrame
      (I := I) S Rm04 gInv frame rm04Dt roughLapInner reaction) :
    Rm04NormTimeDerivativeComponentsOn
      (D := D) (rm04NormSqInFrame (I := I) Rm04 gInv frame)
      roughLapInner reaction := by
  intro t x
  simpa [h_simplify t x] using h_raw t x



def Rm04NormLaplacianComponentsOn
    (rmNormLap roughLapInner nablaRmNormSq : Real -> M -> Real) : Prop :=
  ∀ (t : Real) (x : M),
    rmNormLap t x = 2 * roughLapInner t x + 2 * nablaRmNormSq t x



def Rm04NormHeatEquationOn
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (rmNormSq rmNormLap nablaRmNormSq reaction : Real -> M -> Real) : Prop :=
  ∀ (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
    HasDerivWithinAt
      (fun s : Real => rmNormSq s x)
      (rmNormLap (t : Real) x +
        (-2 * nablaRmNormSq (t : Real) x + reaction (t : Real) x))
      D.carrier
      (t : Real)



omit [TopologicalSpace M] [SigmaCompactSpace M] [T2Space M] in
theorem rm04NormHeatEquationOn_of_components
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (rmNormSq rmNormLap roughLapInner nablaRmNormSq reaction : Real -> M -> Real)
    (h_dt : Rm04NormTimeDerivativeComponentsOn
      (D := D) rmNormSq roughLapInner reaction)
    (h_lap : Rm04NormLaplacianComponentsOn
      rmNormLap roughLapInner nablaRmNormSq) :
    Rm04NormHeatEquationOn
      (D := D) rmNormSq rmNormLap nablaRmNormSq reaction := by
  intro t x
  have hvalue :
      rmNormLap (t : Real) x +
          (-2 * nablaRmNormSq (t : Real) x + reaction (t : Real) x) =
        2 * roughLapInner (t : Real) x + reaction (t : Real) x := by
    rw [h_lap (t : Real) x]
    ring
  rw [hvalue]
  exact h_dt t x



omit [SigmaCompactSpace M] [T2Space M] in
theorem rm04NormHeatEquationOn_of_rawDerivative
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (rm04Dt : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (rmNormLap roughLapInner nablaRmNormSq reaction : Real -> M -> Real)
    (h_raw : Rm04NormRawDerivativeEquationOn
      (I := I) S Rm04 gInv frame rm04Dt)
    (h_simplify : Rm04NormDerivativeSimplifiesInFrame
      (I := I) S Rm04 gInv frame rm04Dt roughLapInner reaction)
    (h_lap : Rm04NormLaplacianComponentsOn
      rmNormLap roughLapInner nablaRmNormSq) :
    Rm04NormHeatEquationOn
      (D := D) (rm04NormSqInFrame (I := I) Rm04 gInv frame)
      rmNormLap nablaRmNormSq reaction := by
  exact
    rm04NormHeatEquationOn_of_components
      (D := D)
      (rm04NormSqInFrame (I := I) Rm04 gInv frame)
      rmNormLap roughLapInner nablaRmNormSq reaction
      (rm04NormTimeDerivativeComponentsOn_of_rawDerivative
        (I := I) S Rm04 gInv frame rm04Dt roughLapInner reaction
        h_raw h_simplify)
      h_lap

end Components

end DifferentialGeometry.PDE.RicciFlow
