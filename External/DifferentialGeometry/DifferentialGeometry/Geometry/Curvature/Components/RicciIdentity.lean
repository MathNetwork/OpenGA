import DifferentialGeometry.Geometry.Curvature.Components.Christoffel

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

noncomputable section

namespace DifferentialGeometry.Integral.Connection

open Bundle Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
variable {x : M}







section CoordinateChristoffelCurvature

open DifferentialGeometry.Tensor.Coordinates

def tensor0SRicciIdentityCoordInput {s : ℕ}
    (i j : CoordinateIdx (𝕜 := Real) E)
    (ks : Fin s -> CoordinateIdx (𝕜 := Real) E) :
    Fin (s + 2) -> CoordinateIdx (𝕜 := Real) E :=
  Fin.cases i (Fin.cases j ks)





omit [FiniteDimensional ℝ E] in
theorem curvatureAction0SAt_coordFrame_of_christoffelCurv
    [T2Space M]
    (_h : FiniteDimensional ℝ E)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (1 : WithTop ℕ∞))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (x0 : M) {s : ℕ}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x0)
    (hRm : Rm13RealizesConnection (I := I) cov Rm13)
    (hcurv : ConnectionCurvatureCoordAt (I := I) cov x0)
    (i j : CoordinateIdx (𝕜 := Real) E)
    (ks : Fin s -> CoordinateIdx (𝕜 := Real) E) :
    curvatureAction0SAt (I := I) Rm13 alpha
        (coordinateFrameAt (I := I) x0 i x0)
        (coordinateFrameAt (I := I) x0 j x0)
        (fun q : Fin s => coordinateFrameAt (I := I) x0 (ks q) x0)
      =
        -∑ q : Fin s, ∑ m : CoordinateIdx (𝕜 := Real) E,
          christoffelCurvCoeffAt (I := I) cov x0 i j (ks q) m *
            coordComponent0SAt (I := I) alpha (Function.update ks q m) := by
  letI := _h
  classical
  let slots : Fin s -> TangentSpace I x0 :=
    fun q => coordinateFrameAt (I := I) x0 (ks q) x0
  have hslot (q : Fin s) (m : CoordinateIdx (𝕜 := Real) E) :
      oneFormAtSlot0S (I := I) alpha slots q
          (fun _ : Fin 1 => coordinateFrameAt (I := I) x0 m x0) =
        coordComponent0SAt (I := I) alpha (Function.update ks q m) := by
    rw [oneFormAtSlot0S_apply, coordComponent0SAt_apply]
    congr 1
    funext a
    by_cases ha : a = q
    · subst ha
      simp [slots]
    · simp [slots, Function.update, ha]
  change
    -∑ q : Fin s,
      Rm13 x0 (oneFormAtSlot0S (I := I) alpha slots q)
        (vec3 (coordinateFrameAt (I := I) x0 i x0)
          (coordinateFrameAt (I := I) x0 j x0) (slots q))
      =
        -∑ q : Fin s, ∑ m : CoordinateIdx (𝕜 := Real) E,
          christoffelCurvCoeffAt (I := I) cov x0 i j (ks q) m *
            coordComponent0SAt (I := I) alpha (Function.update ks q m)
  congr 1
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [rm13_eval_eq_christoffelCurvCoord
    (I := I) cov hcov Rm13 x0 (oneFormAtSlot0S (I := I) alpha slots q)
    hRm hcurv i j (ks q)]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [hslot q m]






omit [FiniteDimensional ℝ E] in
theorem tensor0S_ricciIdentity_coordFrame_of_christoffelCurv
    [T2Space M]
    (_h : FiniteDimensional ℝ E)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (1 : WithTop ℕ∞))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (x0 : M) {s : ℕ}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x0)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (s + 2) x0)
    (hRm : Rm13RealizesConnection (I := I) cov Rm13)
    (hcurv : ConnectionCurvatureCoordAt (I := I) cov x0)
    (hRicci : Tensor0SRicciIdentityAt (I := I) Rm13 alpha nabla2Alpha)
    (i j : CoordinateIdx (𝕜 := Real) E)
    (ks : Fin s -> CoordinateIdx (𝕜 := Real) E) :
    coordComponent0SAt (I := I) nabla2Alpha
        (tensor0SRicciIdentityCoordInput (E := E) i j ks) -
      coordComponent0SAt (I := I) nabla2Alpha
        (tensor0SRicciIdentityCoordInput (E := E) j i ks)
      =
        -∑ q : Fin s, ∑ m : CoordinateIdx (𝕜 := Real) E,
          christoffelCurvCoeffAt (I := I) cov x0 i j (ks q) m *
            coordComponent0SAt (I := I) alpha (Function.update ks q m) := by
  letI := _h
  classical
  let slots : Fin s -> TangentSpace I x0 :=
    fun q => coordinateFrameAt (I := I) x0 (ks q) x0
  have hleft :
      coordComponent0SAt (I := I) nabla2Alpha
          (tensor0SRicciIdentityCoordInput (E := E) i j ks) =
        nabla2Alpha
          (metricTraceInput (I := I) (coordinateFrameAt (I := I) x0 i x0)
            (coordinateFrameAt (I := I) x0 j x0) slots) := by
    rw [coordComponent0SAt_apply]
    congr 1
    funext a
    refine Fin.cases ?_ ?_ a
    · simp [tensor0SRicciIdentityCoordInput, metricTraceInput, slots]
    · intro a
      refine Fin.cases ?_ ?_ a
      · change (coordinateFrameAt_toBasis (I := I) x0) j =
          coordinateFrameAt (I := I) x0 j x0
        rw [coordinateFrameAt_toBasis_apply]
      · intro a
        simp [tensor0SRicciIdentityCoordInput, metricTraceInput, slots]
  have hright :
      coordComponent0SAt (I := I) nabla2Alpha
          (tensor0SRicciIdentityCoordInput (E := E) j i ks) =
        nabla2Alpha
          (metricTraceInput (I := I) (coordinateFrameAt (I := I) x0 j x0)
            (coordinateFrameAt (I := I) x0 i x0) slots) := by
    rw [coordComponent0SAt_apply]
    congr 1
    funext a
    refine Fin.cases ?_ ?_ a
    · simp [tensor0SRicciIdentityCoordInput, metricTraceInput, slots]
    · intro a
      refine Fin.cases ?_ ?_ a
      · change (coordinateFrameAt_toBasis (I := I) x0) i =
          coordinateFrameAt (I := I) x0 i x0
        rw [coordinateFrameAt_toBasis_apply]
      · intro a
        simp [tensor0SRicciIdentityCoordInput, metricTraceInput, slots]
  calc
    coordComponent0SAt (I := I) nabla2Alpha
        (tensor0SRicciIdentityCoordInput (E := E) i j ks) -
      coordComponent0SAt (I := I) nabla2Alpha
        (tensor0SRicciIdentityCoordInput (E := E) j i ks)
        = curvatureAction0SAt (I := I) Rm13 alpha
            (coordinateFrameAt (I := I) x0 i x0)
            (coordinateFrameAt (I := I) x0 j x0) slots := by
          rw [hleft, hright]
          exact hRicci (coordinateFrameAt (I := I) x0 i x0)
            (coordinateFrameAt (I := I) x0 j x0) slots
    _ = -∑ q : Fin s, ∑ m : CoordinateIdx (𝕜 := Real) E,
          christoffelCurvCoeffAt (I := I) cov x0 i j (ks q) m *
            coordComponent0SAt (I := I) alpha (Function.update ks q m) := by
          simpa [slots] using
            curvatureAction0SAt_coordFrame_of_christoffelCurv
              (I := I) inferInstance cov hcov Rm13 x0 alpha hRm hcurv i j ks






def OneFormThirdCommChristoffelCoordAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (x₀ : M)
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x₀)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x₀) :
    Prop :=
  ∀ i k j : CoordinateIdx (𝕜 := Real) E,
    nabla2Alpha
        (vec3 (coordinateFrameAt (I := I) x₀ i x₀)
          (coordinateFrameAt (I := I) x₀ k x₀)
          (coordinateFrameAt (I := I) x₀ j x₀)) -
      nabla2Alpha
        (vec3 (coordinateFrameAt (I := I) x₀ k x₀)
          (coordinateFrameAt (I := I) x₀ i x₀)
          (coordinateFrameAt (I := I) x₀ j x₀)) =
        -∑ m : CoordinateIdx (𝕜 := Real) E,
          christoffelCurvCoeffAt (I := I) cov x₀ i k j m *
            alpha (fun _ : Fin 1 => coordinateFrameAt (I := I) x₀ m x₀)




omit [FiniteDimensional ℝ E] in
theorem one_form_third_comm_coord_of_christoffelCurv
    [T2Space M]
    (_h : FiniteDimensional ℝ E)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (1 : WithTop ℕ∞))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (x₀ : M)
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x₀)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x₀)
    (hRm : Rm13RealizesConnection (I := I) cov Rm13)
    (hcurv : ConnectionCurvatureCoordAt (I := I) cov x₀)
    (hcoord : OneFormThirdCommChristoffelCoordAt (I := I) cov x₀ alpha nabla2Alpha) :
    OneFormThirdCovDerivCommAt (I := I) Rm13 alpha nabla2Alpha := by
  letI := _h
  refine one_form_third_comm_of_coord_ijk (I := I) Rm13 alpha
    (coordinateFrameAt_toBasis (I := I) x₀) nabla2Alpha ?_
  intro i k j
  have hRmCoord := rm13_eval_eq_christoffelCurvCoord
    (I := I) cov hcov Rm13 x₀ alpha hRm hcurv i k j
  have hcoord' := hcoord i k j
  simp only [coordinateFrameAt_toBasis_apply]
  rw [hRmCoord]
  exact hcoord'

end CoordinateChristoffelCurvature
end DifferentialGeometry.Integral.Connection
