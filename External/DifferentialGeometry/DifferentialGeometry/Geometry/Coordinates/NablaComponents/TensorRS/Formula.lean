import DifferentialGeometry.Geometry.Coordinates.NablaComponents.TensorRS.ApplyInput
import DifferentialGeometry.Geometry.Coordinates.NablaComponents.TensorRS.ModelBridge







set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section

namespace DifferentialGeometry.Tensor.Coordinates

open Bundle Set Tensor0SBundle TensorLieDeriv
open scoped BigOperators Manifold ContDiff Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ∞ M]




theorem nablaRS_coordFrame_slots {r s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s)
    (x₀ : M) (hderiv : ModelDerivEqCoordDerivRSAt (I := I) X x₀ (fun x => T x))
    (upper : Fin r -> CoordinateIdx (𝕜 := 𝕜) E)
    (lower : Fin s -> CoordinateIdx (𝕜 := 𝕜) E) :
    coordComponentRSAt (I := I)
        (nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
          r s cov X T x₀)
        upper lower =
      coordDerivRSAt (I := I) (fun x => X x) x₀ (fun x => T x) upper lower
      +
      ∑ a : Fin r, ∑ k : CoordinateIdx (𝕜 := 𝕜) E,
        christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
          x₀ (X x₀) k (upper a) *
          coordComponentRSAt (I := I) (T x₀) (Function.update upper a k) lower
      -
      ∑ b : Fin s, ∑ k : CoordinateIdx (𝕜 := 𝕜) E,
        christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
          x₀ (X x₀) (lower b) k *
          coordComponentRSAt (I := I) (T x₀) upper (Function.update lower b k) := by
  classical
  simp only [nablaRSFun, TensorLieDeriv.mcovariantDeriv_tensorRSFromConnection,
    TensorLieDeriv.mcovariantDeriv_tensorRSWithinFromConnection]
  rw [← tensorRSModelAt_coordComponentRSAt (I := I) x₀
    (TensorLieDeriv.mcovariantDeriv_tensorRSWithin
      (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s X
      (connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀)
      T Set.univ x₀) upper lower]
  have hmodel := TensorLieDeriv.covariantDeriv_tensorRSModelWithin_apply_basis_slots
    (𝕜 := 𝕜) (E := E)
    (basis := Module.finBasis 𝕜 E)
    (X := VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
      (fun x => X x) (Set.range I))
    (ΓX := connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀)
    (T := tensorRSModelInChart (𝕜 := 𝕜) (E := E) (H := H)
      (I := I) (M := M) r s x₀ (fun x => T x))
    (u := ((extChartAt I x₀).symm ⁻¹' Set.univ) ∩ Set.range I)
    (x := extChartAt I x₀ x₀)
    (upper := upper)
    (lower := lower)
  unfold TensorLieDeriv.mcovariantDeriv_tensorRSWithin
  rw [TensorLieDeriv.tensorRSModelAt_trivializationAt_symm]
  refine hmodel.trans ?_
  simp_rw [connCoeff_eq_christoffelAlong_coord (I := I) cov (fun x => X x) x₀]
  change
    modelDerivRSAt (I := I) X x₀ (fun x => T x) upper lower
      +
      (∑ a : Fin r, ∑ k : CoordinateIdx (𝕜 := 𝕜) E,
        christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
          x₀ (X x₀) k (upper a) *
          (tensorRSModelInChart (𝕜 := 𝕜) (E := E) (H := H)
            (I := I) (M := M) r s x₀ (fun x => T x)
            (extChartAt I x₀ x₀)
            ((continuousMultilinearMap_basis
              (𝕜 := 𝕜) (F := E) (Module.finBasis 𝕜 E) r)
              (Function.update upper a k)))
            (fun b : Fin s => (Module.finBasis 𝕜 E) (lower b)))
      -
      (∑ b : Fin s, ∑ k : CoordinateIdx (𝕜 := 𝕜) E,
        christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
          x₀ (X x₀) (lower b) k *
          (tensorRSModelInChart (𝕜 := 𝕜) (E := E) (H := H)
            (I := I) (M := M) r s x₀ (fun x => T x)
            (extChartAt I x₀ x₀)
            ((continuousMultilinearMap_basis
              (𝕜 := 𝕜) (F := E) (Module.finBasis 𝕜 E) r) upper))
            (Function.update
              (fun c : Fin s => (Module.finBasis 𝕜 E) (lower c))
              b ((Module.finBasis 𝕜 E) k))) =
      coordDerivRSAt (I := I) (fun x => X x) x₀ (fun x => T x) upper lower
      +
      (∑ a : Fin r, ∑ k : CoordinateIdx (𝕜 := 𝕜) E,
        christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
          x₀ (X x₀) k (upper a) *
          coordComponentRSAt (I := I) (T x₀) (Function.update upper a k) lower)
      -
      (∑ b : Fin s, ∑ k : CoordinateIdx (𝕜 := 𝕜) E,
        christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
          x₀ (X x₀) (lower b) k *
          coordComponentRSAt (I := I) (T x₀) upper (Function.update lower b k))
  rw [hderiv upper lower]
  have hupperSum :
      (∑ a : Fin r, ∑ k : CoordinateIdx (𝕜 := 𝕜) E,
        christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
          x₀ (X x₀) k (upper a) *
          (tensorRSModelInChart (𝕜 := 𝕜) (E := E) (H := H)
            (I := I) (M := M) r s x₀ (fun x => T x)
            (extChartAt I x₀ x₀)
            ((continuousMultilinearMap_basis
              (𝕜 := 𝕜) (F := E) (Module.finBasis 𝕜 E) r)
              (Function.update upper a k)))
            (fun b : Fin s => (Module.finBasis 𝕜 E) (lower b))) =
      (∑ a : Fin r, ∑ k : CoordinateIdx (𝕜 := 𝕜) E,
        christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
          x₀ (X x₀) k (upper a) *
          coordComponentRSAt (I := I) (T x₀) (Function.update upper a k) lower) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    unfold tensorRSModelInChart
    rw [extChartAt_to_inv]
    rw [tensorRSModelAt_coordComponentRSAt (I := I) x₀ (T x₀)
      (Function.update upper a k) lower]
  have hlowerSum :
      (∑ b : Fin s, ∑ k : CoordinateIdx (𝕜 := 𝕜) E,
        christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
          x₀ (X x₀) (lower b) k *
          (tensorRSModelInChart (𝕜 := 𝕜) (E := E) (H := H)
            (I := I) (M := M) r s x₀ (fun x => T x)
            (extChartAt I x₀ x₀)
            ((continuousMultilinearMap_basis
              (𝕜 := 𝕜) (F := E) (Module.finBasis 𝕜 E) r) upper))
            (Function.update
              (fun c : Fin s => (Module.finBasis 𝕜 E) (lower c))
              b ((Module.finBasis 𝕜 E) k))) =
      (∑ b : Fin s, ∑ k : CoordinateIdx (𝕜 := 𝕜) E,
        christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
          x₀ (X x₀) (lower b) k *
          coordComponentRSAt (I := I) (T x₀) upper (Function.update lower b k)) := by
    refine Finset.sum_congr rfl fun b _ => ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    unfold tensorRSModelInChart
    rw [extChartAt_to_inv]
    have hslots :
        Function.update
            (fun c : Fin s => (Module.finBasis 𝕜 E) (lower c))
            b ((Module.finBasis 𝕜 E) k) =
          fun c : Fin s => (Module.finBasis 𝕜 E) (Function.update lower b k c) := by
      funext c
      by_cases hc : c = b
      · subst hc
        simp
      · simp [Function.update, hc]
    rw [hslots]
    rw [← tensorRSModelAt_coordComponentRSAt (I := I) x₀ (T x₀)
      upper (Function.update lower b k)]
  rw [hupperSum, hlowerSum]



theorem nablaRS_coordFrame_slots_of_smooth {r s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s)
    (x₀ : M)
    (upper : Fin r -> CoordinateIdx (𝕜 := 𝕜) E)
    (lower : Fin s -> CoordinateIdx (𝕜 := 𝕜) E) :
    coordComponentRSAt (I := I)
        (nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
          r s cov X T x₀)
        upper lower =
      coordDerivRSAt (I := I) (fun x => X x) x₀ (fun x => T x) upper lower
      +
      ∑ a : Fin r, ∑ k : CoordinateIdx (𝕜 := 𝕜) E,
        christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
          x₀ (X x₀) k (upper a) *
          coordComponentRSAt (I := I) (T x₀) (Function.update upper a k) lower
      -
      ∑ b : Fin s, ∑ k : CoordinateIdx (𝕜 := 𝕜) E,
        christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
          x₀ (X x₀) (lower b) k *
          coordComponentRSAt (I := I) (T x₀) upper (Function.update lower b k) := by
  exact nablaRS_coordFrame_slots (I := I) cov X T x₀
    (modelDeriv_eq_coordDerivRSAt (I := I) X x₀ T) upper lower


end DifferentialGeometry.Tensor.Coordinates
