import DifferentialGeometry.Geometry.Coordinates.NablaComponents.Tensor0S
import DifferentialGeometry.Geometry.Coordinates.Tensor
import DifferentialGeometry.Tensor.RSTensor.Components
import DifferentialGeometry.Tensor.RSTensor.Field
import DifferentialGeometry.Tensor.RSTensor.Basis
import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.Regularity.TensorRS








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






def coordDerivRSAt {r s : ℕ}
    (X : (x : M) -> TangentSpace I x) (x₀ : M)
    (T : (x : M) -> TensorRSSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) r s x)
    (upper : Fin r -> CoordinateIdx (𝕜 := 𝕜) E)
    (lower : Fin s -> CoordinateIdx (𝕜 := 𝕜) E) : 𝕜 :=
  let β₀ : Tensor0SModel r 𝕜 E :=
    (continuousMultilinearMap_basis (𝕜 := 𝕜) (F := E) (Module.finBasis 𝕜 E) r) upper
  let β : (x : M) -> Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) r x :=
    Tensor0SSpace.constInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      r x₀ β₀
  mfderiv I 𝓘(𝕜, 𝕜)
    (fun y : M =>
      (T y (β y))
        (fun b : Fin s => coordinateFrameAt (I := I) x₀ (lower b) y))
    x₀ (X x₀)


def modelDerivRSAt {r s : ℕ}
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x₀ : M)
    (T : (x : M) -> TensorRSSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) r s x)
    (upper : Fin r -> CoordinateIdx (𝕜 := 𝕜) E)
    (lower : Fin s -> CoordinateIdx (𝕜 := 𝕜) E) : 𝕜 :=
  let X' := VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
    (fun x => X x) (Set.range I)
  let T' : E -> TensorRSModel r s 𝕜 E :=
    tensorRSModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      r s x₀ T
  let β₀ : Tensor0SModel r 𝕜 E :=
    (continuousMultilinearMap_basis (𝕜 := 𝕜) (F := E) (Module.finBasis 𝕜 E) r) upper
  (fderivWithin 𝕜 T'
      (((extChartAt I x₀).symm ⁻¹' Set.univ) ∩ Set.range I)
      (extChartAt I x₀ x₀)
      (X' (extChartAt I x₀ x₀))
    β₀)
    (fun b : Fin s => (Module.finBasis 𝕜 E) (lower b))



def ModelDerivEqCoordDerivRSAt {r s : ℕ}
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x₀ : M)
    (T : (x : M) -> TensorRSSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) r s x) :
    Prop :=
  forall upper lower,
    modelDerivRSAt (I := I) X x₀ T upper lower =
      coordDerivRSAt (I := I) (fun x => X x) x₀ T upper lower

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [IsManifold I 1 M] [IsManifold I 2 M] in
omit [IsManifold I ∞ M] in
private theorem mdifferentiableAt_finset_sum
    {ι : Type*} (t : Finset ι) (f : ι -> M -> 𝕜) {x : M}
    (hf : ∀ i ∈ t, MDifferentiableAt I 𝓘(𝕜, 𝕜) (f i) x) :
    MDifferentiableAt I 𝓘(𝕜, 𝕜) (t.sum f) x := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      simpa using (mdifferentiableAt_const
        (I := I) (I' := 𝓘(𝕜, 𝕜)) (c := (0 : 𝕜)) (x := x))
  | insert i t hit ih =>
      have hfi : MDifferentiableAt I 𝓘(𝕜, 𝕜) (f i) x := hf i (by simp [hit])
      have hft : ∀ j ∈ t, MDifferentiableAt I 𝓘(𝕜, 𝕜) (f j) x := by
        intro j hj
        exact hf j (by simp [hj])
      have hsum : MDifferentiableAt I 𝓘(𝕜, 𝕜) (t.sum f) x := ih hft
      have hadd : MDifferentiableAt I 𝓘(𝕜, 𝕜) (f i + t.sum f) x := hfi.add hsum
      simpa [Finset.sum_insert, hit] using hadd

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [IsManifold I 1 M] [IsManifold I 2 M] in
omit [IsManifold I ∞ M] in
theorem extDerivFun_finset_sum
    {ι : Type*} (t : Finset ι) (f : ι -> M -> 𝕜)
    {x : M} (v : TangentSpace I x)
    (hf : ∀ i ∈ t, MDifferentiableAt I 𝓘(𝕜, 𝕜) (f i) x) :
    extDerivFun (I := I) (t.sum f) x v =
      t.sum (fun i => extDerivFun (I := I) (f i) x v) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      simp
  | insert i t hit ih =>
      have hfi : MDifferentiableAt I 𝓘(𝕜, 𝕜) (f i) x := hf i (by simp [hit])
      have hft : ∀ j ∈ t, MDifferentiableAt I 𝓘(𝕜, 𝕜) (f j) x := by
        intro j hj
        exact hf j (by simp [hj])
      have hsum : MDifferentiableAt I 𝓘(𝕜, 𝕜) (t.sum f) x := by
        exact mdifferentiableAt_finset_sum (I := I) t f hft
      calc
        extDerivFun (I := I) ((insert i t).sum f) x v
            = extDerivFun (I := I)
                (f i + t.sum f) x v := by
              simp [Finset.sum_insert, hit]
        _ = extDerivFun (I := I) (f i) x v +
              extDerivFun (I := I) (t.sum f) x v := by
              have hadd := congr($(extDerivFun_add
                (I := I) (g := f i) (g' := t.sum f)
                (x := x) hfi hsum) v)
              simpa [Pi.add_apply] using hadd
        _ = (insert i t).sum (fun j => extDerivFun (I := I) (f j) x v) := by
              rw [ih hft]
              simp [Finset.sum_insert, hit]

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [IsManifold I 1 M] [IsManifold I 2 M] in
omit [IsManifold I ∞ M] in
theorem extDerivFun_mul
    {f g : M -> 𝕜} {x : M} (v : TangentSpace I x)
    (hf : MDifferentiableAt I 𝓘(𝕜, 𝕜) f x)
    (hg : MDifferentiableAt I 𝓘(𝕜, 𝕜) g x) :
    extDerivFun (I := I) (fun y : M => f y * g y) x v =
      f x * extDerivFun (I := I) g x v +
        extDerivFun (I := I) f x v * g x := by
  change extDerivFun (I := I) (f • g) x v =
      f x * extDerivFun (I := I) g x v +
        extDerivFun (I := I) f x v * g x
  have hprod := fromTangentSpace_mfderiv_smul_apply
    (I := I) (f := f) (g := g) hf hg v
  simpa [extDerivFun, Pi.smul_apply, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
    using hprod

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [IsManifold I 1 M] [IsManifold I 2 M] in
omit [IsManifold I ∞ M] in
theorem extDerivFun_congr_eventually
    {f g : M -> 𝕜} {x : M} (v : TangentSpace I x)
    (h : f =ᶠ[𝓝 x] g) :
    extDerivFun (I := I) f x v = extDerivFun (I := I) g x v := by
  have hmf := Filter.EventuallyEq.mfderiv_eq (I := I) (I' := 𝓘(𝕜, 𝕜)) h
  have hx : f x = g x := h.eq_of_nhds
  unfold extDerivFun
  rw [hmf, hx]

end DifferentialGeometry.Tensor.Coordinates
