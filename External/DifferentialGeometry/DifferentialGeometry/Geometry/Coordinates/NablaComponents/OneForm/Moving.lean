import DifferentialGeometry.Geometry.Coordinates.NablaComponents.OneForm.ConnectionProduct







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


theorem nabla0SFun_one_eval_coordFrame_expanded
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1)
    (x₀ : M) (hderiv : ModelDerivEqCoordDeriv0SAt (I := I) X x₀ (fun x => α x))
    (Z : TangentSpace I x₀) :
    (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      1 cov X α x₀) (fun _ : Fin 1 => Z) =
      ∑ j : CoordinateIdx (𝕜 := 𝕜) E,
        (coordinateFrameAt_toBasis (I := I) x₀).coord j Z *
          (coordDeriv0SAt (I := I) (fun x => X x) x₀ (fun x => α x)
              (fun _ : Fin 1 => j) -
            ∑ k : CoordinateIdx (𝕜 := 𝕜) E,
              christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
                (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
                x₀ (X x₀) j k *
                coordComponent0SAt (I := I) (α x₀) (fun _ : Fin 1 => k)) := by
  classical
  rw [tensor0S_one_eval_coordFrame_sum (I := I)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [nabla0SFun_one_eval_coordFrame (I := I) cov X α x₀ hderiv j]










theorem nabla0SFun_one_eval_of_coordFrame_product
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (Z : (x : M) -> TangentSpace I x)
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1)
    (x₀ : M) (hderiv : ModelDerivEqCoordDeriv0SAt (I := I) X x₀ (fun x => α x))
    (z dz : CoordinateIdx (𝕜 := 𝕜) E -> 𝕜)
    (hz : ∀ j : CoordinateIdx (𝕜 := 𝕜) E,
      z j = (coordinateFrameAt_toBasis (I := I) x₀).coord j (Z x₀))
    (hpair :
      extDerivFun (I := I) (fun y : M => α y (fun _ : Fin 1 => Z y)) x₀ (X x₀) =
        ∑ j : CoordinateIdx (𝕜 := 𝕜) E,
          (dz j * coordComponent0SAt (I := I) (α x₀) (fun _ : Fin 1 => j) +
            z j *
              coordDeriv0SAt (I := I) (fun x => X x) x₀ (fun x => α x)
                (fun _ : Fin 1 => j)))
    (hcovZ :
      α x₀ (fun _ : Fin 1 => (cov (fun y : M => Z y) x₀) (X x₀)) =
        ∑ j : CoordinateIdx (𝕜 := 𝕜) E,
          (dz j * coordComponent0SAt (I := I) (α x₀) (fun _ : Fin 1 => j) +
            z j *
              (∑ k : CoordinateIdx (𝕜 := 𝕜) E,
                christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
                  (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
                  x₀ (X x₀) j k *
                  coordComponent0SAt (I := I) (α x₀) (fun _ : Fin 1 => k)))) :
    (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      1 cov X α x₀) (fun _ : Fin 1 => Z x₀) =
      extDerivFun (I := I) (fun y : M => α y (fun _ : Fin 1 => Z y)) x₀ (X x₀) -
        α x₀ (fun _ : Fin 1 => (cov (fun y : M => Z y) x₀) (X x₀)) := by
  classical
  rw [nabla0SFun_one_eval_coordFrame_expanded (I := I) cov X α x₀ hderiv (Z x₀)]
  rw [hpair, hcovZ]
  simp_rw [← hz]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  simp_rw [Finset.sum_add_distrib]
  ring



theorem nabla0SFun_one_eval_of_coordFrame_product_rule
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (Z : (x : M) -> TangentSpace I x)
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1)
    (x₀ : M) (hderiv : ModelDerivEqCoordDeriv0SAt (I := I) X x₀ (fun x => α x))
    (z dz : CoordinateIdx (𝕜 := 𝕜) E -> 𝕜)
    (hz : ∀ j : CoordinateIdx (𝕜 := 𝕜) E,
      z j = (coordinateFrameAt_toBasis (I := I) x₀).coord j (Z x₀))
    (hdz : ∀ j : CoordinateIdx (𝕜 := 𝕜) E,
      dz j =
        extDerivFun (I := I)
          (fun y : M =>
            (coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff j y (Z y))
          x₀ (X x₀))
    (hdiff_z : ∀ j : CoordinateIdx (𝕜 := 𝕜) E,
      MDifferentiableAt I 𝓘(𝕜, 𝕜)
        (fun y : M =>
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff j y (Z y)) x₀)
    (hdiff_α : ∀ j : CoordinateIdx (𝕜 := 𝕜) E,
      MDifferentiableAt I 𝓘(𝕜, 𝕜)
        (fun y : M => α y (fun _ : Fin 1 => coordinateFrameAt (I := I) x₀ j y)) x₀)
    (hcovZ :
      α x₀ (fun _ : Fin 1 => (cov (fun y : M => Z y) x₀) (X x₀)) =
        ∑ j : CoordinateIdx (𝕜 := 𝕜) E,
          (dz j * coordComponent0SAt (I := I) (α x₀) (fun _ : Fin 1 => j) +
            z j *
              (∑ k : CoordinateIdx (𝕜 := 𝕜) E,
                christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
                  (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
                  x₀ (X x₀) j k *
                  coordComponent0SAt (I := I) (α x₀) (fun _ : Fin 1 => k)))) :
    (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      1 cov X α x₀) (fun _ : Fin 1 => Z x₀) =
      extDerivFun (I := I) (fun y : M => α y (fun _ : Fin 1 => Z y)) x₀ (X x₀) -
        α x₀ (fun _ : Fin 1 => (cov (fun y : M => Z y) x₀) (X x₀)) := by
  exact nabla0SFun_one_eval_of_coordFrame_product
    (I := I) cov X Z α x₀ hderiv z dz hz
    (oneForm_pair_coordFrame_product_rule
      (I := I) X Z α x₀ z dz hz hdz hdiff_z hdiff_α)
    hcovZ





theorem nabla0SFun_one_eval_of_coordFrame_product_rules
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (Z : (x : M) -> TangentSpace I x)
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1)
    (x₀ : M) (hderiv : ModelDerivEqCoordDeriv0SAt (I := I) X x₀ (fun x => α x))
    (z dz : CoordinateIdx (𝕜 := 𝕜) E -> 𝕜)
    (hz : ∀ j : CoordinateIdx (𝕜 := 𝕜) E,
      z j = (coordinateFrameAt_toBasis (I := I) x₀).coord j (Z x₀))
    (hdz : ∀ j : CoordinateIdx (𝕜 := 𝕜) E,
      dz j =
        extDerivFun (I := I)
          (fun y : M =>
            (coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff j y (Z y))
          x₀ (X x₀))
    (hdiff_z : ∀ j : CoordinateIdx (𝕜 := 𝕜) E,
      MDifferentiableAt I 𝓘(𝕜, 𝕜)
        (fun y : M =>
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff j y (Z y)) x₀)
    (hdiff_α : ∀ j : CoordinateIdx (𝕜 := 𝕜) E,
      MDifferentiableAt I 𝓘(𝕜, 𝕜)
        (fun y : M => α y (fun _ : Fin 1 => coordinateFrameAt (I := I) x₀ j y)) x₀)
    (hZ_diff : MDiffAt (T% Z) x₀) :
    (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      1 cov X α x₀) (fun _ : Fin 1 => Z x₀) =
      extDerivFun (I := I) (fun y : M => α y (fun _ : Fin 1 => Z y)) x₀ (X x₀) -
        α x₀ (fun _ : Fin 1 => (cov (fun y : M => Z y) x₀) (X x₀)) := by
  exact nabla0SFun_one_eval_of_coordFrame_product_rule
    (I := I) cov X Z α x₀ hderiv z dz hz hdz hdiff_z hdiff_α
    (oneForm_covariantDerivative_coordFrame_product_rule
      (I := I) cov X Z α x₀ z dz hz hdz hdiff_z hZ_diff)







theorem nabla0SFun_one_eval_coordFrame_moving
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X Z : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1)
    (x₀ : M) (hderiv : ModelDerivEqCoordDeriv0SAt (I := I) X x₀ (fun x => α x))
    (hdiff_z : ∀ j : CoordinateIdx (𝕜 := 𝕜) E,
      MDifferentiableAt I 𝓘(𝕜, 𝕜)
        (fun y : M =>
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff j y (Z y)) x₀)
    (hdiff_α : ∀ j : CoordinateIdx (𝕜 := 𝕜) E,
      MDifferentiableAt I 𝓘(𝕜, 𝕜)
        (fun y : M => α y (fun _ : Fin 1 => coordinateFrameAt (I := I) x₀ j y)) x₀) :
    (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      1 cov X α x₀) (fun _ : Fin 1 => Z x₀) =
      extDerivFun (I := I) (fun y : M => α y (fun _ : Fin 1 => Z y)) x₀ (X x₀) -
        α x₀ (fun _ : Fin 1 => (cov (fun y : M => Z y) x₀) (X x₀)) := by
  let z : CoordinateIdx (𝕜 := 𝕜) E -> 𝕜 :=
    fun j => (coordinateFrameAt_toBasis (I := I) x₀).coord j (Z x₀)
  let dz : CoordinateIdx (𝕜 := 𝕜) E -> 𝕜 :=
    fun j =>
      extDerivFun (I := I)
        (fun y : M =>
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff j y (Z y))
        x₀ (X x₀)
  exact nabla0SFun_one_eval_of_coordFrame_product_rules
    (I := I) cov X Z α x₀ hderiv z dz (by intro j; rfl) (by intro j; rfl)
    hdiff_z hdiff_α
    (Z.contMDiff.contMDiffAt.mdifferentiableAt (by simp))







theorem nabla0SFun_one_eval_coordFrame_moving_raw
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (Z : (x : M) -> TangentSpace I x)
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1)
    (x₀ : M) (hderiv : ModelDerivEqCoordDeriv0SAt (I := I) X x₀ (fun x => α x))
    (hdiff_z : ∀ j : CoordinateIdx (𝕜 := 𝕜) E,
      MDifferentiableAt I 𝓘(𝕜, 𝕜)
        (fun y : M =>
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff j y (Z y)) x₀)
    (hdiff_α : ∀ j : CoordinateIdx (𝕜 := 𝕜) E,
      MDifferentiableAt I 𝓘(𝕜, 𝕜)
        (fun y : M => α y (fun _ : Fin 1 => coordinateFrameAt (I := I) x₀ j y)) x₀)
    (hZ_diff : MDiffAt (T% Z) x₀) :
    (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      1 cov X α x₀) (fun _ : Fin 1 => Z x₀) =
      extDerivFun (I := I) (fun y : M => α y (fun _ : Fin 1 => Z y)) x₀ (X x₀) -
        α x₀ (fun _ : Fin 1 => (cov Z x₀) (X x₀)) := by
  let z : CoordinateIdx (𝕜 := 𝕜) E -> 𝕜 :=
    fun j => (coordinateFrameAt_toBasis (I := I) x₀).coord j (Z x₀)
  let dz : CoordinateIdx (𝕜 := 𝕜) E -> 𝕜 :=
    fun j =>
      extDerivFun (I := I)
        (fun y : M =>
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff j y (Z y))
        x₀ (X x₀)
  exact nabla0SFun_one_eval_of_coordFrame_product_rules
    (I := I) cov X Z α x₀ hderiv z dz (by intro j; rfl) (by intro j; rfl)
    hdiff_z hdiff_α hZ_diff
end DifferentialGeometry.Tensor.Coordinates
