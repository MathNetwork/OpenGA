import OpenGALib.Riemannian.TensorBundle.Defs

/-!
# Riemannian (r,s)-tensor bundle — fiber-to-model coercion algebra

Engineering scaffolding for `Tensor/Defs.lean`'s tensor bundles: the
forward / inverse coercions between the dependent fiber types
(`Tensor0SSpace s I x`, `TensorRSSpace r s I x`) and their model fibers
(`Tensor0SModel s 𝕜 E`, `TensorRSModel r s 𝕜 E`), together with the
algebra simp lemmas making the coercion a `→L[𝕜]` and an
`L`-isomorphism.

These coercions are not used by the bundle structure instances (fiber /
vector / smooth) in `Defs.lean`; they live here as a separate utility
module so consumers that need to manipulate fiber elements via their
model representations can `import` this file directly.
-/

namespace Tensor0SBundle
noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Set IsManifold ContinuousLinearMap

open scoped Manifold Topology Bundle ContDiff BigOperators

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M]

/-!
## Coercion to Model Fiber — (0,s) tensors

The continuous linear equivalence `tensor0SSpace_continuousLinearEquiv` identifies each fiber
`Tensor0SSpace s I x` with `ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜`.  We package
this as `Tensor0SSpace.toModel` (forward direction) and `Tensor0SSpace.ofModel`
(its inverse), together with linearity, continuity, and invertibility lemmas.
-/

namespace Tensor0SSpace

/-- **Eng.** Coerce a `Tensor0SSpace` fiber element to the model fiber.
This is the forward direction of `tensor0SSpace_continuousLinearEquiv`. -/
def toModel {s : ℕ} {x : M} (T : Tensor0SSpace s I x) :
    ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜 :=
  tensor0SSpace_continuousLinearEquiv s x T

/-- **Eng.** `Tensor0SSpace.toModel` as a bundled `ContinuousLinearMap`. -/
def toModelL (s : ℕ) (x : M) :
    Tensor0SSpace s I x →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜 :=
  (tensor0SSpace_continuousLinearEquiv s x).toContinuousLinearMap

/-- **Eng.** Construct a `Tensor0SSpace` fiber element from a model fiber element.
This is the inverse of `Tensor0SSpace.toModel`. -/
def ofModel {s : ℕ} {x : M}
    (f : ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜) :
    Tensor0SSpace s I x :=
  (tensor0SSpace_continuousLinearEquiv s x).symm f

set_option linter.unusedSectionVars false in
@[simp]
theorem toModelL_apply {s : ℕ} {x : M} (T : Tensor0SSpace s I x) :
    toModelL s x T = toModel T := rfl

omit [FiniteDimensional 𝕜 E] in
@[simp]
theorem toModel_add {s : ℕ} {x : M} (T₁ T₂ : Tensor0SSpace s I x) :
    toModel (T₁ + T₂) = toModel T₁ + toModel T₂ :=
  map_add (tensor0SSpace_continuousLinearEquiv s x) T₁ T₂

@[simp]
theorem toModel_smul {s : ℕ} {x : M} (c : 𝕜) (T : Tensor0SSpace s I x) :
    toModel (c • T) = c • toModel T :=
  map_smul (tensor0SSpace_continuousLinearEquiv s x) c T

@[simp]
theorem toModel_zero {s : ℕ} {x : M} :
    toModel (0 : Tensor0SSpace s I x) = 0 :=
  map_zero (tensor0SSpace_continuousLinearEquiv s x)

@[simp]
theorem toModel_neg {s : ℕ} {x : M} (T : Tensor0SSpace s I x) :
    toModel (-T) = -toModel T :=
  map_neg (tensor0SSpace_continuousLinearEquiv s x) T

@[simp]
theorem toModel_sub {s : ℕ} {x : M} (T₁ T₂ : Tensor0SSpace s I x) :
    toModel (T₁ - T₂) = toModel T₁ - toModel T₂ :=
  map_sub (tensor0SSpace_continuousLinearEquiv s x) T₁ T₂

omit [FiniteDimensional 𝕜 E] in
@[simp]
theorem ofModel_toModel {s : ℕ} {x : M} (T : Tensor0SSpace s I x) :
    ofModel (toModel T) = T :=
  (tensor0SSpace_continuousLinearEquiv s x).symm_apply_apply T

set_option linter.unusedSectionVars false in
@[simp]
theorem toModel_ofModel {s : ℕ} {x : M}
    (f : ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜) :
    toModel (ofModel (I := I) (x := x) f) = f :=
  (tensor0SSpace_continuousLinearEquiv s x).apply_symm_apply f

omit [FiniteDimensional 𝕜 E] in
theorem toModel_continuous {s : ℕ} {x : M} :
    Continuous (fun T : Tensor0SSpace s I x => toModel T) :=
  (tensor0SSpace_continuousLinearEquiv s x).continuous_toFun

omit [FiniteDimensional 𝕜 E] in
theorem toModel_injective {s : ℕ} {x : M} :
    Function.Injective (fun T : Tensor0SSpace s I x => toModel T) :=
  (tensor0SSpace_continuousLinearEquiv s x).injective

omit [FiniteDimensional 𝕜 E] in
theorem toModel_surjective {s : ℕ} {x : M} :
    Function.Surjective (fun T : Tensor0SSpace s I x => toModel T) :=
  (tensor0SSpace_continuousLinearEquiv s x).surjective

omit [FiniteDimensional 𝕜 E] in
theorem toModel_bijective {s : ℕ} {x : M} :
    Function.Bijective (fun T : Tensor0SSpace s I x => toModel T) :=
  (tensor0SSpace_continuousLinearEquiv s x).bijective

end Tensor0SSpace

/-!
## Coercion to Model Fiber — (r,s) tensors

The continuous linear equivalence `tensorRSSpace_continuousLinearEquiv` identifies each fiber
`TensorRSSpace r s I x` with the model fiber `TensorRSModel r s 𝕜 E`. We package this as
`TensorRSSpace.toModel` (forward direction) and `TensorRSSpace.ofModel` (its inverse),
together with linearity, continuity, and invertibility lemmas.
-/

namespace TensorRSSpace

/-- **Eng.** Coerce a `TensorRSSpace` fiber element to the model fiber `TensorRSModel r s 𝕜 E`.
This is the forward direction of `tensorRSSpace_continuousLinearEquiv`. -/
def toModel {r s : ℕ} {x : M} (T : TensorRSSpace r s I x) :
    TensorRSModel r s 𝕜 E :=
  tensorRSSpace_continuousLinearEquiv (I := I) r s x T

/-- **Eng.** `TensorRSSpace.toModel` as a bundled `ContinuousLinearMap`. -/
def toModelL (r s : ℕ) (x : M) :
    TensorRSSpace r s I x →L[𝕜] TensorRSModel r s 𝕜 E :=
  (tensorRSSpace_continuousLinearEquiv (I := I) r s x).toContinuousLinearMap

/-- **Eng.** Construct a `TensorRSSpace` fiber element from a model fiber element.
This is the inverse of `TensorRSSpace.toModel`. -/
def ofModel {r s : ℕ} {x : M} (f : TensorRSModel r s 𝕜 E) :
    TensorRSSpace r s I x :=
  (tensorRSSpace_continuousLinearEquiv (I := I) r s x).symm f

set_option linter.unusedSectionVars false in
@[simp]
theorem toModelL_apply {r s : ℕ} {x : M} (T : TensorRSSpace r s I x) :
    (toModelL (I := I) r s x).toFun T = toModel T := rfl

@[simp]
theorem toModel_add {r s : ℕ} {x : M} (T₁ T₂ : TensorRSSpace r s I x) :
    toModel (T₁ + T₂) = toModel T₁ + toModel T₂ :=
  map_add (tensorRSSpace_continuousLinearEquiv (I := I) r s x) T₁ T₂

@[simp]
theorem toModel_smul {r s : ℕ} {x : M} (c : 𝕜) (T : TensorRSSpace r s I x) :
    toModel (c • T) = c • toModel T :=
  map_smul (tensorRSSpace_continuousLinearEquiv (I := I) r s x) c T

@[simp]
theorem toModel_zero {r s : ℕ} {x : M} :
    toModel (0 : TensorRSSpace r s I x) = 0 :=
  (tensorRSSpace_continuousLinearEquiv (I := I) r s x).toLinearEquiv.map_zero

@[simp]
theorem toModel_neg {r s : ℕ} {x : M} (T : TensorRSSpace r s I x) :
    toModel (-T) = -toModel T :=
  (tensorRSSpace_continuousLinearEquiv (I := I) r s x).toLinearEquiv.map_neg T

@[simp]
theorem toModel_sub {r s : ℕ} {x : M} (T₁ T₂ : TensorRSSpace r s I x) :
    toModel (T₁ - T₂) = toModel T₁ - toModel T₂ :=
  (tensorRSSpace_continuousLinearEquiv (I := I) r s x).toLinearEquiv.map_sub T₁ T₂

@[simp]
theorem ofModel_toModel {r s : ℕ} {x : M} (T : TensorRSSpace r s I x) :
    ofModel (toModel T) = T :=
  (tensorRSSpace_continuousLinearEquiv (I := I) r s x).symm_apply_apply T

set_option linter.unusedSectionVars false in
@[simp]
theorem toModel_ofModel {r s : ℕ} {x : M} (f : TensorRSModel r s 𝕜 E) :
    toModel (ofModel (I := I) (x := x) f) = f :=
  (tensorRSSpace_continuousLinearEquiv (I := I) r s x).apply_symm_apply f

theorem toModel_continuous {r s : ℕ} {x : M} :
    Continuous (fun T : TensorRSSpace r s I x => toModel T) :=
  (tensorRSSpace_continuousLinearEquiv (I := I) r s x).continuous_toFun

theorem toModel_injective {r s : ℕ} {x : M} :
    Function.Injective (fun T : TensorRSSpace r s I x => toModel T) :=
  (tensorRSSpace_continuousLinearEquiv (I := I) r s x).injective

theorem toModel_surjective {r s : ℕ} {x : M} :
    Function.Surjective (fun T : TensorRSSpace r s I x => toModel T) :=
  (tensorRSSpace_continuousLinearEquiv (I := I) r s x).surjective

theorem toModel_bijective {r s : ℕ} {x : M} :
    Function.Bijective (fun T : TensorRSSpace r s I x => toModel T) :=
  (tensorRSSpace_continuousLinearEquiv (I := I) r s x).bijective

end TensorRSSpace

end
end Tensor0SBundle
