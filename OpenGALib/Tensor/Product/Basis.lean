import OpenGALib.Tensor.Product.Bundle
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Basis for the tensor product of finite-dimensional spaces (OpenGALib)
# Basis for the Tensor Product of Finite-Dimensional Spaces

If `b₁` is a basis for `F₁` indexed by `Fin d₁` and `b₂` is a basis for `F₂` indexed
by `Fin d₂`, then the family `(i, j) ↦ b₁ i ⊗ₜ b₂ j` is a basis for `F₁ ⊗[𝕜] F₂`,
indexed by `Fin d₁ × Fin d₂`.

## Main Definitions

* `tensorProduct_finiteDimensional` : `F₁ ⊗[𝕜] F₂` is finite-dimensional.
* `tensorProduct_basis` : the explicit basis `(i, j) ↦ b₁ i ⊗ₜ b₂ j`.

## Main Results

* `tensorProduct_basis_apply` : `tensorProduct_basis b₁ b₂ (i, j) = b₁ i ⊗ₜ b₂ j`.
* `tensorProduct_basis_repr_tmul` : `repr (v ⊗ₜ w) (i, j) = b₁.repr v i * b₂.repr w j`.
* `finrank_tensorProduct'` : `finrank (F₁ ⊗ F₂) = finrank F₁ * finrank F₂`.

## Tags

tensor product, basis, finite-dimensional
-/

noncomputable section

open scoped TensorProduct

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
variable {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]

/-!
## Finite-dimensionality
-/

/-- The tensor product of two finite-dimensional normed spaces is finite-dimensional. -/
noncomputable instance tensorProduct_finiteDimensional :
    FiniteDimensional 𝕜 (F₁ ⊗[𝕜] F₂) :=
  Module.Finite.tensorProduct 𝕜 F₁ F₂

/-!
## Dimension
-/

set_option linter.unusedSectionVars false in
/-- The dimension of `F₁ ⊗[𝕜] F₂` equals the product of the dimensions of the factors. -/
theorem finrank_tensorProduct' :
    Module.finrank 𝕜 (F₁ ⊗[𝕜] F₂) = Module.finrank 𝕜 F₁ * Module.finrank 𝕜 F₂ :=
  Module.finrank_tensorProduct

/-!
## Explicit basis construction
-/

/-- If `b₁` is a basis for `F₁` indexed by `Fin d₁` and `b₂` is a basis for `F₂` indexed by
`Fin d₂`, then `(i, j) ↦ b₁ i ⊗ₜ b₂ j` is a basis for `F₁ ⊗[𝕜] F₂` indexed by
`Fin d₁ × Fin d₂`. -/
noncomputable def tensorProduct_basis {d₁ d₂ : ℕ}
    (b₁ : Module.Basis (Fin d₁) 𝕜 F₁) (b₂ : Module.Basis (Fin d₂) 𝕜 F₂) :
    Module.Basis (Fin d₁ × Fin d₂) 𝕜 (F₁ ⊗[𝕜] F₂) :=
  b₁.tensorProduct b₂

set_option linter.unusedSectionVars false in
/-- The basis element at `(i, j)` is the pure tensor `b₁ i ⊗ₜ b₂ j`. -/
@[simp]
theorem tensorProduct_basis_apply {d₁ d₂ : ℕ}
    (b₁ : Module.Basis (Fin d₁) 𝕜 F₁) (b₂ : Module.Basis (Fin d₂) 𝕜 F₂)
    (i : Fin d₁) (j : Fin d₂) :
    tensorProduct_basis b₁ b₂ (i, j) = b₁ i ⊗ₜ b₂ j :=
  Module.Basis.tensorProduct_apply b₁ b₂ i j

set_option linter.unusedSectionVars false in
/-- Variant of `tensorProduct_basis_apply` taking a pair. -/
theorem tensorProduct_basis_apply' {d₁ d₂ : ℕ}
    (b₁ : Module.Basis (Fin d₁) 𝕜 F₁) (b₂ : Module.Basis (Fin d₂) 𝕜 F₂)
    (p : Fin d₁ × Fin d₂) :
    tensorProduct_basis b₁ b₂ p = b₁ p.1 ⊗ₜ b₂ p.2 :=
  Module.Basis.tensorProduct_apply' b₁ b₂ p

set_option linter.unusedSectionVars false in
/-- The representation of a pure tensor `v ⊗ₜ w` in the tensor product basis decomposes as
a product of the individual representations:
`repr (v ⊗ₜ w) (i, j) = (b₁.repr v i) * (b₂.repr w j)`. -/
theorem tensorProduct_basis_repr_tmul {d₁ d₂ : ℕ}
    (b₁ : Module.Basis (Fin d₁) 𝕜 F₁) (b₂ : Module.Basis (Fin d₂) 𝕜 F₂)
    (v : F₁) (w : F₂) (i : Fin d₁) (j : Fin d₂) :
    (tensorProduct_basis b₁ b₂).repr (v ⊗ₜ w) (i, j) = b₁.repr v i * b₂.repr w j := by
  change (b₁.tensorProduct b₂).repr (v ⊗ₜ w) (i, j) = _
  rw [Module.Basis.tensorProduct_repr_tmul_apply, smul_eq_mul, mul_comm]

/-!
## Smooth section characterization via coordinates

A section of the tensor product bundle is smooth if and only if all its basis
coordinate functions (with respect to the tensor product basis) are smooth.
-/

section smooth

open Bundle Set

open scoped Manifold Topology Bundle

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
variable {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]
variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
variable (E₁ : B → Type*) [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
variable (E₂ : B → Type*) [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
variable [∀ x, ContinuousAdd (E₁ x)] [∀ x, ContinuousSMul 𝕜 (E₁ x)]
variable [∀ x, ContinuousAdd (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]
variable (n : WithTop ℕ∞)
variable [ContMDiffVectorBundle n F₁ E₁ IB] [ContMDiffVectorBundle n F₂ E₂ IB]

set_option linter.unusedSectionVars false in
/-- A section of the tensor product bundle is `C^n` if and only if, when read through the
trivialization at each point, all basis coordinate functions are `C^n`.

More precisely, `f` is a `C^n` section of `E₁ ⊗ E₂` iff for every `x₀ : B` and
`p : Fin d₁ × Fin d₂`, the function
`x ↦ (tensorProduct_basis b₁ b₂).repr (triv x₀ ⟨x, f x⟩).2 p` is `C^n` at `x₀`. -/
theorem contMDiff_tensorProductSection_iff_coord
    {d₁ d₂ : ℕ}
    (b₁ : Module.Basis (Fin d₁) 𝕜 F₁)
    (b₂ : Module.Basis (Fin d₂) 𝕜 F₂)
    (f : ∀ x : B, E₁ x ⊗[𝕜] E₂ x) :
    letI := Bundle.TensorProduct.tensorFiberTopology 𝕜 F₁ F₂ E₁ E₂
    letI := Bundle.TensorProduct.fiberBundle
      (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)
    ContMDiff IB (IB.prod 𝓘(𝕜, F₁ ⊗[𝕜] F₂)) n
      (fun x => TotalSpace.mk' (F₁ ⊗[𝕜] F₂) x (f x)) ↔
    ∀ p : Fin d₁ × Fin d₂, ∀ x₀ : B,
      ContMDiffAt IB 𝓘(𝕜, 𝕜) n
        (fun x => (tensorProduct_basis b₁ b₂).repr
          (trivializationAt (F₁ ⊗[𝕜] F₂)
            (fun x => E₁ x ⊗[𝕜] E₂ x) x₀ ⟨x, f x⟩).2 p) x₀ := by
  letI := Bundle.TensorProduct.tensorFiberTopology 𝕜 F₁ F₂ E₁ E₂
  letI := Bundle.TensorProduct.fiberBundle
    (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)
  letI : ChartedSpace (ModelProd HB (F₁ ⊗[𝕜] F₂))
      (TotalSpace (F₁ ⊗[𝕜] F₂) (fun x => E₁ x ⊗[𝕜] E₂ x)) :=
    FiberBundle.chartedSpace
  set Bb := tensorProduct_basis b₁ b₂
  constructor
  · -- Smooth section → smooth coordinates
    intro hf p x₀
    have hsec := (contMDiffAt_section x₀).mp hf.contMDiffAt
    exact (LinearMap.toContinuousLinearMap (Bb.coord p)).contMDiffAt.comp x₀ hsec
  · -- Smooth coordinates → smooth section
    intro hcoord x₀
    rw [contMDiffAt_section]
    let g := fun x => (trivializationAt (F₁ ⊗[𝕜] F₂)
        (fun x => E₁ x ⊗[𝕜] E₂ x) x₀ ⟨x, f x⟩).2
    change ContMDiffAt IB 𝓘(𝕜, F₁ ⊗[𝕜] F₂) n g x₀
    rw [show g = fun x => Bb.equivFun.symm (Bb.equivFun (g x)) from
        funext fun x => (Bb.equivFun.symm_apply_apply (g x)).symm]
    exact (Bb.equivFun.symm.toContinuousLinearEquiv.toContinuousLinearMap.contMDiffAt).comp x₀
      (contMDiffAt_pi_space.mpr fun p => hcoord p x₀)

end smooth

end
