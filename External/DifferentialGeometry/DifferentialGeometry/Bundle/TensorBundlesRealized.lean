import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Topology.FiberBundle.Basic
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.Algebra.Module.LinearMap
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorField.LieBracket
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Analysis.Calculus.VectorField
import DifferentialGeometry.Tensor.Product.Bundle
import DifferentialGeometry.Tensor.Product.Defs
import DifferentialGeometry.Tensor.Product.Fiber
import DifferentialGeometry.Tensor.Product.HomEquiv
import DifferentialGeometry.Tensor.Product.Pretrivialization

open scoped Topology
open scoped TensorProduct











noncomputable section

open Bundle Set Topology
open scoped Bundle TensorProduct

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]

variable {B : Type*}
variable {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
  (E₁ : B → Type*) [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)]

variable {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]
  (E₂ : B → Type*) [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)]

variable {E₁ E₂}
variable [TopologicalSpace B] (e₁ e₁' : Trivialization F₁ (π F₁ E₁))
  (e₂ e₂' : Trivialization F₂ (π F₂ E₂))



section TensorNorm


variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable (F₁ : Type*) [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
variable (F₂ : Type*) [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]










end TensorNorm


noncomputable def TensorProduct.tmulL :
    F₁ →L[𝕜] F₂ →L[𝕜] (F₁ ⊗[𝕜] F₂) := by
  classical
  let innerLM (v : F₁) : F₂ →ₗ[𝕜] (F₁ ⊗[𝕜] F₂) :=
    TensorProduct.mk 𝕜 F₁ F₂ v
  let innerCLM (v : F₁) : F₂ →L[𝕜] (F₁ ⊗[𝕜] F₂) :=
    (innerLM v).toContinuousLinearMap
  let outerLM : F₁ →ₗ[𝕜] F₂ →L[𝕜] (F₁ ⊗[𝕜] F₂) :=
    { toFun := fun v => innerCLM v
      map_add' := by
        intro v v'
        ext w
        simp [innerCLM, innerLM]
      map_smul' := by
        intro c v
        ext w
        simp [innerCLM, innerLM] }
  exact outerLM.toContinuousLinearMap

@[simp]
theorem TensorProduct.tmulL_apply (v : F₁) (w : F₂) :
    TensorProduct.tmulL (𝕜 := 𝕜) (F₁ := F₁) (F₂ := F₂) v w = v ⊗ₜ[𝕜] w := by
  simp [TensorProduct.tmulL]



section MapL

variable {G₁ G₂ : Type*}
  [NormedAddCommGroup G₁] [NormedSpace 𝕜 G₁] [FiniteDimensional 𝕜 G₁]
  [NormedAddCommGroup G₂] [NormedSpace 𝕜 G₂] [FiniteDimensional 𝕜 G₂]



end MapL


namespace Pretrivialization




variable {e₁ e₁' e₂ e₂'}
variable [∀ x, TopologicalSpace (E₁ x)] [FiberBundle F₁ E₁]
variable [∀ x, TopologicalSpace (E₂ x)] [FiberBundle F₂ E₂]


variable (𝕜 e₁ e₁' e₂ e₂')
variable [e₁.IsLinear 𝕜] [e₁'.IsLinear 𝕜] [e₂.IsLinear 𝕜] [e₂'.IsLinear 𝕜]










end Pretrivialization
section
section TensorFiberTopology

open scoped TensorProduct
open Bundle Set Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {B : Type*} [TopologicalSpace B]
variable {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
variable {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]

variable (E₁ : B → Type*) [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]

variable (E₂ : B → Type*) [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]





end TensorFiberTopology

section

universe u𝕜 uB uF₁ uF₂ uE₁ uE₂
namespace Bundle.TensorProduct

open Bundle Set Topology Pretrivialization
open scoped Manifold Bundle TensorProduct



attribute [instance] TensorFiberTopologies.fiberTop

class TensorBundleCore
    (𝕜 : Type u𝕜) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    (B : Type uB) [TopologicalSpace B]
    (F₁ : Type uF₁) [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
    (F₂ : Type uF₂) [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]
    (E₁ : B → Type uE₁) [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
      [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
      [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
    (E₂ : B → Type uE₂) [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
      [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
      [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
    extends TensorFiberTopologies 𝕜 B F₁ F₂ E₁ E₂ where
  totalSpaceTop :
    TopologicalSpace (TotalSpace (F₁ ⊗[𝕜] F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x))
  fiberBundleInst :
    @FiberBundle
      B
      (F₁ ⊗[𝕜] F₂)
      inferInstance
      inferInstance
      (fun x ↦ E₁ x ⊗[𝕜] E₂ x)
      totalSpaceTop
      toTensorFiberTopologies.fiberTop
  vectorBundleInst :
    letI := totalSpaceTop
    letI := fiberBundleInst
    VectorBundle 𝕜 (F₁ ⊗[𝕜] F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x)

attribute [instance] TensorBundleCore.totalSpaceTop
attribute [instance] TensorBundleCore.fiberBundleInst
attribute [instance] TensorBundleCore.vectorBundleInst
attribute [instance] TensorBundleCore.toTensorFiberTopologies

variable [∀ x, TopologicalSpace (E₁ x)] [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
     [∀ (x : B), ContinuousAdd (E₁ x)] [∀ x, ContinuousSMul 𝕜 (E₁ x)]
variable [∀ x, TopologicalSpace (E₂ x)] [FiberBundle F₂ E₂]
    [VectorBundle 𝕜 F₂ E₂] [∀ (x : B), ContinuousAdd (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]









@[reducible]
noncomputable def totalSpaceTopology :
    TopologicalSpace
      (TotalSpace (F₁ ⊗[𝕜] F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x)) := by
  classical

  letI (x : B) : TopologicalSpace (E₁ x ⊗[𝕜] E₂ x) :=
    Bundle.TensorProduct.tensorFiberTopology
      (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂) x

  exact
    (Bundle.TensorProduct.vectorPrebundle
        (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)).totalSpaceTopology



attribute [local instance] tensorTotalSpaceTop


attribute [local instance] fiberBundle


noncomputable instance tensorBundleCore :
    TensorBundleCore 𝕜 B F₁ F₂ E₁ E₂ where
  toTensorFiberTopologies :=
    tensorFiberTopologies
      (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)
  totalSpaceTop :=
    totalSpaceTopology
      (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)
  fiberBundleInst :=
    fiberBundle
      (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)
  vectorBundleInst := by
    classical
    simp [vectorBundle
          (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)]


variable (e₁ : Trivialization F₁ (π F₁ E₁)) (e₂ : Trivialization F₂ (π F₂ E₂))
variable [he₁ : MemTrivializationAtlas e₁] [he₂ : MemTrivializationAtlas e₂]




@[simp]
theorem _root_.Bundle.Trivialization.baseSet_tensorProduct :
    (e₁.tensorProduct (𝕜 := 𝕜) e₂).baseSet = e₁.baseSet ∩ e₂.baseSet :=
  rfl

theorem _root_.Bundle.Trivialization.tensorProduct_apply
    (p : TotalSpace (F₁ ⊗[𝕜] F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x)) :
    e₁.tensorProduct (𝕜 := 𝕜) e₂ p =
      ⟨p.1, TensorProduct.map
        (e₁.continuousLinearMapAt 𝕜 p.1).toLinearMap
        (e₂.continuousLinearMapAt 𝕜 p.1).toLinearMap p.2⟩ :=
  rfl


theorem tensorProduct_trivializationAt_apply_snd
    (x₀ : B) (p : TotalSpace (F₁ ⊗[𝕜] F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x)) :
    letI : (x : B) → TopologicalSpace (E₁ x ⊗[𝕜] E₂ x) :=
      tensorFiberTop (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)
    (trivializationAt (F₁ ⊗[𝕜] F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x) x₀ p).2 =
      TensorProduct.map
        ((trivializationAt F₁ E₁ x₀).continuousLinearMapAt 𝕜 p.1).toLinearMap
        ((trivializationAt F₂ E₂ x₀).continuousLinearMapAt 𝕜 p.1).toLinearMap
        p.2 := by
  rw [tensorProduct_trivializationAt]
  rfl


def inCoordinates
    (x₀ x : B) (y₀ y : B) (t : E₁ x ⊗[𝕜] E₂ y) : F₁ ⊗[𝕜] F₂ :=
  TensorProduct.map
    ((trivializationAt F₁ E₁ x₀).continuousLinearMapAt 𝕜 x).toLinearMap
    ((trivializationAt F₂ E₂ y₀).continuousLinearMapAt 𝕜 y).toLinearMap
    t

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F₁] [FiniteDimensional 𝕜 F₂]
     [∀ x : B, ContinuousAdd (E₁ x)] [∀ x : B, ContinuousSMul 𝕜 (E₁ x)]
     [∀ x : B, ContinuousAdd (E₂ x)] [∀ x : B, ContinuousSMul 𝕜 (E₂ x)] in
@[simp]
theorem inCoordinates_tmul
    (x₀ x : B) (y₀ y : B) (v : E₁ x) (w : E₂ y) :
    inCoordinates (𝕜 := 𝕜) (F₁ := F₁) (E₁ := E₁) (F₂ := F₂) (E₂ := E₂)
      x₀ x y₀ y (v ⊗ₜ[𝕜] w) =
      ((trivializationAt F₁ E₁ x₀).continuousLinearMapAt 𝕜 x v) ⊗ₜ[𝕜]
        ((trivializationAt F₂ E₂ y₀).continuousLinearMapAt 𝕜 y w) := by
  simp [inCoordinates, TensorProduct.map_tmul]






end Bundle.TensorProduct
