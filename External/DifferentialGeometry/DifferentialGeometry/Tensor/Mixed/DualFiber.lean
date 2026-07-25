


import DifferentialGeometry.Tensor.Mixed.Fiber
import DifferentialGeometry.Tensor.Multilinear.Dual
import Mathlib.LinearAlgebra.Contraction

noncomputable section

open Bundle TensorProduct

namespace ContinuousMultilinearMap

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable (V : Type*) [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]
variable (W : Type*) [NormedAddCommGroup W] [NormedSpace 𝕜 W] [FiniteDimensional 𝕜 W]

noncomputable def homEquivCDualTensor :
    (V →L[𝕜] W) ≃ₗ[𝕜] ((V →L[𝕜] 𝕜) ⊗[𝕜] W) := by
  let e1 : (V →L[𝕜] W) ≃ₗ[𝕜] (V →ₗ[𝕜] W) := LinearMap.toContinuousLinearMap.symm
  let e2 : (V →ₗ[𝕜] W) ≃ₗ[𝕜] (Module.Dual 𝕜 V ⊗[𝕜] W) :=
    (dualTensorHomEquiv 𝕜 V W).symm
  let cdualEquiv : (V →L[𝕜] 𝕜) ≃ₗ[𝕜] Module.Dual 𝕜 V :=
    LinearMap.toContinuousLinearMap.symm
  let e3 : (Module.Dual 𝕜 V ⊗[𝕜] W) ≃ₗ[𝕜] ((V →L[𝕜] 𝕜) ⊗[𝕜] W) :=
    TensorProduct.congr cdualEquiv.symm (LinearEquiv.refl 𝕜 W)
  exact e1.trans (e2.trans e3)

noncomputable def multilinearHomEquivDualMultilinearTensor
    (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    (r s : ℕ) :
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜]
       ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜) ≃ₗ[𝕜]
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => (F →L[𝕜] 𝕜)) 𝕜 ⊗[𝕜]
       ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜) :=
  haveI : FiniteDimensional 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜) :=
    continuousMultilinearMap_finiteDimensional r
  haveI : FiniteDimensional 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜) :=
    continuousMultilinearMap_finiteDimensional s
  (homEquivCDualTensor 𝕜
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜)
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)).trans
    (TensorProduct.congr
      (dualMultilinearEquivMultilinearOfDual 𝕜 F r)
      (LinearEquiv.refl 𝕜 _))

end ContinuousMultilinearMap

namespace Bundle.continuousMultilinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {B : Type*} [TopologicalSpace B]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
variable {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
variable [TopologicalSpace (TotalSpace F E)]
variable [FiberBundle F E] [VectorBundle 𝕜 F E]

noncomputable def multilinearHomTensorEquivAt (r s : ℕ) (x : B) :
    ((ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E x) 𝕜) →L[𝕜]
       ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E x) 𝕜) ≃ₗ[𝕜]
    ((ContinuousMultilinearMap 𝕜 (fun _ : Fin r => (E x →L[𝕜] 𝕜)) 𝕜) ⊗[𝕜]
       ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E x) 𝕜) := by
  haveI : FiniteDimensional 𝕜 (E x) := VectorBundle.finiteDimensional 𝕜 F E x
  haveI : FiniteDimensional 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E x) 𝕜) :=
    continuousMultilinearMap_finiteDimensional r
  haveI : FiniteDimensional 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E x) 𝕜) :=
    continuousMultilinearMap_finiteDimensional s
  let e1 : ((ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E x) 𝕜) →L[𝕜]
            ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E x) 𝕜) ≃ₗ[𝕜]
        ((ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E x) 𝕜) →L[𝕜] 𝕜) ⊗[𝕜]
          ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E x) 𝕜 :=
    ContinuousMultilinearMap.homEquivCDualTensor 𝕜
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E x) 𝕜)
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E x) 𝕜)
  let e2 : ((ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E x) 𝕜) →L[𝕜] 𝕜) ⊗[𝕜]
            ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E x) 𝕜 ≃ₗ[𝕜]
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => (E x →L[𝕜] 𝕜)) 𝕜) ⊗[𝕜]
          ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E x) 𝕜 :=
    TensorProduct.congr
      (dualMultilinearLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) r x)
      (LinearEquiv.refl 𝕜 _)
  exact e1.trans e2

noncomputable def dualTensorMultilinearUntrivializeAt (r s : ℕ) (x : B) :
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => (F →L[𝕜] 𝕜)) 𝕜 ⊗[𝕜]
       ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜) ≃ₗ[𝕜]
    (Bundle.continuousMultilinearMap 𝕜 r (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x ⊗[𝕜]
       Bundle.continuousMultilinearMap 𝕜 s F E x) :=
  TensorProduct.congr
    (continuousLinearEquivAt (𝕜 := 𝕜) (F := F →L[𝕜] 𝕜)
      (E := Bundle.dual 𝕜 E) r x).symm.toLinearEquiv
    (continuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) s x).symm.toLinearEquiv

set_option backward.isDefEq.respectTransparency false in

noncomputable def multilinearHomTensorEquivAt_bundle (r s : ℕ) (x : B) :
    (Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
       Bundle.continuousMultilinearMap 𝕜 s F E x) ≃ₗ[𝕜]
    ((Bundle.continuousMultilinearMap 𝕜 r (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) x) ⊗[𝕜]
       Bundle.continuousMultilinearMap 𝕜 s F E x) :=
  ((mixedContinuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) r s x).toLinearEquiv.trans
    (ContinuousMultilinearMap.multilinearHomEquivDualMultilinearTensor 𝕜 F r s)).trans
    (dualTensorMultilinearUntrivializeAt (𝕜 := 𝕜) (F := F) (E := E) r s x)

end Bundle.continuousMultilinearMap

end
