


import DifferentialGeometry.Tensor.Mixed.Fiber
import Mathlib.Geometry.Manifold.VectorBundle.Hom

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Set ContinuousLinearMap

open scoped Manifold Topology Bundle ContDiff BigOperators

namespace Bundle.continuousMultilinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {B : Type*} [TopologicalSpace B]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
variable [TopologicalSpace (TotalSpace F E)]
variable [FiberBundle F E] [VectorBundle 𝕜 F E]
variable {r s : ℕ}

noncomputable instance mixedTopology (r s : ℕ) :
    TopologicalSpace (TotalSpace
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜]
       ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
      (fun x : B => Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
                     Bundle.continuousMultilinearMap 𝕜 s F E x)) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id 𝕜)
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜)
    (fun x => Bundle.continuousMultilinearMap 𝕜 r F E x)
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
    (fun x => Bundle.continuousMultilinearMap 𝕜 s F E x)

noncomputable instance mixedFiberBundle (r s : ℕ) :
    @FiberBundle B
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜]
       ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
      _ (by infer_instance : TopologicalSpace _)
      (fun x : B => Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
                     Bundle.continuousMultilinearMap 𝕜 s F E x)
      (mixedTopology r s) _ :=
  Bundle.ContinuousLinearMap.fiberBundle (RingHom.id 𝕜)
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜)
    (fun x => Bundle.continuousMultilinearMap 𝕜 r F E x)
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
    (fun x => Bundle.continuousMultilinearMap 𝕜 s F E x)

noncomputable instance mixedVectorBundle (r s : ℕ) :
    @VectorBundle 𝕜 B
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜]
       ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
      (fun x : B => Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
                     Bundle.continuousMultilinearMap 𝕜 s F E x)
      _
      (fun x => by infer_instance) (fun x => by infer_instance)
      inferInstance inferInstance _
      (mixedTopology r s) _
      (mixedFiberBundle r s) :=
  Bundle.ContinuousLinearMap.vectorBundle (RingHom.id 𝕜)
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜)
    (fun x => Bundle.continuousMultilinearMap 𝕜 r F E x)
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
    (fun x => Bundle.continuousMultilinearMap 𝕜 s F E x)

section smooth

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]
variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
variable {HB : Type*} [TopologicalSpace HB]
variable (IB : ModelWithCorners 𝕜 EB HB)
variable [ChartedSpace HB B]
variable (n : WithTop ℕ∞)
variable [ContMDiffVectorBundle n F E IB]

noncomputable instance mixedSmoothVectorBundle (r s : ℕ) :
    @ContMDiffVectorBundle n 𝕜 B
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜]
       ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
      (fun x : B => Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
                     Bundle.continuousMultilinearMap 𝕜 s F E x)
      _ EB _ _ HB _ IB _ _ _ _ _ _
      (mixedTopology r s) _
      (mixedFiberBundle r s)
      (mixedVectorBundle r s) :=
  ContMDiffVectorBundle.continuousLinearMap

end smooth

end Bundle.continuousMultilinearMap

end
