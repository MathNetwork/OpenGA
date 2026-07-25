


import DifferentialGeometry.Tensor.Multilinear.Bundle

noncomputable section

open Bundle Set

open scoped Manifold Topology Bundle ContDiff BigOperators

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

noncomputable def continuousMultilinearMap_curryEquiv (r r' : ℕ) :
    ContinuousMultilinearMap 𝕜 (fun _ : Fin (r + r') => F) 𝕜 ≃ₗᵢ[𝕜]
    ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F)
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r' => F) 𝕜) :=
  (ContinuousMultilinearMap.domDomCongrₗᵢ 𝕜 F 𝕜 finSumFinEquiv.symm).trans
    (ContinuousMultilinearMap.currySumEquiv 𝕜 (Fin r) (Fin r') F 𝕜)

noncomputable def continuousMultilinearMap_curryLeft (r r' : ℕ) :
    ContinuousMultilinearMap 𝕜 (fun _ : Fin (r + r') => F) 𝕜 →L[𝕜]
    ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F)
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r' => F) 𝕜) :=
  (continuousMultilinearMap_curryEquiv r r' (𝕜 := 𝕜) (F := F)).toContinuousLinearEquiv

noncomputable def continuousMultilinearMap_uncurryLeft (r r' : ℕ) :
    ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F)
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r' => F) 𝕜) →L[𝕜]
    ContinuousMultilinearMap 𝕜 (fun _ : Fin (r + r') => F) 𝕜 :=
  (continuousMultilinearMap_curryEquiv r r' (𝕜 := 𝕜) (F := F)).symm.toContinuousLinearEquiv

@[simp]
theorem continuousMultilinearMap_curryLeft_uncurryLeft (r r' : ℕ)
    (g : ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F)
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r' => F) 𝕜)) :
    (continuousMultilinearMap_curryLeft (𝕜 := 𝕜) (F := F) r r')
      ((continuousMultilinearMap_uncurryLeft (𝕜 := 𝕜) (F := F) r r') g) = g := by
  simp [continuousMultilinearMap_curryLeft, continuousMultilinearMap_uncurryLeft]

@[simp]
theorem continuousMultilinearMap_uncurryLeft_curryLeft (r r' : ℕ)
    (f : ContinuousMultilinearMap 𝕜 (fun _ : Fin (r + r') => F) 𝕜) :
    (continuousMultilinearMap_uncurryLeft (𝕜 := 𝕜) (F := F) r r')
      ((continuousMultilinearMap_curryLeft (𝕜 := 𝕜) (F := F) r r') f) = f := by
  simp only [continuousMultilinearMap_curryLeft, continuousMultilinearMap_uncurryLeft]
  exact (continuousMultilinearMap_curryEquiv r r').toContinuousLinearEquiv.symm_apply_apply f

end
