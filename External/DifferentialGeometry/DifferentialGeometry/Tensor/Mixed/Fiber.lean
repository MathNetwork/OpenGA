


import DifferentialGeometry.Tensor.Multilinear.Fiber

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

private theorem mixed_type_eq (r s : ℕ) (x : B) :
    (Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
     Bundle.continuousMultilinearMap 𝕜 s F E x) =
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E x) 𝕜 →L[𝕜]
     ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E x) 𝕜) := by
  unfold Bundle.continuousMultilinearMap
  congr 1 <;> exact topology_eq (𝕜 := 𝕜) (F := F) (E := E) _ x

private def mixed_normedInstances (r s : ℕ) (x : B) :
    Σ' (ng : NormedAddCommGroup
          (Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
           Bundle.continuousMultilinearMap 𝕜 s F E x)),
      @NormedSpace 𝕜
        (Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
         Bundle.continuousMultilinearMap 𝕜 s F E x)
        _ ng.toSeminormedAddCommGroup :=
  (mixed_type_eq (𝕜 := 𝕜) (F := F) (E := E) r s x) ▸ ⟨inferInstance, inferInstance⟩

instance mixed_instNormedAddCommGroup (r s : ℕ) (x : B) :
    NormedAddCommGroup
      (Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
       Bundle.continuousMultilinearMap 𝕜 s F E x) :=
  (mixed_normedInstances (𝕜 := 𝕜) (F := F) (E := E) r s x).1

instance mixed_instNormedSpace (r s : ℕ) (x : B) :
    NormedSpace 𝕜
      (Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
       Bundle.continuousMultilinearMap 𝕜 s F E x) :=
  (mixed_normedInstances (𝕜 := 𝕜) (F := F) (E := E) r s x).2

instance mixed_instContinuousSMul (r s : ℕ) (x : B) :
    ContinuousSMul 𝕜
      (Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
       Bundle.continuousMultilinearMap 𝕜 s F E x) :=
  inferInstanceAs (ContinuousSMul 𝕜
    (Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
     Bundle.continuousMultilinearMap 𝕜 s F E x))

def mixedContinuousLinearEquivAt (r s : ℕ) (x : B) :
    (Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
     Bundle.continuousMultilinearMap 𝕜 s F E x) ≃L[𝕜]
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜]
     ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜) :=
  (continuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) r x).arrowCongr
    (continuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) s x)

def mixedToModel {r s : ℕ} {x : B}
    (T : Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
         Bundle.continuousMultilinearMap 𝕜 s F E x) :
    ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜]
    ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜 :=
  (mixedContinuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) r s x).toContinuousLinearMap T

def mixedToModelL (r s : ℕ) (x : B) :
    (Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
     Bundle.continuousMultilinearMap 𝕜 s F E x) →L[𝕜]
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜]
     ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜) :=
  (mixedContinuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) r s x).toContinuousLinearMap

def mixedOfModel {r s : ℕ} {x : B}
    (f : ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜]
         ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜) :
    Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
    Bundle.continuousMultilinearMap 𝕜 s F E x :=
  (mixedContinuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) r s x).symm.toContinuousLinearMap f

@[simp]
theorem mixedToModelL_apply {r s : ℕ} {x : B}
    (T : Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
         Bundle.continuousMultilinearMap 𝕜 s F E x) :
    (mixedToModelL (𝕜 := 𝕜) (F := F) (E := E) r s x).toFun T = mixedToModel T := rfl

@[simp]
theorem mixedToModel_add {r s : ℕ} {x : B}
    (T₁ T₂ : Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
             Bundle.continuousMultilinearMap 𝕜 s F E x) :
    mixedToModel (𝕜 := 𝕜) (F := F) (E := E) (T₁ + T₂) =
      mixedToModel T₁ + mixedToModel T₂ :=
  map_add (mixedContinuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) r s x).toContinuousLinearMap
    T₁ T₂

@[simp]
theorem mixedToModel_smul {r s : ℕ} {x : B}
    (c : 𝕜) (T : Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
                  Bundle.continuousMultilinearMap 𝕜 s F E x) :
    mixedToModel (𝕜 := 𝕜) (F := F) (E := E) (c • T) = c • mixedToModel T :=
  map_smul (mixedContinuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) r s x).toContinuousLinearMap
    c T

@[simp]
theorem mixedToModel_zero {r s : ℕ} {x : B} :
    mixedToModel (𝕜 := 𝕜) (F := F) (E := E)
      (0 : Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
           Bundle.continuousMultilinearMap 𝕜 s F E x) = 0 :=
  map_zero (mixedContinuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) r s x).toContinuousLinearMap

@[simp]
theorem mixedToModel_neg {r s : ℕ} {x : B}
    (T : Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
         Bundle.continuousMultilinearMap 𝕜 s F E x) :
    mixedToModel (𝕜 := 𝕜) (F := F) (E := E) (-T) = -mixedToModel T := by
  ext m; simp only [mixedToModel, ContinuousLinearMap.neg_apply]; rfl

@[simp]
theorem mixedToModel_sub {r s : ℕ} {x : B}
    (T₁ T₂ : Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
             Bundle.continuousMultilinearMap 𝕜 s F E x) :
    mixedToModel (𝕜 := 𝕜) (F := F) (E := E) (T₁ - T₂) =
      mixedToModel T₁ - mixedToModel T₂ := by
  ext m; simp only [mixedToModel, ContinuousLinearMap.sub_apply]; rfl

@[simp]
theorem mixedOfModel_mixedToModel {r s : ℕ} {x : B}
    (T : Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
         Bundle.continuousMultilinearMap 𝕜 s F E x) :
    mixedOfModel (𝕜 := 𝕜) (F := F) (E := E) (mixedToModel T) = T :=
  (mixedContinuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) r s x).left_inv T

@[simp]
theorem mixedToModel_mixedOfModel {r s : ℕ} {x : B}
    (f : ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜]
         ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜) :
    mixedToModel (𝕜 := 𝕜) (F := F) (E := E) (mixedOfModel (x := x) f) = f :=
  (mixedContinuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) r s x).right_inv f

theorem mixedToModel_continuous {r s : ℕ} {x : B} :
    Continuous
      (fun T : Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
              Bundle.continuousMultilinearMap 𝕜 s F E x =>
        mixedToModel (𝕜 := 𝕜) (F := F) (E := E) T) :=
  (mixedContinuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) r s x).toContinuousLinearMap.continuous

theorem mixedToModel_injective {r s : ℕ} {x : B} :
    Function.Injective
      (fun T : Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
              Bundle.continuousMultilinearMap 𝕜 s F E x =>
        mixedToModel (𝕜 := 𝕜) (F := F) (E := E) T) :=
  (mixedContinuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) r s x).injective

theorem mixedToModel_surjective {r s : ℕ} {x : B} :
    Function.Surjective
      (fun T : Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
              Bundle.continuousMultilinearMap 𝕜 s F E x =>
        mixedToModel (𝕜 := 𝕜) (F := F) (E := E) T) :=
  (mixedContinuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) r s x).surjective

theorem mixedToModel_bijective {r s : ℕ} {x : B} :
    Function.Bijective
      (fun T : Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
              Bundle.continuousMultilinearMap 𝕜 s F E x =>
        mixedToModel (𝕜 := 𝕜) (F := F) (E := E) T) :=
  (mixedContinuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) r s x).bijective

end Bundle.continuousMultilinearMap

end
