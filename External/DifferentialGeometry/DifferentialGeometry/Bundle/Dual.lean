


import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Topology.VectorBundle.Constructions

noncomputable section

open Bundle

namespace Bundle

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] {B : Type*}
variable (E : B → Type*) [∀ x, AddCommGroup (E x)] [∀ x, Module 𝕜 (E x)]
  [∀ x, TopologicalSpace (E x)]

abbrev dual : B → Type _ :=
  fun x => E x →L[𝕜] Bundle.Trivial B 𝕜 x

end Bundle

section InstanceCheck

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {B : Type*} [TopologicalSpace B]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {E : B → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module 𝕜 (E x)]
  [TopologicalSpace (TotalSpace F E)] [∀ x, TopologicalSpace (E x)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]

example (x : B) : Bundle.dual 𝕜 E x = (E x →L[𝕜] 𝕜) := rfl

example : TopologicalSpace (TotalSpace (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E)) := inferInstance

example : FiberBundle (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) := inferInstance

example : VectorBundle 𝕜 (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) := inferInstance

end InstanceCheck

section Smooth

open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
variable {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
variable {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {E : B → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module 𝕜 (E x)]
  [TopologicalSpace (TotalSpace F E)] [∀ x, TopologicalSpace (E x)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]
variable {n : WithTop ℕ∞} [ContMDiffVectorBundle n F E IB]

example : ContMDiffVectorBundle n (F →L[𝕜] 𝕜) (Bundle.dual 𝕜 E) IB := inferInstance

end Smooth

end
