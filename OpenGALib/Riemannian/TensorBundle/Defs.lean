import OpenGALib.Tensor.Multilinear.Fiber
import OpenGALib.Tensor.Multilinear.Curry
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional

/-!
# Riemannian (r,s)-tensor bundle: definitions

Model fibers and point-wise fibers for covariant and mixed tensor
bundles on smooth manifolds. The (0,s) covariant tensor bundle is
`Bundle.continuousMultilinearMap` applied to the tangent bundle; the
(r,s) tensor bundle is `Bundle.ContinuousLinearMap` between (0,r)- and
(0,s)-tensor bundles. Each carries fiber-bundle / vector-bundle /
smooth-vector-bundle structure inherited from the tangent bundle.
-/

namespace Tensor0SBundle
noncomputable section

-- issue #8: strict `isDefEq` does not synthesize the topology, normed-space,
-- and `ContMDiffVectorBundle` instances for the tensor-bundle fiber aliases
-- (`Tensor0SModel`, `TensorRSSpace`, etc.). Keep this option locally to this
-- foundational tensor-bundle file until those aliases are replaced by explicit
-- instance bridges.
set_option backward.isDefEq.respectTransparency false

open Bundle Set IsManifold ContinuousLinearMap

open scoped Manifold Topology Bundle ContDiff BigOperators

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M]
variable {x' : M}
variable {r s : ℕ}

/-!
## Model Fibers
-/

/-- **Eng.** The trivial line bundle over `M` with constant fiber `𝕜`. -/
abbrev TrivialBundle : M → Type _ := fun _ ↦  𝕜

/-- **Math.** The model fiber for the bundle of (0,s) covariant tensors:
continuous multilinear maps from `s` copies of `E` to `𝕜`. -/
@[reducible]
def Tensor0SModel (s : ℕ) (𝕜 : Type*) (E : Type*) [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [Module.Finite 𝕜 E] [FiniteDimensional 𝕜 E] :=
  ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜

/-- **Math.** The model fiber for the (r,s)-tensor bundle: continuous linear maps from (0,r)-tensors
to (0,s)-tensors, realizing `V* ⊗ W ≅ Hom(V, W)` for finite-dimensional `V`. -/
@[reducible]
def TensorRSModel (r s : ℕ) (𝕜 : Type*) (E : Type*) [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [Module.Finite 𝕜 E] [FiniteDimensional 𝕜 E] :=
  (Tensor0SModel r 𝕜 E) →L[𝕜] (Tensor0SModel s 𝕜 E)

/-!
## Point-wise Fibers
-/

/-- **Math.** The fiber of the (0,s) covariant tensor bundle at `x ∈ M`, defined as
`Bundle.continuousMultilinearMap 𝕜 s E (TangentSpace I) x`. -/
abbrev Tensor0SSpace (s : ℕ) (I : ModelWithCorners 𝕜 E H) [IsManifold I 1 M] (x : M) :=
  Bundle.continuousMultilinearMap 𝕜 s E (TangentSpace I) x

/-- **Math.** The cotangent space at `x ∈ M`: linear functionals on the tangent space,
realized as (0,1)-tensors. -/
@[reducible]
def CotangentSpace (I : ModelWithCorners 𝕜 E H) [IsManifold I 1 M] (x : M) :=
  Tensor0SSpace 1 I x

/-- **Math.** The fiber of the (r,s)-tensor bundle at `x ∈ M`: continuous linear maps from
(0,r)-tensors to (0,s)-tensors, using `(V⊗W)* ≅ V*⊗W*` and `V*⊗W ≅ Hom(V,W)`. -/
/- TODO: Define the action of (r,s)-tensor on r covectors and s vectors.
    For example, F(ω₁,⋯,ωᵢ,v₁,⋯,vⱼ) := F(ω₁⋯ωⱼ)(v₁,⋯,vⱼ) -/
@[reducible]
def TensorRSSpace (r s : ℕ) (I : ModelWithCorners 𝕜 E H) [IsManifold I 1 M] (x : M) :=
  Tensor0SSpace r I x →L[𝕜] Tensor0SSpace s I x

/-!
## Model Fiber Instances
-/

/-- **Eng.** `Tensor0SModel s 𝕜 E` is a normed additive commutative group. -/
instance (s : ℕ) :
    NormedAddCommGroup (Tensor0SModel s 𝕜 E) := by
  unfold Tensor0SModel
  letI : NormedAddCommGroup (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜) := inferInstance
  infer_instance

/-- **Eng.** `Tensor0SModel s 𝕜 E` is a normed `𝕜`-module. -/
instance tensor0SModel_normedSpace (s : ℕ) :
    NormedSpace 𝕜 (Tensor0SModel s 𝕜 E) := by
  unfold Tensor0SModel
  exact @ContinuousMultilinearMap.normedSpace 𝕜 (Fin s) (fun _ : Fin s => E) 𝕜 _ _ _ _ _ _ 𝕜 _ _ _

/-- **Eng.** `TensorRSModel r s 𝕜 E` is a normed additive commutative group. -/
instance (r s : ℕ) :
    NormedAddCommGroup (TensorRSModel r s 𝕜 E) := by
  unfold TensorRSModel
  unfold Tensor0SModel
  letI : NormedAddCommGroup (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜) := inferInstance
  letI hs : NormedSpace 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜) := inferInstance
  letI hr : NormedSpace 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E) 𝕜) := inferInstance
  apply @ContinuousLinearMap.toNormedAddCommGroup 𝕜 𝕜
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E) 𝕜)
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜)
     _ _ _ _ hr hs _ _

/-- **Eng.** `TensorRSModel r s 𝕜 E` is a normed additive commutative group. -/
instance tensorRSModel_normedAddCommGroup (r s : ℕ) :
    NormedAddCommGroup (TensorRSModel r s 𝕜 E) :=
  inferInstance

/-- **Eng.** `TensorRSModel r s 𝕜 E` is a normed `𝕜`-module. -/
instance tensorRSModel_normedSpace (r s : ℕ) :
    NormedSpace 𝕜 (TensorRSModel r s 𝕜 E) := by
  unfold TensorRSModel
  unfold Tensor0SModel
  letI h : SMulCommClass 𝕜 𝕜 (ContinuousMultilinearMap 𝕜 (fun (x : Fin s) ↦ E) 𝕜) := inferInstance
  exact @ContinuousLinearMap.toNormedSpace 𝕜 𝕜
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E) 𝕜)
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜)
    _ _ _ _ _ _ _ _ 𝕜 _ _ h

/-!
## Point-wise Fiber Instances

The bundle and norm topologies on `Tensor0SSpace s I x` agree because the trivialization at
each point gives a continuous linear equivalence to the model fiber, and all Hausdorff
locally convex topologies on a finite-dimensional space agree.
-/

/-- **Eng.** The tangent space at any point is a normed additive commutative group, inherited from `E`. -/
instance tangentSpace_normedAddCommGroup (x : M) :
    NormedAddCommGroup (TangentSpace I x) :=
  inferInstanceAs (NormedAddCommGroup E)

/-- **Eng.** The tangent space at any point is a normed `𝕜`-module, inherited from `E`. -/
instance tangentSpace_normedSpace (x : M) :
    NormedSpace 𝕜 (TangentSpace I x) :=
  inferInstanceAs (NormedSpace 𝕜 E)

instance tangentSpace_finiteDimensional (x : M) :
    FiniteDimensional 𝕜 (TangentSpace I x) :=
  inferInstanceAs (FiniteDimensional 𝕜 E)

instance tangentSpace_moduleFree (x : M) :
    Module.Free 𝕜 (TangentSpace I x) :=
  inferInstanceAs (Module.Free 𝕜 E)

omit [FiniteDimensional 𝕜 E] in
/-- **Eng.** Alias for the general `Bundle.continuousMultilinearMap.topology_eq`, specialized to the
tangent bundle. Used internally by `tensor0SSpace_continuousLinearEquiv`. -/
private theorem tensor0SSpace_topology_eq (s : ℕ) (x : M) :
    (inferInstance : TopologicalSpace (Tensor0SSpace s I x)) =
    (inferInstanceAs (TopologicalSpace (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜))) :=
  Bundle.continuousMultilinearMap.topology_eq s x

noncomputable instance tensor0SSpace_finiteDimensional [CompleteSpace 𝕜] (s : ℕ) (x : M) :
    FiniteDimensional 𝕜 (Tensor0SSpace s I x) :=
  Bundle.continuousMultilinearMap.instFiniteDimensional s x

@[simp]
theorem finrank_tensor0SSpace [CompleteSpace 𝕜] (s : ℕ) (x : M) :
    Module.finrank 𝕜 (Tensor0SSpace s I x) = (Module.finrank 𝕜 E) ^ s :=
  Bundle.continuousMultilinearMap.finrank_eq s x

omit [FiniteDimensional 𝕜 E] in
/-- **Eng.** `Tensor0SSpace s I x` is definitionally equal to
`ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜`, since `TangentSpace I x = E`. -/
private theorem tensor0SSpace_type_eq (s : ℕ) (x : M) :
    Tensor0SSpace s I x =
    ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜 := by
  unfold Tensor0SSpace Bundle.continuousMultilinearMap
  rfl

/-- **Math.** The fiber `Tensor0SSpace s I x` is continuously linearly isomorphic to
`ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜`: the underlying types are definitionally
equal and the topologies agree by `tensor0SSpace_topology_eq`. -/
def tensor0SSpace_continuousLinearEquiv (s : ℕ) (x : M) :
    Tensor0SSpace s I x ≃L[𝕜]
    ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜 where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  continuous_toFun := by
    change @Continuous (Tensor0SSpace s I x) (ContinuousMultilinearMap 𝕜 (fun _ => E) 𝕜)
      (instTopologicalSpaceContinuousMultilinearMap 𝕜 s E (TangentSpace I) x)
      ContinuousMultilinearMap.instTopologicalSpace id
    rw [show (instTopologicalSpaceContinuousMultilinearMap 𝕜 s E (TangentSpace I) x) =
      ContinuousMultilinearMap.instTopologicalSpace from tensor0SSpace_topology_eq (I := I) s x]
    exact @continuous_id _ ContinuousMultilinearMap.instTopologicalSpace
  continuous_invFun := by
    change @Continuous (ContinuousMultilinearMap 𝕜 (fun _ => E) 𝕜) (Tensor0SSpace s I x)
      ContinuousMultilinearMap.instTopologicalSpace
      (instTopologicalSpaceContinuousMultilinearMap 𝕜 s E (TangentSpace I) x) id
    rw [show (instTopologicalSpaceContinuousMultilinearMap 𝕜 s E (TangentSpace I) x) =
      ContinuousMultilinearMap.instTopologicalSpace from tensor0SSpace_topology_eq (I := I) s x]
    exact @continuous_id _ ContinuousMultilinearMap.instTopologicalSpace


/-- **Math.** The fiber `TensorRSSpace r s I x` is continuously linearly isomorphic to
`TensorRSModel r s 𝕜 E`: this follows from `arrowCongr` applied to the
`tensor0SSpace_continuousLinearEquiv` on both the domain and codomain. -/
def tensorRSSpace_continuousLinearEquiv (r s : ℕ) (x : M) :
    TensorRSSpace r s I x ≃L[𝕜] TensorRSModel r s 𝕜 E :=
  (tensor0SSpace_continuousLinearEquiv (I := I) r x).arrowCongr
    (tensor0SSpace_continuousLinearEquiv (I := I) s x)

omit [FiniteDimensional 𝕜 E] in
/-- **Eng.** The `→L[𝕜]` between `Tensor0SSpace` fibers (with the bundle topology) is the
same type as `→L[𝕜]` between `ContinuousMultilinearMap` fibers (with the norm topology),
since the topologies agree by `tensor0SSpace_topology_eq`. -/
private theorem tensorRSSpace_type_eq (r s : ℕ) (x : M) :
    TensorRSSpace r s I x =
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E) 𝕜 →L[𝕜]
     ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜) := by
  unfold TensorRSSpace Tensor0SSpace Bundle.continuousMultilinearMap
  congr 1 <;> exact tensor0SSpace_topology_eq (I := I) _ x

/-- **Eng.** Transport `NormedAddCommGroup` and `NormedSpace` together from the norm-topology type. -/
private def tensorRSSpace_normedInstances (r s : ℕ) (x : M) :
    Σ' (ng : NormedAddCommGroup (TensorRSSpace r s I x)),
      @NormedSpace 𝕜 (TensorRSSpace r s I x) _ ng.toSeminormedAddCommGroup :=
  (tensorRSSpace_type_eq (I := I) r s x) ▸ ⟨inferInstance, inferInstance⟩

/-- **Eng.** The fiber `TensorRSSpace r s I x` is a normed additive commutative group. -/
instance tensorRSSpace_normedAddCommGroup (r s : ℕ) (x : M) :
    NormedAddCommGroup (TensorRSSpace r s I x) :=
  (tensorRSSpace_normedInstances r s x).1

/-- **Eng.** The fiber `TensorRSSpace r s I x` is a normed `𝕜`-module. -/
instance tensorRSSpace_normedSpace (r s : ℕ) (x : M) :
    NormedSpace 𝕜 (TensorRSSpace r s I x) :=
  (tensorRSSpace_normedInstances r s x).2

/-- **Eng.** Scalar multiplication on `TensorRSSpace r s I x` is continuous. -/
instance tensorRSSpace_continuousSMul (r s : ℕ) (x : M) :
    ContinuousSMul 𝕜 (TensorRSSpace r s I x) :=
  inferInstanceAs (ContinuousSMul 𝕜 (TensorRSSpace r s I x))


/-!
## Currying
-/

/-- **Math.** Currying isomorphism: a (0,s+1)-tensor is equivalent to a continuous linear map
from the tangent space to the space of (0,s)-tensors.

The proof composes three continuous linear equivalences:
1. `tensor0SSpace_continuousLinearEquiv` bridges the bundle/norm topology diamond.
2. `continuousMultilinearCurryLeftEquiv` curries the first argument of the multilinear map.
3. `arrowCongr` with the inverse of `tensor0SSpace_continuousLinearEquiv` converts
   the codomain back from norm to bundle topology. -/
noncomputable def tensor0S_curry (s : ℕ) (x : M) :
    Tensor0SSpace (s+1) I x ≃L[𝕜]
    (TangentSpace I x →L[𝕜] Tensor0SSpace s I x) :=
  (tensor0SSpace_continuousLinearEquiv (I := I) (s + 1) x).trans
    ((continuousMultilinearCurryLeftEquiv 𝕜
      (fun _ : Fin (s + 1) => E) 𝕜).toContinuousLinearEquiv.trans
        ((ContinuousLinearEquiv.refl 𝕜 E).arrowCongr
          (tensor0SSpace_continuousLinearEquiv (I := I) s x).symm))

/-!
## (0,s)-Tensor Bundle Instances

The (0,s) covariant tensor bundle inherits its fiber bundle, vector bundle, and smooth
vector bundle structure from `Bundle.continuousMultilinearMap` applied to the tangent bundle.
-/

/-- **Eng.** The total space of the (0,s)-tensor bundle carries a topology from the
multilinear bundle construction. -/
instance tensor0SBundle_topology (s : ℕ) :
    TopologicalSpace (TotalSpace
      (Tensor0SModel s 𝕜 E)
      (fun x : M => Tensor0SSpace s I x)) :=
  Bundle.continuousMultilinearMap.topologicalSpace_totalSpace 𝕜 s E (TangentSpace I)

/-- **Math.** The (0,s)-tensor bundle is a fiber bundle with model fiber `Tensor0SModel s 𝕜 E`. -/
@[simp]
noncomputable instance tensor0SBundle_fiber (s : ℕ) :
    FiberBundle
      (Tensor0SModel s 𝕜 E)
      (fun x : M => Tensor0SSpace s I x) :=
  Bundle.continuousMultilinearMap.fiberBundle 𝕜 s E (TangentSpace I)

/-- **Math.** The (0,s)-tensor bundle is a vector bundle with model fiber `Tensor0SModel s 𝕜 E`. -/
@[simp]
noncomputable instance tensor0SBundle_vector (s : ℕ) :
    VectorBundle 𝕜
      (Tensor0SModel s 𝕜 E)
      (fun x : M => Tensor0SSpace s I x) :=
  Bundle.continuousMultilinearMap.vectorBundle 𝕜 s E (TangentSpace I)

/-!
## Smooth Bundle Instances

The smooth bundle instances require `IsManifold I (n + 1) M` to get
`ContMDiffVectorBundle n` for the tangent bundle via `TangentBundle.contMDiffVectorBundle`.
-/

variable (n : WithTop ℕ∞) [IsManifold I (n + 1) M]

/-- **Math.** The (0,s)-tensor bundle is a `C^n` vector bundle over `M`. -/
@[simp]
noncomputable instance tensor0SBundle_smooth [CompleteSpace 𝕜] (s : ℕ) :
    ContMDiffVectorBundle n
      (Tensor0SModel s 𝕜 E)
      (fun x : M => Tensor0SSpace s I x) I := by
  haveI : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  haveI : (Bundle.continuousMultilinearMap.vectorPrebundle
      𝕜 s E (TangentSpace I : M → Type _)).IsContMDiff I n :=
    Bundle.continuousMultilinearMap.vectorPrebundle.isSmooth s I n
  exact (Bundle.continuousMultilinearMap.vectorPrebundle
    𝕜 s E (TangentSpace I : M → Type _)).contMDiffVectorBundle I

/-!
## (r,s)-Tensor Bundle Instances

The (r,s) tensor bundle is defined as the hom bundle from the (0,r)- to the (0,s)-tensor
bundle, using `Bundle.ContinuousLinearMap`.
-/

/-- **Eng.** The total space of the (r,s)-tensor bundle carries a topology, induced by viewing it
as the hom bundle from the (0,r)- to the (0,s)-tensor bundle. -/
noncomputable instance tensorRSBundle_topology (r s : ℕ) :
    TopologicalSpace (TotalSpace (TensorRSModel r s 𝕜 E)
      (fun x : M => TensorRSSpace r s I x)) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id 𝕜)
    (Tensor0SModel r 𝕜 E)
    (fun (x : M) => Tensor0SSpace r I x)
    (Tensor0SModel s 𝕜 E)
    (fun (x : M) => Tensor0SSpace s I x)

/-- **Math.** The (r,s)-tensor bundle is a fiber bundle, as a hom bundle between two fiber bundles. -/
noncomputable instance tensorRSBundle_fiber (r s : ℕ) :
    @FiberBundle M (TensorRSModel r s 𝕜 E) _ (by infer_instance : TopologicalSpace _)
      (fun x : M => TensorRSSpace r s I x)
      (tensorRSBundle_topology r s) _ :=
  Bundle.ContinuousLinearMap.fiberBundle (RingHom.id 𝕜)
    (Tensor0SModel r 𝕜 E)
    (fun (x : M) => Tensor0SSpace r I x)
    (Tensor0SModel s 𝕜 E)
    (fun (x : M) => Tensor0SSpace s I x)

/-- **Math.** The (r,s)-tensor bundle is a vector bundle with model fiber `TensorRSModel r s 𝕜 E`. -/
noncomputable instance tensorRSBundle_vector (r s : ℕ) :
    @VectorBundle 𝕜 M (TensorRSModel r s 𝕜 E) (fun x : M => TensorRSSpace r s I x) _
      (fun x => by infer_instance) (fun x => by infer_instance)
      (tensorRSModel_normedAddCommGroup r s) (tensorRSModel_normedSpace r s) _
      (tensorRSBundle_topology r s) _
      (tensorRSBundle_fiber r s) :=
  Bundle.ContinuousLinearMap.vectorBundle (RingHom.id 𝕜)
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E) 𝕜)
    (fun (x : M) => Tensor0SSpace r I x)
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜)
    (fun (x : M) => Tensor0SSpace s I x)

/-- **Math.** The (r,s)-tensor bundle is a `C^n` vector bundle over `M`. -/
noncomputable instance tensorRSBundle_smooth [CompleteSpace 𝕜] (r s : ℕ) :
    @ContMDiffVectorBundle n 𝕜 M (TensorRSModel r s 𝕜 E) (fun x : M => TensorRSSpace r s I x)
      _ E _ _ H _ I _ _ _ _ _ _
      (tensorRSBundle_topology r s) _
      (tensorRSBundle_fiber r s)
      (tensorRSBundle_vector r s) :=
  ContMDiffVectorBundle.continuousLinearMap

-- Removed: `tensor0S_topologicalSpace_zero` (s = 0 diamond fix).
-- It introduced a total-space topology via `Bundle.Trivial` that was propositionally
-- but not definitionally equal to `tensor0SBundle_topology 0`, blocking FiberBundle
-- instance resolution for the (0,0)-tensor bundle. Resolved with user approval to
-- support P23 (covariant derivative on (0,s)-tensor bundles).

/-!
## Bundle / norm topology bridges for differentiability and smoothness

The CLE `tensor0SSpace_continuousLinearEquiv s x` is the identity at the underlying data
level (its `toFun` is `id`); the diamond between the bundle and norm topologies on the
fiber is closed by `tensor0SSpace_topology_eq`. This means that a section
`T : Π x : M, Tensor0SSpace s I x` and the function `fun y => (CLE) (T y)` are equal as
maps on the underlying carrier, only their target type differs.

This section provides the bridges showing that (m)differentiability/smoothness of a section
through the CLEs `tensor0SSpace_continuousLinearEquiv` and `tensor0S_curry` is equivalent
to (m)differentiability/smoothness of the underlying section.
-/

omit [FiniteDimensional 𝕜 E] in
/-- **Eng.** The forward direction of `tensor0SSpace_continuousLinearEquiv` is the identity function
on the underlying carrier. -/
theorem tensor0SSpace_continuousLinearEquiv_apply (s : ℕ) (x : M)
    (T : Tensor0SSpace s I x) :
    tensor0SSpace_continuousLinearEquiv (I := I) (M := M) s x T = T := rfl

omit [FiniteDimensional 𝕜 E] in
/-- **Eng.** The inverse direction of `tensor0SSpace_continuousLinearEquiv` is the identity function
on the underlying carrier. -/
theorem tensor0SSpace_continuousLinearEquiv_symm_apply (s : ℕ) (x : M)
    (T : ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜) :
    (tensor0SSpace_continuousLinearEquiv (I := I) (M := M) s x).symm T = T := rfl

omit [FiniteDimensional 𝕜 E] in
/-- **Eng.** The CLE coerces to `id` on the underlying carrier. -/
theorem tensor0SSpace_continuousLinearEquiv_coe (s : ℕ) (x : M) :
    (tensor0SSpace_continuousLinearEquiv (I := I) (M := M) s x : _ → _) = id := rfl

omit [FiniteDimensional 𝕜 E] in
/-- **Eng.** The inverse CLE coerces to `id` on the underlying carrier. -/
theorem tensor0SSpace_continuousLinearEquiv_symm_coe (s : ℕ) (x : M) :
    ((tensor0SSpace_continuousLinearEquiv (I := I) (M := M) s x).symm : _ → _) = id := rfl

end
end Tensor0SBundle
