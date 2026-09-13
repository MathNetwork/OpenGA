import Definitions.Def_ClosedSurface_DifferentialGeometry_Bundle_TangentSpace
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Basis
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Bundle
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Comp
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Fiber
import Definitions.Def_OpenGA_ImmersedMetric
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Data.Bundle
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Topology.Algebra.Module.FiniteDimension

open DifferentialGeometry.Tensor.Multilinear

namespace DifferentialGeometry

namespace Tensor0SBundle

noncomputable section

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

omit [IsManifold I 1 M] in
@[instance_reducible]
noncomputable instance tangentSpaceNormedAddCommGroup (x : M) :
    NormedAddCommGroup (TangentSpace I x) where
  toNorm := by
    unfold TangentSpace
    infer_instance
  toAddCommGroup := instAddCommGroupTangentSpace I x
  toMetricSpace :=
    let m : MetricSpace (TangentSpace I x) := by
      unfold TangentSpace
      infer_instance
    m.replaceTopology (by unfold TangentSpace; rfl)
  dist_eq := by
    intro v w
    unfold TangentSpace at v w ⊢
    exact NormedAddCommGroup.dist_eq v w

omit [IsManifold I 1 M] in
@[instance_reducible]
noncomputable instance tangentSpaceNormedSpace (x : M) :
    NormedSpace 𝕜 (TangentSpace I x) where
  toModule := instModuleTangentSpace I x
  norm_smul_le := by
    intro c v
    unfold TangentSpace at v ⊢
    exact norm_smul_le c v

omit [IsManifold I 1 M] in
instance tangentSpace_finiteDimensional (x : M) :
    FiniteDimensional 𝕜 (TangentSpace I x) := by
  change FiniteDimensional 𝕜 E
  infer_instance

omit [IsManifold I 1 M] in
instance tangentSpace_moduleFree (x : M) :
    Module.Free 𝕜 (TangentSpace I x) := by
  change Module.Free 𝕜 E
  infer_instance

local instance tangentSpaceFiberBundleExplicit :
    FiberBundle E (TangentSpace I : M → Type _) :=
  TangentSpace.fiberBundle (I := I) (M := M)

local instance tangentSpace_vectorBundleExplicit :
    VectorBundle 𝕜 E (TangentSpace I : M → Type _) :=
  TangentSpace.vectorBundle (I := I) (M := M)

@[reducible]
def Tensor0SModel (s : ℕ) (𝕜 : Type*) (E : Type*) [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [_hfd : FiniteDimensional 𝕜 E] :=
  let _ := _hfd
  ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜

@[ext]
theorem Tensor0SModel.ext {f g : Tensor0SModel s 𝕜 E}
    (h : ∀ v, f v = g v) : f = g := by
  dsimp [Tensor0SModel] at f g
  exact ContinuousMultilinearMap.ext h

@[reducible]
def TensorRSModel (r s : ℕ) (𝕜 : Type*) (E : Type*) [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E] :=
  (Tensor0SModel r 𝕜 E) →L[𝕜] (Tensor0SModel s 𝕜 E)

def Tensor0SSpace (s : ℕ) (I : ModelWithCorners 𝕜 E H)
    [hMfd : IsManifold I 1 M] (x : M) : Type _ :=
  let _ := hMfd
  Bundle.continuousMultilinearMap 𝕜 s E (TangentSpace I : M → Type _) x

@[reducible]
instance tensor0SSpaceTopologicalSpace (s : ℕ) (x : M) :
    TopologicalSpace (Tensor0SSpace s I x) :=
  inferInstanceAs (TopologicalSpace (Bundle.continuousMultilinearMap 𝕜 s E (TangentSpace I : M → Type _) x))

@[reducible]
instance tensor0SSpaceAddCommGroup (s : ℕ) (x : M) :
    AddCommGroup (Tensor0SSpace s I x) :=
  inferInstanceAs (AddCommGroup (Bundle.continuousMultilinearMap 𝕜 s E (TangentSpace I : M → Type _) x))

@[reducible]
instance tensor0SSpaceModule (s : ℕ) (x : M) :
    Module 𝕜 (Tensor0SSpace s I x) :=
  inferInstanceAs (Module 𝕜 (Bundle.continuousMultilinearMap 𝕜 s E (TangentSpace I : M → Type _) x))

instance tensor0SSpace_isTopologicalAddGroup (s : ℕ) (x : M) :
    IsTopologicalAddGroup (Tensor0SSpace s I x) :=
  @Bundle.continuousMultilinearMap.instIsTopologicalAddGroup
    𝕜 _ M _ E _ _ (TangentSpace I : M → Type _)
    (fun y => tangentSpaceNormedAddCommGroup y)
    (fun y => tangentSpaceNormedSpace y) _ tangentSpaceFiberBundleExplicit
    tangentSpace_vectorBundleExplicit s x

instance tensor0SSpace_continuousAdd (s : ℕ) (x : M) :
    ContinuousAdd (Tensor0SSpace s I x) :=
  @Bundle.continuousMultilinearMap.instContinuousAdd
    𝕜 _ M _ E _ _ (TangentSpace I : M → Type _)
    (fun y => tangentSpaceNormedAddCommGroup y)
    (fun y => tangentSpaceNormedSpace y) _ tangentSpaceFiberBundleExplicit
    tangentSpace_vectorBundleExplicit s x

instance tensor0SSpace_continuousSMul (s : ℕ) (x : M) :
    ContinuousSMul 𝕜 (Tensor0SSpace s I x) :=
  @Bundle.continuousMultilinearMap.instContinuousSMul
    𝕜 _ M _ E _ _ (TangentSpace I : M → Type _)
    (fun y => tangentSpaceNormedAddCommGroup y)
    (fun y => tangentSpaceNormedSpace y) _ tangentSpaceFiberBundleExplicit
    tangentSpace_vectorBundleExplicit s x

instance tensor0SSpace_t2Space (s : ℕ) (x : M) :
    T2Space (Tensor0SSpace s I x) :=
  @Bundle.continuousMultilinearMap.instT2Space
    𝕜 _ M _ E _ _ (TangentSpace I : M → Type _)
    (fun y => tangentSpaceNormedAddCommGroup y)
    (fun y => tangentSpaceNormedSpace y) _ tangentSpaceFiberBundleExplicit
    tangentSpace_vectorBundleExplicit s x

instance tensor0SSpace_moduleFree (s : ℕ) (x : M) :
    Module.Free 𝕜 (Tensor0SSpace s I x) :=
  inferInstanceAs (Module.Free 𝕜
    (Bundle.continuousMultilinearMap 𝕜 s E (TangentSpace I : M → Type _) x))

@[reducible]
instance tensor0SSpaceInstFunLike (s : ℕ) (x : M) :
    FunLike (Tensor0SSpace s I x) (Fin s → TangentSpace I x) 𝕜 :=
  inferInstanceAs (FunLike
    (Bundle.continuousMultilinearMap 𝕜 s E (TangentSpace I : M → Type _) x) _ _)

instance tensor0SSpace_isZeroApply (s : ℕ) (x : M) :
    IsZeroApply (Tensor0SSpace s I x) (Fin s → TangentSpace I x) 𝕜 where
  zero_apply _ := rfl

instance tensor0SSpace_isAddApply (s : ℕ) (x : M) :
    IsAddApply (Tensor0SSpace s I x) (Fin s → TangentSpace I x) 𝕜 where
  add_apply _ _ _ := rfl

instance tensor0SSpace_isNegApply (s : ℕ) (x : M) :
    IsNegApply (Tensor0SSpace s I x) (Fin s → TangentSpace I x) 𝕜 where
  neg_apply _ _ := rfl

instance tensor0SSpace_isSubApply (s : ℕ) (x : M) :
    IsSubApply (Tensor0SSpace s I x) (Fin s → TangentSpace I x) 𝕜 where
  sub_apply _ _ _ := rfl

instance tensor0SSpace_isSMulApply (s : ℕ) (x : M) :
    IsSMulApply 𝕜 (Tensor0SSpace s I x) (Fin s → TangentSpace I x) 𝕜 where
  smul_apply _ _ _ := rfl

omit [FiniteDimensional 𝕜 E] in
@[ext]
theorem tensor0SSpace_ext (s : ℕ) (x : M)
    {T T' : Tensor0SSpace s I x}
    (h : ∀ v : Fin s → TangentSpace I x, T v = T' v) : T = T' :=
  ContinuousMultilinearMap.ext (M₁ := fun _ : Fin s => TangentSpace I x) (M₂ := 𝕜) h

omit [FiniteDimensional 𝕜 E] in
noncomputable def Tensor0SSpace.domDomCongr {s s' : ℕ} {x : M}
    (A : Tensor0SSpace s I x) (e : Fin s ≃ Fin s') :
    Tensor0SSpace s' I x := by
  unfold Tensor0SSpace at A ⊢
  exact ContinuousMultilinearMap.domDomCongr e A

omit [FiniteDimensional 𝕜 E] in
 theorem _root_.DifferentialGeometry.Tensor0SBundle.tensor0SSpace_topology_eq_closedSurface_DifferentialGeometry_Tensor_RSTensor_Defs (s : ℕ) (x : M) :
    (inferInstance : TopologicalSpace (Tensor0SSpace s I x)) =
    (inferInstanceAs (TopologicalSpace (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜))) :=
  @Bundle.continuousMultilinearMap.topology_eq
    𝕜 _ M _ E _ _ (TangentSpace I : M → Type _)
    (fun y => tangentSpaceNormedAddCommGroup y)
    (fun y => tangentSpaceNormedSpace y) _ tangentSpaceFiberBundleExplicit
    tangentSpace_vectorBundleExplicit s x

@[reducible]
instance tensor0SSpaceNormedAddCommGroup (s : ℕ) (x : M) :
    NormedAddCommGroup (Tensor0SSpace s I x) :=
  let normed := Bundle.continuousMultilinearMap.instNormedAddCommGroup
    (𝕜 := 𝕜) (B := M) (F := E) (E := (TangentSpace I : M → Type _)) s x
  { normed with
    toAddCommGroup := tensor0SSpaceAddCommGroup s x
    toMetricSpace := normed.toMetricSpace.replaceTopology
      (_root_.DifferentialGeometry.Tensor0SBundle.tensor0SSpace_topology_eq_closedSurface_DifferentialGeometry_Tensor_RSTensor_Defs (I := I) s x) }

@[reducible]
instance tensor0SSpaceNormedSpace (s : ℕ) (x : M) :
    NormedSpace 𝕜 (Tensor0SSpace s I x) :=
  { Bundle.continuousMultilinearMap.instNormedSpace
      (𝕜 := 𝕜) (B := M) (F := E) (E := (TangentSpace I : M → Type _)) s x with
    toModule := tensor0SSpaceModule s x }

@[reducible]
def TensorRSSpace (r s : ℕ) (I : ModelWithCorners 𝕜 E H) [IsManifold I 1 M] (x : M) : Type _ :=
  Tensor0SSpace r I x →L[𝕜] Tensor0SSpace s I x

@[reducible]
instance tensorRSSpaceTopologicalSpace (r s : ℕ) (x : M) :
    TopologicalSpace (TensorRSSpace r s I x) :=
  inferInstanceAs (TopologicalSpace (Tensor0SSpace r I x →L[𝕜] Tensor0SSpace s I x))

@[reducible]
instance tensorRSSpaceAddCommGroup (r s : ℕ) (x : M) :
    AddCommGroup (TensorRSSpace r s I x) :=
  inferInstanceAs (AddCommGroup (Tensor0SSpace r I x →L[𝕜] Tensor0SSpace s I x))

@[reducible]
instance tensorRSSpaceModule (r s : ℕ) (x : M) :
    Module 𝕜 (TensorRSSpace r s I x) :=
  inferInstanceAs (Module 𝕜 (Tensor0SSpace r I x →L[𝕜] Tensor0SSpace s I x))

instance tensorRSSpace_isTopologicalAddGroup (r s : ℕ) (x : M) :
    IsTopologicalAddGroup (TensorRSSpace r s I x) :=
  inferInstanceAs (IsTopologicalAddGroup
    (Tensor0SSpace r I x →L[𝕜] Tensor0SSpace s I x))

instance tensorRSSpace_continuousAdd (r s : ℕ) (x : M) :
    ContinuousAdd (TensorRSSpace r s I x) :=
  inferInstanceAs (ContinuousAdd (Tensor0SSpace r I x →L[𝕜] Tensor0SSpace s I x))

instance tensorRSSpace_moduleFree (r s : ℕ) (x : M) :
    Module.Free 𝕜 (TensorRSSpace r s I x) :=
  inferInstanceAs (Module.Free 𝕜 (Tensor0SSpace r I x →L[𝕜] Tensor0SSpace s I x))

@[reducible]
instance tensorRSSpaceInstFunLike (r s : ℕ) (x : M) :
    FunLike (TensorRSSpace r s I x) (Tensor0SSpace r I x) (Tensor0SSpace s I x) :=
  inferInstanceAs (FunLike (Tensor0SSpace r I x →L[𝕜] Tensor0SSpace s I x) _ _)

instance tensorRSSpace_instContinuousLinearMapClass (r s : ℕ) (x : M) :
    ContinuousLinearMapClass (TensorRSSpace r s I x) 𝕜
      (Tensor0SSpace r I x) (Tensor0SSpace s I x) :=
  inferInstanceAs (ContinuousLinearMapClass
    (Tensor0SSpace r I x →L[𝕜] Tensor0SSpace s I x) 𝕜 _ _)

instance tensorRSSpace_isZeroApply (r s : ℕ) (x : M) :
    IsZeroApply (TensorRSSpace r s I x) (Tensor0SSpace r I x) (Tensor0SSpace s I x) where
  zero_apply _ := rfl

instance tensorRSSpace_isAddApply (r s : ℕ) (x : M) :
    IsAddApply (TensorRSSpace r s I x) (Tensor0SSpace r I x) (Tensor0SSpace s I x) where
  add_apply _ _ _ := rfl

instance tensorRSSpace_isNegApply (r s : ℕ) (x : M) :
    IsNegApply (TensorRSSpace r s I x) (Tensor0SSpace r I x) (Tensor0SSpace s I x) where
  neg_apply _ _ := rfl

instance tensorRSSpace_isSubApply (r s : ℕ) (x : M) :
    IsSubApply (TensorRSSpace r s I x) (Tensor0SSpace r I x) (Tensor0SSpace s I x) where
  sub_apply _ _ _ := rfl

instance tensorRSSpace_isSMulApply (r s : ℕ) (x : M) :
    IsSMulApply 𝕜 (TensorRSSpace r s I x) (Tensor0SSpace r I x)
      (Tensor0SSpace s I x) where
  smul_apply _ _ _ := rfl

instance _root_.DifferentialGeometry.Tensor0SBundle.instNormedAddCommGroupTensor0SModel (s : ℕ) :
    NormedAddCommGroup (Tensor0SModel s 𝕜 E) := by
  unfold Tensor0SModel
  letI : NormedAddCommGroup (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜) := inferInstance
  infer_instance

instance tensor0SModelNormedSpace (s : ℕ) :
    NormedSpace 𝕜 (Tensor0SModel s 𝕜 E) := by
  unfold Tensor0SModel
  exact @ContinuousMultilinearMap.normedSpace 𝕜 (Fin s) (fun _ : Fin s => E) 𝕜 _ _ _ _ _ _ 𝕜 _ _ _

instance _root_.DifferentialGeometry.Tensor0SBundle.instNormedAddCommGroupTensorRSModel (r s : ℕ) :
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

instance tensorRSModelNormedAddCommGroup (r s : ℕ) :
    NormedAddCommGroup (TensorRSModel r s 𝕜 E) :=
  inferInstance

instance tensorRSModelNormedSpace (r s : ℕ) :
    NormedSpace 𝕜 (TensorRSModel r s 𝕜 E) := by
  unfold TensorRSModel
  unfold Tensor0SModel
  letI h : SMulCommClass 𝕜 𝕜 (ContinuousMultilinearMap 𝕜 (fun (x : Fin s) ↦ E) 𝕜) := inferInstance
  exact @ContinuousLinearMap.toNormedSpace 𝕜 𝕜
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E) 𝕜)
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜)
    _ _ _ _ _ _ _ _ 𝕜 _ _ h

noncomputable instance tensor0SSpace_finiteDimensional (s : ℕ) (x : M) :
    FiniteDimensional 𝕜 (Tensor0SSpace s I x) :=
  @Bundle.continuousMultilinearMap.instFiniteDimensional
    𝕜 _ M _ E _ _ (TangentSpace I : M → Type _)
    (fun y => tangentSpaceNormedAddCommGroup y)
    (fun y => tangentSpaceNormedSpace y) _ tangentSpaceFiberBundleExplicit
    tangentSpace_vectorBundleExplicit _ s x

noncomputable instance tensorRSModel_finiteDimensional (r s : ℕ) :
    FiniteDimensional 𝕜 (TensorRSModel r s 𝕜 E) := by
  unfold TensorRSModel
  have : FiniteDimensional 𝕜 (Tensor0SModel r 𝕜 E) :=
    continuousMultilinearMap_finiteDimensional r
  have : FiniteDimensional 𝕜 (Tensor0SModel s 𝕜 E) :=
    continuousMultilinearMap_finiteDimensional s
  exact ContinuousLinearMap.finiteDimensional

noncomputable instance tensorRSSpace_finiteDimensional (r s : ℕ) (x : M) :
    FiniteDimensional 𝕜 (TensorRSSpace r s I x) := by
  unfold TensorRSSpace
  exact ContinuousLinearMap.finiteDimensional

omit [FiniteDimensional 𝕜 E] [IsManifold I 1 M] in
 def _root_.DifferentialGeometry.Tensor0SBundle.tensor0SModelContinuousLinearEquiv_closedSurface_DifferentialGeometry_Tensor_RSTensor_Defs (s : ℕ) (x : M) :
    ContinuousMultilinearMap 𝕜 (fun _ : Fin s => TangentSpace I x) 𝕜 ≃L[𝕜]
      ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜 where
  toFun T := T.compContinuousLinearMap fun _ =>
    (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm.toContinuousLinearMap
  invFun T := T.compContinuousLinearMap fun _ =>
    (tangentSpaceModelContinuousLinearEquiv (I := I) x).toContinuousLinearMap
  left_inv T := by
    ext v
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    congr 1
  right_inv T := by
    ext v
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    congr 1
  map_add' T U := by
    ext v
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, add_apply]
  map_smul' c T := by
    ext v
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, smul_apply, RingHom.id_apply]
  continuous_toFun :=
    (ContinuousMultilinearMap.compContinuousLinearMapL (F := 𝕜) fun _ =>
      (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm.toContinuousLinearMap).continuous
  continuous_invFun :=
    (ContinuousMultilinearMap.compContinuousLinearMapL (F := 𝕜) fun _ =>
      (tangentSpaceModelContinuousLinearEquiv (I := I) x).toContinuousLinearMap).continuous

omit [FiniteDimensional 𝕜 E] [IsManifold I 1 M] in
def tensor0SSpaceFiberContinuousLinearEquiv (s : ℕ) (x : M) :
    Tensor0SSpace s I x ≃L[𝕜]
      ContinuousMultilinearMap 𝕜 (fun _ : Fin s => TangentSpace I x) 𝕜 where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  continuous_toFun := by
    change @Continuous (Tensor0SSpace s I x)
      (ContinuousMultilinearMap 𝕜 (fun _ => TangentSpace I x) 𝕜)
      (_root_.instTopologicalSpaceContinuousMultilinearMap 𝕜 s E (TangentSpace I : M → Type _) x)
      ContinuousMultilinearMap.instTopologicalSpace id
    rw [show (_root_.instTopologicalSpaceContinuousMultilinearMap 𝕜 s E
      (TangentSpace I : M → Type _) x) = ContinuousMultilinearMap.instTopologicalSpace from by
        unfold TangentSpace
        exact _root_.DifferentialGeometry.Tensor0SBundle.tensor0SSpace_topology_eq_closedSurface_DifferentialGeometry_Tensor_RSTensor_Defs (I := I) s x]
    exact @continuous_id _ ContinuousMultilinearMap.instTopologicalSpace
  continuous_invFun := by
    change @Continuous (ContinuousMultilinearMap 𝕜 (fun _ => TangentSpace I x) 𝕜)
      (Tensor0SSpace s I x) ContinuousMultilinearMap.instTopologicalSpace
      (_root_.instTopologicalSpaceContinuousMultilinearMap 𝕜 s E (TangentSpace I : M → Type _) x) id
    rw [show (_root_.instTopologicalSpaceContinuousMultilinearMap 𝕜 s E
      (TangentSpace I : M → Type _) x) = ContinuousMultilinearMap.instTopologicalSpace from by
        unfold TangentSpace
        exact _root_.DifferentialGeometry.Tensor0SBundle.tensor0SSpace_topology_eq_closedSurface_DifferentialGeometry_Tensor_RSTensor_Defs (I := I) s x]
    exact @continuous_id _ ContinuousMultilinearMap.instTopologicalSpace

def tensor0SSpaceContinuousLinearEquiv (s : ℕ) (x : M) :
    Tensor0SSpace s I x ≃L[𝕜]
    ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜 :=
  (tensor0SSpaceFiberContinuousLinearEquiv (I := I) s x).trans
    (_root_.DifferentialGeometry.Tensor0SBundle.tensor0SModelContinuousLinearEquiv_closedSurface_DifferentialGeometry_Tensor_RSTensor_Defs (I := I) s x)

namespace Tensor0SSpace

omit [FiniteDimensional 𝕜 E] [IsManifold I 1 M] in
def eval {s : ℕ} {x : M} (T : Tensor0SSpace s I x)
    (v : Fin s → TangentSpace I x) : 𝕜 :=
  tensor0SSpaceFiberContinuousLinearEquiv (I := I) s x T v

def toModel {s : ℕ} {x : M} (T : Tensor0SSpace s I x) :
    ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜 :=
  tensor0SSpaceContinuousLinearEquiv s x T

def ofModel {s : ℕ} {x : M}
    (f : ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜) :
    Tensor0SSpace s I x :=
  (tensor0SSpaceContinuousLinearEquiv s x).symm f

omit [FiniteDimensional 𝕜 E] in
theorem toModel_apply_model_vector {s : ℕ} {x : M} (T : Tensor0SSpace s I x)
    (v : Fin s → E) :
    toModel T v =
      T (fun i => (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v i)) := by
  rfl

end Tensor0SSpace

def tensorRSSpaceContinuousLinearEquiv (r s : ℕ) (x : M) :
    TensorRSSpace r s I x ≃L[𝕜] TensorRSModel r s 𝕜 E := by
  unfold TensorRSSpace
  exact (tensor0SSpaceContinuousLinearEquiv (I := I) r x).arrowCongr
    (tensor0SSpaceContinuousLinearEquiv (I := I) s x)

 def _root_.DifferentialGeometry.Tensor0SBundle.tensorRSSpace_toModelAddHom_closedSurface_DifferentialGeometry_Tensor_RSTensor_Defs (r s : ℕ) (x : M) :
    TensorRSSpace r s I x →+ TensorRSModel r s 𝕜 E :=
  { toFun := fun T => tensorRSSpaceContinuousLinearEquiv (I := I) r s x T
    map_zero' := map_zero (tensorRSSpaceContinuousLinearEquiv (I := I) r s x)
    map_add' := map_add (tensorRSSpaceContinuousLinearEquiv (I := I) r s x) }

noncomputable instance tensorRSSpaceNormedAddCommGroup (r s : ℕ) (x : M) :
    NormedAddCommGroup (TensorRSSpace r s I x) :=
  NormedAddCommGroup.induced (TensorRSSpace r s I x) (TensorRSModel r s 𝕜 E)
    (_root_.DifferentialGeometry.Tensor0SBundle.tensorRSSpace_toModelAddHom_closedSurface_DifferentialGeometry_Tensor_RSTensor_Defs (I := I) r s x)
    (tensorRSSpaceContinuousLinearEquiv (I := I) r s x).injective

noncomputable instance tensorRSSpaceNormedSpace (r s : ℕ) (x : M) :
    NormedSpace 𝕜 (TensorRSSpace r s I x) where
  norm_smul_le := by
    intro c T
    change ‖tensorRSSpaceContinuousLinearEquiv (I := I) r s x (c • T)‖ ≤
      ‖c‖ * ‖tensorRSSpaceContinuousLinearEquiv (I := I) r s x T‖
    rw [map_smul]
    exact norm_smul_le c (tensorRSSpaceContinuousLinearEquiv (I := I) r s x T)

instance tensorRSSpace_continuousSMul (r s : ℕ) (x : M) :
    ContinuousSMul 𝕜 (TensorRSSpace r s I x) :=
  inferInstanceAs (ContinuousSMul 𝕜 (Tensor0SSpace r I x →L[𝕜] Tensor0SSpace s I x))

namespace TensorRSSpace

def toModel {r s : ℕ} {x : M} (T : TensorRSSpace r s I x) :
    TensorRSModel r s 𝕜 E :=
  tensorRSSpaceContinuousLinearEquiv (I := I) r s x T

def ofModel {r s : ℕ} {x : M} (f : TensorRSModel r s 𝕜 E) :
    TensorRSSpace r s I x :=
  (tensorRSSpaceContinuousLinearEquiv (I := I) r s x).symm f

end TensorRSSpace

noncomputable def tensor0SCurry (s : ℕ) (x : M) :
    Tensor0SSpace (s+1) I x ≃L[𝕜]
    (TangentSpace I x →L[𝕜] Tensor0SSpace s I x) :=
  (tensor0SSpaceFiberContinuousLinearEquiv (I := I) (s + 1) x).trans
    ((continuousMultilinearCurryLeftEquiv 𝕜
      (fun _ : Fin (s + 1) => TangentSpace I x) 𝕜).toContinuousLinearEquiv.trans
        ((ContinuousLinearEquiv.refl 𝕜 (TangentSpace I x)).arrowCongr
          (tensor0SSpaceFiberContinuousLinearEquiv (I := I) s x).symm))

instance tensor0SBundleTopology (s : ℕ) :
    TopologicalSpace (TotalSpace
      (Tensor0SModel s 𝕜 E)
      (fun x : M => Tensor0SSpace s I x)) :=
  Bundle.continuousMultilinearMap.topologicalSpaceTotalSpace 𝕜 s E (TangentSpace I : M → Type _)

@[simp]
noncomputable instance tensor0SBundleFiber (s : ℕ) :
    FiberBundle
      (Tensor0SModel s 𝕜 E)
      (fun x : M => Tensor0SSpace s I x) :=
  Bundle.continuousMultilinearMap.fiberBundle 𝕜 s E (TangentSpace I : M → Type _)

@[simp]
noncomputable instance tensor0SBundle_vector (s : ℕ) :
    VectorBundle 𝕜
      (Tensor0SModel s 𝕜 E)
      (fun x : M => Tensor0SSpace s I x) :=
  Bundle.continuousMultilinearMap.vectorBundle 𝕜 s E (TangentSpace I : M → Type _)

instance isManifold_infty_succ [IsManifold I ∞ M] :
    IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
  have h : ((∞ : WithTop ℕ∞) + 1) = ∞ := by simp
  rw [h]; infer_instance

variable (n : WithTop ℕ∞) [IsManifold I (n + 1) M]

@[simp]
noncomputable instance tensor0SBundle_smooth (s : ℕ) :
    ContMDiffVectorBundle n
      (Tensor0SModel s 𝕜 E)
      (fun x : M => Tensor0SSpace s I x) I := by
  have : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  have : (Bundle.continuousMultilinearMap.vectorPrebundle
      𝕜 s E (TangentSpace I : M → Type _)).IsContMDiff I n :=
    Bundle.continuousMultilinearMap.vectorPrebundle.isSmooth s I n
  exact (Bundle.continuousMultilinearMap.vectorPrebundle
    𝕜 s E (TangentSpace I : M → Type _)).contMDiffVectorBundle I

noncomputable instance tensorRSBundleTopology (r s : ℕ) :
    TopologicalSpace (TotalSpace (TensorRSModel r s 𝕜 E)
      (fun x : M => TensorRSSpace r s I x)) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id 𝕜)
    (Tensor0SModel r 𝕜 E)
    (fun (x : M) => Tensor0SSpace r I x)
    (Tensor0SModel s 𝕜 E)
    (fun (x : M) => Tensor0SSpace s I x)

noncomputable instance tensorRSBundleFiber (r s : ℕ) :
    @FiberBundle M (TensorRSModel r s 𝕜 E) _ (by infer_instance : TopologicalSpace _)
      (fun x : M => TensorRSSpace r s I x)
      (tensorRSBundleTopology r s)
      (fun x : M => tensorRSSpaceTopologicalSpace r s x) :=
  Bundle.ContinuousLinearMap.fiberBundle (RingHom.id 𝕜)
    (Tensor0SModel r 𝕜 E)
    (fun (x : M) => Tensor0SSpace r I x)
    (Tensor0SModel s 𝕜 E)
    (fun (x : M) => Tensor0SSpace s I x)

noncomputable instance tensorRSBundle_vector (r s : ℕ) :
    @VectorBundle 𝕜 M (TensorRSModel r s 𝕜 E) (fun x : M => TensorRSSpace r s I x) _
      (fun x => by infer_instance) (fun x => by infer_instance)
      (tensorRSModelNormedAddCommGroup r s) (tensorRSModelNormedSpace r s) _
      (tensorRSBundleTopology r s) _
      (tensorRSBundleFiber r s) :=
  Bundle.ContinuousLinearMap.vectorBundle (RingHom.id 𝕜)
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E) 𝕜)
    (fun (x : M) => Tensor0SSpace r I x)
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜)
    (fun (x : M) => Tensor0SSpace s I x)

noncomputable instance tensorRSBundle_smooth (r s : ℕ) :
    @ContMDiffVectorBundle n 𝕜 M (TensorRSModel r s 𝕜 E) (fun x : M => TensorRSSpace r s I x)
      _ E _ _ H _ I _ _ _ _ _ _
      (tensorRSBundleTopology r s) _
      (tensorRSBundleFiber r s)
      (tensorRSBundle_vector r s) :=
  ContMDiffVectorBundle.continuousLinearMap

theorem tensorRSSpace_continuousLinearEquiv_apply_apply (r s : ℕ) (x : M)
    (T : TensorRSSpace r s I x) (β : Tensor0SModel r 𝕜 E) (v : Fin s → E) :
    tensorRSSpaceContinuousLinearEquiv (I := I) (M := M) r s x T β v =
      T ((tensor0SSpaceContinuousLinearEquiv (I := I) (M := M) r x).symm β)
        (fun i => (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v i)) := by
  rfl

omit [FiniteDimensional 𝕜 E] in
theorem tensor0SSpaceFiberContinuousLinearEquiv_apply (s : ℕ) (x : M)
    (T : Tensor0SSpace s I x) :
    tensor0SSpaceFiberContinuousLinearEquiv (I := I) (M := M) s x T = T := rfl

omit [FiniteDimensional 𝕜 E] in
theorem tensor0SSpaceFiberContinuousLinearEquiv_apply_apply (s : ℕ) (x : M)
    (T : Tensor0SSpace s I x) (v : Fin s → TangentSpace I x) :
    tensor0SSpaceFiberContinuousLinearEquiv (I := I) (M := M) s x T v = T v := rfl

omit [FiniteDimensional 𝕜 E] in
theorem tensor0SSpaceFiberContinuousLinearEquiv_symm_apply (s : ℕ) (x : M)
    (T : ContinuousMultilinearMap 𝕜 (fun _ : Fin s => TangentSpace I x) 𝕜) :
    (tensor0SSpaceFiberContinuousLinearEquiv (I := I) (M := M) s x).symm T = T := rfl

end

end Tensor0SBundle

end DifferentialGeometry
