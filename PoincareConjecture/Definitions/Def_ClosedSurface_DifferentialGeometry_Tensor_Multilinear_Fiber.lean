import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Basis
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Bundle
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Comp
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
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Topology.Algebra.Module.FiniteDimension

open DifferentialGeometry.Tensor.Multilinear

noncomputable section

open Bundle Set

open scoped Manifold Topology Bundle ContDiff BigOperators

namespace Bundle.continuousMultilinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

variable {B : Type*} [TopologicalSpace B]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]

variable [TopologicalSpace (TotalSpace F E)]

variable [FiberBundle F E] [VectorBundle 𝕜 F E]

variable {s : ℕ}

instance instFunLike (s : ℕ) (x : B) :
    FunLike (Bundle.continuousMultilinearMap 𝕜 s F E x) (Fin s → E x) 𝕜 :=
  ContinuousMultilinearMap.funLike

theorem topology_eq (s : ℕ) (x : B) :
    (inferInstance : TopologicalSpace (Bundle.continuousMultilinearMap 𝕜 s F E x)) =
    (inferInstanceAs (TopologicalSpace
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E x) 𝕜))) := by
  change _root_.instTopologicalSpaceContinuousMultilinearMap 𝕜 s F E x = _
  simp only [_root_.instTopologicalSpaceContinuousMultilinearMap]
  set e := trivializationAt F E x
  set g : ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E x) 𝕜 →L[𝕜]
      ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜 :=
    ContinuousMultilinearMap.compContinuousLinearMapL (fun _ => e.symmL 𝕜 x) with hg_def
  have hfactor : (↑(Pretrivialization.continuousMultilinearMap 𝕜 s e) ∘
      TotalSpace.mk' _ x) = Prod.mk x ∘ g := by funext; rfl
  rw [hfactor, ← induced_compose, (isInducing_prodMkRight x).eq_induced.symm]
  set g' := ContinuousMultilinearMap.compContinuousLinearMapL (F := 𝕜)
    (E₁ := fun _ : Fin s => F) (E := fun _ : Fin s => E x)
    (fun _ => e.continuousLinearMapAt 𝕜 x) with hg'_def
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt F E x
  have hleft : Function.LeftInverse g' g := by
    intro L
    apply ContinuousMultilinearMap.ext
    intro v
    dsimp [g, g']
    apply congrArg L
    funext i
    exact e.symmₗ_linearMapAt hx (v i)
  have hright : Function.RightInverse g' g := by
    intro M
    apply ContinuousMultilinearMap.ext
    intro v
    dsimp [g, g']
    apply congrArg M
    funext i
    exact e.linearMapAt_symmₗ hx (v i)
  exact (Homeomorph.mk ⟨g, g', hleft, hright⟩
    g.continuous g'.continuous).isInducing.eq_induced.symm

instance instNormedAddCommGroup (s : ℕ) (x : B) :
    NormedAddCommGroup (Bundle.continuousMultilinearMap 𝕜 s F E x) := by
  delta Bundle.continuousMultilinearMap; infer_instance

instance instNormedSpace (s : ℕ) (x : B) :
    NormedSpace 𝕜 (Bundle.continuousMultilinearMap 𝕜 s F E x) := by
  delta Bundle.continuousMultilinearMap; exact ContinuousMultilinearMap.normedSpace

instance instT2Space (s : ℕ) (x : B) :
    @T2Space (Bundle.continuousMultilinearMap 𝕜 s F E x) inferInstance :=
  (topology_eq (𝕜 := 𝕜) (F := F) (E := E) s x).symm ▸
    inferInstanceAs (@T2Space (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E x) 𝕜) _)

instance instIsTopologicalAddGroup (s : ℕ) (x : B) :
    @IsTopologicalAddGroup (Bundle.continuousMultilinearMap 𝕜 s F E x) inferInstance _ :=
  (topology_eq (𝕜 := 𝕜) (F := F) (E := E) s x).symm ▸
    inferInstanceAs (@IsTopologicalAddGroup
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E x) 𝕜) _ _)

instance instContinuousSMul (s : ℕ) (x : B) :
    @ContinuousSMul 𝕜 (Bundle.continuousMultilinearMap 𝕜 s F E x) _ _ inferInstance :=
  (topology_eq (𝕜 := 𝕜) (F := F) (E := E) s x).symm ▸
    inferInstanceAs (@ContinuousSMul 𝕜
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E x) 𝕜) _ _ _)

instance instContinuousAdd (s : ℕ) (x : B) :
    @ContinuousAdd (Bundle.continuousMultilinearMap 𝕜 s F E x) inferInstance _ :=
  @IsTopologicalAddGroup.toContinuousAdd _ inferInstance _ (instIsTopologicalAddGroup s x)

def continuousLinearEquivAt (s : ℕ) (x : B) :
    Bundle.continuousMultilinearMap 𝕜 s F E x ≃L[𝕜]
    ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜 where
  toFun := ContinuousMultilinearMap.compContinuousLinearMapL
    (fun _ => (trivializationAt F E x).symmL 𝕜 x)
  invFun := ContinuousMultilinearMap.compContinuousLinearMapL
    (fun _ => (trivializationAt F E x).continuousLinearMapAt 𝕜 x)
  left_inv L := ContinuousMultilinearMap.ext fun v => by
    dsimp [ContinuousMultilinearMap.compContinuousLinearMapL]
    congr 1; funext i
    exact (trivializationAt F E x).symmₗ_linearMapAt
      (mem_baseSet_trivializationAt F E x) (v i)
  right_inv M := ContinuousMultilinearMap.ext fun v => by
    dsimp [ContinuousMultilinearMap.compContinuousLinearMapL]
    congr 1; funext i
    exact (trivializationAt F E x).linearMapAt_symmₗ
      (mem_baseSet_trivializationAt F E x) (v i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  continuous_toFun := by
    change @Continuous (Bundle.continuousMultilinearMap 𝕜 s F E x)
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
      (_root_.instTopologicalSpaceContinuousMultilinearMap 𝕜 s F E x)
      ContinuousMultilinearMap.instTopologicalSpace _
    rw [show _root_.instTopologicalSpaceContinuousMultilinearMap 𝕜 s F E x =
      ContinuousMultilinearMap.instTopologicalSpace from topology_eq s x]
    exact (ContinuousMultilinearMap.compContinuousLinearMapL
      (fun _ => (trivializationAt F E x).symmL 𝕜 x)).continuous
  continuous_invFun := by
    change @Continuous (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
      (Bundle.continuousMultilinearMap 𝕜 s F E x)
      ContinuousMultilinearMap.instTopologicalSpace
      (_root_.instTopologicalSpaceContinuousMultilinearMap 𝕜 s F E x) _
    rw [show _root_.instTopologicalSpaceContinuousMultilinearMap 𝕜 s F E x =
      ContinuousMultilinearMap.instTopologicalSpace from topology_eq s x]
    exact (ContinuousMultilinearMap.compContinuousLinearMapL
      (fun _ => (trivializationAt F E x).continuousLinearMapAt 𝕜 x)).continuous

def toModel {s : ℕ} {x : B}
    (T : Bundle.continuousMultilinearMap 𝕜 s F E x) :
    ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜 :=
  continuousLinearEquivAt (F := F) (E := E) s x T

def ofModel {s : ℕ} {x : B}
    (f : ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜) :
    Bundle.continuousMultilinearMap 𝕜 s F E x :=
  (continuousLinearEquivAt (F := F) (E := E) s x).symm f

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]

noncomputable instance instFiniteDimensional (s : ℕ) (x : B) :
    FiniteDimensional 𝕜 (Bundle.continuousMultilinearMap 𝕜 s F E x) := by
  have : FiniteDimensional 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜) :=
    continuousMultilinearMap_finiteDimensional s
  exact (continuousLinearEquivAt (F := F) (E := E) s x).symm.toLinearEquiv.finiteDimensional

end Bundle.continuousMultilinearMap

end
