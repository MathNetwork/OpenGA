import Definitions.Def_OpenGA_ImmersedMetric
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Normed.Module.Alternating.Curry
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Data.Bundle
import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.Tensoriality
import Mathlib.GroupTheory.Perm.Finite
import Mathlib.GroupTheory.Perm.Option
import Mathlib.LinearAlgebra.Alternating.Basic
import Mathlib.LinearAlgebra.Alternating.DomCoprod
import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.Tactic.Cases
import Mathlib.Tactic.Group
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Idempotent
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.RestrictScalars
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.FiberBundle.Basic
import Mathlib.Topology.VectorBundle.Basic
import Mathlib.Topology.VectorBundle.Hom
import Verified.ClosedSurface_DifferentialGeometry_Bundle_Section
import Verified.ClosedSurface_DifferentialGeometry_Bundle_SectionOperations
import Verified.ClosedSurface_DifferentialGeometry_Bundle_TangentSpace
import Verified.ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Basis
import Verified.ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Bundle
import Verified.ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Comp
import Verified.ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Fiber
import Verified.ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Tensor
import Verified.ClosedSurface_DifferentialGeometry_Tensor_RSTensor_Basis
import Verified.ClosedSurface_DifferentialGeometry_Tensor_RSTensor_Coordinates_Field
import Verified.ClosedSurface_DifferentialGeometry_Tensor_RSTensor_Defs
import Verified.ClosedSurface_DifferentialGeometry_Tensor_RSTensor_Field

noncomputable section

open Bundle Set IsManifold ContinuousLinearMap

open DifferentialGeometry.Tensor0SBundle

open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry

namespace TensorMultilinear

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [FiniteDimensional 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [CompleteSpace 𝕜] in
 theorem _root_.DifferentialGeometry.TensorMultilinear.compContinuousLinearMap_isEmpty_closedSurface_DifferentialGeometry_Tensor_Multilinear_BundleSmoothEvaluation
    {F₁ F₂ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
    [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
    (f : ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F₁) 𝕜)
    (g : ∀ _ : Fin 0, F₂ →L[𝕜] F₁) :
    f.compContinuousLinearMap g =
      (ContinuousMultilinearMap.constOfIsEmpty 𝕜 _ (f 0) :
        ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F₂) 𝕜) := by
  ext v
  have hv : v = 0 := Subsingleton.elim _ _
  subst hv
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply]
  congr 1
  exact Subsingleton.elim _ _

omit [CompleteSpace 𝕜] in
 theorem _root_.DifferentialGeometry.TensorMultilinear.trivializationAt_tensor0SBundle_succ_fibre_closedSurface_DifferentialGeometry_Tensor_Multilinear_BundleSmoothEvaluation {n : ℕ}
    (T : ∀ b : M, Tensor0SSpace (n + 1) I b) (x₀ b : M) :
    (trivializationAt (Tensor0SModel (n + 1) 𝕜 E)
      (fun x : M => Tensor0SSpace (n + 1) I x) x₀ ⟨b, T b⟩).2 =
    (tensor0SSpaceFiberContinuousLinearEquiv (I := I) (n + 1) b (T b)).compContinuousLinearMap
      (fun _ : Fin (n + 1) => (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 b) := rfl

omit [CompleteSpace 𝕜] in
theorem trivializationAt_tensor0SBundle_zero_fibre_gen
    (T : ∀ b : M, Tensor0SSpace 0 I b) (x₀ b : M) :
    (trivializationAt (Tensor0SModel 0 𝕜 E)
      (fun x : M => Tensor0SSpace 0 I x) x₀ ⟨b, T b⟩).2 =
    (ContinuousMultilinearMap.constOfIsEmpty 𝕜 _ ((T b) 0) :
      ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => E) 𝕜) := by
  change ((tensor0SSpaceFiberContinuousLinearEquiv (I := I) 0 b (T b)).compContinuousLinearMap
    (fun _ : Fin 0 => (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 b)) =
    ContinuousMultilinearMap.constOfIsEmpty 𝕜 _ ((T b) 0)
  rw [_root_.DifferentialGeometry.TensorMultilinear.compContinuousLinearMap_isEmpty_closedSurface_DifferentialGeometry_Tensor_Multilinear_BundleSmoothEvaluation]
  congr 1

omit [CompleteSpace 𝕜] in
 theorem _root_.DifferentialGeometry.TensorMultilinear.trivializationAt_homBundle_fibre_closedSurface_DifferentialGeometry_Tensor_Multilinear_BundleSmoothEvaluation {n : ℕ}
    (ϕ : ∀ b : M, TangentSpace I b →L[𝕜] Tensor0SSpace n I b) (x₀ b : M) :
    (trivializationAt (E →L[𝕜] Tensor0SModel n 𝕜 E)
      (fun y : M => TangentSpace I y →L[𝕜] Tensor0SSpace n I y) x₀
      ⟨b, ϕ b⟩).2 =
    ((trivializationAt (Tensor0SModel n 𝕜 E)
      (fun x : M => Tensor0SSpace n I x) x₀).continuousLinearMapAt 𝕜 b).comp
      ((ϕ b).comp
        ((trivializationAt E (TangentSpace I) x₀).symmL 𝕜 b)) := rfl

omit [CompleteSpace 𝕜] in
 theorem _root_.DifferentialGeometry.TensorMultilinear.tensor0SBundle_linearMapAt_apply_of_mem_closedSurface_DifferentialGeometry_Tensor_Multilinear_BundleSmoothEvaluation {n : ℕ} (x₀ b : M)
    (hb : b ∈ (trivializationAt (Tensor0SModel n 𝕜 E)
      (fun x : M => Tensor0SSpace n I x) x₀).baseSet)
    (f : ContinuousMultilinearMap 𝕜 (fun _ : Fin n => E) 𝕜) (v : Fin n → E) :
    (((trivializationAt (Tensor0SModel n 𝕜 E)
        (fun x : M => Tensor0SSpace n I x) x₀).linearMapAt 𝕜 b)
      ((tensor0SSpaceContinuousLinearEquiv (I := I) n b).symm f)) v =
    f (fun j => tangentSpaceModelContinuousLinearEquiv (I := I) b
      ((trivializationAt E (TangentSpace I) x₀).symmL 𝕜 b (v j))) := by
  have h_apply := congr_fun
    (Trivialization.coe_linearMapAt_of_mem (R := 𝕜)
      (e := trivializationAt (Tensor0SModel n 𝕜 E)
        (fun x : M => Tensor0SSpace n I x) x₀) hb)
    ((tensor0SSpaceContinuousLinearEquiv (I := I) n b).symm f)
  rw [h_apply]
  change ((f.compContinuousLinearMap (fun _ : Fin n =>
    (tangentSpaceModelContinuousLinearEquiv (I := I) b).toContinuousLinearMap.comp
      ((trivializationAt E (TangentSpace I) x₀).symmL 𝕜 b)))) v = _
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rfl

@[reducible]
def curriedSectionGen {n : ℕ} (T : ∀ b : M, Tensor0SSpace (n + 1) I b) :
    ∀ b : M, TangentSpace I b →L[𝕜] Tensor0SSpace n I b :=
  fun b => tensor0SCurry (I := I) (M := M) n b (T b)

omit [CompleteSpace 𝕜] in
theorem trivializationAt_homBundle_curriedSection_eq_gen {n : ℕ}
    (T : ∀ b : M, Tensor0SSpace (n + 1) I b) (x₀ b : M)
    (hb : b ∈ (trivializationAt (Tensor0SModel n 𝕜 E)
      (fun x : M => Tensor0SSpace n I x) x₀).baseSet) :
    (trivializationAt (E →L[𝕜] Tensor0SModel n 𝕜 E)
      (fun y : M => TangentSpace I y →L[𝕜] Tensor0SSpace n I y) x₀
      ⟨b, curriedSectionGen T b⟩).2 =
    continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (n + 1) => E) 𝕜
      ((trivializationAt (Tensor0SModel (n + 1) 𝕜 E)
        (fun x : M => Tensor0SSpace (n + 1) I x) x₀ ⟨b, T b⟩).2) := by
  rw [_root_.DifferentialGeometry.TensorMultilinear.trivializationAt_homBundle_fibre_closedSurface_DifferentialGeometry_Tensor_Multilinear_BundleSmoothEvaluation (I := I) (M := M)
    (curriedSectionGen (I := I) (M := M) T) x₀ b]
  rw [_root_.DifferentialGeometry.TensorMultilinear.trivializationAt_tensor0SBundle_succ_fibre_closedSurface_DifferentialGeometry_Tensor_Multilinear_BundleSmoothEvaluation (I := I) (M := M) T x₀ b]
  ext w v
  change (((trivializationAt (Tensor0SModel n 𝕜 E)
      (fun x : M => Tensor0SSpace n I x) x₀).linearMapAt 𝕜 b)
      ((tensor0SSpaceContinuousLinearEquiv (I := I) n b).symm
        ((continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (n + 1) => E) 𝕜)
          (Tensor0SSpace.toModel (I := I) (M := M) (T b))
          (tangentSpaceModelContinuousLinearEquiv (I := I) b
            ((trivializationAt E (TangentSpace I) x₀).symmL 𝕜 b w))))) v =
    ((tensor0SSpaceFiberContinuousLinearEquiv (I := I) (n + 1) b (T b)).compContinuousLinearMap
        (fun _ : Fin (n + 1) => (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 b))
      (Fin.cons w v)
  rw [_root_.DifferentialGeometry.TensorMultilinear.tensor0SBundle_linearMapAt_apply_of_mem_closedSurface_DifferentialGeometry_Tensor_Multilinear_BundleSmoothEvaluation (I := I) (M := M) x₀ b hb]
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rw [continuousMultilinearCurryLeftEquiv_apply]
  rw [Tensor0SSpace.toModel_apply_model_vector]
  rw [tensor0SSpaceFiberContinuousLinearEquiv_apply_apply]
  congr 1
  funext j
  refine Fin.cases ?_ ?_ j
  · simp [Fin.cons_zero]
  · intro k
    simp [Fin.cons_succ]

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] in
theorem tensor0S_curry_apply_eval_gen {n : ℕ} {b : M}
    (T : Tensor0SSpace (n + 1) I b)
    (v0 : TangentSpace I b) (vs : Fin n → TangentSpace I b) :
    Tensor0SSpace.eval (tensor0SCurry (I := I) (M := M) n b T v0) vs =
    Tensor0SSpace.eval T (Fin.cons v0 vs) := by
  rfl

omit [CompleteSpace 𝕜] in
theorem contMDiffAt_curriedSection_of_contMDiffAt_section_gen {n : ℕ}
    (T : ∀ b : M, Tensor0SSpace (n + 1) I b) (x₀ : M)
    (hT : ContMDiffAt I (I.prod 𝓘(𝕜, Tensor0SModel (n + 1) 𝕜 E)) ∞
      (fun b : M =>
        TotalSpace.mk' (Tensor0SModel (n + 1) 𝕜 E)
          (E := fun x : M => Tensor0SSpace (n + 1) I x) b (T b)) x₀) :
    ContMDiffAt I (I.prod 𝓘(𝕜, E →L[𝕜] Tensor0SModel n 𝕜 E)) ∞
      (fun b : M =>
        TotalSpace.mk' (E →L[𝕜] Tensor0SModel n 𝕜 E)
          (E := fun y : M => TangentSpace I y →L[𝕜] Tensor0SSpace n I y) b
          (curriedSectionGen T b)) x₀ := by
  let := tensor0SBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n + 1)
  rw [Bundle.contMDiffAt_section (F := E →L[𝕜] Tensor0SModel n 𝕜 E)
    (E := fun y : M => TangentSpace I y →L[𝕜] Tensor0SSpace n I y)]
  have hT_at := (Bundle.contMDiffAt_section (F := Tensor0SModel (n + 1) 𝕜 E)
    (E := fun y : M => Tensor0SSpace (n + 1) I y) x₀).mp hT
  have hcurry :
      ContMDiff 𝓘(𝕜, Tensor0SModel (n + 1) 𝕜 E) 𝓘(𝕜, E →L[𝕜] Tensor0SModel n 𝕜 E)
        (∞ : WithTop ℕ∞)
        (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (n + 1) => E) 𝕜) :=
    ((continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (n + 1) => E) 𝕜
      ).toContinuousLinearEquiv.toContinuousLinearMap).contMDiff
  have hcomp := hcurry.contMDiffAt.comp x₀ hT_at
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [(trivializationAt (Tensor0SModel n 𝕜 E)
    (fun y : M => Tensor0SSpace n I y) x₀).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt _ _ _)] with b hb
  change (trivializationAt (E →L[𝕜] Tensor0SModel n 𝕜 E)
      (fun y : M => TangentSpace I y →L[𝕜] Tensor0SSpace n I y) x₀
      ⟨b, curriedSectionGen T b⟩).2 =
    (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (n + 1) => E) 𝕜)
      ((trivializationAt (Tensor0SModel (n + 1) 𝕜 E)
        (fun y : M => Tensor0SSpace (n + 1) I y) x₀ ⟨b, T b⟩).2)
  exact trivializationAt_homBundle_curriedSection_eq_gen (I := I) (M := M) T x₀ b hb

 theorem _root_.DifferentialGeometry.TensorMultilinear.contMDiffAt_section_apply_aux : ∀ (n : ℕ) (x₀ : M)
    (T : ∀ b : M, Tensor0SSpace n I b)
    (_hT : ContMDiffAt I (I.prod 𝓘(𝕜, Tensor0SModel n 𝕜 E)) ∞
      (fun b : M =>
        TotalSpace.mk' (Tensor0SModel n 𝕜 E)
          (E := fun x : M => Tensor0SSpace n I x) b (T b)) x₀)
    (v : Fin n → ∀ b : M, TangentSpace I b)
    (_hv : ∀ i : Fin n, ContMDiffAt I (I.prod 𝓘(𝕜, E)) ∞
      (fun b : M =>
        TotalSpace.mk' E (E := fun x : M => TangentSpace I x) b (v i b)) x₀),
    ContMDiffAt I 𝓘(𝕜, 𝕜) ∞
      (fun b : M => Tensor0SSpace.eval (T b) (fun i : Fin n => v i b)) x₀
  | 0, x₀, T, hT, v, _hv => by
    have hT_at := (Bundle.contMDiffAt_section (F := Tensor0SModel 0 𝕜 E)
      (E := fun y : M => Tensor0SSpace 0 I y) x₀).mp hT
    have hcurry :
        ContMDiff 𝓘(𝕜, Tensor0SModel 0 𝕜 E) 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
          (continuousMultilinearCurryFin0 𝕜 E 𝕜) :=
      (continuousMultilinearCurryFin0 𝕜 E 𝕜).toContinuousLinearMap.contMDiff
    have hcomp :
        ContMDiffAt I 𝓘(𝕜, 𝕜) ∞
          (fun b : M =>
            (continuousMultilinearCurryFin0 𝕜 E 𝕜)
              ((trivializationAt (Tensor0SModel 0 𝕜 E)
                (fun y : M => Tensor0SSpace 0 I y) x₀ ⟨b, T b⟩).2)) x₀ :=
      hcurry.contMDiffAt.comp x₀ hT_at
    refine hcomp.congr_of_eventuallyEq ?_
    filter_upwards with b
    rw [trivializationAt_tensor0SBundle_zero_fibre_gen (I := I) (M := M) T x₀ b]
    have hev : (continuousMultilinearCurryFin0 𝕜 E 𝕜)
        (ContinuousMultilinearMap.constOfIsEmpty 𝕜
          (fun _ : Fin 0 => E) ((T b) 0)) = (T b) 0 := by
      change (ContinuousMultilinearMap.constOfIsEmpty 𝕜
        (fun _ : Fin 0 => E) ((T b) 0)) 0 = (T b) 0
      rw [ContinuousMultilinearMap.constOfIsEmpty_apply]
    rw [hev]
    have huniq : (fun i : Fin 0 => v i b) = (0 : Fin 0 → E) := Subsingleton.elim _ _
    rw [huniq]
    rfl
  | n + 1, x₀, T, hT, v, hv => by
    have hCurry := contMDiffAt_curriedSection_of_contMDiffAt_section_gen
      (I := I) (M := M) T x₀ hT
    have hApplied : ContMDiffAt I (I.prod 𝓘(𝕜, Tensor0SModel n 𝕜 E)) ∞
        (fun b : M =>
          TotalSpace.mk' (Tensor0SModel n 𝕜 E)
            (E := fun x : M => Tensor0SSpace n I x) b
            ((curriedSectionGen T b) (v 0 b))) x₀ :=
      ContMDiffAt.clm_bundle_apply (𝕜 := 𝕜) (n := (∞ : WithTop ℕ∞))
        (F₁ := E) (F₂ := Tensor0SModel n 𝕜 E)
        (E₁ := fun x : M => TangentSpace I x)
        (E₂ := fun x : M => Tensor0SSpace n I x)
        (IM := I) (IB := I)
        (b := id) (ϕ := fun b : M => curriedSectionGen T b) (v := fun b : M => v 0 b)
        hCurry (hv 0)
    have hRec := contMDiffAt_section_apply_aux n x₀
      (fun b : M => (curriedSectionGen T b) (v 0 b))
      hApplied
      (fun (i : Fin n) (b : M) => v i.succ b)
      (fun i => hv i.succ)
    refine hRec.congr_of_eventuallyEq ?_
    filter_upwards with b
    show Tensor0SSpace.eval (T b) (fun i : Fin (n + 1) => v i b) =
      Tensor0SSpace.eval ((curriedSectionGen T b) (v 0 b))
        (fun i : Fin n => v i.succ b)
    rw [tensor0S_curry_apply_eval_gen]
    refine Eq.symm ?_
    congr 1
    funext j
    refine Fin.cases ?_ ?_ j
    · simp [Fin.cons_zero]
    · intro k; simp [Fin.cons_succ]

theorem contMDiffAt_section_apply_gen
    {n : ℕ} {x₀ : M}
    (T : ∀ b : M, Tensor0SSpace n I b)
    (hT : ContMDiffAt I (I.prod 𝓘(𝕜, Tensor0SModel n 𝕜 E)) ∞
      (fun b : M =>
        TotalSpace.mk' (Tensor0SModel n 𝕜 E)
          (E := fun x : M => Tensor0SSpace n I x) b (T b)) x₀)
    (v : Fin n → ∀ b : M, TangentSpace I b)
    (hv : ∀ i : Fin n, ContMDiffAt I (I.prod 𝓘(𝕜, E)) ∞
      (fun b : M =>
        TotalSpace.mk' E (E := fun x : M => TangentSpace I x) b (v i b)) x₀) :
    ContMDiffAt I 𝓘(𝕜, 𝕜) ∞
      (fun b : M => Tensor0SSpace.eval (T b) (fun i : Fin n => v i b)) x₀ :=
  _root_.DifferentialGeometry.TensorMultilinear.contMDiffAt_section_apply_aux n x₀ T hT v hv

end TensorMultilinear

end DifferentialGeometry

end
