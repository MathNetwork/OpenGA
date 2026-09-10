import Definitions.Def_OpenGA_ImmersedMetric
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Normed.Module.Alternating.Curry
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
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
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
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
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Trace
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
import Verified.ClosedSurface_DifferentialGeometry_Bundle_Section
import Verified.ClosedSurface_DifferentialGeometry_Bundle_SectionOperations
import Verified.ClosedSurface_DifferentialGeometry_Bundle_TangentSpace
import Verified.ClosedSurface_DifferentialGeometry_Tensor_Auxiliary_PredualBasis
import Verified.ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Basis
import Verified.ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Bundle
import Verified.ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Comp
import Verified.ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Fiber
import Verified.ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Tensor
import Verified.ClosedSurface_DifferentialGeometry_Tensor_RSTensor_Basis
import Verified.ClosedSurface_DifferentialGeometry_Tensor_RSTensor_Coordinates_Field
import Verified.ClosedSurface_DifferentialGeometry_Tensor_RSTensor_Defs
import Verified.ClosedSurface_DifferentialGeometry_Tensor_RSTensor_Derivation_Contract
import Verified.ClosedSurface_DifferentialGeometry_Tensor_RSTensor_Field

namespace DifferentialGeometry.Tensor.RSTensor

noncomputable section

open _root_.Bundle Manifold DifferentialGeometry.Tensor0SBundle

open scoped Manifold Topology Bundle ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)

variable (n : WithTop ℕ∞)

variable (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

 noncomputable def _root_.DifferentialGeometry.Tensor.RSTensor.to02Tensor_eCLM_closedSurface_DifferentialGeometry_Tensor_RSTensor_Metric :
    (E →L[ℝ] ℝ) →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin 1 => E) ℝ :=
  (continuousMultilinearCurryFin1 ℝ E ℝ).symm.toContinuousLinearMap

 noncomputable def _root_.DifferentialGeometry.Tensor.RSTensor.to02Tensor_uCLM_closedSurface_DifferentialGeometry_Tensor_RSTensor_Metric :
    (E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin 1 => E) ℝ) →L[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ :=
  (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 2 => E) ℝ).symm.toContinuousLinearMap

 noncomputable def _root_.DifferentialGeometry.Tensor.RSTensor.to02TensorFiber_closedSurface_DifferentialGeometry_Tensor_RSTensor_Metric {x : M}
    (A : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :
    Tensor0SSpace 2 I x :=
  (tensor0SSpaceFiberContinuousLinearEquiv (I := I) 2 x).symm
    ((_root_.DifferentialGeometry.Tensor.RSTensor.to02Tensor_eCLM_closedSurface_DifferentialGeometry_Tensor_RSTensor_Metric (E := E)).comp A).uncurryLeft

 lemma _root_.DifferentialGeometry.Tensor.RSTensor.to02Tensor_trivialization_eq_closedSurface_DifferentialGeometry_Tensor_RSTensor_Metric {x₀ x : M}
    (A : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    (trivializationAt (Tensor0SBundle.Tensor0SModel 2 ℝ E)
      (fun y => Tensor0SBundle.Tensor0SSpace 2 I y) x₀
      ⟨x, _root_.DifferentialGeometry.Tensor.RSTensor.to02TensorFiber_closedSurface_DifferentialGeometry_Tensor_RSTensor_Metric (I := I) (M := M) A⟩).2
      =
    (_root_.DifferentialGeometry.Tensor.RSTensor.to02Tensor_uCLM_closedSurface_DifferentialGeometry_Tensor_RSTensor_Metric (E := E)) ((_root_.DifferentialGeometry.Tensor.RSTensor.to02Tensor_eCLM_closedSurface_DifferentialGeometry_Tensor_RSTensor_Metric (E := E)).comp
      ((trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
      (fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) x₀ ⟨x, A⟩).2)) := by
  let e₀ := trivializationAt E (TangentSpace I) x₀
  rw [show _root_.DifferentialGeometry.Tensor.RSTensor.to02TensorFiber_closedSurface_DifferentialGeometry_Tensor_RSTensor_Metric (I := I) (M := M) A =
      ((_root_.DifferentialGeometry.Tensor.RSTensor.to02Tensor_eCLM_closedSurface_DifferentialGeometry_Tensor_RSTensor_Metric (E := E)).comp A).uncurryLeft from
    tensor0SSpaceFiberContinuousLinearEquiv_symm_apply (I := I) 2 x _]
  ext m
  change (((e₀.continuousMultilinearMap ℝ 2)
      ⟨x, ((_root_.DifferentialGeometry.Tensor.RSTensor.to02Tensor_eCLM_closedSurface_DifferentialGeometry_Tensor_RSTensor_Metric (E := E)).comp
        A).uncurryLeft⟩).2) m = _
  rw [_root_.Bundle.Trivialization.continuousMultilinearMap_apply]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ]
  have hx' : x ∈ (trivializationAt (E →L[ℝ] ℝ)
      (fun y => TangentSpace I y →L[ℝ] ℝ) x₀).baseSet := by
    rw [hom_trivializationAt_baseSet]
    exact ⟨hx, by simp⟩
  rw [hom_trivializationAt_apply]
  change (_root_.DifferentialGeometry.Tensor.RSTensor.to02Tensor_eCLM_closedSurface_DifferentialGeometry_Tensor_RSTensor_Metric (E := E)) (A
      ((Trivialization.symmL ℝ e₀ x) (m 0)))
      (Fin.tail fun i => (Trivialization.symmL ℝ e₀ x) (m i)) =
    (_root_.DifferentialGeometry.Tensor.RSTensor.to02Tensor_eCLM_closedSurface_DifferentialGeometry_Tensor_RSTensor_Metric (E := E)) (ContinuousLinearMap.inCoordinates E (TangentSpace I) (E →L[ℝ] ℝ)
      (fun y => TangentSpace I y →L[ℝ] ℝ) x₀ x x₀ x
      A (m 0))
      (Fin.tail m)
  change A ((Trivialization.symmL ℝ e₀ x) (m 0))
      ((Trivialization.symmL ℝ e₀ x) (Fin.tail m 0)) =
    ContinuousLinearMap.inCoordinates E (TangentSpace I) (E →L[ℝ] ℝ)
      (fun y => TangentSpace I y →L[ℝ] ℝ) x₀ x x₀ x A (m 0) (Fin.tail m 0)
  rw [inCoordinates_apply_eq₂ hx hx (by simp)]
  dsimp only [e₀]
  simp only [Trivialization.symmL_apply (trivializationAt E (TangentSpace I) x₀) hx,
    Bundle.Trivial.fiberBundle_trivializationAt', Bundle.Trivial.linearMapAt_trivialization,
    LinearMap.id_coe, id_eq]

def RiemannianMetricGen.to02TensorGen {I : ModelWithCorners ℝ E H} {n : WithTop ℕ∞}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [hM : IsManifold I (n + 1) M]
    (g : _root_.Bundle.ContMDiffRiemannianMetric I n E (TangentSpace I : M -> Type _)) :
    Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (I := I) (M := M) (n := n) 2 := by
  unfold Tensor0SBundle.Tensor0SField
  letI := Tensor0SBundle.tensor0SBundleTopology
    (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
  let eCLM := _root_.DifferentialGeometry.Tensor.RSTensor.to02Tensor_eCLM_closedSurface_DifferentialGeometry_Tensor_RSTensor_Metric (E := E)
  let uCLM := _root_.DifferentialGeometry.Tensor.RSTensor.to02Tensor_uCLM_closedSurface_DifferentialGeometry_Tensor_RSTensor_Metric (E := E)
  let gI := _root_.Bundle.ContMDiffRiemannianMetric.inner g
  exact ⟨fun x => _root_.DifferentialGeometry.Tensor.RSTensor.to02TensorFiber_closedSurface_DifferentialGeometry_Tensor_RSTensor_Metric (I := I) (M := M) (gI x), by
    rcases hM with ⟨⟩
    let : IsManifold I (n + 1) M := IsManifold.mk
    have := Tensor0SBundle.tensor0SBundle_smooth
      (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := n) 2
    intro x₀
    refine (contMDiffAt_section (F := Tensor0SModel 2 ℝ E)
      (E := fun x : M => Tensor0SSpace 2 I x)
      (s := fun x => _root_.DifferentialGeometry.Tensor.RSTensor.to02TensorFiber_closedSurface_DifferentialGeometry_Tensor_RSTensor_Metric (I := I) (M := M) (gI x)) x₀).mpr ?_
    have hTriv := (contMDiffAt_section (F := E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun b : M => TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ)
        (s := gI) (x₀ := x₀)).mp (g.contMDiff.contMDiffAt (x := x₀))
    have hCurried :
        ContMDiffAt I 𝓘(ℝ, E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin 1 => E) ℝ) n
          (fun x => eCLM.comp ((trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
            (fun b : M => TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ) x₀
            ⟨x, gI x⟩).2)) x₀ := by
      exact (contMDiffAt_const (c := eCLM)).clm_comp hTriv
    refine (uCLM.contMDiffAt.comp x₀ hCurried).congr_of_eventuallyEq ?_
    filter_upwards [(trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt E (TangentSpace I) x₀)] with x hx
    exact _root_.DifferentialGeometry.Tensor.RSTensor.to02Tensor_trivialization_eq_closedSurface_DifferentialGeometry_Tensor_RSTensor_Metric (I := I) (M := M)
      (A := gI x) (x := x) (x₀ := x₀) hx⟩

end

end DifferentialGeometry.Tensor.RSTensor
