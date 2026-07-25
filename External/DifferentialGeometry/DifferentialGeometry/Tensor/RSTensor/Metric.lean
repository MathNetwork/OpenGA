


import DifferentialGeometry.Tensor.RSTensor.Field
import DifferentialGeometry.Tensor.RSTensor.Derivation.Contract
import DifferentialGeometry.Tensor.RSTensor.Defs
import DifferentialGeometry.Tensor.Multilinear.Fiber
import DifferentialGeometry.Tensor.Multilinear.Bundle
import DifferentialGeometry.Tensor.Alternating.Comp
import DifferentialGeometry.Tensor.Multilinear.Comp
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
import DifferentialGeometry.Tensor.Auxiliary.LinearIsometryContDiff
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Data.Bundle
import DifferentialGeometry.Tensor.Multilinear.Basis
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Topology.Algebra.Module.FiniteDimension
import DifferentialGeometry.Tensor.Multilinear.Curry
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import DifferentialGeometry.Tensor.Multilinear.Tensor
import DifferentialGeometry.Tensor.Multilinear.Field
import DifferentialGeometry.Tensor.Product.Basis
import DifferentialGeometry.Tensor.Product.Bundle
import DifferentialGeometry.Tensor.Product.Pretrivialization
import DifferentialGeometry.Tensor.Product.Defs
import DifferentialGeometry.Tensor.Product.HomEquiv
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Contraction
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.Algebra.Module.LinearMap
import DifferentialGeometry.Tensor.Alternating.Curry
import DifferentialGeometry.Tensor.Alternating.Flip
import DifferentialGeometry.Tensor.Multilinear.Flip
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Normed.Operator.Mul
import DifferentialGeometry.Tensor.Alternating.Congr
import Mathlib.LinearAlgebra.Alternating.Basic
import DifferentialGeometry.Tensor.Auxiliary.Shuffle.Decomposition
import DifferentialGeometry.Tensor.Auxiliary.Shuffle.Split
import Mathlib.GroupTheory.Perm.Option
import Mathlib.LinearAlgebra.Alternating.DomCoprod
import Mathlib.GroupTheory.Perm.Finite
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Group
import Mathlib.Analysis.Normed.Module.Alternating.Curry
import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin
import Mathlib.Tactic.Cases
import Mathlib.Topology.FiberBundle.Basic
import DifferentialGeometry.Tensor.Product.Fiber
import Mathlib.Topology.VectorBundle.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import DifferentialGeometry.Bundle.SectionRealized
import DifferentialGeometry.Tensor.RSTensor.Field
import DifferentialGeometry.Tensor.Auxiliary.PredualBasis
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Trace
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

set_option linter.style.longLine false














noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Tensor0SBundle

open scoped Manifold Topology Bundle ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable (n : WithTop ℕ∞)
variable (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]



abbrev RiemannianMetric_gen := Bundle.ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)

private noncomputable def to02Tensor_eCLM :
    (E →L[ℝ] ℝ) →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin 1 => E) ℝ :=
  (continuousMultilinearCurryFin1 ℝ E ℝ).symm.toContinuousLinearMap

private noncomputable def to02Tensor_uCLM :
    (E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin 1 => E) ℝ) →L[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ :=
  (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 2 => E) ℝ).symm.toContinuousLinearMap



private lemma to02Tensor_trivialization_eq {x₀ x : M}
    (A : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    (trivializationAt (Tensor0SBundle.Tensor0SModel 2 ℝ E)
      (fun y => Tensor0SBundle.Tensor0SSpace 2 I y) x₀
      ⟨x, ((to02Tensor_eCLM (E := E)).comp A).uncurryLeft⟩).2
      =
    (to02Tensor_uCLM (E := E)) ((to02Tensor_eCLM (E := E)).comp
      ((trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
      (fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) x₀ ⟨x, A⟩).2)) := by
  let e₀ := trivializationAt E (TangentSpace I) x₀
  ext m
  change (((e₀.continuousMultilinearMap ℝ 2)
      ⟨x, ((to02Tensor_eCLM (E := E)).comp
        A).uncurryLeft⟩).2) m = _
  rw [Bundle.Trivialization.continuousMultilinearMap_apply]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousLinearMap.uncurryLeft_apply]
  have hx' : x ∈ (trivializationAt (E →L[ℝ] ℝ)
      (fun y => TangentSpace I y →L[ℝ] ℝ) x₀).baseSet := by
    rw [hom_trivializationAt_baseSet]
    exact ⟨hx, by simp⟩
  rw [hom_trivializationAt_apply]
  change (to02Tensor_eCLM (E := E)) (A
      ((Trivialization.symmL ℝ e₀ x) (m 0)))
      (Fin.tail fun i => (Trivialization.symmL ℝ e₀ x) (m i)) =
    (to02Tensor_eCLM (E := E)) (ContinuousLinearMap.inCoordinates E (TangentSpace I) (E →L[ℝ] ℝ)
      (fun y => TangentSpace I y →L[ℝ] ℝ) x₀ x x₀ x
      A (m 0))
      (Fin.tail m)
  rw [ContinuousLinearMap.inCoordinates_eq hx hx']
  simp [to02Tensor_eCLM, hom_trivializationAt, Trivialization.continuousLinearMap_apply]
  rfl



theorem joint_to02 [IsManifold I ∞ M] {S : Set ℝ}
    (A : ∀ p : M × ℝ, TangentSpace I p.1 →L[ℝ] TangentSpace I p.1 →L[ℝ] ℝ)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
        p.1 (A p))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun x : M => Tensor0SBundle.Tensor0SSpace 2 I x) p.1
        (((continuousMultilinearCurryFin1 ℝ E ℝ).symm.toContinuousLinearMap.comp
          (A p)).uncurryLeft))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensor0SBundle_topology
    (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  let eCLM := to02Tensor_eCLM (E := E)
  let uCLM := to02Tensor_uCLM (E := E)
  have htriv := (Bundle.contMDiffWithinAt_totalSpace
    (F := E →L[ℝ] E →L[ℝ] ℝ)
    (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)).mp
      (hA p₀ hp₀)
  have hcurried : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin 1 => E) ℝ) ∞
      (fun p : M × ℝ => eCLM.comp
        ((trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
          p₀.1 ⟨p.1, A p⟩).2))
      ((Set.univ : Set M) ×ˢ S) p₀ :=
    (contMDiffWithinAt_const (c := eCLM)).clm_comp htriv.2
  have hconverted : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E) ∞
      (fun p : M × ℝ => uCLM (eCLM.comp
        ((trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
          p₀.1 ⟨p.1, A p⟩).2)))
      ((Set.univ : Set M) ×ˢ S) p₀ :=
    uCLM.contMDiff.contMDiffAt.comp_contMDiffWithinAt p₀ hcurried
  refine hconverted.congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in
        nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S),
        p.1 ∈ (trivializationAt E (TangentSpace I) p₀.1).baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        ((trivializationAt E (TangentSpace I) p₀.1).open_baseSet.mem_nhds
          (mem_baseSet_trivializationAt E (TangentSpace I) p₀.1))
    filter_upwards [hbase] with p hp
    exact to02Tensor_trivialization_eq (I := I) (M := M)
      (A := A p) hp
  · exact to02Tensor_trivialization_eq (I := I) (M := M)
      (A := A p₀) (mem_baseSet_trivializationAt E (TangentSpace I) p₀.1)




def RiemannianMetric_gen.to02Tensor_gen {I : ModelWithCorners ℝ E H} {n : WithTop ℕ∞}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [IsManifold I (n + 1) M]
    (g : Bundle.ContMDiffRiemannianMetric I n E (TangentSpace I : M -> Type _)) :
    Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (I := I) (M := M) (n := n) 2 := by
  unfold Tensor0SBundle.Tensor0SField
  letI := Tensor0SBundle.tensor0SBundle_topology
    (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
  let eCLM := to02Tensor_eCLM (E := E)
  let uCLM := to02Tensor_uCLM (E := E)
  let gI := Bundle.ContMDiffRiemannianMetric.inner g
  exact ⟨fun x => (eCLM.comp (gI x)).uncurryLeft, by
    haveI := Tensor0SBundle.tensor0SBundle_smooth
      (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := n) 2
    intro x₀; rw [contMDiffAt_section]
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
    exact to02Tensor_trivialization_eq (I := I) (M := M)
      (A := gI x) (x := x) (x₀ := x₀) hx⟩

@[simp]
theorem RiemannianMetric_gen.to02Tensor_apply {I : ModelWithCorners ℝ E H} {n : WithTop ℕ∞}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [IsManifold I (n + 1) M]
    (g : Bundle.ContMDiffRiemannianMetric I n E (TangentSpace I : M -> Type _))
    (x : M) (v : Fin 2 -> TangentSpace I x) :
    RiemannianMetric_gen.to02Tensor_gen (I := I) (n := n) g x v =
      (Bundle.ContMDiffRiemannianMetric.inner g) x (v 0) (v 1) := by
  simp [RiemannianMetric_gen.to02Tensor_gen, to02Tensor_eCLM]
  change ((Bundle.ContMDiffRiemannianMetric.inner g) x (v 0)) (Fin.tail v 0) =
    ((Bundle.ContMDiffRiemannianMetric.inner g) x (v 0)) (v 1)
  simp [Fin.tail]

end
