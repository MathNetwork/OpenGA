import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.FixedChart.Models
import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.Connection.Tangent
import DifferentialGeometry.Tensor.Multilinear.BundleSmoothEvalRealized









set_option autoImplicit false

namespace Tensor0SBundle

open Bundle Set TensorLieDeriv
open scoped BigOperators Manifold ContDiff Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]
set_option backward.isDefEq.respectTransparency false in
theorem tensor0SConstInChart_contMDiffAt_of_mem {r : ℕ}
    (x₀ : M) (β : Tensor0SModel r 𝕜 E) {x : M}
    (hx : x ∈ (trivializationAt (Tensor0SModel r 𝕜 E)
      (fun p : M => Tensor0SSpace r I p) x₀).baseSet) :
    ContMDiffAt I (I.prod 𝓘(𝕜, Tensor0SModel r 𝕜 E)) (∞ : WithTop ℕ∞)
      (fun p : M =>
        (⟨p, Tensor0SSpace.constInChart
          (𝕜 := 𝕜) (I := I) (M := M) r x₀ β p⟩ :
          TotalSpace (Tensor0SModel r 𝕜 E)
            (fun p : M => Tensor0SSpace r I p))) x := by
  let e := trivializationAt (Tensor0SModel r 𝕜 E)
    (fun p : M => Tensor0SSpace r I p) x₀
  have hx' : x ∈ e.baseSet := by simpa [e] using hx
  refine (e.contMDiffAt_section_iff hx').mpr ?_
  have hconst : ContMDiffAt I 𝓘(𝕜, Tensor0SModel r 𝕜 E) (∞ : WithTop ℕ∞)
      (fun _ : M => β) x := contMDiffAt_const
  refine hconst.congr_of_eventuallyEq ?_
  filter_upwards [e.open_baseSet.mem_nhds hx'] with p hp
  have hcoe : ⇑(e.linearMapAt 𝕜 p) = fun z => (e ⟨p, z⟩).2 :=
    e.coe_linearMapAt_of_mem (R := 𝕜) hp
  change (e ⟨p, e.symmL 𝕜 p β⟩).2 = β
  simpa [Bundle.Trivialization.continuousLinearMapAt_apply, hcoe] using
    (e.continuousLinearMapAt_symmL (R := 𝕜) hp β)

set_option backward.isDefEq.respectTransparency false in
theorem tensor0SConstInChart_contMDiffAt {r : ℕ}
    (x₀ : M) (β : Tensor0SModel r 𝕜 E) :
    ContMDiffAt I (I.prod 𝓘(𝕜, Tensor0SModel r 𝕜 E)) (∞ : WithTop ℕ∞)
      (fun p : M =>
        (⟨p, Tensor0SSpace.constInChart
          (𝕜 := 𝕜) (I := I) (M := M) r x₀ β p⟩ :
          TotalSpace (Tensor0SModel r 𝕜 E)
            (fun p : M => Tensor0SSpace r I p))) x₀ := by
  exact tensor0SConstInChart_contMDiffAt_of_mem
    (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
    x₀ β (mem_baseSet_trivializationAt
      (Tensor0SModel r 𝕜 E) (fun p : M => Tensor0SSpace r I p) x₀)

set_option backward.isDefEq.respectTransparency false in
private theorem tensor0SModelInChart_contDiffWithinAt_center_of_contMDiffAt {r : ℕ}
    (β : (x : M) -> Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) r x)
    (x₀ : M)
    (hβ : ContMDiffAt I (I.prod 𝓘(𝕜, Tensor0SModel r 𝕜 E))
      (∞ : WithTop ℕ∞)
      (fun p : M =>
        (⟨p, β p⟩ :
          TotalSpace (Tensor0SModel r 𝕜 E)
            (fun p : M => Tensor0SSpace r I p))) x₀) :
    ContDiffWithinAt 𝕜 (∞ : WithTop ℕ∞)
      (tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
        (M := M) r x₀ β)
      (Set.range I) (extChartAt I x₀ x₀) := by
  let e := trivializationAt (Tensor0SModel r 𝕜 E)
    (fun p : M => Tensor0SSpace r I p) x₀
  have hx : x₀ ∈ e.baseSet := by
    simpa [e] using
      (mem_baseSet_trivializationAt
        (Tensor0SModel r 𝕜 E) (fun p : M => Tensor0SSpace r I p) x₀)
  have hcoord :
      ContMDiffAt I 𝓘(𝕜, Tensor0SModel r 𝕜 E) (∞ : WithTop ℕ∞)
        (fun p : M => (e ⟨p, β p⟩).2) x₀ :=
    (e.contMDiffAt_section_iff hx).mp hβ
  have hsymm :
      ContMDiffWithinAt 𝓘(𝕜, E) I (∞ : WithTop ℕ∞)
        (extChartAt I x₀).symm (Set.range I) (extChartAt I x₀ x₀) := by
    simpa using
      contMDiffWithinAt_extChartAt_symm_range_self
        (I := I) (n := (∞ : WithTop ℕ∞)) x₀
  have hcenter :
      (extChartAt I x₀).symm (extChartAt I x₀ x₀) = x₀ :=
    (extChartAt I x₀).left_inv (mem_extChartAt_source (I := I) x₀)
  have hcoord_center :
      ContMDiffAt I 𝓘(𝕜, Tensor0SModel r 𝕜 E) (∞ : WithTop ℕ∞)
        (fun p : M => (e ⟨p, β p⟩).2)
        ((extChartAt I x₀).symm (extChartAt I x₀ x₀)) := by
    simpa [hcenter] using hcoord
  have hfixed :
      ContMDiffWithinAt 𝓘(𝕜, E) 𝓘(𝕜, Tensor0SModel r 𝕜 E)
        (∞ : WithTop ℕ∞)
        ((fun p : M => (e ⟨p, β p⟩).2) ∘ (extChartAt I x₀).symm)
        (Set.range I) (extChartAt I x₀ x₀) :=
    hcoord_center.comp_contMDiffWithinAt (x := extChartAt I x₀ x₀) hsymm
  have heq :
      tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
        (M := M) r x₀ β
        =ᶠ[𝓝[Set.range I] (extChartAt I x₀ x₀)]
      (fun p : M => (e ⟨p, β p⟩).2) ∘ (extChartAt I x₀).symm := by
    filter_upwards [extChartAt_target_mem_nhdsWithin (I := I) x₀] with y hy
    simp [tensor0SModelInChart, tensor0SModelAt, e]
  have hmdiff :
      ContMDiffWithinAt 𝓘(𝕜, E) 𝓘(𝕜, Tensor0SModel r 𝕜 E)
        (∞ : WithTop ℕ∞)
        (tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
          (M := M) r x₀ β)
        (Set.range I) (extChartAt I x₀ x₀) := by
    refine hfixed.congr_of_eventuallyEq heq ?_
    simp [tensor0SModelInChart, tensor0SModelAt, e]
  exact hmdiff.contDiffWithinAt

set_option backward.isDefEq.respectTransparency false in
theorem tensor0SModelInChart_differentiableWithinAt_center_of_contMDiffAt {r : ℕ}
    (β : (x : M) -> Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) r x)
    (x₀ : M)
    (hβ : ContMDiffAt I (I.prod 𝓘(𝕜, Tensor0SModel r 𝕜 E))
      (∞ : WithTop ℕ∞)
      (fun p : M =>
        (⟨p, β p⟩ :
          TotalSpace (Tensor0SModel r 𝕜 E)
            (fun p : M => Tensor0SSpace r I p))) x₀) :
    DifferentiableWithinAt 𝕜
      (tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
        (M := M) r x₀ β)
      (Set.range I) (extChartAt I x₀ x₀) :=
  (tensor0SModelInChart_contDiffWithinAt_center_of_contMDiffAt
    (I := I) β x₀ hβ).differentiableWithinAt (by simp)

set_option backward.isDefEq.respectTransparency false in
theorem tensorRS_eval_contMDiffAt {r s : ℕ}
    (T : (p : M) -> TensorRSSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) r s p)
    (β : (p : M) -> Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) r p)
    (V : Fin s -> (p : M) -> TangentSpace I p) (x₀ : M)
    (hT : ContMDiffAt I (I.prod 𝓘(𝕜, TensorRSModel r s 𝕜 E))
      (∞ : WithTop ℕ∞)
      (fun p : M =>
        (⟨p, T p⟩ :
          TotalSpace (TensorRSModel r s 𝕜 E)
            (fun p : M => TensorRSSpace r s I p))) x₀)
    (hβ : ContMDiffAt I (I.prod 𝓘(𝕜, Tensor0SModel r 𝕜 E))
      (∞ : WithTop ℕ∞)
      (fun p : M =>
        (⟨p, β p⟩ :
          TotalSpace (Tensor0SModel r 𝕜 E)
            (fun p : M => Tensor0SSpace r I p))) x₀)
    (hV : ∀ a : Fin s,
      ContMDiffAt I (I.prod 𝓘(𝕜, E)) (∞ : WithTop ℕ∞)
        (fun p : M =>
          (⟨p, V a p⟩ : TotalSpace E (TangentSpace I : M -> Type _))) x₀) :
    ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
      (fun p : M => (T p (β p)) (fun a : Fin s => V a p)) x₀ := by
  have hApplied :
      ContMDiffAt I (I.prod 𝓘(𝕜, Tensor0SModel s 𝕜 E)) (∞ : WithTop ℕ∞)
        (fun p : M =>
          (⟨p, T p (β p)⟩ :
            TotalSpace (Tensor0SModel s 𝕜 E)
              (fun p : M => Tensor0SSpace s I p))) x₀ :=
    ContMDiffAt.clm_bundle_apply (𝕜 := 𝕜) (n := (∞ : WithTop ℕ∞))
      (F₁ := Tensor0SModel r 𝕜 E) (F₂ := Tensor0SModel s 𝕜 E)
      (E₁ := fun p : M => Tensor0SSpace r I p)
      (E₂ := fun p : M => Tensor0SSpace s I p)
      (IM := I) (IB := I) (b := id)
      (ϕ := fun p : M => T p) (v := fun p : M => β p) hT hβ
  have hEval := TensorMultilinear.contMDiffAt_section_apply_gen
    (I := I) (M := M) (n := s) (x₀ := x₀)
    (T := fun p : M => T p (β p)) hApplied
    (v := V) hV
  simpa [Tensor0SSpace.toModel, tensor0SSpace_continuousLinearEquiv_apply] using hEval

set_option backward.isDefEq.respectTransparency false in





theorem tensor0S_eval_tangentConstInChart_contMDiffAt
    {s : ℕ}
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (x₀ : M) (slots : Fin s -> Fin (Module.finrank 𝕜 E)) :
    ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
      (fun y : M =>
        α y
          (fun a : Fin s =>
            tangentConstInChart (𝕜 := 𝕜) (I := I) x₀
              ((Module.finBasis 𝕜 E) (slots a)) y))
      x₀ := by
  let e := trivializationAt E (TangentSpace I : M -> Type _) x₀
  have hx₀ : x₀ ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x₀
  have hα_top := α.contMDiff x₀
  have hα := hα_top.of_le
    (by simp : (∞ : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  have hframe :
      ∀ a : Fin s,
        ContMDiffAt I (I.prod 𝓘(𝕜, E)) (∞ : WithTop ℕ∞)
          (fun y : M =>
            (⟨y,
              tangentConstInChart (𝕜 := 𝕜) (I := I) x₀
                ((Module.finBasis 𝕜 E) (slots a)) y⟩ :
              TotalSpace E (TangentSpace I : M -> Type _))) x₀ := by
    intro a
    have hconst_on :
        CMDiff[e.baseSet] (∞ : WithTop ℕ∞)
          (T% (tangentConstInChart (𝕜 := 𝕜) (I := I) x₀
            ((Module.finBasis 𝕜 E) (slots a)) :
            (p : M) -> TangentSpace I p)) := by
      simpa [e] using
        (tangentConstInChart_contMDiffOn_baseSet
          (𝕜 := 𝕜) (I := I) (M := M) (n := (∞ : WithTop ℕ∞))
          x₀ ((Module.finBasis 𝕜 E) (slots a)))
    exact (hconst_on x₀ hx₀).contMDiffAt (e.open_baseSet.mem_nhds hx₀)
  have hEval := TensorMultilinear.contMDiffAt_section_apply_gen
    (I := I) (M := M) (n := s) (x₀ := x₀)
    (T := fun y : M => α y) hα
    (v := fun a : Fin s =>
      tangentConstInChart (𝕜 := 𝕜) (I := I) x₀
        ((Module.finBasis 𝕜 E) (slots a)))
    (hv := hframe)
  simpa [Tensor0SSpace.toModel, tensor0SSpace_continuousLinearEquiv_apply] using hEval


end Tensor0SBundle
