








import DifferentialGeometry.Bundle.Equiv
import Mathlib.Topology.VectorBundle.Basic
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Analysis.Normed.Module.FiniteDimension
import DifferentialGeometry.Bundle.Zero
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import DifferentialGeometry.Bundle.Frame
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set FiberBundle
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]









theorem cotangentCov_clmSection_smooth_aux
    {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [FiniteDimensional ℝ F₂]
    {V₂ : M → Type*} [∀ x, AddCommGroup (V₂ x)] [∀ x, Module ℝ (V₂ x)]
    [TopologicalSpace (TotalSpace F₂ V₂)] [∀ x, TopologicalSpace (V₂ x)]
    [FiberBundle F₂ V₂] [VectorBundle ℝ F₂ V₂]
    [ContMDiffVectorBundle ∞ F₂ V₂ I]
    [∀ x, IsTopologicalAddGroup (V₂ x)] [∀ x, ContinuousSMul ℝ (V₂ x)]
    [SigmaCompactSpace M] [T2Space M]
    (φ : ∀ x : M, TangentSpace I x →L[ℝ] V₂ x)
    (h : ∀ (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯),
      ContMDiff I (I.prod 𝓘(ℝ, F₂)) ∞
        (fun x => TotalSpace.mk' F₂ (E := V₂) x (φ x (Y x)))) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] F₂)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] F₂)
        (E := fun x : M => TangentSpace I x →L[ℝ] V₂ x) x (φ x)) := by
  intro x₀

  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩


  apply contMDiffAt_clm_of_pointwise (IB := I) (X := M)
  intro v

  let e₁ := trivializationAt E (TangentSpace I : M → Type _) x₀
  let e₂ := trivializationAt F₂ V₂ x₀
  let b := Module.finBasis ℝ E
  have he₁ : x₀ ∈ e₁.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x₀
  have he₂ : x₀ ∈ e₂.baseSet := mem_baseSet_trivializationAt F₂ V₂ x₀

  have hframe := e₁.isLocalFrameOn_localFrame_baseSet I (⊤ : ℕ∞) b
  obtain ⟨Y, hY⟩ := hframe.exists_contMDiffSection_eqOn_nhd e₁.open_baseSet he₁

  have hφY : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, F₂)) ∞
      (fun x => TotalSpace.mk' F₂ (E := V₂) x (φ x (Y i x))) := fun i => h (Y i)

  have hφY_fiber : ∀ i, ContMDiffAt I 𝓘(ℝ, F₂) ∞
      (fun x => (e₂ ⟨x, φ x (Y i x)⟩).2) x₀ := fun i => by
    have hi := (contMDiffAt_section (F := F₂) (E := V₂) x₀).mp ((hφY i) x₀)
    simpa [e₂, trivializationAt] using hi

  have hsum : ContMDiffAt I 𝓘(ℝ, F₂) ∞
      (fun x => ∑ i, b.repr v i • (e₂ ⟨x, φ x (Y i x)⟩).2) x₀ := by
    apply ContMDiffAt.sum
    intro i _
    exact (contMDiffAt_const (c := (b.repr v i : ℝ))).smul (hφY_fiber i)

  refine hsum.congr_of_eventuallyEq ?_
  have h_base₁ : ∀ᶠ x in 𝓝 x₀, x ∈ e₁.baseSet :=
    e₁.open_baseSet.mem_nhds he₁
  have h_base₂ : ∀ᶠ x in 𝓝 x₀, x ∈ e₂.baseSet :=
    e₂.open_baseSet.mem_nhds he₂
  filter_upwards [h_base₁, h_base₂, hY] with x hx₁ hx₂ hYx


  have hv_decomp : v = ∑ i, b.repr v i • b i := (b.sum_repr v).symm
  have h_inCoord :
      (ContinuousLinearMap.inCoordinates E (TangentSpace I) F₂ V₂ x₀ x x₀ x (φ x)) v =
      e₂.continuousLinearMapAt ℝ x ((φ x) (e₁.symmL ℝ x v)) := rfl
  rw [h_inCoord]
  have h₁ : e₁.symmL ℝ x v = ∑ i, (b.repr v) i • e₁.symmL ℝ x (b i) := by
    conv_lhs => rw [hv_decomp]
    rw [map_sum]; congr 1; ext i; rw [map_smul]
  have h₂ : (φ x) (∑ i, (b.repr v) i • e₁.symmL ℝ x (b i)) =
      ∑ i, (b.repr v) i • (φ x) (e₁.symmL ℝ x (b i)) := by
    rw [map_sum]; congr 1; ext i; rw [map_smul]
  have h₃ : e₂.continuousLinearMapAt ℝ x
        (∑ i, (b.repr v) i • (φ x) (e₁.symmL ℝ x (b i))) =
      ∑ i, (b.repr v) i • e₂.continuousLinearMapAt ℝ x ((φ x) (e₁.symmL ℝ x (b i))) := by
    rw [map_sum]; congr 1; ext i; rw [map_smul]
  rw [h₁, h₂, h₃]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  congr 1

  have h_lf : e₁.symmL ℝ x (b i) = (Y i) x := by
    rw [hYx i]
    rw [Trivialization.localFrame_apply_of_mem_baseSet (hx := hx₁)]
    simp [Trivialization.basisAt]
  rw [h_lf]

  change (Trivialization.continuousLinearMapAt ℝ e₂ x) ((φ x) ((Y i) x)) = _
  rw [show ⇑(e₂.continuousLinearMapAt ℝ x) = ⇑(e₂.linearMapAt ℝ x) from rfl,
    e₂.coe_linearMapAt_of_mem hx₂]

end DifferentialGeometry
