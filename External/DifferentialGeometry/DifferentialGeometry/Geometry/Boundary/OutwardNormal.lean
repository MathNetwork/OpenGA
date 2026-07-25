import DifferentialGeometry.Geometry.Boundary.InducedMetric
import DifferentialGeometry.Geometry.Operator.Gradient
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.VectorBundle.Tangent


noncomputable section

open Set Function Topology Bundle Manifold MeasureTheory
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem
namespace WithBoundary

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [hI : HasSmoothBoundary E H I] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure

abbrev inwardCoordE : E := hI.inwardCoordE

private def PhiLocal (I : ModelWithCorners ℝ E H) [hI : HasSmoothBoundary E H I] :
    hI.boundaryE → E :=
  (I : H → E) ∘ hI.inclH ∘ hI.boundaryI.symm

private lemma infty_ne_zero_withTopENat' : (∞ : WithTop ℕ∞) ≠ 0 := by
  intro h
  have h' : ((⊤ : ℕ∞) : WithTop ℕ∞) = ((0 : ℕ∞) : WithTop ℕ∞) := h
  exact ENat.top_ne_zero (WithTop.coe_eq_coe.mp h')

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private lemma dincl_eq_fderiv_PhiLocal (x : BoundaryManifold I M)
    [Nonempty hI.boundaryH] :
    (boundaryInclusionMfderiv x : hI.boundaryE →L[ℝ] E) =
      fderiv ℝ (PhiLocal I) (extChartAt hI.boundaryI x x) := by
  unfold boundaryInclusionMfderiv
  have h_diff : MDifferentiableAt hI.boundaryI I (boundaryInclusion I M) x :=
    (boundaryInclusion_contMDiff (I := I) (M := M)).mdifferentiableAt
      infty_ne_zero_withTopENat'
  rw [h_diff.mfderiv]
  have h_range : Set.range hI.boundaryI = Set.univ := hI.boundaryI.range_eq_univ
  rw [h_range, fderivWithin_univ]
  have h_chart_eq :
      chartAt hI.boundaryH x = BoundaryManifold.boundaryChart (I := I) x := by
    change BoundaryManifold.defaultBoundaryChart (I := I) x =
      BoundaryManifold.boundaryChart (I := I) x
    exact BoundaryManifold.defaultBoundaryChart_eq_boundaryChart (I := I) x
  have h_eq : (writtenInExtChartAt hI.boundaryI I x (boundaryInclusion I M))
      =ᶠ[𝓝 (extChartAt hI.boundaryI x x)] PhiLocal I := by
    have h_target_mem : (extChartAt hI.boundaryI x).target ∈
        𝓝 (extChartAt hI.boundaryI x x) :=
      extChartAt_target_mem_nhds (I := hI.boundaryI) (M := BoundaryManifold I M) x
    filter_upwards [h_target_mem] with e he
    have he_target_chart : hI.boundaryI.symm e ∈ (chartAt hI.boundaryH x).target := by
      rw [extChartAt_target] at he
      exact he.1
    rw [h_chart_eq] at he_target_chart
    have h_extChart_symm_val :
        (((extChartAt hI.boundaryI x).symm e : BoundaryManifold I M) : M) =
          (chartAt H (x : M)).symm (hI.inclH (hI.boundaryI.symm e)) := by
      change (((chartAt hI.boundaryH x).symm (hI.boundaryI.symm e) :
          BoundaryManifold I M) : M) = _
      rw [h_chart_eq]
      exact BoundaryManifold.boundaryChartInvFun_val_of_mem_target
        (I := I) x he_target_chart
    change writtenInExtChartAt hI.boundaryI I x (boundaryInclusion I M) e =
      PhiLocal I e
    unfold writtenInExtChartAt
    simp only [Function.comp_apply]
    change extChartAt I (boundaryInclusion I M x)
        (((extChartAt hI.boundaryI x).symm e : BoundaryManifold I M) : M) =
      PhiLocal I e
    rw [h_extChart_symm_val]
    change I (chartAt H (x : M) ((chartAt H (x : M)).symm
      (hI.inclH (hI.boundaryI.symm e)))) = PhiLocal I e
    rw [(chartAt H (x : M)).right_inv he_target_chart]
    rfl
  rw [Filter.EventuallyEq.fderiv_eq h_eq]

def inwardCoord (x : BoundaryManifold I M) : TangentSpace I (x : M) :=
  (trivializationAt E (TangentSpace I) (x : M)).symm (x : M) hI.inwardCoordE

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma inwardCoord_eq (x : BoundaryManifold I M) :
    inwardCoord (M := M) x = hI.inwardCoordE := by
  have h_symmL : inwardCoord (M := M) x =
      ((trivializationAt E (TangentSpace I) (x : M)).symmL ℝ (x : M)) hI.inwardCoordE := rfl
  rw [h_symmL,
      TangentBundle.symmL_trivializationAt
        (x₀ := (x : M)) (x := (x : M)) (mem_chart_source H _),
      mfderivWithin_range_extChartAt_symm]
  rfl

def inwardCoordAt (α₀ : BoundaryManifold I M) (x : BoundaryManifold I M) :
    TangentSpace I (x : M) :=
  (trivializationAt E (TangentSpace I) (α₀ : M)).symm (x : M) hI.inwardCoordE

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
@[simp] lemma inwardCoordAt_self (x : BoundaryManifold I M) :
    inwardCoordAt (M := M) x x = inwardCoord (M := M) x := rfl

def normalSubspace (g : SmoothRiemannianMetric I M) (x : BoundaryManifold I M) :
    Submodule ℝ (TangentSpace I (x : M)) where
  carrier := {v : TangentSpace I (x : M) | ∀ w : hI.boundaryE,
    g.inner (x : M) v (boundaryInclusionMfderiv (M := M) x w) = 0}
  zero_mem' := by
    intro w
    simp
  add_mem' := by
    intro v₁ v₂ h₁ h₂ w
    rw [map_add, ContinuousLinearMap.add_apply, h₁ w, h₂ w, add_zero]
  smul_mem' := by
    intro c v hv w
    rw [map_smul, ContinuousLinearMap.smul_apply, hv w, smul_zero]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
@[simp] lemma mem_normalSubspace_iff
    (g : SmoothRiemannianMetric I M) (x : BoundaryManifold I M)
    (v : TangentSpace I (x : M)) :
    v ∈ normalSubspace (M := M) g x ↔
      ∀ w : hI.boundaryE, g.inner (x : M) v (boundaryInclusionMfderiv (M := M) x w) = 0 :=
  Iff.rfl

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma inner_normalSubspace_dincl
    (g : SmoothRiemannianMetric I M) (x : BoundaryManifold I M)
    {v : TangentSpace I (x : M)} (hv : v ∈ normalSubspace (M := M) g x)
    (w : hI.boundaryE) :
    g.inner (x : M) v (boundaryInclusionMfderiv (M := M) x w) = 0 := hv w

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma inner_dincl_normalSubspace
    (g : SmoothRiemannianMetric I M) (x : BoundaryManifold I M)
    {v : TangentSpace I (x : M)} (hv : v ∈ normalSubspace (M := M) g x)
    (w : hI.boundaryE) :
    g.inner (x : M) (boundaryInclusionMfderiv (M := M) x w) v = 0 := by
  rw [g.symm (x : M) _ v]; exact hv w

variable (g : SmoothRiemannianMetric I M) (x : BoundaryManifold I M)

def boundaryFunOfInward : hI.boundaryE →ₗ[ℝ] ℝ where
  toFun w := g.inner (x : M) (inwardCoord (M := M) x) (boundaryInclusionMfderiv (M := M) x w)
  map_add' u v := by
    rw [ContinuousLinearMap.map_add (boundaryInclusionMfderiv (M := M) x) u v]
    exact ContinuousLinearMap.map_add (g.inner (x : M) (inwardCoord (M := M) x)) _ _
  map_smul' c v := by
    rw [ContinuousLinearMap.map_smul (boundaryInclusionMfderiv (M := M) x) c v]
    exact ContinuousLinearMap.map_smul (g.inner (x : M) (inwardCoord (M := M) x)) _ _

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
@[simp] lemma boundaryFunOfInward_apply (w : hI.boundaryE) :
    boundaryFunOfInward (M := M) g x w =
      g.inner (x : M) (inwardCoord (M := M) x) (boundaryInclusionMfderiv (M := M) x w) := rfl

private def boundaryFlatLinear : hI.boundaryE →ₗ[ℝ] (hI.boundaryE →ₗ[ℝ] ℝ) where
  toFun u := (inducedMetricInner (M := M) g x u).toLinearMap
  map_add' u v := by
    ext w
    change inducedMetricInner (M := M) g x (u + v) w =
      inducedMetricInner (M := M) g x u w + inducedMetricInner (M := M) g x v w
    rw [map_add, ContinuousLinearMap.add_apply]
  map_smul' c v := by
    ext w
    change inducedMetricInner (M := M) g x (c • v) w =
      c • inducedMetricInner (M := M) g x v w
    rw [map_smul, ContinuousLinearMap.smul_apply]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
@[simp] private lemma boundaryFlatLinear_apply (u v : hI.boundaryE) :
    boundaryFlatLinear (M := M) g x u v = inducedMetricInner (M := M) g x u v := rfl

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private lemma boundaryFlatLinear_injective :
    Function.Injective (boundaryFlatLinear (M := M) g x) := by
  intro u v hpoint
  by_contra hne
  have huv_ne : u - v ≠ 0 := sub_ne_zero.mpr hne
  have hpos : 0 < inducedMetricInner (M := M) g x (u - v) (u - v) :=
    inducedMetricInner_pos (M := M) g x (u - v) huv_ne
  have hzero : ∀ z : hI.boundaryE, inducedMetricInner (M := M) g x (u - v) z = 0 := by
    intro z
    have h := congrArg (fun L : hI.boundaryE →ₗ[ℝ] ℝ => L z) hpoint
    simp only [boundaryFlatLinear_apply] at h
    have hsub : inducedMetricInner (M := M) g x (u - v) z =
        inducedMetricInner (M := M) g x u z - inducedMetricInner (M := M) g x v z := by
      rw [map_sub, ContinuousLinearMap.sub_apply]
    rw [hsub, sub_eq_zero]; exact h
  exact (lt_irrefl 0) (hzero (u - v) ▸ hpos)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private lemma boundaryFlatLinear_finrank_eq :
    Module.finrank ℝ hI.boundaryE = Module.finrank ℝ (hI.boundaryE →ₗ[ℝ] ℝ) :=
  Subspace.dual_finrank_eq.symm

private def boundaryFlatMap : hI.boundaryE ≃ₗ[ℝ] (hI.boundaryE →ₗ[ℝ] ℝ) :=
  LinearMap.linearEquivOfInjective
    (boundaryFlatLinear (M := M) g x)
    (boundaryFlatLinear_injective (M := M) g x)
    (boundaryFlatLinear_finrank_eq (E := E) (H := H) (I := I))
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
@[simp] private lemma boundaryFlatMap_apply (u v : hI.boundaryE) :
    boundaryFlatMap (M := M) g x u v = inducedMetricInner (M := M) g x u v := rfl
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private lemma boundaryFlatMap_apply_symm
    (α : hI.boundaryE →ₗ[ℝ] ℝ) (w : hI.boundaryE) :
    inducedMetricInner (M := M) g x ((boundaryFlatMap (M := M) g x).symm α) w = α w := by
  have h := (boundaryFlatMap (M := M) g x).apply_symm_apply α
  have hh : boundaryFlatMap (M := M) g x ((boundaryFlatMap (M := M) g x).symm α) w = α w :=
    congrArg (fun L : hI.boundaryE →ₗ[ℝ] ℝ => L w) h
  rw [boundaryFlatMap_apply] at hh
  exact hh

def boundaryComponentOfInward : hI.boundaryE :=
  (boundaryFlatMap (M := M) g x).symm (boundaryFunOfInward (M := M) g x)
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma inducedMetricInner_boundaryComponentOfInward (w : hI.boundaryE) :
    inducedMetricInner (M := M) g x (boundaryComponentOfInward (M := M) g x) w =
      g.inner (x : M) (inwardCoord (M := M) x) (boundaryInclusionMfderiv (M := M) x w) := by
  unfold boundaryComponentOfInward
  have := boundaryFlatMap_apply_symm (M := M) g x (boundaryFunOfInward (M := M) g x) w
  rw [this]
  rfl

def inwardTangentialPart : TangentSpace I (x : M) :=
  boundaryInclusionMfderiv (M := M) x (boundaryComponentOfInward (M := M) g x)
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
@[simp] lemma inwardTangentialPart_def :
    inwardTangentialPart (M := M) g x =
      boundaryInclusionMfderiv (M := M) x (boundaryComponentOfInward (M := M) g x) := rfl

def outwardDir : TangentSpace I (x : M) :=
  inwardTangentialPart (M := M) g x - inwardCoord (M := M) x
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
@[simp] lemma outwardDir_def :
    outwardDir (M := M) g x =
      inwardTangentialPart (M := M) g x - inwardCoord (M := M) x := rfl
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem outwardDir_mem_normalSubspace :
    outwardDir (M := M) g x ∈ normalSubspace (M := M) g x := by
  intro w
  rw [outwardDir_def]
  have hsub : g.inner (x : M)
        (inwardTangentialPart (M := M) g x - inwardCoord (M := M) x)
        (boundaryInclusionMfderiv (M := M) x w) =
      g.inner (x : M) (inwardTangentialPart (M := M) g x) (boundaryInclusionMfderiv (M := M) x w) -
      g.inner (x : M) (inwardCoord (M := M) x) (boundaryInclusionMfderiv (M := M) x w) := by
    rw [map_sub, ContinuousLinearMap.sub_apply]
  rw [hsub]
  have h1 : g.inner (x : M) (inwardTangentialPart (M := M) g x) (boundaryInclusionMfderiv (M := M) x w) =
      inducedMetricInner (M := M) g x (boundaryComponentOfInward (M := M) g x) w := by
    rw [inducedMetricInner_apply, inwardTangentialPart_def]
  rw [h1]
  rw [inducedMetricInner_boundaryComponentOfInward (M := M) g x w]
  ring
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma g_inner_outwardDir_inwardCoord :
    g.inner (x : M) (outwardDir (M := M) g x) (inwardCoord (M := M) x) =
      g.inner (x : M) (inwardTangentialPart (M := M) g x) (inwardCoord (M := M) x) -
      g.inner (x : M) (inwardCoord (M := M) x) (inwardCoord (M := M) x) := by
  rw [outwardDir_def, map_sub, ContinuousLinearMap.sub_apply]
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma g_inner_inwardCoord_outwardDir :
    g.inner (x : M) (inwardCoord (M := M) x) (outwardDir (M := M) g x) =
      g.inner (x : M) (inwardTangentialPart (M := M) g x) (inwardCoord (M := M) x) -
      g.inner (x : M) (inwardCoord (M := M) x) (inwardCoord (M := M) x) := by
  rw [g.symm (x : M) (inwardCoord (M := M) x) (outwardDir (M := M) g x)]
  exact g_inner_outwardDir_inwardCoord (M := M) g x
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma g_inner_outwardDir_outwardDir :
    g.inner (x : M) (outwardDir (M := M) g x) (outwardDir (M := M) g x) =
      g.inner (x : M) (inwardCoord (M := M) x) (inwardCoord (M := M) x) -
      g.inner (x : M) (inwardTangentialPart (M := M) g x) (inwardCoord (M := M) x) := by
  have h_orth : g.inner (x : M) (outwardDir (M := M) g x)
      (inwardTangentialPart (M := M) g x) = 0 := by
    have hmem : outwardDir (M := M) g x ∈ normalSubspace (M := M) g x :=
      outwardDir_mem_normalSubspace (M := M) g x
    rw [inwardTangentialPart_def]
    exact hmem (boundaryComponentOfInward (M := M) g x)
  have hdecomp : g.inner (x : M) (outwardDir (M := M) g x) (outwardDir (M := M) g x) =
      g.inner (x : M) (outwardDir (M := M) g x) (inwardTangentialPart (M := M) g x) -
      g.inner (x : M) (outwardDir (M := M) g x) (inwardCoord (M := M) x) := by
    change g.inner (x : M) (outwardDir (M := M) g x)
        (inwardTangentialPart (M := M) g x - inwardCoord (M := M) x) =
      g.inner (x : M) (outwardDir (M := M) g x) (inwardTangentialPart (M := M) g x) -
      g.inner (x : M) (outwardDir (M := M) g x) (inwardCoord (M := M) x)
    exact ContinuousLinearMap.map_sub _ _ _
  rw [hdecomp, h_orth, zero_sub]
  rw [g_inner_outwardDir_inwardCoord (M := M) g x]
  ring

def InwardCoordTransverse (x : BoundaryManifold I M) : Prop :=
  inwardCoord (M := M) x ∉ LinearMap.range (boundaryInclusionMfderiv (M := M) x).toLinearMap
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem InwardCoordTransverse_of_HasSmoothBoundary
    (x : BoundaryManifold I M) :
    InwardCoordTransverse (M := M) x := by
  by_cases hN : Nonempty hI.boundaryH
  · haveI := hN
    intro hmem
    have hmem' : inwardCoord (M := M) x ∈ Set.range (boundaryInclusionMfderiv (M := M) x) := by
      rcases hmem with ⟨w, hw⟩
      exact ⟨w, hw⟩
    rw [inwardCoord_eq, dincl_eq_fderiv_PhiLocal (I := I) (M := M) x] at hmem'
    exact hI.inwardCoordE_transverse (extChartAt hI.boundaryI x x) hmem'
  · haveI : IsEmpty hI.boundaryH := not_nonempty_iff.mp hN
    haveI : IsEmpty (BoundaryManifold I M) :=
      BoundaryManifold.isEmpty_of_isEmpty_boundaryH (I := I)
    exact (IsEmpty.false x).elim
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem outwardDir_ne_zero :
    outwardDir (M := M) g x ≠ 0 := by
  intro h0
  have htr : InwardCoordTransverse (M := M) x :=
    InwardCoordTransverse_of_HasSmoothBoundary (M := M) x
  have h_eq : inwardCoord (M := M) x = inwardTangentialPart (M := M) g x := by
    have := h0
    rw [outwardDir_def, sub_eq_zero] at this
    exact this.symm
  apply htr
  rw [h_eq, inwardTangentialPart_def]
  exact ⟨boundaryComponentOfInward (M := M) g x, rfl⟩
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem g_inner_outwardDir_pos :
    0 < g.inner (x : M) (outwardDir (M := M) g x) (outwardDir (M := M) g x) :=
  g.pos (x : M) _ (outwardDir_ne_zero (M := M) g x)
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem g_inner_outwardDir_inwardCoord_neg :
    g.inner (x : M) (outwardDir (M := M) g x) (inwardCoord (M := M) x) < 0 := by
  have hpos : 0 < g.inner (x : M) (outwardDir (M := M) g x) (outwardDir (M := M) g x) :=
    g_inner_outwardDir_pos (M := M) g x
  have h_id : g.inner (x : M) (outwardDir (M := M) g x) (inwardCoord (M := M) x) =
      -g.inner (x : M) (outwardDir (M := M) g x) (outwardDir (M := M) g x) := by
    rw [g_inner_outwardDir_inwardCoord (M := M) g x,
        g_inner_outwardDir_outwardDir (M := M) g x]
    ring
  rw [h_id]
  linarith

def outwardNormal : TangentSpace I (x : M) :=
  open scoped Classical in
  if _h : 0 < g.inner (x : M) (outwardDir (M := M) g x) (outwardDir (M := M) g x) then
    (Real.sqrt (g.inner (x : M) (outwardDir (M := M) g x) (outwardDir (M := M) g x)))⁻¹ •
      outwardDir (M := M) g x
  else
    0
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma outwardNormal_eq :
    outwardNormal (M := M) g x =
      (Real.sqrt (g.inner (x : M) (outwardDir (M := M) g x)
        (outwardDir (M := M) g x)))⁻¹ • outwardDir (M := M) g x := by
  unfold outwardNormal
  rw [dif_pos (g_inner_outwardDir_pos (M := M) g x)]
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem outwardNormal_mem_normalSubspace :
    outwardNormal (M := M) g x ∈ normalSubspace (M := M) g x := by
  rw [outwardNormal_eq (M := M) g x]
  exact (normalSubspace (M := M) g x).smul_mem _
    (outwardDir_mem_normalSubspace (M := M) g x)
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem outwardNormal_orthogonal_to_boundary (w : hI.boundaryE) :
    g.inner (x : M) (outwardNormal (M := M) g x) (boundaryInclusionMfderiv (M := M) x w) = 0 :=
  (outwardNormal_mem_normalSubspace (M := M) g x) w
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem inner_dincl_outwardNormal (w : hI.boundaryE) :
    g.inner (x : M) (boundaryInclusionMfderiv (M := M) x w) (outwardNormal (M := M) g x) = 0 := by
  rw [g.symm (x : M) _ (outwardNormal (M := M) g x)]
  exact outwardNormal_orthogonal_to_boundary (M := M) g x w
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem outwardNormal_norm_one :
    g.inner (x : M) (outwardNormal (M := M) g x) (outwardNormal (M := M) g x) = 1 := by
  set q : ℝ := g.inner (x : M) (outwardDir (M := M) g x) (outwardDir (M := M) g x) with hq_def
  have hq_pos : 0 < q := g_inner_outwardDir_pos (M := M) g x
  have hq_ne : q ≠ 0 := ne_of_gt hq_pos
  have hsq_pos : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq_pos
  have hsq_ne : Real.sqrt q ≠ 0 := ne_of_gt hsq_pos
  have hsq_sq : Real.sqrt q * Real.sqrt q = q := Real.mul_self_sqrt hq_pos.le
  rw [outwardNormal_eq (M := M) g x]
  have h1 : g.inner (x : M) ((Real.sqrt q)⁻¹ • outwardDir (M := M) g x)
          ((Real.sqrt q)⁻¹ • outwardDir (M := M) g x) =
      (Real.sqrt q)⁻¹ • (g.inner (x : M) (outwardDir (M := M) g x))
          ((Real.sqrt q)⁻¹ • outwardDir (M := M) g x) := by
    rw [show g.inner (x : M) ((Real.sqrt q)⁻¹ • outwardDir (M := M) g x) =
        (Real.sqrt q)⁻¹ • g.inner (x : M) (outwardDir (M := M) g x) from
          map_smul _ _ _]
    rfl
  rw [h1]
  rw [show (g.inner (x : M) (outwardDir (M := M) g x))
        ((Real.sqrt q)⁻¹ • outwardDir (M := M) g x) =
      (Real.sqrt q)⁻¹ • g.inner (x : M) (outwardDir (M := M) g x)
        (outwardDir (M := M) g x) from
    ContinuousLinearMap.map_smul _ _ _]
  rw [show g.inner (x : M) (outwardDir (M := M) g x) (outwardDir (M := M) g x) = q from rfl]
  rw [smul_eq_mul, smul_eq_mul]
  rw [show (Real.sqrt q)⁻¹ * ((Real.sqrt q)⁻¹ * q) = q / (Real.sqrt q * Real.sqrt q) by
    field_simp]
  rw [hsq_sq]
  exact div_self hq_ne
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem outwardNormal_inner_inwardCoord_neg :
    g.inner (x : M) (outwardNormal (M := M) g x) (inwardCoord (M := M) x) < 0 := by
  rw [outwardNormal_eq (M := M) g x]
  rw [ContinuousLinearMap.map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  have hq_pos : 0 < g.inner (x : M) (outwardDir (M := M) g x) (outwardDir (M := M) g x) :=
    g_inner_outwardDir_pos (M := M) g x
  have hsq_pos : 0 < Real.sqrt
      (g.inner (x : M) (outwardDir (M := M) g x) (outwardDir (M := M) g x)) :=
    Real.sqrt_pos.mpr hq_pos
  have hsq_inv_pos : 0 < (Real.sqrt
      (g.inner (x : M) (outwardDir (M := M) g x) (outwardDir (M := M) g x)))⁻¹ :=
    inv_pos.mpr hsq_pos
  have hneg : g.inner (x : M) (outwardDir (M := M) g x) (inwardCoord (M := M) x) < 0 :=
    g_inner_outwardDir_inwardCoord_neg (M := M) g x
  exact mul_neg_of_pos_of_neg hsq_inv_pos hneg

def boundaryFunOfInwardAt (g : SmoothRiemannianMetric I M)
    (α₀ x : BoundaryManifold I M) : hI.boundaryE →ₗ[ℝ] ℝ where
  toFun w := g.inner (x : M) (inwardCoordAt (M := M) α₀ x) (boundaryInclusionMfderiv (M := M) x w)
  map_add' u v := by
    rw [ContinuousLinearMap.map_add (boundaryInclusionMfderiv (M := M) x) u v]
    exact ContinuousLinearMap.map_add
      (g.inner (x : M) (inwardCoordAt (M := M) α₀ x)) _ _
  map_smul' c v := by
    rw [ContinuousLinearMap.map_smul (boundaryInclusionMfderiv (M := M) x) c v]
    exact ContinuousLinearMap.map_smul
      (g.inner (x : M) (inwardCoordAt (M := M) α₀ x)) _ _

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
@[simp] lemma boundaryFunOfInwardAt_apply
    (g : SmoothRiemannianMetric I M) (α₀ x : BoundaryManifold I M)
    (w : hI.boundaryE) :
    boundaryFunOfInwardAt (M := M) g α₀ x w =
      g.inner (x : M) (inwardCoordAt (M := M) α₀ x) (boundaryInclusionMfderiv (M := M) x w) := rfl

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
@[simp] lemma boundaryFunOfInwardAt_self
    (g : SmoothRiemannianMetric I M) (x : BoundaryManifold I M) :
    boundaryFunOfInwardAt (M := M) g x x = boundaryFunOfInward (M := M) g x := by
  ext w
  simp [boundaryFunOfInwardAt_apply, boundaryFunOfInward_apply,
    inwardCoordAt_self]

def boundaryComponentOfInwardAt
    (g : SmoothRiemannianMetric I M) (α₀ x : BoundaryManifold I M) :
    hI.boundaryE :=
  (boundaryFlatMap (M := M) g x).symm (boundaryFunOfInwardAt (M := M) g α₀ x)
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
@[simp] lemma boundaryComponentOfInwardAt_self
    (g : SmoothRiemannianMetric I M) (x : BoundaryManifold I M) :
    boundaryComponentOfInwardAt (M := M) g x x =
      boundaryComponentOfInward (M := M) g x := by
  unfold boundaryComponentOfInwardAt boundaryComponentOfInward
  rw [boundaryFunOfInwardAt_self]
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma inducedMetricInner_boundaryComponentOfInwardAt
    (g : SmoothRiemannianMetric I M) (α₀ x : BoundaryManifold I M)
    (w : hI.boundaryE) :
    inducedMetricInner (M := M) g x (boundaryComponentOfInwardAt (M := M) g α₀ x) w =
      g.inner (x : M) (inwardCoordAt (M := M) α₀ x) (boundaryInclusionMfderiv (M := M) x w) := by
  unfold boundaryComponentOfInwardAt
  have := boundaryFlatMap_apply_symm (M := M) g x
    (boundaryFunOfInwardAt (M := M) g α₀ x) w
  rw [this]
  rfl

def inwardTangentialPartAt
    (g : SmoothRiemannianMetric I M) (α₀ x : BoundaryManifold I M) :
    TangentSpace I (x : M) :=
  boundaryInclusionMfderiv (M := M) x (boundaryComponentOfInwardAt (M := M) g α₀ x)
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
@[simp] lemma inwardTangentialPartAt_def
    (g : SmoothRiemannianMetric I M) (α₀ x : BoundaryManifold I M) :
    inwardTangentialPartAt (M := M) g α₀ x =
      boundaryInclusionMfderiv (M := M) x (boundaryComponentOfInwardAt (M := M) g α₀ x) := rfl
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
@[simp] lemma inwardTangentialPartAt_self
    (g : SmoothRiemannianMetric I M) (x : BoundaryManifold I M) :
    inwardTangentialPartAt (M := M) g x x = inwardTangentialPart (M := M) g x := by
  unfold inwardTangentialPartAt inwardTangentialPart
  rw [boundaryComponentOfInwardAt_self]

def outwardDirAt
    (g : SmoothRiemannianMetric I M) (α₀ x : BoundaryManifold I M) :
    TangentSpace I (x : M) :=
  inwardTangentialPartAt (M := M) g α₀ x - inwardCoordAt (M := M) α₀ x
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
@[simp] lemma outwardDirAt_def
    (g : SmoothRiemannianMetric I M) (α₀ x : BoundaryManifold I M) :
    outwardDirAt (M := M) g α₀ x =
      inwardTangentialPartAt (M := M) g α₀ x - inwardCoordAt (M := M) α₀ x := rfl
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
@[simp] lemma outwardDirAt_self
    (g : SmoothRiemannianMetric I M) (x : BoundaryManifold I M) :
    outwardDirAt (M := M) g x x = outwardDir (M := M) g x := by
  unfold outwardDirAt outwardDir
  rw [inwardTangentialPartAt_self, inwardCoordAt_self]
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem outwardDirAt_mem_normalSubspace
    (g : SmoothRiemannianMetric I M) (α₀ x : BoundaryManifold I M) :
    outwardDirAt (M := M) g α₀ x ∈ normalSubspace (M := M) g x := by
  intro w
  rw [outwardDirAt_def]
  have hsub : g.inner (x : M)
        (inwardTangentialPartAt (M := M) g α₀ x - inwardCoordAt (M := M) α₀ x)
        (boundaryInclusionMfderiv (M := M) x w) =
      g.inner (x : M) (inwardTangentialPartAt (M := M) g α₀ x) (boundaryInclusionMfderiv (M := M) x w) -
      g.inner (x : M) (inwardCoordAt (M := M) α₀ x) (boundaryInclusionMfderiv (M := M) x w) := by
    rw [map_sub, ContinuousLinearMap.sub_apply]
  rw [hsub]
  have h1 : g.inner (x : M) (inwardTangentialPartAt (M := M) g α₀ x) (boundaryInclusionMfderiv (M := M) x w) =
      inducedMetricInner (M := M) g x (boundaryComponentOfInwardAt (M := M) g α₀ x) w := by
    rw [inducedMetricInner_apply, inwardTangentialPartAt_def]
  rw [h1]
  rw [inducedMetricInner_boundaryComponentOfInwardAt (M := M) g α₀ x w]
  ring
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma g_inner_outwardDirAt_inwardCoordAt
    (g : SmoothRiemannianMetric I M) (α₀ x : BoundaryManifold I M) :
    g.inner (x : M) (outwardDirAt (M := M) g α₀ x) (inwardCoordAt (M := M) α₀ x) =
      g.inner (x : M) (inwardTangentialPartAt (M := M) g α₀ x)
        (inwardCoordAt (M := M) α₀ x) -
      g.inner (x : M) (inwardCoordAt (M := M) α₀ x) (inwardCoordAt (M := M) α₀ x) := by
  rw [outwardDirAt_def, map_sub, ContinuousLinearMap.sub_apply]
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma g_inner_outwardDirAt_outwardDirAt
    (g : SmoothRiemannianMetric I M) (α₀ x : BoundaryManifold I M) :
    g.inner (x : M) (outwardDirAt (M := M) g α₀ x) (outwardDirAt (M := M) g α₀ x) =
      g.inner (x : M) (inwardCoordAt (M := M) α₀ x) (inwardCoordAt (M := M) α₀ x) -
      g.inner (x : M) (inwardTangentialPartAt (M := M) g α₀ x)
        (inwardCoordAt (M := M) α₀ x) := by
  have h_orth : g.inner (x : M) (outwardDirAt (M := M) g α₀ x)
      (inwardTangentialPartAt (M := M) g α₀ x) = 0 := by
    have hmem : outwardDirAt (M := M) g α₀ x ∈ normalSubspace (M := M) g x :=
      outwardDirAt_mem_normalSubspace (M := M) g α₀ x
    rw [inwardTangentialPartAt_def]
    exact hmem (boundaryComponentOfInwardAt (M := M) g α₀ x)
  have hdecomp : g.inner (x : M)
        (outwardDirAt (M := M) g α₀ x) (outwardDirAt (M := M) g α₀ x) =
      g.inner (x : M) (outwardDirAt (M := M) g α₀ x)
        (inwardTangentialPartAt (M := M) g α₀ x) -
      g.inner (x : M) (outwardDirAt (M := M) g α₀ x)
        (inwardCoordAt (M := M) α₀ x) := by
    change g.inner (x : M) (outwardDirAt (M := M) g α₀ x)
        (inwardTangentialPartAt (M := M) g α₀ x - inwardCoordAt (M := M) α₀ x) =
      g.inner (x : M) (outwardDirAt (M := M) g α₀ x)
        (inwardTangentialPartAt (M := M) g α₀ x) -
      g.inner (x : M) (outwardDirAt (M := M) g α₀ x) (inwardCoordAt (M := M) α₀ x)
    exact ContinuousLinearMap.map_sub _ _ _
  rw [hdecomp, h_orth, zero_sub]
  rw [g_inner_outwardDirAt_inwardCoordAt (M := M) g α₀ x]
  ring

def outwardNormalAt
    (g : SmoothRiemannianMetric I M) (α₀ x : BoundaryManifold I M) :
    TangentSpace I (x : M) :=
  open scoped Classical in
  if _h :
    0 < g.inner (x : M) (outwardDirAt (M := M) g α₀ x)
        (outwardDirAt (M := M) g α₀ x) then
    (Real.sqrt (g.inner (x : M) (outwardDirAt (M := M) g α₀ x)
        (outwardDirAt (M := M) g α₀ x)))⁻¹ • outwardDirAt (M := M) g α₀ x
  else 0
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
@[simp] lemma outwardNormalAt_self
    (g : SmoothRiemannianMetric I M) (x : BoundaryManifold I M) :
    outwardNormalAt (M := M) g x x = outwardNormal (M := M) g x := by
  unfold outwardNormalAt outwardNormal
  rw [outwardDirAt_self]

section Smoothness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [hI : HasSmoothBoundary E H I] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

private lemma infty_le_top_add' : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by
  have h_eq : (∞ : WithTop ℕ∞) + 1 = (∞ : WithTop ℕ∞) := by
    change ((⊤ : ℕ∞) : WithTop ℕ∞) + 1 = ((⊤ : ℕ∞) : WithTop ℕ∞)
    rfl
  rw [h_eq]

private noncomputable def dinclITC (x₀ : BoundaryManifold I M)
    (b : BoundaryManifold I M) (v : hI.boundaryE) : E :=
  inTangentCoordinates hI.boundaryI I id (boundaryInclusion I M)
    (mfderiv hI.boundaryI I (boundaryInclusion I M)) x₀ b v

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private lemma dinclITC_apply_contMDiffAt
    {s : BoundaryManifold I M → hI.boundaryE} {x₀ : BoundaryManifold I M}
    (hs : ContMDiffAt hI.boundaryI 𝓘(ℝ, hI.boundaryE) ∞ s x₀) :
    ContMDiffAt hI.boundaryI 𝓘(ℝ, E) ∞
      (fun b : BoundaryManifold I M => dinclITC (M := M) x₀ b (s b)) x₀ := by
  unfold dinclITC
  have h_inclusion_at : ContMDiffAt hI.boundaryI I ∞ (boundaryInclusion I M) x₀ :=
    boundaryInclusion_contMDiff.contMDiffAt
  have h_f_uncurry : ContMDiffAt (hI.boundaryI.prod hI.boundaryI) I ∞
      (Function.uncurry (fun (_ : BoundaryManifold I M) (b' : BoundaryManifold I M) =>
        boundaryInclusion I M b'))
      (x₀, x₀) := by
    have h_snd : ContMDiffAt (hI.boundaryI.prod hI.boundaryI) hI.boundaryI ∞
        (Prod.snd : BoundaryManifold I M × BoundaryManifold I M → BoundaryManifold I M)
        (x₀, x₀) := contMDiffAt_snd
    exact h_inclusion_at.comp (x₀, x₀) h_snd
  have h_g_at : ContMDiffAt hI.boundaryI hI.boundaryI ∞
      (id : BoundaryManifold I M → BoundaryManifold I M) x₀ := contMDiffAt_id
  have h_g₁_at : ContMDiffAt hI.boundaryI hI.boundaryI ∞
      (id : BoundaryManifold I M → BoundaryManifold I M) x₀ := contMDiffAt_id
  exact ContMDiffAt.mfderiv_apply
    (f := fun (_ : BoundaryManifold I M) (b : BoundaryManifold I M) => boundaryInclusion I M b)
    (g := id) (g₁ := id) (g₂ := s)
    h_f_uncurry h_g_at h_g₁_at hs infty_le_top_add'

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private lemma dinclITC_apply
    (x₀ : BoundaryManifold I M) {b : BoundaryManifold I M}
    (hb_amb : (b : M) ∈ (chartAt H (x₀ : M)).source)
    (hb_bdy : b ∈ (chartAt hI.boundaryH x₀).source) (v : hI.boundaryE) :
    dinclITC (M := M) x₀ b v =
      (trivializationAt E (TangentSpace I) (x₀ : M)).continuousLinearMapAt ℝ
        (b : M) (boundaryInclusionMfderiv (M := M) b
          (((trivializationAt hI.boundaryE
              (TangentSpace hI.boundaryI) x₀).symmL ℝ b) v)) := by
  unfold dinclITC
  have h_inT := inTangentCoordinates_eq_mfderiv_comp
    (I := hI.boundaryI) (I' := I) (𝕜 := ℝ)
    (f := id) (g := boundaryInclusion I M)
    (ϕ := mfderiv hI.boundaryI I (boundaryInclusion I M)) (x₀ := x₀) (x := b)
    (hx := hb_bdy) (hy := hb_amb)
  rw [h_inT]
  have h_first : mfderiv I 𝓘(ℝ, E)
      (extChartAt I (boundaryInclusion I M x₀)) (boundaryInclusion I M b)
      = (trivializationAt E (TangentSpace I) (x₀ : M)).continuousLinearMapAt ℝ (b : M) :=
    (TangentBundle.continuousLinearMapAt_trivializationAt (𝕜 := ℝ) (I := I) hb_amb).symm
  have h_third :
      mfderivWithin 𝓘(ℝ, hI.boundaryE) hI.boundaryI (extChartAt hI.boundaryI x₀).symm
        (Set.range hI.boundaryI) (extChartAt hI.boundaryI x₀ b)
      = (trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) x₀).symmL ℝ b :=
    (TangentBundle.symmL_trivializationAt hb_bdy).symm
  change ((mfderiv I 𝓘(ℝ, E) (extChartAt I (boundaryInclusion I M x₀))
          (boundaryInclusion I M b)).comp
        ((mfderiv hI.boundaryI I (boundaryInclusion I M) b).comp
          (mfderivWithin 𝓘(ℝ, hI.boundaryE) hI.boundaryI (extChartAt hI.boundaryI x₀).symm
            (Set.range hI.boundaryI) (extChartAt hI.boundaryI x₀ b)))) v =
      ((trivializationAt E (TangentSpace I) (x₀ : M)).continuousLinearMapAt ℝ (b : M))
        ((boundaryInclusionMfderiv (M := M) b) (((trivializationAt hI.boundaryE
              (TangentSpace hI.boundaryI) x₀).symmL ℝ b) v))
  rw [h_first, h_third]
  rfl

variable (g : Measure.SmoothRiemannianMetric I M)

private noncomputable def boundaryFlatCharted
    (x₀ : BoundaryManifold I M) (b : BoundaryManifold I M) :
    hI.boundaryE →L[ℝ] hI.boundaryE →L[ℝ] ℝ :=
  ((trivializationAt (hI.boundaryE →L[ℝ] hI.boundaryE →L[ℝ] ℝ)
      (fun y : BoundaryManifold I M =>
        TangentSpace hI.boundaryI y →L[ℝ] TangentSpace hI.boundaryI y →L[ℝ] ℝ) x₀)
    ⟨b, inducedMetricInner g b⟩).2

omit [InnerProductSpace ℝ E] in
omit [FiniteDimensional ℝ E] in
private lemma boundaryFlatCharted_contMDiffAt
    (x₀ : BoundaryManifold I M) :
    ContMDiffAt hI.boundaryI 𝓘(ℝ, hI.boundaryE →L[ℝ] hI.boundaryE →L[ℝ] ℝ) ∞
      (boundaryFlatCharted (M := M) g x₀) x₀ := by
  have h_section := inducedMetricInner_contMDiff (g := g)
  have h_x₀ : x₀ ∈ (trivializationAt (hI.boundaryE →L[ℝ] hI.boundaryE →L[ℝ] ℝ)
      (fun y : BoundaryManifold I M =>
        TangentSpace hI.boundaryI y →L[ℝ] TangentSpace hI.boundaryI y →L[ℝ] ℝ) x₀).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x₀
  exact ((trivializationAt _ _ x₀).contMDiffAt_section_iff h_x₀).mp
    h_section.contMDiffAt

private noncomputable def boundaryFunOfInwardCLM
    (b : BoundaryManifold I M) : hI.boundaryE →L[ℝ] ℝ :=
  (g.inner (b : M) (inwardCoord (M := M) b)).comp (boundaryInclusionMfderiv (M := M) b)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
@[simp] private lemma boundaryFunOfInwardCLM_apply
    (b : BoundaryManifold I M) (w : hI.boundaryE) :
    boundaryFunOfInwardCLM (M := M) g b w =
      g.inner (b : M) (inwardCoord (M := M) b) (boundaryInclusionMfderiv (M := M) b w) := rfl

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private lemma inducedMetricInner_isInvertible
    (b : BoundaryManifold I M) :
    (inducedMetricInner (M := M) g b).IsInvertible := by
  have h_inj : Function.Injective (inducedMetricInner (M := M) g b) := by
    intro u v huv
    by_contra hne
    have huv_ne : u - v ≠ 0 := sub_ne_zero.mpr hne
    have hpos : 0 < inducedMetricInner (M := M) g b (u - v) (u - v) :=
      inducedMetricInner_pos (M := M) g b (u - v) huv_ne
    have hzero : inducedMetricInner (M := M) g b (u - v) (u - v) = 0 := by
      have h1 : inducedMetricInner (M := M) g b (u - v) =
          inducedMetricInner (M := M) g b u - inducedMetricInner (M := M) g b v :=
        ContinuousLinearMap.map_sub _ _ _
      rw [h1, huv, sub_self]
      simp
    rw [hzero] at hpos
    exact lt_irrefl 0 hpos
  let L : hI.boundaryE →ₗ[ℝ] (hI.boundaryE →L[ℝ] ℝ) := (inducedMetricInner g b).toLinearMap
  have hL_inj : Function.Injective L := h_inj
  have hfinrank : Module.finrank ℝ hI.boundaryE =
      Module.finrank ℝ (hI.boundaryE →L[ℝ] ℝ) := by
    rw [show Module.finrank ℝ (hI.boundaryE →L[ℝ] ℝ) =
        Module.finrank ℝ (hI.boundaryE →ₗ[ℝ] ℝ) from ?_]
    · exact Subspace.dual_finrank_eq.symm
    · exact (LinearEquiv.finrank_eq
        (LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := hI.boundaryE) (F' := ℝ))).symm
  let L_equiv : hI.boundaryE ≃ₗ[ℝ] (hI.boundaryE →L[ℝ] ℝ) :=
    LinearMap.linearEquivOfInjective L hL_inj hfinrank
  let L_cle : hI.boundaryE ≃L[ℝ] (hI.boundaryE →L[ℝ] ℝ) := L_equiv.toContinuousLinearEquiv
  have h_eq : (L_cle : hI.boundaryE →L[ℝ] (hI.boundaryE →L[ℝ] ℝ)) =
      inducedMetricInner (M := M) g b := by
    ext u
    rfl
  exact ⟨L_cle, h_eq⟩

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private lemma boundaryFlatCharted_basepoint
    (x₀ : BoundaryManifold I M) :
    boundaryFlatCharted (M := M) g x₀ x₀ = inducedMetricInner (M := M) g x₀ := by
  refine ContinuousLinearMap.ext fun u => ContinuousLinearMap.ext fun v => ?_
  have hb_bdy : x₀ ∈ (trivializationAt hI.boundaryE
      (TangentSpace hI.boundaryI) x₀).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x₀
  change ((trivializationAt (hI.boundaryE →L[ℝ] hI.boundaryE →L[ℝ] ℝ)
          (fun y : BoundaryManifold I M =>
            TangentSpace hI.boundaryI y →L[ℝ]
            TangentSpace hI.boundaryI y →L[ℝ] ℝ) x₀)
        ⟨x₀, inducedMetricInner (M := M) g x₀⟩).2 u v =
      ((inducedMetricInner (M := M) g x₀) u) v
  rw [hom_trivializationAt_apply]
  rw [inCoordinates_apply_eq₂ (𝕜 := ℝ) hb_bdy hb_bdy (Set.mem_univ _)]
  change (trivializationAt ℝ (Bundle.Trivial (BoundaryManifold I M) ℝ) x₀).linearMapAt ℝ x₀ _ = _
  change (Bundle.Trivial.trivialization (BoundaryManifold I M) ℝ).linearMapAt ℝ x₀ _ = _
  rw [Bundle.Trivial.linearMapAt_trivialization (𝕜 := ℝ)
    (B := BoundaryManifold I M) (F := ℝ) x₀]
  have h_symmL_id : ∀ w : hI.boundaryE,
      ((trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) x₀).symmL ℝ x₀) w = w := by
    intro w
    have hsymmL_eq :
        (trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) x₀).symmL ℝ x₀
          = mfderivWithin 𝓘(ℝ, hI.boundaryE) hI.boundaryI
              (extChartAt hI.boundaryI x₀).symm
              (Set.range hI.boundaryI) (extChartAt hI.boundaryI x₀ x₀) :=
      TangentBundle.symmL_trivializationAt hb_bdy
    rw [hsymmL_eq, mfderivWithin_range_extChartAt_symm]
    rfl
  have hcoe :
      ⇑((trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) x₀).symmL ℝ x₀)
        = (trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) x₀).symm x₀ :=
    Trivialization.symmL_apply _ _ _
  have hsymm1 : (trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) x₀).symm x₀ u
      = ((trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) x₀).symmL ℝ x₀) u := by
    rw [hcoe]
  have hsymm2 : (trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) x₀).symm x₀ v
      = ((trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) x₀).symmL ℝ x₀) v := by
    rw [hcoe]
  rw [hsymm1, hsymm2, h_symmL_id u, h_symmL_id v]
  rfl

private noncomputable def boundaryFlatChartedInv
    (x₀ : BoundaryManifold I M) (b : BoundaryManifold I M) :
    (hI.boundaryE →L[ℝ] ℝ) →L[ℝ] hI.boundaryE :=
  ContinuousLinearMap.inverse (boundaryFlatCharted (M := M) g x₀ b)
omit [InnerProductSpace ℝ E] in
omit [FiniteDimensional ℝ E] in
private lemma boundaryFlatChartedInv_contMDiffAt
    (x₀ : BoundaryManifold I M) :
    ContMDiffAt hI.boundaryI 𝓘(ℝ, (hI.boundaryE →L[ℝ] ℝ) →L[ℝ] hI.boundaryE) ∞
      (boundaryFlatChartedInv (M := M) g x₀) x₀ := by
  have h_flat : ContMDiffAt hI.boundaryI 𝓘(ℝ, hI.boundaryE →L[ℝ] hI.boundaryE →L[ℝ] ℝ) ∞
      (boundaryFlatCharted (M := M) g x₀) x₀ :=
    boundaryFlatCharted_contMDiffAt (M := M) g x₀
  have h_inv : (boundaryFlatCharted (M := M) g x₀ x₀).IsInvertible := by
    rw [boundaryFlatCharted_basepoint (M := M) g x₀]
    exact inducedMetricInner_isInvertible (M := M) g x₀
  have h_inverse_smooth :
      ContDiffAt ℝ ∞ ContinuousLinearMap.inverse
        (boundaryFlatCharted (M := M) g x₀ x₀) :=
    h_inv.contDiffAt_map_inverse
  exact h_inverse_smooth.contMDiffAt.comp x₀ h_flat

private noncomputable def boundaryFunOfInwardCharted
    (x₀ : BoundaryManifold I M) (b : BoundaryManifold I M) :
    hI.boundaryE →L[ℝ] ℝ :=
  (boundaryFunOfInwardCLM (M := M) g b).comp
    ((trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) x₀).symmL ℝ b)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
@[simp] private lemma boundaryFunOfInwardCharted_apply
    (x₀ : BoundaryManifold I M) (b : BoundaryManifold I M)
    (w : hI.boundaryE) :
    boundaryFunOfInwardCharted (M := M) g x₀ b w =
      g.inner (b : M) (inwardCoord (M := M) b)
        (boundaryInclusionMfderiv (M := M) b
          (((trivializationAt hI.boundaryE
              (TangentSpace hI.boundaryI) x₀).symmL ℝ b) w)) := rfl

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private lemma inwardCoordAt_section_contMDiffOn
    (α₀ : BoundaryManifold I M) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M =>
        TotalSpace.mk' E y
          ((trivializationAt E (TangentSpace I) (α₀ : M)).symm y hI.inwardCoordE))
      (trivializationAt E (TangentSpace I) (α₀ : M)).baseSet := by
  have hiff :=
    ((trivializationAt E (TangentSpace I) (α₀ : M))).contMDiffOn_section_baseSet_iff
      (IB := I) (n := ∞)
      (s := fun y : M => (trivializationAt E (TangentSpace I) (α₀ : M)).symm y
        hI.inwardCoordE)
  refine hiff.mpr ?_
  have hconst : ContMDiffOn I 𝓘(ℝ, E) ∞
      (fun _ : M => hI.inwardCoordE)
      (trivializationAt E (TangentSpace I) (α₀ : M)).baseSet := contMDiffOn_const
  refine hconst.congr ?_
  intro y hy
  have h := (trivializationAt E (TangentSpace I) (α₀ : M)).apply_mk_symm hy
    hI.inwardCoordE
  exact congrArg Prod.snd h

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private lemma inwardCoordAt_section_contMDiffAt
    (α₀ : BoundaryManifold I M) :
    ContMDiffAt hI.boundaryI (I.prod 𝓘(ℝ, E)) ∞
      (fun b : BoundaryManifold I M =>
        TotalSpace.mk' E (b : M) (inwardCoordAt (M := M) α₀ b)) α₀ := by
  have hα_in : (α₀ : M) ∈ (trivializationAt E (TangentSpace I) (α₀ : M)).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' (α₀ : M)
  have h_section_open :
      (trivializationAt E (TangentSpace I) (α₀ : M)).baseSet ∈ 𝓝 (α₀ : M) :=
    ((trivializationAt E (TangentSpace I) (α₀ : M)).open_baseSet).mem_nhds hα_in
  have h_section_at : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M =>
        TotalSpace.mk' E y
          ((trivializationAt E (TangentSpace I) (α₀ : M)).symm y hI.inwardCoordE))
      (α₀ : M) :=
    (inwardCoordAt_section_contMDiffOn (M := M) α₀).contMDiffAt h_section_open
  have h_inclusion_at : ContMDiffAt hI.boundaryI I ∞ (boundaryInclusion I M) α₀ :=
    boundaryInclusion_contMDiff.contMDiffAt
  exact h_section_at.comp α₀ h_inclusion_at

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private lemma chart_triv_second_inwardCoordAt
    (α₀ : BoundaryManifold I M) {b : BoundaryManifold I M}
    (hb : (b : M) ∈ (trivializationAt E (TangentSpace I) (α₀ : M)).baseSet) :
    ((trivializationAt E (TangentSpace I) (α₀ : M))
        ⟨(b : M), inwardCoordAt (M := M) α₀ b⟩).2 = hI.inwardCoordE := by
  unfold inwardCoordAt
  have h := (trivializationAt E (TangentSpace I) (α₀ : M)).apply_mk_symm hb
    hI.inwardCoordE
  exact congrArg Prod.snd h

private noncomputable def metricPullback
    (g : SmoothRiemannianMetric I M) (x : BoundaryManifold I M) :
    TangentSpace I (x : M) →ₗ[ℝ] (hI.boundaryE →ₗ[ℝ] ℝ) where
  toFun v :=
    { toFun := fun w => g.inner (x : M) v (boundaryInclusionMfderiv (M := M) x w)
      map_add' := fun u v' => by
        rw [ContinuousLinearMap.map_add (boundaryInclusionMfderiv (M := M) x) u v']
        exact ContinuousLinearMap.map_add (g.inner (x : M) v) _ _
      map_smul' := fun c v' => by
        rw [ContinuousLinearMap.map_smul (boundaryInclusionMfderiv (M := M) x) c v']
        exact ContinuousLinearMap.map_smul (g.inner (x : M) v) _ _ }
  map_add' v₁ v₂ := by
    ext w
    change g.inner (x : M) (v₁ + v₂) (boundaryInclusionMfderiv (M := M) x w) =
      g.inner (x : M) v₁ (boundaryInclusionMfderiv (M := M) x w) +
      g.inner (x : M) v₂ (boundaryInclusionMfderiv (M := M) x w)
    rw [map_add, ContinuousLinearMap.add_apply]
  map_smul' c v := by
    ext w
    change g.inner (x : M) (c • v) (boundaryInclusionMfderiv (M := M) x w) =
      c • g.inner (x : M) v (boundaryInclusionMfderiv (M := M) x w)
    rw [map_smul, ContinuousLinearMap.smul_apply]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
@[simp] private lemma metricPullback_apply
    (g : SmoothRiemannianMetric I M) (x : BoundaryManifold I M)
    (v : TangentSpace I (x : M)) (w : hI.boundaryE) :
    metricPullback (M := M) g x v w =
      g.inner (x : M) v (boundaryInclusionMfderiv (M := M) x w) := rfl

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private lemma mem_ker_metricPullback_iff
    (g : SmoothRiemannianMetric I M) (x : BoundaryManifold I M)
    (v : TangentSpace I (x : M)) :
    v ∈ LinearMap.ker (metricPullback (M := M) g x) ↔
      v ∈ normalSubspace (M := M) g x := by
  refine ⟨?_, ?_⟩
  · intro hv w
    have h := congrArg (fun L : hI.boundaryE →ₗ[ℝ] ℝ => L w) hv
    simp only [metricPullback_apply, LinearMap.zero_apply] at h
    exact h
  · intro hv
    apply LinearMap.ext
    intro w
    rw [metricPullback_apply, hv w]
    rfl

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private lemma ker_metricPullback_eq_normalSubspace
    (g : SmoothRiemannianMetric I M) (x : BoundaryManifold I M) :
    LinearMap.ker (metricPullback (M := M) g x) = normalSubspace (M := M) g x := by
  apply Submodule.ext
  intro v
  exact mem_ker_metricPullback_iff (M := M) g x v

variable (g : Measure.SmoothRiemannianMetric I M)

private noncomputable def boundaryFunOfInwardAtChartedCLM
    (α₀ : BoundaryManifold I M) (b : BoundaryManifold I M) :
    hI.boundaryE →L[ℝ] ℝ :=
  ((trivializationAt (E →L[ℝ] ℝ)
        (fun y : M => TangentSpace I y →L[ℝ] ℝ) (α₀ : M))
    ⟨(b : M), g.inner (b : M) (inwardCoordAt (M := M) α₀ b)⟩).2.comp
    (inTangentCoordinates hI.boundaryI I id (boundaryInclusion I M)
      (mfderiv hI.boundaryI I (boundaryInclusion I M)) α₀ b)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private lemma boundaryFunOfInwardAtChartedCLM_contMDiffAt
    (α₀ : BoundaryManifold I M) :
    ContMDiffAt hI.boundaryI 𝓘(ℝ, hI.boundaryE →L[ℝ] ℝ) ∞
      (boundaryFunOfInwardAtChartedCLM (M := M) g α₀) α₀ := by
  have h_inwardCoord_section : ContMDiffAt hI.boundaryI (I.prod 𝓘(ℝ, E)) ∞
      (fun b : BoundaryManifold I M =>
        TotalSpace.mk' E (b : M) (inwardCoordAt (M := M) α₀ b)) α₀ :=
    inwardCoordAt_section_contMDiffAt (M := M) α₀
  have h_inclusion_at : ContMDiffAt hI.boundaryI I ∞ (boundaryInclusion I M) α₀ :=
    boundaryInclusion_contMDiff.contMDiffAt
  have h_g_section : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun y : M =>
        TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun y : M =>
            TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
          y (g.inner y)) := g.contMDiff
  have h_g_at : ContMDiffAt hI.boundaryI (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b : BoundaryManifold I M =>
        TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun y : M =>
            TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
          (b : M) (g.inner (b : M))) α₀ :=
    h_g_section.contMDiffAt.comp α₀ h_inclusion_at
  have h_inner_applied : ContMDiffAt hI.boundaryI (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
      (fun b : BoundaryManifold I M =>
        TotalSpace.mk' (E →L[ℝ] ℝ)
          (E := fun y : M => TangentSpace I y →L[ℝ] ℝ)
          (b : M)
          (g.inner (b : M) (inwardCoordAt (M := M) α₀ b))) α₀ :=
    h_g_at.clm_bundle_apply h_inwardCoord_section
  have h_α_smooth : ContMDiffAt hI.boundaryI 𝓘(ℝ, E →L[ℝ] ℝ) ∞
      (fun b : BoundaryManifold I M =>
        ((trivializationAt (E →L[ℝ] ℝ)
            (fun y : M => TangentSpace I y →L[ℝ] ℝ) (α₀ : M))
          ⟨(b : M),
            g.inner (b : M) (inwardCoordAt (M := M) α₀ b)⟩).2) α₀ := by
    rw [Bundle.contMDiffAt_totalSpace] at h_inner_applied
    exact h_inner_applied.2
  have h_dincl_clm : ContMDiffAt hI.boundaryI 𝓘(ℝ, hI.boundaryE →L[ℝ] E) ∞
      (fun b : BoundaryManifold I M =>
        inTangentCoordinates hI.boundaryI I id (boundaryInclusion I M)
          (mfderiv hI.boundaryI I (boundaryInclusion I M)) α₀ b) α₀ :=
    h_inclusion_at.mfderiv_const infty_le_top_add'
  exact h_α_smooth.clm_comp h_dincl_clm

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private lemma boundaryFunOfInwardAtChartedCLM_apply_of_mem
    (α₀ : BoundaryManifold I M) {b : BoundaryManifold I M}
    (hb_amb : (b : M) ∈ (chartAt H (α₀ : M)).source)
    (hb_bdy : b ∈ (chartAt hI.boundaryH α₀).source)
    (w : hI.boundaryE) :
    boundaryFunOfInwardAtChartedCLM (M := M) g α₀ b w =
      g.inner (b : M) (inwardCoordAt (M := M) α₀ b)
        (boundaryInclusionMfderiv (M := M) b
          (((trivializationAt hI.boundaryE
              (TangentSpace hI.boundaryI) α₀).symmL ℝ b) w)) := by
  unfold boundaryFunOfInwardAtChartedCLM
  rw [ContinuousLinearMap.coe_comp', Function.comp_apply]
  have h_amb_baseSet : (b : M) ∈ (trivializationAt E (TangentSpace I) (α₀ : M)).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact hb_amb
  rw [hom_trivializationAt_apply]
  have h_inC :
      (ContinuousLinearMap.inCoordinates E (TangentSpace I) ℝ (fun _ : M => ℝ)
        (α₀ : M) (b : M) (α₀ : M) (b : M)
        (g.inner (b : M) (inwardCoordAt (M := M) α₀ b)))
        (inTangentCoordinates hI.boundaryI I id (boundaryInclusion I M)
          (mfderiv hI.boundaryI I (boundaryInclusion I M)) α₀ b w) =
        g.inner (b : M) (inwardCoordAt (M := M) α₀ b)
          (boundaryInclusionMfderiv (M := M) b
            (((trivializationAt hI.boundaryE
                (TangentSpace hI.boundaryI) α₀).symmL ℝ b) w)) := by
    rw [ContinuousLinearMap.inCoordinates]
    rw [ContinuousLinearMap.coe_comp', Function.comp_apply,
        ContinuousLinearMap.coe_comp', Function.comp_apply]
    have h_trivial_clmAt : ∀ x : ℝ,
        (trivializationAt ℝ (fun _ : M => ℝ) (α₀ : M)).continuousLinearMapAt ℝ (b : M) x = x := by
      intro x
      change (Bundle.Trivial.trivialization M ℝ).continuousLinearMapAt ℝ (b : M) x = x
      rw [Bundle.Trivial.continuousLinearMapAt_trivialization (𝕜 := ℝ) (B := M) (F := ℝ) (b : M)]
      rfl
    rw [h_trivial_clmAt]
    have h_dinclITC_val :
        inTangentCoordinates hI.boundaryI I id (boundaryInclusion I M)
            (mfderiv hI.boundaryI I (boundaryInclusion I M)) α₀ b w =
          (trivializationAt E (TangentSpace I) (α₀ : M)).continuousLinearMapAt ℝ
            (b : M) (boundaryInclusionMfderiv (M := M) b
              (((trivializationAt hI.boundaryE
                  (TangentSpace hI.boundaryI) α₀).symmL ℝ b) w)) := by
      have := dinclITC_apply (M := M) α₀ hb_amb hb_bdy w
      unfold dinclITC at this
      exact this
    rw [h_dinclITC_val]
    have h_amb_round :
        (((trivializationAt E (TangentSpace I) (α₀ : M)).symmL ℝ (b : M))
            ((trivializationAt E (TangentSpace I) (α₀ : M)).continuousLinearMapAt ℝ
              (b : M)
              (boundaryInclusionMfderiv (M := M) b
                (((trivializationAt hI.boundaryE
                    (TangentSpace hI.boundaryI) α₀).symmL ℝ b) w)))) =
          boundaryInclusionMfderiv (M := M) b
            (((trivializationAt hI.boundaryE
                (TangentSpace hI.boundaryI) α₀).symmL ℝ b) w) :=
      (trivializationAt E (TangentSpace I) (α₀ : M)).symmL_continuousLinearMapAt
        (R := ℝ) h_amb_baseSet (boundaryInclusionMfderiv (M := M) b
          (((trivializationAt hI.boundaryE
              (TangentSpace hI.boundaryI) α₀).symmL ℝ b) w))
    rw [h_amb_round]
  exact h_inC

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private lemma boundaryFlatCharted_apply_of_mem
    (α₀ : BoundaryManifold I M) {b : BoundaryManifold I M}
    (hb_bdy : b ∈ (trivializationAt hI.boundaryE
        (TangentSpace hI.boundaryI) α₀).baseSet)
    (u v : hI.boundaryE) :
    boundaryFlatCharted (M := M) g α₀ b u v =
      inducedMetricInner (M := M) g b
        ((trivializationAt hI.boundaryE
            (TangentSpace hI.boundaryI) α₀).symm b u)
        ((trivializationAt hI.boundaryE
            (TangentSpace hI.boundaryI) α₀).symm b v) := by
  unfold boundaryFlatCharted
  rw [hom_trivializationAt_apply]
  rw [inCoordinates_apply_eq₂ (𝕜 := ℝ) hb_bdy hb_bdy (Set.mem_univ _)]
  change (trivializationAt ℝ (Bundle.Trivial (BoundaryManifold I M) ℝ) α₀).linearMapAt ℝ b _ = _
  change (Bundle.Trivial.trivialization (BoundaryManifold I M) ℝ).linearMapAt ℝ b _ = _
  rw [Bundle.Trivial.linearMapAt_trivialization (𝕜 := ℝ) (B := BoundaryManifold I M) (F := ℝ) b]
  rfl
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private lemma boundaryFlatCharted_isInvertible_of_mem
    (α₀ : BoundaryManifold I M) {b : BoundaryManifold I M}
    (hb_bdy : b ∈ (trivializationAt hI.boundaryE
        (TangentSpace hI.boundaryI) α₀).baseSet) :
    (boundaryFlatCharted (M := M) g α₀ b).IsInvertible := by
  classical
  obtain ⟨L_cle, hL_eq⟩ := inducedMetricInner_isInvertible (M := M) g b
  let T : hI.boundaryE ≃L[ℝ] hI.boundaryE :=
    (trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) α₀).continuousLinearEquivAt ℝ b
      hb_bdy
  let φ : hI.boundaryE ≃L[ℝ] (hI.boundaryE →L[ℝ] ℝ) :=
    T.symm.trans (L_cle.trans (T.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)))
  refine ⟨φ, ?_⟩
  ext u v
  change ((T.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)) (L_cle (T.symm u))) v = _
  simp only [ContinuousLinearEquiv.arrowCongr_apply, ContinuousLinearEquiv.refl_apply]
  have h_eq_LCle : (L_cle : hI.boundaryE →L[ℝ] (hI.boundaryE →L[ℝ] ℝ)) =
      inducedMetricInner (M := M) g b := hL_eq
  have h_lhs : L_cle (T.symm u) (T.symm v) =
      inducedMetricInner (M := M) g b (T.symm u) (T.symm v) := by
    rw [show L_cle (T.symm u) (T.symm v) =
        (L_cle : hI.boundaryE →L[ℝ] (hI.boundaryE →L[ℝ] ℝ)) (T.symm u) (T.symm v) from rfl]
    rw [h_eq_LCle]
  rw [h_lhs]
  have h_T_symm_u : (T.symm u : hI.boundaryE) =
      (trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) α₀).symm b u := rfl
  have h_T_symm_v : (T.symm v : hI.boundaryE) =
      (trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) α₀).symm b v := rfl
  rw [h_T_symm_u, h_T_symm_v]
  rw [boundaryFlatCharted_apply_of_mem (M := M) g α₀ hb_bdy u v]

private noncomputable def boundaryComponentOfInwardAtCharted
    (α₀ : BoundaryManifold I M) (b : BoundaryManifold I M) : hI.boundaryE :=
  (boundaryFlatChartedInv (M := M) g α₀ b)
    (boundaryFunOfInwardAtChartedCLM (M := M) g α₀ b)
omit [InnerProductSpace ℝ E] in
omit [FiniteDimensional ℝ E] in
private lemma boundaryComponentOfInwardAtCharted_contMDiffAt
    (α₀ : BoundaryManifold I M) :
    ContMDiffAt hI.boundaryI 𝓘(ℝ, hI.boundaryE) ∞
      (boundaryComponentOfInwardAtCharted (M := M) g α₀) α₀ :=
  (boundaryFlatChartedInv_contMDiffAt (M := M) g α₀).clm_apply
    (boundaryFunOfInwardAtChartedCLM_contMDiffAt (M := M) g α₀)
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private lemma boundaryFlatCharted_clmAt_bdy_BC_eq
    (α₀ : BoundaryManifold I M) {b : BoundaryManifold I M}
    (hb_amb : (b : M) ∈ (chartAt H (α₀ : M)).source)
    (hb_bdy : b ∈ (chartAt hI.boundaryH α₀).source) :
    boundaryFlatCharted (M := M) g α₀ b
      ((trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) α₀).continuousLinearMapAt
        ℝ b (boundaryComponentOfInwardAt (M := M) g α₀ b)) =
      boundaryFunOfInwardAtChartedCLM (M := M) g α₀ b := by
  refine ContinuousLinearMap.ext fun v => ?_
  have hb_bdy_baseSet : b ∈ (trivializationAt hI.boundaryE
      (TangentSpace hI.boundaryI) α₀).baseSet := hb_bdy
  rw [boundaryFlatCharted_apply_of_mem (M := M) g α₀ hb_bdy_baseSet
    ((trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) α₀).continuousLinearMapAt
        ℝ b (boundaryComponentOfInwardAt (M := M) g α₀ b)) v]
  have h_round_BC :
      ((trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) α₀).symm b
          ((trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) α₀).continuousLinearMapAt
            ℝ b (boundaryComponentOfInwardAt (M := M) g α₀ b))) =
        boundaryComponentOfInwardAt (M := M) g α₀ b := by
    have := (trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) α₀).symmL_continuousLinearMapAt
      (R := ℝ) hb_bdy_baseSet (boundaryComponentOfInwardAt (M := M) g α₀ b)
    simpa using this
  rw [h_round_BC]
  rw [inducedMetricInner_boundaryComponentOfInwardAt (M := M) g α₀ b
    ((trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) α₀).symm b v)]
  rw [boundaryFunOfInwardAtChartedCLM_apply_of_mem (M := M) g α₀ hb_amb hb_bdy v]
  rfl
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private lemma boundaryComponentOfInwardAtCharted_eq
    (α₀ : BoundaryManifold I M) {b : BoundaryManifold I M}
    (hb_amb : (b : M) ∈ (chartAt H (α₀ : M)).source)
    (hb_bdy : b ∈ (chartAt hI.boundaryH α₀).source) :
    boundaryComponentOfInwardAtCharted (M := M) g α₀ b =
      (trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) α₀).continuousLinearMapAt
        ℝ b (boundaryComponentOfInwardAt (M := M) g α₀ b) := by
  unfold boundaryComponentOfInwardAtCharted boundaryFlatChartedInv
  have h_inv := boundaryFlatCharted_isInvertible_of_mem (M := M) g α₀ hb_bdy
  have h_eq := boundaryFlatCharted_clmAt_bdy_BC_eq (M := M) g α₀ hb_amb hb_bdy
  rw [← h_eq]
  exact (ContinuousLinearMap.IsInvertible.inverse_apply_eq h_inv).mpr rfl
omit [InnerProductSpace ℝ E] in
omit [FiniteDimensional ℝ E] in
private lemma inwardTangentialPartAtCharted_contMDiffAt
    (α₀ : BoundaryManifold I M) :
    ContMDiffAt hI.boundaryI 𝓘(ℝ, E) ∞
      (fun b : BoundaryManifold I M =>
        dinclITC (M := M) α₀ b (boundaryComponentOfInwardAtCharted (M := M) g α₀ b)) α₀ :=
  dinclITC_apply_contMDiffAt (M := M)
    (boundaryComponentOfInwardAtCharted_contMDiffAt (M := M) g α₀)
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private lemma inwardTangentialPartAtCharted_eq
    (α₀ : BoundaryManifold I M) {b : BoundaryManifold I M}
    (hb_amb : (b : M) ∈ (chartAt H (α₀ : M)).source)
    (hb_bdy : b ∈ (chartAt hI.boundaryH α₀).source) :
    dinclITC (M := M) α₀ b (boundaryComponentOfInwardAtCharted (M := M) g α₀ b) =
      (trivializationAt E (TangentSpace I) (α₀ : M)).continuousLinearMapAt ℝ
        (b : M) (inwardTangentialPartAt (M := M) g α₀ b) := by
  rw [dinclITC_apply (M := M) α₀ hb_amb hb_bdy]
  rw [boundaryComponentOfInwardAtCharted_eq (M := M) g α₀ hb_amb hb_bdy]
  have hb_bdy_baseSet : b ∈ (trivializationAt hI.boundaryE
      (TangentSpace hI.boundaryI) α₀).baseSet := hb_bdy
  have h_round_bdy :
      (((trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) α₀).symmL ℝ b)
          ((trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) α₀).continuousLinearMapAt
            ℝ b (boundaryComponentOfInwardAt (M := M) g α₀ b))) =
        boundaryComponentOfInwardAt (M := M) g α₀ b := by
    have := (trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) α₀).symmL_continuousLinearMapAt
      (R := ℝ) hb_bdy_baseSet (boundaryComponentOfInwardAt (M := M) g α₀ b)
    simpa using this
  rw [h_round_bdy]
  rfl
omit [InnerProductSpace ℝ E] in
omit [FiniteDimensional ℝ E] in
private lemma outwardDirAt_section_contMDiffAt
    (α₀ : BoundaryManifold I M) :
    ContMDiffAt hI.boundaryI (I.prod 𝓘(ℝ, E)) ∞
      (fun b : BoundaryManifold I M =>
        TotalSpace.mk' E (b : M) (outwardDirAt (M := M) g α₀ b)) α₀ := by
  classical
  set T_amb := trivializationAt E (TangentSpace I) (α₀ : M) with hT_amb_def
  have hα_amb : (α₀ : M) ∈ T_amb.baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' (α₀ : M)
  refine (T_amb.contMDiffAt_iff (n := ∞)
    (f := fun b : BoundaryManifold I M =>
      TotalSpace.mk' E (b : M) (outwardDirAt (M := M) g α₀ b))
    (IM := hI.boundaryI) (x₀ := α₀) ?_).mpr ?_
  · change (TotalSpace.mk' E (α₀ : M)
      (outwardDirAt (M := M) g α₀ α₀)) ∈ T_amb.source
    rw [Trivialization.mem_source]
    change (α₀ : M) ∈ T_amb.baseSet
    simp only [hT_amb_def]
    exact FiberBundle.mem_baseSet_trivializationAt' (α₀ : M)
  refine ⟨?_, ?_⟩
  · convert (boundaryInclusion_contMDiff (I := I) (M := M)).contMDiffAt using 1
  · have h_inwardTangChart_at : ContMDiffAt hI.boundaryI 𝓘(ℝ, E) ∞
        (fun b : BoundaryManifold I M =>
          dinclITC (M := M) α₀ b (boundaryComponentOfInwardAtCharted (M := M) g α₀ b)) α₀ :=
      inwardTangentialPartAtCharted_contMDiffAt (M := M) g α₀
    have h_const : ContMDiffAt hI.boundaryI 𝓘(ℝ, E) ∞
        (fun _ : BoundaryManifold I M => hI.inwardCoordE) α₀ := contMDiffAt_const
    have h_sub : ContMDiffAt hI.boundaryI 𝓘(ℝ, E) ∞
        (fun b : BoundaryManifold I M =>
          dinclITC (M := M) α₀ b (boundaryComponentOfInwardAtCharted (M := M) g α₀ b) -
            hI.inwardCoordE) α₀ :=
      h_inwardTangChart_at.sub h_const
    refine h_sub.congr_of_eventuallyEq ?_
    have h_nhds_amb : ∀ᶠ b : BoundaryManifold I M in 𝓝 α₀,
        (b : M) ∈ (chartAt H (α₀ : M)).source := by
      have h_continuous : Continuous (fun b : BoundaryManifold I M => (b : M)) :=
        continuous_subtype_val
      exact h_continuous.continuousAt.preimage_mem_nhds
        ((chartAt H (α₀ : M)).open_source.mem_nhds (mem_chart_source H _))
    have h_nhds_bdy : ∀ᶠ b : BoundaryManifold I M in 𝓝 α₀,
        b ∈ (chartAt hI.boundaryH α₀).source :=
      (chartAt hI.boundaryH α₀).open_source.mem_nhds (mem_chart_source _ _)
    filter_upwards [h_nhds_amb, h_nhds_bdy] with b hb_amb hb_bdy
    have hb_amb_baseSet : (b : M) ∈ T_amb.baseSet := by
      simp only [hT_amb_def]
      rw [trivializationAt_baseSet_eq_chartAt_source]
      exact hb_amb
    rw [show (T_amb ⟨(b : M), outwardDirAt (M := M) g α₀ b⟩).2 =
        T_amb.continuousLinearMapAt ℝ (b : M) (outwardDirAt (M := M) g α₀ b) from ?_]
    swap
    · rw [Trivialization.continuousLinearMapAt_apply]
      rw [T_amb.coe_linearMapAt_of_mem hb_amb_baseSet]
    rw [outwardDirAt_def, map_sub]
    rw [← inwardTangentialPartAtCharted_eq (M := M) g α₀ hb_amb hb_bdy]
    have h_inwardCoord_chartTriv :
        T_amb.continuousLinearMapAt ℝ (b : M) (inwardCoordAt (M := M) α₀ b) =
          hI.inwardCoordE := by
      rw [show T_amb.continuousLinearMapAt ℝ (b : M) (inwardCoordAt (M := M) α₀ b) =
          (T_amb ⟨(b : M), inwardCoordAt (M := M) α₀ b⟩).2 from ?_]
      · simp only [hT_amb_def]
        exact chart_triv_second_inwardCoordAt (M := M) α₀ hb_amb_baseSet
      · rw [Trivialization.continuousLinearMapAt_apply]
        rw [T_amb.coe_linearMapAt_of_mem hb_amb_baseSet]
    rw [h_inwardCoord_chartTriv]
omit [InnerProductSpace ℝ E] in
omit [FiniteDimensional ℝ E] in
private lemma outwardDirAt_norm_squared_contMDiffAt
    (α₀ : BoundaryManifold I M) :
    ContMDiffAt hI.boundaryI 𝓘(ℝ) ∞
      (fun b : BoundaryManifold I M =>
        g.inner (b : M) (outwardDirAt (M := M) g α₀ b)
          (outwardDirAt (M := M) g α₀ b)) α₀ := by
  classical
  have h_outwardDir_section : ContMDiffAt hI.boundaryI (I.prod 𝓘(ℝ, E)) ∞
      (fun b : BoundaryManifold I M =>
        TotalSpace.mk' E (b : M) (outwardDirAt (M := M) g α₀ b)) α₀ :=
    outwardDirAt_section_contMDiffAt (M := M) g α₀
  have h_inclusion_at : ContMDiffAt hI.boundaryI I ∞ (boundaryInclusion I M) α₀ :=
    boundaryInclusion_contMDiff.contMDiffAt
  have h_g_section : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun y : M =>
        TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun y : M =>
            TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
          y (g.inner y)) := g.contMDiff
  have h_g_at : ContMDiffAt hI.boundaryI (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b : BoundaryManifold I M =>
        TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun y : M =>
            TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
          (b : M) (g.inner (b : M))) α₀ :=
    h_g_section.contMDiffAt.comp α₀ h_inclusion_at
  have h_apply : ContMDiffAt hI.boundaryI (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun b : BoundaryManifold I M =>
        TotalSpace.mk' ℝ (E := fun y : M => ℝ)
          (b : M)
          (g.inner (b : M) (outwardDirAt (M := M) g α₀ b)
            (outwardDirAt (M := M) g α₀ b))) α₀ :=
    h_g_at.clm_bundle_apply₂ h_outwardDir_section h_outwardDir_section
  rw [Bundle.contMDiffAt_totalSpace] at h_apply
  exact h_apply.2
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private lemma outwardDirAt_norm_squared_pos_basepoint
    (α₀ : BoundaryManifold I M) :
    0 < g.inner (α₀ : M) (outwardDirAt (M := M) g α₀ α₀)
        (outwardDirAt (M := M) g α₀ α₀) := by
  rw [outwardDirAt_self (M := M) g α₀]
  exact g_inner_outwardDir_pos (M := M) g α₀
omit [InnerProductSpace ℝ E] in
omit [FiniteDimensional ℝ E] in
theorem outwardNormalAt_section_contMDiffAt
    (α₀ : BoundaryManifold I M) :
    ContMDiffAt hI.boundaryI (I.prod 𝓘(ℝ, E)) ∞
      (fun b : BoundaryManifold I M =>
        TotalSpace.mk' E (b : M) (outwardNormalAt (M := M) g α₀ b)) α₀ := by
  classical
  have h_q_smooth : ContMDiffAt hI.boundaryI 𝓘(ℝ) ∞
      (fun b : BoundaryManifold I M =>
        g.inner (b : M) (outwardDirAt (M := M) g α₀ b)
          (outwardDirAt (M := M) g α₀ b)) α₀ :=
    outwardDirAt_norm_squared_contMDiffAt (M := M) g α₀
  have h_q_pos_at : 0 < g.inner (α₀ : M) (outwardDirAt (M := M) g α₀ α₀)
      (outwardDirAt (M := M) g α₀ α₀) :=
    outwardDirAt_norm_squared_pos_basepoint (M := M) g α₀
  have h_q_ne : g.inner (α₀ : M) (outwardDirAt (M := M) g α₀ α₀)
      (outwardDirAt (M := M) g α₀ α₀) ≠ 0 := ne_of_gt h_q_pos_at
  have h_q_sqrt_at : ContMDiffAt hI.boundaryI 𝓘(ℝ) ∞
      (fun b : BoundaryManifold I M =>
        Real.sqrt (g.inner (b : M) (outwardDirAt (M := M) g α₀ b)
          (outwardDirAt (M := M) g α₀ b))) α₀ := by
    have h_sqrt_at : ContDiffAt ℝ ∞ Real.sqrt
        (g.inner (α₀ : M) (outwardDirAt (M := M) g α₀ α₀)
          (outwardDirAt (M := M) g α₀ α₀)) := Real.contDiffAt_sqrt h_q_ne
    exact h_sqrt_at.contMDiffAt.comp α₀ h_q_smooth
  have h_sqrt_pos : 0 < Real.sqrt (g.inner (α₀ : M)
      (outwardDirAt (M := M) g α₀ α₀)
      (outwardDirAt (M := M) g α₀ α₀)) := Real.sqrt_pos.mpr h_q_pos_at
  have h_sqrt_ne : Real.sqrt (g.inner (α₀ : M) (outwardDirAt (M := M) g α₀ α₀)
      (outwardDirAt (M := M) g α₀ α₀)) ≠ 0 := ne_of_gt h_sqrt_pos
  have h_sqrt_inv_at : ContMDiffAt hI.boundaryI 𝓘(ℝ) ∞
      (fun b : BoundaryManifold I M =>
        (Real.sqrt (g.inner (b : M) (outwardDirAt (M := M) g α₀ b)
          (outwardDirAt (M := M) g α₀ b)))⁻¹) α₀ :=
    h_q_sqrt_at.inv₀ h_sqrt_ne
  have h_outwardDir_section : ContMDiffAt hI.boundaryI (I.prod 𝓘(ℝ, E)) ∞
      (fun b : BoundaryManifold I M =>
        TotalSpace.mk' E (b : M) (outwardDirAt (M := M) g α₀ b)) α₀ :=
    outwardDirAt_section_contMDiffAt (M := M) g α₀
  set T_amb := trivializationAt E (TangentSpace I) (α₀ : M) with hT_amb_def
  have hα_amb : (α₀ : M) ∈ T_amb.baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' (α₀ : M)
  refine (T_amb.contMDiffAt_iff (n := ∞)
    (f := fun b : BoundaryManifold I M =>
      TotalSpace.mk' E (b : M) (outwardNormalAt (M := M) g α₀ b))
    (IM := hI.boundaryI) (x₀ := α₀) ?_).mpr ?_
  · change (TotalSpace.mk' E (α₀ : M)
      (outwardNormalAt (M := M) g α₀ α₀)) ∈ T_amb.source
    rw [Trivialization.mem_source]
    change (α₀ : M) ∈ T_amb.baseSet
    simp only [hT_amb_def]
    exact FiberBundle.mem_baseSet_trivializationAt' (α₀ : M)
  refine ⟨?_, ?_⟩
  · convert (boundaryInclusion_contMDiff (I := I) (M := M)).contMDiffAt using 1
  · have h_outwardDirCharted_at : ContMDiffAt hI.boundaryI 𝓘(ℝ, E) ∞
        (fun b : BoundaryManifold I M =>
          (T_amb ⟨(b : M), outwardDirAt (M := M) g α₀ b⟩).2) α₀ := by
      rw [Bundle.contMDiffAt_totalSpace] at h_outwardDir_section
      exact h_outwardDir_section.2
    have h_smul_smooth : ContMDiffAt hI.boundaryI 𝓘(ℝ, E) ∞
        (fun b : BoundaryManifold I M =>
          (Real.sqrt (g.inner (b : M) (outwardDirAt (M := M) g α₀ b)
            (outwardDirAt (M := M) g α₀ b)))⁻¹ •
            (T_amb ⟨(b : M), outwardDirAt (M := M) g α₀ b⟩).2) α₀ :=
      h_sqrt_inv_at.smul h_outwardDirCharted_at
    refine h_smul_smooth.congr_of_eventuallyEq ?_
    have h_q_continuous : ContinuousAt
        (fun b : BoundaryManifold I M =>
          g.inner (b : M) (outwardDirAt (M := M) g α₀ b)
            (outwardDirAt (M := M) g α₀ b)) α₀ := h_q_smooth.continuousAt
    have h_q_pos_nhds : ∀ᶠ b : BoundaryManifold I M in 𝓝 α₀,
        0 < g.inner (b : M) (outwardDirAt (M := M) g α₀ b)
          (outwardDirAt (M := M) g α₀ b) := by
      filter_upwards [h_q_continuous (eventually_gt_nhds h_q_pos_at)] with b hb
      exact hb
    have h_nhds_amb : ∀ᶠ b : BoundaryManifold I M in 𝓝 α₀,
        (b : M) ∈ T_amb.baseSet := by
      have h_continuous : Continuous (fun b : BoundaryManifold I M => (b : M)) :=
        continuous_subtype_val
      exact h_continuous.continuousAt.preimage_mem_nhds (T_amb.open_baseSet.mem_nhds hα_amb)
    filter_upwards [h_q_pos_nhds, h_nhds_amb] with b hb_q_pos hb_amb_baseSet
    have h_norm_formula : outwardNormalAt (M := M) g α₀ b =
        (Real.sqrt (g.inner (b : M) (outwardDirAt (M := M) g α₀ b)
            (outwardDirAt (M := M) g α₀ b)))⁻¹ • outwardDirAt (M := M) g α₀ b := by
      unfold outwardNormalAt
      rw [dif_pos hb_q_pos]
    rw [h_norm_formula]
    rw [show (T_amb ⟨(b : M), (Real.sqrt (g.inner (b : M) (outwardDirAt (M := M) g α₀ b)
          (outwardDirAt (M := M) g α₀ b)))⁻¹ • outwardDirAt (M := M) g α₀ b⟩).2 =
        T_amb.continuousLinearMapAt ℝ (b : M)
          ((Real.sqrt (g.inner (b : M) (outwardDirAt (M := M) g α₀ b)
            (outwardDirAt (M := M) g α₀ b)))⁻¹ • outwardDirAt (M := M) g α₀ b) from ?_]
    swap
    · rw [Trivialization.continuousLinearMapAt_apply]
      rw [T_amb.coe_linearMapAt_of_mem hb_amb_baseSet]
    rw [map_smul]
    rw [show (T_amb ⟨(b : M), outwardDirAt (M := M) g α₀ b⟩).2 =
        T_amb.continuousLinearMapAt ℝ (b : M) (outwardDirAt (M := M) g α₀ b) from ?_]
    · rw [Trivialization.continuousLinearMapAt_apply]
      rw [T_amb.coe_linearMapAt_of_mem hb_amb_baseSet]
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private lemma metricPullback_surjective
    (g : Measure.SmoothRiemannianMetric I M) (y : BoundaryManifold I M) :
    Function.Surjective (metricPullback (M := M) g y) := by
  intro α
  set u : hI.boundaryE := (boundaryFlatMap (M := M) g y).symm α with hu_def
  refine ⟨boundaryInclusionMfderiv (M := M) y u, ?_⟩
  refine LinearMap.ext fun w => ?_
  rw [metricPullback_apply]
  rw [show g.inner (y : M) (boundaryInclusionMfderiv (M := M) y u) (boundaryInclusionMfderiv (M := M) y w) =
        inducedMetricInner (M := M) g y u w from
        (inducedMetricInner_apply g y u w).symm]
  rw [show inducedMetricInner (M := M) g y u w = boundaryFlatMap (M := M) g y u w from rfl]
  have h := (boundaryFlatMap (M := M) g y).apply_symm_apply α
  exact congrArg (fun L : hI.boundaryE →ₗ[ℝ] ℝ => L w) h
omit [InnerProductSpace ℝ E] in
private lemma finrank_ker_metricPullback_eq_one
    (g : Measure.SmoothRiemannianMetric I M) (y : BoundaryManifold I M) :
    Module.finrank ℝ (LinearMap.ker (metricPullback (M := M) g y)) = 1 := by
  by_cases hN : Nonempty hI.boundaryH
  · haveI := hN
    have h_rk_null :=
      LinearMap.finrank_range_add_finrank_ker (metricPullback (M := M) g y)
    have h_surj : Function.Surjective (metricPullback (M := M) g y) :=
      metricPullback_surjective (M := M) g y
    have h_range_top : LinearMap.range (metricPullback (M := M) g y) = ⊤ :=
      LinearMap.range_eq_top.mpr h_surj
    have h_finrank_range : Module.finrank ℝ
        (LinearMap.range (metricPullback (M := M) g y)) =
        Module.finrank ℝ (hI.boundaryE →ₗ[ℝ] ℝ) := by
      rw [h_range_top, finrank_top]
    have h_dual : Module.finrank ℝ (hI.boundaryE →ₗ[ℝ] ℝ) =
        Module.finrank ℝ hI.boundaryE := Subspace.dual_finrank_eq
    have h_source : Module.finrank ℝ (TangentSpace I (y : M)) = Module.finrank ℝ E := rfl
    have h_codim : Module.finrank ℝ hI.boundaryE + 1 = Module.finrank ℝ E :=
      hI.finrank_boundaryE_succ
    rw [h_finrank_range, h_dual] at h_rk_null
    omega
  · haveI : IsEmpty hI.boundaryH := not_nonempty_iff.mp hN
    haveI : IsEmpty (BoundaryManifold I M) :=
      BoundaryManifold.isEmpty_of_isEmpty_boundaryH (I := I)
    exact (IsEmpty.false y).elim
omit [InnerProductSpace ℝ E] in
theorem normalSubspace_finrank_one
    (g : Measure.SmoothRiemannianMetric I M) (y : BoundaryManifold I M) :
    Module.finrank ℝ (normalSubspace (M := M) g y) = 1 := by
  rw [← ker_metricPullback_eq_normalSubspace (M := M) g y]
  exact finrank_ker_metricPullback_eq_one (M := M) g y

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] hI in
private lemma unit_vectors_in_1dim_equal_or_opposite
    (g : Measure.SmoothRiemannianMetric I M) {y : BoundaryManifold I M}
    {V : Submodule ℝ (TangentSpace I (y : M))}
    (hV : Module.finrank ℝ V = 1)
    {v w : TangentSpace I (y : M)} (hv : v ∈ V) (hw : w ∈ V)
    (hv_unit : g.inner (y : M) v v = 1) (hw_unit : g.inner (y : M) w w = 1) :
    v = w ∨ v = -w := by
  classical
  let v' : V := ⟨v, hv⟩
  let w' : V := ⟨w, hw⟩
  have hv_ne : v ≠ 0 := by
    intro h0
    rw [h0] at hv_unit
    simp at hv_unit
  have hv'_ne : v' ≠ 0 := by
    intro h0
    apply hv_ne
    exact congrArg Subtype.val h0
  obtain ⟨c, hc⟩ :=
    exists_smul_eq_of_finrank_eq_one (K := ℝ) (V := V) hV hv'_ne w'
  have hc_amb : c • v = w := by
    have := congrArg Subtype.val hc
    simpa [v', w'] using this
  have h_g_w_w : g.inner (y : M) w w = c * c * g.inner (y : M) v v := by
    rw [show w = c • v from hc_amb.symm]
    rw [show g.inner (y : M) (c • v) = c • (g.inner (y : M) v) from
          map_smul _ _ _]
    rw [ContinuousLinearMap.smul_apply, smul_eq_mul,
        ContinuousLinearMap.map_smul, smul_eq_mul]
    ring
  have hc_sq : c * c = 1 := by
    rw [hv_unit, mul_one] at h_g_w_w
    rw [h_g_w_w] at hw_unit
    exact hw_unit
  have hc_eq : c = 1 ∨ c = -1 := by
    have hc_sq_one : c ^ 2 = 1 := by rw [sq]; exact hc_sq
    exact sq_eq_one_iff.mp hc_sq_one
  rcases hc_eq with h_pos | h_neg
  · left
    rw [show w = c • v from hc_amb.symm, h_pos, one_smul]
  · right
    rw [show w = c • v from hc_amb.symm, h_neg, neg_one_smul, neg_neg]
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private lemma outwardDirAt_eq_zero_iff_inwardCoordAt_mem_range
    (g : Measure.SmoothRiemannianMetric I M) (α y : BoundaryManifold I M) :
    outwardDirAt (M := M) g α y = 0 ↔
      inwardCoordAt (M := M) α y ∈ Set.range (boundaryInclusionMfderiv (M := M) y) := by
  refine ⟨?_, ?_⟩
  · intro h0
    rw [outwardDirAt_def, sub_eq_zero] at h0
    rw [← h0, inwardTangentialPartAt_def]
    exact ⟨boundaryComponentOfInwardAt (M := M) g α y, rfl⟩
  · rintro ⟨u, hu⟩
    rw [outwardDirAt_def, sub_eq_zero, inwardTangentialPartAt_def, ← hu]
    apply congrArg (boundaryInclusionMfderiv (M := M) y)
    have h_pair : ∀ w : hI.boundaryE,
        inducedMetricInner (M := M) g y
          (boundaryComponentOfInwardAt (M := M) g α y) w =
        inducedMetricInner (M := M) g y u w := by
      intro w
      rw [inducedMetricInner_boundaryComponentOfInwardAt (M := M) g α y w]
      rw [inducedMetricInner_apply]
      rw [hu]
    have h_lin_eq : boundaryFlatLinear (M := M) g y
        (boundaryComponentOfInwardAt (M := M) g α y) =
        boundaryFlatLinear (M := M) g y u := by
      refine LinearMap.ext fun w => ?_
      rw [boundaryFlatLinear_apply, boundaryFlatLinear_apply]
      exact h_pair w
    exact boundaryFlatLinear_injective (M := M) g y h_lin_eq
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private lemma outwardDirAt_ne_zero_of_transverse
    (g : Measure.SmoothRiemannianMetric I M) (α y : BoundaryManifold I M)
    (h_trans : inwardCoordAt (M := M) α y ∉ Set.range (boundaryInclusionMfderiv (M := M) y)) :
    outwardDirAt (M := M) g α y ≠ 0 := by
  intro h0
  exact h_trans
    ((outwardDirAt_eq_zero_iff_inwardCoordAt_mem_range (M := M) g α y).mp h0)
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private lemma g_inner_outwardDirAt_pos_of_transverse
    (g : Measure.SmoothRiemannianMetric I M) (α y : BoundaryManifold I M)
    (h_trans : inwardCoordAt (M := M) α y ∉ Set.range (boundaryInclusionMfderiv (M := M) y)) :
    0 < g.inner (y : M) (outwardDirAt (M := M) g α y)
        (outwardDirAt (M := M) g α y) :=
  g.pos (y : M) _ (outwardDirAt_ne_zero_of_transverse (M := M) g α y h_trans)
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private lemma g_inner_outwardDirAt_inwardCoordAt_neg_of_transverse
    (g : Measure.SmoothRiemannianMetric I M) (α y : BoundaryManifold I M)
    (h_trans : inwardCoordAt (M := M) α y ∉ Set.range (boundaryInclusionMfderiv (M := M) y)) :
    g.inner (y : M) (outwardDirAt (M := M) g α y)
        (inwardCoordAt (M := M) α y) < 0 := by
  have hpos : 0 < g.inner (y : M) (outwardDirAt (M := M) g α y)
        (outwardDirAt (M := M) g α y) :=
    g_inner_outwardDirAt_pos_of_transverse (M := M) g α y h_trans
  have h_id : g.inner (y : M) (outwardDirAt (M := M) g α y)
        (inwardCoordAt (M := M) α y) =
      -g.inner (y : M) (outwardDirAt (M := M) g α y)
        (outwardDirAt (M := M) g α y) := by
    rw [g_inner_outwardDirAt_inwardCoordAt (M := M) g α y,
        g_inner_outwardDirAt_outwardDirAt (M := M) g α y]
    ring
  rw [h_id]
  linarith
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private lemma outwardNormalAt_norm_one_of_transverse
    (g : Measure.SmoothRiemannianMetric I M) (α y : BoundaryManifold I M)
    (h_trans : inwardCoordAt (M := M) α y ∉ Set.range (boundaryInclusionMfderiv (M := M) y)) :
    g.inner (y : M) (outwardNormalAt (M := M) g α y)
        (outwardNormalAt (M := M) g α y) = 1 := by
  set q : ℝ := g.inner (y : M) (outwardDirAt (M := M) g α y)
      (outwardDirAt (M := M) g α y) with hq_def
  have hq_pos : 0 < q :=
    g_inner_outwardDirAt_pos_of_transverse (M := M) g α y h_trans
  have hq_ne : q ≠ 0 := ne_of_gt hq_pos
  have hsq_pos : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq_pos
  have hsq_ne : Real.sqrt q ≠ 0 := ne_of_gt hsq_pos
  have hsq_sq : Real.sqrt q * Real.sqrt q = q := Real.mul_self_sqrt hq_pos.le
  have h_normal_eq : outwardNormalAt (M := M) g α y =
      (Real.sqrt q)⁻¹ • outwardDirAt (M := M) g α y := by
    unfold outwardNormalAt
    rw [dif_pos hq_pos]
  rw [h_normal_eq]
  have h1 : g.inner (y : M) ((Real.sqrt q)⁻¹ • outwardDirAt (M := M) g α y)
          ((Real.sqrt q)⁻¹ • outwardDirAt (M := M) g α y) =
      (Real.sqrt q)⁻¹ • (g.inner (y : M) (outwardDirAt (M := M) g α y))
          ((Real.sqrt q)⁻¹ • outwardDirAt (M := M) g α y) := by
    rw [show g.inner (y : M) ((Real.sqrt q)⁻¹ • outwardDirAt (M := M) g α y) =
        (Real.sqrt q)⁻¹ • g.inner (y : M) (outwardDirAt (M := M) g α y) from
          map_smul _ _ _]
    rfl
  rw [h1]
  rw [show (g.inner (y : M) (outwardDirAt (M := M) g α y))
        ((Real.sqrt q)⁻¹ • outwardDirAt (M := M) g α y) =
      (Real.sqrt q)⁻¹ • g.inner (y : M) (outwardDirAt (M := M) g α y)
        (outwardDirAt (M := M) g α y) from
    ContinuousLinearMap.map_smul _ _ _]
  rw [show g.inner (y : M) (outwardDirAt (M := M) g α y)
        (outwardDirAt (M := M) g α y) = q from rfl]
  rw [smul_eq_mul, smul_eq_mul]
  rw [show (Real.sqrt q)⁻¹ * ((Real.sqrt q)⁻¹ * q) = q / (Real.sqrt q * Real.sqrt q) by
    field_simp]
  rw [hsq_sq]
  exact div_self hq_ne
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private lemma outwardNormalAt_mem_normalSubspace
    (g : Measure.SmoothRiemannianMetric I M) (α y : BoundaryManifold I M) :
    outwardNormalAt (M := M) g α y ∈ normalSubspace (M := M) g y := by
  unfold outwardNormalAt
  classical
  by_cases h_pos : 0 < g.inner (y : M) (outwardDirAt (M := M) g α y)
      (outwardDirAt (M := M) g α y)
  · rw [dif_pos h_pos]
    exact (normalSubspace (M := M) g y).smul_mem _
      (outwardDirAt_mem_normalSubspace (M := M) g α y)
  · rw [dif_neg h_pos]
    exact (normalSubspace (M := M) g y).zero_mem
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private lemma outwardNormalAt_inner_inwardCoordAt_neg_of_transverse
    (g : Measure.SmoothRiemannianMetric I M) (α y : BoundaryManifold I M)
    (h_trans : inwardCoordAt (M := M) α y ∉ Set.range (boundaryInclusionMfderiv (M := M) y)) :
    g.inner (y : M) (outwardNormalAt (M := M) g α y)
        (inwardCoordAt (M := M) α y) < 0 := by
  have hq_pos : 0 < g.inner (y : M) (outwardDirAt (M := M) g α y)
      (outwardDirAt (M := M) g α y) :=
    g_inner_outwardDirAt_pos_of_transverse (M := M) g α y h_trans
  have h_normal_eq : outwardNormalAt (M := M) g α y =
      (Real.sqrt (g.inner (y : M) (outwardDirAt (M := M) g α y)
          (outwardDirAt (M := M) g α y)))⁻¹ • outwardDirAt (M := M) g α y := by
    unfold outwardNormalAt
    rw [dif_pos hq_pos]
  rw [h_normal_eq]
  rw [ContinuousLinearMap.map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  have hsq_pos : 0 < Real.sqrt (g.inner (y : M) (outwardDirAt (M := M) g α y)
      (outwardDirAt (M := M) g α y)) := Real.sqrt_pos.mpr hq_pos
  have hsq_inv_pos : 0 < (Real.sqrt (g.inner (y : M) (outwardDirAt (M := M) g α y)
      (outwardDirAt (M := M) g α y)))⁻¹ := inv_pos.mpr hsq_pos
  have hneg : g.inner (y : M) (outwardDirAt (M := M) g α y)
      (inwardCoordAt (M := M) α y) < 0 :=
    g_inner_outwardDirAt_inwardCoordAt_neg_of_transverse (M := M) g α y h_trans
  exact mul_neg_of_pos_of_neg hsq_inv_pos hneg

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private lemma inwardCoordAt_mem_range_iff_of_orientation
    (α₀ α₁ y : BoundaryManifold I M)
    (c : ℝ) (hc : 0 < c)
    (h_w : inwardCoordAt (M := M) α₀ y - c • inwardCoordAt (M := M) α₁ y ∈
        Set.range (boundaryInclusionMfderiv (M := M) y).toLinearMap) :
    inwardCoordAt (M := M) α₀ y ∈ Set.range (boundaryInclusionMfderiv (M := M) y) ↔
      inwardCoordAt (M := M) α₁ y ∈ Set.range (boundaryInclusionMfderiv (M := M) y) := by
  have h_range_eq : Set.range (boundaryInclusionMfderiv (M := M) y).toLinearMap =
      Set.range (boundaryInclusionMfderiv (M := M) y) := rfl
  rw [h_range_eq] at h_w
  rcases h_w with ⟨w', hw'⟩
  have hc_ne : c ≠ 0 := ne_of_gt hc
  refine ⟨fun h₀ => ?_, fun h₁ => ?_⟩
  · rcases h₀ with ⟨u, hu⟩
    refine ⟨c⁻¹ • (u - w'), ?_⟩
    have h_target : (c : ℝ) • inwardCoordAt (M := M) α₁ y =
        (boundaryInclusionMfderiv (M := M) y) u - (boundaryInclusionMfderiv (M := M) y) w' := by
      rw [hu, hw']; abel
    have h_inv_smul : (c : ℝ)⁻¹ • ((c : ℝ) • inwardCoordAt (M := M) α₁ y) =
        inwardCoordAt (M := M) α₁ y := by
      rw [← mul_smul, inv_mul_cancel₀ hc_ne, one_smul]
    have h_target_inv : inwardCoordAt (M := M) α₁ y =
        (c : ℝ)⁻¹ • ((boundaryInclusionMfderiv (M := M) y) u - (boundaryInclusionMfderiv (M := M) y) w') := by
      rw [← h_inv_smul, h_target]
      rfl
    rw [h_target_inv, ContinuousLinearMap.map_smul, map_sub]
  · rcases h₁ with ⟨u, hu⟩
    refine ⟨c • u + w', ?_⟩
    rw [map_add, ContinuousLinearMap.map_smul, hu]
    set vw : TangentSpace I (y : M) := boundaryInclusionMfderiv (M := M) y w' with hvw_def
    change (c : ℝ) • inwardCoordAt (M := M) α₁ y + vw = inwardCoordAt (M := M) α₀ y
    have hw'' : vw = inwardCoordAt (M := M) α₀ y -
        (c : ℝ) • inwardCoordAt (M := M) α₁ y := hw'
    rw [hw'']; abel

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private lemma inwardCoordAt_not_mem_range_iff_of_orientation
    (α₀ α₁ y : BoundaryManifold I M)
    (c : ℝ) (hc : 0 < c)
    (h_w : inwardCoordAt (M := M) α₀ y - c • inwardCoordAt (M := M) α₁ y ∈
        Set.range (boundaryInclusionMfderiv (M := M) y).toLinearMap) :
    inwardCoordAt (M := M) α₀ y ∉ Set.range (boundaryInclusionMfderiv (M := M) y) ↔
      inwardCoordAt (M := M) α₁ y ∉ Set.range (boundaryInclusionMfderiv (M := M) y) := by
  rw [not_iff_not]
  exact inwardCoordAt_mem_range_iff_of_orientation (M := M) α₀ α₁ y c hc h_w
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private lemma g_inner_outwardNormalAt_inwardCoordAt_other_neg
    (g : Measure.SmoothRiemannianMetric I M) (α₀ α₁ y : BoundaryManifold I M)
    (h_trans₁ : inwardCoordAt (M := M) α₁ y ∉ Set.range (boundaryInclusionMfderiv (M := M) y))
    (c : ℝ) (hc : 0 < c)
    (h_w : inwardCoordAt (M := M) α₀ y - c • inwardCoordAt (M := M) α₁ y ∈
        Set.range (boundaryInclusionMfderiv (M := M) y).toLinearMap) :
    g.inner (y : M) (outwardNormalAt (M := M) g α₁ y)
        (inwardCoordAt (M := M) α₀ y) < 0 := by
  have h_range_eq : Set.range (boundaryInclusionMfderiv (M := M) y).toLinearMap =
      Set.range (boundaryInclusionMfderiv (M := M) y) := rfl
  rw [h_range_eq] at h_w
  rcases h_w with ⟨w', hw'⟩
  set N₁ : TangentSpace I (y : M) := outwardNormalAt (M := M) g α₁ y with hN₁_def
  set v₀ : TangentSpace I (y : M) := inwardCoordAt (M := M) α₀ y with hv₀_def
  set v₁ : TangentSpace I (y : M) := inwardCoordAt (M := M) α₁ y with hv₁_def
  set vw : TangentSpace I (y : M) := boundaryInclusionMfderiv (M := M) y w' with hvw_def
  have hw'' : vw = v₀ - c • v₁ := hw'
  have hv₀_eq : v₀ = c • v₁ + vw := by rw [hw'']; abel
  rw [hv₀_eq, ContinuousLinearMap.map_add, ContinuousLinearMap.map_smul, smul_eq_mul]
  have h_orth : g.inner (y : M) N₁ vw = 0 := by
    rw [hvw_def]
    exact (outwardNormalAt_mem_normalSubspace (M := M) g α₁ y) w'
  rw [h_orth, add_zero]
  have h_neg : g.inner (y : M) N₁ v₁ < 0 :=
    outwardNormalAt_inner_inwardCoordAt_neg_of_transverse (M := M) g α₁ y h_trans₁
  exact mul_neg_of_pos_of_neg hc h_neg
omit [InnerProductSpace ℝ E] in
theorem outwardNormalAt_chart_invariance_of_orientation
    (g : Measure.SmoothRiemannianMetric I M) (α₀ α₁ y : BoundaryManifold I M)
    {c : ℝ} (hc : 0 < c)
    (h_w : inwardCoordAt (M := M) α₀ y - c • inwardCoordAt (M := M) α₁ y ∈
        Set.range (boundaryInclusionMfderiv (M := M) y).toLinearMap) :
    outwardNormalAt (M := M) g α₀ y = outwardNormalAt (M := M) g α₁ y := by
  classical
  by_cases h_trans₁ : inwardCoordAt (M := M) α₁ y ∈ Set.range (boundaryInclusionMfderiv (M := M) y)
  · have h_trans₀ : inwardCoordAt (M := M) α₀ y ∈ Set.range (boundaryInclusionMfderiv (M := M) y) := by
      have h_iff := inwardCoordAt_mem_range_iff_of_orientation (M := M) α₀ α₁ y c hc h_w
      exact h_iff.mpr h_trans₁
    have h0_α₀ : outwardDirAt (M := M) g α₀ y = 0 :=
      (outwardDirAt_eq_zero_iff_inwardCoordAt_mem_range (M := M) g α₀ y).mpr h_trans₀
    have h0_α₁ : outwardDirAt (M := M) g α₁ y = 0 :=
      (outwardDirAt_eq_zero_iff_inwardCoordAt_mem_range (M := M) g α₁ y).mpr h_trans₁
    have h_q_α₀ : g.inner (y : M) (outwardDirAt (M := M) g α₀ y)
        (outwardDirAt (M := M) g α₀ y) = 0 := by
      rw [h0_α₀]; simp
    have h_q_α₁ : g.inner (y : M) (outwardDirAt (M := M) g α₁ y)
        (outwardDirAt (M := M) g α₁ y) = 0 := by
      rw [h0_α₁]; simp
    have h_normal_α₀ : outwardNormalAt (M := M) g α₀ y = 0 := by
      unfold outwardNormalAt
      rw [dif_neg]
      rw [h_q_α₀]; exact lt_irrefl 0
    have h_normal_α₁ : outwardNormalAt (M := M) g α₁ y = 0 := by
      unfold outwardNormalAt
      rw [dif_neg]
      rw [h_q_α₁]; exact lt_irrefl 0
    rw [h_normal_α₀, h_normal_α₁]
  · have h_trans₁_ne : inwardCoordAt (M := M) α₁ y ∉ Set.range (boundaryInclusionMfderiv (M := M) y) :=
      h_trans₁
    have h_trans₀_ne : inwardCoordAt (M := M) α₀ y ∉ Set.range (boundaryInclusionMfderiv (M := M) y) := by
      have h_iff := inwardCoordAt_not_mem_range_iff_of_orientation (M := M) α₀ α₁ y c hc h_w
      exact h_iff.mpr h_trans₁_ne
    have hN₀_mem : outwardNormalAt (M := M) g α₀ y ∈ normalSubspace (M := M) g y :=
      outwardNormalAt_mem_normalSubspace (M := M) g α₀ y
    have hN₁_mem : outwardNormalAt (M := M) g α₁ y ∈ normalSubspace (M := M) g y :=
      outwardNormalAt_mem_normalSubspace (M := M) g α₁ y
    have hN₀_unit : g.inner (y : M) (outwardNormalAt (M := M) g α₀ y)
        (outwardNormalAt (M := M) g α₀ y) = 1 :=
      outwardNormalAt_norm_one_of_transverse (M := M) g α₀ y h_trans₀_ne
    have hN₁_unit : g.inner (y : M) (outwardNormalAt (M := M) g α₁ y)
        (outwardNormalAt (M := M) g α₁ y) = 1 :=
      outwardNormalAt_norm_one_of_transverse (M := M) g α₁ y h_trans₁_ne
    have h_finrank : Module.finrank ℝ (normalSubspace (M := M) g y) = 1 :=
      normalSubspace_finrank_one (M := M) g y
    have h_eq_or_neg :=
      unit_vectors_in_1dim_equal_or_opposite (M := M) g h_finrank hN₀_mem hN₁_mem
        hN₀_unit hN₁_unit
    have h_sign : g.inner (y : M) (outwardNormalAt (M := M) g α₁ y)
        (inwardCoordAt (M := M) α₀ y) < 0 :=
      g_inner_outwardNormalAt_inwardCoordAt_other_neg (M := M) g α₀ α₁ y
        h_trans₁_ne c hc h_w
    have h_sign₀ : g.inner (y : M) (outwardNormalAt (M := M) g α₀ y)
        (inwardCoordAt (M := M) α₀ y) < 0 :=
      outwardNormalAt_inner_inwardCoordAt_neg_of_transverse (M := M) g α₀ y h_trans₀_ne
    rcases h_eq_or_neg with h_eq | h_neg_eq
    · exact h_eq
    · exfalso
      have h_contra : g.inner (y : M) (outwardNormalAt (M := M) g α₀ y)
          (inwardCoordAt (M := M) α₀ y) =
          -g.inner (y : M) (outwardNormalAt (M := M) g α₁ y)
            (inwardCoordAt (M := M) α₀ y) := by
        rw [h_neg_eq]
        rw [show g.inner (y : M) (-outwardNormalAt (M := M) g α₁ y) =
              -g.inner (y : M) (outwardNormalAt (M := M) g α₁ y) from
            map_neg _ _]
        rfl
      rw [h_contra] at h_sign₀
      linarith

end Smoothness

end WithBoundary
end DivergenceTheorem
end Integral
end DifferentialGeometry
