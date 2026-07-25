import DifferentialGeometry.Geometry.Metric.MetricExistence
import DifferentialGeometry.Geometry.Metric.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic





































noncomputable section

open Bundle Manifold Set ContinuousLinearMap Bornology
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]


private def mdlBasis (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E :=
  Module.finBasis ℝ E


private def coCLM (i : Fin (Module.finrank ℝ E)) : E →L[ℝ] ℝ :=
  ((mdlBasis E).coord i).toContinuousLinearMap

@[simp] private lemma coCLM_apply (i : Fin (Module.finrank ℝ E)) (v : E) :
    coCLM (E := E) i v = (mdlBasis E).coord i v := rfl


private def munit (i j : Fin (Module.finrank ℝ E)) : E →L[ℝ] E →L[ℝ] ℝ :=
  (coCLM (E := E) i).smulRight (coCLM (E := E) j)

@[simp] private lemma munit_apply (i j : Fin (Module.finrank ℝ E)) (v w : E) :
    munit (E := E) i j v w = (mdlBasis E).coord i v * (mdlBasis E).coord j w := by
  simp [munit, ContinuousLinearMap.smulRight_apply, smul_eq_mul]


private lemma bilin_expand (φ : E →L[ℝ] E →L[ℝ] ℝ) (v w : E) :
    φ v w = ∑ i, ∑ j,
      (mdlBasis E).coord i v * (mdlBasis E).coord j w * φ (mdlBasis E i) (mdlBasis E j) := by
  set b := mdlBasis E with hb
  have hcoord : ∀ (u : E) (i : Fin (Module.finrank ℝ E)), b.coord i u = b.repr u i :=
    fun u i => Module.Basis.coord_apply b i u
  have e1 : φ v = ∑ i, b.repr v i • φ (b i) := by
    conv_lhs => rw [← b.sum_repr v]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_smul]
  have e2 : ∀ i, φ (b i) w = ∑ j, b.repr w j • φ (b i) (b j) := by
    intro i
    conv_lhs => rw [← b.sum_repr w]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [map_smul]
  calc φ v w
      = (∑ i, b.repr v i • φ (b i)) w := by rw [e1]
    _ = ∑ i, b.repr v i • φ (b i) w := by
          rw [ContinuousLinearMap.sum_apply]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [ContinuousLinearMap.smul_apply]
    _ = ∑ i, b.repr v i • ∑ j, b.repr w j • φ (b i) (b j) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [e2 i]
    _ = ∑ i, ∑ j, b.coord i v * b.coord j w * φ (b i) (b j) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [smul_eq_mul, smul_eq_mul, hcoord, hcoord]
          ring


private lemma clm_eq_sum (φ : E →L[ℝ] E →L[ℝ] ℝ) :
    φ = ∑ i, ∑ j, φ (mdlBasis E i) (mdlBasis E j) • munit (E := E) i j := by
  ext v w
  rw [bilin_expand (E := E) φ v w]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, munit_apply,
    smul_eq_mul]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  ring




def frameVec (x₀ : M) (i : Fin (Module.finrank ℝ E)) (x : M) : TangentSpace I x :=
  (trivializationAt E (TangentSpace I) x₀).symmL ℝ x (mdlBasis E i)





omit [FiniteDimensional ℝ E] in
set_option maxHeartbeats 1000000 in
theorem metricCoeffInModel_apply (x₀ : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (φ : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) (v w : E) :
    ((trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
          (fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) x₀)
        ⟨x, φ⟩).2 v w
      = φ ((trivializationAt E (TangentSpace I) x₀).symmL ℝ x v)
          ((trivializationAt E (TangentSpace I) x₀).symmL ℝ x w) := by
  letI : TopologicalSpace
      (TotalSpace (E →L[ℝ] ℝ) (fun y : M ↦ TangentSpace I y →L[ℝ] ℝ)) :=
    Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
      (RingHom.id ℝ) E (TangentSpace I) ℝ (fun _ : M ↦ ℝ)
  rw [hom_trivializationAt_apply (RingHom.id ℝ) (F₁ := E) (E₁ := TangentSpace I)
    (F₂ := E →L[ℝ] ℝ) (E₂ := fun y => TangentSpace I y →L[ℝ] ℝ)]
  rw [ContinuousLinearMap.inCoordinates]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
  have hone (ψ : TangentSpace I x →L[ℝ] ℝ) :
      (trivializationAt (E →L[ℝ] ℝ) (fun y => TangentSpace I y →L[ℝ] ℝ) x₀).continuousLinearMapAt
          ℝ x ψ = ψ.comp ((trivializationAt E (TangentSpace I) x₀).symmL ℝ x) := by
    have hx2 : x ∈
        (trivializationAt (E →L[ℝ] ℝ) (fun y => TangentSpace I y →L[ℝ] ℝ) x₀).baseSet := by
      rw [hom_trivializationAt (RingHom.id ℝ) x₀,
        Bundle.Trivialization.baseSet_continuousLinearMap]
      exact ⟨hx, mem_baseSet_trivializationAt ℝ (Bundle.Trivial M ℝ) x₀⟩
    ext u
    rw [Bundle.Trivialization.continuousLinearMapAt_apply,
      Bundle.Trivialization.coe_linearMapAt_of_mem _ hx2]
    change ((trivializationAt (E →L[ℝ] ℝ)
      (fun y => TangentSpace I y →L[ℝ] ℝ) x₀) ⟨x, ψ⟩).2 u = _
    rw [hom_trivializationAt (RingHom.id ℝ) x₀,
      Bundle.Trivialization.continuousLinearMap_apply]
    simp only [ContinuousLinearMap.comp_apply]
    have hxR : x ∈ (trivializationAt ℝ (fun _ : M => ℝ) x₀).baseSet := Set.mem_univ x
    rw [Bundle.Trivialization.continuousLinearMapAt_apply,
      Bundle.Trivialization.coe_linearMapAt_of_mem _ hxR]
    rfl
  rw [hone]
  simp only [ContinuousLinearMap.comp_apply]

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in


private lemma metric_contMDiffOn (gm : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (x₀ : M)
    (hcoeff : ∀ i j : Fin (Module.finrank ℝ E),
      ContMDiffOn I 𝓘(ℝ) ∞
        (fun x => gm x (frameVec (I := I) x₀ i x) (frameVec (I := I) x₀ j x))
        (trivializationAt E (TangentSpace I) x₀).baseSet) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) b (gm b))
      (trivializationAt E (TangentSpace I) x₀).baseSet := by
  have hbsub : (trivializationAt E (TangentSpace I) x₀).baseSet ⊆
      (trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
        (fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) x₀).baseSet := by
    rw [hom_trivializationAt (RingHom.id ℝ) x₀, Bundle.Trivialization.baseSet_continuousLinearMap]
    intro y hy
    refine ⟨hy, ?_⟩
    rw [hom_trivializationAt (RingHom.id ℝ) x₀, Bundle.Trivialization.baseSet_continuousLinearMap]
    exact ⟨hy, mem_baseSet_trivializationAt ℝ (Bundle.Trivial M ℝ) x₀⟩
  rw [Bundle.Trivialization.contMDiffOn_section_iff
      (trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
        (fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) x₀)
      (trivializationAt E (TangentSpace I) x₀).open_baseSet hbsub]
  have hsmooth : ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞
      (fun x => ∑ i, ∑ j,
        gm x (frameVec (I := I) x₀ i x) (frameVec (I := I) x₀ j x) • munit (E := E) i j)
      (trivializationAt E (TangentSpace I) x₀).baseSet := by
    refine contMDiffOn_finset_sum (fun i _ => ?_)
    refine contMDiffOn_finset_sum (fun j _ => ?_)
    exact (hcoeff i j).smul contMDiffOn_const
  refine hsmooth.congr ?_
  intro x hx
  rw [clm_eq_sum (E := E)
    ((trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
        (fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) x₀)
      ⟨x, gm x⟩).2]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  simp only [frameVec]
  rw [metricCoeffInModel_apply (I := I) x₀ hx (gm x) (mdlBasis E i) (mdlBasis E j)]




theorem smoothMetric_of_localCoeff
    (gm : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (hsymm : ∀ (x : M) (v w : TangentSpace I x), gm x v w = gm x w v)
    (hpos : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < gm x v v)
    (hcoeff : ∀ x₀ : M, ∀ i j : Fin (Module.finrank ℝ E),
      ContMDiffOn I 𝓘(ℝ) ∞
        (fun x => gm x (frameVec (I := I) x₀ i x) (frameVec (I := I) x₀ j x))
        (trivializationAt E (TangentSpace I) x₀).baseSet) :
    ∃ g : SmoothRiemannianMetric I M,
      ∀ (x : M) (v w : TangentSpace I x), g.inner x v w = gm x v w := by
  refine ⟨{
    inner := gm
    symm := hsymm
    pos := hpos
    isVonNBounded := fun x => posDef_isVonNBounded (E := E) (gm x) (fun v hv => hpos x v hv)
    contMDiff := ?_ }, fun x v w => rfl⟩
  intro x₀
  refine ContMDiffOn.contMDiffAt (metric_contMDiffOn (I := I) gm x₀ (hcoeff x₀)) ?_
  exact (trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt E (TangentSpace I) x₀)

end Geometry
end DifferentialGeometry
