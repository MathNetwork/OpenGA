import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.LocallyConvex.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.ProperSpace


noncomputable section

open Bundle Manifold Set ContinuousLinearMap Bornology Metric
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem posDef_isVonNBounded
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (g : E →L[ℝ] E →L[ℝ] ℝ)
    (hpos : ∀ v : E, v ≠ 0 → 0 < g v v) :
    Bornology.IsVonNBounded ℝ {v : E | g v v < 1} := by
  have hcont : Continuous (fun v : E => g v v) :=
    isBoundedBilinearMap_apply.continuous.comp (g.continuous.prodMk continuous_id)
  rw [NormedSpace.isVonNBounded_iff']
  obtain ⟨c, hc, hcoer⟩ : ∃ c > 0, ∀ v : E, c * ‖v‖ ^ 2 ≤ g v v := by
    rcases subsingleton_or_nontrivial E with hsub | hnt
    · exact ⟨1, one_pos, fun v => by
        have hv0 : v = 0 := Subsingleton.elim _ _
        subst hv0; simp⟩
    · have hsphere : IsCompact (Metric.sphere (0 : E) 1) := isCompact_sphere _ _
      have hne : (Metric.sphere (0 : E) 1).Nonempty := by
        rw [NormedSpace.sphere_nonempty]; exact zero_le_one
      obtain ⟨v₀, hv₀, hmin⟩ := hsphere.exists_isMinOn hne hcont.continuousOn
      have hv₀0 : v₀ ≠ 0 := by intro h; rw [h] at hv₀; simp at hv₀
      refine ⟨g v₀ v₀, hpos v₀ hv₀0, ?_⟩
      intro v
      rcases eq_or_ne v 0 with rfl | hv
      · simp
      · have hvnorm : (0 : ℝ) < ‖v‖ := norm_pos_iff.mpr hv
        have hscaleAll : ∀ (r : ℝ) (w : E), g (r • w) (r • w) = r ^ 2 * g w w := by
          intro r w
          rw [(g (r • w)).map_smul, map_smul, ContinuousLinearMap.smul_apply,
            smul_eq_mul, smul_eq_mul]; ring
        have hu_sphere : ((‖v‖)⁻¹ • v) ∈ Metric.sphere (0 : E) 1 := by
          rw [Metric.mem_sphere, dist_zero_right, norm_smul, norm_inv, norm_norm]
          field_simp
        have hmin' : g v₀ v₀ ≤ g ((‖v‖)⁻¹ • v) ((‖v‖)⁻¹ • v) := hmin hu_sphere
        have hvv : v = ‖v‖ • ((‖v‖)⁻¹ • v) := by
          rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hvnorm), one_smul]
        have hscale : g v v = ‖v‖ ^ 2 * g ((‖v‖)⁻¹ • v) ((‖v‖)⁻¹ • v) := by
          conv_lhs => rw [hvv]
          rw [hscaleAll ‖v‖ ((‖v‖)⁻¹ • v)]
        rw [hscale]
        nlinarith [sq_nonneg ‖v‖, hvnorm, hmin']
  refine ⟨Real.sqrt (1 / c), fun v hv => ?_⟩
  simp only [Set.mem_setOf_eq] at hv
  have h2 : c * ‖v‖ ^ 2 < 1 := lt_of_le_of_lt (hcoer v) hv
  have h3 : ‖v‖ ^ 2 < 1 / c := by rw [lt_div_iff₀ hc, mul_comm]; exact h2
  calc ‖v‖ = Real.sqrt (‖v‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (1 / c) := Real.sqrt_le_sqrt h3.le

def euclForm (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    E →L[ℝ] E →L[ℝ] ℝ := innerSL ℝ

omit [FiniteDimensional ℝ E] in
@[simp] lemma euclForm_apply (v w : E) : euclForm E v w = inner ℝ v w := rfl

private def tangentTrivializationContinuousLinearMapAt (x₀ x : M) : E →L[ℝ] E :=
  ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ x : E →L[ℝ] E)

private def localFiber (x₀ x : M) : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  (((euclForm E).bilinearComp (tangentTrivializationContinuousLinearMapAt (I := I) x₀ x) (tangentTrivializationContinuousLinearMapAt (I := I) x₀ x)) :
    E →L[ℝ] E →L[ℝ] ℝ)

omit [FiniteDimensional ℝ E] in
lemma localFiber_apply (x₀ x : M) (v w : TangentSpace I x) :
    localFiber (I := I) x₀ x v w =
      inner ℝ (tangentTrivializationContinuousLinearMapAt (I := I) x₀ x v) (tangentTrivializationContinuousLinearMapAt (I := I) x₀ x w) := rfl

omit [FiniteDimensional ℝ E] in
lemma localFiber_symm (x₀ x : M) (v w : TangentSpace I x) :
    localFiber (I := I) x₀ x v w = localFiber (I := I) x₀ x w v := by
  rw [localFiber_apply, localFiber_apply, real_inner_comm]

omit [FiniteDimensional ℝ E] in
lemma localFiber_pos (x₀ : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (v : TangentSpace I x) (hv : v ≠ 0) :
    0 < localFiber (I := I) x₀ x v v := by
  rw [localFiber_apply, real_inner_self_eq_norm_sq]
  have hAv : tangentTrivializationContinuousLinearMapAt (I := I) x₀ x v ≠ 0 := by
    change ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ x : E →L[ℝ] E) v ≠ 0
    rw [show ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ x : E →L[ℝ] E) v
          = (trivializationAt E (TangentSpace I) x₀).continuousLinearEquivAt ℝ x hx v from
        congrFun ((trivializationAt E (TangentSpace I) x₀).coe_continuousLinearEquivAt_eq
          (R := ℝ) hx).symm v]
    exact ((trivializationAt E (TangentSpace I) x₀).continuousLinearEquivAt
      ℝ x hx).map_ne_zero_iff.mpr hv
  positivity

omit [FiniteDimensional ℝ E] in
lemma oneForm_continuousLinearMapAt (x₀ : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (φ : TangentSpace I x →L[ℝ] ℝ) :
    (trivializationAt (E →L[ℝ] ℝ) (fun y => TangentSpace I y →L[ℝ] ℝ) x₀).continuousLinearMapAt
        ℝ x φ
      = φ.comp ((trivializationAt E (TangentSpace I) x₀).symmL ℝ x) := by
  have hx2 : x ∈
      (trivializationAt (E →L[ℝ] ℝ) (fun y => TangentSpace I y →L[ℝ] ℝ) x₀).baseSet := by
    rw [hom_trivializationAt (RingHom.id ℝ) x₀, Bundle.Trivialization.baseSet_continuousLinearMap]
    exact ⟨hx, mem_baseSet_trivializationAt ℝ (Bundle.Trivial M ℝ) x₀⟩
  ext u
  rw [Bundle.Trivialization.continuousLinearMapAt_apply,
      Bundle.Trivialization.coe_linearMapAt_of_mem _ hx2]
  change ((trivializationAt (E →L[ℝ] ℝ) (fun y => TangentSpace I y →L[ℝ] ℝ) x₀) ⟨x, φ⟩).2 u = _
  rw [hom_trivializationAt (RingHom.id ℝ) x₀, Bundle.Trivialization.continuousLinearMap_apply]
  simp only [ContinuousLinearMap.comp_apply]
  have hxR : x ∈ (trivializationAt ℝ (fun _ : M => ℝ) x₀).baseSet := Set.mem_univ x
  rw [Bundle.Trivialization.continuousLinearMapAt_apply,
      Bundle.Trivialization.coe_linearMapAt_of_mem _ hxR]
  rfl

omit [FiniteDimensional ℝ E] in
lemma inCoordinates_localFiber (x₀ : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    inCoordinates E (TangentSpace I) (E →L[ℝ] ℝ) (fun y => TangentSpace I y →L[ℝ] ℝ)
        x₀ x x₀ x (localFiber (I := I) x₀ x) = euclForm E := by
  set e₁ := trivializationAt E (TangentSpace I) x₀ with he₁
  ext v w
  rw [ContinuousLinearMap.inCoordinates]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
  rw [oneForm_continuousLinearMapAt x₀ hx]
  simp only [ContinuousLinearMap.comp_apply]
  change inner ℝ (tangentTrivializationContinuousLinearMapAt (I := I) x₀ x (e₁.symmL ℝ x v))
      (tangentTrivializationContinuousLinearMapAt (I := I) x₀ x (e₁.symmL ℝ x w)) = inner ℝ v w
  rw [show tangentTrivializationContinuousLinearMapAt (I := I) x₀ x (e₁.symmL ℝ x v) = v from e₁.continuousLinearMapAt_symmL hx v,
      show tangentTrivializationContinuousLinearMapAt (I := I) x₀ x (e₁.symmL ℝ x w) = w from e₁.continuousLinearMapAt_symmL hx w]

omit [FiniteDimensional ℝ E] in
private lemma coord_localFiber (x₀ : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    (trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
        (fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) x₀
        ⟨x, localFiber (I := I) x₀ x⟩).2 = euclForm E := by
  have h := hom_trivializationAt_apply (RingHom.id ℝ) (F₁ := E) (E₁ := TangentSpace I)
    (F₂ := E →L[ℝ] ℝ) (E₂ := fun y => TangentSpace I y →L[ℝ] ℝ) x₀
    ⟨x, localFiber (I := I) x₀ x⟩
  rw [congrArg Prod.snd h]
  exact inCoordinates_localFiber x₀ hx

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

omit [FiniteDimensional ℝ E] in
lemma localFiber_contMDiffOn (x₀ : M) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) (⊤ : ℕ∞)
      (fun x => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) x (localFiber (I := I) x₀ x))
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
  refine ContMDiffOn.congr (contMDiffOn_const (c := euclForm E)) ?_
  intro x hx
  exact coord_localFiber x₀ hx

private def posDefForms (x : M) : Set (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  {φ | (∀ v w, φ v w = φ w v) ∧ (∀ v, v ≠ 0 → 0 < φ v v)}

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
lemma convex_posDefForms (x : M) : Convex ℝ (posDefForms (I := I) x) := by
  intro φ hφ ψ hψ a b ha hb hab
  refine ⟨?_, ?_⟩
  · intro v w
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [hφ.1 v w, hψ.1 v w]
  · intro v hv
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    have h1 := hφ.2 v hv
    have h2 := hψ.2 v hv
    rcases lt_or_eq_of_le ha with ha' | ha'
    · have hb1 : 0 < a * φ v v := mul_pos ha' h1
      have hb2 : 0 ≤ b * ψ v v := mul_nonneg hb h2.le
      positivity
    · rw [← ha'] at hab ⊢; simp only [zero_add] at hab ⊢
      rw [hab]; simpa using h2

theorem nonempty_contMDiffRiemannianMetric_of_sigmaCompact
    [SigmaCompactSpace M] [T2Space M] :
    Nonempty (Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)) := by
  obtain ⟨s, hs⟩ :=
    exists_contMDiffSection_forall_mem_convex_of_local (M := M) (n := (⊤ : ℕ∞)) I
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
      (fun x => posDefForms (I := I) x)
      (fun x => convex_posDefForms (I := I) x)
      (fun x₀ => by
        refine ⟨(trivializationAt E (TangentSpace I) x₀).baseSet,
          (trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds
            (mem_baseSet_trivializationAt E (TangentSpace I) x₀),
          localFiber (I := I) x₀, localFiber_contMDiffOn x₀, ?_⟩
        intro y hy
        exact ⟨fun v w => localFiber_symm (I := I) x₀ y v w,
          fun v hv => localFiber_pos (I := I) x₀ hy v hv⟩)
  refine ⟨{
    inner := fun x => s x
    symm := fun x v w => (hs x).1 v w
    pos := fun x v hv => (hs x).2 v hv
    isVonNBounded := fun x => ?_
    contMDiff := s.contMDiff }⟩
  exact posDef_isVonNBounded (E := E) ((s x : E →L[ℝ] E →L[ℝ] ℝ))
    (fun v hv => (hs x).2 v hv)

theorem nonempty_smoothRiemannianMetric
    [SigmaCompactSpace M] [T2Space M] :
    Nonempty (Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)) :=
  nonempty_contMDiffRiemannianMetric_of_sigmaCompact

end Geometry
end DifferentialGeometry
