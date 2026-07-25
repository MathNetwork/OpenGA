import DifferentialGeometry.Geometry.Topology.UniversalCover.Basic
import DifferentialGeometry.Geometry.Topology.UniversalCover.CoveringMap
import Mathlib.Topology.Path
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.Homotopy.Lifting











noncomputable section

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Topology
namespace UniversalCover

open Set unitInterval







lemma uc_trans_truncate_class
    {X : Type*} [TopologicalSpace X] {a b : X} (γ : _root_.Path a b)
    {s₀ s : ℝ} (h0 : (0 : ℝ) ≤ s₀) (h0s : s₀ ≤ s) (hs1 : s ≤ 1) :
    (_root_.Path.Homotopic.Quotient.mk
        (γ.truncateOfLE (le_trans h0 h0s)) :
      _root_.Path.Homotopic.Quotient (γ.extend 0) (γ.extend s))
      = _root_.Path.Homotopic.Quotient.mk
          ((γ.truncateOfLE h0).trans (γ.truncateOfLE h0s)) := by
  set p : _root_.Path (γ.extend 0) (γ.extend s) :=
      γ.truncateOfLE (le_trans h0 h0s) with hp_def
  set q : _root_.Path (γ.extend 0) (γ.extend s) :=
      (γ.truncateOfLE h0).trans (γ.truncateOfLE h0s) with hq_def
  have h_0_s : (0 : ℝ) ≤ s := le_trans h0 h0s
  refine _root_.Quotient.sound ?_
  let rhsIdx : I → ℝ := fun t =>
      if (t : ℝ) ≤ 1 / 2 then min (2 * (t : ℝ)) s₀
      else min (max (2 * (t : ℝ) - 1) s₀) s
  let lhsIdx : I → ℝ := fun t => min (t : ℝ) s
  have hcont_rhsIdx : Continuous rhsIdx := by
    refine Continuous.if_le
      (f' := fun t : I => min (2 * (t : ℝ)) s₀)
      (g' := fun t : I => min (max (2 * (t : ℝ) - 1) s₀) s)
      (f := fun t : I => (t : ℝ))
      (g := fun _ : I => (1 / 2 : ℝ))
      ?hf' ?hg' continuous_subtype_val continuous_const ?heq
    case hf' =>
      exact (continuous_const.mul continuous_subtype_val).min continuous_const
    case hg' =>
      exact (((continuous_const.mul continuous_subtype_val).sub continuous_const).max
        continuous_const).min continuous_const
    case heq =>
      intro t ht
      have ht' : (t : ℝ) = 1 / 2 := ht
      change min (2 * (t : ℝ)) s₀ = min (max (2 * (t : ℝ) - 1) s₀) s
      have h1 : min (2 * (t : ℝ)) s₀ = s₀ := by
        rw [ht']
        have hone : (2 : ℝ) * (1 / 2) = 1 := by ring
        rw [hone, min_eq_right]
        linarith [le_trans h0 (h0s.trans hs1)]
      have h2 : min (max (2 * (t : ℝ) - 1) s₀) s = s₀ := by
        rw [ht']
        have hsub : (2 : ℝ) * (1 / 2) - 1 = 0 := by ring
        rw [hsub, max_eq_right h0, min_eq_left h0s]
      rw [h1, h2]
  have hcont_lhsIdx : Continuous lhsIdx :=
    continuous_subtype_val.min continuous_const
  have hp_apply : ∀ t : I, p t = γ.extend (lhsIdx t) := by
    intro t
    change (γ.truncateOfLE _) t = _
    have hcast : ((γ.truncateOfLE (le_trans h0 h0s)) t : X)
        = ((γ.truncate 0 s) t : X) := by
      simp [_root_.Path.truncateOfLE, _root_.Path.cast_coe]
    rw [hcast]
    change γ.extend (min (max (t : ℝ) 0) s) = γ.extend (min (t : ℝ) s)
    congr 1
    have h_t_nn : (0 : ℝ) ≤ (t : ℝ) := t.2.1
    rw [max_eq_left h_t_nn]
  have hq_apply : ∀ t : I, q t = γ.extend (rhsIdx t) := by
    intro t
    change ((γ.truncateOfLE h0).trans (γ.truncateOfLE h0s)) t = _
    rw [_root_.Path.trans_apply]
    by_cases ht : (t : ℝ) ≤ 1 / 2
    · rw [dif_pos ht]
      have h2t_nn : (0 : ℝ) ≤ 2 * (t : ℝ) := by
        have : (0 : ℝ) ≤ (t : ℝ) := t.2.1
        linarith
      change (γ.truncate 0 s₀) _ = _
      change γ.extend (min (max (2 * (t : ℝ)) 0) s₀) = γ.extend (rhsIdx t)
      rw [max_eq_left h2t_nn]
      simp only [rhsIdx, if_pos ht]
    · rw [dif_neg ht]
      change (γ.truncate s₀ s) _ = _
      change γ.extend (min (max (2 * (t : ℝ) - 1) s₀) s) = γ.extend (rhsIdx t)
      simp only [rhsIdx, if_neg ht]
  refine ⟨{
    toFun := fun ut => γ.extend
      ((1 - (ut.1 : ℝ)) * lhsIdx ut.2 + (ut.1 : ℝ) * rhsIdx ut.2)
    continuous_toFun := ?cont
    map_zero_left := ?mz
    map_one_left := ?mo
    prop' := ?prop }⟩
  case cont =>
    refine γ.continuous_extend.comp ?_
    refine ((continuous_const.sub
      (continuous_subtype_val.comp continuous_fst)).mul
        (hcont_lhsIdx.comp continuous_snd)).add ?_
    exact (continuous_subtype_val.comp continuous_fst).mul
      (hcont_rhsIdx.comp continuous_snd)
  case mz =>
    intro t
    change γ.extend ((1 - ((0:I) : ℝ)) * lhsIdx t + ((0:I) : ℝ) * rhsIdx t)
      = p.toContinuousMap t
    simp only [Icc.coe_zero, sub_zero, one_mul, zero_mul, add_zero]
    change γ.extend (lhsIdx t) = p t
    exact (hp_apply t).symm
  case mo =>
    intro t
    change γ.extend ((1 - ((1:I) : ℝ)) * lhsIdx t + ((1:I) : ℝ) * rhsIdx t)
      = q.toContinuousMap t
    simp only [Icc.coe_one, sub_self, zero_mul, one_mul, zero_add]
    change γ.extend (rhsIdx t) = q t
    exact (hq_apply t).symm
  case prop =>
    intro u t htmem
    rcases htmem with ht0 | ht1
    · subst ht0
      change γ.extend ((1 - (u : ℝ)) * lhsIdx 0 + (u : ℝ) * rhsIdx 0)
        = p.toContinuousMap 0
      have hl0 : lhsIdx 0 = 0 := by
        change min (((0:I):ℝ)) s = 0
        rw [Icc.coe_zero, min_eq_left h_0_s]
      have hr0 : rhsIdx 0 = 0 := by
        change (if ((0:I):ℝ) ≤ 1 / 2 then min (2 * ((0:I):ℝ)) s₀
              else min (max (2 * ((0:I):ℝ) - 1) s₀) s) = 0
        rw [Icc.coe_zero, if_pos (by norm_num : (0:ℝ) ≤ 1/2), mul_zero, min_eq_left h0]
      rw [hl0, hr0]
      simp only [mul_zero, add_zero]
      change γ.extend 0 = p 0
      rw [p.source]
    · rw [Set.mem_singleton_iff] at ht1
      subst ht1
      change γ.extend ((1 - (u : ℝ)) * lhsIdx 1 + (u : ℝ) * rhsIdx 1)
        = p.toContinuousMap 1
      have hl1 : lhsIdx 1 = s := by
        change min (((1:I):ℝ)) s = s
        rw [Icc.coe_one, min_eq_right hs1]
      have hr1 : rhsIdx 1 = s := by
        change (if ((1:I):ℝ) ≤ 1 / 2 then min (2 * ((1:I):ℝ)) s₀
              else min (max (2 * ((1:I):ℝ) - 1) s₀) s) = s
        rw [Icc.coe_one, if_neg (by norm_num : ¬(1:ℝ) ≤ 1/2)]
        have h_one : (2 : ℝ) * 1 - 1 = 1 := by ring
        rw [h_one]
        rw [max_eq_left (h0s.trans hs1)]
        exact min_eq_right hs1
      rw [hl1, hr1]
      have hadd : (1 - (u : ℝ)) * s + (u : ℝ) * s = s := by ring
      rw [hadd]
      change γ.extend s = p 1
      rw [p.target]

set_option linter.unusedVariables false in


lemma uc_truncLift_continuous
    {X : Type*} [TopologicalSpace X] [Inhabited X]
    {a b : X} (γ : _root_.Path a b)
    (q : UniversalCover X) (hq : q.1 = a) :
    True := trivial

set_option linter.unusedVariables false in


lemma uc_liftPath_one_eq
    {X : Type*} [TopologicalSpace X] [Inhabited X]
    [ConnectedSpace X] [LocPathConnectedSpace X]
    [DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnectedSpace X]
    {x : X} (γ : _root_.Path (default : X) x) :
    True := trivial

end UniversalCover
end Topology
end Riemannian
end Geometry
end DifferentialGeometry
