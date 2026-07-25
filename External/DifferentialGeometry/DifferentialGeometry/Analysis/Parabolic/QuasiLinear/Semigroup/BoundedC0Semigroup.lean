import Mathlib.Analysis.Normed.Operator.NormedSpace

noncomputable section

open Set Filter Topology

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace QuasiLinear

structure BoundedC0Semigroup (X : Type*) [NormedAddCommGroup X]
    [NormedSpace ℝ X] where

  toFun : ℝ → (X →L[ℝ] X)

  apply_zero : toFun 0 = ContinuousLinearMap.id ℝ X

  apply_add : ∀ t s : ℝ, 0 ≤ t → 0 ≤ s →
    toFun (t + s) = (toFun t).comp (toFun s)

  opNorm_le_one : ∀ t : ℝ, 0 ≤ t → ‖toFun t‖ ≤ 1

  continuousOn_apply : ∀ v : X,
    ContinuousOn (fun t : ℝ => toFun t v) (Set.Ici 0)

namespace BoundedC0Semigroup

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

instance : CoeFun (BoundedC0Semigroup X) (fun _ => ℝ → (X →L[ℝ] X)) :=
  ⟨BoundedC0Semigroup.toFun⟩

@[simp]
theorem coe_mk (toFun : ℝ → (X →L[ℝ] X)) (h₀ h₁ h₂ h₃) :
    ⇑(BoundedC0Semigroup.mk toFun h₀ h₁ h₂ h₃) = toFun :=
  rfl

theorem norm_apply_le (S : BoundedC0Semigroup X) {t : ℝ} (ht : 0 ≤ t)
    (v : X) : ‖S t v‖ ≤ ‖v‖ := by
  have h_op : ‖S t‖ ≤ 1 := S.opNorm_le_one t ht
  have h_le : ‖S t v‖ ≤ ‖S t‖ * ‖v‖ := (S t).le_opNorm v
  have h_nn : (0 : ℝ) ≤ ‖v‖ := norm_nonneg _
  calc ‖S t v‖ ≤ ‖S t‖ * ‖v‖ := h_le
    _ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right h_op h_nn
    _ = ‖v‖ := one_mul _

theorem continuousOn_uncurry (S : BoundedC0Semigroup X) :
    ContinuousOn (fun p : ℝ × X => S p.1 p.2)
      (Set.Ici 0 ×ˢ Set.univ) := by
  refine fun p₀ hp₀ => ?_
  obtain ⟨hσ₀_nn, -⟩ := hp₀
  rw [Set.mem_Ici] at hσ₀_nn
  set σ₀ : ℝ := p₀.1 with hσ₀_def
  set v₀ : X := p₀.2 with hv₀_def
  have h_bound : ∀ p : ℝ × X, p ∈ Set.Ici (0 : ℝ) ×ˢ Set.univ →
      ‖(fun q : ℝ × X => S q.1 q.2) p -
          (fun q : ℝ × X => S q.1 q.2) p₀‖ ≤
        ‖p.2 - v₀‖ + ‖S p.1 v₀ - S σ₀ v₀‖ := by
    rintro ⟨σ, v⟩ hp
    obtain ⟨hσ_nn, -⟩ := hp
    rw [Set.mem_Ici] at hσ_nn
    have h_decomp : S σ v - S σ₀ v₀ =
        S σ (v - v₀) + (S σ v₀ - S σ₀ v₀) := by
      rw [(S σ).map_sub]
      abel
    have h_first : ‖S σ (v - v₀)‖ ≤ ‖v - v₀‖ :=
      S.norm_apply_le hσ_nn (v - v₀)
    calc ‖(fun q : ℝ × X => S q.1 q.2) (σ, v) -
            (fun q : ℝ × X => S q.1 q.2) p₀‖
        = ‖S σ (v - v₀) + (S σ v₀ - S σ₀ v₀)‖ := by
          simp only []; rw [h_decomp]
      _ ≤ ‖S σ (v - v₀)‖ + ‖S σ v₀ - S σ₀ v₀‖ :=
          norm_add_le _ _
      _ ≤ ‖v - v₀‖ + ‖S σ v₀ - S σ₀ v₀‖ := by
          gcongr
  have h_rhs_to_zero :
      Tendsto (fun p : ℝ × X => ‖p.2 - v₀‖ + ‖S p.1 v₀ - S σ₀ v₀‖)
        (𝓝[Set.Ici (0 : ℝ) ×ˢ Set.univ] p₀) (𝓝 0) := by
    have h_term1 :
        Tendsto (fun p : ℝ × X => ‖p.2 - v₀‖)
          (𝓝[Set.Ici (0 : ℝ) ×ˢ Set.univ] p₀) (𝓝 0) := by
      have h_snd : Tendsto (fun p : ℝ × X => p.2)
          (𝓝[Set.Ici (0 : ℝ) ×ˢ Set.univ] p₀) (𝓝 v₀) :=
        (continuous_snd.continuousAt.tendsto).mono_left nhdsWithin_le_nhds
      have h_diff : Tendsto (fun p : ℝ × X => p.2 - v₀)
          (𝓝[Set.Ici (0 : ℝ) ×ˢ Set.univ] p₀) (𝓝 0) := by
        have := h_snd.sub (tendsto_const_nhds (x := v₀))
        simpa using this
      have := h_diff.norm
      simpa using this
    have h_strong : ContinuousWithinAt (fun t : ℝ => S t v₀)
        (Set.Ici 0) σ₀ :=
      S.continuousOn_apply v₀ σ₀ (Set.mem_Ici.mpr hσ₀_nn)
    have h_fst_within :
        Tendsto (fun p : ℝ × X => p.1)
          (𝓝[Set.Ici (0 : ℝ) ×ˢ Set.univ] p₀)
          (𝓝[Set.Ici (0 : ℝ)] σ₀) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨(continuous_fst.continuousAt.tendsto).mono_left
        nhdsWithin_le_nhds, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with p hp
      exact hp.1
    have h_compose :
        Tendsto (fun p : ℝ × X => S p.1 v₀)
          (𝓝[Set.Ici (0 : ℝ) ×ˢ Set.univ] p₀) (𝓝 (S σ₀ v₀)) :=
      h_strong.tendsto.comp h_fst_within
    have h_term2 :
        Tendsto (fun p : ℝ × X => ‖S p.1 v₀ - S σ₀ v₀‖)
          (𝓝[Set.Ici (0 : ℝ) ×ˢ Set.univ] p₀) (𝓝 0) := by
      have h_diff : Tendsto (fun p : ℝ × X => S p.1 v₀ - S σ₀ v₀)
          (𝓝[Set.Ici (0 : ℝ) ×ˢ Set.univ] p₀) (𝓝 0) := by
        have := h_compose.sub
          (tendsto_const_nhds (x := S σ₀ v₀))
        simpa using this
      have := h_diff.norm
      simpa using this
    have := h_term1.add h_term2
    simpa using this
  have h_diff_to_zero :
      Tendsto (fun p : ℝ × X =>
          (fun q : ℝ × X => S q.1 q.2) p -
            (fun q : ℝ × X => S q.1 q.2) p₀)
        (𝓝[Set.Ici (0 : ℝ) ×ˢ Set.univ] p₀) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ h_rhs_to_zero
    filter_upwards [self_mem_nhdsWithin] with p hp
    exact h_bound p hp
  have h_target :
      Tendsto (fun p : ℝ × X => S p.1 p.2)
        (𝓝[Set.Ici (0 : ℝ) ×ˢ Set.univ] p₀)
        (𝓝 ((fun q : ℝ × X => S q.1 q.2) p₀)) := by
    have h_added := h_diff_to_zero.add
      (tendsto_const_nhds (x := (fun q : ℝ × X => S q.1 q.2) p₀))
    simpa using h_added
  exact h_target

end BoundedC0Semigroup

end QuasiLinear
end Parabolic
end Analysis
end DifferentialGeometry

end
