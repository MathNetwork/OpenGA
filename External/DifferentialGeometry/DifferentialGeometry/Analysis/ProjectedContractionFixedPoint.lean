import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Algebra.Module.LinearMap

open Filter Topology
open scoped NNReal

namespace DifferentialGeometry.Analysis

variable {X : Type*}

theorem tendsto_fixedPoint_of_tendsto_apply [MetricSpace X] [Nonempty X] [CompleteSpace X]
    {Φ : X → X} {κ : ℝ≥0} (hΦ : ContractingWith κ Φ)
    {Q : ℕ → X → X} (hQΦ : ∀ N, ContractingWith κ (Q N ∘ Φ))
    (hQ : ∀ x, Tendsto (fun N => Q N x) atTop (𝓝 x)) :
    Tendsto (fun N => ContractingWith.fixedPoint (Q N ∘ Φ) (hQΦ N)) atTop
      (𝓝 (ContractingWith.fixedPoint Φ hΦ)) := by
  set a := ContractingWith.fixedPoint Φ hΦ with ha
  have hfix : Φ a = a := hΦ.fixedPoint_isFixedPt
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (g := fun N => dist a (Q N a) / (1 - (κ : ℝ)))
    (fun N => dist_nonneg) ?_ ?_
  · intro N
    have hcomp : (Q N ∘ Φ) a = Q N a := by
      simp only [Function.comp_apply, hfix]
    have h1 := (hQΦ N).dist_fixedPoint_le a
    rw [hcomp] at h1
    rw [dist_comm]
    exact h1
  · have hd : Tendsto (fun N => dist a (Q N a)) atTop (𝓝 (0 : ℝ)) := by
      have h := (tendsto_const_nhds (x := a) (f := atTop)).dist (hQ a)
      simpa using h
    simpa using hd.div_const (1 - (κ : ℝ))

theorem tendsto_fixedPoint_of_projected_contraction
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    {Φ : X → X} {κ : ℝ≥0} (hΦ : ContractingWith κ Φ)
    (P : ℕ → (X →L[ℝ] X)) (hP : ∀ x, Tendsto (fun N => P N x) atTop (𝓝 x))
    (hPΦ : ∀ N, ContractingWith κ (⇑(P N) ∘ Φ)) :
    Tendsto (fun N => ContractingWith.fixedPoint (⇑(P N) ∘ Φ) (hPΦ N)) atTop
      (𝓝 (ContractingWith.fixedPoint Φ hΦ)) :=
  tendsto_fixedPoint_of_tendsto_apply (Q := fun N => ⇑(P N)) hΦ hPΦ hP

end DifferentialGeometry.Analysis
