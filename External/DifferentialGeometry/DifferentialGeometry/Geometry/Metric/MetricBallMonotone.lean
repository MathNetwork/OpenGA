import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import DifferentialGeometry.Geometry.Metric.Basic

set_option autoImplicit false








namespace DifferentialGeometry

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H]

theorem ball_subset_of_le
    {X : Type*} [PseudoMetricSpace X] {x : X} {r R : Real}
    (hr : r ≤ R) :
    Metric.ball x r ⊆ Metric.ball x R := by
  intro y hy
  rw [Metric.mem_ball] at hy ⊢
  exact lt_of_lt_of_le hy hr


theorem cball_subset_of_le
    {X : Type*} [PseudoMetricSpace X] {x : X} {r R : Real}
    (hr : r ≤ R) :
    Metric.closedBall x r ⊆ Metric.closedBall x R := by
  intro y hy
  rw [Metric.mem_closedBall] at hy ⊢
  exact le_trans hy hr



theorem injOn_of_return
    {X Y ι : Type*} [PseudoMetricSpace X]
    {S : Set X} {F : X → Y} {H : Y → X}
    (K V : ι → Set X) {ρ : Real}
    (hρ : 0 < ρ)
    (hcover : S ⊆ ⋃ i, K i)
    (hbuffer : ∀ i x, x ∈ K i → Metric.ball x ρ ⊆ V i)
    (hlocal : ∀ i, Set.InjOn F (V i))
    (hreturn : ∀ x, x ∈ S → dist (H (F x)) x < ρ / 2) :
    Set.InjOn F S := by
  intro x hx y hy hF
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp (hcover hx)
  apply hlocal i
  · exact hbuffer i x hxi (Metric.mem_ball_self hρ)
  · apply hbuffer i x hxi
    rw [Metric.mem_ball]
    calc
      dist y x ≤ dist y (H (F y)) + dist (H (F y)) x := dist_triangle _ _ _
      _ = dist (H (F y)) y + dist (H (F x)) x := by
        rw [dist_comm y (H (F y)), ← hF]
      _ < ρ / 2 + ρ / 2 := add_lt_add (hreturn y hy) (hreturn x hx)
      _ = ρ := by ring
  · exact hF

end DifferentialGeometry
