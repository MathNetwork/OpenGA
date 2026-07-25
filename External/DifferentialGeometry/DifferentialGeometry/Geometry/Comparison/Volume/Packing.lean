import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Basic

set_option autoImplicit false










namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace VolumeComparison

open MeasureTheory







theorem card_le_of_mul_lt {n N : Nat} {L U : Real}
    (hL : 0 < L)
    (hle : (n : Real) * L <= U)
    (hlt : U < ((N + 1 : Nat) : Real) * L) :
    n <= N := by
  by_contra hn
  have hNn : N + 1 <= n := Nat.succ_le_of_lt (Nat.lt_of_not_ge hn)
  have hNn_real : ((N + 1 : Nat) : Real) <= (n : Real) := by
    exact_mod_cast hNn
  have hmul : ((N + 1 : Nat) : Real) * L <= (n : Real) * L :=
    mul_le_mul_of_nonneg_right hNn_real hL.le
  nlinarith







theorem mul_lower_le_upper {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α)
    (J : Finset ι) (small : ι → Set α) (large : Set α)
    (hsmall_meas : ∀ i ∈ J, MeasurableSet (small i))
    (hdisj : Set.PairwiseDisjoint (↑J : Set ι) small)
    (hsub : ∀ i ∈ J, small i ⊆ large)
    (hlarge_fin : μ large ≠ ⊤)
    {L : Real} (hL : ∀ i ∈ J, L ≤ μ.real (small i)) :
    (J.card : Real) * L ≤ μ.real large := by
  have hsum_lower : (J.card : Real) * L ≤ ∑ i ∈ J, μ.real (small i) := by
    calc
      (J.card : Real) * L = ∑ i ∈ J, L := by
        simp [nsmul_eq_mul, mul_comm]
      _ ≤ ∑ i ∈ J, μ.real (small i) := by
        exact Finset.sum_le_sum fun i hi => hL i hi
  have hUnion_sub : (⋃ i ∈ J, small i) ⊆ large := by
    intro x hx
    rcases Set.mem_iUnion.mp hx with ⟨i, hx_i⟩
    rcases Set.mem_iUnion.mp hx_i with ⟨hi, hx_small⟩
    exact hsub i hi hx_small
  have hsum_upper : ∑ i ∈ J, μ.real (small i) ≤ μ.real large := by
    rw [← measureReal_biUnion_finset (μ := μ) hdisj hsmall_meas
      (fun i hi => measure_ne_top_of_subset (hsub i hi) hlarge_fin)]
    exact measureReal_mono hUnion_sub hlarge_fin
  exact hsum_lower.trans hsum_upper



theorem balls_disjoint {α ι : Type*} [PseudoMetricSpace α]
    {J : Finset ι} {centers : ι → α} {r : Real}
    (hsep : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → r ≤ dist (centers i) (centers j)) :
    Set.PairwiseDisjoint (↑J : Set ι) (fun i => Metric.ball (centers i) (r / 2)) := by
  intro i hi j hj hij
  change Disjoint (Metric.ball (centers i) (r / 2))
    (Metric.ball (centers j) (r / 2))
  rw [Set.disjoint_left]
  intro x hxi hxj
  have hxi' : dist x (centers i) < r / 2 := by
    simpa using hxi
  have hxj' : dist x (centers j) < r / 2 := by
    simpa using hxj
  have hdist : dist (centers i) (centers j) < r := by
    calc
      dist (centers i) (centers j) ≤ dist (centers i) x + dist x (centers j) :=
        dist_triangle _ _ _
      _ < r / 2 + r / 2 := by
        simpa [dist_comm] using add_lt_add_of_lt_of_lt hxi' hxj'
      _ = r := by ring
  exact False.elim ((not_lt_of_ge (hsep i hi j hj hij)) hdist)




theorem balls_subset_ball {α ι : Type*} [PseudoMetricSpace α]
    {J : Finset ι} {centers : ι → α} {z : α} {r m : Real}
    (hJz : ∀ j ∈ J, dist (centers j) z ≤ m * r) :
    (⋃ j ∈ J, Metric.ball (centers j) (r / 2)) ⊆
      Metric.ball z ((m + 1 / 2) * r) := by
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨j, hxj⟩
  rcases Set.mem_iUnion.mp hxj with ⟨hj, hx_small⟩
  have hx_small' : dist x (centers j) < r / 2 := by
    simpa using hx_small
  have hxz : dist x z < r / 2 + m * r := by
    calc
      dist x z ≤ dist x (centers j) + dist (centers j) z := dist_triangle _ _ _
      _ < r / 2 + m * r := add_lt_add_of_lt_of_le hx_small' (hJz j hj)
  have hrewrite : r / 2 + m * r = (m + 1 / 2) * r := by ring
  exact Metric.mem_ball.mpr (by simpa [hrewrite] using hxz)







theorem ball_mul_le {α ι : Type*} [PseudoMetricSpace α]
    [MeasurableSpace α] [BorelSpace α]
    (μ : Measure α)
    (J : Finset ι) (centers : ι → α) (z : α) {r m L : Real}
    (hlarge_fin : μ (Metric.ball z ((m + 1 / 2) * r)) ≠ ⊤)
    (hsep : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → r ≤ dist (centers i) (centers j))
    (hJz : ∀ j ∈ J, dist (centers j) z ≤ m * r)
    (hL : ∀ j ∈ J, L ≤ μ.real (Metric.ball (centers j) (r / 2))) :
    (J.card : Real) * L ≤ μ.real (Metric.ball z ((m + 1 / 2) * r)) := by
  refine mul_lower_le_upper μ J (fun j => Metric.ball (centers j) (r / 2))
    (Metric.ball z ((m + 1 / 2) * r))
    (fun _ _ => Metric.isOpen_ball.measurableSet)
    (balls_disjoint hsep) ?_ hlarge_fin hL
  intro j hj x hx
  exact balls_subset_ball (J := J) (centers := centers) (z := z) (r := r) (m := m) hJz
    (Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨hj, hx⟩⟩)








theorem ball_card_le_meas {α ι : Type*} [PseudoMetricSpace α] [MeasurableSpace α]
    (μ : Measure α) (J : Finset ι) (centers : ι → α) (z : α)
    {r m L U : Real} {N : Nat}
    (hLpos : 0 < L) (hUnonneg : 0 ≤ U)
    (hsmall_meas : ∀ j ∈ J, MeasurableSet (Metric.ball (centers j) (r / 2)))
    (hsep : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → r ≤ dist (centers i) (centers j))
    (hJz : ∀ j ∈ J, dist (centers j) z ≤ m * r)
    (hlower : ∀ j ∈ J,
      ENNReal.ofReal L ≤ μ (Metric.ball (centers j) (r / 2)))
    (hupper : μ (Metric.ball z ((m + 1 / 2) * r)) ≤ ENNReal.ofReal U)
    (hcap : U < ((N + 1 : Nat) : Real) * L) :
    J.card ≤ N := by
  have hlarge_fin : μ (Metric.ball z ((m + 1 / 2) * r)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hupper
  have hLreal :
      ∀ j ∈ J, L ≤ μ.real (Metric.ball (centers j) (r / 2)) := by
    intro j hj
    exact (ENNReal.ofReal_le_iff_le_toReal
      (measure_ne_top_of_subset
        (by
          intro x hx
          exact balls_subset_ball (J := J) (centers := centers) (z := z)
            (r := r) (m := m) hJz
            (Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨hj, hx⟩⟩))
        hlarge_fin)).mp (hlower j hj)
  have hmul :
      (J.card : Real) * L ≤ μ.real (Metric.ball z ((m + 1 / 2) * r)) :=
    mul_lower_le_upper μ J (fun j => Metric.ball (centers j) (r / 2))
      (Metric.ball z ((m + 1 / 2) * r)) hsmall_meas
      (balls_disjoint hsep)
      (by
        intro j hj x hx
        exact balls_subset_ball (J := J) (centers := centers) (z := z)
          (r := r) (m := m) hJz
          (Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨hj, hx⟩⟩))
      hlarge_fin hLreal
  have hupper_real :
      μ.real (Metric.ball z ((m + 1 / 2) * r)) ≤ U :=
    ENNReal.toReal_le_of_le_ofReal hUnonneg hupper
  exact card_le_of_mul_lt hLpos (hmul.trans hupper_real) hcap







theorem ball_card_le_of_vol {α ι : Type*} [PseudoMetricSpace α]
    [MeasurableSpace α] [BorelSpace α]
    (μ : Measure α) (J : Finset ι) (centers : ι → α) (z : α)
    {r m L U : Real} {N : Nat}
    (hLpos : 0 < L) (hUnonneg : 0 ≤ U)
    (hsep : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → r ≤ dist (centers i) (centers j))
    (hJz : ∀ j ∈ J, dist (centers j) z ≤ m * r)
    (hlower : ∀ j ∈ J,
      ENNReal.ofReal L ≤ μ (Metric.ball (centers j) (r / 2)))
    (hupper : μ (Metric.ball z ((m + 1 / 2) * r)) ≤ ENNReal.ofReal U)
    (hcap : U < ((N + 1 : Nat) : Real) * L) :
    J.card ≤ N :=
  ball_card_le_meas μ J centers z hLpos hUnonneg
    (fun _ _ => Metric.isOpen_ball.measurableSet)
    hsep hJz hlower hupper hcap

end VolumeComparison
end Riemannian
end Geometry
end DifferentialGeometry
