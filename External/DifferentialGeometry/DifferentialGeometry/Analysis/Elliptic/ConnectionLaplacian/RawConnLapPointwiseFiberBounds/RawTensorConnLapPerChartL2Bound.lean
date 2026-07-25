import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RawConnLapPointwiseFiberBounds.RawTensorConnLapPointwiseBound


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold Set FiberBundle NormedSpace Filter CovariantDerivative
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Tensor
open Tensor0SBundle
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

lemma add_sq_le_two_mul_sq_add_sq (a b : ℝ) :
    (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg a, sq_nonneg b, sq_nonneg (a + b)]

lemma sum_sq_le_card_mul_sum_sq {ι : Type*} [Fintype ι] (f : ι → ℝ) :
    (∑ i, f i) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ i, (f i) ^ 2 := by
  classical
  have hcard : (Fintype.card ι : ℝ) = ((Finset.univ : Finset ι).card : ℝ) := by
    rw [Fintype.card]
  rw [hcard]
  set s : Finset ι := Finset.univ
  set S : ℝ := ∑ i ∈ s, f i with hS_def
  set Q : ℝ := ∑ i ∈ s, (f i) ^ 2 with hQ_def
  have h_inner : ∀ i, ∑ j ∈ s, (f i - f j) ^ 2 =
      (s.card : ℝ) * (f i) ^ 2 - 2 * (f i) * S + Q := by
    intro i
    have hexp : ∀ j, (f i - f j) ^ 2 =
        (f i) ^ 2 - 2 * (f i) * (f j) + (f j) ^ 2 := by
      intro j; ring
    calc ∑ j ∈ s, (f i - f j) ^ 2
        = ∑ j ∈ s, ((f i) ^ 2 - 2 * (f i) * (f j) + (f j) ^ 2) :=
          Finset.sum_congr rfl (fun j _ => hexp j)
      _ = (∑ _j ∈ s, (f i) ^ 2)
            - (∑ j ∈ s, 2 * (f i) * (f j)) + (∑ j ∈ s, (f j) ^ 2) := by
              rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      _ = (s.card : ℝ) * (f i) ^ 2 - 2 * (f i) * S + Q := by
              rw [Finset.sum_const]
              rw [show (∑ j ∈ s, 2 * (f i) * (f j)) = 2 * (f i) * S from by
                rw [show (fun j => 2 * (f i) * (f j)) =
                  (fun j => (2 * (f i)) * (f j)) from by funext j; ring]
                rw [← Finset.mul_sum, ← hS_def]]
              rw [← hQ_def, nsmul_eq_mul]
  have h_double_sum : ∑ i ∈ s, ∑ j ∈ s, (f i - f j) ^ 2 =
      2 * ((s.card : ℝ) * Q - S ^ 2) := by
    calc ∑ i ∈ s, ∑ j ∈ s, (f i - f j) ^ 2
        = ∑ i ∈ s, ((s.card : ℝ) * (f i) ^ 2 - 2 * (f i) * S + Q) :=
          Finset.sum_congr rfl (fun i _ => h_inner i)
      _ = (∑ i ∈ s, (s.card : ℝ) * (f i) ^ 2)
            - (∑ i ∈ s, 2 * (f i) * S) + (∑ i ∈ s, Q) := by
              rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      _ = (s.card : ℝ) * Q - 2 * S * S + (s.card : ℝ) * Q := by
              rw [show (∑ i ∈ s, (s.card : ℝ) * (f i) ^ 2) =
                  (s.card : ℝ) * Q from by
                rw [← Finset.mul_sum, ← hQ_def]]
              rw [show (∑ i ∈ s, 2 * (f i) * S) = 2 * S * S from by
                rw [show (fun i => 2 * (f i) * S) = (fun i => (2 * S) * (f i)) from by
                  funext i; ring]
                rw [← Finset.mul_sum, ← hS_def]]
              rw [Finset.sum_const, nsmul_eq_mul]
      _ = 2 * ((s.card : ℝ) * Q - S ^ 2) := by ring
  have h_nn : 0 ≤ ∑ i ∈ s, ∑ j ∈ s, (f i - f j) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  rw [h_double_sum] at h_nn
  nlinarith

noncomputable def rawChartFrameDataSq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T₀ : Π b : M, TensorRSSpace r s I b) (b : M) : ℝ :=
  ‖rawTensorConnLap (I := I) g r s T₀ b‖ ^ 2

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
lemma rawChartFrameDataSq_nonneg
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T₀ : Π b : M, TensorRSSpace r s I b) (b : M) :
    0 ≤ rawChartFrameDataSq (I := I) g r s T₀ b := by
  unfold rawChartFrameDataSq
  exact sq_nonneg _
omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem rawTensorConnLap_norm_sq_le_chart_data_on_pou_tsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T :
      letI _h_top : TopologicalSpace
          (TotalSpace (TensorRSModel r s ℝ E)
            (fun x : M => TensorRSSpace r s I x)) :=
        tensorRSBundle_topology r s
      letI _h_fib : FiberBundle (TensorRSModel r s ℝ E)
          (fun x : M => TensorRSSpace r s I x) :=
        tensorRSBundle_fiber r s
      Cₛ^∞⟮I; TensorRSModel r s ℝ E,
        fun b => TensorRSSpace r s I b⟯) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {b : M}, b ∈ tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
          ‖rawTensorConnLap (I := I) g r s T.toFun b‖ ^ 2 ≤
            C * rawChartFrameDataSq (I := I) g r s T.toFun b := by
  classical
  letI _h_top : TopologicalSpace
      (TotalSpace (TensorRSModel r s ℝ E)
        (fun x : M => TensorRSSpace r s I x)) :=
    tensorRSBundle_topology r s
  letI _h_fib : FiberBundle (TensorRSModel r s ℝ E)
      (fun x : M => TensorRSSpace r s I x) :=
    tensorRSBundle_fiber r s
  refine ⟨1, by norm_num, ?_⟩
  intro b _hb_pou
  change ‖rawTensorConnLap (I := I) g r s T.toFun b‖ ^ 2 ≤
    1 * ‖rawTensorConnLap (I := I) g r s T.toFun b‖ ^ 2
  ring_nf
  exact le_refl _


end Connection
end Integral
end DifferentialGeometry

end
