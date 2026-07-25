import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.L2Bound


noncomputable section

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]   [Module.Finite ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] in
lemma riemannianFiberNormSq_add_expand
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (a b : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (a + b) =
      riemannianFiberNormSq (I := I) (M := M) g r s x a +
        2 * tensorInnerPointwise (I := I) (M := M) g r s x
            (TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s)
              (x := x) a)
            (TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s)
              (x := x) b) +
        riemannianFiberNormSq (I := I) (M := M) g r s x b := by
  classical
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (a + b),
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x a,
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x b]
  rw [TensorRSSpace.toModel_add]
  rw [tensorInnerPointwise_add_left, tensorInnerPointwise_add_right,
    tensorInnerPointwise_add_right]
  have hsymm := tensorInnerPointwise_symm (I := I) (M := M) g r s x
    (TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := x) b)
    (TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := x) a)
  rw [hsymm]
  ring

omit [NeZero (Module.finrank ℝ E)] in
theorem riemannianFiberNormSq_add_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (a b : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (a + b) ≤
      2 * riemannianFiberNormSq (I := I) (M := M) g r s x a +
        2 * riemannianFiberNormSq (I := I) (M := M) g r s x b := by
  classical
  set am := TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s)
    (x := x) a with ham
  set bm := TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s)
    (x := x) b with hbm
  have haa : riemannianFiberNormSq (I := I) (M := M) g r s x a =
      tensorInnerPointwise (I := I) (M := M) g r s x am am := by
    rw [ham]; exact riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x a
  have hbb : riemannianFiberNormSq (I := I) (M := M) g r s x b =
      tensorInnerPointwise (I := I) (M := M) g r s x bm bm := by
    rw [hbm]; exact riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x b
  rw [riemannianFiberNormSq_add_expand (I := I) (M := M) g r s x a b, ← ham, ← hbm]
  set A : ℝ := riemannianFiberNormSq (I := I) (M := M) g r s x a with hA
  set B : ℝ := riemannianFiberNormSq (I := I) (M := M) g r s x b with hB
  set C : ℝ := tensorInnerPointwise (I := I) (M := M) g r s x am bm with hC
  have hA_nn : 0 ≤ A := by rw [hA]; exact riemannianFiberNormSq_nonneg (I := I) (M := M) g r s x a
  have hB_nn : 0 ≤ B := by rw [hB]; exact riemannianFiberNormSq_nonneg (I := I) (M := M) g r s x b
  have hCS : C ^ 2 ≤ A * B := by
    rw [haa, hbb]
    exact tensorInnerPointwise_sq_le_mul (I := I) (M := M) g r s x am bm
  nlinarith [hCS, hA_nn, hB_nn, sq_nonneg (A - B), sq_nonneg (C - A), sq_nonneg (C - B)]

omit [NeZero (Module.finrank ℝ E)] in
theorem riemannianFiberNormSq_sub_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (a b : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (a - b) ≤
      2 * riemannianFiberNormSq (I := I) (M := M) g r s x a +
        2 * riemannianFiberNormSq (I := I) (M := M) g r s x b := by
  classical
  have hneg : riemannianFiberNormSq (I := I) (M := M) g r s x (-b) =
      riemannianFiberNormSq (I := I) (M := M) g r s x b := by
    rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (-b),
      riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x b]
    rw [TensorRSSpace.toModel_neg]
    rw [show (-(TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s)
          (x := x) b)) = ((-1 : ℝ) • TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
          (r := r) (s := s) (x := x) b) from by rw [neg_one_smul]]
    rw [tensorInnerPointwise_smul_left, tensorInnerPointwise_smul_right]
    ring
  rw [sub_eq_add_neg]
  calc riemannianFiberNormSq (I := I) (M := M) g r s x (a + (-b))
      ≤ 2 * riemannianFiberNormSq (I := I) (M := M) g r s x a +
          2 * riemannianFiberNormSq (I := I) (M := M) g r s x (-b) :=
        riemannianFiberNormSq_add_le (I := I) (M := M) g r s x a (-b)
    _ = 2 * riemannianFiberNormSq (I := I) (M := M) g r s x a +
          2 * riemannianFiberNormSq (I := I) (M := M) g r s x b := by rw [hneg]

omit [NeZero (Module.finrank ℝ E)] in
private lemma tensorInnerPointwise_plain_sum_left
    {ι : Type*} (g : SmoothRiemannianMetric I M) (r s' : ℕ) (x : M)
    (s : Finset ι) (A : ι → TensorRSModel r s' ℝ E) (B : TensorRSModel r s' ℝ E) :
    tensorInnerPointwise (I := I) (M := M) g r s' x (∑ k ∈ s, A k) B =
      ∑ k ∈ s, tensorInnerPointwise (I := I) (M := M) g r s' x (A k) B := by
  classical
  induction s using Finset.induction with
  | empty => simp [tensorInnerPointwise_zero_left]
  | insert i₀ s'' hi₀ ih =>
      rw [Finset.sum_insert hi₀, tensorInnerPointwise_add_left, ih, Finset.sum_insert hi₀]

omit [NeZero (Module.finrank ℝ E)] in
private lemma tensorInnerPointwise_plain_sum_right
    {ι : Type*} (g : SmoothRiemannianMetric I M) (r s' : ℕ) (x : M)
    (A : TensorRSModel r s' ℝ E) (s : Finset ι) (B : ι → TensorRSModel r s' ℝ E) :
    tensorInnerPointwise (I := I) (M := M) g r s' x A (∑ l ∈ s, B l) =
      ∑ l ∈ s, tensorInnerPointwise (I := I) (M := M) g r s' x A (B l) := by
  classical
  induction s using Finset.induction with
  | empty => simp [tensorInnerPointwise_zero_right]
  | insert j₀ s'' hj₀ ih =>
      rw [Finset.sum_insert hj₀, tensorInnerPointwise_add_right, ih, Finset.sum_insert hj₀]

omit [NeZero (Module.finrank ℝ E)] in
lemma riemannianFiberNormSq_sum_eq_double_sum
    {ι : Type*} (g : SmoothRiemannianMetric I M) (r s' : ℕ) (x : M)
    (s : Finset ι) (F : ι → TensorRSSpace r s' I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s' x (∑ i ∈ s, F i) =
      ∑ i ∈ s, ∑ j ∈ s, tensorInnerPointwise (I := I) (M := M) g r s' x
          (TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s')
            (x := x) (F i))
          (TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s')
            (x := x) (F j)) := by
  classical
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s' x (∑ i ∈ s, F i)]
  have hsum_model : TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s')
      (x := x) (∑ i ∈ s, F i) =
      ∑ i ∈ s, TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s')
        (x := x) (F i) :=
    map_sum (tensorRSSpace_continuousLinearEquiv (I := I) r s' x) F s
  rw [hsum_model]
  rw [tensorInnerPointwise_plain_sum_left (I := I) (M := M) g r s' x s _ _]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [tensorInnerPointwise_plain_sum_right (I := I) (M := M) g r s' x _ s _]

omit [NeZero (Module.finrank ℝ E)] in
theorem riemannianFiberNormSq_sum_le_card_mul
    {ι : Type*} (g : SmoothRiemannianMetric I M) (r s' : ℕ) (x : M)
    (s : Finset ι) (F : ι → TensorRSSpace r s' I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s' x (∑ i ∈ s, F i) ≤
      (s.card : ℝ) * ∑ i ∈ s, riemannianFiberNormSq (I := I) (M := M) g r s' x (F i) := by
  classical
  rw [riemannianFiberNormSq_sum_eq_double_sum (I := I) (M := M) g r s' x s F]
  set fm : ι → TensorRSModel r s' ℝ E := fun i =>
    TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s') (x := x) (F i)
    with hfm
  have hrfns_eq : ∀ i,
      riemannianFiberNormSq (I := I) (M := M) g r s' x (F i) =
        tensorInnerPointwise (I := I) (M := M) g r s' x (fm i) (fm i) := by
    intro i; rw [hfm]
    exact riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s' x (F i)
  have hpair : ∀ i ∈ s, ∀ j ∈ s,
      tensorInnerPointwise (I := I) (M := M) g r s' x (fm i) (fm j) ≤
        (1 / 2 : ℝ) * (riemannianFiberNormSq (I := I) (M := M) g r s' x (F i) +
          riemannianFiberNormSq (I := I) (M := M) g r s' x (F j)) := by
    intro i _ j _
    set bij : ℝ := tensorInnerPointwise (I := I) (M := M) g r s' x (fm i) (fm j) with hbij
    have hsq : bij ^ 2 ≤
        riemannianFiberNormSq (I := I) (M := M) g r s' x (F i) *
          riemannianFiberNormSq (I := I) (M := M) g r s' x (F j) := by
      rw [hbij, hrfns_eq i, hrfns_eq j]
      exact tensorInnerPointwise_sq_le_mul (I := I) (M := M) g r s' x (fm i) (fm j)
    have hi_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g r s' x (F i) :=
      riemannianFiberNormSq_nonneg (I := I) (M := M) g r s' x (F i)
    have hj_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g r s' x (F j) :=
      riemannianFiberNormSq_nonneg (I := I) (M := M) g r s' x (F j)
    nlinarith [hsq, hi_nn, hj_nn, sq_nonneg (riemannianFiberNormSq (I := I) (M := M) g r s' x (F i)
      - riemannianFiberNormSq (I := I) (M := M) g r s' x (F j)), sq_nonneg bij]
  calc (∑ i ∈ s, ∑ j ∈ s, tensorInnerPointwise (I := I) (M := M) g r s' x (fm i) (fm j))
      ≤ ∑ i ∈ s, ∑ j ∈ s, (1 / 2 : ℝ) *
          (riemannianFiberNormSq (I := I) (M := M) g r s' x (F i) +
            riemannianFiberNormSq (I := I) (M := M) g r s' x (F j)) := by
        refine Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => hpair i hi j hj))
    _ = (s.card : ℝ) * ∑ i ∈ s, riemannianFiberNormSq (I := I) (M := M) g r s' x (F i) := by
        rw [show (∑ i ∈ s, ∑ j ∈ s, (1 / 2 : ℝ) *
              (riemannianFiberNormSq (I := I) (M := M) g r s' x (F i) +
                riemannianFiberNormSq (I := I) (M := M) g r s' x (F j))) =
            (1 / 2 : ℝ) * (∑ i ∈ s, ∑ j ∈ s,
              (riemannianFiberNormSq (I := I) (M := M) g r s' x (F i) +
                riemannianFiberNormSq (I := I) (M := M) g r s' x (F j))) from by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun i _ => ?_); rw [Finset.mul_sum]]
        rw [show (∑ i ∈ s, ∑ j ∈ s,
              (riemannianFiberNormSq (I := I) (M := M) g r s' x (F i) +
                riemannianFiberNormSq (I := I) (M := M) g r s' x (F j))) =
            ∑ i ∈ s, ((s.card : ℝ) * riemannianFiberNormSq (I := I) (M := M) g r s' x (F i) +
              ∑ j ∈ s, riemannianFiberNormSq (I := I) (M := M) g r s' x (F j)) from by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
        ring

end Connection
end Integral
end DifferentialGeometry

end
