import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.RankRDiffBilinGrid
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldCovariantCalculusRS


noncomputable section

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] [CompleteSpace E] in
private theorem riemannianFiberNormSq_toSection_heq_congr_leibnizTower (g : SmoothRiemannianMetric I M)
    {a b : ℕ} (h : a = b) {Y : SmoothCcTensor g 0 a} {Z : SmoothCcTensor g 0 b}
    (hYZ : HEq Y Z) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 0 a x (Y.toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g 0 b x (Z.toSection x) := by
  subst h; rw [eq_of_heq hYZ]


omit [BoundarylessManifold I M] [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem rfns_iteratedCovGrad_covGrad_comm_drop (g : SmoothRiemannianMetric I M)
    (s m : ℕ) (W : SmoothCcTensor g 0 s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 0 ((s + 1) + m) x
        ((iteratedCovGrad g 0 (s + 1) m (covGrad g 0 s W)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + (m + 1)) x
        ((iteratedCovGrad g 0 s (m + 1) W).toSection x) :=
  riemannianFiberNormSq_toSection_heq_congr_leibnizTower g (by omega : (s + 1) + m = s + (m + 1))
    (iteratedCovGrad_covGrad_comm_heq' g 0 s m W) x

private lemma sum_range_shift_le_drop (n : ℕ) (f : ℕ → ℝ) (hf : ∀ i, 0 ≤ f i) :
    ∑ i ∈ Finset.range n, f (i + 1) ≤ ∑ i ∈ Finset.range (n + 1), f i := by
  rw [Finset.sum_range_succ' f n]
  exact le_add_of_nonneg_right (hf 0)


omit [BoundarylessManifold I M] [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem rfns_iteratedCovGrad_covGrad_comm (g : SmoothRiemannianMetric I M)
    (s m : ℕ) (W : SmoothCcTensor g 0 s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 0 ((s + 1) + m) x
        ((iteratedCovGrad g 0 (s + 1) m (covGrad g 0 s W)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + (m + 1)) x
        ((iteratedCovGrad g 0 s (m + 1) W).toSection x) :=
  rfns_iteratedCovGrad_covGrad_comm_drop g s m W x

def slotExtendIter (g : SmoothRiemannianMetric I M) (b₀ s₀ : ℕ) :
    ∀ (w : ℕ), SmoothCcTensor g b₀ s₀ → SmoothCcTensor g (b₀ + w) (s₀ + w)
  | 0, C => C
  | (w + 1), C =>
      slotExtend (I := I) (M := M) g (b₀ + w) (s₀ + w) (slotExtendIter g b₀ s₀ w C)

def appCcLeibnizTower (g : SmoothRiemannianMetric I M) (b₀ s₀ : ℕ) (C : SmoothCcTensor g b₀ s₀) :
    ∀ (p w : ℕ), SmoothCcTensor g 0 (b₀ + w) → SmoothCcTensor g 0 ((s₀ + w) + p)
  | 0, w => fun W =>
      ccOperatorFieldComp (I := I) (M := M) g 0 (b₀ + w) (s₀ + w) (slotExtendIter g b₀ s₀ w C) W
  | (p + 1), w => fun W =>
      covGrad (I := I) (M := M) g 0 ((s₀ + w) + p)
          (appCcLeibnizTower g b₀ s₀ C p w W) -
        castCcTensorRank g 0 (by omega : (s₀ + (w + 1)) + p = (s₀ + w) + (p + 1))
          (appCcLeibnizTower g b₀ s₀ C p (w + 1) (covGrad (I := I) (M := M) g 0 (b₀ + w) W))

omit [BoundarylessManifold I M] [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem DropTower_covGrad_op (g : SmoothRiemannianMetric I M) (b₀ s₀ : ℕ)
    (C : SmoothCcTensor g b₀ s₀) (p w : ℕ) (W : SmoothCcTensor g 0 (b₀ + w)) :
    covGrad (I := I) (M := M) g 0 ((s₀ + w) + p)
        (appCcLeibnizTower (I := I) (M := M) g b₀ s₀ C p w W) =
      appCcLeibnizTower (I := I) (M := M) g b₀ s₀ C (p + 1) w W +
        castCcTensorRank g 0 (by omega : (s₀ + (w + 1)) + p = (s₀ + w) + (p + 1))
          (appCcLeibnizTower (I := I) (M := M) g b₀ s₀ C p (w + 1)
            (covGrad (I := I) (M := M) g 0 (b₀ + w) W)) := by
  change _ = (covGrad (I := I) (M := M) g 0 ((s₀ + w) + p)
      (appCcLeibnizTower (I := I) (M := M) g b₀ s₀ C p w W) -
      castCcTensorRank g 0 (by omega : (s₀ + (w + 1)) + p = (s₀ + w) + (p + 1))
        (appCcLeibnizTower (I := I) (M := M) g b₀ s₀ C p (w + 1)
          (covGrad (I := I) (M := M) g 0 (b₀ + w) W))) + _
  rw [sub_add_cancel]

def DropTowerNormalForm (g : SmoothRiemannianMetric I M) (b₀ s₀ : ℕ)
    (C : SmoothCcTensor g b₀ s₀) (p w : ℕ) : Prop :=
  ∃ Ψ : (k : ℕ) → SmoothCcTensor g ((b₀ + w) + k) ((s₀ + w) + p),
    ∀ W : SmoothCcTensor g 0 (b₀ + w),
      appCcLeibnizTower (I := I) (M := M) g b₀ s₀ C p w W =
        ∑ k ∈ Finset.range (p + 1),
          ccOperatorFieldComp (I := I) (M := M) g 0 ((b₀ + w) + k) ((s₀ + w) + p) (Ψ k)
            (iteratedCovGrad g 0 (b₀ + w) k W)

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem covGrad_dropNormalForm_sum (g : SmoothRiemannianMetric I M) (b₀ s₀ p w : ℕ)
    (Ψ : (k : ℕ) → SmoothCcTensor g ((b₀ + w) + k) ((s₀ + w) + p))
    (W : SmoothCcTensor g 0 (b₀ + w)) :
    covGrad (I := I) (M := M) g 0 ((s₀ + w) + p)
        (∑ k ∈ Finset.range (p + 1),
          ccOperatorFieldComp (I := I) (M := M) g 0 ((b₀ + w) + k) ((s₀ + w) + p) (Ψ k)
            (iteratedCovGrad g 0 (b₀ + w) k W)) =
      ∑ k ∈ Finset.range (p + 1),
        (ccOperatorFieldComp (I := I) (M := M) g 0 ((b₀ + w) + k) ((s₀ + w) + (p + 1))
            (covGrad (I := I) (M := M) g ((b₀ + w) + k) ((s₀ + w) + p) (Ψ k))
            (iteratedCovGrad g 0 (b₀ + w) k W) +
          ccOperatorFieldComp (I := I) (M := M) g 0 ((b₀ + w) + (k + 1)) ((s₀ + w) + (p + 1))
            (slotExtend (I := I) (M := M) g ((b₀ + w) + k) ((s₀ + w) + p) (Ψ k))
            (iteratedCovGrad g 0 (b₀ + w) (k + 1) W)) := by
  rw [covGrad_finset_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [covGrad_appCcRS_eq (I := I) (M := M) g 0 ((b₀ + w) + k) ((s₀ + w) + p) (Ψ k)
    (iteratedCovGrad g 0 (b₀ + w) k W)]
  rw [show covGrad (I := I) (M := M) g 0 ((b₀ + w) + k) (iteratedCovGrad g 0 (b₀ + w) k W) =
      iteratedCovGrad g 0 (b₀ + w) (k + 1) W from (iteratedCovGrad_succ g 0 (b₀ + w) k W).symm]
  rfl

omit [BoundarylessManifold I M] [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem castRankCc_appCcRS_drop_iteratedCovGrad_covGrad (g : SmoothRiemannianMetric I M)
    (b₀ s₀ p w k : ℕ)
    (Ψ : SmoothCcTensor g ((b₀ + (w + 1)) + k) ((s₀ + (w + 1)) + p))
    (W : SmoothCcTensor g 0 (b₀ + w)) :
    castCcTensorRank g 0 (by omega : (s₀ + (w + 1)) + p = (s₀ + w) + (p + 1))
        (ccOperatorFieldComp (I := I) (M := M) g 0 ((b₀ + (w + 1)) + k) ((s₀ + (w + 1)) + p) Ψ
          (iteratedCovGrad g 0 (b₀ + (w + 1)) k (covGrad g 0 (b₀ + w) W))) =
      ccOperatorFieldComp (I := I) (M := M) g 0 ((b₀ + w) + (k + 1)) ((s₀ + w) + (p + 1))
        (castCcTensorSourceRank g ((s₀ + w) + (p + 1)) (by omega : (b₀ + (w + 1)) + k = (b₀ + w) + (k + 1))
          (castCcTensorRank g ((b₀ + (w + 1)) + k)
            (by omega : (s₀ + (w + 1)) + p = (s₀ + w) + (p + 1)) Ψ))
        (iteratedCovGrad g 0 (b₀ + w) (k + 1) W) := by
  rw [appCcRS_castRankCc_db g 0 (by omega : (b₀ + (w + 1)) + k = (b₀ + w) + (k + 1))
    (by omega : (s₀ + (w + 1)) + p = (s₀ + w) + (p + 1)) Ψ
    (iteratedCovGrad g 0 (b₀ + (w + 1)) k (covGrad g 0 (b₀ + w) W))]
  congr 1
  apply eq_of_heq
  refine HEq.trans ?_ (iteratedCovGrad_covGrad_comm_heq' g 0 (b₀ + w) k W)
  exact castRankCc_db_heq g 0 (by omega : (b₀ + (w + 1)) + k = (b₀ + w) + (k + 1))
    (iteratedCovGrad g 0 (b₀ + (w + 1)) k (covGrad g 0 (b₀ + w) W))

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem dropNormalForm_succ (g : SmoothRiemannianMetric I M) (b₀ s₀ : ℕ)
    (C : SmoothCcTensor g b₀ s₀) (p : ℕ)
    (hp : ∀ w, DropTowerNormalForm (I := I) (M := M) g b₀ s₀ C p w) (w : ℕ) :
    DropTowerNormalForm (I := I) (M := M) g b₀ s₀ C (p + 1) w := by
  classical
  obtain ⟨Ψr, hΨr⟩ := hp w
  obtain ⟨Ψr1, hΨr1⟩ := hp (w + 1)
  set Tk : (k : ℕ) → SmoothCcTensor g ((b₀ + w) + (k + 1)) ((s₀ + w) + (p + 1)) := fun k =>
    slotExtend (I := I) (M := M) g ((b₀ + w) + k) ((s₀ + w) + p) (Ψr k) -
      castCcTensorSourceRank g ((s₀ + w) + (p + 1)) (by omega : (b₀ + (w + 1)) + k = (b₀ + w) + (k + 1))
        (castCcTensorRank g ((b₀ + (w + 1)) + k)
          (by omega : (s₀ + (w + 1)) + p = (s₀ + w) + (p + 1)) (Ψr1 k))
    with hTk_def
  refine ⟨fun j => match j with
    | 0 => covGrad (I := I) (M := M) g ((b₀ + w) + 0) ((s₀ + w) + p) (Ψr 0)
    | (k + 1) =>
        (if k + 1 < p + 1 then
            covGrad (I := I) (M := M) g ((b₀ + w) + (k + 1)) ((s₀ + w) + p) (Ψr (k + 1)) else 0)
          + Tk k, ?_⟩
  intro W
  have hrec : appCcLeibnizTower (I := I) (M := M) g b₀ s₀ C (p + 1) w W =
      covGrad g 0 ((s₀ + w) + p) (appCcLeibnizTower (I := I) (M := M) g b₀ s₀ C p w W) -
        castCcTensorRank g 0 (by omega : (s₀ + (w + 1)) + p = (s₀ + w) + (p + 1))
          (appCcLeibnizTower (I := I) (M := M) g b₀ s₀ C p (w + 1)
            (covGrad (I := I) (M := M) g 0 (b₀ + w) W)) := by
    rw [DropTower_covGrad_op (I := I) (M := M) g b₀ s₀ C p w W]; abel
  rw [hrec, hΨr W]
  rw [covGrad_dropNormalForm_sum (I := I) (M := M) g b₀ s₀ p w Ψr W]
  rw [hΨr1 (covGrad g 0 (b₀ + w) W), castRankCc_db_finset_sum]
  rw [show (∑ k ∈ Finset.range (p + 1),
        castCcTensorRank g 0 (by omega : (s₀ + (w + 1)) + p = (s₀ + w) + (p + 1))
          (ccOperatorFieldComp (I := I) (M := M) g 0 ((b₀ + (w + 1)) + k) ((s₀ + (w + 1)) + p) (Ψr1 k)
            (iteratedCovGrad g 0 (b₀ + (w + 1)) k (covGrad g 0 (b₀ + w) W)))) =
      ∑ k ∈ Finset.range (p + 1),
        ccOperatorFieldComp (I := I) (M := M) g 0 ((b₀ + w) + (k + 1)) ((s₀ + w) + (p + 1))
          (castCcTensorSourceRank g ((s₀ + w) + (p + 1)) (by omega : (b₀ + (w + 1)) + k = (b₀ + w) + (k + 1))
            (castCcTensorRank g ((b₀ + (w + 1)) + k)
              (by omega : (s₀ + (w + 1)) + p = (s₀ + w) + (p + 1)) (Ψr1 k)))
          (iteratedCovGrad g 0 (b₀ + w) (k + 1) W) from
    Finset.sum_congr rfl (fun k _ =>
      castRankCc_appCcRS_drop_iteratedCovGrad_covGrad (I := I) (M := M) g b₀ s₀ p w k (Ψr1 k) W)]
  rw [Finset.sum_add_distrib]
  rw [Finset.sum_range_succ' (fun j =>
    ccOperatorFieldComp (I := I) (M := M) g 0 ((b₀ + w) + j) ((s₀ + w) + (p + 1))
      ((match j with
        | 0 => covGrad (I := I) (M := M) g ((b₀ + w) + 0) ((s₀ + w) + p) (Ψr 0)
        | (k + 1) =>
            (if k + 1 < p + 1 then
                covGrad (I := I) (M := M) g ((b₀ + w) + (k + 1)) ((s₀ + w) + p) (Ψr (k + 1))
              else 0) + Tk k))
      (iteratedCovGrad g 0 (b₀ + w) j W)) (p + 1)]
  rw [show (∑ k ∈ Finset.range (p + 1),
        ccOperatorFieldComp (I := I) (M := M) g 0 ((b₀ + w) + (k + 1)) ((s₀ + w) + (p + 1))
          ((if k + 1 < p + 1 then
              covGrad (I := I) (M := M) g ((b₀ + w) + (k + 1)) ((s₀ + w) + p) (Ψr (k + 1))
            else 0) + Tk k)
          (iteratedCovGrad g 0 (b₀ + w) (k + 1) W)) =
      (∑ k ∈ Finset.range (p + 1),
        ccOperatorFieldComp (I := I) (M := M) g 0 ((b₀ + w) + (k + 1)) ((s₀ + w) + (p + 1))
          (if k + 1 < p + 1 then
              covGrad (I := I) (M := M) g ((b₀ + w) + (k + 1)) ((s₀ + w) + p) (Ψr (k + 1))
            else 0)
          (iteratedCovGrad g 0 (b₀ + w) (k + 1) W)) +
      (∑ k ∈ Finset.range (p + 1),
        ccOperatorFieldComp (I := I) (M := M) g 0 ((b₀ + w) + (k + 1)) ((s₀ + w) + (p + 1)) (Tk k)
          (iteratedCovGrad g 0 (b₀ + w) (k + 1) W)) from by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [appCcRS_add_left]]
  rw [show (∑ k ∈ Finset.range (p + 1),
        ccOperatorFieldComp (I := I) (M := M) g 0 ((b₀ + w) + (k + 1)) ((s₀ + w) + (p + 1)) (Tk k)
          (iteratedCovGrad g 0 (b₀ + w) (k + 1) W)) =
      (∑ k ∈ Finset.range (p + 1),
        ccOperatorFieldComp (I := I) (M := M) g 0 ((b₀ + w) + (k + 1)) ((s₀ + w) + (p + 1))
          (slotExtend (I := I) (M := M) g ((b₀ + w) + k) ((s₀ + w) + p) (Ψr k))
          (iteratedCovGrad g 0 (b₀ + w) (k + 1) W)) -
      (∑ k ∈ Finset.range (p + 1),
        ccOperatorFieldComp (I := I) (M := M) g 0 ((b₀ + w) + (k + 1)) ((s₀ + w) + (p + 1))
          (castCcTensorSourceRank g ((s₀ + w) + (p + 1)) (by omega : (b₀ + (w + 1)) + k = (b₀ + w) + (k + 1))
            (castCcTensorRank g ((b₀ + (w + 1)) + k)
              (by omega : (s₀ + (w + 1)) + p = (s₀ + w) + (p + 1)) (Ψr1 k)))
          (iteratedCovGrad g 0 (b₀ + w) (k + 1) W)) from by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hTk_def, appCcRS_sub_left]]
  rw [show (∑ k ∈ Finset.range (p + 1),
        ccOperatorFieldComp (I := I) (M := M) g 0 ((b₀ + w) + (k + 1)) ((s₀ + w) + (p + 1))
          (if k + 1 < p + 1 then
              covGrad (I := I) (M := M) g ((b₀ + w) + (k + 1)) ((s₀ + w) + p) (Ψr (k + 1))
            else 0)
          (iteratedCovGrad g 0 (b₀ + w) (k + 1) W)) =
      ∑ k ∈ Finset.range p,
        ccOperatorFieldComp (I := I) (M := M) g 0 ((b₀ + w) + (k + 1)) ((s₀ + w) + (p + 1))
          (covGrad (I := I) (M := M) g ((b₀ + w) + (k + 1)) ((s₀ + w) + p) (Ψr (k + 1)))
          (iteratedCovGrad g 0 (b₀ + w) (k + 1) W) from by
    rw [Finset.sum_range_succ]
    rw [if_neg (by omega : ¬ (p + 1 < p + 1)), appCcRS_zero_left, add_zero]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [if_pos (by simp only [Finset.mem_range] at hk; omega : k + 1 < p + 1)]]
  rw [Finset.sum_range_succ' (fun k =>
    ccOperatorFieldComp (I := I) (M := M) g 0 ((b₀ + w) + k) ((s₀ + w) + (p + 1))
      (covGrad (I := I) (M := M) g ((b₀ + w) + k) ((s₀ + w) + p) (Ψr k))
      (iteratedCovGrad g 0 (b₀ + w) k W)) p]
  abel

omit [BoundarylessManifold I M] [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem dropNormalForm_zero (g : SmoothRiemannianMetric I M) (b₀ s₀ : ℕ)
    (C : SmoothCcTensor g b₀ s₀) (w : ℕ) :
    DropTowerNormalForm (I := I) (M := M) g b₀ s₀ C 0 w := by
  refine ⟨fun k => match k with
    | 0 => slotExtendIter (I := I) (M := M) g b₀ s₀ w C
    | (_ + 1) => 0, fun W => ?_⟩
  rw [Finset.sum_range_one]
  rfl

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem dropTower_normalForm (g : SmoothRiemannianMetric I M) (b₀ s₀ : ℕ)
    (C : SmoothCcTensor g b₀ s₀) (p : ℕ) :
    ∀ w : ℕ, DropTowerNormalForm (I := I) (M := M) g b₀ s₀ C p w := by
  induction p with
  | zero => exact fun w => dropNormalForm_zero (I := I) (M := M) g b₀ s₀ C w
  | succ p ih => exact fun w => dropNormalForm_succ (I := I) (M := M) g b₀ s₀ C p ih w

def dropTowerPsi (g : SmoothRiemannianMetric I M) (b₀ s₀ : ℕ)
    (C : SmoothCcTensor g b₀ s₀) : (p w : ℕ) → (k : ℕ) → SmoothCcTensor g ((b₀ + w) + k) ((s₀ + w) + p)
  | 0, w => fun k => match k with
      | 0 => slotExtendIter (I := I) (M := M) g b₀ s₀ w C
      | (_ + 1) => 0
  | (p + 1), w => fun j => match j with
      | 0 => covGrad (I := I) (M := M) g ((b₀ + w) + 0) ((s₀ + w) + p)
          (dropTowerPsi g b₀ s₀ C p w 0)
      | (k + 1) =>
          (if k + 1 < p + 1 then
              covGrad (I := I) (M := M) g ((b₀ + w) + (k + 1)) ((s₀ + w) + p)
                (dropTowerPsi g b₀ s₀ C p w (k + 1))
            else 0)
          + (slotExtend (I := I) (M := M) g ((b₀ + w) + k) ((s₀ + w) + p)
              (dropTowerPsi g b₀ s₀ C p w k) -
            castCcTensorSourceRank g ((s₀ + w) + (p + 1)) (by omega : (b₀ + (w + 1)) + k = (b₀ + w) + (k + 1))
              (castCcTensorRank g ((b₀ + (w + 1)) + k)
                (by omega : (s₀ + (w + 1)) + p = (s₀ + w) + (p + 1))
                (dropTowerPsi g b₀ s₀ C p (w + 1) k)))

omit [BoundarylessManifold I M] [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem dropTowerPsi_zero (g : SmoothRiemannianMetric I M) (b₀ s₀ : ℕ)
    (C : SmoothCcTensor g b₀ s₀) (w : ℕ) :
    dropTowerPsi (I := I) (M := M) g b₀ s₀ C 0 w =
      fun k => match k with
        | 0 => slotExtendIter (I := I) (M := M) g b₀ s₀ w C
        | (_ + 1) => 0 :=
  rfl

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem dropTowerPsi_spec (g : SmoothRiemannianMetric I M) (b₀ s₀ : ℕ)
    (C : SmoothCcTensor g b₀ s₀) (p w : ℕ) (W : SmoothCcTensor g 0 (b₀ + w)) :
    appCcLeibnizTower (I := I) (M := M) g b₀ s₀ C p w W =
      ∑ k ∈ Finset.range (p + 1),
        ccOperatorFieldComp (I := I) (M := M) g 0 ((b₀ + w) + k) ((s₀ + w) + p)
          (dropTowerPsi (I := I) (M := M) g b₀ s₀ C p w k)
          (iteratedCovGrad g 0 (b₀ + w) k W) := by
  induction p generalizing w W with
  | zero =>
      rw [Finset.sum_range_one]
      change ccOperatorFieldComp (I := I) (M := M) g 0 (b₀ + w) (s₀ + w)
          (slotExtendIter (I := I) (M := M) g b₀ s₀ w C) W = _
      rw [iteratedCovGrad_zero]
      rfl
  | succ p ih =>
      have hrec : appCcLeibnizTower (I := I) (M := M) g b₀ s₀ C (p + 1) w W =
          covGrad g 0 ((s₀ + w) + p) (appCcLeibnizTower (I := I) (M := M) g b₀ s₀ C p w W) -
            castCcTensorRank g 0 (by omega : (s₀ + (w + 1)) + p = (s₀ + w) + (p + 1))
              (appCcLeibnizTower (I := I) (M := M) g b₀ s₀ C p (w + 1)
                (covGrad (I := I) (M := M) g 0 (b₀ + w) W)) := by
        rw [DropTower_covGrad_op (I := I) (M := M) g b₀ s₀ C p w W]; abel
      rw [hrec, ih w W, covGrad_dropNormalForm_sum (I := I) (M := M) g b₀ s₀ p w _ W]
      rw [ih (w + 1) (covGrad g 0 (b₀ + w) W), castRankCc_db_finset_sum]
      rw [show (∑ k ∈ Finset.range (p + 1),
            castCcTensorRank g 0 (by omega : (s₀ + (w + 1)) + p = (s₀ + w) + (p + 1))
              (ccOperatorFieldComp (I := I) (M := M) g 0 ((b₀ + (w + 1)) + k) ((s₀ + (w + 1)) + p)
                (dropTowerPsi (I := I) (M := M) g b₀ s₀ C p (w + 1) k)
                (iteratedCovGrad g 0 (b₀ + (w + 1)) k (covGrad g 0 (b₀ + w) W)))) =
          ∑ k ∈ Finset.range (p + 1),
            ccOperatorFieldComp (I := I) (M := M) g 0 ((b₀ + w) + (k + 1)) ((s₀ + w) + (p + 1))
              (castCcTensorSourceRank g ((s₀ + w) + (p + 1)) (by omega : (b₀ + (w + 1)) + k = (b₀ + w) + (k + 1))
                (castCcTensorRank g ((b₀ + (w + 1)) + k)
                  (by omega : (s₀ + (w + 1)) + p = (s₀ + w) + (p + 1))
                  (dropTowerPsi (I := I) (M := M) g b₀ s₀ C p (w + 1) k)))
              (iteratedCovGrad g 0 (b₀ + w) (k + 1) W) from
        Finset.sum_congr rfl (fun k _ =>
          castRankCc_appCcRS_drop_iteratedCovGrad_covGrad (I := I) (M := M) g b₀ s₀ p w k
            (dropTowerPsi (I := I) (M := M) g b₀ s₀ C p (w + 1) k) W)]
      rw [Finset.sum_add_distrib]
      rw [Finset.sum_range_succ' (fun j =>
        ccOperatorFieldComp (I := I) (M := M) g 0 ((b₀ + w) + j) ((s₀ + w) + (p + 1))
          (dropTowerPsi (I := I) (M := M) g b₀ s₀ C (p + 1) w j)
          (iteratedCovGrad g 0 (b₀ + w) j W)) (p + 1)]
      have hPsi0 : dropTowerPsi (I := I) (M := M) g b₀ s₀ C (p + 1) w 0 =
          covGrad (I := I) (M := M) g ((b₀ + w) + 0) ((s₀ + w) + p)
            (dropTowerPsi (I := I) (M := M) g b₀ s₀ C p w 0) := rfl
      have hPsiSucc : ∀ k : ℕ, dropTowerPsi (I := I) (M := M) g b₀ s₀ C (p + 1) w (k + 1) =
          (if k + 1 < p + 1 then
              covGrad (I := I) (M := M) g ((b₀ + w) + (k + 1)) ((s₀ + w) + p)
                (dropTowerPsi (I := I) (M := M) g b₀ s₀ C p w (k + 1))
            else 0)
          + (slotExtend (I := I) (M := M) g ((b₀ + w) + k) ((s₀ + w) + p)
              (dropTowerPsi (I := I) (M := M) g b₀ s₀ C p w k) -
            castCcTensorSourceRank g ((s₀ + w) + (p + 1)) (by omega : (b₀ + (w + 1)) + k = (b₀ + w) + (k + 1))
              (castCcTensorRank g ((b₀ + (w + 1)) + k)
                (by omega : (s₀ + (w + 1)) + p = (s₀ + w) + (p + 1))
                (dropTowerPsi (I := I) (M := M) g b₀ s₀ C p (w + 1) k))) := fun k => rfl
      rw [hPsi0]
      have hsplit : (∑ k ∈ Finset.range (p + 1),
            ccOperatorFieldComp (I := I) (M := M) g 0 ((b₀ + w) + (k + 1)) ((s₀ + w) + (p + 1))
              (dropTowerPsi (I := I) (M := M) g b₀ s₀ C (p + 1) w (k + 1))
              (iteratedCovGrad g 0 (b₀ + w) (k + 1) W)) =
          (∑ k ∈ Finset.range (p + 1),
            ccOperatorFieldComp (I := I) (M := M) g 0 ((b₀ + w) + (k + 1)) ((s₀ + w) + (p + 1))
              (if k + 1 < p + 1 then
                  covGrad (I := I) (M := M) g ((b₀ + w) + (k + 1)) ((s₀ + w) + p)
                    (dropTowerPsi (I := I) (M := M) g b₀ s₀ C p w (k + 1))
                else 0)
              (iteratedCovGrad g 0 (b₀ + w) (k + 1) W)) +
          ((∑ k ∈ Finset.range (p + 1),
            ccOperatorFieldComp (I := I) (M := M) g 0 ((b₀ + w) + (k + 1)) ((s₀ + w) + (p + 1))
              (slotExtend (I := I) (M := M) g ((b₀ + w) + k) ((s₀ + w) + p)
                (dropTowerPsi (I := I) (M := M) g b₀ s₀ C p w k))
              (iteratedCovGrad g 0 (b₀ + w) (k + 1) W)) -
          (∑ k ∈ Finset.range (p + 1),
            ccOperatorFieldComp (I := I) (M := M) g 0 ((b₀ + w) + (k + 1)) ((s₀ + w) + (p + 1))
              (castCcTensorSourceRank g ((s₀ + w) + (p + 1)) (by omega : (b₀ + (w + 1)) + k = (b₀ + w) + (k + 1))
                (castCcTensorRank g ((b₀ + (w + 1)) + k)
                  (by omega : (s₀ + (w + 1)) + p = (s₀ + w) + (p + 1))
                  (dropTowerPsi (I := I) (M := M) g b₀ s₀ C p (w + 1) k)))
              (iteratedCovGrad g 0 (b₀ + w) (k + 1) W))) := by
        rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [hPsiSucc k, appCcRS_add_left, appCcRS_sub_left]
      rw [hsplit]
      rw [show (∑ k ∈ Finset.range (p + 1),
            ccOperatorFieldComp (I := I) (M := M) g 0 ((b₀ + w) + (k + 1)) ((s₀ + w) + (p + 1))
              (if k + 1 < p + 1 then
                  covGrad (I := I) (M := M) g ((b₀ + w) + (k + 1)) ((s₀ + w) + p)
                    (dropTowerPsi (I := I) (M := M) g b₀ s₀ C p w (k + 1))
                else 0)
              (iteratedCovGrad g 0 (b₀ + w) (k + 1) W)) =
          ∑ k ∈ Finset.range p,
            ccOperatorFieldComp (I := I) (M := M) g 0 ((b₀ + w) + (k + 1)) ((s₀ + w) + (p + 1))
              (covGrad (I := I) (M := M) g ((b₀ + w) + (k + 1)) ((s₀ + w) + p)
                (dropTowerPsi (I := I) (M := M) g b₀ s₀ C p w (k + 1)))
              (iteratedCovGrad g 0 (b₀ + w) (k + 1) W) from by
        rw [Finset.sum_range_succ]
        rw [if_neg (by omega : ¬ (p + 1 < p + 1)), appCcRS_zero_left, add_zero]
        refine Finset.sum_congr rfl (fun k hk => ?_)
        rw [if_pos (by simp only [Finset.mem_range] at hk; omega : k + 1 < p + 1)]]
      rw [Finset.sum_range_succ' (fun k =>
        ccOperatorFieldComp (I := I) (M := M) g 0 ((b₀ + w) + k) ((s₀ + w) + (p + 1))
          (covGrad (I := I) (M := M) g ((b₀ + w) + k) ((s₀ + w) + p)
            (dropTowerPsi (I := I) (M := M) g b₀ s₀ C p w k))
          (iteratedCovGrad g 0 (b₀ + w) k W)) p]
      abel

def dropFibreSup (g : SmoothRiemannianMetric I M) (b₀ s₀ : ℕ)
    (C : SmoothCcTensor g b₀ s₀) (p w k : ℕ) : ℝ :=
  ⨆ x : M, riemannianFiberNormSq (I := I) (M := M) g ((b₀ + w) + k) ((s₀ + w) + p) x
    ((dropTowerPsi (I := I) (M := M) g b₀ s₀ C p w k).toSection x)

omit [BoundarylessManifold I M] [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem dropFibreSup_bddAbove (g : SmoothRiemannianMetric I M) (b₀ s₀ : ℕ)
    (C : SmoothCcTensor g b₀ s₀) (p w k : ℕ) :
    BddAbove (Set.range fun x : M =>
      riemannianFiberNormSq (I := I) (M := M) g ((b₀ + w) + k) ((s₀ + w) + p) x
        ((dropTowerPsi (I := I) (M := M) g b₀ s₀ C p w k).toSection x)) := by
  obtain ⟨K, _, hK⟩ := exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g
    ((b₀ + w) + k) ((s₀ + w) + p) (dropTowerPsi (I := I) (M := M) g b₀ s₀ C p w k)
  exact ⟨K, by rintro _ ⟨x, rfl⟩; exact hK x⟩

omit [BoundarylessManifold I M] [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem dropFibreSup_fibre_le (g : SmoothRiemannianMetric I M) (b₀ s₀ : ℕ)
    (C : SmoothCcTensor g b₀ s₀) (p w k : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g ((b₀ + w) + k) ((s₀ + w) + p) x
        ((dropTowerPsi (I := I) (M := M) g b₀ s₀ C p w k).toSection x) ≤
      dropFibreSup (I := I) (M := M) g b₀ s₀ C p w k :=
  le_ciSup (dropFibreSup_bddAbove (I := I) (M := M) g b₀ s₀ C p w k) x

omit [BoundarylessManifold I M] [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem dropFibreSup_nonneg (g : SmoothRiemannianMetric I M) (b₀ s₀ : ℕ)
    (C : SmoothCcTensor g b₀ s₀) (p w k : ℕ) :
    0 ≤ dropFibreSup (I := I) (M := M) g b₀ s₀ C p w k :=
  Real.iSup_nonneg fun x => riemannianFiberNormSq_nonneg (I := I) (M := M) g ((b₀ + w) + k)
    ((s₀ + w) + p) x ((dropTowerPsi (I := I) (M := M) g b₀ s₀ C p w k).toSection x)

omit [BoundarylessManifold I M] [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem dropFibreSup_le_of_fibreNormSup (g : SmoothRiemannianMetric I M) (b₀ s₀ : ℕ)
    (C : SmoothCcTensor g b₀ s₀) (p w k : ℕ) {K : ℝ} (hK_nonneg : 0 ≤ K)
    (hK : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g ((b₀ + w) + k) ((s₀ + w) + p) x
      ((dropTowerPsi (I := I) (M := M) g b₀ s₀ C p w k).toSection x) ≤ K) :
    dropFibreSup (I := I) (M := M) g b₀ s₀ C p w k ≤ K :=
  Real.iSup_le hK hK_nonneg

omit [BoundarylessManifold I M] [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem dropFibreSup_spec (g : SmoothRiemannianMetric I M) (b₀ s₀ : ℕ)
    (C : SmoothCcTensor g b₀ s₀) (p w k : ℕ)
    (W : SmoothCcTensor g 0 ((b₀ + w) + k)) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 0 ((s₀ + w) + p) x
        ((ccOperatorFieldComp (I := I) (M := M) g 0 ((b₀ + w) + k) ((s₀ + w) + p)
          (dropTowerPsi (I := I) (M := M) g b₀ s₀ C p w k) W).toSection x) ≤
      dropFibreSup (I := I) (M := M) g b₀ s₀ C p w k *
        riemannianFiberNormSq (I := I) (M := M) g 0 ((b₀ + w) + k) x (W.toSection x) := by
  rw [appCcRS_toSection (I := I) (M := M) g 0 ((b₀ + w) + k) ((s₀ + w) + p)
    (dropTowerPsi (I := I) (M := M) g b₀ s₀ C p w k) W x]
  refine le_trans (riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g 0 ((b₀ + w) + k)
    ((s₀ + w) + p) x ((dropTowerPsi (I := I) (M := M) g b₀ s₀ C p w k).toSection x)
    (W.toSection x)) ?_
  exact mul_le_mul_of_nonneg_right (dropFibreSup_fibre_le (I := I) (M := M) g b₀ s₀ C p w k x)
    (riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 ((b₀ + w) + k) x (W.toSection x))

def dropKappa (g : SmoothRiemannianMetric I M) (b₀ s₀ : ℕ) (C : SmoothCcTensor g b₀ s₀) :
    ℕ → ℕ → ℝ :=
  fun p w => (p + 1 : ℝ) * ∑ k ∈ Finset.range (p + 1), dropFibreSup (I := I) (M := M) g b₀ s₀ C p w k

omit [BoundarylessManifold I M] [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem dropKappa_eq_explicit (g : SmoothRiemannianMetric I M) (b₀ s₀ : ℕ)
    (C : SmoothCcTensor g b₀ s₀) (p w : ℕ) :
    dropKappa (I := I) (M := M) g b₀ s₀ C p w =
      (p + 1 : ℝ) * ∑ k ∈ Finset.range (p + 1), dropFibreSup (I := I) (M := M) g b₀ s₀ C p w k :=
  rfl

omit [BoundarylessManifold I M] [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem dropKappa_nonneg (g : SmoothRiemannianMetric I M) (b₀ s₀ : ℕ)
    (C : SmoothCcTensor g b₀ s₀) (p w : ℕ) :
    0 ≤ dropKappa (I := I) (M := M) g b₀ s₀ C p w :=
  mul_nonneg (by positivity)
    (Finset.sum_nonneg fun k _ => dropFibreSup_nonneg (I := I) (M := M) g b₀ s₀ C p w k)

omit [BoundarylessManifold I M] [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem dropKappa_le_of_fibreNormSup (g : SmoothRiemannianMetric I M) (b₀ s₀ : ℕ)
    (C : SmoothCcTensor g b₀ s₀) (p w : ℕ) (S : ℕ → ℕ → ℕ → ℝ)
    (hS : ∀ k ∈ Finset.range (p + 1), dropFibreSup (I := I) (M := M) g b₀ s₀ C p w k ≤ S p w k) :
    dropKappa (I := I) (M := M) g b₀ s₀ C p w ≤
      (p + 1 : ℝ) * ∑ k ∈ Finset.range (p + 1), S p w k := by
  rw [dropKappa_eq_explicit]
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum hS) (by positivity)

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem dropTower_rfns_op_le (g : SmoothRiemannianMetric I M) (b₀ s₀ : ℕ)
    (C : SmoothCcTensor g b₀ s₀) (p w : ℕ) (W : SmoothCcTensor g 0 (b₀ + w)) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 0 ((s₀ + w) + p) x
        ((appCcLeibnizTower (I := I) (M := M) g b₀ s₀ C p w W).toSection x) ≤
      dropKappa (I := I) (M := M) g b₀ s₀ C p w * ∑ q ∈ Finset.range (p + 1),
        riemannianFiberNormSq (I := I) (M := M) g 0 ((b₀ + w) + q) x
          ((iteratedCovGrad g 0 (b₀ + w) q W).toSection x) := by
  set Ck : ℕ → ℝ := fun k => dropFibreSup (I := I) (M := M) g b₀ s₀ C p w k with hCk_def
  have hCk_nn : ∀ k, 0 ≤ Ck k := fun k => dropFibreSup_nonneg (I := I) (M := M) g b₀ s₀ C p w k
  set a : ℕ → ℝ := fun k => riemannianFiberNormSq (I := I) (M := M) g 0 ((b₀ + w) + k) x
    ((iteratedCovGrad g 0 (b₀ + w) k W).toSection x) with ha_def
  have ha_nn : ∀ k, 0 ≤ a k := fun k =>
    riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 ((b₀ + w) + k) x _
  rw [dropKappa_eq_explicit, dropTowerPsi_spec (I := I) (M := M) g b₀ s₀ C p w W,
    SmoothCcTensor.toSection_sum_apply]
  refine le_trans (riemannianFiberNormSq_sum_le_card_mul (I := I) (M := M) g 0 ((s₀ + w) + p) x
    (Finset.range (p + 1))
    (fun k => (ccOperatorFieldComp (I := I) (M := M) g 0 ((b₀ + w) + k) ((s₀ + w) + p)
      (dropTowerPsi (I := I) (M := M) g b₀ s₀ C p w k)
      (iteratedCovGrad g 0 (b₀ + w) k W)).toSection x)) ?_
  rw [Finset.card_range]
  have hsummand : ∀ k ∈ Finset.range (p + 1),
      riemannianFiberNormSq (I := I) (M := M) g 0 ((s₀ + w) + p) x
          ((ccOperatorFieldComp (I := I) (M := M) g 0 ((b₀ + w) + k) ((s₀ + w) + p)
            (dropTowerPsi (I := I) (M := M) g b₀ s₀ C p w k)
            (iteratedCovGrad g 0 (b₀ + w) k W)).toSection x) ≤ Ck k * a k := fun k _ =>
    dropFibreSup_spec (I := I) (M := M) g b₀ s₀ C p w k _ x
  refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hsummand) (by positivity)) ?_
  have hCa_le : (∑ k ∈ Finset.range (p + 1), Ck k * a k) ≤
      (∑ k ∈ Finset.range (p + 1), Ck k) * ∑ k ∈ Finset.range (p + 1), a k := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun k _ => ?_)
    refine mul_le_mul_of_nonneg_left ?_ (hCk_nn k)
    exact Finset.single_le_sum (f := a) (fun j _ => ha_nn j) ‹k ∈ Finset.range (p + 1)›
  rw [show ((p + 1 : ℕ) : ℝ) = (p : ℝ) + 1 from by push_cast; ring]
  calc (p + 1 : ℝ) * ∑ k ∈ Finset.range (p + 1), Ck k * a k
      ≤ (p + 1 : ℝ) * ((∑ k ∈ Finset.range (p + 1), Ck k) * ∑ k ∈ Finset.range (p + 1), a k) :=
        mul_le_mul_of_nonneg_left hCa_le (by positivity)
    _ = (p + 1 : ℝ) * (∑ k ∈ Finset.range (p + 1), Ck k) * ∑ k ∈ Finset.range (p + 1), a k := by ring

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem exists_dropTower_jet_bound (g : SmoothRiemannianMetric I M) (b₀ s₀ : ℕ)
    (C : SmoothCcTensor g b₀ s₀) (p w : ℕ) :
    ∃ kappa : ℝ, 0 ≤ kappa ∧
      ∀ (W : SmoothCcTensor g 0 (b₀ + w)) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g 0 ((s₀ + w) + p) x
            ((appCcLeibnizTower (I := I) (M := M) g b₀ s₀ C p w W).toSection x) ≤
          kappa * ∑ q ∈ Finset.range (p + 1),
            riemannianFiberNormSq (I := I) (M := M) g 0 ((b₀ + w) + q) x
              ((iteratedCovGrad g 0 (b₀ + w) q W).toSection x) :=
  ⟨dropKappa (I := I) (M := M) g b₀ s₀ C p w, dropKappa_nonneg (I := I) (M := M) g b₀ s₀ C p w,
    fun W x => dropTower_rfns_op_le (I := I) (M := M) g b₀ s₀ C p w W x⟩

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem dropTower_rfns_iteratedCovGrad_grid (g : SmoothRiemannianMetric I M) (b₀ s₀ : ℕ)
    (C : SmoothCcTensor g b₀ s₀) (j : ℕ) :
    ∀ (p w : ℕ) (W : SmoothCcTensor g 0 (b₀ + w)) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g 0 (((s₀ + w) + p) + j) x
          ((iteratedCovGrad g 0 ((s₀ + w) + p) j
            (appCcLeibnizTower (I := I) (M := M) g b₀ s₀ C p w W)).toSection x) ≤
        (4 : ℝ) ^ j * gridWindowSum (dropKappa (I := I) (M := M) g b₀ s₀ C) p w j *
          ∑ q ∈ Finset.range (p + j + 1),
            riemannianFiberNormSq (I := I) (M := M) g 0 ((b₀ + w) + q) x
              ((iteratedCovGrad g 0 (b₀ + w) q W).toSection x) := by
  induction j with
  | zero =>
      intro p w W x
      have hrhs : (4 : ℝ) ^ 0 * gridWindowSum (dropKappa (I := I) (M := M) g b₀ s₀ C) p w 0 *
            ∑ q ∈ Finset.range (p + 0 + 1),
              riemannianFiberNormSq (I := I) (M := M) g 0 ((b₀ + w) + q) x
                ((iteratedCovGrad g 0 (b₀ + w) q W).toSection x) =
          dropKappa (I := I) (M := M) g b₀ s₀ C p w * ∑ q ∈ Finset.range (p + 1),
              riemannianFiberNormSq (I := I) (M := M) g 0 ((b₀ + w) + q) x
                ((iteratedCovGrad g 0 (b₀ + w) q W).toSection x) := by
        rw [pow_zero, one_mul, gridWindowSum_zero, Nat.add_zero]
      rw [iteratedCovGrad_zero, hrhs]
      exact dropTower_rfns_op_le (I := I) (M := M) g b₀ s₀ C p w W x
  | succ j ih =>
      intro p w W x
      set K : ℝ := gridWindowSum (dropKappa (I := I) (M := M) g b₀ s₀ C) p w (j + 1) with hK_def
      set S : ℝ := ∑ q ∈ Finset.range (p + (j + 1) + 1),
        riemannianFiberNormSq (I := I) (M := M) g 0 ((b₀ + w) + q) x
          ((iteratedCovGrad g 0 (b₀ + w) q W).toSection x) with hS_def
      have hK_nn : 0 ≤ K :=
        gridWindowSum_nonneg (dropKappa_nonneg (I := I) (M := M) g b₀ s₀ C) p w (j + 1)
      have hS_nn : 0 ≤ S := Finset.sum_nonneg fun q _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 ((b₀ + w) + q) x _
      have hpow_nn : (0 : ℝ) ≤ (4 : ℝ) ^ j := by positivity
      rw [show riemannianFiberNormSq (I := I) (M := M) g 0 (((s₀ + w) + p) + (j + 1)) x
            ((iteratedCovGrad g 0 ((s₀ + w) + p) (j + 1)
              (appCcLeibnizTower (I := I) (M := M) g b₀ s₀ C p w W)).toSection x) =
          riemannianFiberNormSq (I := I) (M := M) g 0 ((((s₀ + w) + p) + 1) + j) x
            ((iteratedCovGrad g 0 (((s₀ + w) + p) + 1) j
              (covGrad g 0 ((s₀ + w) + p)
                (appCcLeibnizTower (I := I) (M := M) g b₀ s₀ C p w W))).toSection x) from
        (rfns_iteratedCovGrad_covGrad_comm_drop g ((s₀ + w) + p) j
          (appCcLeibnizTower (I := I) (M := M) g b₀ s₀ C p w W) x).symm]
      rw [DropTower_covGrad_op (I := I) (M := M) g b₀ s₀ C p w W, iteratedCovGrad_add]
      refine (riemannianFiberNormSq_add_le (I := I) (M := M) g 0 ((((s₀ + w) + p) + 1) + j) x
          ((iteratedCovGrad g 0 (((s₀ + w) + p) + 1) j
            (appCcLeibnizTower (I := I) (M := M) g b₀ s₀ C (p + 1) w W)).toSection x)
          ((iteratedCovGrad g 0 (((s₀ + w) + p) + 1) j
            (castCcTensorRank g 0 (by omega : (s₀ + (w + 1)) + p = (s₀ + w) + (p + 1))
              (appCcLeibnizTower (I := I) (M := M) g b₀ s₀ C p (w + 1)
                (covGrad g 0 (b₀ + w) W)))).toSection x)).trans ?_
      set kA : ℝ := gridWindowSum (dropKappa (I := I) (M := M) g b₀ s₀ C) (p + 1) w j with hkA_def
      set kB : ℝ := gridWindowSum (dropKappa (I := I) (M := M) g b₀ s₀ C) p (w + 1) j with hkB_def
      set sA : ℝ := ∑ q ∈ Finset.range ((p + 1) + j + 1),
        riemannianFiberNormSq (I := I) (M := M) g 0 ((b₀ + w) + q) x
          ((iteratedCovGrad g 0 (b₀ + w) q W).toSection x) with hsA_def
      set sB : ℝ := ∑ q ∈ Finset.range (p + j + 1),
        riemannianFiberNormSq (I := I) (M := M) g 0 ((b₀ + w) + (q + 1)) x
          ((iteratedCovGrad g 0 (b₀ + w) (q + 1) W).toSection x) with hsB_def
      have hA : riemannianFiberNormSq (I := I) (M := M) g 0 (((s₀ + w) + (p + 1)) + j) x
            ((iteratedCovGrad g 0 ((s₀ + w) + (p + 1)) j
              (appCcLeibnizTower (I := I) (M := M) g b₀ s₀ C (p + 1) w W)).toSection x) ≤
          (4 : ℝ) ^ j * (kA * sA) := by
        refine (ih (p + 1) w W x).trans_eq ?_
        rw [hkA_def, hsA_def, mul_assoc]
      have hB0 := ih p (w + 1) (covGrad g 0 (b₀ + w) W) x
      have hBshift : gridWindowSum (dropKappa (I := I) (M := M) g b₀ s₀ C) p (w + 1) j *
            ∑ q ∈ Finset.range (p + j + 1),
              riemannianFiberNormSq (I := I) (M := M) g 0 ((b₀ + (w + 1)) + q) x
                ((iteratedCovGrad g 0 (b₀ + (w + 1)) q (covGrad g 0 (b₀ + w) W)).toSection x) =
          kB * sB := by
        rw [hkB_def, hsB_def]
        congr 1
        exact Finset.sum_congr rfl fun q _ =>
          rfns_iteratedCovGrad_covGrad_comm_drop g (b₀ + w) q W x
      have hB : riemannianFiberNormSq (I := I) (M := M) g 0 (((s₀ + (w + 1)) + p) + j) x
            ((iteratedCovGrad g 0 ((s₀ + (w + 1)) + p) j
              (appCcLeibnizTower (I := I) (M := M) g b₀ s₀ C p (w + 1)
                (covGrad g 0 (b₀ + w) W))).toSection x) ≤
          (4 : ℝ) ^ j * (kB * sB) := by
        refine hB0.trans_eq ?_
        rw [mul_assoc, ← hBshift]
      have hkA_le : kA ≤ K := by
        rw [hkA_def, hK_def]
        exact gridWindowSum_shift_le (dropKappa_nonneg (I := I) (M := M) g b₀ s₀ C)
          p w j 1 0 le_rfl (Nat.zero_le _)
      have hkB_le : kB ≤ K := by
        rw [hkB_def, hK_def]
        exact gridWindowSum_shift_le (dropKappa_nonneg (I := I) (M := M) g b₀ s₀ C)
          p w j 0 1 (Nat.zero_le _) le_rfl
      have hsA_le : sA ≤ S := by
        rw [hsA_def, hS_def]
        exact le_of_eq (Finset.sum_congr (by rw [show (p + 1) + j + 1 = p + (j + 1) + 1 from by omega])
          (fun _ _ => rfl))
      have hsB_le : sB ≤ S := by
        rw [hsB_def, hS_def]
        refine le_trans (sum_range_shift_le_drop (p + j + 1)
          (fun q => riemannianFiberNormSq (I := I) (M := M) g 0 ((b₀ + w) + q) x
            ((iteratedCovGrad g 0 (b₀ + w) q W).toSection x))
          (fun q => riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 ((b₀ + w) + q) x _)) ?_
        exact le_of_eq (Finset.sum_congr (by rw [show (p + j + 1) + 1 = p + (j + 1) + 1 from by omega])
          (fun _ _ => rfl))
      have hkA_nn : 0 ≤ kA :=
        gridWindowSum_nonneg (dropKappa_nonneg (I := I) (M := M) g b₀ s₀ C) (p + 1) w j
      have hkB_nn : 0 ≤ kB :=
        gridWindowSum_nonneg (dropKappa_nonneg (I := I) (M := M) g b₀ s₀ C) p (w + 1) j
      have hsA_nn : 0 ≤ sA :=
        Finset.sum_nonneg fun q _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 ((b₀ + w) + q) x _
      have hsB_nn : 0 ≤ sB :=
        Finset.sum_nonneg fun q _ =>
          riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 ((b₀ + w) + (q + 1)) x _
      have hprodA : kA * sA ≤ K * S := mul_le_mul hkA_le hsA_le hsA_nn hK_nn
      have hprodB : kB * sB ≤ K * S := mul_le_mul hkB_le hsB_le hsB_nn hK_nn
      have hgoal : (2 : ℝ) * ((4 : ℝ) ^ j * (kA * sA)) +
            (2 : ℝ) * ((4 : ℝ) ^ j * (kB * sB)) ≤
          (4 : ℝ) ^ (j + 1) * (K * S) := by
        have h4 : (4 : ℝ) ^ (j + 1) = 4 * (4 : ℝ) ^ j := by rw [pow_succ]; ring
        rw [h4]
        nlinarith [hprodA, hprodB, hpow_nn,
          mul_le_mul_of_nonneg_left hprodA hpow_nn,
          mul_le_mul_of_nonneg_left hprodB hpow_nn]
      have htarget : (4 : ℝ) ^ (j + 1) * (K * S) =
          (4 : ℝ) ^ (j + 1) * gridWindowSum (dropKappa (I := I) (M := M) g b₀ s₀ C) p w (j + 1) *
            ∑ q ∈ Finset.range (p + (j + 1) + 1),
              riemannianFiberNormSq (I := I) (M := M) g 0 ((b₀ + w) + q) x
                ((iteratedCovGrad g 0 (b₀ + w) q W).toSection x) := by
        rw [hK_def, hS_def, mul_assoc]
      rw [htarget] at hgoal
      refine le_trans ?_ hgoal
      have hb_eq : riemannianFiberNormSq (I := I) (M := M) g 0 ((((s₀ + w) + p) + 1) + j) x
            ((iteratedCovGrad g 0 (((s₀ + w) + p) + 1) j
              (castCcTensorRank g 0 (by omega : (s₀ + (w + 1)) + p = (s₀ + w) + (p + 1))
                (appCcLeibnizTower (I := I) (M := M) g b₀ s₀ C p (w + 1)
                  (covGrad g 0 (b₀ + w) W)))).toSection x) =
          riemannianFiberNormSq (I := I) (M := M) g 0 (((s₀ + (w + 1)) + p) + j) x
            ((iteratedCovGrad g 0 ((s₀ + (w + 1)) + p) j
              (appCcLeibnizTower (I := I) (M := M) g b₀ s₀ C p (w + 1)
                (covGrad g 0 (b₀ + w) W))).toSection x) :=
        riemannianFiberNormSq_iteratedCovGrad_castCcTensorRank g 0 (by omega : (s₀ + (w + 1)) + p = (s₀ + w) + (p + 1))
          (appCcLeibnizTower (I := I) (M := M) g b₀ s₀ C p (w + 1) (covGrad g 0 (b₀ + w) W)) j x
      rw [hb_eq]
      exact add_le_add (mul_le_mul_of_nonneg_left hA (by norm_num))
        (mul_le_mul_of_nonneg_left hB (by norm_num))

omit [BoundarylessManifold I M] [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem dropTowerOp_zero_eq_appCc (g : SmoothRiemannianMetric I M) (b₀ s₀ : ℕ)
    (C : SmoothCcTensor g b₀ s₀) (W : SmoothCcTensor g 0 b₀) :
    appCcLeibnizTower (I := I) (M := M) g b₀ s₀ C 0 0 W = operatorFieldApply (I := I) (M := M) g b₀ s₀ C W := by
  change ccOperatorFieldComp (I := I) (M := M) g 0 (b₀ + 0) (s₀ + 0)
      (slotExtendIter (I := I) (M := M) g b₀ s₀ 0 C) W = _
  simp only [slotExtendIter, Nat.add_zero]
  rw [appCcRS_zero_eq_appCc (I := I) (M := M) g b₀ s₀ C W]

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem appCc_iteratedCovGrad_drop_singleSum_le_explicit (g : SmoothRiemannianMetric I M) (b₀ s₀ : ℕ)
    (C : SmoothCcTensor g b₀ s₀) (W : SmoothCcTensor g 0 b₀) (j : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 0 (s₀ + j) x
        ((iteratedCovGrad g 0 s₀ j (operatorFieldApply (I := I) (M := M) g b₀ s₀ C W)).toSection x) ≤
      ((4 : ℝ) ^ j * gridWindowSum (dropKappa (I := I) (M := M) g b₀ s₀ C) 0 0 j) *
        ∑ q ∈ Finset.range (j + 1),
          riemannianFiberNormSq (I := I) (M := M) g 0 (b₀ + q) x
            ((iteratedCovGrad g 0 b₀ q W).toSection x) := by
  have hgrid := dropTower_rfns_iteratedCovGrad_grid (I := I) (M := M) g b₀ s₀ C j 0 0 W x
  rw [dropTowerOp_zero_eq_appCc (I := I) (M := M) g b₀ s₀ C W] at hgrid
  simpa only [Nat.add_zero, Nat.zero_add, mul_assoc] using hgrid

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem appCc_iteratedCovGrad_drop_singleSum_le (g : SmoothRiemannianMetric I M) (b₀ s₀ : ℕ)
    (C : SmoothCcTensor g b₀ s₀) :
    ∃ K : ℕ → ℝ, (∀ j, 0 ≤ K j) ∧
      ∀ (W : SmoothCcTensor g 0 b₀) (j : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g 0 (s₀ + j) x
            ((iteratedCovGrad g 0 s₀ j (operatorFieldApply (I := I) (M := M) g b₀ s₀ C W)).toSection x) ≤
          K j * ∑ q ∈ Finset.range (j + 1),
            riemannianFiberNormSq (I := I) (M := M) g 0 (b₀ + q) x
              ((iteratedCovGrad g 0 b₀ q W).toSection x) :=
  ⟨fun j => (4 : ℝ) ^ j * gridWindowSum (dropKappa (I := I) (M := M) g b₀ s₀ C) 0 0 j,
    fun j => mul_nonneg (by positivity)
      (gridWindowSum_nonneg (dropKappa_nonneg (I := I) (M := M) g b₀ s₀ C) 0 0 j),
    fun W j x => appCc_iteratedCovGrad_drop_singleSum_le_explicit (I := I) (M := M) g b₀ s₀ C W j x⟩

end Connection
end Integral
end DifferentialGeometry

end
