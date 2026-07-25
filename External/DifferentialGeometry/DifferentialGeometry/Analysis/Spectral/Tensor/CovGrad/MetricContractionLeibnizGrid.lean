import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradLinear
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.FiberNormSubadditivity


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

section RankCast


omit [BoundarylessManifold I M] [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem covGrad_heq_congr_db (g : SmoothRiemannianMetric I M) (r : ℕ) {a b : ℕ}
    (h : a = b) {Y : SmoothCcTensor g r a} {Z : SmoothCcTensor g r b} (hYZ : HEq Y Z) :
    HEq (covGrad g r a Y) (covGrad g r b Z) := by
  subst h; rw [eq_of_heq hYZ]

omit [BoundarylessManifold I M] [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem iteratedCovGrad_covGrad_comm_heq_db (g : SmoothRiemannianMetric I M) (r s m : ℕ)
    (X : SmoothCcTensor g r s) :
    HEq (iteratedCovGrad g r (s + 1) m (covGrad g r s X))
      (iteratedCovGrad g r s (m + 1) X) := by
  induction m with
  | zero => rw [iteratedCovGrad_zero, iteratedCovGrad_succ, iteratedCovGrad_zero]; exact HEq.rfl
  | succ k ih =>
      rw [iteratedCovGrad_succ (g := g) (r := r) (s := s + 1) (j := k) (covGrad g r s X)]
      rw [iteratedCovGrad_succ (g := g) (r := r) (s := s) (j := k + 1) X]
      exact covGrad_heq_congr_db g r (by omega : (s + 1) + k = s + (k + 1)) ih


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] [CompleteSpace E] in
private theorem riemannianFiberNormSq_toSection_heq_congr (g : SmoothRiemannianMetric I M)
    (r : ℕ) {a b : ℕ} (h : a = b) {Y : SmoothCcTensor g r a} {Z : SmoothCcTensor g r b}
    (hYZ : HEq Y Z) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r a x (Y.toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g r b x (Z.toSection x) := by
  subst h; rw [eq_of_heq hYZ]

omit [BoundarylessManifold I M] [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem rfns_iteratedCovGrad_covGrad_comm_db (g : SmoothRiemannianMetric I M)
    (r s m : ℕ) (W : SmoothCcTensor g r s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r ((s + 1) + m) x
        ((iteratedCovGrad g r (s + 1) m (covGrad g r s W)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g r (s + (m + 1)) x
        ((iteratedCovGrad g r s (m + 1) W).toSection x) :=
  riemannianFiberNormSq_toSection_heq_congr g r (by omega : (s + 1) + m = s + (m + 1))
    (iteratedCovGrad_covGrad_comm_heq_db g r s m W) x

def castCcTensorRank (g : SmoothRiemannianMetric I M) (r : ℕ) {a b : ℕ} (h : a = b)
    (W : SmoothCcTensor g r a) : SmoothCcTensor g r b :=
  h ▸ W


omit [BoundarylessManifold I M] [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem riemannianFiberNormSq_iteratedCovGrad_castCcTensorRank (g : SmoothRiemannianMetric I M) (r : ℕ)
    {a b : ℕ} (h : a = b) (W : SmoothCcTensor g r a) (j : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r (b + j) x
        ((iteratedCovGrad g r b j (castCcTensorRank g r h W)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g r (a + j) x
        ((iteratedCovGrad g r a j W).toSection x) := by
  subst h; rfl

private lemma sum_range_shift_le_db (n : ℕ) (f : ℕ → ℝ) (hf : ∀ i, 0 ≤ f i) :
    ∑ i ∈ Finset.range n, f (i + 1) ≤ ∑ i ∈ Finset.range (n + 1), f i := by
  rw [Finset.sum_range_succ' f n]
  exact le_add_of_nonneg_right (hf 0)

private lemma sum_range_le_succ_of_nonneg_db (n : ℕ) (f : ℕ → ℝ) (hlast : 0 ≤ f n) :
    ∑ i ∈ Finset.range n, f i ≤ ∑ i ∈ Finset.range (n + 1), f i := by
  rw [Finset.sum_range_succ]
  exact le_add_of_nonneg_right hlast

def gridWindowSum (κ : ℕ → ℕ → ℝ) (p r j : ℕ) : ℝ :=
  ∑ p' ∈ Finset.range (j + 1), ∑ r' ∈ Finset.range (j + 1), κ (p + p') (r + r')

theorem gridWindowSum_nonneg {κ : ℕ → ℕ → ℝ} (hκ : ∀ p r, 0 ≤ κ p r) (p r j : ℕ) :
    0 ≤ gridWindowSum κ p r j :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => hκ _ _

theorem gridWindowSum_zero (κ : ℕ → ℕ → ℝ) (p r : ℕ) :
    gridWindowSum κ p r 0 = κ p r := by
  simp [gridWindowSum]

theorem gridWindowSum_shift_le {κ : ℕ → ℕ → ℝ} (hκ : ∀ p r, 0 ≤ κ p r)
    (p r j dp dr : ℕ) (hdp : dp ≤ 1) (hdr : dr ≤ 1) :
    gridWindowSum κ (p + dp) (r + dr) j ≤ gridWindowSum κ p r (j + 1) := by
  classical
  unfold gridWindowSum
  rw [← Finset.sum_product', ← Finset.sum_product']
  set f : ℕ × ℕ → ℝ := fun b => κ (p + b.1) (r + b.2) with hf_def

  have hshift : ∑ b ∈ (Finset.range (j + 1) ×ˢ Finset.range (j + 1)),
        κ ((p + dp) + b.1) ((r + dr) + b.2) =
      ∑ b ∈ ((Finset.range (j + 1) ×ˢ Finset.range (j + 1)).image
        (fun b : ℕ × ℕ => (dp + b.1, dr + b.2))), f b := by
    rw [Finset.sum_image (by
      intro a _ b _ hab
      simp only [Prod.mk.injEq] at hab
      exact Prod.ext (by omega) (by omega))]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    simp only [hf_def]
    congr 1 <;> omega
  rw [hshift]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => hκ _ _)
  intro a ha
  simp only [Finset.mem_image, Finset.mem_product, Finset.mem_range] at ha
  obtain ⟨b, ⟨hb1, hb2⟩, rfl⟩ := ha
  simp only [Finset.mem_product, Finset.mem_range]
  exact ⟨by omega, by omega⟩

end RankCast

structure DiffBilinOp (g : SmoothRiemannianMetric I M) where

  op : ∀ (p r : ℕ), SmoothCcTensor g 0 r → SmoothCcTensor g 0 (r + p)

  covGrad_op : ∀ (p r : ℕ) (W : SmoothCcTensor g 0 r),
    covGrad g 0 (r + p) (op p r W) =
      op (p + 1) r W +
        castCcTensorRank g 0 (by omega : (r + 1) + p = r + (p + 1)) (op p (r + 1) (covGrad g 0 r W))

  kappa : ℕ → ℕ → ℝ

  kappa_nonneg : ∀ p r, 0 ≤ kappa p r

  rfns_op_le : ∀ (p r : ℕ) (W : SmoothCcTensor g 0 r) (x : M),
    riemannianFiberNormSq (I := I) (M := M) g 0 (r + p) x ((op p r W).toSection x) ≤
      kappa p r * ∑ q ∈ Finset.range (p + 1),
        riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x
          ((iteratedCovGrad g 0 r q W).toSection x)

namespace DiffBilinOp

variable {g : SmoothRiemannianMetric I M}

omit [BoundarylessManifold I M] [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem rfns_iteratedCovGrad_grid (Φ : DiffBilinOp g) (j : ℕ) :
    ∀ (p r : ℕ) (W : SmoothCcTensor g 0 r) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g 0 ((r + p) + j) x
          ((iteratedCovGrad g 0 (r + p) j (Φ.op p r W)).toSection x) ≤
        (4 : ℝ) ^ j * gridWindowSum Φ.kappa p r j *
          ∑ q ∈ Finset.range (p + j + 1),
            riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x
              ((iteratedCovGrad g 0 r q W).toSection x) := by
  induction j with
  | zero =>
      intro p r W x
      have hrhs : (4 : ℝ) ^ 0 * gridWindowSum Φ.kappa p r 0 *
            ∑ q ∈ Finset.range (p + 0 + 1),
              riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x
                ((iteratedCovGrad g 0 r q W).toSection x) =
          Φ.kappa p r * ∑ q ∈ Finset.range (p + 1),
              riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x
                ((iteratedCovGrad g 0 r q W).toSection x) := by
        rw [pow_zero, one_mul, gridWindowSum_zero, Nat.add_zero]
      rw [iteratedCovGrad_zero, hrhs]
      exact Φ.rfns_op_le p r W x
  | succ j ih =>
      intro p r W x
      set K : ℝ := gridWindowSum Φ.kappa p r (j + 1) with hK_def
      set S : ℝ := ∑ q ∈ Finset.range (p + (j + 1) + 1),
        riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x
          ((iteratedCovGrad g 0 r q W).toSection x) with hS_def
      have hK_nn : 0 ≤ K := gridWindowSum_nonneg Φ.kappa_nonneg p r (j + 1)
      have hS_nn : 0 ≤ S := Finset.sum_nonneg fun q _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (r + q) x _
      have hpow_nn : (0 : ℝ) ≤ (4 : ℝ) ^ j := by positivity
      rw [show riemannianFiberNormSq (I := I) (M := M) g 0 ((r + p) + (j + 1)) x
            ((iteratedCovGrad g 0 (r + p) (j + 1) (Φ.op p r W)).toSection x) =
          riemannianFiberNormSq (I := I) (M := M) g 0 (((r + p) + 1) + j) x
            ((iteratedCovGrad g 0 ((r + p) + 1) j
              (covGrad g 0 (r + p) (Φ.op p r W))).toSection x) from
        (rfns_iteratedCovGrad_covGrad_comm_db g 0 (r + p) j (Φ.op p r W) x).symm]
      rw [Φ.covGrad_op p r W, iteratedCovGrad_add]
      refine (riemannianFiberNormSq_add_le (I := I) (M := M) g 0 (((r + p) + 1) + j) x
          ((iteratedCovGrad g 0 ((r + p) + 1) j (Φ.op (p + 1) r W)).toSection x)
          ((iteratedCovGrad g 0 ((r + p) + 1) j
            (castCcTensorRank g 0 (by omega : (r + 1) + p = r + (p + 1))
              (Φ.op p (r + 1) (covGrad g 0 r W)))).toSection x)).trans ?_
      set kA : ℝ := gridWindowSum Φ.kappa (p + 1) r j with hkA_def
      set kB : ℝ := gridWindowSum Φ.kappa p (r + 1) j with hkB_def

      set sA : ℝ := ∑ q ∈ Finset.range ((p + 1) + j + 1),
        riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x
          ((iteratedCovGrad g 0 r q W).toSection x) with hsA_def

      set sB : ℝ := ∑ q ∈ Finset.range (p + j + 1),
        riemannianFiberNormSq (I := I) (M := M) g 0 (r + (q + 1)) x
          ((iteratedCovGrad g 0 r (q + 1) W).toSection x) with hsB_def
      have hA : riemannianFiberNormSq (I := I) (M := M) g 0 ((r + (p + 1)) + j) x
            ((iteratedCovGrad g 0 (r + (p + 1)) j (Φ.op (p + 1) r W)).toSection x) ≤
          (4 : ℝ) ^ j * (kA * sA) := by
        refine (ih (p + 1) r W x).trans_eq ?_
        rw [hkA_def, hsA_def, mul_assoc]
      have hB0 := ih p (r + 1) (covGrad g 0 r W) x
      have hBshift : gridWindowSum Φ.kappa p (r + 1) j *
            ∑ q ∈ Finset.range (p + j + 1),
              riemannianFiberNormSq (I := I) (M := M) g 0 ((r + 1) + q) x
                ((iteratedCovGrad g 0 (r + 1) q (covGrad g 0 r W)).toSection x) =
          kB * sB := by
        rw [hkB_def, hsB_def]
        congr 1
        exact Finset.sum_congr rfl fun q _ => rfns_iteratedCovGrad_covGrad_comm_db g 0 r q W x
      have hB : riemannianFiberNormSq (I := I) (M := M) g 0 (((r + 1) + p) + j) x
            ((iteratedCovGrad g 0 ((r + 1) + p) j
              (Φ.op p (r + 1) (covGrad g 0 r W))).toSection x) ≤
          (4 : ℝ) ^ j * (kB * sB) := by
        refine hB0.trans_eq ?_
        rw [mul_assoc, ← hBshift]
      have hkA_le : kA ≤ K := by
        rw [hkA_def, hK_def]
        exact gridWindowSum_shift_le Φ.kappa_nonneg p r j 1 0 le_rfl (Nat.zero_le _)
      have hkB_le : kB ≤ K := by
        rw [hkB_def, hK_def]
        exact gridWindowSum_shift_le Φ.kappa_nonneg p r j 0 1 (Nat.zero_le _) le_rfl

      have hsA_le : sA ≤ S := by
        rw [hsA_def, hS_def]
        exact le_of_eq (Finset.sum_congr (by rw [show (p + 1) + j + 1 = p + (j + 1) + 1 from by omega])
          (fun _ _ => rfl))

      have hsB_le : sB ≤ S := by
        rw [hsB_def, hS_def]
        refine le_trans (sum_range_shift_le_db (p + j + 1)
          (fun q => riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x
            ((iteratedCovGrad g 0 r q W).toSection x))
          (fun q => riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (r + q) x _)) ?_
        exact le_of_eq (Finset.sum_congr (by rw [show (p + j + 1) + 1 = p + (j + 1) + 1 from by omega])
          (fun _ _ => rfl))
      have hkA_nn : 0 ≤ kA := gridWindowSum_nonneg Φ.kappa_nonneg (p + 1) r j
      have hkB_nn : 0 ≤ kB := gridWindowSum_nonneg Φ.kappa_nonneg p (r + 1) j
      have hsA_nn : 0 ≤ sA :=
        Finset.sum_nonneg fun q _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (r + q) x _
      have hsB_nn : 0 ≤ sB :=
        Finset.sum_nonneg fun q _ =>
          riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (r + (q + 1)) x _
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
          (4 : ℝ) ^ (j + 1) * gridWindowSum Φ.kappa p r (j + 1) *
            ∑ q ∈ Finset.range (p + (j + 1) + 1),
              riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x
                ((iteratedCovGrad g 0 r q W).toSection x) := by
        rw [hK_def, hS_def, mul_assoc]
      rw [htarget] at hgoal
      refine le_trans ?_ hgoal
      have hb_eq : riemannianFiberNormSq (I := I) (M := M) g 0 (((r + p) + 1) + j) x
            ((iteratedCovGrad g 0 ((r + p) + 1) j
              (castCcTensorRank g 0 (by omega : (r + 1) + p = r + (p + 1))
                (Φ.op p (r + 1) (covGrad g 0 r W)))).toSection x) =
          riemannianFiberNormSq (I := I) (M := M) g 0 (((r + 1) + p) + j) x
            ((iteratedCovGrad g 0 ((r + 1) + p) j
              (Φ.op p (r + 1) (covGrad g 0 r W))).toSection x) :=
        riemannianFiberNormSq_iteratedCovGrad_castCcTensorRank g 0 (by omega : (r + 1) + p = r + (p + 1))
          (Φ.op p (r + 1) (covGrad g 0 r W)) j x
      rw [hb_eq]
      exact add_le_add (mul_le_mul_of_nonneg_left hA (by norm_num))
        (mul_le_mul_of_nonneg_left hB (by norm_num))

omit [BoundarylessManifold I M] [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem exists_rfns_iteratedCovGrad_singleSum_le (Φ : DiffBilinOp g) :
    ∃ C : ℕ → ℕ → ℝ, (∀ r j, 0 ≤ C r j) ∧
      ∀ (r : ℕ) (W : SmoothCcTensor g 0 r) (j : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g 0 (r + j) x
            ((iteratedCovGrad g 0 r j (Φ.op 0 r W)).toSection x) ≤
          C r j * ∑ q ∈ Finset.range (j + 1),
            riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x
              ((iteratedCovGrad g 0 r q W).toSection x) := by
  refine ⟨fun r j => (4 : ℝ) ^ j * gridWindowSum Φ.kappa 0 r j,
    fun r j => mul_nonneg (by positivity) (gridWindowSum_nonneg Φ.kappa_nonneg 0 r j),
    fun r W j x => ?_⟩
  have hgrid := Φ.rfns_iteratedCovGrad_grid j 0 r W x

  simpa only [Nat.add_zero, Nat.zero_add] using hgrid

omit [BoundarylessManifold I M] [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem rfns_iteratedCovGrad_grid_at
    (op : ∀ (p r : ℕ), SmoothCcTensor g 0 r → SmoothCcTensor g 0 (r + p))
    (hcovGrad_op : ∀ (p r : ℕ) (W : SmoothCcTensor g 0 r),
      covGrad g 0 (r + p) (op p r W) =
        op (p + 1) r W +
          castCcTensorRank g 0 (by omega : (r + 1) + p = r + (p + 1)) (op p (r + 1) (covGrad g 0 r W)))
    (kappa : ℕ → ℕ → ℝ) (kappa_nonneg : ∀ p r, 0 ≤ kappa p r) (x₀ : M)
    (hrfns_at : ∀ (p r : ℕ) (W : SmoothCcTensor g 0 r),
      riemannianFiberNormSq (I := I) (M := M) g 0 (r + p) x₀ ((op p r W).toSection x₀) ≤
        kappa p r * ∑ q ∈ Finset.range (p + 1),
          riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x₀
            ((iteratedCovGrad g 0 r q W).toSection x₀)) (j : ℕ) :
    ∀ (p r : ℕ) (W : SmoothCcTensor g 0 r),
      riemannianFiberNormSq (I := I) (M := M) g 0 ((r + p) + j) x₀
          ((iteratedCovGrad g 0 (r + p) j (op p r W)).toSection x₀) ≤
        (4 : ℝ) ^ j * gridWindowSum kappa p r j *
          ∑ q ∈ Finset.range (p + j + 1),
            riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x₀
              ((iteratedCovGrad g 0 r q W).toSection x₀) := by
  induction j with
  | zero =>
      intro p r W
      have hrhs : (4 : ℝ) ^ 0 * gridWindowSum kappa p r 0 *
            ∑ q ∈ Finset.range (p + 0 + 1),
              riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x₀
                ((iteratedCovGrad g 0 r q W).toSection x₀) =
          kappa p r * ∑ q ∈ Finset.range (p + 1),
              riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x₀
                ((iteratedCovGrad g 0 r q W).toSection x₀) := by
        rw [pow_zero, one_mul, gridWindowSum_zero, Nat.add_zero]
      rw [iteratedCovGrad_zero, hrhs]
      exact hrfns_at p r W
  | succ j ih =>
      intro p r W
      set K : ℝ := gridWindowSum kappa p r (j + 1) with hK_def
      set S : ℝ := ∑ q ∈ Finset.range (p + (j + 1) + 1),
        riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x₀
          ((iteratedCovGrad g 0 r q W).toSection x₀) with hS_def
      have hK_nn : 0 ≤ K := gridWindowSum_nonneg kappa_nonneg p r (j + 1)
      have hS_nn : 0 ≤ S := Finset.sum_nonneg fun q _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (r + q) x₀ _
      have hpow_nn : (0 : ℝ) ≤ (4 : ℝ) ^ j := by positivity
      rw [show riemannianFiberNormSq (I := I) (M := M) g 0 ((r + p) + (j + 1)) x₀
            ((iteratedCovGrad g 0 (r + p) (j + 1) (op p r W)).toSection x₀) =
          riemannianFiberNormSq (I := I) (M := M) g 0 (((r + p) + 1) + j) x₀
            ((iteratedCovGrad g 0 ((r + p) + 1) j
              (covGrad g 0 (r + p) (op p r W))).toSection x₀) from
        (rfns_iteratedCovGrad_covGrad_comm_db g 0 (r + p) j (op p r W) x₀).symm]
      rw [hcovGrad_op p r W, iteratedCovGrad_add]
      refine (riemannianFiberNormSq_add_le (I := I) (M := M) g 0 (((r + p) + 1) + j) x₀
          ((iteratedCovGrad g 0 ((r + p) + 1) j (op (p + 1) r W)).toSection x₀)
          ((iteratedCovGrad g 0 ((r + p) + 1) j
            (castCcTensorRank g 0 (by omega : (r + 1) + p = r + (p + 1))
              (op p (r + 1) (covGrad g 0 r W)))).toSection x₀)).trans ?_
      set kA : ℝ := gridWindowSum kappa (p + 1) r j with hkA_def
      set kB : ℝ := gridWindowSum kappa p (r + 1) j with hkB_def
      set sA : ℝ := ∑ q ∈ Finset.range ((p + 1) + j + 1),
        riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x₀
          ((iteratedCovGrad g 0 r q W).toSection x₀) with hsA_def
      set sB : ℝ := ∑ q ∈ Finset.range (p + j + 1),
        riemannianFiberNormSq (I := I) (M := M) g 0 (r + (q + 1)) x₀
          ((iteratedCovGrad g 0 r (q + 1) W).toSection x₀) with hsB_def
      have hA : riemannianFiberNormSq (I := I) (M := M) g 0 ((r + (p + 1)) + j) x₀
            ((iteratedCovGrad g 0 (r + (p + 1)) j (op (p + 1) r W)).toSection x₀) ≤
          (4 : ℝ) ^ j * (kA * sA) := by
        refine (ih (p + 1) r W).trans_eq ?_
        rw [hkA_def, hsA_def, mul_assoc]
      have hB0 := ih p (r + 1) (covGrad g 0 r W)
      have hBshift : gridWindowSum kappa p (r + 1) j *
            ∑ q ∈ Finset.range (p + j + 1),
              riemannianFiberNormSq (I := I) (M := M) g 0 ((r + 1) + q) x₀
                ((iteratedCovGrad g 0 (r + 1) q (covGrad g 0 r W)).toSection x₀) =
          kB * sB := by
        rw [hkB_def, hsB_def]
        congr 1
        exact Finset.sum_congr rfl fun q _ => rfns_iteratedCovGrad_covGrad_comm_db g 0 r q W x₀
      have hB : riemannianFiberNormSq (I := I) (M := M) g 0 (((r + 1) + p) + j) x₀
            ((iteratedCovGrad g 0 ((r + 1) + p) j
              (op p (r + 1) (covGrad g 0 r W))).toSection x₀) ≤
          (4 : ℝ) ^ j * (kB * sB) := by
        refine hB0.trans_eq ?_
        rw [mul_assoc, ← hBshift]
      have hkA_le : kA ≤ K := by
        rw [hkA_def, hK_def]
        exact gridWindowSum_shift_le kappa_nonneg p r j 1 0 le_rfl (Nat.zero_le _)
      have hkB_le : kB ≤ K := by
        rw [hkB_def, hK_def]
        exact gridWindowSum_shift_le kappa_nonneg p r j 0 1 (Nat.zero_le _) le_rfl
      have hsA_le : sA ≤ S := by
        rw [hsA_def, hS_def]
        exact le_of_eq (Finset.sum_congr (by rw [show (p + 1) + j + 1 = p + (j + 1) + 1 from by omega])
          (fun _ _ => rfl))
      have hsB_le : sB ≤ S := by
        rw [hsB_def, hS_def]
        refine le_trans (sum_range_shift_le_db (p + j + 1)
          (fun q => riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x₀
            ((iteratedCovGrad g 0 r q W).toSection x₀))
          (fun q => riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (r + q) x₀ _)) ?_
        exact le_of_eq (Finset.sum_congr (by rw [show (p + j + 1) + 1 = p + (j + 1) + 1 from by omega])
          (fun _ _ => rfl))
      have hkA_nn : 0 ≤ kA := gridWindowSum_nonneg kappa_nonneg (p + 1) r j
      have hkB_nn : 0 ≤ kB := gridWindowSum_nonneg kappa_nonneg p (r + 1) j
      have hsA_nn : 0 ≤ sA :=
        Finset.sum_nonneg fun q _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (r + q) x₀ _
      have hsB_nn : 0 ≤ sB :=
        Finset.sum_nonneg fun q _ =>
          riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (r + (q + 1)) x₀ _
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
          (4 : ℝ) ^ (j + 1) * gridWindowSum kappa p r (j + 1) *
            ∑ q ∈ Finset.range (p + (j + 1) + 1),
              riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x₀
                ((iteratedCovGrad g 0 r q W).toSection x₀) := by
        rw [hK_def, hS_def, mul_assoc]
      rw [htarget] at hgoal
      refine le_trans ?_ hgoal
      have hb_eq : riemannianFiberNormSq (I := I) (M := M) g 0 (((r + p) + 1) + j) x₀
            ((iteratedCovGrad g 0 ((r + p) + 1) j
              (castCcTensorRank g 0 (by omega : (r + 1) + p = r + (p + 1))
                (op p (r + 1) (covGrad g 0 r W)))).toSection x₀) =
          riemannianFiberNormSq (I := I) (M := M) g 0 (((r + 1) + p) + j) x₀
            ((iteratedCovGrad g 0 ((r + 1) + p) j
              (op p (r + 1) (covGrad g 0 r W))).toSection x₀) :=
        riemannianFiberNormSq_iteratedCovGrad_castCcTensorRank g 0 (by omega : (r + 1) + p = r + (p + 1))
          (op p (r + 1) (covGrad g 0 r W)) j x₀
      rw [hb_eq]
      exact add_le_add (mul_le_mul_of_nonneg_left hA (by norm_num))
        (mul_le_mul_of_nonneg_left hB (by norm_num))

omit [BoundarylessManifold I M] [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem exists_rfns_iteratedCovGrad_singleSum_le_at
    (op : ∀ (p r : ℕ), SmoothCcTensor g 0 r → SmoothCcTensor g 0 (r + p))
    (hcovGrad_op : ∀ (p r : ℕ) (W : SmoothCcTensor g 0 r),
      covGrad g 0 (r + p) (op p r W) =
        op (p + 1) r W +
          castCcTensorRank g 0 (by omega : (r + 1) + p = r + (p + 1)) (op p (r + 1) (covGrad g 0 r W)))
    (kappa : ℕ → ℕ → ℝ) (kappa_nonneg : ∀ p r, 0 ≤ kappa p r) (x₀ : M)
    (hrfns_at : ∀ (p r : ℕ) (W : SmoothCcTensor g 0 r),
      riemannianFiberNormSq (I := I) (M := M) g 0 (r + p) x₀ ((op p r W).toSection x₀) ≤
        kappa p r * ∑ q ∈ Finset.range (p + 1),
          riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x₀
            ((iteratedCovGrad g 0 r q W).toSection x₀)) :
    ∀ (r : ℕ) (W : SmoothCcTensor g 0 r) (j : ℕ),
      riemannianFiberNormSq (I := I) (M := M) g 0 (r + j) x₀
          ((iteratedCovGrad g 0 r j (op 0 r W)).toSection x₀) ≤
        ((4 : ℝ) ^ j * gridWindowSum kappa 0 r j) *
          ∑ q ∈ Finset.range (j + 1),
            riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x₀
              ((iteratedCovGrad g 0 r q W).toSection x₀) := by
  intro r W j
  have hgrid := rfns_iteratedCovGrad_grid_at op hcovGrad_op kappa kappa_nonneg x₀ hrfns_at j 0 r W
  simpa only [Nat.add_zero, Nat.zero_add] using hgrid
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [CompleteSpace E] in
@[simp] theorem norm_castCcTensorRank (g : SmoothRiemannianMetric I M) (r : ℕ)
    {a b : ℕ} (h : a = b) (W : SmoothCcTensor g r a) :
    ‖castCcTensorRank g r h W‖ = ‖W‖ := by
  subst h
  rfl


end DiffBilinOp

end Connection
end Integral
end DifferentialGeometry

end
