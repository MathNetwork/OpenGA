import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.ConnLapPairing
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.AllOrderGardingConstant
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.HomFieldActionL2JetBound









noncomputable section

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]



theorem iterL_jet_le (g : SmoothRiemannianMetric I M) (s a : ℕ) :
    ∃ C : ℕ → ℝ, (∀ p, 0 ≤ C p) ∧ ∀ (p : ℕ) (v : SmoothCcTensor g 0 s),
      ‖iteratedCovGrad (I := I) g 0 s p
          (oneMinusConnLapSmoothIter (I := I) g 0 s a v)‖ ≤
        C p * ∑ q ∈ Finset.range (p + 2 * a + 1),
          ‖iteratedCovGrad (I := I) g 0 s q v‖ := by
  classical
  induction a with
  | zero =>
      refine ⟨fun _ => 1, fun _ => zero_le_one, fun p v => ?_⟩
      rw [oneMinusConnLapSmoothIter_zero, one_mul]
      refine Finset.single_le_sum
        (f := fun q => ‖iteratedCovGrad (I := I) g 0 s q v‖)
        (fun q _ => norm_nonneg _) ?_
      rw [Finset.mem_range]
      omega
  | succ a ih =>
      obtain ⟨C, hC_nn, hC⟩ := ih
      obtain ⟨D, hD_nn, hD⟩ :=
        exists_iteratedCovGrad_rawConnLapIter_l2Norm_le
          (I := I) (M := M) g 1 s
      refine ⟨fun p => C p + D p * ∑ b ∈ Finset.range (p + 3), C b,
        fun p => add_nonneg (hC_nn p)
          (mul_nonneg (hD_nn p) (Finset.sum_nonneg fun b _ => hC_nn b)),
        fun p v => ?_⟩
      set X : SmoothCcTensor g 0 s :=
        oneMinusConnLapSmoothIter (I := I) g 0 s a v with hX
      have hsucc : oneMinusConnLapSmoothIter (I := I) g 0 s (a + 1) v =
          X - rawTensorConnLapSmooth (I := I) g 0 s X := by
        rw [oneMinusConnLapSmoothIter_succ]
        rfl
      rw [hsucc, iteratedCovGrad_sub (I := I) (M := M) g 0 s p]
      refine le_trans (norm_sub_le _ _) ?_
      set J : ℝ := ∑ q ∈ Finset.range (p + 2 * (a + 1) + 1),
        ‖iteratedCovGrad (I := I) g 0 s q v‖ with hJ
      have hmono : ∀ {m : ℕ}, m ≤ p + 2 * (a + 1) + 1 →
          ∑ q ∈ Finset.range m, ‖iteratedCovGrad (I := I) g 0 s q v‖ ≤ J := by
        intro m hm
        rw [hJ]
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_subset_range.mpr hm) (fun q _ _ => norm_nonneg _)
      have hXj : ∀ b ∈ Finset.range (p + 3),
          ‖iteratedCovGrad (I := I) g 0 s b X‖ ≤ C b * J := by
        intro b hb
        rw [Finset.mem_range] at hb
        refine le_trans (hC b v) ?_
        exact mul_le_mul_of_nonneg_left (hmono (by omega)) (hC_nn b)
      have hleft : ‖iteratedCovGrad (I := I) g 0 s p X‖ ≤ C p * J := by
        refine le_trans (hC p v) ?_
        exact mul_le_mul_of_nonneg_left (hmono (by omega)) (hC_nn p)
      have hright :
          ‖iteratedCovGrad (I := I) g 0 s p
              (rawTensorConnLapSmooth (I := I) g 0 s X)‖ ≤
            D p * ((∑ b ∈ Finset.range (p + 3), C b) * J) := by
        have hraw :
            ‖iteratedCovGrad (I := I) g 0 s p
                (rawTensorConnLapSmooth (I := I) g 0 s X)‖ ≤
              D p * ∑ b ∈ Finset.range (p + 3),
                ‖iteratedCovGrad (I := I) g 0 s b X‖ := by
          simpa only [rawTensorConnLapIter_one, show 2 * 1 + p + 1 = p + 3 by omega]
            using hD p X
        refine le_trans hraw ?_
        refine mul_le_mul_of_nonneg_left ?_ (hD_nn p)
        refine le_trans (Finset.sum_le_sum hXj) ?_
        rw [← Finset.sum_mul]
      calc
        ‖iteratedCovGrad (I := I) g 0 s p X‖ +
            ‖iteratedCovGrad (I := I) g 0 s p
              (rawTensorConnLapSmooth (I := I) g 0 s X)‖
            ≤ C p * J + D p * ((∑ b ∈ Finset.range (p + 3), C b) * J) :=
              add_le_add hleft hright
        _ = (C p + D p * ∑ b ∈ Finset.range (p + 3), C b) * J := by ring

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem jetSum_mono (g : SmoothRiemannianMetric I M) (s : ℕ)
    {m n : ℕ} (h : m ≤ n) (v : SmoothCcTensor g 0 s) :
    ∑ q ∈ Finset.range m, ‖iteratedCovGrad (I := I) g 0 s q v‖ ≤
      ∑ q ∈ Finset.range n, ‖iteratedCovGrad (I := I) g 0 s q v‖ :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr h)
    (fun _ _ _ => norm_nonneg _)

private theorem sum_window_le (P w : ℕ) (c A B : ℕ → ℝ)
    (hc : ∀ i, 0 ≤ c i) (hB : ∀ j, 0 ≤ B j)
    (h : ∀ i, i < P → A i ≤ c i * ∑ j ∈ Finset.range (i + w + 1), B j) :
    ∑ i ∈ Finset.range P, A i ≤
      (∑ i ∈ Finset.range P, c i) * ∑ j ∈ Finset.range (P + w), B j := by
  have hterm : ∀ i ∈ Finset.range P,
      A i ≤ c i * ∑ j ∈ Finset.range (P + w), B j := by
    intro i hi
    rw [Finset.mem_range] at hi
    refine le_trans (h i hi) ?_
    refine mul_le_mul_of_nonneg_left ?_ (hc i)
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.mpr (by omega)) (fun j _ _ => hB j)
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.sum_mul]

private theorem iterL_norm_le (g : SmoothRiemannianMetric I M) (s a : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : SmoothCcTensor g 0 s,
      ‖oneMinusConnLapSmoothIter (I := I) g 0 s a v‖ ≤
        C * ∑ q ∈ Finset.range (2 * a + 1),
          ‖iteratedCovGrad (I := I) g 0 s q v‖ := by
  obtain ⟨C, hC_nn, hC⟩ := iterL_jet_le (I := I) (M := M) g s a
  refine ⟨C 0, hC_nn 0, fun v => ?_⟩
  simpa only [Nat.zero_add, iteratedCovGrad_zero] using hC 0 v

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] in
private theorem inner_abs_le (g : SmoothRiemannianMetric I M) (s : ℕ)
    (A B : SmoothCcTensor g 0 s) :
    |tensorL2Inner (I := I) (M := M) g 0 s A.toFun B.toFun| ≤ ‖A‖ * ‖B‖ := by
  rw [← SmoothCcTensor.inner_def (I := I) (M := M) A B]
  exact abs_real_inner_le_norm A B



theorem iterL_pair_le (g : SmoothRiemannianMetric I M)
    (s a r : ℕ) (hr : r ≤ a) (A B : SmoothCcTensor g 0 s) :
    |tensorL2Inner (I := I) (M := M) g 0 s
        (oneMinusConnLapSmoothIter (I := I) g 0 s a A).toFun B.toFun| ≤
      ‖oneMinusConnLapSmoothIter (I := I) g 0 s (a - r) A‖ *
        ‖oneMinusConnLapSmoothIter (I := I) g 0 s r B‖ := by
  have hsplit : oneMinusConnLapSmoothIter (I := I) g 0 s a A =
      oneMinusConnLapSmoothIter (I := I) g 0 s r
        (oneMinusConnLapSmoothIter (I := I) g 0 s (a - r) A) := by
    rw [← oneMinusConnLapSmoothIter_add (I := I) (M := M) g 0 s r (a - r) A]
    congr 1
    omega
  rw [hsplit, oneMinusConnLapSmoothIter_l2Inner_selfAdjoint
    (I := I) (M := M) g 0 s r]
  exact inner_abs_le (I := I) (M := M) g s _ _




theorem iterL_window_pair (g : SmoothRiemannianMetric I M)
    (s₀ σ a r dX dY NA NB : ℕ) (hr : r ≤ a)
    (hNA : 2 * (a - r) + dX ≤ NA) (hNB : 2 * r + dY ≤ NB)
    (cX cY : ℕ → ℝ) (hcX_nn : ∀ p, 0 ≤ cX p) (hcY_nn : ∀ p, 0 ≤ cY p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : SmoothCcTensor g 0 s₀) (X Y : SmoothCcTensor g 0 σ),
      (∀ p, ‖iteratedCovGrad (I := I) g 0 σ p X‖ ≤
        cX p * ∑ j ∈ Finset.range (p + dX + 1),
          ‖iteratedCovGrad (I := I) g 0 s₀ j u‖) →
      (∀ p, ‖iteratedCovGrad (I := I) g 0 σ p Y‖ ≤
        cY p * ∑ j ∈ Finset.range (p + dY + 1),
          ‖iteratedCovGrad (I := I) g 0 s₀ j u‖) →
      |tensorL2Inner (I := I) (M := M) g 0 σ
          (oneMinusConnLapSmoothIter (I := I) g 0 σ a X).toFun Y.toFun| ≤
        C * ((∑ j ∈ Finset.range (NA + 1),
          ‖iteratedCovGrad (I := I) g 0 s₀ j u‖) *
          (∑ j ∈ Finset.range (NB + 1),
            ‖iteratedCovGrad (I := I) g 0 s₀ j u‖)) := by
  classical
  obtain ⟨CL, hCL_nn, hCL⟩ := iterL_norm_le (I := I) (M := M) g σ (a - r)
  obtain ⟨CR, hCR_nn, hCR⟩ := iterL_norm_le (I := I) (M := M) g σ r
  refine ⟨(CL * ∑ p ∈ Finset.range (2 * (a - r) + 1), cX p) *
      (CR * ∑ p ∈ Finset.range (2 * r + 1), cY p),
    mul_nonneg (mul_nonneg hCL_nn (Finset.sum_nonneg fun p _ => hcX_nn p))
      (mul_nonneg hCR_nn (Finset.sum_nonneg fun p _ => hcY_nn p)),
    fun u X Y hX hY => ?_⟩
  have hXb : ‖oneMinusConnLapSmoothIter (I := I) g 0 σ (a - r) X‖ ≤
      (CL * ∑ p ∈ Finset.range (2 * (a - r) + 1), cX p) *
        ∑ j ∈ Finset.range (NA + 1),
          ‖iteratedCovGrad (I := I) g 0 s₀ j u‖ := by
    refine le_trans (hCL X) ?_
    have hsum : ∑ p ∈ Finset.range (2 * (a - r) + 1),
        ‖iteratedCovGrad (I := I) g 0 σ p X‖ ≤
        (∑ p ∈ Finset.range (2 * (a - r) + 1), cX p) *
          ∑ j ∈ Finset.range (2 * (a - r) + 1 + dX),
            ‖iteratedCovGrad (I := I) g 0 s₀ j u‖ :=
      sum_window_le (2 * (a - r) + 1) dX cX
        (fun p => ‖iteratedCovGrad (I := I) g 0 σ p X‖)
        (fun j => ‖iteratedCovGrad (I := I) g 0 s₀ j u‖)
        hcX_nn (fun _ => norm_nonneg _) (fun p _ => hX p)
    refine le_trans (mul_le_mul_of_nonneg_left hsum hCL_nn) ?_
    rw [← mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_
      (mul_nonneg hCL_nn (Finset.sum_nonneg fun p _ => hcX_nn p))
    exact jetSum_mono (I := I) (M := M) g s₀ (by omega) u
  have hYb : ‖oneMinusConnLapSmoothIter (I := I) g 0 σ r Y‖ ≤
      (CR * ∑ p ∈ Finset.range (2 * r + 1), cY p) *
        ∑ j ∈ Finset.range (NB + 1),
          ‖iteratedCovGrad (I := I) g 0 s₀ j u‖ := by
    refine le_trans (hCR Y) ?_
    have hsum : ∑ p ∈ Finset.range (2 * r + 1),
        ‖iteratedCovGrad (I := I) g 0 σ p Y‖ ≤
        (∑ p ∈ Finset.range (2 * r + 1), cY p) *
          ∑ j ∈ Finset.range (2 * r + 1 + dY),
            ‖iteratedCovGrad (I := I) g 0 s₀ j u‖ :=
      sum_window_le (2 * r + 1) dY cY
        (fun p => ‖iteratedCovGrad (I := I) g 0 σ p Y‖)
        (fun j => ‖iteratedCovGrad (I := I) g 0 s₀ j u‖)
        hcY_nn (fun _ => norm_nonneg _) (fun p _ => hY p)
    refine le_trans (mul_le_mul_of_nonneg_left hsum hCR_nn) ?_
    rw [← mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_
      (mul_nonneg hCR_nn (Finset.sum_nonneg fun p _ => hcY_nn p))
    exact jetSum_mono (I := I) (M := M) g s₀ (by omega) u
  refine le_trans (iterL_pair_le (I := I) (M := M) g σ a r hr X Y) ?_
  calc
    ‖oneMinusConnLapSmoothIter (I := I) g 0 σ (a - r) X‖ *
          ‖oneMinusConnLapSmoothIter (I := I) g 0 σ r Y‖
        ≤ ((CL * ∑ p ∈ Finset.range (2 * (a - r) + 1), cX p) *
            ∑ j ∈ Finset.range (NA + 1),
              ‖iteratedCovGrad (I := I) g 0 s₀ j u‖) *
          ((CR * ∑ p ∈ Finset.range (2 * r + 1), cY p) *
            ∑ j ∈ Finset.range (NB + 1),
              ‖iteratedCovGrad (I := I) g 0 s₀ j u‖) :=
          mul_le_mul hXb hYb (norm_nonneg _) (le_trans (norm_nonneg _) hXb)
    _ = (CL * ∑ p ∈ Finset.range (2 * (a - r) + 1), cX p) *
          (CR * ∑ p ∈ Finset.range (2 * r + 1), cY p) *
        ((∑ j ∈ Finset.range (NA + 1),
            ‖iteratedCovGrad (I := I) g 0 s₀ j u‖) *
          (∑ j ∈ Finset.range (NB + 1),
            ‖iteratedCovGrad (I := I) g 0 s₀ j u‖)) := by
      ring

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem covJet_norm_comp (g : SmoothRiemannianMetric I M) (s j i : ℕ)
    (S : SmoothCcTensor g 0 s) :
    ‖iteratedCovGrad (I := I) g 0 (s + j) i
        (iteratedCovGrad (I := I) g 0 s j S)‖ =
      ‖iteratedCovGrad (I := I) g 0 s (j + i) S‖ := by
  have hleft : ‖iteratedCovGrad (I := I) g 0 (s + j) i
      (iteratedCovGrad (I := I) g 0 s j S)‖ =
      tensorL2Norm (I := I) (M := M) g 0 ((s + j) + i)
        (iteratedCovGrad (I := I) g 0 (s + j) i
          (iteratedCovGrad (I := I) g 0 s j S)).toFun :=
    SmoothCcTensor.norm_def (I := I) (M := M) _
  have hright : ‖iteratedCovGrad (I := I) g 0 s (j + i) S‖ =
      tensorL2Norm (I := I) (M := M) g 0 (s + (j + i))
        (iteratedCovGrad (I := I) g 0 s (j + i) S).toFun :=
    SmoothCcTensor.norm_def (I := I) (M := M) _
  have hsq : ‖iteratedCovGrad (I := I) g 0 (s + j) i
        (iteratedCovGrad (I := I) g 0 s j S)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g 0 s (j + i) S‖ ^ 2 := by
    rw [hleft, hright,
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq
        (I := I) (M := M) g ((s + j) + i)
        (iteratedCovGrad (I := I) g 0 (s + j) i
          (iteratedCovGrad (I := I) g 0 s j S)),
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq
        (I := I) (M := M) g (s + (j + i))
        (iteratedCovGrad (I := I) g 0 s (j + i) S)]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    exact riemannianFiberNormSq_iteratedCovGrad_comp (I := I) (M := M) g 0 s j i S x
  have hleft_nn : 0 ≤ ‖iteratedCovGrad (I := I) g 0 (s + j) i
      (iteratedCovGrad (I := I) g 0 s j S)‖ := norm_nonneg _
  have hright_nn : 0 ≤ ‖iteratedCovGrad (I := I) g 0 s (j + i) S‖ := norm_nonneg _
  rw [← Real.sqrt_sq hleft_nn, ← Real.sqrt_sq hright_nn, hsq]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem covJet_norm_order (g : SmoothRiemannianMetric I M) (s : ℕ)
    {i j : ℕ} (hij : i = j) (S : SmoothCcTensor g 0 s) :
    ‖iteratedCovGrad (I := I) g 0 s i S‖ =
      ‖iteratedCovGrad (I := I) g 0 s j S‖ := by
  subst j
  rfl

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem grad_jet_sum_le (g : SmoothRiemannianMetric I M) (s m : ℕ)
    (S : SmoothCcTensor g 0 s) :
    ∑ q ∈ Finset.range m,
        ‖iteratedCovGrad (I := I) g 0 (s + 1) q
          (covGrad (I := I) (M := M) g 0 s S)‖ ≤
      ∑ q ∈ Finset.range (m + 1),
        ‖iteratedCovGrad (I := I) g 0 s q S‖ := by
  have hterm : ∀ q : ℕ,
      ‖iteratedCovGrad (I := I) g 0 (s + 1) q
          (covGrad (I := I) (M := M) g 0 s S)‖ =
        ‖iteratedCovGrad (I := I) g 0 s (q + 1) S‖ := by
    intro q
    have hgrad : covGrad (I := I) (M := M) g 0 s S =
        iteratedCovGrad (I := I) g 0 s 1 S := rfl
    rw [hgrad, covJet_norm_comp (I := I) (M := M) g s 1 q S]
    exact covJet_norm_order (I := I) (M := M) g s (by omega) S
  rw [Finset.sum_congr rfl (fun q _ => hterm q)]
  have hsum := Finset.sum_range_succ'
    (fun q => ‖iteratedCovGrad (I := I) g 0 s q S‖) m
  have hzero : 0 ≤ ‖iteratedCovGrad (I := I) g 0 s 0 S‖ := norm_nonneg _
  linarith

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem jetProduct_le (g : SmoothRiemannianMetric I M) (s n p q : ℕ)
    (hp : p ≤ n + 2) (hq : q ≤ n + 2) (hpq : p + q ≤ 2 * n + 3)
    (S : SmoothCcTensor g 0 s) :
    (∑ j ∈ Finset.range p, ‖iteratedCovGrad (I := I) g 0 s j S‖) *
        (∑ j ∈ Finset.range q, ‖iteratedCovGrad (I := I) g 0 s j S‖) ≤
      (∑ j ∈ Finset.range (n + 1), ‖iteratedCovGrad (I := I) g 0 s j S‖) *
        (∑ j ∈ Finset.range (n + 2), ‖iteratedCovGrad (I := I) g 0 s j S‖) := by
  have hnonneg : ∀ m : ℕ,
      0 ≤ ∑ j ∈ Finset.range m, ‖iteratedCovGrad (I := I) g 0 s j S‖ :=
    fun m => Finset.sum_nonneg (fun j _ => norm_nonneg _)
  rcases le_total p q with hpq' | hqp'
  · have hp' : p ≤ n + 1 := by omega
    exact mul_le_mul (jetSum_mono (I := I) (M := M) g s hp' S)
      (jetSum_mono (I := I) (M := M) g s hq S) (hnonneg q) (hnonneg (n + 1))
  · have hq' : q ≤ n + 1 := by omega
    calc
      (∑ j ∈ Finset.range p, ‖iteratedCovGrad (I := I) g 0 s j S‖) *
          (∑ j ∈ Finset.range q, ‖iteratedCovGrad (I := I) g 0 s j S‖) =
        (∑ j ∈ Finset.range q, ‖iteratedCovGrad (I := I) g 0 s j S‖) *
          (∑ j ∈ Finset.range p, ‖iteratedCovGrad (I := I) g 0 s j S‖) := mul_comm _ _
      _ ≤ (∑ j ∈ Finset.range (n + 1),
            ‖iteratedCovGrad (I := I) g 0 s j S‖) *
          (∑ j ∈ Finset.range (n + 2),
            ‖iteratedCovGrad (I := I) g 0 s j S‖) :=
        mul_le_mul (jetSum_mono (I := I) (M := M) g s hq' S)
          (jetSum_mono (I := I) (M := M) g s hp S)
          (hnonneg p) (hnonneg (n + 1))



theorem iterL_pair_jet_of (g : SmoothRiemannianMetric I M) (s n : ℕ)
    {α : Type*} (Φ : α → SmoothCcTensor g (s + 1) s) (K : Set α)
    (CG : ℕ → ℝ) (hCG_nn : ∀ q, 0 ≤ CG q)
    (hCG : ∀ t, t ∈ K → ∀ (W : SmoothCcTensor g 0 (s + 1)) (q : ℕ),
      ‖iteratedCovGrad (I := I) g 0 s q
          (operatorFieldApply (I := I) (M := M) g (s + 1) s (Φ t) W)‖ ≤
        CG q * ∑ k ∈ Finset.range (q + 1),
          ‖iteratedCovGrad (I := I) g 0 (s + 1) k W‖) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t, t ∈ K → ∀ S : SmoothCcTensor g 0 s,
      |tensorL2Inner (I := I) (M := M) g 0 s
          (oneMinusConnLapSmoothIter (I := I) g 0 s n S).toFun
          (operatorFieldApply (I := I) (M := M) g (s + 1) s (Φ t)
            (covGrad (I := I) (M := M) g 0 s S)).toFun| ≤
        C * ((∑ j ∈ Finset.range (n + 1),
            ‖iteratedCovGrad (I := I) g 0 s j S‖) *
          (∑ j ∈ Finset.range (n + 2),
            ‖iteratedCovGrad (I := I) g 0 s j S‖)) := by
  classical
  set a : ℕ := n / 2 with ha
  set b : ℕ := n - n / 2 with hb
  obtain ⟨CL, hCL_nn, hCL⟩ := iterL_jet_le (I := I) (M := M) g s b
  obtain ⟨CR, hCR_nn, hCR⟩ := iterL_jet_le (I := I) (M := M) g s a
  refine ⟨CL 0 * (CR 0 * ∑ q ∈ Finset.range (2 * a + 1), CG q),
    mul_nonneg (hCL_nn 0)
      (mul_nonneg (hCR_nn 0) (Finset.sum_nonneg fun q _ => hCG_nn q)),
    fun t ht S => ?_⟩
  let G : SmoothCcTensor g 0 s :=
    operatorFieldApply (I := I) (M := M) g (s + 1) s (Φ t)
      (covGrad (I := I) (M := M) g 0 s S)
  have hpair := iterL_pair_le (I := I) (M := M) g s n a (by omega) S G
  rw [show n - a = b by omega] at hpair
  have hleft : ‖oneMinusConnLapSmoothIter (I := I) g 0 s b S‖ ≤
      CL 0 * ∑ q ∈ Finset.range (2 * b + 1),
        ‖iteratedCovGrad (I := I) g 0 s q S‖ := by
    simpa only [Nat.zero_add, iteratedCovGrad_zero] using hCL 0 S
  have hright : ‖oneMinusConnLapSmoothIter (I := I) g 0 s a G‖ ≤
      CR 0 * ((∑ q ∈ Finset.range (2 * a + 1), CG q) *
        ∑ k ∈ Finset.range (2 * a + 2),
          ‖iteratedCovGrad (I := I) g 0 s k S‖) := by
    have hbase := hCR 0 G
    simp only [Nat.zero_add, iteratedCovGrad_zero] at hbase
    refine le_trans hbase ?_
    refine mul_le_mul_of_nonneg_left ?_ (hCR_nn 0)
    have hterm : ∀ q ∈ Finset.range (2 * a + 1),
        ‖iteratedCovGrad (I := I) g 0 s q G‖ ≤
          CG q * ∑ k ∈ Finset.range (2 * a + 2),
            ‖iteratedCovGrad (I := I) g 0 s k S‖ := by
      intro q hq
      rw [Finset.mem_range] at hq
      have hstep := hCG t ht (covGrad (I := I) (M := M) g 0 s S) q
      change ‖iteratedCovGrad (I := I) g 0 s q G‖ ≤ _ at hstep
      refine le_trans hstep ?_
      refine mul_le_mul_of_nonneg_left ?_ (hCG_nn q)
      refine le_trans
        (jetSum_mono (I := I) (M := M) g (s + 1)
          (m := q + 1) (n := 2 * a + 1) (by omega)
          (covGrad (I := I) (M := M) g 0 s S)) ?_
      exact grad_jet_sum_le (I := I) (M := M) g s (2 * a + 1) S
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.sum_mul]
  refine le_trans hpair ?_
  have hleft_nn : 0 ≤ CL 0 * ∑ q ∈ Finset.range (2 * b + 1),
      ‖iteratedCovGrad (I := I) g 0 s q S‖ :=
    mul_nonneg (hCL_nn 0) (Finset.sum_nonneg fun q _ => norm_nonneg _)
  calc
    ‖oneMinusConnLapSmoothIter (I := I) g 0 s b S‖ *
        ‖oneMinusConnLapSmoothIter (I := I) g 0 s a G‖ ≤
      (CL 0 * ∑ q ∈ Finset.range (2 * b + 1),
          ‖iteratedCovGrad (I := I) g 0 s q S‖) *
        (CR 0 * ((∑ q ∈ Finset.range (2 * a + 1), CG q) *
          ∑ k ∈ Finset.range (2 * a + 2),
            ‖iteratedCovGrad (I := I) g 0 s k S‖)) :=
      mul_le_mul hleft hright (norm_nonneg _) hleft_nn
    _ = (CL 0 * (CR 0 * ∑ q ∈ Finset.range (2 * a + 1), CG q)) *
        ((∑ q ∈ Finset.range (2 * b + 1),
            ‖iteratedCovGrad (I := I) g 0 s q S‖) *
          (∑ k ∈ Finset.range (2 * a + 2),
            ‖iteratedCovGrad (I := I) g 0 s k S‖)) := by ring
    _ ≤ (CL 0 * (CR 0 * ∑ q ∈ Finset.range (2 * a + 1), CG q)) *
        ((∑ j ∈ Finset.range (n + 1),
            ‖iteratedCovGrad (I := I) g 0 s j S‖) *
          (∑ j ∈ Finset.range (n + 2),
            ‖iteratedCovGrad (I := I) g 0 s j S‖)) := by
      refine mul_le_mul_of_nonneg_left ?_
        (mul_nonneg (hCL_nn 0)
          (mul_nonneg (hCR_nn 0) (Finset.sum_nonneg fun q _ => hCG_nn q)))
      exact jetProduct_le (I := I) (M := M) g s n (2 * b + 1) (2 * a + 2)
        (by omega) (by omega) (by omega) S



theorem iterL_pair_jet_le (g : SmoothRiemannianMetric I M) (s n : ℕ)
    (Φ : SmoothCcTensor g (s + 1) s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ S : SmoothCcTensor g 0 s,
      |tensorL2Inner (I := I) (M := M) g 0 s
          (oneMinusConnLapSmoothIter (I := I) g 0 s n S).toFun
          (operatorFieldApply (I := I) (M := M) g (s + 1) s Φ
            (covGrad (I := I) (M := M) g 0 s S)).toFun| ≤
        C * ((∑ j ∈ Finset.range (n + 1),
            ‖iteratedCovGrad (I := I) g 0 s j S‖) *
          (∑ j ∈ Finset.range (n + 2),
            ‖iteratedCovGrad (I := I) g 0 s j S‖)) := by
  obtain ⟨CG, hCG_nn, hCG⟩ :=
    exists_appCc_iteratedCovGrad_l2_window_bound
      (I := I) (M := M) g (s + 1) s Φ
  obtain ⟨C, hC_nn, hC⟩ :=
    iterL_pair_jet_of (I := I) (M := M) g s n
      (fun _ : Unit => Φ) Set.univ CG hCG_nn
      (fun _ _ W q => hCG W q)
  exact ⟨C, hC_nn, fun S => hC () (Set.mem_univ ()) S⟩




theorem curv_iterL_pair_le (g : SmoothRiemannianMetric I M)
    (s₀ σ i q dS dZ NA NB : ℕ) (hNA : i + q + 2 + dS ≤ NA)
    (hNB : i + q + dZ ≤ NB) (cS cZ : ℕ → ℝ)
    (hcS : ∀ p, 0 ≤ cS p) (hcZ : ∀ p, 0 ≤ cZ p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : SmoothCcTensor g 0 s₀)
      (S : SmoothCcTensor g 0 σ) (Z : SmoothCcTensor g 0 (σ + 1)),
      (∀ p, ‖iteratedCovGrad (I := I) g 0 σ p S‖ ≤
        cS p * ∑ j ∈ Finset.range (p + dS + 1),
          ‖iteratedCovGrad (I := I) g 0 s₀ j u‖) →
      (∀ p, ‖iteratedCovGrad (I := I) g 0 (σ + 1) p Z‖ ≤
        cZ p * ∑ j ∈ Finset.range (p + dZ + 1),
          ‖iteratedCovGrad (I := I) g 0 s₀ j u‖) →
      |tensorL2Inner (I := I) (M := M) g 0 (σ + 1)
          (oneMinusConnLapSmoothIter (I := I) g 0 (σ + 1) i
            (pointwiseTensorCurv (I := I) (M := M) g σ
              (oneMinusConnLapSmoothIter (I := I) g 0 σ q S))).toFun Z.toFun| ≤
        C * ((∑ j ∈ Finset.range (NA + 1),
            ‖iteratedCovGrad (I := I) g 0 s₀ j u‖) *
          (∑ j ∈ Finset.range (NB + 1),
            ‖iteratedCovGrad (I := I) g 0 s₀ j u‖)) := by
  classical
  rcases le_or_gt q i with hqi | hiq
  · obtain ⟨Kp, hKp_nn, hKp⟩ :=
      exists_iteratedCovGrad_pointwiseTensorCurv_l2Norm_le
        (I := I) (M := M) g σ
    obtain ⟨CQ, hCQ_nn, hCQ⟩ := iterL_jet_le (I := I) (M := M) g σ q
    obtain ⟨CL, hCL_nn, hCL⟩ :=
      iterL_norm_le (I := I) (M := M) g (σ + 1) (i - (i + q) / 2)
    obtain ⟨CR, hCR_nn, hCR⟩ :=
      iterL_norm_le (I := I) (M := M) g (σ + 1) ((i + q) / 2)
    refine ⟨(CL * ((∑ c ∈ Finset.range (2 * (i - (i + q) / 2) + 1), Kp c) *
        ((∑ e ∈ Finset.range (2 * (i - (i + q) / 2) + 1 + 1), CQ e) *
          ∑ p ∈ Finset.range (2 * (i - (i + q) / 2) + 1 + 1 + 2 * q), cS p))) *
      (CR * ∑ p ∈ Finset.range (2 * ((i + q) / 2) + 1), cZ p),
      mul_nonneg (mul_nonneg hCL_nn (mul_nonneg
          (Finset.sum_nonneg fun c _ => hKp_nn c)
          (mul_nonneg (Finset.sum_nonneg fun e _ => hCQ_nn e)
            (Finset.sum_nonneg fun p _ => hcS p))))
        (mul_nonneg hCR_nn (Finset.sum_nonneg fun p _ => hcZ p)),
      fun u S Z hS hZ => ?_⟩
    have hLb :
        ‖oneMinusConnLapSmoothIter (I := I) g 0 (σ + 1) (i - (i + q) / 2)
          (pointwiseTensorCurv (I := I) (M := M) g σ
            (oneMinusConnLapSmoothIter (I := I) g 0 σ q S))‖ ≤
        (CL * ((∑ c ∈ Finset.range (2 * (i - (i + q) / 2) + 1), Kp c) *
          ((∑ e ∈ Finset.range (2 * (i - (i + q) / 2) + 1 + 1), CQ e) *
            ∑ p ∈ Finset.range (2 * (i - (i + q) / 2) + 1 + 1 + 2 * q), cS p))) *
          ∑ j ∈ Finset.range (NA + 1),
            ‖iteratedCovGrad (I := I) g 0 s₀ j u‖ := by
      refine le_trans (hCL (pointwiseTensorCurv (I := I) (M := M) g σ
        (oneMinusConnLapSmoothIter (I := I) g 0 σ q S))) ?_
      have h1 : ∑ c ∈ Finset.range (2 * (i - (i + q) / 2) + 1),
          ‖iteratedCovGrad (I := I) g 0 (σ + 1) c
            (pointwiseTensorCurv (I := I) (M := M) g σ
              (oneMinusConnLapSmoothIter (I := I) g 0 σ q S))‖ ≤
          (∑ c ∈ Finset.range (2 * (i - (i + q) / 2) + 1), Kp c) *
            ∑ e ∈ Finset.range (2 * (i - (i + q) / 2) + 1 + 1),
              ‖iteratedCovGrad (I := I) g 0 σ e
                (oneMinusConnLapSmoothIter (I := I) g 0 σ q S)‖ :=
        sum_window_le (2 * (i - (i + q) / 2) + 1) 1 Kp
          (fun c => ‖iteratedCovGrad (I := I) g 0 (σ + 1) c
            (pointwiseTensorCurv (I := I) (M := M) g σ
              (oneMinusConnLapSmoothIter (I := I) g 0 σ q S))‖)
          (fun e => ‖iteratedCovGrad (I := I) g 0 σ e
            (oneMinusConnLapSmoothIter (I := I) g 0 σ q S)‖)
          hKp_nn (fun _ => norm_nonneg _)
          (fun c _ => hKp c (oneMinusConnLapSmoothIter (I := I) g 0 σ q S))
      have h2 : ∑ e ∈ Finset.range (2 * (i - (i + q) / 2) + 1 + 1),
          ‖iteratedCovGrad (I := I) g 0 σ e
            (oneMinusConnLapSmoothIter (I := I) g 0 σ q S)‖ ≤
          (∑ e ∈ Finset.range (2 * (i - (i + q) / 2) + 1 + 1), CQ e) *
            ∑ p ∈ Finset.range (2 * (i - (i + q) / 2) + 1 + 1 + 2 * q),
              ‖iteratedCovGrad (I := I) g 0 σ p S‖ :=
        sum_window_le (2 * (i - (i + q) / 2) + 1 + 1) (2 * q) CQ
          (fun e => ‖iteratedCovGrad (I := I) g 0 σ e
            (oneMinusConnLapSmoothIter (I := I) g 0 σ q S)‖)
          (fun p => ‖iteratedCovGrad (I := I) g 0 σ p S‖)
          hCQ_nn (fun _ => norm_nonneg _) (fun e _ => hCQ e S)
      have h3 : ∑ p ∈ Finset.range (2 * (i - (i + q) / 2) + 1 + 1 + 2 * q),
          ‖iteratedCovGrad (I := I) g 0 σ p S‖ ≤
          (∑ p ∈ Finset.range (2 * (i - (i + q) / 2) + 1 + 1 + 2 * q), cS p) *
            ∑ j ∈ Finset.range (2 * (i - (i + q) / 2) + 1 + 1 + 2 * q + dS),
              ‖iteratedCovGrad (I := I) g 0 s₀ j u‖ :=
        sum_window_le (2 * (i - (i + q) / 2) + 1 + 1 + 2 * q) dS cS
          (fun p => ‖iteratedCovGrad (I := I) g 0 σ p S‖)
          (fun j => ‖iteratedCovGrad (I := I) g 0 s₀ j u‖)
          hcS (fun _ => norm_nonneg _) (fun p _ => hS p)
      have h4 :
          ∑ j ∈ Finset.range (2 * (i - (i + q) / 2) + 1 + 1 + 2 * q + dS),
              ‖iteratedCovGrad (I := I) g 0 s₀ j u‖ ≤
            ∑ j ∈ Finset.range (NA + 1),
              ‖iteratedCovGrad (I := I) g 0 s₀ j u‖ :=
        jetSum_mono (I := I) (M := M) g s₀ (by omega) u
      calc
        CL * ∑ c ∈ Finset.range (2 * (i - (i + q) / 2) + 1),
            ‖iteratedCovGrad (I := I) g 0 (σ + 1) c
              (pointwiseTensorCurv (I := I) (M := M) g σ
                (oneMinusConnLapSmoothIter (I := I) g 0 σ q S))‖
            ≤ CL * ((∑ c ∈ Finset.range (2 * (i - (i + q) / 2) + 1), Kp c) *
              ((∑ e ∈ Finset.range (2 * (i - (i + q) / 2) + 1 + 1), CQ e) *
                ((∑ p ∈ Finset.range
                    (2 * (i - (i + q) / 2) + 1 + 1 + 2 * q), cS p) *
                  ∑ j ∈ Finset.range (NA + 1),
                    ‖iteratedCovGrad (I := I) g 0 s₀ j u‖))) := by
              refine mul_le_mul_of_nonneg_left ?_ hCL_nn
              refine le_trans h1 ?_
              refine mul_le_mul_of_nonneg_left ?_
                (Finset.sum_nonneg fun c _ => hKp_nn c)
              refine le_trans h2 ?_
              refine mul_le_mul_of_nonneg_left ?_
                (Finset.sum_nonneg fun e _ => hCQ_nn e)
              refine le_trans h3 ?_
              exact mul_le_mul_of_nonneg_left h4
                (Finset.sum_nonneg fun p _ => hcS p)
        _ = (CL * ((∑ c ∈ Finset.range (2 * (i - (i + q) / 2) + 1), Kp c) *
              ((∑ e ∈ Finset.range (2 * (i - (i + q) / 2) + 1 + 1), CQ e) *
                ∑ p ∈ Finset.range
                  (2 * (i - (i + q) / 2) + 1 + 1 + 2 * q), cS p))) *
            ∑ j ∈ Finset.range (NA + 1),
              ‖iteratedCovGrad (I := I) g 0 s₀ j u‖ := by ring
    have hRb :
        ‖oneMinusConnLapSmoothIter (I := I) g 0 (σ + 1) ((i + q) / 2) Z‖ ≤
          (CR * ∑ p ∈ Finset.range (2 * ((i + q) / 2) + 1), cZ p) *
            ∑ j ∈ Finset.range (NB + 1),
              ‖iteratedCovGrad (I := I) g 0 s₀ j u‖ := by
      refine le_trans (hCR Z) ?_
      have h1 : ∑ p ∈ Finset.range (2 * ((i + q) / 2) + 1),
          ‖iteratedCovGrad (I := I) g 0 (σ + 1) p Z‖ ≤
          (∑ p ∈ Finset.range (2 * ((i + q) / 2) + 1), cZ p) *
            ∑ j ∈ Finset.range (2 * ((i + q) / 2) + 1 + dZ),
              ‖iteratedCovGrad (I := I) g 0 s₀ j u‖ :=
        sum_window_le (2 * ((i + q) / 2) + 1) dZ cZ
          (fun p => ‖iteratedCovGrad (I := I) g 0 (σ + 1) p Z‖)
          (fun j => ‖iteratedCovGrad (I := I) g 0 s₀ j u‖)
          hcZ (fun _ => norm_nonneg _) (fun p _ => hZ p)
      refine le_trans (mul_le_mul_of_nonneg_left h1 hCR_nn) ?_
      rw [← mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_
        (mul_nonneg hCR_nn (Finset.sum_nonneg fun p _ => hcZ p))
      exact jetSum_mono (I := I) (M := M) g s₀ (by omega) u
    refine le_trans (iterL_pair_le (I := I) (M := M) g (σ + 1) i
      ((i + q) / 2) (by omega)
      (pointwiseTensorCurv (I := I) (M := M) g σ
        (oneMinusConnLapSmoothIter (I := I) g 0 σ q S)) Z) ?_
    calc
      ‖oneMinusConnLapSmoothIter (I := I) g 0 (σ + 1) (i - (i + q) / 2)
          (pointwiseTensorCurv (I := I) (M := M) g σ
            (oneMinusConnLapSmoothIter (I := I) g 0 σ q S))‖ *
          ‖oneMinusConnLapSmoothIter (I := I) g 0 (σ + 1) ((i + q) / 2) Z‖
          ≤ ((CL * ((∑ c ∈ Finset.range (2 * (i - (i + q) / 2) + 1), Kp c) *
              ((∑ e ∈ Finset.range (2 * (i - (i + q) / 2) + 1 + 1), CQ e) *
                ∑ p ∈ Finset.range
                  (2 * (i - (i + q) / 2) + 1 + 1 + 2 * q), cS p))) *
              ∑ j ∈ Finset.range (NA + 1),
                ‖iteratedCovGrad (I := I) g 0 s₀ j u‖) *
            ((CR * ∑ p ∈ Finset.range (2 * ((i + q) / 2) + 1), cZ p) *
              ∑ j ∈ Finset.range (NB + 1),
                ‖iteratedCovGrad (I := I) g 0 s₀ j u‖) :=
            mul_le_mul hLb hRb (norm_nonneg _) (le_trans (norm_nonneg _) hLb)
      _ = (CL * ((∑ c ∈ Finset.range (2 * (i - (i + q) / 2) + 1), Kp c) *
            ((∑ e ∈ Finset.range (2 * (i - (i + q) / 2) + 1 + 1), CQ e) *
              ∑ p ∈ Finset.range
                (2 * (i - (i + q) / 2) + 1 + 1 + 2 * q), cS p))) *
          (CR * ∑ p ∈ Finset.range (2 * ((i + q) / 2) + 1), cZ p) *
          ((∑ j ∈ Finset.range (NA + 1),
              ‖iteratedCovGrad (I := I) g 0 s₀ j u‖) *
            (∑ j ∈ Finset.range (NB + 1),
              ‖iteratedCovGrad (I := I) g 0 s₀ j u‖)) := by ring
  · obtain ⟨K, hK_nn, hK⟩ :=
      exists_iteratedCovGrad_rawConnLap_covDivergence_commutator_l2_le
        (I := I) (M := M) g σ
    obtain ⟨CI, hCI_nn, hCI⟩ := iterL_jet_le (I := I) (M := M) g (σ + 1) i
    obtain ⟨CL, hCL_nn, hCL⟩ :=
      iterL_norm_le (I := I) (M := M) g σ (q - (q - i - 1) / 2)
    obtain ⟨CR, hCR_nn, hCR⟩ :=
      iterL_norm_le (I := I) (M := M) g σ ((q - i - 1) / 2)
    refine ⟨(CL * ∑ p ∈ Finset.range (2 * (q - (q - i - 1) / 2) + 1), cS p) *
      (CR * ((∑ c ∈ Finset.range (2 * ((q - i - 1) / 2) + 1), K c) *
        ((∑ e ∈ Finset.range (2 * ((q - i - 1) / 2) + 1 + 1), CI e) *
          ∑ b ∈ Finset.range (2 * ((q - i - 1) / 2) + 1 + 1 + 2 * i), cZ b))),
      mul_nonneg (mul_nonneg hCL_nn (Finset.sum_nonneg fun p _ => hcS p))
        (mul_nonneg hCR_nn (mul_nonneg (Finset.sum_nonneg fun c _ => hK_nn c)
          (mul_nonneg (Finset.sum_nonneg fun e _ => hCI_nn e)
            (Finset.sum_nonneg fun b _ => hcZ b)))),
      fun u S Z hS hZ => ?_⟩
    have hmove : tensorL2Inner (I := I) (M := M) g 0 (σ + 1)
        (oneMinusConnLapSmoothIter (I := I) g 0 (σ + 1) i
          (pointwiseTensorCurv (I := I) (M := M) g σ
            (oneMinusConnLapSmoothIter (I := I) g 0 σ q S))).toFun Z.toFun =
      tensorL2Inner (I := I) (M := M) g 0 (σ + 1)
        (pointwiseTensorCurv (I := I) (M := M) g σ
          (oneMinusConnLapSmoothIter (I := I) g 0 σ q S)).toFun
        (oneMinusConnLapSmoothIter (I := I) g 0 (σ + 1) i Z).toFun :=
      oneMinusConnLapSmoothIter_l2Inner_selfAdjoint
        (I := I) (M := M) g 0 (σ + 1) i _ Z
    have hgreen := pointwiseTensorCurv_l2Inner_eq_covDivergence_commutator
      (I := I) (M := M) g σ
      (oneMinusConnLapSmoothIter (I := I) g 0 σ q S)
      (oneMinusConnLapSmoothIter (I := I) g 0 (σ + 1) i Z)
    rw [hmove, hgreen]
    have hLb :
        ‖oneMinusConnLapSmoothIter (I := I) g 0 σ (q - (q - i - 1) / 2) S‖ ≤
          (CL * ∑ p ∈ Finset.range (2 * (q - (q - i - 1) / 2) + 1), cS p) *
            ∑ j ∈ Finset.range (NA + 1),
              ‖iteratedCovGrad (I := I) g 0 s₀ j u‖ := by
      refine le_trans (hCL S) ?_
      have hw : ∑ p ∈ Finset.range (2 * (q - (q - i - 1) / 2) + 1),
          ‖iteratedCovGrad (I := I) g 0 σ p S‖ ≤
          (∑ p ∈ Finset.range (2 * (q - (q - i - 1) / 2) + 1), cS p) *
            ∑ j ∈ Finset.range (2 * (q - (q - i - 1) / 2) + 1 + dS),
              ‖iteratedCovGrad (I := I) g 0 s₀ j u‖ :=
        sum_window_le (2 * (q - (q - i - 1) / 2) + 1) dS cS
          (fun p => ‖iteratedCovGrad (I := I) g 0 σ p S‖)
          (fun j => ‖iteratedCovGrad (I := I) g 0 s₀ j u‖)
          hcS (fun _ => norm_nonneg _) (fun p _ => hS p)
      refine le_trans (mul_le_mul_of_nonneg_left hw hCL_nn) ?_
      rw [← mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_
        (mul_nonneg hCL_nn (Finset.sum_nonneg fun p _ => hcS p))
      exact jetSum_mono (I := I) (M := M) g s₀ (by omega) u
    set D : SmoothCcTensor g 0 σ :=
      rawTensorConnLapSmooth (I := I) g 0 σ
          (covDivergence (I := I) (M := M) g σ
            (oneMinusConnLapSmoothIter (I := I) g 0 (σ + 1) i Z)) -
        covDivergence (I := I) (M := M) g σ
          (rawTensorConnLapSmooth (I := I) g 0 (σ + 1)
            (oneMinusConnLapSmoothIter (I := I) g 0 (σ + 1) i Z)) with hD
    have hRb :
        ‖oneMinusConnLapSmoothIter (I := I) g 0 σ ((q - i - 1) / 2) D‖ ≤
        (CR * ((∑ c ∈ Finset.range (2 * ((q - i - 1) / 2) + 1), K c) *
          ((∑ e ∈ Finset.range (2 * ((q - i - 1) / 2) + 1 + 1), CI e) *
            ∑ b ∈ Finset.range (2 * ((q - i - 1) / 2) + 1 + 1 + 2 * i), cZ b))) *
          ∑ j ∈ Finset.range (NB + 1),
            ‖iteratedCovGrad (I := I) g 0 s₀ j u‖ := by
      refine le_trans (hCR D) ?_
      have h1 : ∑ c ∈ Finset.range (2 * ((q - i - 1) / 2) + 1),
          ‖iteratedCovGrad (I := I) g 0 σ c D‖ ≤
          (∑ c ∈ Finset.range (2 * ((q - i - 1) / 2) + 1), K c) *
            ∑ e ∈ Finset.range (2 * ((q - i - 1) / 2) + 1 + 1),
              ‖iteratedCovGrad (I := I) g 0 (σ + 1) e
                (oneMinusConnLapSmoothIter (I := I) g 0 (σ + 1) i Z)‖ := by
        rw [hD]
        exact sum_window_le (2 * ((q - i - 1) / 2) + 1) 1 K
          (fun c => ‖iteratedCovGrad (I := I) g 0 σ c
            (rawTensorConnLapSmooth (I := I) g 0 σ
                (covDivergence (I := I) (M := M) g σ
                  (oneMinusConnLapSmoothIter (I := I) g 0 (σ + 1) i Z)) -
              covDivergence (I := I) (M := M) g σ
                (rawTensorConnLapSmooth (I := I) g 0 (σ + 1)
                  (oneMinusConnLapSmoothIter (I := I) g 0 (σ + 1) i Z)))‖)
          (fun e => ‖iteratedCovGrad (I := I) g 0 (σ + 1) e
            (oneMinusConnLapSmoothIter (I := I) g 0 (σ + 1) i Z)‖)
          hK_nn (fun _ => norm_nonneg _)
          (fun c _ => hK c (oneMinusConnLapSmoothIter (I := I) g 0 (σ + 1) i Z))
      have h2 : ∑ e ∈ Finset.range (2 * ((q - i - 1) / 2) + 1 + 1),
          ‖iteratedCovGrad (I := I) g 0 (σ + 1) e
            (oneMinusConnLapSmoothIter (I := I) g 0 (σ + 1) i Z)‖ ≤
          (∑ e ∈ Finset.range (2 * ((q - i - 1) / 2) + 1 + 1), CI e) *
            ∑ b ∈ Finset.range (2 * ((q - i - 1) / 2) + 1 + 1 + 2 * i),
              ‖iteratedCovGrad (I := I) g 0 (σ + 1) b Z‖ :=
        sum_window_le (2 * ((q - i - 1) / 2) + 1 + 1) (2 * i) CI
          (fun e => ‖iteratedCovGrad (I := I) g 0 (σ + 1) e
            (oneMinusConnLapSmoothIter (I := I) g 0 (σ + 1) i Z)‖)
          (fun b => ‖iteratedCovGrad (I := I) g 0 (σ + 1) b Z‖)
          hCI_nn (fun _ => norm_nonneg _) (fun e _ => hCI e Z)
      have h3 : ∑ b ∈ Finset.range (2 * ((q - i - 1) / 2) + 1 + 1 + 2 * i),
          ‖iteratedCovGrad (I := I) g 0 (σ + 1) b Z‖ ≤
          (∑ b ∈ Finset.range (2 * ((q - i - 1) / 2) + 1 + 1 + 2 * i), cZ b) *
            ∑ j ∈ Finset.range (2 * ((q - i - 1) / 2) + 1 + 1 + 2 * i + dZ),
              ‖iteratedCovGrad (I := I) g 0 s₀ j u‖ :=
        sum_window_le (2 * ((q - i - 1) / 2) + 1 + 1 + 2 * i) dZ cZ
          (fun b => ‖iteratedCovGrad (I := I) g 0 (σ + 1) b Z‖)
          (fun j => ‖iteratedCovGrad (I := I) g 0 s₀ j u‖)
          hcZ (fun _ => norm_nonneg _) (fun b _ => hZ b)
      have h4 :
          ∑ j ∈ Finset.range (2 * ((q - i - 1) / 2) + 1 + 1 + 2 * i + dZ),
              ‖iteratedCovGrad (I := I) g 0 s₀ j u‖ ≤
            ∑ j ∈ Finset.range (NB + 1),
              ‖iteratedCovGrad (I := I) g 0 s₀ j u‖ :=
        jetSum_mono (I := I) (M := M) g s₀ (by omega) u
      calc
        CR * ∑ c ∈ Finset.range (2 * ((q - i - 1) / 2) + 1),
            ‖iteratedCovGrad (I := I) g 0 σ c D‖
            ≤ CR * ((∑ c ∈ Finset.range (2 * ((q - i - 1) / 2) + 1), K c) *
              ((∑ e ∈ Finset.range (2 * ((q - i - 1) / 2) + 1 + 1), CI e) *
                ((∑ b ∈ Finset.range
                    (2 * ((q - i - 1) / 2) + 1 + 1 + 2 * i), cZ b) *
                  ∑ j ∈ Finset.range (NB + 1),
                    ‖iteratedCovGrad (I := I) g 0 s₀ j u‖))) := by
              refine mul_le_mul_of_nonneg_left ?_ hCR_nn
              refine le_trans h1 ?_
              refine mul_le_mul_of_nonneg_left ?_
                (Finset.sum_nonneg fun c _ => hK_nn c)
              refine le_trans h2 ?_
              refine mul_le_mul_of_nonneg_left ?_
                (Finset.sum_nonneg fun e _ => hCI_nn e)
              refine le_trans h3 ?_
              exact mul_le_mul_of_nonneg_left h4
                (Finset.sum_nonneg fun b _ => hcZ b)
        _ = (CR * ((∑ c ∈ Finset.range (2 * ((q - i - 1) / 2) + 1), K c) *
              ((∑ e ∈ Finset.range (2 * ((q - i - 1) / 2) + 1 + 1), CI e) *
                ∑ b ∈ Finset.range
                  (2 * ((q - i - 1) / 2) + 1 + 1 + 2 * i), cZ b))) *
            ∑ j ∈ Finset.range (NB + 1),
              ‖iteratedCovGrad (I := I) g 0 s₀ j u‖ := by ring
    refine le_trans (iterL_pair_le (I := I) (M := M) g σ q
      ((q - i - 1) / 2) (by omega) S D) ?_
    calc
      ‖oneMinusConnLapSmoothIter (I := I) g 0 σ (q - (q - i - 1) / 2) S‖ *
          ‖oneMinusConnLapSmoothIter (I := I) g 0 σ ((q - i - 1) / 2) D‖
          ≤ ((CL * ∑ p ∈ Finset.range (2 * (q - (q - i - 1) / 2) + 1), cS p) *
              ∑ j ∈ Finset.range (NA + 1),
                ‖iteratedCovGrad (I := I) g 0 s₀ j u‖) *
            ((CR * ((∑ c ∈ Finset.range (2 * ((q - i - 1) / 2) + 1), K c) *
              ((∑ e ∈ Finset.range (2 * ((q - i - 1) / 2) + 1 + 1), CI e) *
                ∑ b ∈ Finset.range
                  (2 * ((q - i - 1) / 2) + 1 + 1 + 2 * i), cZ b))) *
              ∑ j ∈ Finset.range (NB + 1),
                ‖iteratedCovGrad (I := I) g 0 s₀ j u‖) :=
            mul_le_mul hLb hRb (norm_nonneg _) (le_trans (norm_nonneg _) hLb)
      _ = (CL * ∑ p ∈ Finset.range (2 * (q - (q - i - 1) / 2) + 1), cS p) *
          (CR * ((∑ c ∈ Finset.range (2 * ((q - i - 1) / 2) + 1), K c) *
            ((∑ e ∈ Finset.range (2 * ((q - i - 1) / 2) + 1 + 1), CI e) *
              ∑ b ∈ Finset.range
                (2 * ((q - i - 1) / 2) + 1 + 1 + 2 * i), cZ b))) *
          ((∑ j ∈ Finset.range (NA + 1),
              ‖iteratedCovGrad (I := I) g 0 s₀ j u‖) *
            (∑ j ∈ Finset.range (NB + 1),
              ‖iteratedCovGrad (I := I) g 0 s₀ j u‖)) := by ring

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry
