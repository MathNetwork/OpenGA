import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingCm
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.PointwiseToL2Packaging
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.IntegratedOrder2Garding
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RawConnLapL2SobolevBounds.RoughLaplacianSecondCovGradL2Bound

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Analysis.Sobolev.Tensor

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev
open DifferentialGeometry.Integral.Connection

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem exists_moserTameProduct_iteratedCovGrad_l2Norm_le
    (g : SmoothRiemannianMetric I M) (p q k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (c : Integral.L2.SmoothCcTensor g 0 p) (w : Integral.L2.SmoothCcTensor g 0 q)
        (P : Integral.L2.SmoothCcTensor g 0 (p + q)) (Λ Λ₀ : ℝ), 0 ≤ Λ → 0 ≤ Λ₀ →
        (∀ (x : M) (i : ℕ), i ≤ k →
          riemannianFiberNormSq (I := I) (M := M) g 0 (p + i) x
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 p i c).toSection x) ≤ Λ ^ 2) →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g 0 q x (w.toSection x) ≤ Λ₀ ^ 2) →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g 0 (p + q + k) x
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 (p + q) k P).toSection x) ≤
            (∑ i ∈ Finset.range (k + 1),
              (k.choose i : ℝ) ^ 2 *
                (riemannianFiberNormSq (I := I) (M := M) g 0 (p + i) x
                    ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 p i c).toSection x) *
                  riemannianFiberNormSq (I := I) (M := M) g 0 (q + (k - i)) x
                    ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 q (k - i) w).toSection x)))) →
        Integral.L2.tensorL2Norm (I := I) g 0 (p + q + k)
            (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 (p + q) k P).toFun ≤
          C * (Λ * ∑ i ∈ Finset.range (k + 1),
                  Integral.L2.tensorL2Norm (I := I) g 0 (q + i)
                    (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 q i w).toFun
              + Λ₀ * ∑ i ∈ Finset.range (k + 1),
                  Integral.L2.tensorL2Norm (I := I) g 0 (p + i)
                    (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 p i c).toFun) := by
  classical
  refine ⟨(2 : ℝ) ^ k, by positivity, ?_⟩
  intro c w P Λ Λ₀ hΛ hΛ₀ hc hw hP

  set Tw : ∀ i, Integral.L2.SmoothCcTensor g 0 (q + (k - i)) :=
    fun i => PDE.RicciFlow.iteratedCovGrad (I := I) g 0 q (k - i) w with hTw_def

  have hpt :
      ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g 0 (p + q + k) x
            ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 (p + q) k P).toSection x) ≤
          ((2 : ℝ) ^ k * Λ) ^ 2 * ∑ i ∈ Finset.range (k + 1),
            riemannianFiberNormSq (I := I) (M := M) g 0 (q + (k - i)) x ((Tw i).toSection x) := by
    intro x
    refine le_trans (hP x) ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun i hi => ?_)
    have hi_le : i ≤ k := by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hi
    have hcΛ : riemannianFiberNormSq (I := I) (M := M) g 0 (p + i) x
        ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 p i c).toSection x) ≤ Λ ^ 2 := hc x i hi_le
    have hc_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g 0 (p + i) x
        ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 p i c).toSection x) :=
      riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (p + i) x _
    have hw_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g 0 (q + (k - i)) x ((Tw i).toSection x) :=
      riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (q + (k - i)) x _
    have hchoose : ((k.choose i : ℝ)) ^ 2 ≤ ((2 : ℝ) ^ k) ^ 2 := by
      have h1 : (k.choose i : ℝ) ≤ (2 : ℝ) ^ k := by
        have := Nat.choose_le_two_pow (n := k) (k := i)
        calc (k.choose i : ℝ) ≤ ((2 ^ k : ℕ) : ℝ) := by exact_mod_cast this
          _ = (2 : ℝ) ^ k := by push_cast; ring
      have h0 : (0 : ℝ) ≤ (k.choose i : ℝ) := by positivity
      nlinarith [h1, h0]
    have hchoose_nn : (0 : ℝ) ≤ ((k.choose i : ℝ)) ^ 2 := by positivity
    calc (k.choose i : ℝ) ^ 2 *
            (riemannianFiberNormSq (I := I) (M := M) g 0 (p + i) x
                ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 p i c).toSection x) *
              riemannianFiberNormSq (I := I) (M := M) g 0 (q + (k - i)) x ((Tw i).toSection x))
        ≤ ((2 : ℝ) ^ k) ^ 2 * (Λ ^ 2 *
              riemannianFiberNormSq (I := I) (M := M) g 0 (q + (k - i)) x ((Tw i).toSection x)) := by
          apply mul_le_mul hchoose ?_ (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_right hcΛ hw_nn
      _ = ((2 : ℝ) ^ k * Λ) ^ 2 *
            riemannianFiberNormSq (I := I) (M := M) g 0 (q + (k - i)) x ((Tw i).toSection x) := by
          ring

  have hpack :
      ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 (p + q) k P‖ ≤
        ((2 : ℝ) ^ k * Λ) * ∑ i ∈ Finset.range (k + 1), ‖Tw i‖ :=
    tensorL2Norm_le_of_pointwise_fiberNormSq_bound_sum (I := I) (M := M) g (k + 1)
      (fun i => q + (k - i)) Tw
      (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 (p + q) k P)
      ((2 : ℝ) ^ k * Λ) (by positivity) hpt

  have hreindex : (∑ i ∈ Finset.range (k + 1), ‖Tw i‖) =
      ∑ i ∈ Finset.range (k + 1),
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 q i w‖ := by
    have := Finset.sum_range_reflect
      (fun i => ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 q i w‖) (k + 1)
    simpa [hTw_def, Nat.succ_sub_one] using this
  rw [hreindex] at hpack

  rw [Integral.L2.SmoothCcTensor.norm_def (I := I) (M := M)
        (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 (p + q) k P)] at hpack
  have hsum_w_eq : (∑ i ∈ Finset.range (k + 1),
      ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 q i w‖) =
      ∑ i ∈ Finset.range (k + 1),
        Integral.L2.tensorL2Norm (I := I) g 0 (q + i)
          (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 q i w).toFun :=
    Finset.sum_congr rfl (fun i _ => Integral.L2.SmoothCcTensor.norm_def (I := I) (M := M) _)
  rw [hsum_w_eq] at hpack
  set Sw : ℝ := ∑ i ∈ Finset.range (k + 1),
      Integral.L2.tensorL2Norm (I := I) g 0 (q + i)
        (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 q i w).toFun with hSw_def
  set Sc : ℝ := ∑ i ∈ Finset.range (k + 1),
      Integral.L2.tensorL2Norm (I := I) g 0 (p + i)
        (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 p i c).toFun with hSc_def
  have hSw_nn : 0 ≤ Sw :=
    Finset.sum_nonneg (fun i _ => Integral.L2.tensorL2Norm_nonneg (I := I) (M := M) g 0 (q + i) _)
  have hSc_nn : 0 ≤ Sc :=
    Finset.sum_nonneg (fun i _ => Integral.L2.tensorL2Norm_nonneg (I := I) (M := M) g 0 (p + i) _)
  calc Integral.L2.tensorL2Norm (I := I) g 0 (p + q + k)
          (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 (p + q) k P).toFun
      ≤ (2 : ℝ) ^ k * Λ * Sw := hpack
    _ ≤ (2 : ℝ) ^ k * (Λ * Sw + Λ₀ * Sc) := by
        have hexp : (2 : ℝ) ^ k * (Λ * Sw + Λ₀ * Sc)
            = (2 : ℝ) ^ k * Λ * Sw + (2 : ℝ) ^ k * (Λ₀ * Sc) := by ring
        have hnn : 0 ≤ (2 : ℝ) ^ k * (Λ₀ * Sc) :=
          mul_nonneg (by positivity) (mul_nonneg hΛ₀ hSc_nn)
        rw [hexp]; linarith

set_option maxHeartbeats 1600000 in
omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem exists_moserTameProduct_three_iteratedCovGrad_l2Norm_le
    (g : SmoothRiemannianMetric I M) (p q r k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (a : Integral.L2.SmoothCcTensor g 0 p) (b : Integral.L2.SmoothCcTensor g 0 q)
        (c : Integral.L2.SmoothCcTensor g 0 r)
        (P : Integral.L2.SmoothCcTensor g 0 (p + q + r)) (Λa Λb Λc : ℝ),
        0 ≤ Λa → 0 ≤ Λb → 0 ≤ Λc →
        (∀ (x : M) (i : ℕ), i ≤ k →
          riemannianFiberNormSq (I := I) (M := M) g 0 (p + i) x
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 p i a).toSection x) ≤ Λa ^ 2) →
        (∀ (x : M) (j : ℕ), j ≤ k →
          riemannianFiberNormSq (I := I) (M := M) g 0 (q + j) x
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 q j b).toSection x) ≤ Λb ^ 2) →
        (∀ (x : M) (l : ℕ), l ≤ k →
          riemannianFiberNormSq (I := I) (M := M) g 0 (r + l) x
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 r l c).toSection x) ≤ Λc ^ 2) →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g 0 (p + q + r + k) x
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 (p + q + r) k P).toSection x) ≤
            (∑ i ∈ Finset.range (k + 1),
              ((k.choose i : ℝ)) ^ 2 *
                (riemannianFiberNormSq (I := I) (M := M) g 0 (p + (k - i)) x
                    ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 p (k - i) a).toSection x) *
                  (∑ j ∈ Finset.range (i + 1),
                    ((i.choose j : ℝ)) ^ 2 *
                      (riemannianFiberNormSq (I := I) (M := M) g 0 (q + (i - j)) x
                          ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 q (i - j) b).toSection x) *
                        riemannianFiberNormSq (I := I) (M := M) g 0 (r + j) x
                          ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 r j c).toSection x)))))) →
        Integral.L2.tensorL2Norm (I := I) g 0 (p + q + r + k)
            (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 (p + q + r) k P).toFun ≤
          C * (Λb * Λc * ∑ i ∈ Finset.range (k + 1),
                  Integral.L2.tensorL2Norm (I := I) g 0 (p + i)
                    (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 p i a).toFun
              + Λa * Λc * ∑ j ∈ Finset.range (k + 1),
                  Integral.L2.tensorL2Norm (I := I) g 0 (q + j)
                    (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 q j b).toFun
              + Λa * Λb * ∑ l ∈ Finset.range (k + 1),
                  Integral.L2.tensorL2Norm (I := I) g 0 (r + l)
                    (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 r l c).toFun) := by
  classical
  refine ⟨Real.sqrt (k + 1) * (2 : ℝ) ^ (2 * k), by positivity, ?_⟩
  intro a b c P Λa Λb Λc hΛa hΛb hΛc ha hb hc hP

  set Ta : ∀ i, Integral.L2.SmoothCcTensor g 0 (p + (k - i)) :=
    fun i => PDE.RicciFlow.iteratedCovGrad (I := I) g 0 p (k - i) a with hTa_def

  set D : ℝ := Real.sqrt (k + 1) * (2 : ℝ) ^ (2 * k) * (Λb * Λc) with hD_def
  have hD_nn : 0 ≤ D := by rw [hD_def]; positivity

  have hpt :
      ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g 0 (p + q + r + k) x
            ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 (p + q + r) k P).toSection x) ≤
          D ^ 2 * ∑ i ∈ Finset.range (k + 1),
            riemannianFiberNormSq (I := I) (M := M) g 0 (p + (k - i)) x ((Ta i).toSection x) := by
    intro x
    refine le_trans (hP x) ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun i hi => ?_)
    have hi_le : i ≤ k := by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hi
    have ha_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g 0 (p + (k - i)) x
        ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 p (k - i) a).toSection x) :=
      riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (p + (k - i)) x _
    have hinner :
        (∑ j ∈ Finset.range (i + 1),
            ((i.choose j : ℝ)) ^ 2 *
              (riemannianFiberNormSq (I := I) (M := M) g 0 (q + (i - j)) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 q (i - j) b).toSection x) *
                riemannianFiberNormSq (I := I) (M := M) g 0 (r + j) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 r j c).toSection x)))
          ≤ ((k : ℝ) + 1) * ((2 : ℝ) ^ k) ^ 2 * (Λb ^ 2 * Λc ^ 2) := by
      have hbound : ∀ j ∈ Finset.range (i + 1),
          ((i.choose j : ℝ)) ^ 2 *
            (riemannianFiberNormSq (I := I) (M := M) g 0 (q + (i - j)) x
                ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 q (i - j) b).toSection x) *
              riemannianFiberNormSq (I := I) (M := M) g 0 (r + j) x
                ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 r j c).toSection x))
            ≤ ((2 : ℝ) ^ k) ^ 2 * (Λb ^ 2 * Λc ^ 2) := by
        intro j hj
        have hj_le : j ≤ i := by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hj
        have hjk : j ≤ k := le_trans hj_le hi_le
        have hij_k : i - j ≤ k := le_trans (Nat.sub_le i j) hi_le
        have hbΛ : riemannianFiberNormSq (I := I) (M := M) g 0 (q + (i - j)) x
            ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 q (i - j) b).toSection x) ≤ Λb ^ 2 :=
          hb x (i - j) hij_k
        have hcΛ : riemannianFiberNormSq (I := I) (M := M) g 0 (r + j) x
            ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 r j c).toSection x) ≤ Λc ^ 2 :=
          hc x j hjk
        have hb_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g 0 (q + (i - j)) x
            ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 q (i - j) b).toSection x) :=
          riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (q + (i - j)) x _
        have hc_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g 0 (r + j) x
            ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 r j c).toSection x) :=
          riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (r + j) x _
        have hchoose_i : ((i.choose j : ℝ)) ^ 2 ≤ ((2 : ℝ) ^ k) ^ 2 := by
          have h1 : (i.choose j : ℝ) ≤ (2 : ℝ) ^ k := by
            have hle := Nat.choose_le_two_pow (n := i) (k := j)
            calc (i.choose j : ℝ) ≤ ((2 ^ i : ℕ) : ℝ) := by exact_mod_cast hle
              _ = (2 : ℝ) ^ i := by push_cast; ring
              _ ≤ (2 : ℝ) ^ k := by
                  apply pow_le_pow_right₀ (by norm_num) hi_le
          have h0 : (0 : ℝ) ≤ (i.choose j : ℝ) := by positivity
          nlinarith [h1, h0]
        have hprod_le : riemannianFiberNormSq (I := I) (M := M) g 0 (q + (i - j)) x
            ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 q (i - j) b).toSection x) *
              riemannianFiberNormSq (I := I) (M := M) g 0 (r + j) x
                ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 r j c).toSection x)
            ≤ Λb ^ 2 * Λc ^ 2 := by
          apply mul_le_mul hbΛ hcΛ hc_nn (by positivity)
        have hprod_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g 0 (q + (i - j)) x
            ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 q (i - j) b).toSection x) *
              riemannianFiberNormSq (I := I) (M := M) g 0 (r + j) x
                ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 r j c).toSection x) :=
          mul_nonneg hb_nn hc_nn
        exact mul_le_mul hchoose_i hprod_le hprod_nn (by positivity)
      refine le_trans (Finset.sum_le_sum hbound) ?_
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hik : ((i + 1 : ℕ) : ℝ) ≤ (k : ℝ) + 1 := by
        have hii : i + 1 ≤ k + 1 := by omega
        calc ((i + 1 : ℕ) : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast hii
          _ = (k : ℝ) + 1 := by push_cast; ring
      have hrest_nn : 0 ≤ ((2 : ℝ) ^ k) ^ 2 * (Λb ^ 2 * Λc ^ 2) := by positivity
      nlinarith [hik, hrest_nn]
    have hchoose_k : ((k.choose i : ℝ)) ^ 2 ≤ ((2 : ℝ) ^ k) ^ 2 := by
      have h1 : (k.choose i : ℝ) ≤ (2 : ℝ) ^ k := by
        have hle := Nat.choose_le_two_pow (n := k) (k := i)
        calc (k.choose i : ℝ) ≤ ((2 ^ k : ℕ) : ℝ) := by exact_mod_cast hle
          _ = (2 : ℝ) ^ k := by push_cast; ring
      have h0 : (0 : ℝ) ≤ (k.choose i : ℝ) := by positivity
      nlinarith [h1, h0]
    have hinner_nn : 0 ≤ (∑ j ∈ Finset.range (i + 1),
        ((i.choose j : ℝ)) ^ 2 *
          (riemannianFiberNormSq (I := I) (M := M) g 0 (q + (i - j)) x
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 q (i - j) b).toSection x) *
            riemannianFiberNormSq (I := I) (M := M) g 0 (r + j) x
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 r j c).toSection x))) := by
      apply Finset.sum_nonneg
      intro j _
      apply mul_nonneg (by positivity)
      exact mul_nonneg
        (riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (q + (i - j)) x _)
        (riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (r + j) x _)
    have hDsq : D ^ 2 = ((k : ℝ) + 1) * (((2 : ℝ) ^ k) ^ 2 * ((2 : ℝ) ^ k) ^ 2) * (Λb ^ 2 * Λc ^ 2) := by
      rw [hD_def]
      have hsq : Real.sqrt ((k : ℝ) + 1) ^ 2 = (k : ℝ) + 1 := Real.sq_sqrt (by positivity)
      have h2 : ((2 : ℝ) ^ (2 * k)) = ((2 : ℝ) ^ k) * ((2 : ℝ) ^ k) := by
        rw [two_mul, pow_add]
      rw [mul_pow, mul_pow, hsq, h2]; ring
    calc ((k.choose i : ℝ)) ^ 2 *
            (riemannianFiberNormSq (I := I) (M := M) g 0 (p + (k - i)) x
                ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 p (k - i) a).toSection x) *
              (∑ j ∈ Finset.range (i + 1),
                ((i.choose j : ℝ)) ^ 2 *
                  (riemannianFiberNormSq (I := I) (M := M) g 0 (q + (i - j)) x
                      ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 q (i - j) b).toSection x) *
                    riemannianFiberNormSq (I := I) (M := M) g 0 (r + j) x
                      ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 r j c).toSection x))))
        ≤ ((2 : ℝ) ^ k) ^ 2 *
            (riemannianFiberNormSq (I := I) (M := M) g 0 (p + (k - i)) x
                ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 p (k - i) a).toSection x) *
              (((k : ℝ) + 1) * ((2 : ℝ) ^ k) ^ 2 * (Λb ^ 2 * Λc ^ 2))) := by
          apply mul_le_mul hchoose_k _ _ (by positivity)
          · apply mul_le_mul_of_nonneg_left hinner ha_nn
          · exact mul_nonneg ha_nn hinner_nn
      _ = D ^ 2 * riemannianFiberNormSq (I := I) (M := M) g 0 (p + (k - i)) x
            ((Ta i).toSection x) := by
          rw [hDsq, hTa_def]; ring

  have hpack :
      ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 (p + q + r) k P‖ ≤
        D * ∑ i ∈ Finset.range (k + 1), ‖Ta i‖ :=
    tensorL2Norm_le_of_pointwise_fiberNormSq_bound_sum (I := I) (M := M) g (k + 1)
      (fun i => p + (k - i)) Ta
      (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 (p + q + r) k P)
      D hD_nn hpt

  have hreindex : (∑ i ∈ Finset.range (k + 1), ‖Ta i‖) =
      ∑ i ∈ Finset.range (k + 1),
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 p i a‖ := by
    have := Finset.sum_range_reflect
      (fun i => ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 p i a‖) (k + 1)
    simpa [hTa_def, Nat.succ_sub_one] using this
  rw [hreindex] at hpack

  rw [Integral.L2.SmoothCcTensor.norm_def (I := I) (M := M)
        (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 (p + q + r) k P)] at hpack
  have hsum_a_eq : (∑ i ∈ Finset.range (k + 1),
      ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 p i a‖) =
      ∑ i ∈ Finset.range (k + 1),
        Integral.L2.tensorL2Norm (I := I) g 0 (p + i)
          (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 p i a).toFun :=
    Finset.sum_congr rfl (fun i _ => Integral.L2.SmoothCcTensor.norm_def (I := I) (M := M) _)
  rw [hsum_a_eq] at hpack
  set Sa : ℝ := ∑ i ∈ Finset.range (k + 1),
      Integral.L2.tensorL2Norm (I := I) g 0 (p + i)
        (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 p i a).toFun with hSa_def
  set Sb : ℝ := ∑ j ∈ Finset.range (k + 1),
      Integral.L2.tensorL2Norm (I := I) g 0 (q + j)
        (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 q j b).toFun with hSb_def
  set Sc : ℝ := ∑ l ∈ Finset.range (k + 1),
      Integral.L2.tensorL2Norm (I := I) g 0 (r + l)
        (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 r l c).toFun with hSc_def
  have hSa_nn : 0 ≤ Sa :=
    Finset.sum_nonneg (fun i _ => Integral.L2.tensorL2Norm_nonneg (I := I) (M := M) g 0 (p + i) _)
  have hSb_nn : 0 ≤ Sb :=
    Finset.sum_nonneg (fun j _ => Integral.L2.tensorL2Norm_nonneg (I := I) (M := M) g 0 (q + j) _)
  have hSc_nn : 0 ≤ Sc :=
    Finset.sum_nonneg (fun l _ => Integral.L2.tensorL2Norm_nonneg (I := I) (M := M) g 0 (r + l) _)
  set C : ℝ := Real.sqrt (k + 1) * (2 : ℝ) ^ (2 * k) with hC_def
  have hC_nn : 0 ≤ C := by rw [hC_def]; positivity
  have hDeq : D = C * (Λb * Λc) := by rw [hD_def, hC_def]
  calc Integral.L2.tensorL2Norm (I := I) g 0 (p + q + r + k)
          (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 (p + q + r) k P).toFun
      ≤ D * Sa := hpack
    _ = C * (Λb * Λc * Sa) := by rw [hDeq]; ring
    _ ≤ C * (Λb * Λc * Sa + Λa * Λc * Sb + Λa * Λb * Sc) := by
        have hnn1 : 0 ≤ Λa * Λc * Sb := by positivity
        have hnn2 : 0 ≤ Λa * Λb * Sc := by positivity
        apply mul_le_mul_of_nonneg_left _ hC_nn
        linarith

set_option maxHeartbeats 1600000 in
omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem exists_moserTameProduct_pi_iteratedCovGrad_l2Norm_le
    (g : SmoothRiemannianMetric I M) {n : ℕ} (hn : 0 < n) (p : Fin n → ℕ) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (c : (m : Fin n) → Integral.L2.SmoothCcTensor g 0 (p m))
        (P : Integral.L2.SmoothCcTensor g 0 (∑ m, p m)) (Λ : Fin n → ℝ) (K : ℝ),
        0 ≤ K →
        (∀ m, 0 ≤ Λ m) →
        (∀ (m : Fin n) (x : M) (i : ℕ), i ≤ k →
          riemannianFiberNormSq (I := I) (M := M) g 0 (p m + i) x
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 (p m) i (c m)).toSection x) ≤
            (Λ m) ^ 2) →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g 0 ((∑ m, p m) + k) x
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 (∑ m, p m) k P).toSection x) ≤
            K * ∑ k' ∈ Finset.range (k + 1),
                  ∑ e ∈ Finset.Nat.antidiagonalTuple n k',
                    ∏ m : Fin n,
                      riemannianFiberNormSq (I := I) (M := M) g 0 (p m + e m) x
                          ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 (p m) (e m) (c m)).toSection x)) →
        Integral.L2.tensorL2Norm (I := I) g 0 ((∑ m, p m) + k)
            (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 (∑ m, p m) k P).toFun ≤
          (C * Real.sqrt K) * ∑ m : Fin n,
                (∏ j ∈ Finset.univ.erase m, Λ j) *
                  ∑ i ∈ Finset.range (k + 1),
                    Integral.L2.tensorL2Norm (I := I) g 0 (p m + i)
                      (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 (p m) i (c m)).toFun := by
  classical
  refine ⟨Real.sqrt (∑ k' ∈ Finset.range (k + 1),
      ((Finset.Nat.antidiagonalTuple n k').card : ℝ)), by positivity, ?_⟩
  intro c P Λ K hK hΛ hjet hP
  set i₀ : Fin n := ⟨0, hn⟩ with hi₀
  set Tcard : ℝ := ∑ k' ∈ Finset.range (k + 1),
      ((Finset.Nat.antidiagonalTuple n k').card : ℝ) with hTcard
  have hTcard_nn : 0 ≤ Tcard := by rw [hTcard]; positivity
  set C : ℝ := Real.sqrt Tcard with hC
  have hC_nn : 0 ≤ C := by rw [hC]; exact Real.sqrt_nonneg _
  set sK : ℝ := Real.sqrt K with hsK
  have hsK_nn : 0 ≤ sK := by rw [hsK]; exact Real.sqrt_nonneg _
  set PΛ : ℝ := ∏ j ∈ Finset.univ.erase i₀, Λ j with hPΛ
  have hPΛ_nn : 0 ≤ PΛ := Finset.prod_nonneg (fun j _ => hΛ j)
  set D : ℝ := C * sK * PΛ with hD
  have hD_nn : 0 ≤ D := by rw [hD]; exact mul_nonneg (mul_nonneg hC_nn hsK_nn) hPΛ_nn
  have hC2 : C ^ 2 = Tcard := by rw [hC]; exact Real.sq_sqrt hTcard_nn
  have hsK2 : sK ^ 2 = K := by rw [hsK]; exact Real.sq_sqrt hK
  have hD2 : D ^ 2 = Tcard * K * PΛ ^ 2 := by
    rw [hD, mul_pow, mul_pow, hC2, hsK2]
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 ((∑ m, p m) + k) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 (∑ m, p m) k P).toSection x) ≤
        D ^ 2 * ∑ i ∈ Finset.range (k + 1),
          riemannianFiberNormSq (I := I) (M := M) g 0 (p i₀ + i) x
            ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 (p i₀) i (c i₀)).toSection x) := by
    intro x
    set Jet0 : ℝ := ∑ i ∈ Finset.range (k + 1),
        riemannianFiberNormSq (I := I) (M := M) g 0 (p i₀ + i) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 (p i₀) i (c i₀)).toSection x) with hJet0
    have hJet0_nn : 0 ≤ Jet0 :=
      Finset.sum_nonneg (fun i _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 _ x _)
    refine le_trans (hP x) ?_
    have hterm : ∀ k' ∈ Finset.range (k + 1), ∀ e ∈ Finset.Nat.antidiagonalTuple n k',
        ∏ m : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g 0 (p m + e m) x
                ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 (p m) (e m) (c m)).toSection x)
          ≤ PΛ ^ 2 * Jet0 := by
      intro k' hk' e he
      have hk'_le : k' ≤ k := by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hk'
      have hsum_e : ∑ i, e i = k' := Finset.Nat.mem_antidiagonalTuple.mp he
      have he_le : ∀ m, e m ≤ k := by
        intro m
        have hsm : e m ≤ ∑ i, e i :=
          Finset.single_le_sum (f := e) (fun i _ => Nat.zero_le _) (Finset.mem_univ _)
        rw [hsum_e] at hsm
        exact le_trans hsm hk'_le
      set f : Fin n → ℝ := fun m =>
        riemannianFiberNormSq (I := I) (M := M) g 0 (p m + e m) x
            ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 (p m) (e m) (c m)).toSection x) with hf
      have hf_nn : ∀ m, 0 ≤ f m := fun m =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 _ x _
      have herase : ∏ m ∈ Finset.univ.erase i₀, f m ≤
          ∏ m ∈ Finset.univ.erase i₀, (Λ m) ^ 2 :=
        Finset.prod_le_prod (fun m _ => hf_nn m) (fun m _ => hjet m x (e m) (he_le m))
      have hsplit : ∏ m : Fin n, f m = f i₀ * ∏ m ∈ Finset.univ.erase i₀, f m :=
        (Finset.mul_prod_erase Finset.univ f (Finset.mem_univ i₀)).symm
      have hprod_erase_nn : 0 ≤ ∏ m ∈ Finset.univ.erase i₀, f m :=
        Finset.prod_nonneg (fun m _ => hf_nn m)
      have hprodΛ_eq : ∏ m ∈ Finset.univ.erase i₀, (Λ m) ^ 2 = PΛ ^ 2 := by
        rw [Finset.prod_pow, ← hPΛ]
      have hfi0 : f i₀ ≤ Jet0 := by
        have hmem : e i₀ ∈ Finset.range (k + 1) :=
          Finset.mem_range.mpr (by have := he_le i₀; omega)
        have hss := Finset.single_le_sum
          (f := fun i => riemannianFiberNormSq (I := I) (M := M) g 0 (p i₀ + i) x
            ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 (p i₀) i (c i₀)).toSection x))
          (fun i _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 _ x _) hmem
        rw [← hJet0] at hss
        simpa [hf] using hss
      calc ∏ m : Fin n, f m
          = f i₀ * ∏ m ∈ Finset.univ.erase i₀, f m := hsplit
        _ ≤ Jet0 * PΛ ^ 2 := by
            apply mul_le_mul hfi0 _ hprod_erase_nn hJet0_nn
            rw [← hprodΛ_eq]; exact herase
        _ = PΛ ^ 2 * Jet0 := by ring
    have hinner : ∀ k' ∈ Finset.range (k + 1),
        (∑ _e ∈ Finset.Nat.antidiagonalTuple n k', PΛ ^ 2 * Jet0)
          = ((Finset.Nat.antidiagonalTuple n k').card : ℝ) * (PΛ ^ 2 * Jet0) := by
      intro k' _; rw [Finset.sum_const, nsmul_eq_mul]
    calc K * ∑ k' ∈ Finset.range (k + 1),
              ∑ e ∈ Finset.Nat.antidiagonalTuple n k',
                ∏ m : Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g 0 (p m + e m) x
                      ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 (p m) (e m) (c m)).toSection x)
        ≤ K * ∑ k' ∈ Finset.range (k + 1),
              ∑ _e ∈ Finset.Nat.antidiagonalTuple n k', PΛ ^ 2 * Jet0 := by
          apply mul_le_mul_of_nonneg_left _ hK
          apply Finset.sum_le_sum
          intro k' hk'
          apply Finset.sum_le_sum
          intro e he
          exact hterm k' hk' e he
      _ = K * (Tcard * (PΛ ^ 2 * Jet0)) := by
          rw [Finset.sum_congr rfl hinner, ← Finset.sum_mul, ← hTcard]
      _ = D ^ 2 * Jet0 := by rw [hD2]; ring
  have hpack : ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 (∑ m, p m) k P‖ ≤
      D * ∑ i ∈ Finset.range (k + 1),
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 (p i₀) i (c i₀)‖ :=
    tensorL2Norm_le_of_pointwise_fiberNormSq_bound_sum (I := I) (M := M) g (k + 1)
      (fun i => p i₀ + i)
      (fun i => PDE.RicciFlow.iteratedCovGrad (I := I) g 0 (p i₀) i (c i₀))
      (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 (∑ m, p m) k P) D hD_nn hpt
  rw [Integral.L2.SmoothCcTensor.norm_def (I := I) (M := M)
        (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 (∑ m, p m) k P)] at hpack
  have hsum0_eq : (∑ i ∈ Finset.range (k + 1),
      ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 (p i₀) i (c i₀)‖) =
      ∑ i ∈ Finset.range (k + 1),
        Integral.L2.tensorL2Norm (I := I) g 0 (p i₀ + i)
          (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 (p i₀) i (c i₀)).toFun :=
    Finset.sum_congr rfl (fun i _ => Integral.L2.SmoothCcTensor.norm_def (I := I) (M := M) _)
  rw [hsum0_eq] at hpack
  calc Integral.L2.tensorL2Norm (I := I) g 0 ((∑ m, p m) + k)
          (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 (∑ m, p m) k P).toFun
      ≤ D * ∑ i ∈ Finset.range (k + 1),
            Integral.L2.tensorL2Norm (I := I) g 0 (p i₀ + i)
              (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 (p i₀) i (c i₀)).toFun := hpack
    _ = (C * sK) * ((∏ j ∈ Finset.univ.erase i₀, Λ j) *
              ∑ i ∈ Finset.range (k + 1),
                Integral.L2.tensorL2Norm (I := I) g 0 (p i₀ + i)
                  (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 (p i₀) i (c i₀)).toFun) := by
          rw [hD, hPΛ]; ring
    _ ≤ (C * sK) * ∑ m : Fin n,
            (∏ j ∈ Finset.univ.erase m, Λ j) *
              ∑ i ∈ Finset.range (k + 1),
                Integral.L2.tensorL2Norm (I := I) g 0 (p m + i)
                  (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 (p m) i (c m)).toFun := by
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC_nn hsK_nn)
          exact Finset.single_le_sum
            (f := fun m : Fin n => (∏ j ∈ Finset.univ.erase m, Λ j) *
                ∑ i ∈ Finset.range (k + 1),
                  Integral.L2.tensorL2Norm (I := I) g 0 (p m + i)
                    (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 (p m) i (c m)).toFun)
            (fun m _ => mul_nonneg (Finset.prod_nonneg (fun j _ => hΛ j))
              (Finset.sum_nonneg (fun i _ =>
                Integral.L2.tensorL2Norm_nonneg (I := I) (M := M) g 0 _ _)))
            (Finset.mem_univ i₀)

section DiscreteLogConvex

private lemma slope_spread (Δ : ℕ → ℝ) (d : ℝ) (N : ℕ)
    (hstep : ∀ i, i < N → Δ i ≤ Δ (i + 1) + d) :
    ∀ i i' : ℕ, i ≤ i' → i' ≤ N → Δ i ≤ Δ i' + (i' - i : ℕ) * d := by
  intro i i' hii' hiN
  induction i' with
  | zero => interval_cases i; simp
  | succ n ih =>
      rcases Nat.lt_or_ge i (n + 1) with hlt | hge
      · have hin : i ≤ n := Nat.lt_succ_iff.mp hlt
        have h1 := ih hin (by omega)
        have h2 := hstep n (by omega)
        have hbody : Δ i ≤ Δ (n + 1) + d + (n - i : ℕ) * d := by
          calc Δ i ≤ Δ n + (n - i : ℕ) * d := h1
            _ ≤ (Δ (n + 1) + d) + (n - i : ℕ) * d := by linarith
        have hcast : ((n + 1 - i : ℕ) : ℝ) = (n - i : ℕ) + 1 := by
          have hn : n + 1 - i = (n - i) + 1 := by omega
          rw [hn]; push_cast; ring
        rw [hcast]; nlinarith [hbody]
      · have hie : i = n + 1 := le_antisymm hii' hge
        subst hie; simp

private lemma chord_bound (Δ : ℕ → ℝ) (d : ℝ) (hd : 0 ≤ d) (j k : ℕ)
    (hstep : ∀ i, i + 1 < k → Δ i ≤ Δ (i + 1) + d) (hj : 0 < j) (hjk : j < k) :
    (k : ℝ) * (∑ i ∈ Finset.range j, Δ i)
      ≤ (j : ℝ) * (∑ i ∈ Finset.range k, Δ i) + (k ^ 3 : ℕ) * d := by
  have hsplit : (∑ i ∈ Finset.range k, Δ i)
      = (∑ i ∈ Finset.range j, Δ i) + ∑ i ∈ Finset.Ico j k, Δ i := by
    rw [← Finset.sum_range_add_sum_Ico Δ (le_of_lt hjk)]
  rw [hsplit, mul_add]
  set Sj : ℝ := ∑ i ∈ Finset.range j, Δ i with hSj
  set Sjk : ℝ := ∑ i ∈ Finset.Ico j k, Δ i with hSjk
  have hcard1 : (Finset.Ico j k).card = k - j := by rw [Nat.card_Ico]
  have hcard2 : (Finset.range j).card = j := by rw [Finset.card_range]
  have hLHS : ((k : ℝ) - j) * Sj = ∑ _i' ∈ Finset.Ico j k, Sj := by
    rw [Finset.sum_const, hcard1, nsmul_eq_mul]
    have hc : ((k - j : ℕ) : ℝ) = (k : ℝ) - j := by rw [Nat.cast_sub (le_of_lt hjk)]
    rw [hc]
  have hRHS : (j : ℝ) * Sjk = ∑ _i ∈ Finset.range j, Sjk := by
    rw [Finset.sum_const, hcard2, nsmul_eq_mul]
  have key : ((k : ℝ) - j) * Sj - (j : ℝ) * Sjk ≤ (k ^ 3 : ℕ) * d := by
    rw [hLHS, hRHS]
    have e1 : (∑ _i' ∈ Finset.Ico j k, Sj)
        = ∑ p ∈ (Finset.range j) ×ˢ (Finset.Ico j k), Δ p.1 := by
      rw [hSj, Finset.sum_product' (f := fun (a : ℕ) (_ : ℕ) => Δ a)]
      exact (Finset.sum_comm).symm
    have e2 : (∑ _i ∈ Finset.range j, Sjk)
        = ∑ p ∈ (Finset.range j) ×ˢ (Finset.Ico j k), Δ p.2 := by
      rw [hSjk, Finset.sum_product' (f := fun (_ : ℕ) (b : ℕ) => Δ b)]
    rw [e1, e2, ← Finset.sum_sub_distrib]
    have hbound : ∀ p ∈ (Finset.range j) ×ˢ (Finset.Ico j k),
        Δ p.1 - Δ p.2 ≤ (k : ℝ) * d := by
      intro p hp
      rw [Finset.mem_product] at hp
      obtain ⟨hp1, hp2⟩ := hp
      have hi : p.1 < j := Finset.mem_range.mp hp1
      have hi' : j ≤ p.2 := (Finset.mem_Ico.mp hp2).1
      have hi'k : p.2 < k := (Finset.mem_Ico.mp hp2).2
      have hle : p.1 ≤ p.2 := le_trans (le_of_lt hi) hi'
      have hstep' : ∀ i, i < k - 1 → Δ i ≤ Δ (i + 1) + d := fun i hik => hstep i (by omega)
      have hsp := slope_spread Δ d (k - 1) hstep' p.1 p.2 hle (by omega)
      have hdiff : ((p.2 - p.1 : ℕ) : ℝ) ≤ (k : ℝ) := by
        have hpp : p.2 - p.1 ≤ k := by omega
        exact_mod_cast hpp
      have hstep2 : Δ p.1 - Δ p.2 ≤ (p.2 - p.1 : ℕ) * d := by linarith [hsp]
      calc Δ p.1 - Δ p.2 ≤ (p.2 - p.1 : ℕ) * d := hstep2
        _ ≤ (k : ℝ) * d := mul_le_mul_of_nonneg_right hdiff hd
    calc ∑ p ∈ (Finset.range j) ×ˢ (Finset.Ico j k), (Δ p.1 - Δ p.2)
        ≤ ∑ _p ∈ (Finset.range j) ×ˢ (Finset.Ico j k), (k : ℝ) * d :=
          Finset.sum_le_sum hbound
      _ = ((Finset.range j) ×ˢ (Finset.Ico j k)).card * ((k : ℝ) * d) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = ((j * (k - j) : ℕ) : ℝ) * ((k : ℝ) * d) := by
          rw [Finset.card_product, hcard1, hcard2]
      _ ≤ (k ^ 3 : ℕ) * d := by
          have hjk_le : j * (k - j) ≤ k * k := by
            calc j * (k - j) ≤ k * (k - j) := by apply Nat.mul_le_mul_right; omega
              _ ≤ k * k := by apply Nat.mul_le_mul_left; omega
          have hcastjk : ((j * (k - j) : ℕ) : ℝ) ≤ (k : ℝ) * (k : ℝ) := by exact_mod_cast hjk_le
          have hcast3 : ((k ^ 3 : ℕ) : ℝ) = (k : ℝ) * (k : ℝ) * (k : ℝ) := by push_cast; ring
          have hkd : 0 ≤ (k : ℝ) * d := mul_nonneg (by positivity) hd
          have hknn : (0 : ℝ) ≤ (k : ℝ) := by positivity
          rw [hcast3]
          nlinarith [hcastjk, hkd, hknn, hd, mul_le_mul_of_nonneg_right hcastjk hkd]
  nlinarith [key]

private lemma pos_propagate (a : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i) (M : ℝ)
    (hlc : ∀ i, (a (i + 1)) ^ 2 ≤ M * a i * a (i + 2)) (j : ℕ) (hpos : 0 < a j) :
    ∀ i, i ≤ j → 0 < a i := by
  have hL : ∀ i, 0 < a (i + 1) → 0 < a i := by
    intro i hi
    by_contra h
    rw [not_lt] at h
    have hai : a i = 0 := le_antisymm h (ha i)
    have hh := hlc i
    rw [hai] at hh
    simp only [mul_zero, zero_mul] at hh
    nlinarith [hh, hi, sq_nonneg (a (i + 1))]
  have key0 : ∀ s, s ≤ j → 0 < a (j - s) := by
    intro s
    induction s with
    | zero => intro _; simpa using hpos
    | succ m ihm =>
        intro hs
        have hjm : 0 < a (j - m) := ihm (by omega)
        have hidx : j - m = (j - (m + 1)) + 1 := by omega
        rw [hidx] at hjm
        exact hL (j - (m + 1)) hjm
  intro i hi
  have heq : i = j - (j - i) := by omega
  rw [heq]
  exact key0 (j - i) (by omega)

private lemma pos_propagate_up (a : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i) (M : ℝ)
    (hlc : ∀ i, (a (i + 1)) ^ 2 ≤ M * a i * a (i + 2)) (j : ℕ) (hj : 0 < j)
    (hpos : 0 < a j) :
    ∀ i, j ≤ i → 0 < a i := by
  have hR : ∀ i, 0 < a (i + 1) → 0 < a (i + 2) := by
    intro i hi
    by_contra h
    rw [not_lt] at h
    have hai : a (i + 2) = 0 := le_antisymm h (ha (i + 2))
    have hh := hlc i
    rw [hai] at hh
    simp only [mul_zero] at hh
    nlinarith [hh, hi, sq_nonneg (a (i + 1))]
  intro i hji
  obtain ⟨t, rfl⟩ : ∃ t, i = j + t := ⟨i - j, by omega⟩
  clear hji
  induction t with
  | zero => simpa using hpos
  | succ n ih =>
      have hjn : 0 < a (j + n) := ih
      have hidx : j + n = (j + n - 1) + 1 := by omega
      rw [hidx] at hjn
      have hRr := hR (j + n - 1) hjn
      have hidx2 : j + n - 1 + 2 = j + (n + 1) := by omega
      rw [hidx2] at hRr
      exact hRr

private theorem hlp_real (a : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i) (M : ℝ) (hM : 1 ≤ M)
    (hlc : ∀ i, (a (i + 1)) ^ 2 ≤ M * a i * a (i + 2)) (j k : ℕ) (hj : 0 < j) (hjk : j < k) :
    (a j) ^ k ≤ M ^ (k ^ 3) * (a 0) ^ (k - j) * (a k) ^ j := by
  have hM0 : 0 < M := lt_of_lt_of_le one_pos hM
  rcases eq_or_lt_of_le (ha j) with hzero | hpos
  · rw [← hzero, zero_pow (by omega)]
    have h0 : 0 ≤ a 0 := ha 0
    have hk : 0 ≤ a k := ha k
    have hMnn : 0 ≤ M := le_of_lt hM0
    positivity
  · have hposj : 0 < a j := hpos
    have hpL : ∀ i, i ≤ j → 0 < a i := pos_propagate a ha M hlc j hposj
    have hpU : ∀ i, j ≤ i → 0 < a i := pos_propagate_up a ha M hlc j hj hposj
    have hpall : ∀ i, i ≤ k → 0 < a i := by
      intro i hik
      rcases Nat.lt_or_ge i j with h | h
      · exact hpL i (le_of_lt h)
      · exact hpU i h
    set L : ℕ → ℝ := fun i => Real.log (a i) with hLdef
    set Δ : ℕ → ℝ := fun i => L (i + 1) - L i with hΔdef
    have hlogM : 0 ≤ Real.log M := Real.log_nonneg hM
    have hstep : ∀ i, i + 1 < k → Δ i ≤ Δ (i + 1) + Real.log M := by
      intro i hik
      have hi0 : 0 < a i := hpall i (by omega)
      have hi1 : 0 < a (i + 1) := hpall (i + 1) (by omega)
      have hi2 : 0 < a (i + 2) := hpall (i + 2) (by omega)
      have hlci := hlc i
      have hlog : Real.log ((a (i + 1)) ^ 2) ≤ Real.log (M * a i * a (i + 2)) :=
        Real.log_le_log (by positivity) hlci
      rw [Real.log_pow] at hlog
      rw [Real.log_mul (by positivity) (ne_of_gt hi2),
          Real.log_mul (ne_of_gt hM0) (ne_of_gt hi0)] at hlog
      simp only [hΔdef, hLdef]
      push_cast at hlog
      nlinarith [hlog]
    have hchord := chord_bound Δ (Real.log M) hlogM j k hstep hj hjk
    have htel : ∀ n, (∑ i ∈ Finset.range n, Δ i) = L n - L 0 := by
      intro n; simp only [hΔdef]; exact Finset.sum_range_sub L n
    rw [htel j, htel k] at hchord
    have hlin : (k : ℝ) * L j ≤
        ((k - j : ℕ) : ℝ) * L 0 + (j : ℝ) * L k + (k ^ 3 : ℕ) * Real.log M := by
      have hcastsub : ((k - j : ℕ) : ℝ) = (k : ℝ) - (j : ℝ) := by rw [Nat.cast_sub (le_of_lt hjk)]
      rw [hcastsub]; nlinarith [hchord]
    have hLHSpos : 0 < (a j) ^ k := by positivity
    have h0 : 0 < a 0 := hpall 0 (by omega)
    have hk : 0 < a k := hpall k (le_refl k)
    have hRHSpos : 0 < M ^ (k ^ 3) * (a 0) ^ (k - j) * (a k) ^ j := by positivity
    rw [← Real.log_le_log_iff hLHSpos hRHSpos]
    rw [Real.log_pow]
    rw [Real.log_mul (ne_of_gt (by positivity)) (ne_of_gt (by positivity)),
        Real.log_mul (ne_of_gt (by positivity)) (ne_of_gt (by positivity))]
    rw [Real.log_pow, Real.log_pow, Real.log_pow]
    simp only [hLdef] at hlin ⊢
    push_cast at hlin ⊢
    nlinarith [hlin]

end DiscreteLogConvex

private theorem exists_rawConnLap_l2Norm_le_secondCovGrad_l2Norm
    (g : SmoothRiemannianMetric I M) :
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ (s' : ℕ) (S : Integral.L2.SmoothCcTensor g 0 s'),
        Integral.L2.tensorL2Norm (I := I) g 0 s'
            (rawTensorConnLapSmooth (I := I) g 0 s' S).toFun ≤
          K * Integral.L2.tensorL2Norm (I := I) g 0 (s' + 1 + 1)
            (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad (I := I) g 0 (s' + 1)
              (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad (I := I) g 0 s' S)).toFun :=
  Integral.Connection.exists_rawConnLap_l2Norm_le_secondCovGrad_l2Norm_gen (I := I) (M := M) g

private theorem l2jet_logConvex_iteratedCovGrad
    (g : SmoothRiemannianMetric I M) (s : ℕ) :
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ (u : Integral.L2.SmoothCcTensor g 0 s) (i : ℕ),
        (Integral.L2.tensorL2Norm (I := I) g 0 (s + (i + 1))
            (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s (i + 1) u).toFun) ^ 2 ≤
          K * Integral.L2.tensorL2Norm (I := I) g 0 (s + i)
                (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s i u).toFun *
            Integral.L2.tensorL2Norm (I := I) g 0 (s + (i + 2))
              (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s (i + 2) u).toFun := by
  classical
  obtain ⟨K, hK1, htrace⟩ := exists_rawConnLap_l2Norm_le_secondCovGrad_l2Norm (I := I) (M := M) g
  refine ⟨K, hK1, ?_⟩
  intro u i

  simp only [PDE.RicciFlow.iteratedCovGrad_succ (I := I) g 0 s (i + 1) u,
    PDE.RicciFlow.iteratedCovGrad_succ (I := I) g 0 s i u]

  set S : Integral.L2.SmoothCcTensor g 0 (s + i) :=
    PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s i u with hS_def

  set aGrad : ℝ := Integral.L2.tensorL2Norm (I := I) g 0 (s + (i + 1))
    (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad (I := I) g 0 (s + i) S).toFun
    with haGrad_def
  set aS : ℝ := Integral.L2.tensorL2Norm (I := I) g 0 (s + i) S.toFun with haS_def
  set aHess : ℝ := Integral.L2.tensorL2Norm (I := I) g 0 (s + (i + 2))
    (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad (I := I) g 0 (s + (i + 1))
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad (I := I) g 0 (s + i) S)).toFun
    with haHess_def
  have haS_nn : 0 ≤ aS := Integral.L2.tensorL2Norm_nonneg (I := I) (M := M) g 0 (s + i) _

  have hibp : aGrad ^ 2 ≤
      Integral.L2.tensorL2Norm (I := I) g 0 (s + i)
          (rawTensorConnLapSmooth (I := I) g 0 (s + i) S).toFun * aS := by
    rw [haGrad_def, haS_def]
    exact covGrad_l2NormSq_le_rawConnLap_mul_self_gen (I := I) (M := M) g (s + i) S

  have htr : Integral.L2.tensorL2Norm (I := I) g 0 (s + i)
        (rawTensorConnLapSmooth (I := I) g 0 (s + i) S).toFun ≤ K * aHess := by
    rw [haHess_def]
    exact htrace (s + i) S

  calc aGrad ^ 2
      ≤ Integral.L2.tensorL2Norm (I := I) g 0 (s + i)
          (rawTensorConnLapSmooth (I := I) g 0 (s + i) S).toFun * aS := hibp
    _ ≤ (K * aHess) * aS := mul_le_mul_of_nonneg_right htr haS_nn
    _ = K * aS * aHess := by ring

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [I.Boundaryless] in
private theorem l2Norm_le_sup_mul_sqrt_vol
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (u : Integral.L2.SmoothCcTensor g 0 s) (Λ₀ : ℝ) (hΛ₀ : 0 ≤ Λ₀)
    (hsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 s x (u.toSection x) ≤ Λ₀ ^ 2) :
    Integral.L2.tensorL2Norm (I := I) g 0 s u.toFun ≤
      Λ₀ * Real.sqrt ((Integral.Measure.riemannianVolumeMeasure I M g) Set.univ).toReal := by
  classical
  have hfin : MeasureTheory.IsFiniteMeasure (Integral.Measure.riemannianVolumeMeasure I M g) :=
    Integral.Measure.riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  set μ := Integral.Measure.riemannianVolumeMeasure I M g with hμ
  set V : ℝ := (μ Set.univ).toReal with hV
  have hVnn : 0 ≤ V := ENNReal.toReal_nonneg

  have hsq := tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g s u

  have hint_mono : (∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 s x (u.toSection x) ∂μ)
      ≤ ∫ _x : M, Λ₀ ^ 2 ∂μ := by
    apply MeasureTheory.integral_mono
    · exact integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g 0 s u
    · exact MeasureTheory.integrable_const _
    · exact hsup
  have hconst : (∫ _x : M, Λ₀ ^ 2 ∂μ) = V * Λ₀ ^ 2 := by
    rw [MeasureTheory.integral_const, smul_eq_mul, hV, MeasureTheory.measureReal_def]
  have hsq_le : Integral.L2.tensorL2Norm (I := I) g 0 s u.toFun ^ 2 ≤ V * Λ₀ ^ 2 := by
    rw [hsq]; rw [hconst] at hint_mono; exact hint_mono

  have hnn : 0 ≤ Integral.L2.tensorL2Norm (I := I) g 0 s u.toFun :=
    Integral.L2.tensorL2Norm_nonneg (I := I) (M := M) g 0 s _
  have hrhs_nn : 0 ≤ Λ₀ * Real.sqrt V := mul_nonneg hΛ₀ (Real.sqrt_nonneg V)
  rw [← Real.sqrt_sq hnn]
  rw [show Λ₀ * Real.sqrt V = Real.sqrt (Λ₀ ^ 2 * V) by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hΛ₀]]
  apply Real.sqrt_le_sqrt
  rw [mul_comm (Λ₀ ^ 2) V]; exact hsq_le

private theorem l2Interp_pow_iteratedCovGrad
    (g : SmoothRiemannianMetric I M) (s k : ℕ) (_hk : 1 ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (u : Integral.L2.SmoothCcTensor g 0 s) (Λ₀ : ℝ), 0 ≤ Λ₀ →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 s x (u.toSection x) ≤ Λ₀ ^ 2) →
        ∀ j : ℕ, 0 < j → j < k →
          (Integral.L2.tensorL2Norm (I := I) g 0 (s + j)
              (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s j u).toFun) ^ k ≤
            C ^ k * Λ₀ ^ (k - j) *
              (Integral.L2.tensorL2Norm (I := I) g 0 (s + k)
                  (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s k u).toFun) ^ j := by
  classical
  obtain ⟨K, hK1, hlc⟩ := l2jet_logConvex_iteratedCovGrad (I := I) (M := M) g s
  set V : ℝ := Real.sqrt ((Integral.Measure.riemannianVolumeMeasure I M g) Set.univ).toReal with hV
  have hVnn : 0 ≤ V := Real.sqrt_nonneg _
  have hmax1 : (1 : ℝ) ≤ max 1 V := le_max_left _ _
  have hmaxV : V ≤ max 1 V := le_max_right _ _
  have hmax_nn : 0 ≤ max 1 V := le_trans zero_le_one hmax1
  set C : ℝ := K ^ (k ^ 2) * max 1 V with hC
  have hC_nn : 0 ≤ C := by
    have hKnn : 0 ≤ K := le_trans zero_le_one hK1
    rw [hC]; positivity
  refine ⟨C, hC_nn, ?_⟩
  intro u Λ₀ hΛ₀ hsup j hj0 hjk

  set a : ℕ → ℝ := fun i =>
    Integral.L2.tensorL2Norm (I := I) g 0 (s + i)
      (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s i u).toFun with ha_def
  have ha_nn : ∀ i, 0 ≤ a i := fun i =>
    Integral.L2.tensorL2Norm_nonneg (I := I) (M := M) g 0 (s + i) _

  have ha_lc : ∀ i, (a (i + 1)) ^ 2 ≤ K * a i * a (i + 2) := fun i => hlc u i

  have hpow : (a j) ^ k ≤ K ^ (k ^ 3) * (a 0) ^ (k - j) * (a k) ^ j :=
    hlp_real a ha_nn K hK1 ha_lc j k hj0 hjk

  have ha0_eq : a 0 = Integral.L2.tensorL2Norm (I := I) g 0 s u.toFun := by
    rw [ha_def]
    simp only [Nat.add_zero]
    rw [PDE.RicciFlow.iteratedCovGrad_zero (I := I) g 0 s u]
  have ha0_le : a 0 ≤ Λ₀ * V := by
    rw [ha0_eq, hV]
    exact l2Norm_le_sup_mul_sqrt_vol (I := I) (M := M) g s u Λ₀ hΛ₀ hsup

  have ha0_pow : (a 0) ^ (k - j) ≤ (Λ₀ * V) ^ (k - j) :=
    pow_le_pow_left₀ (ha_nn 0) ha0_le (k - j)

  have hΛ₀V_nn : 0 ≤ Λ₀ * V := mul_nonneg hΛ₀ hVnn
  have hak_pow_nn : 0 ≤ (a k) ^ j := pow_nonneg (ha_nn k) j
  have hKpow_nn : 0 ≤ K ^ (k ^ 3) := pow_nonneg (le_trans zero_le_one hK1) _

  have hKV_le_Ck : K ^ (k ^ 3) * V ^ (k - j) ≤ C ^ k := by
    have hVpow : V ^ (k - j) ≤ (max 1 V) ^ k := by
      calc V ^ (k - j) ≤ (max 1 V) ^ (k - j) := pow_le_pow_left₀ hVnn hmaxV (k - j)
        _ ≤ (max 1 V) ^ k := pow_le_pow_right₀ hmax1 (by omega)
    have hexp : k ^ 2 * k = k ^ 3 := by ring
    have hCk : C ^ k = K ^ (k ^ 3) * (max 1 V) ^ k := by
      rw [hC, mul_pow, ← pow_mul, hexp]
    rw [hCk]
    apply mul_le_mul_of_nonneg_left hVpow hKpow_nn

  calc (a j) ^ k ≤ K ^ (k ^ 3) * (a 0) ^ (k - j) * (a k) ^ j := hpow
    _ ≤ K ^ (k ^ 3) * (Λ₀ * V) ^ (k - j) * (a k) ^ j := by
        apply mul_le_mul_of_nonneg_right _ hak_pow_nn
        apply mul_le_mul_of_nonneg_left ha0_pow hKpow_nn
    _ = (K ^ (k ^ 3) * V ^ (k - j)) * Λ₀ ^ (k - j) * (a k) ^ j := by
        rw [mul_pow]; ring
    _ ≤ C ^ k * Λ₀ ^ (k - j) * (a k) ^ j := by
        apply mul_le_mul_of_nonneg_right _ hak_pow_nn
        apply mul_le_mul_of_nonneg_right hKV_le_Ck (by positivity)

theorem exists_gagliardoNirenberg_iteratedCovGrad_l2Norm_le
    (g : SmoothRiemannianMetric I M) (s k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (u : Integral.L2.SmoothCcTensor g 0 s) (Λ₀ : ℝ), 0 ≤ Λ₀ →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 s x (u.toSection x) ≤ Λ₀ ^ 2) →
        ∀ j : ℕ, 0 < j → j < k →
          Integral.L2.tensorL2Norm (I := I) g 0 (s + j)
              (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s j u).toFun ≤
            C * Λ₀ ^ (1 - (j : ℝ) / k) *
              (Integral.L2.tensorL2Norm (I := I) g 0 (s + k)
                  (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s k u).toFun) ^ ((j : ℝ) / k) := by
  obtain ⟨C, hC0, hC⟩ := l2Interp_pow_iteratedCovGrad (I := I) (M := M) g s k hk
  refine ⟨C, hC0, ?_⟩
  intro u Λ₀ hΛ₀ hsup j hj0 hjk
  have hk0 : (k : ℕ) ≠ 0 := by omega
  set aj : ℝ := Integral.L2.tensorL2Norm (I := I) g 0 (s + j)
    (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s j u).toFun with haj_def
  set ak : ℝ := Integral.L2.tensorL2Norm (I := I) g 0 (s + k)
    (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s k u).toFun with hak_def
  have haj_nn : 0 ≤ aj :=
    Integral.L2.tensorL2Norm_nonneg (I := I) (M := M) g 0 (s + j) _
  have hak_nn : 0 ≤ ak :=
    Integral.L2.tensorL2Norm_nonneg (I := I) (M := M) g 0 (s + k) _

  have hpow : aj ^ k ≤ C ^ k * Λ₀ ^ (k - j) * ak ^ j := hC u Λ₀ hΛ₀ hsup j hj0 hjk

  have hmono : (aj ^ k) ^ ((k : ℝ)⁻¹) ≤ (C ^ k * Λ₀ ^ (k - j) * ak ^ j) ^ ((k : ℝ)⁻¹) :=
    Real.rpow_le_rpow (by positivity) hpow (by positivity)
  rw [Real.pow_rpow_inv_natCast haj_nn hk0] at hmono

  have hcast_sub : ((k - j : ℕ) : ℝ) = (k : ℝ) - (j : ℝ) := by
    rw [Nat.cast_sub (le_of_lt hjk)]
  have hexp1 : ((k : ℝ) - (j : ℝ)) * (k : ℝ)⁻¹ = 1 - (j : ℝ) / k := by
    have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk0
    field_simp
  have hrhs : (C ^ k * Λ₀ ^ (k - j) * ak ^ j) ^ ((k : ℝ)⁻¹) =
      C * Λ₀ ^ (1 - (j : ℝ) / k) * ak ^ ((j : ℝ) / k) := by
    rw [Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow (by positivity) (by positivity)]
    rw [Real.pow_rpow_inv_natCast hC0 hk0]
    congr 1
    · rw [← Real.rpow_natCast Λ₀ (k - j), ← Real.rpow_mul hΛ₀, hcast_sub, hexp1]
    · rw [← Real.rpow_natCast ak j, ← Real.rpow_mul hak_nn, div_eq_mul_inv]
  rw [hrhs] at hmono
  exact hmono

end DifferentialGeometry.Analysis.Sobolev.Tensor
