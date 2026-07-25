import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.BalancedPairing
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.AppCcDropIteratedGrid
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.ParametricAppCcJetBound










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

local instance : CompleteSpace E := FiniteDimensional.complete ℝ E





theorem slot_pair_step (g : SmoothRiemannianMetric I M) (σ k : ℕ)
    (C : SmoothCcTensor g σ σ) (V : SmoothCcTensor g 0 σ) :
    tensorL2Inner (I := I) (M := M) g 0 σ
        (oneMinusConnLapSmoothIter (I := I) g 0 σ (k + 1) V).toFun
        (ccOperatorFieldComp (I := I) (M := M) g 0 σ σ C V).toFun =
      tensorL2Inner (I := I) (M := M) g 0 σ
          (oneMinusConnLapSmoothIter (I := I) g 0 σ k V).toFun
          (ccOperatorFieldComp (I := I) (M := M) g 0 σ σ C V).toFun +
        tensorL2Inner (I := I) (M := M) g 0 (σ + 1)
          (oneMinusConnLapSmoothIter (I := I) g 0 (σ + 1) k
              (covGrad (I := I) (M := M) g 0 σ V) +
            ∑ i ∈ Finset.range k,
              oneMinusConnLapSmoothIter (I := I) g 0 (σ + 1) i
                (pointwiseTensorCurv (I := I) (M := M) g σ
                  (oneMinusConnLapSmoothIter (I := I) g 0 σ (k - 1 - i) V))).toFun
          (ccOperatorFieldComp (I := I) (M := M) g 0 σ (σ + 1)
              (covGrad (I := I) (M := M) g σ σ C) V +
            ccOperatorFieldComp (I := I) (M := M) g 0 (σ + 1) (σ + 1)
              (slotExtend (I := I) (M := M) g σ σ C)
              (covGrad (I := I) (M := M) g 0 σ V)).toFun := by
  rw [oneMinusConnLapSmoothIter_succ]
  rw [oneMinusConnLapSmooth_l2Inner_eq_add_covGrad
    (I := I) (M := M) g 0 σ]
  rw [covGrad_iterL (I := I) (M := M) g σ k V]
  rw [covGrad_appCcRS_eq (I := I) (M := M) g 0 σ σ C V]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] in
private theorem l2_zero_left (g : SmoothRiemannianMetric I M) (σ : ℕ)
    (Z : SmoothCcTensor g 0 σ) :
    tensorL2Inner (I := I) (M := M) g 0 σ
        (0 : SmoothCcTensor g 0 σ).toFun Z.toFun = 0 := by
  rw [SmoothCcTensor.toFun_zero]
  exact tensorL2Inner_zero_left (I := I) (M := M) g 0 σ Z.toFun

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] in
private theorem l2_add_left (g : SmoothRiemannianMetric I M) (σ : ℕ)
    (A B Z : SmoothCcTensor g 0 σ) :
    tensorL2Inner (I := I) (M := M) g 0 σ (A + B).toFun Z.toFun =
      tensorL2Inner (I := I) (M := M) g 0 σ A.toFun Z.toFun +
        tensorL2Inner (I := I) (M := M) g 0 σ B.toFun Z.toFun := by
  rw [SmoothCcTensor.toFun_add]
  exact tensorL2Inner_add_left (I := I) (M := M) g 0 σ A.toFun B.toFun Z.toFun
    (SmoothCcTensor.integrable_inner_cross (I := I) (M := M) A Z)
    (SmoothCcTensor.integrable_inner_cross (I := I) (M := M) B Z)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] in
private theorem l2_add_right (g : SmoothRiemannianMetric I M) (σ : ℕ)
    (Z A B : SmoothCcTensor g 0 σ) :
    tensorL2Inner (I := I) (M := M) g 0 σ Z.toFun (A + B).toFun =
      tensorL2Inner (I := I) (M := M) g 0 σ Z.toFun A.toFun +
        tensorL2Inner (I := I) (M := M) g 0 σ Z.toFun B.toFun := by
  rw [SmoothCcTensor.toFun_add]
  exact tensorL2Inner_add_right (I := I) (M := M) g 0 σ Z.toFun A.toFun B.toFun
    (SmoothCcTensor.integrable_inner_cross (I := I) (M := M) Z A)
    (SmoothCcTensor.integrable_inner_cross (I := I) (M := M) Z B)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] in
private theorem l2_sum_left (g : SmoothRiemannianMetric I M) (σ c : ℕ)
    (f : ℕ → SmoothCcTensor g 0 σ) (Z : SmoothCcTensor g 0 σ) :
    tensorL2Inner (I := I) (M := M) g 0 σ
        (∑ i ∈ Finset.range c, f i).toFun Z.toFun =
      ∑ i ∈ Finset.range c,
        tensorL2Inner (I := I) (M := M) g 0 σ (f i).toFun Z.toFun := by
  induction c with
  | zero =>
      rw [Finset.range_zero, Finset.sum_empty, Finset.sum_empty]
      exact l2_zero_left (I := I) (M := M) g σ Z
  | succ d ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ,
        l2_add_left (I := I) (M := M) g σ
          (∑ i ∈ Finset.range d, f i) (f d) Z, ih]

private def slotEnergy (g : SmoothRiemannianMetric I M) (σ k : ℕ)
    (C : SmoothCcTensor g σ σ) (V : SmoothCcTensor g 0 σ) : ℝ :=
  tensorL2Inner (I := I) (M := M) g 0 σ
    (oneMinusConnLapSmoothIter (I := I) g 0 σ k V).toFun
    (ccOperatorFieldComp (I := I) (M := M) g 0 σ σ C V).toFun

private def slotStage (g : SmoothRiemannianMetric I M) (σ m k : ℕ)
    (C : SmoothCcTensor g σ σ) (V : SmoothCcTensor g 0 σ) : ℝ :=
  slotEnergy (I := I) (M := M) g (σ + m) k
    (slotExtendIter (I := I) (M := M) g σ σ m C)
    (iteratedCovGrad (I := I) g 0 σ m V)

private theorem slot_step_exp (g : SmoothRiemannianMetric I M) (σ k : ℕ)
    (C : SmoothCcTensor g σ σ) (V : SmoothCcTensor g 0 σ) :
    slotEnergy (I := I) (M := M) g σ (k + 1) C V =
      slotEnergy (I := I) (M := M) g σ k C V +
      tensorL2Inner (I := I) (M := M) g 0 (σ + 1)
        (oneMinusConnLapSmoothIter (I := I) g 0 (σ + 1) k
          (covGrad (I := I) (M := M) g 0 σ V)).toFun
        (ccOperatorFieldComp (I := I) (M := M) g 0 σ (σ + 1)
          (covGrad (I := I) (M := M) g σ σ C) V).toFun +
      slotEnergy (I := I) (M := M) g (σ + 1) k
        (slotExtend (I := I) (M := M) g σ σ C)
        (covGrad (I := I) (M := M) g 0 σ V) +
      ∑ i ∈ Finset.range k,
        tensorL2Inner (I := I) (M := M) g 0 (σ + 1)
          (oneMinusConnLapSmoothIter (I := I) g 0 (σ + 1) i
            (pointwiseTensorCurv (I := I) (M := M) g σ
              (oneMinusConnLapSmoothIter (I := I) g 0 σ (k - 1 - i) V))).toFun
          (ccOperatorFieldComp (I := I) (M := M) g 0 σ (σ + 1)
            (covGrad (I := I) (M := M) g σ σ C) V).toFun +
      ∑ i ∈ Finset.range k,
        tensorL2Inner (I := I) (M := M) g 0 (σ + 1)
          (oneMinusConnLapSmoothIter (I := I) g 0 (σ + 1) i
            (pointwiseTensorCurv (I := I) (M := M) g σ
              (oneMinusConnLapSmoothIter (I := I) g 0 σ (k - 1 - i) V))).toFun
          (ccOperatorFieldComp (I := I) (M := M) g 0 (σ + 1) (σ + 1)
            (slotExtend (I := I) (M := M) g σ σ C)
            (covGrad (I := I) (M := M) g 0 σ V)).toFun := by
  rw [slotEnergy, slot_pair_step (I := I) (M := M) g σ k C V]
  rw [l2_add_left (I := I) (M := M) g (σ + 1)]
  rw [l2_add_right (I := I) (M := M) g (σ + 1),
    l2_add_right (I := I) (M := M) g (σ + 1)]
  rw [l2_sum_left (I := I) (M := M) g (σ + 1),
    l2_sum_left (I := I) (M := M) g (σ + 1)]
  unfold slotEnergy
  ring

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem jet_comp_norm (g : SmoothRiemannianMetric I M) (σ m p : ℕ)
    (V : SmoothCcTensor g 0 σ) :
    ‖iteratedCovGrad (I := I) g 0 (σ + m) p
        (iteratedCovGrad (I := I) g 0 σ m V)‖ =
      ‖iteratedCovGrad (I := I) g 0 σ (m + p) V‖ := by
  have hleft : ‖iteratedCovGrad (I := I) g 0 (σ + m) p
      (iteratedCovGrad (I := I) g 0 σ m V)‖ =
      tensorL2Norm (I := I) (M := M) g 0 ((σ + m) + p)
        (iteratedCovGrad (I := I) g 0 (σ + m) p
          (iteratedCovGrad (I := I) g 0 σ m V)).toFun :=
    SmoothCcTensor.norm_def (I := I) (M := M) _
  have hright : ‖iteratedCovGrad (I := I) g 0 σ (m + p) V‖ =
      tensorL2Norm (I := I) (M := M) g 0 (σ + (m + p))
        (iteratedCovGrad (I := I) g 0 σ (m + p) V).toFun :=
    SmoothCcTensor.norm_def (I := I) (M := M) _
  have hsq : ‖iteratedCovGrad (I := I) g 0 (σ + m) p
        (iteratedCovGrad (I := I) g 0 σ m V)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g 0 σ (m + p) V‖ ^ 2 := by
    rw [hleft, hright,
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq
        (I := I) (M := M) g ((σ + m) + p)
        (iteratedCovGrad (I := I) g 0 (σ + m) p
          (iteratedCovGrad (I := I) g 0 σ m V)),
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq
        (I := I) (M := M) g (σ + (m + p))
        (iteratedCovGrad (I := I) g 0 σ (m + p) V)]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    exact riemannianFiberNormSq_iteratedCovGrad_comp (I := I) (M := M) g 0 σ m p V x
  have hleft_nn : 0 ≤ ‖iteratedCovGrad (I := I) g 0 (σ + m) p
      (iteratedCovGrad (I := I) g 0 σ m V)‖ := norm_nonneg _
  have hright_nn : 0 ≤ ‖iteratedCovGrad (I := I) g 0 σ (m + p) V‖ := norm_nonneg _
  rw [← Real.sqrt_sq hleft_nn, ← Real.sqrt_sq hright_nn, hsq]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem jet_shift_le (g : SmoothRiemannianMetric I M) (σ m c : ℕ)
    (V : SmoothCcTensor g 0 σ) :
    ∑ p ∈ Finset.range c,
        ‖iteratedCovGrad (I := I) g 0 (σ + m) p
          (iteratedCovGrad (I := I) g 0 σ m V)‖ ≤
      ∑ j ∈ Finset.range (c + m),
        ‖iteratedCovGrad (I := I) g 0 σ j V‖ := by
  have hterm : ∀ p ∈ Finset.range c,
      ‖iteratedCovGrad (I := I) g 0 (σ + m) p
          (iteratedCovGrad (I := I) g 0 σ m V)‖ =
        ‖iteratedCovGrad (I := I) g 0 σ (m + p) V‖ :=
    fun p _ => jet_comp_norm (I := I) (M := M) g σ m p V
  rw [Finset.sum_congr rfl hterm]
  have hIco : ∑ p ∈ Finset.range c,
      ‖iteratedCovGrad (I := I) g 0 σ (m + p) V‖ =
      ∑ j ∈ Finset.Ico m (m + c),
        ‖iteratedCovGrad (I := I) g 0 σ j V‖ := by
    rw [Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr ?_ (fun p _ => rfl)
    congr 1
    omega
  rw [hIco]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun j _ _ => norm_nonneg _)
  intro j hj
  rw [Finset.mem_Ico] at hj
  rw [Finset.mem_range]
  omega

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem jet_one_win (g : SmoothRiemannianMetric I M) (σ m : ℕ)
    (V : SmoothCcTensor g 0 σ) (p : ℕ) :
    ‖iteratedCovGrad (I := I) g 0 (σ + m) p
        (iteratedCovGrad (I := I) g 0 σ m V)‖ ≤
      (1 : ℝ) * ∑ j ∈ Finset.range (p + m + 1),
        ‖iteratedCovGrad (I := I) g 0 σ j V‖ := by
  rw [one_mul, jet_comp_norm (I := I) (M := M) g σ m p V]
  refine Finset.single_le_sum
    (f := fun j : ℕ => ‖iteratedCovGrad (I := I) g 0 σ j V‖)
    (fun j _ => norm_nonneg _) ?_
  rw [Finset.mem_range]
  omega

private def ShiftWin (g : SmoothRiemannianMetric I M)
    (sigma m c : ℕ) (Phi : SmoothCcTensor g (sigma + m) c)
    (cc : ℕ → ℝ) : Prop :=
  ∀ (V : SmoothCcTensor g 0 sigma) (p : ℕ),
    ‖iteratedCovGrad (I := I) g 0 c p
      (ccOperatorFieldComp (I := I) (M := M) g 0 (sigma + m) c Phi
        (iteratedCovGrad (I := I) g 0 sigma m V))‖ ≤
      cc p * ∑ j ∈ Finset.range (p + m + 1),
        ‖iteratedCovGrad (I := I) g 0 sigma j V‖

omit [NeZero (Module.finrank ℝ E)] in
private theorem app_shift_win (g : SmoothRiemannianMetric I M)
    (σ m c : ℕ) (Φ : SmoothCcTensor g (σ + m) c) :
    ∃ cc : ℕ → ℝ, (∀ p, 0 ≤ cc p) ∧
      ShiftWin (I := I) (M := M) g σ m c Φ cc := by
  obtain ⟨cc, hcc_nn, hcc⟩ :=
    exists_appCc_iteratedCovGrad_l2_window_bound
      (I := I) (M := M) g (σ + m) c Φ
  refine ⟨cc, hcc_nn, fun V p => ?_⟩
  rw [appCcRS_zero_eq_appCc (I := I) (M := M) g (σ + m) c]
  refine le_trans (hcc (iteratedCovGrad (I := I) g 0 σ m V) p) ?_
  refine mul_le_mul_of_nonneg_left ?_ (hcc_nn p)
  have hshift := jet_shift_le (I := I) (M := M) g σ m (p + 1) V
  rw [show p + 1 + m = p + m + 1 from by omega] at hshift
  exact hshift

private theorem shift_win_of_bdd (g : SmoothRiemannianMetric I M)
    (sigma m c : ℕ) {α : Type*} (Phi : α → SmoothCcTensor g (sigma + m) c)
    (A : Set α) (B : ℕ → ℝ) (hB_nn : ∀ i, 0 ≤ B i)
    (hB : ∀ i t, t ∈ A → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g (sigma + m) (c + i) x
        ((iteratedCovGrad (I := I) g (sigma + m) c i (Phi t)).toSection x) ≤ B i) :
    ∃ cc : ℕ → ℝ, (∀ p, 0 ≤ cc p) ∧ ∀ t, t ∈ A →
      ShiftWin (I := I) (M := M) g sigma m c (Phi t) cc := by
  obtain ⟨cc, hcc_nn, hcc⟩ :=
    app_jet_of_bdd (I := I) (M := M) g (sigma + m) c Phi A B hB_nn hB
  refine ⟨cc, hcc_nn, fun t ht V p => ?_⟩
  rw [appCcRS_zero_eq_appCc (I := I) (M := M) g (sigma + m) c]
  refine le_trans (hcc t ht (iteratedCovGrad (I := I) g 0 sigma m V) p) ?_
  refine mul_le_mul_of_nonneg_left ?_ (hcc_nn p)
  have hshift := jet_shift_le (I := I) (M := M) g sigma m (p + 1) V
  rw [show p + 1 + m = p + m + 1 from by omega] at hshift
  exact hshift

private theorem slot_iter_bdd (g : SmoothRiemannianMetric I M) (sigma : ℕ)
    {α : Type*} (C : α → SmoothCcTensor g sigma sigma) (A : Set α)
    (B : ℕ → ℝ)
    (hB : ∀ i t, t ∈ A → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g sigma (sigma + i) x
        ((iteratedCovGrad (I := I) g sigma sigma i (C t)).toSection x) ≤ B i) :
    ∀ m i t, t ∈ A → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g (sigma + m) ((sigma + m) + i) x
        ((iteratedCovGrad (I := I) g (sigma + m) (sigma + m) i
          (slotExtendIter (I := I) (M := M) g sigma sigma m (C t))).toSection x) ≤
        (Module.finrank ℝ E : ℝ) ^ m * B i := by
  intro m
  induction m with
  | zero =>
      intro i t ht x
      simpa only [slotExtendIter, Nat.add_zero, pow_zero, one_mul] using hB i t ht x
  | succ m ih =>
      intro i t ht x
      have hslot := rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g
        (sigma + m) (sigma + m)
        (slotExtendIter (I := I) (M := M) g sigma sigma m (C t)) i x
      have hprev := ih i t ht x
      calc
        riemannianFiberNormSq (I := I) (M := M) g
              (sigma + Nat.succ m) ((sigma + Nat.succ m) + i) x
              ((iteratedCovGrad (I := I) g (sigma + Nat.succ m)
                (sigma + Nat.succ m) i
                (slotExtendIter (I := I) (M := M) g sigma sigma
                  (Nat.succ m) (C t))).toSection x) ≤
            (Module.finrank ℝ E : ℝ) *
              riemannianFiberNormSq (I := I) (M := M) g
                (sigma + m) ((sigma + m) + i) x
                ((iteratedCovGrad (I := I) g (sigma + m) (sigma + m) i
                  (slotExtendIter (I := I) (M := M) g sigma sigma m
                    (C t))).toSection x) := by
              simpa only [slotExtendIter, Nat.succ_eq_add_one, Nat.add_assoc] using hslot
        _ ≤ (Module.finrank ℝ E : ℝ) *
              ((Module.finrank ℝ E : ℝ) ^ m * B i) :=
            mul_le_mul_of_nonneg_left hprev (by positivity)
        _ = (Module.finrank ℝ E : ℝ) ^ Nat.succ m * B i := by
            rw [pow_succ]
            ring

private theorem abs_add4 (a b c d : ℝ) :
    |a + b + c + d| ≤ |a| + |b| + |c| + |d| := by
  calc
    |a + b + c + d| ≤ |a + b + c| + |d| := abs_add_le _ _
    _ ≤ |a + b| + |c| + |d| := by
      linarith [abs_add_le (a + b) c]
    _ ≤ |a| + |b| + |c| + |d| := by
      linarith [abs_add_le a b]

private theorem slot_stage_unif (g : SmoothRiemannianMetric I M)
    (σ m k : ℕ) {α : Type*} (C : α → SmoothCcTensor g σ σ) (A : Set α)
    (cC cD cE : ℕ → ℝ) (hcC_nn : ∀ p, 0 ≤ cC p)
    (hcD_nn : ∀ p, 0 ≤ cD p) (hcE_nn : ∀ p, 0 ≤ cE p)
    (hcC : ∀ t, t ∈ A → ShiftWin (I := I) (M := M) g σ m (σ + m)
      (slotExtendIter (I := I) (M := M) g σ σ m (C t)) cC)
    (hcD : ∀ t, t ∈ A → ShiftWin (I := I) (M := M) g σ m ((σ + m) + 1)
      (covGrad (I := I) (M := M) g (σ + m) (σ + m)
        (slotExtendIter (I := I) (M := M) g σ σ m (C t))) cD)
    (hcE : ∀ t, t ∈ A → ShiftWin (I := I) (M := M) g σ (m + 1) ((σ + m) + 1)
      (slotExtend (I := I) (M := M) g (σ + m) (σ + m)
        (slotExtendIter (I := I) (M := M) g σ σ m (C t))) cE) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t, t ∈ A → ∀ V : SmoothCcTensor g 0 σ,
      |slotStage (I := I) (M := M) g σ m (k + 1) (C t) V -
        slotStage (I := I) (M := M) g σ (m + 1) k (C t) V| ≤
      K * ((∑ j ∈ Finset.range (m + k + 1),
          ‖iteratedCovGrad (I := I) g 0 σ j V‖) *
        (∑ j ∈ Finset.range (m + k + 2),
          ‖iteratedCovGrad (I := I) g 0 σ j V‖)) := by
  classical
  let Cm : α → SmoothCcTensor g (σ + m) (σ + m) := fun t =>
    slotExtendIter (I := I) (M := M) g σ σ m (C t)
  let D : α → SmoothCcTensor g (σ + m) ((σ + m) + 1) := fun t =>
    covGrad (I := I) (M := M) g (σ + m) (σ + m) (Cm t)
  let E₁ : α → SmoothCcTensor g ((σ + m) + 1) ((σ + m) + 1) := fun t =>
    slotExtend (I := I) (M := M) g (σ + m) (σ + m) (Cm t)
  obtain ⟨CZ, hCZ_nn, hCZ⟩ :=
    iterL_window_pair (I := I) (M := M) g σ (σ + m) k (k / 2)
      m m (m + k + 1) (m + k) (by omega) (by omega) (by omega)
      (fun _ => 1) cC (fun _ => zero_le_one) hcC_nn
  have hADEx : ∃ CAD : ℝ, 0 ≤ CAD ∧ ∀ t, t ∈ A →
      ∀ V : SmoothCcTensor g 0 σ,
      |tensorL2Inner (I := I) (M := M) g 0 ((σ + m) + 1)
        (oneMinusConnLapSmoothIter (I := I) g 0 ((σ + m) + 1) k
          (iteratedCovGrad (I := I) g 0 σ (m + 1) V)).toFun
        (ccOperatorFieldComp (I := I) (M := M) g 0 (σ + m) ((σ + m) + 1) (D t)
          (iteratedCovGrad (I := I) g 0 σ m V)).toFun| ≤
        CAD * ((∑ j ∈ Finset.range (m + k + 1),
            ‖iteratedCovGrad (I := I) g 0 σ j V‖) *
          (∑ j ∈ Finset.range (m + k + 2),
            ‖iteratedCovGrad (I := I) g 0 σ j V‖)) := by
    by_cases hsmall : 2 * ((k + 1) / 2) ≤ k
    · obtain ⟨CAD, hCAD_nn, hCAD⟩ :=
        iterL_window_pair (I := I) (M := M) g σ ((σ + m) + 1) k
          ((k + 1) / 2) (m + 1) m (m + k + 1) (m + k)
          (by omega) (by omega) (by omega)
          (fun _ => 1) cD (fun _ => zero_le_one) hcD_nn
      refine ⟨CAD, hCAD_nn, fun t ht V => ?_⟩
      have h := hCAD V
        (iteratedCovGrad (I := I) g 0 σ (m + 1) V)
        (ccOperatorFieldComp (I := I) (M := M) g 0 (σ + m) ((σ + m) + 1) (D t)
          (iteratedCovGrad (I := I) g 0 σ m V))
        (fun p => jet_one_win (I := I) (M := M) g σ (m + 1) V p)
        (hcD t ht V)
      rw [show m + k + 1 + 1 = m + k + 2 from by omega,
        show m + k + 1 = m + k + 1 from rfl] at h
      exact le_trans h (le_of_eq (by ring))
    · obtain ⟨CAD, hCAD_nn, hCAD⟩ :=
        iterL_window_pair (I := I) (M := M) g σ ((σ + m) + 1) k
          ((k + 1) / 2) (m + 1) m (m + k) (m + k + 1)
          (by omega) (by omega) (by omega)
          (fun _ => 1) cD (fun _ => zero_le_one) hcD_nn
      refine ⟨CAD, hCAD_nn, fun t ht V => ?_⟩
      have h := hCAD V
        (iteratedCovGrad (I := I) g 0 σ (m + 1) V)
        (ccOperatorFieldComp (I := I) (M := M) g 0 (σ + m) ((σ + m) + 1) (D t)
          (iteratedCovGrad (I := I) g 0 σ m V))
        (fun p => jet_one_win (I := I) (M := M) g σ (m + 1) V p)
        (hcD t ht V)
      rw [show m + k + 1 + 1 = m + k + 2 from by omega] at h
      exact h
  obtain ⟨CAD, hCAD_nn, hCAD⟩ := hADEx
  have hCDEx : ∀ i : ℕ, ∃ Ki : ℝ, 0 ≤ Ki ∧
      ∀ t, t ∈ A → ∀ (V : SmoothCcTensor g 0 σ), i < k →
        |tensorL2Inner (I := I) (M := M) g 0 ((σ + m) + 1)
          (oneMinusConnLapSmoothIter (I := I) g 0 ((σ + m) + 1) i
            (pointwiseTensorCurv (I := I) (M := M) g (σ + m)
              (oneMinusConnLapSmoothIter (I := I) g 0 (σ + m) (k - 1 - i)
                (iteratedCovGrad (I := I) g 0 σ m V)))).toFun
          (ccOperatorFieldComp (I := I) (M := M) g 0 (σ + m) ((σ + m) + 1) (D t)
            (iteratedCovGrad (I := I) g 0 σ m V)).toFun| ≤
          Ki * ((∑ j ∈ Finset.range (m + k + 1),
              ‖iteratedCovGrad (I := I) g 0 σ j V‖) *
            (∑ j ∈ Finset.range (m + k + 2),
              ‖iteratedCovGrad (I := I) g 0 σ j V‖)) := by
    intro i
    by_cases hi : i < k
    · obtain ⟨Ki, hKi_nn, hKi⟩ :=
        curv_iterL_pair_le (I := I) (M := M) g σ (σ + m) i (k - 1 - i)
          m m (m + k + 1) (m + k) (by omega) (by omega)
          (fun _ => 1) cD (fun _ => zero_le_one) hcD_nn
      refine ⟨Ki, hKi_nn, fun t ht V _ => ?_⟩
      have h := hKi V
        (iteratedCovGrad (I := I) g 0 σ m V)
        (ccOperatorFieldComp (I := I) (M := M) g 0 (σ + m) ((σ + m) + 1) (D t)
          (iteratedCovGrad (I := I) g 0 σ m V))
        (fun p => jet_one_win (I := I) (M := M) g σ m V p)
        (hcD t ht V)
      rw [show m + k + 1 + 1 = m + k + 2 from by omega] at h
      exact le_trans h (le_of_eq (by ring))
    · exact ⟨0, le_rfl, fun _ _ _ hi' => absurd hi' hi⟩
  choose KD hKD_nn hKD using hCDEx
  have hCEEx : ∀ i : ℕ, ∃ Ki : ℝ, 0 ≤ Ki ∧
      ∀ t, t ∈ A → ∀ (V : SmoothCcTensor g 0 σ), i < k →
        |tensorL2Inner (I := I) (M := M) g 0 ((σ + m) + 1)
          (oneMinusConnLapSmoothIter (I := I) g 0 ((σ + m) + 1) i
            (pointwiseTensorCurv (I := I) (M := M) g (σ + m)
              (oneMinusConnLapSmoothIter (I := I) g 0 (σ + m) (k - 1 - i)
                (iteratedCovGrad (I := I) g 0 σ m V)))).toFun
          (ccOperatorFieldComp (I := I) (M := M) g 0 ((σ + m) + 1) ((σ + m) + 1) (E₁ t)
            (iteratedCovGrad (I := I) g 0 σ (m + 1) V)).toFun| ≤
          Ki * ((∑ j ∈ Finset.range (m + k + 1),
              ‖iteratedCovGrad (I := I) g 0 σ j V‖) *
            (∑ j ∈ Finset.range (m + k + 2),
              ‖iteratedCovGrad (I := I) g 0 σ j V‖)) := by
    intro i
    by_cases hi : i < k
    · obtain ⟨Ki, hKi_nn, hKi⟩ :=
        curv_iterL_pair_le (I := I) (M := M) g σ (σ + m) i (k - 1 - i)
          m (m + 1) (m + k + 1) (m + k) (by omega) (by omega)
          (fun _ => 1) cE (fun _ => zero_le_one) hcE_nn
      refine ⟨Ki, hKi_nn, fun t ht V _ => ?_⟩
      have h := hKi V
        (iteratedCovGrad (I := I) g 0 σ m V)
        (ccOperatorFieldComp (I := I) (M := M) g 0 ((σ + m) + 1) ((σ + m) + 1) (E₁ t)
          (iteratedCovGrad (I := I) g 0 σ (m + 1) V))
        (fun p => jet_one_win (I := I) (M := M) g σ m V p)
        (hcE t ht V)
      rw [show m + k + 1 + 1 = m + k + 2 from by omega] at h
      exact le_trans h (le_of_eq (by ring))
    · exact ⟨0, le_rfl, fun _ _ _ hi' => absurd hi' hi⟩
  choose KE hKE_nn hKE using hCEEx
  refine ⟨CZ + CAD + (∑ i ∈ Finset.range k, KD i) +
      (∑ i ∈ Finset.range k, KE i),
    add_nonneg (add_nonneg (add_nonneg hCZ_nn hCAD_nn)
      (Finset.sum_nonneg fun i _ => hKD_nn i))
      (Finset.sum_nonneg fun i _ => hKE_nn i), fun t ht V => ?_⟩
  let W : SmoothCcTensor g 0 (σ + m) :=
    iteratedCovGrad (I := I) g 0 σ m V
  let W₁ : SmoothCcTensor g 0 ((σ + m) + 1) :=
    iteratedCovGrad (I := I) g 0 σ (m + 1) V
  have hW₁ : covGrad (I := I) (M := M) g 0 (σ + m) W = W₁ := by
    exact (iteratedCovGrad_succ (I := I) (M := M) g 0 σ m V).symm
  have hnext : slotEnergy (I := I) (M := M) g ((σ + m) + 1) k (E₁ t) W₁ =
      slotStage (I := I) (M := M) g σ (m + 1) k (C t) V := by
    rfl
  have hstep := slot_step_exp (I := I) (M := M) g (σ + m) k (Cm t) W
  rw [hW₁, hnext] at hstep
  have hZ : |slotEnergy (I := I) (M := M) g (σ + m) k (Cm t) W| ≤
      CZ * ((∑ j ∈ Finset.range (m + k + 1),
          ‖iteratedCovGrad (I := I) g 0 σ j V‖) *
        (∑ j ∈ Finset.range (m + k + 2),
          ‖iteratedCovGrad (I := I) g 0 σ j V‖)) := by
    have h := hCZ V W
      (ccOperatorFieldComp (I := I) (M := M) g 0 (σ + m) (σ + m) (Cm t) W)
      (fun p => jet_one_win (I := I) (M := M) g σ m V p) (hcC t ht V)
    rw [show m + k + 1 + 1 = m + k + 2 from by omega] at h
    exact le_trans h (le_of_eq (by ring))
  have hAD := hCAD t ht V
  have hDsum : |∑ i ∈ Finset.range k,
      tensorL2Inner (I := I) (M := M) g 0 ((σ + m) + 1)
        (oneMinusConnLapSmoothIter (I := I) g 0 ((σ + m) + 1) i
          (pointwiseTensorCurv (I := I) (M := M) g (σ + m)
            (oneMinusConnLapSmoothIter (I := I) g 0 (σ + m) (k - 1 - i) W))).toFun
        (ccOperatorFieldComp (I := I) (M := M) g 0 (σ + m) ((σ + m) + 1) (D t) W).toFun| ≤
      (∑ i ∈ Finset.range k, KD i) *
        ((∑ j ∈ Finset.range (m + k + 1),
            ‖iteratedCovGrad (I := I) g 0 σ j V‖) *
          (∑ j ∈ Finset.range (m + k + 2),
            ‖iteratedCovGrad (I := I) g 0 σ j V‖)) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine le_trans (Finset.sum_le_sum
      (fun i hi => hKD i t ht V (Finset.mem_range.mp hi))) ?_
    rw [← Finset.sum_mul]
  have hEsum : |∑ i ∈ Finset.range k,
      tensorL2Inner (I := I) (M := M) g 0 ((σ + m) + 1)
        (oneMinusConnLapSmoothIter (I := I) g 0 ((σ + m) + 1) i
          (pointwiseTensorCurv (I := I) (M := M) g (σ + m)
            (oneMinusConnLapSmoothIter (I := I) g 0 (σ + m) (k - 1 - i) W))).toFun
        (ccOperatorFieldComp (I := I) (M := M) g 0 ((σ + m) + 1) ((σ + m) + 1) (E₁ t) W₁).toFun| ≤
      (∑ i ∈ Finset.range k, KE i) *
        ((∑ j ∈ Finset.range (m + k + 1),
            ‖iteratedCovGrad (I := I) g 0 σ j V‖) *
          (∑ j ∈ Finset.range (m + k + 2),
            ‖iteratedCovGrad (I := I) g 0 σ j V‖)) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine le_trans (Finset.sum_le_sum
      (fun i hi => hKE i t ht V (Finset.mem_range.mp hi))) ?_
    rw [← Finset.sum_mul]
  change |slotEnergy (I := I) (M := M) g (σ + m) (k + 1) (Cm t) W -
    slotStage (I := I) (M := M) g σ (m + 1) k (C t) V| ≤ _
  rw [hstep]
  have hcancel :
      slotEnergy (I := I) (M := M) g (σ + m) k (Cm t) W +
        tensorL2Inner (I := I) (M := M) g 0 ((σ + m) + 1)
          (oneMinusConnLapSmoothIter (I := I) g 0 ((σ + m) + 1) k W₁).toFun
          (ccOperatorFieldComp (I := I) (M := M) g 0 (σ + m) ((σ + m) + 1) (D t) W).toFun +
        slotStage (I := I) (M := M) g σ (m + 1) k (C t) V +
        (∑ i ∈ Finset.range k,
          tensorL2Inner (I := I) (M := M) g 0 ((σ + m) + 1)
            (oneMinusConnLapSmoothIter (I := I) g 0 ((σ + m) + 1) i
              (pointwiseTensorCurv (I := I) (M := M) g (σ + m)
                (oneMinusConnLapSmoothIter (I := I) g 0 (σ + m) (k - 1 - i) W))).toFun
            (ccOperatorFieldComp (I := I) (M := M) g 0 (σ + m) ((σ + m) + 1) (D t) W).toFun) +
        (∑ i ∈ Finset.range k,
          tensorL2Inner (I := I) (M := M) g 0 ((σ + m) + 1)
            (oneMinusConnLapSmoothIter (I := I) g 0 ((σ + m) + 1) i
              (pointwiseTensorCurv (I := I) (M := M) g (σ + m)
                (oneMinusConnLapSmoothIter (I := I) g 0 (σ + m) (k - 1 - i) W))).toFun
            (ccOperatorFieldComp (I := I) (M := M) g 0 ((σ + m) + 1) ((σ + m) + 1) (E₁ t) W₁).toFun) -
        slotStage (I := I) (M := M) g σ (m + 1) k (C t) V =
      slotEnergy (I := I) (M := M) g (σ + m) k (Cm t) W +
        tensorL2Inner (I := I) (M := M) g 0 ((σ + m) + 1)
          (oneMinusConnLapSmoothIter (I := I) g 0 ((σ + m) + 1) k W₁).toFun
          (ccOperatorFieldComp (I := I) (M := M) g 0 (σ + m) ((σ + m) + 1) (D t) W).toFun +
        (∑ i ∈ Finset.range k,
          tensorL2Inner (I := I) (M := M) g 0 ((σ + m) + 1)
            (oneMinusConnLapSmoothIter (I := I) g 0 ((σ + m) + 1) i
              (pointwiseTensorCurv (I := I) (M := M) g (σ + m)
                (oneMinusConnLapSmoothIter (I := I) g 0 (σ + m) (k - 1 - i) W))).toFun
            (ccOperatorFieldComp (I := I) (M := M) g 0 (σ + m) ((σ + m) + 1) (D t) W).toFun) +
        (∑ i ∈ Finset.range k,
          tensorL2Inner (I := I) (M := M) g 0 ((σ + m) + 1)
            (oneMinusConnLapSmoothIter (I := I) g 0 ((σ + m) + 1) i
              (pointwiseTensorCurv (I := I) (M := M) g (σ + m)
                (oneMinusConnLapSmoothIter (I := I) g 0 (σ + m) (k - 1 - i) W))).toFun
            (ccOperatorFieldComp (I := I) (M := M) g 0 ((σ + m) + 1) ((σ + m) + 1) (E₁ t) W₁).toFun) := by
    ring
  rw [hcancel]
  refine le_trans (abs_add4 _ _ _ _) ?_
  exact le_trans (add_le_add (add_le_add (add_le_add hZ hAD) hDsum) hEsum)
    (le_of_eq (by ring))

private theorem slot_stage_bound (g : SmoothRiemannianMetric I M)
    (σ m k : ℕ) (C : SmoothCcTensor g σ σ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ V : SmoothCcTensor g 0 σ,
      |slotStage (I := I) (M := M) g σ m (k + 1) C V -
        slotStage (I := I) (M := M) g σ (m + 1) k C V| ≤
      K * ((∑ j ∈ Finset.range (m + k + 1),
          ‖iteratedCovGrad (I := I) g 0 σ j V‖) *
        (∑ j ∈ Finset.range (m + k + 2),
          ‖iteratedCovGrad (I := I) g 0 σ j V‖)) := by
  let Cm : SmoothCcTensor g (σ + m) (σ + m) :=
    slotExtendIter (I := I) (M := M) g σ σ m C
  let D : SmoothCcTensor g (σ + m) ((σ + m) + 1) :=
    covGrad (I := I) (M := M) g (σ + m) (σ + m) Cm
  let E₁ : SmoothCcTensor g ((σ + m) + 1) ((σ + m) + 1) :=
    slotExtend (I := I) (M := M) g (σ + m) (σ + m) Cm
  obtain ⟨cC, hcC_nn, hcC⟩ :=
    app_shift_win (I := I) (M := M) g σ m (σ + m) Cm
  obtain ⟨cD, hcD_nn, hcD⟩ :=
    app_shift_win (I := I) (M := M) g σ m ((σ + m) + 1) D
  obtain ⟨cE, hcE_nn, hcE⟩ :=
    app_shift_win (I := I) (M := M) g σ (m + 1) ((σ + m) + 1) E₁
  obtain ⟨K, hK_nn, hK⟩ := slot_stage_unif (I := I) (M := M) g σ m k
    (fun _ : Unit => C) Set.univ cC cD cE hcC_nn hcD_nn hcE_nn
    (fun _ _ => by simpa only [Cm] using hcC)
    (fun _ _ => by simpa only [Cm, D] using hcD)
    (fun _ _ => by simpa only [Cm, E₁] using hcE)
  exact ⟨K, hK_nn, hK () (Set.mem_univ ())⟩

private theorem sum_telescope (H : ℕ → ℝ) (n : ℕ) :
    ∑ m ∈ Finset.range n, (H m - H (m + 1)) = H 0 - H n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      ring

private theorem slot_main_unif (g : SmoothRiemannianMetric I M)
    (sigma n : ℕ) {α : Type*} (C : α → SmoothCcTensor g sigma sigma)
    (A : Set α) (cC cD cE : ℕ → ℕ → ℝ)
    (hcC_nn : ∀ m p, 0 ≤ cC m p) (hcD_nn : ∀ m p, 0 ≤ cD m p)
    (hcE_nn : ∀ m p, 0 ≤ cE m p)
    (hcC : ∀ m t, t ∈ A → ShiftWin (I := I) (M := M) g sigma m
      (sigma + m) (slotExtendIter (I := I) (M := M) g sigma sigma m (C t)) (cC m))
    (hcD : ∀ m t, t ∈ A → ShiftWin (I := I) (M := M) g sigma m
      ((sigma + m) + 1)
      (covGrad (I := I) (M := M) g (sigma + m) (sigma + m)
        (slotExtendIter (I := I) (M := M) g sigma sigma m (C t))) (cD m))
    (hcE : ∀ m t, t ∈ A → ShiftWin (I := I) (M := M) g sigma (m + 1)
      ((sigma + m) + 1)
      (slotExtend (I := I) (M := M) g (sigma + m) (sigma + m)
        (slotExtendIter (I := I) (M := M) g sigma sigma m (C t))) (cE m)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t, t ∈ A → ∀ V : SmoothCcTensor g 0 sigma,
      |slotStage (I := I) (M := M) g sigma 0 n (C t) V -
        slotStage (I := I) (M := M) g sigma n 0 (C t) V| ≤
      K * ((∑ j ∈ Finset.range n,
          ‖iteratedCovGrad (I := I) g 0 sigma j V‖) *
        (∑ j ∈ Finset.range (n + 1),
          ‖iteratedCovGrad (I := I) g 0 sigma j V‖)) := by
  classical
  have hKEx : ∀ m : ℕ, ∃ Km : ℝ, 0 ≤ Km ∧
      ∀ t, t ∈ A → ∀ (V : SmoothCcTensor g 0 sigma), m < n →
        |slotStage (I := I) (M := M) g sigma m (n - m) (C t) V -
          slotStage (I := I) (M := M) g sigma (m + 1) (n - (m + 1)) (C t) V| ≤
        Km * ((∑ j ∈ Finset.range n,
            ‖iteratedCovGrad (I := I) g 0 sigma j V‖) *
          (∑ j ∈ Finset.range (n + 1),
            ‖iteratedCovGrad (I := I) g 0 sigma j V‖)) := by
    intro m
    by_cases hm : m < n
    · obtain ⟨Km, hKm_nn, hKm⟩ := slot_stage_unif (I := I) (M := M) g
        sigma m (n - 1 - m) C A (cC m) (cD m) (cE m)
        (hcC_nn m) (hcD_nn m) (hcE_nn m) (hcC m) (hcD m) (hcE m)
      refine ⟨Km, hKm_nn, fun t ht V _ => ?_⟩
      have h := hKm t ht V
      simpa only [show n - m = n - 1 - m + 1 from by omega,
        show n - (m + 1) = n - 1 - m from by omega,
        show m + (n - 1 - m) + 1 = n from by omega,
        show m + (n - 1 - m) + 2 = n + 1 from by omega] using h
    · exact ⟨0, le_rfl, fun _ _ _ hm' => absurd hm' hm⟩
  choose K hK_nn hK using hKEx
  refine ⟨∑ m ∈ Finset.range n, K m,
    Finset.sum_nonneg (fun m _ => hK_nn m), fun t ht V => ?_⟩
  let F : ℕ → ℝ := fun m =>
    slotStage (I := I) (M := M) g sigma m (n - m) (C t) V
  have htele := sum_telescope F n
  have hF0 : F 0 = slotStage (I := I) (M := M) g sigma 0 n (C t) V := by
    simp only [F, Nat.sub_zero]
  have hFn : F n = slotStage (I := I) (M := M) g sigma n 0 (C t) V := by
    simp only [F, Nat.sub_self]
  have hstep : ∀ m ∈ Finset.range n,
      |F m - F (m + 1)| ≤
        K m * ((∑ j ∈ Finset.range n,
            ‖iteratedCovGrad (I := I) g 0 sigma j V‖) *
          (∑ j ∈ Finset.range (n + 1),
            ‖iteratedCovGrad (I := I) g 0 sigma j V‖)) := by
    intro m hm
    exact hK m t ht V (Finset.mem_range.mp hm)
  rw [← hF0, ← hFn, ← htele]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum hstep) ?_
  rw [← Finset.sum_mul]

private theorem slot_main_bdd (g : SmoothRiemannianMetric I M)
    (sigma n : ℕ) {α : Type*} (C : α → SmoothCcTensor g sigma sigma)
    (A : Set α) (B : ℕ → ℝ) (hB_nn : ∀ i, 0 ≤ B i)
    (hB : ∀ i t, t ∈ A → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g sigma (sigma + i) x
        ((iteratedCovGrad (I := I) g sigma sigma i (C t)).toSection x) ≤ B i) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t, t ∈ A → ∀ V : SmoothCcTensor g 0 sigma,
      |slotStage (I := I) (M := M) g sigma 0 n (C t) V -
        slotStage (I := I) (M := M) g sigma n 0 (C t) V| ≤
      K * ((∑ j ∈ Finset.range n,
          ‖iteratedCovGrad (I := I) g 0 sigma j V‖) *
        (∑ j ∈ Finset.range (n + 1),
          ‖iteratedCovGrad (I := I) g 0 sigma j V‖)) := by
  classical
  have hwin : ∀ m : ℕ, ∃ cC cD cE : ℕ → ℝ,
      (∀ p, 0 ≤ cC p) ∧ (∀ p, 0 ≤ cD p) ∧ (∀ p, 0 ≤ cE p) ∧
      (∀ t, t ∈ A → ShiftWin (I := I) (M := M) g sigma m (sigma + m)
        (slotExtendIter (I := I) (M := M) g sigma sigma m (C t)) cC) ∧
      (∀ t, t ∈ A → ShiftWin (I := I) (M := M) g sigma m
        ((sigma + m) + 1)
        (covGrad (I := I) (M := M) g (sigma + m) (sigma + m)
          (slotExtendIter (I := I) (M := M) g sigma sigma m (C t))) cD) ∧
      (∀ t, t ∈ A → ShiftWin (I := I) (M := M) g sigma (m + 1)
        ((sigma + m) + 1)
        (slotExtend (I := I) (M := M) g (sigma + m) (sigma + m)
          (slotExtendIter (I := I) (M := M) g sigma sigma m (C t))) cE) := by
    intro m
    let BC : ℕ → ℝ := fun i => (Module.finrank ℝ E : ℝ) ^ m * B i
    have hBC_nn : ∀ i, 0 ≤ BC i := fun i =>
      mul_nonneg (by positivity) (hB_nn i)
    have hBC : ∀ i t, t ∈ A → ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g (sigma + m)
          ((sigma + m) + i) x
          ((iteratedCovGrad (I := I) g (sigma + m) (sigma + m) i
            (slotExtendIter (I := I) (M := M) g sigma sigma m (C t))).toSection x) ≤
          BC i := by
      intro i t ht x
      exact slot_iter_bdd (I := I) (M := M) g sigma C A B hB m i t ht x
    obtain ⟨cC, hcC_nn, hcC⟩ := shift_win_of_bdd (I := I) (M := M) g
      sigma m (sigma + m)
      (fun t => slotExtendIter (I := I) (M := M) g sigma sigma m (C t))
      A BC hBC_nn hBC
    let BD : ℕ → ℝ := fun i => (Module.finrank ℝ E : ℝ) ^ m * B (i + 1)
    have hBD_nn : ∀ i, 0 ≤ BD i := fun i =>
      mul_nonneg (by positivity) (hB_nn (i + 1))
    have hBD : ∀ i t, t ∈ A → ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g (sigma + m)
          (((sigma + m) + 1) + i) x
          ((iteratedCovGrad (I := I) g (sigma + m) ((sigma + m) + 1) i
            (covGrad (I := I) (M := M) g (sigma + m) (sigma + m)
              (slotExtendIter (I := I) (M := M) g sigma sigma m (C t)))).toSection x) ≤
          BD i := by
      intro i t ht x
      rw [rfns_iteratedCovGrad_covGrad_comm_rs (I := I) (M := M)]
      exact slot_iter_bdd (I := I) (M := M) g sigma C A B hB m (i + 1) t ht x
    obtain ⟨cD, hcD_nn, hcD⟩ := shift_win_of_bdd (I := I) (M := M) g
      sigma m ((sigma + m) + 1)
      (fun t => covGrad (I := I) (M := M) g (sigma + m) (sigma + m)
        (slotExtendIter (I := I) (M := M) g sigma sigma m (C t)))
      A BD hBD_nn hBD
    let BE : ℕ → ℝ := fun i =>
      (Module.finrank ℝ E : ℝ) ^ (m + 1) * B i
    have hBE_nn : ∀ i, 0 ≤ BE i := fun i =>
      mul_nonneg (by positivity) (hB_nn i)
    have hBE : ∀ i t, t ∈ A → ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g ((sigma + m) + 1)
          (((sigma + m) + 1) + i) x
          ((iteratedCovGrad (I := I) g ((sigma + m) + 1) ((sigma + m) + 1) i
            (slotExtend (I := I) (M := M) g (sigma + m) (sigma + m)
              (slotExtendIter (I := I) (M := M) g sigma sigma m (C t)))).toSection x) ≤
          BE i := by
      intro i t ht x
      simpa only [slotExtendIter, Nat.add_assoc] using
        (slot_iter_bdd (I := I) (M := M) g sigma C A B hB (m + 1) i t ht x)
    obtain ⟨cE, hcE_nn, hcE⟩ := shift_win_of_bdd (I := I) (M := M) g
      sigma (m + 1) ((sigma + m) + 1)
      (fun t => slotExtend (I := I) (M := M) g (sigma + m) (sigma + m)
        (slotExtendIter (I := I) (M := M) g sigma sigma m (C t)))
      A BE hBE_nn hBE
    exact ⟨cC, cD, cE, hcC_nn, hcD_nn, hcE_nn, hcC, hcD, hcE⟩
  choose cC cD cE hcC_nn hcD_nn hcE_nn hcC hcD hcE using hwin
  exact slot_main_unif (I := I) (M := M) g sigma n C A cC cD cE
    hcC_nn hcD_nn hcE_nn hcC hcD hcE

private theorem slot_main_bound (g : SmoothRiemannianMetric I M)
    (σ n : ℕ) (C : SmoothCcTensor g σ σ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ V : SmoothCcTensor g 0 σ,
      |slotStage (I := I) (M := M) g σ 0 n C V -
        slotStage (I := I) (M := M) g σ n 0 C V| ≤
      K * ((∑ j ∈ Finset.range n,
          ‖iteratedCovGrad (I := I) g 0 σ j V‖) *
        (∑ j ∈ Finset.range (n + 1),
          ‖iteratedCovGrad (I := I) g 0 σ j V‖)) := by
  classical
  have hKEx : ∀ m : ℕ, ∃ Km : ℝ, 0 ≤ Km ∧
      ∀ (V : SmoothCcTensor g 0 σ), m < n →
        |slotStage (I := I) (M := M) g σ m (n - m) C V -
          slotStage (I := I) (M := M) g σ (m + 1) (n - (m + 1)) C V| ≤
        Km * ((∑ j ∈ Finset.range n,
            ‖iteratedCovGrad (I := I) g 0 σ j V‖) *
          (∑ j ∈ Finset.range (n + 1),
            ‖iteratedCovGrad (I := I) g 0 σ j V‖)) := by
    intro m
    by_cases hm : m < n
    · obtain ⟨Km, hKm_nn, hKm⟩ :=
        slot_stage_bound (I := I) (M := M) g σ m (n - 1 - m) C
      refine ⟨Km, hKm_nn, fun V _ => ?_⟩
      have h := hKm V
      simpa only [show n - m = n - 1 - m + 1 from by omega,
        show n - (m + 1) = n - 1 - m from by omega,
        show m + (n - 1 - m) + 1 = n from by omega,
        show m + (n - 1 - m) + 2 = n + 1 from by omega] using h
    · exact ⟨0, le_rfl, fun _ hm' => absurd hm' hm⟩
  choose K hK_nn hK using hKEx
  refine ⟨∑ m ∈ Finset.range n, K m,
    Finset.sum_nonneg (fun m _ => hK_nn m), fun V => ?_⟩
  let H : ℕ → ℝ := fun m =>
    slotStage (I := I) (M := M) g σ m (n - m) C V
  have htele := sum_telescope H n
  have hH0 : H 0 = slotStage (I := I) (M := M) g σ 0 n C V := by
    simp only [H, Nat.sub_zero]
  have hHn : H n = slotStage (I := I) (M := M) g σ n 0 C V := by
    simp only [H, Nat.sub_self]
  have hstep : ∀ m ∈ Finset.range n,
      |H m - H (m + 1)| ≤
        K m * ((∑ j ∈ Finset.range n,
            ‖iteratedCovGrad (I := I) g 0 σ j V‖) *
          (∑ j ∈ Finset.range (n + 1),
            ‖iteratedCovGrad (I := I) g 0 σ j V‖)) := by
    intro m hm
    exact hK m V (Finset.mem_range.mp hm)
  rw [← hH0, ← hHn, ← htele]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum hstep) ?_
  rw [← Finset.sum_mul]





theorem slot_iterL_pair (g : SmoothRiemannianMetric I M) (s n : ℕ)
    (C₀ : SmoothCcTensor g (s + 1) (s + 1)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ U : SmoothCcTensor g 0 s,
      |tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (covGrad (I := I) (M := M) g 0 s
            (oneMinusConnLapSmoothIter (I := I) g 0 s n U)).toFun
          (ccOperatorFieldComp (I := I) (M := M) g 0 (s + 1) (s + 1) C₀
            (covGrad (I := I) (M := M) g 0 s U)).toFun -
        tensorL2Inner (I := I) (M := M) g 0 ((s + 1) + n)
          (iteratedCovGrad (I := I) g 0 (s + 1) n
            (covGrad (I := I) (M := M) g 0 s U)).toFun
          (ccOperatorFieldComp (I := I) (M := M) g 0 ((s + 1) + n) ((s + 1) + n)
            (slotExtendIter (I := I) (M := M) g (s + 1) (s + 1) n C₀)
            (iteratedCovGrad (I := I) g 0 (s + 1) n
              (covGrad (I := I) (M := M) g 0 s U))).toFun| ≤
        K * ((∑ j ∈ Finset.range (n + 1),
            ‖iteratedCovGrad (I := I) g 0 s j U‖) *
          (∑ j ∈ Finset.range (n + 2),
            ‖iteratedCovGrad (I := I) g 0 s j U‖)) := by
  classical
  obtain ⟨Km, hKm_nn, hKm⟩ :=
    slot_main_bound (I := I) (M := M) g (s + 1) n C₀
  obtain ⟨cZ, hcZ_nn, hcZ⟩ :=
    app_shift_win (I := I) (M := M) g s 1 (s + 1) C₀
  have hKEx : ∀ i : ℕ, ∃ Ki : ℝ, 0 ≤ Ki ∧
      ∀ (U : SmoothCcTensor g 0 s), i < n →
        |tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (oneMinusConnLapSmoothIter (I := I) g 0 (s + 1) i
            (pointwiseTensorCurv (I := I) (M := M) g s
              (oneMinusConnLapSmoothIter (I := I) g 0 s (n - 1 - i) U))).toFun
          (ccOperatorFieldComp (I := I) (M := M) g 0 (s + 1) (s + 1) C₀
            (covGrad (I := I) (M := M) g 0 s U)).toFun| ≤
          Ki * ((∑ j ∈ Finset.range (n + 1),
              ‖iteratedCovGrad (I := I) g 0 s j U‖) *
            (∑ j ∈ Finset.range (n + 2),
              ‖iteratedCovGrad (I := I) g 0 s j U‖)) := by
    intro i
    by_cases hi : i < n
    · obtain ⟨Ki, hKi_nn, hKi⟩ :=
        curv_iterL_pair_le (I := I) (M := M) g s s i (n - 1 - i)
          0 1 (n + 1) n (by omega) (by omega)
          (fun _ => 1) cZ (fun _ => zero_le_one) hcZ_nn
      refine ⟨Ki, hKi_nn, fun U _ => ?_⟩
      have hZwin : ∀ p,
          ‖iteratedCovGrad (I := I) g 0 (s + 1) p
            (ccOperatorFieldComp (I := I) (M := M) g 0 (s + 1) (s + 1) C₀
              (covGrad (I := I) (M := M) g 0 s U))‖ ≤
            cZ p * ∑ j ∈ Finset.range (p + 1 + 1),
              ‖iteratedCovGrad (I := I) g 0 s j U‖ := by
        intro p
        simpa only [iteratedCovGrad_succ, iteratedCovGrad_zero] using hcZ U p
      have h := hKi U U
        (ccOperatorFieldComp (I := I) (M := M) g 0 (s + 1) (s + 1) C₀
          (covGrad (I := I) (M := M) g 0 s U))
        (fun p => jet_one_win (I := I) (M := M) g s 0 U p)
        hZwin
      rw [show n + 1 + 1 = n + 2 from by omega] at h
      exact le_trans h (le_of_eq (by ring))
    · exact ⟨0, le_rfl, fun _ hi' => absurd hi' hi⟩
  choose Ki hKi_nn hKi using hKEx
  refine ⟨Km + ∑ i ∈ Finset.range n, Ki i,
    add_nonneg hKm_nn (Finset.sum_nonneg fun i _ => hKi_nn i), fun U => ?_⟩
  let W : SmoothCcTensor g 0 (s + 1) :=
    covGrad (I := I) (M := M) g 0 s U
  let P : ℝ :=
    (∑ j ∈ Finset.range (n + 1),
        ‖iteratedCovGrad (I := I) g 0 s j U‖) *
      (∑ j ∈ Finset.range (n + 2),
        ‖iteratedCovGrad (I := I) g 0 s j U‖)
  have hsmall : ∑ j ∈ Finset.range n,
      ‖iteratedCovGrad (I := I) g 0 (s + 1) j W‖ ≤
      ∑ j ∈ Finset.range (n + 1),
        ‖iteratedCovGrad (I := I) g 0 s j U‖ := by
    change ∑ j ∈ Finset.range n,
      ‖iteratedCovGrad (I := I) g 0 (s + 1) j
        (iteratedCovGrad (I := I) g 0 s 1 U)‖ ≤ _
    simpa only [show n + 1 = n + 1 from rfl] using
      jet_shift_le (I := I) (M := M) g s 1 n U
  have hlarge : ∑ j ∈ Finset.range (n + 1),
      ‖iteratedCovGrad (I := I) g 0 (s + 1) j W‖ ≤
      ∑ j ∈ Finset.range (n + 2),
        ‖iteratedCovGrad (I := I) g 0 s j U‖ := by
    change ∑ j ∈ Finset.range (n + 1),
      ‖iteratedCovGrad (I := I) g 0 (s + 1) j
        (iteratedCovGrad (I := I) g 0 s 1 U)‖ ≤ _
    simpa only [show n + 1 + 1 = n + 2 by omega] using
      jet_shift_le (I := I) (M := M) g s 1 (n + 1) U
  have hmain : |slotStage (I := I) (M := M) g (s + 1) 0 n C₀ W -
      slotStage (I := I) (M := M) g (s + 1) n 0 C₀ W| ≤ Km * P := by
    refine le_trans (hKm W) ?_
    refine mul_le_mul_of_nonneg_left ?_ hKm_nn
    exact mul_le_mul hsmall hlarge
      (Finset.sum_nonneg fun j _ => norm_nonneg _)
      (Finset.sum_nonneg fun j _ => norm_nonneg _)
  have hcurv : |∑ i ∈ Finset.range n,
      tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (oneMinusConnLapSmoothIter (I := I) g 0 (s + 1) i
          (pointwiseTensorCurv (I := I) (M := M) g s
            (oneMinusConnLapSmoothIter (I := I) g 0 s (n - 1 - i) U))).toFun
        (ccOperatorFieldComp (I := I) (M := M) g 0 (s + 1) (s + 1) C₀ W).toFun| ≤
      (∑ i ∈ Finset.range n, Ki i) * P := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine le_trans (Finset.sum_le_sum (fun i hi => hKi i U (Finset.mem_range.mp hi))) ?_
    rw [← Finset.sum_mul]
  have hbase : tensorL2Inner (I := I) (M := M) g 0 (s + 1)
      (covGrad (I := I) (M := M) g 0 s
        (oneMinusConnLapSmoothIter (I := I) g 0 s n U)).toFun
      (ccOperatorFieldComp (I := I) (M := M) g 0 (s + 1) (s + 1) C₀ W).toFun =
      slotStage (I := I) (M := M) g (s + 1) 0 n C₀ W +
        ∑ i ∈ Finset.range n,
          tensorL2Inner (I := I) (M := M) g 0 (s + 1)
            (oneMinusConnLapSmoothIter (I := I) g 0 (s + 1) i
              (pointwiseTensorCurv (I := I) (M := M) g s
                (oneMinusConnLapSmoothIter (I := I) g 0 s (n - 1 - i) U))).toFun
            (ccOperatorFieldComp (I := I) (M := M) g 0 (s + 1) (s + 1) C₀ W).toFun := by
    rw [covGrad_iterL (I := I) (M := M) g s n U,
      l2_add_left (I := I) (M := M) g (s + 1),
      l2_sum_left (I := I) (M := M) g (s + 1)]
    rfl
  have htop : slotStage (I := I) (M := M) g (s + 1) n 0 C₀ W =
      tensorL2Inner (I := I) (M := M) g 0 ((s + 1) + n)
        (iteratedCovGrad (I := I) g 0 (s + 1) n W).toFun
        (ccOperatorFieldComp (I := I) (M := M) g 0 ((s + 1) + n) ((s + 1) + n)
          (slotExtendIter (I := I) (M := M) g (s + 1) (s + 1) n C₀)
          (iteratedCovGrad (I := I) g 0 (s + 1) n W)).toFun := by
    simp only [slotStage, slotEnergy, oneMinusConnLapSmoothIter_zero]
  rw [show covGrad (I := I) (M := M) g 0 s U = W from rfl, hbase, ← htop]
  have hsplit :
      slotStage (I := I) (M := M) g (s + 1) 0 n C₀ W +
          (∑ i ∈ Finset.range n,
            tensorL2Inner (I := I) (M := M) g 0 (s + 1)
              (oneMinusConnLapSmoothIter (I := I) g 0 (s + 1) i
                (pointwiseTensorCurv (I := I) (M := M) g s
                  (oneMinusConnLapSmoothIter (I := I) g 0 s (n - 1 - i) U))).toFun
              (ccOperatorFieldComp (I := I) (M := M) g 0 (s + 1) (s + 1) C₀ W).toFun) -
          slotStage (I := I) (M := M) g (s + 1) n 0 C₀ W =
        (slotStage (I := I) (M := M) g (s + 1) 0 n C₀ W -
          slotStage (I := I) (M := M) g (s + 1) n 0 C₀ W) +
          ∑ i ∈ Finset.range n,
            tensorL2Inner (I := I) (M := M) g 0 (s + 1)
              (oneMinusConnLapSmoothIter (I := I) g 0 (s + 1) i
                (pointwiseTensorCurv (I := I) (M := M) g s
                  (oneMinusConnLapSmoothIter (I := I) g 0 s (n - 1 - i) U))).toFun
              (ccOperatorFieldComp (I := I) (M := M) g 0 (s + 1) (s + 1) C₀ W).toFun := by
    ring
  rw [hsplit]
  refine le_trans (abs_add_le _ _) ?_
  exact le_trans (add_le_add hmain hcurv) (le_of_eq (by ring))




theorem slot_iterL_unif (g : SmoothRiemannianMetric I M) (s n : ℕ)
    {α : Type*} (C : α → SmoothCcTensor g (s + 1) (s + 1)) (A : Set α)
    (B : ℕ → ℝ) (hB_nn : ∀ i, 0 ≤ B i)
    (hB : ∀ i t, t ∈ A → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g (s + 1) ((s + 1) + i) x
        ((iteratedCovGrad (I := I) g (s + 1) (s + 1) i (C t)).toSection x) ≤ B i) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t, t ∈ A → ∀ U : SmoothCcTensor g 0 s,
      |tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (covGrad (I := I) (M := M) g 0 s
            (oneMinusConnLapSmoothIter (I := I) g 0 s n U)).toFun
          (ccOperatorFieldComp (I := I) (M := M) g 0 (s + 1) (s + 1) (C t)
            (covGrad (I := I) (M := M) g 0 s U)).toFun -
        tensorL2Inner (I := I) (M := M) g 0 ((s + 1) + n)
          (iteratedCovGrad (I := I) g 0 (s + 1) n
            (covGrad (I := I) (M := M) g 0 s U)).toFun
          (ccOperatorFieldComp (I := I) (M := M) g 0 ((s + 1) + n) ((s + 1) + n)
            (slotExtendIter (I := I) (M := M) g (s + 1) (s + 1) n (C t))
            (iteratedCovGrad (I := I) g 0 (s + 1) n
              (covGrad (I := I) (M := M) g 0 s U))).toFun| ≤
        K * ((∑ j ∈ Finset.range (n + 1),
            ‖iteratedCovGrad (I := I) g 0 s j U‖) *
          (∑ j ∈ Finset.range (n + 2),
            ‖iteratedCovGrad (I := I) g 0 s j U‖)) := by
  classical
  obtain ⟨Km, hKm_nn, hKm⟩ :=
    slot_main_bdd (I := I) (M := M) g (s + 1) n C A B hB_nn hB
  obtain ⟨cZ, hcZ_nn, hcZ⟩ :=
    shift_win_of_bdd (I := I) (M := M) g s 1 (s + 1) C A B hB_nn hB
  have hKEx : ∀ i : ℕ, ∃ Ki : ℝ, 0 ≤ Ki ∧
      ∀ t, t ∈ A → ∀ (U : SmoothCcTensor g 0 s), i < n →
        |tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (oneMinusConnLapSmoothIter (I := I) g 0 (s + 1) i
            (pointwiseTensorCurv (I := I) (M := M) g s
              (oneMinusConnLapSmoothIter (I := I) g 0 s (n - 1 - i) U))).toFun
          (ccOperatorFieldComp (I := I) (M := M) g 0 (s + 1) (s + 1) (C t)
            (covGrad (I := I) (M := M) g 0 s U)).toFun| ≤
          Ki * ((∑ j ∈ Finset.range (n + 1),
              ‖iteratedCovGrad (I := I) g 0 s j U‖) *
            (∑ j ∈ Finset.range (n + 2),
              ‖iteratedCovGrad (I := I) g 0 s j U‖)) := by
    intro i
    by_cases hi : i < n
    · obtain ⟨Ki, hKi_nn, hKi⟩ :=
        curv_iterL_pair_le (I := I) (M := M) g s s i (n - 1 - i)
          0 1 (n + 1) n (by omega) (by omega)
          (fun _ => 1) cZ (fun _ => zero_le_one) hcZ_nn
      refine ⟨Ki, hKi_nn, fun t ht U _ => ?_⟩
      have hZwin : ∀ p,
          ‖iteratedCovGrad (I := I) g 0 (s + 1) p
            (ccOperatorFieldComp (I := I) (M := M) g 0 (s + 1) (s + 1) (C t)
              (covGrad (I := I) (M := M) g 0 s U))‖ ≤
            cZ p * ∑ j ∈ Finset.range (p + 1 + 1),
              ‖iteratedCovGrad (I := I) g 0 s j U‖ := by
        intro p
        simpa only [iteratedCovGrad_succ, iteratedCovGrad_zero] using hcZ t ht U p
      have h := hKi U U
        (ccOperatorFieldComp (I := I) (M := M) g 0 (s + 1) (s + 1) (C t)
          (covGrad (I := I) (M := M) g 0 s U))
        (fun p => jet_one_win (I := I) (M := M) g s 0 U p) hZwin
      rw [show n + 1 + 1 = n + 2 from by omega] at h
      exact le_trans h (le_of_eq (by ring))
    · exact ⟨0, le_rfl, fun _ _ _ hi' => absurd hi' hi⟩
  choose Ki hKi_nn hKi using hKEx
  refine ⟨Km + ∑ i ∈ Finset.range n, Ki i,
    add_nonneg hKm_nn (Finset.sum_nonneg fun i _ => hKi_nn i),
    fun t ht U => ?_⟩
  let W : SmoothCcTensor g 0 (s + 1) :=
    covGrad (I := I) (M := M) g 0 s U
  let P : ℝ :=
    (∑ j ∈ Finset.range (n + 1),
        ‖iteratedCovGrad (I := I) g 0 s j U‖) *
      (∑ j ∈ Finset.range (n + 2),
        ‖iteratedCovGrad (I := I) g 0 s j U‖)
  have hsmall : ∑ j ∈ Finset.range n,
      ‖iteratedCovGrad (I := I) g 0 (s + 1) j W‖ ≤
      ∑ j ∈ Finset.range (n + 1),
        ‖iteratedCovGrad (I := I) g 0 s j U‖ := by
    change ∑ j ∈ Finset.range n,
      ‖iteratedCovGrad (I := I) g 0 (s + 1) j
        (iteratedCovGrad (I := I) g 0 s 1 U)‖ ≤ _
    simpa only [show n + 1 = n + 1 from rfl] using
      jet_shift_le (I := I) (M := M) g s 1 n U
  have hlarge : ∑ j ∈ Finset.range (n + 1),
      ‖iteratedCovGrad (I := I) g 0 (s + 1) j W‖ ≤
      ∑ j ∈ Finset.range (n + 2),
        ‖iteratedCovGrad (I := I) g 0 s j U‖ := by
    change ∑ j ∈ Finset.range (n + 1),
      ‖iteratedCovGrad (I := I) g 0 (s + 1) j
        (iteratedCovGrad (I := I) g 0 s 1 U)‖ ≤ _
    simpa only [show n + 1 + 1 = n + 2 by omega] using
      jet_shift_le (I := I) (M := M) g s 1 (n + 1) U
  have hmain : |slotStage (I := I) (M := M) g (s + 1) 0 n (C t) W -
      slotStage (I := I) (M := M) g (s + 1) n 0 (C t) W| ≤ Km * P := by
    refine le_trans (hKm t ht W) ?_
    refine mul_le_mul_of_nonneg_left ?_ hKm_nn
    exact mul_le_mul hsmall hlarge
      (Finset.sum_nonneg fun j _ => norm_nonneg _)
      (Finset.sum_nonneg fun j _ => norm_nonneg _)
  have hcurv : |∑ i ∈ Finset.range n,
      tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (oneMinusConnLapSmoothIter (I := I) g 0 (s + 1) i
          (pointwiseTensorCurv (I := I) (M := M) g s
            (oneMinusConnLapSmoothIter (I := I) g 0 s (n - 1 - i) U))).toFun
        (ccOperatorFieldComp (I := I) (M := M) g 0 (s + 1) (s + 1) (C t) W).toFun| ≤
      (∑ i ∈ Finset.range n, Ki i) * P := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine le_trans (Finset.sum_le_sum
      (fun i hi => hKi i t ht U (Finset.mem_range.mp hi))) ?_
    rw [← Finset.sum_mul]
  have hbase : tensorL2Inner (I := I) (M := M) g 0 (s + 1)
      (covGrad (I := I) (M := M) g 0 s
        (oneMinusConnLapSmoothIter (I := I) g 0 s n U)).toFun
      (ccOperatorFieldComp (I := I) (M := M) g 0 (s + 1) (s + 1) (C t) W).toFun =
      slotStage (I := I) (M := M) g (s + 1) 0 n (C t) W +
        ∑ i ∈ Finset.range n,
          tensorL2Inner (I := I) (M := M) g 0 (s + 1)
            (oneMinusConnLapSmoothIter (I := I) g 0 (s + 1) i
              (pointwiseTensorCurv (I := I) (M := M) g s
                (oneMinusConnLapSmoothIter (I := I) g 0 s (n - 1 - i) U))).toFun
            (ccOperatorFieldComp (I := I) (M := M) g 0 (s + 1) (s + 1) (C t) W).toFun := by
    rw [covGrad_iterL (I := I) (M := M) g s n U,
      l2_add_left (I := I) (M := M) g (s + 1),
      l2_sum_left (I := I) (M := M) g (s + 1)]
    rfl
  have htop : slotStage (I := I) (M := M) g (s + 1) n 0 (C t) W =
      tensorL2Inner (I := I) (M := M) g 0 ((s + 1) + n)
        (iteratedCovGrad (I := I) g 0 (s + 1) n W).toFun
        (ccOperatorFieldComp (I := I) (M := M) g 0 ((s + 1) + n) ((s + 1) + n)
          (slotExtendIter (I := I) (M := M) g (s + 1) (s + 1) n (C t))
          (iteratedCovGrad (I := I) g 0 (s + 1) n W)).toFun := by
    simp only [slotStage, slotEnergy, oneMinusConnLapSmoothIter_zero]
  rw [show covGrad (I := I) (M := M) g 0 s U = W from rfl, hbase, ← htop]
  have hsplit :
      slotStage (I := I) (M := M) g (s + 1) 0 n (C t) W +
          (∑ i ∈ Finset.range n,
            tensorL2Inner (I := I) (M := M) g 0 (s + 1)
              (oneMinusConnLapSmoothIter (I := I) g 0 (s + 1) i
                (pointwiseTensorCurv (I := I) (M := M) g s
                  (oneMinusConnLapSmoothIter (I := I) g 0 s (n - 1 - i) U))).toFun
              (ccOperatorFieldComp (I := I) (M := M) g 0 (s + 1) (s + 1) (C t) W).toFun) -
          slotStage (I := I) (M := M) g (s + 1) n 0 (C t) W =
        (slotStage (I := I) (M := M) g (s + 1) 0 n (C t) W -
          slotStage (I := I) (M := M) g (s + 1) n 0 (C t) W) +
          ∑ i ∈ Finset.range n,
            tensorL2Inner (I := I) (M := M) g 0 (s + 1)
              (oneMinusConnLapSmoothIter (I := I) g 0 (s + 1) i
                (pointwiseTensorCurv (I := I) (M := M) g s
                  (oneMinusConnLapSmoothIter (I := I) g 0 s (n - 1 - i) U))).toFun
              (ccOperatorFieldComp (I := I) (M := M) g 0 (s + 1) (s + 1) (C t) W).toFun := by
    ring
  rw [hsplit]
  refine le_trans (abs_add_le _ _) ?_
  exact le_trans (add_le_add hmain hcurv) (le_of_eq (by ring))

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry
