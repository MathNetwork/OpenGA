import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingCm
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.L2Bound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.TensorConnLapGradientL2Bound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.IntegratedOrder2Garding
import DifferentialGeometry.Analysis.Integration.L2.Hilbert.DenseSubset


























































































noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E






def Order2GardingFamily (g : SmoothRiemannianMetric I M) (Cg : ℝ) : Prop :=
  0 ≤ Cg ∧ ∀ (s : ℕ) (S : SmoothCcTensor g 0 s),
    ‖covGrad (I := I) (M := M) g 0 (s + 1) (covGrad (I := I) (M := M) g 0 s S)‖ ^ 2 ≤
      Cg * (‖rawTensorConnLapSmooth (I := I) g 0 s S‖ ^ 2 + ‖S‖ ^ 2)






def Order1ControlFamily (g : SmoothRiemannianMetric I M) : Prop :=
  ∀ (s : ℕ) (S : SmoothCcTensor g 0 s),
    ‖covGrad (I := I) (M := M) g 0 s S‖ ^ 2 ≤
      ‖rawTensorConnLapSmooth (I := I) g 0 s S‖ * ‖S‖








def CommutatorDefectBound (g : SmoothRiemannianMetric I M) (Cc : ℝ) : Prop :=
  0 ≤ Cc ∧ ∀ (U : SmoothCcTensor g 0 2) (p : ℕ),
    ‖rawTensorConnLapSmooth (I := I) g 0 (2 + p)
          (iteratedCovGrad g 0 2 p U) -
        iteratedCovGrad g 0 2 p (rawTensorConnLapSmooth (I := I) g 0 2 U)‖ ≤
      Cc * ∑ i ∈ Finset.range (p + 2),
        ‖iteratedCovGrad g 0 2 i U‖


















def CurvatureCrossTermBound (g : SmoothRiemannianMetric I M) (Ccross : ℝ) : Prop :=
  0 ≤ Ccross ∧ ∀ (s : ℕ) (S : SmoothCcTensor g 0 s),
    - tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (rawTensorConnLapSmooth (I := I) g 0 (s + 1)
              (covGrad (I := I) (M := M) g 0 s S) -
            covGrad (I := I) (M := M) g 0 s
              (rawTensorConnLapSmooth (I := I) g 0 s S)).toFun
          (covGrad (I := I) (M := M) g 0 s S).toFun ≤
      Ccross *
        (tensorL2Norm (I := I) (M := M) g 0 (s + 1)
            (covGrad (I := I) (M := M) g 0 s S).toFun ^ 2 +
          tensorL2Norm (I := I) (M := M) g 0 s S.toFun *
            tensorL2Norm (I := I) (M := M) g 0 (s + 1)
              (covGrad (I := I) (M := M) g 0 s S).toFun)









theorem order2GardingFamily_of_curvatureCrossTermBound
    (g : SmoothRiemannianMetric I M) (Ccross : ℝ)
    (hcross : CurvatureCrossTermBound (I := I) (M := M) g Ccross) :
    Order2GardingFamily (I := I) (M := M) g (2 + 2 * Ccross) := by
  obtain ⟨hCcross, hcrossS⟩ := hcross
  refine ⟨by linarith, fun s S => ?_⟩
  rw [SmoothCcTensor.norm_def (I := I) (M := M)
      (covGrad (I := I) (M := M) g 0 (s + 1) (covGrad (I := I) (M := M) g 0 s S)),
    SmoothCcTensor.norm_def (I := I) (M := M) (rawTensorConnLapSmooth (I := I) g 0 s S),
    SmoothCcTensor.norm_def (I := I) (M := M) S]
  exact secondCovGrad_l2NormSq_le_of_cross_bound (I := I) (M := M) g s S Ccross hCcross
    (hcrossS s S)



omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma iteratedCovGrad_norm_eq_tensorL2Norm
    (g : SmoothRiemannianMetric I M) (j : ℕ) (U : SmoothCcTensor g 0 2) :
    ‖iteratedCovGrad g 0 2 j U‖ =
      tensorL2Norm (I := I) (M := M) g 0 (2 + j)
        (iteratedCovGrad g 0 2 j U).toFun :=
  SmoothCcTensor.norm_def (I := I) (M := M) (iteratedCovGrad g 0 2 j U)



omit [CompactSpace M] [I.Boundaryless] in
private lemma rawTensorConnLapIter_norm_eq_toL2
    (g : SmoothRiemannianMetric I M) (i : ℕ) (U : SmoothCcTensor g 0 2) :
    ‖rawTensorConnLapIter (I := I) g 0 2 i U‖ =
      ‖SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2)
        (rawTensorConnLapIter (I := I) g 0 2 i U)‖ :=
  (SmoothCcTensor.norm_toL2 (I := I) (M := M)
    (rawTensorConnLapIter (I := I) g 0 2 i U)).symm











private lemma gradOrder_l2Norm_le_lapIter_sum
    (g : SmoothRiemannianMetric I M) (Cg Cc : ℝ)
    (hgard : Order2GardingFamily (I := I) (M := M) g Cg)
    (hgrad1 : Order1ControlFamily (I := I) (M := M) g)
    (hcomm : CommutatorDefectBound (I := I) (M := M) g Cc) :
    ∃ Cmix : ℕ → ℝ, (∀ p, 0 ≤ Cmix p) ∧
      ∀ (p : ℕ) (U : SmoothCcTensor g 0 2),
        ‖iteratedCovGrad g 0 2 p U‖ ≤
          Cmix p * ∑ i ∈ Finset.range ((p + 1) / 2 + 1),
            ‖rawTensorConnLapIter (I := I) g 0 2 i U‖ := by
  classical
  obtain ⟨hCg, hgardS⟩ := hgard
  obtain ⟨hCc, hcommU⟩ := hcomm
  set sg : ℝ := Real.sqrt Cg with hsg_def
  have hsg_nn : 0 ≤ sg := Real.sqrt_nonneg _
  set K : ℝ := sg * (2 + Cc) with hK_def
  have hK_nn : 0 ≤ K := mul_nonneg hsg_nn (by linarith [hCc])
  let Bpair : ℕ → ℝ × ℝ := fun n => Nat.rec (motive := fun _ => ℝ × ℝ)
    (1, 1)
    (fun n prev =>
      let s := prev.2
      let b : ℝ := if n = 0 then 1 else K * s + 1
      (b, s + b))
    n
  let B : ℕ → ℝ := fun n => (Bpair n).1
  have hBfst_succ : ∀ n, (Bpair (n + 1)).1 =
      (if n = 0 then 1 else K * (Bpair n).2 + 1) := fun _ => rfl
  have hBsnd_succ : ∀ n, (Bpair (n + 1)).2 =
      (Bpair n).2 + (Bpair (n + 1)).1 := fun _ => rfl
  have hBsnd_zero : (Bpair 0).2 = 1 := rfl
  have hB0 : B 0 = 1 := rfl
  have hB1 : B 1 = 1 := rfl
  have hB_fst : ∀ n, B n = (Bpair n).1 := fun _ => rfl
  have hBpair_sum : ∀ n, (Bpair n).2 = ∑ i ∈ Finset.range (n + 1), B i := by
    intro n
    induction n with
    | zero => rw [hBsnd_zero, Finset.sum_range_one, hB0]
    | succ m ihm =>
        rw [Finset.sum_range_succ, ← ihm, hBsnd_succ m, hB_fst (m + 1)]
  have hBsucc_pos : ∀ n, B (n + 2) = K * (∑ i ∈ Finset.range (n + 2), B i) + 1 := by
    intro n
    rw [hB_fst (n + 2), hBfst_succ (n + 1)]
    simp only [Nat.succ_ne_zero, if_false]
    rw [hBpair_sum (n + 1)]
  have hB_nn : ∀ p, 0 ≤ B p := by
    intro p
    induction p using Nat.strong_induction_on with
    | _ n ih =>
      match n with
      | 0 => rw [hB0]; norm_num
      | 1 => rw [hB1]; norm_num
      | (m + 2) =>
          rw [hBsucc_pos m]
          have h2 : 0 ≤ ∑ i ∈ Finset.range (m + 2), B i :=
            Finset.sum_nonneg (fun i hi => ih i (by
              have := Finset.mem_range.mp hi; omega))
          have : 0 ≤ K * (∑ i ∈ Finset.range (m + 2), B i) := mul_nonneg hK_nn h2
          linarith
  have hBstep : ∀ m, sg * (B m + Cc * (∑ i ∈ Finset.range (m + 2), B i) + B m) + 1 ≤
      B (m + 2) := by
    intro m
    rw [hBsucc_pos m]
    have hBm_le : B m ≤ ∑ i ∈ Finset.range (m + 2), B i := by
      apply Finset.single_le_sum (f := B) (fun i _ => hB_nn i)
      rw [Finset.mem_range]; omega
    have hsum_nn : 0 ≤ ∑ i ∈ Finset.range (m + 2), B i :=
      Finset.sum_nonneg (fun i _ => hB_nn i)
    have hkey : sg * (B m + Cc * (∑ i ∈ Finset.range (m + 2), B i) + B m) ≤
        K * (∑ i ∈ Finset.range (m + 2), B i) := by
      rw [hK_def]
      have h1 : B m + Cc * (∑ i ∈ Finset.range (m + 2), B i) + B m ≤
          (2 + Cc) * (∑ i ∈ Finset.range (m + 2), B i) := by nlinarith [hBm_le, hCc, hsum_nn]
      calc sg * (B m + Cc * (∑ i ∈ Finset.range (m + 2), B i) + B m)
          ≤ sg * ((2 + Cc) * (∑ i ∈ Finset.range (m + 2), B i)) :=
            mul_le_mul_of_nonneg_left h1 hsg_nn
        _ = sg * (2 + Cc) * (∑ i ∈ Finset.range (m + 2), B i) := by ring
    linarith
  refine ⟨B, hB_nn, ?_⟩
  intro p
  induction p using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 =>
        intro U
        rw [iteratedCovGrad_zero]
        rw [hB0]
        have hsum : ∑ i ∈ Finset.range ((0 + 1) / 2 + 1),
            ‖rawTensorConnLapIter (I := I) g 0 2 i U‖ = ‖U‖ := by
          norm_num [rawTensorConnLapIter_zero]
        rw [hsum]; ring_nf; exact le_refl _
    | 1 =>
        intro U
        rw [hB1]
        have hord1 : ‖covGrad (I := I) (M := M) g 0 2 U‖ ^ 2 ≤
            ‖rawTensorConnLapSmooth (I := I) g 0 2 U‖ * ‖U‖ := hgrad1 2 U
        have hgrad_eq :
            iteratedCovGrad g 0 2 1 U = covGrad (I := I) (M := M) g 0 2 U := by
          rw [iteratedCovGrad_succ, iteratedCovGrad_zero]
        rw [hgrad_eq]
        have hsum : ∑ i ∈ Finset.range ((1 + 1) / 2 + 1),
              ‖rawTensorConnLapIter (I := I) g 0 2 i U‖ =
            ‖U‖ + ‖rawTensorConnLapSmooth (I := I) g 0 2 U‖ := by
          have : (1 + 1) / 2 + 1 = 2 := by norm_num
          rw [this]
          rw [Finset.sum_range_succ, Finset.sum_range_one]
          rw [rawTensorConnLapIter_zero, rawTensorConnLapIter_one]
        rw [hsum, one_mul]
        set a : ℝ := ‖rawTensorConnLapSmooth (I := I) g 0 2 U‖ with ha_def
        set b : ℝ := ‖U‖ with hb_def
        have ha_nn : 0 ≤ a := norm_nonneg _
        have hb_nn : 0 ≤ b := norm_nonneg _
        have hgrad_nn : 0 ≤ ‖covGrad (I := I) (M := M) g 0 2 U‖ := norm_nonneg _
        have hsqrt : ‖covGrad (I := I) (M := M) g 0 2 U‖ ≤ Real.sqrt (a * b) := by
          rw [← Real.sqrt_sq hgrad_nn]
          exact Real.sqrt_le_sqrt hord1
        have hamgm : Real.sqrt (a * b) ≤ b + a := by
          rw [← Real.sqrt_sq (by positivity : (0:ℝ) ≤ b + a)]
          apply Real.sqrt_le_sqrt
          nlinarith [sq_nonneg (a - b), ha_nn, hb_nn]
        linarith [hsqrt, hamgm]
    | (m + 2) =>
        intro U
        set S : SmoothCcTensor g 0 (2 + m) := iteratedCovGrad g 0 2 m U with hS_def
        have hgrad2_eq :
            iteratedCovGrad g 0 2 (m + 2) U =
              covGrad (I := I) (M := M) g 0 (2 + m + 1)
                (covGrad (I := I) (M := M) g 0 (2 + m) S) := by
          rw [hS_def]
          rfl
        have hgard2 :
            ‖covGrad (I := I) (M := M) g 0 (2 + m + 1)
                (covGrad (I := I) (M := M) g 0 (2 + m) S)‖ ^ 2 ≤
              Cg * (‖rawTensorConnLapSmooth (I := I) g 0 (2 + m) S‖ ^ 2 + ‖S‖ ^ 2) :=
          hgardS (2 + m) S
        set nHess : ℝ := ‖covGrad (I := I) (M := M) g 0 (2 + m + 1)
          (covGrad (I := I) (M := M) g 0 (2 + m) S)‖ with hnHess_def
        set nLapS : ℝ := ‖rawTensorConnLapSmooth (I := I) g 0 (2 + m) S‖ with hnLapS_def
        set nS : ℝ := ‖S‖ with hnS_def
        have hnHess_nn : 0 ≤ nHess := norm_nonneg _
        have hnLapS_nn : 0 ≤ nLapS := norm_nonneg _
        have hnS_nn : 0 ≤ nS := norm_nonneg _
        have hgard_fp : nHess ≤ sg * (nLapS + nS) := by
          rw [hsg_def]
          rw [← Real.sqrt_sq hnHess_nn]
          calc Real.sqrt (nHess ^ 2)
              ≤ Real.sqrt (Cg * (nLapS ^ 2 + nS ^ 2)) := Real.sqrt_le_sqrt hgard2
            _ = Real.sqrt Cg * Real.sqrt (nLapS ^ 2 + nS ^ 2) := by
                  rw [Real.sqrt_mul hCg]
            _ ≤ Real.sqrt Cg * (nLapS + nS) := by
                  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
                  rw [← Real.sqrt_sq (by positivity : (0:ℝ) ≤ nLapS + nS)]
                  apply Real.sqrt_le_sqrt
                  nlinarith [mul_nonneg hnLapS_nn hnS_nn]
        have hΔS_eq : rawTensorConnLapSmooth (I := I) g 0 (2 + m) S =
            rawTensorConnLapSmooth (I := I) g 0 (2 + m) (iteratedCovGrad g 0 2 m U) := by
          rw [hS_def]
        have hcomm_m := hcommU U m
        have hnLapS_eq : nLapS =
            ‖rawTensorConnLapSmooth (I := I) g 0 (2 + m) (iteratedCovGrad g 0 2 m U)‖ := by
          rw [hnLapS_def, hΔS_eq]
        set DefM : SmoothCcTensor g 0 (2 + m) :=
          iteratedCovGrad g 0 2 m (rawTensorConnLapSmooth (I := I) g 0 2 U) with hDefM_def
        have htri :
            ‖rawTensorConnLapSmooth (I := I) g 0 (2 + m) (iteratedCovGrad g 0 2 m U)‖ ≤
              ‖DefM‖ +
                ‖rawTensorConnLapSmooth (I := I) g 0 (2 + m)
                    (iteratedCovGrad g 0 2 m U) - DefM‖ :=
          norm_le_norm_add_norm_sub'
            (rawTensorConnLapSmooth (I := I) g 0 (2 + m) (iteratedCovGrad g 0 2 m U)) DefM
        have hdef_bound :
            ‖rawTensorConnLapSmooth (I := I) g 0 (2 + m)
                  (iteratedCovGrad g 0 2 m U) - DefM‖ ≤
              Cc * ∑ i ∈ Finset.range (m + 2), ‖iteratedCovGrad g 0 2 i U‖ := by
          rw [hDefM_def]; exact hcomm_m
        have hih_base :
            ‖DefM‖ ≤ B m * ∑ i ∈ Finset.range ((m + 1) / 2 + 1),
              ‖rawTensorConnLapIter (I := I) g 0 2 i
                (rawTensorConnLapSmooth (I := I) g 0 2 U)‖ := by
          rw [hDefM_def]
          exact ih m (by omega) (rawTensorConnLapSmooth (I := I) g 0 2 U)
        have hlapiter_shift : ∀ i,
            rawTensorConnLapIter (I := I) g 0 2 i
                (rawTensorConnLapSmooth (I := I) g 0 2 U) =
              rawTensorConnLapIter (I := I) g 0 2 (i + 1) U := by
          intro i
          induction i with
          | zero => simp [rawTensorConnLapIter]
          | succ n ihn =>
              rw [rawTensorConnLapIter_succ, ihn, ← rawTensorConnLapIter_succ]
        have hih_low : ∀ i, i < m + 2 →
            ‖iteratedCovGrad g 0 2 i U‖ ≤
              B i * ∑ j ∈ Finset.range ((i + 1) / 2 + 1),
                ‖rawTensorConnLapIter (I := I) g 0 2 j U‖ :=
          fun i hi => ih i hi U
        set Rfull : ℕ := ((m + 2) + 1) / 2 + 1 with hRfull_def
        set Sfull : ℝ := ∑ i ∈ Finset.range Rfull,
          ‖rawTensorConnLapIter (I := I) g 0 2 i U‖ with hSfull_def
        have hSfull_nn : 0 ≤ Sfull :=
          Finset.sum_nonneg (fun i _ => norm_nonneg _)
        have hbase_le_full :
            ∑ i ∈ Finset.range ((m + 1) / 2 + 1),
                ‖rawTensorConnLapIter (I := I) g 0 2 i
                  (rawTensorConnLapSmooth (I := I) g 0 2 U)‖ ≤ Sfull := by
          rw [hSfull_def]
          have hrw : ∑ i ∈ Finset.range ((m + 1) / 2 + 1),
                ‖rawTensorConnLapIter (I := I) g 0 2 i
                  (rawTensorConnLapSmooth (I := I) g 0 2 U)‖ =
              ∑ i ∈ Finset.range ((m + 1) / 2 + 1),
                ‖rawTensorConnLapIter (I := I) g 0 2 (i + 1) U‖ := by
            apply Finset.sum_congr rfl
            intro i _; rw [hlapiter_shift i]
          rw [hrw]
          have hshift : ∑ i ∈ Finset.range ((m + 1) / 2 + 1),
                ‖rawTensorConnLapIter (I := I) g 0 2 (i + 1) U‖ =
              ∑ i ∈ Finset.Ico 1 ((m + 1) / 2 + 2),
                ‖rawTensorConnLapIter (I := I) g 0 2 i U‖ := by
            rw [Finset.sum_Ico_eq_sum_range]
            apply Finset.sum_congr (by norm_num) (fun i _ => by ring_nf)
          rw [hshift]
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro x hx
            rw [Finset.mem_Ico] at hx
            rw [Finset.mem_range]
            rw [hRfull_def]; omega
          · intro i _ _; exact norm_nonneg _
        have hlow_sub_le_full : ∀ i, i < m + 2 →
            ∑ j ∈ Finset.range ((i + 1) / 2 + 1),
                ‖rawTensorConnLapIter (I := I) g 0 2 j U‖ ≤ Sfull := by
          intro i hi
          rw [hSfull_def]
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro x hx
            rw [Finset.mem_range] at hx ⊢
            rw [hRfull_def]; omega
          · intro j _ _; exact norm_nonneg _
        have hSlow_nn : 0 ≤ ∑ i ∈ Finset.range (m + 2), ‖iteratedCovGrad g 0 2 i U‖ :=
          Finset.sum_nonneg (fun i _ => norm_nonneg _)
        have hnLapS_le :
            nLapS ≤ B m * Sfull
              + Cc * ∑ i ∈ Finset.range (m + 2), ‖iteratedCovGrad g 0 2 i U‖ := by
          rw [hnLapS_eq]
          calc ‖rawTensorConnLapSmooth (I := I) g 0 (2 + m) (iteratedCovGrad g 0 2 m U)‖
              ≤ ‖DefM‖ + ‖rawTensorConnLapSmooth (I := I) g 0 (2 + m)
                    (iteratedCovGrad g 0 2 m U) - DefM‖ := htri
            _ ≤ (B m * ∑ i ∈ Finset.range ((m + 1) / 2 + 1),
                    ‖rawTensorConnLapIter (I := I) g 0 2 i
                      (rawTensorConnLapSmooth (I := I) g 0 2 U)‖)
                  + Cc * ∑ i ∈ Finset.range (m + 2), ‖iteratedCovGrad g 0 2 i U‖ :=
                add_le_add hih_base hdef_bound
            _ ≤ B m * Sfull
                  + Cc * ∑ i ∈ Finset.range (m + 2), ‖iteratedCovGrad g 0 2 i U‖ := by
                have hb := mul_le_mul_of_nonneg_left hbase_le_full (hB_nn m)
                linarith [hb]
        have hSlow_le :
            ∑ i ∈ Finset.range (m + 2), ‖iteratedCovGrad g 0 2 i U‖ ≤
              (∑ i ∈ Finset.range (m + 2), B i) * Sfull := by
          rw [Finset.sum_mul]
          apply Finset.sum_le_sum
          intro i hi
          rw [Finset.mem_range] at hi
          calc ‖iteratedCovGrad g 0 2 i U‖
              ≤ B i * ∑ j ∈ Finset.range ((i + 1) / 2 + 1),
                  ‖rawTensorConnLapIter (I := I) g 0 2 j U‖ := hih_low i hi
            _ ≤ B i * Sfull :=
                mul_le_mul_of_nonneg_left (hlow_sub_le_full i hi) (hB_nn i)
        have hnS_le : nS ≤ B m * Sfull := by
          rw [hnS_def, hS_def]
          calc ‖iteratedCovGrad g 0 2 m U‖
              ≤ B m * ∑ j ∈ Finset.range ((m + 1) / 2 + 1),
                  ‖rawTensorConnLapIter (I := I) g 0 2 j U‖ := ih m (by omega) U
            _ ≤ B m * Sfull :=
                mul_le_mul_of_nonneg_left (hlow_sub_le_full m (by omega)) (hB_nn m)
        have hcombine : nLapS + nS ≤
            (B m + Cc * (∑ i ∈ Finset.range (m + 2), B i) + B m) * Sfull := by
          have h1 : nLapS ≤ B m * Sfull + Cc * ((∑ i ∈ Finset.range (m + 2), B i) * Sfull) := by
            calc nLapS ≤ B m * Sfull
                  + Cc * ∑ i ∈ Finset.range (m + 2), ‖iteratedCovGrad g 0 2 i U‖ := hnLapS_le
              _ ≤ B m * Sfull + Cc * ((∑ i ∈ Finset.range (m + 2), B i) * Sfull) := by
                  have hc := mul_le_mul_of_nonneg_left hSlow_le hCc
                  linarith [hc]
          nlinarith [h1, hnS_le, hSfull_nn]
        have hfinal : nHess ≤ B (m + 2) * Sfull := by
          have hstep := hBstep m
          calc nHess ≤ sg * (nLapS + nS) := hgard_fp
            _ ≤ sg * ((B m + Cc * (∑ i ∈ Finset.range (m + 2), B i) + B m) * Sfull) := by
                exact mul_le_mul_of_nonneg_left hcombine hsg_nn
            _ = (sg * (B m + Cc * (∑ i ∈ Finset.range (m + 2), B i) + B m)) * Sfull := by ring
            _ ≤ B (m + 2) * Sfull := by
                have hle : sg * (B m + Cc * (∑ i ∈ Finset.range (m + 2), B i) + B m) ≤
                    B (m + 2) := by linarith [hstep]
                exact mul_le_mul_of_nonneg_right hle hSfull_nn
        have hLHS : ‖iteratedCovGrad g 0 2 (m + 2) U‖ = nHess := by
          rw [hgrad2_eq, hnHess_def]
        have hRHS : (B (m + 2) * ∑ i ∈ Finset.range (((m + 2) + 1) / 2 + 1),
              ‖rawTensorConnLapIter (I := I) g 0 2 i U‖) = B (m + 2) * Sfull := by
          rw [hSfull_def, hRfull_def]
        rw [hLHS, hRHS]
        exact hfinal

























theorem allOrder_covGrad_l2Norm_le_lapIter_sum
    (g : SmoothRiemannianMetric I M) (Cg Cc : ℝ) (k : ℕ)
    (hgard : Order2GardingFamily (I := I) (M := M) g Cg)
    (hgrad1 : Order1ControlFamily (I := I) (M := M) g)
    (hcomm : CommutatorDefectBound (I := I) (M := M) g Cc) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : SmoothCcTensor g 0 2),
        ∑ j ∈ Finset.range (2 * k + 1),
            tensorL2Norm (I := I) (M := M) g 0 (2 + j)
              (iteratedCovGrad g 0 2 j T).toFun ≤
          C * ∑ i ∈ Finset.range (k + 1),
            ‖SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2)
              (rawTensorConnLapIter (I := I) g 0 2 i T)‖ := by
  classical
  obtain ⟨Cmix, hCmix_nn, hmix⟩ :=
    gradOrder_l2Norm_le_lapIter_sum (I := I) (M := M) g Cg Cc hgard hgrad1 hcomm
  set Cmax : ℝ := ∑ j ∈ Finset.range (2 * k + 1), Cmix j with hCmax_def
  have hCmax_nn : 0 ≤ Cmax :=
    Finset.sum_nonneg (fun j _ => hCmix_nn j)
  refine ⟨Cmax, hCmax_nn, fun T => ?_⟩
  have hLHS_eq : ∀ j,
      tensorL2Norm (I := I) (M := M) g 0 (2 + j) (iteratedCovGrad g 0 2 j T).toFun =
        ‖iteratedCovGrad g 0 2 j T‖ :=
    fun j => (iteratedCovGrad_norm_eq_tensorL2Norm (I := I) (M := M) g j T).symm
  have hRHS_eq : ∀ i,
      ‖SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2)
          (rawTensorConnLapIter (I := I) g 0 2 i T)‖ =
        ‖rawTensorConnLapIter (I := I) g 0 2 i T‖ :=
    fun i => (rawTensorConnLapIter_norm_eq_toL2 (I := I) (M := M) g i T).symm
  rw [Finset.sum_congr rfl (fun j _ => hLHS_eq j),
      Finset.sum_congr rfl (fun i _ => hRHS_eq i)]
  set Sk : ℝ := ∑ i ∈ Finset.range (k + 1), ‖rawTensorConnLapIter (I := I) g 0 2 i T‖
    with hSk_def
  have hSk_nn : 0 ≤ Sk := Finset.sum_nonneg (fun i _ => norm_nonneg _)
  have hper : ∀ j ∈ Finset.range (2 * k + 1),
      ‖iteratedCovGrad g 0 2 j T‖ ≤ Cmix j * Sk := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hsub_le : ∑ i ∈ Finset.range ((j + 1) / 2 + 1),
          ‖rawTensorConnLapIter (I := I) g 0 2 i T‖ ≤ Sk := by
      rw [hSk_def]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro x hx
        rw [Finset.mem_range] at hx ⊢
        omega
      · intro i _ _; exact norm_nonneg _
    calc ‖iteratedCovGrad g 0 2 j T‖
        ≤ Cmix j * ∑ i ∈ Finset.range ((j + 1) / 2 + 1),
            ‖rawTensorConnLapIter (I := I) g 0 2 i T‖ := hmix j T
      _ ≤ Cmix j * Sk := mul_le_mul_of_nonneg_left hsub_le (hCmix_nn j)
  calc ∑ j ∈ Finset.range (2 * k + 1), ‖iteratedCovGrad g 0 2 j T‖
      ≤ ∑ j ∈ Finset.range (2 * k + 1), Cmix j * Sk := Finset.sum_le_sum hper
    _ = (∑ j ∈ Finset.range (2 * k + 1), Cmix j) * Sk := by rw [Finset.sum_mul]
    _ = Cmax * Sk := by rw [hCmax_def]



theorem order1Control_rank_two
    (g : SmoothRiemannianMetric I M) (S : SmoothCcTensor g 0 2) :
    ‖covGrad (I := I) (M := M) g 0 2 S‖ ^ 2 ≤
      ‖rawTensorConnLapSmooth (I := I) g 0 2 S‖ * ‖S‖ := by
  rw [SmoothCcTensor.norm_def (I := I) (M := M) (covGrad (I := I) (M := M) g 0 2 S),
    SmoothCcTensor.norm_def (I := I) (M := M) (rawTensorConnLapSmooth (I := I) g 0 2 S),
    SmoothCcTensor.norm_def (I := I) (M := M) S]
  exact covGrad_l2NormSq_le_rawConnLap_mul_self (I := I) (M := M) g S








theorem order1ControlFamily_holds (g : SmoothRiemannianMetric I M) :
    Order1ControlFamily (I := I) (M := M) g := by
  intro s S
  rw [SmoothCcTensor.norm_def (I := I) (M := M) (covGrad (I := I) (M := M) g 0 s S),
    SmoothCcTensor.norm_def (I := I) (M := M) (rawTensorConnLapSmooth (I := I) g 0 s S),
    SmoothCcTensor.norm_def (I := I) (M := M) S]
  exact covGrad_l2NormSq_le_rawConnLap_mul_self_gen (I := I) (M := M) g s S







theorem order2Garding_rank_two_of_pointwise_curv_bound
    (g : SmoothRiemannianMetric I M) (S : SmoothCcTensor g 0 2) (C₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 3 x
          ((covGradRoughLapCurv (I := I) (M := M) g S).toSection x) ≤
        C₀ ^ 2 *
          (riemannianFiberNormSq (I := I) (M := M) g 0 2 x (S.toSection x) +
            riemannianFiberNormSq (I := I) (M := M) g 0 3 x
              ((covGrad (I := I) (M := M) g 0 2 S).toSection x) +
            riemannianFiberNormSq (I := I) (M := M) g 0 (3 + 1) x
              ((covGrad (I := I) (M := M) g 0 3
                (covGrad (I := I) (M := M) g 0 2 S)).toSection x))) :
    ‖covGrad (I := I) (M := M) g 0 (2 + 1) (covGrad (I := I) (M := M) g 0 2 S)‖ ^ 2 ≤
      (2 + 3 * C₀ + 2 * C₀ ^ 2) *
        (‖rawTensorConnLapSmooth (I := I) g 0 2 S‖ ^ 2 + ‖S‖ ^ 2) := by
  rw [SmoothCcTensor.norm_def (I := I) (M := M)
      (covGrad (I := I) (M := M) g 0 (2 + 1) (covGrad (I := I) (M := M) g 0 2 S)),
    SmoothCcTensor.norm_def (I := I) (M := M) (rawTensorConnLapSmooth (I := I) g 0 2 S),
    SmoothCcTensor.norm_def (I := I) (M := M) S]
  exact secondCovGrad_l2NormSq_le_rawConnLap_of_pointwise_curv_bound
    (I := I) (M := M) g S C₀ hC₀ hpt

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
