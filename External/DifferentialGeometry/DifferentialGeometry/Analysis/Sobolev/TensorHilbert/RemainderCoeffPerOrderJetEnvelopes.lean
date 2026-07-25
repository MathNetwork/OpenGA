import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RicciDeTurckArmCoeffPerOrderJetTower
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.ConvexPerturbationPointwiseC2
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceJetTower
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.InverseMetricRaisedEndomorphismJetBound
import DifferentialGeometry.Analysis.Sobolev.GagliardoNirenbergLpFiberNorm
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderHigherOrderTame
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckPrincipalCometricExtraction
import Mathlib.Analysis.MeanInequalities


noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Tensor0SBundle ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Integral.Connection

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (ricciArmOrder0RiemannCoeff raisedKoszul)
open DifferentialGeometry.PDE.DeTurck.RicciLinearization (realizedFam)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

section L2OutputFeeder

open DifferentialGeometry.PDE.DeTurck.RicciLinearization
  (convexPerturbation convexPerturbation_gFibreOpBound realizedFam_inner_of_mem
    Icc_subset_realizedSmallSet realizedSmallSet)

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem iteratedCovGrad_smul_real (g : SmoothRiemannianMetric I M) (r s j : ℕ) (c : ℝ)
    (w : SmoothCcTensor g r s) :
    iteratedCovGrad (I := I) g r s j (c • w) = c • iteratedCovGrad (I := I) g r s j w := by
  induction j with
  | zero => simp only [iteratedCovGrad_zero]
  | succ j ih => rw [iteratedCovGrad_succ, iteratedCovGrad_succ, ih,
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad_smul]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem diagonalProductTerm_integral_le
    (g₀ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2)
    {R : ℝ} (hR : 0 ≤ R)
    (i : ℕ) (hi1 : 1 ≤ i)
    {Λ : ℝ} (hΛ_nn : 0 ≤ Λ)
    (hΛsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (P.toSection x) ≤ Λ ^ 2)
    (hNi : ‖iteratedCovGrad (I := I) g₀ 0 2 i P‖ ≤ R)
    {C : ℝ} (hC_nn : 0 ≤ C)
    (hGNP : ∀ j : ℕ, 0 < j → j < i →
      (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
              ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) ^ ((i : ℝ) / (j : ℝ))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ^ ((j : ℝ) / (i : ℝ)) ≤
        C * Λ ^ (2 * (1 - (j : ℝ) / (i : ℝ))) * R ^ (2 * (j : ℝ) / (i : ℝ)))
    (n : ℕ) (hn_le : n ≤ i) (e : Fin n → ℕ) (he : ∑ m, e m = i) :
    MeasureTheory.Integrable
        (fun x => ∏ m : Fin n,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
        (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
      (∫ x, ∏ m : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
        (i : ℝ) * (max Λ (max R (max C 1))) ^ (7 * i) := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  set μ : MeasureTheory.Measure M := riemannianVolumeMeasure (I := I) (M := M) g₀ with hμ
  haveI : IsFiniteMeasure μ := by rw [hμ]; infer_instance
  have hi_pos : 0 < i := hi1
  have hiR_pos : (0 : ℝ) < (i : ℝ) := by exact_mod_cast hi_pos
  have hiR_ne : (i : ℝ) ≠ 0 := ne_of_gt hiR_pos
  have hnn : ∀ (j : ℕ) (x : M),
      0 ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x) :=
    fun j x => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j) x _
  have hcont : ∀ j : ℕ, Continuous (fun x => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
      ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) := by
    intro j
    have hc := Integral.L2.SmoothCcTensor.continuous_inner_self (I := I) (M := M)
      (iteratedCovGrad (I := I) g₀ 0 2 j P)
    refine hc.congr (fun x => ?_)
    rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x),
      ← Integral.L2.SmoothCcTensor.toFun_apply (I := I) (M := M)
        (iteratedCovGrad (I := I) g₀ 0 2 j P) x]
  have hint : ∀ j : ℕ, MeasureTheory.Integrable
      (fun x => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) μ := by
    intro j
    rw [hμ]
    exact integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 0 (2 + j)
      (iteratedCovGrad (I := I) g₀ 0 2 j P)
  have hint_rpow : ∀ (j : ℕ) (p : ℝ), 0 ≤ p → MeasureTheory.Integrable
      (fun x => (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) ^ p) μ := by
    intro j p hp
    have hcp : Continuous (fun x => (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) ^ p) :=
      (hcont j).rpow_const (fun x => Or.inr hp)
    exact hcp.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hint_prod : MeasureTheory.Integrable
      (fun x => ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) μ := by
    have hcp : Continuous (fun x => ∏ m : Fin n,
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) :=
      continuous_finset_prod Finset.univ (fun m _ => hcont (e m))
    exact hcp.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  refine ⟨hint_prod, ?_⟩
  set Mbar : ℝ := max Λ (max R (max C 1)) with hMbar
  have hMbar1 : (1 : ℝ) ≤ Mbar :=
    le_trans (le_max_right C 1) (le_trans (le_max_right R _) (le_max_right Λ _))
  have hMbar_nn : 0 ≤ Mbar := le_trans zero_le_one hMbar1
  have hΛ_le : Λ ≤ Mbar := le_max_left _ _
  have hR_le : R ≤ Mbar := le_trans (le_max_left R _) (le_max_right Λ _)
  have hC_le : C ≤ Mbar :=
    le_trans (le_trans (le_max_left C 1) (le_max_right R _)) (le_max_right Λ _)
  set Sset : Finset (Fin n) := Finset.univ.filter (fun m => 0 < e m) with hSset
  set Zset : Finset (Fin n) := Finset.univ.filter (fun m => ¬ (0 < e m)) with hZset
  have hsplit : ∀ x : M,
      (∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) =
        (∏ m ∈ Sset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) *
          (∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) := by
    intro x
    rw [hSset, hZset]
    exact (Finset.prod_filter_mul_prod_filter_not Finset.univ (fun m => 0 < e m)
      (fun m => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))).symm
  have hZbound : ∀ x : M,
      (∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ≤ Λ ^ (2 * Zset.card) := by
    intro x
    calc (∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
        ≤ ∏ _m ∈ Zset, Λ ^ 2 := by
          apply Finset.prod_le_prod (fun m _ => hnn (e m) x)
          intro m hm
          have hem0 : e m = 0 := by have := (Finset.mem_filter.mp hm).2; omega
          rw [hem0]; exact hΛsup x
      _ = Λ ^ (2 * Zset.card) := by rw [Finset.prod_const, ← pow_mul]
  have hZsum0 : ∑ m ∈ Zset, e m = 0 := by
    apply Finset.sum_eq_zero
    intro m hm
    have := (Finset.mem_filter.mp hm).2; omega
  have hSsum : ∑ m ∈ Sset, e m = i := by
    have h := Finset.sum_filter_add_sum_filter_not Finset.univ (fun m => 0 < e m) e
    rw [← hSset, ← hZset, hZsum0, add_zero, he] at h
    exact h
  have hScard_pos : 1 ≤ Sset.card := by
    rcases Nat.eq_zero_or_pos Sset.card with h0 | hp
    · exfalso
      rw [Finset.card_eq_zero] at h0
      rw [h0, Finset.sum_empty] at hSsum
      omega
    · exact hp
  rcases Nat.lt_or_ge Sset.card 2 with hScard_lt2 | hScard_ge2
  · have hScard1 : Sset.card = 1 := by omega
    obtain ⟨m₀, hm₀⟩ := Finset.card_eq_one.mp hScard1
    have hem₀ : e m₀ = i := by
      have hss : ∑ m ∈ Sset, e m = e m₀ := by rw [hm₀, Finset.sum_singleton]
      rw [hss] at hSsum; exact hSsum
    have hSprod : ∀ x : M,
        (∏ m ∈ Sset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) =
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x) := by
      intro x; rw [hm₀, Finset.prod_singleton, hem₀]
    have hpt : ∀ x : M,
        (∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ≤
          Λ ^ (2 * Zset.card) * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x) := by
      intro x
      rw [hsplit x, hSprod x]
      calc (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
              ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x)) *
            (∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
          ≤ (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
              ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x)) * Λ ^ (2 * Zset.card) :=
            mul_le_mul_of_nonneg_left (hZbound x) (hnn i x)
        _ = Λ ^ (2 * Zset.card) * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
              ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x) := mul_comm _ _
    have hintFi : (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x) ∂μ) ≤ R ^ 2 := by
      have heq : (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x) ∂μ) =
          ‖iteratedCovGrad (I := I) g₀ 0 2 i P‖ ^ 2 := by
        rw [SmoothCcTensor.norm_def (iteratedCovGrad (I := I) g₀ 0 2 i P), hμ]
        exact (tensorL2Norm_sq_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i)
          ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection)).symm
      rw [heq]
      nlinarith [hNi, norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 i P), hR]
    have hΛZ_nn : 0 ≤ Λ ^ (2 * Zset.card) := pow_nonneg hΛ_nn _
    calc (∫ x, ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x) ∂μ)
        ≤ ∫ x, Λ ^ (2 * Zset.card) * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x) ∂μ :=
          MeasureTheory.integral_mono hint_prod ((hint i).const_mul _) hpt
      _ = Λ ^ (2 * Zset.card) * ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x) ∂μ :=
          MeasureTheory.integral_const_mul _ _
      _ ≤ Λ ^ (2 * Zset.card) * R ^ 2 := mul_le_mul_of_nonneg_left hintFi hΛZ_nn
      _ ≤ (i : ℝ) * Mbar ^ (7 * i) := by
          have hZle : Zset.card ≤ i := le_trans (Finset.card_le_univ _) (by simpa using hn_le)
          have e1 : Λ ^ (2 * Zset.card) ≤ Mbar ^ (2 * i) :=
            le_trans (pow_le_pow_left₀ hΛ_nn hΛ_le _)
              (pow_le_pow_right₀ hMbar1 (by omega))
          have e2 : R ^ 2 ≤ Mbar ^ 2 := pow_le_pow_left₀ hR hR_le 2
          have e3 : Mbar ^ (2 * i) * Mbar ^ 2 ≤ Mbar ^ (7 * i) := by
            rw [← pow_add]
            exact pow_le_pow_right₀ hMbar1 (by omega)
          have e4 : Λ ^ (2 * Zset.card) * R ^ 2 ≤ Mbar ^ (2 * i) * Mbar ^ 2 :=
            mul_le_mul e1 e2 (by positivity) (by positivity)
          have e5 : Mbar ^ (7 * i) ≤ (i : ℝ) * Mbar ^ (7 * i) := by
            have : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi1
            nlinarith [pow_nonneg hMbar_nn (7 * i)]
          calc Λ ^ (2 * Zset.card) * R ^ 2 ≤ Mbar ^ (2 * i) * Mbar ^ 2 := e4
            _ ≤ Mbar ^ (7 * i) := e3
            _ ≤ (i : ℝ) * Mbar ^ (7 * i) := e5
  · have hem_lt : ∀ m ∈ Sset, e m < i := by
      intro m hm
      have hmpos : 0 < e m := (Finset.mem_filter.mp hm).2
      have hadd : e m + ∑ m' ∈ Sset.erase m, e m' = ∑ m' ∈ Sset, e m' :=
        Finset.add_sum_erase Sset e hm
      rw [hSsum] at hadd
      have herase_ne : (Sset.erase m).Nonempty := by
        rw [← Finset.card_pos, Finset.card_erase_of_mem hm]; omega
      obtain ⟨m', hm'⟩ := herase_ne
      have hm'S : m' ∈ Sset := Finset.mem_of_mem_erase hm'
      have hm'pos : 1 ≤ e m' := (Finset.mem_filter.mp hm'S).2
      have hle : e m' ≤ ∑ m'' ∈ Sset.erase m, e m'' :=
        Finset.single_le_sum (fun k _ => Nat.zero_le _) hm'
      omega
    have hAMGM : ∀ x : M,
        (∏ m ∈ Sset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ≤
          ∑ m ∈ Sset, ((e m : ℝ) / i) *
            (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) := by
      intro x
      have hw_nn : ∀ m ∈ Sset, 0 ≤ (e m : ℝ) / i := fun m _ => by positivity
      have hw_sum : ∑ m ∈ Sset, (e m : ℝ) / i = 1 := by
        rw [← Finset.sum_div]
        rw [show (∑ m ∈ Sset, (e m : ℝ)) = ((i : ℕ) : ℝ) from by
          rw [← Nat.cast_sum]; exact_mod_cast hSsum]
        exact div_self hiR_ne
      have hz_nn : ∀ m ∈ Sset, 0 ≤ (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) :=
        fun m _ => Real.rpow_nonneg (hnn (e m) x) _
      have hAM := Real.geom_mean_le_arith_mean_weighted Sset (fun m => (e m : ℝ) / i)
        (fun m => (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)))
        hw_nn hw_sum hz_nn
      have hLHS : (∏ m ∈ Sset, ((riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)))
            ^ ((e m : ℝ) / i)) =
          ∏ m ∈ Sset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x) := by
        apply Finset.prod_congr rfl
        intro m hm
        have hmpos : 0 < e m := (Finset.mem_filter.mp hm).2
        have hemR_ne : (e m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hmpos.ne'
        rw [← Real.rpow_mul (hnn (e m) x)]
        rw [show ((i : ℝ) / (e m : ℝ)) * ((e m : ℝ) / i) = 1 by field_simp]
        rw [Real.rpow_one]
      rw [hLHS] at hAM
      exact hAM
    have hfactor : ∀ m ∈ Sset,
        (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ) ≤
          Mbar ^ (5 * i) := by
      intro m hm
      have hmpos : 0 < e m := (Finset.mem_filter.mp hm).2
      have hem_lt_i : e m < i := hem_lt m hm
      have hemR_pos : (0 : ℝ) < (e m : ℝ) := by exact_mod_cast hmpos
      have hemR_ne : (e m : ℝ) ≠ 0 := ne_of_gt hemR_pos
      have hgn := hGNP (e m) hmpos hem_lt_i
      set Ival : ℝ := ∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ
        with hIval
      have hIval_nn : 0 ≤ Ival := by
        rw [hIval]; exact integral_nonneg (fun x => Real.rpow_nonneg (hnn (e m) x) _)
      have hθ_nn : 0 ≤ (e m : ℝ) / i := by positivity
      have hθ_le1 : (e m : ℝ) / i ≤ 1 := by
        rw [div_le_one hiR_pos]; exact_mod_cast Nat.le_of_lt hem_lt_i
      have hexp1_nn : 0 ≤ 2 * (1 - (e m : ℝ) / i) := by nlinarith
      have hexp1_le : 2 * (1 - (e m : ℝ) / i) ≤ 2 := by nlinarith
      have hexp2_nn : 0 ≤ 2 * (e m : ℝ) / i := by positivity
      have hexp2_le : 2 * (e m : ℝ) / i ≤ 2 := by
        rw [mul_div_assoc]; nlinarith
      have hΛpow : Λ ^ (2 * (1 - (e m : ℝ) / i)) ≤ Mbar ^ (2 : ℕ) := by
        calc Λ ^ (2 * (1 - (e m : ℝ) / i)) ≤ Mbar ^ (2 * (1 - (e m : ℝ) / i)) :=
              Real.rpow_le_rpow hΛ_nn hΛ_le hexp1_nn
          _ ≤ Mbar ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hMbar1 hexp1_le
          _ = Mbar ^ (2 : ℕ) := by rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      have hRpow : R ^ (2 * (e m : ℝ) / i) ≤ Mbar ^ (2 : ℕ) := by
        calc R ^ (2 * (e m : ℝ) / i) ≤ Mbar ^ (2 * (e m : ℝ) / i) :=
              Real.rpow_le_rpow hR hR_le hexp2_nn
          _ ≤ Mbar ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hMbar1 hexp2_le
          _ = Mbar ^ (2 : ℕ) := by rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      have hbase_le : C * Λ ^ (2 * (1 - (e m : ℝ) / i)) * R ^ (2 * (e m : ℝ) / i) ≤
          Mbar ^ (5 : ℕ) := by
        have h1 : C * Λ ^ (2 * (1 - (e m : ℝ) / i)) ≤ Mbar * Mbar ^ (2 : ℕ) :=
          mul_le_mul hC_le hΛpow (Real.rpow_nonneg hΛ_nn _) hMbar_nn
        have h2 : C * Λ ^ (2 * (1 - (e m : ℝ) / i)) * R ^ (2 * (e m : ℝ) / i) ≤
            Mbar * Mbar ^ (2 : ℕ) * Mbar ^ (2 : ℕ) :=
          mul_le_mul h1 hRpow (Real.rpow_nonneg hR _) (by positivity)
        calc C * Λ ^ (2 * (1 - (e m : ℝ) / i)) * R ^ (2 * (e m : ℝ) / i)
            ≤ Mbar * Mbar ^ (2 : ℕ) * Mbar ^ (2 : ℕ) := h2
          _ = Mbar ^ (5 : ℕ) := by ring
      have hbase_nn : 0 ≤ C * Λ ^ (2 * (1 - (e m : ℝ) / i)) * R ^ (2 * (e m : ℝ) / i) := by
        apply mul_nonneg (mul_nonneg hC_nn (Real.rpow_nonneg hΛ_nn _)) (Real.rpow_nonneg hR _)
      have hIval_eq : Ival = (Ival ^ ((e m : ℝ) / i)) ^ ((i : ℝ) / (e m : ℝ)) := by
        rw [← Real.rpow_mul hIval_nn]
        rw [show ((e m : ℝ) / i) * ((i : ℝ) / (e m : ℝ)) = 1 by field_simp]
        rw [Real.rpow_one]
      have hM5_one : (1 : ℝ) ≤ Mbar ^ (5 : ℕ) :=
        le_trans hMbar1 (le_self_pow₀ hMbar1 (by norm_num))
      have hidiv : (i : ℝ) / (e m : ℝ) ≤ (i : ℝ) :=
        div_le_self hiR_pos.le (by exact_mod_cast hmpos)
      calc Ival = (Ival ^ ((e m : ℝ) / i)) ^ ((i : ℝ) / (e m : ℝ)) := hIval_eq
        _ ≤ (C * Λ ^ (2 * (1 - (e m : ℝ) / i)) * R ^ (2 * (e m : ℝ) / i)) ^ ((i : ℝ) / (e m : ℝ)) :=
            Real.rpow_le_rpow (Real.rpow_nonneg hIval_nn _) hgn (by positivity)
        _ ≤ (Mbar ^ (5 : ℕ)) ^ ((i : ℝ) / (e m : ℝ)) :=
            Real.rpow_le_rpow hbase_nn hbase_le (by positivity)
        _ ≤ (Mbar ^ (5 : ℕ)) ^ ((i : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le hM5_one hidiv
        _ = (Mbar ^ (5 : ℕ)) ^ (i : ℕ) := by rw [Real.rpow_natCast]
        _ = Mbar ^ (5 * i) := by rw [← pow_mul]
    have hSsum_factor : ∑ m ∈ Sset, ((e m : ℝ) / i) *
        (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ) ≤
        Mbar ^ (5 * i) := by
      have hw_nn : ∀ m ∈ Sset, 0 ≤ (e m : ℝ) / i := fun m _ => by positivity
      have hw_sum : ∑ m ∈ Sset, (e m : ℝ) / i = 1 := by
        rw [← Finset.sum_div]
        rw [show (∑ m ∈ Sset, (e m : ℝ)) = ((i : ℕ) : ℝ) from by
          rw [← Nat.cast_sum]; exact_mod_cast hSsum]
        exact div_self hiR_ne
      calc ∑ m ∈ Sset, ((e m : ℝ) / i) *
            (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ)
          ≤ ∑ m ∈ Sset, ((e m : ℝ) / i) * Mbar ^ (5 * i) := by
            apply Finset.sum_le_sum
            intro m hm
            exact mul_le_mul_of_nonneg_left (hfactor m hm) (hw_nn m hm)
        _ = (∑ m ∈ Sset, (e m : ℝ) / i) * Mbar ^ (5 * i) := by rw [Finset.sum_mul]
        _ = Mbar ^ (5 * i) := by rw [hw_sum, one_mul]
    have hpt2 : ∀ x : M,
        (∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ≤
          Λ ^ (2 * Zset.card) * ∑ m ∈ Sset, ((e m : ℝ) / i) *
            (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) := by
      intro x
      rw [hsplit x]
      have hZnn : 0 ≤ ∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x) :=
        Finset.prod_nonneg (fun m _ => hnn (e m) x)
      have hsum_nn : 0 ≤ ∑ m ∈ Sset, ((e m : ℝ) / i) *
          (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) :=
        Finset.sum_nonneg (fun m _ => mul_nonneg (by positivity) (Real.rpow_nonneg (hnn (e m) x) _))
      calc (∏ m ∈ Sset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) *
            (∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
          ≤ (∑ m ∈ Sset, ((e m : ℝ) / i) *
              (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ))) *
              Λ ^ (2 * Zset.card) :=
            mul_le_mul (hAMGM x) (hZbound x) hZnn hsum_nn
        _ = Λ ^ (2 * Zset.card) * ∑ m ∈ Sset, ((e m : ℝ) / i) *
              (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) :=
            mul_comm _ _
    have hsum_int : MeasureTheory.Integrable
        (fun x => ∑ m ∈ Sset, ((e m : ℝ) / i) *
          (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ))) μ := by
      apply MeasureTheory.integrable_finset_sum
      intro m _
      exact (hint_rpow (e m) ((i : ℝ) / (e m : ℝ)) (by positivity)).const_mul _
    have hint_eq : (∫ x, ∑ m ∈ Sset, ((e m : ℝ) / i) *
          (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ) =
        ∑ m ∈ Sset, ((e m : ℝ) / i) *
          (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ) := by
      rw [MeasureTheory.integral_finset_sum]
      · apply Finset.sum_congr rfl
        intro m _; rw [MeasureTheory.integral_const_mul]
      · intro m _
        exact (hint_rpow (e m) ((i : ℝ) / (e m : ℝ)) (by positivity)).const_mul _
    have hΛZ_nn : 0 ≤ Λ ^ (2 * Zset.card) := pow_nonneg hΛ_nn _
    calc (∫ x, ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x) ∂μ)
        ≤ ∫ x, Λ ^ (2 * Zset.card) * ∑ m ∈ Sset, ((e m : ℝ) / i) *
            (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ :=
          MeasureTheory.integral_mono hint_prod (hsum_int.const_mul _) hpt2
      _ = Λ ^ (2 * Zset.card) * ∫ x, ∑ m ∈ Sset, ((e m : ℝ) / i) *
            (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ :=
          MeasureTheory.integral_const_mul _ _
      _ ≤ Λ ^ (2 * Zset.card) * Mbar ^ (5 * i) := by
          rw [hint_eq]
          exact mul_le_mul_of_nonneg_left hSsum_factor hΛZ_nn
      _ ≤ (i : ℝ) * Mbar ^ (7 * i) := by
          have hZle : Zset.card ≤ i := le_trans (Finset.card_le_univ _) (by simpa using hn_le)
          have e1 : Λ ^ (2 * Zset.card) ≤ Mbar ^ (2 * i) :=
            le_trans (pow_le_pow_left₀ hΛ_nn hΛ_le _) (pow_le_pow_right₀ hMbar1 (by omega))
          have e3 : Mbar ^ (2 * i) * Mbar ^ (5 * i) = Mbar ^ (7 * i) := by
            rw [← pow_add]; congr 1; ring
          have e4 : Λ ^ (2 * Zset.card) * Mbar ^ (5 * i) ≤ Mbar ^ (2 * i) * Mbar ^ (5 * i) :=
            mul_le_mul_of_nonneg_right e1 (by positivity)
          have e5 : Mbar ^ (7 * i) ≤ (i : ℝ) * Mbar ^ (7 * i) := by
            have : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi1
            nlinarith [pow_nonneg hMbar_nn (7 * i)]
          calc Λ ^ (2 * Zset.card) * Mbar ^ (5 * i) ≤ Mbar ^ (2 * i) * Mbar ^ (5 * i) := e4
            _ = Mbar ^ (7 * i) := e3
            _ ≤ (i : ℝ) * Mbar ^ (7 * i) := e5

theorem diagonalProductGrid_riemannianFiberNormSq_integral_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (_hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (P : SmoothCcTensor g₀ 0 2),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a →
          MeasureTheory.Integrable
              (fun x => ∑ n ∈ Finset.range (i + 1),
                ∑ e ∈ Finset.Nat.antidiagonalTuple n i,
                  ∏ m : Fin n,
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                      ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
              (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
            (∫ x, ∑ n ∈ Finset.range (i + 1),
                  ∑ e ∈ Finset.Nat.antidiagonalTuple n i,
                    ∏ m : Fin n,
                      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                        ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
                ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤ K i := by
  classical
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  obtain ⟨Cemb, hCemb_nn, hCemb⟩ :=
    DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.deTurckSmoothRemainderDiff_supercritical_pointwise_jet_le_fixedWindow
      (I := I) (M := M) g₀ a ha_super
  set Lam : ℝ := Cemb * Real.sqrt ((a + 1 + 1 : ℕ) : ℝ) * R with hLam
  have hLam_nn : 0 ≤ Lam := by rw [hLam]; positivity
  set Cgn : ℕ → ℝ := fun k =>
    if h : 1 ≤ k then
      (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
        (I := I) (M := M) g₀ 0 2 k h).choose
    else 0 with hCgn
  have hCgn_nn : ∀ k, 0 ≤ Cgn k := by
    intro k
    simp only [hCgn]
    split_ifs with h
    · exact (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
        (I := I) (M := M) g₀ 0 2 k h).choose_spec.1
    · exact le_refl 0
  set Gfun : ℕ → ℝ := fun k => (k : ℝ) * (max Lam (max R (max (Cgn k) 1))) ^ (7 * k) with hGfun
  have hGfun_nn : ∀ k, 0 ≤ Gfun k := by
    intro k
    rw [hGfun]
    apply mul_nonneg (Nat.cast_nonneg k)
    apply pow_nonneg
    exact le_trans zero_le_one
      (le_trans (le_max_right (Cgn k) 1) (le_trans (le_max_right R _) (le_max_right Lam _)))
  set vol : ℝ := ((riemannianVolumeMeasure (I := I) (M := M) g₀) Set.univ).toReal with hvol
  have hvol_nn : 0 ≤ vol := ENNReal.toReal_nonneg
  refine ⟨fun k => (∑ n ∈ Finset.range (k + 1),
      ((Finset.Nat.antidiagonalTuple n k).card : ℝ)) * Gfun k + vol, ?_, ?_⟩
  · intro k
    exact add_nonneg
      (mul_nonneg (Finset.sum_nonneg (fun n _ => Nat.cast_nonneg _)) (hGfun_nn k)) hvol_nn
  · intro P hPball i hi
    by_cases hi0 : i = 0
    · subst hi0
      have hgrid0 : (fun x => ∑ n ∈ Finset.range (0 + 1),
          ∑ e ∈ Finset.Nat.antidiagonalTuple n 0, ∏ m : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) = (fun _ : M => (1 : ℝ)) := by
        funext x
        simp only [Nat.zero_add, Finset.sum_range_one, Finset.Nat.antidiagonalTuple_zero_zero,
          Finset.sum_singleton, Finset.univ_eq_empty, Finset.prod_empty]
      refine ⟨?_, ?_⟩
      · rw [hgrid0]; exact MeasureTheory.integrable_const 1
      · rw [hgrid0, MeasureTheory.integral_const, smul_eq_mul, mul_one,
          MeasureTheory.measureReal_def, ← hvol]
        exact le_add_of_nonneg_left
          (mul_nonneg (Finset.sum_nonneg (fun n _ => Nat.cast_nonneg _)) (hGfun_nn 0))
    · have hi1 : 1 ≤ i := Nat.one_le_iff_ne_zero.mpr hi0
      have hNi : ‖iteratedCovGrad (I := I) g₀ 0 2 i P‖ ≤ R := hPball i (by omega)
      have hΛsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (P.toSection x) ≤
          Lam ^ 2 := by
        intro x
        have hsum_le : ∑ j ∈ Finset.range (a + 1 + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 ≤ ((a + 1 + 1 : ℕ) : ℝ) * R ^ 2 := by
          calc ∑ j ∈ Finset.range (a + 1 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2
              ≤ ∑ j ∈ Finset.range (a + 1 + 1), R ^ 2 := by
                apply Finset.sum_le_sum
                intro j hj
                have hjle : j ≤ a + 2 := by have := Finset.mem_range.mp hj; omega
                nlinarith [norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 j P), hPball j hjle, hR]
            _ = ((a + 1 + 1 : ℕ) : ℝ) * R ^ 2 := by
                rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        have hsingle : riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (P.toSection x) ≤
            ∑ m ∈ Finset.range 3, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 m P).toSection x) := by
          have h0mem : (0 : ℕ) ∈ Finset.range 3 := by norm_num
          have hsl := Finset.single_le_sum
            (f := fun m => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 m P).toSection x))
            (fun m _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + m) x _) h0mem
          simpa using hsl
        have hLam2 : Lam ^ 2 = Cemb ^ 2 * ((a + 1 + 1 : ℕ) : ℝ) * R ^ 2 := by
          rw [hLam, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
        have hchain : ∑ m ∈ Finset.range 3, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 m P).toSection x) ≤ Lam ^ 2 := by
          refine le_trans (hCemb P x) ?_
          rw [hLam2]
          calc Cemb ^ 2 * ∑ j ∈ Finset.range (a + 1 + 1),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2
              ≤ Cemb ^ 2 * (((a + 1 + 1 : ℕ) : ℝ) * R ^ 2) :=
                mul_le_mul_of_nonneg_left hsum_le (by positivity)
            _ = Cemb ^ 2 * ((a + 1 + 1 : ℕ) : ℝ) * R ^ 2 := by ring
        exact le_trans hsingle hchain
      have hGNspec := (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
        (I := I) (M := M) g₀ 0 2 i hi1).choose_spec.2
      have hGNP : ∀ j : ℕ, 0 < j → j < i →
          (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) ^ ((i : ℝ) / (j : ℝ))
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ^ ((j : ℝ) / (i : ℝ)) ≤
            Cgn i * Lam ^ (2 * (1 - (j : ℝ) / (i : ℝ))) * R ^ (2 * (j : ℝ) / (i : ℝ)) := by
        intro j hj0 hji
        have hb := hGNspec P Lam hLam_nn hΛsup j hj0 hji
        have hchoose : (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
            (I := I) (M := M) g₀ 0 2 i hi1).choose = Cgn i := by
          rw [hCgn]; simp only [dif_pos hi1]
        rw [hchoose] at hb
        refine le_trans hb ?_
        have hnorm : Integral.L2.tensorL2Norm (I := I) (M := M) g₀ 0 (2 + i)
            (iteratedCovGrad (I := I) g₀ 0 2 i P).toFun = ‖iteratedCovGrad (I := I) g₀ 0 2 i P‖ :=
          (SmoothCcTensor.norm_def (iteratedCovGrad (I := I) g₀ 0 2 i P)).symm
        rw [hnorm]
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (norm_nonneg _) hNi (by positivity))
          (mul_nonneg (hCgn_nn i) (Real.rpow_nonneg hLam_nn _))
      have hPT : ∀ n ∈ Finset.range (i + 1), ∀ e ∈ Finset.Nat.antidiagonalTuple n i,
          MeasureTheory.Integrable (fun x => ∏ m : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
            (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
          (∫ x, ∏ m : Fin n,
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤ Gfun i := by
        intro n hn e he
        have hn_le : n ≤ i := by have := Finset.mem_range.mp hn; omega
        have hsum_e : ∑ m, e m = i := Finset.Nat.mem_antidiagonalTuple.mp he
        have hres := diagonalProductTerm_integral_le (I := I) (M := M) g₀ P hR i hi1 hLam_nn hΛsup
          hNi (hCgn_nn i) hGNP n hn_le e hsum_e
        simpa only [hGfun] using hres
      have hgrid_int : MeasureTheory.Integrable (fun x => ∑ n ∈ Finset.range (i + 1),
          ∑ e ∈ Finset.Nat.antidiagonalTuple n i, ∏ m : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
          (riemannianVolumeMeasure (I := I) (M := M) g₀) := by
        apply MeasureTheory.integrable_finset_sum
        intro n hn
        apply MeasureTheory.integrable_finset_sum
        intro e he
        exact (hPT n hn e he).1
      refine ⟨hgrid_int, ?_⟩
      rw [MeasureTheory.integral_finset_sum _
        (fun n hn => MeasureTheory.integrable_finset_sum _ (fun e he => (hPT n hn e he).1))]
      have hinner : ∀ n ∈ Finset.range (i + 1),
          (∫ x, ∑ e ∈ Finset.Nat.antidiagonalTuple n i, ∏ m : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) =
          ∑ e ∈ Finset.Nat.antidiagonalTuple n i, ∫ x, ∏ m : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := by
        intro n hn
        exact MeasureTheory.integral_finset_sum _ (fun e he => (hPT n hn e he).1)
      rw [Finset.sum_congr rfl hinner]
      have hle1 : ∑ n ∈ Finset.range (i + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n i,
            (∫ x, ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
          ∑ n ∈ Finset.range (i + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n i, Gfun i := by
        apply Finset.sum_le_sum; intro n hn
        apply Finset.sum_le_sum; intro e he
        exact (hPT n hn e he).2
      have heq2 : ∑ n ∈ Finset.range (i + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n i, Gfun i =
          (∑ n ∈ Finset.range (i + 1), ((Finset.Nat.antidiagonalTuple n i).card : ℝ)) * Gfun i := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl; intro n _
        rw [Finset.sum_const, nsmul_eq_mul]
      refine le_trans hle1 ?_
      rw [heq2]
      exact le_add_of_nonneg_right hvol_nn

theorem gInvDiffSlotCoeff_perOrder_l2_ballUniform_generic
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a →
          ‖iteratedCovGrad (I := I) g₀ 2 2 i (gInvDiffSlotCoeff (I := I) g₀ g₁)‖ ^ 2 ≤ K i := by
  obtain ⟨Cgrid, hCgrid_nn, hgrid⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_gInvDiffSlotCoeff_diagonalProductGrid_le (I := I) (M := M) g₀ hδ₀
  obtain ⟨Kgrid, hKgrid_nn, hKgrid⟩ :=
    diagonalProductGrid_riemannianFiberNormSq_integral_ballUniform
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  refine ⟨fun i => Cgrid i * Kgrid i,
    fun i => mul_nonneg (hCgrid_nn i) (hKgrid_nn i), ?_⟩
  intro g₁ P δ hδ_le hδ htie hPball i hi
  by_cases hM : Nonempty M
  · obtain ⟨x₀⟩ := hM
    obtain ⟨v, hv⟩ : ∃ v : TangentSpace I x₀, v ≠ 0 := by
      haveI : Nontrivial (TangentSpace I x₀) := by
        have hfr : 0 < Module.finrank ℝ (TangentSpace I x₀) := by
          have heq : Module.finrank ℝ (TangentSpace I x₀) = Module.finrank ℝ E := rfl
          rw [heq]; exact Nat.pos_of_ne_zero (NeZero.ne _)
        exact Module.nontrivial_of_finrank_pos hfr
      exact exists_ne 0
    have hpos : 0 < g₀.inner x₀ v v := g₀.pos x₀ v hv
    have hbound := hδ x₀ v v
    have hsqrt_pos : 0 < Real.sqrt (g₀.inner x₀ v v) := Real.sqrt_pos.mpr hpos
    have habs_nn : 0 ≤ |ccTensorBilinSymm (I := I) g₀ P x₀ v v| := abs_nonneg _
    have hδ0 : 0 ≤ δ := by
      by_contra hδc
      have hδc' : δ < 0 := lt_of_not_ge hδc
      have hrhs_neg : δ * Real.sqrt (g₀.inner x₀ v v) * Real.sqrt (g₀.inner x₀ v v) < 0 := by
        have h1 : δ * Real.sqrt (g₀.inner x₀ v v) < 0 :=
          mul_neg_of_neg_of_pos hδc' hsqrt_pos
        exact mul_neg_of_neg_of_pos h1 hsqrt_pos
      linarith [le_trans habs_nn hbound]
    obtain ⟨hgrid_int, hgrid_bound⟩ := hKgrid P hPball i hi
    have hF_int : MeasureTheory.Integrable
        (fun x => Cgrid i * ∑ n ∈ Finset.range (i + 1),
          ∑ e ∈ Finset.Nat.antidiagonalTuple n i,
            ∏ m : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
        (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
      hgrid_int.const_mul (Cgrid i)
    have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 2 (2 + i)
      (iteratedCovGrad (I := I) g₀ 2 2 i (gInvDiffSlotCoeff (I := I) g₀ g₁))
      (fun x => Cgrid i * ∑ n ∈ Finset.range (i + 1),
        ∑ e ∈ Finset.Nat.antidiagonalTuple n i,
          ∏ m : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
      hF_int
      (fun x => hgrid g₁ P htie hδ_le hδ0 hδ i x)
    refine le_trans key ?_
    rw [MeasureTheory.integral_const_mul]
    exact mul_le_mul_of_nonneg_left hgrid_bound (hCgrid_nn i)
  · haveI hM' : IsEmpty M := not_nonempty_iff.mp hM
    have hz : ‖iteratedCovGrad (I := I) g₀ 2 2 i (gInvDiffSlotCoeff (I := I) g₀ g₁)‖ = 0 := by
      rw [SmoothCcTensor.norm_def, tensorL2Norm_def, tensorL2Inner,
        MeasureTheory.integral_of_isEmpty, Real.sqrt_zero]
    rw [hz]
    simpa using mul_nonneg (hCgrid_nn i) (hKgrid_nn i)

theorem gInvDiffSlotCoeff_realizedFam_perOrder_l2_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (_hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a → ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (gInvDiffSlotCoeff (I := I) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s))‖ ^ 2 ≤ K i := by
  obtain ⟨K, hK_nn, hK⟩ := gInvDiffSlotCoeff_perOrder_l2_ballUniform_generic
    (I := I) (M := M) g₀ a ha_super hR hδ₀
  refine ⟨K, hK_nn, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball i hi s hs
  have hs0 : (0 : ℝ) ≤ s := hs.1
  have hs1 : s ≤ 1 := hs.2
  have h1ms : (0 : ℝ) ≤ 1 - s := by linarith
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  have hδP : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s))
      ((1 - s) * δ' + s * δ) :=
    convexPerturbation_gFibreOpBound (I := I) (M := M) g₀ T T' hδ hδ' hs0 hs1
  have hδP_le : (1 - s) * δ' + s * δ ≤ δ₀ := by
    have e1 : (1 - s) * δ' ≤ (1 - s) * δ₀ := mul_le_mul_of_nonneg_left hδ'_le h1ms
    have e2 : s * δ ≤ s * δ₀ := mul_le_mul_of_nonneg_left hδ_le hs0
    have e3 : (1 - s) * δ₀ + s * δ₀ = δ₀ := by ring
    linarith [e1, e2, e3]
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      (realizedFam (I := I) g₀ T T' hδ hδ' s).inner y v w =
        g₀.inner y v w +
          ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s) y v w :=
    fun y v w =>
      realizedFam_inner_of_mem (I := I) g₀ T T' hδ hδ'
        (Icc_subset_realizedSmallSet hδ_lt hδ'_lt hs) y v w
  have hPball : ∀ j : ℕ, j ≤ a + 2 →
      ‖iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)‖ ≤ R := by
    intro j hj
    have heq : iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)
        = (1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'
          + s • iteratedCovGrad (I := I) g₀ 0 2 j T := by
      rw [show convexPerturbation (I := I) g₀ T T' s = (1 - s) • T' + s • T from rfl,
        iteratedCovGrad_add, iteratedCovGrad_smul_real, iteratedCovGrad_smul_real]
    rw [heq]
    calc ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'
            + s • iteratedCovGrad (I := I) g₀ 0 2 j T‖
        ≤ ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'‖
            + ‖s • iteratedCovGrad (I := I) g₀ 0 2 j T‖ := norm_add_le _ _
      _ = (1 - s) * ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖
            + s * ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg h1ms, abs_of_nonneg hs0]
      _ ≤ (1 - s) * R + s * R :=
          add_le_add (mul_le_mul_of_nonneg_left (hT'ball j hj) h1ms)
            (mul_le_mul_of_nonneg_left (hTball j hj) hs0)
      _ = R := by ring
  exact hK (realizedFam (I := I) g₀ T T' hδ hδ' s) (convexPerturbation (I := I) g₀ T T' s)
    hδP_le hδP htie hPball i hi

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem continuous_rfns_arm
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) :
    Continuous (fun x => riemannianFiberNormSq (I := I) (M := M) g r s x (S.toSection x)) := by
  have hc := Integral.L2.SmoothCcTensor.continuous_inner_self (I := I) (M := M) S
  refine hc.congr (fun x => ?_)
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (S.toSection x),
    ← Integral.L2.SmoothCcTensor.toFun_apply (I := I) (M := M) S x]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] in
private theorem real_holder_two_nonneg_arm
    (g : SmoothRiemannianMetric I M) (φ ψ : M → ℝ)
    (hφc : Continuous φ) (hψc : Continuous ψ)
    (hφ0 : ∀ x, 0 ≤ φ x) (hψ0 : ∀ x, 0 ≤ ψ x)
    {p q : ℝ} (hpq : p.HolderConjugate q) :
    ∫ x, φ x * ψ x ∂(riemannianVolumeMeasure (I := I) (M := M) g) ≤
      (∫ x, φ x ^ p ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ^ (1 / p) *
      (∫ x, ψ x ^ q ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ^ (1 / q) := by
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  set μ : MeasureTheory.Measure M := riemannianVolumeMeasure (I := I) (M := M) g with hμ
  haveI : IsFiniteMeasure μ :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g
  have hp_pos : 0 < p := hpq.left_pos
  have hq_pos : 0 < q := hpq.right_pos
  have hφm : AEMeasurable (fun x => ENNReal.ofReal (φ x)) μ :=
    (hφc.measurable.ennreal_ofReal).aemeasurable
  have hψm : AEMeasurable (fun x => ENNReal.ofReal (ψ x)) μ :=
    (hψc.measurable.ennreal_ofReal).aemeasurable
  have hint_prod : Integrable (fun x => φ x * ψ x) μ :=
    (hφc.mul hψc).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hint_φp : Integrable (fun x => φ x ^ p) μ :=
    ((hφc.rpow_const (fun x => Or.inr hp_pos.le)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
  have hint_ψq : Integrable (fun x => ψ x ^ q) μ :=
    ((hψc.rpow_const (fun x => Or.inr hq_pos.le)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
  have hφp0 : ∀ x, 0 ≤ φ x ^ p := fun x => Real.rpow_nonneg (hφ0 x) _
  have hψq0 : ∀ x, 0 ≤ ψ x ^ q := fun x => Real.rpow_nonneg (hψ0 x) _
  have hIφp_nn : 0 ≤ ∫ x, φ x ^ p ∂μ := integral_nonneg hφp0
  have hIψq_nn : 0 ≤ ∫ x, ψ x ^ q ∂μ := integral_nonneg hψq0
  have hHolder := ENNReal.lintegral_mul_le_Lp_mul_Lq (μ := μ) hpq hφm hψm
  have hLHS_lint : (∫⁻ x, ((fun x => ENNReal.ofReal (φ x)) * (fun x => ENNReal.ofReal (ψ x))) x ∂μ)
      = ENNReal.ofReal (∫ x, φ x * ψ x ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint_prod
      (Eventually.of_forall (fun x => mul_nonneg (hφ0 x) (hψ0 x)))]
    refine lintegral_congr_ae (Eventually.of_forall (fun x => ?_))
    simp only [Pi.mul_apply]
    rw [ENNReal.ofReal_mul (hφ0 x)]
  have hφp_pt : ∀ x, (ENNReal.ofReal (φ x)) ^ p = ENNReal.ofReal (φ x ^ p) :=
    fun x => ENNReal.ofReal_rpow_of_nonneg (hφ0 x) hp_pos.le
  have hψq_pt : ∀ x, (ENNReal.ofReal (ψ x)) ^ q = ENNReal.ofReal (ψ x ^ q) :=
    fun x => ENNReal.ofReal_rpow_of_nonneg (hψ0 x) hq_pos.le
  have hφp_lint : (∫⁻ x, (ENNReal.ofReal (φ x)) ^ p ∂μ) = ENNReal.ofReal (∫ x, φ x ^ p ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint_φp (Eventually.of_forall hφp0)]
    exact lintegral_congr_ae (Eventually.of_forall hφp_pt)
  have hψq_lint : (∫⁻ x, (ENNReal.ofReal (ψ x)) ^ q ∂μ) = ENNReal.ofReal (∫ x, ψ x ^ q ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint_ψq (Eventually.of_forall hψq0)]
    exact lintegral_congr_ae (Eventually.of_forall hψq_pt)
  rw [hLHS_lint, hφp_lint, hψq_lint] at hHolder
  rw [ENNReal.ofReal_rpow_of_nonneg hIφp_nn (by positivity),
    ENNReal.ofReal_rpow_of_nonneg hIψq_nn (by positivity),
    ← ENNReal.ofReal_mul (by positivity)] at hHolder
  have hrhs_nn : 0 ≤ (∫ x, φ x ^ p ∂μ) ^ (1 / p) * (∫ x, ψ x ^ q ∂μ) ^ (1 / q) := by positivity
  exact (ENNReal.ofReal_le_ofReal_iff hrhs_nn).mp hHolder

private theorem young_weighted_product_bound
    (wi wl CS CT ΛS ΛT NS NT Iφp Iψq : ℝ)
    (hwi_nn : 0 ≤ wi) (hwl_nn : 0 ≤ wl) (hwsum : wi + wl = 1)
    (hCS : 0 ≤ CS) (hCT : 0 ≤ CT) (hΛS : 0 ≤ ΛS) (hΛT : 0 ≤ ΛT)
    (hNS : 0 ≤ NS) (hNT : 0 ≤ NT) (_hIφp : 0 ≤ Iφp) (hIψq : 0 ≤ Iψq)
    (hS : Iφp ^ wi ≤ CS * ΛS ^ (2 * (1 - wi)) * NS ^ (2 * wi))
    (hT : Iψq ^ wl ≤ CT * ΛT ^ (2 * (1 - wl)) * NT ^ (2 * wl)) :
    Iφp ^ wi * Iψq ^ wl ≤
      CS * CT * (wi * (ΛT ^ 2 * NS ^ 2) + wl * (ΛS ^ 2 * NT ^ 2)) := by
  have hT_nn : 0 ≤ Iψq ^ wl := Real.rpow_nonneg hIψq _
  have hprod : Iφp ^ wi * Iψq ^ wl ≤
      (CS * ΛS ^ (2 * (1 - wi)) * NS ^ (2 * wi)) *
      (CT * ΛT ^ (2 * (1 - wl)) * NT ^ (2 * wl)) :=
    mul_le_mul hS hT hT_nn (by positivity)
  have h1wi : (1 : ℝ) - wi = wl := by rw [← hwsum]; ring
  have h1wl : (1 : ℝ) - wl = wi := by rw [← hwsum]; ring
  rw [h1wi, h1wl] at hprod
  have hsq_rpow : ∀ (b : ℝ), 0 ≤ b → ∀ w : ℝ, b ^ (2 * w) = (b ^ 2) ^ w := by
    intro b hb w
    rw [Real.rpow_mul hb 2 w, Real.rpow_two]
  have hregroup :
      (CS * ΛS ^ (2 * wl) * NS ^ (2 * wi)) * (CT * ΛT ^ (2 * wi) * NT ^ (2 * wl))
        = CS * CT * ((ΛT ^ 2 * NS ^ 2) ^ wi * (ΛS ^ 2 * NT ^ 2) ^ wl) := by
    rw [Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow (by positivity) (by positivity),
      hsq_rpow ΛS hΛS wl, hsq_rpow NS hNS wi, hsq_rpow ΛT hΛT wi, hsq_rpow NT hNT wl]
    ring
  rw [hregroup] at hprod
  have hyoung : (ΛT ^ 2 * NS ^ 2) ^ wi * (ΛS ^ 2 * NT ^ 2) ^ wl ≤
      wi * (ΛT ^ 2 * NS ^ 2) + wl * (ΛS ^ 2 * NT ^ 2) :=
    Real.geom_mean_le_arith_mean2_weighted hwi_nn hwl_nn (by positivity) (by positivity) hwsum
  calc Iφp ^ wi * Iψq ^ wl
      ≤ CS * CT * ((ΛT ^ 2 * NS ^ 2) ^ wi * (ΛS ^ 2 * NT ^ 2) ^ wl) := hprod
    _ ≤ CS * CT * (wi * (ΛT ^ 2 * NS ^ 2) + wl * (ΛS ^ 2 * NT ^ 2)) :=
        mul_le_mul_of_nonneg_left hyoung (by positivity)

theorem exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le
    (g : SmoothRiemannianMetric I M) (r₁ r₂ s₁ s₂ k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g r₁ s₁) (T : SmoothCcTensor g r₂ s₂)
        (ΛS ΛT : ℝ), 0 ≤ ΛS → 0 ≤ ΛT →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g r₁ s₁ x (S.toSection x) ≤ ΛS ^ 2) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g r₂ s₂ x (T.toSection x) ≤ ΛT ^ 2) →
        MeasureTheory.Integrable
            (fun x => ∑ i ∈ Finset.range (k + 1),
              riemannianFiberNormSq (I := I) (M := M) g r₁ (s₁ + i) x
                  ((iteratedCovGrad (I := I) g r₁ s₁ i S).toSection x)
                * ∑ l ∈ Finset.range (k + 1 - i),
                    riemannianFiberNormSq (I := I) (M := M) g r₂ (s₂ + l) x
                      ((iteratedCovGrad (I := I) g r₂ s₂ l T).toSection x))
            (riemannianVolumeMeasure (I := I) (M := M) g) ∧
          (∫ x, (∑ i ∈ Finset.range (k + 1),
              riemannianFiberNormSq (I := I) (M := M) g r₁ (s₁ + i) x
                  ((iteratedCovGrad (I := I) g r₁ s₁ i S).toSection x)
                * ∑ l ∈ Finset.range (k + 1 - i),
                    riemannianFiberNormSq (I := I) (M := M) g r₂ (s₂ + l) x
                      ((iteratedCovGrad (I := I) g r₂ s₂ l T).toSection x))
              ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤
            C * (ΛT ^ 2 * ∑ i ∈ Finset.range (k + 1),
                  ‖iteratedCovGrad (I := I) g r₁ s₁ i S‖ ^ 2
                + ΛS ^ 2 * ∑ l ∈ Finset.range (k + 1),
                  ‖iteratedCovGrad (I := I) g r₂ s₂ l T‖ ^ 2) := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g
  set CSf : ℕ → ℝ := fun m =>
    if h : 1 ≤ m then
      (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
        (I := I) (M := M) g r₁ s₁ m h).choose
    else 0 with hCSf
  set CTf : ℕ → ℝ := fun m =>
    if h : 1 ≤ m then
      (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
        (I := I) (M := M) g r₂ s₂ m h).choose
    else 0 with hCTf
  have hCSf_nn : ∀ m, 0 ≤ CSf m := by
    intro m; rw [hCSf]; dsimp only; split
    · rename_i h
      exact (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
        (I := I) (M := M) g r₁ s₁ m h).choose_spec.1
    · exact le_refl 0
  have hCTf_nn : ∀ m, 0 ≤ CTf m := by
    intro m; rw [hCTf]; dsimp only; split
    · rename_i h
      exact (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
        (I := I) (M := M) g r₂ s₂ m h).choose_spec.1
    · exact le_refl 0
  set Cbig : ℝ := 1 + ∑ m ∈ Finset.range (k + 1), CSf m * CTf m with hCbig
  have hCbig1 : (1 : ℝ) ≤ Cbig := by
    rw [hCbig]
    have : (0 : ℝ) ≤ ∑ m ∈ Finset.range (k + 1), CSf m * CTf m :=
      Finset.sum_nonneg (fun m _ => mul_nonneg (hCSf_nn m) (hCTf_nn m))
    linarith
  have hCbig_nn : (0 : ℝ) ≤ Cbig := le_trans zero_le_one hCbig1
  have hCSCT_le : ∀ m, m ≤ k → CSf m * CTf m ≤ Cbig := by
    intro m hm
    rw [hCbig]
    have hmem : m ∈ Finset.range (k + 1) := Finset.mem_range.mpr (by omega)
    have hterm : CSf m * CTf m ≤ ∑ m' ∈ Finset.range (k + 1), CSf m' * CTf m' :=
      Finset.single_le_sum (fun m' _ => mul_nonneg (hCSf_nn m') (hCTf_nn m')) hmem
    linarith
  refine ⟨(k + 1) ^ 2 * Cbig, by positivity, ?_⟩
  intro S T ΛS ΛT hΛS hΛT hSsup hTsup
  set μ : MeasureTheory.Measure M := riemannianVolumeMeasure (I := I) (M := M) g with hμ
  set Sj : ℕ → M → ℝ := fun a x =>
    riemannianFiberNormSq (I := I) (M := M) g r₁ (s₁ + a) x
      ((iteratedCovGrad (I := I) g r₁ s₁ a S).toSection x) with hSj
  set Tj : ℕ → M → ℝ := fun b x =>
    riemannianFiberNormSq (I := I) (M := M) g r₂ (s₂ + b) x
      ((iteratedCovGrad (I := I) g r₂ s₂ b T).toSection x) with hTj
  have hSnorm : ∀ a, ∫ x, Sj a x ∂μ =
      ‖iteratedCovGrad (I := I) g r₁ s₁ a S‖ ^ 2 := by
    intro a
    rw [hSj, hμ,
      ← tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g r₁ (s₁ + a)
        (iteratedCovGrad (I := I) g r₁ s₁ a S),
      ← Integral.L2.SmoothCcTensor.norm_def (iteratedCovGrad (I := I) g r₁ s₁ a S)]
  have hTnorm : ∀ b, ∫ x, Tj b x ∂μ =
      ‖iteratedCovGrad (I := I) g r₂ s₂ b T‖ ^ 2 := by
    intro b
    rw [hTj, hμ,
      ← tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g r₂ (s₂ + b)
        (iteratedCovGrad (I := I) g r₂ s₂ b T),
      ← Integral.L2.SmoothCcTensor.norm_def (iteratedCovGrad (I := I) g r₂ s₂ b T)]
  have hSj_cont : ∀ a, Continuous (Sj a) := fun a => by
    rw [hSj]; exact continuous_rfns_arm g r₁ (s₁ + a) _
  have hTj_cont : ∀ b, Continuous (Tj b) := fun b => by
    rw [hTj]; exact continuous_rfns_arm g r₂ (s₂ + b) _
  have hSj_nn : ∀ a x, 0 ≤ Sj a x := fun a x => by
    rw [hSj]; exact riemannianFiberNormSq_nonneg (I := I) (M := M) g r₁ (s₁ + a) x _
  have hTj_nn : ∀ b x, 0 ≤ Tj b x := fun b x => by
    rw [hTj]; exact riemannianFiberNormSq_nonneg (I := I) (M := M) g r₂ (s₂ + b) x _
  have hSj_int : ∀ a, Integrable (Sj a) μ := fun a => by
    rw [hμ]; exact (hSj_cont a).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hTj_int : ∀ b, Integrable (Tj b) μ := fun b => by
    rw [hμ]; exact (hTj_cont b).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hint_cell : ∀ a b, Integrable (fun x => Sj a x * Tj b x) μ := fun a b => by
    rw [hμ]
    exact ((hSj_cont a).mul (hTj_cont b)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hSsup0 : ∀ x, Sj 0 x ≤ ΛS ^ 2 := by
    intro x; rw [hSj]; dsimp only
    rw [iteratedCovGrad_zero (I := I) g r₁ s₁ S]
    exact hSsup x
  have hTsup0 : ∀ x, Tj 0 x ≤ ΛT ^ 2 := by
    intro x; rw [hTj]; dsimp only
    rw [iteratedCovGrad_zero (I := I) g r₂ s₂ T]
    exact hTsup x
  have hAS_nn : 0 ≤ ΛT ^ 2 * ∑ a ∈ Finset.range (k + 1),
      ‖iteratedCovGrad (I := I) g r₁ s₁ a S‖ ^ 2 := by positivity
  have hAT_nn : 0 ≤ ΛS ^ 2 * ∑ b ∈ Finset.range (k + 1),
      ‖iteratedCovGrad (I := I) g r₂ s₂ b T‖ ^ 2 := by positivity
  have hcell : ∀ i, i ≤ k → ∀ l, i + l ≤ k →
      ∫ x, Sj i x * Tj l x ∂μ ≤ Cbig *
        ((ΛT ^ 2 * ∑ a ∈ Finset.range (k + 1),
            ‖iteratedCovGrad (I := I) g r₁ s₁ a S‖ ^ 2)
          + (ΛS ^ 2 * ∑ b ∈ Finset.range (k + 1),
            ‖iteratedCovGrad (I := I) g r₂ s₂ b T‖ ^ 2)) := by
    intro i hik l hilk
    have hSi_in : ‖iteratedCovGrad (I := I) g r₁ s₁ i S‖ ^ 2 ≤
        ∑ a ∈ Finset.range (k + 1),
          ‖iteratedCovGrad (I := I) g r₁ s₁ a S‖ ^ 2 :=
      Finset.single_le_sum
        (f := fun a => ‖iteratedCovGrad (I := I) g r₁ s₁ a S‖ ^ 2)
        (fun a _ => sq_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hik))
    have hTl_in : ‖iteratedCovGrad (I := I) g r₂ s₂ l T‖ ^ 2 ≤
        ∑ b ∈ Finset.range (k + 1),
          ‖iteratedCovGrad (I := I) g r₂ s₂ b T‖ ^ 2 :=
      Finset.single_le_sum
        (f := fun b => ‖iteratedCovGrad (I := I) g r₂ s₂ b T‖ ^ 2)
        (fun b _ => sq_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le (by omega)))
    rcases Nat.eq_zero_or_pos i with hi0 | hipos
    · subst hi0
      have hbound : ∫ x, Sj 0 x * Tj l x ∂μ ≤ ΛS ^ 2 * ∫ x, Tj l x ∂μ := by
        rw [← integral_const_mul]
        refine integral_mono_of_nonneg (Eventually.of_forall (fun x => ?_)) ?_
          (Eventually.of_forall (fun x => ?_))
        · exact mul_nonneg (hSj_nn 0 x) (hTj_nn l x)
        · exact (hTj_int l).const_mul _
        · exact mul_le_mul_of_nonneg_right (hSsup0 x) (hTj_nn l x)
      rw [hTnorm l] at hbound
      calc ∫ x, Sj 0 x * Tj l x ∂μ
          ≤ ΛS ^ 2 * ‖iteratedCovGrad (I := I) g r₂ s₂ l T‖ ^ 2 := hbound
        _ ≤ Cbig * (ΛS ^ 2 * ∑ b ∈ Finset.range (k + 1),
              ‖iteratedCovGrad (I := I) g r₂ s₂ b T‖ ^ 2) := by
              rw [← mul_assoc, mul_comm (Cbig) (ΛS ^ 2), mul_assoc]
              exact mul_le_mul_of_nonneg_left
                (le_trans hTl_in (le_mul_of_one_le_left (Finset.sum_nonneg
                  (fun b _ => sq_nonneg _)) hCbig1)) (by positivity)
        _ ≤ Cbig * ((ΛT ^ 2 * ∑ a ∈ Finset.range (k + 1),
              ‖iteratedCovGrad (I := I) g r₁ s₁ a S‖ ^ 2)
            + (ΛS ^ 2 * ∑ b ∈ Finset.range (k + 1),
              ‖iteratedCovGrad (I := I) g r₂ s₂ b T‖ ^ 2)) := by
              apply mul_le_mul_of_nonneg_left _ hCbig_nn
              linarith [hAS_nn]
    · rcases Nat.eq_zero_or_pos l with hl0 | hlpos
      · subst hl0
        have hbound : ∫ x, Sj i x * Tj 0 x ∂μ ≤ ΛT ^ 2 * ∫ x, Sj i x ∂μ := by
          rw [← integral_const_mul]
          refine integral_mono_of_nonneg (Eventually.of_forall (fun x => ?_)) ?_
            (Eventually.of_forall (fun x => ?_))
          · exact mul_nonneg (hSj_nn i x) (hTj_nn 0 x)
          · exact (hSj_int i).const_mul _
          · calc Sj i x * Tj 0 x
                ≤ Sj i x * ΛT ^ 2 := mul_le_mul_of_nonneg_left (hTsup0 x) (hSj_nn i x)
              _ = ΛT ^ 2 * Sj i x := mul_comm _ _
        rw [hSnorm i] at hbound
        calc ∫ x, Sj i x * Tj 0 x ∂μ
            ≤ ΛT ^ 2 * ‖iteratedCovGrad (I := I) g r₁ s₁ i S‖ ^ 2 := hbound
          _ ≤ Cbig * (ΛT ^ 2 * ∑ a ∈ Finset.range (k + 1),
                ‖iteratedCovGrad (I := I) g r₁ s₁ a S‖ ^ 2) := by
                rw [← mul_assoc, mul_comm (Cbig) (ΛT ^ 2), mul_assoc]
                exact mul_le_mul_of_nonneg_left
                  (le_trans hSi_in (le_mul_of_one_le_left (Finset.sum_nonneg
                    (fun a _ => sq_nonneg _)) hCbig1)) (by positivity)
          _ ≤ Cbig * ((ΛT ^ 2 * ∑ a ∈ Finset.range (k + 1),
                ‖iteratedCovGrad (I := I) g r₁ s₁ a S‖ ^ 2)
              + (ΛS ^ 2 * ∑ b ∈ Finset.range (k + 1),
                ‖iteratedCovGrad (I := I) g r₂ s₂ b T‖ ^ 2)) := by
                apply mul_le_mul_of_nonneg_left _ hCbig_nn
                linarith [hAT_nn]
      · set m : ℕ := i + l with hm
        have hmk : m ≤ k := by rw [hm]; exact hilk
        have hm1 : 1 ≤ m := by omega
        have hmi : i < m := by omega
        have hml : l < m := by omega
        have hm_posR : 0 < (m : ℝ) := by positivity
        set wi : ℝ := (i : ℝ) / m with hwi
        set wl : ℝ := (l : ℝ) / m with hwl
        have hwi_nn : 0 ≤ wi := by rw [hwi]; positivity
        have hwl_nn : 0 ≤ wl := by rw [hwl]; positivity
        have hwsum : wi + wl = 1 := by
          rw [hwi, hwl, ← add_div, show (i : ℝ) + l = (m : ℝ) by push_cast [hm]; ring]
          exact div_self (ne_of_gt hm_posR)
        have hi_posR : 0 < (i : ℝ) := by exact_mod_cast hipos
        have hl_posR : 0 < (l : ℝ) := by exact_mod_cast hlpos
        set p : ℝ := (m : ℝ) / i with hp
        set q : ℝ := (m : ℝ) / l with hq
        have hp_one : 1 < p := by rw [hp, lt_div_iff₀ hi_posR, one_mul]; exact_mod_cast hmi
        have hpq : p.HolderConjugate q := by
          rw [Real.holderConjugate_iff]
          refine ⟨hp_one, ?_⟩
          rw [hp, hq, inv_div, inv_div, ← add_div,
            show (i : ℝ) + l = (m : ℝ) by push_cast [hm]; ring]
          exact div_self (ne_of_gt hm_posR)
        have hHolder := real_holder_two_nonneg_arm g (Sj i) (Tj l)
          (hSj_cont i) (hTj_cont l) (hSj_nn i) (hTj_nn l) hpq
        have h1p : (1 : ℝ) / p = wi := by rw [hp, one_div_div, hwi]
        have h1q : (1 : ℝ) / q = wl := by rw [hq, one_div_div, hwl]
        rw [h1p, h1q] at hHolder
        have hSe := (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
          (I := I) (M := M) g r₁ s₁ m hm1).choose_spec.2 S ΛS hΛS hSsup i hipos hmi
        have hTe := (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
          (I := I) (M := M) g r₂ s₂ m hm1).choose_spec.2 T ΛT hΛT hTsup l hlpos hml
        have hCSf_m : (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
            (I := I) (M := M) g r₁ s₁ m hm1).choose = CSf m := by
          simp only [hCSf, dif_pos hm1]
        have hCTf_m : (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
            (I := I) (M := M) g r₂ s₂ m hm1).choose = CTf m := by
          simp only [hCTf, dif_pos hm1]
        rw [hCSf_m] at hSe
        rw [hCTf_m] at hTe
        rw [mul_div_assoc 2 (i : ℝ) m, ← hwi] at hSe
        rw [mul_div_assoc 2 (l : ℝ) m, ← hwl] at hTe
        rw [show Integral.L2.tensorL2Norm (I := I) g r₁ (s₁ + m)
              (iteratedCovGrad (I := I) g r₁ s₁ m S).toFun =
              ‖iteratedCovGrad (I := I) g r₁ s₁ m S‖ from
            (Integral.L2.SmoothCcTensor.norm_def
              (iteratedCovGrad (I := I) g r₁ s₁ m S)).symm] at hSe
        rw [show Integral.L2.tensorL2Norm (I := I) g r₂ (s₂ + m)
              (iteratedCovGrad (I := I) g r₂ s₂ m T).toFun =
              ‖iteratedCovGrad (I := I) g r₂ s₂ m T‖ from
            (Integral.L2.SmoothCcTensor.norm_def
              (iteratedCovGrad (I := I) g r₂ s₂ m T)).symm] at hTe
        set Iφp : ℝ := ∫ x, Sj i x ^ p ∂μ with hIφp
        set Iψq : ℝ := ∫ x, Tj l x ^ q ∂μ with hIψq
        have hIφp_nn : 0 ≤ Iφp := by
          rw [hIφp]; exact integral_nonneg (fun x => Real.rpow_nonneg (hSj_nn i x) _)
        have hIψq_nn : 0 ≤ Iψq := by
          rw [hIψq]; exact integral_nonneg (fun x => Real.rpow_nonneg (hTj_nn l x) _)
        have hys := young_weighted_product_bound wi wl (CSf m) (CTf m) ΛS ΛT
          ‖iteratedCovGrad (I := I) g r₁ s₁ m S‖
          ‖iteratedCovGrad (I := I) g r₂ s₂ m T‖
          Iφp Iψq hwi_nn hwl_nn hwsum (hCSf_nn m) (hCTf_nn m) hΛS hΛT
          (norm_nonneg _) (norm_nonneg _) hIφp_nn hIψq_nn hSe hTe
        have hNS_sum : ‖iteratedCovGrad (I := I) g r₁ s₁ m S‖ ^ 2 ≤
            ∑ a ∈ Finset.range (k + 1),
              ‖iteratedCovGrad (I := I) g r₁ s₁ a S‖ ^ 2 :=
          Finset.single_le_sum
            (f := fun a => ‖iteratedCovGrad (I := I) g r₁ s₁ a S‖ ^ 2)
            (fun a _ => sq_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hmk))
        have hNT_sum : ‖iteratedCovGrad (I := I) g r₂ s₂ m T‖ ^ 2 ≤
            ∑ b ∈ Finset.range (k + 1),
              ‖iteratedCovGrad (I := I) g r₂ s₂ b T‖ ^ 2 :=
          Finset.single_le_sum
            (f := fun b => ‖iteratedCovGrad (I := I) g r₂ s₂ b T‖ ^ 2)
            (fun b _ => sq_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hmk))
        have hwi_le1 : wi ≤ 1 := by rw [← hwsum]; linarith
        have hwl_le1 : wl ≤ 1 := by rw [← hwsum]; linarith
        calc ∫ x, Sj i x * Tj l x ∂μ
            ≤ Iφp ^ wi * Iψq ^ wl := hHolder
          _ ≤ CSf m * CTf m * (wi * (ΛT ^ 2 *
                ‖iteratedCovGrad (I := I) g r₁ s₁ m S‖ ^ 2)
              + wl * (ΛS ^ 2 *
                ‖iteratedCovGrad (I := I) g r₂ s₂ m T‖ ^ 2)) := hys
          _ ≤ Cbig * ((ΛT ^ 2 * ∑ a ∈ Finset.range (k + 1),
                ‖iteratedCovGrad (I := I) g r₁ s₁ a S‖ ^ 2)
              + (ΛS ^ 2 * ∑ b ∈ Finset.range (k + 1),
                ‖iteratedCovGrad (I := I) g r₂ s₂ b T‖ ^ 2)) := by
              refine le_trans (mul_le_mul_of_nonneg_right (hCSCT_le m hmk) ?_) ?_
              · have : 0 ≤ wi * (ΛT ^ 2 *
                    ‖iteratedCovGrad (I := I) g r₁ s₁ m S‖ ^ 2)
                  + wl * (ΛS ^ 2 *
                    ‖iteratedCovGrad (I := I) g r₂ s₂ m T‖ ^ 2) := by positivity
                exact this
              · refine mul_le_mul_of_nonneg_left ?_ hCbig_nn
                have harm1 : wi * (ΛT ^ 2 *
                    ‖iteratedCovGrad (I := I) g r₁ s₁ m S‖ ^ 2) ≤
                    ΛT ^ 2 * ∑ a ∈ Finset.range (k + 1),
                      ‖iteratedCovGrad (I := I) g r₁ s₁ a S‖ ^ 2 := by
                  calc wi * (ΛT ^ 2 *
                        ‖iteratedCovGrad (I := I) g r₁ s₁ m S‖ ^ 2)
                      ≤ 1 * (ΛT ^ 2 *
                        ‖iteratedCovGrad (I := I) g r₁ s₁ m S‖ ^ 2) :=
                        mul_le_mul_of_nonneg_right hwi_le1 (by positivity)
                    _ = ΛT ^ 2 *
                        ‖iteratedCovGrad (I := I) g r₁ s₁ m S‖ ^ 2 := one_mul _
                    _ ≤ ΛT ^ 2 * ∑ a ∈ Finset.range (k + 1),
                          ‖iteratedCovGrad (I := I) g r₁ s₁ a S‖ ^ 2 :=
                        mul_le_mul_of_nonneg_left hNS_sum (by positivity)
                have harm2 : wl * (ΛS ^ 2 *
                    ‖iteratedCovGrad (I := I) g r₂ s₂ m T‖ ^ 2) ≤
                    ΛS ^ 2 * ∑ b ∈ Finset.range (k + 1),
                      ‖iteratedCovGrad (I := I) g r₂ s₂ b T‖ ^ 2 := by
                  calc wl * (ΛS ^ 2 *
                        ‖iteratedCovGrad (I := I) g r₂ s₂ m T‖ ^ 2)
                      ≤ 1 * (ΛS ^ 2 *
                        ‖iteratedCovGrad (I := I) g r₂ s₂ m T‖ ^ 2) :=
                        mul_le_mul_of_nonneg_right hwl_le1 (by positivity)
                    _ = ΛS ^ 2 *
                        ‖iteratedCovGrad (I := I) g r₂ s₂ m T‖ ^ 2 := one_mul _
                    _ ≤ ΛS ^ 2 * ∑ b ∈ Finset.range (k + 1),
                          ‖iteratedCovGrad (I := I) g r₂ s₂ b T‖ ^ 2 :=
                        mul_le_mul_of_nonneg_left hNT_sum (by positivity)
                linarith
  constructor
  · have hcont : Continuous (fun x => ∑ i ∈ Finset.range (k + 1), Sj i x *
        ∑ l ∈ Finset.range (k + 1 - i), Tj l x) := by
      refine continuous_finset_sum _ (fun i _ => (hSj_cont i).mul ?_)
      exact continuous_finset_sum _ (fun l _ => hTj_cont l)
    rw [hμ]
    exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · have hrw : (∫ x, ∑ i ∈ Finset.range (k + 1), Sj i x *
          ∑ l ∈ Finset.range (k + 1 - i), Tj l x ∂μ)
        = ∑ i ∈ Finset.range (k + 1), ∑ l ∈ Finset.range (k + 1 - i),
            ∫ x, Sj i x * Tj l x ∂μ := by
      rw [MeasureTheory.integral_finset_sum _
        (fun i _ => by
          rw [hμ]
          exact ((hSj_cont i).mul (continuous_finset_sum _
            (fun l _ => hTj_cont l))).integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _))]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [show (∫ x, Sj i x * ∑ l ∈ Finset.range (k + 1 - i), Tj l x ∂μ)
            = ∫ x, ∑ l ∈ Finset.range (k + 1 - i), Sj i x * Tj l x ∂μ from by
          simp only [Finset.mul_sum],
        MeasureTheory.integral_finset_sum _ (fun l _ => hint_cell i l)]
    rw [hrw]
    have hsum_le : ∑ i ∈ Finset.range (k + 1), ∑ l ∈ Finset.range (k + 1 - i),
          ∫ x, Sj i x * Tj l x ∂μ ≤
        ∑ i ∈ Finset.range (k + 1), ∑ l ∈ Finset.range (k + 1 - i),
          Cbig * ((ΛT ^ 2 * ∑ a ∈ Finset.range (k + 1),
              ‖iteratedCovGrad (I := I) g r₁ s₁ a S‖ ^ 2)
            + (ΛS ^ 2 * ∑ b ∈ Finset.range (k + 1),
              ‖iteratedCovGrad (I := I) g r₂ s₂ b T‖ ^ 2)) := by
      refine Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun l hl => ?_))
      have hik : i ≤ k := by rw [Finset.mem_range] at hi; omega
      have hilk : i + l ≤ k := by
        rw [Finset.mem_range] at hi hl; omega
      exact hcell i hik l hilk
    refine le_trans hsum_le ?_
    set c : ℝ := Cbig * ((ΛT ^ 2 * ∑ a ∈ Finset.range (k + 1),
        ‖iteratedCovGrad (I := I) g r₁ s₁ a S‖ ^ 2)
      + (ΛS ^ 2 * ∑ b ∈ Finset.range (k + 1),
        ‖iteratedCovGrad (I := I) g r₂ s₂ b T‖ ^ 2)) with hc
    have hc_nn : 0 ≤ c := by
      rw [hc]; exact mul_nonneg hCbig_nn (by linarith [hAS_nn, hAT_nn])
    have hinner : ∀ i ∈ Finset.range (k + 1),
        (∑ _l ∈ Finset.range (k + 1 - i), c) ≤ (k + 1 : ℝ) * c := by
      intro i _
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_range]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le (k + 1) i) hc_nn
    have hdouble : (∑ i ∈ Finset.range (k + 1), ∑ _l ∈ Finset.range (k + 1 - i), c)
        ≤ (k + 1 : ℝ) * ((k + 1 : ℝ) * c) := by
      calc (∑ i ∈ Finset.range (k + 1), ∑ _l ∈ Finset.range (k + 1 - i), c)
          ≤ ∑ _i ∈ Finset.range (k + 1), (k + 1 : ℝ) * c := Finset.sum_le_sum hinner
        _ = (k + 1 : ℝ) * ((k + 1 : ℝ) * c) := by
            rw [Finset.sum_const, nsmul_eq_mul, Finset.card_range]; push_cast; ring
    refine le_trans hdouble (le_of_eq ?_)
    rw [hc]
    ring

noncomputable def cometricDoubleTraceCastG0 (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 3 1 where
  toSection :=
    (DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.cometricDoubleTraceField
      (I := I) g₁ 1).toSection
  hasCompactSupport :=
    (DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.cometricDoubleTraceField
      (I := I) g₁ 1).hasCompactSupport

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem ricciArmOrder1KoszulCoeff_eq_raisedKoszul_contract_cometricDoubleTraceCastG0 (g₀ g₁ : SmoothRiemannianMetric I M) :
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder1KoszulCoeff
        (I := I) g₀ g₁ =
      ccOperatorFieldComp (I := I) (M := M) g₀ 3 1 2 (raisedKoszul (I := I) g₀ g₁)
        (cometricDoubleTraceCastG0 (I := I) g₀ g₁) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rfl

section RaisedKoszulOrder0SumHelpers
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

private lemma raisedKoszul_norm_eq_of_sq_eq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a ^ 2 = b ^ 2) : a = b := by
  have hsqrt := congrArg Real.sqrt h
  rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb] at hsqrt

omit [NeZero (Module.finrank ℝ E)] in
private lemma raisedKoszul_norm_iteratedCovGrad_domDomCongr_eq
    (g₀ : SmoothRiemannianMetric I M) (s : ℕ) (σ : Equiv.Perm (Fin s))
    (S : SmoothCcTensor g₀ 0 s) (n : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 0 s n (domDomCongrSection (I := I) g₀ σ S)‖ =
      ‖iteratedCovGrad (I := I) g₀ 0 s n S‖ := by
  refine raisedKoszul_norm_eq_of_sq_eq (norm_nonneg _) (norm_nonneg _) ?_
  rw [SmoothCcTensor.norm_def, SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
  have hpt : (fun x => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + n) x
        ((iteratedCovGrad (I := I) g₀ 0 s n
          (domDomCongrSection (I := I) g₀ σ S)).toSection x)) =
      (fun x => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + n) x
        ((iteratedCovGrad (I := I) g₀ 0 s n S).toSection x)) :=
    funext fun x =>
      riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) g₀ σ S n x
  rw [hpt]

omit [NeZero (Module.finrank ℝ E)] in
private lemma raisedKoszul_norm_iteratedCovGrad_symmS_le
    (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2) (m : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 0 2 m (ccTensor02Symm (I := I) g₀ P)‖ ≤
      ‖iteratedCovGrad (I := I) g₀ 0 2 m P‖ := by
  rw [iteratedCovGrad_symmS_eq (I := I) g₀ P m]
  refine le_trans (norm_add_le _ _) ?_
  simp only [norm_smul, Real.norm_eq_abs]
  rw [raisedKoszul_norm_iteratedCovGrad_domDomCongr_eq (I := I) g₀ 2 (Equiv.swap 0 1) P m,
    show |(1 / 2 : ℝ)| = 1 / 2 from by norm_num]
  linarith

omit [NeZero (Module.finrank ℝ E)] in
private lemma raisedKoszul_norm_iteratedCovGrad_eq_koszul
    (g₀ g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w) (n : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 1 2 n (raisedKoszul (I := I) g₀ g₁)‖ =
      ‖iteratedCovGrad (I := I) g₀ 0 3 n (koszulCovecCc (I := I) g₀ P)‖ := by
  refine raisedKoszul_norm_eq_of_sq_eq (norm_nonneg _) (norm_nonneg _) ?_
  rw [raisedKoszul_eq_cometricRaiseSlot0Field_koszulCovecCc (I := I) g₀ g₁ P htie,
    SmoothCcTensor.norm_def, SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
  have hpt : (fun x => riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
        ((iteratedCovGrad (I := I) g₀ 1 2 n
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
            (koszulCovecCc (I := I) g₀ P))).toSection x)) =
      (fun x => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
        ((iteratedCovGrad (I := I) g₀ 0 3 n (koszulCovecCc (I := I) g₀ P)).toSection x)) :=
    funext fun x =>
      riemannianFiberNormSq_iteratedCovGrad_cometricRaiseSlot0Field_koszul_eq (I := I) g₀ P n x
  rw [hpt]

omit [NeZero (Module.finrank ℝ E)] in
private lemma raisedKoszul_norm_iteratedCovGrad_koszul_le
    (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2) (n : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 0 3 n (koszulCovecCc (I := I) g₀ P)‖ ≤
      (3 / 2) * ‖iteratedCovGrad (I := I) g₀ 0 2 (n + 1) P‖ := by
  set W : SmoothCcTensor g₀ 0 3 := symmSCovGrad3 (I := I) g₀ P with hW
  set DA : SmoothCcTensor g₀ 0 3 :=
    domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 2) W with hDA
  set DB : SmoothCcTensor g₀ 0 3 := domDomCongrSection (I := I) g₀ (finRotate 3) W with hDB
  set DC : SmoothCcTensor g₀ 0 3 :=
    domDomCongrSection (I := I) g₀ (Equiv.swap (1 : Fin 3) 2) W with hDC
  have hkos : koszulCovecCc (I := I) g₀ P = (1 / 2 : ℝ) • (DA + DB - DC) := by
    rw [koszulCovecCc, hDA, hDB, hDC, hW]
  have hWeq : ‖iteratedCovGrad (I := I) g₀ 0 3 n W‖ =
      ‖iteratedCovGrad (I := I) g₀ 0 2 (n + 1) (ccTensor02Symm (I := I) g₀ P)‖ := by
    refine raisedKoszul_norm_eq_of_sq_eq (norm_nonneg _) (norm_nonneg _) ?_
    rw [SmoothCcTensor.norm_def, SmoothCcTensor.norm_def,
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs,
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs, hW, symmSCovGrad3_def]
    have hpt : (fun x => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
          ((iteratedCovGrad (I := I) g₀ 0 3 n
            (covGrad (I := I) (M := M) g₀ 0 2 (ccTensor02Symm (I := I) g₀ P))).toSection x)) =
        (fun x => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (n + 1)) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (n + 1) (ccTensor02Symm (I := I) g₀ P)).toSection x)) :=
      funext fun x =>
        rfns_iteratedCovGrad_covGrad_comm_rs (I := I) g₀ 0 2 n (ccTensor02Symm (I := I) g₀ P) x
    rw [hpt]
  have hDAeq : ‖iteratedCovGrad (I := I) g₀ 0 3 n DA‖ =
      ‖iteratedCovGrad (I := I) g₀ 0 3 n W‖ := by
    rw [hDA]; exact raisedKoszul_norm_iteratedCovGrad_domDomCongr_eq (I := I) g₀ 3 _ W n
  have hDBeq : ‖iteratedCovGrad (I := I) g₀ 0 3 n DB‖ =
      ‖iteratedCovGrad (I := I) g₀ 0 3 n W‖ := by
    rw [hDB]; exact raisedKoszul_norm_iteratedCovGrad_domDomCongr_eq (I := I) g₀ 3 _ W n
  have hDCeq : ‖iteratedCovGrad (I := I) g₀ 0 3 n DC‖ =
      ‖iteratedCovGrad (I := I) g₀ 0 3 n W‖ := by
    rw [hDC]; exact raisedKoszul_norm_iteratedCovGrad_domDomCongr_eq (I := I) g₀ 3 _ W n
  have hsymmS_le := raisedKoszul_norm_iteratedCovGrad_symmS_le (I := I) g₀ P (n + 1)
  have hWbound : ‖iteratedCovGrad (I := I) g₀ 0 3 n W‖ ≤
      ‖iteratedCovGrad (I := I) g₀ 0 2 (n + 1) P‖ := le_trans (le_of_eq hWeq) hsymmS_le
  have htri : ‖iteratedCovGrad (I := I) g₀ 0 3 n (DA + DB - DC)‖ ≤
      ‖iteratedCovGrad (I := I) g₀ 0 3 n DA‖ + ‖iteratedCovGrad (I := I) g₀ 0 3 n DB‖ +
        ‖iteratedCovGrad (I := I) g₀ 0 3 n DC‖ := by
    rw [show DA + DB - DC = DA + DB + (-DC) from by abel, iteratedCovGrad_add,
      iteratedCovGrad_add, iteratedCovGrad_neg]
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_neg]
    exact add_le_add (norm_add_le _ _) le_rfl
  rw [hDAeq, hDBeq, hDCeq] at htri
  rw [hkos, iteratedCovGrad_smul_real, norm_smul, Real.norm_eq_abs,
    show |(1 / 2 : ℝ)| = 1 / 2 from by norm_num]
  linarith [htri, hWbound]

end RaisedKoszulOrder0SumHelpers

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral in
theorem raisedKoszul_order0sup_jetL2_ballUniform_generic
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ (Λ : ℝ) (F : ℕ → ℝ), 0 ≤ Λ ∧ (∀ i, 0 ≤ F i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x
            ((raisedKoszul (I := I) g₀ g₁).toSection x) ≤ Λ ^ 2) ∧
        ∀ (i : ℕ), i ≤ a →
          ∑ n ∈ Finset.range (i + 1),
              ‖iteratedCovGrad (I := I) g₀ 1 2 n (raisedKoszul (I := I) g₀ g₁)‖ ^ 2 ≤ F i := by
  obtain ⟨C, hC_nn, hC⟩ :=
    riemannianFiberNormSq_raisedKoszul_le_of_lt_one (I := I) g₀ (le_max_right δ₀ 0) (max_lt hδ₀ one_pos)
  obtain ⟨Csob, hCsob_nn, hCsob⟩ :=
    exists_Csob_convexPerturbation_pointwise_C2_le (I := I) g₀ a ha_super
  refine ⟨C * (Csob * R), fun i => ((i : ℝ) + 1) * ((3 / 2) * R) ^ 2,
    mul_nonneg hC_nn (mul_nonneg hCsob_nn hR), fun i => by positivity, ?_⟩
  intro g₁ P δ hδ_le hδ htie hPball
  refine ⟨?_, ?_⟩
  · intro x
    obtain ⟨v, hv⟩ : ∃ v : TangentSpace I x, v ≠ 0 := by
      haveI : Nontrivial (TangentSpace I x) := by
        have hfr : 0 < Module.finrank ℝ (TangentSpace I x) := by
          have heq : Module.finrank ℝ (TangentSpace I x) = Module.finrank ℝ E := rfl
          rw [heq]; exact Nat.pos_of_ne_zero (NeZero.ne _)
        exact Module.nontrivial_of_finrank_pos hfr
      exact exists_ne 0
    have hpos : 0 < g₀.inner x v v := g₀.pos x v hv
    have hbound := hδ x v v
    have hsqrt_pos : 0 < Real.sqrt (g₀.inner x v v) := Real.sqrt_pos.mpr hpos
    have habs_nn : 0 ≤ |ccTensorBilinSymm (I := I) g₀ P x v v| := abs_nonneg _
    have hδ0 : 0 ≤ δ := by
      by_contra hδc
      have hδc' : δ < 0 := lt_of_not_ge hδc
      have hrhs_neg : δ * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x v v) < 0 := by
        have h1 : δ * Real.sqrt (g₀.inner x v v) < 0 := mul_neg_of_neg_of_pos hδc' hsqrt_pos
        exact mul_neg_of_neg_of_pos h1 hsqrt_pos
      linarith [le_trans habs_nn hbound]
    have hrfns := hC g₁ P htie (le_trans hδ_le (le_max_left δ₀ 0)) hδ0 hδ x
    have henv := hCsob P P hR hPball hPball 0 (Set.mem_Icc.mpr ⟨le_refl 0, zero_le_one⟩) x
    simp only [DifferentialGeometry.PDE.DeTurck.RicciLinearization.convexPerturbation_zero] at henv
    letI instTens12 : Bundle.RiemannianBundle
        (fun b : M => Tensor0SBundle.TensorRSSpace 0 (2 + 1) I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + 1)
    set N : ℝ := ‖(iteratedCovGrad (I := I) g₀ 0 2 1 P).toSection x‖ with hN_def
    have hN_nn : 0 ≤ N := norm_nonneg _
    have hnorm_le : N ≤ Csob * R := by
      refine le_trans ?_ henv
      exact Finset.single_le_sum (f := fun j =>
          letI : Bundle.RiemannianBundle
              (fun b : M => Tensor0SBundle.TensorRSSpace 0 (2 + j) I b) :=
            Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
          ‖(iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x‖)
          (fun j _ =>
            letI : Bundle.RiemannianBundle
                (fun b : M => Tensor0SBundle.TensorRSSpace 0 (2 + j) I b) :=
              Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
            norm_nonneg ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x))
          (by simp : (1 : ℕ) ∈ Finset.range 3)
    have hsq : N ^ 2 ≤ (Csob * R) ^ 2 := by nlinarith [hnorm_le, hN_nn]
    refine le_trans hrfns ?_
    rw [show (C * (Csob * R)) ^ 2 = C ^ 2 * (Csob * R) ^ 2 from by rw [mul_pow]]
    exact mul_le_mul_of_nonneg_left hsq (sq_nonneg C)
  · intro i hi
    have hbnd : ∀ n ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 1 2 n (raisedKoszul (I := I) g₀ g₁)‖ ^ 2 ≤
          ((3 / 2) * R) ^ 2 := by
      intro n hn
      have hni : n ≤ i := by have := Finset.mem_range.mp hn; omega
      have h3a := raisedKoszul_norm_iteratedCovGrad_eq_koszul (I := I) g₀ g₁ P htie n
      have h3b := raisedKoszul_norm_iteratedCovGrad_koszul_le (I := I) g₀ P n
      have hPn1 : ‖iteratedCovGrad (I := I) g₀ 0 2 (n + 1) P‖ ≤ R := hPball (n + 1) (by omega)
      have hle : ‖iteratedCovGrad (I := I) g₀ 1 2 n (raisedKoszul (I := I) g₀ g₁)‖ ≤
          (3 / 2) * R := by
        rw [h3a]
        exact le_trans h3b (mul_le_mul_of_nonneg_left hPn1 (by norm_num))
      exact pow_le_pow_left₀ (norm_nonneg _) hle 2
    refine le_trans (Finset.sum_le_sum hbnd) (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    ring

section CometricCastG0Decomposition

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma cometricDoubleTraceFib_sub_toModel_eq
    (g₀ g₁ : SmoothRiemannianMetric I M) (p : ℕ) (x : M)
    (w : Tensor0SSpace (p + 2) I x) (m : Fin p → E) :
    Tensor0SSpace.toModel
        ((cometricDoubleTraceFib (I := I) g₁ p x
            - cometricDoubleTraceFib (I := I) g₀ p x) w) m =
      ∑ k : Fin (Module.finrank ℝ E),
        (Tensor0SSpace.toModel w)
          (Fin.cons
            ((metricComparisonDiffEndo (I := I) g₀ g₁ x
              (cometricLmodel (I := I) g₀ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k))) : TangentSpace I x) : E)
            (Fin.cons (((Module.finBasis ℝ E) k : E)) m)) := by
  classical
  rw [ContinuousLinearMap.sub_apply, Tensor0SSpace.toModel_sub,
    ContinuousMultilinearMap.sub_apply,
    cometricDoubleTraceFib_toModel, cometricDoubleTraceFib_toModel,
    modelDoubleTrace_apply, modelDoubleTrace_apply, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  set wm : ContinuousMultilinearMap ℝ (fun _ : Fin (p + 2) => E) ℝ :=
    Tensor0SSpace.toModel w with hwm
  set tail : Fin (p + 1) → E := Fin.cons (((Module.finBasis ℝ E) k : E)) m with htail
  have hcurry : ∀ z : TangentSpace I x,
      wm (Fin.cons ((z : E)) tail)
        = ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (p + 2) => E) ℝ) wm
            ((z : TangentSpace I x) : E)) tail := by
    intro z; rw [continuousMultilinearCurryLeftEquiv_apply]
  rw [hcurry (cometricLmodel (I := I) g₁ x
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis k))),
    hcurry (cometricLmodel (I := I) g₀ x
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis k))),
    hcurry (metricComparisonDiffEndo (I := I) g₀ g₁ x
        (cometricLmodel (I := I) g₀ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k))))]
  rw [← ContinuousMultilinearMap.sub_apply, ← map_sub]
  congr 2
  rw [cometricLmodel_sub_eq_gInvDiffRaisedEndo (I := I) g₀ g₁ x
    ((Module.finBasis ℝ E).cDualBasis k)]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma cometricCastG0_sub_doubleTrace_clm
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 1 I x from
        (cometricDoubleTraceCastG0 (I := I) g₀ g₁ - cometricDoubleTraceField (I := I) g₀ 1).toSection x) =
      cometricDoubleTraceFib (I := I) g₁ 1 x - cometricDoubleTraceFib (I := I) g₀ 1 x := by
  rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]
  have hcast : (cometricDoubleTraceCastG0 (I := I) g₀ g₁).toSection x
      = (cometricDoubleTraceField (I := I) g₁ 1).toSection x := rfl
  rw [hcast, cometricDoubleTraceField_toSection, cometricDoubleTraceField_toSection]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem cometricCastG0_eq_doubleTrace_add_appCcRS
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    cometricDoubleTraceCastG0 (I := I) g₀ g₁ =
      cometricDoubleTraceField (I := I) g₀ 1 +
        ccOperatorFieldComp (I := I) (M := M) g₀ 3 3 1
          (cometricDoubleTraceField (I := I) g₀ 1)
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ 2
            (gInvDiffRaisedEndoField (I := I) g₀ g₁)) := by
  classical
  have hsub : cometricDoubleTraceCastG0 (I := I) g₀ g₁ - cometricDoubleTraceField (I := I) g₀ 1 =
      ccOperatorFieldComp (I := I) (M := M) g₀ 3 3 1
        (cometricDoubleTraceField (I := I) g₀ 1)
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 2
          (gInvDiffRaisedEndoField (I := I) g₀ g₁)) := by
    apply SmoothCcTensor.ext
    apply ContMDiffSection.ext
    intro x
    refine tensorRSSpace_ext 3 1 x (fun w => ?_)
    apply Tensor0SSpace.toModel_injective
    refine ContinuousMultilinearMap.ext (fun m => ?_)
    beta_reduce
    rw [cometricCastG0_sub_doubleTrace_clm (I := I) g₀ g₁ x,
      cometricDoubleTraceFib_sub_toModel_eq (I := I) g₀ g₁ 1 x w m,
      appCcRS_toSection, ContinuousLinearMap.comp_apply,
      cometricDoubleTraceField_toSection, cometricDoubleTraceFib_toModel,
      modelDoubleTrace_apply]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [slotInsertEndoCc_toSection, slotInsertEndoFib_apply_eval, Fin.cons_zero,
      Fin.update_cons_zero]
    rfl
  rw [← hsub]; abel

end CometricCastG0Decomposition

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck in
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
theorem cometricDoubleTraceField_order0sup_jetL2_ballUniform_generic
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ (Λ : ℝ) (F : ℕ → ℝ), 0 ≤ Λ ∧ (∀ i, 0 ≤ F i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 3 1 x
            ((cometricDoubleTraceCastG0 (I := I) g₀ g₁).toSection x) ≤ Λ ^ 2) ∧
        ∀ (i : ℕ), i ≤ a →
          ∑ l ∈ Finset.range (i + 1),
              ‖iteratedCovGrad (I := I) g₀ 3 1 l (cometricDoubleTraceCastG0 (I := I) g₀ g₁)‖ ^ 2 ≤ F i := by
  classical
  set Φ : SmoothCcTensor g₀ 3 1 := cometricDoubleTraceField (I := I) g₀ 1 with hΦ_def
  obtain ⟨C_base, hC_base_nn, hC_base⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_slotInsertEndoCc_zero_gInvDiffRaisedEndoField_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨K_mos, hK_mos_nn, hK_mos⟩ :=
    diagonalProductGrid_riemannianFiberNormSq_integral_ballUniform
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  have hSΦ_ex : ∀ i : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + i) x
        ((iteratedCovGrad (I := I) g₀ 3 1 i Φ).toSection x) ≤ K :=
    fun i => exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 3 (1 + i)
      (iteratedCovGrad (I := I) g₀ 3 1 i Φ)
  choose SΦ hSΦ_nn hSΦ using hSΦ_ex
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  set KW : ℕ → ℝ := fun q => fr ^ 2 * C_base q * K_mos q with hKW_def
  set FW : ℕ → ℝ := fun i => ∑ q ∈ Finset.range (i + 1), KW q with hFW_def
  set KD : ℕ → ℝ := fun l => diagonalGridGrowthFactor (E := E) l *
    (∑ i' ∈ Finset.range (l + 1), SΦ i') * FW l with hKD_def
  set aL : ℕ → ℝ :=
    fun l => ‖iteratedCovGrad (I := I) g₀ 3 1 l Φ‖ ^ 2 with haL_def
  set Ff : ℕ → ℝ :=
    fun i => ∑ l ∈ Finset.range (i + 1), (2 * aL l + 2 * KD l) with hFf_def
  set ΛT2 : ℝ := fr ^ 2 * C_base 0 with hΛT2_def
  have hFnn : ∀ i, 0 ≤ Ff i := by
    intro i
    simp only [hFf_def]
    apply Finset.sum_nonneg
    intro l _
    have h1 : 0 ≤ aL l := by simp only [haL_def]; positivity
    have h2 : 0 ≤ KD l := by
      simp only [hKD_def, hFW_def, hKW_def]
      refine mul_nonneg (mul_nonneg (appCcGdiag_nonneg _)
        (Finset.sum_nonneg (fun i' _ => hSΦ_nn i'))) ?_
      exact Finset.sum_nonneg (fun q _ =>
        mul_nonneg (mul_nonneg (by positivity) (hC_base_nn q)) (hK_mos_nn q))
    linarith
  refine ⟨Real.sqrt (2 * SΦ 0 + 2 * (SΦ 0 * ΛT2)), Ff, Real.sqrt_nonneg _, hFnn, ?_⟩
  · intro g₁ P δ hδ_le hδ htie hPball
    by_cases hMne : Nonempty M
    · obtain ⟨x₀⟩ := hMne
      have hδ0 : 0 ≤ δ := by
        obtain ⟨v, hv⟩ : ∃ v : TangentSpace I x₀, v ≠ 0 := by
          haveI : Nontrivial (TangentSpace I x₀) := by
            have hfr' : 0 < Module.finrank ℝ (TangentSpace I x₀) := by
              have heq : Module.finrank ℝ (TangentSpace I x₀) = Module.finrank ℝ E := rfl
              rw [heq]; exact Nat.pos_of_ne_zero (NeZero.ne _)
            exact Module.nontrivial_of_finrank_pos hfr'
          exact exists_ne 0
        have hpos : 0 < g₀.inner x₀ v v := g₀.pos x₀ v hv
        have hbound := hδ x₀ v v
        have hsqrt_pos : 0 < Real.sqrt (g₀.inner x₀ v v) := Real.sqrt_pos.mpr hpos
        have habs_nn : 0 ≤ |ccTensorBilinSymm (I := I) g₀ P x₀ v v| := abs_nonneg _
        by_contra hδc
        have hδc' : δ < 0 := lt_of_not_ge hδc
        have hrhs_neg : δ * Real.sqrt (g₀.inner x₀ v v) * Real.sqrt (g₀.inner x₀ v v) < 0 := by
          have h1 : δ * Real.sqrt (g₀.inner x₀ v v) < 0 := mul_neg_of_neg_of_pos hδc' hsqrt_pos
          exact mul_neg_of_neg_of_pos h1 hsqrt_pos
        linarith [le_trans habs_nn hbound]
      set W : SmoothCcTensor g₀ 3 3 :=
        endoSlotZeroCcTensor (I := I) (M := M) g₀ 2 (gInvDiffRaisedEndoField (I := I) g₀ g₁)
        with hW_def
      have hid : cometricDoubleTraceCastG0 (I := I) g₀ g₁ =
          Φ + ccOperatorFieldComp (I := I) (M := M) g₀ 3 3 1 Φ W := by
        have h := cometricCastG0_eq_doubleTrace_add_appCcRS (I := I) g₀ g₁
        rw [← hΦ_def, ← hW_def] at h
        exact h
      have hΛT : ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 3 3 x (W.toSection x) ≤ ΛT2 := by
        intro x
        have h1 := rfns_iteratedCovGrad_slotInsertEndoCc_le_endo (I := I) g₀ 2
          (gInvDiffRaisedEndoField (I := I) g₀ g₁) 0 x
        simp only [iteratedCovGrad_zero] at h1
        rw [← hW_def, ← hfr_def] at h1
        have h2 := hC_base g₁ P htie hδ_le hδ0 hδ 0 x
        simp only [iteratedCovGrad_zero] at h2
        have hgrid0 : (∑ n ∈ Finset.range (0 + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n 0,
            ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) = 1 := by
          simp
        rw [hgrid0, mul_one] at h2
        calc riemannianFiberNormSq (I := I) (M := M) g₀ 3 3 x (W.toSection x)
            ≤ fr ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x
                ((endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
                  (gInvDiffRaisedEndoField (I := I) g₀ g₁)).toSection x) := h1
          _ ≤ fr ^ 2 * C_base 0 := mul_le_mul_of_nonneg_left h2 (sq_nonneg fr)
          _ = ΛT2 := hΛT2_def.symm
      have hstep2 : ∀ q : ℕ, q ≤ a →
          ‖iteratedCovGrad (I := I) g₀ 3 3 q W‖ ^ 2 ≤ KW q := by
        intro q hq
        obtain ⟨hgi, hgb⟩ := hK_mos P hPball q hq
        have hpt : ∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + q) x
                ((iteratedCovGrad (I := I) g₀ 3 3 q W).toSection x) ≤
              fr ^ 2 * C_base q *
                (∑ n ∈ Finset.range (q + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n q,
                  ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) := by
          intro x
          have h1 := rfns_iteratedCovGrad_slotInsertEndoCc_le_endo (I := I) g₀ 2
            (gInvDiffRaisedEndoField (I := I) g₀ g₁) q x
          rw [← hW_def, ← hfr_def] at h1
          have h2 := hC_base g₁ P htie hδ_le hδ0 hδ q x
          calc riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + q) x
                ((iteratedCovGrad (I := I) g₀ 3 3 q W).toSection x)
              ≤ fr ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + q) x
                  ((iteratedCovGrad (I := I) g₀ 1 1 q
                    (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
                      (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x) := h1
            _ ≤ fr ^ 2 * (C_base q *
                  (∑ n ∈ Finset.range (q + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n q,
                    ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                      ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))) :=
                mul_le_mul_of_nonneg_left h2 (sq_nonneg fr)
            _ = fr ^ 2 * C_base q *
                  (∑ n ∈ Finset.range (q + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n q,
                    ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                      ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) := by ring
        have hint : MeasureTheory.Integrable
            (fun x => fr ^ 2 * C_base q *
              (∑ n ∈ Finset.range (q + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n q,
                ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)))
            (riemannianVolumeMeasure (I := I) (M := M) g₀) := hgi.const_mul _
        have hkey := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 3 (3 + q)
          (iteratedCovGrad (I := I) g₀ 3 3 q W) _ hint hpt
        refine le_trans hkey ?_
        rw [MeasureTheory.integral_const_mul, hKW_def]
        exact mul_le_mul_of_nonneg_left hgb (mul_nonneg (sq_nonneg fr) (hC_base_nn q))
      have hstep3 : ∀ l : ℕ, l ≤ a →
          ‖iteratedCovGrad (I := I) g₀ 3 1 l (ccOperatorFieldComp (I := I) (M := M) g₀ 3 3 1 Φ W)‖ ^ 2 ≤
            KD l := by
        intro l hl
        have hpt : ∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + l) x
                ((iteratedCovGrad (I := I) g₀ 3 1 l
                  (ccOperatorFieldComp (I := I) (M := M) g₀ 3 3 1 Φ W)).toSection x) ≤
              (diagonalGridGrowthFactor (E := E) l * (∑ i' ∈ Finset.range (l + 1), SΦ i')) *
                (∑ q ∈ Finset.range (l + 1),
                  riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + q) x
                    ((iteratedCovGrad (I := I) g₀ 3 3 q W).toSection x)) := by
          intro x
          refine le_trans (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le
            (I := I) (M := M) g₀ l 3 3 1 Φ W x) ?_
          rw [mul_assoc]
          refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg _)
          rw [Finset.sum_mul]
          refine Finset.sum_le_sum (fun i' _ => ?_)
          refine mul_le_mul (hSΦ i' x) ?_
            (Finset.sum_nonneg (fun q _ => riemannianFiberNormSq_nonneg _ _ _ _ _)) (hSΦ_nn i')
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_
            (fun q _ _ => riemannianFiberNormSq_nonneg _ _ _ _ _)
          intro q hq
          rw [Finset.mem_range] at hq ⊢
          omega
        have hint : MeasureTheory.Integrable
            (fun x => (diagonalGridGrowthFactor (E := E) l * (∑ i' ∈ Finset.range (l + 1), SΦ i')) *
              (∑ q ∈ Finset.range (l + 1),
                riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + q) x
                  ((iteratedCovGrad (I := I) g₀ 3 3 q W).toSection x)))
            (riemannianVolumeMeasure (I := I) (M := M) g₀) := by
          apply MeasureTheory.Integrable.const_mul
          apply MeasureTheory.integrable_finset_sum
          intro q _
          exact integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 3 (3 + q)
            (iteratedCovGrad (I := I) g₀ 3 3 q W)
        have hkey := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 3 (1 + l)
          (iteratedCovGrad (I := I) g₀ 3 1 l (ccOperatorFieldComp (I := I) (M := M) g₀ 3 3 1 Φ W)) _ hint hpt
        refine le_trans hkey ?_
        rw [MeasureTheory.integral_const_mul,
          MeasureTheory.integral_finset_sum _ (fun q _ =>
            integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 3 (3 + q)
              (iteratedCovGrad (I := I) g₀ 3 3 q W))]
        have hconv : ∀ q ∈ Finset.range (l + 1),
            (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + q) x
                ((iteratedCovGrad (I := I) g₀ 3 3 q W).toSection x)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) =
            ‖iteratedCovGrad (I := I) g₀ 3 3 q W‖ ^ 2 := by
          intro q _
          rw [SmoothCcTensor.norm_def,
            tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g₀ 3 (3 + q)
              (iteratedCovGrad (I := I) g₀ 3 3 q W)]
        rw [Finset.sum_congr rfl hconv]
        simp only [hKD_def]
        refine mul_le_mul_of_nonneg_left ?_
          (mul_nonneg (appCcGdiag_nonneg _) (Finset.sum_nonneg (fun i' _ => hSΦ_nn i')))
        simp only [hFW_def]
        exact Finset.sum_le_sum (fun q hq => hstep2 q (by rw [Finset.mem_range] at hq; omega))
      refine ⟨?_, ?_⟩
      · intro x
        have hΛT2_nn : 0 ≤ ΛT2 := by rw [hΛT2_def]; exact mul_nonneg (sq_nonneg fr) (hC_base_nn 0)
        rw [Real.sq_sqrt (by
          have := hSΦ_nn 0
          have := mul_nonneg (hSΦ_nn 0) hΛT2_nn
          linarith : (0 : ℝ) ≤ 2 * SΦ 0 + 2 * (SΦ 0 * ΛT2))]
        rw [hid, SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]
        refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 3 1 x
          (Φ.toSection x) ((ccOperatorFieldComp (I := I) (M := M) g₀ 3 3 1 Φ W).toSection x)) ?_
        have hΦ0 : riemannianFiberNormSq (I := I) (M := M) g₀ 3 1 x (Φ.toSection x) ≤ SΦ 0 := by
          have h := hSΦ 0 x
          simp only [iteratedCovGrad_zero] at h
          exact h
        have hDIFF0 : riemannianFiberNormSq (I := I) (M := M) g₀ 3 1 x
            ((ccOperatorFieldComp (I := I) (M := M) g₀ 3 3 1 Φ W).toSection x) ≤ SΦ 0 * ΛT2 := by
          refine le_trans (riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ 3 3 1 x
            (Φ.toSection x) (W.toSection x)) ?_
          exact mul_le_mul hΦ0 (hΛT x) (riemannianFiberNormSq_nonneg _ _ _ _ _) (hSΦ_nn 0)
        linarith
      · intro i hi
        simp only [hFf_def]
        refine Finset.sum_le_sum (fun l hl => ?_)
        have hl_a : l ≤ a := by rw [Finset.mem_range] at hl; omega
        rw [hid, iteratedCovGrad_add]
        have hKDl := hstep3 l hl_a
        have haLl : aL l = ‖iteratedCovGrad (I := I) g₀ 3 1 l Φ‖ ^ 2 := by simp only [haL_def]
        have hsq := pow_le_pow_left₀ (norm_nonneg (iteratedCovGrad (I := I) g₀ 3 1 l Φ +
            iteratedCovGrad (I := I) g₀ 3 1 l (ccOperatorFieldComp (I := I) (M := M) g₀ 3 3 1 Φ W)))
          (norm_add_le (iteratedCovGrad (I := I) g₀ 3 1 l Φ)
            (iteratedCovGrad (I := I) g₀ 3 1 l (ccOperatorFieldComp (I := I) (M := M) g₀ 3 3 1 Φ W))) 2
        nlinarith [hsq, hKDl, haLl,
          sq_nonneg (‖iteratedCovGrad (I := I) g₀ 3 1 l Φ‖ -
            ‖iteratedCovGrad (I := I) g₀ 3 1 l (ccOperatorFieldComp (I := I) (M := M) g₀ 3 3 1 Φ W)‖)]
    · haveI hem : IsEmpty M := not_nonempty_iff.mp hMne
      refine ⟨fun x => (hem.false x).elim, ?_⟩
      intro i hi
      have hz : ∀ l : ℕ,
          ‖iteratedCovGrad (I := I) g₀ 3 1 l (cometricDoubleTraceCastG0 (I := I) g₀ g₁)‖ = 0 := by
        intro l
        rw [SmoothCcTensor.norm_def, tensorL2Norm_def, tensorL2Inner,
          MeasureTheory.integral_of_isEmpty, Real.sqrt_zero]
      have hsum0 : (∑ l ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 3 1 l (cometricDoubleTraceCastG0 (I := I) g₀ g₁)‖ ^ 2) = 0 := by
        apply Finset.sum_eq_zero
        intro l _
        rw [hz l]; ring
      rw [hsum0]
      exact hFnn i

theorem ricciArmOrder1KoszulCoeff_perOrder_l2_ballUniform_generic
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a →
          ‖iteratedCovGrad (I := I) g₀ 3 2 i
            (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder1KoszulCoeff
              (I := I) (M := M) g₀ g₁)‖ ^ 2 ≤ K i := by
  obtain ⟨ΛA, FΦ, hΛA, hFΦ_nn, hΦfeed⟩ :=
    raisedKoszul_order0sup_jetL2_ballUniform_generic (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨ΛB, FW, hΛB, hFW_nn, hWfeed⟩ :=
    cometricDoubleTraceField_order0sup_jetL2_ballUniform_generic
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  refine ⟨fun i => diagonalGridGrowthFactor (E := E) i *
      (exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le
        (I := I) (M := M) g₀ 1 3 2 1 i).choose * (ΛB ^ 2 * FΦ i + ΛA ^ 2 * FW i),
    fun i => by
      refine mul_nonneg (mul_nonneg (appCcGdiag_nonneg (E := E) i)
        (exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le
          (I := I) (M := M) g₀ 1 3 2 1 i).choose_spec.1) (add_nonneg ?_ ?_)
      · exact mul_nonneg (sq_nonneg _) (hFΦ_nn i)
      · exact mul_nonneg (sq_nonneg _) (hFW_nn i), ?_⟩
  intro g₁ P δ hδ_le hδ htie hPball i hi
  obtain ⟨hΦsup, hΦsum⟩ := hΦfeed g₁ P hδ_le hδ htie hPball
  obtain ⟨hWsup, hWsum⟩ := hWfeed g₁ P hδ_le hδ htie hPball
  obtain ⟨hgrid_int, hgrid_bound⟩ :=
    (exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le
      (I := I) (M := M) g₀ 1 3 2 1 i).choose_spec.2
      (raisedKoszul (I := I) g₀ g₁) (cometricDoubleTraceCastG0 (I := I) g₀ g₁) ΛA ΛB hΛA hΛB hΦsup hWsup
  rw [ricciArmOrder1KoszulCoeff_eq_raisedKoszul_contract_cometricDoubleTraceCastG0 (I := I) (M := M) g₀ g₁]
  have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 3 (2 + i)
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (ccOperatorFieldComp (I := I) (M := M) g₀ 3 1 2 (raisedKoszul (I := I) g₀ g₁)
        (cometricDoubleTraceCastG0 (I := I) g₀ g₁)))
    (fun x => diagonalGridGrowthFactor (E := E) i *
      ∑ n ∈ Finset.range (i + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
            ((iteratedCovGrad (I := I) g₀ 1 2 n (raisedKoszul (I := I) g₀ g₁)).toSection x)
          * ∑ l ∈ Finset.range (i + 1 - n),
              riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + l) x
                ((iteratedCovGrad (I := I) g₀ 3 1 l (cometricDoubleTraceCastG0 (I := I) g₀ g₁)).toSection x))
    (hgrid_int.const_mul (diagonalGridGrowthFactor (E := E) i))
    (fun x => riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le (I := I) (M := M) g₀
      i 3 1 2 (raisedKoszul (I := I) g₀ g₁) (cometricDoubleTraceCastG0 (I := I) g₀ g₁) x)
  refine le_trans key ?_
  rw [MeasureTheory.integral_const_mul]
  have hAnn : (0 : ℝ) ≤ diagonalGridGrowthFactor (E := E) i := appCcGdiag_nonneg (E := E) i
  have hCnn : (0 : ℝ) ≤ (exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le
      (I := I) (M := M) g₀ 1 3 2 1 i).choose :=
    (exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le
      (I := I) (M := M) g₀ 1 3 2 1 i).choose_spec.1
  calc diagonalGridGrowthFactor (E := E) i * ∫ x,
          (∑ n ∈ Finset.range (i + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
                ((iteratedCovGrad (I := I) g₀ 1 2 n (raisedKoszul (I := I) g₀ g₁)).toSection x)
              * ∑ l ∈ Finset.range (i + 1 - n),
                  riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + l) x
                    ((iteratedCovGrad (I := I) g₀ 3 1 l
                      (cometricDoubleTraceCastG0 (I := I) g₀ g₁)).toSection x))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)
      ≤ diagonalGridGrowthFactor (E := E) i *
          ((exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le
            (I := I) (M := M) g₀ 1 3 2 1 i).choose *
            (ΛB ^ 2 * ∑ n ∈ Finset.range (i + 1),
                ‖iteratedCovGrad (I := I) g₀ 1 2 n (raisedKoszul (I := I) g₀ g₁)‖ ^ 2
              + ΛA ^ 2 * ∑ l ∈ Finset.range (i + 1),
                ‖iteratedCovGrad (I := I) g₀ 3 1 l (cometricDoubleTraceCastG0 (I := I) g₀ g₁)‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hgrid_bound hAnn
    _ ≤ diagonalGridGrowthFactor (E := E) i *
          ((exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le
            (I := I) (M := M) g₀ 1 3 2 1 i).choose * (ΛB ^ 2 * FΦ i + ΛA ^ 2 * FW i)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hCnn) hAnn
        have h1 := mul_le_mul_of_nonneg_left (hΦsum i hi) (sq_nonneg ΛB)
        have h2 := mul_le_mul_of_nonneg_left (hWsum i hi) (sq_nonneg ΛA)
        linarith
    _ = diagonalGridGrowthFactor (E := E) i *
          (exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le
            (I := I) (M := M) g₀ 1 3 2 1 i).choose * (ΛB ^ 2 * FΦ i + ΛA ^ 2 * FW i) := by
        ring

end L2OutputFeeder

end DifferentialGeometry.Integral.Connection

end
