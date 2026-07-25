import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RemainderCoeffL2JetMoser
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.FlatArmCoeffConnectionDifferenceBridge
import DifferentialGeometry.Geometry.Flow.DeTurckVFConnDiffVariation
import DifferentialGeometry.Geometry.Curvature.Bochner.WeitzenbockIdentity
import Mathlib.Analysis.MeanInequalities

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open MeasureTheory Set Filter Topology Bundle Manifold Tensor0SBundle ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Integral.Connection

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.PDE.DeTurck.RicciLinearization (realizedFam)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem iteratedCovGrad_smul_real (g : SmoothRiemannianMetric I M) (r s j : ℕ) (c : ℝ)
    (w : SmoothCcTensor g r s) :
    iteratedCovGrad (I := I) g r s j (c • w) = c • iteratedCovGrad (I := I) g r s j w := by
  induction j with
  | zero => simp only [iteratedCovGrad_zero]
  | succ j ih => rw [iteratedCovGrad_succ, iteratedCovGrad_succ, ih,
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad_smul]

section RaisedKoszulSuccHelpers

lemma raisedKoszul_norm_eq_of_sq_eq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
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

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral in
theorem raisedKoszul_order0sup_jetL2_succ_generic
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
        ∀ (i : ℕ), i ≤ a + 1 →
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

end RaisedKoszulSuccHelpers

end DifferentialGeometry.Integral.Connection

end
