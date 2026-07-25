import DifferentialGeometry.Analysis.Sobolev.GagliardoNirenbergLpFiberNorm


noncomputable section

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.Analysis.Sobolev.Tensor

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩


omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [I.Boundaryless] in
private theorem real_holder_two_nonneg
    (g : SmoothRiemannianMetric I M) (φ ψ : M → ℝ)
    (hφc : Continuous φ) (hψc : Continuous ψ)
    (hφ0 : ∀ x, 0 ≤ φ x) (hψ0 : ∀ x, 0 ≤ ψ x)
    {p q : ℝ} (hpq : p.HolderConjugate q) :
    ∫ x, φ x * ψ x ∂(riemannianVolumeMeasure (I := I) (M := M) g) ≤
      (∫ x, φ x ^ p ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ^ (1 / p) *
      (∫ x, ψ x ^ q ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ^ (1 / q) := by
  set μ : Measure M := riemannianVolumeMeasure (I := I) (M := M) g with hμ
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


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem continuous_riemannianFiberNormSq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : Integral.L2.SmoothCcTensor g r s) :
    Continuous (fun x => riemannianFiberNormSq (I := I) (M := M) g r s x (S.toSection x)) := by
  have hc := Integral.L2.SmoothCcTensor.continuous_inner_self (I := I) (M := M) S
  refine hc.congr (fun x => ?_)
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (S.toSection x),
    ← Integral.L2.SmoothCcTensor.toFun_apply (I := I) (M := M) S x]


omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [I.Boundaryless] in
private theorem integrable_riemannianFiberNormSq_mul
    (g : SmoothRiemannianMetric I M) (r₁ s₁ r₂ s₂ : ℕ)
    (S : Integral.L2.SmoothCcTensor g r₁ s₁) (T : Integral.L2.SmoothCcTensor g r₂ s₂) :
    Integrable
      (fun x => riemannianFiberNormSq (I := I) (M := M) g r₁ s₁ x (S.toSection x) *
        riemannianFiberNormSq (I := I) (M := M) g r₂ s₂ x (T.toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g
  exact ((continuous_riemannianFiberNormSq g r₁ s₁ S).mul (continuous_riemannianFiberNormSq g r₂ s₂ T)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

private theorem young_arm_split
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

theorem exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_le
    (g : SmoothRiemannianMetric I M) (s₁ s₂ k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : Integral.L2.SmoothCcTensor g 0 s₁) (T : Integral.L2.SmoothCcTensor g 0 s₂)
        (ΛS ΛT : ℝ), 0 ≤ ΛS → 0 ≤ ΛT →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 s₁ x (S.toSection x) ≤ ΛS ^ 2) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 s₂ x (T.toSection x) ≤ ΛT ^ 2) →
        MeasureTheory.Integrable
            (fun x => ∑ i ∈ Finset.range (k + 1),
              riemannianFiberNormSq (I := I) (M := M) g 0 (s₁ + i) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₁ i S).toSection x)
                * ∑ l ∈ Finset.range (k + 1 - i),
                    riemannianFiberNormSq (I := I) (M := M) g 0 (s₂ + l) x
                      ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₂ l T).toSection x))
            (riemannianVolumeMeasure (I := I) (M := M) g) ∧
          (∫ x, (∑ i ∈ Finset.range (k + 1),
              riemannianFiberNormSq (I := I) (M := M) g 0 (s₁ + i) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₁ i S).toSection x)
                * ∑ l ∈ Finset.range (k + 1 - i),
                    riemannianFiberNormSq (I := I) (M := M) g 0 (s₂ + l) x
                      ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₂ l T).toSection x))
              ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤
            C * (ΛT ^ 2 * ∑ i ∈ Finset.range (k + 1),
                  ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₁ i S‖ ^ 2
                + ΛS ^ 2 * ∑ l ∈ Finset.range (k + 1),
                  ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₂ l T‖ ^ 2) := by
  classical
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g

  set CSf : ℕ → ℝ := fun m =>
    if h : 1 ≤ m then
      (exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le (I := I) (M := M) g s₁ m h).choose
    else 0 with hCSf
  set CTf : ℕ → ℝ := fun m =>
    if h : 1 ≤ m then
      (exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le (I := I) (M := M) g s₂ m h).choose
    else 0 with hCTf
  have hCSf_nn : ∀ m, 0 ≤ CSf m := by
    intro m; rw [hCSf]; dsimp only; split
    · rename_i h
      exact (exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le
        (I := I) (M := M) g s₁ m h).choose_spec.1
    · exact le_refl 0
  have hCTf_nn : ∀ m, 0 ≤ CTf m := by
    intro m; rw [hCTf]; dsimp only; split
    · rename_i h
      exact (exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le
        (I := I) (M := M) g s₂ m h).choose_spec.1
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
  set μ : Measure M := riemannianVolumeMeasure (I := I) (M := M) g with hμ

  set Sj : ℕ → M → ℝ := fun a x =>
    riemannianFiberNormSq (I := I) (M := M) g 0 (s₁ + a) x
      ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₁ a S).toSection x) with hSj
  set Tj : ℕ → M → ℝ := fun b x =>
    riemannianFiberNormSq (I := I) (M := M) g 0 (s₂ + b) x
      ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₂ b T).toSection x) with hTj

  have hSnorm : ∀ a, ∫ x, Sj a x ∂μ =
      ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₁ a S‖ ^ 2 := by
    intro a
    rw [hSj, hμ,
      ← tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g (s₁ + a)
        (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₁ a S),
      ← Integral.L2.SmoothCcTensor.norm_def (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₁ a S)]
  have hTnorm : ∀ b, ∫ x, Tj b x ∂μ =
      ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₂ b T‖ ^ 2 := by
    intro b
    rw [hTj, hμ,
      ← tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g (s₂ + b)
        (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₂ b T),
      ← Integral.L2.SmoothCcTensor.norm_def (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₂ b T)]

  have hSj_cont : ∀ a, Continuous (Sj a) := fun a => by
    rw [hSj]; exact continuous_riemannianFiberNormSq g 0 (s₁ + a) _
  have hTj_cont : ∀ b, Continuous (Tj b) := fun b => by
    rw [hTj]; exact continuous_riemannianFiberNormSq g 0 (s₂ + b) _
  have hSj_nn : ∀ a x, 0 ≤ Sj a x := fun a x => by
    rw [hSj]; exact riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s₁ + a) x _
  have hTj_nn : ∀ b x, 0 ≤ Tj b x := fun b x => by
    rw [hTj]; exact riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s₂ + b) x _
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
    rw [PDE.RicciFlow.iteratedCovGrad_zero (I := I) g 0 s₁ S]
    exact hSsup x
  have hTsup0 : ∀ x, Tj 0 x ≤ ΛT ^ 2 := by
    intro x; rw [hTj]; dsimp only
    rw [PDE.RicciFlow.iteratedCovGrad_zero (I := I) g 0 s₂ T]
    exact hTsup x

  have hAS_nn : 0 ≤ ΛT ^ 2 * ∑ a ∈ Finset.range (k + 1),
      ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₁ a S‖ ^ 2 := by positivity
  have hAT_nn : 0 ≤ ΛS ^ 2 * ∑ b ∈ Finset.range (k + 1),
      ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₂ b T‖ ^ 2 := by positivity

  have hcell : ∀ i, i ≤ k → ∀ l, i + l ≤ k →
      ∫ x, Sj i x * Tj l x ∂μ ≤ Cbig *
        ((ΛT ^ 2 * ∑ a ∈ Finset.range (k + 1),
            ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₁ a S‖ ^ 2)
          + (ΛS ^ 2 * ∑ b ∈ Finset.range (k + 1),
            ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₂ b T‖ ^ 2)) := by
    intro i hik l hilk
    have hSi_in : ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₁ i S‖ ^ 2 ≤
        ∑ a ∈ Finset.range (k + 1),
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₁ a S‖ ^ 2 :=
      Finset.single_le_sum
        (f := fun a => ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₁ a S‖ ^ 2)
        (fun a _ => sq_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hik))
    have hTl_in : ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₂ l T‖ ^ 2 ≤
        ∑ b ∈ Finset.range (k + 1),
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₂ b T‖ ^ 2 :=
      Finset.single_le_sum
        (f := fun b => ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₂ b T‖ ^ 2)
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
          ≤ ΛS ^ 2 * ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₂ l T‖ ^ 2 := hbound
        _ ≤ Cbig * (ΛS ^ 2 * ∑ b ∈ Finset.range (k + 1),
              ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₂ b T‖ ^ 2) := by
              rw [← mul_assoc, mul_comm (Cbig) (ΛS ^ 2), mul_assoc]
              exact mul_le_mul_of_nonneg_left
                (le_trans hTl_in (le_mul_of_one_le_left (Finset.sum_nonneg
                  (fun b _ => sq_nonneg _)) hCbig1)) (by positivity)
        _ ≤ Cbig * ((ΛT ^ 2 * ∑ a ∈ Finset.range (k + 1),
              ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₁ a S‖ ^ 2)
            + (ΛS ^ 2 * ∑ b ∈ Finset.range (k + 1),
              ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₂ b T‖ ^ 2)) := by
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
            ≤ ΛT ^ 2 * ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₁ i S‖ ^ 2 := hbound
          _ ≤ Cbig * (ΛT ^ 2 * ∑ a ∈ Finset.range (k + 1),
                ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₁ a S‖ ^ 2) := by
                rw [← mul_assoc, mul_comm (Cbig) (ΛT ^ 2), mul_assoc]
                exact mul_le_mul_of_nonneg_left
                  (le_trans hSi_in (le_mul_of_one_le_left (Finset.sum_nonneg
                    (fun a _ => sq_nonneg _)) hCbig1)) (by positivity)
          _ ≤ Cbig * ((ΛT ^ 2 * ∑ a ∈ Finset.range (k + 1),
                ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₁ a S‖ ^ 2)
              + (ΛS ^ 2 * ∑ b ∈ Finset.range (k + 1),
                ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₂ b T‖ ^ 2)) := by
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

        have hHolder := real_holder_two_nonneg g (Sj i) (Tj l)
          (hSj_cont i) (hTj_cont l) (hSj_nn i) (hTj_nn l) hpq
        have h1p : (1 : ℝ) / p = wi := by rw [hp, one_div_div, hwi]
        have h1q : (1 : ℝ) / q = wl := by rw [hq, one_div_div, hwl]
        rw [h1p, h1q] at hHolder

        have hSe := (exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le
          (I := I) (M := M) g s₁ m hm1).choose_spec.2 S ΛS hΛS hSsup i hipos hmi
        have hTe := (exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le
          (I := I) (M := M) g s₂ m hm1).choose_spec.2 T ΛT hΛT hTsup l hlpos hml

        have hCSf_m : (exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le
            (I := I) (M := M) g s₁ m hm1).choose = CSf m := by
          simp only [hCSf, dif_pos hm1]
        have hCTf_m : (exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le
            (I := I) (M := M) g s₂ m hm1).choose = CTf m := by
          simp only [hCTf, dif_pos hm1]
        rw [hCSf_m] at hSe
        rw [hCTf_m] at hTe

        rw [mul_div_assoc 2 (i : ℝ) m, ← hwi] at hSe
        rw [mul_div_assoc 2 (l : ℝ) m, ← hwl] at hTe

        rw [show Integral.L2.tensorL2Norm (I := I) g 0 (s₁ + m)
              (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₁ m S).toFun =
              ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₁ m S‖ from
            (Integral.L2.SmoothCcTensor.norm_def
              (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₁ m S)).symm] at hSe
        rw [show Integral.L2.tensorL2Norm (I := I) g 0 (s₂ + m)
              (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₂ m T).toFun =
              ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₂ m T‖ from
            (Integral.L2.SmoothCcTensor.norm_def
              (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₂ m T)).symm] at hTe

        set Iφp : ℝ := ∫ x, Sj i x ^ p ∂μ with hIφp
        set Iψq : ℝ := ∫ x, Tj l x ^ q ∂μ with hIψq

        have hIφp_nn : 0 ≤ Iφp := by
          rw [hIφp]; exact integral_nonneg (fun x => Real.rpow_nonneg (hSj_nn i x) _)
        have hIψq_nn : 0 ≤ Iψq := by
          rw [hIψq]; exact integral_nonneg (fun x => Real.rpow_nonneg (hTj_nn l x) _)

        have hys := young_arm_split wi wl (CSf m) (CTf m) ΛS ΛT
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₁ m S‖
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₂ m T‖
          Iφp Iψq hwi_nn hwl_nn hwsum (hCSf_nn m) (hCTf_nn m) hΛS hΛT
          (norm_nonneg _) (norm_nonneg _) hIφp_nn hIψq_nn hSe hTe

        have hNS_sum : ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₁ m S‖ ^ 2 ≤
            ∑ a ∈ Finset.range (k + 1),
              ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₁ a S‖ ^ 2 :=
          Finset.single_le_sum
            (f := fun a => ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₁ a S‖ ^ 2)
            (fun a _ => sq_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hmk))
        have hNT_sum : ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₂ m T‖ ^ 2 ≤
            ∑ b ∈ Finset.range (k + 1),
              ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₂ b T‖ ^ 2 :=
          Finset.single_le_sum
            (f := fun b => ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₂ b T‖ ^ 2)
            (fun b _ => sq_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hmk))
        have hwi_le1 : wi ≤ 1 := by rw [← hwsum]; linarith
        have hwl_le1 : wl ≤ 1 := by rw [← hwsum]; linarith
        calc ∫ x, Sj i x * Tj l x ∂μ
            ≤ Iφp ^ wi * Iψq ^ wl := hHolder
          _ ≤ CSf m * CTf m * (wi * (ΛT ^ 2 *
                ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₁ m S‖ ^ 2)
              + wl * (ΛS ^ 2 *
                ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₂ m T‖ ^ 2)) := hys
          _ ≤ Cbig * ((ΛT ^ 2 * ∑ a ∈ Finset.range (k + 1),
                ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₁ a S‖ ^ 2)
              + (ΛS ^ 2 * ∑ b ∈ Finset.range (k + 1),
                ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₂ b T‖ ^ 2)) := by
              refine le_trans (mul_le_mul_of_nonneg_right (hCSCT_le m hmk) ?_) ?_
              · have : 0 ≤ wi * (ΛT ^ 2 *
                    ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₁ m S‖ ^ 2)
                  + wl * (ΛS ^ 2 *
                    ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₂ m T‖ ^ 2) := by positivity
                exact this
              · refine mul_le_mul_of_nonneg_left ?_ hCbig_nn
                have harm1 : wi * (ΛT ^ 2 *
                    ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₁ m S‖ ^ 2) ≤
                    ΛT ^ 2 * ∑ a ∈ Finset.range (k + 1),
                      ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₁ a S‖ ^ 2 := by
                  calc wi * (ΛT ^ 2 *
                        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₁ m S‖ ^ 2)
                      ≤ 1 * (ΛT ^ 2 *
                        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₁ m S‖ ^ 2) :=
                        mul_le_mul_of_nonneg_right hwi_le1 (by positivity)
                    _ = ΛT ^ 2 *
                        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₁ m S‖ ^ 2 := one_mul _
                    _ ≤ ΛT ^ 2 * ∑ a ∈ Finset.range (k + 1),
                          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₁ a S‖ ^ 2 :=
                        mul_le_mul_of_nonneg_left hNS_sum (by positivity)
                have harm2 : wl * (ΛS ^ 2 *
                    ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₂ m T‖ ^ 2) ≤
                    ΛS ^ 2 * ∑ b ∈ Finset.range (k + 1),
                      ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₂ b T‖ ^ 2 := by
                  calc wl * (ΛS ^ 2 *
                        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₂ m T‖ ^ 2)
                      ≤ 1 * (ΛS ^ 2 *
                        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₂ m T‖ ^ 2) :=
                        mul_le_mul_of_nonneg_right hwl_le1 (by positivity)
                    _ = ΛS ^ 2 *
                        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₂ m T‖ ^ 2 := one_mul _
                    _ ≤ ΛS ^ 2 * ∑ b ∈ Finset.range (k + 1),
                          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₂ b T‖ ^ 2 :=
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
              ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₁ a S‖ ^ 2)
            + (ΛS ^ 2 * ∑ b ∈ Finset.range (k + 1),
              ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₂ b T‖ ^ 2)) := by
      refine Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun l hl => ?_))
      have hik : i ≤ k := by rw [Finset.mem_range] at hi; omega
      have hilk : i + l ≤ k := by
        rw [Finset.mem_range] at hi hl; omega
      exact hcell i hik l hilk
    refine le_trans hsum_le ?_

    set c : ℝ := Cbig * ((ΛT ^ 2 * ∑ a ∈ Finset.range (k + 1),
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₁ a S‖ ^ 2)
      + (ΛS ^ 2 * ∑ b ∈ Finset.range (k + 1),
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₂ b T‖ ^ 2)) with hc
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

theorem exists_integrated_diagonalProductGrid_twoArm_pair_le
    (g : SmoothRiemannianMetric I M) (s₁ s₂ k j : ℕ) :
    ∃ Cd : ℝ, 0 ≤ Cd ∧
      ∀ (U W : Integral.L2.SmoothCcTensor g 0 s₁)
        (T₁ T₂ : Integral.L2.SmoothCcTensor g 0 s₂) (Cmid ΛW ΛT : ℝ),
        0 ≤ Cmid → 0 ≤ ΛW → 0 ≤ ΛT →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 s₁ x (W.toSection x) ≤ ΛW ^ 2) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 s₂ x (T₁.toSection x) ≤ ΛT ^ 2) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 s₂ x (T₂.toSection x) ≤ ΛT ^ 2) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 (s₁ + j) x
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₁ j U).toSection x) ≤
            Cmid * ∑ i ∈ Finset.range (k + 1),
              riemannianFiberNormSq (I := I) (M := M) g 0 (s₁ + i) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₁ i W).toSection x)
                * ∑ l ∈ Finset.range (k + 1 - i),
                    (riemannianFiberNormSq (I := I) (M := M) g 0 (s₂ + l) x
                        ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₂ l T₁).toSection x)
                      + riemannianFiberNormSq (I := I) (M := M) g 0 (s₂ + l) x
                        ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₂ l T₂).toSection x))) →
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₁ j U‖ ^ 2 ≤
            Cd * Cmid * ΛT ^ 2 * ∑ i ∈ Finset.range (k + 1),
                ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₁ i W‖ ^ 2
          + Cd * Cmid * ΛW ^ 2 * ∑ l ∈ Finset.range (k + 1),
                (‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₂ l T₁‖ ^ 2
                  + ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₂ l T₂‖ ^ 2) := by
  classical
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g
  set μ : Measure M := riemannianVolumeMeasure (I := I) (M := M) g with hμ

  obtain ⟨C, hC0, hsym⟩ :=
    exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_le (I := I) (M := M) g s₁ s₂ k
  refine ⟨2 * C, by positivity, ?_⟩
  intro U W T₁ T₂ Cmid ΛW ΛT hCmid hΛW hΛT hWsup hT₁sup hT₂sup hgrid

  set Wj : ℕ → M → ℝ := fun a x =>
    riemannianFiberNormSq (I := I) (M := M) g 0 (s₁ + a) x
      ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₁ a W).toSection x) with hWj
  set T1j : ℕ → M → ℝ := fun b x =>
    riemannianFiberNormSq (I := I) (M := M) g 0 (s₂ + b) x
      ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₂ b T₁).toSection x) with hT1j
  set T2j : ℕ → M → ℝ := fun b x =>
    riemannianFiberNormSq (I := I) (M := M) g 0 (s₂ + b) x
      ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₂ b T₂).toSection x) with hT2j

  have hWj_cont : ∀ a, Continuous (Wj a) := fun a => by
    rw [hWj]; exact continuous_riemannianFiberNormSq g 0 (s₁ + a) _
  have hT1j_cont : ∀ b, Continuous (T1j b) := fun b => by
    rw [hT1j]; exact continuous_riemannianFiberNormSq g 0 (s₂ + b) _
  have hT2j_cont : ∀ b, Continuous (T2j b) := fun b => by
    rw [hT2j]; exact continuous_riemannianFiberNormSq g 0 (s₂ + b) _
  have hWj_nn : ∀ a x, 0 ≤ Wj a x := fun a x => by
    rw [hWj]; exact riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s₁ + a) x _
  have hT1j_nn : ∀ b x, 0 ≤ T1j b x := fun b x => by
    rw [hT1j]; exact riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s₂ + b) x _
  have hT2j_nn : ∀ b x, 0 ≤ T2j b x := fun b x => by
    rw [hT2j]; exact riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s₂ + b) x _

  set grid : (ℕ → M → ℝ) → M → ℝ := fun Tj x =>
    ∑ i ∈ Finset.range (k + 1), Wj i x * ∑ l ∈ Finset.range (k + 1 - i), Tj l x with hgridDef
  have hgrid_cont : ∀ Tj : ℕ → M → ℝ, (∀ b, Continuous (Tj b)) → Continuous (grid Tj) := by
    intro Tj hTj; rw [hgridDef]
    exact continuous_finset_sum _ (fun i _ => (hWj_cont i).mul
      (continuous_finset_sum _ (fun l _ => hTj l)))
  have hgrid_int : ∀ Tj : ℕ → M → ℝ, (∀ b, Continuous (Tj b)) → Integrable (grid Tj) μ := by
    intro Tj hTj; rw [hμ]
    exact (hgrid_cont Tj hTj).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

  have hUbridge : ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₁ j U‖ ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 (s₁ + j) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₁ j U).toSection x) ∂μ := by
    rw [hμ, Integral.L2.SmoothCcTensor.norm_def
        (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₁ j U),
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g (s₁ + j)
        (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₁ j U)]

  have hgrid_split : ∀ x,
      (∑ i ∈ Finset.range (k + 1), Wj i x *
          ∑ l ∈ Finset.range (k + 1 - i), (T1j l x + T2j l x)) = grid T1j x + grid T2j x := by
    intro x; rw [hgridDef]; dsimp only
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_add_distrib, mul_add]

  have hUgrid_int : Integrable
      (fun x => riemannianFiberNormSq (I := I) (M := M) g 0 (s₁ + j) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₁ j U).toSection x)) μ := by
    rw [hμ]
    exact (continuous_riemannianFiberNormSq g 0 (s₁ + j) _).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

  have hintU_le : ∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 (s₁ + j) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₁ j U).toSection x) ∂μ ≤
      Cmid * ((∫ x, grid T1j x ∂μ) + ∫ x, grid T2j x ∂μ) := by
    have hstep : ∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 (s₁ + j) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₁ j U).toSection x) ∂μ ≤
        ∫ x, Cmid * (grid T1j x + grid T2j x) ∂μ := by
      refine integral_mono_of_nonneg (Eventually.of_forall (fun x => ?_))
        (((hgrid_int T1j hT1j_cont).add (hgrid_int T2j hT2j_cont)).const_mul _)
        (Eventually.of_forall (fun x => ?_))
      · exact riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s₁ + j) x _
      · change riemannianFiberNormSq (I := I) (M := M) g 0 (s₁ + j) x
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₁ j U).toSection x) ≤
            Cmid * (grid T1j x + grid T2j x)
        rw [← hgrid_split x]; exact hgrid x
    refine le_trans hstep (le_of_eq ?_)
    rw [integral_const_mul, integral_add (hgrid_int T1j hT1j_cont) (hgrid_int T2j hT2j_cont)]

  have harm : ∀ (T : Integral.L2.SmoothCcTensor g 0 s₂) (Tj : ℕ → M → ℝ),
      (Tj = fun b x => riemannianFiberNormSq (I := I) (M := M) g 0 (s₂ + b) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₂ b T).toSection x)) →
      (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 s₂ x (T.toSection x) ≤ ΛT ^ 2) →
      ∫ x, grid Tj x ∂μ ≤
        C * (ΛT ^ 2 * ∑ i ∈ Finset.range (k + 1),
              ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₁ i W‖ ^ 2
            + ΛW ^ 2 * ∑ l ∈ Finset.range (k + 1),
              ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₂ l T‖ ^ 2) := by
    intro T Tj hTjdef hTsup
    have he := hsym W T ΛW ΛT hΛW hΛT hWsup hTsup

    have hgrideq : ∫ x, grid Tj x ∂μ =
        ∫ x, ∑ i ∈ Finset.range (k + 1),
            riemannianFiberNormSq (I := I) (M := M) g 0 (s₁ + i) x
                ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₁ i W).toSection x)
              * ∑ l ∈ Finset.range (k + 1 - i),
                  riemannianFiberNormSq (I := I) (M := M) g 0 (s₂ + l) x
                    ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₂ l T).toSection x) ∂μ := by
      refine integral_congr_ae (Eventually.of_forall (fun x => ?_))
      rw [hgridDef]; dsimp only; rw [hWj, hTjdef]
    rw [hgrideq]

    exact he.2
  have harm1 := harm T₁ T1j hT1j hT₁sup
  have harm2 := harm T₂ T2j hT2j hT₂sup

  rw [hUbridge]
  refine le_trans hintU_le ?_
  have hWsum_nn : (0 : ℝ) ≤ ∑ i ∈ Finset.range (k + 1),
      ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₁ i W‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hT1sum_nn : (0 : ℝ) ≤ ∑ l ∈ Finset.range (k + 1),
      ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₂ l T₁‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hT2sum_nn : (0 : ℝ) ≤ ∑ l ∈ Finset.range (k + 1),
      ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₂ l T₂‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  calc Cmid * ((∫ x, grid T1j x ∂μ) + ∫ x, grid T2j x ∂μ)
      ≤ Cmid * ((C * (ΛT ^ 2 * ∑ i ∈ Finset.range (k + 1),
              ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₁ i W‖ ^ 2
            + ΛW ^ 2 * ∑ l ∈ Finset.range (k + 1),
              ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₂ l T₁‖ ^ 2))
          + (C * (ΛT ^ 2 * ∑ i ∈ Finset.range (k + 1),
              ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₁ i W‖ ^ 2
            + ΛW ^ 2 * ∑ l ∈ Finset.range (k + 1),
              ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₂ l T₂‖ ^ 2))) :=
        mul_le_mul_of_nonneg_left (add_le_add harm1 harm2) hCmid
    _ = Cmid * (C * (2 * (ΛT ^ 2 * ∑ i ∈ Finset.range (k + 1),
              ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₁ i W‖ ^ 2)
            + ΛW ^ 2 * ∑ l ∈ Finset.range (k + 1),
              (‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₂ l T₁‖ ^ 2
                + ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₂ l T₂‖ ^ 2))) := by
        rw [Finset.sum_add_distrib]; ring
    _ = (2 * C * Cmid * ΛT ^ 2 * ∑ i ∈ Finset.range (k + 1),
              ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₁ i W‖ ^ 2
          + 2 * C * Cmid * ΛW ^ 2 * ∑ l ∈ Finset.range (k + 1),
              (‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₂ l T₁‖ ^ 2
                + ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₂ l T₂‖ ^ 2))
        - C * Cmid * ΛW ^ 2 * ∑ l ∈ Finset.range (k + 1),
              (‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₂ l T₁‖ ^ 2
                + ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₂ l T₂‖ ^ 2) := by ring
    _ ≤ 2 * C * Cmid * ΛT ^ 2 * ∑ i ∈ Finset.range (k + 1),
              ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₁ i W‖ ^ 2
          + 2 * C * Cmid * ΛW ^ 2 * ∑ l ∈ Finset.range (k + 1),
              (‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₂ l T₁‖ ^ 2
                + ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₂ l T₂‖ ^ 2) := by
        have hcross_extra : 0 ≤ C * Cmid * ΛW ^ 2 * ∑ l ∈ Finset.range (k + 1),
            (‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₂ l T₁‖ ^ 2
              + ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₂ l T₂‖ ^ 2) := by
          have : 0 ≤ ∑ l ∈ Finset.range (k + 1),
              (‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₂ l T₁‖ ^ 2
                + ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₂ l T₂‖ ^ 2) :=
            Finset.sum_nonneg (fun _ _ => by positivity)
          positivity
        linarith

private theorem young_arm_split_scaled
    (wi wl CS CT ΛS ΛT NS NT Iφp Iψq t : ℝ) (k : ℕ)
    (hwi_pos : 0 < wi) (hwl_pos : 0 < wl) (hwsum : wi + wl = 1) (hwk : wi / wl ≤ (k : ℝ))
    (hCS : 0 ≤ CS) (hCT : 0 ≤ CT) (hΛS : 0 ≤ ΛS) (hΛT : 0 ≤ ΛT)
    (hNS : 0 ≤ NS) (hNT : 0 ≤ NT) (_hIφp : 0 ≤ Iφp) (hIψq : 0 ≤ Iψq)
    (ht0 : 0 < t) (ht1 : t ≤ 1)
    (hS : Iφp ^ wi ≤ CS * ΛS ^ (2 * (1 - wi)) * NS ^ (2 * wi))
    (hT : Iψq ^ wl ≤ CT * ΛT ^ (2 * (1 - wl)) * NT ^ (2 * wl)) :
    Iφp ^ wi * Iψq ^ wl ≤
      CS * CT * (t * (ΛT ^ 2 * NS ^ 2) + (1 / t) ^ k * (ΛS ^ 2 * NT ^ 2)) := by
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
  set X : ℝ := ΛT ^ 2 * NS ^ 2 with hX
  set Y : ℝ := ΛS ^ 2 * NT ^ 2 with hY
  have hX_nn : 0 ≤ X := by rw [hX]; positivity
  have hY_nn : 0 ≤ Y := by rw [hY]; positivity
  have hs_pos : (0 : ℝ) < t ^ (-(wi / wl)) := Real.rpow_pos_of_pos ht0 _

  have hpow : (t * X) ^ wi * (t ^ (-(wi / wl)) * Y) ^ wl = X ^ wi * Y ^ wl := by
    rw [Real.mul_rpow ht0.le hX_nn, Real.mul_rpow hs_pos.le hY_nn,
      ← Real.rpow_mul ht0.le (-(wi / wl)) wl]
    rw [show (-(wi / wl)) * wl = -wi from by field_simp]
    rw [show t ^ wi * X ^ wi * (t ^ (-wi) * Y ^ wl) =
      (t ^ wi * t ^ (-wi)) * (X ^ wi * Y ^ wl) from by ring, ← Real.rpow_add ht0,
      add_neg_cancel, Real.rpow_zero, one_mul]
  have hgm := Real.geom_mean_le_arith_mean2_weighted hwi_pos.le hwl_pos.le
    (mul_nonneg ht0.le hX_nn) (mul_nonneg hs_pos.le hY_nn) hwsum
  rw [hpow] at hgm

  have hwi1 : wi ≤ 1 := by linarith
  have hwl1 : wl ≤ 1 := by linarith
  have hsk : t ^ (-(wi / wl)) ≤ (1 / t) ^ k := by
    have h1t : (1 : ℝ) ≤ 1 / t := by rw [le_div_iff₀ ht0]; linarith
    have heq : t ^ (-(wi / wl)) = (1 / t) ^ (wi / wl) := by
      rw [Real.rpow_neg ht0.le, one_div, Real.inv_rpow ht0.le]
    rw [heq, ← Real.rpow_natCast (1 / t) k]
    exact Real.rpow_le_rpow_of_exponent_le h1t hwk
  have hXY : X ^ wi * Y ^ wl ≤ t * X + (1 / t) ^ k * Y := by
    have h1 : wi * (t * X) ≤ t * X := by nlinarith [mul_nonneg ht0.le hX_nn]
    have h2 : wl * (t ^ (-(wi / wl)) * Y) ≤ (1 / t) ^ k * Y := by
      have h2a : wl * (t ^ (-(wi / wl)) * Y) ≤ t ^ (-(wi / wl)) * Y := by
        nlinarith [mul_nonneg hs_pos.le hY_nn]
      exact h2a.trans (mul_le_mul_of_nonneg_right hsk hY_nn)
    linarith [hgm]
  calc Iφp ^ wi * Iψq ^ wl
      ≤ CS * CT * (X ^ wi * Y ^ wl) := hprod
    _ ≤ CS * CT * (t * X + (1 / t) ^ k * Y) :=
        mul_le_mul_of_nonneg_left hXY (by positivity)

theorem exists_integrated_iteratedCovGrad_antiDiagGrid_topArm_scaled_le
    (g : SmoothRiemannianMetric I M) (s₁ s₂ k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : Integral.L2.SmoothCcTensor g 0 s₁) (T : Integral.L2.SmoothCcTensor g 0 s₂)
        (ΛS ΛT : ℝ), 0 ≤ ΛS → 0 ≤ ΛT →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 s₁ x (S.toSection x) ≤ ΛS ^ 2) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 s₂ x (T.toSection x) ≤ ΛT ^ 2) →
        ∀ t : ℝ, 0 < t → t ≤ 1 →
        MeasureTheory.Integrable
            (fun x => ∑ i ∈ Finset.range k,
              riemannianFiberNormSq (I := I) (M := M) g 0 (s₁ + i) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₁ i S).toSection x)
                * riemannianFiberNormSq (I := I) (M := M) g 0 (s₂ + (k - i)) x
                    ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₂ (k - i) T).toSection x))
            (riemannianVolumeMeasure (I := I) (M := M) g) ∧
          (∫ x, (∑ i ∈ Finset.range k,
              riemannianFiberNormSq (I := I) (M := M) g 0 (s₁ + i) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₁ i S).toSection x)
                * riemannianFiberNormSq (I := I) (M := M) g 0 (s₂ + (k - i)) x
                    ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₂ (k - i) T).toSection x))
              ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤
            t * (ΛT ^ 2 * ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₁ k S‖ ^ 2)
              + C * (1 / t) ^ k *
                (ΛS ^ 2 * ∑ l ∈ Finset.range (k + 1),
                  ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₂ l T‖ ^ 2) := by
  classical
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g

  set CS : ℝ :=
    if h : 1 ≤ k then
      (exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le (I := I) (M := M) g s₁ k h).choose
    else 0 with hCSdef
  set CT : ℝ :=
    if h : 1 ≤ k then
      (exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le (I := I) (M := M) g s₂ k h).choose
    else 0 with hCTdef
  have hCS_nn : 0 ≤ CS := by
    rw [hCSdef]; split
    · rename_i h
      exact (exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le
        (I := I) (M := M) g s₁ k h).choose_spec.1
    · exact le_refl 0
  have hCT_nn : 0 ≤ CT := by
    rw [hCTdef]; split
    · rename_i h
      exact (exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le
        (I := I) (M := M) g s₂ k h).choose_spec.1
    · exact le_refl 0
  set Cbig : ℝ := 1 + CS * CT with hCbig
  have hCbig1 : (1 : ℝ) ≤ Cbig := by
    rw [hCbig]; nlinarith [mul_nonneg hCS_nn hCT_nn]
  have hCbig_nn : (0 : ℝ) ≤ Cbig := le_trans zero_le_one hCbig1
  have hkC1 : (1 : ℝ) ≤ (k : ℝ) * Cbig + 1 := by
    have : (0 : ℝ) ≤ (k : ℝ) * Cbig := by positivity
    linarith
  refine ⟨(k : ℝ) * Cbig * ((k : ℝ) * Cbig + 1) ^ k + 1, by positivity, ?_⟩
  intro S T ΛS ΛT hΛS hΛT hSsup hTsup t ht0 ht1
  set μ : Measure M := riemannianVolumeMeasure (I := I) (M := M) g with hμ
  set Sj : ℕ → M → ℝ := fun a x =>
    riemannianFiberNormSq (I := I) (M := M) g 0 (s₁ + a) x
      ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₁ a S).toSection x) with hSj
  set Tj : ℕ → M → ℝ := fun b x =>
    riemannianFiberNormSq (I := I) (M := M) g 0 (s₂ + b) x
      ((PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₂ b T).toSection x) with hTj
  have hTnorm : ∀ b, ∫ x, Tj b x ∂μ =
      ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₂ b T‖ ^ 2 := by
    intro b
    rw [hTj, hμ,
      ← tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g (s₂ + b)
        (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₂ b T),
      ← Integral.L2.SmoothCcTensor.norm_def (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₂ b T)]
  have hSj_cont : ∀ a, Continuous (Sj a) := fun a => by
    rw [hSj]; exact continuous_riemannianFiberNormSq g 0 (s₁ + a) _
  have hTj_cont : ∀ b, Continuous (Tj b) := fun b => by
    rw [hTj]; exact continuous_riemannianFiberNormSq g 0 (s₂ + b) _
  have hSj_nn : ∀ a x, 0 ≤ Sj a x := fun a x => by
    rw [hSj]; exact riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s₁ + a) x _
  have hTj_nn : ∀ b x, 0 ≤ Tj b x := fun b x => by
    rw [hTj]; exact riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s₂ + b) x _
  have hTj_int : ∀ b, Integrable (Tj b) μ := fun b => by
    rw [hμ]; exact (hTj_cont b).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hint_cell : ∀ a b, Integrable (fun x => Sj a x * Tj b x) μ := fun a b => by
    rw [hμ]
    exact ((hSj_cont a).mul (hTj_cont b)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hSsup0 : ∀ x, Sj 0 x ≤ ΛS ^ 2 := by
    intro x; rw [hSj]; dsimp only
    rw [PDE.RicciFlow.iteratedCovGrad_zero (I := I) g 0 s₁ S]
    exact hSsup x
  have hTsup0 : ∀ x, Tj 0 x ≤ ΛT ^ 2 := by
    intro x; rw [hTj]; dsimp only
    rw [PDE.RicciFlow.iteratedCovGrad_zero (I := I) g 0 s₂ T]
    exact hTsup x
  set NS : ℝ := ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₁ k S‖ with hNSdef
  set NT : ℝ := ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₂ k T‖ with hNTdef
  have hNT_sum : NT ^ 2 ≤ ∑ l ∈ Finset.range (k + 1),
      ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₂ l T‖ ^ 2 := by
    rw [hNTdef]
    exact Finset.single_le_sum
      (f := fun b => ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₂ b T‖ ^ 2)
      (fun b _ => sq_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le le_rfl))

  set tt : ℝ := t / ((k : ℝ) * Cbig + 1) with htt
  have htt0 : 0 < tt := by rw [htt]; positivity
  have htt1 : tt ≤ 1 := by
    rw [htt, div_le_one (by linarith)]
    linarith
  have htt_le_t : tt ≤ t := by
    rw [htt, div_le_iff₀ (by linarith)]
    nlinarith [ht0.le]

  have hcell : ∀ i, i < k →
      ∫ x, Sj i x * Tj (k - i) x ∂μ ≤
        Cbig * tt * (ΛT ^ 2 * NS ^ 2) + Cbig * (1 / tt) ^ k * (ΛS ^ 2 * NT ^ 2) := by
    intro i hik
    have hk1 : 1 ≤ k := by omega
    have h1tt : (1 : ℝ) ≤ 1 / tt := by rw [le_div_iff₀ htt0]; linarith
    have h1ttk : (1 : ℝ) ≤ (1 / tt) ^ k := one_le_pow₀ h1tt
    rcases Nat.eq_zero_or_pos i with hi0 | hipos
    · subst hi0
      have hbound : ∫ x, Sj 0 x * Tj (k - 0) x ∂μ ≤ ΛS ^ 2 * ∫ x, Tj (k - 0) x ∂μ := by
        rw [← integral_const_mul]
        refine integral_mono_of_nonneg (Eventually.of_forall (fun x => ?_)) ?_
          (Eventually.of_forall (fun x => ?_))
        · exact mul_nonneg (hSj_nn 0 x) (hTj_nn (k - 0) x)
        · exact (hTj_int (k - 0)).const_mul _
        · exact mul_le_mul_of_nonneg_right (hSsup0 x) (hTj_nn (k - 0) x)
      rw [hTnorm (k - 0)] at hbound
      have hNT0 : ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₂ (k - 0) T‖ ^ 2 = NT ^ 2 := by
        rw [hNTdef, Nat.sub_zero]
      rw [hNT0] at hbound
      have harm : ΛS ^ 2 * NT ^ 2 ≤ Cbig * (1 / tt) ^ k * (ΛS ^ 2 * NT ^ 2) := by
        have h1 : (1 : ℝ) ≤ Cbig * (1 / tt) ^ k := by nlinarith
        nlinarith [mul_nonneg (sq_nonneg ΛS) (sq_nonneg NT)]
      have htop_nn : 0 ≤ Cbig * tt * (ΛT ^ 2 * NS ^ 2) := by positivity
      linarith [hbound, harm]
    · have hl_pos : 0 < k - i := by omega
      set l : ℕ := k - i with hl
      have hil : i + l = k := by omega
      have hmi : i < k := hik
      have hml : l < k := by omega
      have hk_posR : 0 < (k : ℝ) := by positivity
      set wi : ℝ := (i : ℝ) / k with hwi
      set wl : ℝ := (l : ℝ) / k with hwl
      have hi_posR : 0 < (i : ℝ) := by exact_mod_cast hipos
      have hl_posR : 0 < (l : ℝ) := by exact_mod_cast hl_pos
      have hwi_pos : 0 < wi := by rw [hwi]; positivity
      have hwl_pos : 0 < wl := by rw [hwl]; positivity
      have hwsum : wi + wl = 1 := by
        rw [hwi, hwl, ← add_div, show (i : ℝ) + l = (k : ℝ) by push_cast [← hil]; ring]
        exact div_self (ne_of_gt hk_posR)
      have hwk : wi / wl ≤ (k : ℝ) := by
        have hwiwl : wi / wl = (i : ℝ) / l := by
          rw [hwi, hwl]
          field_simp
        rw [hwiwl, div_le_iff₀ hl_posR]
        have h1l : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl_pos
        have hik' : (i : ℝ) ≤ (k : ℝ) := le_of_lt (by exact_mod_cast hik)
        nlinarith
      set p : ℝ := (k : ℝ) / i with hp
      set q : ℝ := (k : ℝ) / l with hq
      have hp_one : 1 < p := by rw [hp, lt_div_iff₀ hi_posR, one_mul]; exact_mod_cast hmi
      have hpq : p.HolderConjugate q := by
        rw [Real.holderConjugate_iff]
        refine ⟨hp_one, ?_⟩
        rw [hp, hq, inv_div, inv_div, ← add_div,
          show (i : ℝ) + l = (k : ℝ) by push_cast [← hil]; ring]
        exact div_self (ne_of_gt hk_posR)
      have hHolder := real_holder_two_nonneg g (Sj i) (Tj l)
        (hSj_cont i) (hTj_cont l) (hSj_nn i) (hTj_nn l) hpq
      have h1p : (1 : ℝ) / p = wi := by rw [hp, one_div_div, hwi]
      have h1q : (1 : ℝ) / q = wl := by rw [hq, one_div_div, hwl]
      rw [h1p, h1q] at hHolder
      have hSe := (exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le
        (I := I) (M := M) g s₁ k hk1).choose_spec.2 S ΛS hΛS hSsup i hipos hmi
      have hTe := (exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le
        (I := I) (M := M) g s₂ k hk1).choose_spec.2 T ΛT hΛT hTsup l hl_pos hml
      have hCS_m : (exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le
          (I := I) (M := M) g s₁ k hk1).choose = CS := by
        simp only [hCSdef, dif_pos hk1]
      have hCT_m : (exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le
          (I := I) (M := M) g s₂ k hk1).choose = CT := by
        simp only [hCTdef, dif_pos hk1]
      rw [hCS_m] at hSe
      rw [hCT_m] at hTe
      rw [mul_div_assoc 2 (i : ℝ) k, ← hwi] at hSe
      rw [mul_div_assoc 2 (l : ℝ) k, ← hwl] at hTe
      rw [show Integral.L2.tensorL2Norm (I := I) g 0 (s₁ + k)
            (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₁ k S).toFun = NS from by
          rw [hNSdef]
          exact (Integral.L2.SmoothCcTensor.norm_def
            (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₁ k S)).symm] at hSe
      rw [show Integral.L2.tensorL2Norm (I := I) g 0 (s₂ + k)
            (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₂ k T).toFun = NT from by
          rw [hNTdef]
          exact (Integral.L2.SmoothCcTensor.norm_def
            (PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₂ k T)).symm] at hTe
      set Iφp : ℝ := ∫ x, Sj i x ^ p ∂μ with hIφp
      set Iψq : ℝ := ∫ x, Tj l x ^ q ∂μ with hIψq
      have hIφp_nn : 0 ≤ Iφp := by
        rw [hIφp]; exact integral_nonneg (fun x => Real.rpow_nonneg (hSj_nn i x) _)
      have hIψq_nn : 0 ≤ Iψq := by
        rw [hIψq]; exact integral_nonneg (fun x => Real.rpow_nonneg (hTj_nn l x) _)
      have hys := young_arm_split_scaled wi wl CS CT ΛS ΛT NS NT Iφp Iψq tt k
        hwi_pos hwl_pos hwsum hwk hCS_nn hCT_nn hΛS hΛT
        (by rw [hNSdef]; exact norm_nonneg _) (by rw [hNTdef]; exact norm_nonneg _)
        hIφp_nn hIψq_nn htt0 htt1 hSe hTe
      have hCSCT_le : CS * CT ≤ Cbig := by rw [hCbig]; linarith
      calc ∫ x, Sj i x * Tj l x ∂μ
          ≤ Iφp ^ wi * Iψq ^ wl := hHolder
        _ ≤ CS * CT * (tt * (ΛT ^ 2 * NS ^ 2) + (1 / tt) ^ k * (ΛS ^ 2 * NT ^ 2)) := hys
        _ ≤ Cbig * (tt * (ΛT ^ 2 * NS ^ 2) + (1 / tt) ^ k * (ΛS ^ 2 * NT ^ 2)) := by
            refine mul_le_mul_of_nonneg_right hCSCT_le ?_
            positivity
        _ = Cbig * tt * (ΛT ^ 2 * NS ^ 2) + Cbig * (1 / tt) ^ k * (ΛS ^ 2 * NT ^ 2) := by
            ring

  refine ⟨?_, ?_⟩
  · have hcont : Continuous (fun x => ∑ i ∈ Finset.range k, Sj i x * Tj (k - i) x) := by
      refine continuous_finset_sum _ (fun i _ => (hSj_cont i).mul (hTj_cont (k - i)))
    rw [hμ]
    exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · have hrw : (∫ x, ∑ i ∈ Finset.range k, Sj i x * Tj (k - i) x ∂μ)
        = ∑ i ∈ Finset.range k, ∫ x, Sj i x * Tj (k - i) x ∂μ :=
      MeasureTheory.integral_finset_sum _ (fun i _ => hint_cell i (k - i))
    rw [hrw]
    have hsum_le : (∑ i ∈ Finset.range k, ∫ x, Sj i x * Tj (k - i) x ∂μ) ≤
        ∑ _i ∈ Finset.range k,
          (Cbig * tt * (ΛT ^ 2 * NS ^ 2) + Cbig * (1 / tt) ^ k * (ΛS ^ 2 * NT ^ 2)) :=
      Finset.sum_le_sum (fun i hi => hcell i (Finset.mem_range.mp hi))
    refine le_trans hsum_le ?_
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_range]

    have htop : (k : ℝ) * (Cbig * tt) ≤ t := by
      rw [htt]
      rw [show (k : ℝ) * (Cbig * (t / ((k : ℝ) * Cbig + 1)))
          = ((k : ℝ) * Cbig * t) / ((k : ℝ) * Cbig + 1) from by ring]
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < (k : ℝ) * Cbig + 1)]
      nlinarith [ht0.le,
        mul_nonneg (mul_nonneg (Nat.cast_nonneg k : (0:ℝ) ≤ (k:ℝ)) hCbig_nn) ht0.le]
    have hinv_tt : (1 / tt) ^ k = ((k : ℝ) * Cbig + 1) ^ k * (1 / t) ^ k := by
      rw [htt, one_div_div,
        show ((k : ℝ) * Cbig + 1) / t = ((k : ℝ) * Cbig + 1) * (1 / t) from by ring,
        mul_pow]
    have hlow : (k : ℝ) * (Cbig * (1 / tt) ^ k) ≤
        ((k : ℝ) * Cbig * ((k : ℝ) * Cbig + 1) ^ k + 1) * (1 / t) ^ k := by
      rw [hinv_tt]
      have h1tk : (0 : ℝ) ≤ (1 / t) ^ k := by positivity
      have hbase : (0 : ℝ) ≤ ((k : ℝ) * Cbig + 1) ^ k := by positivity
      nlinarith [mul_nonneg (Nat.cast_nonneg k : (0:ℝ) ≤ (k:ℝ)) hCbig_nn]
    have hXnn : (0 : ℝ) ≤ ΛT ^ 2 * NS ^ 2 := by positivity
    have hYnn : (0 : ℝ) ≤ ΛS ^ 2 * NT ^ 2 := by positivity
    have hYsum : ΛS ^ 2 * NT ^ 2 ≤ ΛS ^ 2 * ∑ l ∈ Finset.range (k + 1),
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₂ l T‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hNT_sum (by positivity)
    have hCfin_nn : (0 : ℝ) ≤ ((k : ℝ) * Cbig * ((k : ℝ) * Cbig + 1) ^ k + 1) * (1 / t) ^ k := by
      positivity
    calc (k : ℝ) * (Cbig * tt * (ΛT ^ 2 * NS ^ 2) + Cbig * (1 / tt) ^ k * (ΛS ^ 2 * NT ^ 2))
        = ((k : ℝ) * (Cbig * tt)) * (ΛT ^ 2 * NS ^ 2)
            + ((k : ℝ) * (Cbig * (1 / tt) ^ k)) * (ΛS ^ 2 * NT ^ 2) := by ring
      _ ≤ t * (ΛT ^ 2 * NS ^ 2)
            + (((k : ℝ) * Cbig * ((k : ℝ) * Cbig + 1) ^ k + 1) * (1 / t) ^ k)
              * (ΛS ^ 2 * NT ^ 2) := by
          refine add_le_add (mul_le_mul_of_nonneg_right htop hXnn)
            (mul_le_mul_of_nonneg_right hlow hYnn)
      _ ≤ t * (ΛT ^ 2 * NS ^ 2)
            + (((k : ℝ) * Cbig * ((k : ℝ) * Cbig + 1) ^ k + 1) * (1 / t) ^ k)
              * (ΛS ^ 2 * ∑ l ∈ Finset.range (k + 1),
                  ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₂ l T‖ ^ 2) := by
          exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hYsum hCfin_nn)
      _ = t * (ΛT ^ 2 * NS ^ 2)
            + ((k : ℝ) * Cbig * ((k : ℝ) * Cbig + 1) ^ k + 1) * (1 / t) ^ k *
              (ΛS ^ 2 * ∑ l ∈ Finset.range (k + 1),
                ‖PDE.RicciFlow.iteratedCovGrad (I := I) g 0 s₂ l T‖ ^ 2) := by ring

end DifferentialGeometry.Analysis.Sobolev.Tensor

end
