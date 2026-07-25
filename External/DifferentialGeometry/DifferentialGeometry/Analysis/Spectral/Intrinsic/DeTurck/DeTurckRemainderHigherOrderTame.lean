import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderDefs
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldFibreNormJet
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradLinear
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.HomFieldActionIteratedCovGradWindow
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.PointwiseToL2Packaging
import DifferentialGeometry.Analysis.Sobolev.GagliardoNirenbergLpFiberNorm
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingManifoldC0
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingCmOrderDropping
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingReverseHebeyToHs
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.SingleSlotOperatorFiberNormBound


noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Tensor0SBundle ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem mixed_continuous_rfns
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : Integral.L2.SmoothCcTensor g r s) :
    Continuous (fun x => riemannianFiberNormSq (I := I) (M := M) g r s x (S.toSection x)) := by
  have hc := Integral.L2.SmoothCcTensor.continuous_inner_self (I := I) (M := M) S
  refine hc.congr (fun x => ?_)
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (S.toSection x),
    ← Integral.L2.SmoothCcTensor.toFun_apply (I := I) (M := M) S x]


omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] in
private theorem mixed_real_holder_two_nonneg
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


private theorem mixed_young_arm_split
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

open DifferentialGeometry.Analysis.Sobolev.Tensor in

private theorem appCc_integrated_grid_twoArm_mixed
    (g : SmoothRiemannianMetric I M) (r s₁ s₂ k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : Integral.L2.SmoothCcTensor g r s₁) (T : Integral.L2.SmoothCcTensor g 0 s₂)
        (ΛS ΛT : ℝ), 0 ≤ ΛS → 0 ≤ ΛT →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g r s₁ x (S.toSection x) ≤ ΛS ^ 2) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 s₂ x (T.toSection x) ≤ ΛT ^ 2) →
        (∫ x, (∑ i ∈ Finset.range (k + 1),
            riemannianFiberNormSq (I := I) (M := M) g r (s₁ + i) x
                ((iteratedCovGrad (I := I) g r s₁ i S).toSection x)
              * ∑ l ∈ Finset.range (k + 1 - i),
                  riemannianFiberNormSq (I := I) (M := M) g 0 (s₂ + l) x
                    ((iteratedCovGrad (I := I) g 0 s₂ l T).toSection x))
            ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤
          C * (ΛT ^ 2 * ∑ i ∈ Finset.range (k + 1),
                ‖iteratedCovGrad (I := I) g r s₁ i S‖ ^ 2
              + ΛS ^ 2 * ∑ l ∈ Finset.range (k + 1),
                ‖iteratedCovGrad (I := I) g 0 s₂ l T‖ ^ 2) := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g
  set CSf : ℕ → ℝ := fun m =>
    if h : 1 ≤ m then
      (exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs (I := I) (M := M) g r s₁ m h).choose
    else 0 with hCSf
  set CTf : ℕ → ℝ := fun m =>
    if h : 1 ≤ m then
      (exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs (I := I) (M := M) g 0 s₂ m h).choose
    else 0 with hCTf
  have hCSf_nn : ∀ m, 0 ≤ CSf m := by
    intro m; rw [hCSf]; dsimp only; split
    · rename_i h
      exact (exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
        (I := I) (M := M) g r s₁ m h).choose_spec.1
    · exact le_refl 0
  have hCTf_nn : ∀ m, 0 ≤ CTf m := by
    intro m; rw [hCTf]; dsimp only; split
    · rename_i h
      exact (exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
        (I := I) (M := M) g 0 s₂ m h).choose_spec.1
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
    riemannianFiberNormSq (I := I) (M := M) g r (s₁ + a) x
      ((iteratedCovGrad (I := I) g r s₁ a S).toSection x) with hSj
  set Tj : ℕ → M → ℝ := fun b x =>
    riemannianFiberNormSq (I := I) (M := M) g 0 (s₂ + b) x
      ((iteratedCovGrad (I := I) g 0 s₂ b T).toSection x) with hTj
  have hSnorm : ∀ a, ∫ x, Sj a x ∂μ =
      ‖iteratedCovGrad (I := I) g r s₁ a S‖ ^ 2 := by
    intro a
    rw [hSj, hμ,
      ← (show Integral.L2.tensorL2Norm (I := I) (M := M) g r (s₁ + a)
            (iteratedCovGrad (I := I) g r s₁ a S).toFun ^ 2 =
          ∫ x, riemannianFiberNormSq (I := I) (M := M) g r (s₁ + a) x
            ((iteratedCovGrad (I := I) g r s₁ a S).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) from by
        have hfun : (iteratedCovGrad (I := I) g r s₁ a S).toFun =
            fun x => Tensor0SBundle.TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I)
              (M := M) (r := r) (s := s₁ + a) (x := x)
              ((iteratedCovGrad (I := I) g r s₁ a S).toSection x) := rfl
        rw [hfun]
        exact tensorL2Norm_sq_eq_integral_riemannianFiberNormSq (I := I) (M := M) g r (s₁ + a) _),
      ← Integral.L2.SmoothCcTensor.norm_def (iteratedCovGrad (I := I) g r s₁ a S)]
  have hTnorm : ∀ b, ∫ x, Tj b x ∂μ =
      ‖iteratedCovGrad (I := I) g 0 s₂ b T‖ ^ 2 := by
    intro b
    rw [hTj, hμ,
      ← (show Integral.L2.tensorL2Norm (I := I) (M := M) g 0 (s₂ + b)
            (iteratedCovGrad (I := I) g 0 s₂ b T).toFun ^ 2 =
          ∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 (s₂ + b) x
            ((iteratedCovGrad (I := I) g 0 s₂ b T).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) from by
        have hfun : (iteratedCovGrad (I := I) g 0 s₂ b T).toFun =
            fun x => Tensor0SBundle.TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I)
              (M := M) (r := 0) (s := s₂ + b) (x := x)
              ((iteratedCovGrad (I := I) g 0 s₂ b T).toSection x) := rfl
        rw [hfun]
        exact tensorL2Norm_sq_eq_integral_riemannianFiberNormSq (I := I) (M := M) g 0 (s₂ + b) _),
      ← Integral.L2.SmoothCcTensor.norm_def (iteratedCovGrad (I := I) g 0 s₂ b T)]
  have hSj_cont : ∀ a, Continuous (Sj a) := fun a => by
    rw [hSj]; exact mixed_continuous_rfns g r (s₁ + a) _
  have hTj_cont : ∀ b, Continuous (Tj b) := fun b => by
    rw [hTj]; exact mixed_continuous_rfns g 0 (s₂ + b) _
  have hSj_nn : ∀ a x, 0 ≤ Sj a x := fun a x => by
    rw [hSj]; exact riemannianFiberNormSq_nonneg (I := I) (M := M) g r (s₁ + a) x _
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
    rw [iteratedCovGrad_zero (I := I) g r s₁ S]
    exact hSsup x
  have hTsup0 : ∀ x, Tj 0 x ≤ ΛT ^ 2 := by
    intro x; rw [hTj]; dsimp only
    rw [iteratedCovGrad_zero (I := I) g 0 s₂ T]
    exact hTsup x
  have hAS_nn : 0 ≤ ΛT ^ 2 * ∑ a ∈ Finset.range (k + 1),
      ‖iteratedCovGrad (I := I) g r s₁ a S‖ ^ 2 := by positivity
  have hAT_nn : 0 ≤ ΛS ^ 2 * ∑ b ∈ Finset.range (k + 1),
      ‖iteratedCovGrad (I := I) g 0 s₂ b T‖ ^ 2 := by positivity
  have hcell : ∀ i, i ≤ k → ∀ l, i + l ≤ k →
      ∫ x, Sj i x * Tj l x ∂μ ≤ Cbig *
        ((ΛT ^ 2 * ∑ a ∈ Finset.range (k + 1),
            ‖iteratedCovGrad (I := I) g r s₁ a S‖ ^ 2)
          + (ΛS ^ 2 * ∑ b ∈ Finset.range (k + 1),
            ‖iteratedCovGrad (I := I) g 0 s₂ b T‖ ^ 2)) := by
    intro i hik l hilk
    have hSi_in : ‖iteratedCovGrad (I := I) g r s₁ i S‖ ^ 2 ≤
        ∑ a ∈ Finset.range (k + 1),
          ‖iteratedCovGrad (I := I) g r s₁ a S‖ ^ 2 :=
      Finset.single_le_sum
        (f := fun a => ‖iteratedCovGrad (I := I) g r s₁ a S‖ ^ 2)
        (fun a _ => sq_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hik))
    have hTl_in : ‖iteratedCovGrad (I := I) g 0 s₂ l T‖ ^ 2 ≤
        ∑ b ∈ Finset.range (k + 1),
          ‖iteratedCovGrad (I := I) g 0 s₂ b T‖ ^ 2 :=
      Finset.single_le_sum
        (f := fun b => ‖iteratedCovGrad (I := I) g 0 s₂ b T‖ ^ 2)
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
          ≤ ΛS ^ 2 * ‖iteratedCovGrad (I := I) g 0 s₂ l T‖ ^ 2 := hbound
        _ ≤ Cbig * (ΛS ^ 2 * ∑ b ∈ Finset.range (k + 1),
              ‖iteratedCovGrad (I := I) g 0 s₂ b T‖ ^ 2) := by
              rw [← mul_assoc, mul_comm (Cbig) (ΛS ^ 2), mul_assoc]
              exact mul_le_mul_of_nonneg_left
                (le_trans hTl_in (le_mul_of_one_le_left (Finset.sum_nonneg
                  (fun b _ => sq_nonneg _)) hCbig1)) (by positivity)
        _ ≤ Cbig * ((ΛT ^ 2 * ∑ a ∈ Finset.range (k + 1),
              ‖iteratedCovGrad (I := I) g r s₁ a S‖ ^ 2)
            + (ΛS ^ 2 * ∑ b ∈ Finset.range (k + 1),
              ‖iteratedCovGrad (I := I) g 0 s₂ b T‖ ^ 2)) := by
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
            ≤ ΛT ^ 2 * ‖iteratedCovGrad (I := I) g r s₁ i S‖ ^ 2 := hbound
          _ ≤ Cbig * (ΛT ^ 2 * ∑ a ∈ Finset.range (k + 1),
                ‖iteratedCovGrad (I := I) g r s₁ a S‖ ^ 2) := by
                rw [← mul_assoc, mul_comm (Cbig) (ΛT ^ 2), mul_assoc]
                exact mul_le_mul_of_nonneg_left
                  (le_trans hSi_in (le_mul_of_one_le_left (Finset.sum_nonneg
                    (fun a _ => sq_nonneg _)) hCbig1)) (by positivity)
          _ ≤ Cbig * ((ΛT ^ 2 * ∑ a ∈ Finset.range (k + 1),
                ‖iteratedCovGrad (I := I) g r s₁ a S‖ ^ 2)
              + (ΛS ^ 2 * ∑ b ∈ Finset.range (k + 1),
                ‖iteratedCovGrad (I := I) g 0 s₂ b T‖ ^ 2)) := by
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
        have hHolder := mixed_real_holder_two_nonneg g (Sj i) (Tj l)
          (hSj_cont i) (hTj_cont l) (hSj_nn i) (hTj_nn l) hpq
        have h1p : (1 : ℝ) / p = wi := by rw [hp, one_div_div, hwi]
        have h1q : (1 : ℝ) / q = wl := by rw [hq, one_div_div, hwl]
        rw [h1p, h1q] at hHolder
        have hSe := (exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
          (I := I) (M := M) g r s₁ m hm1).choose_spec.2 S ΛS hΛS hSsup i hipos hmi
        have hTe := (exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
          (I := I) (M := M) g 0 s₂ m hm1).choose_spec.2 T ΛT hΛT hTsup l hlpos hml
        have hCSf_m : (exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
            (I := I) (M := M) g r s₁ m hm1).choose = CSf m := by
          simp only [hCSf, dif_pos hm1]
        have hCTf_m : (exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
            (I := I) (M := M) g 0 s₂ m hm1).choose = CTf m := by
          simp only [hCTf, dif_pos hm1]
        rw [hCSf_m] at hSe
        rw [hCTf_m] at hTe
        rw [mul_div_assoc 2 (i : ℝ) m, ← hwi] at hSe
        rw [mul_div_assoc 2 (l : ℝ) m, ← hwl] at hTe
        rw [show Integral.L2.tensorL2Norm (I := I) g r (s₁ + m)
              (iteratedCovGrad (I := I) g r s₁ m S).toFun =
              ‖iteratedCovGrad (I := I) g r s₁ m S‖ from
            (Integral.L2.SmoothCcTensor.norm_def
              (iteratedCovGrad (I := I) g r s₁ m S)).symm] at hSe
        rw [show Integral.L2.tensorL2Norm (I := I) g 0 (s₂ + m)
              (iteratedCovGrad (I := I) g 0 s₂ m T).toFun =
              ‖iteratedCovGrad (I := I) g 0 s₂ m T‖ from
            (Integral.L2.SmoothCcTensor.norm_def
              (iteratedCovGrad (I := I) g 0 s₂ m T)).symm] at hTe
        set Iφp : ℝ := ∫ x, Sj i x ^ p ∂μ with hIφp
        set Iψq : ℝ := ∫ x, Tj l x ^ q ∂μ with hIψq
        have hIφp_nn : 0 ≤ Iφp := by
          rw [hIφp]; exact integral_nonneg (fun x => Real.rpow_nonneg (hSj_nn i x) _)
        have hIψq_nn : 0 ≤ Iψq := by
          rw [hIψq]; exact integral_nonneg (fun x => Real.rpow_nonneg (hTj_nn l x) _)
        have hys := mixed_young_arm_split wi wl (CSf m) (CTf m) ΛS ΛT
          ‖iteratedCovGrad (I := I) g r s₁ m S‖
          ‖iteratedCovGrad (I := I) g 0 s₂ m T‖
          Iφp Iψq hwi_nn hwl_nn hwsum (hCSf_nn m) (hCTf_nn m) hΛS hΛT
          (norm_nonneg _) (norm_nonneg _) hIφp_nn hIψq_nn hSe hTe
        have hNS_sum : ‖iteratedCovGrad (I := I) g r s₁ m S‖ ^ 2 ≤
            ∑ a ∈ Finset.range (k + 1),
              ‖iteratedCovGrad (I := I) g r s₁ a S‖ ^ 2 :=
          Finset.single_le_sum
            (f := fun a => ‖iteratedCovGrad (I := I) g r s₁ a S‖ ^ 2)
            (fun a _ => sq_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hmk))
        have hNT_sum : ‖iteratedCovGrad (I := I) g 0 s₂ m T‖ ^ 2 ≤
            ∑ b ∈ Finset.range (k + 1),
              ‖iteratedCovGrad (I := I) g 0 s₂ b T‖ ^ 2 :=
          Finset.single_le_sum
            (f := fun b => ‖iteratedCovGrad (I := I) g 0 s₂ b T‖ ^ 2)
            (fun b _ => sq_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hmk))
        have hwi_le1 : wi ≤ 1 := by rw [← hwsum]; linarith
        have hwl_le1 : wl ≤ 1 := by rw [← hwsum]; linarith
        calc ∫ x, Sj i x * Tj l x ∂μ
            ≤ Iφp ^ wi * Iψq ^ wl := hHolder
          _ ≤ CSf m * CTf m * (wi * (ΛT ^ 2 *
                ‖iteratedCovGrad (I := I) g r s₁ m S‖ ^ 2)
              + wl * (ΛS ^ 2 *
                ‖iteratedCovGrad (I := I) g 0 s₂ m T‖ ^ 2)) := hys
          _ ≤ Cbig * ((ΛT ^ 2 * ∑ a ∈ Finset.range (k + 1),
                ‖iteratedCovGrad (I := I) g r s₁ a S‖ ^ 2)
              + (ΛS ^ 2 * ∑ b ∈ Finset.range (k + 1),
                ‖iteratedCovGrad (I := I) g 0 s₂ b T‖ ^ 2)) := by
              refine le_trans (mul_le_mul_of_nonneg_right (hCSCT_le m hmk) ?_) ?_
              · have : 0 ≤ wi * (ΛT ^ 2 *
                    ‖iteratedCovGrad (I := I) g r s₁ m S‖ ^ 2)
                  + wl * (ΛS ^ 2 *
                    ‖iteratedCovGrad (I := I) g 0 s₂ m T‖ ^ 2) := by positivity
                exact this
              · refine mul_le_mul_of_nonneg_left ?_ hCbig_nn
                have harm1 : wi * (ΛT ^ 2 *
                    ‖iteratedCovGrad (I := I) g r s₁ m S‖ ^ 2) ≤
                    ΛT ^ 2 * ∑ a ∈ Finset.range (k + 1),
                      ‖iteratedCovGrad (I := I) g r s₁ a S‖ ^ 2 := by
                  calc wi * (ΛT ^ 2 *
                        ‖iteratedCovGrad (I := I) g r s₁ m S‖ ^ 2)
                      ≤ 1 * (ΛT ^ 2 *
                        ‖iteratedCovGrad (I := I) g r s₁ m S‖ ^ 2) :=
                        mul_le_mul_of_nonneg_right hwi_le1 (by positivity)
                    _ = ΛT ^ 2 *
                        ‖iteratedCovGrad (I := I) g r s₁ m S‖ ^ 2 := one_mul _
                    _ ≤ ΛT ^ 2 * ∑ a ∈ Finset.range (k + 1),
                          ‖iteratedCovGrad (I := I) g r s₁ a S‖ ^ 2 :=
                        mul_le_mul_of_nonneg_left hNS_sum (by positivity)
                have harm2 : wl * (ΛS ^ 2 *
                    ‖iteratedCovGrad (I := I) g 0 s₂ m T‖ ^ 2) ≤
                    ΛS ^ 2 * ∑ b ∈ Finset.range (k + 1),
                      ‖iteratedCovGrad (I := I) g 0 s₂ b T‖ ^ 2 := by
                  calc wl * (ΛS ^ 2 *
                        ‖iteratedCovGrad (I := I) g 0 s₂ m T‖ ^ 2)
                      ≤ 1 * (ΛS ^ 2 *
                        ‖iteratedCovGrad (I := I) g 0 s₂ m T‖ ^ 2) :=
                        mul_le_mul_of_nonneg_right hwl_le1 (by positivity)
                    _ = ΛS ^ 2 *
                        ‖iteratedCovGrad (I := I) g 0 s₂ m T‖ ^ 2 := one_mul _
                    _ ≤ ΛS ^ 2 * ∑ b ∈ Finset.range (k + 1),
                          ‖iteratedCovGrad (I := I) g 0 s₂ b T‖ ^ 2 :=
                        mul_le_mul_of_nonneg_left hNT_sum (by positivity)
                linarith
  have hrw : (∫ x, ∑ i ∈ Finset.range (k + 1), Sj i x *
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
            ‖iteratedCovGrad (I := I) g r s₁ a S‖ ^ 2)
          + (ΛS ^ 2 * ∑ b ∈ Finset.range (k + 1),
            ‖iteratedCovGrad (I := I) g 0 s₂ b T‖ ^ 2)) := by
    refine Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun l hl => ?_))
    have hik : i ≤ k := by rw [Finset.mem_range] at hi; omega
    have hilk : i + l ≤ k := by
      rw [Finset.mem_range] at hi hl; omega
    exact hcell i hik l hilk
  refine le_trans hsum_le ?_
  set c : ℝ := Cbig * ((ΛT ^ 2 * ∑ a ∈ Finset.range (k + 1),
      ‖iteratedCovGrad (I := I) g r s₁ a S‖ ^ 2)
    + (ΛS ^ 2 * ∑ b ∈ Finset.range (k + 1),
      ‖iteratedCovGrad (I := I) g 0 s₂ b T‖ ^ 2)) with hc
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

theorem ccTensorContract_topOrder_l2_twoArm_mixed_le
    (g₀ : SmoothRiemannianMetric I M) (b₀ s₀ q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Φ : SmoothCcTensor g₀ b₀ s₀) (W : SmoothCcTensor g₀ 0 b₀) (ΛΦ ΛW : ℝ),
        0 ≤ ΛΦ → 0 ≤ ΛW →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ b₀ s₀ x (Φ.toSection x) ≤ ΛΦ ^ 2) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 b₀ x (W.toSection x) ≤ ΛW ^ 2) →
        ‖iteratedCovGrad (I := I) g₀ 0 s₀ q
            (operatorFieldApply (I := I) (M := M) g₀ b₀ s₀ Φ W)‖ ^ 2 ≤
          C * (ΛW ^ 2 * ∑ i ∈ Finset.range (q + 1),
                ‖iteratedCovGrad (I := I) g₀ b₀ s₀ i Φ‖ ^ 2
              + ΛΦ ^ 2 * ∑ l ∈ Finset.range (q + 1),
                ‖iteratedCovGrad (I := I) g₀ 0 b₀ l W‖ ^ 2) := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀

  obtain ⟨Cgrid, hCgrid_nn, hCgrid⟩ :=
    appCc_integrated_grid_twoArm_mixed (I := I) g₀ b₀ s₀ b₀ q

  set Gk : ℝ := diagonalGridGrowthFactor (E := E) q with hGk
  have hGk_nn : 0 ≤ Gk := appCcGdiag_nonneg (E := E) q
  refine ⟨Gk * Cgrid, by positivity, ?_⟩
  intro Φ W ΛΦ ΛW hΛΦ hΛW hΦsup hWsup
  set μ : Measure M := riemannianVolumeMeasure (I := I) (M := M) g₀ with hμ
  set P : SmoothCcTensor g₀ 0 s₀ := operatorFieldApply (I := I) (M := M) g₀ b₀ s₀ Φ W with hP

  have hLHS_eq : ‖iteratedCovGrad (I := I) g₀ 0 s₀ q P‖ ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s₀ + q) x
        ((iteratedCovGrad (I := I) g₀ 0 s₀ q P).toSection x) ∂μ := by
    rw [hμ, Integral.L2.SmoothCcTensor.norm_def
        (iteratedCovGrad (I := I) g₀ 0 s₀ q P)]
    have hfun : (iteratedCovGrad (I := I) g₀ 0 s₀ q P).toFun =
        fun x => Tensor0SBundle.TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I)
          (M := M) (r := 0) (s := s₀ + q) (x := x)
          ((iteratedCovGrad (I := I) g₀ 0 s₀ q P).toSection x) := rfl
    rw [hfun]
    exact tensorL2Norm_sq_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s₀ + q) _

  set grid : M → ℝ := fun x => ∑ i ∈ Finset.range (q + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ b₀ (s₀ + i) x
          ((iteratedCovGrad (I := I) g₀ b₀ s₀ i Φ).toSection x)
        * ∑ l ∈ Finset.range (q + 1 - i),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (b₀ + l) x
              ((iteratedCovGrad (I := I) g₀ 0 b₀ l W).toSection x) with hgrid

  have hptwise : ∀ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s₀ + q) x
        ((iteratedCovGrad (I := I) g₀ 0 s₀ q P).toSection x) ≤ Gk * grid x := by
    intro x
    rw [hGk, hgrid, hP]
    exact riemannianFiberNormSq_iteratedCovGrad_comp_diagonalProductGrid_le (I := I) g₀ b₀ s₀ Φ W q x

  have hgrid_cont : Continuous grid := by
    rw [hgrid]
    refine continuous_finset_sum _ (fun i _ => (mixed_continuous_rfns g₀ b₀ (s₀ + i) _).mul ?_)
    exact continuous_finset_sum _ (fun l _ => mixed_continuous_rfns g₀ 0 (b₀ + l) _)
  have hgrid_int : Integrable grid μ := by
    rw [hμ]; exact hgrid_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

  have hmono : ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s₀ + q) x
        ((iteratedCovGrad (I := I) g₀ 0 s₀ q P).toSection x) ∂μ ≤
      Gk * ∫ x, grid x ∂μ := by
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (Eventually.of_forall (fun x =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (s₀ + q) x _)) ?_
      (Eventually.of_forall hptwise)
    exact hgrid_int.const_mul _

  have hgrid_bound := hCgrid Φ W ΛΦ ΛW hΛΦ hΛW hΦsup hWsup
  rw [hLHS_eq]
  calc ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s₀ + q) x
        ((iteratedCovGrad (I := I) g₀ 0 s₀ q P).toSection x) ∂μ
      ≤ Gk * ∫ x, grid x ∂μ := hmono
    _ ≤ Gk * (Cgrid * (ΛW ^ 2 * ∑ i ∈ Finset.range (q + 1),
            ‖iteratedCovGrad (I := I) g₀ b₀ s₀ i Φ‖ ^ 2
          + ΛΦ ^ 2 * ∑ l ∈ Finset.range (q + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 b₀ l W‖ ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ hGk_nn
        rw [hgrid]; exact hgrid_bound
    _ = Gk * Cgrid * (ΛW ^ 2 * ∑ i ∈ Finset.range (q + 1),
            ‖iteratedCovGrad (I := I) g₀ b₀ s₀ i Φ‖ ^ 2
          + ΛΦ ^ 2 * ∑ l ∈ Finset.range (q + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 b₀ l W‖ ^ 2) := by ring

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
omit [BoundarylessManifold I M] in
theorem deTurckSmoothRemainderDiff_supercritical_pointwise_jet_le_fixedWindow
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) :
    ∃ Cemb : ℝ, 0 ≤ Cemb ∧
      ∀ (W : SmoothCcTensor g₀ 0 2) (x : M),
        (∑ m ∈ Finset.range 3,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 m W).toSection x)) ≤
          Cemb ^ 2 * ∑ i ∈ Finset.range (a + 1 + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 i W‖ ^ 2 := by
  classical
  set K : ℕ := Module.finrank ℝ E / 2 + 1 with hK_def
  have hK_super : 2 * K > Module.finrank ℝ E + 2 * 0 := by rw [hK_def]; omega
  set L : ℕ := 4 * K + 4 with hL_def
  have hL_le : L ≤ a + 1 := by rw [hL_def, hK_def]; omega
  have hperdeg : ∀ q : ℕ, q ≤ 2 → ∃ Dq : ℝ, 0 ≤ Dq ∧
      ∀ (W : SmoothCcTensor g₀ 0 2) (x : M),
        (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + q) I b) :=
          Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + q)
        ‖(iteratedCovGrad (I := I) g₀ 0 2 q W).toSection x‖) ≤
          Dq * ∑ j ∈ Finset.range (L + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j W‖ := by
    intro q hq
    obtain ⟨Cemb, hCemb_pos, hCemb⟩ :=
      tensorPouSobolevHilbert_embedding_Ck_gNorm (I := I) (M := M) g₀ 0 (2 + q) K 0 hK_super
    obtain ⟨Cit, hCit_nn, hCit⟩ :=
      iteratedCovGrad_toHs_norm_le (I := I) (M := M) g₀ 0 2 q (2 * K)
    obtain ⟨Crev, hCrev_nn, hCrev⟩ :=
      exists_toHs_norm_le_iteratedCovGrad_tensorL2Norm_sum (I := I) (M := M) g₀ 0 2 (2 * K + q)
    refine ⟨Cemb * Cit * Crev, by positivity, fun W x => ?_⟩
    have hwin : 2 * (2 * K + q) + 1 ≤ L + 1 := by rw [hL_def]; omega
    have hrev : ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2)
        (2 * K + q) W‖ ≤
        Crev * ∑ j ∈ Finset.range (L + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j W‖ := by
      refine le_trans (hCrev W) ?_
      refine mul_le_mul_of_nonneg_left ?_ hCrev_nn
      have hcongr : (∑ j ∈ Finset.range (2 * (2 * K + q) + 1),
          tensorL2Norm (I := I) (M := M) g₀ 0 (2 + j)
            (iteratedCovGrad (I := I) g₀ 0 2 j W).toFun) =
          ∑ j ∈ Finset.range (2 * (2 * K + q) + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j W‖ :=
        Finset.sum_congr rfl
          (fun j _ => (SmoothCcTensor.norm_def (iteratedCovGrad (I := I) g₀ 0 2 j W)).symm)
      rw [hcongr]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hwin)
        (fun j _ _ => norm_nonneg _)
    have hit : ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2 + q)
        (2 * K) (iteratedCovGrad (I := I) g₀ 0 2 q W)‖ ≤
        Cit * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2)
          (2 * K + q) W‖ := hCit W
    have hemb := hCemb (iteratedCovGrad (I := I) g₀ 0 2 q W) x
    calc (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + q) I b) :=
            Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + q)
          ‖(iteratedCovGrad (I := I) g₀ 0 2 q W).toSection x‖)
        ≤ Cemb * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2 + q)
            (2 * K) (iteratedCovGrad (I := I) g₀ 0 2 q W)‖ := hemb
      _ ≤ Cemb * (Cit * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2)
            (2 * K + q) W‖) := mul_le_mul_of_nonneg_left hit hCemb_pos.le
      _ ≤ Cemb * (Cit * (Crev * ∑ j ∈ Finset.range (L + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j W‖)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hrev hCit_nn) hCemb_pos.le
      _ = Cemb * Cit * Crev * ∑ j ∈ Finset.range (L + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j W‖ := by ring
  choose Dfun hDfun_nn hDfun using hperdeg
  set D : ℝ := max (Dfun 0 (by norm_num))
    (max (Dfun 1 (by norm_num)) (Dfun 2 (by norm_num))) with hD_def
  have hD_nn : 0 ≤ D := le_trans (hDfun_nn 0 (by norm_num)) (le_max_left _ _)
  have hD0 : Dfun 0 (by norm_num) ≤ D := le_max_left _ _
  have hD1 : Dfun 1 (by norm_num) ≤ D := le_trans (le_max_left _ _) (le_max_right _ _)
  have hD2 : Dfun 2 (by norm_num) ≤ D := le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨Real.sqrt (3 * D ^ 2 * ((L + 1 : ℕ) : ℝ)), Real.sqrt_nonneg _, fun W x => ?_⟩
  set Ssum : ℝ := ∑ j ∈ Finset.range (L + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j W‖
    with hSsum_def
  have hSsum_nn : 0 ≤ Ssum := Finset.sum_nonneg fun j _ => norm_nonneg _
  letI inst0 : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + 0) I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + 0)
  letI inst1 : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + 1) I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + 1)
  letI inst2 : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + 2) I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + 2)
  have hptdeg : ∀ q : ℕ, q ≤ 2 →
      (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + q) I b) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + q)
      ‖(iteratedCovGrad (I := I) g₀ 0 2 q W).toSection x‖) ≤ D * Ssum := by
    intro q hq
    interval_cases q
    · exact le_trans (hDfun 0 (by norm_num) W x)
        (mul_le_mul_of_nonneg_right hD0 hSsum_nn)
    · exact le_trans (hDfun 1 (by norm_num) W x)
        (mul_le_mul_of_nonneg_right hD1 hSsum_nn)
    · exact le_trans (hDfun 2 (by norm_num) W x)
        (mul_le_mul_of_nonneg_right hD2 hSsum_nn)
  have hcs : Ssum ^ 2 ≤ ((L + 1 : ℕ) : ℝ) *
      ∑ j ∈ Finset.range (L + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j W‖ ^ 2 := by
    rw [hSsum_def]
    have := sq_sum_le_card_mul_sum_sq (s := Finset.range (L + 1))
      (f := fun j => ‖iteratedCovGrad (I := I) g₀ 0 2 j W‖)
    rw [Finset.card_range] at this
    exact_mod_cast this
  have hwin2 : (∑ j ∈ Finset.range (L + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j W‖ ^ 2) ≤
      ∑ i ∈ Finset.range (a + 1 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 i W‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_mono (by omega)) (fun i _ _ => sq_nonneg _)
  have hsqrt_sq : Real.sqrt (3 * D ^ 2 * ((L + 1 : ℕ) : ℝ)) ^ 2 =
      3 * D ^ 2 * ((L + 1 : ℕ) : ℝ) := Real.sq_sqrt (by positivity)
  rw [hsqrt_sq]
  set RHS : ℝ := ∑ i ∈ Finset.range (a + 1 + 1),
    ‖iteratedCovGrad (I := I) g₀ 0 2 i W‖ ^ 2 with hRHS_def
  have hRHS_nn : 0 ≤ RHS := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hpt0 := hptdeg 0 (by norm_num)
  have hpt1 := hptdeg 1 (by norm_num)
  have hpt2 := hptdeg 2 (by norm_num)
  have hcolsq_le : (∑ q ∈ Finset.range 3,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
        ((iteratedCovGrad (I := I) g₀ 0 2 q W).toSection x)) ≤
      3 * (D * Ssum) ^ 2 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero, zero_add,
      riemannianFiberNormSq_eq_bundle_norm_sq' (I := I) (M := M) g₀ 0 (2 + 0) x
        ((iteratedCovGrad (I := I) g₀ 0 2 0 W).toSection x),
      riemannianFiberNormSq_eq_bundle_norm_sq' (I := I) (M := M) g₀ 0 (2 + 1) x
        ((iteratedCovGrad (I := I) g₀ 0 2 1 W).toSection x),
      riemannianFiberNormSq_eq_bundle_norm_sq' (I := I) (M := M) g₀ 0 (2 + 2) x
        ((iteratedCovGrad (I := I) g₀ 0 2 2 W).toSection x)]
    have hDS_nn : 0 ≤ D * Ssum := mul_nonneg hD_nn hSsum_nn
    nlinarith [hpt0, hpt1, hpt2,
      norm_nonneg ((iteratedCovGrad (I := I) g₀ 0 2 0 W).toSection x),
      norm_nonneg ((iteratedCovGrad (I := I) g₀ 0 2 1 W).toSection x),
      norm_nonneg ((iteratedCovGrad (I := I) g₀ 0 2 2 W).toSection x), hDS_nn]
  calc (∑ q ∈ Finset.range 3,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
            ((iteratedCovGrad (I := I) g₀ 0 2 q W).toSection x))
      ≤ 3 * (D * Ssum) ^ 2 := hcolsq_le
    _ = 3 * D ^ 2 * Ssum ^ 2 := by ring
    _ ≤ 3 * D ^ 2 * (((L + 1 : ℕ) : ℝ) * RHS) := by
        rw [hRHS_def]
        exact mul_le_mul_of_nonneg_left
          (le_trans hcs (mul_le_mul_of_nonneg_left hwin2 (by positivity))) (by positivity)
    _ = (3 * D ^ 2 * ((L + 1 : ℕ) : ℝ)) * RHS := by ring

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem iteratedCovGrad_compWindow_l2_eq
    (g₀ : SmoothRiemannianMetric I M) (m l : ℕ) (W : SmoothCcTensor g₀ 0 2) :
    ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l (iteratedCovGrad (I := I) g₀ 0 2 m W)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g₀ 0 2 (m + l) W‖ ^ 2 := by
  have hbridgeL : ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l
        (iteratedCovGrad (I := I) g₀ 0 2 m W)‖ ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + m) + l) x
        ((iteratedCovGrad (I := I) g₀ 0 (2 + m) l
          (iteratedCovGrad (I := I) g₀ 0 2 m W)).toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := by
    rw [SmoothCcTensor.norm_def]
    exact tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀ ((2 + m) + l)
      (iteratedCovGrad (I := I) g₀ 0 (2 + m) l (iteratedCovGrad (I := I) g₀ 0 2 m W))
  have hbridgeR : ‖iteratedCovGrad (I := I) g₀ 0 2 (m + l) W‖ ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (m + l)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (m + l) W).toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := by
    rw [SmoothCcTensor.norm_def]
    exact tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀ (2 + (m + l))
      (iteratedCovGrad (I := I) g₀ 0 2 (m + l) W)
  rw [hbridgeL, hbridgeR]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  have hrw := riemannianFiberNormSq_iteratedCovGrad_comp (I := I) (M := M) g₀ 0 2 m l W x
  simpa only [Nat.add_assoc] using hrw

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem iteratedCovGrad_compWindow_jetSum_le
    (g₀ : SmoothRiemannianMetric I M) (q m : ℕ) (W : SmoothCcTensor g₀ 0 2) :
    (∑ l ∈ Finset.range (q + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l (iteratedCovGrad (I := I) g₀ 0 2 m W)‖ ^ 2) ≤
      ∑ i ∈ Finset.range (q + m + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 i W‖ ^ 2 := by
  rw [show (∑ l ∈ Finset.range (q + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l (iteratedCovGrad (I := I) g₀ 0 2 m W)‖ ^ 2) =
      ∑ l ∈ Finset.range (q + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 2 (m + l) W‖ ^ 2 from
    Finset.sum_congr rfl (fun l _ => iteratedCovGrad_compWindow_l2_eq (I := I) g₀ m l W)]
  set f : ℕ → ℝ := fun i => ‖iteratedCovGrad (I := I) g₀ 0 2 i W‖ ^ 2 with hf_def
  have hf_nn : ∀ i, 0 ≤ f i := fun i => sq_nonneg _
  have himg : (Finset.range (q + 1)).image (fun l => m + l) ⊆ Finset.range (q + m + 1) := by
    intro i hi
    rw [Finset.mem_image] at hi
    obtain ⟨l, hl, rfl⟩ := hi
    rw [Finset.mem_range] at hl ⊢
    omega
  have hinj : ∀ l₁ ∈ Finset.range (q + 1), ∀ l₂ ∈ Finset.range (q + 1),
      m + l₁ = m + l₂ → l₁ = l₂ := fun l₁ _ l₂ _ h => by omega
  calc (∑ l ∈ Finset.range (q + 1), f (m + l))
      = ∑ i ∈ (Finset.range (q + 1)).image (fun l => m + l), f i :=
        (Finset.sum_image hinj).symm
    _ ≤ ∑ i ∈ Finset.range (q + m + 1), f i :=
        Finset.sum_le_sum_of_subset_of_nonneg himg (fun i _ _ => hf_nn i)

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
