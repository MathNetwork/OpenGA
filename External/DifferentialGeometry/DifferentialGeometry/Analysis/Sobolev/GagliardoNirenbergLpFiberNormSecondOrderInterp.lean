import DifferentialGeometry.Analysis.Sobolev.MoserTameProduct
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.CovGradBundleEquivFiberNormFrameSum
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovGradCrossBridge
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RankRReadingDominationUniformSup
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.GradientField
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.HomFieldCurvatureJetDecomposition
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.TensorThirdOrderWeitzenbock
import DifferentialGeometry.Analysis.Spectral.Tensor.Variational.CovDerivPointwise
import DifferentialGeometry.Bundle.Section
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.TensorDirichletCurrentGreenIdentityRS
import DifferentialGeometry.Analysis.Sobolev.GagliardoNirenbergLpFiberNormDiscreteLogConvex
import DifferentialGeometry.Analysis.Sobolev.GagliardoNirenbergLpFiberNormHolderIntegrability
import DifferentialGeometry.Analysis.Sobolev.GagliardoNirenbergLpFiberNormWeightedCovIBP

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Analysis.Sobolev.Tensor

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
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

section GeneralValenceRS

open Bundle Tensor0SBundle Tensor0SNabla TensorRSNabla TensorMultilinear

set_option maxHeartbeats 1600000 in

theorem secondOrderInterp_lpFiberJet_fin_rs
    (g : SmoothRiemannianMetric I M) (k r : ℕ) (_hk : 1 ≤ k) :
    ∃ K' : ℝ, 1 ≤ K' ∧
      ∀ (m : ℕ) (w : Integral.L2.SmoothCcTensor g r m) (i : ℕ), 1 ≤ i → i + 1 < k →
        ((∫ x, (riemannianFiberNormSq (I := I) (M := M) g r (m + 1) x
              ((covGrad (I := I) (M := M) g r m w).toSection x)) ^ ((k : ℝ) / (i + 1))
            ∂(Integral.Measure.riemannianVolumeMeasure I M g)) ^ (((i : ℝ) + 1) / (2 * k))) ^ 2 ≤
          K' *
            ((∫ x, (riemannianFiberNormSq (I := I) (M := M) g r m x (w.toSection x)) ^ ((k : ℝ) / i)
                ∂(Integral.Measure.riemannianVolumeMeasure I M g)) ^ ((i : ℝ) / (2 * k))) *
            ((∫ x, (riemannianFiberNormSq (I := I) (M := M) g r (m + 1 + 1) x
                  ((covGrad (I := I) (M := M) g r (m + 1)
                    (covGrad (I := I) (M := M) g r m w)).toSection x)) ^ ((k : ℝ) / (i + 2))
                ∂(Integral.Measure.riemannianVolumeMeasure I M g)) ^ (((i : ℝ) + 2) / (2 * k))) := by
  classical
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one _hk)

  refine ⟨max (max (2 * ((k : ℝ) - 1) + Real.sqrt (Module.finrank ℝ E : ℝ)) 1) 1, ?_, ?_⟩
  · exact le_trans (le_max_right _ _) (le_max_left _ _)
  intro m w i hi1 hreg_lt
  set μ : MeasureTheory.Measure M := Integral.Measure.riemannianVolumeMeasure I M g with hμ
  haveI : MeasureTheory.IsFiniteMeasure μ :=
    Integral.Measure.riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  set K' : ℝ := max (max (2 * ((k : ℝ) - 1) + Real.sqrt (Module.finrank ℝ E : ℝ)) 1) 1
    with hK'def

  set a : M → ℝ := fun x => riemannianFiberNormSq (I := I) (M := M) g r m x (w.toSection x)
    with ha_def
  set b : M → ℝ := fun x => riemannianFiberNormSq (I := I) (M := M) g r (m + 1) x
    ((covGrad (I := I) (M := M) g r m w).toSection x) with hb_def
  set c : M → ℝ := fun x => riemannianFiberNormSq (I := I) (M := M) g r (m + 1 + 1) x
    ((covGrad (I := I) (M := M) g r (m + 1) (covGrad (I := I) (M := M) g r m w)).toSection x)
    with hc_def
  have ha0 : ∀ x, 0 ≤ a x := fun x => riemannianFiberNormSq_nonneg (I := I) (M := M) g r m x _
  have hb0 : ∀ x, 0 ≤ b x := fun x =>
    riemannianFiberNormSq_nonneg (I := I) (M := M) g r (m + 1) x _
  have hc0 : ∀ x, 0 ≤ c x := fun x =>
    riemannianFiberNormSq_nonneg (I := I) (M := M) g r (m + 1 + 1) x _
  have hac : Continuous a := continuous_riemannianFiberNormSq_section (I := I) (M := M) g r m w
  have hbc : Continuous b :=
    continuous_riemannianFiberNormSq_section (I := I) (M := M) g r (m + 1) (covGrad (I := I) (M := M) g r m w)
  have hcc : Continuous c :=
    continuous_riemannianFiberNormSq_section (I := I) (M := M) g r (m + 1 + 1)
      (covGrad (I := I) (M := M) g r (m + 1) (covGrad (I := I) (M := M) g r m w))
  rcases lt_or_ge (i + 1) k with hreg | hreg
  · have hiR : (0 : ℝ) < (i : ℝ) := by exact_mod_cast hi1
    have hi1R : (0 : ℝ) < (i : ℝ) + 1 := by positivity
    have hi2R : (0 : ℝ) < (i : ℝ) + 2 := by positivity

    set p : ℝ := (k : ℝ) / (i + 1) with hp_def
    have hp1 : 1 < p := by
      rw [hp_def, lt_div_iff₀ hi1R, one_mul]; exact_mod_cast hreg
    have hp0 : 0 < p := lt_trans one_pos hp1
    have hp1m : 0 < p - 1 := by linarith

    set α : ℝ := 2 * (k : ℝ) / i with hα_def
    set β : ℝ := (k : ℝ) / ((k : ℝ) - ((i : ℝ) + 1)) with hβ_def
    set γ : ℝ := 2 * (k : ℝ) / (i + 2) with hγ_def
    have hkmi : 0 < (k : ℝ) - ((i : ℝ) + 1) := by
      have : ((i : ℝ) + 1) < (k : ℝ) := by exact_mod_cast hreg
      linarith
    have hα0 : 0 < α := by rw [hα_def]; positivity
    have hβ0 : 0 < β := by rw [hβ_def]; positivity
    have hγ0 : 0 < γ := by rw [hγ_def]; positivity

    have hbalance : α⁻¹ + β⁻¹ + γ⁻¹ = 1 := by
      rw [hα_def, hβ_def, hγ_def]
      rw [inv_div, inv_div, inv_div]
      field_simp
      ring

    set f₁ : M → ℝ := fun x => a x ^ (1 / 2 : ℝ) with hf₁_def
    set f₂ : M → ℝ := fun x => b x ^ (p - 1) with hf₂_def
    set f₃ : M → ℝ := fun x => c x ^ (1 / 2 : ℝ) with hf₃_def
    have hf₁c : Continuous f₁ := hac.rpow_const (fun _ => Or.inr (by norm_num))
    have hf₂c : Continuous f₂ := hbc.rpow_const (fun _ => Or.inr (le_of_lt hp1m))
    have hf₃c : Continuous f₃ := hcc.rpow_const (fun _ => Or.inr (by norm_num))
    have hf₁0 : ∀ x, 0 ≤ f₁ x := fun x => Real.rpow_nonneg (ha0 x) _
    have hf₂0 : ∀ x, 0 ≤ f₂ x := fun x => Real.rpow_nonneg (hb0 x) _
    have hf₃0 : ∀ x, 0 ≤ f₃ x := fun x => Real.rpow_nonneg (hc0 x) _

    have hHolder := real_holder_three_nonneg (I := I) (M := M) g f₁ f₂ f₃
      hf₁c hf₂c hf₃c hf₁0 hf₂0 hf₃0 hα0 hβ0 hγ0 hbalance

    have hαexp : (1 / 2 : ℝ) * α = (k : ℝ) / i := by
      rw [hα_def]; field_simp
    have he1 : ∀ x, f₁ x ^ α = a x ^ ((k : ℝ) / i) := by
      intro x; rw [hf₁_def, ← Real.rpow_mul (ha0 x), hαexp]

    have hγexp : (1 / 2 : ℝ) * γ = (k : ℝ) / (i + 2) := by
      rw [hγ_def]; field_simp
    have he3 : ∀ x, f₃ x ^ γ = c x ^ ((k : ℝ) / (i + 2)) := by
      intro x; rw [hf₃_def, ← Real.rpow_mul (hc0 x), hγexp]

    have hβexp : (p - 1) * β = p := by
      have hpm1 : p - 1 = ((k : ℝ) - ((i : ℝ) + 1)) / ((i : ℝ) + 1) := by
        rw [hp_def, div_sub_one (ne_of_gt hi1R)]
      rw [hpm1, hβ_def, hp_def, div_mul_div_comm, mul_comm ((k : ℝ) - ((i : ℝ) + 1)) (k : ℝ),
        mul_div_mul_right _ _ (ne_of_gt hkmi)]
    have he2 : ∀ x, f₂ x ^ β = b x ^ p := by
      intro x; rw [hf₂_def, ← Real.rpow_mul (hb0 x), hβexp]
    rw [MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ he1),
        MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ he2),
        MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ he3)] at hHolder

    have hprod_pt : ∀ x, a x ^ (1 / 2 : ℝ) * b x ^ (p - 1) * c x ^ (1 / 2 : ℝ)
        = f₁ x * f₂ x * f₃ x := fun x => by rw [hf₁_def, hf₂_def, hf₃_def]

    have hIBP := weightedCovIBP_lpFiberJet_fin_rs (I := I) (M := M) g k m i r _hk hi1 hreg w

    rw [show (∫ x, (riemannianFiberNormSq (I := I) (M := M) g r m x (w.toSection x)) ^ (1 / 2 : ℝ) *
              (riemannianFiberNormSq (I := I) (M := M) g r (m + 1) x
                ((covGrad (I := I) (M := M) g r m w).toSection x)) ^ ((k : ℝ) / (i + 1) - 1) *
              (riemannianFiberNormSq (I := I) (M := M) g r (m + 1 + 1) x
                ((covGrad (I := I) (M := M) g r (m + 1)
                  (covGrad (I := I) (M := M) g r m w)).toSection x)) ^ (1 / 2 : ℝ) ∂μ)
            = ∫ x, f₁ x * f₂ x * f₃ x ∂μ from by
        refine MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ (fun x => ?_))
        rw [hf₁_def, hf₂_def, hf₃_def, ha_def, hb_def, hc_def, hp_def]] at hIBP

    set Ia : ℝ := ∫ x, a x ^ ((k : ℝ) / i) ∂μ with hIa_def
    set Ib : ℝ := ∫ x, b x ^ p ∂μ with hIb_def
    set Ic : ℝ := ∫ x, c x ^ ((k : ℝ) / (i + 2)) ∂μ with hIc_def
    have hIa_nn : 0 ≤ Ia := MeasureTheory.integral_nonneg (fun x => Real.rpow_nonneg (ha0 x) _)
    have hIb_nn : 0 ≤ Ib := MeasureTheory.integral_nonneg (fun x => Real.rpow_nonneg (hb0 x) _)
    have hIc_nn : 0 ≤ Ic := MeasureTheory.integral_nonneg (fun x => Real.rpow_nonneg (hc0 x) _)
    set Aw : ℝ := Ia ^ ((i : ℝ) / (2 * k)) with hAw_def
    set C : ℝ := Ic ^ (((i : ℝ) + 2) / (2 * k)) with hC_def
    have hAw_nn : 0 ≤ Aw := Real.rpow_nonneg hIa_nn _
    have hC_nn : 0 ≤ C := Real.rpow_nonneg hIc_nn _

    have hinvα : (1 : ℝ) / α = (i : ℝ) / (2 * k) := by rw [hα_def]; rw [one_div_div]
    have hinvγ : (1 : ℝ) / γ = ((i : ℝ) + 2) / (2 * k) := by rw [hγ_def]; rw [one_div_div]

    set D : ℝ := 2 * (p - 1) + Real.sqrt (Module.finrank ℝ E : ℝ) with hD_def
    have hsqrt_nn : (0 : ℝ) ≤ Real.sqrt (Module.finrank ℝ E : ℝ) := Real.sqrt_nonneg _

    have hIb_bound : Ib ≤ D * (Aw * (Ib ^ (1 / β) * C)) := by
      have hcoef_nn : 0 ≤ D := by rw [hD_def]; nlinarith [hp1m, hsqrt_nn]
      have hstep : Ib ≤ D * (∫ x, f₁ x * f₂ x * f₃ x ∂μ) := hIBP
      refine le_trans hstep ?_
      apply mul_le_mul_of_nonneg_left _ hcoef_nn
      rw [hinvα, hinvγ] at hHolder
      rw [hAw_def, hC_def]
      exact hHolder

    have hinvp : (1 : ℝ) / p = ((i : ℝ) + 1) / k := by
      rw [hp_def, one_div_div]
    have hinvβ : (1 : ℝ) / β = ((k : ℝ) - ((i : ℝ) + 1)) / k := by
      rw [hβ_def, one_div_div]
    have hsum_pβ : (1 : ℝ) / p + 1 / β = 1 := by
      rw [hinvp, hinvβ, ← add_div]
      rw [show ((i : ℝ) + 1) + ((k : ℝ) - ((i : ℝ) + 1)) = (k : ℝ) from by ring,
        div_self (ne_of_gt hkR)]

    have hLHS_sq : (Ib ^ (((i : ℝ) + 1) / (2 * k))) ^ 2 = Ib ^ ((1 : ℝ) / p) := by
      have hexp : ((i : ℝ) + 1) / (2 * k) * ((2 : ℕ) : ℝ) = (1 : ℝ) / p := by
        rw [hinvp]; push_cast; ring
      rw [← Real.rpow_natCast (Ib ^ (((i : ℝ) + 1) / (2 * k))) 2, ← Real.rpow_mul hIb_nn, hexp]

    have hcoef_le : D ≤ K' := by
      have hp_le_k : p ≤ (k : ℝ) := by
        rw [hp_def, div_le_iff₀ hi1R]
        nlinarith [hkR, hiR]
      have hDk : D ≤ 2 * ((k : ℝ) - 1) + Real.sqrt (Module.finrank ℝ E : ℝ) := by
        rw [hD_def]; linarith
      exact le_trans hDk (le_trans (le_max_left _ _) (le_max_left _ _))

    rw [hLHS_sq]
    rcases eq_or_lt_of_le hIb_nn with hIb0 | hIbpos
    · rw [← hIb0, Real.zero_rpow (by rw [hinvp]; positivity)]
      positivity
    · have hIbβ_pos : 0 < Ib ^ (1 / β) := Real.rpow_pos_of_pos hIbpos _

      have hIb_split : Ib = Ib ^ ((1 : ℝ) / p) * Ib ^ (1 / β) := by
        rw [← Real.rpow_add hIbpos, hsum_pβ, Real.rpow_one]

      have hkey : Ib ^ ((1 : ℝ) / p) * Ib ^ (1 / β) ≤ (D * (Aw * C)) * Ib ^ (1 / β) := by
        rw [← hIb_split]
        calc Ib ≤ D * (Aw * (Ib ^ (1 / β) * C)) := hIb_bound
          _ = (D * (Aw * C)) * Ib ^ (1 / β) := by ring
      have hcancel : Ib ^ ((1 : ℝ) / p) ≤ D * (Aw * C) :=
        le_of_mul_le_mul_right hkey hIbβ_pos
      calc Ib ^ ((1 : ℝ) / p) ≤ D * (Aw * C) := hcancel
        _ ≤ K' * (Aw * C) := by
            apply mul_le_mul_of_nonneg_right hcoef_le (mul_nonneg hAw_nn hC_nn)
        _ = K' * Aw * C := by ring
  · exfalso; omega

set_option maxHeartbeats 1600000 in

theorem secondOrderInterp_lpFiberJet_sup_rs
    (g : SmoothRiemannianMetric I M) (k r : ℕ) (_hk : 1 ≤ k) :
    ∃ K' : ℝ, 1 ≤ K' ∧
      ∀ (m : ℕ) (w : Integral.L2.SmoothCcTensor g r m) (A : ℝ), 0 ≤ A →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g r m x (w.toSection x) ≤ A ^ 2) →
        ((∫ x, (riemannianFiberNormSq (I := I) (M := M) g r (m + 1) x
              ((covGrad (I := I) (M := M) g r m w).toSection x)) ^ ((k : ℝ) / 1)
            ∂(Integral.Measure.riemannianVolumeMeasure I M g)) ^ ((1 : ℝ) / (2 * k))) ^ 2 ≤
          K' * A *
            ((∫ x, (riemannianFiberNormSq (I := I) (M := M) g r (m + 1 + 1) x
                  ((covGrad (I := I) (M := M) g r (m + 1)
                    (covGrad (I := I) (M := M) g r m w)).toSection x)) ^ ((k : ℝ) / 2)
                ∂(Integral.Measure.riemannianVolumeMeasure I M g)) ^ ((2 : ℝ) / (2 * k))) := by
  classical
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one _hk)
  refine ⟨max (2 * ((k : ℝ) - 1) + Real.sqrt (Module.finrank ℝ E : ℝ)) 1, le_max_right _ _, ?_⟩
  intro m w A hA hsup
  set μ : MeasureTheory.Measure M := Integral.Measure.riemannianVolumeMeasure I M g with hμ
  haveI : MeasureTheory.IsFiniteMeasure μ :=
    Integral.Measure.riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  set K' : ℝ := max (2 * ((k : ℝ) - 1) + Real.sqrt (Module.finrank ℝ E : ℝ)) 1 with hK'def
  set b : M → ℝ := fun x => riemannianFiberNormSq (I := I) (M := M) g r (m + 1) x
    ((covGrad (I := I) (M := M) g r m w).toSection x) with hb_def
  set c : M → ℝ := fun x => riemannianFiberNormSq (I := I) (M := M) g r (m + 1 + 1) x
    ((covGrad (I := I) (M := M) g r (m + 1) (covGrad (I := I) (M := M) g r m w)).toSection x)
    with hc_def
  have hb0 : ∀ x, 0 ≤ b x := fun x =>
    riemannianFiberNormSq_nonneg (I := I) (M := M) g r (m + 1) x _
  have hc0 : ∀ x, 0 ≤ c x := fun x =>
    riemannianFiberNormSq_nonneg (I := I) (M := M) g r (m + 1 + 1) x _
  have hbc : Continuous b :=
    continuous_riemannianFiberNormSq_section (I := I) (M := M) g r (m + 1) (covGrad (I := I) (M := M) g r m w)
  have hcc : Continuous c :=
    continuous_riemannianFiberNormSq_section (I := I) (M := M) g r (m + 1 + 1)
      (covGrad (I := I) (M := M) g r (m + 1) (covGrad (I := I) (M := M) g r m w))
  set Ib : ℝ := ∫ x, b x ^ ((k : ℝ) / 1) ∂μ with hIb_def
  set Ic : ℝ := ∫ x, c x ^ ((k : ℝ) / 2) ∂μ with hIc_def
  have hIb_nn : 0 ≤ Ib := MeasureTheory.integral_nonneg (fun x => Real.rpow_nonneg (hb0 x) _)
  have hIc_nn : 0 ≤ Ic := MeasureTheory.integral_nonneg (fun x => Real.rpow_nonneg (hc0 x) _)
  set C : ℝ := Ic ^ ((2 : ℝ) / (2 * k)) with hC_def
  have hC_nn : 0 ≤ C := Real.rpow_nonneg hIc_nn _

  have hIBP := weightedCovIBP_lpFiberJet_sup_rs (I := I) (M := M) g k m r _hk w A hA hsup

  have hk1 : (k : ℝ) / 1 = (k : ℝ) := by norm_num
  have hLHS_sq : (Ib ^ ((1 : ℝ) / (2 * k))) ^ 2 = Ib ^ ((1 : ℝ) / k) := by
    have hexp : (1 : ℝ) / (2 * k) * ((2 : ℕ) : ℝ) = (1 : ℝ) / k := by push_cast; ring
    rw [← Real.rpow_natCast (Ib ^ ((1 : ℝ) / (2 * k))) 2, ← Real.rpow_mul hIb_nn, hexp]

  have hC_eq : C = Ic ^ ((1 : ℝ) / k) := by
    rw [hC_def]; congr 1; rw [eq_div_iff (by positivity)]; field_simp
  rw [hLHS_sq]

  set J : ℝ := ∫ x, b x ^ ((k : ℝ) - 1) * c x ^ (1 / 2 : ℝ) ∂μ with hJ_def
  have hJ_nn : 0 ≤ J := MeasureTheory.integral_nonneg (fun x =>
    mul_nonneg (Real.rpow_nonneg (hb0 x) _) (Real.rpow_nonneg (hc0 x) _))

  set D : ℝ := 2 * ((k : ℝ) - 1) + Real.sqrt (Module.finrank ℝ E : ℝ) with hD_def
  have hsqrt_nn : (0 : ℝ) ≤ Real.sqrt (Module.finrank ℝ E : ℝ) := Real.sqrt_nonneg _
  have hkm1_nn : (0 : ℝ) ≤ (k : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast _hk
    linarith
  have hD_nn : 0 ≤ D := by rw [hD_def]; nlinarith [hkm1_nn, hsqrt_nn]

  have hIBP' : Ib ≤ D * A * J := by
    rw [hIb_def, hJ_def, hD_def]; exact hIBP

  have hJ_bound : J ≤ Ib ^ (((k : ℝ) - 1) / k) * C := by
    rcases eq_or_lt_of_le _hk with hk_eq | hk_gt
    · have hk1' : (k : ℝ) = 1 := by exact_mod_cast hk_eq.symm
      have hb0pow : ∀ x, b x ^ ((k : ℝ) - 1) = 1 := by
        intro x; rw [hk1']; norm_num
      rw [hJ_def]
      simp_rw [hb0pow, one_mul]
      rw [hk1']
      simp only [sub_self, zero_div, Real.rpow_zero, one_mul]

      have hCeq1 : C = ∫ x, c x ^ (1 / 2 : ℝ) ∂μ := by
        rw [hC_def, hIc_def, hk1']
        norm_num
      rw [hCeq1]
    · have hk2R : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk_gt
      have hkm1 : 0 < (k : ℝ) - 1 := by linarith
      set β : ℝ := (k : ℝ) / ((k : ℝ) - 1) with hβ_def
      have hβ0 : 0 < β := by rw [hβ_def]; positivity
      have hconj : β.HolderConjugate (k : ℝ) := by
        refine Real.holderConjugate_iff.mpr ⟨?_, ?_⟩
        · rw [hβ_def, one_lt_div hkm1]; linarith
        · rw [hβ_def, inv_div, inv_eq_one_div, div_add_div _ _ (ne_of_gt hkR) (ne_of_gt hkR),
            div_eq_one_iff_eq (by positivity)]
          ring

      have hf2c : Continuous (fun x => b x ^ ((k : ℝ) - 1)) :=
        hbc.rpow_const (fun _ => Or.inr (le_of_lt hkm1))
      have hf3c : Continuous (fun x => c x ^ (1 / 2 : ℝ)) :=
        hcc.rpow_const (fun _ => Or.inr (by norm_num))
      have hf2mem : MeasureTheory.MemLp (fun x => b x ^ ((k : ℝ) - 1)) (ENNReal.ofReal β) μ :=
        hf2c.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      have hf3mem : MeasureTheory.MemLp (fun x => c x ^ (1 / 2 : ℝ)) (ENNReal.ofReal (k : ℝ)) μ :=
        hf3c.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      have hH := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) hconj
        (f := fun x => b x ^ ((k : ℝ) - 1)) (g := fun x => c x ^ (1 / 2 : ℝ))
        (MeasureTheory.ae_of_all _ (fun x => Real.rpow_nonneg (hb0 x) _))
        (MeasureTheory.ae_of_all _ (fun x => Real.rpow_nonneg (hc0 x) _)) hf2mem hf3mem

      have hβcancel : ((k : ℝ) - 1) * β = (k : ℝ) := by
        rw [hβ_def, ← mul_div_assoc, mul_comm, mul_div_assoc, div_self (ne_of_gt hkm1), mul_one]
      have hpow2 : ∀ x, (b x ^ ((k : ℝ) - 1)) ^ β = b x ^ ((k : ℝ) / 1) := by
        intro x; rw [← Real.rpow_mul (hb0 x), hβcancel, hk1]
      have hpow3 : ∀ x, (c x ^ (1 / 2 : ℝ)) ^ (k : ℝ) = c x ^ ((k : ℝ) / 2) := by
        intro x; rw [← Real.rpow_mul (hc0 x)]; congr 1; ring
      rw [MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ hpow2),
          MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ hpow3)] at hH

      have hinvβ : (1 : ℝ) / β = ((k : ℝ) - 1) / k := by rw [hβ_def, one_div_div]
      have hinvk : (1 : ℝ) / (k : ℝ) = (2 : ℝ) / (2 * k) := by
        rw [eq_div_iff (by positivity)]; field_simp
      rw [hinvβ, hinvk] at hH

      rw [show (∫ x, b x ^ ((k : ℝ) / 1) ∂μ) = Ib from hIb_def.symm,
          show (∫ x, c x ^ ((k : ℝ) / 2) ∂μ) = Ic from hIc_def.symm,
          ← hC_def] at hH
      rw [hJ_def]
      exact hH

  have hcoef_le : D ≤ K' := by rw [hD_def]; exact le_max_left _ _
  have hAC_nn : 0 ≤ A * C := mul_nonneg hA hC_nn

  have hsum_k : (1 : ℝ) / k + ((k : ℝ) - 1) / k = 1 := by
    rw [← add_div, show (1 : ℝ) + ((k : ℝ) - 1) = (k : ℝ) from by ring, div_self (ne_of_gt hkR)]
  rcases eq_or_lt_of_le hIb_nn with hIb0 | hIbpos
  · rw [← hIb0, Real.zero_rpow (by positivity)]
    positivity
  · have hIbβ_pos : 0 < Ib ^ (((k : ℝ) - 1) / k) := Real.rpow_pos_of_pos hIbpos _
    have hIb_split : Ib = Ib ^ ((1 : ℝ) / k) * Ib ^ (((k : ℝ) - 1) / k) := by
      rw [← Real.rpow_add hIbpos, hsum_k, Real.rpow_one]
    have hchain : Ib ^ ((1 : ℝ) / k) * Ib ^ (((k : ℝ) - 1) / k)
        ≤ (D * (A * C)) * Ib ^ (((k : ℝ) - 1) / k) := by
      rw [← hIb_split]
      calc Ib ≤ D * A * J := hIBP'
        _ ≤ D * A * (Ib ^ (((k : ℝ) - 1) / k) * C) := by
            apply mul_le_mul_of_nonneg_left hJ_bound
            exact mul_nonneg hD_nn hA
        _ = (D * (A * C)) * Ib ^ (((k : ℝ) - 1) / k) := by ring
    have hcancel : Ib ^ ((1 : ℝ) / k) ≤ D * (A * C) :=
      le_of_mul_le_mul_right hchain hIbβ_pos
    calc Ib ^ ((1 : ℝ) / k) ≤ D * (A * C) := hcancel
      _ ≤ K' * (A * C) := mul_le_mul_of_nonneg_right hcoef_le hAC_nn
      _ = K' * A * C := by ring

end GeneralValenceRS

end DifferentialGeometry.Analysis.Sobolev.Tensor

end
