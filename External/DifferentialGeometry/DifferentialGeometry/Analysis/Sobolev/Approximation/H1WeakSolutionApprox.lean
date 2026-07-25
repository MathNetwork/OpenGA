import DifferentialGeometry.Analysis.Sobolev.Approximation.SmoothApproximationConstruction
import DifferentialGeometry.Analysis.Sobolev.Solutions.WeakSolution
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Density

noncomputable section

open MeasureTheory Metric Filter Topology Set Function
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
open DifferentialGeometry.Analysis.Sobolev.NirenbergNonSmooth
open DifferentialGeometry.Analysis.Sobolev.H2NonSmoothDirect
open scoped ENNReal NNReal Convolution Pointwise BigOperators

namespace DifferentialGeometry.Analysis.Sobolev.H1WeakSolutionApprox

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in

private lemma mollifyEps_eq_convolution_swap
    {ε : ℝ} (hε : 0 < ε) (u : E → ℝ) (x : E) :
    mollifyEps (d := d) hε u x =
      (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)]
        mollifierEps (d := d) hε) x := by
  classical
  unfold mollifyEps
  rw [convolution_lsmul, convolution_lsmul_swap]
  refine integral_congr_ae ?_
  filter_upwards with t
  rw [smul_eq_mul, smul_eq_mul, mul_comm]

omit [NeZero d] in
theorem mollifyEps_partial_eq_mollifyEps_weakPartial
    {ε : ℝ} (hε : 0 < ε)
    {u g : E → ℝ} {j : Fin d}
    (hu_loc : LocallyIntegrable u (volume : Measure E))
    (hweak : DeGiorgi.HasWeakPartialDeriv (d := d) j g u Set.univ) (x : E) :
    (fderiv ℝ (mollifyEps (d := d) hε u) x)
        (EuclideanSpace.single j 1) =
      mollifyEps (d := d) hε g x := by
  classical
  have hη_smooth : ContDiff ℝ (⊤ : ℕ∞) (mollifierEps (d := d) hε) :=
    mollifierEps_smooth hε
  have hη_C1 : ContDiff ℝ 1 (mollifierEps (d := d) hε) :=
    hη_smooth.of_le (by norm_cast)
  have hη_compact : HasCompactSupport (mollifierEps (d := d) hε) :=
    mollifierEps_compactSupport hε
  have hderiv : HasFDerivAt
      (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)]
        mollifierEps (d := d) hε)
      ((u ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).precompR E,
        (volume : Measure E)] fderiv ℝ (mollifierEps (d := d) hε)) x) x :=
    hη_compact.hasFDerivAt_convolution_right
      (L := ContinuousLinearMap.lsmul ℝ ℝ) hu_loc hη_C1 x
  have hpartial_uη :
      (fderiv ℝ (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)]
        mollifierEps (d := d) hε) x) (EuclideanSpace.single j 1) =
      (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)]
        (fun y => (fderiv ℝ (mollifierEps (d := d) hε) y)
          (EuclideanSpace.single j 1))) x := by
    rw [hderiv.fderiv]
    exact convolution_precompR_apply (𝕜 := ℝ)
      (L := ContinuousLinearMap.lsmul ℝ ℝ)
      hu_loc (hη_compact.fderiv ℝ)
      (hη_smooth.continuous_fderiv (by simp)) x
        (EuclideanSpace.single j 1)
  have hcomm : mollifyEps (d := d) hε u =
      (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)]
        mollifierEps (d := d) hε) := by
    funext y
    exact mollifyEps_eq_convolution_swap hε u y
  rw [hcomm]
  rw [hpartial_uη]
  have h_swap_conv : ∀ y : E,
      (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)]
        (fun z => (fderiv ℝ (mollifierEps (d := d) hε) z)
          (EuclideanSpace.single j 1))) y =
      ((fun z => (fderiv ℝ (mollifierEps (d := d) hε) z)
          (EuclideanSpace.single j 1))
        ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] u) y := by
    intro y
    rw [convolution_lsmul, convolution_lsmul_swap]
    refine integral_congr_ae ?_
    filter_upwards with t
    rw [smul_eq_mul, smul_eq_mul, mul_comm]
  rw [h_swap_conv x]
  have hη_smooth' : ContDiff ℝ (⊤ : ℕ∞) (mollifierEps (d := d) hε) :=
    mollifierEps_smooth hε
  have h_ibp :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.convolution_fderiv_eq_convolution_weakPartial_univ
      (d := d) (i := j) (g := g) (u := u) hweak hη_smooth' hη_compact x
  rw [h_ibp]
  rfl

omit [NeZero d] in
theorem eLpNorm_mollifyEps_le
    {ε : ℝ} (hε : 0 < ε) {u : E → ℝ}
    (hu : MemLp u 2 (volume : Measure E)) :
    eLpNorm (mollifyEps (d := d) hε u) 2 (volume : Measure E) ≤
      eLpNorm u 2 (volume : Measure E) := by
  classical
  have hmem_p : MemLp u (ENNReal.ofReal 2) (volume : Measure E) := by
    have h_eq : (ENNReal.ofReal 2 : ℝ≥0∞) = (2 : ℝ≥0∞) := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_cast]
      rw [show (2 : ℝ≥0∞) = ((2 : ℕ) : ℝ≥0∞) from by norm_cast]
      exact ENNReal.ofReal_natCast 2
    rw [h_eq]; exact hu
  set ψ : E → ℝ := mollifierEps (d := d) hε with hψ_def
  have hψ_int : ∫ y, ψ y ∂(volume : Measure E) = 1 := mollifierEps_integral_eq_one hε
  have hψ_nn : ∀ y, 0 ≤ ψ y := mollifierEps_nonneg hε
  have hψ_integrable : Integrable ψ (volume : Measure E) := mollifierEps_integrable hε
  have hψ_cont : Continuous ψ := mollifierEps_continuous hε
  have hψ_compact : HasCompactSupport ψ := mollifierEps_compactSupport hε
  set C : ℝ≥0∞ := eLpNorm u 2 (volume : Measure E) with hC_def
  have hu_aestrong : AEStronglyMeasurable u (volume : Measure E) := hu.aestronglyMeasurable
  have h_pt_jensen : ∀ x : E,
      ‖(ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] u) x‖ ^ (2 : ℝ) ≤
      ((fun y => ‖u y‖ ^ (2 : ℝ))
          ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] ψ) x := by
    intro x
    set h_norm_sq : E → ℝ := fun y => ‖u y‖ ^ (2 : ℝ) with hh_norm_sq_def
    set ρ : E → ℝ≥0∞ := fun y => ENNReal.ofReal (ψ y) with hρ_def
    set ν : Measure E := (volume : Measure E).withDensity ρ with hν_def
    have hρ_meas : Measurable ρ := hψ_cont.measurable.ennreal_ofReal
    have hρ_lt_top : ∀ᵐ y ∂(volume : Measure E), ρ y < ∞ := by
      filter_upwards with y
      simp [ρ]
    have hν_prob : IsProbabilityMeasure ν := by
      refine ⟨?_⟩
      rw [hν_def, withDensity_apply _ MeasurableSet.univ]
      rw [Measure.restrict_univ]
      rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hψ_integrable
        (Filter.Eventually.of_forall hψ_nn)]
      rw [hψ_int]
      simp
    have hu_loc : LocallyIntegrable u (volume : Measure E) :=
      hu.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have hce_u : ConvolutionExistsAt ψ u x
        (ContinuousLinearMap.lsmul ℝ ℝ) (volume : Measure E) :=
      hψ_compact.convolutionExists_left
        (L := ContinuousLinearMap.lsmul ℝ ℝ) hψ_cont hu_loc x
    have hconv_ν :
        ((ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] u) x) =
          ∫ y, u (x - y) ∂ν := by
      rw [hν_def]
      rw [integral_withDensity_eq_integral_toReal_smul hρ_meas hρ_lt_top]
      rw [MeasureTheory.convolution_def]
      refine integral_congr_ae ?_
      filter_upwards with y
      simp [ρ, ψ, ContinuousLinearMap.lsmul_apply, smul_eq_mul, hψ_nn y]
    have h_norm_sq_int_vol : Integrable (fun y => (ρ y).toReal * ‖u (x - y)‖) (volume : Measure E) := by
      refine hce_u.integrable.norm.congr ?_
      filter_upwards with y
      simp [ρ, ψ, ContinuousLinearMap.lsmul_apply, smul_eq_mul, hψ_nn y]
    have h_norm_int : Integrable (fun y => ‖u (x - y)‖) ν := by
      exact (MeasureTheory.integrable_withDensity_iff_integrable_smul' hρ_meas hρ_lt_top).2 <| by
        simpa [ρ, ψ, hψ_nn] using h_norm_sq_int_vol
    have hu_sq_loc : LocallyIntegrable (fun y => ‖u y‖ ^ (2 : ℝ)) (volume : Measure E) := by
      have hh_int : Integrable (fun y => ‖u y‖ ^ (2 : ℝ)) (volume : Measure E) := by
        have := hu.integrable_norm_rpow (p := 2) (by norm_num : (2 : ℝ≥0∞) ≠ 0)
          (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
        simpa using this
      exact hh_int.locallyIntegrable
    have hce_h : ConvolutionExistsAt ψ h_norm_sq x
        (ContinuousLinearMap.lsmul ℝ ℝ) (volume : Measure E) :=
      hψ_compact.convolutionExists_left
        (L := ContinuousLinearMap.lsmul ℝ ℝ) hψ_cont hu_sq_loc x
    have h_rpow_int_vol :
        Integrable (fun y => (ρ y).toReal * ‖u (x - y)‖ ^ (2 : ℝ)) (volume : Measure E) := by
      refine hce_h.integrable.congr ?_
      filter_upwards with y
      simp [ρ, ψ, h_norm_sq, ContinuousLinearMap.lsmul_apply, smul_eq_mul,
        hψ_nn y]
    have h_rpow_int : Integrable (fun y => ‖u (x - y)‖ ^ (2 : ℝ)) ν := by
      exact (MeasureTheory.integrable_withDensity_iff_integrable_smul' hρ_meas hρ_lt_top).2 <| by
        simpa [ρ, ψ, hψ_nn] using h_rpow_int_vol
    have hnorm_le_int : ‖((ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] u) x)‖ ≤
        ∫ y, ‖u (x - y)‖ ∂ν := by
      rw [hconv_ν]
      exact MeasureTheory.norm_integral_le_integral_norm _
    have hJensen_ν : (∫ y, ‖u (x - y)‖ ∂ν) ^ (2 : ℝ) ≤ ∫ y, ‖u (x - y)‖ ^ (2 : ℝ) ∂ν := by
      have hconv : ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun t : ℝ => t ^ (2 : ℝ)) :=
        convexOn_rpow (by norm_num : (1 : ℝ) ≤ 2)
      have hcont : ContinuousOn (fun t : ℝ => t ^ (2 : ℝ)) (Set.Ici (0 : ℝ)) :=
        continuousOn_id.rpow_const (fun t _ => Or.inr (by norm_num : (0 : ℝ) ≤ 2))
      have hmem : ∀ᵐ y ∂ν, ‖u (x - y)‖ ∈ Set.Ici (0 : ℝ) := by
        filter_upwards with y
        exact norm_nonneg _
      exact hconv.map_integral_le hcont isClosed_Ici hmem h_norm_int h_rpow_int
    calc
      ‖((ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] u) x)‖ ^ (2 : ℝ)
          ≤ (∫ y, ‖u (x - y)‖ ∂ν) ^ (2 : ℝ) :=
            Real.rpow_le_rpow (norm_nonneg _) hnorm_le_int (by norm_num : (0 : ℝ) ≤ 2)
      _ ≤ ∫ y, ‖u (x - y)‖ ^ (2 : ℝ) ∂ν := hJensen_ν
      _ = ∫ y, ψ y * ‖u (x - y)‖ ^ (2 : ℝ) ∂(volume : Measure E) := by
            rw [hν_def]
            rw [integral_withDensity_eq_integral_toReal_smul hρ_meas hρ_lt_top]
            refine integral_congr_ae ?_
            filter_upwards with y
            simp [ρ, ψ, hψ_nn y]
      _ = ((fun y => ‖u y‖ ^ (2 : ℝ))
            ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] ψ) x := by
            have hMP : MeasurePreserving (fun y : E => x - y) (volume : Measure E)
                (volume : Measure E) := by
              have h_neg : MeasurePreserving (fun t : E => -t) (volume : Measure E)
                  (volume : Measure E) :=
                Measure.measurePreserving_neg (volume : Measure E)
              have h_addL : MeasurePreserving (fun t : E => x + t) (volume : Measure E)
                  (volume : Measure E) :=
                measurePreserving_add_left (volume : Measure E) x
              have heq : (fun y : E => x - y) = (fun y : E => x + (-y)) := by
                funext y; rw [sub_eq_add_neg]
              rw [heq]; exact h_addL.comp h_neg
            have h_subst : ∫ y, ψ y * ‖u (x - y)‖ ^ (2 : ℝ) ∂(volume : Measure E) =
                ∫ t, ψ (x - t) * ‖u (x - (x - t))‖ ^ (2 : ℝ) ∂(volume : Measure E) :=
              (hMP.integral_comp (Homeomorph.subLeft x).measurableEmbedding
                (fun y : E => ψ y * ‖u (x - y)‖ ^ (2 : ℝ))).symm
            rw [h_subst]
            have h_rearr : ∀ t : E,
                ψ (x - t) * ‖u (x - (x - t))‖ ^ (2 : ℝ) =
                ‖u t‖ ^ (2 : ℝ) * ψ (x - t) := by
              intro t
              have h_simp : x - (x - t) = t := by abel
              rw [h_simp]
              ring
            rw [convolution_def]
            refine integral_congr_ae ?_
            filter_upwards with t
            rw [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
            exact h_rearr t
  have hu_loc : LocallyIntegrable u (volume : Measure E) :=
    hu.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hu_sq_int : Integrable (fun y => ‖u y‖ ^ (2 : ℝ)) (volume : Measure E) := by
    have := hu.integrable_norm_rpow (p := 2) (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
    simpa using this
  have hconv_cont : Continuous
      (ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] u :
        E → ℝ) :=
    hψ_compact.continuous_convolution_left (L := ContinuousLinearMap.lsmul ℝ ℝ)
      hψ_cont hu_loc
  have hh_conv_int : Integrable
      ((fun y => ‖u y‖ ^ (2 : ℝ))
        ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] ψ)
      (volume : Measure E) :=
    hu_sq_int.integrable_convolution (L := ContinuousLinearMap.lsmul ℝ ℝ) hψ_integrable
  have hpow_int : Integrable
      (fun x => ‖((ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] u) x)‖
        ^ (2 : ℝ)) (volume : Measure E) := by
    refine Integrable.mono' hh_conv_int ?_ ?_
    · exact (hconv_cont.norm.rpow_const
        (fun _ => Or.inr (by norm_num : (0 : ℝ) ≤ 2))).aestronglyMeasurable
    · filter_upwards with x
      have h_nn :
          0 ≤ ‖((ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] u) x)‖
            ^ (2 : ℝ) :=
        Real.rpow_nonneg (norm_nonneg _) _
      rw [Real.norm_eq_abs, abs_of_nonneg h_nn]
      exact h_pt_jensen x
  have h_int_le :
      ∫ x, ‖((ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] u) x)‖ ^ (2 : ℝ)
        ∂(volume : Measure E) ≤
      ∫ x, ((fun y => ‖u y‖ ^ (2 : ℝ))
        ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] ψ) x
        ∂(volume : Measure E) := by
    refine integral_mono_ae hpow_int hh_conv_int ?_
    filter_upwards with x
    exact h_pt_jensen x
  have h_conv_eq :
      ∫ x, ((fun y => ‖u y‖ ^ (2 : ℝ))
        ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] ψ) x
        ∂(volume : Measure E) =
      ∫ x, ‖u x‖ ^ (2 : ℝ) ∂(volume : Measure E) := by
    have h := MeasureTheory.integral_convolution
      (L := ContinuousLinearMap.lsmul ℝ ℝ) (μ := (volume : Measure E))
      (ν := (volume : Measure E)) hu_sq_int hψ_integrable
    rw [h]
    simp [ContinuousLinearMap.lsmul_apply, smul_eq_mul, hψ_int]
  have hconv_memLp : MemLp (ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] u : E → ℝ)
      2 (volume : Measure E) := by
    refine ⟨hconv_cont.aestronglyMeasurable, ?_⟩
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (μ := (volume : Measure E))
      (f := (ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] u : E → ℝ))
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)]
    have h_2_toReal : ((2 : ℝ≥0∞).toReal) = (2 : ℝ) := by norm_num
    rw [h_2_toReal]
    have h_lint_finite : ∫⁻ x, ‖((ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] u) x)‖ₑ
        ^ (2 : ℝ) ∂(volume : Measure E) < ∞ := by
      have h_pt_lint : ∀ x : E,
          ‖((ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] u) x)‖ₑ
            ^ (2 : ℝ) =
          ENNReal.ofReal (‖((ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] u) x)‖
            ^ (2 : ℝ)) := by
        intro x
        rw [← ofReal_norm_eq_enorm,
          ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)]
      have h_lint_pt :
          (fun x => ‖((ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] u) x)‖ₑ
            ^ (2 : ℝ)) =
          (fun x => ENNReal.ofReal (‖((ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] u) x)‖
            ^ (2 : ℝ))) := by
        funext x
        exact h_pt_lint x
      rw [h_lint_pt]
      rw [← ofReal_integral_eq_lintegral_ofReal hpow_int
        (Filter.Eventually.of_forall (fun x => Real.rpow_nonneg (norm_nonneg _) _))]
      exact ENNReal.ofReal_lt_top
    refine ENNReal.rpow_lt_top_of_nonneg ?_ h_lint_finite.ne
    norm_num
  have h_2_ne_zero : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h_2_ne_top : (2 : ℝ≥0∞) ≠ ∞ := by norm_num
  have h_eLp_lhs :
      eLpNorm (ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] u : E → ℝ)
        2 (volume : Measure E) =
      ENNReal.ofReal ((∫ x,
        ‖((ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] u) x)‖ ^ (2 : ℝ)
          ∂(volume : Measure E)) ^ ((2 : ℝ)⁻¹)) := by
    have h := hconv_memLp.eLpNorm_eq_integral_rpow_norm h_2_ne_zero h_2_ne_top
    have h_2_toReal : ((2 : ℝ≥0∞).toReal) = (2 : ℝ) := by norm_num
    rw [h_2_toReal] at h
    exact h
  have h_eLp_rhs :
      eLpNorm u 2 (volume : Measure E) =
      ENNReal.ofReal ((∫ x, ‖u x‖ ^ (2 : ℝ) ∂(volume : Measure E)) ^ ((2 : ℝ)⁻¹)) := by
    have h := hu.eLpNorm_eq_integral_rpow_norm h_2_ne_zero h_2_ne_top
    have h_2_toReal : ((2 : ℝ≥0∞).toReal) = (2 : ℝ) := by norm_num
    rw [h_2_toReal] at h
    exact h
  have hcomm : mollifyEps (d := d) hε u =
      (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)]
        mollifierEps (d := d) hε) := by
    funext y
    exact mollifyEps_eq_convolution_swap hε u y
  rw [hcomm]
  have hcomm_conv : ∀ y : E,
      (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)]
        mollifierEps (d := d) hε) y =
      (mollifierEps (d := d) hε
        ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] u) y := by
    intro y
    rw [convolution_lsmul, convolution_lsmul_swap]
    refine integral_congr_ae ?_
    filter_upwards with t
    rw [smul_eq_mul, smul_eq_mul, mul_comm]
  have hfun_eq :
      (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)]
        mollifierEps (d := d) hε) =
      (mollifierEps (d := d) hε
        ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] u) := by
    funext y; exact hcomm_conv y
  rw [hfun_eq]
  change eLpNorm (mollifierEps (d := d) hε
        ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] u) 2
      (volume : Measure E) ≤ eLpNorm u 2 (volume : Measure E)
  rw [h_eLp_lhs, h_eLp_rhs]
  refine ENNReal.ofReal_le_ofReal ?_
  have h_int_combined :
      ∫ x, ‖((ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] u) x)‖ ^ (2 : ℝ)
        ∂(volume : Measure E) ≤
      ∫ x, ‖u x‖ ^ (2 : ℝ) ∂(volume : Measure E) :=
    h_int_le.trans (le_of_eq h_conv_eq)
  refine Real.rpow_le_rpow ?_ h_int_combined ?_
  · exact integral_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _
  · exact inv_nonneg.mpr (by norm_num : (0 : ℝ) ≤ 2)

omit [NeZero d] in
theorem eLpNorm_partial_mollifyEps_le_of_weakPartial_univ
    {ε : ℝ} (hε : 0 < ε)
    {u g : E → ℝ} {j : Fin d}
    (hu_loc : LocallyIntegrable u (volume : Measure E))
    (hg : MemLp g 2 (volume : Measure E))
    (hweak : DeGiorgi.HasWeakPartialDeriv (d := d) j g u Set.univ) :
    eLpNorm
      (fun x => (fderiv ℝ (mollifyEps (d := d) hε u) x)
        (EuclideanSpace.single j 1)) 2 (volume : Measure E) ≤
      eLpNorm g 2 (volume : Measure E) := by
  have h_pointwise : (fun x : E =>
      (fderiv ℝ (mollifyEps (d := d) hε u) x)
        (EuclideanSpace.single j 1)) =
      (fun x : E => mollifyEps (d := d) hε g x) := by
    funext x
    exact mollifyEps_partial_eq_mollifyEps_weakPartial hε hu_loc hweak x
  rw [h_pointwise]
  exact eLpNorm_mollifyEps_le hε hg

structure H1WeakSolutionData
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω) (u f : E → ℝ) where

  hu_l2 : MemLp u 2 (volume : Measure E)

  hf_l2 : MemLp f 2 (volume : Measure E)

  weakPartial : Fin d → (E → ℝ)
  weakPartial_l2 : ∀ j, MemLp (weakPartial j) 2 (volume : Measure E)
  weakPartial_isWeak : ∀ j,
    DeGiorgi.HasWeakPartialDeriv (d := d) j (weakPartial j) u Set.univ

  isWeakSolution : B.IsWeakSolution u f

  fseq_l2_bound : ℝ
  fseq_l2_bound_nn : 0 ≤ fseq_l2_bound
  fseq_l2_bounded : ∀ n : ℕ,
    eLpNorm (B.classicalApply
      (mollifyEps (d := d) (show (0 : ℝ) < 1 / ((n : ℝ) + 2) by positivity) u))
      2 (volume : Measure E) ≤ ENNReal.ofReal fseq_l2_bound

omit [NeZero d] in
private lemma contDiff_mollifyEps_of_memLp_two
    {ε : ℝ} (hε : 0 < ε) {u : E → ℝ}
    (hu : MemLp u 2 (volume : Measure E)) :
    ContDiff ℝ (⊤ : ℕ∞) (mollifyEps (d := d) hε u) :=
  mollifyEps_contDiff hε (hu.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2))

private lemma is_smooth_weak_sol_mollifyEps
    {Ω : Set E} (hΩ : IsOpen Ω) (B : SmoothEllipticBilinearForm d Ω)
    {u : E → ℝ} (hu : MemLp u 2 (volume : Measure E))
    {ε : ℝ} (hε : 0 < ε) :
    B.IsSmoothWeakSolution
      (mollifyEps (d := d) hε u)
      (B.classicalApply (mollifyEps (d := d) hε u)) :=
  SmoothEllipticBilinearForm.mollifyEps_isSmoothWeakSolution_classicalApply
    (d := d) hΩ B (hu.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)) hε

omit [NeZero d] in

private lemma memLp_two_restrict_of_memLp_two
    {f : E → ℝ} (hf : MemLp f 2 (volume : Measure E)) (S : Set E) :
    MemLp f 2 (volume.restrict S) :=
  hf.restrict S

omit [NeZero d] in

private lemma integral_sq_le_eLpNorm_sq
    {f : E → ℝ} (hf : MemLp f 2 (volume : Measure E))
    {S : Set E} (_hS_open : IsOpen S) :
    ∫ x in S, (f x) ^ 2 ∂(volume : Measure E) ≤
      ((eLpNorm f 2 (volume : Measure E)).toReal) ^ 2 := by
  classical
  have hf_sq_int : Integrable (fun x => (f x) ^ 2) (volume : Measure E) := by
    have h_norm_eq : ∀ x : E, (f x) ^ 2 = ‖f x‖ ^ (2 : ℝ) := by
      intro x
      rw [Real.norm_eq_abs, ← sq_abs, ← Real.rpow_natCast, Nat.cast_ofNat]
    have h_funeq : (fun x : E => (f x) ^ 2) = (fun x : E => ‖f x‖ ^ (2 : ℝ)) := by
      funext x; exact h_norm_eq x
    rw [h_funeq]
    have := hf.integrable_norm_rpow (p := 2) (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
    simpa using this
  have h_int_le_E :
      ∫ x in S, (f x) ^ 2 ∂(volume : Measure E) ≤
      ∫ x, (f x) ^ 2 ∂(volume : Measure E) := by
    refine integral_mono_measure Measure.restrict_le_self
      (Filter.Eventually.of_forall (fun x => sq_nonneg _)) hf_sq_int
  have h_int_E : ∫ x, (f x) ^ 2 ∂(volume : Measure E) =
      ((eLpNorm f 2 (volume : Measure E)).toReal) ^ 2 := by
    have h_norm_eq : ∀ x : E, (f x) ^ 2 = ‖f x‖ ^ (2 : ℝ) := by
      intro x
      rw [Real.norm_eq_abs, ← sq_abs, ← Real.rpow_natCast, Nat.cast_ofNat]
    have h_funeq_int : ∫ x, (f x) ^ 2 ∂(volume : Measure E) =
        ∫ x, ‖f x‖ ^ (2 : ℝ) ∂(volume : Measure E) := by
      refine integral_congr_ae ?_
      filter_upwards with x using h_norm_eq x
    rw [h_funeq_int]
    have h_2_ne_zero : (2 : ℝ≥0∞) ≠ 0 := by norm_num
    have h_2_ne_top : (2 : ℝ≥0∞) ≠ ∞ := by norm_num
    have h_eLp := hf.eLpNorm_eq_integral_rpow_norm h_2_ne_zero h_2_ne_top
    have h_2_toReal : ((2 : ℝ≥0∞).toReal) = (2 : ℝ) := by norm_num
    rw [h_2_toReal] at h_eLp
    have h_int_nn : 0 ≤ ∫ x, ‖f x‖ ^ (2 : ℝ) ∂(volume : Measure E) :=
      integral_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _
    have h_pow_nn : 0 ≤ (∫ x, ‖f x‖ ^ (2 : ℝ) ∂(volume : Measure E)) ^ ((2 : ℝ)⁻¹) :=
      Real.rpow_nonneg h_int_nn _
    have hh : (eLpNorm f 2 (volume : Measure E)).toReal =
        (∫ x, ‖f x‖ ^ (2 : ℝ) ∂(volume : Measure E)) ^ ((2 : ℝ)⁻¹) := by
      rw [h_eLp]
      exact ENNReal.toReal_ofReal h_pow_nn
    rw [hh]
    rw [← Real.rpow_two]
    rw [← Real.rpow_mul h_int_nn]
    norm_num
  rw [h_int_E] at h_int_le_E
  exact h_int_le_E

theorem exists_smoothApproximation_of_h1WeakSolutionData
    {Ω : Set E} (hΩ : IsOpen Ω) (B : SmoothEllipticBilinearForm d Ω)
    {u f : E → ℝ}
    (D : H1WeakSolutionData B u f) :
    Nonempty (SmoothApproximation B u f) := by
  classical
  set εFun : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 2) with hεFun_def
  have hε_pos : ∀ n, 0 < εFun n := fun n => by
    rw [hεFun_def]
    positivity
  set uSeq : ℕ → E → ℝ := fun n => mollifyEps (d := d) (hε_pos n) u with huSeq_def
  set fSeq : ℕ → E → ℝ := fun n => B.classicalApply (uSeq n) with hfSeq_def
  have huSeq_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (uSeq n) := fun n =>
    contDiff_mollifyEps_of_memLp_two (hε_pos n) D.hu_l2
  have huSeq_cont : ∀ n, Continuous (uSeq n) := fun n => (huSeq_smooth n).continuous
  have hfSeq_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (fSeq n) := fun n =>
    SmoothEllipticBilinearForm.contDiff_classicalApply (d := d) B (huSeq_smooth n)
  have hfSeq_cont : ∀ n, Continuous (fSeq n) := fun n => (hfSeq_smooth n).continuous
  have h_smooth_weak : ∀ n, B.IsSmoothWeakSolution (uSeq n) (fSeq n) := fun n =>
    is_smooth_weak_sol_mollifyEps hΩ B D.hu_l2 (hε_pos n)
  have hgrad_cont : ∀ n, ∀ j : Fin d,
      Continuous (fun x : E => (fderiv ℝ (uSeq n) x)
        (EuclideanSpace.single j 1)) := fun n j =>
    ((huSeq_smooth n).continuous_fderiv (by simp)).clm_apply continuous_const
  have huSeq_l2 : ∀ n, MemLp (uSeq n) 2 (volume : Measure E) := fun n => by
    have h_eLp : eLpNorm (uSeq n) 2 (volume : Measure E) ≤
        eLpNorm u 2 (volume : Measure E) :=
      eLpNorm_mollifyEps_le (hε_pos n) D.hu_l2
    refine ⟨?_, ?_⟩
    · exact (huSeq_cont n).aestronglyMeasurable
    · exact lt_of_le_of_lt h_eLp D.hu_l2.eLpNorm_lt_top
  have hgrad_l2 : ∀ n, ∀ j : Fin d, MemLp
      (fun x : E => (fderiv ℝ (uSeq n) x) (EuclideanSpace.single j 1))
      2 (volume : Measure E) := fun n j => by
    have h_eLp : eLpNorm
        (fun x : E => (fderiv ℝ (uSeq n) x) (EuclideanSpace.single j 1)) 2
        (volume : Measure E) ≤
      eLpNorm (D.weakPartial j) 2 (volume : Measure E) :=
      eLpNorm_partial_mollifyEps_le_of_weakPartial_univ (hε_pos n)
        (D.hu_l2.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2))
        (D.weakPartial_l2 j) (D.weakPartial_isWeak j)
    refine ⟨?_, ?_⟩
    · exact (hgrad_cont n j).aestronglyMeasurable
    · exact lt_of_le_of_lt h_eLp (D.weakPartial_l2 j).eLpNorm_lt_top
  have hfSeq_l2 : ∀ n, MemLp (fSeq n) 2 (volume : Measure E) := fun n => by
    refine ⟨?_, ?_⟩
    · exact (hfSeq_cont n).aestronglyMeasurable
    · have h_bound := D.fseq_l2_bounded n
      have hM_top : ENNReal.ofReal D.fseq_l2_bound ≠ ∞ := ENNReal.ofReal_ne_top
      exact lt_of_le_of_lt h_bound (lt_of_le_of_ne le_top hM_top)
  set DB : ℝ :=
    ((eLpNorm u 2 (volume : Measure E)).toReal) ^ 2 +
      ∑ j : Fin d, ((eLpNorm (D.weakPartial j) 2 (volume : Measure E)).toReal) ^ 2 +
        ((eLpNorm f 2 (volume : Measure E)).toReal) ^ 2 +
        D.fseq_l2_bound ^ 2 with hDB_def
  have hDB_nn : 0 ≤ DB := by
    refine add_nonneg (add_nonneg (add_nonneg (sq_nonneg _) ?_) (sq_nonneg _))
      (sq_nonneg _)
    exact Finset.sum_nonneg (fun j _ => sq_nonneg _)
  have hf_seq_l2_loc : ∀ n, ∀ {S : Set E}, IsCompact (closure S) →
      MemLp (fSeq n) 2 (volume.restrict S) := fun n {S} _ =>
    memLp_two_restrict_of_memLp_two (hfSeq_l2 n) S
  have hu_seq_l2_loc : ∀ n, ∀ {S : Set E}, IsCompact (closure S) →
      MemLp (uSeq n) 2 (volume.restrict S) := fun n {S} _ =>
    memLp_two_restrict_of_memLp_two (huSeq_l2 n) S
  have hgrad_seq_l2_loc : ∀ n, ∀ {S : Set E}, IsCompact (closure S) →
      ∀ j : Fin d, MemLp
        (fun y : E => (fderiv ℝ (uSeq n) y) (EuclideanSpace.single j 1))
        2 (volume.restrict S) := fun n {S} _ j =>
    memLp_two_restrict_of_memLp_two (hgrad_l2 n j) S
  refine ⟨{
    u_seq := uSeq
    f_seq := fSeq
    u_seq_smooth := huSeq_smooth
    is_smooth_weak_sol := h_smooth_weak
    f_seq_l2_loc := hf_seq_l2_loc
    u_seq_l2_loc := hu_seq_l2_loc
    grad_seq_l2_loc := hgrad_seq_l2_loc
    data_bound := DB
    data_bound_nn := hDB_nn
    data_integrated_bound := ?_
  }⟩
  intro Ω' hΩ'_open _hΩ'_cc
  refine ⟨1, by norm_num, fun n => ?_⟩
  have h_grad_each : ∀ j : Fin d,
      ∫ y in Ω', ((fderiv ℝ (uSeq n) y) (EuclideanSpace.single j 1)) ^ 2
        ∂(volume : Measure E) ≤
      ((eLpNorm (D.weakPartial j) 2 (volume : Measure E)).toReal) ^ 2 := by
    intro j
    have h_partial_bound := integral_sq_le_eLpNorm_sq (hgrad_l2 n j) hΩ'_open
    refine h_partial_bound.trans ?_
    have h_eLp_bound :
        eLpNorm (fun x : E => (fderiv ℝ (uSeq n) x)
            (EuclideanSpace.single j 1)) 2 (volume : Measure E) ≤
        eLpNorm (D.weakPartial j) 2 (volume : Measure E) :=
      eLpNorm_partial_mollifyEps_le_of_weakPartial_univ (hε_pos n)
        (D.hu_l2.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2))
        (D.weakPartial_l2 j) (D.weakPartial_isWeak j)
    have h_lhs_top : eLpNorm (fun x : E => (fderiv ℝ (uSeq n) x)
        (EuclideanSpace.single j 1)) 2 (volume : Measure E) ≠ ∞ :=
      (hgrad_l2 n j).eLpNorm_ne_top
    have h_rhs_top : eLpNorm (D.weakPartial j) 2 (volume : Measure E) ≠ ∞ :=
      (D.weakPartial_l2 j).eLpNorm_ne_top
    have h_toReal_le := (ENNReal.toReal_le_toReal h_lhs_top h_rhs_top).mpr h_eLp_bound
    have h_lhs_nn : 0 ≤ (eLpNorm (fun x : E => (fderiv ℝ (uSeq n) x)
        (EuclideanSpace.single j 1)) 2 (volume : Measure E)).toReal :=
      ENNReal.toReal_nonneg
    have h_rhs_nn : 0 ≤ (eLpNorm (D.weakPartial j) 2 (volume : Measure E)).toReal :=
      ENNReal.toReal_nonneg
    exact pow_le_pow_left₀ h_lhs_nn h_toReal_le 2
  have h_u_bound :
      ∫ y in Ω', (uSeq n y) ^ 2 ∂(volume : Measure E) ≤
      ((eLpNorm u 2 (volume : Measure E)).toReal) ^ 2 := by
    refine (integral_sq_le_eLpNorm_sq (huSeq_l2 n) hΩ'_open).trans ?_
    have h_eLp_bound : eLpNorm (uSeq n) 2 (volume : Measure E) ≤
        eLpNorm u 2 (volume : Measure E) :=
      eLpNorm_mollifyEps_le (hε_pos n) D.hu_l2
    have h_lhs_top : eLpNorm (uSeq n) 2 (volume : Measure E) ≠ ∞ :=
      (huSeq_l2 n).eLpNorm_ne_top
    have h_rhs_top : eLpNorm u 2 (volume : Measure E) ≠ ∞ :=
      D.hu_l2.eLpNorm_ne_top
    have h_toReal_le := (ENNReal.toReal_le_toReal h_lhs_top h_rhs_top).mpr h_eLp_bound
    have h_lhs_nn : 0 ≤ (eLpNorm (uSeq n) 2 (volume : Measure E)).toReal :=
      ENNReal.toReal_nonneg
    exact pow_le_pow_left₀ h_lhs_nn h_toReal_le 2
  have h_f_bound :
      ∫ y in Ω', (fSeq n y) ^ 2 ∂(volume : Measure E) ≤
      D.fseq_l2_bound ^ 2 := by
    refine (integral_sq_le_eLpNorm_sq (hfSeq_l2 n) hΩ'_open).trans ?_
    have h_eLp_bound : eLpNorm (fSeq n) 2 (volume : Measure E) ≤
        ENNReal.ofReal D.fseq_l2_bound := D.fseq_l2_bounded n
    have h_lhs_top : eLpNorm (fSeq n) 2 (volume : Measure E) ≠ ∞ :=
      (hfSeq_l2 n).eLpNorm_ne_top
    have h_rhs_top : ENNReal.ofReal D.fseq_l2_bound ≠ ∞ := ENNReal.ofReal_ne_top
    have h_toReal_le :
        (eLpNorm (fSeq n) 2 (volume : Measure E)).toReal ≤
          (ENNReal.ofReal D.fseq_l2_bound).toReal :=
      (ENNReal.toReal_le_toReal h_lhs_top h_rhs_top).mpr h_eLp_bound
    rw [ENNReal.toReal_ofReal D.fseq_l2_bound_nn] at h_toReal_le
    have h_lhs_nn : 0 ≤ (eLpNorm (fSeq n) 2 (volume : Measure E)).toReal :=
      ENNReal.toReal_nonneg
    exact pow_le_pow_left₀ h_lhs_nn h_toReal_le 2
  have h_grad_sum_int :
      ∫ y in Ω', ∑ j : Fin d,
          ((fderiv ℝ (uSeq n) y) (EuclideanSpace.single j 1)) ^ 2
        ∂(volume : Measure E) =
      ∑ j : Fin d, ∫ y in Ω',
          ((fderiv ℝ (uSeq n) y) (EuclideanSpace.single j 1)) ^ 2
        ∂(volume : Measure E) := by
    refine integral_finset_sum (μ := (volume : Measure E).restrict Ω') Finset.univ ?_
    intro j _
    have h_norm_eq : ∀ y : E,
        ((fderiv ℝ (uSeq n) y) (EuclideanSpace.single j 1)) ^ 2 =
        ‖((fderiv ℝ (uSeq n) y) (EuclideanSpace.single j 1))‖ ^ (2 : ℝ) := by
      intro y
      rw [Real.norm_eq_abs, ← sq_abs, ← Real.rpow_natCast, Nat.cast_ofNat]
    have h_funeq : (fun y : E =>
        ((fderiv ℝ (uSeq n) y) (EuclideanSpace.single j 1)) ^ 2) =
        (fun y : E =>
        ‖((fderiv ℝ (uSeq n) y) (EuclideanSpace.single j 1))‖ ^ (2 : ℝ)) := by
      funext y; exact h_norm_eq y
    rw [h_funeq]
    have h_int_E : Integrable (fun y : E =>
        ‖((fderiv ℝ (uSeq n) y) (EuclideanSpace.single j 1))‖ ^ (2 : ℝ))
        (volume : Measure E) := by
      have := (hgrad_l2 n j).integrable_norm_rpow
        (p := 2) (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
      simpa using this
    exact h_int_E.restrict
  rw [h_grad_sum_int]
  have h_grad_sum_le :
      ∑ j : Fin d, ∫ y in Ω',
          ((fderiv ℝ (uSeq n) y) (EuclideanSpace.single j 1)) ^ 2
        ∂(volume : Measure E) ≤
      ∑ j : Fin d, ((eLpNorm (D.weakPartial j) 2 (volume : Measure E)).toReal) ^ 2 :=
    Finset.sum_le_sum (fun j _ => h_grad_each j)
  have h_combined :
      (∑ j : Fin d, ∫ y in Ω',
          ((fderiv ℝ (uSeq n) y) (EuclideanSpace.single j 1)) ^ 2
        ∂(volume : Measure E)) +
      (∫ y in Ω', (uSeq n y) ^ 2 ∂(volume : Measure E)) +
      (∫ y in Ω', (fSeq n y) ^ 2 ∂(volume : Measure E)) ≤
      (∑ j : Fin d, ((eLpNorm (D.weakPartial j) 2 (volume : Measure E)).toReal) ^ 2) +
      ((eLpNorm u 2 (volume : Measure E)).toReal) ^ 2 +
      D.fseq_l2_bound ^ 2 := by
    linarith
  refine h_combined.trans ?_
  rw [hDB_def]
  rw [one_mul]
  have h_f_nn : 0 ≤ ((eLpNorm f 2 (volume : Measure E)).toReal) ^ 2 := sq_nonneg _
  linarith

theorem exists_smoothApproximation_of_h1_weak_solution
    {Ω : Set E} (hΩ : IsOpen Ω) (B : SmoothEllipticBilinearForm d Ω)
    {u f : E → ℝ}
    (hu_l2 : MemLp u 2 (volume : Measure E))
    (hu_grad_l2 : ∀ j : Fin d, ∃ g : E → ℝ,
      MemLp g 2 (volume : Measure E) ∧
      DeGiorgi.HasWeakPartialDeriv (d := d) j g u Set.univ)
    (hf_l2 : MemLp f 2 (volume : Measure E))
    (h_weak : B.IsWeakSolution u f)
    {M_F : ℝ} (hMF_nn : 0 ≤ M_F)
    (hMF_bound : ∀ n : ℕ,
      eLpNorm
        (B.classicalApply (mollifyEps (d := d)
          (show (0 : ℝ) < 1 / ((n : ℝ) + 2) by positivity) u))
        2 (volume : Measure E) ≤ ENNReal.ofReal M_F) :
    Nonempty (SmoothApproximation B u f) := by
  classical
  set wp : Fin d → (E → ℝ) := fun j => Classical.choose (hu_grad_l2 j) with hwp_def
  have hwp_l2 : ∀ j, MemLp (wp j) 2 (volume : Measure E) := fun j =>
    (Classical.choose_spec (hu_grad_l2 j)).1
  have hwp_isWeak : ∀ j,
      DeGiorgi.HasWeakPartialDeriv (d := d) j (wp j) u Set.univ := fun j =>
    (Classical.choose_spec (hu_grad_l2 j)).2
  let D : H1WeakSolutionData B u f :=
    { hu_l2 := hu_l2
      hf_l2 := hf_l2
      weakPartial := wp
      weakPartial_l2 := hwp_l2
      weakPartial_isWeak := hwp_isWeak
      isWeakSolution := h_weak
      fseq_l2_bound := M_F
      fseq_l2_bound_nn := hMF_nn
      fseq_l2_bounded := hMF_bound }
  exact exists_smoothApproximation_of_h1WeakSolutionData hΩ B D

end DifferentialGeometry.Analysis.Sobolev.H1WeakSolutionApprox
