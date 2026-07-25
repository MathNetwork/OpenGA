import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.Cartan.EvaluationFormChainRule
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.RemainderShortTimeExistence
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.DeTurckGeometricNonlinearity
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.EigenCombination
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.ParabolicInteriorSmoothing
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.SpectralWeylCounting
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.WeylSummability
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.ChartLocalExistence.ChartLocalPicard
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.ChartLocalExistence.ChartOverlapUniqueness
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.Regularity.BareFlowFromJointC1
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothDependence.GlobalClosedManifold

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff NNReal ENNReal Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.PDE
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.DeTurck
open DifferentialGeometry.PDE.RicciFlow.ODE
open DifferentialGeometry.PDE.RicciFlow.Pullback
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open MeasureTheory Set

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]


















omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem heatTraceWeighted_summable_of_tailSummable
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (htail : EigenvalueTailSummable (I := I) (M := M) g r s)
    (σ : ℝ) (hσ : 0 ≤ σ) {ε : ℝ} (hε : 0 < ε) :
    Summable (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
      tensorSobolevWeight (I := I) (M := M) i σ *
        Real.exp (-(2 * (TensorEigenIdx.lambda (I := I) (M := M) i) * ε))) := by
  obtain ⟨p, hp_pos, htp⟩ := htail
  set C : ℝ := tensorSmoothingConst (σ + p) * (min ε 1) ^ (-(σ + p)) with hC
  have hC_nn : 0 ≤ C := by
    apply mul_nonneg (tensorSmoothingConst_nonneg _)
    exact Real.rpow_nonneg (le_of_lt (lt_min hε one_pos)) _
  refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) (htp.mul_left C)
  · exact mul_nonneg (tensorSobolevWeight_nonneg _ _) (Real.exp_pos _).le
  · set lam := TensorEigenIdx.lambda (I := I) (M := M) i with hlam
    have hlam_nn : 0 ≤ lam := tensor_lambda_nonneg (I := I) (M := M) i
    have hbase_pos : (0 : ℝ) < 1 + lam := by linarith
    have hsplit : tensorSobolevWeight (I := I) (M := M) i σ =
        ((1 + lam) ^ (σ + p)) * ((1 + lam) ^ (-p)) := by
      unfold tensorSobolevWeight
      rw [hlam, ← Real.rpow_add hbase_pos]; congr 1; ring
    have hbound := tensorSmoothingScalarBound_of_pos
      (μ := σ + p) (by linarith) (t := ε) hε (lam := lam) hlam_nn
    calc tensorSobolevWeight (I := I) (M := M) i σ *
            Real.exp (-(2 * lam * ε))
        = ((1 + lam) ^ (σ + p) * Real.exp (-(2 * lam * ε))) * ((1 + lam) ^ (-p)) := by
          rw [hsplit]; ring
      _ ≤ C * ((1 + lam) ^ (-p)) := by
          apply mul_le_mul_of_nonneg_right hbound
          exact Real.rpow_nonneg hbase_pos.le _

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem hom_integral_eq
    {g : SmoothRiemannianMetric I M} {a : ℝ} {T : ℝ}
    (u₀ : tensorHs (I := I) (M := M) g 0 2 (a + 2))
    (i : TensorEigenIdx (I := I) (M := M) g 0 2)
    {s : ℝ} (hs : s ∈ Set.Icc (0:ℝ) T) :
    (∫ τ in (0:ℝ)..s, (homDerivModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i) τ)
      = (Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * s) - 1) * u₀.coeff i := by
  set lam := TensorEigenIdx.lambda (I := I) (M := M) i with hlam_def
  set c := u₀.coeff i with hc_def
  have hderiv : ⇑(homDerivModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i) =ᵐ[timeMeasure T]
      fun t => -lam * (Real.exp (-lam * t) * c) :=
    coeFn_ofContinuousOn _
  have hint_congr : (∫ τ in (0:ℝ)..s, (homDerivModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i) τ)
      = ∫ τ in (0:ℝ)..s, -lam * (Real.exp (-lam * τ) * c) := by
    refine intervalIntegral.integral_congr_ae ?_
    have hsub : Set.uIoc (0 : ℝ) s ⊆ Set.Icc (0 : ℝ) T :=
      (Set.uIoc_subset_uIcc).trans (uIcc_subset_Icc ⟨le_rfl, hs.1.trans hs.2⟩ hs)
    have hae := ae_restrict_of_ae_restrict_of_subset (μ := volume) hsub hderiv
    rw [ae_restrict_iff' measurableSet_uIoc] at hae
    filter_upwards [hae] with τ hτ using hτ
  rw [hint_congr]
  have hF : ∀ τ : ℝ, HasDerivAt (fun τ => Real.exp (-lam * τ) * c)
      (-lam * (Real.exp (-lam * τ) * c)) τ := by
    intro τ
    have hlin : HasDerivAt (fun τ : ℝ => -lam * τ) (-lam) τ := by
      simpa using (hasDerivAt_id τ).const_mul (-lam)
    have hexp : HasDerivAt (fun τ => Real.exp (-lam * τ))
        (Real.exp (-lam * τ) * (-lam)) τ := hlin.exp
    have := hexp.mul_const c
    convert this using 1
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun τ _ => hF τ)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  simp only [mul_zero, Real.exp_zero, one_mul]
  ring

omit [BoundarylessManifold I M] in
private theorem coeffFun_u_eq
    {g_bg : SmoothRiemannianMetric I M} {a : ℝ} {T : ℝ}
    (u₀ : tensorHs (I := I) (M := M) g_bg 0 2 (a + 2))
    (gforce : timeL2 (tensorHs (I := I) (M := M) g_bg 0 2 a) T)
    (hT : 0 < T) (hT1 : T ≤ 1)
    (i : TensorEigenIdx (I := I) (M := M) g_bg 0 2)
    {s : ℝ} (hs : s ∈ Set.Icc (0:ℝ) T) :
    (timeH1.toFun (maxRegDuhamelMap (I := I) (M := M) a hT hT1 u₀ gforce) s).coeff i
      = Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * s) * u₀.coeff i
        + ∫ τ in (0:ℝ)..s, (derivModeCoeff (I := I) (M := M) (a := a) hT.le gforce i) τ := by
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, hs.1.trans hs.2⟩
  set u := maxRegDuhamelMap (I := I) (M := M) a hT hT1 u₀ gforce with hu_def
  have hcomm : (coeffCLM (I := I) (M := M) (g := g_bg) (r := 0) (s := 2) (σ := a) i)
        (∫ τ in (0:ℝ)..s, u.deriv τ)
      = ∫ τ in (0:ℝ)..s, (u.deriv τ).coeff i := by
    rw [← ContinuousLinearMap.intervalIntegral_comp_comm
      (coeffCLM (I := I) (M := M) (g := g_bg) (r := 0) (s := 2) (σ := a) i)
      (u.intervalIntegrable_deriv h0 hs)]
    rfl
  have hval : (timeH1.toFun u s).coeff i =
      (u.init).coeff i + ∫ τ in (0:ℝ)..s, (u.deriv τ).coeff i := by
    have he : (timeH1.toFun u s).coeff i =
        (coeffCLM (I := I) (M := M) (g := g_bg) (r := 0) (s := 2) (σ := a) i) (timeH1.toFun u s) := rfl
    rw [he, timeH1.toFun_apply, map_add, hcomm]
    rfl
  rw [hval]
  have hinit : (u.init).coeff i = u₀.coeff i := by
    rw [hu_def, maxRegDuhamelMap_init]; rfl
  rw [hinit]
  have hsplit_ae := maxRegDuhamelMap_deriv_coeff_ae (I := I) (M := M)
    (h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g_bg 0 2)
    (a := a) hT hT1 u₀ gforce i
  have hint_split : (∫ τ in (0:ℝ)..s, (u.deriv τ).coeff i)
      = (∫ τ in (0:ℝ)..s, (homDerivModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i) τ)
        + ∫ τ in (0:ℝ)..s, (derivModeCoeff (I := I) (M := M) (a := a) hT.le gforce i) τ := by
    have hint_hom : IntervalIntegrable
        (fun τ => (homDerivModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i) τ) volume 0 s :=
      ((integrableOn (homDerivModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i)).mono_set
        (uIcc_subset_Icc h0 hs)).intervalIntegrable
    have hint_duh : IntervalIntegrable
        (fun τ => (derivModeCoeff (I := I) (M := M) (a := a) hT.le gforce i) τ) volume 0 s :=
      ((integrableOn (derivModeCoeff (I := I) (M := M) (a := a) hT.le gforce i)).mono_set
        (uIcc_subset_Icc h0 hs)).intervalIntegrable
    rw [← intervalIntegral.integral_add hint_hom hint_duh]
    refine intervalIntegral.integral_congr_ae ?_
    have hsub : Set.uIoc (0 : ℝ) s ⊆ Set.Icc (0 : ℝ) T :=
      (Set.uIoc_subset_uIcc).trans (uIcc_subset_Icc h0 hs)
    have hae := ae_restrict_of_ae_restrict_of_subset (μ := volume) hsub hsplit_ae
    rw [ae_restrict_iff' measurableSet_uIoc] at hae
    filter_upwards [hae] with τ hτ hτmem
    exact (hτ hτmem)
  rw [hint_split, hom_integral_eq (I := I) (M := M) u₀ i hs]
  ring

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem duhamel_integral_abs_le
    {g : SmoothRiemannianMetric I M} {a : ℝ} {T : ℝ} (hT : 0 ≤ T)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g 0 2 a) T)
    (i : TensorEigenIdx (I := I) (M := M) g 0 2)
    {s : ℝ} (hs : s ∈ Set.Icc (0:ℝ) T) :
    |∫ τ in (0:ℝ)..s, (derivModeCoeff (I := I) (M := M) (a := a) hT gforce i) τ|
      ≤ Real.sqrt T * ‖derivModeCoeff (I := I) (M := M) (a := a) hT gforce i‖ := by
  set v := derivModeCoeff (I := I) (M := M) (a := a) hT gforce i with hv_def
  set w := timeH1.mk (0:ℝ) v with hw_def
  have hval : (∫ τ in (0:ℝ)..s, (v) τ) = w.toFun s := by
    rw [timeH1.toFun_apply, hw_def, timeH1.init_mk,
      timeH1.deriv_mk, zero_add]
  have hbound := timeH1.norm_toFun_le w hs
  rw [timeH1.trace0_apply, timeH1.timeDeriv_apply,
    hw_def, timeH1.init_mk, timeH1.deriv_mk, norm_zero, zero_add] at hbound
  rw [hval, ← Real.norm_eq_abs]
  exact hbound

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem u0_coeff_sq_summable
    {g : SmoothRiemannianMetric I M} {a : ℝ} (ha2 : 0 ≤ a + 2)
    (u₀ : tensorHs (I := I) (M := M) g 0 2 (a + 2)) :
    Summable (fun i : TensorEigenIdx (I := I) (M := M) g 0 2 => (u₀.coeff i) ^ 2) := by
  refine Summable.of_nonneg_of_le (fun i => sq_nonneg _) (fun i => ?_) u₀.weighted_summable
  have hw : (1:ℝ) ≤ tensorSobolevWeight (I := I) (M := M) i (a + 2) := by
    rw [tensorSobolevWeight]
    exact Real.one_le_rpow (one_le_one_add_lambda (I := I) (M := M) i) ha2
  calc (u₀.coeff i)^2 = 1 * (u₀.coeff i)^2 := by ring
    _ ≤ tensorSobolevWeight (I := I) (M := M) i (a + 2) * (u₀.coeff i)^2 :=
        mul_le_mul_of_nonneg_right hw (sq_nonneg _)

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem hom_majorant_summable
    {g : SmoothRiemannianMetric I M} {a : ℝ} (ha2 : 0 ≤ a + 2)
    (u₀ : tensorHs (I := I) (M := M) g 0 2 (a + 2))
    (htail : EigenvalueTailSummable (I := I) (M := M) g 0 2)
    {σ : ℝ} (hσ : 0 ≤ σ) {ε : ℝ} (hε : 0 < ε) :
    Summable (fun i : TensorEigenIdx (I := I) (M := M) g 0 2 =>
      Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ)
        * Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * ε) * |u₀.coeff i|) := by
  have hheat := heatTraceWeighted_summable_of_tailSummable (I := I) (M := M) htail σ hσ hε
  have hu0 := u0_coeff_sq_summable (I := I) (M := M) ha2 u₀
  have hmaj : Summable (fun i : TensorEigenIdx (I := I) (M := M) g 0 2 =>
      (1/2 : ℝ) * (tensorSobolevWeight (I := I) (M := M) i σ
          * Real.exp (-(2 * (TensorEigenIdx.lambda (I := I) (M := M) i) * ε)) + (u₀.coeff i)^2)) :=
    ((hheat.add hu0).mul_left (1/2))
  refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) hmaj
  · positivity
  · set lam := TensorEigenIdx.lambda (I := I) (M := M) i with hlam
    set wσ := tensorSobolevWeight (I := I) (M := M) i σ with hwσ
    have hwσ_nn : 0 ≤ wσ := tensorSobolevWeight_nonneg (I := I) (M := M) i σ
    set A : ℝ := Real.sqrt (wσ * Real.exp (-(2 * lam * ε))) with hA
    set B : ℝ := |u₀.coeff i| with hB
    have hexp_sqrt : Real.sqrt (Real.exp (-(2 * lam * ε))) = Real.exp (-lam * ε) := by
      have he2 : Real.exp (-(2 * lam * ε)) = (Real.exp (-lam * ε))^2 := by
        rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
      rw [he2, Real.sqrt_sq (Real.exp_pos _).le]
    have hAB_eq : Real.sqrt wσ * Real.exp (-lam * ε) * B = A * B := by
      rw [hA, Real.sqrt_mul hwσ_nn, hexp_sqrt]
    rw [hAB_eq]
    have hAnn : 0 ≤ A := Real.sqrt_nonneg _
    have hBnn : 0 ≤ B := abs_nonneg _
    have hkey : 2 * A * B ≤ A^2 + B^2 := two_mul_le_add_sq A B
    have hA2 : A^2 = wσ * Real.exp (-(2 * lam * ε)) := by
      rw [hA, Real.sq_sqrt (by positivity)]
    have hB2 : B^2 = (u₀.coeff i)^2 := by rw [hB, sq_abs]
    nlinarith [hkey, hA2, hB2]

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem norm_derivModeCoeff_le
    {g : SmoothRiemannianMetric I M} {a : ℝ} {T : ℝ} (hT : 0 ≤ T)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g 0 2 a) T)
    (i : TensorEigenIdx (I := I) (M := M) g 0 2) :
    ‖derivModeCoeff (I := I) (M := M) (a := a) hT gforce i‖
      ≤ 2 * ‖timeModeCoeff (I := I) (M := M) gforce i‖ := by
  rw [derivModeCoeff]
  exact perModeConvDerivL2_sq_le _ (tensor_lambda_nonneg (I := I) (M := M) i) hT _

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem duhamel_majorant_summable
    {g : SmoothRiemannianMetric I M} {a : ℝ} {T : ℝ}
    (gforce : timeL2 (tensorHs (I := I) (M := M) g 0 2 a) T)
    (htail : EigenvalueTailSummable (I := I) (M := M) g 0 2)
    (hforce : ∀ d : ℝ, Summable (forcingMass (I := I) (M := M) gforce d))
    {σ : ℝ} :
    Summable (fun i : TensorEigenIdx (I := I) (M := M) g 0 2 =>
      Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ)
        * (Real.sqrt T * (2 * ‖timeModeCoeff (I := I) (M := M) gforce i‖))) := by
  obtain ⟨p, hp_pos, htp⟩ := htail
  have hfm := hforce (σ + p)
  have hmaj : Summable (fun i : TensorEigenIdx (I := I) (M := M) g 0 2 =>
      Real.sqrt T * (forcingMass (I := I) (M := M) gforce (σ + p) i
        + (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (-p))) :=
    (hfm.add htp).mul_left (Real.sqrt T)
  refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) hmaj
  · positivity
  · set lam := TensorEigenIdx.lambda (I := I) (M := M) i with hlam
    set wσ := tensorSobolevWeight (I := I) (M := M) i σ with hwσ
    set nm := ‖timeModeCoeff (I := I) (M := M) gforce i‖ with hnm
    have hbase_pos : (0:ℝ) < 1 + lam := by
      have := tensor_lambda_nonneg (I := I) (M := M) i; linarith
    set A : ℝ := Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (σ + p)) * nm with hA
    set B : ℝ := Real.sqrt ((1 + lam) ^ (-p)) with hB
    have hw_split : tensorSobolevWeight (I := I) (M := M) i (σ + p) * (1 + lam) ^ (-p) = wσ := by
      rw [hwσ, tensorSobolevWeight, tensorSobolevWeight, hlam, ← Real.rpow_add hbase_pos]
      congr 1; ring
    have hAB_eq : Real.sqrt wσ * nm = A * B := by
      rw [hA, hB]
      rw [show Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (σ + p)) * nm
            * Real.sqrt ((1 + lam) ^ (-p))
          = (Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (σ + p))
              * Real.sqrt ((1 + lam) ^ (-p))) * nm by ring,
        ← Real.sqrt_mul (tensorSobolevWeight_nonneg (I := I) (M := M) i (σ+p)) ((1+lam)^(-p)),
        hw_split]
    have hAnn : 0 ≤ A :=
      mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
    have hBnn : 0 ≤ B := Real.sqrt_nonneg _
    have hkey : 2 * A * B ≤ A^2 + B^2 := two_mul_le_add_sq A B
    have hA2 : A^2 = forcingMass (I := I) (M := M) gforce (σ + p) i := by
      rw [hA, mul_pow, Real.sq_sqrt (tensorSobolevWeight_nonneg (I := I) (M := M) i (σ+p)),
        forcingMass, hnm]
    have hB2 : B^2 = (1 + lam) ^ (-p) := by
      rw [hB, Real.sq_sqrt (Real.rpow_nonneg hbase_pos.le _)]
    have hexpand : Real.sqrt wσ * (Real.sqrt T * (2 * nm)) = Real.sqrt T * (2 * (A * B)) := by
      rw [← hAB_eq]; ring
    rw [hexpand]
    have hTnn : 0 ≤ Real.sqrt T := Real.sqrt_nonneg T
    have h2ab : 2 * (A * B) ≤ A^2 + B^2 := by nlinarith [hkey]
    calc Real.sqrt T * (2 * (A * B))
        ≤ Real.sqrt T * (A^2 + B^2) := mul_le_mul_of_nonneg_left h2ab hTnn
      _ = Real.sqrt T * (forcingMass (I := I) (M := M) gforce (σ + p) i
            + (1 + lam) ^ (-p)) := by rw [hA2, hB2]

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem tsum_singleModeCLM_coeff
    {g : SmoothRiemannianMetric I M} {σ : ℝ}
    (c : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ)
    (hsum : Summable (fun j => singleModeCLM (I := I) (M := M) (g := g) (r := 0) (s := 2) (σ := σ) j (c j)))
    (i : TensorEigenIdx (I := I) (M := M) g 0 2) :
    (∑' j, singleModeCLM (I := I) (M := M) (g := g) (r := 0) (s := 2) (σ := σ) j (c j)).coeff i = c i := by
  classical
  have hmap := ContinuousLinearMap.map_tsum
    (coeffCLM (I := I) (M := M) (g := g) (r := 0) (s := 2) (σ := σ) i) hsum
  have hlhs : (∑' j, singleModeCLM (I := I) (M := M) (g := g) (r := 0) (s := 2) (σ := σ) j (c j)).coeff i
      = (coeffCLM (I := I) (M := M) (g := g) (r := 0) (s := 2) (σ := σ) i)
          (∑' j, singleModeCLM (I := I) (M := M) (g := g) (r := 0) (s := 2) (σ := σ) j (c j)) := rfl
  rw [hlhs, hmap]
  have hterm : ∀ j, (coeffCLM (I := I) (M := M) (g := g) (r := 0) (s := 2) (σ := σ) i)
      (singleModeCLM (I := I) (M := M) (g := g) (r := 0) (s := 2) (σ := σ) j (c j))
      = (if j = i then c j else 0) := by
    intro j
    rw [coeffCLM_apply, singleModeCLM_coeff]
    by_cases h : j = i
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (fun hc => h hc.symm)]
  rw [tsum_congr hterm, tsum_ite_eq i c]

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem continuousOn_coeffFun_u
    {g_bg : SmoothRiemannianMetric I M} {a : ℝ} {T : ℝ}
    (u : MaxRegSolutionSpace (I := I) (M := M) a T)
    (i : TensorEigenIdx (I := I) (M := M) g_bg 0 2) :
    ContinuousOn (fun s => (timeH1.toFun u s).coeff i) (Set.Icc (0:ℝ) T) := by
  have hcomp : ContinuousOn
      (fun s => coeffCLM (I := I) (M := M) (g := g_bg) (r := 0) (s := 2) (σ := a) i (timeH1.toFun u s))
      (Set.Icc (0:ℝ) T) :=
    (coeffCLM (I := I) (M := M) (g := g_bg) (r := 0) (s := 2) (σ := a) i).continuous.comp_continuousOn
      u.continuousOn_toFun
  simpa only [coeffCLM_apply] using hcomp

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem norm_singleModeCLM_eq
    {g : SmoothRiemannianMetric I M} {σ : ℝ}
    (i : TensorEigenIdx (I := I) (M := M) g 0 2) (c : ℝ) :
    ‖singleModeCLM (I := I) (M := M) (g := g) (r := 0) (s := 2) (σ := σ) i c‖
      = Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) * |c| := by
  rw [singleModeCLM_apply, norm_smul, norm_tensorHsBasisVec (I := I) (M := M) i,
    Real.norm_eq_abs, mul_comm]













omit [BoundarylessManifold I M] in
theorem interior_allscale_time_continuity
    (g_bg : SmoothRiemannianMetric I M) (a : ℕ) {T : ℝ}
    (u₀ : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 2))
    (gforce : timeL2 (tensorHs (I := I) (M := M) g_bg 0 2 (a : ℝ)) T)
    (hT : 0 < T) (hT1 : T ≤ 1)
    (u : MaxRegSolutionSpace (I := I) (M := M) (a : ℝ) T)
    (hu : u = maxRegDuhamelMap (I := I) (M := M) (a : ℝ) hT hT1 u₀ gforce)
    (hcouple : ∀ d : ℝ,
      Summable (solFieldMass (I := I) (M := M) hT.le gforce (d + 1)) →
        Summable (forcingMass (I := I) (M := M) gforce d))
    (hbase : Summable (solFieldMass (I := I) (M := M) hT.le gforce (a : ℝ)))
    (σ : ℝ) (haσ : (a : ℝ) ≤ σ) :
    ∀ ε : ℝ, 0 < ε →
      ∃ uσ : ℝ → tensorHs (I := I) (M := M) g_bg 0 2 σ,
        ContinuousOn uσ (Set.Icc ε T) ∧
          ∀ s ∈ Set.Icc ε T,
            tensorHsInclusion (I := I) (M := M) (g := g_bg) (r := 0) (s := 2) haσ
              (uσ s) = timeH1.toFun u s := by
  intro ε hε
  have ha0 : (0:ℝ) ≤ (a:ℝ) := Nat.cast_nonneg a
  have hσ0 : (0:ℝ) ≤ σ := le_trans ha0 haσ
  have ha2 : (0:ℝ) ≤ (a:ℝ) + 2 := by linarith
  have htail : EigenvalueTailSummable (I := I) (M := M) g_bg 0 2 :=
    ⟨((weylSobolevExp (E := E) : ℕ) : ℝ) + 1, by positivity,
      tensorEigen_summable_negpow (I := I) (M := M) g_bg
        (((weylSobolevExp (E := E) : ℕ) : ℝ) + 1) (by linarith)⟩
  have hforce : ∀ d : ℝ, Summable (forcingMass (I := I) (M := M) gforce d) := by
    intro d
    exact hcouple d (solFieldMass_summable_all (I := I) (M := M) hT.le gforce hcouple hbase (d + 1))
  set cfun : TensorEigenIdx (I := I) (M := M) g_bg 0 2 → ℝ → ℝ :=
    fun i s => (timeH1.toFun u s).coeff i with hcfun_def
  set Mhom : TensorEigenIdx (I := I) (M := M) g_bg 0 2 → ℝ :=
    fun i => Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ)
      * Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * ε) * |u₀.coeff i| with hMhom_def
  set Mduh : TensorEigenIdx (I := I) (M := M) g_bg 0 2 → ℝ :=
    fun i => Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ)
      * (Real.sqrt T * (2 * ‖timeModeCoeff (I := I) (M := M) gforce i‖)) with hMduh_def
  have hMhom_sum : Summable Mhom :=
    hom_majorant_summable (I := I) (M := M) ha2 u₀ htail hσ0 hε
  have hMduh_sum : Summable Mduh :=
    duhamel_majorant_summable (I := I) (M := M) gforce htail hforce
  set Maj : TensorEigenIdx (I := I) (M := M) g_bg 0 2 → ℝ := fun i => Mhom i + Mduh i with hMaj_def
  have hMaj_sum : Summable Maj := hMhom_sum.add hMduh_sum
  have hbound : ∀ i, ∀ s ∈ Set.Icc ε T,
      ‖singleModeCLM (I := I) (M := M) (g := g_bg) (r := 0) (s := 2) (σ := σ) i (cfun i s)‖ ≤ Maj i := by
    intro i s hsεT
    have hsT : s ∈ Set.Icc (0:ℝ) T := ⟨le_trans hε.le hsεT.1, hsεT.2⟩
    set lam := TensorEigenIdx.lambda (I := I) (M := M) i with hlam
    have hlam_nn : 0 ≤ lam := tensor_lambda_nonneg (I := I) (M := M) i
    have hval : cfun i s
        = Real.exp (-lam * s) * u₀.coeff i
          + ∫ τ in (0:ℝ)..s, (derivModeCoeff (I := I) (M := M) (a := (a:ℝ)) hT.le gforce i) τ := by
      rw [hcfun_def, hu]
      exact coeffFun_u_eq (I := I) (M := M) u₀ gforce hT hT1 i hsT
    rw [norm_singleModeCLM_eq]
    set wσsqrt := Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) with hwσsqrt
    have hwσsqrt_nn : 0 ≤ wσsqrt := Real.sqrt_nonneg _
    have hexp_mono : Real.exp (-lam * s) ≤ Real.exp (-lam * ε) := by
      apply Real.exp_le_exp.mpr
      have : lam * ε ≤ lam * s := mul_le_mul_of_nonneg_left hsεT.1 hlam_nn
      nlinarith
    have hexp_nn : 0 ≤ Real.exp (-lam * s) := (Real.exp_pos _).le
    have habs : |cfun i s|
        ≤ Real.exp (-lam * ε) * |u₀.coeff i|
          + Real.sqrt T * (2 * ‖timeModeCoeff (I := I) (M := M) gforce i‖) := by
      rw [hval]
      refine le_trans (abs_add_le _ _) ?_
      apply add_le_add
      · rw [abs_mul, abs_of_nonneg hexp_nn]
        exact mul_le_mul_of_nonneg_right hexp_mono (abs_nonneg _)
      · have h1 := duhamel_integral_abs_le (I := I) (M := M) (a := (a:ℝ)) hT.le gforce i hsT
        have h2 := norm_derivModeCoeff_le (I := I) (M := M) (a := (a:ℝ)) hT.le gforce i
        have hTnn : 0 ≤ Real.sqrt T := Real.sqrt_nonneg T
        calc |∫ τ in (0:ℝ)..s, (derivModeCoeff (I := I) (M := M) (a := (a:ℝ)) hT.le gforce i) τ|
            ≤ Real.sqrt T * ‖derivModeCoeff (I := I) (M := M) (a := (a:ℝ)) hT.le gforce i‖ := h1
          _ ≤ Real.sqrt T * (2 * ‖timeModeCoeff (I := I) (M := M) gforce i‖) :=
              mul_le_mul_of_nonneg_left h2 hTnn
    calc wσsqrt * |cfun i s|
        ≤ wσsqrt * (Real.exp (-lam * ε) * |u₀.coeff i|
            + Real.sqrt T * (2 * ‖timeModeCoeff (I := I) (M := M) gforce i‖)) :=
          mul_le_mul_of_nonneg_left habs hwσsqrt_nn
      _ = Maj i := by rw [hMaj_def, hMhom_def, hMduh_def, hwσsqrt]; ring
  have hsummable : ∀ s ∈ Set.Icc ε T,
      Summable (fun i => singleModeCLM (I := I) (M := M) (g := g_bg) (r := 0) (s := 2) (σ := σ) i (cfun i s)) := by
    intro s hs
    exact Summable.of_norm_bounded hMaj_sum (fun i => hbound i s hs)
  refine ⟨fun s => ∑' i, singleModeCLM (I := I) (M := M) (g := g_bg) (r := 0) (s := 2) (σ := σ) i (cfun i s), ?_, ?_⟩
  · refine continuousOn_tsum ?_ hMaj_sum (fun i s hs => hbound i s hs)
    intro i
    have hcfcont : ContinuousOn (fun s => cfun i s) (Set.Icc ε T) :=
      (continuousOn_coeffFun_u (I := I) (M := M) u i).mono
        (fun s hs => ⟨le_trans hε.le hs.1, hs.2⟩)
    exact (singleModeCLM (I := I) (M := M) (g := g_bg) (r := 0) (s := 2) (σ := σ) i).continuous.comp_continuousOn hcfcont
  · intro s hs
    refine tensorHs.ext ?_
    funext i
    rw [tensorHsInclusion_coeff_apply,
      tsum_singleModeCLM_coeff (I := I) (M := M) (fun j => cfun j s) (hsummable s hs) i]

end DifferentialGeometry.PDE.RicciFlow
