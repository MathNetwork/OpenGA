import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RawConnLapL2SobolevBounds.RawTensorConnLapIterL2WtwokTwoBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartCoordinateExpansion.RawConnLapChartComponentSecondCovDerivFormula
import DifferentialGeometry.Analysis.Elliptic.TensorRegularity.SecondCovDerivExpansion.SecondCovDerivChartProjEuclidGlobal
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartCoordinateExpansion.RawConnLapChartCoordFormulaT0Linear
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartCoordinateExpansion.RawConnLapMinusInvGramPrincipalSmoothCoeff
import DifferentialGeometry.Geometry.Operator.Gradient
import DifferentialGeometry.Analysis.Sobolev.Approximation.SmoothDensity
import DifferentialGeometry.Tensor.Multilinear.HsBoundOp
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.HilbertSpace
import DifferentialGeometry.Analysis.Sobolev.Tensor.PouWeightedHsNorm
import DifferentialGeometry.Analysis.Sobolev.Tensor.PouWeightedHsNormReverseOrderZero
import DifferentialGeometry.Analysis.Integration.L2.Hilbert.DenseSubset
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.TensorSectionL2BoundByComponents
import DifferentialGeometry.Analysis.Sobolev.Manifold.MeasureBridgeUniform
import DifferentialGeometry.Analysis.Spectral.Tensor.NormEstimates.TensorChartComponentSobolevBound
import DifferentialGeometry.Geometry.Connection.ChartFrameNormGlobalSmoothCoordBasisExpansion
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartCoordinateExpansion.CovApplyFrameToCoordExpansion
import DifferentialGeometry.Analysis.Elliptic.TensorRegularity.CovDeriv.ComponentFormula
import DifferentialGeometry.Geometry.Connection.ChartTensorNabla.TensorRS.ChartTensorRSCovariantDerivativeAgreement
import DifferentialGeometry.Tensor.RSTensor.Defs


namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff NNReal ENNReal Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Tensor
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

section ReverseOrderZeroBridge

open MeasureTheory
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Sobolev.Tensor
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

private lemma sq_eLpNorm_two_eq_lintegral_enorm_sq'
    {β : Type*} [MeasurableSpace β] (μ : Measure β) (f : β → ℝ) :
    (eLpNorm f 2 μ) ^ 2 = ∫⁻ x, (‖f x‖ₑ : ℝ≥0∞) ^ 2 ∂μ := by
  classical
  have h2_ne_zero : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h2_ne_top : (2 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞) := by norm_num
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (μ := μ) h2_ne_zero h2_ne_top]
  have h2_toReal : ((2 : ℝ≥0∞)).toReal = 2 := by show ENNReal.toReal 2 = 2; rfl
  rw [h2_toReal]
  have h_inner_eq : ∫⁻ x, (‖f x‖ₑ : ℝ≥0∞) ^ (2 : ℝ) ∂μ =
      ∫⁻ x, (‖f x‖ₑ : ℝ≥0∞) ^ 2 ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards with x
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]
  rw [h_inner_eq, ← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
  norm_num

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] in
private lemma hsNorm_zero_summand_eq_sq_eLpNorm_chartPushedSqrtPou
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Integral.L2.SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (basisIdx : Fin 0 → Fin (Module.finrank ℝ E)) :
    (∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
        ENNReal.ofReal
          (((chartAtlasPOU I M α : M → ℝ)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            |(iteratedFDeriv ℝ 0
                  (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                    ∘ (extChartAt I α).symm
                    ∘ (toEuclidean (E := E)).symm)
                  y)
                (fun i => EuclideanSpace.basisFun
                  (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2)
        ∂(volume : Measure EuclN)) =
      (eLpNorm
          (chartPushedRaw I α
            (tensorChartComponentSqrtPou (I := I) (M := M) g r s T α Idx Jdx)) 2
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α))) ^ 2 := by
  classical
  rw [sq_eLpNorm_two_eq_lintegral_enorm_sq']
  rw [← MeasureTheory.lintegral_indicator
        (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet,
      ← MeasureTheory.lintegral_indicator
        (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet]
  refine MeasureTheory.lintegral_congr (fun y => ?_)
  by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
  · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
    set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb_def
    have hraw_eval :
        (iteratedFDeriv ℝ 0
              (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                ∘ (extChartAt I α).symm
                ∘ (toEuclidean (E := E)).symm) y)
            (fun i => EuclideanSpace.basisFun
              (Fin (Module.finrank ℝ E)) ℝ (basisIdx i)) =
          tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx b := by
      rw [iteratedFDeriv_zero_apply]; rfl
    have hpush :
        chartPushedRaw I α
            (tensorChartComponentSqrtPou (I := I) (M := M) g r s T α Idx Jdx) y =
          tensorChartComponentSqrtPou (I := I) (M := M) g r s T α Idx Jdx b :=
      chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy
    rw [hraw_eval, hpush]
    have hw_sq :
        (tensorChartComponentSqrtPou (I := I) (M := M) g r s T α Idx Jdx b) ^ 2 =
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
            (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx b) ^ 2 :=
      tensorChartComponentSqrtPou_sq (I := I) (M := M) g r s T α Idx Jdx b
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _) 2]
    congr 1
    rw [sq_abs, sq_abs, hw_sq]
  · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] in
private lemma support_sqrt_pou_eq' (α : M) :
    Function.support
        (fun b : M => Real.sqrt
          (((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b)) =
      Function.support (((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) := by
  ext b
  simp only [Function.mem_support, ne_eq, Real.sqrt_eq_zero']
  constructor
  · intro hb hcontra
    exact hb (by rw [hcontra])
  · intro hb hle
    have hρ_nn : 0 ≤ ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b :=
      (chartAtlasPOU I M).nonneg α b
    exact hb (le_antisymm hle hρ_nn)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] in
private lemma tsupport_sqrtPou_subset
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Integral.L2.SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tsupport (tensorChartComponentSqrtPou (I := I) (M := M) g r s T α Idx Jdx) ⊆
      tsupport (((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) := by
  have h_mul : tsupport (tensorChartComponentSqrtPou (I := I) (M := M)
        g r s T α Idx Jdx) ⊆
      tsupport (fun b : M => Real.sqrt
        (((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b)) :=
    tsupport_mul_subset_left
      (f := fun b : M => Real.sqrt
        (((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b))
      (g := tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx)
  refine h_mul.trans ?_
  unfold tsupport
  rw [support_sqrt_pou_eq' (I := I) (M := M) α]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] in
private lemma continuous_sqrtPou
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Integral.L2.SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    Continuous
      (tensorChartComponentSqrtPou (I := I) (M := M) g r s T α Idx Jdx) := by
  classical
  have hSqrt_cont : Continuous
      (fun y : M => Real.sqrt
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) y)) :=
    Real.continuous_sqrt.comp
      (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff.continuous
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx_chart : x ∈ (chartAt H α).source
  · have hRaw_on := tensorChartComponentRaw_contMDiffOn_chart_source
      (I := I) (M := M) g r s T α Idx Jdx
    have hRaw_at : ContinuousAt
        (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx) x :=
      ((hRaw_on.contMDiffAt
        (IsOpen.mem_nhds (chartAt H α).open_source hx_chart)).continuousAt)
    exact (hSqrt_cont.continuousAt).mul hRaw_at
  · have hsupp_sub :
        tsupport (tensorChartComponentSqrtPou (I := I) (M := M)
            g r s T α Idx Jdx) ⊆ (chartAt H α).source :=
      (tsupport_sqrtPou_subset (I := I) (M := M)
        g r s T α Idx Jdx).trans
        (chartAtlasPOU_isSubordinate I M α)
    have hx_notin : x ∉ tsupport (tensorChartComponentSqrtPou (I := I) (M := M)
        g r s T α Idx Jdx) := fun h => hx_chart (hsupp_sub h)
    refine (continuousAt_const (y := (0 : ℝ))).congr ?_
    have hopen : IsOpen
        (tsupport (tensorChartComponentSqrtPou (I := I) (M := M)
          g r s T α Idx Jdx))ᶜ :=
      isClosed_tsupport _ |>.isOpen_compl
    filter_upwards [hopen.mem_nhds hx_notin] with y hy
    have hy_notsupp : y ∉ Function.support
        (tensorChartComponentSqrtPou (I := I) (M := M)
          g r s T α Idx Jdx) := fun h_in => hy (subset_tsupport _ h_in)
    have hzero : tensorChartComponentSqrtPou (I := I) (M := M)
        g r s T α Idx Jdx y = 0 := by
      by_contra hne; exact hy_notsupp hne
    exact hzero.symm

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] in
private lemma measurable_sqrtPou
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Integral.L2.SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    Measurable
      (tensorChartComponentSqrtPou (I := I) (M := M) g r s T α Idx Jdx) :=
  (continuous_sqrtPou (I := I) (M := M) g r s T α Idx Jdx).measurable

omit [BoundarylessManifold I M] in
private lemma sq_eLpNorm_scalar_le_const_mul_hsNorm_zero_summand
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : Integral.L2.SmoothCcTensor g r s)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        (eLpNorm (tensorChartComponentScalar (I := I) (M := M) g r s T α Idx Jdx) 2
              (riemannianVolumeMeasure (I := I) (M := M) g)) ^ 2 ≤
          ENNReal.ofReal C *
            (∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                ENNReal.ofReal
                  (((chartAtlasPOU I M α : M → ℝ)
                      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                    |(iteratedFDeriv ℝ 0
                          (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                            ∘ (extChartAt I α).symm
                            ∘ (toEuclidean (E := E)).symm)
                          y)
                        (fun i => EuclideanSpace.basisFun
                          (Fin (Module.finrank ℝ E)) ℝ
                          ((default : Fin 0 → Fin (Module.finrank ℝ E)) i))| ^ 2)
                ∂(volume : Measure EuclN)) := by
  classical
  set Kα : Set M := tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) with hKα_def
  have hKα_compact : IsCompact Kα := (isClosed_tsupport _).isCompact
  have hKα_sub : Kα ⊆ (chartAt H α).source := chartAtlasPOU_isSubordinate I M α
  obtain ⟨Cbr, hCbr_pos, hCbr⟩ :=
    eLpNorm_riemannianMeasure_le_const_mul_eLpNorm_chartPushedRaw_uniform_of_subset
      (I := I) (M := M) g α hKα_compact hKα_sub (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (by decide : (2 : ℝ≥0∞) ≠ ⊤)
  refine ⟨Cbr ^ 2, sq_nonneg _, ?_⟩
  intro T Idx Jdx
  set w : M → ℝ := tensorChartComponentSqrtPou (I := I) (M := M) g r s T α Idx Jdx with hw_def
  have hw_meas : Measurable w :=
    measurable_sqrtPou (I := I) (M := M) g r s T α Idx Jdx
  have hw_supp : tsupport w ⊆ Kα :=
    tsupport_sqrtPou_subset (I := I) (M := M) g r s T α Idx Jdx

  have h_ptwise : ∀ x : M,
      ‖tensorChartComponentScalar (I := I) (M := M) g r s T α Idx Jdx x‖ ≤ ‖w x‖ := by
    intro x
    have hρ_nn : 0 ≤ ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x :=
      (chartAtlasPOU I M).nonneg α x
    have hρ_le_one : ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x ≤ 1 :=
      (chartAtlasPOU I M).le_one α x
    have hsqrt_nn : 0 ≤ Real.sqrt (((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) :=
      Real.sqrt_nonneg _
    have hsqrt_le_one :
        Real.sqrt (((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ≤ 1 := by
      rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
      exact Real.sqrt_le_sqrt hρ_le_one
    have hρ_eq : ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x =
        Real.sqrt (((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) *
          Real.sqrt (((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) :=
      (Real.mul_self_sqrt hρ_nn).symm
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    rw [show tensorChartComponentScalar (I := I) (M := M) g r s T α Idx Jdx x =
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x *
            tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx x from rfl,
      hw_def, tensorChartComponentSqrtPou_apply]
    rw [abs_mul, abs_mul]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    rw [abs_of_nonneg hρ_nn, abs_of_nonneg hsqrt_nn]
    calc ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x
        = Real.sqrt (((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) *
            Real.sqrt (((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) := hρ_eq
      _ ≤ 1 * Real.sqrt (((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) :=
          mul_le_mul_of_nonneg_right hsqrt_le_one hsqrt_nn
      _ = Real.sqrt (((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) := one_mul _
  have h_scalar_le_w :
      eLpNorm (tensorChartComponentScalar (I := I) (M := M) g r s T α Idx Jdx) 2
          (riemannianVolumeMeasure (I := I) (M := M) g) ≤
        eLpNorm w 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
    eLpNorm_mono h_ptwise

  have h_bridge := hCbr (u := w) hw_meas hw_supp
  rw [show DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)
        = DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g
      from rfl] at h_bridge

  set lhsE : ℝ≥0∞ :=
    eLpNorm (tensorChartComponentScalar (I := I) (M := M) g r s T α Idx Jdx) 2
      (riemannianVolumeMeasure (I := I) (M := M) g) with hlhsE_def
  set chE : ℝ≥0∞ :=
    eLpNorm (chartPushedRaw I α w) 2
      ((volume : Measure EuclN).restrict (chartTargetEuclid (I := I) (M := M) α)) with hchE_def
  have h_lhsE_le : lhsE ≤ ENNReal.ofReal Cbr * chE :=
    le_trans h_scalar_le_w h_bridge
  have h_chE_sq :
      chE ^ 2 =
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal
            (((chartAtlasPOU I M α : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
              |(iteratedFDeriv ℝ 0
                    (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                      ∘ (extChartAt I α).symm
                      ∘ (toEuclidean (E := E)).symm)
                    y)
                  (fun i => EuclideanSpace.basisFun
                    (Fin (Module.finrank ℝ E)) ℝ
                    ((default : Fin 0 → Fin (Module.finrank ℝ E)) i))| ^ 2)
          ∂(volume : Measure EuclN) := by
    rw [hchE_def, hw_def,
      ← hsNorm_zero_summand_eq_sq_eLpNorm_chartPushedSqrtPou
          (I := I) (M := M) g r s T α Idx Jdx (default : Fin 0 → Fin (Module.finrank ℝ E))]
  rw [← h_chE_sq]
  calc lhsE ^ 2 ≤ (ENNReal.ofReal Cbr * chE) ^ 2 := pow_le_pow_left' h_lhsE_le 2
    _ = (ENNReal.ofReal Cbr) ^ 2 * chE ^ 2 := by rw [mul_pow]
    _ = ENNReal.ofReal (Cbr ^ 2) * chE ^ 2 := by rw [← ENNReal.ofReal_pow hCbr_pos.le]

omit [BoundarylessManifold I M] in
theorem exists_sum_componentL2Norm_sq_le_tensorPouSobolevHsNormSq_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ T : Integral.L2.SmoothCcTensor g r s,
        (∑ α ∈ DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset (I := I) (M := M),
            ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
              ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
                ((MeasureTheory.eLpNorm
                    (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar
                      (I := I) (M := M) g r s T α Idx Jdx) 2
                    (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure
                      (I := I) (M := M) g)).toReal) ^ 2) ≤
          C * (tensorPouSobolevHsNormSq (I := I) (M := M) g 0 T).toReal := by
  classical
  set Sf : Finset M := DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset
    (I := I) (M := M) with hSf_def

  choose Cα hCα_nn hCα using fun α (_ : α ∈ Sf) =>
    sq_eLpNorm_scalar_le_const_mul_hsNorm_zero_summand (I := I) (M := M) (E := E) g r s α
  set Cmax : ℝ := ∑ α ∈ Sf.attach, Cα α.val α.property with hCmax_def
  have hCmax_nn : 0 ≤ Cmax :=
    Finset.sum_nonneg (fun α _ => hCα_nn α.val α.property)
  refine ⟨Cmax, hCmax_nn, fun T => ?_⟩

  set summand : M → (Fin r → Fin (Module.finrank ℝ E)) →
      (Fin s → Fin (Module.finrank ℝ E)) → ℝ≥0∞ :=
    fun α Idx Jdx =>
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
        ENNReal.ofReal
          (((chartAtlasPOU I M α : M → ℝ)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            |(iteratedFDeriv ℝ 0
                  (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                    ∘ (extChartAt I α).symm
                    ∘ (toEuclidean (E := E)).symm)
                  y)
                (fun i => EuclideanSpace.basisFun
                  (Fin (Module.finrank ℝ E)) ℝ
                  ((default : Fin 0 → Fin (Module.finrank ℝ E)) i))| ^ 2)
        ∂(volume : Measure EuclN) with hsummand_def
  set lhsEsq : M → (Fin r → Fin (Module.finrank ℝ E)) →
      (Fin s → Fin (Module.finrank ℝ E)) → ℝ≥0∞ :=
    fun α Idx Jdx =>
      (MeasureTheory.eLpNorm
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar
            (I := I) (M := M) g r s T α Idx Jdx) 2
          (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure
            (I := I) (M := M) g)) ^ 2 with hlhsEsq_def

  have h_perchart : ∀ α ∈ Sf, ∀ Idx Jdx,
      lhsEsq α Idx Jdx ≤ ENNReal.ofReal Cmax * summand α Idx Jdx := by
    intro α hα Idx Jdx
    have hCα_le : Cα α hα ≤ Cmax := by
      rw [hCmax_def]
      refine Finset.single_le_sum (f := fun β : Sf => Cα β.val β.property)
        (fun β _ => hCα_nn β.val β.property) (Finset.mem_attach Sf ⟨α, hα⟩)
    calc lhsEsq α Idx Jdx
        ≤ ENNReal.ofReal (Cα α hα) * summand α Idx Jdx := hCα α hα T Idx Jdx
      _ ≤ ENNReal.ofReal Cmax * summand α Idx Jdx := by
          gcongr

  have h_sum_le :
      (∑ α ∈ Sf, ∑ Idx, ∑ Jdx, lhsEsq α Idx Jdx) ≤
        ENNReal.ofReal Cmax * ∑ α ∈ Sf, ∑ Idx, ∑ Jdx, summand α Idx Jdx := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun α hα => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun Idx _ => ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun Jdx _ => h_perchart α hα Idx Jdx)

  have h_summand_eq_normSq :
      tensorPouSobolevHsNormSq (I := I) (M := M) g 0 T =
        ∑' α : M, ∑ Idx, ∑ Jdx, summand α Idx Jdx := by
    rw [tensorPouSobolevHsNormSq_eq_inner_sum (I := I) (M := M) g 0 T]
    refine tsum_congr (fun α => ?_)
    rw [Fintype.sum_prod_type
      (f := fun IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)) =>
        ∑ j ∈ Finset.range (2 * 0 + 1),
          ∑ basisIdx : Fin j → Fin (Module.finrank ℝ E),
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                  |(iteratedFDeriv ℝ j
                        (tensorChartComponentRaw (I := I) (M := M) g r s T α IJ.1 IJ.2
                          ∘ (extChartAt I α).symm
                          ∘ (toEuclidean (E := E)).symm)
                        y)
                      (fun i => EuclideanSpace.basisFun
                        (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2)
              ∂(volume : Measure EuclN))]
    refine Finset.sum_congr rfl (fun Idx _ => ?_)
    refine Finset.sum_congr rfl (fun Jdx _ => ?_)
    rw [show (2 * 0 + 1) = 1 from rfl, Finset.sum_range_one,
      Fintype.sum_subsingleton _ (default : Fin 0 → Fin (Module.finrank ℝ E))]
  have h_finset_le_tsum :
      (∑ α ∈ Sf, ∑ Idx, ∑ Jdx, summand α Idx Jdx) ≤
        ∑' α : M, ∑ Idx, ∑ Jdx, summand α Idx Jdx :=
    ENNReal.sum_le_tsum Sf
  have h_total_le :
      (∑ α ∈ Sf, ∑ Idx, ∑ Jdx, lhsEsq α Idx Jdx) ≤
        ENNReal.ofReal Cmax * tensorPouSobolevHsNormSq (I := I) (M := M) g 0 T := by
    rw [h_summand_eq_normSq]
    refine h_sum_le.trans ?_
    gcongr

  have h_lhsEsq_ne_top : ∀ α Idx Jdx, lhsEsq α Idx Jdx ≠ ⊤ := by
    intro α Idx Jdx
    rw [hlhsEsq_def]
    refine (ENNReal.pow_ne_top ?_)
    exact (tensorChartComponentScalar_eLpNorm_two_lt_top
      (I := I) (M := M) (E := E) g r s T α Idx Jdx).ne
  have h_normSq_ne_top :
      tensorPouSobolevHsNormSq (I := I) (M := M) g 0 T ≠ ⊤ :=
    (tensorPouSobolevHsNormSq_lt_top (I := I) (M := M) g 0 T).ne
  have h_rhs_ne_top :
      ENNReal.ofReal Cmax * tensorPouSobolevHsNormSq (I := I) (M := M) g 0 T ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top h_normSq_ne_top
  have h_toReal := ENNReal.toReal_mono h_rhs_ne_top h_total_le
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hCmax_nn] at h_toReal

  have h_lhs_toReal :
      (∑ α ∈ Sf, ∑ Idx, ∑ Jdx, lhsEsq α Idx Jdx).toReal =
        ∑ α ∈ Sf, ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            ((MeasureTheory.eLpNorm
                (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar
                  (I := I) (M := M) g r s T α Idx Jdx) 2
                (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure
                  (I := I) (M := M) g)).toReal) ^ 2 := by
    rw [ENNReal.toReal_sum (fun α _ => ?_)]
    · refine Finset.sum_congr rfl (fun α _ => ?_)
      rw [ENNReal.toReal_sum (fun Idx _ => ?_)]
      · refine Finset.sum_congr rfl (fun Idx _ => ?_)
        rw [ENNReal.toReal_sum (fun Jdx _ => h_lhsEsq_ne_top α Idx Jdx)]
        refine Finset.sum_congr rfl (fun Jdx _ => ?_)
        rw [hlhsEsq_def, ENNReal.toReal_pow]
      · exact ENNReal.sum_ne_top.mpr (fun Jdx _ => h_lhsEsq_ne_top α Idx Jdx)
    · exact ENNReal.sum_ne_top.mpr (fun Idx _ =>
        ENNReal.sum_ne_top.mpr (fun Jdx _ => h_lhsEsq_ne_top α Idx Jdx))
  rw [hSf_def] at h_lhs_toReal
  rw [← h_lhs_toReal]
  exact h_toReal

end ReverseOrderZeroBridge

end DifferentialGeometry.PDE.RicciFlow
