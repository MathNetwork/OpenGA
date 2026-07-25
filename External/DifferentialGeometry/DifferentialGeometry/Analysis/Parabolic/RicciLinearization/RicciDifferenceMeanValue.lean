import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnection
import DifferentialGeometry.Analysis.Parabolic.DeTurckLinearization.MetricFamilyChartLinearization
import DifferentialGeometry.Geometry.Connection.ChartBridge.Ricci
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifference
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckMetricArmCoeffField
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.LocalFormula
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciDifferenceMeanValueJointChartCurvatureSmoothness
import DifferentialGeometry.Bundle.RicciDifferenceMeanValueClmSectionJointSmoothness
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciDifferenceMeanValueJointTensorFieldSmoothness


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 1600000

open Set Function MeasureTheory intervalIntegral Bundle Tensor0SBundle
open scoped Topology Manifold BigOperators ContDiff Matrix

namespace DifferentialGeometry
namespace PDE
namespace DeTurck
namespace RicciLinearization

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.PDE.DeTurck.DeTurckLinearization
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem ccTensorMultilinear_add (g : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g 0 2) (x : M) :
    (ccTensorMultilinear (I := I) g (T + T') x : Tensor0SSpace 2 I x)
      = (ccTensorMultilinear (I := I) g T x : Tensor0SSpace 2 I x)
        + (ccTensorMultilinear (I := I) g T' x : Tensor0SSpace 2 I x) := by
  unfold ccTensorMultilinear
  rw [SmoothCcTensor.toSection_add]
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem ccTensorModel_add (g : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g 0 2) (x : M) :
    ccTensorModel (I := I) g (T + T') x =
      ccTensorModel (I := I) g T x + ccTensorModel (I := I) g T' x := by
  unfold ccTensorModel
  rw [ccTensorMultilinear_add, Tensor0SSpace.toModel_add]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem ccTensorBilinSymm_add (g : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g 0 2) (x : M) (v w : TangentSpace I x) :
    ccTensorBilinSymm (I := I) g (T + T') x v w =
      ccTensorBilinSymm (I := I) g T x v w + ccTensorBilinSymm (I := I) g T' x v w := by
  simp only [ccTensorBilinSymm_apply, ccTensorBilin_apply, ccTensorModel_add,
    ContinuousMultilinearMap.add_apply]
  ring

def convexPerturbation (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2) (s : ℝ) : SmoothCcTensor g₀ 0 2 :=
  (1 - s) • T' + s • T

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
@[simp] lemma convexPerturbation_zero (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2) :
    convexPerturbation (I := I) g₀ T T' 0 = T' := by
  simp [convexPerturbation]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
@[simp] lemma convexPerturbation_one (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2) :
    convexPerturbation (I := I) g₀ T T' 1 = T := by
  simp [convexPerturbation]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma ccTensorBilinSymm_convexPerturbation (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2) (s : ℝ) (x : M) (v w : TangentSpace I x) :
    ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s) x v w =
      (1 - s) * ccTensorBilinSymm (I := I) g₀ T' x v w +
        s * ccTensorBilinSymm (I := I) g₀ T x v w := by
  rw [convexPerturbation, ccTensorBilinSymm_add, ccTensorBilinSymm_smul,
    ccTensorBilinSymm_smul]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem convexPerturbation_gFibreOpBound (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s))
      ((1 - s) * δ' + s * δ) := by
  intro x v w
  have hsqv : (0 : ℝ) ≤ Real.sqrt (g₀.inner x v v) := Real.sqrt_nonneg _
  have hsqw : (0 : ℝ) ≤ Real.sqrt (g₀.inner x w w) := Real.sqrt_nonneg _
  have hprod : (0 : ℝ) ≤ Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) :=
    mul_nonneg hsqv hsqw
  have h1ms : (0 : ℝ) ≤ 1 - s := by linarith
  have hbT := hδ x v w
  have hbT' := hδ' x v w
  rw [ccTensorBilinSymm_convexPerturbation]
  calc
    |(1 - s) * ccTensorBilinSymm (I := I) g₀ T' x v w +
        s * ccTensorBilinSymm (I := I) g₀ T x v w|
        ≤ |(1 - s) * ccTensorBilinSymm (I := I) g₀ T' x v w| +
            |s * ccTensorBilinSymm (I := I) g₀ T x v w| := abs_add_le _ _
    _ = (1 - s) * |ccTensorBilinSymm (I := I) g₀ T' x v w| +
            s * |ccTensorBilinSymm (I := I) g₀ T x v w| := by
        rw [abs_mul, abs_mul, abs_of_nonneg h1ms, abs_of_nonneg hs0]
    _ ≤ (1 - s) * (δ' * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w)) +
            s * (δ * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w)) := by
        gcongr
    _ = ((1 - s) * δ' + s * δ) * Real.sqrt (g₀.inner x v v) *
            Real.sqrt (g₀.inner x w w) := by ring

theorem convex_smallConstant_lt_one {δ δ' : ℝ} (hδ_lt : δ < 1) (hδ'_lt : δ' < 1)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (1 - s) * δ' + s * δ < 1 := by
  have h1ms : (0 : ℝ) ≤ 1 - s := by linarith
  nlinarith [mul_nonneg h1ms (le_of_lt (by linarith : (0 : ℝ) < 1 - δ')),
    mul_nonneg hs0 (le_of_lt (by linarith : (0 : ℝ) < 1 - δ))]

def realizedMetricPath (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    SmoothRiemannianMetric I M :=
  tensorSectionRealizeMetric (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s)
    (convex_smallConstant_lt_one hδ_lt hδ'_lt hs0 hs1)
    (convexPerturbation_gFibreOpBound (I := I) g₀ T T' hδ hδ' hs0 hs1)

omit [CompactSpace M] in
theorem realizedMetricPath_inner (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (x : M) (v w : TangentSpace I x) :
    (realizedMetricPath (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' hs0 hs1).inner x v w =
      g₀.inner x v w +
        ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s) x v w := by
  rw [realizedMetricPath, tensorSectionRealizeMetric_inner]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem riemannianMetric_eq_of_inner (g g' : SmoothRiemannianMetric I M)
    (h : ∀ (b : M) (v w : TangentSpace I b), g.inner b v w = g'.inner b v w) :
    g = g' := by
  have hinner : g.inner = g'.inner := by
    funext b
    exact ContinuousLinearMap.ext fun v => ContinuousLinearMap.ext fun w => h b v w
  cases g; cases g'
  congr

private lemma clamp_eq_of_mem_Icc {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    max 0 (min s 1) = s := by
  obtain ⟨hs0, hs1⟩ := hs
  rw [min_eq_left hs1, max_eq_right hs0]

def realizedRicciPathValue (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) (s : ℝ) : ℝ :=
  ricciTensor (I := I)
    (realizedMetricPath (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
      (le_max_left 0 (min s 1)) (by
        have : min s 1 ≤ 1 := min_le_right s 1
        exact max_le (zero_le_one) this)) x v w

omit [CompactSpace M] in
theorem realizedRicciPathValue_one (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) :
    realizedRicciPathValue (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w 1 =
      ricciTensor (I := I) (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ) x v w := by
  rw [realizedRicciPathValue]
  have hmetric :
      realizedMetricPath (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
          (le_max_left 0 (min (1 : ℝ) 1))
          (max_le (zero_le_one) (le_trans (min_le_right (1 : ℝ) 1) (le_refl 1))) =
        tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ := by
    refine riemannianMetric_eq_of_inner _ _ (fun b u z => ?_)
    rw [realizedMetricPath_inner, tensorSectionRealizeMetric_inner,
      ccTensorBilinSymm_convexPerturbation]
    have : max (0 : ℝ) (min 1 1) = 1 := by norm_num
    rw [this]; ring
  rw [hmetric]

omit [CompactSpace M] in
theorem realizedRicciPathValue_zero (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) :
    realizedRicciPathValue (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w 0 =
      ricciTensor (I := I) (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ') x v w := by
  rw [realizedRicciPathValue]
  have hmetric :
      realizedMetricPath (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
          (le_max_left 0 (min (0 : ℝ) 1))
          (max_le (zero_le_one) (le_trans (min_le_right (0 : ℝ) 1) (le_refl 1))) =
        tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ' := by
    refine riemannianMetric_eq_of_inner _ _ (fun b u z => ?_)
    rw [realizedMetricPath_inner, tensorSectionRealizeMetric_inner,
      ccTensorBilinSymm_convexPerturbation]
    have : max (0 : ℝ) (min 0 1) = 0 := by norm_num
    rw [this]; ring
  rw [hmetric]

def linearizedRicciAt (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) (s₀ : ℝ) : ℝ :=
  deriv (realizedRicciPathValue (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w) s₀

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem convexPerturbation_gFibreOpBound_abs (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) :
    metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s))
      (|1 - s| * δ' + |s| * δ) := by
  intro x v w
  have hbT := hδ x v w
  have hbT' := hδ' x v w
  rw [ccTensorBilinSymm_convexPerturbation]
  calc
    |(1 - s) * ccTensorBilinSymm (I := I) g₀ T' x v w +
        s * ccTensorBilinSymm (I := I) g₀ T x v w|
        ≤ |(1 - s) * ccTensorBilinSymm (I := I) g₀ T' x v w| +
            |s * ccTensorBilinSymm (I := I) g₀ T x v w| := abs_add_le _ _
    _ = |1 - s| * |ccTensorBilinSymm (I := I) g₀ T' x v w| +
            |s| * |ccTensorBilinSymm (I := I) g₀ T x v w| := by rw [abs_mul, abs_mul]
    _ ≤ |1 - s| * (δ' * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w)) +
            |s| * (δ * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w)) := by
        have ha1 : (0:ℝ) ≤ |1 - s| := abs_nonneg _
        have ha2 : (0:ℝ) ≤ |s| := abs_nonneg _
        gcongr
    _ = (|1 - s| * δ' + |s| * δ) * Real.sqrt (g₀.inner x v v) *
            Real.sqrt (g₀.inner x w w) := by ring

theorem abs_convex_smallConstant_lt_one {δ δ' : ℝ} (hδ_lt : δ < 1) (hδ'_lt : δ' < 1)
    {s : ℝ} (hs : s ∈ Set.Icc (0:ℝ) 1) :
    |1 - s| * δ' + |s| * δ < 1 := by
  obtain ⟨h0, h1⟩ := hs
  rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - s), abs_of_nonneg h0]
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - s) (by linarith : (0:ℝ) < 1 - δ').le,
    mul_nonneg h0 (by linarith : (0:ℝ) < 1 - δ).le]

def realizedMetricPathOpen (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) (hs : |1 - s| * δ' + |s| * δ < 1) :
    SmoothRiemannianMetric I M :=
  tensorSectionRealizeMetric (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s)
    hs (convexPerturbation_gFibreOpBound_abs (I := I) g₀ T T' hδ hδ' s)

omit [CompactSpace M] in
theorem realizedMetricPathOpen_inner (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) (hs : |1 - s| * δ' + |s| * δ < 1) (x : M) (v w : TangentSpace I x) :
    (realizedMetricPathOpen (I := I) g₀ T T' hδ hδ' s hs).inner x v w =
      g₀.inner x v w +
        ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s) x v w := by
  rw [realizedMetricPathOpen, tensorSectionRealizeMetric_inner]

def realizedSmallSet {δ δ' : ℝ} : Set ℝ := {s : ℝ | |1 - s| * δ' + |s| * δ < 1}

theorem realizedSmallSet_isOpen {δ δ' : ℝ} :
    IsOpen (realizedSmallSet (δ := δ) (δ' := δ')) := by
  have hcont : Continuous (fun s : ℝ => |1 - s| * δ' + |s| * δ) := by fun_prop
  exact isOpen_lt hcont continuous_const

theorem Icc_subset_realizedSmallSet {δ δ' : ℝ} (hδ_lt : δ < 1) (hδ'_lt : δ' < 1) :
    Set.Icc (0:ℝ) 1 ⊆ realizedSmallSet (δ := δ) (δ' := δ') :=
  fun _ hs => abs_convex_smallConstant_lt_one hδ_lt hδ'_lt hs

def realizedFam (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) : SmoothRiemannianMetric I M :=
  if h : |1 - s| * δ' + |s| * δ < 1 then
    realizedMetricPathOpen (I := I) g₀ T T' hδ hδ' s h
  else g₀

omit [CompactSpace M] in
theorem realizedFam_inner_of_mem (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    {s : ℝ} (hs : s ∈ realizedSmallSet (δ := δ) (δ' := δ')) (x : M) (v w : TangentSpace I x) :
    (realizedFam (I := I) g₀ T T' hδ hδ' s).inner x v w =
      g₀.inner x v w +
        ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s) x v w := by
  rw [realizedFam, dif_pos (Set.mem_setOf.mp hs), realizedMetricPathOpen_inner]

omit [CompactSpace M] in
theorem realizedFam_chartGramOnE (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    {s : ℝ} (hs : s ∈ realizedSmallSet (δ := δ) (δ' := δ'))
    (α : M) (i j : Fin (Module.finrank ℝ E)) (y : E) :
    chartGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) α i j y =
      (1 - s) *
          chartGramOnE (I := I) (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ') α i j y +
        s * chartGramOnE (I := I) (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ) α i j y := by
  rw [chartGramOnE_def, chartGramOnE_def, chartGramOnE_def, chartGramMatrix_apply,
    chartGramMatrix_apply, chartGramMatrix_apply,
    realizedFam_inner_of_mem (I := I) g₀ T T' hδ hδ' hs,
    tensorSectionRealizeMetric_inner, tensorSectionRealizeMetric_inner,
    ccTensorBilinSymm_convexPerturbation]
  ring

omit [CompactSpace M] in
theorem realizedFam_genJointGram (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (α : M) :
    ChartGramFamilyJointSmoothNondegenerate (I := I) (realizedFam (I := I) g₀ T T' hδ hδ') α
      (realizedSmallSet (δ := δ) (δ' := δ')) := by
  refine ⟨?_, ?_⟩
  · intro i j s₀ y₀ hs hy
    have hSopen : IsOpen (realizedSmallSet (δ := δ) (δ' := δ')) := realizedSmallSet_isOpen
    set F : E → ℝ :=
      chartGramOnE (I := I) (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ') α i j with hF
    set G : E → ℝ :=
      chartGramOnE (I := I) (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ) α i j with hG
    have heq : (fun p : ℝ × E =>
          chartGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.1) α i j p.2)
        =ᶠ[nhds (s₀, y₀)] (fun p : ℝ × E => (1 - p.1) * F p.2 + p.1 * G p.2) := by
      have hmem : (realizedSmallSet (δ := δ) (δ' := δ')) ×ˢ (Set.univ : Set E) ∈ nhds (s₀, y₀) :=
        (hSopen.prod isOpen_univ).mem_nhds ⟨hs, Set.mem_univ _⟩
      filter_upwards [hmem] with p hp
      exact realizedFam_chartGramOnE (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' hp.1 α i j p.2
    refine ContDiffAt.congr_of_eventuallyEq ?_ heq
    have hFc : ContDiffAt ℝ ∞ (fun p : ℝ × E => F p.2) (s₀, y₀) :=
      (((chartGramOnE_contDiffOn (I := I) _ α i j).mono interior_subset).contDiffAt
        (isOpen_interior.mem_nhds hy)).comp (s₀, y₀) contDiffAt_snd
    have hGc : ContDiffAt ℝ ∞ (fun p : ℝ × E => G p.2) (s₀, y₀) :=
      (((chartGramOnE_contDiffOn (I := I) _ α i j).mono interior_subset).contDiffAt
        (isOpen_interior.mem_nhds hy)).comp (s₀, y₀) contDiffAt_snd
    exact ((contDiffAt_const.sub contDiffAt_fst).mul hFc).add (contDiffAt_fst.mul hGc)
  · intro s₀ _ x hx
    exact chartGramMatrix_det_pos (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) α hx

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma chartBilinSymmEntry_contMDiffOn (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (α : M) (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun x => ccTensorBilinSymm (I := I) g₀ T x
        (chartBasisVecFiber (I := I) α i x) (chartBasisVecFiber (I := I) α j x))
      (trivializationAt E (TangentSpace I) α).baseSet := by
  have hB := ccTensorBilinSymm_contMDiff (I := I) g₀ T
  have hv := chartBasisVec_contMDiffOn (I := I) α i
  have hw := chartBasisVec_contMDiffOn (I := I) α j
  have happ :
      ContMDiffOn I (I.prod 𝓘(ℝ, ℝ)) ∞
        (fun m : M => (⟨m,
            ccTensorBilinSymm (I := I) g₀ T m
              (chartBasisVecFiber (I := I) α i m)
              (chartBasisVecFiber (I := I) α j m)⟩ :
              TotalSpace ℝ (Bundle.Trivial M ℝ)))
        (trivializationAt E (TangentSpace I) α).baseSet :=
    ContMDiffOn.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ)
      (b := id) hB.contMDiffOn hv hw
  intro x hx
  have hpx := happ x hx
  rw [Bundle.contMDiffWithinAt_totalSpace] at hpx
  exact hpx.2

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma chartBilinSymmOnE_contDiffOn (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (α : M) (i j : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun y : E => ccTensorBilinSymm (I := I) g₀ T ((extChartAt I α).symm y)
        (chartBasisVecFiber (I := I) α i ((extChartAt I α).symm y))
        (chartBasisVecFiber (I := I) α j ((extChartAt I α).symm y)))
      (extChartAt I α).target := by
  have hbase := chartBilinSymmEntry_contMDiffOn (I := I) g₀ T α i j
  have hsymm : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I α).symm
      (extChartAt I α).target := contMDiffOn_extChartAt_symm (I := I) α
  have hsubset : (extChartAt I α).target ⊆
      (extChartAt I α).symm ⁻¹'
        (trivializationAt E (TangentSpace I) α).baseSet := by
    intro y hy
    have hsource : (extChartAt I α).symm y ∈ (extChartAt I α).source :=
      (extChartAt I α).map_target hy
    rw [extChartAt_source_eq_chartAt_source (I := I)] at hsource
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact hsource
  exact (hbase.comp hsymm hsubset).contDiffOn

omit [CompactSpace M] in
theorem realizedFam_genJointGram_free (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (α : M) :
    ChartGramFamilyJointSmoothNondegenerate (I := I) (realizedFam (I := I) g₀ T T' hδ hδ') α
      (realizedSmallSet (δ := δ) (δ' := δ')) := by
  refine ⟨?_, ?_⟩
  · intro i j s₀ y₀ hs hy
    have hSopen : IsOpen (realizedSmallSet (δ := δ) (δ' := δ')) := realizedSmallSet_isOpen
    have heq : (fun p : ℝ × E =>
          chartGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.1) α i j p.2)
        =ᶠ[nhds (s₀, y₀)] (fun p : ℝ × E =>
          chartGramOnE (I := I) g₀ α i j p.2 +
            ((1 - p.1) * (fun y : E => ccTensorBilinSymm (I := I) g₀ T' ((extChartAt I α).symm y)
                (chartBasisVecFiber (I := I) α i ((extChartAt I α).symm y))
                (chartBasisVecFiber (I := I) α j ((extChartAt I α).symm y))) p.2 +
              p.1 * (fun y : E => ccTensorBilinSymm (I := I) g₀ T ((extChartAt I α).symm y)
                (chartBasisVecFiber (I := I) α i ((extChartAt I α).symm y))
                (chartBasisVecFiber (I := I) α j ((extChartAt I α).symm y))) p.2)) := by
      have hmem : (realizedSmallSet (δ := δ) (δ' := δ')) ×ˢ (Set.univ : Set E) ∈ nhds (s₀, y₀) :=
        (hSopen.prod isOpen_univ).mem_nhds ⟨hs, Set.mem_univ _⟩
      filter_upwards [hmem] with p hp
      have hps : p.1 ∈ realizedSmallSet (δ := δ) (δ' := δ') := hp.1
      rw [chartGramOnE_def, chartGramMatrix_apply,
        realizedFam_inner_of_mem (I := I) g₀ T T' hδ hδ' hps,
        ccTensorBilinSymm_convexPerturbation, chartGramOnE_def, chartGramMatrix_apply]
    refine ContDiffAt.congr_of_eventuallyEq ?_ heq
    have hsnd : ContDiffAt ℝ ∞ (Prod.snd : ℝ × E → E) (s₀, y₀) := contDiffAt_snd
    have hG₀c : ContDiffAt ℝ ∞ (fun p : ℝ × E => chartGramOnE (I := I) g₀ α i j p.2) (s₀, y₀) := by
      have h0 := (((chartGramOnE_contDiffOn (I := I) g₀ α i j).mono interior_subset).contDiffAt
        (isOpen_interior.mem_nhds hy)).comp (s₀, y₀) hsnd
      exact h0
    have hBc : ContDiffAt ℝ ∞ (fun p : ℝ × E =>
        ccTensorBilinSymm (I := I) g₀ T ((extChartAt I α).symm p.2)
          (chartBasisVecFiber (I := I) α i ((extChartAt I α).symm p.2))
          (chartBasisVecFiber (I := I) α j ((extChartAt I α).symm p.2))) (s₀, y₀) := by
      have h0 := (((chartBilinSymmOnE_contDiffOn (I := I) g₀ T α i j).mono interior_subset).contDiffAt
        (isOpen_interior.mem_nhds hy)).comp (s₀, y₀) hsnd
      exact h0
    have hB'c : ContDiffAt ℝ ∞ (fun p : ℝ × E =>
        ccTensorBilinSymm (I := I) g₀ T' ((extChartAt I α).symm p.2)
          (chartBasisVecFiber (I := I) α i ((extChartAt I α).symm p.2))
          (chartBasisVecFiber (I := I) α j ((extChartAt I α).symm p.2))) (s₀, y₀) := by
      have h0 := (((chartBilinSymmOnE_contDiffOn (I := I) g₀ T' α i j).mono interior_subset).contDiffAt
        (isOpen_interior.mem_nhds hy)).comp (s₀, y₀) hsnd
      exact h0
    exact hG₀c.add (((contDiffAt_const.sub contDiffAt_fst).mul hB'c).add (contDiffAt_fst.mul hBc))
  · intro s₀ _ x hx
    exact chartGramMatrix_det_pos (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) α hx

omit [CompactSpace M] in
theorem realizedFam_chartInvGramMatrix_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (α : M) (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun p : M × ℝ => chartInvGramMatrix (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' p.2) α p.1 i j)
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  have hG := realizedFam_genJointGram (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' α
  have hmove : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => (p.2, extChartAt I α p.1))
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
    refine ContMDiffOn.prodMk contMDiffOn_snd ?_
    exact (contMDiffOn_extChartAt (I := I) (x := α)).comp contMDiffOn_fst (fun p hp => hp.1)
  intro p hp
  obtain ⟨hx, hs⟩ := hp
  have hxsrc : p.1 ∈ (extChartAt I α).source := by rw [extChartAt_source (I := I)]; exact hx
  have hy : extChartAt I α p.1 ∈ interior (extChartAt I α).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α
      ((extChartAt I α).map_source hxsrc)
  have hentry := chartInvGramOnE_contDiffAt_joint (I := I)
    (realizedFam (I := I) g₀ T T' hδ hδ') α hG i j hs hy
  have hentryM : ContMDiffAt (𝓘(ℝ, ℝ × E)) 𝓘(ℝ) ∞
      (fun r : ℝ × E => chartInvGramOnE (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' r.1) α i j r.2) (p.2, extChartAt I α p.1) :=
    hentry.contMDiffAt
  have hmoveAt : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ × E)) ∞
      (fun p : M × ℝ => (p.2, extChartAt I α p.1))
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) p := by
    have hm := hmove p ⟨hx, hs⟩
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hm
    exact hm
  refine (hentryM.comp_contMDiffWithinAt p hmoveAt).congr ?_ ?_
  · intro q hq
    have hqx : q.1 ∈ (extChartAt I α).source := by rw [extChartAt_source (I := I)]; exact hq.1
    rw [Function.comp_apply, chartInvGramOnE_def, (extChartAt I α).left_inv hqx]
  · rw [Function.comp_apply, chartInvGramOnE_def, (extChartAt I α).left_inv hxsrc]

omit [CompactSpace M] in
theorem realizedFam_chartInvGramMatrix_jointContMDiffOn_free
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (α : M) (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun p : M × ℝ => chartInvGramMatrix (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' p.2) α p.1 i j)
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  have hG := realizedFam_genJointGram_free (I := I) g₀ T T' hδ hδ' α
  have hmove : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => (p.2, extChartAt I α p.1))
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
    refine ContMDiffOn.prodMk contMDiffOn_snd ?_
    exact (contMDiffOn_extChartAt (I := I) (x := α)).comp contMDiffOn_fst (fun p hp => hp.1)
  intro p hp
  obtain ⟨hx, hs⟩ := hp
  have hxsrc : p.1 ∈ (extChartAt I α).source := by rw [extChartAt_source (I := I)]; exact hx
  have hy : extChartAt I α p.1 ∈ interior (extChartAt I α).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α
      ((extChartAt I α).map_source hxsrc)
  have hentry := chartInvGramOnE_contDiffAt_joint (I := I)
    (realizedFam (I := I) g₀ T T' hδ hδ') α hG i j hs hy
  have hentryM : ContMDiffAt (𝓘(ℝ, ℝ × E)) 𝓘(ℝ) ∞
      (fun r : ℝ × E => chartInvGramOnE (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' r.1) α i j r.2) (p.2, extChartAt I α p.1) :=
    hentry.contMDiffAt
  have hmoveAt : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ × E)) ∞
      (fun p : M × ℝ => (p.2, extChartAt I α p.1))
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) p := by
    have hm := hmove p ⟨hx, hs⟩
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hm
    exact hm
  refine (hentryM.comp_contMDiffWithinAt p hmoveAt).congr ?_ ?_
  · intro q hq
    have hqx : q.1 ∈ (extChartAt I α).source := by rw [extChartAt_source (I := I)]; exact hq.1
    rw [Function.comp_apply, chartInvGramOnE_def, (extChartAt I α).left_inv hqx]
  · rw [Function.comp_apply, chartInvGramOnE_def, (extChartAt I α).left_inv hxsrc]

open DifferentialGeometry.Integral.DivergenceTheorem in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem chartBasisVec_jointContMDiffOn (α : M) (i : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1
        (chartBasisVecFiber (I := I) α i p.1))
      ((chartAt H α).source ×ˢ (Set.univ : Set ℝ)) := by
  have hbase := chartBasisVec_contMDiffOn (I := I) α i
  have hbase_eq : (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source :=
    trivializationAt_baseSet_eq_chartAt_source (I := I) α
  rw [hbase_eq] at hbase
  exact hbase.comp contMDiffOn_fst (fun p hp => hp.1)

open DifferentialGeometry.Integral.DivergenceTheorem in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem metricSharpChartCoeff_jointContMDiffOn
    (gfam : ℝ → SmoothRiemannianMetric I M) (α : M)
    (cv : ℝ → Π b : M, TangentSpace I b →ₗ[ℝ] ℝ) {S : Set ℝ}
    (hinv : ∀ i j : Fin (Module.finrank ℝ E),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
        (fun p : M × ℝ => chartInvGramMatrix (I := I) (gfam p.2) α p.1 i j)
        ((chartAt H α).source ×ˢ S))
    (hcv : ∀ j : Fin (Module.finrank ℝ E),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
        (fun p : M × ℝ => cv p.2 p.1 (chartBasisVecFiber (I := I) α j p.1))
        ((chartAt H α).source ×ˢ S))
    (i : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun p : M × ℝ => metricSharpChartCoeff (I := I) (gfam p.2) α (cv p.2) i p.1)
      ((chartAt H α).source ×ˢ S) := by
  classical
  have heq : (fun p : M × ℝ => metricSharpChartCoeff (I := I) (gfam p.2) α (cv p.2) i p.1) =
      (fun p : M × ℝ => ∑ j : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (gfam p.2) α p.1 i j *
          cv p.2 p.1 (chartBasisVecFiber (I := I) α j p.1)) := by
    funext p; rw [metricSharpChartCoeff_def]
  rw [heq]
  exact contMDiffOn_finset_sum (fun j _ => (hinv i j).mul (hcv j))

open DifferentialGeometry.Integral.DivergenceTheorem in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem metricSharpChartLocal_jointContMDiffOn
    (gfam : ℝ → SmoothRiemannianMetric I M) (α : M)
    (cv : ℝ → Π b : M, TangentSpace I b →ₗ[ℝ] ℝ) {S : Set ℝ}
    (hinv : ∀ i j : Fin (Module.finrank ℝ E),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
        (fun p : M × ℝ => chartInvGramMatrix (I := I) (gfam p.2) α p.1 i j)
        ((chartAt H α).source ×ˢ S))
    (hcv : ∀ j : Fin (Module.finrank ℝ E),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
        (fun p : M × ℝ => cv p.2 p.1 (chartBasisVecFiber (I := I) α j p.1))
        ((chartAt H α).source ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1
        (metricSharpChartLocal (I := I) (gfam p.2) α (cv p.2) p.1))
      ((chartAt H α).source ×ˢ S) := by
  classical
  have hcoeff : ∀ i, ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun p : M × ℝ => metricSharpChartCoeff (I := I) (gfam p.2) α (cv p.2) i p.1)
      ((chartAt H α).source ×ˢ S) :=
    fun i => metricSharpChartCoeff_jointContMDiffOn (I := I) gfam α cv hinv hcv i
  set e := trivializationAt E (TangentSpace I) α with he

  have hcoord_eq : ∀ q ∈ (chartAt H α).source ×ˢ S,
      (e ⟨q.1, metricSharpChartLocal (I := I) (gfam q.2) α (cv q.2) q.1⟩).2 =
        ∑ i, metricSharpChartCoeff (I := I) (gfam q.2) α (cv q.2) i q.1 •
          (chartModelBasis E) i := by
    rintro q ⟨hqx, _⟩
    have hqbase : q.1 ∈ e.baseSet := by
      rw [he, trivializationAt_baseSet_eq_chartAt_source (I := I)]; exact hqx
    have hclm : ∀ w : TangentSpace I q.1,
        (e ⟨q.1, w⟩).2 = e.continuousLinearMapAt ℝ q.1 w := fun w => by
      rw [Trivialization.continuousLinearMapAt_apply]
      exact (congrFun (Trivialization.coe_linearMapAt_of_mem (R := ℝ) (e := e) hqbase) w).symm
    unfold metricSharpChartLocal
    rw [hclm, map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_smul, ← hclm]
    congr 1
    rw [trivializationAt_chartBasisVec_snd (I := I) α i hqbase]

  have hcoordSmooth : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
      (fun q : M × ℝ => (e ⟨q.1, metricSharpChartLocal (I := I) (gfam q.2) α (cv q.2) q.1⟩).2)
      ((chartAt H α).source ×ˢ S) := by
    refine ContMDiffOn.congr ?_ hcoord_eq
    refine contMDiffOn_finset_sum (fun i _ => ?_)
    exact (hcoeff i).smul contMDiffOn_const

  haveI : MemTrivializationAtlas e := by rw [he]; infer_instance
  rw [Bundle.Trivialization.contMDiffOn_iff (e := e) ?_]
  · exact ⟨contMDiffOn_fst, hcoordSmooth⟩
  · rintro q ⟨hqx, _⟩
    rw [Trivialization.mem_source, he, trivializationAt_baseSet_eq_chartAt_source (I := I)]
    exact hqx

open DifferentialGeometry.Integral.DivergenceTheorem in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem metricSharp_jointContMDiffOn
    (gfam : ℝ → SmoothRiemannianMetric I M)
    (cv : ℝ → Π b : M, TangentSpace I b →ₗ[ℝ] ℝ) {S : Set ℝ} (hS : IsOpen S)
    (hinv : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
        (fun p : M × ℝ => chartInvGramMatrix (I := I) (gfam p.2) α p.1 i j)
        ((chartAt H α).source ×ˢ S))
    (hcv : ∀ (α : M) (j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
        (fun p : M × ℝ => cv p.2 p.1 (chartBasisVecFiber (I := I) α j p.1))
        ((chartAt H α).source ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1
        (DifferentialGeometry.Integral.DivergenceTheorem.metricSharp
          (I := I) (gfam p.2) p.1 (cv p.2 p.1)))
      (Set.univ ×ˢ S) := by
  intro p hp
  obtain ⟨_, hps⟩ := hp

  have hlocal := metricSharpChartLocal_jointContMDiffOn (I := I) gfam p.1 cv
    (hinv p.1) (hcv p.1)

  have heqOn : ∀ q ∈ (chartAt H p.1).source ×ˢ S,
      TotalSpace.mk' E (E := fun z : M => TangentSpace I z) q.1
          (metricSharpChartLocal (I := I) (gfam q.2) p.1 (cv q.2) q.1) =
        TotalSpace.mk' E (E := fun z : M => TangentSpace I z) q.1
          (DifferentialGeometry.Integral.DivergenceTheorem.metricSharp
            (I := I) (gfam q.2) q.1 (cv q.2 q.1)) := by
    rintro q ⟨hqx, _⟩
    have hqbase : q.1 ∈ (trivializationAt E (TangentSpace I) p.1).baseSet := by
      rw [trivializationAt_baseSet_eq_chartAt_source (I := I)]; exact hqx
    rw [metricSharpChartLocal_eq_metricSharp (I := I) (gfam q.2) p.1 (cv q.2) hqbase]

  have hpmem : p ∈ (chartAt H p.1).source ×ˢ S := ⟨mem_chart_source H p.1, hps⟩
  have hnhd : (chartAt H p.1).source ×ˢ S ∈ nhdsWithin p (Set.univ ×ˢ S) := by
    refine mem_nhdsWithin.mpr ⟨(chartAt H p.1).source ×ˢ S,
      (chartAt H p.1).open_source.prod hS, hpmem, fun q hq => hq.1⟩

  have hlocalAt : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) q.1
        (metricSharpChartLocal (I := I) (gfam q.2) p.1 (cv q.2) q.1))
      (Set.univ ×ˢ S) p :=
    (hlocal p hpmem).mono_of_mem_nhdsWithin hnhd

  refine hlocalAt.congr_of_eventuallyEq ?_ (heqOn p hpmem).symm
  filter_upwards [hnhd] with q hq using (heqOn q hq).symm

open DifferentialGeometry.Integral.DivergenceTheorem in

omit [CompactSpace M] in
theorem inverseMetricSharpField_realizedFam_jointContMDiffOn [BoundarylessManifold I M]
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel 1 ℝ E →L[ℝ] E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel 1 ℝ E →L[ℝ] E)
        (E := fun z : M => Tensor0SSpace 1 I z →L[ℝ] TangentSpace I z) p.1
        (inverseMetricSharpFib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  apply contMDiffOn_clm_section_of_pointwise_joint_manifold_time (I := I) (M := M)
    (F₁ := Tensor0SModel 1 ℝ E) (V₁ := fun x : M => Tensor0SSpace 1 I x)
    (F₂ := E) (V₂ := fun x : M => TangentSpace I x)
    (φ := fun p : M × ℝ => inverseMetricSharpFib (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
  intro Y

  set cv : ℝ → Π b : M, TangentSpace I b →ₗ[ℝ] ℝ :=
    fun _ b => cotangentToDualLinear (I := I) (x := b) (Y b) with hcvdef
  have hinv : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
        (fun p : M × ℝ => chartInvGramMatrix (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' p.2) α p.1 i j)
        ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    fun α i j => realizedFam_chartInvGramMatrix_jointContMDiffOn_free
      (I := I) g₀ T T' hδ hδ' α i j
  have hcv : ∀ (α : M) (j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
        (fun p : M × ℝ => cv p.2 p.1 (chartBasisVecFiber (I := I) α j p.1))
        ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
    intro α j
    have hbase := cotangentSection_chartComponent_contMDiffOn (I := I) Y α j
    have heqfn : (fun p : M × ℝ => cv p.2 p.1 (chartBasisVecFiber (I := I) α j p.1)) =
        (fun p : M × ℝ => (fun b : M => Tensor0SSpace.toModel (Y b)
          (fun _ : Fin 1 => chartBasisVecFiber (I := I) α j b)) p.1) := by
      funext p
      rw [hcvdef]
      simp only
      rw [cotangentToDualLinear_apply, cotangentToDual_apply]
      rfl
    rw [heqfn]
    exact hbase.comp contMDiffOn_fst (fun p hp => hp.1)
  have hjoint := metricSharp_jointContMDiffOn (I := I)
    (gfam := fun s => realizedFam (I := I) g₀ T T' hδ hδ' s) (cv := cv)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) realizedSmallSet_isOpen hinv hcv
  refine hjoint.congr (fun p hp => ?_)

  change TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1
      (DifferentialGeometry.Integral.DivergenceTheorem.metricSharp
        (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1 (cv p.2 p.1)) =
    TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1
      (inverseMetricSharpFib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1 (Y p.1))
  rw [inverseMetricSharpFib_apply, hcvdef]

omit [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma gen_s_contDiffAt_ricci (gfam : ℝ → SmoothRiemannianMetric I M) (α : M)
    {S : Set ℝ} (hG : ChartGramFamilyJointSmoothNondegenerate (I := I) gfam α S)
    (i k : Fin (Module.finrank ℝ E)) {s₀ : ℝ} {y₀ : E} (hs : s₀ ∈ S)
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    ContDiffAt ℝ ∞ (fun s : ℝ => chartRicciTensor (I := I) (gfam s) α i k y₀) s₀ := by
  have hjoint := gen_joint_ricci (I := I) gfam α hG i k hs hy
  have hcomp : (fun s : ℝ => chartRicciTensor (I := I) (gfam s) α i k y₀) =
      (fun p : ℝ × E => chartRicciTensor (I := I) (gfam p.1) α i k p.2) ∘
        (fun s : ℝ => (s, y₀)) := by funext s; rfl
  rw [hcomp]
  exact hjoint.comp s₀ ((contDiffAt_id).prodMk contDiffAt_const)

omit [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma gen_s_contDiffAt_deTurckRicciRHS (gfam : ℝ → SmoothRiemannianMetric I M) (α : M)
    {S : Set ℝ} (hG : ChartGramFamilyJointSmoothNondegenerate (I := I) gfam α S) (g_bg : SmoothRiemannianMetric I M)
    (i k : Fin (Module.finrank ℝ E)) {s₀ : ℝ} {y₀ : E} (hs : s₀ ∈ S)
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    ContDiffAt ℝ ∞ (fun s : ℝ => chartDeTurckRicciRHS (I := I) (gfam s) g_bg α i k y₀) s₀ := by
  have hjoint := gen_joint_chartDeTurckRicciRHS (I := I) gfam α hG g_bg i k hs hy
  have hcomp : (fun s : ℝ => chartDeTurckRicciRHS (I := I) (gfam s) g_bg α i k y₀) =
      (fun p : ℝ × E => chartDeTurckRicciRHS (I := I) (gfam p.1) g_bg α i k p.2) ∘
        (fun s : ℝ => (s, y₀)) := by funext s; rfl
  rw [hcomp]
  exact hjoint.comp s₀ ((contDiffAt_id).prodMk contDiffAt_const)

omit [CompactSpace M] in
theorem realizedMetricPath_eq_realizedFam (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hmem : s ∈ realizedSmallSet (δ := δ) (δ' := δ')) :
    realizedMetricPath (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' hs0 hs1 =
      realizedFam (I := I) g₀ T T' hδ hδ' s := by
  refine riemannianMetric_eq_of_inner _ _ (fun b u z => ?_)
  rw [realizedMetricPath_inner, realizedFam_inner_of_mem (I := I) g₀ T T' hδ hδ' hmem]

def realizedRicciChartSum (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) (s : ℝ) : ℝ :=
  ∑ i, ∑ k,
    ((chartModelBasis E).repr v) k * ((chartModelBasis E).repr w) i *
      chartRicciTensor (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i k
        (extChartAt I x x)

omit [CompactSpace M] in
theorem realizedRicciChartSum_contDiffAt (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) {s₀ : ℝ}
    (hs : s₀ ∈ realizedSmallSet (δ := δ) (δ' := δ')) :
    ContDiffAt ℝ ∞ (realizedRicciChartSum (I := I) g₀ T T' hδ hδ' x v w) s₀ := by
  have hG := realizedFam_genJointGram (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x
  have hy : (extChartAt I x x) ∈ interior (extChartAt I x).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) x (mem_extChartAt_target x)
  unfold realizedRicciChartSum
  refine ContDiffAt.sum (fun i _ => ContDiffAt.sum (fun k _ => ?_))
  exact contDiffAt_const.mul (gen_s_contDiffAt_ricci (I := I) _ x hG i k hs hy)

omit [CompactSpace M] in
theorem realizedDeTurckRicciChartSum_contDiffAt (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) {s₀ : ℝ}
    (hs : s₀ ∈ realizedSmallSet (δ := δ) (δ' := δ')) :
    ContDiffAt ℝ ∞
      (fun s : ℝ => ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr v) k * ((chartModelBasis E).repr w) i *
          DifferentialGeometry.PDE.RicciFlow.chartFComponentOnE (I := I)
            (DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS (I := I) g_bg)
            (realizedFam (I := I) g₀ T T' hδ hδ' s) x i k (extChartAt I x x)) s₀ := by
  have hG := realizedFam_genJointGram (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x
  have hy : (extChartAt I x x) ∈ interior (extChartAt I x).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) x (mem_extChartAt_target x)
  have heq : (fun s : ℝ => ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr v) k * ((chartModelBasis E).repr w) i *
          DifferentialGeometry.PDE.RicciFlow.chartFComponentOnE (I := I)
            (DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS (I := I) g_bg)
            (realizedFam (I := I) g₀ T T' hδ hδ' s) x i k (extChartAt I x x)) =
      (fun s : ℝ => ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr v) k * ((chartModelBasis E).repr w) i *
          chartDeTurckRicciRHS (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x i k
            (extChartAt I x x)) := by
    funext s
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => ?_))
    rw [DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.chartFComponentOnE_deTurckRicciRHS_eq
      (I := I) g_bg (realizedFam (I := I) g₀ T T' hδ hδ' s) x i k hy]
  rw [heq]
  refine ContDiffAt.sum (fun i _ => ContDiffAt.sum (fun k _ => ?_))
  exact contDiffAt_const.mul
    (gen_s_contDiffAt_deTurckRicciRHS (I := I) _ x hG g_bg i k hs hy)

omit [CompactSpace M] in
theorem realizedRicciPathValue_eq_chartSum_on_Icc (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) {s : ℝ} (hs : s ∈ Set.Icc (0:ℝ) 1) :
    realizedRicciPathValue (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w s =
      realizedRicciChartSum (I := I) g₀ T T' hδ hδ' x v w s := by
  obtain ⟨h0, h1⟩ := hs
  have hmem : s ∈ realizedSmallSet (δ := δ) (δ' := δ') :=
    abs_convex_smallConstant_lt_one hδ_lt hδ'_lt ⟨h0, h1⟩
  have hclamp : max 0 (min s 1) = s := by rw [min_eq_left h1, max_eq_right h0]
  rw [realizedRicciPathValue]
  have hmetric :
      realizedMetricPath (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
          (le_max_left 0 (min s 1))
          (max_le (zero_le_one) (le_trans (min_le_right s 1) (le_refl 1))) =
        realizedFam (I := I) g₀ T T' hδ hδ' s := by
    refine riemannianMetric_eq_of_inner _ _ (fun b u z => ?_)
    rw [realizedMetricPath_inner, realizedFam_inner_of_mem (I := I) g₀ T T' hδ hδ' hmem,
      hclamp]
  rw [hmetric]

  rw [realizedRicciChartSum]
  exact ricciTensor_eq_chartRicciSwap_of_basis_identity (I := I)
    (realizedFam (I := I) g₀ T T' hδ hδ' s) x
    (chartRiemannBasisIdentity_holds (I := I) _ x) v w

omit [CompactSpace M] in
theorem realizedRicciPathValue_differentiableAt_Ioo (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) {s₀ : ℝ} (hs₀ : s₀ ∈ Set.Ioo (0:ℝ) 1) :
    DifferentiableAt ℝ
      (realizedRicciPathValue (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w) s₀ := by
  have heq : realizedRicciPathValue (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w
      =ᶠ[nhds s₀] realizedRicciChartSum (I := I) g₀ T T' hδ hδ' x v w := by
    filter_upwards [isOpen_Ioo.mem_nhds hs₀] with s hs
    exact realizedRicciPathValue_eq_chartSum_on_Icc (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w
      (Set.mem_Icc_of_Ioo hs)
  have hmem : s₀ ∈ realizedSmallSet (δ := δ) (δ' := δ') :=
    abs_convex_smallConstant_lt_one hδ_lt hδ'_lt ⟨hs₀.1.le, hs₀.2.le⟩
  exact ((realizedRicciChartSum_contDiffAt (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w
    hmem).differentiableAt (by simp)).congr_of_eventuallyEq heq

omit [CompactSpace M] in
theorem linearizedRicciAt_eq_deriv_chartSum_on_Ioo (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) {s : ℝ} (hs : s ∈ Set.Ioo (0:ℝ) 1) :
    linearizedRicciAt (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w s =
      deriv (realizedRicciChartSum (I := I) g₀ T T' hδ hδ' x v w) s := by
  have heq : realizedRicciPathValue (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w
      =ᶠ[nhds s] realizedRicciChartSum (I := I) g₀ T T' hδ hδ' x v w := by
    filter_upwards [isOpen_Ioo.mem_nhds hs] with t ht
    exact realizedRicciPathValue_eq_chartSum_on_Icc (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w
      (Set.mem_Icc_of_Ioo ht)
  rw [linearizedRicciAt]
  exact Filter.EventuallyEq.deriv_eq heq

omit [CompactSpace M] in
theorem deriv_realizedRicciChartSum_continuousOn (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) :
    ContinuousOn (deriv (realizedRicciChartSum (I := I) g₀ T T' hδ hδ' x v w))
      (realizedSmallSet (δ := δ) (δ' := δ')) := by
  have hcd : ContDiffOn ℝ ∞ (realizedRicciChartSum (I := I) g₀ T T' hδ hδ' x v w)
      (realizedSmallSet (δ := δ) (δ' := δ')) := fun s hs =>
    (realizedRicciChartSum_contDiffAt (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w
      hs).contDiffWithinAt
  exact hcd.continuousOn_deriv_of_isOpen realizedSmallSet_isOpen (by exact_mod_cast le_top)

omit [CompactSpace M] in
theorem linearizedRicciAt_intervalIntegrable (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) :
    IntervalIntegrable
      (linearizedRicciAt (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w)
      MeasureTheory.volume 0 1 := by

  have hcont : ContinuousOn (deriv (realizedRicciChartSum (I := I) g₀ T T' hδ hδ' x v w))
      (Set.Icc (0:ℝ) 1) :=
    (deriv_realizedRicciChartSum_continuousOn (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w).mono
      (Icc_subset_realizedSmallSet hδ_lt hδ'_lt)
  have hii : IntervalIntegrable
      (deriv (realizedRicciChartSum (I := I) g₀ T T' hδ hδ' x v w))
      MeasureTheory.volume 0 1 :=
    hcont.intervalIntegrable_of_Icc zero_le_one

  refine hii.congr_ae ?_
  have hsub : Set.Ioo (0:ℝ) 1 ⊆
      {s | deriv (realizedRicciChartSum (I := I) g₀ T T' hδ hδ' x v w) s =
        linearizedRicciAt (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w s} := by
    intro s hs
    exact (linearizedRicciAt_eq_deriv_chartSum_on_Ioo (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w
      hs).symm
  have hnull : (MeasureTheory.volume.restrict (Set.uIoc (0:ℝ) 1)) (Set.Ioo (0:ℝ) 1)ᶜ = 0 := by
    rw [Set.uIoc_of_le zero_le_one]
    rw [MeasureTheory.Measure.restrict_apply (measurableSet_Ioo.compl)]
    have hsub1 : (Set.Ioo (0:ℝ) 1)ᶜ ∩ Set.Ioc 0 1 ⊆ {1} := by
      intro t ht
      obtain ⟨htc, ht0, ht1⟩ := ht
      rw [Set.mem_compl_iff, Set.mem_Ioo, not_and_or, not_lt, not_lt] at htc
      rcases htc with h | h
      · exact absurd ht0 (not_lt.mpr h)
      · exact (le_antisymm ht1 h) ▸ rfl
    exact MeasureTheory.measure_mono_null hsub1 (by simp)
  refine MeasureTheory.measure_mono_null (fun s hs => ?_) hnull
  exact fun hs' => hs (hsub hs')

omit [CompactSpace M] in
theorem realizedRicciPathValue_continuousOn_Icc (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) :
    ContinuousOn (realizedRicciPathValue (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w)
      (Set.Icc (0:ℝ) 1) := by
  refine ContinuousOn.congr
    (f := realizedRicciChartSum (I := I) g₀ T T' hδ hδ' x v w) ?_ ?_
  · exact fun s hs =>
      (realizedRicciChartSum_contDiffAt (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w
        (Icc_subset_realizedSmallSet hδ_lt hδ'_lt hs)).continuousAt.continuousWithinAt
  · intro s hs
    exact realizedRicciPathValue_eq_chartSum_on_Icc (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
      x v w hs

omit [CompactSpace M] in
theorem hasDerivAt_ricciTensor_realizedMetricPath (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) :
    (∀ s₀ ∈ Set.Ioo (0 : ℝ) 1,
        HasDerivAt
          (realizedRicciPathValue (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w)
          (linearizedRicciAt (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w s₀) s₀) ∧
      IntervalIntegrable
        (linearizedRicciAt (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w)
        MeasureTheory.volume 0 1 := by
  refine ⟨fun s₀ hs₀ => ?_, ?_⟩
  · rw [linearizedRicciAt]
    exact (realizedRicciPathValue_differentiableAt_Ioo (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
      x v w hs₀).hasDerivAt
  · exact linearizedRicciAt_intervalIntegrable (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w

omit [CompactSpace M] in
theorem ricciTensor_realized_sub_eq_integral_linearizedRicci
    (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) :
    ricciTensor (I := I) (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ) x v w -
        ricciTensor (I := I) (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ') x v w =
      ∫ s in (0 : ℝ)..1,
        linearizedRicciAt (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w s := by
  obtain ⟨hderiv, hint⟩ :=
    hasDerivAt_ricciTensor_realizedMetricPath (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w
  have hcont := realizedRicciPathValue_continuousOn_Icc (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w
  have hFTC :
      ∫ s in (0 : ℝ)..1,
          linearizedRicciAt (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w s =
        realizedRicciPathValue (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w 1 -
          realizedRicciPathValue (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w 0 :=
    integral_eq_sub_of_hasDerivAt_of_le zero_le_one hcont hderiv hint
  rw [hFTC, realizedRicciPathValue_one, realizedRicciPathValue_zero]

private local instance instCompleteSpaceE_keystone : CompleteSpace E :=
  FiniteDimensional.complete ℝ E

open DifferentialGeometry.Integral.DivergenceTheorem in

omit [CompactSpace M] in
theorem cometricRaiseSlot0Fib_realizedFam_jointContMDiffOn [BoundarylessManifold I M] (s : ℕ)
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (Y : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace (s + 2) I p.1)
    (hY : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (s + 2) ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (s + 2) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace (s + 2) I z) p.1 (Y p))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ'))) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 1 (s + 1) ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 1 (s + 1) ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 1 (s + 1) I z) p.1
        (cometricRaiseSlot0Fib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) s p.1 (Y p)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  apply contMDiffOn_clm_section_of_pointwise_joint_manifold_time (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 1 ℝ E) (V₁ := fun x : M => Tensor0SBundle.Tensor0SSpace 1 I x)
    (F₂ := Tensor0SBundle.Tensor0SModel (s + 1) ℝ E)
    (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace (s + 1) I x)
    (φ := fun p : M × ℝ => (show Tensor0SBundle.Tensor0SSpace 1 I p.1 →L[ℝ]
        Tensor0SBundle.Tensor0SSpace (s + 1) I p.1 from
      cometricRaiseSlot0Fib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) s p.1 (Y p)))
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
  intro β

  have hsharp := inverseMetricSharpField_realizedFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ'
  have hβjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 1 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 1 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 1 I z) p.1 (β p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
    have hβM : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 1 ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 1 ℝ E)
          (E := fun z : M => Tensor0SBundle.Tensor0SSpace 1 I z) x (β x)) := β.contMDiff
    exact (hβM.comp_contMDiffOn contMDiffOn_fst)
  have hsharpβ : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1
        (inverseMetricSharpFib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1 (β p.1)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    ContMDiffOn.clm_bundle_apply (b := Prod.fst) hsharp hβjoint

  set sharpβ : ∀ p : M × ℝ, TangentSpace I p.1 :=
    fun p => inverseMetricSharpFib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1 (β p.1)
    with hsharpβdef

  have hraise := interiorProductField_jointContMDiffOn_vecJoint (I := I) (s := s + 1)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) (X := sharpβ) hsharpβ (α := fun p => Y p) hY
  refine hraise.congr (fun p hp => ?_)

  change TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (s + 1) ℝ E)
      (E := fun z : M => Tensor0SBundle.Tensor0SSpace (s + 1) I z) p.1
      (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (s + 1) p.1 (sharpβ p) (Y p)) =
    TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (s + 1) ℝ E)
      (E := fun z : M => Tensor0SBundle.Tensor0SSpace (s + 1) I z) p.1
      ((show Tensor0SBundle.Tensor0SSpace 1 I p.1 →L[ℝ]
          Tensor0SBundle.Tensor0SSpace (s + 1) I p.1 from
        cometricRaiseSlot0Fib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) s p.1 (Y p)) (β p.1))
  congr 1

set_option backward.isDefEq.respectTransparency false in
open DifferentialGeometry.Integral.DivergenceTheorem in

omit [CompactSpace M] in
theorem cometricDoubleTraceFib_realizedFam_jointContMDiffOn [BoundarylessManifold I M] (p : ℕ)
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (Y : ∀ q : M × ℝ, Tensor0SBundle.Tensor0SSpace (p + 2) I q.1)
    (hY : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (p + 2) ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (p + 2) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace (p + 2) I z) q.1 (Y q))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ'))) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel p ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel p ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace p I z) q.1
        (cometricDoubleTraceFib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' q.2) p q.1 (Y q)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by

  have hraise := cometricRaiseSlot0Fib_realizedFam_jointContMDiffOn (I := I) (s := p) g₀ T T' hδ hδ' Y hY

  have htrace := contractTraceField_jointContMDiffOn (I := I) 0 p
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun q : M × ℝ => cometricRaiseSlot0Fib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' q.2) p q.1 (Y q))
    hraise

  have hunit : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 0 ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 0 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 0 I z) q.1
        (Integral.Connection.unitZeroSec (I := I) (M := M) q.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    ((Integral.Connection.unitZeroSec (I := I) (M := M)).contMDiff.comp_contMDiffOn contMDiffOn_fst)
  have htraceUnit := ContMDiffOn.clm_bundle_apply (b := Prod.fst) htrace hunit
  refine htraceUnit.congr (fun q hq => ?_)

  congr 1
  apply Tensor0SBundle.Tensor0SSpace.toModel_injective
  beta_reduce
  rw [cometricDoubleTraceFib_toModel]
  rw [← model_contract_trace_raiseSlot0ModelL (E := E) p
    (cometricLmodel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' q.2) q.1)
    (Tensor0SBundle.Tensor0SSpace.toModel (Y q))]
  rw [contract_trace_unitZero_toModel (I := I) p q.1
    (cometricRaiseSlot0Fib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' q.2) p q.1 (Y q))]
  congr 1

set_option backward.isDefEq.respectTransparency false in
omit [CompactSpace M] in
theorem ricciArmPrincipalCoeffFib_realizedFam_jointContMDiffOn [BoundarylessManifold I M]
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 4 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) p.1
        (ricciDeTurckPrincipalCoeffAtPoint (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  classical
  apply contMDiffOn_clm_section_of_pointwise_joint_manifold_time (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 4 ℝ E) (V₁ := fun x : M => Tensor0SBundle.Tensor0SSpace 4 I x)
    (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E) (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace 2 I x)
    (φ := fun p : M × ℝ => ricciDeTurckPrincipalCoeffAtPoint (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
  intro Y
  set κ : Equiv.Perm (Fin 4) := koszulDoubleTraceSlotPerm with hκ
  set g_s : ℝ → SmoothRiemannianMetric I M := fun s => realizedFam (I := I) g₀ T T' hδ hδ' s with hg_s

  have hYjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 4 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 4 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 4 I z) p.1 (Y p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    Y.contMDiff.comp_contMDiffOn contMDiffOn_fst

  have hYκ := domDomCongrField_jointContMDiffOn (I := I) κ
    (S := realizedSmallSet (δ := δ) (δ' := δ')) (fun p : M × ℝ => Y p.1) hYjoint

  have hT03 := cometricDoubleTraceFib_realizedFam_jointContMDiffOn (I := I) (p := 2) g₀ T T' hδ hδ'
    (fun p : M × ℝ => Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := p.1)
      (ContinuousMultilinearMap.domDomCongr κ (Tensor0SBundle.Tensor0SSpace.toModel (Y p.1)))) hYκ

  have hCDT := cometricDoubleTraceFib_realizedFam_jointContMDiffOn (I := I) (p := 2) g₀ T T' hδ hδ'
    (fun p : M × ℝ => Y p.1) hYjoint

  have hswap := domDomCongrField_jointContMDiffOn (I := I) (Equiv.swap (0 : Fin 2) 1)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun p : M × ℝ => (show Tensor0SBundle.Tensor0SSpace 4 I p.1 →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I p.1 from
        cometricDoubleTraceFib (I := I) (g_s p.2) 2 p.1)
        (Tensor0SBundle.Tensor0SSpace.ofModel
          (ContinuousMultilinearMap.domDomCongr κ (Tensor0SBundle.Tensor0SSpace.toModel (Y p.1)))))
    hT03

  have hcomb := jointTotalSpace_smul (I := I) (d := 2) (1 / 2 : ℝ) _
    (jointTotalSpace_sub (I := I) (d := 2) _ _ (jointTotalSpace_add (I := I) (d := 2) _ _ hT03 hswap) hCDT)
  refine hcomb.congr (fun p hp => ?_)

  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1 t) ?_
  apply Tensor0SBundle.Tensor0SSpace.toModel_injective
  beta_reduce
  rw [ricciArmPrincipalCoeffFib_toModel]
  simp only [Tensor0SBundle.Tensor0SSpace.toModel_smul, Tensor0SBundle.Tensor0SSpace.toModel_sub,
    Tensor0SBundle.Tensor0SSpace.toModel_add, cometricDoubleTraceFib_toModel,
    Tensor0SBundle.Tensor0SSpace.toModel_ofModel]
  rw [ricciPrincipalCoeffDoubleTraceModel]
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  rfl

theorem ricciArmPrincipalCoeff_realizedFam_jointContMDiff [BoundarylessManifold I M]
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 4 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) p.1
        ((ricciArmPrincipalCoeff (I := I) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' p.2)).toSection p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by

  have hfib := ricciArmPrincipalCoeffFib_realizedFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ'
  refine hfib.congr (fun p _ => ?_)
  rw [ricciArmPrincipalCoeff_toSection]

theorem ricciArmPrincipalCoeff_realizedFam_toModel_continuous [BoundarylessManifold I M]
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) :
    ContinuousOn (fun t : ℝ =>
      Tensor0SBundle.TensorRSSpace.toModel
        ((ricciArmPrincipalCoeff (I := I) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' t)).toSection x))
      (realizedSmallSet (δ := δ) (δ' := δ')) := by
  have hjoint := ricciArmPrincipalCoeff_realizedFam_jointContMDiff
    (I := I) g₀ T T' hδ hδ'
  exact jointContMDiff_toModel_continuous_slice (I := I) g₀ 4 2
    (fun t => ricciArmPrincipalCoeff (I := I) g₀
      (realizedFam (I := I) g₀ T T' hδ hδ' t)) (realizedSmallSet (δ := δ) (δ' := δ')) hjoint x

omit [CompactSpace M] in
theorem realizedFam_chartRicciTensor_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (α : M) (i k : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun p : M × ℝ => chartRicciTensor (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' p.2) α i k (extChartAt I α p.1))
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  have hG := realizedFam_genJointGram_free (I := I) g₀ T T' hδ hδ' α
  have hmove : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => (p.2, extChartAt I α p.1))
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
    refine ContMDiffOn.prodMk contMDiffOn_snd ?_
    exact (contMDiffOn_extChartAt (I := I) (x := α)).comp contMDiffOn_fst (fun p hp => hp.1)
  intro p hp
  obtain ⟨hx, hs⟩ := hp
  have hxsrc : p.1 ∈ (extChartAt I α).source := by rw [extChartAt_source (I := I)]; exact hx
  have hy : extChartAt I α p.1 ∈ interior (extChartAt I α).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α
      ((extChartAt I α).map_source hxsrc)
  have hentry := gen_joint_ricci (I := I)
    (realizedFam (I := I) g₀ T T' hδ hδ') α hG i k hs hy
  have hentryM : ContMDiffAt (𝓘(ℝ, ℝ × E)) 𝓘(ℝ) ∞
      (fun r : ℝ × E => chartRicciTensor (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' r.1) α i k r.2) (p.2, extChartAt I α p.1) :=
    hentry.contMDiffAt
  have hmoveAt : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ × E)) ∞
      (fun p : M × ℝ => (p.2, extChartAt I α p.1))
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) p := by
    have hm := hmove p ⟨hx, hs⟩
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hm
    exact hm
  exact (hentryM.comp_contMDiffWithinAt p hmoveAt).congr
    (fun q _ => rfl) rfl

set_option backward.isDefEq.respectTransparency false in

omit [CompactSpace M] in
theorem ricciTensorSection_chartComponent_realizedFam_jointContMDiffOn [BoundarylessManifold I M]
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (Y : Cₛ^∞⟮I; E, (fun x : M => TangentSpace I x)⟯)
    (α : M) (j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun p : M × ℝ => ricciTensor (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1 (Y p.1)
        (chartBasisVecFiber (I := I) α j p.1))
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  classical
  have hbase_eq : (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source :=
    trivializationAt_baseSet_eq_chartAt_source (I := I) α

  have hsum : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun p : M × ℝ => ∑ q : Fin (Module.finrank ℝ E),
        chartCoeff (I := I) α Y q p.1 *
          chartRicciTensor (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) α q j
            (extChartAt I α p.1))
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
    refine contMDiffOn_finset_sum (fun q _ => ?_)
    have hcoeff : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
        (fun p : M × ℝ => chartCoeff (I := I) α Y q p.1)
        ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
      have hc := chartCoeff_contMDiffOn (I := I) α Y q
      rw [hbase_eq] at hc
      exact hc.comp contMDiffOn_fst (fun p hp => hp.1)
    exact hcoeff.mul
      (realizedFam_chartRicciTensor_jointContMDiffOn (I := I) g₀ T T' hδ hδ' α q j)
  refine hsum.congr (fun p hp => ?_)
  obtain ⟨hx, _hs⟩ := hp
  have hxbase : p.1 ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [hbase_eq]; exact hx
  have hxgood : p.1 ∈ chartLeviCivitaGoodSet (I := I) α := by
    rw [chartLeviCivitaGoodSet_eq_extChartAt_source (I := I) α, extChartAt_source (I := I)]
    exact hx

  set gs := realizedFam (I := I) g₀ T T' hδ hδ' p.2 with hgs
  rw [chartCoeff_recompose (I := I) α Y hxbase]
  rw [map_sum (ricciTensor (I := I) gs p.1), ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul,
    ricciTensor_chartBasisVec_alpha_eq (I := I) gs α q j hxgood]

set_option backward.isDefEq.respectTransparency false in
open DifferentialGeometry.Integral.DivergenceTheorem in

omit [CompactSpace M] in
theorem ricEndoRaisedFib_realizedFam_jointContMDiffOn [BoundarylessManifold I M]
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z) p.1
        (ricEndoRaisedFib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  apply contMDiffOn_clm_section_of_pointwise_joint_manifold_time (I := I) (M := M)
    (F₁ := E) (V₁ := fun x : M => TangentSpace I x)
    (F₂ := E) (V₂ := fun x : M => TangentSpace I x)
    (φ := fun p : M × ℝ => ricEndoRaisedFib (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
  intro Y

  set cv : ℝ → Π b : M, TangentSpace I b →ₗ[ℝ] ℝ :=
    fun s b => (ricciTensor (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) b (Y b)).toLinearMap
    with hcvdef
  have hinv : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
        (fun p : M × ℝ => chartInvGramMatrix (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' p.2) α p.1 i j)
        ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    fun α i j => realizedFam_chartInvGramMatrix_jointContMDiffOn_free
      (I := I) g₀ T T' hδ hδ' α i j
  have hcv : ∀ (α : M) (j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
        (fun p : M × ℝ => cv p.2 p.1 (chartBasisVecFiber (I := I) α j p.1))
        ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
    intro α j
    have hbase := ricciTensorSection_chartComponent_realizedFam_jointContMDiffOn
      (I := I) g₀ T T' hδ hδ' Y α j
    refine hbase.congr (fun p _ => ?_)
    rw [hcvdef]
    rfl
  have hjoint := metricSharp_jointContMDiffOn (I := I)
    (gfam := fun s => realizedFam (I := I) g₀ T T' hδ hδ' s) (cv := cv)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) realizedSmallSet_isOpen hinv hcv
  refine hjoint.congr (fun p hp => ?_)

  change TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1
      (DifferentialGeometry.Integral.DivergenceTheorem.metricSharp
        (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1 (cv p.2 p.1)) =
    TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1
      (ricEndoRaisedFib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1 (Y p.1))
  rw [ricEndoRaisedFib_apply, hcvdef]
  refine congrArg (TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1) ?_
  apply DifferentialGeometry.Integral.DivergenceTheorem.metricFlatLinear_injective
    (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1
  ext w
  change (realizedFam (I := I) g₀ T T' hδ hδ' p.2).inner p.1
      (DifferentialGeometry.Integral.DivergenceTheorem.metricSharp
        (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1
          ((ricciTensor (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1
            (Y p.1)).toLinearMap)) w =
    (realizedFam (I := I) g₀ T T' hδ hδ' p.2).inner p.1
      (DifferentialGeometry.Integral.Connection.metricSharp
        (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1
          ((ricciTensor (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1
            (Y p.1)).toLinearMap)) w
  rw [DifferentialGeometry.Integral.DivergenceTheorem.inner_metricSharp,
    DifferentialGeometry.Integral.Connection.inner_metricSharp]

set_option backward.isDefEq.respectTransparency false in

omit [CompactSpace M] in
theorem ricciArmOrder0CurvCoeffFibSlot0_realizedFam_jointContMDiffOn [BoundarylessManifold I M]
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 2 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 2 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 2 2 I z) p.1
        (Tensor0SBundle.TensorRSSpace.ofCLM
          (ricciArmOrder0CurvCoeffFibSlot (I := I)
            (realizedFam (I := I) g₀ T T' hδ hδ' p.2) 0 p.1)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  classical
  apply contMDiffOn_clm_section_of_pointwise_joint_manifold_time (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 2 ℝ E) (V₁ := fun x : M => Tensor0SBundle.Tensor0SSpace 2 I x)
    (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E) (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace 2 I x)
    (φ := fun p : M × ℝ => ricciArmOrder0CurvCoeffFibSlot (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2) 0 p.1)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
  intro Y
  set g_s : ℝ → SmoothRiemannianMetric I M := fun s => realizedFam (I := I) g₀ T T' hδ hδ' s with hg_s

  have hric := ricEndoRaisedFib_realizedFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ'

  have hYjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1 (Y p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    Y.contMDiff.comp_contMDiffOn contMDiffOn_fst

  have happ := slotInsertEndo0Field_apply_jointContMDiffOn (I := I) (M := M) (d := 1)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (Λ := fun p : M × ℝ => ricEndoRaisedFib (I := I) (g_s p.2) p.1) hric
    (A := fun p : M × ℝ => Y p.1) hYjoint
  refine happ.congr (fun p _ => ?_)

  rw [ricciArmOrder0CurvCoeffFibSlot]

set_option backward.isDefEq.respectTransparency false in

omit [CompactSpace M] in
theorem ricciArmOrder0CurvCoeffFibSlot1_realizedFam_jointContMDiffOn [BoundarylessManifold I M]
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 2 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 2 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 2 2 I z) p.1
        (Tensor0SBundle.TensorRSSpace.ofCLM
          (ricciArmOrder0CurvCoeffFibSlot (I := I)
            (realizedFam (I := I) g₀ T T' hδ hδ' p.2) 1 p.1)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  classical
  apply contMDiffOn_clm_section_of_pointwise_joint_manifold_time (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 2 ℝ E) (V₁ := fun x : M => Tensor0SBundle.Tensor0SSpace 2 I x)
    (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E) (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace 2 I x)
    (φ := fun p : M × ℝ => ricciArmOrder0CurvCoeffFibSlot (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2) 1 p.1)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
  intro Y
  set g_s : ℝ → SmoothRiemannianMetric I M := fun s => realizedFam (I := I) g₀ T T' hδ hδ' s with hg_s

  have hric := ricEndoRaisedFib_realizedFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ'

  have hYjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1 (Y p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    Y.contMDiff.comp_contMDiffOn contMDiffOn_fst

  have happ := slotInsertEndo1Field_apply_jointContMDiffOn (I := I) (M := M) (d := 0) g₀
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (Λ := fun p : M × ℝ => ricEndoRaisedFib (I := I) (g_s p.2) p.1) hric
    (A := fun p : M × ℝ => Y p.1) hYjoint
  refine happ.congr (fun p _ => ?_)

  rw [ricciArmOrder0CurvCoeffFibSlot]

set_option backward.isDefEq.respectTransparency false in

omit [CompactSpace M] in
theorem ricciArmOrder0CurvCoeffFib_realizedFam_jointContMDiffOn [BoundarylessManifold I M]
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 2 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 2 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 2 2 I z) p.1
        (Tensor0SBundle.TensorRSSpace.ofCLM
          (ricciArmOrder0CurvCoeffFib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  have hslot0 := ricciArmOrder0CurvCoeffFibSlot0_realizedFam_jointContMDiffOn
    (I := I) g₀ T T' hδ hδ'
  have hslot1 := ricciArmOrder0CurvCoeffFibSlot1_realizedFam_jointContMDiffOn
    (I := I) g₀ T T' hδ hδ'
  have hadd := jointTotalSpaceRS_add (I := I) (r := 2) (s := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (A := fun p : M × ℝ => Tensor0SBundle.TensorRSSpace.ofCLM
      (ricciArmOrder0CurvCoeffFibSlot (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) 0 p.1))
    (B := fun p : M × ℝ => Tensor0SBundle.TensorRSSpace.ofCLM
      (ricciArmOrder0CurvCoeffFibSlot (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) 1 p.1))
    hslot0 hslot1
  refine hadd.congr (fun p _ => ?_)
  rfl

theorem ricciArmOrder0CurvCoeff_realizedFam_jointContMDiff [BoundarylessManifold I M]
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 2 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 2 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 2 2 I z) p.1
        ((ricciArmOrder0CurvCoeff (I := I) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' p.2)).toSection p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by

  have hfib := ricciArmOrder0CurvCoeffFib_realizedFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ'
  refine hfib.congr (fun p _ => ?_)
  rw [ricciArmOrder0CurvCoeff_toSection]

theorem ricciArmOrder0CurvCoeff_realizedFam_toModel_continuous [BoundarylessManifold I M]
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) :
    ContinuousOn (fun t : ℝ =>
      Tensor0SBundle.TensorRSSpace.toModel
        ((ricciArmOrder0CurvCoeff (I := I) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' t)).toSection x))
      (realizedSmallSet (δ := δ) (δ' := δ')) := by
  have hjoint := ricciArmOrder0CurvCoeff_realizedFam_jointContMDiff
    (I := I) g₀ T T' hδ hδ'
  exact jointContMDiff_toModel_continuous_slice (I := I) g₀ 2 2
    (fun t => ricciArmOrder0CurvCoeff (I := I) g₀
      (realizedFam (I := I) g₀ T T' hδ hδ' t)) (realizedSmallSet (δ := δ) (δ' := δ')) hjoint x

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem genGram_of_family
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    (α : M) :
    ChartGramFamilyJointSmoothNondegenerate (I := I) (fun t => G.metric t) α D.regular := by
  classical
  refine ⟨?_, ?_⟩
  · intro i j s₀ y₀ hs hy
    set e := trivializationAt E (TangentSpace I) α with he
    have hframe :
        IsLocalFrameOn I E (∞ : WithTop ℕ∞) (e.localFrame (chartModelBasis E)) e.baseSet :=
      e.isLocalFrameOn_localFrame_baseSet I (∞ : WithTop ℕ∞) (chartModelBasis E)
    have hbridge : ∀ {x : M}, x ∈ e.baseSet → ∀ k : Fin (Module.finrank ℝ E),
        e.localFrame (chartModelBasis E) k x = chartBasisVecFiber (I := I) α k x := by
      intro x hx k
      rw [e.localFrame_apply_of_mem_baseSet (chartModelBasis E) hx]
      rfl
    have hsmooth : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (G.metric p.1) α p.2 i j)
        (D.regular ×ˢ e.baseSet) := by
      have hcomp := hG.frameCompSmooth (e.localFrame (chartModelBasis E)) hframe i j
      refine hcomp.congr ?_
      intro p hp
      simp only [chartGramMatrix_apply, hbridge hp.2 i, hbridge hp.2 j]
    have hsymm : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I α).symm
        (extChartAt I α).target :=
      contMDiffOn_extChartAt_symm (I := I) α
    have hsubset : (extChartAt I α).target ⊆ (extChartAt I α).symm ⁻¹' e.baseSet := by
      intro y hy'
      have hsource : (extChartAt I α).symm y ∈ (extChartAt I α).source :=
        (extChartAt I α).map_target hy'
      rw [extChartAt_source_eq_chartAt_source (I := I)] at hsource
      rw [he, trivializationAt_baseSet_eq_chartAt_source]
      exact hsource
    have hσ1 : ContMDiffOn 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × E => p.1) (D.regular ×ˢ interior (extChartAt I α).target) :=
      (contMDiff_iff_contDiff.mpr contDiff_fst).contMDiffOn
    have hsnd : ContMDiffOn 𝓘(ℝ, ℝ × E) 𝓘(ℝ, E) ∞
        (fun p : ℝ × E => p.2) (D.regular ×ˢ interior (extChartAt I α).target) :=
      (contMDiff_iff_contDiff.mpr contDiff_snd).contMDiffOn
    have hmaps2 : Set.MapsTo (fun p : ℝ × E => p.2)
        (D.regular ×ˢ interior (extChartAt I α).target) (extChartAt I α).target :=
      fun p hp => interior_subset hp.2
    have hσ2 : ContMDiffOn 𝓘(ℝ, ℝ × E) I ∞
        (fun p : ℝ × E => (extChartAt I α).symm p.2)
        (D.regular ×ˢ interior (extChartAt I α).target) :=
      hsymm.comp hsnd hmaps2
    have hσ : ContMDiffOn 𝓘(ℝ, ℝ × E) (𝓘(ℝ, ℝ).prod I) ∞
        (fun p : ℝ × E => (p.1, (extChartAt I α).symm p.2))
        (D.regular ×ˢ interior (extChartAt I α).target) :=
      hσ1.prodMk hσ2
    have hcomp : ContMDiffOn 𝓘(ℝ, ℝ × E) 𝓘(ℝ) ∞
        (fun p : ℝ × E => chartGramOnE (I := I) (G.metric p.1) α i j p.2)
        (D.regular ×ˢ interior (extChartAt I α).target) := by
      refine (hsmooth.comp hσ (fun p hp => ⟨hp.1, hsubset (interior_subset hp.2)⟩)).congr ?_
      intro p _
      rfl
    exact hcomp.contDiffOn.contDiffAt
      (prod_mem_nhds (D.regular_isOpen.mem_nhds hs) (isOpen_interior.mem_nhds hy))
  · intro s₀ _ x hx
    exact chartGramMatrix_det_pos (I := I) (G.metric s₀) α hx

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
theorem invGram_of_family
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    (α : M) (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun p : M × ℝ => chartInvGramMatrix (I := I) (G.metric p.2) α p.1 i j)
      ((chartAt H α).source ×ˢ D.regular) := by
  have hGram := genGram_of_family (I := I) G hG α
  have hmove : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => (p.2, extChartAt I α p.1))
      ((chartAt H α).source ×ˢ D.regular) := by
    refine ContMDiffOn.prodMk contMDiffOn_snd ?_
    exact (contMDiffOn_extChartAt (I := I) (x := α)).comp contMDiffOn_fst
      (fun p hp => hp.1)
  intro p hp
  obtain ⟨hx, ht⟩ := hp
  have hxsrc : p.1 ∈ (extChartAt I α).source := by
    rw [extChartAt_source (I := I)]
    exact hx
  have hy : extChartAt I α p.1 ∈ interior (extChartAt I α).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α
      ((extChartAt I α).map_source hxsrc)
  have hentry := chartInvGramOnE_contDiffAt_joint (I := I) (fun t => G.metric t) α hGram i j ht hy
  have hentryM : ContMDiffAt 𝓘(ℝ, ℝ × E) 𝓘(ℝ) ∞
      (fun r : ℝ × E => chartInvGramOnE (I := I) (G.metric r.1) α i j r.2)
      (p.2, extChartAt I α p.1) :=
    hentry.contMDiffAt
  have hmoveAt : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ × E) ∞
      (fun q : M × ℝ => (q.2, extChartAt I α q.1))
      ((chartAt H α).source ×ˢ D.regular) p := by
    have hm := hmove p ⟨hx, ht⟩
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hm
    exact hm
  refine (hentryM.comp_contMDiffWithinAt p hmoveAt).congr ?_ ?_
  · intro q hq
    have hqx : q.1 ∈ (extChartAt I α).source := by
      rw [extChartAt_source (I := I)]
      exact hq.1
    rw [Function.comp_apply, chartInvGramOnE_def, (extChartAt I α).left_inv hqx]
  · rw [Function.comp_apply, chartInvGramOnE_def, (extChartAt I α).left_inv hxsrc]

omit [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem christ_of_family
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    (α : M) (i j k : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun p : M × ℝ =>
        chartChristoffel (I := I) (G.metric p.2) α i j k (extChartAt I α p.1))
      ((chartAt H α).source ×ˢ D.regular) := by
  have hGram := genGram_of_family (I := I) G hG α
  have hmove : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => (p.2, extChartAt I α p.1))
      ((chartAt H α).source ×ˢ D.regular) := by
    refine ContMDiffOn.prodMk contMDiffOn_snd ?_
    exact (contMDiffOn_extChartAt (I := I) (x := α)).comp contMDiffOn_fst
      (fun p hp => hp.1)
  intro p hp
  obtain ⟨hx, ht⟩ := hp
  have hxsrc : p.1 ∈ (extChartAt I α).source := by
    rw [extChartAt_source (I := I)]
    exact hx
  have hy : extChartAt I α p.1 ∈ interior (extChartAt I α).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α
      ((extChartAt I α).map_source hxsrc)
  have hentry := gen_joint_christoffel (I := I) (fun t => G.metric t) α hGram i j k ht hy
  have hentryM : ContMDiffAt 𝓘(ℝ, ℝ × E) 𝓘(ℝ) ∞
      (fun r : ℝ × E => chartChristoffel (I := I) (G.metric r.1) α i j k r.2)
      (p.2, extChartAt I α p.1) :=
    hentry.contMDiffAt
  have hmoveAt : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ × E) ∞
      (fun q : M × ℝ => (q.2, extChartAt I α q.1))
      ((chartAt H α).source ×ˢ D.regular) p := by
    have hm := hmove p ⟨hx, ht⟩
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hm
    exact hm
  simpa only [Function.comp_apply] using hentryM.comp_contMDiffWithinAt p hmoveAt

open DifferentialGeometry.Integral.DivergenceTheorem in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M] in
theorem invSharp_of_family
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel 1 ℝ E →L[ℝ] E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel 1 ℝ E →L[ℝ] E)
        (E := fun z : M => Tensor0SSpace 1 I z →L[ℝ] TangentSpace I z) p.1
        (inverseMetricSharpFib (I := I) (G.metric p.2) p.1))
      ((Set.univ : Set M) ×ˢ D.regular) := by
  apply contMDiffOn_clm_section_of_pointwise_joint_manifold_time (I := I) (M := M)
    (F₁ := Tensor0SModel 1 ℝ E) (V₁ := fun x : M => Tensor0SSpace 1 I x)
    (F₂ := E) (V₂ := fun x : M => TangentSpace I x)
    (φ := fun p : M × ℝ => inverseMetricSharpFib (I := I) (G.metric p.2) p.1)
    (S := D.regular)
  intro Y
  set cv : ℝ → Π b : M, TangentSpace I b →ₗ[ℝ] ℝ :=
    fun _ b => cotangentToDualLinear (I := I) (x := b) (Y b) with hcvdef
  have hinv : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
        (fun p : M × ℝ => chartInvGramMatrix (I := I) (G.metric p.2) α p.1 i j)
        ((chartAt H α).source ×ˢ D.regular) :=
    fun α i j => invGram_of_family (I := I) G hG α i j
  have hcv : ∀ (α : M) (j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
        (fun p : M × ℝ => cv p.2 p.1 (chartBasisVecFiber (I := I) α j p.1))
        ((chartAt H α).source ×ˢ D.regular) := by
    intro α j
    have hbase := cotangentSection_chartComponent_contMDiffOn (I := I) Y α j
    have heqfn : (fun p : M × ℝ => cv p.2 p.1 (chartBasisVecFiber (I := I) α j p.1)) =
        (fun p : M × ℝ => (fun b : M => Tensor0SSpace.toModel (Y b)
          (fun _ : Fin 1 => chartBasisVecFiber (I := I) α j b)) p.1) := by
      funext p
      rw [hcvdef]
      simp only
      rw [cotangentToDualLinear_apply, cotangentToDual_apply]
      rfl
    rw [heqfn]
    exact hbase.comp contMDiffOn_fst (fun p hp => hp.1)
  have hjoint := metricSharp_jointContMDiffOn (I := I)
    (gfam := fun t => G.metric t) (cv := cv) (S := D.regular)
    D.regular_isOpen hinv hcv
  refine hjoint.congr (fun p _ => ?_)
  change TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1
      (DifferentialGeometry.Integral.DivergenceTheorem.metricSharp
        (I := I) (G.metric p.2) p.1 (cv p.2 p.1)) =
    TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1
      (inverseMetricSharpFib (I := I) (G.metric p.2) p.1 (Y p.1))
  rw [inverseMetricSharpFib_apply, hcvdef]

open DifferentialGeometry.Integral.DivergenceTheorem in










omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M] in
theorem comRaise_of_family (s : ℕ)
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    (Y : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace (s + 2) I p.1)
    (hY : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (s + 2) ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (s + 2) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace (s + 2) I z) p.1 (Y p))
      ((Set.univ : Set M) ×ˢ D.regular)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 1 (s + 1) ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 1 (s + 1) ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 1 (s + 1) I z) p.1
        (cometricRaiseSlot0Fib (I := I) (G.metric p.2) s p.1 (Y p)))
      ((Set.univ : Set M) ×ˢ D.regular) := by
  apply contMDiffOn_clm_section_of_pointwise_joint_manifold_time (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 1 ℝ E)
    (V₁ := fun x : M => Tensor0SBundle.Tensor0SSpace 1 I x)
    (F₂ := Tensor0SBundle.Tensor0SModel (s + 1) ℝ E)
    (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace (s + 1) I x)
    (φ := fun p : M × ℝ => (show Tensor0SBundle.Tensor0SSpace 1 I p.1 →L[ℝ]
        Tensor0SBundle.Tensor0SSpace (s + 1) I p.1 from
      cometricRaiseSlot0Fib (I := I) (G.metric p.2) s p.1 (Y p)))
    (S := D.regular)
  intro β
  have hsharp := invSharp_of_family (I := I) G hG
  have hβjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 1 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 1 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 1 I z) p.1 (β p.1))
      ((Set.univ : Set M) ×ˢ D.regular) := by
    have hβM : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 1 ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 1 ℝ E)
          (E := fun z : M => Tensor0SBundle.Tensor0SSpace 1 I z) x (β x)) := β.contMDiff
    exact hβM.comp_contMDiffOn contMDiffOn_fst
  have hsharpβ : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1
        (inverseMetricSharpFib (I := I) (G.metric p.2) p.1 (β p.1)))
      ((Set.univ : Set M) ×ˢ D.regular) :=
    ContMDiffOn.clm_bundle_apply (b := Prod.fst) hsharp hβjoint
  set sharpβ : ∀ p : M × ℝ, TangentSpace I p.1 :=
    fun p => inverseMetricSharpFib (I := I) (G.metric p.2) p.1 (β p.1)
  have hraise := interiorProductField_jointContMDiffOn_vecJoint (I := I) (s := s + 1)
    (S := D.regular) (X := sharpβ) hsharpβ (α := fun p => Y p) hY
  refine hraise.congr (fun p _ => ?_)
  change TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (s + 1) ℝ E)
      (E := fun z : M => Tensor0SBundle.Tensor0SSpace (s + 1) I z) p.1
      (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (s + 1) p.1
        (sharpβ p) (Y p)) =
    TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (s + 1) ℝ E)
      (E := fun z : M => Tensor0SBundle.Tensor0SSpace (s + 1) I z) p.1
      ((show Tensor0SBundle.Tensor0SSpace 1 I p.1 →L[ℝ]
          Tensor0SBundle.Tensor0SSpace (s + 1) I p.1 from
        cometricRaiseSlot0Fib (I := I) (G.metric p.2) s p.1 (Y p)) (β p.1))
  congr 1

open DifferentialGeometry.Integral.DivergenceTheorem in










omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M] in
theorem comTrace_of_family (p : ℕ)
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    (Y : ∀ q : M × ℝ, Tensor0SBundle.Tensor0SSpace (p + 2) I q.1)
    (hY : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (p + 2) ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (p + 2) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace (p + 2) I z) q.1 (Y q))
      ((Set.univ : Set M) ×ˢ D.regular)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel p ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel p ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace p I z) q.1
        (cometricDoubleTraceFib (I := I) (G.metric q.2) p q.1 (Y q)))
      ((Set.univ : Set M) ×ˢ D.regular) := by
  have hraise := comRaise_of_family (I := I) p G hG Y hY
  have htrace := contractTraceField_jointContMDiffOn (I := I) 0 p
    (S := D.regular)
    (fun q : M × ℝ => cometricRaiseSlot0Fib (I := I) (G.metric q.2) p q.1 (Y q))
    hraise
  have hunit : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 0 ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 0 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 0 I z) q.1
        (Integral.Connection.unitZeroSec (I := I) (M := M) q.1))
      ((Set.univ : Set M) ×ˢ D.regular) :=
    (Integral.Connection.unitZeroSec (I := I) (M := M)).contMDiff.comp_contMDiffOn
      contMDiffOn_fst
  have htraceUnit := ContMDiffOn.clm_bundle_apply (b := Prod.fst) htrace hunit
  refine htraceUnit.congr (fun q _ => ?_)
  congr 1
  apply Tensor0SBundle.Tensor0SSpace.toModel_injective
  beta_reduce
  rw [cometricDoubleTraceFib_toModel]
  rw [← model_contract_trace_raiseSlot0ModelL (E := E) p
    (cometricLmodel (I := I) (G.metric q.2) q.1)
    (Tensor0SBundle.Tensor0SSpace.toModel (Y q))]
  rw [contract_trace_unitZero_toModel (I := I) p q.1
    (cometricRaiseSlot0Fib (I := I) (G.metric q.2) p q.1 (Y q))]
  congr 1

end RicciLinearization
end DeTurck
end PDE
end DifferentialGeometry
