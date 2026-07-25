import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.SpectralMassUniformSup
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.MaxRegInteriorTimeSmoothing
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.SpectralSmoothRepresentativeRealize
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.EigenCombination
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.RealizeMetricChartGramDifference
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.RawComponentEuclideanBridge
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingCmOrderDropping
import DifferentialGeometry.Analysis.Calculus.ContDiffOnTsum
import DifferentialGeometry.Analysis.Spectral.Tensor.SmoothSection.CompactChartJetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.WeylSummability
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.EigensectionSobolevDecay
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.DeTurckChartRegularityFromJoint
import DifferentialGeometry.Analysis.Elliptic.TensorRegularity.DirichletForm.RotatedTestSection
import DifferentialGeometry.Analysis.Spectral.Tensor.SmoothSection.SmoothTensorAllOrderCompleteness
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.Representation.TensorReprFromFrame
import DifferentialGeometry.Analysis.Calculus.AnisotropicJointContDiff
import DifferentialGeometry.Analysis.Calculus.SpectralEigenSeriesJointGramProjectionJetBound
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.SpectralEigenSeriesJointGramSobolevWeightSummability
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.SpectralEigenSeriesJointGramRawComponentJetBound
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.SpectralEigenSeriesJointGramEigenChartIncrementMajorant


noncomputable section

open Bundle Manifold MeasureTheory Set Filter Topology
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Tensor
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Analysis.Sobolev.Tensor
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem ccTensorBilinSymm_add (g : SmoothRiemannianMetric I M)
    (S T : SmoothCcTensor g 0 2) (x : M) (v w : TangentSpace I x) :
    ccTensorBilinSymm (I := I) g (S + T) x v w =
      ccTensorBilinSymm (I := I) g S x v w + ccTensorBilinSymm (I := I) g T x v w := by
  rw [ccTensorBilinSymm_apply, ccTensorBilinSymm_apply, ccTensorBilinSymm_apply]
  have hbilin : ∀ (a b : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g (S + T) x a b =
        smoothCcTensorBilinForm (I := I) g S x a b + smoothCcTensorBilinForm (I := I) g T x a b := by
    intro a b
    rw [ccTensorBilin_apply, ccTensorBilin_apply, ccTensorBilin_apply]
    show ccTensorModel (I := I) g (S + T) x ![a, b] =
      ccTensorModel (I := I) g S x ![a, b] + ccTensorModel (I := I) g T x ![a, b]
    have hmodel : ccTensorModel (I := I) g (S + T) x =
        ccTensorModel (I := I) g S x + ccTensorModel (I := I) g T x := by
      rw [ccTensorModel, ccTensorModel, ccTensorModel]
      have hmul : (ccTensorMultilinear (I := I) g (S + T) x :
            Tensor0SBundle.Tensor0SSpace 2 I x) =
          (ccTensorMultilinear (I := I) g S x : Tensor0SBundle.Tensor0SSpace 2 I x) +
            (ccTensorMultilinear (I := I) g T x : Tensor0SBundle.Tensor0SSpace 2 I x) := by
        rw [ccTensorMultilinear_apply, ccTensorMultilinear_apply, ccTensorMultilinear_apply,
          SmoothCcTensor.toSection_add]
        exact ContinuousLinearMap.add_apply _ _ _
      rw [hmul, Tensor0SBundle.Tensor0SSpace.toModel_add]
    rw [hmodel, ContinuousMultilinearMap.add_apply]
  rw [hbilin v w, hbilin w v]; ring

omit [BoundarylessManifold I M] in
private theorem tensorL2_ext_of_tensorL2Coeff'
    (g : SmoothRiemannianMetric I M)
    {S T : TensorL2 0 2 g}
    (h : ∀ i, tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2) S i =
        tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2) T i) :
    S = T := by
  classical
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2 with hhc
  set b := DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventHilbertEigenbasisSigma
    (I := I) (M := M) hc with hb
  apply b.repr.injective
  ext i
  have hS : (b.repr S) i = tensorL2Coeff (I := I) (M := M) hc S i := rfl
  have hT : (b.repr T) i = tensorL2Coeff (I := I) (M := M) hc T i := rfl
  rw [hS, hT, h i]

omit [BoundarylessManifold I M] in
private theorem allHs_of_weighted_summable
    (g : SmoothRiemannianMetric I M) (u : TensorL2 0 2 g)
    (hsum : ∀ σ : ℝ, 0 ≤ σ →
      Summable (fun i : TensorEigenIdx (I := I) (M := M) g 0 2 =>
        tensorSobolevWeight (I := I) (M := M) i σ *
          (tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2) u i) ^ 2)) :
    ∀ σ : ℝ, ∀ hσ : 0 ≤ σ,
      ∃ v : tensorHs (I := I) (M := M) g 0 2 σ,
        tensorHsToL2 (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2) hσ v = u := by
  intro σ hσ
  classical
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2 with hhc
  set v : tensorHs (I := I) (M := M) g 0 2 σ :=
    { coeff := fun i => tensorL2Coeff (I := I) (M := M) hc u i
      weighted_summable := hsum σ hσ } with hv
  refine ⟨v, ?_⟩
  refine tensorL2_ext_of_tensorL2Coeff' (I := I) (M := M) g (fun i => ?_)
  rw [tensorHsToL2_tensorL2Coeff]

omit [BoundarylessManifold I M] in
private theorem ccTensorBilinSymm_finiteEigenCombo
    (g : SmoothRiemannianMetric I M)
    (F : Finset (TensorEigenIdx (I := I) (M := M) g 0 2))
    (c : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ)
    (x : M) (v w : TangentSpace I x) :
    ccTensorBilinSymm (I := I) g (finiteEigenCombo (I := I) (M := M) g F c) x v w =
      ∑ i ∈ F, c i *
        ccTensorBilinSymm (I := I) g (eigenSmooth (I := I) (M := M) g i) x v w := by
  classical
  rw [finiteEigenCombo_eq]
  induction F using Finset.induction with
  | empty =>
      simp only [Finset.sum_empty]
      have h0 : (0 : SmoothCcTensor g 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g 0 2) := by
        rw [zero_smul]
      rw [h0, ccTensorBilinSymm_smul, zero_mul]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ccTensorBilinSymm_add,
        ccTensorBilinSymm_smul, ih]

def fibreSymmBilinForm (x : M) (T : Tensor0SBundle.TensorRSSpace 0 2 I x)
    (v w : TangentSpace I x) : ℝ :=
  (1 / 2 : ℝ) * (
    Tensor0SBundle.Tensor0SSpace.toModel
      (T (ContinuousMultilinearMap.constOfIsEmpty ℝ
        (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) ![v, w]
    + Tensor0SBundle.Tensor0SSpace.toModel
      (T (ContinuousMultilinearMap.constOfIsEmpty ℝ
        (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) ![w, v])

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem ccTensorBilinSymm_eq_fibreSymmBilinForm (g : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g 0 2) (x : M) (v w : TangentSpace I x) :
    ccTensorBilinSymm (I := I) g S x v w =
      fibreSymmBilinForm (I := I) x (S.toSection x) v w := by
  rw [ccTensorBilinSymm_apply, ccTensorBilin_apply, ccTensorBilin_apply]
  rfl

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem fibreSymmBilinForm_add (x : M) (T₁ T₂ : Tensor0SBundle.TensorRSSpace 0 2 I x)
    (v w : TangentSpace I x) :
    fibreSymmBilinForm (I := I) x (T₁ + T₂) v w =
      fibreSymmBilinForm (I := I) x T₁ v w + fibreSymmBilinForm (I := I) x T₂ v w := by
  unfold fibreSymmBilinForm
  rw [show (T₁ + T₂) (ContinuousMultilinearMap.constOfIsEmpty ℝ
        (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))
      = T₁ (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))
        + T₂ (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)) from rfl,
    Tensor0SBundle.Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply,
    ContinuousMultilinearMap.add_apply]
  ring

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem fibreSymmBilinForm_smul (x : M) (a : ℝ) (T : Tensor0SBundle.TensorRSSpace 0 2 I x)
    (v w : TangentSpace I x) :
    fibreSymmBilinForm (I := I) x (a • T) v w = a * fibreSymmBilinForm (I := I) x T v w := by
  unfold fibreSymmBilinForm
  rw [show (a • T) (ContinuousMultilinearMap.constOfIsEmpty ℝ
        (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))
      = a • (T (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) from rfl,
    Tensor0SBundle.Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply,
    ContinuousMultilinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
  ring

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem fibreSymmBilinForm_sum {ι : Type*} (s : Finset ι) (x : M)
    (c : ι → ℝ) (T : ι → Tensor0SBundle.TensorRSSpace 0 2 I x)
    (v w : TangentSpace I x) :
    fibreSymmBilinForm (I := I) x (∑ i ∈ s, c i • T i) v w =
      ∑ i ∈ s, c i * fibreSymmBilinForm (I := I) x (T i) v w := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp only [Finset.sum_empty]
      have h0 : (0 : Tensor0SBundle.TensorRSSpace 0 2 I x) =
          (0 : ℝ) • (0 : Tensor0SBundle.TensorRSSpace 0 2 I x) := by rw [zero_smul]
      rw [h0, fibreSymmBilinForm_smul, zero_mul]
  | insert a t ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, fibreSymmBilinForm_add,
        fibreSymmBilinForm_smul, ih]

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (tensorChartComponentRaw) in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem ccTensorBilinSymm_eq_sum_chartBasis (g : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g 0 2) (β : M) {b : M} (hb : b ∈ (chartAt H β).source)
    (v w : TangentSpace I b) :
    ccTensorBilinSymm (I := I) g S b v w =
      ∑ Q : CompIdx E 0 2,
        tensorChartComponentRaw (I := I) (M := M) g 0 2 S β Q.1 Q.2 b *
          fibreSymmBilinForm (I := I) b
            (chartBasisFiberSection (I := I) (M := M) 0 2 β Q b) v w := by
  rw [ccTensorBilinSymm_eq_fibreSymmBilinForm,
    toSection_eq_sum_chartBasisFiberSection (I := I) (M := M) g 0 2 S β hb,
    fibreSymmBilinForm_sum]

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral in
open DifferentialGeometry.Analysis.Sobolev.Chart in

omit [BoundarylessManifold I M] in
theorem spectralChartComponent_tendsto
    (g : SmoothRiemannianMetric I M) (u : TensorL2 0 2 g)
    (hcauchy : ∀ k : ℕ, CauchySeq (fun n =>
      SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) (2 * k)
        (spectralPartialSum (I := I) (M := M) g u n)))
    (hF_L2 : Tendsto (fun n => (spectralPartialSum (I := I) (M := M) g u n : TensorL2 0 2 g))
      atTop (𝓝 u))
    (Trep : SmoothCcTensor g 0 2) (hTrep : (Trep : TensorL2 0 2 g) = u)
    (β : M) (P : TensorCompIdx (E := E) 0 2)
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) β) :
    Tendsto (fun n => tensorChartComponent (I := I) (M := M) g 0 2
        (spectralPartialSum (I := I) (M := M) g u n) β P.1 P.2 y)
      atTop (𝓝 (tensorChartComponent (I := I) (M := M) g 0 2 Trep β P.1 P.2 y)) := by
  classical
  set F : ℕ → SmoothCcTensor g 0 2 :=
    fun n => spectralPartialSum (I := I) (M := M) g u n with hF_def
  set S : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
    chartTargetEuclid (I := I) (M := M) β with hS_def
  set μ : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
    chartL2Measure (I := I) (M := M) β with hμ_def
  have hμ_eq : μ = (volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict S := by
    rw [hμ_def, chartL2Measure, hS_def]
  have hS_open : IsOpen S := chartTargetEuclid_isOpen (I := I) (M := M) β
  obtain ⟨uP, huP_contDiff, _huP_supp, huP_tendsto⟩ :=
    exists_chartComponent_limit_smooth_compactSupport (I := I) (M := M) g 0 2 F hcauchy β
  have hmemFn : ∀ n,
      MemLp (tensorChartComponent (I := I) (M := M) g 0 2 (F n) β P.1 P.2) 2 μ :=
    fun n => tensorChartComponent_memLp (I := I) (M := M) g 0 2 (F n) β P.1 P.2
  have hmemTrep : MemLp (tensorChartComponent (I := I) (M := M) g 0 2 Trep β P.1 P.2) 2 μ :=
    tensorChartComponent_memLp (I := I) (M := M) g 0 2 Trep β P.1 P.2
  have hL2cont : Tendsto (fun n => tensorL2ChartComponent (I := I) (M := M) g 0 2
        ((F n : TensorL2 0 2 g)) β P) atTop
        (𝓝 (tensorL2ChartComponent (I := I) (M := M) g 0 2 u β P)) :=
    ((continuous_tensorL2ChartComponent (I := I) (M := M) g 0 2 β P).tendsto u).comp hF_L2
  have hLp_Fn : ∀ n, tensorL2ChartComponent (I := I) (M := M) g 0 2
      ((F n : TensorL2 0 2 g)) β P = (hmemFn n).toLp _ :=
    fun n => tensorL2ChartComponent_smoothToTensorL2_eq (I := I) (M := M) g 0 2 (F n) β P
  have hLp_Trep : tensorL2ChartComponent (I := I) (M := M) g 0 2 u β P = hmemTrep.toLp _ := by
    rw [← hTrep]
    exact tensorL2ChartComponent_smoothToTensorL2_eq (I := I) (M := M) g 0 2 Trep β P
  rw [hLp_Trep] at hL2cont
  simp only [hLp_Fn] at hL2cont
  have heLp : Tendsto (fun n => eLpNorm
      (tensorChartComponent (I := I) (M := M) g 0 2 (F n) β P.1 P.2 -
        tensorChartComponent (I := I) (M := M) g 0 2 Trep β P.1 P.2) 2 μ) atTop (𝓝 0) := by
    have hed : Tendsto (fun n => edist ((hmemFn n).toLp _)
        (hmemTrep.toLp (tensorChartComponent (I := I) (M := M) g 0 2 Trep β P.1 P.2)))
        atTop (𝓝 (edist (hmemTrep.toLp _) (hmemTrep.toLp _))) :=
      hL2cont.edist tendsto_const_nhds
    rw [edist_self] at hed
    refine hed.congr (fun n => ?_)
    exact Lp.edist_toLp_toLp _ _ (hmemFn n) hmemTrep
  have h_tim : TendstoInMeasure μ
      (fun n => tensorChartComponent (I := I) (M := M) g 0 2 (F n) β P.1 P.2)
      atTop (tensorChartComponent (I := I) (M := M) g 0 2 Trep β P.1 P.2) :=
    MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm (μ := μ) (p := 2) (by norm_num)
      (fun n => (hmemFn n).aestronglyMeasurable) hmemTrep.aestronglyMeasurable heLp
  obtain ⟨σ, hσ_mono, hσ_ae⟩ := h_tim.exists_seq_tendsto_ae
  have hae_eq : (uP P) =ᵐ[μ] tensorChartComponent (I := I) (M := M) g 0 2 Trep β P.1 P.2 := by
    filter_upwards [hσ_ae] with z hz
    have hfull : Tendsto
        (fun n => tensorChartComponent (I := I) (M := M) g 0 2 (F (σ n)) β P.1 P.2 z)
        atTop (𝓝 (uP P z)) := (huP_tendsto P z).comp hσ_mono.tendsto_atTop
    exact tendsto_nhds_unique hfull hz
  have huP_contOn : ContinuousOn (uP P) S := (huP_contDiff P).continuousOn
  have hTrep_contOn :
      ContinuousOn (tensorChartComponent (I := I) (M := M) g 0 2 Trep β P.1 P.2) S :=
    (tensorChartComponent_contDiff' (I := I) (M := M) g 0 2 Trep β P.1 P.2).continuous.continuousOn
  have hEqOn :
      Set.EqOn (uP P) (tensorChartComponent (I := I) (M := M) g 0 2 Trep β P.1 P.2) S := by
    rw [hμ_eq] at hae_eq
    exact MeasureTheory.Measure.eqOn_of_ae_eq hae_eq huP_contOn hTrep_contOn
      (by rw [hS_open.interior_eq]; exact subset_closure)
  have hlimit_y :
      tensorChartComponent (I := I) (M := M) g 0 2 Trep β P.1 P.2 y = uP P y :=
    (hEqOn hy).symm
  rw [hlimit_y]
  exact huP_tendsto P y

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral in
open DifferentialGeometry.Analysis.Sobolev.Chart in

private theorem spectralPartialSum_ccTensorBilinSymm_tendsto
    (g : SmoothRiemannianMetric I M) (u : TensorL2 0 2 g)
    (hu : ∀ σ : ℝ, ∀ hσ : 0 ≤ σ,
      ∃ v : tensorHs (I := I) (M := M) g 0 2 σ,
        tensorHsToL2 (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2) hσ v = u)
    (Trep : SmoothCcTensor g 0 2)
    (hTrep : (Trep : TensorL2 0 2 g) = u)
    (x : M) (v w : TangentSpace I x) :
    Filter.Tendsto
      (fun n => ccTensorBilinSymm (I := I) g
          (spectralPartialSum (I := I) (M := M) g u n) x v w)
      Filter.atTop
      (𝓝 (ccTensorBilinSymm (I := I) g Trep x v w)) := by
  classical
  set F : ℕ → SmoothCcTensor g 0 2 :=
    fun n => spectralPartialSum (I := I) (M := M) g u n with hF_def
  have hcauchy : ∀ k : ℕ, CauchySeq (fun n =>
      SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) (2 * k) (F n)) :=
    fun k => spectralPartialSum_toHs_cauchy (I := I) (M := M) g u hu (2 * k)
  have hF_L2 : Tendsto (fun n => (F n : TensorL2 0 2 g)) atTop (𝓝 u) :=
    spectralPartialSum_toL2_tendsto (I := I) (M := M) g u

  have hsum := chartAtlasPOU_finset_sum_eq_one (I := I) (M := M) x
  have hexists : ∃ β ∈ chartAtlasPOU_finset (I := I) (M := M),
      0 < ((chartAtlasPOU I M) β : C^∞⟮I, M; ℝ⟯) x := by
    by_contra hcon
    push Not at hcon
    have hzero : ∀ β ∈ chartAtlasPOU_finset (I := I) (M := M),
        ((chartAtlasPOU I M) β : M → ℝ) x = 0 := by
      intro β hβ
      have hle := hcon β hβ
      have hnn := (chartAtlasPOU I M).nonneg β x
      linarith
    rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero] at hsum
    exact absurd hsum (by norm_num)
  obtain ⟨β, _hβmem, hβpos⟩ := hexists
  set ρ : ℝ := ((chartAtlasPOU I M) β : C^∞⟮I, M; ℝ⟯) x with hρ_def
  have hx_src : x ∈ (chartAt H β).source := by
    have hsub := chartAtlasPOU_isSubordinate (I := I) (M := M) β
    apply hsub
    exact subset_tsupport _ (Function.mem_support.mpr (ne_of_gt hβpos))
  set yx : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    toEuclidean (extChartAt I β x) with hyx_def
  have hyx_mem : yx ∈ chartTargetEuclid (I := I) (M := M) β :=
    toEuclidean_extChartAt_mem_chartTargetEuclid (I := I) (M := M) β hx_src
  have hround : (extChartAt I β).symm (toEuclidean.symm yx) = x := by
    rw [hyx_def, ContinuousLinearEquiv.symm_apply_apply]
    exact (extChartAt I β).left_inv (by rw [extChartAt_source (I := I)]; exact hx_src)

  have hcomp_eq : ∀ (Z : SmoothCcTensor g 0 2) (Q : CompIdx E 0 2),
      tensorChartComponent (I := I) (M := M) g 0 2 Z β Q.1 Q.2 yx =
        ρ * tensorChartComponentRaw (I := I) (M := M) g 0 2 Z β Q.1 Q.2 x := by
    intro Z Q
    rw [tensorChartComponent_def,
      chartPushedRaw_apply_of_mem (I := I) (M := M) β _ hyx_mem, hround]
    rfl

  have hraw_tendsto : ∀ Q : CompIdx E 0 2,
      Tendsto (fun n => tensorChartComponentRaw (I := I) (M := M) g 0 2 (F n) β Q.1 Q.2 x)
        atTop (𝓝 (tensorChartComponentRaw (I := I) (M := M) g 0 2 Trep β Q.1 Q.2 x)) := by
    intro Q
    have hct := spectralChartComponent_tendsto (I := I) (M := M) g u hcauchy hF_L2 Trep hTrep
      β Q hyx_mem
    simp only [hcomp_eq] at hct
    have hρne : ρ ≠ 0 := ne_of_gt hβpos
    have hscaled := hct.const_mul ρ⁻¹
    simp only [← mul_assoc, inv_mul_cancel₀ hρne, one_mul] at hscaled
    exact hscaled

  rw [ccTensorBilinSymm_eq_sum_chartBasis (I := I) (M := M) g Trep β hx_src v w]
  have hrw : (fun n => ccTensorBilinSymm (I := I) g (F n) x v w) =
      fun n => ∑ Q : CompIdx E 0 2,
        tensorChartComponentRaw (I := I) (M := M) g 0 2 (F n) β Q.1 Q.2 x *
          fibreSymmBilinForm (I := I) x
            (chartBasisFiberSection (I := I) (M := M) 0 2 β Q x) v w := by
    funext n
    exact ccTensorBilinSymm_eq_sum_chartBasis (I := I) (M := M) g (F n) β hx_src v w
  rw [hrw]
  refine tendsto_finset_sum _ (fun Q _ => ?_)
  exact (hraw_tendsto Q).mul_const _

private theorem realizedChartGramIncrement_eigenSeries_eq
    (g : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T)
    (T_rep : ℝ → SmoothCcTensor g 0 2)
    (φ : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ ∞ (φ i))
    (hcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ (i : TensorEigenIdx (I := I) (M := M) g 0 2),
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
            (SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2) (T_rep t)) i = φ i t)
    (hmodemass : ∀ (k : ℕ) (σ : ℝ), 0 ≤ σ →
      ∃ Cmaj : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable Cmaj ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv k (φ i) t) ^ 2 ≤ Cmaj i)
    (α : M) (i' j' : Fin (Module.finrank ℝ E)) :
    ∀ q ∈ Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target,
      ccTensorBilinSymm (I := I) g (T_rep q.1) ((extChartAt I α).symm q.2)
          (chartBasisVecFiber (I := I) α i' ((extChartAt I α).symm q.2))
          (chartBasisVecFiber (I := I) α j' ((extChartAt I α).symm q.2))
        = ∑' i, eigenChartIncrementMode (I := I) (M := M) g φ α i' j' i q := by
  classical
  rintro q ⟨hqt, hqy⟩
  set t : ℝ := q.1 with ht_def
  set x : M := (extChartAt I α).symm q.2 with hx_def
  set vv : TangentSpace I x := chartBasisVecFiber (I := I) α i' x with hvv
  set ww : TangentSpace I x := chartBasisVecFiber (I := I) α j' x with hww
  set u : TensorL2 0 2 g := SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2) (T_rep t) with hu_def

  have hcoeff_t : ∀ i, tensorL2Coeff (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2) u i = φ i t :=
    fun i => hcoeff t hqt i

  have hu : ∀ σ : ℝ, ∀ hσ : 0 ≤ σ,
      ∃ vH : tensorHs (I := I) (M := M) g 0 2 σ,
        tensorHsToL2 (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2) hσ vH = u := by
    refine allHs_of_weighted_summable (I := I) (M := M) g u (fun σ hσ => ?_)
    obtain ⟨Cmaj, hCmaj_sum, hCmaj⟩ := hmodemass 0 σ hσ
    refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) hCmaj_sum
    · exact mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i σ) (sq_nonneg _)
    · have h := hCmaj i t hqt
      rw [iteratedDeriv_zero] at h
      rw [hcoeff_t i]
      exact h

  have hpartial : ∀ n,
      ccTensorBilinSymm (I := I) g (spectralPartialSum (I := I) (M := M) g u n) x vv ww =
        ∑ i ∈ eigenIdxFinset (I := I) (M := M) g n,
          eigenChartIncrementMode (I := I) (M := M) g φ α i' j' i q := by
    intro n
    rw [spectralPartialSum, ccTensorBilinSymm_finiteEigenCombo]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hcoeff_t i, eigenChartIncrementMode]

  have hTrep_u : (T_rep t : TensorL2 0 2 g) = u := by rw [hu_def, SmoothCcTensor.toL2_apply]
  have htend_lhs : Filter.Tendsto
      (fun n => ∑ i ∈ eigenIdxFinset (I := I) (M := M) g n,
          eigenChartIncrementMode (I := I) (M := M) g φ α i' j' i q)
      Filter.atTop
      (𝓝 (ccTensorBilinSymm (I := I) g (T_rep t) x vv ww)) := by
    have h := spectralPartialSum_ccTensorBilinSymm_tendsto
      (I := I) (M := M) g u hu (T_rep t) hTrep_u x vv ww
    refine h.congr (fun n => (hpartial n))

  set Ω : Set E := interior (extChartAt I α).target with hΩ_def
  have hΩ_open : IsOpen Ω := isOpen_interior
  obtain ⟨r, hr_pos, hball_sub⟩ := Metric.isOpen_iff.mp hΩ_open q.2 hqy
  set Bc : Set E := Metric.closedBall q.2 (r / 2) with hBc_def
  have hBc_sub : Bc ⊆ Ω := by
    intro z hz
    rw [hBc_def, Metric.mem_closedBall] at hz
    exact hball_sub (by rw [Metric.mem_ball]; linarith)
  have hBc_compact : IsCompact Bc := isCompact_closedBall q.2 (r / 2)
  have hBc_int_ne : (interior Bc).Nonempty := by
    rw [hBc_def, interior_closedBall q.2 (by positivity : (r / 2) ≠ 0)]
    exact ⟨q.2, Metric.mem_ball_self (by positivity)⟩
  have huniqBc : UniqueDiffOn ℝ Bc :=
    uniqueDiffOn_convex (convex_closedBall q.2 (r / 2)) hBc_int_ne
  have hqBc : q.2 ∈ Bc := Metric.mem_closedBall_self (by positivity)
  have hqmemBc : q ∈ Set.Icc (0 : ℝ) T ×ˢ Bc := ⟨hqt, hqBc⟩
  obtain ⟨v0, hv0_sum, hv0_bd⟩ :=
    eigenChartIncrementMode_iteratedFDerivWithin_summable_majorant
      (I := I) (M := M) (T := T) g hT φ hφ_smooth hmodemass α i' j'
      hBc_compact huniqBc hBc_sub 0
  have hsummable : Summable (fun i =>
      eigenChartIncrementMode (I := I) (M := M) g φ α i' j' i q) := by
    refine Summable.of_norm_bounded hv0_sum (fun i => ?_)
    have hb := hv0_bd i q hqmemBc
    rwa [iteratedFDerivWithin_zero_eq_comp, Function.comp_apply,
      (LinearIsometryEquiv.norm_map _ _)] at hb

  have hhasSum : HasSum
      (fun i => eigenChartIncrementMode (I := I) (M := M) g φ α i' j' i q)
      (∑' i, eigenChartIncrementMode (I := I) (M := M) g φ α i' j' i q) :=
    hsummable.hasSum
  have htend_tsum : Filter.Tendsto
      (fun n => ∑ i ∈ eigenIdxFinset (I := I) (M := M) g n,
          eigenChartIncrementMode (I := I) (M := M) g φ α i' j' i q)
      Filter.atTop
      (𝓝 (∑' i, eigenChartIncrementMode (I := I) (M := M) g φ α i' j' i q)) :=
    hhasSum.comp (tendsto_eigenIdxFinset_atTop (I := I) (M := M) g)

  exact tendsto_nhds_unique htend_lhs htend_tsum

theorem realizedChartGramIncrement_euclidean_contDiffOn
    (g : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T)
    (T_rep : ℝ → SmoothCcTensor g 0 2)
    (φ : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ ∞ (φ i))
    (hcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ (i : TensorEigenIdx (I := I) (M := M) g 0 2),
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
            (SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2) (T_rep t)) i = φ i t)
    (hmodemass : ∀ (k : ℕ) (σ : ℝ), 0 ≤ σ →
      ∃ Cmaj : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable Cmaj ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv k (φ i) t) ^ 2 ≤ Cmaj i)
    (α : M) (i' j' : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun q : ℝ × E =>
        ccTensorBilinSymm (I := I) g (T_rep q.1) ((extChartAt I α).symm q.2)
          (chartBasisVecFiber (I := I) α i' ((extChartAt I α).symm q.2))
          (chartBasisVecFiber (I := I) α j' ((extChartAt I α).symm q.2)))
      (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target) := by
  set Ω : Set E := interior (extChartAt I α).target with hΩ_def
  have hΩ_open : IsOpen Ω := isOpen_interior
  refine contDiffOn_of_locally_contDiffOn ?_
  rintro ⟨t₀, y₀⟩ hmem
  obtain ⟨_ht₀, hy₀⟩ := hmem
  obtain ⟨r, hr_pos, hball_sub⟩ := Metric.isOpen_iff.mp hΩ_open y₀ hy₀

  refine ⟨Set.univ ×ˢ Metric.ball y₀ (r / 2), isOpen_univ.prod Metric.isOpen_ball,
    ⟨Set.mem_univ t₀, Metric.mem_ball_self (by positivity)⟩, ?_⟩
  set B : Set E := Metric.ball y₀ (r / 2) with hB_def
  set Bc : Set E := Metric.closedBall y₀ (r / 2) with hBc_def
  have hball_le : B ⊆ Bc := Metric.ball_subset_closedBall
  have hBc_sub : Bc ⊆ Ω := by
    intro x hx
    rw [hBc_def, Metric.mem_closedBall] at hx
    exact hball_sub (by rw [Metric.mem_ball]; linarith)
  have hB_sub : B ⊆ Ω := hball_le.trans hBc_sub
  have hBc_compact : IsCompact Bc := isCompact_closedBall y₀ (r / 2)
  have hslab_inter :
      (Set.Icc (0 : ℝ) T ×ˢ Ω) ∩ (Set.univ ×ˢ B) = Set.Icc (0 : ℝ) T ×ˢ B := by
    rw [Set.prod_inter_prod, Set.inter_univ, Set.inter_eq_right.mpr hB_sub]
  rw [hslab_inter]
  have hBc_int_ne : (interior Bc).Nonempty := by
    rw [hBc_def, interior_closedBall y₀ (by positivity : (r / 2) ≠ 0)]
    exact ⟨y₀, Metric.mem_ball_self (by positivity)⟩
  have hconv : Convex ℝ (Set.Icc (0 : ℝ) T ×ˢ Bc) :=
    (convex_Icc (0 : ℝ) T).prod (convex_closedBall y₀ (r / 2))
  have huniqBc : UniqueDiffOn ℝ Bc :=
    uniqueDiffOn_convex (convex_closedBall y₀ (r / 2)) hBc_int_ne
  have huniq : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) T ×ˢ Bc) :=
    (uniqueDiffOn_Icc hT).prod huniqBc
  have hmajorant :=
    eigenChartIncrementMode_iteratedFDerivWithin_summable_majorant
      (I := I) (M := M) (T := T) g hT φ hφ_smooth hmodemass α i' j' hBc_compact huniqBc hBc_sub
  classical
  set v : ℕ → TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ :=
    fun k => Classical.choose (hmajorant k) with hv_def
  have hv_spec : ∀ k, Summable (v k) ∧
      ∀ (i : TensorEigenIdx (I := I) (M := M) g 0 2) (q : ℝ × E),
        q ∈ Set.Icc (0 : ℝ) T ×ˢ Bc →
        ‖iteratedFDerivWithin ℝ k (eigenChartIncrementMode (I := I) (M := M) g φ α i' j' i)
            (Set.Icc (0 : ℝ) T ×ˢ Bc) q‖ ≤ v k i :=
    fun k => Classical.choose_spec (hmajorant k)
  have htsum_Bc : ContDiffOn ℝ ∞
      (fun q : ℝ × E => ∑' i, eigenChartIncrementMode (I := I) (M := M) g φ α i' j' i q)
      (Set.Icc (0 : ℝ) T ×ˢ Bc) := by
    refine DifferentialGeometry.Analysis.contDiffOn_tsum (v := v) (x₀ := (0, y₀))
      huniq hconv
      (fun i => (eigenChartIncrementMode_contDiffOn (I := I) (M := M) (T := T)
        g φ hφ_smooth α i' j' i).mono (Set.prod_mono (le_refl _) hBc_sub))
      (fun k _hk => (hv_spec k).1)
      (fun k i q hq _hk => (hv_spec k).2 i q hq)
      ⟨left_mem_Icc.mpr hT.le, Metric.mem_closedBall_self (by positivity)⟩
  have htsum : ContDiffOn ℝ ∞
      (fun q : ℝ × E => ∑' i, eigenChartIncrementMode (I := I) (M := M) g φ α i' j' i q)
      (Set.Icc (0 : ℝ) T ×ˢ B) :=
    htsum_Bc.mono (Set.prod_mono (le_refl _) hball_le)
  refine htsum.congr ?_
  intro q hq
  have hq' : q ∈ Set.Icc (0 : ℝ) T ×ˢ Ω := ⟨hq.1, hB_sub hq.2⟩
  exact realizedChartGramIncrement_eigenSeries_eq (I := I) (M := M) (T := T)
    g hT T_rep φ hφ_smooth hcoeff hmodemass α i' j' q hq'

private theorem realizedChartGramIncrement_alongChart_contMDiffOn
    (g : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T)
    (T_rep : ℝ → SmoothCcTensor g 0 2)
    (φ : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ ∞ (φ i))
    (hcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ (i : TensorEigenIdx (I := I) (M := M) g 0 2),
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
            (SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2) (T_rep t)) i = φ i t)
    (hmodemass : ∀ (k : ℕ) (σ : ℝ), 0 ≤ σ →
      ∃ Cmaj : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable Cmaj ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv k (φ i) t) ^ 2 ≤ Cmaj i)
    (α : M) (i' j' : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
      (fun q : ℝ × M =>
        ccTensorBilinSymm (I := I) g (T_rep q.1) q.2
          (chartBasisVecFiber (I := I) α i' q.2)
          (chartBasisVecFiber (I := I) α j' q.2))
      (Set.Icc (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) := by
  set G : ℝ × E → ℝ :=
    fun q : ℝ × E =>
      ccTensorBilinSymm (I := I) g (T_rep q.1) ((extChartAt I α).symm q.2)
        (chartBasisVecFiber (I := I) α i' ((extChartAt I α).symm q.2))
        (chartBasisVecFiber (I := I) α j' ((extChartAt I α).symm q.2)) with hG_def
  have hGEuclid : ContDiffOn ℝ ∞ G
      (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target) :=
    realizedChartGramIncrement_euclidean_contDiffOn
      (I := I) (M := M) g hT T_rep φ hφ_smooth hcoeff hmodemass α i' j'
  set f : ℝ × M → ℝ × E := fun q : ℝ × M => (q.1, extChartAt I α q.2) with hf_def
  have hf_smooth : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ × E) ∞ f
      (Set.Icc (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) := by
    refine ContMDiffOn.prodMk_space contMDiffOn_fst ?_
    refine (contMDiffOn_extChartAt (I := I) (n := ∞) (x := α)).comp contMDiffOn_snd ?_
    rintro ⟨t, x⟩ ⟨_, hx⟩
    rw [Integral.Measure.trivializationAt_baseSet_eq_chartAt_source (I := I)] at hx
    exact hx
  have hmaps : Set.MapsTo f
      (Set.Icc (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) α).baseSet)
      (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target) := by
    rintro ⟨t, x⟩ ⟨ht, hx⟩
    refine ⟨ht, ?_⟩
    rw [Integral.Measure.trivializationAt_baseSet_eq_chartAt_source (I := I)] at hx
    have hx' : x ∈ (extChartAt I α).source := by rw [extChartAt_source (I := I)]; exact hx
    have hmem : extChartAt I α x ∈ (extChartAt I α).target :=
      (extChartAt I α).map_source hx'
    rwa [(isOpen_extChartAt_target (I := I) α).interior_eq]
  have heq : Set.EqOn
      (fun q : ℝ × M =>
        ccTensorBilinSymm (I := I) g (T_rep q.1) q.2
          (chartBasisVecFiber (I := I) α i' q.2)
          (chartBasisVecFiber (I := I) α j' q.2))
      (G ∘ f)
      (Set.Icc (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) := by
    rintro ⟨t, x⟩ ⟨_, hx⟩
    rw [Integral.Measure.trivializationAt_baseSet_eq_chartAt_source (I := I)] at hx
    have hx' : x ∈ (extChartAt I α).source := by rw [extChartAt_source (I := I)]; exact hx
    simp only [Function.comp, hG_def, hf_def]
    rw [(extChartAt I α).left_inv hx']
  intro q hq
  refine (ContMDiffWithinAt.congr ?_ (fun y hy => heq hy) (heq hq))
  have hGf : ContDiffWithinAt ℝ ∞ G
      (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target) (f q) :=
    hGEuclid.contDiffWithinAt (hmaps hq)
  exact hGf.comp_contMDiffWithinAt (hf_smooth q hq) hmaps

theorem jointChartGramSmooth_of_spectralSmooth_timeSmooth
    (g : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T)
    (T_rep : ℝ → SmoothCcTensor g 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : ∀ t : ℝ, metricCauchySchwarzBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (T_rep t)) δ)
    (φ : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ ∞ (φ i))
    (hcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ (i : TensorEigenIdx (I := I) (M := M) g 0 2),
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
            (SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2) (T_rep t)) i = φ i t)
    (hmodemass : ∀ (k : ℕ) (σ : ℝ), 0 ≤ σ →
      ∃ Cmaj : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable Cmaj ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv k (φ i) t) ^ 2 ≤ Cmaj i) :
    JointChartGramSmooth (I := I) T
      (fun t : ℝ => tensorSectionRealizeMetric (I := I) g (T_rep t) hδ_lt (hδ t)) := by
  intro α i j
  have hincrement := realizedChartGramIncrement_alongChart_contMDiffOn
    (I := I) (M := M) g hT T_rep φ hφ_smooth hcoeff hmodemass α i j
  have hbg : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
      (fun p : ℝ × M =>
        Integral.Measure.chartGramMatrix (I := I) g α p.2 i j)
      (Set.Icc (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) := by
    have hbase := chartGramMatrix_entry_contMDiffOn (I := I) g α i j
    have hsnd : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M => p.2)
        (Set.Icc (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) :=
      contMDiffOn_snd
    have hmaps : Set.MapsTo (fun p : ℝ × M => p.2)
        (Set.Icc (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) α).baseSet)
        (trivializationAt E (TangentSpace I) α).baseSet :=
      fun p hp => hp.2
    exact hbase.comp hsnd hmaps
  refine (hbg.add hincrement).congr ?_
  rintro ⟨t, x⟩ _
  change Integral.Measure.chartGramMatrix (I := I)
      (tensorSectionRealizeMetric (I := I) g (T_rep t) hδ_lt (hδ t)) α x i j =
    Integral.Measure.chartGramMatrix (I := I) g α x i j +
      ccTensorBilinSymm (I := I) g (T_rep t) x
        (chartBasisVecFiber (I := I) α i x)
        (chartBasisVecFiber (I := I) α j x)
  rw [chartGramMatrix_apply, chartGramMatrix_apply,
    tensorSectionRealizeMetric_inner]

section FiniteOrderEigenSeries

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (eigenvectorSmooth
  tensorChartComponentRaw tensorChartComponentRaw_add tensorChartComponentRaw_smul
  tensorChartComponentProjection tensorChartBasisElement
  toEuclidean_extChartAt_mem_chartTargetEuclid)

private local instance tensorRSModel02NormedAddCommGroup_local :
    NormedAddCommGroup (Tensor0SBundle.TensorRSModel 0 2 ℝ E) :=
  Tensor0SBundle.tensorRSModel_normedAddCommGroup 0 2

private local instance tensorRSModel02NormedSpace_local :
    NormedSpace ℝ (Tensor0SBundle.TensorRSModel 0 2 ℝ E) :=
  Tensor0SBundle.tensorRSModel_normedSpace 0 2

def eigenRawIncrementMode
    (g : SmoothRiemannianMetric I M)
    (φ : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ)
    (α : M) (Jdx : Fin 2 → Fin (Module.finrank ℝ E))
    (i : TensorEigenIdx (I := I) (M := M) g 0 2) : ℝ × E → ℝ :=
  fun q : ℝ × E =>
    φ i q.1 * tensorChartComponentOnModel (I := I) (M := M) g
      (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α Jdx q.2

omit [BoundarylessManifold I M] in
lemma eigenRawIncrementMode_contDiffOn_ofOrder
    (g : SmoothRiemannianMetric I M) {T : ℝ} (kk : ℕ)
    (φ : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ (kk : ℕ) (φ i))
    (α : M) (Jdx : Fin 2 → Fin (Module.finrank ℝ E))
    (i : TensorEigenIdx (I := I) (M := M) g 0 2) :
    ContDiffOn ℝ (kk : ℕ) (eigenRawIncrementMode (I := I) (M := M) g φ α Jdx i)
      (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target) := by
  have htime : ContDiffOn ℝ (kk : ℕ) (fun q : ℝ × E => φ i q.1)
      (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target) :=
    ((hφ_smooth i).contDiffOn).comp contDiffOn_fst (Set.mapsTo_fst_prod)
  have hspace : ContDiffOn ℝ (kk : ℕ)
      (fun q : ℝ × E => tensorChartComponentOnModel (I := I) (M := M) g
        (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α Jdx q.2)
      (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target) :=
    ((rawCompOnE_contDiffOn (I := I) (M := M) g
        (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α Jdx).of_le
      (by exact_mod_cast le_top)).comp contDiffOn_snd (Set.mapsTo_snd_prod)
  exact htime.mul hspace

set_option maxHeartbeats 1600000 in
theorem eigenRawIncrementMode_iteratedFDerivWithin_summable_majorant_ofOrder
    (g : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T) (kk : ℕ)
    (φ : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ (kk : ℕ) (φ i))
    (hmodemass : ∀ (j : ℕ), j ≤ kk → ∀ (σ : ℝ), 0 ≤ σ →
      ∃ Cmaj : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable Cmaj ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv j (φ i) t) ^ 2 ≤ Cmaj i)
    (α : M) (Jdx : Fin 2 → Fin (Module.finrank ℝ E))
    {B : Set E} (hB_compact : IsCompact B) (hB_uniq : UniqueDiffOn ℝ B)
    (hB : B ⊆ interior (extChartAt I α).target) :
    ∀ n : ℕ, n ≤ kk →
      ∃ v : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable v ∧
        ∀ (i : TensorEigenIdx (I := I) (M := M) g 0 2) (q : ℝ × E),
          q ∈ Set.Icc (0 : ℝ) T ×ˢ B →
          ‖iteratedFDerivWithin ℝ n (eigenRawIncrementMode (I := I) (M := M) g φ α Jdx i)
              (Set.Icc (0 : ℝ) T ×ˢ B) q‖ ≤ v i := by
  classical
  intro n hn
  set O : Set E := interior (extChartAt I α).target with hO_def
  set s : Set (ℝ × E) := Set.Icc (0 : ℝ) T ×ˢ B with hs_def
  have hUD : UniqueDiffOn ℝ s := (uniqueDiffOn_Icc hT).prod hB_uniq
  obtain ⟨Csp, pSp, hCsp_nn, hCsp⟩ :=
    exists_rawCompOnE_eigen_jet_le_lambda_pow (I := I) (M := M) g α Jdx n hB_compact hB
  set sW : ℕ := weylSobolevExp (E := E) + 1 with hsW_def
  have hsW_gt : ((weylSobolevExp (E := E) : ℕ) : ℝ) < (sW : ℝ) := by
    rw [hsW_def]; push_cast; linarith
  set σ0 : ℝ := 2 * ((pSp : ℝ) + (sW : ℝ)) with hσ0_def
  have hσ0_nn : (0 : ℝ) ≤ σ0 := by rw [hσ0_def]; positivity
  have htime : ∀ a : ℕ, ∃ Cm : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ,
      a ≤ kk → Summable Cm ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ0 * (iteratedDeriv a (φ i) t) ^ 2 ≤ Cm i := by
    intro a
    by_cases ha : a ≤ kk
    · obtain ⟨Cm, h1, h2⟩ := hmodemass a ha σ0 hσ0_nn
      exact ⟨Cm, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨fun _ => 0, fun h => absurd h ha⟩
  choose Cmf hCmf using htime
  have hbase_pos : ∀ i : TensorEigenIdx (I := I) (M := M) g 0 2,
      (0 : ℝ) < 1 + TensorEigenIdx.lambda (I := I) (M := M) i := fun i => by
    have := tensor_lambda_nonneg (I := I) (M := M) i; linarith
  have hCm_nn : ∀ (a : ℕ), a ≤ kk →
      ∀ (i : TensorEigenIdx (I := I) (M := M) g 0 2), 0 ≤ Cmf a i := by
    intro a ha i
    have h := (hCmf a ha).2 i 0 (Set.left_mem_Icc.mpr hT.le)
    have hw := tensorSobolevWeight_pos (I := I) (M := M) i σ0
    nlinarith [sq_nonneg (iteratedDeriv a (φ i) 0), hw.le, h]
  have htime_pt : ∀ (j : ℕ), j ≤ kk →
      ∀ (i : TensorEigenIdx (I := I) (M := M) g 0 2), ∀ t ∈ Set.Icc (0 : ℝ) T,
      |iteratedDeriv j (φ i) t| ≤
        Real.sqrt (Cmf j i) *
          (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (-((pSp : ℝ) + (sW : ℝ))) := by
    intro j hj i t ht
    exact abs_le_sqrt_of_weight_sq_le (I := I) (M := M) g i ((pSp : ℝ) + (sW : ℝ))
      (by rw [← hσ0_def]; exact (hCmf j hj).2 i t ht)
  set Kconst : ℝ := (2 : ℝ) ^ n * (n.factorial : ℝ) * (n.factorial : ℝ) *
    (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) ^ n * (‖ContinuousLinearMap.snd ℝ ℝ E‖ + 1) ^ n *
    Csp with hKconst_def
  have hKconst_nn : 0 ≤ Kconst := by rw [hKconst_def]; positivity
  set wfun : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ :=
    fun i => tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ)) with hwfun_def
  have hwfun_nn : ∀ i, 0 ≤ wfun i := fun i => by
    rw [hwfun_def]; exact (tensorSobolevWeight_nonneg (I := I) (M := M) i _)
  have hsqrt_summable : ∀ j : ℕ, j ≤ kk →
      Summable (fun i => Real.sqrt (Cmf j i) * wfun i) := by
    intro j hj
    exact summable_sqrt_mul_weight_neg (I := I) (M := M) g (Cmf j) (hCmf j hj).1
      (hCm_nn j hj) hsW_gt
  set termf : ℕ → TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ :=
    fun a i => Kconst * ((∑ j ∈ Finset.range (a + 1), Real.sqrt (Cmf j i)) * wfun i)
    with htermf_def
  have htermf_summable : ∀ a : ℕ, a ≤ kk → Summable (termf a) := by
    intro a ha
    refine Summable.mul_left Kconst ?_
    have heq : (fun i => (∑ j ∈ Finset.range (a + 1), Real.sqrt (Cmf j i)) * wfun i) =
        (fun i => ∑ j ∈ Finset.range (a + 1), Real.sqrt (Cmf j i) * wfun i) := by
      funext i; rw [Finset.sum_mul]
    rw [heq]
    exact summable_sum (fun j hj => hsqrt_summable j
      (le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) ha))
  refine ⟨fun i => ∑ a ∈ Finset.range (n + 1), termf a i, ?_, ?_⟩
  · exact summable_sum (fun a ha => htermf_summable a
      (le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)) hn))
  · intro i q hq
    have hqt : q.1 ∈ Set.Icc (0 : ℝ) T := hq.1
    have hqB : q.2 ∈ B := hq.2
    have hbase_nn : (0 : ℝ) ≤ 1 + TensorEigenIdx.lambda (I := I) (M := M) i :=
      (hbase_pos i).le
    have hcd_fst : ContDiffOn ℝ (kk : ℕ) (fun p : ℝ × E => φ i p.1) s :=
      ((hφ_smooth i).contDiffOn).comp contDiffOn_fst (Set.mapsTo_fst_prod)
    have hcd_snd : ContDiffOn ℝ (kk : ℕ)
        (fun p : ℝ × E => tensorChartComponentOnModel (I := I) (M := M) g
          (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α Jdx p.2) s := by
      refine (((rawCompOnE_contDiffOn (I := I) (M := M) g
          (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α Jdx).of_le
        (by exact_mod_cast le_top)).comp contDiffOn_snd ?_)
      intro p hp; exact hB hp.2
    have heqmode : eigenRawIncrementMode (I := I) (M := M) g φ α Jdx i =
        (fun p : ℝ × E => φ i p.1) *
          (fun p : ℝ × E => tensorChartComponentOnModel (I := I) (M := M) g
            (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α Jdx p.2) := by
      funext p; rw [eigenRawIncrementMode]; rfl
    rw [heqmode]
    have hleib := norm_iteratedFDerivWithin_mul_le (𝕜 := ℝ)
      (f := fun p : ℝ × E => φ i p.1)
      (g := fun p : ℝ × E => tensorChartComponentOnModel (I := I) (M := M) g
        (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α Jdx p.2)
      hcd_fst hcd_snd hUD (x := q) hq (n := n) (by exact_mod_cast hn)
    refine le_trans hleib ?_
    change _ ≤ ∑ a ∈ Finset.range (n + 1), termf a i
    refine Finset.sum_le_sum (fun a ha => ?_)
    have han : a ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
    have hak : a ≤ kk := le_trans han hn
    set Cφa : ℝ := (∑ j ∈ Finset.range (a + 1), Real.sqrt (Cmf j i)) *
      (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (-((pSp : ℝ) + (sW : ℝ)))
      with hCφa_def
    have hCφa_nn : 0 ≤ Cφa := by
      rw [hCφa_def]
      exact mul_nonneg (Finset.sum_nonneg (fun j _ => Real.sqrt_nonneg _))
        (Real.rpow_nonneg hbase_nn _)
    have hfst_bnd := norm_iteratedFDerivWithin_compFst_le_ofOrder
      kk (φ i) (hφ_smooth i) hUD hT a hak q hq Cφa
      (fun jj hjj => by
        rw [Real.norm_eq_abs]
        refine le_trans (htime_pt jj (le_trans hjj hak) i q.1 hqt) ?_
        rw [hCφa_def]
        refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hbase_nn _)
        refine Finset.single_le_sum (f := fun j => Real.sqrt (Cmf j i))
          (fun j _ => Real.sqrt_nonneg _) (Finset.mem_range.mpr (by omega)))
    have hsnd_bnd := norm_iteratedFDerivWithin_compSnd_le
      (tensorChartComponentOnModel (I := I) (M := M) g
        (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α Jdx) isOpen_interior
      (rawCompOnE_contDiffOn (I := I) (M := M) g
        (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α Jdx) hB hUD (n - a) q hq
      (Csp * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ pSp)
      (fun jj hjj => hCsp jj (by omega) i q.2 hqB)
    have hgn_nn : (0:ℝ) ≤ ‖iteratedFDerivWithin ℝ (n - a)
        (fun p : ℝ × E => tensorChartComponentOnModel (I := I) (M := M) g
          (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α Jdx p.2) s q‖ := norm_nonneg _
    have hchoose_nn : (0:ℝ) ≤ (n.choose a : ℝ) := by positivity
    have hprod : ‖iteratedFDerivWithin ℝ a (fun p : ℝ × E => φ i p.1) s q‖ *
          ‖iteratedFDerivWithin ℝ (n - a)
            (fun p : ℝ × E => tensorChartComponentOnModel (I := I) (M := M) g
              (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α Jdx p.2) s q‖ ≤
        ((a.factorial : ℝ) * Cφa * (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) ^ a) *
          (((n - a).factorial : ℝ) *
            (Csp * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ pSp) *
            (‖ContinuousLinearMap.snd ℝ ℝ E‖ + 1) ^ (n - a)) := by
      refine mul_le_mul hfst_bnd hsnd_bnd hgn_nn ?_
      positivity
    calc (n.choose a : ℝ) * ‖iteratedFDerivWithin ℝ a (fun p : ℝ × E => φ i p.1) s q‖ *
            ‖iteratedFDerivWithin ℝ (n - a)
              (fun p : ℝ × E => tensorChartComponentOnModel (I := I) (M := M) g
                (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α Jdx p.2) s q‖
        = (n.choose a : ℝ) * (‖iteratedFDerivWithin ℝ a (fun p : ℝ × E => φ i p.1) s q‖ *
            ‖iteratedFDerivWithin ℝ (n - a)
              (fun p : ℝ × E => tensorChartComponentOnModel (I := I) (M := M) g
                (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α Jdx p.2) s q‖) := by ring
      _ ≤ (n.choose a : ℝ) *
            (((a.factorial : ℝ) * Cφa * (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) ^ a) *
            (((n - a).factorial : ℝ) *
              (Csp * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ pSp) *
              (‖ContinuousLinearMap.snd ℝ ℝ E‖ + 1) ^ (n - a))) :=
          mul_le_mul_of_nonneg_left hprod hchoose_nn
      _ ≤ termf a i := by
          simp only [htermf_def, hCφa_def, hKconst_def, hwfun_def]
          have hcollapse :
              (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (-((pSp : ℝ) + (sW : ℝ))) *
              (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ pSp =
              tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ)) := by
            unfold tensorSobolevWeight
            rw [← Real.rpow_natCast (1 + TensorEigenIdx.lambda (I := I) (M := M) i) pSp,
              ← Real.rpow_add (hbase_pos i)]
            congr 1; ring
          set Ssqrt : ℝ := ∑ j ∈ Finset.range (a + 1), Real.sqrt (Cmf j i) with hSs_def
          have hSs_nn : 0 ≤ Ssqrt := Finset.sum_nonneg (fun j _ => Real.sqrt_nonneg _)
          have hbinom : (n.choose a : ℝ) ≤ (2 : ℝ) ^ n := by
            calc (n.choose a : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) := by
                  exact_mod_cast Nat.choose_le_two_pow n a
              _ = (2:ℝ) ^ n := by push_cast; ring
          have hfa : (a.factorial : ℝ) ≤ (n.factorial : ℝ) := by
            exact_mod_cast Nat.factorial_le han
          have hfka : ((n-a).factorial : ℝ) ≤ (n.factorial : ℝ) := by
            exact_mod_cast Nat.factorial_le (by omega)
          have hfst_pow : (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) ^ a ≤
              (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) ^ n :=
            pow_le_pow_right₀
              (by linarith [norm_nonneg (ContinuousLinearMap.fst ℝ ℝ E)]) han
          have hsnd_pow : (‖ContinuousLinearMap.snd ℝ ℝ E‖ + 1) ^ (n - a) ≤
              (‖ContinuousLinearMap.snd ℝ ℝ E‖ + 1) ^ n :=
            pow_le_pow_right₀
              (by linarith [norm_nonneg (ContinuousLinearMap.snd ℝ ℝ E)]) (by omega)
          have hlhs_eq : (n.choose a : ℝ) * (((a.factorial : ℝ) *
                (Ssqrt *
                  (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^
                    (-((pSp : ℝ) + (sW : ℝ)))) *
                (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) ^ a) *
              (((n - a).factorial : ℝ) *
                (Csp * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ pSp) *
                (‖ContinuousLinearMap.snd ℝ ℝ E‖ + 1) ^ (n - a))) =
              ((n.choose a : ℝ) * (a.factorial : ℝ) * ((n-a).factorial : ℝ) *
                (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) ^ a *
                (‖ContinuousLinearMap.snd ℝ ℝ E‖ + 1) ^ (n - a) * Csp) *
              (Ssqrt *
                ((1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^
                    (-((pSp : ℝ) + (sW : ℝ))) *
                  (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ pSp)) := by ring
          rw [hlhs_eq, hcollapse]
          have hrhs_eq : (2 : ℝ) ^ n * (n.factorial : ℝ) * (n.factorial : ℝ) *
                (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) ^ n *
                (‖ContinuousLinearMap.snd ℝ ℝ E‖ + 1) ^ n * Csp *
              (Ssqrt * tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ))) =
              ((2 : ℝ) ^ n * (n.factorial : ℝ) * (n.factorial : ℝ) *
                (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) ^ n *
                (‖ContinuousLinearMap.snd ℝ ℝ E‖ + 1) ^ n * Csp) *
              (Ssqrt * tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ))) := by ring
          rw [hrhs_eq]
          refine mul_le_mul ?_ (le_refl _) ?_ (by positivity)
          · have hfst_nn : (0:ℝ) ≤ (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) := by positivity
            have hsnd_nn : (0:ℝ) ≤ (‖ContinuousLinearMap.snd ℝ ℝ E‖ + 1) := by positivity
            gcongr
          · exact mul_nonneg hSs_nn (tensorSobolevWeight_nonneg (I := I) (M := M) i _)

lemma exists_rawComponentRaw_eigen_pointwise_le_lambda_pow
    (g : SmoothRiemannianMetric I M) (α : M)
    (Jdx : Fin 2 → Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ (chartAt H α).source) :
    ∃ (C : ℝ) (p : ℕ), 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g 0 2,
        |tensorChartComponentRaw (I := I) (M := M) g 0 2
            (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α ![] Jdx x| ≤
          C * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ p := by
  have hx' : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source (I := I)]; exact hx
  set y : E := extChartAt I α x with hy_def
  have hy_int : y ∈ interior (extChartAt I α).target := by
    rw [(isOpen_extChartAt_target (I := I) α).interior_eq]
    exact (extChartAt I α).map_source hx'
  obtain ⟨C, p, hC_nn, hC⟩ := exists_rawCompOnE_eigen_jet_le_lambda_pow (I := I) (M := M)
    g α Jdx 0 isCompact_singleton (Set.singleton_subset_iff.mpr hy_int)
  refine ⟨C, p, hC_nn, fun i => ?_⟩
  have h0 := hC 0 le_rfl i y (Set.mem_singleton y)
  rw [iteratedFDerivWithin_zero_eq_comp, Function.comp_apply,
    LinearIsometryEquiv.norm_map] at h0
  have heq : tensorChartComponentOnModel (I := I) (M := M) g
      (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α Jdx y =
      tensorChartComponentRaw (I := I) (M := M) g 0 2
        (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α ![] Jdx
        ((extChartAt I α).symm y) := rfl
  have hxy : (extChartAt I α).symm y = x := (extChartAt I α).left_inv hx'
  rw [heq, hxy, Real.norm_eq_abs] at h0
  exact h0

omit [BoundarylessManifold I M] in
lemma tensorChartComponentRaw_finiteEigenCombo
    (g : SmoothRiemannianMetric I M)
    (F : Finset (TensorEigenIdx (I := I) (M := M) g 0 2))
    (c : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ) (α : M)
    (Idx : Fin 0 → Fin (Module.finrank ℝ E))
    (Jdx : Fin 2 → Fin (Module.finrank ℝ E)) (x : M) :
    tensorChartComponentRaw (I := I) (M := M) g 0 2
        (finiteEigenCombo (I := I) (M := M) g F c) α Idx Jdx x =
      ∑ i ∈ F, c i * tensorChartComponentRaw (I := I) (M := M) g 0 2
        (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α Idx Jdx x := by
  classical
  rw [finiteEigenCombo_eq]
  induction F using Finset.induction with
  | empty =>
      simp only [Finset.sum_empty]
      have h0 : (0 : SmoothCcTensor g 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g 0 2) := by
        rw [zero_smul]
      rw [h0, tensorChartComponentRaw_smul (I := I) (M := M)]
      simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        tensorChartComponentRaw_add (I := I) (M := M),
        tensorChartComponentRaw_smul (I := I) (M := M), ih]
      simp [smul_eq_mul]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma pdIter_rawCompOnE_contDiffOn
    (g : SmoothRiemannianMetric I M) (S : SmoothCcTensor g 0 2) (α : M)
    (Jdx : Fin 2 → Fin (Module.finrank ℝ E)) (L : List E) :
    ContDiffOn ℝ ∞
      (DifferentialGeometry.Analysis.iteratedDirDeriv L (tensorChartComponentOnModel (I := I) (M := M) g S α Jdx))
      (interior (extChartAt I α).target) :=
  DifferentialGeometry.Analysis.pdIter_contDiffOn isOpen_interior
    (rawCompOnE_contDiffOn (I := I) (M := M) g S α Jdx) L

lemma exists_pdIter_rawCompOnE_eigen_jet_le_lambda_pow
    (g : SmoothRiemannianMetric I M) (α : M)
    (Jdx : Fin 2 → Fin (Module.finrank ℝ E)) (m : ℕ) (L : List E)
    {B : Set E} (hB_compact : IsCompact B)
    (hB : B ⊆ interior (extChartAt I α).target) :
    ∃ (C : ℝ) (p : ℕ), 0 ≤ C ∧
      ∀ (m' : ℕ), m' ≤ m → ∀ (i : TensorEigenIdx (I := I) (M := M) g 0 2), ∀ y ∈ B,
        ‖iteratedFDerivWithin ℝ m'
            (DifferentialGeometry.Analysis.iteratedDirDeriv L (tensorChartComponentOnModel (I := I) (M := M) g
              (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α Jdx))
            (interior (extChartAt I α).target) y‖ ≤
          C * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ p := by
  classical
  obtain ⟨C, p, hC_nn, hC⟩ := exists_rawCompOnE_eigen_jet_le_lambda_pow (I := I) (M := M)
    g α Jdx (m + L.length) hB_compact hB
  set Cnorm : ℝ := (L.map (fun v => ‖v‖)).prod with hCnorm_def
  have hCnorm_nn : 0 ≤ Cnorm := List.prod_nonneg (by
    intro a ha
    simp only [List.mem_map] at ha
    obtain ⟨w, _, hw⟩ := ha
    rw [← hw]; exact norm_nonneg w)
  refine ⟨Cnorm * C, p, by positivity, fun m' hm' i y hy => ?_⟩
  have h1 := DifferentialGeometry.Analysis.norm_iteratedFDerivWithin_pdIter_le
    isOpen_interior (rawCompOnE_contDiffOn (I := I) (M := M) g
      (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α Jdx) L (hB hy) m'
  have h2 := hC (m' + L.length) (by omega) i y hy
  calc ‖iteratedFDerivWithin ℝ m'
        (DifferentialGeometry.Analysis.iteratedDirDeriv L (tensorChartComponentOnModel (I := I) (M := M) g
          (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α Jdx))
        (interior (extChartAt I α).target) y‖
      ≤ Cnorm * ‖iteratedFDerivWithin ℝ (m' + L.length)
          (tensorChartComponentOnModel (I := I) (M := M) g
            (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α Jdx)
          (interior (extChartAt I α).target) y‖ := h1
    _ ≤ Cnorm * (C * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ p) :=
        mul_le_mul_of_nonneg_left h2 hCnorm_nn
    _ = Cnorm * C * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ p := by ring

omit [BoundarylessManifold I M] in
set_option maxHeartbeats 1600000 in
theorem eigenTimeSpatialProductMode_iteratedFDerivWithin_summable_majorant_ofOrder
    (g : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T) (kk : ℕ)
    (φ : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ (kk : ℕ) (φ i))
    (hmodemass : ∀ (j : ℕ), j ≤ kk → ∀ (σ : ℝ), 0 ≤ σ →
      ∃ Cmaj : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable Cmaj ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv j (φ i) t) ^ 2 ≤ Cmaj i)
    (ψ : TensorEigenIdx (I := I) (M := M) g 0 2 → E → ℝ)
    {O : Set E} (hO_open : IsOpen O)
    (hψ_smooth : ∀ i, ContDiffOn ℝ ∞ (ψ i) O)
    {B : Set E} (hB_uniq : UniqueDiffOn ℝ B) (hBO : B ⊆ O)
    (Csp : ℝ) (pSp : ℕ) (hCsp_nn : 0 ≤ Csp)
    (hCsp : ∀ (n : ℕ), n ≤ kk → ∀ (i : TensorEigenIdx (I := I) (M := M) g 0 2),
      ∀ y ∈ B, ‖iteratedFDerivWithin ℝ n (ψ i) O y‖ ≤
        Csp * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ pSp) :
    ∀ n : ℕ, n ≤ kk →
      ∃ v : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable v ∧
        ∀ (i : TensorEigenIdx (I := I) (M := M) g 0 2) (q : ℝ × E),
          q ∈ Set.Icc (0 : ℝ) T ×ˢ B →
          ‖iteratedFDerivWithin ℝ n (fun p : ℝ × E => φ i p.1 * ψ i p.2)
              (Set.Icc (0 : ℝ) T ×ˢ B) q‖ ≤ v i := by
  classical
  intro n hn
  set s : Set (ℝ × E) := Set.Icc (0 : ℝ) T ×ˢ B with hs_def
  have hUD : UniqueDiffOn ℝ s := (uniqueDiffOn_Icc hT).prod hB_uniq
  set sW : ℕ := weylSobolevExp (E := E) + 1 with hsW_def
  have hsW_gt : ((weylSobolevExp (E := E) : ℕ) : ℝ) < (sW : ℝ) := by
    rw [hsW_def]; push_cast; linarith
  set σ0 : ℝ := 2 * ((pSp : ℝ) + (sW : ℝ)) with hσ0_def
  have hσ0_nn : (0 : ℝ) ≤ σ0 := by rw [hσ0_def]; positivity
  have htime : ∀ a : ℕ, ∃ Cm : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ,
      a ≤ kk → Summable Cm ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ0 * (iteratedDeriv a (φ i) t) ^ 2 ≤ Cm i := by
    intro a
    by_cases ha : a ≤ kk
    · obtain ⟨Cm, h1, h2⟩ := hmodemass a ha σ0 hσ0_nn
      exact ⟨Cm, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨fun _ => 0, fun h => absurd h ha⟩
  choose Cmf hCmf using htime
  have hbase_pos : ∀ i : TensorEigenIdx (I := I) (M := M) g 0 2,
      (0 : ℝ) < 1 + TensorEigenIdx.lambda (I := I) (M := M) i := fun i => by
    have := tensor_lambda_nonneg (I := I) (M := M) i; linarith
  have hCm_nn : ∀ (a : ℕ), a ≤ kk →
      ∀ (i : TensorEigenIdx (I := I) (M := M) g 0 2), 0 ≤ Cmf a i := by
    intro a ha i
    have h := (hCmf a ha).2 i 0 (Set.left_mem_Icc.mpr hT.le)
    have hw := tensorSobolevWeight_pos (I := I) (M := M) i σ0
    nlinarith [sq_nonneg (iteratedDeriv a (φ i) 0), hw.le, h]
  have htime_pt : ∀ (j : ℕ), j ≤ kk →
      ∀ (i : TensorEigenIdx (I := I) (M := M) g 0 2), ∀ t ∈ Set.Icc (0 : ℝ) T,
      |iteratedDeriv j (φ i) t| ≤
        Real.sqrt (Cmf j i) *
          (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (-((pSp : ℝ) + (sW : ℝ))) := by
    intro j hj i t ht
    exact abs_le_sqrt_of_weight_sq_le (I := I) (M := M) g i ((pSp : ℝ) + (sW : ℝ))
      (by rw [← hσ0_def]; exact (hCmf j hj).2 i t ht)
  set Kconst : ℝ := (2 : ℝ) ^ n * (n.factorial : ℝ) * (n.factorial : ℝ) *
    (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) ^ n * (‖ContinuousLinearMap.snd ℝ ℝ E‖ + 1) ^ n *
    Csp with hKconst_def
  have hKconst_nn : 0 ≤ Kconst := by rw [hKconst_def]; positivity
  set wfun : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ :=
    fun i => tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ)) with hwfun_def
  have hwfun_nn : ∀ i, 0 ≤ wfun i := fun i => by
    rw [hwfun_def]; exact (tensorSobolevWeight_nonneg (I := I) (M := M) i _)
  have hsqrt_summable : ∀ j : ℕ, j ≤ kk →
      Summable (fun i => Real.sqrt (Cmf j i) * wfun i) := by
    intro j hj
    exact summable_sqrt_mul_weight_neg (I := I) (M := M) g (Cmf j) (hCmf j hj).1
      (hCm_nn j hj) hsW_gt
  set termf : ℕ → TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ :=
    fun a i => Kconst * ((∑ j ∈ Finset.range (a + 1), Real.sqrt (Cmf j i)) * wfun i)
    with htermf_def
  have htermf_summable : ∀ a : ℕ, a ≤ kk → Summable (termf a) := by
    intro a ha
    refine Summable.mul_left Kconst ?_
    have heq : (fun i => (∑ j ∈ Finset.range (a + 1), Real.sqrt (Cmf j i)) * wfun i) =
        (fun i => ∑ j ∈ Finset.range (a + 1), Real.sqrt (Cmf j i) * wfun i) := by
      funext i; rw [Finset.sum_mul]
    rw [heq]
    exact summable_sum (fun j hj => hsqrt_summable j
      (le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) ha))
  refine ⟨fun i => ∑ a ∈ Finset.range (n + 1), termf a i, ?_, ?_⟩
  · exact summable_sum (fun a ha => htermf_summable a
      (le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)) hn))
  · intro i q hq
    have hqt : q.1 ∈ Set.Icc (0 : ℝ) T := hq.1
    have hqB : q.2 ∈ B := hq.2
    have hbase_nn : (0 : ℝ) ≤ 1 + TensorEigenIdx.lambda (I := I) (M := M) i :=
      (hbase_pos i).le
    have hcd_fst : ContDiffOn ℝ (kk : ℕ) (fun p : ℝ × E => φ i p.1) s :=
      ((hφ_smooth i).contDiffOn).comp contDiffOn_fst (Set.mapsTo_fst_prod)
    have hcd_snd : ContDiffOn ℝ (kk : ℕ) (fun p : ℝ × E => ψ i p.2) s := by
      refine ((hψ_smooth i).of_le (by exact_mod_cast le_top)).comp contDiffOn_snd ?_
      intro p hp; exact hBO hp.2
    have heqmode : (fun p : ℝ × E => φ i p.1 * ψ i p.2) =
        (fun p : ℝ × E => φ i p.1) * (fun p : ℝ × E => ψ i p.2) := rfl
    rw [heqmode]
    have hleib := norm_iteratedFDerivWithin_mul_le (𝕜 := ℝ)
      (f := fun p : ℝ × E => φ i p.1)
      (g := fun p : ℝ × E => ψ i p.2)
      hcd_fst hcd_snd hUD (x := q) hq (n := n) (by exact_mod_cast hn)
    refine le_trans hleib ?_
    change _ ≤ ∑ a ∈ Finset.range (n + 1), termf a i
    refine Finset.sum_le_sum (fun a ha => ?_)
    have han : a ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
    have hak : a ≤ kk := le_trans han hn
    set Cφa : ℝ := (∑ j ∈ Finset.range (a + 1), Real.sqrt (Cmf j i)) *
      (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (-((pSp : ℝ) + (sW : ℝ)))
      with hCφa_def
    have hCφa_nn : 0 ≤ Cφa := by
      rw [hCφa_def]
      exact mul_nonneg (Finset.sum_nonneg (fun j _ => Real.sqrt_nonneg _))
        (Real.rpow_nonneg hbase_nn _)
    have hfst_bnd := norm_iteratedFDerivWithin_compFst_le_ofOrder
      kk (φ i) (hφ_smooth i) hUD hT a hak q hq Cφa
      (fun jj hjj => by
        rw [Real.norm_eq_abs]
        refine le_trans (htime_pt jj (le_trans hjj hak) i q.1 hqt) ?_
        rw [hCφa_def]
        refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hbase_nn _)
        refine Finset.single_le_sum (f := fun j => Real.sqrt (Cmf j i))
          (fun j _ => Real.sqrt_nonneg _) (Finset.mem_range.mpr (by omega)))
    have hsnd_bnd := norm_iteratedFDerivWithin_compSnd_le
      (ψ i) hO_open (hψ_smooth i) hBO hUD (n - a) q hq
      (Csp * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ pSp)
      (fun jj hjj => hCsp jj (by omega) i q.2 hqB)
    have hgn_nn : (0:ℝ) ≤ ‖iteratedFDerivWithin ℝ (n - a)
        (fun p : ℝ × E => ψ i p.2) s q‖ := norm_nonneg _
    have hchoose_nn : (0:ℝ) ≤ (n.choose a : ℝ) := by positivity
    have hprod : ‖iteratedFDerivWithin ℝ a (fun p : ℝ × E => φ i p.1) s q‖ *
          ‖iteratedFDerivWithin ℝ (n - a) (fun p : ℝ × E => ψ i p.2) s q‖ ≤
        ((a.factorial : ℝ) * Cφa * (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) ^ a) *
          (((n - a).factorial : ℝ) *
            (Csp * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ pSp) *
            (‖ContinuousLinearMap.snd ℝ ℝ E‖ + 1) ^ (n - a)) := by
      refine mul_le_mul hfst_bnd hsnd_bnd hgn_nn ?_
      positivity
    calc (n.choose a : ℝ) * ‖iteratedFDerivWithin ℝ a (fun p : ℝ × E => φ i p.1) s q‖ *
            ‖iteratedFDerivWithin ℝ (n - a) (fun p : ℝ × E => ψ i p.2) s q‖
        = (n.choose a : ℝ) * (‖iteratedFDerivWithin ℝ a (fun p : ℝ × E => φ i p.1) s q‖ *
            ‖iteratedFDerivWithin ℝ (n - a) (fun p : ℝ × E => ψ i p.2) s q‖) := by ring
      _ ≤ (n.choose a : ℝ) *
            (((a.factorial : ℝ) * Cφa * (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) ^ a) *
            (((n - a).factorial : ℝ) *
              (Csp * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ pSp) *
              (‖ContinuousLinearMap.snd ℝ ℝ E‖ + 1) ^ (n - a))) :=
          mul_le_mul_of_nonneg_left hprod hchoose_nn
      _ ≤ termf a i := by
          simp only [htermf_def, hCφa_def, hKconst_def, hwfun_def]
          have hcollapse :
              (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (-((pSp : ℝ) + (sW : ℝ))) *
              (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ pSp =
              tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ)) := by
            unfold tensorSobolevWeight
            rw [← Real.rpow_natCast (1 + TensorEigenIdx.lambda (I := I) (M := M) i) pSp,
              ← Real.rpow_add (hbase_pos i)]
            congr 1; ring
          set Ssqrt : ℝ := ∑ j ∈ Finset.range (a + 1), Real.sqrt (Cmf j i) with hSs_def
          have hSs_nn : 0 ≤ Ssqrt := Finset.sum_nonneg (fun j _ => Real.sqrt_nonneg _)
          have hbinom : (n.choose a : ℝ) ≤ (2 : ℝ) ^ n := by
            calc (n.choose a : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) := by
                  exact_mod_cast Nat.choose_le_two_pow n a
              _ = (2:ℝ) ^ n := by push_cast; ring
          have hfa : (a.factorial : ℝ) ≤ (n.factorial : ℝ) := by
            exact_mod_cast Nat.factorial_le han
          have hfka : ((n-a).factorial : ℝ) ≤ (n.factorial : ℝ) := by
            exact_mod_cast Nat.factorial_le (by omega)
          have hfst_pow : (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) ^ a ≤
              (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) ^ n :=
            pow_le_pow_right₀
              (by linarith [norm_nonneg (ContinuousLinearMap.fst ℝ ℝ E)]) han
          have hsnd_pow : (‖ContinuousLinearMap.snd ℝ ℝ E‖ + 1) ^ (n - a) ≤
              (‖ContinuousLinearMap.snd ℝ ℝ E‖ + 1) ^ n :=
            pow_le_pow_right₀
              (by linarith [norm_nonneg (ContinuousLinearMap.snd ℝ ℝ E)]) (by omega)
          have hlhs_eq : (n.choose a : ℝ) * (((a.factorial : ℝ) *
                (Ssqrt *
                  (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^
                    (-((pSp : ℝ) + (sW : ℝ)))) *
                (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) ^ a) *
              (((n - a).factorial : ℝ) *
                (Csp * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ pSp) *
                (‖ContinuousLinearMap.snd ℝ ℝ E‖ + 1) ^ (n - a))) =
              ((n.choose a : ℝ) * (a.factorial : ℝ) * ((n-a).factorial : ℝ) *
                (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) ^ a *
                (‖ContinuousLinearMap.snd ℝ ℝ E‖ + 1) ^ (n - a) * Csp) *
              (Ssqrt *
                ((1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^
                    (-((pSp : ℝ) + (sW : ℝ))) *
                  (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ pSp)) := by ring
          rw [hlhs_eq, hcollapse]
          have hrhs_eq : (2 : ℝ) ^ n * (n.factorial : ℝ) * (n.factorial : ℝ) *
                (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) ^ n *
                (‖ContinuousLinearMap.snd ℝ ℝ E‖ + 1) ^ n * Csp *
              (Ssqrt * tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ))) =
              ((2 : ℝ) ^ n * (n.factorial : ℝ) * (n.factorial : ℝ) *
                (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) ^ n *
                (‖ContinuousLinearMap.snd ℝ ℝ E‖ + 1) ^ n * Csp) *
              (Ssqrt * tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ))) := by ring
          rw [hrhs_eq]
          refine mul_le_mul ?_ (le_refl _) ?_ (by positivity)
          · have hfst_nn : (0:ℝ) ≤ (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) := by positivity
            have hsnd_nn : (0:ℝ) ≤ (‖ContinuousLinearMap.snd ℝ ℝ E‖ + 1) := by positivity
            gcongr
          · exact mul_nonneg hSs_nn (tensorSobolevWeight_nonneg (I := I) (M := M) i _)

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
lemma chartGramOnE_realize_eq_add_half_rawCompOnE
    (g : SmoothRiemannianMetric I M) (S : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g (ccTensorBilinSymm (I := I) g S) δ)
    (α : M) (a b : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    Integral.DivergenceTheorem.chartGramOnE (I := I)
        (tensorSectionRealizeMetric (I := I) g S hδ_lt hδ) α a b y =
      Integral.DivergenceTheorem.chartGramOnE (I := I) g α a b y +
        (1 / 2 : ℝ) * (tensorChartComponentOnModel (I := I) (M := M) g S α ![a, b] y +
          tensorChartComponentOnModel (I := I) (M := M) g S α ![b, a] y) := by
  classical
  have hy_t : y ∈ (extChartAt I α).target := interior_subset hy
  have hp_src : (extChartAt I α).symm y ∈ (chartAt H α).source := by
    have := (extChartAt I α).map_target hy_t
    rwa [extChartAt_source] at this
  rw [Integral.DivergenceTheorem.chartGramOnE_def, Integral.DivergenceTheorem.chartGramOnE_def,
    chartGramMatrix_apply, chartGramMatrix_apply, tensorSectionRealizeMetric_inner]
  have hhalf := ccTensorBilinSymm_eq_half_rawComponent (I := I) (M := M) g S α a b hp_src
  rw [hhalf]
  rfl

end FiniteOrderEigenSeries

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
