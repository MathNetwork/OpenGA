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
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.SpectralEigenSeriesJointGramRawComponentJetBound


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

def eigenChartIncrementMode
    (g : SmoothRiemannianMetric I M)
    (φ : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ)
    (α : M) (i' j' : Fin (Module.finrank ℝ E))
    (i : TensorEigenIdx (I := I) (M := M) g 0 2) : ℝ × E → ℝ :=
  fun q : ℝ × E =>
    φ i q.1 *
      ccTensorBilinSymm (I := I) g
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorSmooth
          (I := I) (M := M) g 0 2 i)
        ((extChartAt I α).symm q.2)
        (chartBasisVecFiber (I := I) α i' ((extChartAt I α).symm q.2))
        (chartBasisVecFiber (I := I) α j' ((extChartAt I α).symm q.2))

omit [BoundarylessManifold I M] in
theorem eigenChartIncrementMode_contDiffOn
    (g : SmoothRiemannianMetric I M) {T : ℝ}
    (φ : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ ∞ (φ i))
    (α : M) (i' j' : Fin (Module.finrank ℝ E))
    (i : TensorEigenIdx (I := I) (M := M) g 0 2) :
    ContDiffOn ℝ ∞ (eigenChartIncrementMode (I := I) (M := M) g φ α i' j' i)
      (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target) := by
  set S := DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorSmooth
    (I := I) (M := M) g 0 2 i with hS_def

  have hB : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
        b (ccTensorBilinSymm (I := I) g S b))
      (trivializationAt E (TangentSpace I) α).baseSet :=
    (MetricRealization.ccTensorBilinSymm_contMDiff (I := I) g S).contMDiffOn
  have hv := chartBasisVec_contMDiffOn (I := I) α i'
  have hw := chartBasisVec_contMDiffOn (I := I) α j'
  have happ :
      ContMDiffOn I (I.prod 𝓘(ℝ, ℝ)) ∞
        (fun m : M => (⟨m,
            ccTensorBilinSymm (I := I) g S m
              (chartBasisVecFiber (I := I) α i' m)
              (chartBasisVecFiber (I := I) α j' m)⟩ :
              TotalSpace ℝ (Bundle.Trivial M ℝ)))
        (trivializationAt E (TangentSpace I) α).baseSet :=
    ContMDiffOn.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ) (b := id) hB hv hw
  have hScal : ContMDiffOn I 𝓘(ℝ) ∞
      (fun m : M => ccTensorBilinSymm (I := I) g S m
        (chartBasisVecFiber (I := I) α i' m)
        (chartBasisVecFiber (I := I) α j' m))
      (trivializationAt E (TangentSpace I) α).baseSet := by
    intro x hx
    have hpx := happ x hx
    rw [Bundle.contMDiffWithinAt_totalSpace] at hpx
    exact hpx.2

  rw [Integral.Measure.trivializationAt_baseSet_eq_chartAt_source (I := I)] at hScal
  have hsource_eq : (chartAt H α).source = (extChartAt I α).source := by
    rw [extChartAt_source (I := I)]
  rw [hsource_eq] at hScal
  have hmapsTo : Set.MapsTo (extChartAt I α).symm (interior (extChartAt I α).target)
      (extChartAt I α).source := by
    intro y hy
    have hy' : y ∈ (extChartAt I α).target := interior_subset hy
    exact (extChartAt I α).map_target hy'
  have hsymm_cmdiff : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I α).symm
      (interior (extChartAt I α).target) :=
    (contMDiffOn_extChartAt_symm (I := I) (n := ∞) α).mono interior_subset
  have hcomp : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞
      (fun y : E => ccTensorBilinSymm (I := I) g S ((extChartAt I α).symm y)
        (chartBasisVecFiber (I := I) α i' ((extChartAt I α).symm y))
        (chartBasisVecFiber (I := I) α j' ((extChartAt I α).symm y)))
      (interior (extChartAt I α).target) :=
    hScal.comp hsymm_cmdiff hmapsTo
  have hSpace : ContDiffOn ℝ ∞
      (fun y : E => ccTensorBilinSymm (I := I) g S ((extChartAt I α).symm y)
        (chartBasisVecFiber (I := I) α i' ((extChartAt I α).symm y))
        (chartBasisVecFiber (I := I) α j' ((extChartAt I α).symm y)))
      (interior (extChartAt I α).target) :=
    hcomp.contDiffOn

  have htime : ContDiffOn ℝ ∞ (fun q : ℝ × E => φ i q.1)
      (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target) :=
    ((hφ_smooth i).contDiffOn).comp contDiffOn_fst (Set.mapsTo_fst_prod)
  have hspaceComp : ContDiffOn ℝ ∞
      (fun q : ℝ × E => ccTensorBilinSymm (I := I) g S ((extChartAt I α).symm q.2)
        (chartBasisVecFiber (I := I) α i' ((extChartAt I α).symm q.2))
        (chartBasisVecFiber (I := I) α j' ((extChartAt I α).symm q.2)))
      (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target) :=
    hSpace.comp contDiffOn_snd (Set.mapsTo_snd_prod)
  exact htime.mul hspaceComp

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (eigenvectorSmooth tensorChartComponentRaw) in

private def eigenSpatialFactor
    (g : SmoothRiemannianMetric I M) (α : M) (i' j' : Fin (Module.finrank ℝ E))
    (i : TensorEigenIdx (I := I) (M := M) g 0 2) : E → ℝ :=
  fun y : E =>
    ccTensorBilinSymm (I := I) g
      (eigenvectorSmooth (I := I) (M := M) g 0 2 i)
      ((extChartAt I α).symm y)
      (chartBasisVecFiber (I := I) α i' ((extChartAt I α).symm y))
      (chartBasisVecFiber (I := I) α j' ((extChartAt I α).symm y))

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (eigenvectorSmooth tensorChartComponentRaw) in
omit [BoundarylessManifold I M] in
private lemma eigenSpatialFactor_eqOn
    (g : SmoothRiemannianMetric I M) (α : M) (i' j' : Fin (Module.finrank ℝ E))
    (i : TensorEigenIdx (I := I) (M := M) g 0 2) :
    Set.EqOn (eigenSpatialFactor (I := I) (M := M) g α i' j' i)
      (fun y : E => (1 / 2 : ℝ) *
        (tensorChartComponentOnModel (I := I) (M := M) g (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α ![i', j'] y +
          tensorChartComponentOnModel (I := I) (M := M) g (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α ![j', i'] y))
      (interior (extChartAt I α).target) := by
  intro y hy
  have hsrc : (extChartAt I α).symm y ∈ (chartAt H α).source := by
    have hyt : y ∈ (extChartAt I α).target := interior_subset hy
    have := (extChartAt I α).map_target hyt
    rwa [extChartAt_source (I := I)] at this
  rw [eigenSpatialFactor,
    ccTensorBilinSymm_eq_half_rawComponent (I := I) (M := M) g
      (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α i' j' hsrc]
  rfl

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (eigenvectorSmooth tensorChartComponentRaw) in
omit [BoundarylessManifold I M] in
private lemma eigenSpatialFactor_contDiffOn
    (g : SmoothRiemannianMetric I M) (α : M) (i' j' : Fin (Module.finrank ℝ E))
    (i : TensorEigenIdx (I := I) (M := M) g 0 2) :
    ContDiffOn ℝ ∞ (eigenSpatialFactor (I := I) (M := M) g α i' j' i)
      (interior (extChartAt I α).target) := by
  refine ContDiffOn.congr ?_ (eigenSpatialFactor_eqOn (I := I) (M := M) g α i' j' i)
  have hadd : ContDiffOn ℝ ∞
      (fun y : E => tensorChartComponentOnModel (I := I) (M := M) g (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α ![i', j'] y +
          tensorChartComponentOnModel (I := I) (M := M) g (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α ![j', i'] y)
      (interior (extChartAt I α).target) :=
    (rawCompOnE_contDiffOn (I := I) (M := M) g (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α ![i', j']).add
      (rawCompOnE_contDiffOn (I := I) (M := M) g (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α ![j', i'])
  exact contDiffOn_const.mul hadd

set_option maxHeartbeats 1600000 in
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (eigenvectorSmooth tensorChartComponentRaw) in
private lemma exists_eigenSpatialFactor_jet_le_lambda_pow
    (g : SmoothRiemannianMetric I M) (α : M) (i' j' : Fin (Module.finrank ℝ E)) (m : ℕ)
    {B : Set E} (hB_compact : IsCompact B) (hB : B ⊆ interior (extChartAt I α).target) :
    ∃ (C : ℝ) (p : ℕ), 0 ≤ C ∧
      ∀ (m' : ℕ), m' ≤ m → ∀ (i : TensorEigenIdx (I := I) (M := M) g 0 2), ∀ y ∈ B,
        ‖iteratedFDerivWithin ℝ m' (eigenSpatialFactor (I := I) (M := M) g α i' j' i)
            (interior (extChartAt I α).target) y‖ ≤
          C * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ p := by
  classical
  set O : Set E := interior (extChartAt I α).target with hO_def
  have hUDO : UniqueDiffOn ℝ O := isOpen_interior.uniqueDiffOn

  set kE : ℕ := Module.finrank ℝ E + 2 * m + 1 with hkE_def

  have hper : ∀ m' : ℕ, m' ≤ m → ∃ Cm' : ℝ, 0 ≤ Cm' ∧
      ∀ (i : TensorEigenIdx (I := I) (M := M) g 0 2), ∀ y ∈ B,
        ‖iteratedFDerivWithin ℝ m' (eigenSpatialFactor (I := I) (M := M) g α i' j' i) O y‖ ≤
          Cm' * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * kE) := by
   intro m' hm'
   have h_super : 2 * kE > Module.finrank ℝ E + 2 * m' := by rw [hkE_def]; omega
   obtain ⟨Cab, hCab_nn, hCab⟩ :=
     exists_rawCompOnE_jet_le_toHs_on_compact (I := I) (M := M) g α ![i', j'] m' kE h_super hB_compact hB
   obtain ⟨Cba, hCba_nn, hCba⟩ :=
     exists_rawCompOnE_jet_le_toHs_on_compact (I := I) (M := M) g α ![j', i'] m' kE h_super hB_compact hB
   obtain ⟨Cdec, hCdec_nn, hCdec⟩ :=
     eigenvectorSmooth_toHs_norm_le_lambda_pow (I := I) (M := M) g kE
   refine ⟨(1 / 2 : ℝ) * (Cab + Cba) * Cdec, by positivity, fun i y hy => ?_⟩
   set S := eigenvectorSmooth (I := I) (M := M) g 0 2 i with hS_def

   have hcongr : iteratedFDerivWithin ℝ m' (eigenSpatialFactor (I := I) (M := M) g α i' j' i) O y =
       iteratedFDerivWithin ℝ m'
         ((1 / 2 : ℝ) • (tensorChartComponentOnModel (I := I) (M := M) g S α ![i', j'] +
           tensorChartComponentOnModel (I := I) (M := M) g S α ![j', i'])) O y := by
     refine iteratedFDerivWithin_congr ?_ (hB hy) m'
     intro z hz
     rw [eigenSpatialFactor_eqOn (I := I) (M := M) g α i' j' i hz]
     simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, hS_def]
   rw [hcongr]
   have hcd_ab : ContDiffWithinAt ℝ (m' : ℕ∞) (tensorChartComponentOnModel (I := I) (M := M) g S α ![i', j']) O y :=
     ((rawCompOnE_contDiffOn (I := I) (M := M) g S α ![i', j']).contDiffWithinAt (hB hy)).of_le
       (by exact_mod_cast le_top)
   have hcd_ba : ContDiffWithinAt ℝ (m' : ℕ∞) (tensorChartComponentOnModel (I := I) (M := M) g S α ![j', i']) O y :=
     ((rawCompOnE_contDiffOn (I := I) (M := M) g S α ![j', i']).contDiffWithinAt (hB hy)).of_le
       (by exact_mod_cast le_top)
   rw [iteratedFDerivWithin_const_smul_apply (f := tensorChartComponentOnModel (I := I) (M := M) g S α ![i', j'] +
         tensorChartComponentOnModel (I := I) (M := M) g S α ![j', i']) (hcd_ab.add hcd_ba) hUDO (hB hy),
     iteratedFDerivWithin_add_apply hcd_ab hcd_ba hUDO (hB hy)]
   refine le_trans (norm_smul_le (1 / 2 : ℝ)
     (iteratedFDerivWithin ℝ m' (tensorChartComponentOnModel (I := I) (M := M) g S α ![i', j']) O y +
       iteratedFDerivWithin ℝ m' (tensorChartComponentOnModel (I := I) (M := M) g S α ![j', i']) O y)) ?_
   have htri : ‖iteratedFDerivWithin ℝ m' (tensorChartComponentOnModel (I := I) (M := M) g S α ![i', j']) O y +
         iteratedFDerivWithin ℝ m' (tensorChartComponentOnModel (I := I) (M := M) g S α ![j', i']) O y‖ ≤
       Cab * ‖SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) (2 * kE) S‖ +
         Cba * ‖SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) (2 * kE) S‖ :=
     le_trans (norm_add_le _ _) (add_le_add (hCab S y hy) (hCba S y hy))
   set N : ℝ := ‖SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) (2 * kE) S‖ with hN_def
   have hN_nn : 0 ≤ N := norm_nonneg _
   have hdec : N ≤ Cdec * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * kE) := hCdec i
   have hbase_nn : (0 : ℝ) ≤ (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * kE) :=
     pow_nonneg (by have := tensor_lambda_nonneg (I := I) (M := M) i; linarith) _
   calc ‖(1 / 2 : ℝ)‖ * ‖iteratedFDerivWithin ℝ m' (tensorChartComponentOnModel (I := I) (M := M) g S α ![i', j']) O y +
           iteratedFDerivWithin ℝ m' (tensorChartComponentOnModel (I := I) (M := M) g S α ![j', i']) O y‖
       ≤ ‖(1 / 2 : ℝ)‖ * ((Cab + Cba) * N) := by
         refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
         calc ‖iteratedFDerivWithin ℝ m' (tensorChartComponentOnModel (I := I) (M := M) g S α ![i', j']) O y +
               iteratedFDerivWithin ℝ m' (tensorChartComponentOnModel (I := I) (M := M) g S α ![j', i']) O y‖
             ≤ Cab * N + Cba * N := htri
           _ = (Cab + Cba) * N := by ring
     _ ≤ ‖(1 / 2 : ℝ)‖ * ((Cab + Cba) * (Cdec * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * kE))) := by
         refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
         exact mul_le_mul_of_nonneg_left hdec (by positivity)
     _ = (1 / 2 : ℝ) * (Cab + Cba) * Cdec * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * kE) := by
         rw [Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]; ring
  choose Cf hCf_nn hCf using hper
  set Cmax : ℝ := (Finset.range (m + 1)).sup'
    (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero m))
    (fun b => if hb : b ≤ m then Cf b hb else 0) with hCmax_def
  have hCmax_ge : ∀ (m' : ℕ) (h : m' ≤ m), Cf m' h ≤ Cmax := by
    intro m' h
    rw [hCmax_def]
    refine le_trans (le_of_eq ?_) (Finset.le_sup' (fun b => if hb : b ≤ m then Cf b hb else 0)
      (Finset.mem_range.mpr (by omega : m' < m + 1)))
    rw [dif_pos h]
  refine ⟨Cmax, 2 * kE, ?_, fun m' hm' i y hy => ?_⟩
  · exact le_trans (hCf_nn 0 (Nat.zero_le m)) (hCmax_ge 0 (Nat.zero_le m))
  · refine le_trans (hCf m' hm' i y hy) ?_
    refine mul_le_mul_of_nonneg_right (hCmax_ge m' hm') ?_
    exact pow_nonneg (by have := tensor_lambda_nonneg (I := I) (M := M) i; linarith) _

set_option maxHeartbeats 1600000 in
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (eigenvectorSmooth tensorChartComponentRaw) in
theorem eigenChartIncrementMode_iteratedFDerivWithin_summable_majorant
    (g : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T)
    (φ : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ ∞ (φ i))
    (hmodemass : ∀ (k : ℕ) (σ : ℝ), 0 ≤ σ →
      ∃ Cmaj : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable Cmaj ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv k (φ i) t) ^ 2 ≤ Cmaj i)
    (α : M) (i' j' : Fin (Module.finrank ℝ E))
    {B : Set E} (hB_compact : IsCompact B) (hB_uniq : UniqueDiffOn ℝ B)
    (hB : B ⊆ interior (extChartAt I α).target) :
    ∀ k : ℕ, ∃ v : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable v ∧
      ∀ (i : TensorEigenIdx (I := I) (M := M) g 0 2) (q : ℝ × E),
        q ∈ Set.Icc (0 : ℝ) T ×ˢ B →
        ‖iteratedFDerivWithin ℝ k (eigenChartIncrementMode (I := I) (M := M) g φ α i' j' i)
            (Set.Icc (0 : ℝ) T ×ˢ B) q‖ ≤ v i := by
  classical
  intro k
  set O : Set E := interior (extChartAt I α).target with hO_def
  set s : Set (ℝ × E) := Set.Icc (0 : ℝ) T ×ˢ B with hs_def
  have hUD : UniqueDiffOn ℝ s := (uniqueDiffOn_Icc hT).prod hB_uniq

  obtain ⟨Csp, pSp, hCsp_nn, hCsp⟩ :=
    exists_eigenSpatialFactor_jet_le_lambda_pow (I := I) (M := M) g α i' j' k hB_compact hB

  set sW : ℕ := weylSobolevExp (E := E) + 1 with hsW_def
  set σ0 : ℝ := 2 * (pSp : ℝ) + 2 * (sW : ℝ) with hσ0_def
  have hσ0_nn : (0 : ℝ) ≤ σ0 := by rw [hσ0_def]; positivity

  have htime : ∀ a : ℕ, ∃ Cm : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable Cm ∧
      ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
        tensorSobolevWeight (I := I) (M := M) i σ0 * (iteratedDeriv a (φ i) t) ^ 2 ≤ Cm i :=
    fun a => hmodemass a σ0 hσ0_nn
  choose Cmf hCmf_summable hCmf using htime

  have hweyl : Summable (fun i : TensorEigenIdx (I := I) (M := M) g 0 2 =>
      tensorSobolevWeight (I := I) (M := M) i (-(2 * (sW : ℝ)))) := by
    refine tensorEigen_summable_negpow (I := I) (M := M) g (2 * (sW : ℝ)) ?_
    rw [hsW_def]; push_cast; have := weylSobolevExp_gt_finrank (E := E); push_cast at this ⊢
    have h0 : (0:ℝ) ≤ (weylSobolevExp (E := E) : ℝ) := by positivity
    nlinarith [h0]

  have hbase_pos : ∀ i : TensorEigenIdx (I := I) (M := M) g 0 2,
      (0 : ℝ) < 1 + TensorEigenIdx.lambda (I := I) (M := M) i := fun i => by
    have := tensor_lambda_nonneg (I := I) (M := M) i; linarith
  have htime_pt : ∀ (j : ℕ) (i : TensorEigenIdx (I := I) (M := M) g 0 2) (t : ℝ),
      t ∈ Set.Icc (0 : ℝ) T →
      |iteratedDeriv j (φ i) t| ≤
        Real.sqrt (Cmf j i) * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (-(((pSp : ℝ)) + (sW : ℝ))) := by
    intro j i t ht
    have hmm := hCmf j i t ht

    have hw : tensorSobolevWeight (I := I) (M := M) i σ0 =
        ((1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (((pSp : ℝ)) + (sW : ℝ))) ^ 2 := by
      unfold tensorSobolevWeight
      rw [hσ0_def, show 2 * (pSp : ℝ) + 2 * (sW : ℝ) = ((pSp : ℝ) + (sW : ℝ)) * 2 by ring,
        Real.rpow_mul (hbase_pos i).le, Real.rpow_two]
    rw [hw] at hmm
    set W : ℝ := (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (((pSp : ℝ)) + (sW : ℝ)) with hW_def
    have hW_pos : 0 < W := Real.rpow_pos_of_pos (hbase_pos i) _

    have hCm_nn : 0 ≤ Cmf j i := le_trans (by positivity) hmm
    have habs : |iteratedDeriv j (φ i) t| ≤ Real.sqrt (Cmf j i) / W := by
      rw [le_div_iff₀ hW_pos]
      have h2 : (|iteratedDeriv j (φ i) t| * W) ^ 2 ≤ (Real.sqrt (Cmf j i)) ^ 2 := by
        rw [Real.sq_sqrt hCm_nn, mul_pow, sq_abs]
        nlinarith [hmm, hW_pos.le]
      have hlhs_nn : 0 ≤ |iteratedDeriv j (φ i) t| * W := by positivity
      nlinarith [Real.sqrt_nonneg (Cmf j i), h2, hlhs_nn, sq_nonneg (|iteratedDeriv j (φ i) t| * W - Real.sqrt (Cmf j i))]
    rw [Real.rpow_neg (hbase_pos i).le]
    rw [div_eq_mul_inv] at habs
    rwa [← hW_def]

  set Kconst : ℝ := (2 : ℝ) ^ k * (k.factorial : ℝ) * (k.factorial : ℝ) *
    (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) ^ k * (‖ContinuousLinearMap.snd ℝ ℝ E‖ + 1) ^ k *
    Csp with hKconst_def
  have hKconst_nn : 0 ≤ Kconst := by rw [hKconst_def]; positivity
  set wfun : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ :=
    fun i => tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ)) with hwfun_def
  have hwfun_nn : ∀ i, 0 ≤ wfun i := fun i => by
    rw [hwfun_def]; exact (tensorSobolevWeight_nonneg (I := I) (M := M) i _)
  have hwfun_sq : ∀ i, wfun i ^ 2 = tensorSobolevWeight (I := I) (M := M) i (-(2 * (sW : ℝ))) := by
    intro i
    rw [hwfun_def]
    unfold tensorSobolevWeight
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (hbase_pos i).le]
    congr 1; push_cast; ring
  have hCm_nn : ∀ (a : ℕ) (i : TensorEigenIdx (I := I) (M := M) g 0 2), 0 ≤ Cmf a i := by
    intro a i
    have h := hCmf a i 0 (Set.left_mem_Icc.mpr hT.le)
    have hw := tensorSobolevWeight_pos (I := I) (M := M) i σ0
    nlinarith [sq_nonneg (iteratedDeriv a (φ i) 0), hw.le, h]
  set termf : ℕ → TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ :=
    fun a i => Kconst * ((∑ j ∈ Finset.range (a + 1), Real.sqrt (Cmf j i)) * wfun i) with htermf_def
  have hw2_summable : Summable (fun i => wfun i ^ 2) := by simp_rw [hwfun_sq]; exact hweyl
  have hsqrt_summable : ∀ j, Summable (fun i => Real.sqrt (Cmf j i) * wfun i) := by
    intro j
    have hbound : ∀ i, Real.sqrt (Cmf j i) * wfun i ≤ (Cmf j i + wfun i ^ 2) / 2 := by
      intro i
      have h1 : Real.sqrt (Cmf j i) * wfun i ≤ (Real.sqrt (Cmf j i) ^ 2 + wfun i ^ 2) / 2 := by
        nlinarith [sq_nonneg (Real.sqrt (Cmf j i) - wfun i), Real.sq_sqrt (hCm_nn j i)]
      rwa [Real.sq_sqrt (hCm_nn j i)] at h1
    have hnn : ∀ i, 0 ≤ Real.sqrt (Cmf j i) * wfun i :=
      fun i => mul_nonneg (Real.sqrt_nonneg _) (hwfun_nn i)
    exact Summable.of_nonneg_of_le hnn hbound (((hCmf_summable j).add hw2_summable).div_const 2)
  have htermf_summable : ∀ a, Summable (termf a) := by
    intro a
    refine Summable.mul_left Kconst ?_
    have heq : (fun i => (∑ j ∈ Finset.range (a + 1), Real.sqrt (Cmf j i)) * wfun i) =
        (fun i => ∑ j ∈ Finset.range (a + 1), Real.sqrt (Cmf j i) * wfun i) := by
      funext i; rw [Finset.sum_mul]
    rw [heq]
    exact summable_sum (fun j _ => hsqrt_summable j)
  refine ⟨fun i => ∑ a ∈ Finset.range (k + 1), termf a i, ?_, ?_⟩
  · exact summable_sum (fun a _ => htermf_summable a)
  · intro i q hq
    have hqt : q.1 ∈ Set.Icc (0 : ℝ) T := hq.1
    have hqB : q.2 ∈ B := hq.2
    have hbase_nn : (0 : ℝ) ≤ 1 + TensorEigenIdx.lambda (I := I) (M := M) i := (hbase_pos i).le
    have hcd_fst : ContDiffOn ℝ ∞ (fun p : ℝ × E => φ i p.1) s :=
      ((hφ_smooth i).contDiffOn).comp contDiffOn_fst (Set.mapsTo_fst_prod)
    have hcd_snd : ContDiffOn ℝ ∞ (fun p : ℝ × E => eigenSpatialFactor (I := I) (M := M) g α i' j' i p.2) s := by
      refine (eigenSpatialFactor_contDiffOn (I := I) (M := M) g α i' j' i).comp contDiffOn_snd ?_
      intro p hp; exact hB hp.2
    have heqmode : eigenChartIncrementMode (I := I) (M := M) g φ α i' j' i =
        (fun p : ℝ × E => φ i p.1) * (fun p : ℝ × E => eigenSpatialFactor (I := I) (M := M) g α i' j' i p.2) := by
      funext p; rw [eigenChartIncrementMode]; rfl
    rw [heqmode]
    have hleib := norm_iteratedFDerivWithin_mul_le (𝕜 := ℝ) (f := fun p : ℝ × E => φ i p.1)
      (g := fun p : ℝ × E => eigenSpatialFactor (I := I) (M := M) g α i' j' i p.2)
      hcd_fst hcd_snd hUD (x := q) hq (n := k) (by exact_mod_cast le_top)
    refine le_trans hleib ?_
    change _ ≤ ∑ a ∈ Finset.range (k + 1), termf a i
    refine Finset.sum_le_sum (fun a ha => ?_)
    have hak : a ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)

    set Cφa : ℝ := (∑ j ∈ Finset.range (a + 1), Real.sqrt (Cmf j i)) *
      (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (-(((pSp : ℝ)) + (sW : ℝ))) with hCφa_def
    have hCφa_nn : 0 ≤ Cφa := by
      rw [hCφa_def]
      exact mul_nonneg (Finset.sum_nonneg (fun j _ => Real.sqrt_nonneg _))
        (Real.rpow_nonneg hbase_nn _)
    have hfst_bnd := norm_iteratedFDerivWithin_compFst_le (φ i) (hφ_smooth i) hUD hT a q hq Cφa
      (fun jj hjj => by
        rw [Real.norm_eq_abs]
        refine le_trans (htime_pt jj i q.1 hqt) ?_
        rw [hCφa_def]
        refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hbase_nn _)
        refine Finset.single_le_sum (f := fun j => Real.sqrt (Cmf j i))
          (fun j _ => Real.sqrt_nonneg _) (Finset.mem_range.mpr (by omega)))
    have hsnd_bnd := norm_iteratedFDerivWithin_compSnd_le
      (eigenSpatialFactor (I := I) (M := M) g α i' j' i) isOpen_interior
      (eigenSpatialFactor_contDiffOn (I := I) (M := M) g α i' j' i) hB hUD (k - a) q hq
      (Csp * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ pSp)
      (fun jj hjj => hCsp jj (by omega) i q.2 hqB)

    have hfn_nn : (0:ℝ) ≤ ‖iteratedFDerivWithin ℝ a (fun p : ℝ × E => φ i p.1) s q‖ := norm_nonneg _
    have hgn_nn : (0:ℝ) ≤ ‖iteratedFDerivWithin ℝ (k - a)
        (fun p : ℝ × E => eigenSpatialFactor (I := I) (M := M) g α i' j' i p.2) s q‖ := norm_nonneg _
    have hchoose_nn : (0:ℝ) ≤ (k.choose a : ℝ) := by positivity
    have hF1 := hfst_bnd
    have hG1 := hsnd_bnd

    have hsp_nn : 0 ≤ Csp * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ pSp :=
      mul_nonneg hCsp_nn (pow_nonneg hbase_nn _)
    have hprod : ‖iteratedFDerivWithin ℝ a (fun p : ℝ × E => φ i p.1) s q‖ *
          ‖iteratedFDerivWithin ℝ (k - a)
            (fun p : ℝ × E => eigenSpatialFactor (I := I) (M := M) g α i' j' i p.2) s q‖ ≤
        ((a.factorial : ℝ) * Cφa * (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) ^ a) *
          (((k - a).factorial : ℝ) * (Csp * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ pSp) *
            (‖ContinuousLinearMap.snd ℝ ℝ E‖ + 1) ^ (k - a)) := by
      refine mul_le_mul hF1 hG1 hgn_nn ?_
      positivity
    calc (k.choose a : ℝ) * ‖iteratedFDerivWithin ℝ a (fun p : ℝ × E => φ i p.1) s q‖ *
            ‖iteratedFDerivWithin ℝ (k - a)
              (fun p : ℝ × E => eigenSpatialFactor (I := I) (M := M) g α i' j' i p.2) s q‖
        = (k.choose a : ℝ) * (‖iteratedFDerivWithin ℝ a (fun p : ℝ × E => φ i p.1) s q‖ *
            ‖iteratedFDerivWithin ℝ (k - a)
              (fun p : ℝ × E => eigenSpatialFactor (I := I) (M := M) g α i' j' i p.2) s q‖) := by ring
      _ ≤ (k.choose a : ℝ) * (((a.factorial : ℝ) * Cφa * (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) ^ a) *
            (((k - a).factorial : ℝ) * (Csp * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ pSp) *
              (‖ContinuousLinearMap.snd ℝ ℝ E‖ + 1) ^ (k - a))) :=
          mul_le_mul_of_nonneg_left hprod hchoose_nn
      _ ≤ termf a i := by
          simp only [htermf_def, hCφa_def, hKconst_def, hwfun_def]

          have hcollapse : (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (-(((pSp : ℝ)) + (sW : ℝ))) *
              (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ pSp =
              tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ)) := by
            unfold tensorSobolevWeight
            rw [← Real.rpow_natCast (1 + TensorEigenIdx.lambda (I := I) (M := M) i) pSp,
              ← Real.rpow_add (hbase_pos i)]
            congr 1; ring
          set Ssqrt : ℝ := ∑ j ∈ Finset.range (a + 1), Real.sqrt (Cmf j i) with hSs_def
          have hSs_nn : 0 ≤ Ssqrt := Finset.sum_nonneg (fun j _ => Real.sqrt_nonneg _)
          have hbinom : (k.choose a : ℝ) ≤ (2 : ℝ) ^ k := by
            calc (k.choose a : ℝ) ≤ ((2 ^ k : ℕ) : ℝ) := by exact_mod_cast Nat.choose_le_two_pow k a
              _ = (2:ℝ) ^ k := by push_cast; ring
          have hfa : (a.factorial : ℝ) ≤ (k.factorial : ℝ) := by
            exact_mod_cast Nat.factorial_le hak
          have hfka : ((k-a).factorial : ℝ) ≤ (k.factorial : ℝ) := by
            exact_mod_cast Nat.factorial_le (by omega)
          have hfst_pow : (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) ^ a ≤
              (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) ^ k :=
            pow_le_pow_right₀ (by linarith [norm_nonneg (ContinuousLinearMap.fst ℝ ℝ E)]) hak
          have hsnd_pow : (‖ContinuousLinearMap.snd ℝ ℝ E‖ + 1) ^ (k - a) ≤
              (‖ContinuousLinearMap.snd ℝ ℝ E‖ + 1) ^ k :=
            pow_le_pow_right₀ (by linarith [norm_nonneg (ContinuousLinearMap.snd ℝ ℝ E)]) (by omega)

          have hlhs_eq : (k.choose a : ℝ) * (((a.factorial : ℝ) *
                (Ssqrt * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (-(((pSp : ℝ)) + (sW : ℝ)))) *
                (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) ^ a) *
              (((k - a).factorial : ℝ) * (Csp * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ pSp) *
                (‖ContinuousLinearMap.snd ℝ ℝ E‖ + 1) ^ (k - a))) =
              ((k.choose a : ℝ) * (a.factorial : ℝ) * ((k-a).factorial : ℝ) *
                (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) ^ a *
                (‖ContinuousLinearMap.snd ℝ ℝ E‖ + 1) ^ (k - a) * Csp) *
              (Ssqrt * ((1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (-(((pSp : ℝ)) + (sW : ℝ))) *
                (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ pSp)) := by ring
          rw [hlhs_eq, hcollapse]
          have hrhs_eq : (2 : ℝ) ^ k * (k.factorial : ℝ) * (k.factorial : ℝ) *
                (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) ^ k * (‖ContinuousLinearMap.snd ℝ ℝ E‖ + 1) ^ k * Csp *
              (Ssqrt * tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ))) =
              ((2 : ℝ) ^ k * (k.factorial : ℝ) * (k.factorial : ℝ) *
                (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) ^ k * (‖ContinuousLinearMap.snd ℝ ℝ E‖ + 1) ^ k * Csp) *
              (Ssqrt * tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ))) := by ring
          rw [hrhs_eq]
          refine mul_le_mul ?_ (le_refl _) ?_ (by positivity)
          · have hcoef_nn : (0:ℝ) ≤ (k.choose a : ℝ) * (a.factorial : ℝ) * ((k-a).factorial : ℝ) *
                (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) ^ a *
                (‖ContinuousLinearMap.snd ℝ ℝ E‖ + 1) ^ (k - a) * Csp := by positivity
            have hstep : (k.choose a : ℝ) * (a.factorial : ℝ) * ((k-a).factorial : ℝ) *
                (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) ^ a *
                (‖ContinuousLinearMap.snd ℝ ℝ E‖ + 1) ^ (k - a) * Csp ≤
                (2:ℝ) ^ k * (k.factorial : ℝ) * (k.factorial : ℝ) *
                (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) ^ k * (‖ContinuousLinearMap.snd ℝ ℝ E‖ + 1) ^ k * Csp := by
              have hfst_nn : (0:ℝ) ≤ (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) := by positivity
              have hsnd_nn : (0:ℝ) ≤ (‖ContinuousLinearMap.snd ℝ ℝ E‖ + 1) := by positivity
              gcongr
            exact hstep
          · exact mul_nonneg hSs_nn (tensorSobolevWeight_nonneg (I := I) (M := M) i _)

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
