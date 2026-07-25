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

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (eigenvectorSmooth tensorChartComponentRaw) in
omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma ccTensorBilinSymm_eq_half_rawComponent
    (g : SmoothRiemannianMetric I M) (S : SmoothCcTensor g 0 2)
    (α : M) (a b : Fin (Module.finrank ℝ E)) {p : M}
    (hp : p ∈ (chartAt H α).source) :
    ccTensorBilinSymm (I := I) g S p
        (chartBasisVecFiber (I := I) α a p) (chartBasisVecFiber (I := I) α b p) =
      (1 / 2 : ℝ) *
        (tensorChartComponentRaw (I := I) (M := M) g 0 2 S α ![] ![a, b] p +
          tensorChartComponentRaw (I := I) (M := M) g 0 2 S α ![] ![b, a] p) := by
  classical
  rw [ccTensorBilinSymm_apply]
  have hrawAB := tensorChartComponentRaw_eq_chartFrame (I := I) (M := M) g 0 2
    S α hp (![] : Fin 0 → Fin (Module.finrank ℝ E))
    (![a, b] : Fin 2 → Fin (Module.finrank ℝ E))
  have hrawBA := tensorChartComponentRaw_eq_chartFrame (I := I) (M := M) g 0 2
    S α hp (![] : Fin 0 → Fin (Module.finrank ℝ E))
    (![b, a] : Fin 2 → Fin (Module.finrank ℝ E))
  have hframe : chartFrameBasisModel (I := I) (M := M) α p 0
      (![] : Fin 0 → Fin (Module.finrank ℝ E)) =
      (ContinuousMultilinearMap.constOfIsEmpty ℝ
        (fun _ : Fin 0 => TangentSpace I p) (1 : ℝ)) := by
    apply ContinuousMultilinearMap.ext
    intro v
    have h := chartFrameBasisModel_apply (I := I) (M := M) α p 0
      (![] : Fin 0 → Fin (Module.finrank ℝ E)) v
    rw [Fin.prod_univ_zero] at h
    rw [ContinuousMultilinearMap.constOfIsEmpty_apply]
    exact h
  rw [hframe] at hrawAB hrawBA
  have hbilin : ∀ (i j : Fin (Module.finrank ℝ E)),
      (S.toSection p
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I p) (1 : ℝ)) :
        ContinuousMultilinearMap ℝ (fun _ : Fin 2 => TangentSpace I p) ℝ)
          (fun k : Fin 2 =>
            chartBasisVecFiber (I := I) α ((![i, j] : Fin 2 → _) k) p) =
        smoothCcTensorBilinForm (I := I) g S p
            (chartBasisVecFiber (I := I) α i p) (chartBasisVecFiber (I := I) α j p) := by
    intro i j
    have hvecAB : (fun k : Fin 2 =>
        chartBasisVecFiber (I := I) α ((![i, j] : Fin 2 → _) k) p) =
        ![chartBasisVecFiber (I := I) α i p, chartBasisVecFiber (I := I) α j p] := by
      funext k; fin_cases k <;> rfl
    rw [hvecAB, ccTensorBilin_apply]
    rfl
  rw [hrawAB, hrawBA, hbilin a b, hbilin b a]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma norm_iteratedFDerivWithin_rawCompOnE_le_rawPullR
    (g : SmoothRiemannianMetric I M) (S : SmoothCcTensor g 0 2) (α : M)
    (Jdx : Fin 2 → Fin (Module.finrank ℝ E)) (m : ℕ) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    ‖iteratedFDerivWithin ℝ m (tensorChartComponentOnModel (I := I) (M := M) g S α Jdx)
        (interior (extChartAt I α).target) y‖ ≤
      ‖(toEuclidean (E := E) : E →L[ℝ] EuclN)‖ ^ m *
        ‖iteratedFDeriv ℝ m (tensorComponentEuclideanChart (I := I) (M := M) g 0 2 S α
          (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx)
          (toEuclidean (E := E) y)‖ := by
  classical
  set e : E ≃L[ℝ] EuclN := toEuclidean (E := E) with he_def
  set O : Set E := interior (extChartAt I α).target with hO_def
  have hO_open : IsOpen O := isOpen_interior
  have hcompose : tensorChartComponentOnModel (I := I) (M := M) g S α Jdx =
      (tensorComponentEuclideanChart (I := I) (M := M) g 0 2 S α (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx) ∘ ⇑e := by
    have h := rawPullR_eq_rawCompOnE_comp (I := I) (M := M) g S α Jdx
    funext z
    have := congrFun h (e z)
    simp only [Function.comp_apply, he_def] at this ⊢
    rw [this, ContinuousLinearEquiv.symm_apply_apply]
  rw [hcompose]
  set Oe : Set EuclN := e '' O with hOe_def
  have hOe_open : IsOpen Oe := e.isOpenMap O hO_open
  have hUDe : UniqueDiffOn ℝ Oe := hOe_open.uniqueDiffOn
  have hpre : (⇑e) ⁻¹' Oe = O := by rw [hOe_def, Set.preimage_image_eq _ e.injective]
  have hey : e y ∈ Oe := ⟨y, hy, rfl⟩
  have hOe_sub : Oe ⊆ DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α := by
    rw [hOe_def]
    rintro z ⟨x, hx, rfl⟩
    rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_eq_preimage_symm (I := I) (M := M)]
    simp only [Set.mem_preimage, he_def, ContinuousLinearEquiv.symm_apply_apply]
    exact interior_subset hx
  have hcr := e.iteratedFDerivWithin_comp_right
    (f := tensorComponentEuclideanChart (I := I) (M := M) g 0 2 S α (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx)
    hUDe (x := y) hey m
  rw [hpre] at hcr
  rw [hcr]
  rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) m hOe_open hey]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [mul_comm]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
omit [BoundarylessManifold I M] in
lemma exists_rawCompOnE_jet_le_toHs_on_compact
    (g : SmoothRiemannianMetric I M) (α : M)
    (Jdx : Fin 2 → Fin (Module.finrank ℝ E)) (m k : ℕ)
    (h_super : 2 * k > Module.finrank ℝ E + 2 * m)
    {B : Set E} (hB_compact : IsCompact B)
    (hB : B ⊆ interior (extChartAt I α).target) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g 0 2), ∀ y ∈ B,
        ‖iteratedFDerivWithin ℝ m (tensorChartComponentOnModel (I := I) (M := M) g S α Jdx)
            (interior (extChartAt I α).target) y‖ ≤
          C * ‖SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) (2 * k) S‖ := by
  classical
  set O : Set E := interior (extChartAt I α).target with hO_def
  set K : Set EuclN := (toEuclidean (E := E)) '' B with hK_def
  have hK_compact : IsCompact K := hB_compact.image (toEuclidean (E := E)).continuous
  have hK_sub : K ⊆ DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α := by
    rw [hK_def]
    rintro z ⟨x, hx, rfl⟩
    rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_eq_preimage_symm (I := I) (M := M)]
    simp only [Set.mem_preimage, ContinuousLinearEquiv.symm_apply_apply]
    exact interior_subset (hB hx)
  set KM : Set M := (extChartAt I α).symm '' B with hKM_def
  have hKM_compact : IsCompact KM :=
    hB_compact.image_of_continuousOn
      ((continuousOn_extChartAt_symm (I := I) α).mono
        (fun x hx => interior_subset (hB hx)))
  have hKM_sub : KM ⊆ (chartAt H α).source := by
    rw [hKM_def]
    rintro b ⟨x, hx, rfl⟩
    have hx' : x ∈ (extChartAt I α).target := interior_subset (hB hx)
    have := (extChartAt I α).map_target hx'
    rwa [extChartAt_source (I := I)] at this
  obtain ⟨Cpeel, hCpeel_nn, hpeel⟩ :=
    iteratedFDeriv_rawPullR_le_zeroContent_sum_on_compact (I := I) (M := M) g 0 2 α m
      hK_compact hK_sub m (le_refl m)
  have hz_per : ∀ i : ℕ, ∃ Cz : ℝ, 0 ≤ Cz ∧ ∀ (S : SmoothCcTensor g 0 2) {b : M}, b ∈ KM →
      tensorComponentAbsSum (I := I) (M := M) g 0 (2 + i)
          (iteratedCovGrad g 0 2 i S) α (toEuclidean (E := E) (extChartAt I α b)) ≤
        Cz * (letI : Bundle.RiemannianBundle (fun bb : M => Tensor0SBundle.TensorRSSpace 0 (2 + i) I bb) :=
              Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g 0 (2 + i)
          ‖(iteratedCovGrad g 0 2 i S).toSection b‖) := by
    intro i
    obtain ⟨Cz, hCz_nn, hCz⟩ :=
      exists_zeroContentR_le_fiberNorm_on_compact (I := I) (M := M) g 0 (2 + i) α
        hKM_compact hKM_sub
    exact ⟨Cz, hCz_nn, fun S b hb => hCz (iteratedCovGrad g 0 2 i S) hb⟩
  choose Czf hCzf_nn hCzf using hz_per
  set Czmax : ℝ := (Finset.range (m + 1)).sup' (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero m)) Czf with hCzmax_def
  have hCzmax_nn : 0 ≤ Czmax := by
    rw [hCzmax_def]
    exact le_trans (hCzf_nn 0) (Finset.le_sup' Czf (Finset.mem_range.mpr (Nat.succ_pos m)))
  have hCz_le : ∀ i ∈ Finset.range (m + 1), Czf i ≤ Czmax :=
    fun i hi => Finset.le_sup' Czf hi
  obtain ⟨Cemb, hCemb_pos, hCemb⟩ :=
    iteratedCovGrad_toSobolev_embedding_Cm_singleNorm (I := I) (M := M) g 0 2 k m h_super
  set Cnorm : ℝ := ‖(toEuclidean (E := E) : E →L[ℝ] EuclN)‖ ^ m with hCnorm_def
  have hCnorm_nn : 0 ≤ Cnorm := by rw [hCnorm_def]; positivity
  refine ⟨Cnorm * (Cpeel * (Czmax * Cemb)), by positivity, fun S y hy => ?_⟩
  set N : ℝ := ‖SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) (2 * k) S‖ with hN_def
  have hN_nn : 0 ≤ N := norm_nonneg _
  set b : M := (extChartAt I α).symm y with hb_def
  have hyt : y ∈ (extChartAt I α).target := interior_subset (hB hy)
  have hb_mem : b ∈ KM := ⟨y, hy, rfl⟩
  have hyB : toEuclidean (E := E) y ∈ K := ⟨y, hy, rfl⟩
  have hy_eq : extChartAt I α b = y := by rw [hb_def]; exact (extChartAt I α).right_inv hyt
  have hrev := norm_iteratedFDerivWithin_rawCompOnE_le_rawPullR (I := I) (M := M) g S α Jdx m (hB hy)
  refine le_trans hrev ?_
  have hpeel_y := hpeel S m (le_refl m) 0 (by omega) (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx
    (toEuclidean (E := E) y) hyB
  rw [iteratedCovGrad_zero] at hpeel_y
  have hsum_fiber : ∑ i ∈ Finset.range (m + 1),
        tensorComponentAbsSum (I := I) (M := M) g 0 (2 + (0 + i))
          (iteratedCovGrad g 0 2 (0 + i) S) α (toEuclidean (E := E) y) ≤
      Czmax * ∑ i ∈ Finset.range (m + 1),
        (letI : Bundle.RiemannianBundle (fun bb : M => Tensor0SBundle.TensorRSSpace 0 (2 + i) I bb) :=
              Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g 0 (2 + i)
        ‖(iteratedCovGrad g 0 2 i S).toSection b‖) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun i hi => ?_)
    rw [Nat.zero_add]
    have hzi := hCzf i S hb_mem
    rw [hy_eq] at hzi
    refine le_trans hzi ?_
    letI : Bundle.RiemannianBundle (fun bb : M => Tensor0SBundle.TensorRSSpace 0 (2 + i) I bb) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g 0 (2 + i)
    exact mul_le_mul_of_nonneg_right (hCz_le i hi) (norm_nonneg _)
  have hemb := hCemb S b
  have hpeel_y' : ‖iteratedFDeriv ℝ m (tensorComponentEuclideanChart (I := I) (M := M) g 0 2 S α
        (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx) (toEuclidean (E := E) y)‖ ≤
      Cpeel * (Czmax * (Cemb * N)) := by
    refine le_trans hpeel_y ?_
    have hstep1 : Cpeel * ∑ i ∈ Finset.range (m + 1),
          tensorComponentAbsSum (I := I) (M := M) g 0 (2 + (0 + i))
            (iteratedCovGrad g 0 2 (0 + i) S) α (toEuclidean (E := E) y) ≤
        Cpeel * (Czmax * ∑ i ∈ Finset.range (m + 1),
          (letI : Bundle.RiemannianBundle (fun bb : M => Tensor0SBundle.TensorRSSpace 0 (2 + i) I bb) :=
              Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g 0 (2 + i)
          ‖(iteratedCovGrad g 0 2 i S).toSection b‖)) :=
      mul_le_mul_of_nonneg_left hsum_fiber hCpeel_nn
    refine le_trans hstep1 ?_
    have hfiber_le : ∑ i ∈ Finset.range (m + 1),
          (letI : Bundle.RiemannianBundle (fun bb : M => Tensor0SBundle.TensorRSSpace 0 (2 + i) I bb) :=
              Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g 0 (2 + i)
          ‖(iteratedCovGrad g 0 2 i S).toSection b‖) ≤ Cemb * N := hemb
    have hthis : Czmax * ∑ i ∈ Finset.range (m + 1),
          (letI : Bundle.RiemannianBundle (fun bb : M => Tensor0SBundle.TensorRSSpace 0 (2 + i) I bb) :=
              Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g 0 (2 + i)
          ‖(iteratedCovGrad g 0 2 i S).toSection b‖) ≤ Czmax * (Cemb * N) :=
      mul_le_mul_of_nonneg_left hfiber_le hCzmax_nn
    exact mul_le_mul_of_nonneg_left hthis hCpeel_nn
  calc Cnorm * ‖iteratedFDeriv ℝ m (tensorComponentEuclideanChart (I := I) (M := M) g 0 2 S α
          (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx) (toEuclidean (E := E) y)‖
      ≤ Cnorm * (Cpeel * (Czmax * (Cemb * N))) :=
        mul_le_mul_of_nonneg_left hpeel_y' hCnorm_nn
    _ = Cnorm * (Cpeel * (Czmax * Cemb)) * N := by ring

set_option maxHeartbeats 1600000 in
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (eigenvectorSmooth tensorChartComponentRaw) in
lemma exists_rawCompOnE_eigen_jet_le_lambda_pow
    (g : SmoothRiemannianMetric I M) (α : M)
    (Jdx : Fin 2 → Fin (Module.finrank ℝ E)) (m : ℕ)
    {B : Set E} (hB_compact : IsCompact B) (hB : B ⊆ interior (extChartAt I α).target) :
    ∃ (C : ℝ) (p : ℕ), 0 ≤ C ∧
      ∀ (m' : ℕ), m' ≤ m → ∀ (i : TensorEigenIdx (I := I) (M := M) g 0 2), ∀ y ∈ B,
        ‖iteratedFDerivWithin ℝ m' (tensorChartComponentOnModel (I := I) (M := M) g
            (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α Jdx)
            (interior (extChartAt I α).target) y‖ ≤
          C * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ p := by
  classical
  set kE : ℕ := Module.finrank ℝ E + 2 * m + 1 with hkE_def
  obtain ⟨Cdec, hCdec_nn, hCdec⟩ :=
    eigenvectorSmooth_toHs_norm_le_lambda_pow (I := I) (M := M) g kE
  have hper : ∀ m' : ℕ, m' ≤ m → ∃ Cm' : ℝ, 0 ≤ Cm' ∧
      ∀ (i : TensorEigenIdx (I := I) (M := M) g 0 2), ∀ y ∈ B,
        ‖iteratedFDerivWithin ℝ m' (tensorChartComponentOnModel (I := I) (M := M) g
            (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α Jdx)
            (interior (extChartAt I α).target) y‖ ≤
          Cm' * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * kE) := by
    intro m' hm'
    have h_super : 2 * kE > Module.finrank ℝ E + 2 * m' := by rw [hkE_def]; omega
    obtain ⟨Cj, hCj_nn, hCj⟩ :=
      exists_rawCompOnE_jet_le_toHs_on_compact (I := I) (M := M) g α Jdx m' kE h_super
        hB_compact hB
    refine ⟨Cj * Cdec, by positivity, fun i y hy => ?_⟩
    have h1 := hCj (eigenvectorSmooth (I := I) (M := M) g 0 2 i) y hy
    have h2 := hCdec i
    have hbase_nn : (0 : ℝ) ≤ (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * kE) := by
      have := tensor_lambda_nonneg (I := I) (M := M) i; positivity
    calc ‖iteratedFDerivWithin ℝ m' (tensorChartComponentOnModel (I := I) (M := M) g
            (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α Jdx)
            (interior (extChartAt I α).target) y‖
        ≤ Cj * ‖SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) (2 * kE)
            (eigenvectorSmooth (I := I) (M := M) g 0 2 i)‖ := h1
      _ ≤ Cj * (Cdec * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * kE)) :=
          mul_le_mul_of_nonneg_left h2 hCj_nn
      _ = Cj * Cdec * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * kE) := by ring
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
    have := tensor_lambda_nonneg (I := I) (M := M) i; positivity

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
