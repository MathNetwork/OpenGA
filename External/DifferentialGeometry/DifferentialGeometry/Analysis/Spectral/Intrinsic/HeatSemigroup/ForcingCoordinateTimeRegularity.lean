import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.MaxRegInteriorTimeSmoothing
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.GalerkinLimitUniformMass
import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.Plancherel
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SobolevNonlinearityExistence
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.SolutionSpace
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.PointwiseSpectralCoordinate
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.SmallTimeSmoothness
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckQuasilinearExistence
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.SpectralPointwiseFlowDeriv
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.SpectralSmoothRepresentativeRealize
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.SeriesContinuous
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.DeTurckRemainderPathTimeJet
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.SmoothCoordinateJetPreservation
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.SpectralMassUniformSup
import DifferentialGeometry.Analysis.Calculus.SmoothExtension.BorelHalfLineParam
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.ForcingFiniteOrderTimeRegularity

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators NNReal
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem maxRegForcing_smoothTimeJetDriver_of_galerkinSpatialMass
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
    (hspatial : ∀ σ : ℝ, ∃ Cσ : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T,
      Summable (fun i => tensorSobolevWeight (I := I) (M := M) i σ *
          (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u) t) ^ 2) ∧
        ∑' i, tensorSobolevWeight (I := I) (M := M) i σ *
            (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
              (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u) t) ^ 2 ≤ Cσ) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ T ∧
      ∃ f : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ,
      (∀ i, ContDiff ℝ ∞ (f i)) ∧
      (∀ (j : ℕ) (τ : ℝ), 0 ≤ τ →
        ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
          ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) d₀,
            tensorSobolevWeight (I := I) (M := M) i τ *
                (iteratedDeriv j (f i) t) ^ 2 ≤ B i) ∧
      (∀ i, (fun t => (gforce t).coeff i)
          =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₀)] f i) := by
  classical
  obtain ⟨d, hd_pos, hd_le, hk⟩ :=
    deTurckForcing_finiteOrderSmoothDriver (I := I) (M := M)
      g₀ g_bg a ha_super hT hT1 gforce hforce hspatial
  choose F hF_smooth hF_mass hF_ae using hk
  set f0 : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ := F 0 with hf0_def
  have hsub_clo : Set.Icc (0 : ℝ) d ⊆ closure (interior (Set.Icc (0 : ℝ) d)) := by
    rw [interior_Icc, closure_Ioo (ne_of_lt hd_pos)]
  have hEqOn : ∀ (k : ℕ) (i), Set.EqOn (F k i) (f0 i) (Set.Icc (0 : ℝ) d) := by
    intro k i
    have hae : (F k i) =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d)] (f0 i) :=
      (hF_ae k i).symm.trans (hF_ae 0 i)
    exact MeasureTheory.Measure.eqOn_of_ae_eq hae
      ((hF_smooth k i).continuous).continuousOn ((hF_smooth 0 i).continuous).continuousOn hsub_clo
  have hf0_smoothOn : ∀ i, ContDiffOn ℝ ∞ (f0 i) (Set.Icc (0 : ℝ) d) := by
    intro i
    rw [contDiffOn_infty]
    intro n
    exact ((hF_smooth n i).contDiffOn).congr (fun x hx => (hEqOn n i hx).symm)
  have hext : ∀ i, ∃ ψi : ℝ → ℝ, ContDiff ℝ ∞ ψi ∧
      Set.EqOn (f0 i) ψi (Set.Icc (0 : ℝ) d) :=
    fun i => contDiffOn_Icc_scalar_globalExtend hd_pos (hf0_smoothOn i)
  choose ψ hψ_smooth hψ_eqOn using hext
  have hjetEq : ∀ (j : ℕ) (i) (t), t ∈ Set.Icc (0 : ℝ) d →
      iteratedDeriv j (ψ i) t = iteratedDerivWithin j (f0 i) (Set.Icc (0 : ℝ) d) t := by
    intro j i t ht
    rw [iteratedDerivWithin_congr (hψ_eqOn i) ht]
    exact (iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hd_pos)
      ((hψ_smooth i).contDiffAt.of_le (mod_cast le_top)) ht).symm
  refine ⟨d, hd_pos, hd_le, ψ, hψ_smooth, ?_, ?_⟩
  · intro j τ hτ
    obtain ⟨B, hB_sum, hB_le⟩ := hF_mass j j (le_refl j) τ hτ
    refine ⟨B, hB_sum, fun i t ht => ?_⟩
    have hval : iteratedDeriv j (ψ i) t = iteratedDeriv j (F j i) t := by
      rw [hjetEq j i t ht, iteratedDerivWithin_congr ((hEqOn j i).symm) ht]
      exact iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hd_pos)
        ((hF_smooth j i).contDiffAt) ht
    rw [hval]
    exact hB_le i t ht
  · intro i
    have hf0ψ : (f0 i) =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d)] (ψ i) := by
      filter_upwards [MeasureTheory.ae_restrict_mem
        (measurableSet_Icc (a := (0 : ℝ)) (b := d))] with t ht
      exact hψ_eqOn i ht
    exact (hF_ae 0 i).trans hf0ψ

section SymmSCoefficientBlockTransfer

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (ccTensor02Symm domDomCongrSection tensorResolventHilbertEigenbasisSigma
    tensorResolventHilbertEigenbasisSigma_apply eigenvectorSmooth_toL2)

private noncomputable def eigenBlockFinset (g₀ : SmoothRiemannianMetric I M)
    (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2) :
    Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2) :=
  Finset.univ.map ⟨Sigma.mk i.1, sigma_mk_injective⟩

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma mem_eigenBlockFinset (g₀ : SmoothRiemannianMetric I M)
    {i j : TensorEigenIdx (I := I) (M := M) g₀ 0 2} :
    j ∈ eigenBlockFinset (I := I) (M := M) g₀ i ↔ j.1 = i.1 := by
  constructor
  · intro hj
    obtain ⟨k, -, rfl⟩ := Finset.mem_map.mp hj
    rfl
  · intro hj
    obtain ⟨μ, kk⟩ := j
    have hμ : μ = i.1 := hj
    subst hμ
    exact Finset.mem_map.mpr ⟨kk, Finset.mem_univ kk, rfl⟩

private noncomputable def swapEigenCoeff (g₀ : SmoothRiemannianMetric I M)
    (i j : TensorEigenIdx (I := I) (M := M) g₀ 0 2) : ℝ :=
  tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g₀)
    (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
      (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
        (eigenSmooth (I := I) (M := M) g₀ i))) j

private lemma eigenbasis_eq_toL2_eigenSmooth_loc (g₀ : SmoothRiemannianMetric I M)
    (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2) :
    tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
        (hCompact (I := I) (M := M) g₀) i =
      SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (eigenSmooth (I := I) (M := M) g₀ i) := by
  rw [tensorResolventHilbertEigenbasisSigma_apply (I := I) (M := M)
    (hCompact (I := I) (M := M) g₀) i]
  exact (eigenvectorSmooth_toL2 (I := I) (M := M) g₀ 0 2 i).symm

private lemma tensorL2_eq_of_coeff_eq (g₀ : SmoothRiemannianMetric I M)
    {U V : TensorL2 0 2 g₀}
    (h : ∀ k, tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g₀) U k =
      tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g₀) V k) : U = V := by
  apply (tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
    (hCompact (I := I) (M := M) g₀)).repr.injective
  ext k
  exact h k

open scoped Classical in

private lemma tensorL2Coeff_sum_smul_basis (g₀ : SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
    (c : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ)
    (k : TensorEigenIdx (I := I) (M := M) g₀ 0 2) :
    tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g₀)
        (∑ j ∈ S, c j • tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
          (hCompact (I := I) (M := M) g₀) j) k =
      (if k ∈ S then c k else 0) := by
  classical
  rw [tensorL2Coeff_eq_inner, inner_sum]
  have h_term : ∀ j ∈ S,
      ⟪tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
          (hCompact (I := I) (M := M) g₀) k,
        c j • tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
          (hCompact (I := I) (M := M) g₀) j⟫_ℝ =
      (if k = j then c j else 0) := by
    intro j _
    rw [inner_smul_right]
    have horth := (tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
      (hCompact (I := I) (M := M) g₀)).orthonormal
    rw [orthonormal_iff_ite] at horth
    rw [horth k j]
    by_cases h : k = j <;> simp [h]
  rw [Finset.sum_congr rfl h_term]
  by_cases hkS : k ∈ S
  · rw [Finset.sum_eq_single k]
    · simp [hkS]
    · intro j _ hjk
      rw [if_neg (fun h => hjk h.symm)]
    · intro h
      exact absurd hkS h
  · rw [if_neg hkS, Finset.sum_eq_zero]
    intro j hj
    rw [if_neg (fun h => hkS (by rw [h]; exact hj))]

private lemma toL2_swap_eigenSmooth_eq_blockSum (g₀ : SmoothRiemannianMetric I M)
    (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2) :
    SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
          (eigenSmooth (I := I) (M := M) g₀ i)) =
      ∑ j ∈ eigenBlockFinset (I := I) (M := M) g₀ i,
        swapEigenCoeff (I := I) (M := M) g₀ i j •
          tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
            (hCompact (I := I) (M := M) g₀) j := by
  classical
  refine tensorL2_eq_of_coeff_eq (I := I) (M := M) g₀ (fun k => ?_)
  rw [tensorL2Coeff_sum_smul_basis (I := I) (M := M) g₀ _ _ k]
  by_cases hk : k ∈ eigenBlockFinset (I := I) (M := M) g₀ i
  · rw [if_pos hk]
    rfl
  · rw [if_neg hk]
    refine tensorL2Coeff_toL2_swap_eigenSmooth_eq_zero_of_fst_ne (I := I) (M := M) g₀ i k ?_
    exact fun h => hk ((mem_eigenBlockFinset (I := I) (M := M) g₀).mpr h.symm)

private lemma sum_sq_swapEigenCoeff_le_one (g₀ : SmoothRiemannianMetric I M)
    (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2) :
    ∑ j ∈ eigenBlockFinset (I := I) (M := M) g₀ i,
      (swapEigenCoeff (I := I) (M := M) g₀ i j) ^ 2 ≤ 1 := by
  classical
  set Y : TensorL2 0 2 g₀ := SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
    (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
      (eigenSmooth (I := I) (M := M) g₀ i)) with hY_def
  have horth := (tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
    (hCompact (I := I) (M := M) g₀)).orthonormal
  have hb := horth.sum_inner_products_le (𝕜 := ℝ)
    (s := eigenBlockFinset (I := I) (M := M) g₀ i) Y
  have hnorm : ‖Y‖ = 1 := by
    rw [hY_def]
    exact (orthonormal_toL2_swap_eigenSmooth (I := I) (M := M) g₀).1 i
  calc ∑ j ∈ eigenBlockFinset (I := I) (M := M) g₀ i,
        (swapEigenCoeff (I := I) (M := M) g₀ i j) ^ 2
      = ∑ j ∈ eigenBlockFinset (I := I) (M := M) g₀ i,
          ‖⟪tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
              (hCompact (I := I) (M := M) g₀) j, Y⟫_ℝ‖ ^ 2 := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [show swapEigenCoeff (I := I) (M := M) g₀ i j =
            tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g₀) Y j from rfl,
          tensorL2Coeff_eq_inner, Real.norm_eq_abs, sq_abs]
    _ ≤ ‖Y‖ ^ 2 := hb
    _ = 1 := by rw [hnorm, one_pow]

private lemma tensorL2Coeff_toL2_swap_eq_blockSum (g₀ : SmoothRiemannianMetric I M)
    (X : SmoothCcTensor g₀ 0 2)
    (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2) :
    tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g₀)
        (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) X)) i =
      ∑ j ∈ eigenBlockFinset (I := I) (M := M) g₀ i,
        swapEigenCoeff (I := I) (M := M) g₀ i j *
          tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g₀)
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) X) j := by
  classical
  rw [tensorL2Coeff_eq_inner, eigenbasis_eq_toL2_eigenSmooth_loc (I := I) (M := M) g₀ i,
    SmoothCcTensor.inner_toL2,
    ← inner_domDomCongrSection_swap (I := I) (M := M) g₀
      (eigenSmooth (I := I) (M := M) g₀ i) X,
    ← SmoothCcTensor.inner_toL2, toL2_swap_eigenSmooth_eq_blockSum (I := I) (M := M) g₀ i,
    sum_inner]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [real_inner_smul_left, ← tensorL2Coeff_eq_inner]

private lemma tensorL2Coeff_toL2_symmS_eq_blockSum (g₀ : SmoothRiemannianMetric I M)
    (X : SmoothCcTensor g₀ 0 2)
    (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2) :
    tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g₀)
        (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (ccTensor02Symm (I := I) (M := M) g₀ X)) i =
      (1 / 2 : ℝ) * (tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g₀)
          (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) X) i +
        ∑ j ∈ eigenBlockFinset (I := I) (M := M) g₀ i,
          swapEigenCoeff (I := I) (M := M) g₀ i j *
            tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g₀)
              (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) X) j) := by
  have htoL2 : SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
      (ccTensor02Symm (I := I) (M := M) g₀ X) =
      (1 / 2 : ℝ) • (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) X +
        SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) X)) := by
    simp only [ccTensor02Symm]
    rw [map_smul, map_add]
  rw [htoL2, tensorL2Coeff_smul, tensorL2Coeff_add,
    tensorL2Coeff_toL2_swap_eq_blockSum (I := I) (M := M) g₀ X i]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma tensorSobolevWeight_eq_of_block (g₀ : SmoothRiemannianMetric I M)
    {i j : TensorEigenIdx (I := I) (M := M) g₀ 0 2} (h : j.1 = i.1) (σ : ℝ) :
    tensorSobolevWeight (I := I) (M := M) j σ = tensorSobolevWeight (I := I) (M := M) i σ := by
  unfold tensorSobolevWeight
  have hlam : TensorEigenIdx.lambda (I := I) (M := M) j =
      TensorEigenIdx.lambda (I := I) (M := M) i := by
    unfold TensorEigenIdx.lambda
    rw [h]
  rw [hlam]

private noncomputable def symmCoeffPath (g₀ : SmoothRiemannianMetric I M)
    (φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ)
    (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2) (t : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (φ i t + ∑ j ∈ eigenBlockFinset (I := I) (M := M) g₀ i,
    swapEigenCoeff (I := I) (M := M) g₀ i j * φ j t)

private lemma symmCoeffPath_contDiff (g₀ : SmoothRiemannianMetric I M)
    {φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ} {n : WithTop ℕ∞}
    (hφ : ∀ i, ContDiff ℝ n (φ i)) (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2) :
    ContDiff ℝ n (symmCoeffPath (I := I) (M := M) g₀ φ i) := by
  unfold symmCoeffPath
  exact contDiff_const.mul ((hφ i).add
    (ContDiff.sum fun j _ => contDiff_const.mul (hφ j)))

private lemma symmCoeffPath_realizes (g₀ : SmoothRiemannianMetric I M)
    (φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ)
    (X : SmoothCcTensor g₀ 0 2) {t : ℝ}
    (hX : ∀ j, tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g₀)
      (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) X) j = φ j t)
    (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2) :
    tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g₀)
        (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (ccTensor02Symm (I := I) (M := M) g₀ X)) i =
      symmCoeffPath (I := I) (M := M) g₀ φ i t := by
  rw [tensorL2Coeff_toL2_symmS_eq_blockSum (I := I) (M := M) g₀ X i, hX i]
  unfold symmCoeffPath
  congr 2
  exact Finset.sum_congr rfl fun j _ => by rw [hX j]

private lemma iteratedDeriv_finsetSum_const_mul {ι' : Type*} (s : Finset ι')
    (c : ι' → ℝ) (f : ι' → ℝ → ℝ) (k : ℕ)
    (hf : ∀ j, ContDiff ℝ (k : ℕ) (f j)) (t : ℝ) :
    iteratedDeriv k (fun u => ∑ j ∈ s, c j * f j u) t =
      ∑ j ∈ s, c j * iteratedDeriv k (f j) t := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp only [Finset.sum_empty]; exact iteratedDeriv_fun_const_zero
  | cons b s hb ih =>
    have hfun : (fun u => ∑ j ∈ Finset.cons b s hb, c j * f j u) =
        fun u => c b * f b u + ∑ j ∈ s, c j * f j u := by
      funext u
      rw [Finset.sum_cons]
    rw [hfun, iteratedDeriv_fun_add ((contDiff_const.mul (hf b)).contDiffAt)
        ((ContDiff.sum fun j _ => contDiff_const.mul (hf j)).contDiffAt),
      Finset.sum_cons, ih]
    congr 1
    exact iteratedDeriv_const_mul_field (c b) (f b)

private lemma iteratedDeriv_symmCoeffPath (g₀ : SmoothRiemannianMetric I M)
    {φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ} (k : ℕ)
    (hφ : ∀ j, ContDiff ℝ (k : ℕ) (φ j))
    (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2) (t : ℝ) :
    iteratedDeriv k (symmCoeffPath (I := I) (M := M) g₀ φ i) t =
      (1 / 2 : ℝ) * (iteratedDeriv k (φ i) t +
        ∑ j ∈ eigenBlockFinset (I := I) (M := M) g₀ i,
          swapEigenCoeff (I := I) (M := M) g₀ i j * iteratedDeriv k (φ j) t) := by
  unfold symmCoeffPath
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_fun_add ((hφ i).contDiffAt)
    ((ContDiff.sum fun j _ => contDiff_const.mul (hφ j)).contDiffAt),
    iteratedDeriv_finsetSum_const_mul _ _ _ k hφ t]

private lemma symmCoeffPath_spectralMass (g₀ : SmoothRiemannianMetric I M)
    {d : ℝ} (hd_pos : 0 < d)
    {φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ} (k : ℕ)
    (hφ : ∀ j, ContDiff ℝ (k : ℕ) (φ j)) (τ : ℝ)
    (hmτ : ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
      ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) d,
        tensorSobolevWeight (I := I) (M := M) i τ * (iteratedDeriv k (φ i) t) ^ 2 ≤ B i)
    (hmτρ : ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
      ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) d,
        tensorSobolevWeight (I := I) (M := M) i
            (τ + (((weylSobolevExp (E := E) : ℕ) : ℝ) + 1)) *
          (iteratedDeriv k (φ i) t) ^ 2 ≤ B i) :
    ∃ B' : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B' ∧
      ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) d,
        tensorSobolevWeight (I := I) (M := M) i τ *
          (iteratedDeriv k (symmCoeffPath (I := I) (M := M) g₀ φ i) t) ^ 2 ≤ B' i := by
  classical
  obtain ⟨B₁, hB₁s, hB₁⟩ := hmτ
  obtain ⟨B₂, hB₂s, hB₂⟩ := hmτρ
  set ρ : ℝ := ((weylSobolevExp (E := E) : ℕ) : ℝ) + 1 with hρ_def
  have hρ_gt : ((weylSobolevExp (E := E) : ℕ) : ℝ) < ρ := by
    rw [hρ_def]; linarith
  have hB₂nn : ∀ j, 0 ≤ B₂ j := fun j =>
    le_trans (mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) j _) (sq_nonneg _))
      (hB₂ j 0 ⟨le_rfl, hd_pos.le⟩)
  set K : ℝ := ∑' j, B₂ j with hK_def
  refine ⟨fun i => (1 / 2 : ℝ) * B₁ i +
    (1 / 2 : ℝ) * (tensorSobolevWeight (I := I) (M := M) i (-ρ) * K), ?_, ?_⟩
  · exact (hB₁s.mul_left _).add
      (((tensorEigen_summable_negpow (I := I) (M := M) g₀ ρ hρ_gt).mul_right K).mul_left _)
  · intro i t ht
    rw [iteratedDeriv_symmCoeffPath (I := I) (M := M) g₀ k hφ i t]
    set x : ℝ := iteratedDeriv k (φ i) t with hx_def
    set y : ℝ := ∑ j ∈ eigenBlockFinset (I := I) (M := M) g₀ i,
      swapEigenCoeff (I := I) (M := M) g₀ i j * iteratedDeriv k (φ j) t with hy_def
    have hw_nn : 0 ≤ tensorSobolevWeight (I := I) (M := M) i τ :=
      tensorSobolevWeight_nonneg (I := I) (M := M) i τ
    have hsq : ((1 / 2 : ℝ) * (x + y)) ^ 2 ≤ (1 / 2) * x ^ 2 + (1 / 2) * y ^ 2 := by
      nlinarith [sq_nonneg (x - y)]
    have h1 : tensorSobolevWeight (I := I) (M := M) i τ * x ^ 2 ≤ B₁ i := hB₁ i t ht
    have h2 : tensorSobolevWeight (I := I) (M := M) i τ * y ^ 2 ≤
        tensorSobolevWeight (I := I) (M := M) i (-ρ) * K := by
      have hcs := Finset.sum_mul_sq_le_sq_mul_sq (eigenBlockFinset (I := I) (M := M) g₀ i)
        (fun j => swapEigenCoeff (I := I) (M := M) g₀ i j)
        (fun j => iteratedDeriv k (φ j) t)
      have hsum_nn : (0 : ℝ) ≤ ∑ j ∈ eigenBlockFinset (I := I) (M := M) g₀ i,
          (iteratedDeriv k (φ j) t) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
      have hy2 : y ^ 2 ≤ ∑ j ∈ eigenBlockFinset (I := I) (M := M) g₀ i,
          (iteratedDeriv k (φ j) t) ^ 2 :=
        le_trans hcs (mul_le_of_le_one_left hsum_nn
          (sum_sq_swapEigenCoeff_le_one (I := I) (M := M) g₀ i))

      have hstep : tensorSobolevWeight (I := I) (M := M) i τ *
          ∑ j ∈ eigenBlockFinset (I := I) (M := M) g₀ i, (iteratedDeriv k (φ j) t) ^ 2 =
          tensorSobolevWeight (I := I) (M := M) i (-ρ) *
            ∑ j ∈ eigenBlockFinset (I := I) (M := M) g₀ i,
              tensorSobolevWeight (I := I) (M := M) j (τ + ρ) *
                (iteratedDeriv k (φ j) t) ^ 2 := by
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j hj => ?_
        have hjw : tensorSobolevWeight (I := I) (M := M) j (τ + ρ) =
            tensorSobolevWeight (I := I) (M := M) i (τ + ρ) :=
          tensorSobolevWeight_eq_of_block (I := I) (M := M) g₀
            ((mem_eigenBlockFinset (I := I) (M := M) g₀).mp hj) (τ + ρ)
        have hsplit : tensorSobolevWeight (I := I) (M := M) i τ =
            tensorSobolevWeight (I := I) (M := M) i (-ρ) *
              tensorSobolevWeight (I := I) (M := M) i (τ + ρ) := by
          rw [← tensorHs.tensorSobolevWeight_add (I := I) (M := M) i (-ρ) (τ + ρ)]
          congr 1
          ring
        rw [hjw, hsplit]
        ring
      have hblock : ∑ j ∈ eigenBlockFinset (I := I) (M := M) g₀ i,
          tensorSobolevWeight (I := I) (M := M) j (τ + ρ) *
            (iteratedDeriv k (φ j) t) ^ 2 ≤ K := by
        refine le_trans (Finset.sum_le_sum fun j _ => hB₂ j t ht) ?_
        exact hB₂s.sum_le_tsum _ fun j _ => hB₂nn j
      calc tensorSobolevWeight (I := I) (M := M) i τ * y ^ 2
          ≤ tensorSobolevWeight (I := I) (M := M) i τ *
            ∑ j ∈ eigenBlockFinset (I := I) (M := M) g₀ i, (iteratedDeriv k (φ j) t) ^ 2 :=
            mul_le_mul_of_nonneg_left hy2 hw_nn
        _ = tensorSobolevWeight (I := I) (M := M) i (-ρ) *
            ∑ j ∈ eigenBlockFinset (I := I) (M := M) g₀ i,
              tensorSobolevWeight (I := I) (M := M) j (τ + ρ) *
                (iteratedDeriv k (φ j) t) ^ 2 := hstep
        _ ≤ tensorSobolevWeight (I := I) (M := M) i (-ρ) * K :=
            mul_le_mul_of_nonneg_left hblock
              (tensorSobolevWeight_nonneg (I := I) (M := M) i (-ρ))
    calc tensorSobolevWeight (I := I) (M := M) i τ * ((1 / 2 : ℝ) * (x + y)) ^ 2
        ≤ tensorSobolevWeight (I := I) (M := M) i τ *
          ((1 / 2) * x ^ 2 + (1 / 2) * y ^ 2) := mul_le_mul_of_nonneg_left hsq hw_nn
      _ = (1 / 2) * (tensorSobolevWeight (I := I) (M := M) i τ * x ^ 2) +
          (1 / 2) * (tensorSobolevWeight (I := I) (M := M) i τ * y ^ 2) := by ring
      _ ≤ (1 / 2 : ℝ) * B₁ i +
          (1 / 2 : ℝ) * (tensorSobolevWeight (I := I) (M := M) i (-ρ) * K) :=
          add_le_add (mul_le_mul_of_nonneg_left h1 (by norm_num))
            (mul_le_mul_of_nonneg_left h2 (by norm_num))

private theorem exists_smoothCcPath_realizing_coeff (g₀ : SmoothRiemannianMetric I M)
    {d₂ : ℝ}
    (φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ)
    (hmass0 : ∀ σ : ℝ, 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) d₂,
          tensorSobolevWeight (I := I) (M := M) i σ * (φ i t) ^ 2 ≤ B i) :
    ∃ F : ℝ → SmoothCcTensor g₀ 0 2, ∀ t ∈ Set.Icc (0 : ℝ) d₂, ∀ i,
      tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
          (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t)) i = φ i t := by
  classical
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2 with hhc
  have hsum_pt : ∀ t, t ∈ Set.Icc (0 : ℝ) d₂ →
      ∀ σ : ℝ, 0 ≤ σ →
        Summable (fun i => tensorSobolevWeight (I := I) (M := M) i σ * (φ i t) ^ 2) := by
    intro t ht σ hσ
    obtain ⟨B, hBs, hBle⟩ := hmass0 σ hσ
    refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => hBle i t ht) hBs
    exact mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i σ) (sq_nonneg _)
  set ct : ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ :=
    fun t i => φ i t with hct_def
  have hreconstruct : ∀ t ∈ Set.Icc (0 : ℝ) d₂,
      ∃ S : SmoothCcTensor g₀ 0 2, ∀ i,
        tensorL2Coeff (I := I) (M := M) hc
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) S) i = φ i t := by
    intro t ht
    obtain ⟨B0, hB0s, hB0le⟩ := hmass0 0 le_rfl
    set v0 : tensorHs (I := I) (M := M) g₀ 0 2 0 :=
      tensorHs_of_spectralMass_majorant (I := I) (M := M) (ct t) B0 hB0s
        (fun i => by
          have := hB0le i t ht
          simpa [hct_def] using this) with hv0_def
    set u : TensorL2 0 2 g₀ :=
      tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2) hc le_rfl v0 with hu_def
    have hu_coeff : ∀ i, tensorL2Coeff (I := I) (M := M) hc u i = φ i t := by
      intro i
      rw [hu_def, tensorHsToL2_tensorL2Coeff]
      simp only [hv0_def, tensorHs_of_spectralMass_majorant_coeff, hct_def]
    have hsum_u : ∀ σ : ℝ, 0 ≤ σ →
        Summable (fun i => tensorSobolevWeight (I := I) (M := M) i σ *
          (tensorL2Coeff (I := I) (M := M) hc u i) ^ 2) := by
      intro σ hσ
      refine (hsum_pt t ht σ hσ).congr (fun i => ?_)
      rw [hu_coeff i]
    have hmem : ∀ σ : ℝ, ∀ hσ : 0 ≤ σ,
        ∃ vσ : tensorHs (I := I) (M := M) g₀ 0 2 σ,
          tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2) hc hσ vσ = u :=
      allHs_of_weighted_summable_pub (I := I) (M := M) g₀ u hsum_u
    obtain ⟨S, hS⟩ := spectralSmoothRealizesAsSmooth_holds (I := I) (M := M) (g := g₀) u hmem
    refine ⟨S, fun i => ?_⟩
    have hSL2 : SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) S = u := by
      rw [show SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) S
          = (S : TensorL2 0 2 g₀) from rfl, hS]
    rw [hSL2, hu_coeff i]
  choose! S₀ hS₀ using hreconstruct
  exact ⟨S₀, hS₀⟩

private theorem deTurckSobolevNHa2Symm_embed_eq_raw_embed_symmS
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) (X : SmoothCcTensor g₀ 0 2)
    (hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) X‖ ≤
      (Classical.choose (deTurckSobolevNHa2_exists_of_super
        (I := I) (M := M) g₀ a ha_super)).1) :
    deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
        (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) X) =
      deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a
        (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
          (ccTensor02Symm (I := I) (M := M) g₀ X)) := by
  classical
  obtain ⟨hp_pos, hp_lt, hp_ball⟩ := Classical.choose_spec
    (deTurckSobolevNHa2_exists_of_super (I := I) (M := M) g₀ a ha_super)
  have hδ_lt : (Classical.choose (deTurckSobolevNHa2_exists_of_super
      (I := I) (M := M) g₀ a ha_super)).2 < 1 :=
    lt_of_le_of_lt hp_lt (deTurckArmContractionThreshold''_lt_one' (Module.finrank ℝ E))
  rw [deTurckSobolevNHa2Symm_eq_smoothN (I := I) (M := M) g₀ g_bg a ha_super X hδ_lt
    (fiberwiseOperatorNormBound_of_tensorSymmetrization (I := I) (M := M) g₀ X (hp_ball X hball)) hball]
  exact (deTurckSobolevNHa2_eq_smoothN (I := I) (M := M) g₀ g_bg a ha_super
    (ccTensor02Symm (I := I) (M := M) g₀ X) hδ_lt
    (fiberwiseOperatorNormBound_of_tensorSymmetrization (I := I) (M := M) g₀ X (hp_ball X hball))
    (le_trans (norm_smoothCcToTensorHs_symmS_le (I := I) (M := M) g₀ ((a : ℝ) + 2) X)
      hball)).symm


private theorem deTurckForcing_jetSpectralMass_preservingSymm
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (_hT : 0 < T) {d₂ : ℝ} (hd₂_pos : 0 < d₂) (_hd₂_le : d₂ ≤ T)
    (w : ℝ → tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
    (hw_ball : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)),
      ‖w t‖ ≤ deTurckRealizabilityRadius (I := I) (M := M) g₀ a ha_super)
    (φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ)
    (hφ : JetSpectralMassControl (I := I) (M := M) g₀ φ d₂)
    (hw : ∀ i, (fun t => (w t).coeff i)
        =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)] φ i) :
    ∃ ψ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ,
      JetSpectralMassControl (I := I) (M := M) g₀ ψ d₂ ∧
        ∀ i, (fun t => (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a (w t)).coeff i)
            =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)] ψ i := by
  classical
  haveI : Countable (TensorEigenIdx (I := I) (M := M) g₀ 0 2) :=
    countable_tensorEigenIdx (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
  obtain ⟨hφ_smooth, hφ_mass⟩ := hφ
  have hmass0 : ∀ σ : ℝ, 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) d₂,
          tensorSobolevWeight (I := I) (M := M) i σ * (φ i t) ^ 2 ≤ B i := by
    intro σ hσ
    obtain ⟨B, hBs, hBle⟩ := hφ_mass 0 σ hσ
    refine ⟨B, hBs, fun i t ht => ?_⟩
    have h := hBle i t ht
    rwa [iteratedDeriv_zero] at h
  obtain ⟨F, hF_coeff⟩ :=
    exists_smoothCcPath_realizing_coeff (I := I) (M := M) g₀ φ hmass0
  have hφ'_smooth : ∀ i, ContDiff ℝ ∞ (symmCoeffPath (I := I) (M := M) g₀ φ i) :=
    symmCoeffPath_contDiff (I := I) (M := M) g₀ hφ_smooth
  have hφ'_mass : ∀ (j : ℕ) (τ : ℝ), 0 ≤ τ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) d₂,
          tensorSobolevWeight (I := I) (M := M) i τ *
              (iteratedDeriv j (symmCoeffPath (I := I) (M := M) g₀ φ i) t) ^ 2 ≤ B i := by
    intro j τ hτ
    exact symmCoeffPath_spectralMass (I := I) (M := M) g₀ hd₂_pos j
      (fun j' => (hφ_smooth j').of_le (mod_cast le_top)) τ
      (hφ_mass j τ hτ)
      (hφ_mass j (τ + (((weylSobolevExp (E := E) : ℕ) : ℝ) + 1)) (by positivity))
  have hae_all : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)),
      ∀ j, (w t).coeff j = φ j t := (MeasureTheory.ae_all_iff).2 hw
  have hwF : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)),
      w t = smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F t) := by
    filter_upwards [hae_all, MeasureTheory.ae_restrict_mem
      (measurableSet_Icc (a := (0 : ℝ)) (b := d₂))] with t htall htmem
    refine tensorHs.ext (funext fun j => ?_)
    rw [htall j, smoothCcToTensorHs_coeff, hF_coeff t htmem j]
  have hw'_ball : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
          (ccTensor02Symm (I := I) (M := M) g₀ (F t))‖ ≤
        deTurckRealizabilityRadius (I := I) (M := M) g₀ a ha_super := by
    filter_upwards [hw_ball, hwF] with t hwball_t hwF_t
    refine le_trans (norm_smoothCcToTensorHs_symmS_le (I := I) (M := M) g₀ ((a : ℝ) + 2)
      (F t)) ?_
    rw [← hwF_t]
    exact hwball_t
  have hw'_ae : ∀ i, (fun t => (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
      (ccTensor02Symm (I := I) (M := M) g₀ (F t))).coeff i)
      =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)]
        symmCoeffPath (I := I) (M := M) g₀ φ i := by
    intro i
    filter_upwards [MeasureTheory.ae_restrict_mem
      (measurableSet_Icc (a := (0 : ℝ)) (b := d₂))] with t ht
    rw [smoothCcToTensorHs_coeff]
    exact symmCoeffPath_realizes (I := I) (M := M) g₀ φ (F t)
      (fun j => hF_coeff t ht j) i
  obtain ⟨ψ, hψ_ctrl, hψ_ae⟩ :=
    deTurckSobolevNHa2_jetSpectralMass_preserving (I := I) (M := M) g₀ g_bg a ha_super
      _hT hd₂_pos _hd₂_le
      (fun t => smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
        (ccTensor02Symm (I := I) (M := M) g₀ (F t)))
      hw'_ball (symmCoeffPath (I := I) (M := M) g₀ φ) ⟨hφ'_smooth, hφ'_mass⟩ hw'_ae
  refine ⟨ψ, hψ_ctrl, fun i => ?_⟩
  filter_upwards [hψ_ae i, hw_ball, hwF] with t hψt hwball_t hwF_t
  have hballF : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F t)‖ ≤
      (Classical.choose (deTurckSobolevNHa2_exists_of_super
        (I := I) (M := M) g₀ a ha_super)).1 := by
    rw [← hwF_t]
    exact hwball_t
  rw [hwF_t, deTurckSobolevNHa2Symm_embed_eq_raw_embed_symmS (I := I) (M := M)
    g₀ g_bg a ha_super (F t) hballF]
  exact hψt


private theorem deTurckSobolevNHa2Symm_finiteOrder_jetSpectralMass_preserving
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) {d₂ : ℝ} (hd₂_pos : 0 < d₂) (hd₂_le : d₂ ≤ T)
    (w : ℝ → tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
    (hw_ball : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)),
      ‖w t‖ ≤ deTurckRealizabilityRadius (I := I) (M := M) g₀ a ha_super)
    (k : ℕ)
    (φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ (k : ℕ) (φ i))
    (hφ_mass : ∀ (j : ℕ), j ≤ k → ∀ (τ : ℝ), 0 ≤ τ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) d₂,
          tensorSobolevWeight (I := I) (M := M) i τ *
              (iteratedDeriv j (φ i) t) ^ 2 ≤ B i)
    (hw : ∀ i, (fun t => (w t).coeff i)
        =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)] φ i) :
    ∃ ψ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ,
      (∀ i, ContDiff ℝ (k : ℕ) (ψ i)) ∧
      (∀ (j : ℕ), j ≤ k → ∀ (τ : ℝ), 0 ≤ τ →
        ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
          ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) d₂,
            tensorSobolevWeight (I := I) (M := M) i τ *
                (iteratedDeriv j (ψ i) t) ^ 2 ≤ B i) ∧
      (∀ i, (fun t => (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a (w t)).coeff i)
          =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)] ψ i) := by
  classical
  haveI : Countable (TensorEigenIdx (I := I) (M := M) g₀ 0 2) :=
    countable_tensorEigenIdx (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
  have hmass0 : ∀ σ : ℝ, 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) d₂,
          tensorSobolevWeight (I := I) (M := M) i σ * (φ i t) ^ 2 ≤ B i := by
    intro σ hσ
    obtain ⟨B, hBs, hBle⟩ := hφ_mass 0 (Nat.zero_le k) σ hσ
    refine ⟨B, hBs, fun i t ht => ?_⟩
    have h := hBle i t ht
    rwa [iteratedDeriv_zero] at h
  obtain ⟨F, hF_coeff⟩ :=
    exists_smoothCcPath_realizing_coeff (I := I) (M := M) g₀ φ hmass0
  have hφ'_smooth : ∀ i, ContDiff ℝ (k : ℕ) (symmCoeffPath (I := I) (M := M) g₀ φ i) :=
    symmCoeffPath_contDiff (I := I) (M := M) g₀ hφ_smooth
  have hφ'_mass : ∀ (j : ℕ), j ≤ k → ∀ (τ : ℝ), 0 ≤ τ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) d₂,
          tensorSobolevWeight (I := I) (M := M) i τ *
              (iteratedDeriv j (symmCoeffPath (I := I) (M := M) g₀ φ i) t) ^ 2 ≤ B i := by
    intro j hjk τ hτ
    exact symmCoeffPath_spectralMass (I := I) (M := M) g₀ hd₂_pos j
      (fun j' => (hφ_smooth j').of_le (mod_cast hjk)) τ
      (hφ_mass j hjk τ hτ)
      (hφ_mass j hjk (τ + (((weylSobolevExp (E := E) : ℕ) : ℝ) + 1)) (by positivity))
  have hae_all : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)),
      ∀ j, (w t).coeff j = φ j t := (MeasureTheory.ae_all_iff).2 hw
  have hwF : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)),
      w t = smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F t) := by
    filter_upwards [hae_all, MeasureTheory.ae_restrict_mem
      (measurableSet_Icc (a := (0 : ℝ)) (b := d₂))] with t htall htmem
    refine tensorHs.ext (funext fun j => ?_)
    rw [htall j, smoothCcToTensorHs_coeff, hF_coeff t htmem j]
  have hw'_ball : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
          (ccTensor02Symm (I := I) (M := M) g₀ (F t))‖ ≤
        deTurckRealizabilityRadius (I := I) (M := M) g₀ a ha_super := by
    filter_upwards [hw_ball, hwF] with t hwball_t hwF_t
    refine le_trans (norm_smoothCcToTensorHs_symmS_le (I := I) (M := M) g₀ ((a : ℝ) + 2)
      (F t)) ?_
    rw [← hwF_t]
    exact hwball_t
  have hw'_ae : ∀ i, (fun t => (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
      (ccTensor02Symm (I := I) (M := M) g₀ (F t))).coeff i)
      =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)]
        symmCoeffPath (I := I) (M := M) g₀ φ i := by
    intro i
    filter_upwards [MeasureTheory.ae_restrict_mem
      (measurableSet_Icc (a := (0 : ℝ)) (b := d₂))] with t ht
    rw [smoothCcToTensorHs_coeff]
    exact symmCoeffPath_realizes (I := I) (M := M) g₀ φ (F t)
      (fun j => hF_coeff t ht j) i
  obtain ⟨ψ, hψ_smooth, hψ_mass, hψ_ae⟩ :=
    deTurckSobolevNHa2_finiteOrder_jetSpectralMass_preserving (I := I) (M := M)
      g₀ g_bg a ha_super hT hd₂_pos hd₂_le
      (fun t => smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
        (ccTensor02Symm (I := I) (M := M) g₀ (F t)))
      hw'_ball k (symmCoeffPath (I := I) (M := M) g₀ φ) hφ'_smooth hφ'_mass hw'_ae
  refine ⟨ψ, hψ_smooth, hψ_mass, fun i => ?_⟩
  filter_upwards [hψ_ae i, hw_ball, hwF] with t hψt hwball_t hwF_t
  have hballF : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (F t)‖ ≤
      (Classical.choose (deTurckSobolevNHa2_exists_of_super
        (I := I) (M := M) g₀ a ha_super)).1 := by
    rw [← hwF_t]
    exact hwball_t
  rw [hwF_t, deTurckSobolevNHa2Symm_embed_eq_raw_embed_symmS (I := I) (M := M)
    g₀ g_bg a ha_super (F t) hballF]
  exact hψt


private theorem deTurckForcing_finiteOrderSmoothDriverSymm
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
    (hspatial : ∀ σ : ℝ, ∃ Cσ : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T,
      Summable (fun i => tensorSobolevWeight (I := I) (M := M) i σ *
          (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u) t) ^ 2) ∧
        ∑' i, tensorSobolevWeight (I := I) (M := M) i σ *
            (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
              (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u) t) ^ 2 ≤ Cσ) :
    ∃ d : ℝ, 0 < d ∧ d ≤ T ∧
      ∀ k : ℕ, ∃ f : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ,
        (∀ i, ContDiff ℝ (k : ℕ) (f i)) ∧
        (∀ (j : ℕ), j ≤ k → ∀ (τ : ℝ), 0 ≤ τ →
          ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
            ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) d,
              tensorSobolevWeight (I := I) (M := M) i τ *
                  (iteratedDeriv j (f i) t) ^ 2 ≤ B i) ∧
        (∀ i, (fun t => (gforce t).coeff i)
            =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d)] f i) := by
  classical
  obtain ⟨d, hd_pos, hd_le, hs_cont, hs_mass, hball, hcoeff_id⟩ :=
    deTurckForcing_solCoeff_continuous_smallTimeBase (I := I) (M := M)
      g₀ a ha_super hT hT1 gforce hspatial
  choose c hc_cont hc_ae using hs_cont
  have hae_d : ∀ i, c i =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d)]
      (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
        (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u)) := fun i =>
    MeasureTheory.ae_restrict_of_ae_restrict_of_subset (μ := MeasureTheory.volume)
      (Set.Icc_subset_Icc le_rfl hd_le) (hc_ae i)
  have hcont_pmc : ∀ i, ContinuousOn
      (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
        (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u)) (Set.Icc (0 : ℝ) d) := fun i =>
    (continuousOn_perModeConv_timeL2 (TensorEigenIdx.lambda (I := I) (M := M) i)
      (timeModeCoeff (I := I) (M := M) gforce i) hT.le).mono (Set.Icc_subset_Icc le_rfl hd_le)
  have heqOn_d : ∀ i, Set.EqOn (c i)
      (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
        (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u)) (Set.Icc (0 : ℝ) d) := fun i =>
    MeasureTheory.Measure.eqOn_Icc_of_ae_eq (MeasureTheory.volume : MeasureTheory.Measure ℝ)
      (ne_of_lt hd_pos) (hae_d i) (hc_cont i).continuousOn (hcont_pmc i)
  refine ⟨d, hd_pos, hd_le, ?_⟩
  have hsub : Set.Icc (0 : ℝ) d ⊆ Set.Icc (0 : ℝ) T := Set.Icc_subset_Icc le_rfl hd_le
  have hforce_coeff : ∀ i, (fun t => (gforce t).coeff i)
      =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d)]
        (fun t => (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
          (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)).coeff i) := by
    intro i
    exact MeasureTheory.ae_restrict_of_ae_restrict_of_subset (μ := MeasureTheory.volume) hsub
      (hforce.fun_comp (fun w => w.coeff i))
  have hgforce_tmc : ∀ i, (fun t => (gforce t).coeff i)
      =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d)]
        (fun s => (timeModeCoeff (I := I) (M := M) gforce i) s) := by
    intro i
    exact MeasureTheory.ae_restrict_of_ae_restrict_of_subset (μ := MeasureTheory.volume) hsub
      (timeModeCoeff_coeFn (I := I) (M := M) gforce i).symm
  intro k
  induction k with
  | zero =>
    obtain ⟨ψ, hψ_smooth, hψ_mass, hψ_ae⟩ :=
      deTurckSobolevNHa2Symm_finiteOrder_jetSpectralMass_preserving (I := I) (M := M)
        g₀ g_bg a ha_super hT hd_pos hd_le
        (fun t => maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)
        hball 0
        c
        (fun i => by rw [Nat.cast_zero, contDiff_zero]; exact hc_cont i)
        (fun j hj τ hτ => by
          obtain rfl := Nat.le_zero.mp hj
          obtain ⟨B, hBs, hBle⟩ := hs_mass τ hτ
          refine ⟨B, hBs, fun i t ht => ?_⟩
          rw [iteratedDeriv_zero, heqOn_d i ht]
          exact hBle i t ht)
        (fun i => (hcoeff_id i).trans (hae_d i).symm)
    exact ⟨ψ, hψ_smooth, hψ_mass, fun i => (hforce_coeff i).trans (hψ_ae i)⟩
  | succ k ih =>
    obtain ⟨fk, hfk_cont, hfk_mass, hfk_ae⟩ := ih
    obtain ⟨hφ_cont, hφ_mass⟩ :=
      perModeConv_finiteOrder_timeJet_spectralMass_gain (I := I) (M := M)
        g₀ hd_pos.le k fk hfk_cont hfk_mass
    have hw_coeff : ∀ i, (fun t => (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t).coeff i)
        =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d)]
          (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (fk i)) := by
      intro i
      have hfk_tmc : (fun s => (timeModeCoeff (I := I) (M := M) gforce i) s)
          =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d)] (fk i) :=
        (hgforce_tmc i).symm.trans (hfk_ae i)
      have hbridge : (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u))
          =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d)]
            (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (fk i)) := by
        filter_upwards [MeasureTheory.ae_restrict_mem
          (measurableSet_Icc (a := (0 : ℝ)) (b := d))] with t ht
        exact perModeConv_timeL2_congr (T := d) (TensorEigenIdx.lambda (I := I) (M := M) i)
          hfk_tmc ht
      exact (hcoeff_id i).trans hbridge
    obtain ⟨ψ, hψ_smooth, hψ_mass, hψ_ae⟩ :=
      deTurckSobolevNHa2Symm_finiteOrder_jetSpectralMass_preserving (I := I) (M := M)
        g₀ g_bg a ha_super hT hd_pos hd_le
        (fun t => maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)
        hball (k + 1)
        (fun i => perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (fk i))
        hφ_cont hφ_mass hw_coeff
    exact ⟨ψ, hψ_smooth, hψ_mass, fun i => (hforce_coeff i).trans (hψ_ae i)⟩


theorem maxRegForcing_smoothTimeJetDriver_of_galerkinSpatialMassSymm
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
    (hspatial : ∀ σ : ℝ, ∃ Cσ : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T,
      Summable (fun i => tensorSobolevWeight (I := I) (M := M) i σ *
          (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u) t) ^ 2) ∧
        ∑' i, tensorSobolevWeight (I := I) (M := M) i σ *
            (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
              (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u) t) ^ 2 ≤ Cσ) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ T ∧
      ∃ f : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ,
      (∀ i, ContDiff ℝ ∞ (f i)) ∧
      (∀ (j : ℕ) (τ : ℝ), 0 ≤ τ →
        ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
          ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) d₀,
            tensorSobolevWeight (I := I) (M := M) i τ *
                (iteratedDeriv j (f i) t) ^ 2 ≤ B i) ∧
      (∀ i, (fun t => (gforce t).coeff i)
          =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₀)] f i) := by
  classical
  obtain ⟨d, hd_pos, hd_le, hk⟩ :=
    deTurckForcing_finiteOrderSmoothDriverSymm (I := I) (M := M)
      g₀ g_bg a ha_super hT hT1 gforce hforce hspatial
  choose F hF_smooth hF_mass hF_ae using hk
  set f0 : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ := F 0 with hf0_def
  have hsub_clo : Set.Icc (0 : ℝ) d ⊆ closure (interior (Set.Icc (0 : ℝ) d)) := by
    rw [interior_Icc, closure_Ioo (ne_of_lt hd_pos)]
  have hEqOn : ∀ (k : ℕ) (i), Set.EqOn (F k i) (f0 i) (Set.Icc (0 : ℝ) d) := by
    intro k i
    have hae : (F k i) =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d)] (f0 i) :=
      (hF_ae k i).symm.trans (hF_ae 0 i)
    exact MeasureTheory.Measure.eqOn_of_ae_eq hae
      ((hF_smooth k i).continuous).continuousOn ((hF_smooth 0 i).continuous).continuousOn hsub_clo
  have hf0_smoothOn : ∀ i, ContDiffOn ℝ ∞ (f0 i) (Set.Icc (0 : ℝ) d) := by
    intro i
    rw [contDiffOn_infty]
    intro n
    exact ((hF_smooth n i).contDiffOn).congr (fun x hx => (hEqOn n i hx).symm)
  have hext : ∀ i, ∃ ψi : ℝ → ℝ, ContDiff ℝ ∞ ψi ∧
      Set.EqOn (f0 i) ψi (Set.Icc (0 : ℝ) d) :=
    fun i => contDiffOn_Icc_scalar_globalExtend hd_pos (hf0_smoothOn i)
  choose ψ hψ_smooth hψ_eqOn using hext
  have hjetEq : ∀ (j : ℕ) (i) (t), t ∈ Set.Icc (0 : ℝ) d →
      iteratedDeriv j (ψ i) t = iteratedDerivWithin j (f0 i) (Set.Icc (0 : ℝ) d) t := by
    intro j i t ht
    rw [iteratedDerivWithin_congr (hψ_eqOn i) ht]
    exact (iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hd_pos)
      ((hψ_smooth i).contDiffAt.of_le (mod_cast le_top)) ht).symm
  refine ⟨d, hd_pos, hd_le, ψ, hψ_smooth, ?_, ?_⟩
  · intro j τ hτ
    obtain ⟨B, hB_sum, hB_le⟩ := hF_mass j j (le_refl j) τ hτ
    refine ⟨B, hB_sum, fun i t ht => ?_⟩
    have hval : iteratedDeriv j (ψ i) t = iteratedDeriv j (F j i) t := by
      rw [hjetEq j i t ht, iteratedDerivWithin_congr ((hEqOn j i).symm) ht]
      exact iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hd_pos)
        ((hF_smooth j i).contDiffAt) ht
    rw [hval]
    exact hB_le i t ht
  · intro i
    have hf0ψ : (f0 i) =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d)] (ψ i) := by
      filter_upwards [MeasureTheory.ae_restrict_mem
        (measurableSet_Icc (a := (0 : ℝ)) (b := d))] with t ht
      exact hψ_eqOn i ht
    exact (hF_ae 0 i).trans hf0ψ

end SymmSCoefficientBlockTransfer


theorem maxRegSolField_parabolicInterior_jetSpectralMassSymm
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 4 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hTT₀ : T ≤ (quasilinear_maxreg_solution_of_nemytskii g₀ a
      (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a)
      (deTurckSobolevNHa2Symm_lipschitzWith_lipConst (I := I) (M := M) (g₀ := g₀)
        (g_bg := g_bg) a (by omega))
      (deTurckSobolevNHa2Symm_mixed_lipschitz_pointwise (I := I) (M := M) (g₀ := g₀)
        (g_bg := g_bg) a (by omega))).choose)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
    (hgforce : ‖gforce‖ ≤ deTurckForceBallRadiusSymm (I := I) (M := M) g₀ g_bg a (by omega)) :
    ∃ d₂ : ℝ, 0 < d₂ ∧ d₂ ≤ T ∧
      ∃ φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ,
      JetSpectralMassControl (I := I) (M := M) g₀ φ d₂ ∧
        (∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)),
          ‖maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
              (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t‖ ≤
            deTurckRealizabilityRadius (I := I) (M := M) g₀ a (by omega)) ∧
        ∀ i, (fun t => (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
              (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t).coeff i)
            =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)] φ i := by
  classical
  obtain ⟨d₀, hd₀_pos, hd₀_le, f, hf_smooth, hf_mass, hf_ae⟩ :=
    maxRegForcing_smoothTimeJetDriver_of_galerkinSpatialMassSymm (I := I) (M := M)
      g₀ g_bg a (by omega) hT hT1 gforce hforce
      (deTurckGalerkin_solField_uniformSpatialMass_allOrderSymm (I := I) (M := M)
        g₀ g_bg a ha_super hT hT1 hTT₀ gforce hforce hgforce)
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2 with hhc_def
  haveI : Countable (TensorEigenIdx (I := I) (M := M) g₀ 0 2) :=
    countable_tensorEigenIdx (I := I) (M := M) (g := g₀) (r := 0) (s := 2) hc
  set φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ :=
    fun i => perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (f i) with hφ_def
  have hφ_smooth : ∀ i, ContDiff ℝ ∞ (φ i) := fun i =>
    perModeConv_contDiff_top (TensorEigenIdx.lambda (I := I) (M := M) i) (f i) (hf_smooth i)
  obtain ⟨B0, hB0_sum, hB0_le⟩ := hf_mass 0 ((a : ℝ) + 2) (by positivity)
  obtain ⟨d₂, hd₂_pos, hd₂_le_d₀, hball_W⟩ :=
    tensorHs_smallTime_norm_le_of_perModeConv (I := I) (M := M)
      (g := g₀) (r := 0) (s := 2) (a := (a : ℝ)) hd₀_pos f
      (fun i => (hf_smooth i).continuous) (B := B0) hB0_sum
      (fun i s hs => by
        have h := hB0_le i s hs
        rwa [iteratedDeriv_zero] at h)
      (deTurckRealizabilityRadius_pos (I := I) (M := M) g₀ a (by omega))
  have hd₂_le : d₂ ≤ T := le_trans hd₂_le_d₀ hd₀_le
  have hd₂_le_d₀' : Set.Icc (0 : ℝ) d₂ ⊆ Set.Icc (0 : ℝ) d₀ :=
    Set.Icc_subset_Icc le_rfl hd₂_le_d₀
  refine ⟨d₂, hd₂_pos, hd₂_le, φ, ⟨hφ_smooth, ?_⟩, ?_, ?_⟩
  · intro j τ hτ
    obtain ⟨Cmaj, hCmaj_sum, hCmaj_le⟩ :=
      perModeConv_allOrder_timeDeriv_spectralMass_le (I := I) (M := M)
        (g := g₀) (r := 0) (s := 2) (T := d₀) hd₀_pos.le f hf_smooth hf_mass j τ hτ
    refine ⟨Cmaj, hCmaj_sum, fun i t ht => ?_⟩
    exact hCmaj_le i t (hd₂_le_d₀' ht)
  · have hsolcoeff_ae : ∀ i,
        (fun t => (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
              (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t).coeff i)
          =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)]
            (fun t => perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (f i) t) := by
      intro i
      have hsub : Set.Icc (0 : ℝ) d₂ ⊆ Set.Icc (0 : ℝ) T :=
        Set.Icc_subset_Icc le_rfl hd₂_le
      have hstep1 : (fun t => (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
              (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t).coeff i)
          =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)]
            (fun t => perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
              (fun s => (timeModeCoeff (I := I) (M := M) gforce i) s) t) :=
        MeasureTheory.ae_restrict_of_ae_restrict_of_subset (μ := MeasureTheory.volume) hsub
          (timeModeCoeff_eq_perModeConv_forcing (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            (a := (a : ℝ)) hT hT1 hc gforce i)
      have hforce_ae : (fun s => (timeModeCoeff (I := I) (M := M) gforce i) s)
          =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)] f i := by
        have htmc : (fun s => (timeModeCoeff (I := I) (M := M) gforce i) s)
            =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)]
              (fun s => (gforce s).coeff i) :=
          MeasureTheory.ae_restrict_of_ae_restrict_of_subset (μ := MeasureTheory.volume) hsub
            (timeModeCoeff_coeFn (I := I) (M := M) gforce i)
        exact htmc.trans
          (MeasureTheory.ae_restrict_of_ae_restrict_of_subset (μ := MeasureTheory.volume)
            hd₂_le_d₀' (hf_ae i))
      have hstep2 : (fun t => perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
              (fun s => (timeModeCoeff (I := I) (M := M) gforce i) s) t)
          =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)]
            (fun t => perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (f i) t) := by
        filter_upwards [MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume)
          (measurableSet_Icc (a := (0 : ℝ)) (b := d₂))] with t ht
        exact perModeConv_timeL2_congr (T := d₂) (TensorEigenIdx.lambda (I := I) (M := M) i)
          hforce_ae ht
      exact hstep1.trans hstep2
    have hcoeff_eq : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)),
        ∀ i, (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
              (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t).coeff i =
            perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (f i) t :=
      (MeasureTheory.ae_all_iff).2 hsolcoeff_ae
    filter_upwards [hcoeff_eq, MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume)
      (measurableSet_Icc (a := (0 : ℝ)) (b := d₂))] with t ht_coeff ht_mem
    refine hball_W t ht_mem
      (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
        (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t) ?_
    intro i
    exact ht_coeff i
  · intro i
    have hsub : Set.Icc (0 : ℝ) d₂ ⊆ Set.Icc (0 : ℝ) T :=
      Set.Icc_subset_Icc le_rfl hd₂_le
    have hstep1 : (fun t => (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t).coeff i)
        =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)]
          (fun t => perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun s => (timeModeCoeff (I := I) (M := M) gforce i) s) t) :=
      MeasureTheory.ae_restrict_of_ae_restrict_of_subset (μ := MeasureTheory.volume) hsub
        (timeModeCoeff_eq_perModeConv_forcing (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (a := (a : ℝ)) hT hT1 hc gforce i)
    have hforce_ae : (fun s => (timeModeCoeff (I := I) (M := M) gforce i) s)
        =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)] f i := by
      have htmc : (fun s => (timeModeCoeff (I := I) (M := M) gforce i) s)
          =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)]
            (fun s => (gforce s).coeff i) :=
        MeasureTheory.ae_restrict_of_ae_restrict_of_subset (μ := MeasureTheory.volume) hsub
          (timeModeCoeff_coeFn (I := I) (M := M) gforce i)
      exact htmc.trans
        (MeasureTheory.ae_restrict_of_ae_restrict_of_subset (μ := MeasureTheory.volume)
          hd₂_le_d₀' (hf_ae i))
    have hstep2 : (fun t => perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun s => (timeModeCoeff (I := I) (M := M) gforce i) s) t)
        =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)] φ i := by
      filter_upwards [MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume)
        (measurableSet_Icc (a := (0 : ℝ)) (b := d₂))] with t ht
      rw [hφ_def]
      exact perModeConv_timeL2_congr (T := d₂) (TensorEigenIdx.lambda (I := I) (M := M) i)
        hforce_ae ht
    exact hstep1.trans hstep2


private theorem deTurckForcing_smoothForcingDriverSymm
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 4 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hTT₀ : T ≤ (quasilinear_maxreg_solution_of_nemytskii g₀ a
      (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a)
      (deTurckSobolevNHa2Symm_lipschitzWith_lipConst (I := I) (M := M) (g₀ := g₀)
        (g_bg := g_bg) a (by omega))
      (deTurckSobolevNHa2Symm_mixed_lipschitz_pointwise (I := I) (M := M) (g₀ := g₀)
        (g_bg := g_bg) a (by omega))).choose)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
    (hgforce : ‖gforce‖ ≤ deTurckForceBallRadiusSymm (I := I) (M := M) g₀ g_bg a (by omega)) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ T ∧
      ∃ f : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ,
      (∀ i, ContDiff ℝ ∞ (f i)) ∧
      (∀ (j : ℕ) (τ : ℝ), 0 ≤ τ →
        ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
          ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) d₀,
            tensorSobolevWeight (I := I) (M := M) i τ *
                (iteratedDeriv j (f i) t) ^ 2 ≤ B i) ∧
      (∀ i, (fun t => (gforce t).coeff i)
          =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₀)] f i) := by
  classical
  obtain ⟨d₂, hd₂_pos, hd₂_le, φ, hφ_ctrl, hφ_ball, hφ_ae⟩ :=
    maxRegSolField_parabolicInterior_jetSpectralMassSymm (I := I) (M := M)
      g₀ g_bg a ha_super hT hT1 hTT₀ gforce hforce hgforce
  obtain ⟨ψ, hψ_ctrl, hψ_ae⟩ :=
    deTurckForcing_jetSpectralMass_preservingSymm (I := I) (M := M)
      g₀ g_bg a (by omega) hT hd₂_pos hd₂_le
      (fun t => maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
        (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)
      hφ_ball φ hφ_ctrl hφ_ae
  refine ⟨d₂, hd₂_pos, hd₂_le, ψ, hψ_ctrl.1, hψ_ctrl.2, fun i => ?_⟩
  have hsub : Set.Icc (0 : ℝ) d₂ ⊆ Set.Icc (0 : ℝ) T :=
    Set.Icc_subset_Icc le_rfl hd₂_le
  have hforce_coeff : (fun t => (gforce t).coeff i)
      =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)]
        (fun t => (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
          (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)).coeff i) :=
    MeasureTheory.ae_restrict_of_ae_restrict_of_subset (μ := MeasureTheory.volume) hsub
      (hforce.fun_comp (fun w => w.coeff i))
  exact hforce_coeff.trans (hψ_ae i)


private theorem deTurckForcing_fixedPoint_coeff_smooth_and_massSymm
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 4 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hTT₀ : T ≤ (quasilinear_maxreg_solution_of_nemytskii g₀ a
      (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a)
      (deTurckSobolevNHa2Symm_lipschitzWith_lipConst (I := I) (M := M) (g₀ := g₀)
        (g_bg := g_bg) a (by omega))
      (deTurckSobolevNHa2Symm_mixed_lipschitz_pointwise (I := I) (M := M) (g₀ := g₀)
        (g_bg := g_bg) a (by omega))).choose)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
    (hgforce : ‖gforce‖ ≤ deTurckForceBallRadiusSymm (I := I) (M := M) g₀ g_bg a (by omega)) :
    ∃ d₂ : ℝ, 0 < d₂ ∧ d₂ ≤ T ∧
      ∃ c : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ,
      (∀ i, ContDiff ℝ ∞ (c i)) ∧
      (∀ (j : ℕ) (τ : ℝ), 0 ≤ τ →
        ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
          ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) d₂,
            tensorSobolevWeight (I := I) (M := M) i τ *
                (iteratedDeriv j (c i) t) ^ 2 ≤ B i) ∧
      (∀ i, (timeModeCoeff (I := I) (M := M) gforce i : ℝ → ℝ)
          =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)] c i) := by
  classical
  obtain ⟨d₀, hd₀_pos, hd₀_le, f, hf_smooth, hf_mass, hf_ae⟩ :=
    deTurckForcing_smoothForcingDriverSymm (I := I) (M := M)
      g₀ g_bg a ha_super hT hT1 hTT₀ gforce hforce hgforce
  refine ⟨d₀, hd₀_pos, hd₀_le, f, hf_smooth, hf_mass, fun i => ?_⟩
  have hsub : Set.Icc (0 : ℝ) d₀ ⊆ Set.Icc (0 : ℝ) T :=
    Set.Icc_subset_Icc le_rfl hd₀_le
  have hbridge : (timeModeCoeff (I := I) (M := M) gforce i : ℝ → ℝ)
      =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₀)]
        (fun t => (gforce t).coeff i) :=
    MeasureTheory.ae_restrict_of_ae_restrict_of_subset (μ := MeasureTheory.volume) hsub
      (timeModeCoeff_coeFn (I := I) (M := M) gforce i)
  exact hbridge.trans (hf_ae i)


theorem deTurckForcing_timeModeCoeff_smooth_allOrderJetSymm
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 4 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hTT₀ : T ≤ (quasilinear_maxreg_solution_of_nemytskii g₀ a
      (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a)
      (deTurckSobolevNHa2Symm_lipschitzWith_lipConst (I := I) (M := M) (g₀ := g₀)
        (g_bg := g_bg) a (by omega))
      (deTurckSobolevNHa2Symm_mixed_lipschitz_pointwise (I := I) (M := M) (g₀ := g₀)
        (g_bg := g_bg) a (by omega))).choose)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
    (hgforce : ‖gforce‖ ≤ deTurckForceBallRadiusSymm (I := I) (M := M) g₀ g_bg a (by omega)) :
    ∃ d₂ : ℝ, 0 < d₂ ∧ d₂ ≤ T ∧
      ∃ g : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ,
      (∀ i, ContDiff ℝ ∞ (g i)) ∧
      (∀ (j : ℕ) (τ : ℝ), 0 ≤ τ →
        ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
          ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) d₂,
            tensorSobolevWeight (I := I) (M := M) i τ *
                (iteratedDeriv j (g i) t) ^ 2 ≤ B i) ∧
      (∀ i, (timeModeCoeff (I := I) (M := M) gforce i : ℝ → ℝ)
          =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)] g i) :=
  deTurckForcing_fixedPoint_coeff_smooth_and_massSymm (I := I) (M := M)
    g₀ g_bg a ha_super hT hT1 hTT₀ gforce hforce hgforce


theorem deTurckForcing_smoothCoordinate_aeTimeJetSymm
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 4 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hTT₀ : T ≤ (quasilinear_maxreg_solution_of_nemytskii g₀ a
      (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a)
      (deTurckSobolevNHa2Symm_lipschitzWith_lipConst (I := I) (M := M) (g₀ := g₀)
        (g_bg := g_bg) a (by omega))
      (deTurckSobolevNHa2Symm_mixed_lipschitz_pointwise (I := I) (M := M) (g₀ := g₀)
        (g_bg := g_bg) a (by omega))).choose)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
    (hgforce : ‖gforce‖ ≤ deTurckForceBallRadiusSymm (I := I) (M := M) g₀ g_bg a (by omega)) :
    ∃ d₂ : ℝ, 0 < d₂ ∧ d₂ ≤ T ∧
      ∃ f : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ,
      (∀ i, ContDiff ℝ ∞ (f i)) ∧
      (∀ (j : ℕ) (τ : ℝ), 0 ≤ τ →
        ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
          ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) d₂,
            tensorSobolevWeight (I := I) (M := M) i τ *
                (iteratedDeriv j (f i) t) ^ 2 ≤ B i) ∧
      (∀ i, (fun t => (gforce t).coeff i)
          =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)] f i) := by
  obtain ⟨d₂, hd₂_pos, hd₂_le, g, hg_smooth, hg_mass, hg_ae⟩ :=
    deTurckForcing_timeModeCoeff_smooth_allOrderJetSymm (I := I) (M := M)
      g₀ g_bg a ha_super hT hT1 hTT₀ gforce hforce hgforce
  refine ⟨d₂, hd₂_pos, hd₂_le, g, hg_smooth, hg_mass, fun i => ?_⟩
  have htmc : (fun t => (gforce t).coeff i)
      =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d₂)]
        (timeModeCoeff (I := I) (M := M) gforce i : ℝ → ℝ) := by
    refine MeasureTheory.ae_restrict_of_ae_restrict_of_subset (μ := MeasureTheory.volume)
      (Set.Icc_subset_Icc le_rfl hd₂_le) ?_
    exact (timeModeCoeff_coeFn (I := I) (M := M) gforce i).symm
  exact htmc.trans (hg_ae i)

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
