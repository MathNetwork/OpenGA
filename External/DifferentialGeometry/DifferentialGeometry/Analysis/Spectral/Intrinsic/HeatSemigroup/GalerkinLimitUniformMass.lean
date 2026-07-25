import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.GalerkinParabolicEnergyDeTurck
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.GalerkinForcingTimeL2Limit
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.SolutionSpace
import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.Operator
import Mathlib.Topology.Algebra.InfiniteSum.Real

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable {T : ℝ}

theorem fatou_weighted_sq_mass_le {ι : Type*} (S : ℕ → Finset ι)
    (hS : Tendsto S atTop atTop) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (v : ℕ → ι → ℝ) (vlim : ι → ℝ)
    (hconv : ∀ i, Tendsto (fun N => v N i) atTop (𝓝 (vlim i)))
    (B : ℝ) (hbound : ∀ N, ∑ i ∈ S N, w i * (v N i) ^ 2 ≤ B) :
    Summable (fun i => w i * (vlim i) ^ 2) ∧
      ∑' i, w i * (vlim i) ^ 2 ≤ B := by
  have hnn : ∀ i, 0 ≤ w i * (vlim i) ^ 2 := fun i => mul_nonneg (hw i) (sq_nonneg _)
  have hpartial : ∀ K : Finset ι, ∑ i ∈ K, w i * (vlim i) ^ 2 ≤ B := by
    intro K
    have hlim : Tendsto (fun N => ∑ i ∈ K, w i * (v N i) ^ 2) atTop
        (𝓝 (∑ i ∈ K, w i * (vlim i) ^ 2)) := by
      refine tendsto_finset_sum K (fun i _ => ?_)
      exact ((hconv i).pow 2).const_mul (w i)
    have hev : ∀ᶠ N in atTop, ∑ i ∈ K, w i * (v N i) ^ 2 ≤ B := by
      have hsub : ∀ᶠ N in atTop, K ≤ S N := hS.eventually_ge_atTop K
      filter_upwards [hsub] with N hKN
      have hKsub : K ⊆ S N := hKN
      have hmono : ∑ i ∈ K, w i * (v N i) ^ 2 ≤ ∑ i ∈ S N, w i * (v N i) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hKsub
          (fun i _ _ => mul_nonneg (hw i) (sq_nonneg _))
      exact le_trans hmono (hbound N)
    exact le_of_tendsto hlim hev
  refine ⟨summable_of_sum_le hnn hpartial, ?_⟩
  exact Real.tsum_le_of_sum_le hnn hpartial

private theorem continuousOn_galerkinForcingSymm
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {T : ℝ}
    (U : ℕ → ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) (N : ℕ)
    (hUcont : ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
      ContinuousOn (fun t => U N t i) (Set.Icc (0 : ℝ) T))
    (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2) :
    ContinuousOn (fun t => deTurckGalerkinForcingSymm (I := I) (M := M) g₀ g_bg a U N t i)
      (Set.Icc (0 : ℝ) T) := by
  classical
  by_cases hi : i ∈ eigenIdxFinset (I := I) (M := M) g₀ N
  · have hfield := continuousOn_galerkinForcing_field (I := I) (M := M) g₀ a U N hUcont
    have hcoeff : ContinuousOn
        (fun t => (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
          (finiteEigenComboHs (I := I) (M := M) g₀
            (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t) ((a : ℝ) + 2))).coeff i)
        (Set.Icc (0 : ℝ) T) := by
      obtain ⟨K, hK⟩ := deTurckSobolevNHa2Symm_lipschitzWith (I := I) (M := M) g₀ g_bg a ha_super
      have hN_cont : ContinuousOn
          (fun t => deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
            (finiteEigenComboHs (I := I) (M := M) g₀
              (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t) ((a : ℝ) + 2)))
          (Set.Icc (0 : ℝ) T) :=
        hK.continuous.comp_continuousOn hfield
      have hcoeff_cont : ContinuousOn
          (fun t => tensorHsCoeffL (I := I) (M := M) (a := (a : ℝ)) i
            (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
              (finiteEigenComboHs (I := I) (M := M) g₀
                (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t) ((a : ℝ) + 2))))
          (Set.Icc (0 : ℝ) T) :=
        (tensorHsCoeffL (I := I) (M := M) (a := (a : ℝ)) i).continuous.comp_continuousOn hN_cont
      simpa only [tensorHsCoeffL_apply] using hcoeff_cont
    refine hcoeff.congr (fun t _ => ?_)
    rw [deTurckGalerkinForcingSymm_apply, if_pos hi]
  · refine (continuousOn_const (c := (0 : ℝ))).congr (fun t _ => ?_)
    rw [deTurckGalerkinForcingSymm_apply, if_neg hi]

private theorem galerkinPerMode_eq_perModeConvSymm
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {T : ℝ} (hT : 0 < T)
    (U : ℕ → ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) (N : ℕ)
    (hUinit : ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N, U N 0 i = 0)
    (hUcont : ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
      ContinuousOn (fun t => U N t i) (Set.Icc (0 : ℝ) T))
    (hUderiv : ∀ t ∈ Set.Ico (0 : ℝ) T,
      ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
        HasDerivWithinAt (fun r => U N r i)
          (-(TensorEigenIdx.lambda (I := I) (M := M) i) * U N t i +
            deTurckGalerkinForcingSymm (I := I) (M := M) g₀ g_bg a U N t i)
          (Set.Ici t) t)
    (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2)
    (hi : i ∈ eigenIdxFinset (I := I) (M := M) g₀ N)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    U N t i =
      perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
        (Set.IccExtend hT.le (fun p : ↑(Set.Icc (0 : ℝ) T) =>
          deTurckGalerkinForcingSymm (I := I) (M := M) g₀ g_bg a U N p.1 i)) t := by
  classical
  set lam := TensorEigenIdx.lambda (I := I) (M := M) i with hlam_def
  have hlam_nonneg : 0 ≤ lam := tensor_lambda_nonneg (I := I) (M := M) i
  set fForce : ℝ → ℝ :=
    Set.IccExtend hT.le (fun p : ↑(Set.Icc (0 : ℝ) T) =>
      deTurckGalerkinForcingSymm (I := I) (M := M) g₀ g_bg a U N p.1 i) with hfForce_def
  have hfForce_cont : Continuous fForce := by
    refine Continuous.Icc_extend' ?_
    exact (continuousOn_galerkinForcingSymm (I := I) (M := M) g₀ g_bg a ha_super U N hUcont i).restrict
  have hfForce_mem : ∀ {x : ℝ}, x ∈ Set.Icc (0 : ℝ) T →
      fForce x = deTurckGalerkinForcingSymm (I := I) (M := M) g₀ g_bg a U N x i := by
    intro x hx
    rw [hfForce_def, Set.IccExtend_of_mem hT.le _ hx]
  set v : ℝ → ℝ → ℝ := fun s y => -lam * y + fForce s with hv_def
  have hv_lip : ∀ s ∈ Set.Ico (0 : ℝ) T, LipschitzOnWith ⟨|lam|, abs_nonneg lam⟩
      (v s) (Set.univ : Set ℝ) := by
    intro s _
    have hlip : LipschitzWith ⟨|lam|, abs_nonneg lam⟩ (fun y : ℝ => -lam * y + fForce s) := by
      refine LipschitzWith.of_dist_le_mul (fun y₁ y₂ => ?_)
      rw [Real.dist_eq, Real.dist_eq]
      have heq : -lam * y₁ + fForce s - (-lam * y₂ + fForce s) = -lam * (y₁ - y₂) := by ring
      rw [heq, abs_mul, abs_neg]
      simp only [NNReal.coe_mk, le_refl]
    exact hlip.lipschitzOnWith
  set gG : ℝ → ℝ := fun s => U N s i with hgG_def
  set gP : ℝ → ℝ := fun s => perModeConv lam fForce s with hgP_def
  have hgG_cont : ContinuousOn gG (Set.Icc (0 : ℝ) T) := hUcont i hi
  have hgP_cont : ContinuousOn gP (Set.Icc (0 : ℝ) T) :=
    (continuous_perModeConv lam hfForce_cont).continuousOn
  have hgG_deriv : ∀ s ∈ Set.Ico (0 : ℝ) T, HasDerivWithinAt gG (v s (gG s)) (Set.Ici s) s := by
    intro s hs
    have hd := hUderiv s hs i hi
    have hforce_eq : fForce s = deTurckGalerkinForcingSymm (I := I) (M := M) g₀ g_bg a U N s i :=
      hfForce_mem ⟨hs.1, le_of_lt hs.2⟩
    have hval : v s (gG s) =
        -(lam) * U N s i + deTurckGalerkinForcingSymm (I := I) (M := M) g₀ g_bg a U N s i := by
      simp only [hv_def, hgG_def, hforce_eq]
    rw [hval]
    exact hd
  have hgP_deriv : ∀ s ∈ Set.Ico (0 : ℝ) T, HasDerivWithinAt gP (v s (gP s)) (Set.Ici s) s := by
    intro s _
    have hd := (perModeConv_hasDerivAt lam hfForce_cont s).hasDerivWithinAt (s := Set.Ici s)
    have hval : v s (gP s) = fForce s - lam * perModeConv lam fForce s := by
      simp only [hv_def, hgP_def]; ring
    rw [hval]
    exact hd
  have hinit : gG 0 = gP 0 := by
    simp only [hgG_def, hgP_def, hUinit i hi, perModeConv_zero_left]
  have heqOn : Set.EqOn gG gP (Set.Icc (0 : ℝ) T) :=
    ODE_solution_unique_of_mem_Icc_right hv_lip hgG_cont
      (fun s hs => hgG_deriv s hs) (fun s _ => Set.mem_univ _)
      hgP_cont (fun s hs => hgP_deriv s hs) (fun s _ => Set.mem_univ _) hinit
  exact heqOn ht

private noncomputable def galerkinCoordFieldSymm
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2)) :
    EuclideanSpace ℝ {i // i ∈ S} → EuclideanSpace ℝ {i // i ∈ S} :=
  fun w => galerkinCoordDiag (I := I) (M := M) g₀ S w +
    galerkinCoordRestrict (I := I) (M := M) g₀ a S
      (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
        (galerkinCoordEmbed (I := I) (M := M) g₀ a S w))

private lemma galerkinCoordFieldSymm_apply
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
    (w : EuclideanSpace ℝ {i // i ∈ S}) (j : {i // i ∈ S}) :
    (galerkinCoordFieldSymm (I := I) (M := M) g₀ g_bg a S w) j =
      -(TensorEigenIdx.lambda (I := I) (M := M) j.1) * w j +
        (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
          (galerkinCoordEmbed (I := I) (M := M) g₀ a S w)).coeff j.1 := by
  change (galerkinCoordDiag (I := I) (M := M) g₀ S w) j +
    (galerkinCoordRestrict (I := I) (M := M) g₀ a S _) j = _
  rw [galerkinCoordDiag_apply, galerkinCoordRestrict_apply]

private theorem galerkinCoordFieldSymm_lipschitzWith
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2)) :
    ∃ K : ℝ≥0, LipschitzWith K (galerkinCoordFieldSymm (I := I) (M := M) g₀ g_bg a S) := by
  obtain ⟨K₀, hK₀⟩ := deTurckSobolevNHa2Symm_lipschitzWith (I := I) (M := M) g₀ g_bg a ha_super
  refine ⟨‖galerkinCoordDiag (I := I) (M := M) g₀ S‖₊ +
    ‖galerkinCoordRestrict (I := I) (M := M) g₀ a S‖₊ * K₀ *
      ‖galerkinCoordEmbed (I := I) (M := M) g₀ a S‖₊, ?_⟩
  have hdiag : LipschitzWith ‖galerkinCoordDiag (I := I) (M := M) g₀ S‖₊
      (galerkinCoordDiag (I := I) (M := M) g₀ S) :=
    (galerkinCoordDiag (I := I) (M := M) g₀ S).lipschitz
  have hnonlin : LipschitzWith
      (‖galerkinCoordRestrict (I := I) (M := M) g₀ a S‖₊ * K₀ *
        ‖galerkinCoordEmbed (I := I) (M := M) g₀ a S‖₊)
      (fun w => galerkinCoordRestrict (I := I) (M := M) g₀ a S
        (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
          (galerkinCoordEmbed (I := I) (M := M) g₀ a S w))) :=
    ((galerkinCoordRestrict (I := I) (M := M) g₀ a S).lipschitz.comp hK₀).comp
      (galerkinCoordEmbed (I := I) (M := M) g₀ a S).lipschitz
  exact hdiag.add hnonlin

private theorem galerkinODE_solution_uniqueSymm
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {T : ℝ} (_hT : 0 < T)
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
    (V V' : ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ)
    (hVcont : ∀ i ∈ S, ContinuousOn (fun t => V t i) (Set.Icc (0 : ℝ) T))
    (hVderiv : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ i ∈ S,
      HasDerivWithinAt (fun r => V r i)
        (-(TensorEigenIdx.lambda (I := I) (M := M) i) * V t i +
          (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
            (finiteEigenComboHs (I := I) (M := M) g₀ S (V t) ((a : ℝ) + 2))).coeff i)
        (Set.Ici t) t)
    (hV'cont : ∀ i ∈ S, ContinuousOn (fun t => V' t i) (Set.Icc (0 : ℝ) T))
    (hV'deriv : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ i ∈ S,
      HasDerivWithinAt (fun r => V' r i)
        (-(TensorEigenIdx.lambda (I := I) (M := M) i) * V' t i +
          (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
            (finiteEigenComboHs (I := I) (M := M) g₀ S (V' t) ((a : ℝ) + 2))).coeff i)
        (Set.Ici t) t)
    (hinit : ∀ i ∈ S, V 0 i = V' 0 i)
    (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2) (hi : i ∈ S)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    V t i = V' t i := by
  classical
  obtain ⟨Klip, hKlip⟩ :=
    galerkinCoordFieldSymm_lipschitzWith (I := I) (M := M) g₀ g_bg a ha_super S
  set e := EuclideanSpace.equiv {i // i ∈ S} ℝ with he_def
  set γ : (ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) →
      ℝ → EuclideanSpace ℝ {i // i ∈ S} :=
    fun W t => e.symm (fun j => W t j.1) with hγ_def
  have hcomp_j : ∀ (W : ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) (t : ℝ)
      (j : {i // i ∈ S}), (γ W t) j = W t j.1 := by
    intro W t j; rfl
  have hembed : ∀ (W : ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) (t : ℝ),
      galerkinCoordEmbed (I := I) (M := M) g₀ a S (γ W t) =
        finiteEigenComboHs (I := I) (M := M) g₀ S (W t) ((a : ℝ) + 2) := by
    intro W t
    apply tensorHs.ext
    funext i'
    rw [galerkinCoordEmbed_coeff, finiteEigenComboHs_coeff]
    by_cases hi' : i' ∈ S
    · rw [dif_pos hi', if_pos hi']; rfl
    · rw [dif_neg hi', if_neg hi']
  have hγcont : ∀ (W : ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ),
      (∀ i ∈ S, ContinuousOn (fun t => W t i) (Set.Icc (0 : ℝ) T)) →
      ContinuousOn (γ W) (Set.Icc (0 : ℝ) T) := by
    intro W hWcont
    exact e.symm.continuous.comp_continuousOn (continuousOn_pi.2 (fun j => hWcont j.1 j.2))
  have hγderiv : ∀ (W : ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ),
      (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ i ∈ S,
        HasDerivWithinAt (fun r => W r i)
          (-(TensorEigenIdx.lambda (I := I) (M := M) i) * W t i +
            (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
              (finiteEigenComboHs (I := I) (M := M) g₀ S (W t) ((a : ℝ) + 2))).coeff i)
          (Set.Ici t) t) →
      ∀ t ∈ Set.Ico (0 : ℝ) T,
        HasDerivWithinAt (γ W)
          (galerkinCoordFieldSymm (I := I) (M := M) g₀ g_bg a S (γ W t)) (Set.Ici t) t := by
    intro W hWderiv t ht
    have hpi : HasDerivWithinAt (fun s => (fun j : {i // i ∈ S} => W s j.1))
        (fun j : {i // i ∈ S} =>
          -(TensorEigenIdx.lambda (I := I) (M := M) j.1) * W t j.1 +
            (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
              (finiteEigenComboHs (I := I) (M := M) g₀ S (W t) ((a : ℝ) + 2))).coeff j.1)
        (Set.Ici t) t :=
      hasDerivWithinAt_pi.mpr (fun j => hWderiv t ht j.1 j.2)
    have hcomp := (e.symm.hasFDerivAt (x := (fun j : {i // i ∈ S} => W t j.1))).comp_hasDerivWithinAt
      t hpi
    rw [ContinuousLinearEquiv.coe_coe] at hcomp
    have hval : e.symm
        (fun j : {i // i ∈ S} =>
          -(TensorEigenIdx.lambda (I := I) (M := M) j.1) * W t j.1 +
            (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
              (finiteEigenComboHs (I := I) (M := M) g₀ S (W t) ((a : ℝ) + 2))).coeff j.1) =
        galerkinCoordFieldSymm (I := I) (M := M) g₀ g_bg a S (γ W t) := by
      apply e.injective
      ext j
      rw [ContinuousLinearEquiv.apply_symm_apply]
      change _ = (galerkinCoordFieldSymm (I := I) (M := M) g₀ g_bg a S (γ W t)) j
      rw [galerkinCoordFieldSymm_apply, hcomp_j, hembed]
    rw [hval] at hcomp
    exact hcomp
  have hlip_univ : ∀ s ∈ Set.Ico (0 : ℝ) T,
      LipschitzOnWith Klip (galerkinCoordFieldSymm (I := I) (M := M) g₀ g_bg a S)
        (Set.univ : Set (EuclideanSpace ℝ {i // i ∈ S})) :=
    fun _ _ => hKlip.lipschitzOnWith
  have heqOn : Set.EqOn (γ V) (γ V') (Set.Icc (0 : ℝ) T) := by
    refine ODE_solution_unique_of_mem_Icc_right
      (v := fun _ => galerkinCoordFieldSymm (I := I) (M := M) g₀ g_bg a S)
      (s := fun _ => (Set.univ : Set (EuclideanSpace ℝ {i // i ∈ S})))
      hlip_univ (hγcont V hVcont) (fun s hs => hγderiv V hVderiv s hs)
      (fun _ _ => Set.mem_univ _) (hγcont V' hV'cont) (fun s hs => hγderiv V' hV'deriv s hs)
      (fun _ _ => Set.mem_univ _) ?_
    apply e.injective
    ext j
    rw [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply]
    exact hinit j.1 j.2
  have := heqOn ht
  have hj : (γ V t) ⟨i, hi⟩ = (γ V' t) ⟨i, hi⟩ := by rw [this]
  rw [hcomp_j, hcomp_j] at hj
  exact hj

private theorem galerkinForcing_field_eq_maxRegDuhamel_projTruncationSymm
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (U : ℕ → ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ)
    (hUinit : ∀ N, ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N, U N 0 i = 0)
    (hUcont : ∀ N, ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
      ContinuousOn (fun t => U N t i) (Set.Icc (0 : ℝ) T))
    (hUderiv : ∀ N, ∀ t ∈ Set.Ico (0 : ℝ) T,
      ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
        HasDerivWithinAt (fun r => U N r i)
          (-(TensorEigenIdx.lambda (I := I) (M := M) i) * U N t i +
            deTurckGalerkinForcingSymm (I := I) (M := M) g₀ g_bg a U N t i)
          (Set.Ici t) t)
    (N : ℕ) :
    TimeSobolev.ofContinuousOn
        (continuousOn_galerkinForcing_field (I := I) (M := M) g₀ a U N (hUcont N)) =
      maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
        (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
        (timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N
          (nemytskii (I := I) (M := M)
            (deTurckSobolevNHa2Symm_lipschitzWith_lipConst (I := I) (M := M) (g₀ := g₀) (g_bg := g_bg)
              a ha_super)
            (TimeSobolev.ofContinuousOn
              (continuousOn_galerkinForcing_field (I := I) (M := M) g₀ a U N (hUcont N))))) := by
  classical
  have h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2
  set hLipC := deTurckSobolevNHa2Symm_lipschitzWith_lipConst (I := I) (M := M)
    (g₀ := g₀) (g_bg := g_bg) a ha_super with hLipC_def
  set VN := TimeSobolev.ofContinuousOn
    (continuousOn_galerkinForcing_field (I := I) (M := M) g₀ a U N (hUcont N)) with hVN_def
  set gforceN := nemytskii (I := I) (M := M) hLipC VN with hgforceN_def
  refine timeModeCoeff_injective (I := I) (M := M) h_compact (fun i => ?_)
  set lam := TensorEigenIdx.lambda (I := I) (M := M) i with hlam_def
  refine Lp.ext ?_
  have hLco := timeModeCoeff_coeFn (I := I) (M := M) VN i
  have hVco : ⇑VN =ᵐ[timeMeasure T]
      (fun t => finiteEigenComboHs (I := I) (M := M) g₀
        (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t) ((a : ℝ) + 2)) :=
    TimeSobolev.coeFn_ofContinuousOn _
  have hRco := timeModeCoeff_coeFn (I := I) (M := M)
    (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
      (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
      (timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N gforceN)) i
  have hRpm := timeModeCoeff_eq_perModeConv_forcing (I := I) (M := M) (h_compact := h_compact)
    hT hT1 (timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N gforceN) i
  have hPNco := timeModeCoeff_coeFn (I := I) (M := M)
    (timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N gforceN) i
  have hPproj : ⇑(timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N gforceN) =ᵐ[timeMeasure T]
      fun s => spatialEigenProj (I := I) (M := M) g₀ (a : ℝ) N (gforceN s) :=
    ContinuousLinearMap.coeFn_compLpL _ gforceN
  have hgco : ⇑gforceN =ᵐ[timeMeasure T]
      (fun s => deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a (VN s)) :=
    nemytskii_coeFn (I := I) (M := M) hLipC VN
  have hPNforcing : ⇑(timeModeCoeff (I := I) (M := M)
        (timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N gforceN) i) =ᵐ[timeMeasure T]
      (fun s => deTurckGalerkinForcingSymm (I := I) (M := M) g₀ g_bg a U N s i) := by
    filter_upwards [hPNco, hPproj, hgco, hVco] with s hs1 hs2 hs3 hs4
    rw [hs1, hs2, spatialEigenProj_apply, finiteEigenComboHs_coeff, deTurckGalerkinForcingSymm_apply]
    by_cases hi : i ∈ eigenIdxFinset (I := I) (M := M) g₀ N
    · rw [if_pos hi, if_pos hi, hs3, hs4]
    · rw [if_neg hi, if_neg hi]
  by_cases hi : i ∈ eigenIdxFinset (I := I) (M := M) g₀ N
  · have hVNi : ⇑(timeModeCoeff (I := I) (M := M) VN i) =ᵐ[timeMeasure T]
        fun t => U N t i := by
      refine hLco.trans ?_
      filter_upwards [hVco] with t ht
      rw [ht, finiteEigenComboHs_coeff, if_pos hi]
    refine hVNi.trans (EventuallyEq.trans ?_ (hRco.trans hRpm).symm)
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc] with t htmem
    have htmem' : t ∈ Set.Icc (0 : ℝ) T := htmem
    have hcongr1 : perModeConv lam
          (fun s => (timeModeCoeff (I := I) (M := M)
            (timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N gforceN) i) s) t =
        perModeConv lam
          (fun s => deTurckGalerkinForcingSymm (I := I) (M := M) g₀ g_bg a U N s i) t :=
      perModeConv_timeL2_congr lam hPNforcing htmem'
    have hgp := galerkinPerMode_eq_perModeConvSymm (I := I) (M := M) g₀ g_bg a ha_super hT U N
      (hUinit N) (hUcont N) (hUderiv N) i hi htmem'
    rw [← hlam_def] at hgp
    rw [hgp, hcongr1]
    refine perModeConv_timeL2_congr lam ?_ htmem'
    refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall (fun s hs => ?_))
    rw [Set.IccExtend_of_mem hT.le _ hs]
  · have hVNi : ⇑(timeModeCoeff (I := I) (M := M) VN i) =ᵐ[timeMeasure T]
        fun _ => (0 : ℝ) := by
      refine hLco.trans ?_
      filter_upwards [hVco] with t ht
      rw [ht, finiteEigenComboHs_coeff, if_neg hi]
    refine hVNi.trans (EventuallyEq.trans ?_ (hRco.trans hRpm).symm)
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc] with t htmem
    have htmem' : t ∈ Set.Icc (0 : ℝ) T := htmem
    have hcongr1 : perModeConv lam
          (fun s => (timeModeCoeff (I := I) (M := M)
            (timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N gforceN) i) s) t =
        perModeConv lam (fun _ => (0 : ℝ)) t := by
      refine perModeConv_timeL2_congr lam ?_ htmem'
      filter_upwards [hPNforcing] with s hs
      rw [hs, deTurckGalerkinForcingSymm_apply, if_neg hi]
    rw [hcongr1]
    unfold perModeConv
    simp

private noncomputable def deTurckForceShortTimeSymm (g₀ g_bg : SmoothRiemannianMetric I M)
    (a : ℕ) (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) : ℝ :=
  (quasilinear_maxreg_solution_of_nemytskii (I := I) (M := M) g₀ a
    (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a)
    (deTurckSobolevNHa2Symm_lipschitzWith_lipConst (I := I) (M := M) (g₀ := g₀) (g_bg := g_bg)
      a ha_super)
    (deTurckSobolevNHa2Symm_mixed_lipschitz_pointwise (I := I) (M := M) (g₀ := g₀)
      (g_bg := g_bg) a ha_super)).choose

private theorem deTurckForceShortTimeSymm_eq (g₀ g_bg : SmoothRiemannianMetric I M)
    (a : ℕ) (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) :
    deTurckForceShortTimeSymm (I := I) (M := M) g₀ g_bg a ha_super =
      min 1 (min (1 / (64 * (((deTurckSobolevNHa2Symm_mixed_lipschitz_pointwise (I := I)
              (M := M) (g₀ := g₀) (g_bg := g_bg) a ha_super).choose_spec.choose : ℝ) + 1) ^ 2))
        ((deTurckForceBallRadiusSymm (I := I) (M := M) g₀ g_bg a ha_super /
            (2 * (‖deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
              (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))‖ + 1))) ^ 2)) :=
  (quasilinear_maxreg_solution_of_nemytskii (I := I) (M := M) g₀ a
    (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a)
    (deTurckSobolevNHa2Symm_lipschitzWith_lipConst (I := I) (M := M) (g₀ := g₀) (g_bg := g_bg)
      a ha_super)
    (deTurckSobolevNHa2Symm_mixed_lipschitz_pointwise (I := I) (M := M) (g₀ := g₀)
      (g_bg := g_bg) a ha_super)).choose_spec.1

private theorem symmForce_contraction_coeff_le_half (C₁ C₂ : ℝ≥0) {T : ℝ}
    (hT0 : 0 ≤ T) (hT1 : T ≤ 1)
    (hT_lo : T ≤ 1 / (64 * ((C₂ : ℝ) + 1) ^ 2)) :
    (C₁ : ℝ) * (Real.sqrt (1 + T)) * (1 / (16 * ((C₁ : ℝ) + 1))) * (1 + T) +
      (C₂ : ℝ) * (2 * Real.sqrt T) ≤ 1 / 2 := by
  have h1T : (1 : ℝ) + T ≤ 2 := by linarith
  have hsqrt1T_le : Real.sqrt (1 + T) ≤ 1 + T := by
    have h1le : (1 : ℝ) ≤ 1 + T := by linarith
    calc Real.sqrt (1 + T) ≤ Real.sqrt ((1 + T) ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (1 + T)])
      _ = 1 + T := Real.sqrt_sq (by linarith)
  have harm1 : (C₁ : ℝ) * (Real.sqrt (1 + T)) * (1 / (16 * ((C₁ : ℝ) + 1))) * (1 + T) ≤ 1 / 4 := by
    have hle : (C₁ : ℝ) * (Real.sqrt (1 + T)) * (1 / (16 * ((C₁ : ℝ) + 1))) * (1 + T) ≤
        (C₁ : ℝ) * 2 * (1 / (16 * ((C₁ : ℝ) + 1))) * 2 := by
      have hc1 : (0:ℝ) ≤ (C₁:ℝ) := C₁.coe_nonneg
      have h0 : (0:ℝ) ≤ 1 + T := by linarith
      have hsqrt2 : Real.sqrt (1 + T) ≤ 2 := le_trans hsqrt1T_le h1T
      have hρnn : (0:ℝ) ≤ 1 / (16 * ((C₁ : ℝ) + 1)) := by positivity
      gcongr
    refine le_trans hle ?_
    rw [show (C₁ : ℝ) * 2 * (1 / (16 * ((C₁ : ℝ) + 1))) * 2 =
        (C₁ : ℝ) / ((C₁ : ℝ) + 1) * (4 / 16) by field_simp; ring]
    have hfrac : (C₁ : ℝ) / ((C₁ : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [C₁.coe_nonneg]
    nlinarith [hfrac, div_nonneg C₁.coe_nonneg (by positivity : (0:ℝ) ≤ (C₁:ℝ)+1)]
  have hsqrtT : Real.sqrt T ≤ 1 / (8 * ((C₂ : ℝ) + 1)) := by
    rw [show (1 : ℝ) / (8 * ((C₂ : ℝ) + 1)) =
        Real.sqrt ((1 / (8 * ((C₂ : ℝ) + 1))) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    refine Real.sqrt_le_sqrt (le_trans hT_lo ?_)
    rw [div_pow, one_pow, mul_pow]; norm_num
  have harm2 : (C₂ : ℝ) * (2 * Real.sqrt T) ≤ 1 / 4 := by
    have hc2 : (0:ℝ) ≤ (C₂:ℝ) := C₂.coe_nonneg
    calc (C₂ : ℝ) * (2 * Real.sqrt T)
        = 2 * (C₂ : ℝ) * Real.sqrt T := by ring
      _ ≤ 2 * (C₂ : ℝ) * (1 / (8 * ((C₂ : ℝ) + 1))) := by
          apply mul_le_mul_of_nonneg_left hsqrtT (by positivity)
      _ = (C₂ : ℝ) / ((C₂ : ℝ) + 1) * (1 / 4) := by
          have hne : ((C₂ : ℝ) + 1) ≠ 0 := by positivity
          field_simp
          ring
      _ ≤ 1 / 4 := by
          have hfrac : (C₂ : ℝ) / ((C₂ : ℝ) + 1) ≤ 1 := by
            rw [div_le_one (by positivity)]; linarith
          nlinarith [hfrac, div_nonneg hc2 (by positivity : (0:ℝ) ≤ (C₂:ℝ)+1)]
  linarith

private noncomputable def deTurckForceRetractedMapSymm (g₀ g_bg : SmoothRiemannianMetric I M)
    (a : ℕ) (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1) :
    timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T →
      timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T :=
  fun F => nemytskiiMixedForcingMap (I := I) (M := M) g₀ a
    (deTurckSobolevNHa2Symm_lipschitzWith_lipConst (I := I) (M := M) (g₀ := g₀) (g_bg := g_bg)
      a ha_super) hT hT1
    (recenteredBallRetraction (0 : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
      (deTurckForceBallRadiusSymm (I := I) (M := M) g₀ g_bg a ha_super) F)

private theorem deTurckForceRetractedMapSymm_apply (g₀ g_bg : SmoothRiemannianMetric I M)
    (a : ℕ) (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (F : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T) :
    deTurckForceRetractedMapSymm (I := I) (M := M) g₀ g_bg a ha_super hT hT1 F =
      nemytskiiMixedForcingMap (I := I) (M := M) g₀ a
        (deTurckSobolevNHa2Symm_lipschitzWith_lipConst (I := I) (M := M) (g₀ := g₀)
          (g_bg := g_bg) a ha_super) hT hT1
        (recenteredBallRetraction (0 : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
          (deTurckForceBallRadiusSymm (I := I) (M := M) g₀ g_bg a ha_super) F) := rfl

private theorem deTurckForceRetractedMapSymm_eq_of_mem_ball
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (F : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hF : ‖F‖ ≤ deTurckForceBallRadiusSymm (I := I) (M := M) g₀ g_bg a ha_super) :
    deTurckForceRetractedMapSymm (I := I) (M := M) g₀ g_bg a ha_super hT hT1 F =
      nemytskiiMixedForcingMap (I := I) (M := M) g₀ a
        (deTurckSobolevNHa2Symm_lipschitzWith_lipConst (I := I) (M := M) (g₀ := g₀)
          (g_bg := g_bg) a ha_super) hT hT1 F := by
  rw [deTurckForceRetractedMapSymm_apply, recenteredBallRetraction_eq_self_of_mem
    (by rw [Metric.mem_closedBall, dist_zero_right]; exact hF)]

private theorem deTurckForceRetractedMapSymm_dist_le_half
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hTsh : T ≤ deTurckForceShortTimeSymm (I := I) (M := M) g₀ g_bg a ha_super)
    (x y : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T) :
    ‖deTurckForceRetractedMapSymm (I := I) (M := M) g₀ g_bg a ha_super hT hT1 x -
        deTurckForceRetractedMapSymm (I := I) (M := M) g₀ g_bg a ha_super hT hT1 y‖ ≤
      (1 / 2) * ‖x - y‖ := by
  classical
  rw [deTurckForceShortTimeSymm_eq (I := I) (M := M) g₀ g_bg a ha_super] at hTsh
  set hLip := deTurckSobolevNHa2Symm_lipschitzWith_lipConst (I := I) (M := M)
    (g₀ := g₀) (g_bg := g_bg) a ha_super with hLip_def
  set hmix := deTurckSobolevNHa2Symm_mixed_lipschitz_pointwise (I := I) (M := M)
    (g₀ := g₀) (g_bg := g_bg) a ha_super with hmix_def
  set C₁ : ℝ≥0 := hmix.choose with hC₁def
  set C₂ : ℝ≥0 := hmix.choose_spec.choose with hC₂def
  set ρ : ℝ := deTurckForceBallRadiusSymm (I := I) (M := M) g₀ g_bg a ha_super with hρdef
  have hsingle := hmix.choose_spec.choose_spec
  have hρeq : ρ = 1 / (16 * ((C₁ : ℝ) + 1)) := rfl
  have hρpos : 0 < ρ := by rw [hρeq]; positivity
  have hT_lo : T ≤ 1 / (64 * ((C₂ : ℝ) + 1) ^ 2) :=
    le_trans hTsh (le_trans (min_le_right _ _) (min_le_left _ _))
  set ρt := recenteredBallRetraction
    (0 : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T) ρ with hρt_def
  have hρt_norm : ∀ F : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T,
      ‖ρt F‖ ≤ ρ := by
    intro F
    have hmem := recenteredBallRetraction_mapsTo
      (X := timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T) hρpos.le
      (0 : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T) (Set.mem_univ F)
    rw [Metric.mem_closedBall, dist_zero_right] at hmem
    exact hmem
  have hdist := nemytskiiMixedForcingMap_dist_le (I := I) (M := M) g₀ a hLip hsingle
    hT hT1 hρpos.le (ρt x) (ρt y) (hρt_norm x) (hρt_norm y)
  have hretr : ‖ρt x - ρt y‖ ≤ ‖x - y‖ := by
    have h := (recenteredBallRetraction_lipschitzWith hρpos.le
      (0 : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)).dist_le_mul x y
    rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm] at h
    exact h
  have hcoef_nn : (0:ℝ) ≤ (C₁ : ℝ) * (Real.sqrt (1 + T)) * ρ * (1 + T) +
      (C₂ : ℝ) * (2 * Real.sqrt T) := by
    have : (0:ℝ) ≤ 1 + T := by linarith
    positivity
  have hcoef_le : (C₁ : ℝ) * (Real.sqrt (1 + T)) * ρ * (1 + T) +
      (C₂ : ℝ) * (2 * Real.sqrt T) ≤ 1 / 2 := by
    rw [hρeq]
    exact symmForce_contraction_coeff_le_half C₁ C₂ hT.le hT1 hT_lo
  calc ‖deTurckForceRetractedMapSymm (I := I) (M := M) g₀ g_bg a ha_super hT hT1 x -
          deTurckForceRetractedMapSymm (I := I) (M := M) g₀ g_bg a ha_super hT hT1 y‖
      = ‖nemytskiiMixedForcingMap (I := I) (M := M) g₀ a hLip hT hT1 (ρt x) -
          nemytskiiMixedForcingMap (I := I) (M := M) g₀ a hLip hT hT1 (ρt y)‖ := rfl
    _ ≤ ((C₁ : ℝ) * (Real.sqrt (1 + T)) * ρ * (1 + T) + (C₂ : ℝ) * (2 * Real.sqrt T)) *
          ‖ρt x - ρt y‖ := hdist
    _ ≤ ((C₁ : ℝ) * (Real.sqrt (1 + T)) * ρ * (1 + T) + (C₂ : ℝ) * (2 * Real.sqrt T)) *
          ‖x - y‖ := mul_le_mul_of_nonneg_left hretr hcoef_nn
    _ ≤ (1 / 2) * ‖x - y‖ := mul_le_mul_of_nonneg_right hcoef_le (norm_nonneg _)

private theorem deTurckForceRetractedMapSymm_lipschitzWith
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hTsh : T ≤ deTurckForceShortTimeSymm (I := I) (M := M) g₀ g_bg a ha_super) :
    LipschitzWith (1 / 2 : ℝ≥0)
      (deTurckForceRetractedMapSymm (I := I) (M := M) g₀ g_bg a ha_super hT hT1) := by
  refine LipschitzWith.of_dist_le_mul (fun x y => ?_)
  rw [dist_eq_norm, dist_eq_norm, show ((1 / 2 : ℝ≥0) : ℝ) = 1 / 2 by norm_num]
  exact deTurckForceRetractedMapSymm_dist_le_half (I := I) (M := M) g₀ g_bg a ha_super
    hT hT1 hTsh x y

private theorem nemytskiiMixedForcingMapSymm_norm_le_ballRadius
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hTsh : T ≤ deTurckForceShortTimeSymm (I := I) (M := M) g₀ g_bg a ha_super)
    (G : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hG : ‖G‖ ≤ deTurckForceBallRadiusSymm (I := I) (M := M) g₀ g_bg a ha_super) :
    ‖nemytskiiMixedForcingMap (I := I) (M := M) g₀ a
        (deTurckSobolevNHa2Symm_lipschitzWith_lipConst (I := I) (M := M) (g₀ := g₀) (g_bg := g_bg)
          a ha_super) hT hT1 G‖ ≤
      deTurckForceBallRadiusSymm (I := I) (M := M) g₀ g_bg a ha_super := by
  classical
  rw [deTurckForceShortTimeSymm_eq (I := I) (M := M) g₀ g_bg a ha_super] at hTsh
  set hLip := deTurckSobolevNHa2Symm_lipschitzWith_lipConst (I := I) (M := M)
    (g₀ := g₀) (g_bg := g_bg) a ha_super with hLip_def
  set hmix := deTurckSobolevNHa2Symm_mixed_lipschitz_pointwise (I := I) (M := M)
    (g₀ := g₀) (g_bg := g_bg) a ha_super with hmix_def
  set C₁ : ℝ≥0 := hmix.choose with hC₁def
  set C₂ : ℝ≥0 := hmix.choose_spec.choose with hC₂def
  set ρ : ℝ := deTurckForceBallRadiusSymm (I := I) (M := M) g₀ g_bg a ha_super with hρdef
  have hsingle := hmix.choose_spec.choose_spec
  have hρeq : ρ = 1 / (16 * ((C₁ : ℝ) + 1)) := rfl
  have hρpos : 0 < ρ := by rw [hρeq]; positivity
  set M₀ : ℝ := ‖deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
    (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))‖ with hM₀def
  have hM₀ : 0 ≤ M₀ := norm_nonneg _
  have hT_lo : T ≤ 1 / (64 * ((C₂ : ℝ) + 1) ^ 2) :=
    le_trans hTsh (le_trans (min_le_right _ _) (min_le_left _ _))
  have hT_stay : T ≤ (ρ / (2 * (M₀ + 1))) ^ 2 :=
    le_trans hTsh (le_trans (min_le_right _ _) (min_le_right _ _))
  have hcoef_nn : (0:ℝ) ≤ (C₁ : ℝ) * (Real.sqrt (1 + T)) * ρ * (1 + T) +
      (C₂ : ℝ) * (2 * Real.sqrt T) := by
    have : (0:ℝ) ≤ 1 + T := by linarith
    positivity
  have hcoef_le : (C₁ : ℝ) * (Real.sqrt (1 + T)) * ρ * (1 + T) +
      (C₂ : ℝ) * (2 * Real.sqrt T) ≤ 1 / 2 := by
    rw [hρeq]
    exact symmForce_contraction_coeff_le_half C₁ C₂ hT.le hT1 hT_lo
  have hsqrtTM : Real.sqrt T * M₀ ≤ ρ / 2 := by
    have hsqrtT_le : Real.sqrt T ≤ ρ / (2 * (M₀ + 1)) := by
      rw [show ρ / (2 * (M₀ + 1)) = Real.sqrt ((ρ / (2 * (M₀ + 1))) ^ 2) from
        (Real.sqrt_sq (by positivity)).symm]
      exact Real.sqrt_le_sqrt hT_stay
    calc Real.sqrt T * M₀ ≤ (ρ / (2 * (M₀ + 1))) * M₀ :=
          mul_le_mul_of_nonneg_right hsqrtT_le hM₀
      _ ≤ (ρ / (2 * (M₀ + 1))) * (M₀ + 1) := by
          apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = ρ / 2 := by
          have hne : (M₀ + 1) ≠ 0 := by positivity
          field_simp
  have hΨ0 : ‖nemytskiiMixedForcingMap (I := I) (M := M) g₀ a hLip hT hT1
      (0 : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)‖ ≤ Real.sqrt T * M₀ := by
    rw [nemytskiiMixedForcingMap_apply,
      maxRegDuhamelSolField_zero_zero (I := I) (M := M) (g₀ := g₀) hT hT1]
    refine timeL2_norm_le_of_ae_bound _ (by positivity) ?_
    have hcoe := nemytskii_coeFn (I := I) (M := M) hLip
      (0 : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) T)
    have hzero := Lp.coeFn_zero (E := tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
      (p := 2) (μ := timeMeasure T)
    filter_upwards [hcoe, hzero] with t ht htz
    rw [ht, htz, Pi.zero_apply]
  have hball := nemytskiiMixedForcingMap_dist_le (I := I) (M := M) g₀ a hLip hsingle
    hT hT1 hρpos.le G (0 : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T) hG
    (by rw [norm_zero]; exact hρpos.le)
  rw [sub_zero] at hball
  calc ‖nemytskiiMixedForcingMap (I := I) (M := M) g₀ a hLip hT hT1 G‖
      = ‖(nemytskiiMixedForcingMap (I := I) (M := M) g₀ a hLip hT hT1 G -
            nemytskiiMixedForcingMap (I := I) (M := M) g₀ a hLip hT hT1
              (0 : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)) +
          nemytskiiMixedForcingMap (I := I) (M := M) g₀ a hLip hT hT1
            (0 : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)‖ := by
        rw [sub_add_cancel]
    _ ≤ ‖nemytskiiMixedForcingMap (I := I) (M := M) g₀ a hLip hT hT1 G -
            nemytskiiMixedForcingMap (I := I) (M := M) g₀ a hLip hT hT1
              (0 : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)‖ +
          ‖nemytskiiMixedForcingMap (I := I) (M := M) g₀ a hLip hT hT1
            (0 : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)‖ := norm_add_le _ _
    _ ≤ ((C₁ : ℝ) * (Real.sqrt (1 + T)) * ρ * (1 + T) + (C₂ : ℝ) * (2 * Real.sqrt T)) * ‖G‖ +
          Real.sqrt T * M₀ := add_le_add hball hΨ0
    _ ≤ (1 / 2) * ρ + ρ / 2 := by
        refine add_le_add ?_ hsqrtTM
        calc ((C₁ : ℝ) * (Real.sqrt (1 + T)) * ρ * (1 + T) + (C₂ : ℝ) * (2 * Real.sqrt T)) * ‖G‖
            ≤ ((C₁ : ℝ) * (Real.sqrt (1 + T)) * ρ * (1 + T) + (C₂ : ℝ) * (2 * Real.sqrt T)) * ρ :=
              mul_le_mul_of_nonneg_left hG hcoef_nn
          _ ≤ (1 / 2) * ρ := mul_le_mul_of_nonneg_right hcoef_le hρpos.le
    _ = ρ := by ring

private theorem galerkinForcing_norm_le_ballRadiusSymm
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hTT₀ : T ≤ deTurckForceShortTimeSymm (I := I) (M := M) g₀ g_bg a ha_super)
    (U : ℕ → ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ)
    (hUinit : ∀ N, ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N, U N 0 i = 0)
    (hUcont : ∀ N, ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
      ContinuousOn (fun t => U N t i) (Set.Icc (0 : ℝ) T))
    (hUderiv : ∀ N, ∀ t ∈ Set.Ico (0 : ℝ) T,
      ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
        HasDerivWithinAt (fun r => U N r i)
          (-(TensorEigenIdx.lambda (I := I) (M := M) i) * U N t i +
            deTurckGalerkinForcingSymm (I := I) (M := M) g₀ g_bg a U N t i)
          (Set.Ici t) t)
    (N : ℕ) :
    ‖nemytskii (I := I) (M := M)
        (deTurckSobolevNHa2Symm_lipschitzWith_lipConst (I := I) (M := M) (g₀ := g₀) (g_bg := g_bg)
          a ha_super)
        (TimeSobolev.ofContinuousOn
          (continuousOn_galerkinForcing_field (I := I) (M := M) g₀ a U N (hUcont N)))‖ ≤
      deTurckForceBallRadiusSymm (I := I) (M := M) g₀ g_bg a ha_super := by
  classical
  have h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2
  haveI hcount : Countable (TensorEigenIdx (I := I) (M := M) g₀ 0 2) :=
    countable_tensorEigenIdx (I := I) (M := M) h_compact
  set hLipC := deTurckSobolevNHa2Symm_lipschitzWith_lipConst (I := I) (M := M)
    (g₀ := g₀) (g_bg := g_bg) a ha_super with hLipC_def
  set ρ : ℝ := deTurckForceBallRadiusSymm (I := I) (M := M) g₀ g_bg a ha_super with hρdef
  have hρpos : 0 < ρ := by rw [hρdef, deTurckForceBallRadiusSymm]; positivity
  set VN := TimeSobolev.ofContinuousOn
    (continuousOn_galerkinForcing_field (I := I) (M := M) g₀ a U N (hUcont N)) with hVN_def
  set Ψ' := deTurckForceRetractedMapSymm (I := I) (M := M) g₀ g_bg a ha_super hT hT1 with hΨ'_def
  have hκlt : (1 / 2 : ℝ≥0) < 1 := by rw [← NNReal.coe_lt_coe]; push_cast; norm_num
  have hΨ'_lip : LipschitzWith (1 / 2 : ℝ≥0) Ψ' :=
    deTurckForceRetractedMapSymm_lipschitzWith (I := I) (M := M) g₀ g_bg a ha_super hT hT1 hTT₀
  have hPΦ : ContractingWith (1 / 2 : ℝ≥0)
      (⇑(timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N) ∘ Ψ') := by
    refine ⟨hκlt, LipschitzWith.of_dist_le_mul (fun x y => ?_)⟩
    rw [Function.comp_apply, Function.comp_apply,
      show ((1 / 2 : ℝ≥0) : ℝ) = 1 / 2 by norm_num, dist_eq_norm, dist_eq_norm]
    calc ‖timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N (Ψ' x) -
            timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N (Ψ' y)‖
        = ‖timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N (Ψ' x - Ψ' y)‖ := by rw [← map_sub]
      _ ≤ ‖Ψ' x - Ψ' y‖ := by
          refine le_trans ((timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N).le_opNorm _) ?_
          exact mul_le_of_le_one_left (norm_nonneg _)
            (norm_timeL2EigenProj_le_one (I := I) (M := M) g₀ (a : ℝ) T N)
      _ ≤ (1 / 2) * ‖x - y‖ := by
          have hd := hΨ'_lip.dist_le_mul x y
          rw [dist_eq_norm, dist_eq_norm, show ((1 / 2 : ℝ≥0) : ℝ) = 1 / 2 by norm_num] at hd
          exact hd
  set yN := ContractingWith.fixedPoint
    (⇑(timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N) ∘ Ψ') hPΦ with hyN_def
  have hyN_fix : (⇑(timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N) ∘ Ψ') yN = yN :=
    ContractingWith.fixedPoint_isFixedPt hPΦ
  have hΨ'stay : ∀ z, ‖Ψ' z‖ ≤ ρ := by
    intro z
    rw [hΨ'_def, deTurckForceRetractedMapSymm_apply]
    refine nemytskiiMixedForcingMapSymm_norm_le_ballRadius (I := I) (M := M) g₀ g_bg a ha_super
      hT hT1 hTT₀ _ ?_
    have hmem := recenteredBallRetraction_mapsTo
      (X := timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T) hρpos.le
      (0 : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T) (Set.mem_univ z)
    rw [Metric.mem_closedBall, dist_zero_right] at hmem
    exact hmem
  have hyN_norm : ‖yN‖ ≤ ρ := by
    have h1 := hyN_fix
    rw [Function.comp_apply] at h1
    calc ‖yN‖ = ‖timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N (Ψ' yN)‖ := by rw [h1]
      _ ≤ ‖Ψ' yN‖ := by
          refine le_trans ((timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N).le_opNorm _) ?_
          exact mul_le_of_le_one_left (norm_nonneg _)
            (norm_timeL2EigenProj_le_one (I := I) (M := M) g₀ (a : ℝ) T N)
      _ ≤ ρ := hΨ'stay yN
  set vN := maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
    (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) yN with hvN_def
  have hΨ'yN : Ψ' yN = nemytskiiMixedForcingMap (I := I) (M := M) g₀ a hLipC hT hT1 yN := by
    rw [hΨ'_def,
      deTurckForceRetractedMapSymm_eq_of_mem_ball (I := I) (M := M) g₀ g_bg a ha_super hT hT1 yN hyN_norm]
  have hyN_eq : yN = timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N
      (nemytskii (I := I) (M := M) hLipC vN) := by
    have h1 := hyN_fix
    rw [Function.comp_apply, hΨ'yN, nemytskiiMixedForcingMap_apply] at h1
    exact h1.symm
  set W : ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ :=
    fun t i => perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
      (fun s => (timeModeCoeff (I := I) (M := M) yN i) s) t with hW_def
  have hvN_coeff : ∀ i, (fun t => (vN t).coeff i) =ᵐ[timeMeasure T] (fun t => W t i) := by
    intro i
    exact timeModeCoeff_eq_perModeConv_forcing (I := I) (M := M) (h_compact := h_compact)
      (a := (a : ℝ)) hT hT1 yN i
  have hyN_mode : ∀ j, ⇑(timeModeCoeff (I := I) (M := M) yN j) =ᵐ[timeMeasure T]
      (fun s => if j ∈ eigenIdxFinset (I := I) (M := M) g₀ N then
        (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a (vN s)).coeff j else 0) := by
    intro j
    have hco := timeModeCoeff_coeFn (I := I) (M := M)
      (timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N (nemytskii (I := I) (M := M) hLipC vN)) j
    have hproj : ⇑(timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N
          (nemytskii (I := I) (M := M) hLipC vN)) =ᵐ[timeMeasure T]
        (fun s => spatialEigenProj (I := I) (M := M) g₀ (a : ℝ) N
          ((nemytskii (I := I) (M := M) hLipC vN) s)) :=
      ContinuousLinearMap.coeFn_compLpL _ (nemytskii (I := I) (M := M) hLipC vN)
    have hX := nemytskii_coeFn (I := I) (M := M) hLipC vN
    rw [hyN_eq]
    filter_upwards [hco, hproj, hX] with s hs1 hs2 hs3
    rw [hs1, hs2, spatialEigenProj_apply, finiteEigenComboHs_coeff]
    by_cases hj : j ∈ eigenIdxFinset (I := I) (M := M) g₀ N
    · rw [if_pos hj, if_pos hj, hs3]
    · rw [if_neg hj, if_neg hj]
  have hvN_eq_combo : ∀ᵐ s ∂(timeMeasure T),
      vN s = finiteEigenComboHs (I := I) (M := M) g₀
        (eigenIdxFinset (I := I) (M := M) g₀ N) (W s) ((a : ℝ) + 2) := by
    have hall : ∀ᵐ s ∂(timeMeasure T), ∀ j,
        (vN s).coeff j = (finiteEigenComboHs (I := I) (M := M) g₀
          (eigenIdxFinset (I := I) (M := M) g₀ N) (W s) ((a : ℝ) + 2)).coeff j := by
      refine ae_all_iff.2 (fun j => ?_)
      by_cases hj : j ∈ eigenIdxFinset (I := I) (M := M) g₀ N
      · filter_upwards [hvN_coeff j] with s hs
        rw [hs, finiteEigenComboHs_coeff, if_pos hj]
      · filter_upwards [hvN_coeff j, hyN_mode j, ae_restrict_mem (μ := volume) measurableSet_Icc]
          with s hs hmode humem
        have humem' : s ∈ Set.Icc (0 : ℝ) T := humem
        rw [hs, finiteEigenComboHs_coeff, if_neg hj]
        change perModeConv (TensorEigenIdx.lambda (I := I) (M := M) j)
          (fun u => (timeModeCoeff (I := I) (M := M) yN j) u) s = 0
        have hcongr : perModeConv (TensorEigenIdx.lambda (I := I) (M := M) j)
              (fun u => (timeModeCoeff (I := I) (M := M) yN j) u) s =
            perModeConv (TensorEigenIdx.lambda (I := I) (M := M) j) (fun _ => (0 : ℝ)) s := by
          refine perModeConv_timeL2_congr _ ?_ humem'
          filter_upwards [hyN_mode j] with u hu
          rw [hu, if_neg hj]
        rw [hcongr]; unfold perModeConv; simp
    filter_upwards [hall] with s hs
    apply tensorHs.ext
    funext j
    exact hs j
  have hWcont : ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
      ContinuousOn (fun t => W t i) (Set.Icc (0 : ℝ) T) := by
    intro i _
    exact continuousOn_perModeConv_timeL2 (TensorEigenIdx.lambda (I := I) (M := M) i)
      (timeModeCoeff (I := I) (M := M) yN i) hT.le
  have hWderiv : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
      HasDerivWithinAt (fun r => W r i)
        (-(TensorEigenIdx.lambda (I := I) (M := M) i) * W t i +
          (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
            (finiteEigenComboHs (I := I) (M := M) g₀
              (eigenIdxFinset (I := I) (M := M) g₀ N) (W t) ((a : ℝ) + 2))).coeff i)
        (Set.Ici t) t := by
    intro t ht i hi
    set fForce : ℝ → ℝ := Set.IccExtend hT.le (fun p : ↑(Set.Icc (0 : ℝ) T) =>
      (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
        (finiteEigenComboHs (I := I) (M := M) g₀
          (eigenIdxFinset (I := I) (M := M) g₀ N) (W p.1) ((a : ℝ) + 2))).coeff i) with hfForce_def
    have hg_cont : ContinuousOn (fun s => (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
        (finiteEigenComboHs (I := I) (M := M) g₀
          (eigenIdxFinset (I := I) (M := M) g₀ N) (W s) ((a : ℝ) + 2))).coeff i)
        (Set.Icc (0 : ℝ) T) := by
      refine (continuousOn_galerkinForcingSymm (I := I) (M := M) g₀ g_bg a ha_super
        (fun _ => W) N hWcont i).congr (fun s _ => ?_)
      rw [deTurckGalerkinForcingSymm_apply, if_pos hi]
    have hfForce_cont : Continuous fForce := Continuous.Icc_extend' hg_cont.restrict
    have hfForce_mem : ∀ {x : ℝ}, x ∈ Set.Icc (0 : ℝ) T →
        fForce x = (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
          (finiteEigenComboHs (I := I) (M := M) g₀
            (eigenIdxFinset (I := I) (M := M) g₀ N) (W x) ((a : ℝ) + 2))).coeff i := by
      intro x hx
      rw [hfForce_def, Set.IccExtend_of_mem hT.le _ hx]
    have hWrep : ∀ s ∈ Set.Icc (0 : ℝ) T,
        W s i = perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) fForce s := by
      intro s hs
      change perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
        (fun u => (timeModeCoeff (I := I) (M := M) yN i) u) s =
          perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) fForce s
      refine perModeConv_timeL2_congr (TensorEigenIdx.lambda (I := I) (M := M) i) ?_ hs
      filter_upwards [hyN_mode i, hvN_eq_combo, ae_restrict_mem (μ := volume) measurableSet_Icc]
        with u hu1 hu2 humem'
      have humem : u ∈ Set.Icc (0 : ℝ) T := humem'
      rw [hu1, if_pos hi, hu2, hfForce_mem humem]
    have hIcc_mem : Set.Icc (0 : ℝ) T ∈ 𝓝[Set.Ici t] t := by
      have h1 : Set.Ici t ∩ Set.Iic T ∈ 𝓝[Set.Ici t] t :=
        inter_mem_nhdsWithin (Set.Ici t) (Iic_mem_nhds ht.2)
      rw [Set.Ici_inter_Iic] at h1
      exact Filter.mem_of_superset h1 (Set.Icc_subset_Icc_left ht.1)
    have htIcc : t ∈ Set.Icc (0 : ℝ) T := ⟨ht.1, ht.2.le⟩
    have hWi_eqEv : (fun r => W r i) =ᶠ[𝓝[Set.Ici t] t]
        (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) fForce) :=
      Filter.eventuallyEq_of_mem hIcc_mem (fun r hr => hWrep r hr)
    have hderiv_pmc : HasDerivWithinAt (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) fForce)
        (fForce t - TensorEigenIdx.lambda (I := I) (M := M) i *
          perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) fForce t) (Set.Ici t) t :=
      (perModeConv_hasDerivAt (TensorEigenIdx.lambda (I := I) (M := M) i) hfForce_cont t).hasDerivWithinAt
    have hderiv_W := hderiv_pmc.congr_of_eventuallyEq hWi_eqEv (hWrep t htIcc)
    have hval_eq : fForce t - TensorEigenIdx.lambda (I := I) (M := M) i *
          perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) fForce t =
        -(TensorEigenIdx.lambda (I := I) (M := M) i) * W t i +
          (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
            (finiteEigenComboHs (I := I) (M := M) g₀
              (eigenIdxFinset (I := I) (M := M) g₀ N) (W t) ((a : ℝ) + 2))).coeff i := by
      rw [hfForce_mem htIcc, ← hWrep t htIcc]; ring
    rw [hval_eq] at hderiv_W
    exact hderiv_W
  have hUderivN : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
      HasDerivWithinAt (fun r => U N r i)
        (-(TensorEigenIdx.lambda (I := I) (M := M) i) * U N t i +
          (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
            (finiteEigenComboHs (I := I) (M := M) g₀
              (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t) ((a : ℝ) + 2))).coeff i)
        (Set.Ici t) t := by
    intro t ht i hi
    have hd := hUderiv N t ht i hi
    rwa [deTurckGalerkinForcingSymm_apply, if_pos hi] at hd
  have hinit : ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N, U N 0 i = W 0 i := by
    intro i hi
    rw [hUinit N i hi]
    change (0 : ℝ) = perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
      (fun s => (timeModeCoeff (I := I) (M := M) yN i) s) 0
    rw [perModeConv_zero_left]
  have hVN_eq_vN : VN = vN := by
    refine timeModeCoeff_injective (I := I) (M := M) h_compact (fun i => ?_)
    refine Lp.ext ?_
    have hL := timeModeCoeff_coeFn (I := I) (M := M) VN i
    have hVco : ⇑VN =ᵐ[timeMeasure T]
        (fun t => finiteEigenComboHs (I := I) (M := M) g₀
          (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t) ((a : ℝ) + 2)) :=
      TimeSobolev.coeFn_ofContinuousOn _
    have hR := timeModeCoeff_coeFn (I := I) (M := M) vN i
    refine hL.trans (Filter.EventuallyEq.trans ?_ (hR.trans (hvN_coeff i)).symm)
    by_cases hi : i ∈ eigenIdxFinset (I := I) (M := M) g₀ N
    · filter_upwards [hVco, ae_restrict_mem (μ := volume) measurableSet_Icc] with t htV htmem
      have htmem' : t ∈ Set.Icc (0 : ℝ) T := htmem
      rw [htV, finiteEigenComboHs_coeff, if_pos hi]
      exact galerkinODE_solution_uniqueSymm (I := I) (M := M) g₀ g_bg a ha_super hT
        (eigenIdxFinset (I := I) (M := M) g₀ N) (U N) W (hUcont N) hUderivN hWcont hWderiv
        hinit i hi htmem'
    · filter_upwards [hVco, hyN_mode i, ae_restrict_mem (μ := volume) measurableSet_Icc]
        with t htV hmode htmem
      have htmem' : t ∈ Set.Icc (0 : ℝ) T := htmem
      rw [htV, finiteEigenComboHs_coeff, if_neg hi]
      change (0 : ℝ) = perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
        (fun s => (timeModeCoeff (I := I) (M := M) yN i) s) t
      have hcongr : perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun s => (timeModeCoeff (I := I) (M := M) yN i) s) t =
          perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (fun _ => (0 : ℝ)) t := by
        refine perModeConv_timeL2_congr _ ?_ htmem'
        filter_upwards [hyN_mode i] with s hs
        rw [hs, if_neg hi]
      rw [hcongr]; unfold perModeConv; simp
  have hfinal : nemytskii (I := I) (M := M) hLipC VN = Ψ' yN := by
    rw [hVN_eq_vN, hΨ'yN, nemytskiiMixedForcingMap_apply]
  rw [hfinal]
  exact hΨ'stay yN

private theorem galerkinForcing_tendsto_force_timeL2_ofProjFixedPointSymm
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hTT₀ : T ≤ deTurckForceShortTimeSymm (I := I) (M := M) g₀ g_bg a ha_super)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
    (hgforce : ‖gforce‖ ≤ deTurckForceBallRadiusSymm (I := I) (M := M) g₀ g_bg a ha_super)
    (U : ℕ → ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ)
    (hUinit : ∀ N, ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N, U N 0 i = 0)
    (hUcont : ∀ N, ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
      ContinuousOn (fun t => U N t i) (Set.Icc (0 : ℝ) T))
    (hUderiv : ∀ N, ∀ t ∈ Set.Ico (0 : ℝ) T,
      ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
        HasDerivWithinAt (fun r => U N r i)
          (-(TensorEigenIdx.lambda (I := I) (M := M) i) * U N t i +
            deTurckGalerkinForcingSymm (I := I) (M := M) g₀ g_bg a U N t i)
          (Set.Ici t) t)
    (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2) :
    Tendsto (fun N => TimeSobolev.ofContinuousOn
        (continuousOn_galerkinForcingSymm (I := I) (M := M) g₀ g_bg a ha_super U N (hUcont N) i))
      atTop (𝓝 (timeModeCoeff (I := I) (M := M) gforce i)) := by
  classical
  obtain ⟨N₀, hN₀⟩ := exists_mem_eigenIdxFinset (I := I) (M := M) g₀ i
  obtain ⟨K, hK⟩ := deTurckSobolevNHa2Symm_lipschitzWith (I := I) (M := M) g₀ g_bg a ha_super
  have hcontField : ∀ N, ContinuousOn
      (fun t => deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
        (finiteEigenComboHs (I := I) (M := M) g₀ (eigenIdxFinset (I := I) (M := M) g₀ N)
          (U N t) ((a : ℝ) + 2))) (Set.Icc (0 : ℝ) T) :=
    fun N => hK.continuous.comp_continuousOn
      (continuousOn_galerkinForcing_field (I := I) (M := M) g₀ a U N (hUcont N))
  have hfield : Tendsto (fun N => TimeSobolev.ofContinuousOn (hcontField N)) atTop (𝓝 gforce) := by
    have hTsh : T ≤ deTurckForceShortTimeSymm (I := I) (M := M) g₀ g_bg a ha_super := hTT₀
    set Ψ' := deTurckForceRetractedMapSymm (I := I) (M := M) g₀ g_bg a ha_super hT hT1 with hΨ'_def
    have hκcoe : ((1 / 2 : ℝ≥0) : ℝ) = 1 / 2 := by norm_num
    have hκlt : (1 / 2 : ℝ≥0) < 1 := by
      rw [← NNReal.coe_lt_coe, hκcoe, NNReal.coe_one]; norm_num
    have hΨ'_lip : LipschitzWith (1 / 2 : ℝ≥0) Ψ' :=
      deTurckForceRetractedMapSymm_lipschitzWith (I := I) (M := M) g₀ g_bg a ha_super hT hT1 hTsh
    have hcontr : ContractingWith (1 / 2 : ℝ≥0) Ψ' := ⟨hκlt, hΨ'_lip⟩
    have hPtendsto : ∀ x, Tendsto (fun N => timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N x)
        atTop (𝓝 x) := fun x => timeL2EigenProj_tendsto (I := I) (M := M) g₀ (a : ℝ) T x
    have hPΦ : ∀ N, ContractingWith (1 / 2 : ℝ≥0)
        (⇑(timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N) ∘ Ψ') := by
      intro N
      refine ⟨hκlt, LipschitzWith.of_dist_le_mul (fun x y => ?_)⟩
      rw [Function.comp_apply, Function.comp_apply, hκcoe, dist_eq_norm, dist_eq_norm]
      calc ‖timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N (Ψ' x) -
              timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N (Ψ' y)‖
          = ‖timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N (Ψ' x - Ψ' y)‖ := by rw [← map_sub]
        _ ≤ ‖Ψ' x - Ψ' y‖ := by
            refine le_trans ((timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N).le_opNorm _) ?_
            exact mul_le_of_le_one_left (norm_nonneg _)
              (norm_timeL2EigenProj_le_one (I := I) (M := M) g₀ (a : ℝ) T N)
        _ ≤ (1 / 2) * ‖x - y‖ :=
            deTurckForceRetractedMapSymm_dist_le_half (I := I) (M := M) g₀ g_bg a ha_super hT hT1 hTsh x y
    have hFP := DifferentialGeometry.Analysis.tendsto_fixedPoint_of_projected_contraction
      hcontr (fun N => timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N) hPtendsto hPΦ
    have hgforce_fix : Ψ' gforce = gforce := by
      rw [hΨ'_def, deTurckForceRetractedMapSymm_eq_of_mem_ball (I := I) (M := M) g₀ g_bg a ha_super
        hT hT1 gforce hgforce, nemytskiiMixedForcingMap_apply]
      refine Lp.ext ?_
      exact (nemytskii_coeFn (I := I) (M := M)
        (deTurckSobolevNHa2Symm_lipschitzWith_lipConst (I := I) (M := M) (g₀ := g₀) (g_bg := g_bg) a ha_super)
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce)).trans hforce.symm
    have hFstar_eq : ContractingWith.fixedPoint Ψ' hcontr = gforce :=
      (ContractingWith.fixedPoint_unique hcontr hgforce_fix).symm
    rw [hFstar_eq] at hFP
    have hgforceN_eq : ∀ N, TimeSobolev.ofContinuousOn (hcontField N) =
        nemytskii (I := I) (M := M)
          (deTurckSobolevNHa2Symm_lipschitzWith_lipConst (I := I) (M := M) (g₀ := g₀) (g_bg := g_bg)
            a ha_super)
          (TimeSobolev.ofContinuousOn
            (continuousOn_galerkinForcing_field (I := I) (M := M) g₀ a U N (hUcont N))) := by
      intro N
      refine Lp.ext ?_
      have h1 := TimeSobolev.coeFn_ofContinuousOn (hcontField N)
      have h2 := nemytskii_coeFn (I := I) (M := M)
        (deTurckSobolevNHa2Symm_lipschitzWith_lipConst (I := I) (M := M) (g₀ := g₀) (g_bg := g_bg) a ha_super)
        (TimeSobolev.ofContinuousOn
          (continuousOn_galerkinForcing_field (I := I) (M := M) g₀ a U N (hUcont N)))
      have h3 := TimeSobolev.coeFn_ofContinuousOn
        (continuousOn_galerkinForcing_field (I := I) (M := M) g₀ a U N (hUcont N))
      filter_upwards [h1, h2, h3] with t ht1 ht2 ht3
      rw [ht1, ht2, ht3]
    have hball : ∀ N, ‖TimeSobolev.ofContinuousOn (hcontField N)‖ ≤
        deTurckForceBallRadiusSymm (I := I) (M := M) g₀ g_bg a ha_super := by
      intro N
      rw [hgforceN_eq N]
      exact galerkinForcing_norm_le_ballRadiusSymm (I := I) (M := M) g₀ g_bg a ha_super hT hT1 hTsh U
        hUinit hUcont hUderiv N
    have hxN_ball : ∀ N, ‖timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N
        (TimeSobolev.ofContinuousOn (hcontField N))‖ ≤
        deTurckForceBallRadiusSymm (I := I) (M := M) g₀ g_bg a ha_super := by
      intro N
      refine le_trans ?_ (hball N)
      refine le_trans ((timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N).le_opNorm _) ?_
      exact mul_le_of_le_one_left (norm_nonneg _)
        (norm_timeL2EigenProj_le_one (I := I) (M := M) g₀ (a : ℝ) T N)
    have hgforceN_Ψ' : ∀ N, TimeSobolev.ofContinuousOn (hcontField N) =
        Ψ' (timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N
          (TimeSobolev.ofContinuousOn (hcontField N))) := by
      intro N
      rw [hΨ'_def, deTurckForceRetractedMapSymm_eq_of_mem_ball (I := I) (M := M) g₀ g_bg a ha_super
        hT hT1 _ (hxN_ball N), nemytskiiMixedForcingMap_apply, hgforceN_eq N]
      congr 1
      exact galerkinForcing_field_eq_maxRegDuhamel_projTruncationSymm (I := I) (M := M) g₀ g_bg a
        ha_super hT hT1 U hUinit hUcont hUderiv N
    have hxN_fix : ∀ N, ContractingWith.fixedPoint
          (⇑(timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N) ∘ Ψ') (hPΦ N) =
        timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N
          (TimeSobolev.ofContinuousOn (hcontField N)) := by
      intro N
      refine (ContractingWith.fixedPoint_unique (hPΦ N) ?_).symm
      change (⇑(timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N) ∘ Ψ')
          (timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N
            (TimeSobolev.ofContinuousOn (hcontField N))) =
        timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N
          (TimeSobolev.ofContinuousOn (hcontField N))
      rw [Function.comp_apply, ← hgforceN_Ψ' N]
    have hxN_tendsto : Tendsto (fun N => timeL2EigenProj (I := I) (M := M) g₀ (a : ℝ) T N
        (TimeSobolev.ofContinuousOn (hcontField N))) atTop (𝓝 gforce) :=
      hFP.congr (fun N => hxN_fix N)
    have hcomp := (hΨ'_lip.continuous.tendsto gforce).comp hxN_tendsto
    rw [hgforce_fix] at hcomp
    exact hcomp.congr (fun N => (hgforceN_Ψ' N).symm)
  have hmode : Tendsto
      (fun N => timeModeCoeff (I := I) (M := M) (TimeSobolev.ofContinuousOn (hcontField N)) i)
      atTop (𝓝 (timeModeCoeff (I := I) (M := M) gforce i)) :=
    (((tensorHsCoeffL (I := I) (M := M) (a := (a : ℝ)) i).compLpL 2 (timeMeasure T)).continuous.tendsto
      gforce).comp hfield
  refine hmode.congr' ?_
  filter_upwards [eventually_ge_atTop N₀] with N hN
  have hi : i ∈ eigenIdxFinset (I := I) (M := M) g₀ N :=
    eigenIdxFinset_mono (I := I) (M := M) g₀ hN hN₀
  refine Lp.ext ?_
  have hL := timeModeCoeff_coeFn (I := I) (M := M)
    (TimeSobolev.ofContinuousOn (hcontField N)) i
  have hF := TimeSobolev.coeFn_ofContinuousOn (hcontField N)
  have hG := TimeSobolev.coeFn_ofContinuousOn
    (continuousOn_galerkinForcingSymm (I := I) (M := M) g₀ g_bg a ha_super U N (hUcont N) i)
  refine hL.trans (Filter.EventuallyEq.trans ?_ hG.symm)
  filter_upwards [hF] with t ht
  rw [ht, deTurckGalerkinForcingSymm_apply, if_pos hi]

theorem galerkinSol_tendsto_solField_perModeConvSymm
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
    (hgforce : ‖gforce‖ ≤ deTurckForceBallRadiusSymm (I := I) (M := M) g₀ g_bg a (by omega))
    (U : ℕ → ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ)
    (hUinit : ∀ N, ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N, U N 0 i = 0)
    (hUcont : ∀ N, ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
      ContinuousOn (fun t => U N t i) (Set.Icc (0 : ℝ) T))
    (hUderiv : ∀ N, ∀ t ∈ Set.Ico (0 : ℝ) T,
      ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
        HasDerivWithinAt (fun r => U N r i)
          (-(TensorEigenIdx.lambda (I := I) (M := M) i) * U N t i +
            deTurckGalerkinForcingSymm (I := I) (M := M) g₀ g_bg a U N t i)
          (Set.Ici t) t)
    (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) T) :
    Tendsto (fun N => U N t i) atTop
      (𝓝 (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
        (fun s => (timeModeCoeff (I := I) (M := M) gforce i) s) t)) := by
  classical
  set lam := TensorEigenIdx.lambda (I := I) (M := M) i with hlam_def
  have hlam_nn : 0 ≤ lam := tensor_lambda_nonneg (I := I) (M := M) i
  have hcontF : ∀ N, ContinuousOn
      (fun s => deTurckGalerkinForcingSymm (I := I) (M := M) g₀ g_bg a U N s i)
      (Set.Icc (0 : ℝ) T) :=
    fun N => continuousOn_galerkinForcingSymm (I := I) (M := M) g₀ g_bg a (by omega) U N
      (hUcont N) i
  set fseq : ℕ → timeL2 ℝ T := fun N => TimeSobolev.ofContinuousOn (hcontF N) with hfseq_def
  have hposit : Tendsto fseq atTop (𝓝 (timeModeCoeff (I := I) (M := M) gforce i)) :=
    galerkinForcing_tendsto_force_timeL2_ofProjFixedPointSymm (I := I) (M := M) g₀ g_bg a
      (by omega) hT hT1 hTT₀ gforce hforce hgforce U hUinit hUcont hUderiv i
  have hstab : Tendsto (fun N => perModeConv lam (fun s => (fseq N) s) t) atTop
      (𝓝 (perModeConv lam (fun s => (timeModeCoeff (I := I) (M := M) gforce i) s) t)) :=
    tendsto_perModeConv_of_tendsto_timeL2 lam hlam_nn hposit ht
  have hmem_ev : ∀ᶠ N in atTop, i ∈ eigenIdxFinset (I := I) (M := M) g₀ N := by
    obtain ⟨N₀, hN₀⟩ := exists_mem_eigenIdxFinset (I := I) (M := M) g₀ i
    filter_upwards [eventually_ge_atTop N₀] with N hN
    exact eigenIdxFinset_mono (I := I) (M := M) g₀ hN hN₀
  refine hstab.congr' ?_
  filter_upwards [hmem_ev] with N hiN
  have hae : (fun s => (fseq N) s) =ᵐ[volume.restrict (Set.Icc (0 : ℝ) T)]
      Set.IccExtend hT.le (fun p : ↑(Set.Icc (0 : ℝ) T) =>
        deTurckGalerkinForcingSymm (I := I) (M := M) g₀ g_bg a U N p.1 i) := by
    have hcoe : ⇑(fseq N) =ᵐ[timeMeasure T]
        fun s => deTurckGalerkinForcingSymm (I := I) (M := M) g₀ g_bg a U N s i := by
      rw [hfseq_def]
      exact TimeSobolev.coeFn_ofContinuousOn (hcontF N)
    have hcoe' : (fun s => (fseq N) s) =ᵐ[volume.restrict (Set.Icc (0 : ℝ) T)]
        fun s => deTurckGalerkinForcingSymm (I := I) (M := M) g₀ g_bg a U N s i := hcoe
    filter_upwards [hcoe', ae_restrict_mem measurableSet_Icc] with s hs hsmem
    rw [hs, Set.IccExtend_of_mem hT.le _ hsmem]
  have hperm_eq :
      perModeConv lam (fun s => (fseq N) s) t =
        perModeConv lam (Set.IccExtend hT.le (fun p : ↑(Set.Icc (0 : ℝ) T) =>
          deTurckGalerkinForcingSymm (I := I) (M := M) g₀ g_bg a U N p.1 i)) t :=
    perModeConv_timeL2_congr lam hae ht
  have hstagea :=
    galerkinPerMode_eq_perModeConvSymm (I := I) (M := M) g₀ g_bg a (by omega) hT U N
      (hUinit N) (hUcont N) (hUderiv N) i hiN ht
  rw [← hlam_def] at hstagea
  rw [hperm_eq, ← hstagea]

theorem deTurckGalerkin_solField_uniformSpatialMass_allOrderSymm
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
    ∀ σ : ℝ, ∃ Cσ : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T,
      Summable (fun i => tensorSobolevWeight (I := I) (M := M) i σ *
          (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u) t) ^ 2) ∧
        ∑' i, tensorSobolevWeight (I := I) (M := M) i σ *
            (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
              (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u) t) ^ 2 ≤ Cσ := by
  classical
  obtain ⟨U, hUcont, hUderiv, hUinit_coeff⟩ :=
    deTurckGalerkin_solution_existsSymm (I := I) (M := M) g₀ g_bg a (by omega)
      (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) hT.le
  have hUinit : ∀ N, ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N, U N 0 i = 0 := by
    intro N i hi
    rw [hUinit_coeff N i hi]; rfl
  obtain ⟨Cδ, Cmid, seed, B0, hCδ, hCmid, hclosure, hinitB⟩ :=
    deTurckGalerkin_forcing_closure_perScaleSymm (I := I) (M := M) g₀ g_bg a ha_super
      (T := T) U hUinit
  have hUmass : ∀ k : ℕ, ∃ Bound : ℝ, ∀ N, ∀ t ∈ Set.Icc (0 : ℝ) T,
      galerkinEnergy (I := I) (M := M) (eigenIdxFinset (I := I) (M := M) g₀ N)
        (U N) ((a : ℝ) + (k : ℝ)) t ≤ Bound :=
    galerkin_energy_uniform_bound_perScale (I := I) (M := M) (g := g₀)
      (U := U)
      (Fseq := deTurckGalerkinForcingSymm (I := I) (M := M) g₀ g_bg a U)
      (sseq := eigenIdxFinset (I := I) (M := M) g₀)
      (T := T) (σ₀ := (a : ℝ)) (Cδ := Cδ) (Cmid := Cmid) (seed := seed) (B0 := B0)
      hCδ hCmid hUcont hUderiv hclosure hinitB
  intro σ
  obtain ⟨k, hk⟩ := exists_nat_ge (σ - (a : ℝ))
  have hσk : σ ≤ (a : ℝ) + (k : ℝ) := by linarith
  obtain ⟨Bound, hBound⟩ := hUmass k
  refine ⟨Bound, fun t ht => ?_⟩
  set wσ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ :=
    fun i => tensorSobolevWeight (I := I) (M := M) i σ with hwσ
  have hwσ_nn : ∀ i, 0 ≤ wσ i := fun i => tensorSobolevWeight_nonneg (I := I) (M := M) i σ
  have hweight_dom : ∀ (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2),
      tensorSobolevWeight (I := I) (M := M) i σ ≤
        tensorSobolevWeight (I := I) (M := M) i ((a : ℝ) + (k : ℝ)) := by
    intro i
    exact Real.rpow_le_rpow_of_exponent_le
      (one_le_one_add_lambda (I := I) (M := M) i) hσk
  have hpartialbound : ∀ N,
      ∑ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N, wσ i * (U N t i) ^ 2 ≤ Bound := by
    intro N
    have hle : ∑ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N, wσ i * (U N t i) ^ 2 ≤
        ∑ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
          tensorSobolevWeight (I := I) (M := M) i ((a : ℝ) + (k : ℝ)) * (U N t i) ^ 2 := by
      refine Finset.sum_le_sum (fun i _ => ?_)
      exact mul_le_mul_of_nonneg_right (hweight_dom i) (sq_nonneg _)
    have hgal : galerkinEnergy (I := I) (M := M)
        (eigenIdxFinset (I := I) (M := M) g₀ N) (U N) ((a : ℝ) + (k : ℝ)) t ≤ Bound :=
      hBound N t ht
    have hgal_eq : galerkinEnergy (I := I) (M := M)
        (eigenIdxFinset (I := I) (M := M) g₀ N) (U N) ((a : ℝ) + (k : ℝ)) t =
        ∑ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
          tensorSobolevWeight (I := I) (M := M) i ((a : ℝ) + (k : ℝ)) * (U N t i) ^ 2 := rfl
    rw [hgal_eq] at hgal
    exact le_trans hle hgal
  have hconv : ∀ i,
      Tendsto (fun N => U N t i) atTop
        (𝓝 (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
          (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u) t)) :=
    fun i => galerkinSol_tendsto_solField_perModeConvSymm (I := I) (M := M)
      g₀ g_bg a ha_super hT hT1 hTT₀ gforce hforce hgforce U hUinit hUcont hUderiv i t ht
  have hfatou := fatou_weighted_sq_mass_le
    (eigenIdxFinset (I := I) (M := M) g₀) (tendsto_eigenIdxFinset_atTop (I := I) (M := M) g₀)
    wσ hwσ_nn (fun N i => U N t i)
    (fun i => perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
      (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u) t)
    (fun i => hconv i) Bound hpartialbound
  exact hfatou

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
