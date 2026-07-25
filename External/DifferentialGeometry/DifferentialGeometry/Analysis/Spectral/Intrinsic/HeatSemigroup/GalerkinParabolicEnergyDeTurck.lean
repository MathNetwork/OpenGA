import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.GalerkinParabolicEnergy
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.SpectralSmoothRepresentativeRealize
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SobolevNonlinearityExistence
import DifferentialGeometry.Analysis.Spectral.Tensor.Spectrum.SlotSwapEquivariance
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderRealizeBallUniformSplit
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.CrossScaleCauchySchwarz
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.EigenCombination
import DifferentialGeometry.Analysis.ODE.GlobalLipschitzAffineExistence
import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.Plancherel
import Mathlib.Analysis.InnerProductSpace.PiL2


noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.ODE
open DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private lemma oneThird_lt_one : (1 : ℝ) / 3 < 1 := by norm_num

open scoped Classical in
def deTurckGalerkinForcing (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (U : ℕ → ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) (N : ℕ) (t : ℝ)
    (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2) : ℝ :=
  if i ∈ eigenIdxFinset (I := I) (M := M) g₀ N then
    (deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a
      (finiteEigenComboHs (I := I) (M := M) g₀ (eigenIdxFinset (I := I) (M := M) g₀ N)
        (U N t) ((a : ℝ) + 2))).coeff i
  else 0

open scoped Classical in
@[simp] lemma deTurckGalerkinForcing_apply (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (U : ℕ → ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) (N : ℕ) (t : ℝ)
    (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2) :
    deTurckGalerkinForcing (I := I) (M := M) g₀ g_bg a U N t i =
      (if i ∈ eigenIdxFinset (I := I) (M := M) g₀ N then
        (deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a
          (finiteEigenComboHs (I := I) (M := M) g₀ (eigenIdxFinset (I := I) (M := M) g₀ N)
            (U N t) ((a : ℝ) + 2))).coeff i
      else 0) := rfl

open scoped Classical in
def deTurckGalerkinForcingSymm (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (U : ℕ → ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) (N : ℕ) (t : ℝ)
    (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2) : ℝ :=
  if i ∈ eigenIdxFinset (I := I) (M := M) g₀ N then
    (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
      (finiteEigenComboHs (I := I) (M := M) g₀ (eigenIdxFinset (I := I) (M := M) g₀ N)
        (U N t) ((a : ℝ) + 2))).coeff i
  else 0

open scoped Classical in
@[simp] lemma deTurckGalerkinForcingSymm_apply (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (U : ℕ → ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) (N : ℕ) (t : ℝ)
    (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2) :
    deTurckGalerkinForcingSymm (I := I) (M := M) g₀ g_bg a U N t i =
      (if i ∈ eigenIdxFinset (I := I) (M := M) g₀ N then
        (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
          (finiteEigenComboHs (I := I) (M := M) g₀ (eigenIdxFinset (I := I) (M := M) g₀ N)
            (U N t) ((a : ℝ) + 2))).coeff i
      else 0) := rfl

open scoped Classical in
private noncomputable def galerkinCoordEmbedLM
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2)) :
    EuclideanSpace ℝ {i // i ∈ S} →ₗ[ℝ] tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2) where
  toFun w := finiteEigenComboHs (I := I) (M := M) g₀ S
    (fun i => if h : i ∈ S then w ⟨i, h⟩ else 0) ((a : ℝ) + 2)
  map_add' w w' := by
    apply tensorHs.ext
    funext i
    simp only [tensorHs.add_coeff, finiteEigenComboHs_coeff]
    by_cases hi : i ∈ S
    · simp only [if_pos hi, dif_pos hi]
      change (w + w') ⟨i, hi⟩ = w ⟨i, hi⟩ + w' ⟨i, hi⟩
      rfl
    · simp only [if_neg hi, add_zero]
  map_smul' c w := by
    apply tensorHs.ext
    funext i
    simp only [tensorHs.smul_coeff, RingHom.id_apply, finiteEigenComboHs_coeff]
    by_cases hi : i ∈ S
    · simp only [if_pos hi, dif_pos hi]
      change (c • w) ⟨i, hi⟩ = c * w ⟨i, hi⟩
      rfl
    · simp only [if_neg hi, mul_zero]

noncomputable def galerkinCoordEmbed
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2)) :
    EuclideanSpace ℝ {i // i ∈ S} →L[ℝ] tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2) :=
  (galerkinCoordEmbedLM (I := I) (M := M) g₀ a S).toContinuousLinearMap

open scoped Classical in
omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma galerkinCoordEmbed_coeff
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
    (w : EuclideanSpace ℝ {i // i ∈ S})
    (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2) :
    (galerkinCoordEmbed (I := I) (M := M) g₀ a S w).coeff i =
      (if h : i ∈ S then w ⟨i, h⟩ else 0) := by
  change (finiteEigenComboHs (I := I) (M := M) g₀ S
    (fun i => if h : i ∈ S then w ⟨i, h⟩ else 0) ((a : ℝ) + 2)).coeff i = _
  rw [finiteEigenComboHs_coeff]
  by_cases hi : i ∈ S
  · rw [if_pos hi, dif_pos hi]
  · rw [if_neg hi, dif_neg hi]

noncomputable def galerkinCoordRestrict
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2)) :
    tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ) →L[ℝ] EuclideanSpace ℝ {i // i ∈ S} :=
  (EuclideanSpace.equiv {i // i ∈ S} ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun j : {i // i ∈ S} =>
      DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.tensorHsCoeffL
        (I := I) (M := M) (a := (a : ℝ)) j.1))

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma galerkinCoordRestrict_apply
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
    (v : tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) (j : {i // i ∈ S}) :
    (galerkinCoordRestrict (I := I) (M := M) g₀ a S v) j = v.coeff j.1 := rfl

private noncomputable def galerkinCoordDiagLM
    (g₀ : SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2)) :
    EuclideanSpace ℝ {i // i ∈ S} →ₗ[ℝ] EuclideanSpace ℝ {i // i ∈ S} where
  toFun w := WithLp.toLp 2
    (fun j => -(TensorEigenIdx.lambda (I := I) (M := M) j.1) * w.ofLp j)
  map_add' w w' := by
    apply WithLp.ofLp_injective 2
    funext j
    simp only [WithLp.ofLp_add, Pi.add_apply]
    ring
  map_smul' c w := by
    apply WithLp.ofLp_injective 2
    funext j
    simp only [WithLp.ofLp_smul, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    ring

noncomputable def galerkinCoordDiag
    (g₀ : SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2)) :
    EuclideanSpace ℝ {i // i ∈ S} →L[ℝ] EuclideanSpace ℝ {i // i ∈ S} :=
  (galerkinCoordDiagLM (I := I) (M := M) g₀ S).toContinuousLinearMap

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma galerkinCoordDiag_apply
    (g₀ : SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
    (w : EuclideanSpace ℝ {i // i ∈ S}) (j : {i // i ∈ S}) :
    (galerkinCoordDiag (I := I) (M := M) g₀ S w) j =
      -(TensorEigenIdx.lambda (I := I) (M := M) j.1) * w j := rfl

noncomputable def galerkinCoordField
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2)) :
    EuclideanSpace ℝ {i // i ∈ S} → EuclideanSpace ℝ {i // i ∈ S} :=
  fun w => galerkinCoordDiag (I := I) (M := M) g₀ S w +
    galerkinCoordRestrict (I := I) (M := M) g₀ a S
      (deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a
        (galerkinCoordEmbed (I := I) (M := M) g₀ a S w))

@[simp] lemma galerkinCoordField_apply
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
    (w : EuclideanSpace ℝ {i // i ∈ S}) (j : {i // i ∈ S}) :
    (galerkinCoordField (I := I) (M := M) g₀ g_bg a S w) j =
      -(TensorEigenIdx.lambda (I := I) (M := M) j.1) * w j +
        (deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a
          (galerkinCoordEmbed (I := I) (M := M) g₀ a S w)).coeff j.1 := by
  change (galerkinCoordDiag (I := I) (M := M) g₀ S w) j +
    (galerkinCoordRestrict (I := I) (M := M) g₀ a S _) j = _
  rw [galerkinCoordDiag_apply, galerkinCoordRestrict_apply]

theorem galerkinCoordField_lipschitzWith
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2)) :
    ∃ K : ℝ≥0, LipschitzWith K (galerkinCoordField (I := I) (M := M) g₀ g_bg a S) := by
  obtain ⟨K₀, hK₀⟩ := deTurckSobolevNHa2_lipschitzWith (I := I) (M := M) g₀ g_bg a ha_super
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
        (deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a
          (galerkinCoordEmbed (I := I) (M := M) g₀ a S w))) :=
    ((galerkinCoordRestrict (I := I) (M := M) g₀ a S).lipschitz.comp hK₀).comp
      (galerkinCoordEmbed (I := I) (M := M) g₀ a S).lipschitz
  exact hdiag.add hnonlin

theorem galerkinCoordField_affineBound
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2)) :
    ∃ (C : ℝ) (K : ℝ≥0), 0 ≤ C ∧ ∀ w : EuclideanSpace ℝ {i // i ∈ S},
      ‖galerkinCoordField (I := I) (M := M) g₀ g_bg a S w‖ ≤ C + (K : ℝ) * ‖w‖ := by
  obtain ⟨K₀, hK₀⟩ := deTurckSobolevNHa2_lipschitzWith (I := I) (M := M) g₀ g_bg a ha_super
  set Rst := galerkinCoordRestrict (I := I) (M := M) g₀ a S with hRst
  set Emb := galerkinCoordEmbed (I := I) (M := M) g₀ a S with hEmb
  set Diag := galerkinCoordDiag (I := I) (M := M) g₀ S with hDiag
  set N0 : ℝ := ‖deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a
    (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))‖ with hN0
  refine ⟨‖Rst‖ * N0, ‖Diag‖₊ + ‖Rst‖₊ * K₀ * ‖Emb‖₊,
    by positivity, ?_⟩
  intro w
  have hdecomp : galerkinCoordField (I := I) (M := M) g₀ g_bg a S w =
      Diag w + Rst (deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a (Emb w)) := rfl
  rw [hdecomp]
  have hdiag_bd : ‖Diag w‖ ≤ ‖Diag‖ * ‖w‖ := Diag.le_opNorm w
  have hN_bd : ‖deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a (Emb w)‖ ≤
      N0 + (K₀ : ℝ) * ‖Emb w‖ := by
    have hlip2 : ‖deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a (Emb w) -
        deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a 0‖ ≤ (K₀ : ℝ) * ‖Emb w‖ := by
      have hd := hK₀.dist_le_mul (Emb w) (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
      rw [dist_eq_norm, dist_eq_norm, sub_zero] at hd
      exact hd
    have htri : ‖deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a (Emb w)‖ ≤
        ‖deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a (Emb w) -
          deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a 0‖ +
        ‖deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a 0‖ := by
      calc ‖deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a (Emb w)‖
          = ‖(deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a (Emb w) -
              deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a 0) +
              deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a 0‖ := by
            rw [sub_add_cancel]
        _ ≤ _ := norm_add_le _ _
    rw [hN0]; linarith [htri, hlip2]
  have hRst_bd : ‖Rst (deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a (Emb w))‖ ≤
      ‖Rst‖ * ‖deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a (Emb w)‖ :=
    Rst.le_opNorm _
  have hEmb_bd : ‖Emb w‖ ≤ ‖Emb‖ * ‖w‖ := Emb.le_opNorm w
  have hRst_nn : 0 ≤ ‖Rst‖ := norm_nonneg Rst
  have hK₀_nn : 0 ≤ (K₀ : ℝ) := K₀.coe_nonneg
  calc ‖Diag w + Rst (deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a (Emb w))‖
      ≤ ‖Diag w‖ + ‖Rst (deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a (Emb w))‖ :=
        norm_add_le _ _
    _ ≤ ‖Diag‖ * ‖w‖ +
          ‖Rst‖ * (N0 + (K₀ : ℝ) * ‖Emb w‖) := by
        gcongr
        exact le_trans hRst_bd (mul_le_mul_of_nonneg_left hN_bd hRst_nn)
    _ ≤ ‖Diag‖ * ‖w‖ + ‖Rst‖ * (N0 + (K₀ : ℝ) * (‖Emb‖ * ‖w‖)) := by
        gcongr
    _ = ‖Rst‖ * N0 +
          (‖Diag‖ + ‖Rst‖ * (K₀ : ℝ) * ‖Emb‖) * ‖w‖ := by ring
    _ = ‖Rst‖ * N0 +
          ((‖Diag‖₊ + ‖Rst‖₊ * K₀ * ‖Emb‖₊ : ℝ≥0) : ℝ) * ‖w‖ := by
        push_cast [coe_nnnorm]
        ring

open scoped Classical in
theorem deTurckGalerkin_solution_exists_single
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    (u₀ : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) {T : ℝ} (hT : 0 < T)
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2)) :
    ∃ V : ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ,
      (∀ i ∈ S, ContinuousOn (fun t => V t i) (Set.Icc (0 : ℝ) T)) ∧
      (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ i ∈ S,
        HasDerivWithinAt (fun r => V r i)
          (-(TensorEigenIdx.lambda (I := I) (M := M) i) * V t i +
            (if i ∈ S then (deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a
              (finiteEigenComboHs (I := I) (M := M) g₀ S (V t) ((a : ℝ) + 2))).coeff i else 0))
          (Set.Ici t) t) ∧
      (∀ i ∈ S, V 0 i = u₀.coeff i) ∧
      (∀ t, ∀ i, i ∉ S → V t i = 0) := by
  obtain ⟨Klip, hKlip⟩ :=
    galerkinCoordField_lipschitzWith (I := I) (M := M) g₀ g_bg a ha_super S
  obtain ⟨C, Kaff, hC, hAff⟩ :=
    galerkinCoordField_affineBound (I := I) (M := M) g₀ g_bg a ha_super S
  set K : ℝ≥0 := max Klip Kaff with hK_def
  have hlip_t : ∀ t ∈ Set.Icc (0 : ℝ) T,
      LipschitzWith K (galerkinCoordField (I := I) (M := M) g₀ g_bg a S) :=
    fun _ _ => hKlip.weaken (le_max_left _ _)
  have hcont_t : ∀ x : EuclideanSpace ℝ {i // i ∈ S},
      ContinuousOn (fun _ : ℝ => galerkinCoordField (I := I) (M := M) g₀ g_bg a S x)
        (Set.Icc (0 : ℝ) T) := fun _ => continuousOn_const
  have haff_t : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : EuclideanSpace ℝ {i // i ∈ S},
      ‖galerkinCoordField (I := I) (M := M) g₀ g_bg a S x‖ ≤ C + (K : ℝ) * ‖x‖ := by
    intro _ _ x
    have h1 := hAff x
    have h2 : (Kaff : ℝ) * ‖x‖ ≤ (K : ℝ) * ‖x‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg x)
      exact_mod_cast le_max_right Klip Kaff
    linarith
  set w₀ : EuclideanSpace ℝ {i // i ∈ S} :=
    WithLp.toLp 2 (fun j : {i // i ∈ S} => u₀.coeff j.1) with hw₀_def
  obtain ⟨γ, hγ0, hγcont, hγderiv⟩ :=
    forward_solution_of_lipschitzWith_affineBound
      (E := EuclideanSpace ℝ {i // i ∈ S})
      (f := fun _ => galerkinCoordField (I := I) (M := M) g₀ g_bg a S) hT hC
      hlip_t hcont_t haff_t w₀
  refine ⟨fun t i => if h : i ∈ S then (γ t).ofLp ⟨i, h⟩ else 0, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have hcoord : ContinuousOn (fun t => (γ t).ofLp ⟨i, hi⟩) (Set.Icc (0 : ℝ) T) := by
      have hproj : Continuous (fun y : EuclideanSpace ℝ {i // i ∈ S} =>
          y.ofLp (⟨i, hi⟩ : {i // i ∈ S})) :=
        (EuclideanSpace.proj (𝕜 := ℝ) (⟨i, hi⟩ : {i // i ∈ S})).continuous
      exact hproj.comp_continuousOn hγcont
    refine hcoord.congr (fun t _ => ?_)
    simp only [dif_pos hi]
  · intro t ht i hi
    have hVeq : ∀ s, (fun r => if h : i ∈ S then (γ r).ofLp ⟨i, h⟩ else 0) s =
        (EuclideanSpace.proj (𝕜 := ℝ) ⟨i, hi⟩) (γ s) := by
      intro s; simp only [dif_pos hi]; rfl
    have hderiv_proj := ((EuclideanSpace.proj (𝕜 := ℝ) ⟨i, hi⟩).hasFDerivAt
      (x := γ t)).comp_hasDerivWithinAt t (hγderiv t ht)
    have hderiv_proj' :
        HasDerivWithinAt (fun s => (γ s).ofLp ⟨i, hi⟩)
          ((EuclideanSpace.proj (𝕜 := ℝ) ⟨i, hi⟩)
            (galerkinCoordField (I := I) (M := M) g₀ g_bg a S (γ t)))
          (Set.Ici (0 : ℝ)) t := hderiv_proj
    have hRHS_eq : (EuclideanSpace.proj (𝕜 := ℝ) ⟨i, hi⟩)
        (galerkinCoordField (I := I) (M := M) g₀ g_bg a S (γ t)) =
        -(TensorEigenIdx.lambda (I := I) (M := M) i) *
            (if h : i ∈ S then (γ t).ofLp ⟨i, h⟩ else 0) +
          (if i ∈ S then (deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a
            (finiteEigenComboHs (I := I) (M := M) g₀ S
              (fun i => if h : i ∈ S then (γ t).ofLp ⟨i, h⟩ else 0) ((a : ℝ) + 2))).coeff i
            else 0) := by
      have hembed_eq : galerkinCoordEmbed (I := I) (M := M) g₀ a S (γ t) =
          finiteEigenComboHs (I := I) (M := M) g₀ S
            (fun i => if h : i ∈ S then (γ t).ofLp ⟨i, h⟩ else 0) ((a : ℝ) + 2) := by
        apply tensorHs.ext
        funext i'
        rw [galerkinCoordEmbed_coeff, finiteEigenComboHs_coeff]
        by_cases hi' : i' ∈ S
        · simp only [if_pos hi', dif_pos hi']
        · simp only [if_neg hi', dif_neg hi']
      rw [EuclideanSpace.coe_proj]
      change (galerkinCoordField (I := I) (M := M) g₀ g_bg a S (γ t)) ⟨i, hi⟩ = _
      rw [galerkinCoordField_apply, if_pos hi, dif_pos hi, hembed_eq]
    have hfinal : HasDerivWithinAt (fun r => (γ r).ofLp ⟨i, hi⟩)
        (-(TensorEigenIdx.lambda (I := I) (M := M) i) *
            (if h : i ∈ S then (γ t).ofLp ⟨i, h⟩ else 0) +
          (if i ∈ S then (deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a
            (finiteEigenComboHs (I := I) (M := M) g₀ S
              (fun i => if h : i ∈ S then (γ t).ofLp ⟨i, h⟩ else 0) ((a : ℝ) + 2))).coeff i
            else 0))
        (Set.Ici (0 : ℝ)) t := hRHS_eq ▸ hderiv_proj'
    have hIci : HasDerivWithinAt (fun r => (γ r).ofLp ⟨i, hi⟩) _ (Set.Ici t) t :=
      DifferentialGeometry.Analysis.ODE.hasDerivWithinAt_Ici_of_Ici_zero hfinal ht.1
    have hcongr : (fun r => if h : i ∈ S then (γ r).ofLp ⟨i, h⟩ else 0) =
        (fun r => (γ r).ofLp ⟨i, hi⟩) := by
      funext r; rw [dif_pos hi]
    rw [hcongr]
    convert hIci using 2
  · intro i hi
    simp only [dif_pos hi]
    rw [hγ0, hw₀_def]
  · intro t i hi
    simp only [dif_neg hi]

theorem deTurckGalerkin_solution_exists
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    (u₀ : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) {T : ℝ} (hT : 0 ≤ T) :
    ∃ U : ℕ → ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ,
      (∀ N, ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
        ContinuousOn (fun t => U N t i) (Set.Icc (0 : ℝ) T)) ∧
      (∀ N, ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
        HasDerivWithinAt (fun r => U N r i)
          (-(TensorEigenIdx.lambda (I := I) (M := M) i) * U N t i +
            deTurckGalerkinForcing (I := I) (M := M) g₀ g_bg a U N t i)
          (Set.Ici t) t) ∧
      (∀ N, ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N, U N 0 i = u₀.coeff i) := by
  classical
  rcases eq_or_lt_of_le hT with hT0 | hTpos
  · refine ⟨fun _ _ i => u₀.coeff i, ?_, ?_, ?_⟩
    · intro N i _
      exact continuousOn_const
    · intro N t ht i _
      rw [← hT0] at ht
      exact absurd ht.2 (not_lt.mpr ht.1)
    · intro N i _; rfl
  · choose V hVcont hVderiv hVinit hVzero using fun N =>
      deTurckGalerkin_solution_exists_single (I := I) (M := M) g₀ g_bg a ha_super u₀ hTpos
        (eigenIdxFinset (I := I) (M := M) g₀ N)
    refine ⟨V, hVcont, ?_, hVinit⟩
    intro N t ht i hi
    have hderiv := hVderiv N t ht i hi
    have hforcing_eq :
        (if i ∈ eigenIdxFinset (I := I) (M := M) g₀ N then
          (deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a
            (finiteEigenComboHs (I := I) (M := M) g₀
              (eigenIdxFinset (I := I) (M := M) g₀ N) (V N t) ((a : ℝ) + 2))).coeff i
          else 0) =
        deTurckGalerkinForcing (I := I) (M := M) g₀ g_bg a V N t i := by
      rw [deTurckGalerkinForcing_apply]
    rw [hforcing_eq] at hderiv
    exact hderiv

theorem deTurckGalerkinForcing_seed_mass
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) :
    ∃ Cseed : ℕ → ℝ, (∀ k, 0 ≤ Cseed k) ∧
      ∀ (N : ℕ) (k : ℕ),
        ∑ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
            tensorSobolevWeight (I := I) (M := M) i ((a : ℝ) + (k : ℝ)) *
              ((deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a
                (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))).coeff i) ^ 2 ≤
          Cseed k ^ 2 := by
  classical
  set h := deTurckSobolevNHa2_exists_of_super (I := I) (M := M) g₀ a ha_super with hh
  set R₀ := (Classical.choose h).1 with hR₀_def
  have hR₀ : 0 < R₀ := (Classical.choose_spec h).1
  set S₀ : SmoothCcTensor g₀ 0 2 :=
    radialScaleSmooth (I := I) (M := M) g₀ a R₀ (0 : SmoothCcTensor g₀ 0 2) with hS₀_def
  have hS₀ball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S₀‖ ≤ R₀ :=
    norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M) g₀ a hR₀.le
      (0 : SmoothCcTensor g₀ 0 2)
  have hS₀fibre := (Classical.choose_spec h).2.2 _ hS₀ball
  set Wrem : SmoothCcTensor g₀ 0 2 :=
    deTurckSmoothRemainder (I := I) g₀ g_bg
      (radialScaleSmooth (I := I) (M := M) g₀ a (Classical.choose h).1
        (0 : SmoothCcTensor g₀ 0 2))
      (lt_of_le_of_lt (Classical.choose_spec h).2.1 (deTurckArmContractionThreshold''_lt_one' (Module.finrank ℝ E)))
      ((Classical.choose_spec h).2.2 _
        (norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M) g₀ a
          (Classical.choose_spec h).1.le (0 : SmoothCcTensor g₀ 0 2)))
    with hWrem_def
  have hzero_embed : (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) =
      smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
        (0 : SmoothCcTensor g₀ 0 2) := by
    refine tensorHs.ext ?_
    funext i
    rw [tensorHs.zero_coeff, smoothCcToTensorHs_coeff,
      show SmoothCcTensor.toL2 (0 : SmoothCcTensor g₀ 0 2) = 0 from map_zero _,
      tensorL2Coeff_eq_inner, inner_zero_right]
  have hseed_coeff : ∀ i,
      (deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))).coeff i =
        (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) Wrem).coeff i := by
    intro i
    rw [hzero_embed, deTurckSobolevNHa2_smoothEmbed_eq (I := I) (M := M) g₀ g_bg a ha_super
      (0 : SmoothCcTensor g₀ 0 2), deTurckSmoothN_coeff, smoothCcToTensorHs_coeff, hWrem_def]
  refine ⟨fun k => ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ)) Wrem‖,
    fun k => norm_nonneg _, ?_⟩
  intro N k
  set v : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + (k : ℝ)) :=
    smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ)) Wrem with hv_def
  have hcoeff_v : ∀ i, (deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a
      (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))).coeff i = v.coeff i := by
    intro i
    rw [hseed_coeff i, hv_def, smoothCcToTensorHs_coeff, smoothCcToTensorHs_coeff]
  have hterm_nn : ∀ i, 0 ≤ tensorSobolevWeight (I := I) (M := M) i ((a : ℝ) + (k : ℝ)) *
      (v.coeff i) ^ 2 :=
    fun i => mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i _) (sq_nonneg _)
  have hsum_le_tsum :
      ∑ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
          tensorSobolevWeight (I := I) (M := M) i ((a : ℝ) + (k : ℝ)) * (v.coeff i) ^ 2 ≤
        ∑' i, tensorSobolevWeight (I := I) (M := M) i ((a : ℝ) + (k : ℝ)) * (v.coeff i) ^ 2 :=
    v.weighted_summable.sum_le_tsum _ (fun i _ => hterm_nn i)
  calc ∑ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
        tensorSobolevWeight (I := I) (M := M) i ((a : ℝ) + (k : ℝ)) *
          ((deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))).coeff i) ^ 2
      = ∑ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
          tensorSobolevWeight (I := I) (M := M) i ((a : ℝ) + (k : ℝ)) * (v.coeff i) ^ 2 := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [hcoeff_v i]
    _ ≤ ∑' i, tensorSobolevWeight (I := I) (M := M) i ((a : ℝ) + (k : ℝ)) *
          (v.coeff i) ^ 2 := hsum_le_tsum
    _ = ‖v‖ ^ 2 := (tensorHs.norm_sq_eq_tsum (I := I) (M := M) v).symm
    _ = ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ)) Wrem‖ ^ 2 := by
        rw [hv_def]

private lemma mass_le_of_sqrt_split {A B C c d : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hc : 0 ≤ c) (hc1 : c < 1) (hd : 0 ≤ d)
    (hsplit : Real.sqrt A ≤ c * Real.sqrt B + d * Real.sqrt C) :
    A ≤ ((1 + c ^ 2) / 2) * B + (d ^ 2 * (1 + c ^ 2) / (1 - c ^ 2)) * C := by
  have hsqA : Real.sqrt A ^ 2 = A := Real.sq_sqrt hA
  have hsqB : Real.sqrt B ^ 2 = B := Real.sq_sqrt hB
  have hsqC : Real.sqrt C ^ 2 = C := Real.sq_sqrt hC
  set sB := Real.sqrt B with hsB
  set sC := Real.sqrt C with hsC
  have hsB_nn : 0 ≤ sB := Real.sqrt_nonneg _
  have hsC_nn : 0 ≤ sC := Real.sqrt_nonneg _
  have hrhs_nn : 0 ≤ c * sB + d * sC :=
    add_nonneg (mul_nonneg hc hsB_nn) (mul_nonneg hd hsC_nn)
  have hAle : A ≤ (c * sB + d * sC) ^ 2 := by
    have := mul_le_mul hsplit hsplit (Real.sqrt_nonneg _) hrhs_nn
    rwa [← sq, ← sq, hsqA] at this
  have hc2_lt : c ^ 2 < 1 := by nlinarith [hc, hc1]
  have hden_pos : 0 < 1 - c ^ 2 := by linarith [hc2_lt]
  have hyoung_mul : 2 * c * d * (1 - c ^ 2) * (sB * sC) ≤
      (1 - c ^ 2) ^ 2 / 2 * sB ^ 2 + 2 * c ^ 2 * d ^ 2 * sC ^ 2 := by
    nlinarith [sq_nonneg ((1 - c ^ 2) * sB - 2 * c * d * sC), hden_pos,
      mul_nonneg hc hd]
  have hkey : (c * sB + d * sC) ^ 2 ≤
      ((1 + c ^ 2) / 2) * B + (d ^ 2 * (1 + c ^ 2) / (1 - c ^ 2)) * C := by
    rw [← hsqB, ← hsqC, ← sub_nonneg]
    have hRHS_eq : (1 + c ^ 2) / 2 * sB ^ 2 + d ^ 2 * (1 + c ^ 2) / (1 - c ^ 2) * sC ^ 2 -
        (c * sB + d * sC) ^ 2 =
        ((1 - c ^ 2) ^ 2 / 2 * sB ^ 2 + 2 * c ^ 2 * d ^ 2 * sC ^ 2 -
          2 * c * d * (1 - c ^ 2) * (sB * sC)) / (1 - c ^ 2) := by
      rw [eq_div_iff hden_pos.ne']
      field_simp
      ring
    rw [hRHS_eq]
    apply div_nonneg _ hden_pos.le
    linarith [hyoung_mul]
  exact le_trans hAle hkey

open scoped Classical in
private lemma finiteEigenComboHs_eq_smoothCcToTensorHs
    (g₀ : SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
    (c : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) (σ : ℝ) :
    finiteEigenComboHs (I := I) (M := M) g₀ S c σ =
      smoothCcToTensorHs (I := I) (M := M) g₀ σ
        (finiteEigenCombo (I := I) (M := M) g₀ S c) := by
  refine tensorHs.ext ?_
  funext i
  rw [finiteEigenComboHs_coeff_eq, smoothCcToTensorHs_coeff,
    ← SmoothCcTensor.toL2_apply]

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

private lemma galerkinCoordFieldSymm_lipschitzWith
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

private lemma galerkinCoordFieldSymm_affineBound
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2)) :
    ∃ (C : ℝ) (K : ℝ≥0), 0 ≤ C ∧ ∀ w : EuclideanSpace ℝ {i // i ∈ S},
      ‖galerkinCoordFieldSymm (I := I) (M := M) g₀ g_bg a S w‖ ≤ C + (K : ℝ) * ‖w‖ := by
  obtain ⟨K₀, hK₀⟩ := deTurckSobolevNHa2Symm_lipschitzWith (I := I) (M := M) g₀ g_bg a ha_super
  set Rst := galerkinCoordRestrict (I := I) (M := M) g₀ a S with hRst
  set Emb := galerkinCoordEmbed (I := I) (M := M) g₀ a S with hEmb
  set Diag := galerkinCoordDiag (I := I) (M := M) g₀ S with hDiag
  set N0 : ℝ := ‖deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
    (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))‖ with hN0
  refine ⟨‖Rst‖ * N0, ‖Diag‖₊ + ‖Rst‖₊ * K₀ * ‖Emb‖₊,
    by positivity, ?_⟩
  intro w
  have hdecomp : galerkinCoordFieldSymm (I := I) (M := M) g₀ g_bg a S w =
      Diag w + Rst (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a (Emb w)) := rfl
  rw [hdecomp]
  have hdiag_bd : ‖Diag w‖ ≤ ‖Diag‖ * ‖w‖ := Diag.le_opNorm w
  have hN_bd : ‖deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a (Emb w)‖ ≤
      N0 + (K₀ : ℝ) * ‖Emb w‖ := by
    have hlip2 : ‖deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a (Emb w) -
        deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a 0‖ ≤ (K₀ : ℝ) * ‖Emb w‖ := by
      have hd := hK₀.dist_le_mul (Emb w) (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
      rw [dist_eq_norm, dist_eq_norm, sub_zero] at hd
      exact hd
    have htri : ‖deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a (Emb w)‖ ≤
        ‖deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a (Emb w) -
          deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a 0‖ +
        ‖deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a 0‖ := by
      calc ‖deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a (Emb w)‖
          = ‖(deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a (Emb w) -
              deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a 0) +
              deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a 0‖ := by
            rw [sub_add_cancel]
        _ ≤ _ := norm_add_le _ _
    rw [hN0]; linarith [htri, hlip2]
  have hRst_bd : ‖Rst (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a (Emb w))‖ ≤
      ‖Rst‖ * ‖deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a (Emb w)‖ :=
    Rst.le_opNorm _
  have hEmb_bd : ‖Emb w‖ ≤ ‖Emb‖ * ‖w‖ := Emb.le_opNorm w
  have hRst_nn : 0 ≤ ‖Rst‖ := norm_nonneg Rst
  have hK₀_nn : 0 ≤ (K₀ : ℝ) := K₀.coe_nonneg
  calc ‖Diag w + Rst (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a (Emb w))‖
      ≤ ‖Diag w‖ + ‖Rst (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a (Emb w))‖ :=
        norm_add_le _ _
    _ ≤ ‖Diag‖ * ‖w‖ +
          ‖Rst‖ * (N0 + (K₀ : ℝ) * ‖Emb w‖) := by
        gcongr
        exact le_trans hRst_bd (mul_le_mul_of_nonneg_left hN_bd hRst_nn)
    _ ≤ ‖Diag‖ * ‖w‖ + ‖Rst‖ * (N0 + (K₀ : ℝ) * (‖Emb‖ * ‖w‖)) := by
        gcongr
    _ = ‖Rst‖ * N0 +
          (‖Diag‖ + ‖Rst‖ * (K₀ : ℝ) * ‖Emb‖) * ‖w‖ := by ring
    _ = ‖Rst‖ * N0 +
          ((‖Diag‖₊ + ‖Rst‖₊ * K₀ * ‖Emb‖₊ : ℝ≥0) : ℝ) * ‖w‖ := by
        push_cast [coe_nnnorm]
        ring

open scoped Classical in
private theorem deTurckGalerkin_solution_exists_singleSymm
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    (u₀ : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) {T : ℝ} (hT : 0 < T)
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2)) :
    ∃ V : ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ,
      (∀ i ∈ S, ContinuousOn (fun t => V t i) (Set.Icc (0 : ℝ) T)) ∧
      (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ i ∈ S,
        HasDerivWithinAt (fun r => V r i)
          (-(TensorEigenIdx.lambda (I := I) (M := M) i) * V t i +
            (if i ∈ S then (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
              (finiteEigenComboHs (I := I) (M := M) g₀ S (V t) ((a : ℝ) + 2))).coeff i else 0))
          (Set.Ici t) t) ∧
      (∀ i ∈ S, V 0 i = u₀.coeff i) ∧
      (∀ t, ∀ i, i ∉ S → V t i = 0) := by
  obtain ⟨Klip, hKlip⟩ :=
    galerkinCoordFieldSymm_lipschitzWith (I := I) (M := M) g₀ g_bg a ha_super S
  obtain ⟨C, Kaff, hC, hAff⟩ :=
    galerkinCoordFieldSymm_affineBound (I := I) (M := M) g₀ g_bg a ha_super S
  set K : ℝ≥0 := max Klip Kaff with hK_def
  have hlip_t : ∀ t ∈ Set.Icc (0 : ℝ) T,
      LipschitzWith K (galerkinCoordFieldSymm (I := I) (M := M) g₀ g_bg a S) :=
    fun _ _ => hKlip.weaken (le_max_left _ _)
  have hcont_t : ∀ x : EuclideanSpace ℝ {i // i ∈ S},
      ContinuousOn (fun _ : ℝ => galerkinCoordFieldSymm (I := I) (M := M) g₀ g_bg a S x)
        (Set.Icc (0 : ℝ) T) := fun _ => continuousOn_const
  have haff_t : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : EuclideanSpace ℝ {i // i ∈ S},
      ‖galerkinCoordFieldSymm (I := I) (M := M) g₀ g_bg a S x‖ ≤ C + (K : ℝ) * ‖x‖ := by
    intro _ _ x
    have h1 := hAff x
    have h2 : (Kaff : ℝ) * ‖x‖ ≤ (K : ℝ) * ‖x‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg x)
      exact_mod_cast le_max_right Klip Kaff
    linarith
  set w₀ : EuclideanSpace ℝ {i // i ∈ S} :=
    WithLp.toLp 2 (fun j : {i // i ∈ S} => u₀.coeff j.1) with hw₀_def
  obtain ⟨γ, hγ0, hγcont, hγderiv⟩ :=
    forward_solution_of_lipschitzWith_affineBound
      (E := EuclideanSpace ℝ {i // i ∈ S})
      (f := fun _ => galerkinCoordFieldSymm (I := I) (M := M) g₀ g_bg a S) hT hC
      hlip_t hcont_t haff_t w₀
  refine ⟨fun t i => if h : i ∈ S then (γ t).ofLp ⟨i, h⟩ else 0, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have hcoord : ContinuousOn (fun t => (γ t).ofLp ⟨i, hi⟩) (Set.Icc (0 : ℝ) T) := by
      have hproj : Continuous (fun y : EuclideanSpace ℝ {i // i ∈ S} =>
          y.ofLp (⟨i, hi⟩ : {i // i ∈ S})) :=
        (EuclideanSpace.proj (𝕜 := ℝ) (⟨i, hi⟩ : {i // i ∈ S})).continuous
      exact hproj.comp_continuousOn hγcont
    refine hcoord.congr (fun t _ => ?_)
    simp only [dif_pos hi]
  · intro t ht i hi
    have hVeq : ∀ s, (fun r => if h : i ∈ S then (γ r).ofLp ⟨i, h⟩ else 0) s =
        (EuclideanSpace.proj (𝕜 := ℝ) ⟨i, hi⟩) (γ s) := by
      intro s; simp only [dif_pos hi]; rfl
    have hderiv_proj := ((EuclideanSpace.proj (𝕜 := ℝ) ⟨i, hi⟩).hasFDerivAt
      (x := γ t)).comp_hasDerivWithinAt t (hγderiv t ht)
    have hderiv_proj' :
        HasDerivWithinAt (fun s => (γ s).ofLp ⟨i, hi⟩)
          ((EuclideanSpace.proj (𝕜 := ℝ) ⟨i, hi⟩)
            (galerkinCoordFieldSymm (I := I) (M := M) g₀ g_bg a S (γ t)))
          (Set.Ici (0 : ℝ)) t := hderiv_proj
    have hRHS_eq : (EuclideanSpace.proj (𝕜 := ℝ) ⟨i, hi⟩)
        (galerkinCoordFieldSymm (I := I) (M := M) g₀ g_bg a S (γ t)) =
        -(TensorEigenIdx.lambda (I := I) (M := M) i) *
            (if h : i ∈ S then (γ t).ofLp ⟨i, h⟩ else 0) +
          (if i ∈ S then (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
            (finiteEigenComboHs (I := I) (M := M) g₀ S
              (fun i => if h : i ∈ S then (γ t).ofLp ⟨i, h⟩ else 0) ((a : ℝ) + 2))).coeff i
            else 0) := by
      have hembed_eq : galerkinCoordEmbed (I := I) (M := M) g₀ a S (γ t) =
          finiteEigenComboHs (I := I) (M := M) g₀ S
            (fun i => if h : i ∈ S then (γ t).ofLp ⟨i, h⟩ else 0) ((a : ℝ) + 2) := by
        apply tensorHs.ext
        funext i'
        rw [galerkinCoordEmbed_coeff, finiteEigenComboHs_coeff]
        by_cases hi' : i' ∈ S
        · simp only [if_pos hi', dif_pos hi']
        · simp only [if_neg hi', dif_neg hi']
      rw [EuclideanSpace.coe_proj]
      change (galerkinCoordFieldSymm (I := I) (M := M) g₀ g_bg a S (γ t)) ⟨i, hi⟩ = _
      rw [galerkinCoordFieldSymm_apply, if_pos hi, dif_pos hi, hembed_eq]
    have hfinal : HasDerivWithinAt (fun r => (γ r).ofLp ⟨i, hi⟩)
        (-(TensorEigenIdx.lambda (I := I) (M := M) i) *
            (if h : i ∈ S then (γ t).ofLp ⟨i, h⟩ else 0) +
          (if i ∈ S then (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
            (finiteEigenComboHs (I := I) (M := M) g₀ S
              (fun i => if h : i ∈ S then (γ t).ofLp ⟨i, h⟩ else 0) ((a : ℝ) + 2))).coeff i
            else 0))
        (Set.Ici (0 : ℝ)) t := hRHS_eq ▸ hderiv_proj'
    have hIci : HasDerivWithinAt (fun r => (γ r).ofLp ⟨i, hi⟩) _ (Set.Ici t) t :=
      DifferentialGeometry.Analysis.ODE.hasDerivWithinAt_Ici_of_Ici_zero hfinal ht.1
    have hcongr : (fun r => if h : i ∈ S then (γ r).ofLp ⟨i, h⟩ else 0) =
        (fun r => (γ r).ofLp ⟨i, hi⟩) := by
      funext r; rw [dif_pos hi]
    rw [hcongr]
    convert hIci using 2
  · intro i hi
    simp only [dif_pos hi]
    rw [hγ0, hw₀_def]
  · intro t i hi
    simp only [dif_neg hi]

theorem deTurckGalerkin_solution_existsSymm
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    (u₀ : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) {T : ℝ} (hT : 0 ≤ T) :
    ∃ U : ℕ → ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ,
      (∀ N, ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
        ContinuousOn (fun t => U N t i) (Set.Icc (0 : ℝ) T)) ∧
      (∀ N, ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
        HasDerivWithinAt (fun r => U N r i)
          (-(TensorEigenIdx.lambda (I := I) (M := M) i) * U N t i +
            deTurckGalerkinForcingSymm (I := I) (M := M) g₀ g_bg a U N t i)
          (Set.Ici t) t) ∧
      (∀ N, ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N, U N 0 i = u₀.coeff i) := by
  classical
  rcases eq_or_lt_of_le hT with hT0 | hTpos
  · refine ⟨fun _ _ i => u₀.coeff i, ?_, ?_, ?_⟩
    · intro N i _
      exact continuousOn_const
    · intro N t ht i _
      rw [← hT0] at ht
      exact absurd ht.2 (not_lt.mpr ht.1)
    · intro N i _; rfl
  · choose V hVcont hVderiv hVinit hVzero using fun N =>
      deTurckGalerkin_solution_exists_singleSymm (I := I) (M := M) g₀ g_bg a ha_super u₀ hTpos
        (eigenIdxFinset (I := I) (M := M) g₀ N)
    refine ⟨V, hVcont, ?_, hVinit⟩
    intro N t ht i hi
    have hderiv := hVderiv N t ht i hi
    have hforcing_eq :
        (if i ∈ eigenIdxFinset (I := I) (M := M) g₀ N then
          (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
            (finiteEigenComboHs (I := I) (M := M) g₀
              (eigenIdxFinset (I := I) (M := M) g₀ N) (V N t) ((a : ℝ) + 2))).coeff i
          else 0) =
        deTurckGalerkinForcingSymm (I := I) (M := M) g₀ g_bg a V N t i := by
      rw [deTurckGalerkinForcingSymm_apply]
    rw [hforcing_eq] at hderiv
    exact hderiv

section

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (ccTensor02Symm symmS_smul domDomCongrSection)
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization (smoothCcTensorBilinForm)

omit [BoundarylessManifold I M] in
set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in
private lemma eigenIdxFinset_mem_iff_of_eigenvalue_eq (g₀ : SmoothRiemannianMetric I M) (N : ℕ) :
    ∀ i j : TensorEigenIdx (I := I) (M := M) g₀ 0 2, i.1 = j.1 →
      (i ∈ eigenIdxFinset (I := I) (M := M) g₀ N ↔
        j ∈ eigenIdxFinset (I := I) (M := M) g₀ N) := by
  intro i j hij
  rw [mem_eigenIdxFinset, mem_eigenIdxFinset]
  have hl : TensorEigenIdx.lambda (I := I) (M := M) i =
      TensorEigenIdx.lambda (I := I) (M := M) j := by
    unfold TensorEigenIdx.lambda
    rw [hij]
  rw [hl]

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in
private lemma gscr_finiteEigenComboHs_eq_smoothCcToTensorHs
    (g₀ : SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
    (c : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) (σ : ℝ) :
    finiteEigenComboHs (I := I) (M := M) g₀ S c σ =
      smoothCcToTensorHs (I := I) (M := M) g₀ σ
        (finiteEigenCombo (I := I) (M := M) g₀ S c) := by
  refine tensorHs.ext ?_
  funext i
  rw [finiteEigenComboHs_coeff_eq, smoothCcToTensorHs_coeff,
    ← SmoothCcTensor.toL2_apply]

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in

theorem deTurckSmoothRemainder_spectralCoercive_split'
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 4 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {δ : ℝ} (hδ_le : δ ≤ deTurckArmContractionThresholdSharp (Module.finrank ℝ E))
    (hδ_fibre : ∀ (T₀ : SmoothCcTensor g₀ 0 2),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
      DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization.metricCauchySchwarzBound
        (I := I) (M := M) g₀
        (DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization.ccTensorBilinSymm
          (I := I) g₀ T₀) δ) :
    ∃ (Cδ₀ : ℝ) (Crem : ℕ → ℝ), 0 ≤ Cδ₀ ∧ Cδ₀ < 1 ∧ (∀ k, 0 ≤ Crem k) ∧
      ∀ (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2)) (k : ℕ)
        (T₀ : SmoothCcTensor g₀ 0 2)
        (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
          smoothCcTensorBilinForm (I := I) g₀ T₀ x v w = smoothCcTensorBilinForm (I := I) g₀ T₀ x w v)
        (hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀)
        (hsupp : ∀ i, i ∉ S →
          (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀).coeff i = 0),
        Real.sqrt (∑ i ∈ S,
            tensorSobolevWeight (I := I) (M := M) i ((a : ℝ) + (k : ℝ) - 1) *
              ((smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1)
                  (deTurckSmoothRemainder (I := I) g₀ g_bg T₀
                    (lt_of_le_of_lt hδ_le (deTurckArmContractionThreshold''_lt_one' (Module.finrank ℝ E)))
                    (hδ_fibre T₀ hball))).coeff i -
                (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1)
                  (deTurckSmoothRemainder (I := I) g₀ g_bg
                    (0 : SmoothCcTensor g₀ 0 2)
                    (lt_of_le_of_lt hδ_le (deTurckArmContractionThreshold''_lt_one' (Module.finrank ℝ E)))
                    (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
                      (by
                        rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                            from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                          tensorHs_norm_smul]
                        simpa using hR₀)))).coeff i) ^ 2) ≤
          Cδ₀ * Real.sqrt (∑ i ∈ S,
              tensorSobolevWeight (I := I) (M := M) i ((a : ℝ) + (k : ℝ) + 1) *
                ((smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) + 1)
                  T₀).coeff i) ^ 2) +
            Crem k * Real.sqrt (∑ i ∈ S,
              tensorSobolevWeight (I := I) (M := M) i ((a : ℝ) + (k : ℝ)) *
                ((smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ))
                  T₀).coeff i) ^ 2) := by
  classical
  obtain ⟨Cδ₀, Crem, hCδ₀_nn, hCδ₀_lt, hCrem_nn, hker⟩ :=
    deTurckSmoothRemainderDiff_ballUniform_spectralSplit_of_symm (I := I) (M := M) g₀ g_bg a ha_super
      hR₀ hδ_le hδ_fibre
  refine ⟨Cδ₀, Crem, hCδ₀_nn, hCδ₀_lt, hCrem_nn, ?_⟩
  intro S k T₀ hTsymm hball hsupp
  set Rdiff : SmoothCcTensor g₀ 0 2 :=
    deTurckSmoothRemainder (I := I) g₀ g_bg T₀
        (lt_of_le_of_lt hδ_le (deTurckArmContractionThreshold''_lt_one' (Module.finrank ℝ E))) (hδ_fibre T₀ hball) -
      deTurckSmoothRemainder (I := I) g₀ g_bg (0 : SmoothCcTensor g₀ 0 2)
        (lt_of_le_of_lt hδ_le (deTurckArmContractionThreshold''_lt_one' (Module.finrank ℝ E)))
        (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
          (by
            rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                from (zero_smul _ _).symm, smoothCcToTensorHs_smul, tensorHs_norm_smul]
            simpa using hR₀)) with hRdiff_def
  have hLHS_coeff : ∀ i,
      (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1)
            (deTurckSmoothRemainder (I := I) g₀ g_bg T₀
              (lt_of_le_of_lt hδ_le (deTurckArmContractionThreshold''_lt_one' (Module.finrank ℝ E))) (hδ_fibre T₀ hball))).coeff i -
          (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1)
            (deTurckSmoothRemainder (I := I) g₀ g_bg (0 : SmoothCcTensor g₀ 0 2)
              (lt_of_le_of_lt hδ_le (deTurckArmContractionThreshold''_lt_one' (Module.finrank ℝ E)))
              (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
                (by
                  rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                      from (zero_smul _ _).symm, smoothCcToTensorHs_smul, tensorHs_norm_smul]
                  simpa using hR₀)))).coeff i =
        (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1) Rdiff).coeff i := by
    intro i
    rw [hRdiff_def, smoothCcToTensorHs_sub]
    rfl
  have hLHS_le :
      Real.sqrt (∑ i ∈ S,
          tensorSobolevWeight (I := I) (M := M) i ((a : ℝ) + (k : ℝ) - 1) *
            ((smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1)
              Rdiff).coeff i) ^ 2) ≤
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1) Rdiff‖ := by
    rw [tensorHs.norm_eq_sqrt_tsum]
    refine Real.sqrt_le_sqrt ?_
    exact (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1)
      Rdiff).weighted_summable.sum_le_tsum _
      (fun i _ => mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i _) (sq_nonneg _))
  have hsupp_all : ∀ (τ : ℝ) (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2), i ∉ S →
      (smoothCcToTensorHs (I := I) (M := M) g₀ τ T₀).coeff i = 0 := by
    intro τ i hi
    rw [smoothCcToTensorHs_coeff]
    have := hsupp i hi
    rwa [smoothCcToTensorHs_coeff] at this
  have hRHS_eq : ∀ (τ : ℝ),
      ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i τ *
          ((smoothCcToTensorHs (I := I) (M := M) g₀ τ T₀).coeff i) ^ 2 =
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ τ T₀‖ ^ 2 := by
    intro τ
    rw [tensorHs.norm_sq_eq_tsum]
    refine (tsum_eq_sum (s := S) ?_).symm
    intro i hi
    rw [hsupp_all τ i hi]
    ring
  have hRHS1 :
      Real.sqrt (∑ i ∈ S,
          tensorSobolevWeight (I := I) (M := M) i ((a : ℝ) + (k : ℝ) + 1) *
            ((smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) + 1) T₀).coeff i) ^ 2) =
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) + 1) T₀‖ := by
    rw [hRHS_eq ((a : ℝ) + (k : ℝ) + 1), Real.sqrt_sq (norm_nonneg _)]
  have hRHS2 :
      Real.sqrt (∑ i ∈ S,
          tensorSobolevWeight (I := I) (M := M) i ((a : ℝ) + (k : ℝ)) *
            ((smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ)) T₀).coeff i) ^ 2) =
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ)) T₀‖ := by
    rw [hRHS_eq ((a : ℝ) + (k : ℝ)), Real.sqrt_sq (norm_nonneg _)]
  have hLHS_rw :
      (∑ i ∈ S,
          tensorSobolevWeight (I := I) (M := M) i ((a : ℝ) + (k : ℝ) - 1) *
            ((smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1)
                (deTurckSmoothRemainder (I := I) g₀ g_bg T₀
                  (lt_of_le_of_lt hδ_le (deTurckArmContractionThreshold''_lt_one' (Module.finrank ℝ E))) (hδ_fibre T₀ hball))).coeff i -
              (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1)
                (deTurckSmoothRemainder (I := I) g₀ g_bg (0 : SmoothCcTensor g₀ 0 2)
                  (lt_of_le_of_lt hδ_le (deTurckArmContractionThreshold''_lt_one' (Module.finrank ℝ E)))
                  (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
                    (by
                      rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                          from (zero_smul _ _).symm, smoothCcToTensorHs_smul, tensorHs_norm_smul]
                      simpa using hR₀)))).coeff i) ^ 2) =
        ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i ((a : ℝ) + (k : ℝ) - 1) *
            ((smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1) Rdiff).coeff i) ^ 2 :=
    Finset.sum_congr rfl (fun i _ => by rw [hLHS_coeff i])
  rw [hLHS_rw, hRHS1, hRHS2]
  exact le_trans hLHS_le (hker k T₀ hTsymm hball)

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in

theorem deTurckSobolevNHa2_diff_sobolevSplit_perScale'
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 4 * Module.finrank ℝ E + 10 ≤ a)
    {R₀ : ℝ} (hR₀ : 0 < R₀)
    {δ : ℝ} (hδ_le : δ ≤ deTurckArmContractionThresholdSharp (Module.finrank ℝ E))
    (hδ_fibre : ∀ (T₀ : SmoothCcTensor g₀ 0 2),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
      DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization.metricCauchySchwarzBound
        (I := I) (M := M) g₀
        (DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization.ccTensorBilinSymm
          (I := I) g₀ T₀) δ)
    (htie : ∀ (T : SmoothCcTensor g₀ 0 2),
      deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a
          (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T) =
        deTurckSmoothRemainderTensorHs (I := I) (M := M) g₀ g_bg a
          (radialScaleSmooth (I := I) (M := M) g₀ a R₀ T)
          (lt_of_le_of_lt hδ_le (deTurckArmContractionThreshold''_lt_one' (Module.finrank ℝ E)))
          (hδ_fibre _ (norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M) g₀ a
            hR₀.le T)))
    (U : ℕ → ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) :
    ∃ (Cδ₀ : ℝ) (Crem : ℕ → ℝ), 0 ≤ Cδ₀ ∧ Cδ₀ < 1 ∧ (∀ k, 0 ≤ Crem k) ∧
      ∀ (N : ℕ) (k : ℕ) (t : ℝ),
        Real.sqrt (∑ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
            tensorSobolevWeight (I := I) (M := M) i ((a : ℝ) + (k : ℝ) - 1) *
              ((deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a
                  (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                    (ccTensor02Symm (I := I) (M := M) g₀
                      (finiteEigenCombo (I := I) (M := M) g₀
                        (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t))))).coeff i -
                (deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a
                  (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))).coeff i) ^ 2) ≤
          Cδ₀ * Real.sqrt (galerkinEnergy (I := I) (M := M)
              (eigenIdxFinset (I := I) (M := M) g₀ N) (U N) ((a : ℝ) + (k : ℝ) + 1) t) +
            Crem k * Real.sqrt (galerkinEnergy (I := I) (M := M)
              (eigenIdxFinset (I := I) (M := M) g₀ N) (U N) ((a : ℝ) + (k : ℝ)) t) := by
  classical
  have hδ_lt : δ < 1 :=
    lt_of_le_of_lt hδ_le (deTurckArmContractionThreshold''_lt_one' (Module.finrank ℝ E))
  obtain ⟨Cδ₀, Crem, hCδ₀_nn, hCδ₀_lt, hCrem_nn, hsplit⟩ :=
    deTurckSmoothRemainder_spectralCoercive_split' (I := I) (M := M) g₀ g_bg a ha_super
      hR₀.le hδ_le hδ_fibre
  refine ⟨Cδ₀, Crem, hCδ₀_nn, hCδ₀_lt, hCrem_nn, ?_⟩
  intro N k t
  set S := eigenIdxFinset (I := I) (M := M) g₀ N with hS
  set σ : ℝ := (a : ℝ) + (k : ℝ) with hσ
  set Tb : SmoothCcTensor g₀ 0 2 := finiteEigenCombo (I := I) (M := M) g₀ S (U N t)
    with hTb_def
  set Ts : SmoothCcTensor g₀ 0 2 := ccTensor02Symm (I := I) (M := M) g₀ Tb with hTs_def
  set T₀ : SmoothCcTensor g₀ 0 2 := radialScaleSmooth (I := I) (M := M) g₀ a R₀ Ts
    with hT₀_def
  have hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ :=
    norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M) g₀ a hR₀.le Ts
  set c : ℝ := min 1 (R₀ / ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) Ts‖)
    with hc_def
  have hc_nn : 0 ≤ c := le_min zero_le_one (div_nonneg hR₀.le (norm_nonneg _))
  have hc_le_one : c ≤ 1 := min_le_left _ _
  have hsmul : T₀ = c • Ts := by rw [hT₀_def, hc_def]; rfl
  have hT₀_symmS : T₀ = ccTensor02Symm (I := I) (M := M) g₀ (c • Tb) := by
    rw [hsmul, hTs_def, symmS_smul]
  have hTsymm : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ T₀ x v w = smoothCcTensorBilinForm (I := I) g₀ T₀ x w v := by
    intro x v w
    rw [hT₀_symmS]
    exact bilinearForm_of_tensorSymmetrization_symm (I := I) (M := M) g₀ (c • Tb) x v w
  have hbridge : ∀ (τ : ℝ),
      finiteEigenComboHs (I := I) (M := M) g₀ S (U N t) τ =
        smoothCcToTensorHs (I := I) (M := M) g₀ τ Tb :=
    fun τ => by
      rw [hTb_def]
      exact gscr_finiteEigenComboHs_eq_smoothCcToTensorHs g₀ S (U N t) τ
  have hTb_coeff_off : ∀ i, i ∉ S →
      (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) Tb).coeff i = 0 := by
    intro i hi
    rw [← hbridge ((a : ℝ) + 2), finiteEigenComboHs_coeff, if_neg hi]
  have hTb_L2_off : ∀ i, i ∉ S →
      tensorL2Coeff (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
        (SmoothCcTensor.toL2 Tb) i = 0 := by
    intro i hi
    have h := hTb_coeff_off i hi
    rwa [smoothCcToTensorHs_coeff] at h
  have hTs_L2_off : ∀ i, i ∉ S →
      tensorL2Coeff (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
        (SmoothCcTensor.toL2 Ts) i = 0 := by
    intro i hi
    rw [hTs_def]
    exact tensorL2Coeff_toL2_symmS_eq_zero_of_notMem (I := I) (M := M) (g := g₀) S
      (eigenIdxFinset_mem_iff_of_eigenvalue_eq g₀ N) Tb hTb_L2_off i hi
  have hTs_coeff_off : ∀ i, i ∉ S →
      (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) Ts).coeff i = 0 := by
    intro i hi
    rw [smoothCcToTensorHs_coeff]
    exact hTs_L2_off i hi
  have hsupp : ∀ i, i ∉ S →
      (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀).coeff i = 0 := by
    intro i hi
    rw [hsmul, smoothCcToTensorHs_smul]
    simp only [tensorHs.smul_coeff]
    rw [hTs_coeff_off i hi, mul_zero]
  have hzero : (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2) :=
    (zero_smul _ _).symm
  have hLHS_eq : ∀ i,
      (deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a
            (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) Ts)).coeff i -
          (deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))).coeff i =
        (smoothCcToTensorHs (I := I) (M := M) g₀ (σ - 1)
            (deTurckSmoothRemainder (I := I) g₀ g_bg T₀ hδ_lt (hδ_fibre T₀ hball))).coeff i -
          (smoothCcToTensorHs (I := I) (M := M) g₀ (σ - 1)
            (deTurckSmoothRemainder (I := I) g₀ g_bg (0 : SmoothCcTensor g₀ 0 2) hδ_lt
              (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
                (by
                  rw [hzero, smoothCcToTensorHs_smul, tensorHs_norm_smul]
                  simpa using hR₀.le)))).coeff i := by
    intro i
    have hNT : (deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a
          (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) Ts)).coeff i =
        (smoothCcToTensorHs (I := I) (M := M) g₀ (σ - 1)
          (deTurckSmoothRemainder (I := I) g₀ g_bg T₀ hδ_lt (hδ_fibre T₀ hball))).coeff i := by
      rw [htie Ts, deTurckSmoothN_coeff, smoothCcToTensorHs_coeff]
    have hN0 : (deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))).coeff i =
        (smoothCcToTensorHs (I := I) (M := M) g₀ (σ - 1)
          (deTurckSmoothRemainder (I := I) g₀ g_bg (0 : SmoothCcTensor g₀ 0 2) hδ_lt
            (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
              (by
                rw [hzero, smoothCcToTensorHs_smul, tensorHs_norm_smul]
                simpa using hR₀.le)))).coeff i := by
      have hembed0 : (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) =
          smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
            (0 : SmoothCcTensor g₀ 0 2) := by
        refine tensorHs.ext ?_
        funext j
        rw [tensorHs.zero_coeff, smoothCcToTensorHs_coeff,
          show SmoothCcTensor.toL2 (0 : SmoothCcTensor g₀ 0 2) = 0 from map_zero _,
          tensorL2Coeff_eq_inner, inner_zero_right]
      have hscale0 : radialScaleSmooth (I := I) (M := M) g₀ a R₀
          (0 : SmoothCcTensor g₀ 0 2) = (0 : SmoothCcTensor g₀ 0 2) := by
        rw [radialScaleSmooth, smul_zero]
      have hRemEq : ∀ (hp : DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization.metricCauchySchwarzBound
              (I := I) (M := M) g₀
              (DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization.ccTensorBilinSymm
                (I := I) g₀ (radialScaleSmooth (I := I) (M := M) g₀ a R₀
                  (0 : SmoothCcTensor g₀ 0 2))) δ)
            (hp0 : DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization.metricCauchySchwarzBound
              (I := I) (M := M) g₀
              (DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization.ccTensorBilinSymm
                (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ),
            deTurckSmoothRemainder (I := I) g₀ g_bg
                (radialScaleSmooth (I := I) (M := M) g₀ a R₀ (0 : SmoothCcTensor g₀ 0 2))
                hδ_lt hp =
              deTurckSmoothRemainder (I := I) g₀ g_bg (0 : SmoothCcTensor g₀ 0 2) hδ_lt hp0 := by
        rw [hscale0]; intro hp hp0; rfl
      rw [hembed0, htie (0 : SmoothCcTensor g₀ 0 2), deTurckSmoothN_coeff,
        smoothCcToTensorHs_coeff, hRemEq]
    rw [hNT, hN0]
  have hRHS_scale : ∀ (τ : ℝ) (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2),
      (smoothCcToTensorHs (I := I) (M := M) g₀ τ T₀).coeff i =
        c * (smoothCcToTensorHs (I := I) (M := M) g₀ τ Ts).coeff i := by
    intro τ i
    rw [hsmul, smoothCcToTensorHs_smul]
    simp only [tensorHs.smul_coeff]
  have hD2 : ∀ (τ : ℝ),
      (∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i τ *
        ((smoothCcToTensorHs (I := I) (M := M) g₀ τ Ts).coeff i) ^ 2) ≤
      ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i τ * (U N t i) ^ 2 := by
    intro τ
    have hstep1 : (∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i τ *
        ((smoothCcToTensorHs (I := I) (M := M) g₀ τ Ts).coeff i) ^ 2) =
        ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i τ *
          (tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (ccTensor02Symm (I := I) (M := M) g₀ Tb)) i) ^ 2 := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [smoothCcToTensorHs_coeff, hTs_def]
    have hstep2 := sum_tensorSobolevWeight_mul_sq_tensorL2Coeff_toL2_symmS_le
      (I := I) (M := M) (g := g₀) τ S
      (eigenIdxFinset_mem_iff_of_eigenvalue_eq g₀ N) Tb hTb_L2_off
    have hstep3 : (∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i τ *
        (tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
          (SmoothCcTensor.toL2 Tb) i) ^ 2) =
        ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i τ * (U N t i) ^ 2 := by
      refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [← smoothCcToTensorHs_coeff (I := I) (M := M) g₀ τ Tb i, ← hbridge τ,
        finiteEigenComboHs_coeff, if_pos hi]
    calc (∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i τ *
        ((smoothCcToTensorHs (I := I) (M := M) g₀ τ Ts).coeff i) ^ 2)
        = ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i τ *
          (tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (ccTensor02Symm (I := I) (M := M) g₀ Tb)) i) ^ 2 := hstep1
      _ ≤ ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i τ *
          (tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 Tb) i) ^ 2 := hstep2
      _ = ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i τ * (U N t i) ^ 2 := hstep3
  have hRHS_le : ∀ (τ : ℝ),
      Real.sqrt (∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i τ *
        ((smoothCcToTensorHs (I := I) (M := M) g₀ τ T₀).coeff i) ^ 2) ≤
      Real.sqrt (galerkinEnergy (I := I) (M := M) S (U N) τ t) := by
    intro τ
    rw [galerkinEnergy]
    refine Real.sqrt_le_sqrt ?_
    have hc2 : c ^ 2 ≤ 1 := by nlinarith [hc_nn, hc_le_one]
    have hstep : (∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i τ *
        ((smoothCcToTensorHs (I := I) (M := M) g₀ τ T₀).coeff i) ^ 2) ≤
        ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i τ *
          ((smoothCcToTensorHs (I := I) (M := M) g₀ τ Ts).coeff i) ^ 2 := by
      refine Finset.sum_le_sum (fun i hi => ?_)
      rw [hRHS_scale τ i, mul_pow]
      have hwnn := tensorSobolevWeight_nonneg (I := I) (M := M) i τ
      have hsqnn : (0 : ℝ) ≤ ((smoothCcToTensorHs (I := I) (M := M) g₀ τ Ts).coeff i) ^ 2 :=
        sq_nonneg _
      nlinarith [mul_nonneg hwnn hsqnn, hc2, hwnn, hsqnn,
        mul_le_mul_of_nonneg_right hc2 (mul_nonneg hwnn hsqnn)]
    exact le_trans hstep (hD2 τ)
  have hkey := hsplit S k T₀ hTsymm hball hsupp
  rw [← hσ] at hkey
  have hLHS_rw :
      Real.sqrt (∑ i ∈ S,
          tensorSobolevWeight (I := I) (M := M) i (σ - 1) *
            ((deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a
                (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                  (ccTensor02Symm (I := I) (M := M) g₀
                    (finiteEigenCombo (I := I) (M := M) g₀ S (U N t))))).coeff i -
              (deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a
                (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))).coeff i) ^ 2) =
        Real.sqrt (∑ i ∈ S,
          tensorSobolevWeight (I := I) (M := M) i (σ - 1) *
            ((smoothCcToTensorHs (I := I) (M := M) g₀ (σ - 1)
                (deTurckSmoothRemainder (I := I) g₀ g_bg T₀ hδ_lt (hδ_fibre T₀ hball))).coeff i -
              (smoothCcToTensorHs (I := I) (M := M) g₀ (σ - 1)
                (deTurckSmoothRemainder (I := I) g₀ g_bg (0 : SmoothCcTensor g₀ 0 2) hδ_lt
                  (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
                    (by
                      rw [hzero, smoothCcToTensorHs_smul, tensorHs_norm_smul]
                      simpa using hR₀.le)))).coeff i) ^ 2) := by
    refine congrArg Real.sqrt (Finset.sum_congr rfl (fun i _ => ?_))
    rw [show (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
        (ccTensor02Symm (I := I) (M := M) g₀
          (finiteEigenCombo (I := I) (M := M) g₀ S (U N t)))) =
        smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) Ts from by
      rw [hTs_def, hTb_def]]
    rw [hLHS_eq i]
  rw [hLHS_rw]
  refine le_trans hkey ?_
  exact add_le_add (mul_le_mul_of_nonneg_left (hRHS_le (σ + 1)) hCδ₀_nn)
    (mul_le_mul_of_nonneg_left (hRHS_le σ) (hCrem_nn k))

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in
private lemma deTurckSobolevNHa2Symm_finiteEigenComboHs_eq
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    (S : Finset (TensorEigenIdx (I := I) (M := M) g₀ 0 2))
    (c : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) :
    deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
        (finiteEigenComboHs (I := I) (M := M) g₀ S c ((a : ℝ) + 2)) =
      deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a
        (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
          (ccTensor02Symm (I := I) (M := M) g₀ (finiteEigenCombo (I := I) (M := M) g₀ S c))) := by
  rw [gscr_finiteEigenComboHs_eq_smoothCcToTensorHs g₀ S c ((a : ℝ) + 2),
    deTurckSobolevNHa2Symm_smoothEmbed_eq (I := I) (M := M) g₀ g_bg a ha_super
      (finiteEigenCombo (I := I) (M := M) g₀ S c),
    ← deTurckSobolevNHa2_smoothEmbed_eq (I := I) (M := M) g₀ g_bg a ha_super
      (ccTensor02Symm (I := I) (M := M) g₀ (finiteEigenCombo (I := I) (M := M) g₀ S c))]

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in
private lemma deTurckSobolevNHa2Symm_zero_eq
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) :
    deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
        (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) =
      deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a
        (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) := by
  have hzero_embed : (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) =
      smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
        (0 : SmoothCcTensor g₀ 0 2) := by
    refine tensorHs.ext ?_
    funext i
    rw [tensorHs.zero_coeff, smoothCcToTensorHs_coeff,
      show SmoothCcTensor.toL2 (0 : SmoothCcTensor g₀ 0 2) = 0 from map_zero _,
      tensorL2Coeff_eq_inner, inner_zero_right]
  have hsymmS_zero : ccTensor02Symm (I := I) (M := M) g₀ (0 : SmoothCcTensor g₀ 0 2) =
      (0 : SmoothCcTensor g₀ 0 2) := by
    have h0 := symmS_smul (I := I) (M := M) g₀ (0 : ℝ) (0 : SmoothCcTensor g₀ 0 2)
    rw [zero_smul, zero_smul] at h0
    exact h0
  conv_lhs => rw [hzero_embed]
  rw [deTurckSobolevNHa2Symm_smoothEmbed_eq (I := I) (M := M) g₀ g_bg a ha_super
      (0 : SmoothCcTensor g₀ 0 2),
    ← deTurckSobolevNHa2_smoothEmbed_eq (I := I) (M := M) g₀ g_bg a ha_super
      (ccTensor02Symm (I := I) (M := M) g₀ (0 : SmoothCcTensor g₀ 0 2)),
    hsymmS_zero, ← hzero_embed]

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in

private theorem deTurckGalerkinForcingSymm_tame_diff_mass_perScale
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 4 * Module.finrank ℝ E + 10 ≤ a) {T : ℝ}
    (U : ℕ → ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) :
    ∃ (Cδ₀ : ℝ) (Ctame : ℕ → ℝ), 0 ≤ Cδ₀ ∧ Cδ₀ < 1 ∧ (∀ k, 0 ≤ Ctame k) ∧
      ∀ (N : ℕ) (k : ℕ), ∀ t ∈ Set.Ico (0 : ℝ) T,
        ∑ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
            tensorSobolevWeight (I := I) (M := M) i ((a : ℝ) + (k : ℝ) - 1) *
              ((deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
                  (finiteEigenComboHs (I := I) (M := M) g₀
                    (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t) ((a : ℝ) + 2))).coeff i -
                (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
                  (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))).coeff i) ^ 2 ≤
          Cδ₀ ^ 2 * galerkinEnergy (I := I) (M := M)
            (eigenIdxFinset (I := I) (M := M) g₀ N) (U N) ((a : ℝ) + (k : ℝ) + 1) t +
          Ctame k ^ 2 * galerkinEnergy (I := I) (M := M)
            (eigenIdxFinset (I := I) (M := M) g₀ N) (U N) ((a : ℝ) + (k : ℝ)) t := by
  classical
  have ha2 : 2 * Module.finrank ℝ E + 10 ≤ a := by omega
  obtain ⟨Cδ₀, Crem, hCδ₀_nn, hCδ₀_lt, hCrem_nn, hsplit⟩ :=
    deTurckSobolevNHa2_diff_sobolevSplit_perScale' (I := I) (M := M) g₀ g_bg a ha_super
      (Classical.choose_spec (deTurckSobolevNHa2_exists_of_super (I := I) (M := M) g₀ a ha2)).1
      (Classical.choose_spec (deTurckSobolevNHa2_exists_of_super (I := I) (M := M) g₀ a ha2)).2.1
      (Classical.choose_spec (deTurckSobolevNHa2_exists_of_super (I := I) (M := M) g₀ a ha2)).2.2
      (fun T' => deTurckSobolevNHa2_smoothEmbed_eq (I := I) (M := M) g₀ g_bg a ha2 T') U
  have hden_pos : 0 < 1 - Cδ₀ ^ 2 := by nlinarith [hCδ₀_nn, hCδ₀_lt]
  refine ⟨Real.sqrt ((1 + Cδ₀ ^ 2) / 2),
    fun k => Real.sqrt (Crem k ^ 2 * (1 + Cδ₀ ^ 2) / (1 - Cδ₀ ^ 2)),
    Real.sqrt_nonneg _,
    (Real.sqrt_lt' one_pos).mpr (by rw [one_pow]; nlinarith [hCδ₀_nn, hCδ₀_lt]),
    fun k => Real.sqrt_nonneg _, ?_⟩
  intro N k t _
  have hEq :
      ∑ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
          tensorSobolevWeight (I := I) (M := M) i ((a : ℝ) + (k : ℝ) - 1) *
            ((deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
                (finiteEigenComboHs (I := I) (M := M) g₀
                  (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t) ((a : ℝ) + 2))).coeff i -
              (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
                (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))).coeff i) ^ 2 =
        ∑ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
          tensorSobolevWeight (I := I) (M := M) i ((a : ℝ) + (k : ℝ) - 1) *
            ((deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a
                (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                  (ccTensor02Symm (I := I) (M := M) g₀
                    (finiteEigenCombo (I := I) (M := M) g₀
                      (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t))))).coeff i -
              (deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a
                (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))).coeff i) ^ 2 := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [deTurckSobolevNHa2Symm_finiteEigenComboHs_eq (I := I) (M := M) g₀ g_bg a ha2
        (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t),
      deTurckSobolevNHa2Symm_zero_eq (I := I) (M := M) g₀ g_bg a ha2]
  have hA_nn : 0 ≤ ∑ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
      tensorSobolevWeight (I := I) (M := M) i ((a : ℝ) + (k : ℝ) - 1) *
        ((deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a
            (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
              (ccTensor02Symm (I := I) (M := M) g₀
                (finiteEigenCombo (I := I) (M := M) g₀
                  (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t))))).coeff i -
          (deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))).coeff i) ^ 2 :=
    Finset.sum_nonneg (fun i _ =>
      mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i _) (sq_nonneg _))
  have hmass := mass_le_of_sqrt_split hA_nn
    (galerkinEnergy_nonneg (I := I) (M := M) (eigenIdxFinset (I := I) (M := M) g₀ N)
      (U N) ((a : ℝ) + (k : ℝ) + 1) t)
    (galerkinEnergy_nonneg (I := I) (M := M) (eigenIdxFinset (I := I) (M := M) g₀ N)
      (U N) ((a : ℝ) + (k : ℝ)) t)
    hCδ₀_nn hCδ₀_lt (hCrem_nn k) (hsplit N k t)
  have hsq1 : Real.sqrt ((1 + Cδ₀ ^ 2) / 2) ^ 2 = (1 + Cδ₀ ^ 2) / 2 :=
    Real.sq_sqrt (by positivity)
  have hsq2 : Real.sqrt (Crem k ^ 2 * (1 + Cδ₀ ^ 2) / (1 - Cδ₀ ^ 2)) ^ 2 =
      Crem k ^ 2 * (1 + Cδ₀ ^ 2) / (1 - Cδ₀ ^ 2) :=
    Real.sq_sqrt (div_nonneg (by positivity) hden_pos.le)
  have hfinal :
      ∑ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
          tensorSobolevWeight (I := I) (M := M) i ((a : ℝ) + (k : ℝ) - 1) *
            ((deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
                (finiteEigenComboHs (I := I) (M := M) g₀
                  (eigenIdxFinset (I := I) (M := M) g₀ N) (U N t) ((a : ℝ) + 2))).coeff i -
              (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
                (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))).coeff i) ^ 2 ≤
        Real.sqrt ((1 + Cδ₀ ^ 2) / 2) ^ 2 * galerkinEnergy (I := I) (M := M)
            (eigenIdxFinset (I := I) (M := M) g₀ N) (U N) ((a : ℝ) + (k : ℝ) + 1) t +
          Real.sqrt (Crem k ^ 2 * (1 + Cδ₀ ^ 2) / (1 - Cδ₀ ^ 2)) ^ 2 *
            galerkinEnergy (I := I) (M := M)
              (eigenIdxFinset (I := I) (M := M) g₀ N) (U N) ((a : ℝ) + (k : ℝ)) t := by
    rw [hEq, hsq1, hsq2]
    exact hmass
  exact hfinal

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in

private theorem deTurckGalerkinForcingSymm_seed_mass
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) :
    ∃ Cseed : ℕ → ℝ, (∀ k, 0 ≤ Cseed k) ∧
      ∀ (N : ℕ) (k : ℕ),
        ∑ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
            tensorSobolevWeight (I := I) (M := M) i ((a : ℝ) + (k : ℝ)) *
              ((deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
                (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))).coeff i) ^ 2 ≤
          Cseed k ^ 2 := by
  obtain ⟨Cseed, hCseed_nn, hb⟩ :=
    deTurckGalerkinForcing_seed_mass (I := I) (M := M) g₀ g_bg a ha_super
  refine ⟨Cseed, hCseed_nn, fun N k => ?_⟩
  calc ∑ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
        tensorSobolevWeight (I := I) (M := M) i ((a : ℝ) + (k : ℝ)) *
          ((deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))).coeff i) ^ 2
      = ∑ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
          tensorSobolevWeight (I := I) (M := M) i ((a : ℝ) + (k : ℝ)) *
            ((deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a
              (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))).coeff i) ^ 2 := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [deTurckSobolevNHa2Symm_zero_eq (I := I) (M := M) g₀ g_bg a ha_super]
    _ ≤ Cseed k ^ 2 := hb N k

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in

private theorem deTurckGalerkin_forcing_dissipation_perScaleSymm
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 4 * Module.finrank ℝ E + 10 ≤ a) {T : ℝ}
    (U : ℕ → ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ) :
    ∃ (Cδ : ℝ) (Cmid seed : ℕ → ℝ), Cδ < 2 ∧ (∀ k, 0 ≤ Cmid k) ∧
      ∀ (N : ℕ) (k : ℕ), ∀ t ∈ Set.Ico (0 : ℝ) T,
        2 * ∑ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
            tensorSobolevWeight (I := I) (M := M) i ((a : ℝ) + (k : ℝ)) *
              (U N t i * deTurckGalerkinForcingSymm (I := I) (M := M) g₀ g_bg a U N t i) ≤
          Cδ * galerkinEnergy (I := I) (M := M) (eigenIdxFinset (I := I) (M := M) g₀ N)
              (U N) ((a : ℝ) + (k : ℝ) + 1) t +
            Cmid k * galerkinEnergy (I := I) (M := M) (eigenIdxFinset (I := I) (M := M) g₀ N)
              (U N) ((a : ℝ) + (k : ℝ)) t +
            seed k *
              Real.sqrt (galerkinEnergy (I := I) (M := M)
                (eigenIdxFinset (I := I) (M := M) g₀ N) (U N) ((a : ℝ) + (k : ℝ)) t) := by
  classical
  have ha2 : 2 * Module.finrank ℝ E + 10 ≤ a := by omega
  obtain ⟨Cδ₀, Ctame, hCδ₀_nn, hCδ₀_lt, hCtame_nn, htame⟩ :=
    deTurckGalerkinForcingSymm_tame_diff_mass_perScale (I := I) (M := M) g₀ g_bg a ha_super
      (T := T) U
  obtain ⟨Cseed, hCseed_nn, hseed⟩ :=
    deTurckGalerkinForcingSymm_seed_mass (I := I) (M := M) g₀ g_bg a ha2
  refine ⟨1 + Cδ₀ ^ 2, fun k => Ctame k ^ 2, fun k => 2 * Cseed k,
    by nlinarith [hCδ₀_lt, hCδ₀_nn], fun k => by positivity, ?_⟩
  intro N k t ht
  set S := eigenIdxFinset (I := I) (M := M) g₀ N with hS
  set σ : ℝ := (a : ℝ) + (k : ℝ) with hσ
  set v := finiteEigenComboHs (I := I) (M := M) g₀ S (U N t) ((a : ℝ) + 2) with hv
  set w0 := deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
    (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) with hw0
  set w := deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a v with hw
  have hUcoeff : ∀ i ∈ S, U N t i = v.coeff i := by
    intro i hi
    rw [hv, finiteEigenComboHs_coeff, if_pos hi]
  have hFcoeff : ∀ i ∈ S, deTurckGalerkinForcingSymm (I := I) (M := M) g₀ g_bg a U N t i =
      w.coeff i := by
    intro i hi
    rw [deTurckGalerkinForcingSymm_apply, if_pos hi]
  have hLHS_eq :
      ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i σ *
          (U N t i * deTurckGalerkinForcingSymm (I := I) (M := M) g₀ g_bg a U N t i) =
        ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i σ *
          (v.coeff i * ((w.coeff i - w0.coeff i) + w0.coeff i)) := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [hUcoeff i hi, hFcoeff i hi]; ring
  have hsplit :
      ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i σ *
          (v.coeff i * ((w.coeff i - w0.coeff i) + w0.coeff i)) =
        (∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i σ *
            (v.coeff i * (w.coeff i - w0.coeff i))) +
          ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i σ *
            (v.coeff i * w0.coeff i) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_); ring
  have hEσ1 : galerkinEnergy (I := I) (M := M) S (U N) (σ + 1) t =
      ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i (σ + 1) * (v.coeff i) ^ 2 := by
    unfold galerkinEnergy
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [hUcoeff i hi]
  have hEσ : galerkinEnergy (I := I) (M := M) S (U N) σ t =
      ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i σ * (v.coeff i) ^ 2 := by
    unfold galerkinEnergy
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [hUcoeff i hi]
  have htame_k := htame N k t ht
  have hseed_k := hseed N k
  have hmass_general :
      ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i (σ - 1) *
          (w.coeff i - w0.coeff i) ^ 2 ≤
        Cδ₀ ^ 2 * galerkinEnergy (I := I) (M := M) S (U N) (σ + 1) t +
          Ctame k ^ 2 * galerkinEnergy (I := I) (M := M) S (U N) σ t := htame_k
  have hTame :
      2 * ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i σ *
          (v.coeff i * (w.coeff i - w0.coeff i)) ≤
        (1 + Cδ₀ ^ 2) * galerkinEnergy (I := I) (M := M) S (U N) (σ + 1) t +
          Ctame k ^ 2 * galerkinEnergy (I := I) (M := M) S (U N) σ t := by
    have hcs := two_mul_sum_crossScale_le_eps (I := I) (M := M) S σ
      (fun i => v.coeff i) (fun i => w.coeff i - w0.coeff i) (ε := 1) one_pos
    have hmass' :
        ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i (σ - 1) *
            (w.coeff i - w0.coeff i) ^ 2 ≤
          Cδ₀ ^ 2 * (∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i (σ + 1) *
              (v.coeff i) ^ 2) +
            Ctame k ^ 2 * ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i σ *
              (v.coeff i) ^ 2 := by
      rw [hEσ1, hEσ] at hmass_general; exact hmass_general
    rw [hEσ1, hEσ]
    calc 2 * ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i σ *
            (v.coeff i * (w.coeff i - w0.coeff i))
        ≤ 1 * (∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i (σ + 1) * (v.coeff i) ^ 2) +
            1⁻¹ * ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i (σ - 1) *
              (w.coeff i - w0.coeff i) ^ 2 := hcs
      _ ≤ (1 + Cδ₀ ^ 2) *
            (∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i (σ + 1) * (v.coeff i) ^ 2) +
            Ctame k ^ 2 * ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i σ *
              (v.coeff i) ^ 2 := by
          rw [one_mul, inv_one, one_mul]; nlinarith [hmass']
  have hSeed :
      2 * ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i σ * (v.coeff i * w0.coeff i) ≤
        2 * Cseed k *
          Real.sqrt (galerkinEnergy (I := I) (M := M) S (U N) σ t) := by
    have hmono : ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i σ * (w0.coeff i) ^ 2 ≤
        Cseed k ^ 2 := hseed_k
    have hbound := two_mul_sum_sameScale_le_sqrt (I := I) (M := M) S σ
      (fun i => v.coeff i) (fun i => w0.coeff i) (hCseed_nn k) hmono
    rw [hEσ]; exact hbound
  have hfinal :
      2 * ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i σ *
          (U N t i * deTurckGalerkinForcingSymm (I := I) (M := M) g₀ g_bg a U N t i) ≤
        (1 + Cδ₀ ^ 2) * galerkinEnergy (I := I) (M := M) S (U N) (σ + 1) t +
          Ctame k ^ 2 * galerkinEnergy (I := I) (M := M) S (U N) σ t +
          2 * Cseed k * Real.sqrt (galerkinEnergy (I := I) (M := M) S (U N) σ t) := by
    rw [hLHS_eq, hsplit, mul_add]
    have hEσ1nn := galerkinEnergy_nonneg (I := I) (M := M) S (U N) (σ + 1) t
    nlinarith [hTame, hSeed, hEσ1nn]
  exact hfinal

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in

theorem deTurckGalerkin_forcing_closure_perScaleSymm
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 4 * Module.finrank ℝ E + 10 ≤ a) {T : ℝ}
    (U : ℕ → ℝ → TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ)
    (hU0 : ∀ N, ∀ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N, U N 0 i = 0) :
    ∃ (Cδ : ℝ) (Cmid seed B0 : ℕ → ℝ), Cδ < 2 ∧ (∀ k, 0 ≤ Cmid k) ∧
      (∀ (N : ℕ) (k : ℕ), ∀ t ∈ Set.Ico (0 : ℝ) T,
        2 * ∑ i ∈ eigenIdxFinset (I := I) (M := M) g₀ N,
            tensorSobolevWeight (I := I) (M := M) i ((a : ℝ) + (k : ℝ)) *
              (U N t i * deTurckGalerkinForcingSymm (I := I) (M := M) g₀ g_bg a U N t i) ≤
          Cδ * galerkinEnergy (I := I) (M := M) (eigenIdxFinset (I := I) (M := M) g₀ N)
              (U N) ((a : ℝ) + (k : ℝ) + 1) t +
            Cmid k * galerkinEnergy (I := I) (M := M) (eigenIdxFinset (I := I) (M := M) g₀ N)
              (U N) ((a : ℝ) + (k : ℝ)) t +
            seed k *
              Real.sqrt (galerkinEnergy (I := I) (M := M)
                (eigenIdxFinset (I := I) (M := M) g₀ N) (U N) ((a : ℝ) + (k : ℝ)) t)) ∧
      (∀ (N : ℕ) (k : ℕ),
        galerkinEnergy (I := I) (M := M) (eigenIdxFinset (I := I) (M := M) g₀ N)
          (U N) ((a : ℝ) + (k : ℝ)) 0 ≤ B0 k) := by
  obtain ⟨Cδ, Cmid, seed, hCδ, hCmid, hdiss⟩ :=
    deTurckGalerkin_forcing_dissipation_perScaleSymm (I := I) (M := M) g₀ g_bg a ha_super
      (T := T) U
  refine ⟨Cδ, Cmid, seed, fun _ => 0, hCδ, hCmid, hdiss, ?_⟩
  intro N k
  have hzero : galerkinEnergy (I := I) (M := M) (eigenIdxFinset (I := I) (M := M) g₀ N)
      (U N) ((a : ℝ) + (k : ℝ)) 0 = 0 := by
    unfold galerkinEnergy
    refine Finset.sum_eq_zero (fun i hi => ?_)
    rw [hU0 N i hi]
    ring
  rw [hzero]

end

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
