import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RaisedKoszulCometricRaise


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma iteratedCovGrad_smul' (g : SmoothRiemannianMetric I M) (r s j : ℕ)
    (c : ℝ) (w : SmoothCcTensor g r s) :
    iteratedCovGrad (I := I) g r s j (c • w) = c • iteratedCovGrad (I := I) g r s j w := by
  induction j with
  | zero => simp only [iteratedCovGrad_zero]
  | succ j ih =>
    rw [iteratedCovGrad_succ, iteratedCovGrad_succ, ih, covGrad_smul]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma riemannianFiberNormSq_smul' (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (c : ℝ) (v : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (c • v) =
      c ^ 2 * riemannianFiberNormSq (I := I) (M := M) g r s x v := by
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (c • v),
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x v]
  rw [TensorRSSpace.toModel_smul, tensorInnerPointwise_smul_left,
    tensorInnerPointwise_smul_right]
  ring

omit [NeZero (Module.finrank ℝ E)] in
theorem rfns_iteratedCovGrad_symmS_le
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) (T : SmoothCcTensor g₀ 0 2)
    {R : ℝ}
    (hTjet : ∀ j : ℕ, j ≤ a + 1 → ∀ y : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) y
        ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection y) ≤ R ^ 2)
    (k : ℕ) (hk : k ≤ a + 1) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x
        ((iteratedCovGrad (I := I) g₀ 0 2 k (ccTensor02Symm (I := I) (M := M) g₀ T)).toSection x) ≤
      R ^ 2 := by
  have hswap_inv : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x
      ((iteratedCovGrad (I := I) g₀ 0 2 k
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x
        ((iteratedCovGrad (I := I) g₀ 0 2 k T).toSection x) :=
    riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) T k x
  set A := iteratedCovGrad (I := I) g₀ 0 2 k T with hA
  set B := iteratedCovGrad (I := I) g₀ 0 2 k
    (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T) with hB
  have hiter : iteratedCovGrad (I := I) g₀ 0 2 k (ccTensor02Symm (I := I) (M := M) g₀ T) =
      (1 / 2 : ℝ) • A + (1 / 2 : ℝ) • B := by
    rw [hA, hB]; exact iteratedCovGrad_symmS_eq (I := I) (M := M) g₀ T k
  have htoSec : ((iteratedCovGrad (I := I) g₀ 0 2 k
        (ccTensor02Symm (I := I) (M := M) g₀ T)).toSection x : TensorRSSpace 0 (2 + k) I x) =
      (1 / 2 : ℝ) • (A.toSection x) + (1 / 2 : ℝ) • (B.toSection x) := by
    rw [hiter]
    rw [show (((1 / 2 : ℝ) • A + (1 / 2 : ℝ) • B).toSection x) =
        ((1 / 2 : ℝ) • A).toSection x + ((1 / 2 : ℝ) • B).toSection x from by
      rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add]; rfl]
    rw [show (((1 / 2 : ℝ) • A).toSection x) = (1 / 2 : ℝ) • (A.toSection x) from by
        rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul]; rfl,
      show (((1 / 2 : ℝ) • B).toSection x) = (1 / 2 : ℝ) • (B.toSection x) from by
        rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul]; rfl]
  rw [htoSec]
  have hRA : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x (A.toSection x) ≤ R ^ 2 :=
    hTjet k hk x
  have hRB : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x (B.toSection x) ≤ R ^ 2 := by
    rw [hswap_inv]; exact hTjet k hk x
  calc riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x
          ((1 / 2 : ℝ) • (A.toSection x) + (1 / 2 : ℝ) • (B.toSection x))
      ≤ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x ((1 / 2 : ℝ) • (A.toSection x)) +
          2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x ((1 / 2 : ℝ) • (B.toSection x)) :=
        riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (2 + k) x _ _
    _ = (1 / 2 : ℝ) * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x (A.toSection x) +
          (1 / 2 : ℝ) * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x (B.toSection x) := by
        rw [riemannianFiberNormSq_smul', riemannianFiberNormSq_smul']; ring
    _ ≤ (1 / 2 : ℝ) * R ^ 2 + (1 / 2 : ℝ) * R ^ 2 := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hRA (by norm_num)
        · exact mul_le_mul_of_nonneg_left hRB (by norm_num)
    _ = R ^ 2 := by ring

omit [NeZero (Module.finrank ℝ E)] in
private lemma rfns_iteratedCovGrad_domDomCongr_symmSCovGrad3_le
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) (T : SmoothCcTensor g₀ 0 2)
    {R : ℝ}
    (hTjet : ∀ j : ℕ, j ≤ a + 1 → ∀ y : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) y
        ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection y) ≤ R ^ 2)
    (σ : Equiv.Perm (Fin 3)) (i : ℕ) (hi : i ≤ a) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
        ((iteratedCovGrad (I := I) g₀ 0 3 i
          (domDomCongrSection (I := I) g₀ σ (symmSCovGrad3 (I := I) g₀ T))).toSection x) ≤
      R ^ 2 := by
  rw [riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀ σ
    (symmSCovGrad3 (I := I) g₀ T) i x]
  have hcomm := rfns_iteratedCovGrad_covGrad_comm_rs (I := I) (M := M) g₀ 0 2 i
    (ccTensor02Symm (I := I) g₀ T) x
  have hbnd := rfns_iteratedCovGrad_symmS_le (I := I) (M := M) g₀ a T hTjet (i + 1) (by omega) x
  exact le_trans (le_of_eq hcomm) hbnd

omit [NeZero (Module.finrank ℝ E)] in
theorem rfns_iteratedCovGrad_koszulCovecCc_le
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) (T : SmoothCcTensor g₀ 0 2)
    {R : ℝ}
    (hTjet : ∀ j : ℕ, j ≤ a + 1 → ∀ y : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) y
        ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection y) ≤ R ^ 2)
    (i : ℕ) (hi : i ≤ a) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
        ((iteratedCovGrad (I := I) g₀ 0 3 i (koszulCovecCc (I := I) g₀ T)).toSection x) ≤
      10 * R ^ 2 := by
  set W : SmoothCcTensor g₀ 0 3 := symmSCovGrad3 (I := I) g₀ T with hW
  set DA : SmoothCcTensor g₀ 0 3 :=
    domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 2) W with hDA
  set DB : SmoothCcTensor g₀ 0 3 := domDomCongrSection (I := I) g₀ (finRotate 3) W with hDB
  set DC : SmoothCcTensor g₀ 0 3 :=
    domDomCongrSection (I := I) g₀ (Equiv.swap (1 : Fin 3) 2) W with hDC
  have hkos : koszulCovecCc (I := I) g₀ T = (1 / 2 : ℝ) • (DA + DB - DC) := by
    rw [koszulCovecCc, hDA, hDB, hDC, hW]
  have hiter : iteratedCovGrad (I := I) g₀ 0 3 i (koszulCovecCc (I := I) g₀ T) =
      (1 / 2 : ℝ) • iteratedCovGrad (I := I) g₀ 0 3 i (DA + DB - DC) := by
    rw [hkos, iteratedCovGrad_smul']
  have hsub : iteratedCovGrad (I := I) g₀ 0 3 i (DA + DB - DC) =
      iteratedCovGrad (I := I) g₀ 0 3 i DA + iteratedCovGrad (I := I) g₀ 0 3 i DB -
        iteratedCovGrad (I := I) g₀ 0 3 i DC := by
    rw [sub_eq_add_neg, sub_eq_add_neg, iteratedCovGrad_add, iteratedCovGrad_add,
      iteratedCovGrad_neg]
  have htoSec : ((iteratedCovGrad (I := I) g₀ 0 3 i (koszulCovecCc (I := I) g₀ T)).toSection x :
        TensorRSSpace 0 (3 + i) I x) =
      (1 / 2 : ℝ) • ((iteratedCovGrad (I := I) g₀ 0 3 i DA).toSection x +
        (iteratedCovGrad (I := I) g₀ 0 3 i DB).toSection x -
        (iteratedCovGrad (I := I) g₀ 0 3 i DC).toSection x) := by
    rw [hiter, hsub]
    simp only [SmoothCcTensor.toSection_smul, SmoothCcTensor.toSection_sub,
      SmoothCcTensor.toSection_add, ContMDiffSection.coe_smul, ContMDiffSection.coe_sub,
      ContMDiffSection.coe_add, Pi.smul_apply, Pi.sub_apply, Pi.add_apply]
  set PA := (iteratedCovGrad (I := I) g₀ 0 3 i DA).toSection x with hPA
  set PB := (iteratedCovGrad (I := I) g₀ 0 3 i DB).toSection x with hPB
  set PC := (iteratedCovGrad (I := I) g₀ 0 3 i DC).toSection x with hPC
  have hbA : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x PA ≤ R ^ 2 :=
    rfns_iteratedCovGrad_domDomCongr_symmSCovGrad3_le (I := I) (M := M) g₀ a T hTjet
      (Equiv.swap (0 : Fin 3) 2) i hi x
  have hbB : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x PB ≤ R ^ 2 :=
    rfns_iteratedCovGrad_domDomCongr_symmSCovGrad3_le (I := I) (M := M) g₀ a T hTjet
      (finRotate 3) i hi x
  have hbC : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x PC ≤ R ^ 2 :=
    rfns_iteratedCovGrad_domDomCongr_symmSCovGrad3_le (I := I) (M := M) g₀ a T hTjet
      (Equiv.swap (1 : Fin 3) 2) i hi x
  rw [htoSec, riemannianFiberNormSq_smul']
  have hnegC : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x (-PC) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x PC := by
    have hh := riemannianFiberNormSq_smul' (I := I) (M := M) g₀ 0 (3 + i) x (-1 : ℝ) PC
    rw [neg_one_smul] at hh
    rw [hh]; norm_num
  have hsum : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x (PA + PB - PC) ≤
      4 * R ^ 2 + 4 * R ^ 2 + 2 * R ^ 2 := by
    have h1 := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (3 + i) x (PA + PB) (-PC)
    have h2 := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (3 + i) x PA PB
    rw [hnegC] at h1
    rw [show PA + PB - PC = (PA + PB) + (-PC) from sub_eq_add_neg _ _]
    nlinarith [h1, h2, hbA, hbB, hbC,
      riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (3 + i) x PA,
      riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (3 + i) x PB,
      riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (3 + i) x PC]
  nlinarith [hsum, sq_nonneg R,
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (3 + i) x (PA + PB - PC)]

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
