import DifferentialGeometry.Geometry.Connection.TensorNabla.OperatorFieldSecondGradientRefold
import DifferentialGeometry.Geometry.Flow.DeTurckVFConnDiffVariation
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciThreeArmCorrectionFieldBound
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciLinearizationArmFields
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciPathPalatiniLinearization
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifference
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTower
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderDefs
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.DeTurckLieHigherOrderCoeffField
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLieKernelL2JetBound
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLieCoeffL2JetBound
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.CurvatureRefoldMonomialFibreNormBound
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciArmResidualCoefficientFields
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RicciArmResidualFieldGridWindow
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RiemannCoefficientPalatiniRefoldFamilyJointSmoothness
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RiemannCoefficientPalatiniRefoldLieCovDerivFamily
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RiemannCoefficientPalatiniRefoldEndoArmGridWindow
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RiemannCoefficientPalatiniRefoldCovDerivArmPairTrace
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RiemannCoefficientPalatiniRefoldLinearizedRefoldIdentity
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RiemannCoefficientPalatiniRefoldMonomialRefoldL2JetWindow
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RiemannCoefficientPalatiniRefoldRicciFoldWeightKernel
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RiemannCoefficientPalatiniRefoldSharpGradKoszulResidualSmoothness

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle MeasureTheory
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] in
lemma bdRfns_iCG_koszulCovecCc_le (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (i : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
        ((iteratedCovGrad (I := I) g₀ 0 3 i (koszulCovecCc (I := I) g₀ T)).toSection x) ≤
      10 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 1)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (i + 1) T).toSection x) := by
  classical
  set W : SmoothCcTensor g₀ 0 3 := symmSCovGrad3 (I := I) g₀ T with hW
  set DA : SmoothCcTensor g₀ 0 3 :=
    domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 2) W with hDA
  set DB : SmoothCcTensor g₀ 0 3 := domDomCongrSection (I := I) g₀ (finRotate 3) W with hDB
  set DC : SmoothCcTensor g₀ 0 3 :=
    domDomCongrSection (I := I) g₀ (Equiv.swap (1 : Fin 3) 2) W with hDC
  have hpermW : ∀ σ : Equiv.Perm (Fin 3),
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
        ((iteratedCovGrad (I := I) g₀ 0 3 i
          (domDomCongrSection (I := I) g₀ σ W)).toSection x) ≤
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 1)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (i + 1) T).toSection x) := by
    intro σ
    rw [riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀ σ W i x]
    rw [hW]
    rw [show symmSCovGrad3 (I := I) g₀ T =
        covGrad (I := I) (M := M) g₀ 0 2 (ccTensor02Symm (I := I) g₀ T) from rfl]
    have hcomm := rfns_iteratedCovGrad_covGrad_comm_rs (I := I) (M := M) g₀ 0 2 i
      (ccTensor02Symm (I := I) g₀ T) x
    rw [hcomm]
    exact bdRfns_iCG_symmS_le (I := I) (M := M) g₀ T (i + 1) x
  have hkos : koszulCovecCc (I := I) g₀ T = (1 / 2 : ℝ) • (DA + DB - DC) := by
    rw [koszulCovecCc, hDA, hDB, hDC, hW]
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
    rw [hkos, iteratedCovGrad_smul_real, hsub]
    rw [show (((1 / 2 : ℝ) • (iteratedCovGrad (I := I) g₀ 0 3 i DA +
          iteratedCovGrad (I := I) g₀ 0 3 i DB -
          iteratedCovGrad (I := I) g₀ 0 3 i DC)).toSection x) =
        (1 / 2 : ℝ) • ((iteratedCovGrad (I := I) g₀ 0 3 i DA +
          iteratedCovGrad (I := I) g₀ 0 3 i DB -
          iteratedCovGrad (I := I) g₀ 0 3 i DC).toSection x) from by
      rw [SmoothCcTensor.toSection_smul]; rfl]
    rw [show ((iteratedCovGrad (I := I) g₀ 0 3 i DA +
          iteratedCovGrad (I := I) g₀ 0 3 i DB -
          iteratedCovGrad (I := I) g₀ 0 3 i DC).toSection x) =
        (iteratedCovGrad (I := I) g₀ 0 3 i DA).toSection x +
          (iteratedCovGrad (I := I) g₀ 0 3 i DB).toSection x -
          (iteratedCovGrad (I := I) g₀ 0 3 i DC).toSection x from by
      rw [SmoothCcTensor.toSection_sub, SmoothCcTensor.toSection_add]; rfl]
  set PA := (iteratedCovGrad (I := I) g₀ 0 3 i DA).toSection x with hPA
  set PB := (iteratedCovGrad (I := I) g₀ 0 3 i DB).toSection x with hPB
  set PC := (iteratedCovGrad (I := I) g₀ 0 3 i DC).toSection x with hPC
  set R2 : ℝ := riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 1)) x
    ((iteratedCovGrad (I := I) g₀ 0 2 (i + 1) T).toSection x) with hR2
  have hbA : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x PA ≤ R2 :=
    hpermW (Equiv.swap (0 : Fin 3) 2)
  have hbB : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x PB ≤ R2 :=
    hpermW (finRotate 3)
  have hbC : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x PC ≤ R2 :=
    hpermW (Equiv.swap (1 : Fin 3) 2)
  rw [htoSec, riemannianFiberNormSq_smul (I := I) (M := M) g₀ 0 (3 + i) x]
  have hnegC : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x (-PC) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x PC :=
    bdRfns_neg (I := I) (M := M) g₀ 0 (3 + i) x PC
  have hR2_nn : 0 ≤ R2 := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + (i + 1)) x _
  have hsum : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x (PA + PB - PC) ≤
      10 * R2 := by
    have h1 := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (3 + i) x (PA + PB) (-PC)
    have h2 := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (3 + i) x PA PB
    rw [hnegC] at h1
    rw [show PA + PB - PC = (PA + PB) + (-PC) from sub_eq_add_neg _ _]
    nlinarith [h1, h2, hbA, hbB, hbC,
      riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (3 + i) x PA,
      riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (3 + i) x PB,
      riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (3 + i) x PC]
  nlinarith [hsum, hR2_nn,
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (3 + i) x (PA + PB - PC)]

omit [NeZero (Module.finrank ℝ E)] in
lemma riemannianFiberNormSq_iteratedCovGrad_bdKRaw_le (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (i : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
        ((iteratedCovGrad (I := I) g₀ 0 3 i (koszulCovGradRaw (I := I) (M := M) g₀ T)).toSection x) ≤
      10 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 1)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (i + 1) T).toSection x) := by
  classical
  set W : SmoothCcTensor g₀ 0 3 := covGrad (I := I) (M := M) g₀ 0 2 T with hW
  set DA : SmoothCcTensor g₀ 0 3 :=
    domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 2) W with hDA
  set DB : SmoothCcTensor g₀ 0 3 := domDomCongrSection (I := I) g₀ (finRotate 3) W with hDB
  set DC : SmoothCcTensor g₀ 0 3 :=
    domDomCongrSection (I := I) g₀ (Equiv.swap (1 : Fin 3) 2) W with hDC
  have hpermW : ∀ σ : Equiv.Perm (Fin 3),
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
        ((iteratedCovGrad (I := I) g₀ 0 3 i
          (domDomCongrSection (I := I) g₀ σ W)).toSection x) ≤
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 1)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (i + 1) T).toSection x) := by
    intro σ
    rw [riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀ σ W i x]
    rw [hW]
    have hcomm := rfns_iteratedCovGrad_covGrad_comm_rs (I := I) (M := M) g₀ 0 2 i T x
    rw [hcomm]
  have hkos : koszulCovGradRaw (I := I) (M := M) g₀ T = (1 / 2 : ℝ) • (DA + DB - DC) := by
    rw [koszulCovGradRaw, hDA, hDB, hDC, hW]
  have hsub : iteratedCovGrad (I := I) g₀ 0 3 i (DA + DB - DC) =
      iteratedCovGrad (I := I) g₀ 0 3 i DA + iteratedCovGrad (I := I) g₀ 0 3 i DB -
        iteratedCovGrad (I := I) g₀ 0 3 i DC := by
    rw [sub_eq_add_neg, sub_eq_add_neg, iteratedCovGrad_add, iteratedCovGrad_add,
      iteratedCovGrad_neg]
  have htoSec : ((iteratedCovGrad (I := I) g₀ 0 3 i
        (koszulCovGradRaw (I := I) (M := M) g₀ T)).toSection x :
        TensorRSSpace 0 (3 + i) I x) =
      (1 / 2 : ℝ) • ((iteratedCovGrad (I := I) g₀ 0 3 i DA).toSection x +
        (iteratedCovGrad (I := I) g₀ 0 3 i DB).toSection x -
        (iteratedCovGrad (I := I) g₀ 0 3 i DC).toSection x) := by
    rw [hkos, iteratedCovGrad_smul_real, hsub]
    rw [show (((1 / 2 : ℝ) • (iteratedCovGrad (I := I) g₀ 0 3 i DA +
          iteratedCovGrad (I := I) g₀ 0 3 i DB -
          iteratedCovGrad (I := I) g₀ 0 3 i DC)).toSection x) =
        (1 / 2 : ℝ) • ((iteratedCovGrad (I := I) g₀ 0 3 i DA +
          iteratedCovGrad (I := I) g₀ 0 3 i DB -
          iteratedCovGrad (I := I) g₀ 0 3 i DC).toSection x) from by
      rw [SmoothCcTensor.toSection_smul]; rfl]
    rw [show ((iteratedCovGrad (I := I) g₀ 0 3 i DA +
          iteratedCovGrad (I := I) g₀ 0 3 i DB -
          iteratedCovGrad (I := I) g₀ 0 3 i DC).toSection x) =
        (iteratedCovGrad (I := I) g₀ 0 3 i DA).toSection x +
          (iteratedCovGrad (I := I) g₀ 0 3 i DB).toSection x -
          (iteratedCovGrad (I := I) g₀ 0 3 i DC).toSection x from by
      rw [SmoothCcTensor.toSection_sub, SmoothCcTensor.toSection_add]; rfl]
  set PA := (iteratedCovGrad (I := I) g₀ 0 3 i DA).toSection x with hPA
  set PB := (iteratedCovGrad (I := I) g₀ 0 3 i DB).toSection x with hPB
  set PC := (iteratedCovGrad (I := I) g₀ 0 3 i DC).toSection x with hPC
  set R2 : ℝ := riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 1)) x
    ((iteratedCovGrad (I := I) g₀ 0 2 (i + 1) T).toSection x) with hR2
  have hbA : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x PA ≤ R2 :=
    hpermW (Equiv.swap (0 : Fin 3) 2)
  have hbB : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x PB ≤ R2 :=
    hpermW (finRotate 3)
  have hbC : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x PC ≤ R2 :=
    hpermW (Equiv.swap (1 : Fin 3) 2)
  rw [htoSec, riemannianFiberNormSq_smul (I := I) (M := M) g₀ 0 (3 + i) x]
  have hnegC : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x (-PC) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x PC :=
    bdRfns_neg (I := I) (M := M) g₀ 0 (3 + i) x PC
  have hR2_nn : 0 ≤ R2 := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + (i + 1)) x _
  have hsum : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x (PA + PB - PC) ≤
      10 * R2 := by
    have h1 := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (3 + i) x (PA + PB) (-PC)
    have h2 := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (3 + i) x PA PB
    rw [hnegC] at h1
    rw [show PA + PB - PC = (PA + PB) + (-PC) from sub_eq_add_neg _ _]
    nlinarith [h1, h2, hbA, hbB, hbC,
      riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (3 + i) x PA,
      riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (3 + i) x PB,
      riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (3 + i) x PC]
  nlinarith [hsum, hR2_nn,
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (3 + i) x (PA + PB - PC)]

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
omit [BoundarylessManifold I M] in
theorem exists_sobolevConst_riemannianFiberNormSq_covGrad_T_le_sq (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) :
    ∃ Csob : ℝ, 0 ≤ Csob ∧
      ∀ (T : SmoothCcTensor g₀ 0 2) {R : ℝ} (_hR : 0 ≤ R),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 1) x
            ((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x) ≤
            (Csob * R) ^ 2 := by
  classical
  obtain ⟨Csob, hCsob_nn, hCsob⟩ :=
    exists_Csob_convexPerturbation_pointwise_C2_le (I := I) (M := M) g₀ a ha_super
  refine ⟨Csob, hCsob_nn, ?_⟩
  intro T R hR hball x
  have hball0 : ∀ j : ℕ, j ≤ a + 2 →
      ‖iteratedCovGrad (I := I) g₀ 0 2 j (0 : SmoothCcTensor g₀ 0 2)‖ ≤ R := by
    intro j hj
    rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • T from (zero_smul ℝ T).symm,
      iteratedCovGrad_smul_real, norm_smul, Real.norm_eq_abs, abs_zero, zero_mul]
    exact hR
  have hsum := hCsob T 0 hR hball hball0 1 ⟨by norm_num, le_refl 1⟩ x
  have hterms : ∀ k ∈ Finset.range 3, 0 ≤
      (letI : Bundle.RiemannianBundle
          (fun b : M => Tensor0SBundle.TensorRSSpace 0 (2 + k) I b) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + k)
      ‖(iteratedCovGrad (I := I) g₀ 0 2 k
          (convexPerturbation (I := I) g₀ T 0 1)).toSection x‖) := by
    intro k _
    letI : Bundle.RiemannianBundle
        (fun b : M => Tensor0SBundle.TensorRSSpace 0 (2 + k) I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + k)
    exact norm_nonneg _
  have h0 := le_trans (Finset.single_le_sum hterms
    (show (1 : ℕ) ∈ Finset.range 3 from Finset.mem_range.mpr (by norm_num))) hsum
  have hcp1 : convexPerturbation (I := I) g₀ T 0 1 = T := by
    rw [convexPerturbation, smul_zero, zero_add, one_smul]
  rw [hcp1] at h0
  letI : Bundle.RiemannianBundle (fun b : M => Tensor0SBundle.TensorRSSpace 0 (2 + 1) I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + 1)
  have h0' : ‖((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x :
      Tensor0SBundle.TensorRSSpace 0 (2 + 1) I x)‖ ≤ Csob * R := h0
  have hb : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 1) x
      ((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x) =
      ‖((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x :
        Tensor0SBundle.TensorRSSpace 0 (2 + 1) I x)‖ ^ 2 :=
    riemannianFiberNormSq_eq_bundle_norm_sq' (I := I) (M := M) g₀ 0 (2 + 1) x
      ((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x)
  have hnn : (0 : ℝ) ≤ ‖((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x :
      Tensor0SBundle.TensorRSSpace 0 (2 + 1) I x)‖ :=
    norm_nonneg _
  nlinarith [h0', hb, hnn, mul_nonneg hCsob_nn hR]


theorem exists_ricciArmSharpGradKoszulResidualField_realizedFam_riemannianFiberNormSq_uniformBound
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ (T : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
              ((ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T 0 hδ hδZ s) (s • T)).toSection x) ≤ Λ := by
  classical
  set δ₁ : ℝ := max δ₀ 0 with hδ₁_def
  have hδ₁_lt : δ₁ < 1 := max_lt hδ₀ one_pos
  obtain ⟨CP, hCP_nn, hCP⟩ := bdPairTraceOp_tgrid (I := I) (M := M) g₀ hδ₁_lt
  obtain ⟨C4, hC4_nn, hC4⟩ := bdPureDT_tgrid (I := I) (M := M) g₀ 4 hδ₁_lt
  obtain ⟨Csob1, hCsob1_nn, hcap1⟩ :=
    exists_sobolevConst_riemannianFiberNormSq_covGrad_T_le_sq (I := I) (M := M) g₀ a ha_super
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : 0 ≤ fr := Nat.cast_nonneg _
  set ZB : ℝ := fr * (fr * (fr *
    ((10 * (Csob1 * R) ^ 2) * (10 * (Csob1 * R) ^ 2)))) with hZB_def
  have hZB_nn : 0 ≤ ZB := by positivity
  refine ⟨4 * (CP 0 * (fr * (fr * (16 * (C4 0 * ZB))))),
    mul_nonneg (by norm_num) (mul_nonneg (hCP_nn 0) (mul_nonneg hfr_nn (mul_nonneg hfr_nn
      (mul_nonneg (by norm_num) (mul_nonneg (hC4_nn 0) hZB_nn))))), ?_⟩
  intro T δ hδ_le hδ hδZ hball s hs x
  by_cases hM : Nonempty M
  swap
  · exact ((not_nonempty_iff.mp hM).false x).elim
  obtain ⟨x₀⟩ := hM
  have hδ0 : 0 ≤ δ := bdDelta_nonneg (I := I) (M := M) g₀ x₀ T hδ
  have hδ_le' : δ ≤ δ₁ := le_trans hδ_le (le_max_left _ _)
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hs_mem : s ∈ realizedSmallSet (δ := δ) (δ' := δ) :=
    Icc_subset_realizedSmallSet hδ_lt hδ_lt hs
  obtain ⟨hs0, hs1⟩ := hs
  have htie0 : ∀ (y : M) (v w : TangentSpace I y),
      (realizedFam (I := I) g₀ T 0 hδ hδZ s).inner y v w =
        g₀.inner y v w +
          ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T 0 s) y v w :=
    fun y v w => realizedFam_inner_of_mem (I := I) g₀ T 0 hδ hδZ hs_mem y v w
  have hδP : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T 0 s)) δ := by
    intro y v w
    have hraw := convexPerturbation_gFibreOpBound_abs (I := I) g₀ T 0 hδ hδZ s y v w
    have heq : |1 - s| * δ + |s| * δ = δ := by
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - s), abs_of_nonneg hs0]
      ring
    rwa [heq] at hraw
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      (realizedFam (I := I) g₀ T 0 hδ hδZ s).inner y v w =
        g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ (s • T) y v w := by
    intro y v w
    have h0 := htie0 y v w
    rwa [show convexPerturbation (I := I) g₀ T 0 s = s • T from by
      rw [convexPerturbation, smul_zero, zero_add]] at h0
  have hfield : ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) (s • T) =
      ((2 : ℝ) * (s * s)) •
        ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
        (armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s))
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau1 T T +
      sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau2 T T) -
      (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau3 T T +
      sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau4 T T)))) := by
    rw [bdSGK_eq_refold (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s)
      (s • T) (s • T) htie]
    rw [bdSGKXi_smul (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s) T s]
    rw [appCcRS_smul_right (I := I) (M := M) g₀ 2 6 2 (s * s)
      (armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s))
      (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2
          ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau1 T T +
      sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau2 T T) -
      (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau3 T T +
      sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau4 T T))))]
    rw [smul_smul]
  rw [hfield]
  rw [show ((((2 : ℝ) * (s * s)) •
      ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
        (armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s))
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau1 T T +
      sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau2 T T) -
      (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau3 T T +
      sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau4 T T))))).toSection x) =
      ((2 : ℝ) * (s * s)) •
        ((ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
        (armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s))
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau1 T T +
      sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau2 T T) -
      (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau3 T T +
      sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau4 T T))))).toSection x) from by
    rw [SmoothCcTensor.toSection_smul]; rfl]
  rw [riemannianFiberNormSq_smul (I := I) (M := M) g₀ 2 2 x]
  have hss : 0 ≤ s * s := mul_nonneg hs0 hs0
  have hs2 : s * s ≤ 1 := by nlinarith
  have hsq1 : ((2 : ℝ) * (s * s)) ^ 2 ≤ 4 := by nlinarith [hss, hs2]
  have hcomp : riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
      ((ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
        (armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s))
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau1 T T +
      sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau2 T T) -
      (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau3 T T +
      sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau4 T T))))).toSection x) ≤
      riemannianFiberNormSq (I := I) (M := M) g₀ 6 2 x
          ((armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s)).toSection x) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 6 x
          ((rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau1 T T +
      sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau2 T T) -
      (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau3 T T +
      sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau4 T T)))).toSection x) := by
    rw [appCcRS_toSection]
    exact riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ 2 6 2 x _ _
  have hPTO : riemannianFiberNormSq (I := I) (M := M) g₀ 6 2 x
      ((armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s)).toSection x) ≤ CP 0 := by
    have h := hCP (realizedFam (I := I) g₀ T 0 hδ hδZ s)
      (convexPerturbation (I := I) g₀ T 0 s) htie0 hδ_le' hδ0 hδP 0 x
    rw [iteratedCovGrad_zero] at h
    refine le_trans h (le_of_eq ?_)
    rw [Combinatorics.antidiagonalTupleGridWindow, Finset.sum_range_one,
      Combinatorics.antidiagonalTupleGrid_zero, mul_one]
  have hDT4cap : riemannianFiberNormSq (I := I) (M := M) g₀ 6 4 x
      ((cometricDoubleTraceCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s) 4).toSection x) ≤ C4 0 := by
    have h := hC4 (realizedFam (I := I) g₀ T 0 hδ hδZ s)
      (convexPerturbation (I := I) g₀ T 0 s) htie0 hδ_le' hδ0 hδP 0 x
    rw [iteratedCovGrad_zero] at h
    refine le_trans h (le_of_eq ?_)
    rw [Combinatorics.antidiagonalTupleGridWindow, Finset.sum_range_one,
      Combinatorics.antidiagonalTupleGrid_zero, mul_one]
  have hcapT1 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 1) x
      ((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x) ≤ (Csob1 * R) ^ 2 :=
    hcap1 T hR hball x
  have hKRawcap : riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
      ((koszulCovGradRaw (I := I) (M := M) g₀ T).toSection x) ≤
      10 * (Csob1 * R) ^ 2 := by
    have h := riemannianFiberNormSq_iteratedCovGrad_bdKRaw_le (I := I) (M := M) g₀ T 0 x
    rw [iteratedCovGrad_zero] at h
    refine le_trans h ?_
    have h10 : (0 : ℝ) ≤ 10 := by norm_num
    exact mul_le_mul_of_nonneg_left hcapT1 h10
  have hKcap : riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
      ((koszulCovecCc (I := I) g₀ T).toSection x) ≤
      10 * (Csob1 * R) ^ 2 := by
    have h := bdRfns_iCG_koszulCovecCc_le (I := I) (M := M) g₀ T 0 x
    rw [iteratedCovGrad_zero] at h
    refine le_trans h ?_
    have h10 : (0 : ℝ) ≤ 10 := by norm_num
    exact mul_le_mul_of_nonneg_left hcapT1 h10
  have hslotK : riemannianFiberNormSq (I := I) (M := M) g₀ 3 6 x
      ((slotExtendIter (I := I) (M := M) g₀ 0 3 3
        (koszulCovGradRaw (I := I) (M := M) g₀ T)).toSection x) ≤
      fr * (fr * (fr * (10 * (Csob1 * R) ^ 2))) := by
    have h3 := rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 2 5
      (slotExtendIter (I := I) (M := M) g₀ 0 3 2 (koszulCovGradRaw (I := I) (M := M) g₀ T)) 0 x
    rw [iteratedCovGrad_zero, iteratedCovGrad_zero] at h3
    have h2 := rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 1 4
      (slotExtendIter (I := I) (M := M) g₀ 0 3 1 (koszulCovGradRaw (I := I) (M := M) g₀ T)) 0 x
    rw [iteratedCovGrad_zero, iteratedCovGrad_zero] at h2
    have h1 := rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 0 3
      (koszulCovGradRaw (I := I) (M := M) g₀ T) 0 x
    rw [iteratedCovGrad_zero, iteratedCovGrad_zero] at h1
    have hnn2 : (0 : ℝ) ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 2 5 x
        ((slotExtendIter (I := I) (M := M) g₀ 0 3 2
          (koszulCovGradRaw (I := I) (M := M) g₀ T)).toSection x) :=
      riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 5 x _
    have hnn1 : (0 : ℝ) ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 1 4 x
        ((slotExtendIter (I := I) (M := M) g₀ 0 3 1
          (koszulCovGradRaw (I := I) (M := M) g₀ T)).toSection x) :=
      riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 4 x _
    refine le_trans h3 ?_
    refine mul_le_mul_of_nonneg_left (le_trans h2 ?_) hfr_nn
    refine mul_le_mul_of_nonneg_left (le_trans h1 ?_) hfr_nn
    exact mul_le_mul_of_nonneg_left hKRawcap hfr_nn
  have hZcap : ∀ τ : Equiv.Perm (Fin 6),
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 6 x
        ((rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 τ
          (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
            (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovGradRaw (I := I) (M := M) g₀ T))
            (koszulCovecCc (I := I) g₀ T))).toSection x) ≤ ZB := by
    intro τ
    have hperm : riemannianFiberNormSq (I := I) (M := M) g₀ 0 6 x
        ((rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 τ
          (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
            (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovGradRaw (I := I) (M := M) g₀ T))
            (koszulCovecCc (I := I) g₀ T))).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 6 x
          ((ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
            (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovGradRaw (I := I) (M := M) g₀ T))
            (koszulCovecCc (I := I) g₀ T)).toSection x) := by
      have h := riemannianFiberNormSq_iteratedCovGrad_rs_eq_of_section_domDomCongr (I := I) (M := M)
        g₀ 0 6 τ
        (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
          (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovGradRaw (I := I) (M := M) g₀ T))
          (koszulCovecCc (I := I) g₀ T))
        (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 τ
          (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
            (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovGradRaw (I := I) (M := M) g₀ T))
            (koszulCovecCc (I := I) g₀ T)))
        (fun y d => by
          rw [rsDomDomCongrSection_toSection, toModel_rsDomDomCongr_apply]) 0 x
      rwa [iteratedCovGrad_zero, iteratedCovGrad_zero] at h
    rw [hperm]
    have hc2 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 6 x
        ((ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
          (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovGradRaw (I := I) (M := M) g₀ T))
          (koszulCovecCc (I := I) g₀ T)).toSection x) ≤
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 6 x
            ((slotExtendIter (I := I) (M := M) g₀ 0 3 3
              (koszulCovGradRaw (I := I) (M := M) g₀ T)).toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
            ((koszulCovecCc (I := I) g₀ T).toSection x) := by
      rw [appCcRS_toSection]
      exact riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ 0 3 6 x _ _
    refine le_trans hc2 ?_
    rw [hZB_def]
    have hknn : (0 : ℝ) ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
        ((koszulCovecCc (I := I) g₀ T).toSection x) :=
      riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 3 x _
    have hslnn : (0 : ℝ) ≤ fr * (fr * (fr * (10 * (Csob1 * R) ^ 2))) := by positivity
    refine le_trans (mul_le_mul hslotK hKcap hknn hslnn) (le_of_eq (by ring))
  have hW1 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 4 x
      ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau1 T T).toSection x) ≤ C4 0 * ZB := by
    have hcw : riemannianFiberNormSq (I := I) (M := M) g₀ 0 4 x
        ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau1 T T).toSection x) ≤
        riemannianFiberNormSq (I := I) (M := M) g₀ 6 4 x
            ((cometricDoubleTraceCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s) 4).toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 6 x
            ((rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 bdSGKTau1
        (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
          (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovGradRaw (I := I) (M := M) g₀ T))
          (koszulCovecCc (I := I) g₀ T))).toSection x) := by
      rw [show sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau1 T T =
          ccOperatorFieldComp (I := I) (M := M) g₀ 0 6 4
            (cometricDoubleTraceCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s) 4)
            (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 bdSGKTau1
        (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
          (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovGradRaw (I := I) (M := M) g₀ T))
          (koszulCovecCc (I := I) g₀ T))) from rfl]
      rw [appCcRS_toSection]
      exact riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ 0 6 4 x _ _
    refine le_trans hcw ?_
    have hz := hZcap bdSGKTau1
    have hznn : (0 : ℝ) ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 0 6 x
        ((rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 bdSGKTau1
        (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
          (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovGradRaw (I := I) (M := M) g₀ T))
          (koszulCovecCc (I := I) g₀ T))).toSection x) :=
      riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 6 x _
    refine le_trans (mul_le_mul_of_nonneg_right hDT4cap hznn) ?_
    exact mul_le_mul_of_nonneg_left hz (hC4_nn 0)
  have hW2 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 4 x
      ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau2 T T).toSection x) ≤ C4 0 * ZB := by
    have hcw : riemannianFiberNormSq (I := I) (M := M) g₀ 0 4 x
        ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau2 T T).toSection x) ≤
        riemannianFiberNormSq (I := I) (M := M) g₀ 6 4 x
            ((cometricDoubleTraceCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s) 4).toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 6 x
            ((rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 bdSGKTau2
        (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
          (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovGradRaw (I := I) (M := M) g₀ T))
          (koszulCovecCc (I := I) g₀ T))).toSection x) := by
      rw [show sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau2 T T =
          ccOperatorFieldComp (I := I) (M := M) g₀ 0 6 4
            (cometricDoubleTraceCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s) 4)
            (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 bdSGKTau2
        (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
          (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovGradRaw (I := I) (M := M) g₀ T))
          (koszulCovecCc (I := I) g₀ T))) from rfl]
      rw [appCcRS_toSection]
      exact riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ 0 6 4 x _ _
    refine le_trans hcw ?_
    have hz := hZcap bdSGKTau2
    have hznn : (0 : ℝ) ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 0 6 x
        ((rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 bdSGKTau2
        (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
          (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovGradRaw (I := I) (M := M) g₀ T))
          (koszulCovecCc (I := I) g₀ T))).toSection x) :=
      riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 6 x _
    refine le_trans (mul_le_mul_of_nonneg_right hDT4cap hznn) ?_
    exact mul_le_mul_of_nonneg_left hz (hC4_nn 0)
  have hW3 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 4 x
      ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau3 T T).toSection x) ≤ C4 0 * ZB := by
    have hcw : riemannianFiberNormSq (I := I) (M := M) g₀ 0 4 x
        ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau3 T T).toSection x) ≤
        riemannianFiberNormSq (I := I) (M := M) g₀ 6 4 x
            ((cometricDoubleTraceCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s) 4).toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 6 x
            ((rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 bdSGKTau3
        (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
          (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovGradRaw (I := I) (M := M) g₀ T))
          (koszulCovecCc (I := I) g₀ T))).toSection x) := by
      rw [show sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau3 T T =
          ccOperatorFieldComp (I := I) (M := M) g₀ 0 6 4
            (cometricDoubleTraceCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s) 4)
            (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 bdSGKTau3
        (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
          (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovGradRaw (I := I) (M := M) g₀ T))
          (koszulCovecCc (I := I) g₀ T))) from rfl]
      rw [appCcRS_toSection]
      exact riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ 0 6 4 x _ _
    refine le_trans hcw ?_
    have hz := hZcap bdSGKTau3
    have hznn : (0 : ℝ) ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 0 6 x
        ((rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 bdSGKTau3
        (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
          (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovGradRaw (I := I) (M := M) g₀ T))
          (koszulCovecCc (I := I) g₀ T))).toSection x) :=
      riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 6 x _
    refine le_trans (mul_le_mul_of_nonneg_right hDT4cap hznn) ?_
    exact mul_le_mul_of_nonneg_left hz (hC4_nn 0)
  have hW4 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 4 x
      ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau4 T T).toSection x) ≤ C4 0 * ZB := by
    have hcw : riemannianFiberNormSq (I := I) (M := M) g₀ 0 4 x
        ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau4 T T).toSection x) ≤
        riemannianFiberNormSq (I := I) (M := M) g₀ 6 4 x
            ((cometricDoubleTraceCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s) 4).toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 6 x
            ((rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 bdSGKTau4
        (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
          (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovGradRaw (I := I) (M := M) g₀ T))
          (koszulCovecCc (I := I) g₀ T))).toSection x) := by
      rw [show sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau4 T T =
          ccOperatorFieldComp (I := I) (M := M) g₀ 0 6 4
            (cometricDoubleTraceCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s) 4)
            (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 bdSGKTau4
        (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
          (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovGradRaw (I := I) (M := M) g₀ T))
          (koszulCovecCc (I := I) g₀ T))) from rfl]
      rw [appCcRS_toSection]
      exact riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ 0 6 4 x _ _
    refine le_trans hcw ?_
    have hz := hZcap bdSGKTau4
    have hznn : (0 : ℝ) ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 0 6 x
        ((rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 bdSGKTau4
        (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
          (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovGradRaw (I := I) (M := M) g₀ T))
          (koszulCovecCc (I := I) g₀ T))).toSection x) :=
      riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 6 x _
    refine le_trans (mul_le_mul_of_nonneg_right hDT4cap hznn) ?_
    exact mul_le_mul_of_nonneg_left hz (hC4_nn 0)
  have hXsplit : ((((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau1 T T +
      sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau2 T T) -
      (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau3 T T +
      sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau4 T T))).toSection x : TensorRSSpace 0 4 I x) =
      (((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau1 T T).toSection x +
        (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau2 T T).toSection x) -
        ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau3 T T).toSection x +
        (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau4 T T).toSection x)) := by
    rw [SmoothCcTensor.toSection_sub, SmoothCcTensor.toSection_add,
      SmoothCcTensor.toSection_add]
    rfl
  have hXval : riemannianFiberNormSq (I := I) (M := M) g₀ 0 4 x
      ((((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau1 T T +
      sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau2 T T) -
      (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau3 T T +
      sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau4 T T))).toSection x) ≤ 16 * (C4 0 * ZB) := by
    rw [hXsplit]
    have hadd12 := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 4 x
      ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau1 T T).toSection x)
      ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau2 T T).toSection x)
    have hadd34 := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 4 x
      ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau3 T T).toSection x)
      ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau4 T T).toSection x)
    have hsub := riemannianFiberNormSq_sub_le (I := I) (M := M) g₀ 0 4 x
      ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau1 T T).toSection x +
        (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau2 T T).toSection x)
      ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau3 T T).toSection x +
        (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau4 T T).toSection x)
    nlinarith [hW1, hW2, hW3, hW4, hadd12, hadd34, hsub,
      riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 4 x
        ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau1 T T).toSection x),
      riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 4 x
        ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau2 T T).toSection x),
      riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 4 x
        ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau3 T T).toSection x),
      riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 4 x
        ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau4 T T).toSection x),
      mul_nonneg (hC4_nn 0) hZB_nn]
  have hperm6 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 6 x
      ((rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2
          ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau1 T T +
      sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau2 T T) -
      (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau3 T T +
      sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau4 T T)))).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 6 x
        ((slotExtendIter (I := I) (M := M) g₀ 0 4 2
          ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau1 T T +
      sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau2 T T) -
      (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau3 T T +
      sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau4 T T))).toSection x) := by
    have h := riemannianFiberNormSq_iteratedCovGrad_rs_eq_of_section_domDomCongr (I := I) (M := M)
      g₀ 2 6 armPairTraceSlotPerm6
      (slotExtendIter (I := I) (M := M) g₀ 0 4 2
        ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau1 T T +
      sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau2 T T) -
      (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau3 T T +
      sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau4 T T)))
      (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2
          ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau1 T T +
      sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau2 T T) -
      (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau3 T T +
      sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau4 T T))))
      (fun y d => by
        rw [rsDomDomCongrSection_toSection, toModel_rsDomDomCongr_apply]) 0 x
    rwa [iteratedCovGrad_zero, iteratedCovGrad_zero] at h
  have hslot2 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 6 x
      ((slotExtendIter (I := I) (M := M) g₀ 0 4 2
        ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau1 T T +
      sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau2 T T) -
      (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau3 T T +
      sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau4 T T))).toSection x) ≤
      fr * (fr * riemannianFiberNormSq (I := I) (M := M) g₀ 0 4 x
        ((((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau1 T T +
      sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau2 T T) -
      (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau3 T T +
      sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau4 T T))).toSection x)) := by
    have h2 := rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 1 5
      (slotExtendIter (I := I) (M := M) g₀ 0 4 1
        ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau1 T T +
      sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau2 T T) -
      (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau3 T T +
      sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau4 T T))) 0 x
    rw [iteratedCovGrad_zero, iteratedCovGrad_zero] at h2
    have h1 := rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 0 4
      ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau1 T T +
      sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau2 T T) -
      (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau3 T T +
      sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau4 T T)) 0 x
    rw [iteratedCovGrad_zero, iteratedCovGrad_zero] at h1
    refine le_trans h2 ?_
    refine mul_le_mul_of_nonneg_left ?_ hfr_nn
    exact h1
  have hXi : riemannianFiberNormSq (I := I) (M := M) g₀ 2 6 x
      ((rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2
          ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau1 T T +
      sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau2 T T) -
      (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau3 T T +
      sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau4 T T)))).toSection x) ≤
      fr * (fr * (16 * (C4 0 * ZB))) := by
    rw [hperm6]
    refine le_trans hslot2 ?_
    refine mul_le_mul_of_nonneg_left ?_ hfr_nn
    exact mul_le_mul_of_nonneg_left hXval hfr_nn
  have hcompnn : (0 : ℝ) ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 2 6 x
      ((rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2
          ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau1 T T +
      sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau2 T T) -
      (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau3 T T +
      sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau4 T T)))).toSection x) :=
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 6 x _
  have hfnn : (0 : ℝ) ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
      ((ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
        (armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s))
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau1 T T +
      sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau2 T T) -
      (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau3 T T +
      sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau4 T T))))).toSection x) :=
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 2 x _
  have hXi_nn : (0 : ℝ) ≤ fr * (fr * (16 * (C4 0 * ZB))) := by
    refine mul_nonneg hfr_nn (mul_nonneg hfr_nn (mul_nonneg (by norm_num)
      (mul_nonneg (hC4_nn 0) hZB_nn)))
  calc ((2 : ℝ) * (s * s)) ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
        ((ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
        (armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s))
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau1 T T +
      sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau2 T T) -
      (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau3 T T +
      sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau4 T T))))).toSection x)
      ≤ 4 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
          ((ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
        (armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s))
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau1 T T +
      sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau2 T T) -
      (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau3 T T +
      sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau4 T T))))).toSection x) :=
        mul_le_mul_of_nonneg_right hsq1 hfnn
    _ ≤ 4 * (riemannianFiberNormSq (I := I) (M := M) g₀ 6 2 x
            ((armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s)).toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 6 x
            ((rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                ((sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau1 T T +
      sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau2 T T) -
      (sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau3 T T +
      sharpGradKoszulWeightedTerm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) bdSGKTau4 T T)))).toSection x)) := by
        refine mul_le_mul_of_nonneg_left hcomp (by norm_num)
    _ ≤ 4 * (CP 0 * (fr * (fr * (16 * (C4 0 * ZB))))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        exact mul_le_mul hPTO hXi hcompnn (hCP_nn 0)

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
omit [BoundarylessManifold I M] in
theorem exists_sobolevConst_riemannianFiberNormSq_T_le_sq (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) :
    ∃ Csob : ℝ, 0 ≤ Csob ∧
      ∀ (T : SmoothCcTensor g₀ 0 2) {R : ℝ} (_hR : 0 ≤ R),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (T.toSection x) ≤
            (Csob * R) ^ 2 := by
  classical
  obtain ⟨Csob, hCsob_nn, hCsob⟩ :=
    exists_Csob_convexPerturbation_pointwise_C2_le (I := I) (M := M) g₀ a ha_super
  refine ⟨Csob, hCsob_nn, ?_⟩
  intro T R hR hball x
  have hball0 : ∀ j : ℕ, j ≤ a + 2 →
      ‖iteratedCovGrad (I := I) g₀ 0 2 j (0 : SmoothCcTensor g₀ 0 2)‖ ≤ R := by
    intro j hj
    rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • T from (zero_smul ℝ T).symm,
      iteratedCovGrad_smul_real, norm_smul, Real.norm_eq_abs, abs_zero, zero_mul]
    exact hR
  have hsum := hCsob T 0 hR hball hball0 1 ⟨by norm_num, le_refl 1⟩ x
  have hterms : ∀ k ∈ Finset.range 3, 0 ≤
      (letI : Bundle.RiemannianBundle
          (fun b : M => Tensor0SBundle.TensorRSSpace 0 (2 + k) I b) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + k)
      ‖(iteratedCovGrad (I := I) g₀ 0 2 k
          (convexPerturbation (I := I) g₀ T 0 1)).toSection x‖) := by
    intro k _
    letI : Bundle.RiemannianBundle
        (fun b : M => Tensor0SBundle.TensorRSSpace 0 (2 + k) I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + k)
    exact norm_nonneg _
  have h0 := le_trans (Finset.single_le_sum hterms
    (show (0 : ℕ) ∈ Finset.range 3 from Finset.mem_range.mpr (by norm_num))) hsum
  have hcp1 : convexPerturbation (I := I) g₀ T 0 1 = T := by
    rw [convexPerturbation, smul_zero, zero_add, one_smul]
  rw [hcp1, iteratedCovGrad_zero] at h0
  letI : Bundle.RiemannianBundle (fun b : M => Tensor0SBundle.TensorRSSpace 0 2 I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 2
  have h0' : ‖(T.toSection x : Tensor0SBundle.TensorRSSpace 0 2 I x)‖ ≤ Csob * R := h0
  have hb : riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (T.toSection x) =
      ‖(T.toSection x : Tensor0SBundle.TensorRSSpace 0 2 I x)‖ ^ 2 :=
    riemannianFiberNormSq_eq_bundle_norm_sq' (I := I) (M := M) g₀ 0 2 x (T.toSection x)
  have hnn : (0 : ℝ) ≤ ‖(T.toSection x : Tensor0SBundle.TensorRSSpace 0 2 I x)‖ :=
    norm_nonneg _
  nlinarith [h0', hb, hnn, mul_nonneg hCsob_nn hR]


theorem exists_ricciArmRicciFoldRemainderField_realizedFam_riemannianFiberNormSq_uniformBound
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ (T : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
              ((ricciArmRicciFoldRemainderField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T 0 hδ hδZ s) (s • T)).toSection x) ≤ Λ := by
  classical
  set δ₁ : ℝ := max δ₀ 0 with hδ₁_def
  have hδ₁_lt : δ₁ < 1 := max_lt hδ₀ one_pos
  obtain ⟨CP, hCP_nn, hCP⟩ := bdPairTraceOp_tgrid (I := I) (M := M) g₀ hδ₁_lt
  obtain ⟨Csob, hCsob_nn, hTcapAll⟩ :=
    exists_sobolevConst_riemannianFiberNormSq_T_le_sq (I := I) (M := M) g₀ a ha_super
  obtain ⟨KD4, hKD4_nn, hKD4⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 6 4
      (cometricDoubleTraceField (I := I) g₀ 4)
  obtain ⟨KsR, hKsR_nn, hKsR⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 2 6
      (slotExtendIter (I := I) (M := M) g₀ 0 4 2
        (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀))
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : 0 ≤ fr := Nat.cast_nonneg _
  refine ⟨CP 0 * (fr * (fr * (4 * (KD4 * (KsR * (Csob * R) ^ 2))))),
    mul_nonneg (hCP_nn 0) (mul_nonneg hfr_nn (mul_nonneg hfr_nn (mul_nonneg (by norm_num)
      (mul_nonneg hKD4_nn (mul_nonneg hKsR_nn (sq_nonneg _)))))), ?_⟩
  intro T δ hδ_le hδ hδZ hball s hs x
  by_cases hM : Nonempty M
  swap
  · exact ((not_nonempty_iff.mp hM).false x).elim
  obtain ⟨x₀⟩ := hM
  have hδ0 : 0 ≤ δ := bdDelta_nonneg (I := I) (M := M) g₀ x₀ T hδ
  have hδ_le' : δ ≤ δ₁ := le_trans hδ_le (le_max_left _ _)
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hs_mem : s ∈ realizedSmallSet (δ := δ) (δ' := δ) :=
    Icc_subset_realizedSmallSet hδ_lt hδ_lt hs
  obtain ⟨hs0, hs1⟩ := hs
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      (realizedFam (I := I) g₀ T 0 hδ hδZ s).inner y v w =
        g₀.inner y v w +
          ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T 0 s) y v w :=
    fun y v w => realizedFam_inner_of_mem (I := I) g₀ T 0 hδ hδZ hs_mem y v w
  have hδP : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T 0 s)) δ := by
    intro y v w
    have hraw := convexPerturbation_gFibreOpBound_abs (I := I) g₀ T 0 hδ hδZ s y v w
    have heq : |1 - s| * δ + |s| * δ = δ := by
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - s), abs_of_nonneg hs0]
      ring
    rwa [heq] at hraw
  have hfield : ricciArmRicciFoldRemainderField (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) (s • T) =
      ((-(1 / 2) : ℝ) * s) •
        ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
          (armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s))
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (palatiniRicciFoldWeightA (I := I) (M := M) g₀ T +
                palatiniRicciFoldWeightB (I := I) (M := M) g₀ T))) := by
    rw [bdRicciFold_eq_refold (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s) (s • T)]
    rw [bdRicciFoldXi_smul (I := I) (M := M) g₀ T s]
    rw [appCcRS_smul_right (I := I) (M := M) g₀ 2 6 2 s
      (armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s))
      (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2
          (palatiniRicciFoldWeightA (I := I) (M := M) g₀ T +
            palatiniRicciFoldWeightB (I := I) (M := M) g₀ T)))]
    rw [smul_smul]
  rw [hfield]
  rw [show (((((-(1 / 2) : ℝ) * s) •
      ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
        (armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s))
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (palatiniRicciFoldWeightA (I := I) (M := M) g₀ T +
              palatiniRicciFoldWeightB (I := I) (M := M) g₀ T)))).toSection x)) =
      ((-(1 / 2) : ℝ) * s) •
        ((ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
          (armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s))
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (palatiniRicciFoldWeightA (I := I) (M := M) g₀ T +
                palatiniRicciFoldWeightB (I := I) (M := M) g₀ T)))).toSection x) from by
    rw [SmoothCcTensor.toSection_smul]; rfl]
  rw [riemannianFiberNormSq_smul (I := I) (M := M) g₀ 2 2 x]
  have hsq1 : ((-(1 / 2) : ℝ) * s) ^ 2 ≤ 1 := by nlinarith
  have hcomp : riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
      ((ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
        (armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s))
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (palatiniRicciFoldWeightA (I := I) (M := M) g₀ T +
              palatiniRicciFoldWeightB (I := I) (M := M) g₀ T)))).toSection x) ≤
      riemannianFiberNormSq (I := I) (M := M) g₀ 6 2 x
          ((armPairTraceOpCc (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T 0 hδ hδZ s)).toSection x) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 6 x
          ((rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (palatiniRicciFoldWeightA (I := I) (M := M) g₀ T +
                palatiniRicciFoldWeightB (I := I) (M := M) g₀ T))).toSection x) := by
    rw [appCcRS_toSection]
    exact riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ 2 6 2 x
      ((armPairTraceOpCc (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T 0 hδ hδZ s)).toSection x)
      ((rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2
          (palatiniRicciFoldWeightA (I := I) (M := M) g₀ T +
            palatiniRicciFoldWeightB (I := I) (M := M) g₀ T))).toSection x)
  have hPTO : riemannianFiberNormSq (I := I) (M := M) g₀ 6 2 x
      ((armPairTraceOpCc (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T 0 hδ hδZ s)).toSection x) ≤ CP 0 := by
    have h := hCP (realizedFam (I := I) g₀ T 0 hδ hδZ s)
      (convexPerturbation (I := I) g₀ T 0 s) htie hδ_le' hδ0 hδP 0 x
    rw [iteratedCovGrad_zero] at h
    refine le_trans h (le_of_eq ?_)
    rw [Combinatorics.antidiagonalTupleGridWindow, Finset.sum_range_one,
      Combinatorics.antidiagonalTupleGrid_zero, mul_one]
  have hTcap : riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
      (T.toSection x) ≤ (Csob * R) ^ 2 := hTcapAll T hR hball x
  have hXi : riemannianFiberNormSq (I := I) (M := M) g₀ 2 6 x
      ((rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2
          (palatiniRicciFoldWeightA (I := I) (M := M) g₀ T +
            palatiniRicciFoldWeightB (I := I) (M := M) g₀ T))).toSection x) ≤
      fr * (fr * (4 * (KD4 * (KsR * (Csob * R) ^ 2)))) := by
    have hWgen : ∀ σw : Equiv.Perm (Fin 6),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 4 x
          ((ccOperatorFieldComp (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
            (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 σw
              (ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 6
                (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                  (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)) T))).toSection x) ≤
        KD4 * (KsR * (Csob * R) ^ 2) := by
      intro σw
      have hc1 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 4 x
          ((ccOperatorFieldComp (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
            (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 σw
              (ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 6
                (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                  (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)) T))).toSection x) ≤
          riemannianFiberNormSq (I := I) (M := M) g₀ 6 4 x
              ((cometricDoubleTraceField (I := I) g₀ 4).toSection x) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 6 x
              ((rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 σw
                (ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 6
                  (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                    (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)) T)).toSection x) := by
        rw [appCcRS_toSection]
        exact riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ 0 6 4 x _ _
      have hperm : riemannianFiberNormSq (I := I) (M := M) g₀ 0 6 x
          ((rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 σw
            (ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 6
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)) T)).toSection x) =
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 6 x
            ((ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 6
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)) T).toSection x) := by
        have h := riemannianFiberNormSq_iteratedCovGrad_rs_eq_of_section_domDomCongr (I := I) (M := M)
          g₀ 0 6 σw
          (ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 6
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)) T)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 σw
            (ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 6
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)) T))
          (fun y d => by
            rw [rsDomDomCongrSection_toSection, toModel_rsDomDomCongr_apply]) 0 x
        rwa [iteratedCovGrad_zero, iteratedCovGrad_zero] at h
      have hc2 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 6 x
          ((ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 6
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)) T).toSection x) ≤
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 6 x
              ((slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)).toSection x) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (T.toSection x) := by
        rw [appCcRS_toSection]
        exact riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ 0 2 6 x _ _
      have hKsRx := hKsR x
      have hKD4x := hKD4 x
      have hrfns2 : (0 : ℝ) ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 0 6 x
          ((rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 σw
            (ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 6
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)) T)).toSection x) :=
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 6 x _
      have hTnn : (0 : ℝ) ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
          (T.toSection x) :=
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 2 x _
      have hsE : (0 : ℝ) ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 2 6 x
          ((slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)).toSection x) :=
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 6 x _
      have hD4nn : (0 : ℝ) ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 6 4 x
          ((cometricDoubleTraceField (I := I) g₀ 4).toSection x) :=
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 6 4 x _
      calc riemannianFiberNormSq (I := I) (M := M) g₀ 0 4 x
            ((ccOperatorFieldComp (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
              (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 σw
                (ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 6
                  (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                    (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)) T))).toSection x)
          ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 6 4 x
                ((cometricDoubleTraceField (I := I) g₀ 4).toSection x) *
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 6 x
                ((rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 σw
                  (ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 6
                    (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                      (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)) T)).toSection x) := hc1
        _ ≤ KD4 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 6 x
              ((rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 σw
                (ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 6
                  (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                    (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)) T)).toSection x) :=
            mul_le_mul_of_nonneg_right hKD4x hrfns2
        _ = KD4 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 6 x
              ((ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 6
                (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                  (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)) T).toSection x) := by
            rw [hperm]
        _ ≤ KD4 * (riemannianFiberNormSq (I := I) (M := M) g₀ 2 6 x
              ((slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)).toSection x) *
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (T.toSection x)) :=
            mul_le_mul_of_nonneg_left hc2 hKD4_nn
        _ ≤ KD4 * (KsR * (Csob * R) ^ 2) := by
            refine mul_le_mul_of_nonneg_left ?_ hKD4_nn
            exact mul_le_mul hKsRx hTcap hTnn hKsR_nn
    have hperm6 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 6 x
        ((rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (palatiniRicciFoldWeightA (I := I) (M := M) g₀ T +
              palatiniRicciFoldWeightB (I := I) (M := M) g₀ T))).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 6 x
          ((slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (palatiniRicciFoldWeightA (I := I) (M := M) g₀ T +
              palatiniRicciFoldWeightB (I := I) (M := M) g₀ T)).toSection x) := by
      have h := riemannianFiberNormSq_iteratedCovGrad_rs_eq_of_section_domDomCongr (I := I) (M := M)
        g₀ 2 6 armPairTraceSlotPerm6
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2
          (palatiniRicciFoldWeightA (I := I) (M := M) g₀ T +
            palatiniRicciFoldWeightB (I := I) (M := M) g₀ T))
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (palatiniRicciFoldWeightA (I := I) (M := M) g₀ T +
              palatiniRicciFoldWeightB (I := I) (M := M) g₀ T)))
        (fun y d => by
          rw [rsDomDomCongrSection_toSection, toModel_rsDomDomCongr_apply]) 0 x
      rwa [iteratedCovGrad_zero, iteratedCovGrad_zero] at h
    have hslot2 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 6 x
        ((slotExtendIter (I := I) (M := M) g₀ 0 4 2
          (palatiniRicciFoldWeightA (I := I) (M := M) g₀ T +
            palatiniRicciFoldWeightB (I := I) (M := M) g₀ T)).toSection x) ≤
        fr * riemannianFiberNormSq (I := I) (M := M) g₀ 1 5 x
          ((slotExtendIter (I := I) (M := M) g₀ 0 4 1
            (palatiniRicciFoldWeightA (I := I) (M := M) g₀ T +
              palatiniRicciFoldWeightB (I := I) (M := M) g₀ T)).toSection x) := by
      have h := rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 1 5
        (slotExtendIter (I := I) (M := M) g₀ 0 4 1
          (palatiniRicciFoldWeightA (I := I) (M := M) g₀ T +
            palatiniRicciFoldWeightB (I := I) (M := M) g₀ T)) 0 x
      rwa [iteratedCovGrad_zero, iteratedCovGrad_zero] at h
    have hslot1 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 5 x
        ((slotExtendIter (I := I) (M := M) g₀ 0 4 1
          (palatiniRicciFoldWeightA (I := I) (M := M) g₀ T +
            palatiniRicciFoldWeightB (I := I) (M := M) g₀ T)).toSection x) ≤
        fr * riemannianFiberNormSq (I := I) (M := M) g₀ 0 4 x
          ((palatiniRicciFoldWeightA (I := I) (M := M) g₀ T +
            palatiniRicciFoldWeightB (I := I) (M := M) g₀ T).toSection x) := by
      have h := rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 0 4
        (palatiniRicciFoldWeightA (I := I) (M := M) g₀ T +
          palatiniRicciFoldWeightB (I := I) (M := M) g₀ T) 0 x
      rwa [iteratedCovGrad_zero, iteratedCovGrad_zero] at h
    have hW4 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 4 x
        ((palatiniRicciFoldWeightA (I := I) (M := M) g₀ T +
          palatiniRicciFoldWeightB (I := I) (M := M) g₀ T).toSection x) ≤
        4 * (KD4 * (KsR * (Csob * R) ^ 2)) := by
      have hsplit : ((palatiniRicciFoldWeightA (I := I) (M := M) g₀ T +
          palatiniRicciFoldWeightB (I := I) (M := M) g₀ T).toSection x) =
          (palatiniRicciFoldWeightA (I := I) (M := M) g₀ T).toSection x +
            (palatiniRicciFoldWeightB (I := I) (M := M) g₀ T).toSection x := by
        rw [SmoothCcTensor.toSection_add]
        rfl
      rw [hsplit]
      have hadd := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 4 x
        ((palatiniRicciFoldWeightA (I := I) (M := M) g₀ T).toSection x)
        ((palatiniRicciFoldWeightB (I := I) (M := M) g₀ T).toSection x)
      have hWA := hWgen (Equiv.swap (1 : Fin 6) 3)
      have hWB := hWgen palatiniRicciFoldWeightBPerm
      have hWA' : riemannianFiberNormSq (I := I) (M := M) g₀ 0 4 x
          ((palatiniRicciFoldWeightA (I := I) (M := M) g₀ T).toSection x) ≤
          KD4 * (KsR * (Csob * R) ^ 2) := hWA
      have hWB' : riemannianFiberNormSq (I := I) (M := M) g₀ 0 4 x
          ((palatiniRicciFoldWeightB (I := I) (M := M) g₀ T).toSection x) ≤
          KD4 * (KsR * (Csob * R) ^ 2) := hWB
      linarith
    calc riemannianFiberNormSq (I := I) (M := M) g₀ 2 6 x
          ((rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (palatiniRicciFoldWeightA (I := I) (M := M) g₀ T +
                palatiniRicciFoldWeightB (I := I) (M := M) g₀ T))).toSection x)
        = riemannianFiberNormSq (I := I) (M := M) g₀ 2 6 x
            ((slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (palatiniRicciFoldWeightA (I := I) (M := M) g₀ T +
                palatiniRicciFoldWeightB (I := I) (M := M) g₀ T)).toSection x) := hperm6
      _ ≤ fr * riemannianFiberNormSq (I := I) (M := M) g₀ 1 5 x
            ((slotExtendIter (I := I) (M := M) g₀ 0 4 1
              (palatiniRicciFoldWeightA (I := I) (M := M) g₀ T +
                palatiniRicciFoldWeightB (I := I) (M := M) g₀ T)).toSection x) := hslot2
      _ ≤ fr * (fr * riemannianFiberNormSq (I := I) (M := M) g₀ 0 4 x
            ((palatiniRicciFoldWeightA (I := I) (M := M) g₀ T +
              palatiniRicciFoldWeightB (I := I) (M := M) g₀ T).toSection x)) :=
          mul_le_mul_of_nonneg_left hslot1 hfr_nn
      _ ≤ fr * (fr * (4 * (KD4 * (KsR * (Csob * R) ^ 2)))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hW4 hfr_nn) hfr_nn
  have hPTOnn : (0 : ℝ) ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 6 2 x
      ((armPairTraceOpCc (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T 0 hδ hδZ s)).toSection x) :=
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 6 2 x _
  have hXinn : (0 : ℝ) ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 2 6 x
      ((rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2
          (palatiniRicciFoldWeightA (I := I) (M := M) g₀ T +
            palatiniRicciFoldWeightB (I := I) (M := M) g₀ T))).toSection x) :=
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 6 x _
  have hcompnn : (0 : ℝ) ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
      ((ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
        (armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s))
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (palatiniRicciFoldWeightA (I := I) (M := M) g₀ T +
              palatiniRicciFoldWeightB (I := I) (M := M) g₀ T)))).toSection x) :=
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 2 x _
  calc (((-(1 / 2) : ℝ) * s) ^ 2) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
          ((ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
            (armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s))
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (palatiniRicciFoldWeightA (I := I) (M := M) g₀ T +
                  palatiniRicciFoldWeightB (I := I) (M := M) g₀ T)))).toSection x)
      ≤ 1 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
          ((ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
            (armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s))
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (palatiniRicciFoldWeightA (I := I) (M := M) g₀ T +
                  palatiniRicciFoldWeightB (I := I) (M := M) g₀ T)))).toSection x) :=
        mul_le_mul_of_nonneg_right hsq1 hcompnn
    _ = riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
          ((ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
            (armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s))
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (palatiniRicciFoldWeightA (I := I) (M := M) g₀ T +
                  palatiniRicciFoldWeightB (I := I) (M := M) g₀ T)))).toSection x) := one_mul _
    _ ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 6 2 x
          ((armPairTraceOpCc (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T 0 hδ hδZ s)).toSection x) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 6 x
          ((rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (palatiniRicciFoldWeightA (I := I) (M := M) g₀ T +
                palatiniRicciFoldWeightB (I := I) (M := M) g₀ T))).toSection x) := hcomp
    _ ≤ CP 0 * (fr * (fr * (4 * (KD4 * (KsR * (Csob * R) ^ 2))))) :=
        mul_le_mul hPTO hXi hXinn (hCP_nn 0)

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
