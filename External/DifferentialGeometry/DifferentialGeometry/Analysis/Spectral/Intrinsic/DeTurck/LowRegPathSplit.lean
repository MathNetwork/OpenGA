import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.PhiMetSymmetry
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.RHSPathIntegral
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.H2H3Principal
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ParametricJetIntegral
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.PrincipalCoeffH2
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitzPhiMetTotalCurvatureFold








noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Set Filter Topology Tensor0SBundle ContinuousLinearMap
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance instCompleteSpaceE : CompleteSpace E :=
  FiniteDimensional.complete ℝ E

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
private theorem phi_dev_joint
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound g₀
      (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound g₀
      (ccTensorBilinSymm (I := I) g₀ T') δ') :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 4
      (fun s => deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
          (realizedFam (I := I) g₀ T T' hδ hδ' s) -
        deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)
      (δ := δ) (δ' := δ') := by
  have hpath := rhsTop_path_joint (I := I) (M := M) g₀ g_bg T T' hδ hδ'
  have hconst : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel 4 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel 4 2 ℝ E)
        (E := fun z : M => TensorRSSpace 4 2 I z) p.1
        ((deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀).toSection p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀).toSection.contMDiff.comp_contMDiffOn
      contMDiffOn_fst
  have hsub := joint_rs_sub (I := I) (r := 4) (s := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun p : M × ℝ => (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2)).toSection p.1)
    (fun p : M × ℝ => (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀).toSection p.1)
    hpath hconst
  refine hsub.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (TensorRSModel 4 2 ℝ E)
    (E := fun z : M => TensorRSSpace 4 2 I z) p.1 t) ?_
  rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] in
private theorem norm_sq_add_le
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (A B : SmoothCcTensor g₀ r s) :
    ‖A + B‖ ^ 2 ≤ 2 * ‖A‖ ^ 2 + 2 * ‖B‖ ^ 2 := by
  have h := norm_add_le A B
  have hA : 0 ≤ ‖A‖ := norm_nonneg _
  have hB : 0 ≤ ‖B‖ := norm_nonneg _
  have hAB : 0 ≤ ‖A + B‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖A‖ - ‖B‖)]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] in
private theorem norm_sq_sub_le
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (A B : SmoothCcTensor g₀ r s) :
    ‖A - B‖ ^ 2 ≤ 2 * ‖A‖ ^ 2 + 2 * ‖B‖ ^ 2 := by
  have h := norm_sub_le A B
  have hA : 0 ≤ ‖A‖ := norm_nonneg _
  have hB : 0 ≤ ‖B‖ := norm_nonneg _
  have hAB : 0 ≤ ‖A - B‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖A‖ - ‖B‖)]

omit [NeZero (Module.finrank ℝ E)] in
private theorem reindex_norm_sq
    (g₀ : SmoothRiemannianMetric I M) (r s i : ℕ)
    (A : SmoothCcTensor g₀ r s) (ρ : Equiv.Perm (Fin r)) :
    ‖iteratedCovGrad (I := I) g₀ r s i
        (reindexCoeffGen (I := I) (M := M) g₀ r s A ρ)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g₀ r s i A‖ ^ 2 := by
  rw [iteratedCovGrad_reindexCoeffGen (I := I) (M := M) g₀ r s A ρ i,
    norm_reindexCoeffGen_eq (I := I) (M := M) g₀ r (s + i)]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem reindex_sub
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (A B : SmoothCcTensor g₀ r s) (ρ : Equiv.Perm (Fin r)) :
    reindexCoeffGen (I := I) (M := M) g₀ r s (A - B) ρ =
      reindexCoeffGen (I := I) (M := M) g₀ r s A ρ -
        reindexCoeffGen (I := I) (M := M) g₀ r s B ρ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((reindexCoeffGen (I := I) (M := M) g₀ r s A ρ -
        reindexCoeffGen (I := I) (M := M) g₀ r s B ρ).toSection x) =
      (reindexCoeffGen (I := I) (M := M) g₀ r s A ρ).toSection x -
        (reindexCoeffGen (I := I) (M := M) g₀ r s B ρ).toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  rw [reindexCoeffGen_toSection, reindexCoeffGen_toSection, reindexCoeffGen_toSection]
  rw [show (A - B).toSection x = A.toSection x - B.toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  rw [reindexCoeffFibGen, reindexCoeffFibGen, reindexCoeffFibGen]
  exact ContinuousLinearMap.sub_comp _ _ _

private theorem convex_hs_bound
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {s R : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hT : ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T‖ ≤ R)
    (hT' : ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T'‖ ≤ R) :
    ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ)
        (convexPerturbation (I := I) g₀ T T' s)‖ ≤ R := by
  have h1ms : (0 : ℝ) ≤ 1 - s := by linarith
  rw [show convexPerturbation (I := I) g₀ T T' s =
      (1 - s) • T' + s • T from rfl,
    ccTensorToHs_add, ccTensorToHs_smul, ccTensorToHs_smul]
  calc
    ‖(1 - s) • ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T' +
        s • ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T‖
        ≤ ‖(1 - s) • ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T'‖ +
          ‖s • ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T‖ := norm_add_le _ _
    _ = (1 - s) * ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T'‖ +
          s * ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg h1ms, abs_of_nonneg hs0]
    _ ≤ (1 - s) * R + s * R :=
      add_le_add (mul_le_mul_of_nonneg_left hT' h1ms)
        (mul_le_mul_of_nonneg_left hT hs0)
    _ = R := by ring

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in



theorem phi_dev_h2
    (hDim : Module.finrank ℝ E = 3)
    (g₀ g_bg : SmoothRiemannianMetric I M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_lt : δ < 1)
        (hδ : metricCauchySchwarzBound g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (_hδ'_lt : δ' < 1)
        (hδ' : metricCauchySchwarzBound g₀
          (ccTensorBilinSymm (I := I) g₀ T') δ')
        {R : ℝ}, 0 ≤ R → R ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T‖ ≤ R →
        ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T'‖ ≤ R →
        ∀ {s : ℝ}, 0 ≤ s → s ≤ 1 →
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
                ((deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
                    (realizedFam (I := I) g₀ T T' hδ hδ' s) -
                  deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀).toSection x) ≤
              (C * R) ^ 2) ∧
            (∑ i ∈ Finset.range 3,
              ‖iteratedCovGrad (I := I) g₀ 4 2 i
                (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
                    (realizedFam (I := I) g₀ T T' hδ hδ' s) -
                  deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)‖ ^ 2) ≤
              (C * R) ^ 2 := by
  classical
  obtain ⟨ρ, Cinv, hρ, hCinv, hinv⟩ := inv_coeff_h2 (I := I) (M := M) hDim g₀
  obtain ⟨CTH, hCTH_nn, hCTH⟩ :=
    traceHessianCoeff_sub_background_perOrder_riemannianFiberNormSq_le_gInvDiffSlotCoeff_riemannianFiberNormSq
      (I := I) (M := M) g₀
  obtain ⟨CR, hCR_nn, hCR⟩ :=
    ricciArmPrincipalCoeff_sub_background_perOrder_riemannianFiberNormSq_le_gInvDiffSlotCoeff_riemannianFiberNormSq
      (I := I) (M := M) g₀
  obtain ⟨DTH, hDTH_nn, hDTH⟩ :=
    traceHessianCoeff_sub_background_jetL2_le_gInvDiffSlotCoeff_jetL2
      (I := I) (M := M) g₀
  obtain ⟨DR, hDR_nn, hDR⟩ :=
    ricciArmPrincipalCoeff_sub_background_jetL2_le_gInvDiffSlotCoeff_jetL2
      (I := I) (M := M) g₀
  let Kpt : ℝ := 8 * CTH 0 + 8 * CR 0
  let Kjet : ℝ := 8 * (∑ i ∈ Finset.range 3, DTH i) +
    8 * (∑ i ∈ Finset.range 3, DR i)
  let K : ℝ := Kpt + Kjet
  let C : ℝ := Real.sqrt K * Cinv
  have hKpt : 0 ≤ Kpt := by
    dsimp [Kpt]
    exact add_nonneg (mul_nonneg (by norm_num) (hCTH_nn 0))
      (mul_nonneg (by norm_num) (hCR_nn 0))
  have hKjet : 0 ≤ Kjet := by
    dsimp [Kjet]
    exact add_nonneg
      (mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => hDTH_nn i))
      (mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => hDR_nn i))
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro T T' δ hδ_lt hδ δ' hδ'_lt hδ' R hR hRρ hT hT' s hs0 hs1
  let P : SmoothCcTensor g₀ 0 2 := convexPerturbation (I := I) g₀ T T' s
  let g₁ : SmoothRiemannianMetric I M := realizedFam (I := I) g₀ T T' hδ hδ' s
  have hP : ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) P‖ ≤ R := by
    simpa [P] using convex_hs_bound (I := I) (M := M) g₀ T T' hs0 hs1 hT hT'
  have hs_mem : s ∈ realizedSmallSet (δ := δ) (δ' := δ') :=
    Icc_subset_realizedSmallSet hδ_lt hδ'_lt ⟨hs0, hs1⟩
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w +
        ccTensorBilinSymm (I := I) g₀ P y v w := by
    intro y v w
    simpa [g₁, P] using realizedFam_inner_of_mem
      (I := I) g₀ T T' hδ hδ' hs_mem y v w
  obtain ⟨hinv_pt, hinv_jet⟩ := hinv P g₁ (hP.trans hRρ) htie
  have hinv_scale :
      (Cinv * ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) P‖) ^ 2 ≤
        (Cinv * R) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hCinv (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hP hCinv) 2
  have hinv_jet_R : (∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)‖ ^ 2) ≤
        (Cinv * R) ^ 2 := hinv_jet.trans hinv_scale
  let DTHs : SmoothCcTensor g₀ 4 2 :=
    traceHessianCoeff (I := I) (M := M) g₀ g₁ -
      traceHessianCoeff (I := I) (M := M) g₀ g₀
  let DRs : SmoothCcTensor g₀ 4 2 :=
    ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁ -
      ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀
  let Dev : SmoothCcTensor g₀ 4 2 :=
    deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₁ -
      deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀
  let ρA : Equiv.Perm (Fin 4) :=
    traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermA
  let ρAT : Equiv.Perm (Fin 4) :=
    traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermAT
  have hdev_eq : Dev =
      reindexCoeffGen (I := I) (M := M) g₀ 4 2 DTHs ρA +
        reindexCoeffGen (I := I) (M := M) g₀ 4 2 DTHs ρAT -
          (DRs + DRs) := by
    dsimp [Dev, DTHs, DRs]
    rw [deTurckPhiMetTotal_eq_reindex_decomp_fw (I := I) (M := M) g₀ g_bg g₁,
      deTurckPhiMetTotal_eq_reindex_decomp_fw (I := I) (M := M) g₀ g_bg g₀,
      reindex_sub g₀ _ _ _ _ ρA,
      reindex_sub g₀ _ _ _ _ ρAT]
    abel
  have htarget : (C * R) ^ 2 = K * (Cinv * R) ^ 2 := by
    dsimp [C]
    rw [show (Real.sqrt K * Cinv * R) ^ 2 =
        (Real.sqrt K) ^ 2 * (Cinv * R) ^ 2 by ring,
      Real.sq_sqrt hK]
  refine ⟨?_, ?_⟩
  · intro x
    let Ks : ℝ := riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
      ((gInvDiffSlotCoeff (I := I) g₀ g₁).toSection x)
    have hKs : Ks ≤ (Cinv * R) ^ 2 := (hinv_pt x).trans hinv_scale
    have hKs_nn : 0 ≤ Ks := by
      dsimp [Ks]
      exact riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 2 x _
    have hTH0 : riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
        (DTHs.toSection x) ≤ CTH 0 * Ks := by
      simpa [DTHs, Ks] using hCTH g₁ 0 x
    have hR0 : riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
        (DRs.toSection x) ≤ CR 0 * Ks := by
      simpa [DRs, Ks] using hCR g₁ 0 x
    have hAr : riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
        ((reindexCoeffGen (I := I) (M := M) g₀ 4 2 DTHs ρA).toSection x) =
          riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (DTHs.toSection x) := by
      rw [reindexCoeffGen_toSection]
      exact riemannianFiberNormSq_reindexCoeffFibGen
        (I := I) (M := M) g₀ 4 2 x ρA
          (show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from DTHs.toSection x)
    have hATr : riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
        ((reindexCoeffGen (I := I) (M := M) g₀ 4 2 DTHs ρAT).toSection x) =
          riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (DTHs.toSection x) := by
      rw [reindexCoeffGen_toSection]
      exact riemannianFiberNormSq_reindexCoeffFibGen
        (I := I) (M := M) g₀ 4 2 x ρAT
          (show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from DTHs.toSection x)
    have h0 : riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
        (Dev.toSection x) ≤
          4 * riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
            ((reindexCoeffGen (I := I) (M := M) g₀ 4 2 DTHs ρA).toSection x) +
          4 * riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
            ((reindexCoeffGen (I := I) (M := M) g₀ 4 2 DTHs ρAT).toSection x) +
          8 * riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
            (DRs.toSection x) := by
      rw [hdev_eq]
      simp only [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
        SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]
      have hsub := riemannianFiberNormSq_sub_le (I := I) (M := M) g₀ 4 2 x
        ((reindexCoeffGen (I := I) (M := M) g₀ 4 2 DTHs ρA).toSection x +
          (reindexCoeffGen (I := I) (M := M) g₀ 4 2 DTHs ρAT).toSection x)
        (DRs.toSection x + DRs.toSection x)
      have hadd1 := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 4 2 x
        ((reindexCoeffGen (I := I) (M := M) g₀ 4 2 DTHs ρA).toSection x)
        ((reindexCoeffGen (I := I) (M := M) g₀ 4 2 DTHs ρAT).toSection x)
      have hadd2 := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 4 2 x
        (DRs.toSection x) (DRs.toSection x)
      linarith
    rw [hAr, hATr] at h0
    have hraw : riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
        (Dev.toSection x) ≤ Kpt * (Cinv * R) ^ 2 := by
      dsimp [Kpt]
      nlinarith [mul_le_mul_of_nonneg_left hKs hKpt, hCTH_nn 0, hCR_nn 0]
    rw [htarget]
    exact hraw.trans (mul_le_mul_of_nonneg_right
      (by dsimp [K]; linarith [hKjet]) (sq_nonneg _))
  · have hDTHsum : (∑ i ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g₀ 4 2 i DTHs‖ ^ 2) ≤
        (∑ i ∈ Finset.range 3, DTH i) * (Cinv * R) ^ 2 := by
      calc
        (∑ i ∈ Finset.range 3, ‖iteratedCovGrad (I := I) g₀ 4 2 i DTHs‖ ^ 2)
            ≤ ∑ i ∈ Finset.range 3, DTH i * (Cinv * R) ^ 2 := by
              apply Finset.sum_le_sum
              intro i hi
              have hi3 : i < 3 := Finset.mem_range.mp hi
              have hwindow : (∑ j ∈ Finset.range (i + 1),
                  ‖iteratedCovGrad (I := I) g₀ 2 2 j
                    (gInvDiffSlotCoeff (I := I) g₀ g₁)‖ ^ 2) ≤
                  ∑ j ∈ Finset.range 3,
                    ‖iteratedCovGrad (I := I) g₀ 2 2 j
                      (gInvDiffSlotCoeff (I := I) g₀ g₁)‖ ^ 2 :=
                Finset.sum_le_sum_of_subset_of_nonneg
                  (Finset.range_mono (by omega)) (fun j _ _ => sq_nonneg _)
              have hcoeff :
                  ‖iteratedCovGrad (I := I) g₀ 4 2 i DTHs‖ ^ 2 ≤
                    DTH i * ∑ j ∈ Finset.range (i + 1),
                      ‖iteratedCovGrad (I := I) g₀ 2 2 j
                        (gInvDiffSlotCoeff (I := I) g₀ g₁)‖ ^ 2 := by
                simpa [DTHs] using hDTH g₁ i
              exact hcoeff.trans
                (mul_le_mul_of_nonneg_left (hwindow.trans hinv_jet_R) (hDTH_nn i))
        _ = (∑ i ∈ Finset.range 3, DTH i) * (Cinv * R) ^ 2 := by
              rw [Finset.sum_mul]
    have hDRsum : (∑ i ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g₀ 4 2 i DRs‖ ^ 2) ≤
        (∑ i ∈ Finset.range 3, DR i) * (Cinv * R) ^ 2 := by
      calc
        (∑ i ∈ Finset.range 3, ‖iteratedCovGrad (I := I) g₀ 4 2 i DRs‖ ^ 2)
            ≤ ∑ i ∈ Finset.range 3, DR i * (Cinv * R) ^ 2 := by
              apply Finset.sum_le_sum
              intro i hi
              have hi3 : i < 3 := Finset.mem_range.mp hi
              have hwindow : (∑ j ∈ Finset.range (i + 1),
                  ‖iteratedCovGrad (I := I) g₀ 2 2 j
                    (gInvDiffSlotCoeff (I := I) g₀ g₁)‖ ^ 2) ≤
                  ∑ j ∈ Finset.range 3,
                    ‖iteratedCovGrad (I := I) g₀ 2 2 j
                      (gInvDiffSlotCoeff (I := I) g₀ g₁)‖ ^ 2 :=
                Finset.sum_le_sum_of_subset_of_nonneg
                  (Finset.range_mono (by omega)) (fun j _ _ => sq_nonneg _)
              have hcoeff :
                  ‖iteratedCovGrad (I := I) g₀ 4 2 i DRs‖ ^ 2 ≤
                    DR i * ∑ j ∈ Finset.range (i + 1),
                      ‖iteratedCovGrad (I := I) g₀ 2 2 j
                        (gInvDiffSlotCoeff (I := I) g₀ g₁)‖ ^ 2 := by
                simpa [DRs] using hDR g₁ i
              exact hcoeff.trans
                (mul_le_mul_of_nonneg_left (hwindow.trans hinv_jet_R) (hDR_nn i))
        _ = (∑ i ∈ Finset.range 3, DR i) * (Cinv * R) ^ 2 := by
              rw [Finset.sum_mul]
    have hdev_sum : (∑ i ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g₀ 4 2 i Dev‖ ^ 2) ≤
        8 * (∑ i ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 4 2 i DTHs‖ ^ 2) +
        8 * (∑ i ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 4 2 i DRs‖ ^ 2) := by
      have hsub : (∑ i ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 4 2 i Dev‖ ^ 2) ≤
          2 * (∑ i ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g₀ 4 2 i
              (reindexCoeffGen (I := I) (M := M) g₀ 4 2 DTHs ρA +
                reindexCoeffGen (I := I) (M := M) g₀ 4 2 DTHs ρAT)‖ ^ 2) +
          2 * (∑ i ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g₀ 4 2 i (DRs + DRs)‖ ^ 2) := by
        calc
          (∑ i ∈ Finset.range 3, ‖iteratedCovGrad (I := I) g₀ 4 2 i Dev‖ ^ 2)
              ≤ ∑ i ∈ Finset.range 3,
                (2 * ‖iteratedCovGrad (I := I) g₀ 4 2 i
                    (reindexCoeffGen (I := I) (M := M) g₀ 4 2 DTHs ρA +
                      reindexCoeffGen (I := I) (M := M) g₀ 4 2 DTHs ρAT)‖ ^ 2 +
                  2 * ‖iteratedCovGrad (I := I) g₀ 4 2 i (DRs + DRs)‖ ^ 2) := by
                    apply Finset.sum_le_sum
                    intro i hi
                    rw [hdev_eq, iteratedCovGrad_sub]
                    exact norm_sq_sub_le (I := I) (M := M) g₀ 4 (2 + i) _ _
          _ = 2 * (∑ i ∈ Finset.range 3,
                ‖iteratedCovGrad (I := I) g₀ 4 2 i
                  (reindexCoeffGen (I := I) (M := M) g₀ 4 2 DTHs ρA +
                    reindexCoeffGen (I := I) (M := M) g₀ 4 2 DTHs ρAT)‖ ^ 2) +
              2 * (∑ i ∈ Finset.range 3,
                ‖iteratedCovGrad (I := I) g₀ 4 2 i (DRs + DRs)‖ ^ 2) := by
                  rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      have hAB : (∑ i ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 4 2 i
            (reindexCoeffGen (I := I) (M := M) g₀ 4 2 DTHs ρA +
              reindexCoeffGen (I := I) (M := M) g₀ 4 2 DTHs ρAT)‖ ^ 2) ≤
          4 * (∑ i ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g₀ 4 2 i DTHs‖ ^ 2) := by
        calc
          _ ≤ ∑ i ∈ Finset.range 3,
              (2 * ‖iteratedCovGrad (I := I) g₀ 4 2 i
                  (reindexCoeffGen (I := I) (M := M) g₀ 4 2 DTHs ρA)‖ ^ 2 +
                2 * ‖iteratedCovGrad (I := I) g₀ 4 2 i
                  (reindexCoeffGen (I := I) (M := M) g₀ 4 2 DTHs ρAT)‖ ^ 2) := by
                  apply Finset.sum_le_sum
                  intro i hi
                  rw [iteratedCovGrad_add]
                  exact norm_sq_add_le (I := I) (M := M) g₀ 4 (2 + i) _ _
          _ = 4 * (∑ i ∈ Finset.range 3,
              ‖iteratedCovGrad (I := I) g₀ 4 2 i DTHs‖ ^ 2) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro i hi
                simp only [reindex_norm_sq (I := I) (M := M) g₀ 4 2]
                ring
      have hCC : (∑ i ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 4 2 i (DRs + DRs)‖ ^ 2) ≤
          4 * (∑ i ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g₀ 4 2 i DRs‖ ^ 2) := by
        calc
          _ ≤ ∑ i ∈ Finset.range 3,
              (2 * ‖iteratedCovGrad (I := I) g₀ 4 2 i DRs‖ ^ 2 +
                2 * ‖iteratedCovGrad (I := I) g₀ 4 2 i DRs‖ ^ 2) := by
                  apply Finset.sum_le_sum
                  intro i hi
                  rw [iteratedCovGrad_add]
                  exact norm_sq_add_le (I := I) (M := M) g₀ 4 (2 + i) _ _
          _ = 4 * (∑ i ∈ Finset.range 3,
              ‖iteratedCovGrad (I := I) g₀ 4 2 i DRs‖ ^ 2) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro i hi
                ring
      linarith
    have hraw : (∑ i ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g₀ 4 2 i Dev‖ ^ 2) ≤
        Kjet * (Cinv * R) ^ 2 := by
      dsimp [Kjet]
      nlinarith
    rw [htarget]
    exact hraw.trans (mul_le_mul_of_nonneg_right
      (by dsimp [K]; linarith [hKpt]) (sq_nonneg _))

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in



theorem top_path_dev_h2
    (hDim : Module.finrank ℝ E = 3)
    (g₀ g_bg : SmoothRiemannianMetric I M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_lt : δ < 1)
        (hδ : metricCauchySchwarzBound g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_lt : δ' < 1)
        (hδ' : metricCauchySchwarzBound g₀
          (ccTensorBilinSymm (I := I) g₀ T') δ')
        {R : ℝ}, 0 ≤ R → R ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T‖ ≤ R →
        ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T'‖ ≤ R →
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
                ((rhsTopPathIntegral (I := I) (M := M) g₀ g_bg T T'
                    hδ_lt hδ hδ'_lt hδ' -
                  deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀).toSection x) ≤
              (C * R) ^ 2) ∧
            (∑ i ∈ Finset.range 3,
              ‖iteratedCovGrad (I := I) g₀ 4 2 i
                (rhsTopPathIntegral (I := I) (M := M) g₀ g_bg T T'
                    hδ_lt hδ hδ'_lt hδ' -
                  deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)‖ ^ 2) ≤
              (C * R) ^ 2 := by
  classical
  obtain ⟨ρ, C, hρ, hC, hdev⟩ := phi_dev_h2 (I := I) (M := M) hDim g₀ g_bg
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro T T' δ hδ_lt hδ δ' hδ'_lt hδ' R hR hRρ hT hT'
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆ realizedSmallSet (δ := δ) (δ' := δ') := by
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_realizedSmallSet hδ_lt hδ'_lt
  have hSopen : IsOpen (realizedSmallSet (δ := δ) (δ' := δ')) :=
    realizedSmallSet_isOpen
  let Φ : ℝ → SmoothCcTensor g₀ 4 2 := fun s =>
    deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
        (realizedFam (I := I) g₀ T T' hδ hδ' s) -
      deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀
  have hjpath := rhsTop_path_joint (I := I) (M := M) g₀ g_bg T T' hδ hδ'
  have hjdev : linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 4 Φ
      (δ := δ) (δ' := δ') := by
    simpa [Φ] using phi_dev_joint (I := I) (M := M) g₀ g_bg T T' hδ hδ'
  let Pdev : SmoothCcTensor g₀ 4 2 :=
    pathIntegralCoeffField (I := I) (M := M) g₀ 4 2 Φ
      (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hjdev
  have hcpath : ∀ x : M, ContinuousOn (fun t : ℝ =>
      TensorRSSpace.toModel
        ((deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
          (realizedFam (I := I) g₀ T T' hδ hδ' t)).toSection x))
      (realizedSmallSet (δ := δ) (δ' := δ')) := by
    intro x
    have h := hjpath
    rw [linearizedRicciThreeArmHjoint] at h
    exact jointContMDiff_toModel_continuous_slice (I := I) g₀ 4 2
      (fun s => deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
        (realizedFam (I := I) g₀ T T' hδ hδ' s))
      (realizedSmallSet (δ := δ) (δ' := δ')) h x
  have hcdev : ∀ x : M, ContinuousOn (fun t : ℝ =>
      TensorRSSpace.toModel ((Φ t).toSection x))
      (realizedSmallSet (δ := δ) (δ' := δ')) := fun x =>
    jointContMDiff_toModel_continuous_slice (I := I) g₀ 4 2 Φ
      (realizedSmallSet (δ := δ) (δ' := δ')) hjdev x
  have heq : rhsTopPathIntegral (I := I) (M := M) g₀ g_bg T T'
      hδ_lt hδ hδ'_lt hδ' -
      deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀ = Pdev := by
    have hPeq : rhsTopPathIntegral (I := I) (M := M) g₀ g_bg T T'
        hδ_lt hδ hδ'_lt hδ' =
        pathIntegralCoeffField (I := I) (M := M) g₀ 4 2
          (fun s => deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
            (realizedFam (I := I) g₀ T T' hδ hδ' s))
          (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hjpath := rfl
    apply SmoothCcTensor.ext
    apply ContMDiffSection.ext
    intro x
    apply TensorRSSpace.toModel_injective
    change TensorRSSpace.toModel
        ((rhsTopPathIntegral (I := I) (M := M) g₀ g_bg T T'
          hδ_lt hδ hδ'_lt hδ' -
            deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀).toSection x) =
      TensorRSSpace.toModel (Pdev.toSection x)
    rw [show (rhsTopPathIntegral (I := I) (M := M) g₀ g_bg T T'
          hδ_lt hδ hδ'_lt hδ' -
            deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀).toSection x =
        (rhsTopPathIntegral (I := I) (M := M) g₀ g_bg T T'
          hδ_lt hδ hδ'_lt hδ').toSection x -
          (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀).toSection x from by
      rw [SmoothCcTensor.toSection_sub]; rfl]
    rw [TensorRSSpace.toModel_sub, hPeq]
    dsimp [Pdev]
    rw [pathIntegralFib_toModel, pathIntegralFib_toModel]
    have hint : IntervalIntegrable (fun t : ℝ =>
        TensorRSSpace.toModel
          ((deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
            (realizedFam (I := I) g₀ T T' hδ hδ' t)).toSection x))
        MeasureTheory.volume 0 1 :=
      ((hcpath x).mono hSI).intervalIntegrable
    rw [show (∫ t in (0 : ℝ)..1, TensorRSSpace.toModel ((Φ t).toSection x)) =
        ∫ t in (0 : ℝ)..1,
          (TensorRSSpace.toModel
              ((deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
                (realizedFam (I := I) g₀ T T' hδ hδ' t)).toSection x) -
            TensorRSSpace.toModel
              ((deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀).toSection x)) from
      intervalIntegral.integral_congr (fun t _ => by
        simp only [Φ]
        rw [show (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
              (realizedFam (I := I) g₀ T T' hδ hδ' t) -
                deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀).toSection x =
              (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
                (realizedFam (I := I) g₀ T T' hδ hδ' t)).toSection x -
              (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀).toSection x from by
          rw [SmoothCcTensor.toSection_sub]; rfl]
        rw [TensorRSSpace.toModel_sub])]
    rw [intervalIntegral.integral_sub hint intervalIntegrable_const,
      intervalIntegral.integral_const]
    norm_num
  have hCR : 0 ≤ C * R := mul_nonneg hC hR
  have hper : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
          ((Φ s).toSection x) ≤ (C * R) ^ 2) ∧
        (∑ i ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 4 2 i (Φ s)‖ ^ 2) ≤ (C * R) ^ 2 := by
    intro s hs
    simpa [Φ] using hdev T T' hδ_lt hδ hδ'_lt hδ' hR hRρ hT hT' hs.1 hs.2
  refine ⟨?_, ?_⟩
  · intro x
    rw [heq]
    dsimp [Pdev]
    have hsup : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
          ((Φ t).toSection x)) ≤ C * R := by
      intro t ht
      calc
        Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
            ((Φ t).toSection x)) ≤ Real.sqrt ((C * R) ^ 2) :=
          Real.sqrt_le_sqrt ((hper t ht).1 x)
        _ = C * R := Real.sqrt_sq hCR
    exact riemannianFiberNormSq_pathIntegralCoeffField_le_sq
      (I := I) (M := M) g₀ 4 2 Φ
      (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hjdev x
      (C * R) hCR ((hcdev x).mono (Icc_subset_realizedSmallSet hδ_lt hδ'_lt)) hsup
  · rw [heq]
    dsimp [Pdev]
    exact path_jetL2_le (I := I) (M := M) g₀ 4 2 2 Φ
      (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hjdev hCR
      (fun t ht => by simpa using (hper t ht).2)



theorem top_path_split
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound g₀
      (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound g₀
      (ccTensorBilinSymm (I := I) g₀ T') δ')
    (U : SmoothCcTensor g₀ 0 2) :
    operatorFieldApply (I := I) (M := M) g₀ 4 2
        (rhsTopPathIntegral (I := I) (M := M) g₀ g_bg T T'
          hδ_lt hδ hδ'_lt hδ')
        (iteratedCovGrad (I := I) g₀ 0 2 2 U) -
      rawTensorConnLapSmooth (I := I) g₀ 0 2 U =
    operatorFieldApply (I := I) (M := M) g₀ 4 2
        (rhsTopPathIntegral (I := I) (M := M) g₀ g_bg T T'
            hδ_lt hδ hδ'_lt hδ' -
          deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)
        (iteratedCovGrad (I := I) g₀ 0 2 2 U) +
      operatorFieldApply (I := I) (M := M) g₀ 2 2
        (phiMetCurvCoeff (I := I) g₀ g_bg g₀)
        (iteratedCovGrad (I := I) g₀ 0 2 0 U) := by
  have hlap : rawTensorConnLapSmooth (I := I) g₀ 0 2 U =
      operatorFieldApply (I := I) (M := M) g₀ 4 2
        (ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₀)
        (iteratedCovGrad (I := I) g₀ 0 2 2 U) := by
    apply smoothCcTensor_ext_of_unitModel
    intro x
    apply ContinuousMultilinearMap.ext
    intro v
    exact rawTensorConnLapSmooth_eq_appCc_cometricDoubleTrace
      (I := I) (M := M) g₀ U x v
  rw [hlap, ← appCc_sub_left]
  rw [show rhsTopPathIntegral (I := I) (M := M) g₀ g_bg T T'
          hδ_lt hδ hδ'_lt hδ' -
        ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₀ =
      (rhsTopPathIntegral (I := I) (M := M) g₀ g_bg T T'
          hδ_lt hδ hδ'_lt hδ' -
        deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀) +
      (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀ -
        ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₀) by abel]
  rw [appCc_add_left, appCc_sub_left,
    phiMet_curv_fold (I := I) (M := M) g₀ g_bg g₀ U]



theorem fixed_curv_h1
    (hDim : Module.finrank ℝ E = 3)
    (g₀ g_bg : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ U : SmoothCcTensor g₀ 0 2,
      ‖ccTensorToHs (I := I) (M := M) g₀ 2 (1 : ℝ)
          (operatorFieldApply (I := I) (M := M) g₀ 2 2
            (phiMetCurvCoeff (I := I) g₀ g_bg g₀) U)‖ ≤
        C * ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) U‖ := by
  obtain ⟨Capp, hCapp, happ⟩ :=
    appCc_c1_h2_h1 (I := I) (M := M) hDim g₀ 2 2
  obtain ⟨K, hK, hKbound⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor
      (I := I) (M := M) g₀ 2 2 (phiMetCurvCoeff (I := I) g₀ g_bg g₀)
  let B0 : ℝ := Real.sqrt K
  let B1 : ℝ := ‖covGrad (I := I) (M := M) g₀ 2 2
    (phiMetCurvCoeff (I := I) g₀ g_bg g₀)‖
  let C : ℝ := Capp * (B0 + B1)
  have hB0 : 0 ≤ B0 := Real.sqrt_nonneg _
  have hB1 : 0 ≤ B1 := norm_nonneg _
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro U
  have hpoint : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
          ((phiMetCurvCoeff (I := I) g₀ g_bg g₀).toSection x) ≤ B0 ^ 2 := by
    intro x
    rw [show B0 ^ 2 = K by dsimp [B0]; exact Real.sq_sqrt hK]
    exact hKbound x
  simpa only [C, B1] using happ
    (phiMetCurvCoeff (I := I) g₀ g_bg g₀) U B0 B1 hB0 hB1 hpoint (le_refl B1)




theorem top_path_h1
    (hDim : Module.finrank ℝ E = 3)
    (g₀ g_bg : SmoothRiemannianMetric I M) :
    ∃ Ctop Clow : ℝ, 0 ≤ Ctop ∧ 0 ≤ Clow ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_lt : δ < 1)
        (hδ : metricCauchySchwarzBound g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_lt : δ' < 1)
        (hδ' : metricCauchySchwarzBound g₀
          (ccTensorBilinSymm (I := I) g₀ T') δ')
        (U : SmoothCcTensor g₀ 0 2) (A : ℝ),
        0 ≤ A →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
              ((rhsTopPathIntegral (I := I) (M := M) g₀ g_bg T T'
                  hδ_lt hδ hδ'_lt hδ' -
                deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀).toSection x) ≤
            A ^ 2) →
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 4 2 j
            (rhsTopPathIntegral (I := I) (M := M) g₀ g_bg T T'
                hδ_lt hδ hδ'_lt hδ' -
              deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)‖ ^ 2) ≤ A ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g₀ 2 (1 : ℝ)
          (operatorFieldApply (I := I) (M := M) g₀ 4 2
              (rhsTopPathIntegral (I := I) (M := M) g₀ g_bg T T'
                hδ_lt hδ hδ'_lt hδ')
              (iteratedCovGrad (I := I) g₀ 0 2 2 U) -
            rawTensorConnLapSmooth (I := I) g₀ 0 2 U)‖ ≤
          Ctop * A * ‖ccTensorToHs (I := I) (M := M) g₀ 2 (3 : ℝ) U‖ +
            Clow * ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) U‖ := by
  obtain ⟨Ctop, hCtop, htop⟩ :=
    appCc_h2_h3_h1 (I := I) (M := M) hDim g₀ 2 2
  obtain ⟨Clow, hClow, hlow⟩ := fixed_curv_h1 (I := I) (M := M) hDim g₀ g_bg
  refine ⟨Ctop, Clow, hCtop, hClow, ?_⟩
  intro T T' δ hδ_lt hδ δ' hδ'_lt hδ' U A hA hdevPt hdevJet
  have htop' := htop
    (rhsTopPathIntegral (I := I) (M := M) g₀ g_bg T T'
        hδ_lt hδ hδ'_lt hδ' -
      deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)
    U A hA hdevPt hdevJet
  have hlow' := hlow U
  rw [top_path_split (I := I) (M := M) g₀ g_bg T T'
    hδ_lt hδ hδ'_lt hδ' U, ccTensorToHs_add]
  exact (norm_add_le _ _).trans (add_le_add htop' hlow')




theorem top_path_ball_h1
    (hDim : Module.finrank ℝ E = 3)
    (g₀ g_bg : SmoothRiemannianMetric I M) :
    ∃ ρ Ctop Clow : ℝ, 0 < ρ ∧ 0 ≤ Ctop ∧ 0 ≤ Clow ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_lt : δ < 1)
        (hδ : metricCauchySchwarzBound g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_lt : δ' < 1)
        (hδ' : metricCauchySchwarzBound g₀
          (ccTensorBilinSymm (I := I) g₀ T') δ')
        {R : ℝ}, 0 ≤ R → R ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T‖ ≤ R →
        ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T'‖ ≤ R →
        ∀ U : SmoothCcTensor g₀ 0 2,
          ‖ccTensorToHs (I := I) (M := M) g₀ 2 (1 : ℝ)
            (operatorFieldApply (I := I) (M := M) g₀ 4 2
                (rhsTopPathIntegral (I := I) (M := M) g₀ g_bg T T'
                  hδ_lt hδ hδ'_lt hδ')
                (iteratedCovGrad (I := I) g₀ 0 2 2 U) -
              rawTensorConnLapSmooth (I := I) g₀ 0 2 U)‖ ≤
            Ctop * R * ‖ccTensorToHs (I := I) (M := M) g₀ 2 (3 : ℝ) U‖ +
              Clow * ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) U‖ := by
  obtain ⟨ρ, Cdev, hρ, hCdev, hdev⟩ :=
    top_path_dev_h2 (I := I) (M := M) hDim g₀ g_bg
  obtain ⟨Capp, Clow, hCapp, hClow, happ⟩ :=
    top_path_h1 (I := I) (M := M) hDim g₀ g_bg
  refine ⟨ρ, Capp * Cdev, Clow, hρ, mul_nonneg hCapp hCdev, hClow, ?_⟩
  intro T T' δ hδ_lt hδ δ' hδ'_lt hδ' R hR hRρ hT hT' U
  obtain ⟨hpt, hjet⟩ := hdev T T' hδ_lt hδ hδ'_lt hδ' hR hRρ hT hT'
  have hA : 0 ≤ Cdev * R := mul_nonneg hCdev hR
  have hbound := happ T T' hδ_lt hδ hδ'_lt hδ' U (Cdev * R)
    hA hpt hjet
  simpa only [mul_assoc] using hbound

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
