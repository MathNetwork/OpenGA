import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RemainderCoeffL2JetMoser
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.DeTurckLieHigherOrderCoeffField
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradFibreNormPermutationInvariance
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.SymmAbsorbedCoeffInputReindexBounds
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradLinear
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.FiberNormSubadditivity


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open MeasureTheory Set Filter Topology Bundle Manifold Tensor0SBundle ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Integral.Connection

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (traceHessianCoeff traceHessianCoeff_toSection traceHessianFib traceHessianSlotPerm
    domDomCongrFib domDomCongrFib_apply reindexCoeffGen reindexCoeffGen_toSection
    reindexCoeffFibGen reindexCoeffFibGen_apply riemannianFiberNormSq_reindexCoeffFibGen
    deTurckLieTraceCoeff deTurckLieTraceCoeff_toSection deTurckLieTraceFib
    domDomCongrFibPerm domDomCongrFibPerm_apply deTurckLieArm2DivSlotPermA
    deTurckLieArm2DivSlotPermAT deTurckLieArm2PrincipalCoeff
    exists_lichnerowicz_cometric_realizedFam_rfns_ballUniform)
open DifferentialGeometry.PDE.DeTurck.RicciLinearization (realizedFam)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private theorem traceHessianSlotPerm_inv_mul_apply (σ : Equiv.Perm (Fin 4)) (j : Fin 4) :
    traceHessianSlotPerm ((traceHessianSlotPerm⁻¹ * σ) j) = σ j := by
  rw [Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Equiv.apply_symm_apply]

omit [NeZero (Module.finrank ℝ E)] in
omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem deTurckLieTraceCoeff_eq_reindex_traceHessianCoeff
    (g₀ g₁ : SmoothRiemannianMetric I M) (σ ρ : Equiv.Perm (Fin 4))
    (hcomp : ∀ j : Fin 4, traceHessianSlotPerm (ρ j) = σ j) :
    deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ σ =
      reindexCoeffGen (I := I) (M := M) g₀ 4 2
        (traceHessianCoeff (I := I) (M := M) g₀ g₁) ρ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [deTurckLieTraceCoeff_toSection, reindexCoeffGen_toSection, traceHessianCoeff_toSection]
  apply ContinuousLinearMap.ext
  intro D
  rw [reindexCoeffFibGen_apply, deTurckLieTraceFib, traceHessianFib,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    domDomCongrFibPerm_apply, domDomCongrFib_apply,
    Tensor0SBundle.Tensor0SSpace.toModel_ofModel]
  have harg : ContinuousMultilinearMap.domDomCongr σ
      (Tensor0SBundle.Tensor0SSpace.toModel D) =
      ContinuousMultilinearMap.domDomCongr traceHessianSlotPerm
        (ContinuousMultilinearMap.domDomCongr ρ
          (Tensor0SBundle.Tensor0SSpace.toModel D)) := by
    apply ContinuousMultilinearMap.ext
    intro v
    simp only [ContinuousMultilinearMap.domDomCongr_apply]
    refine congrArg _ (funext fun j => ?_)
    rw [hcomp j]
  rw [harg]

omit [NeZero (Module.finrank ℝ E)] in
private theorem normSq_iteratedCovGrad_reindexCoeffGen_eq
    (g₀ : SmoothRiemannianMetric I M) (R : SmoothCcTensor g₀ 4 2)
    (ρ : Equiv.Perm (Fin 4)) (i : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 4 2 i
        (reindexCoeffGen (I := I) (M := M) g₀ 4 2 R ρ)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g₀ 4 2 i R‖ ^ 2 := by
  rw [SmoothCcTensor.norm_def (I := I) (M := M)
      (iteratedCovGrad (I := I) g₀ 4 2 i (reindexCoeffGen (I := I) (M := M) g₀ 4 2 R ρ)),
    SmoothCcTensor.norm_def (I := I) (M := M) (iteratedCovGrad (I := I) g₀ 4 2 i R),
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g₀ 4 (2 + i)
      (iteratedCovGrad (I := I) g₀ 4 2 i (reindexCoeffGen (I := I) (M := M) g₀ 4 2 R ρ)),
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g₀ 4 (2 + i)
      (iteratedCovGrad (I := I) g₀ 4 2 i R)]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact riemannianFiberNormSq_iteratedCovGrad_reindexCoeffGen_eq (I := I) (M := M) g₀ 4 2 R ρ i x

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem rfns_toSection_reindexCoeffGen_eq
    (g₀ : SmoothRiemannianMetric I M) (R : SmoothCcTensor g₀ 4 2)
    (ρ : Equiv.Perm (Fin 4)) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
        ((reindexCoeffGen (I := I) (M := M) g₀ 4 2 R ρ).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (R.toSection x) := by
  rw [reindexCoeffGen_toSection]
  exact riemannianFiberNormSq_reindexCoeffFibGen (I := I) (M := M) g₀ 4 2 x ρ
    (show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
      R.toSection x)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem riemannianFiberNormSq_neg_local
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) (v : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (-v) =
      riemannianFiberNormSq (I := I) (M := M) g r s x v := by
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (-v),
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x v]
  rw [TensorRSSpace.toModel_neg]
  rw [← neg_one_smul ℝ (TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
        (r := r) (s := s) (x := x) v),
    tensorInnerPointwise_smul_left, tensorInnerPointwise_smul_right]
  ring

theorem deTurckLieArm2PrincipalCoeff_realizedFam_jetL2_perOrder_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ P : ℕ → ℝ, (∀ i, 0 ≤ P i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (_hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a → ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ‖iteratedCovGrad (I := I) g₀ 4 2 i
              (deTurckLieArm2PrincipalCoeff (I := I) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)‖ ^ 2 ≤ P i := by
  obtain ⟨Q, hQ_nn, hQ⟩ :=
    traceHessianCoeff_realizedFam_jetL2_perOrder_ballUniform (I := I) (M := M) g₀ a
      ha_super hR hδ₀
  refine ⟨fun i => 9 * Q i, fun i => by linarith [hQ_nn i], ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball i hi s hs
  set g₁ : SmoothRiemannianMetric I M := realizedFam (I := I) g₀ T T' hδ hδ' s with hg₁
  have hH : ‖iteratedCovGrad (I := I) g₀ 4 2 i
      (traceHessianCoeff (I := I) (M := M) g₀ g₁)‖ ^ 2 ≤ Q i := by
    rw [hg₁]
    exact hQ T T' hδ_le hδ hδ'_le hδ' hTball hT'ball i hi s hs
  have hA : ‖iteratedCovGrad (I := I) g₀ 4 2 i
      (deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ deTurckLieArm2DivSlotPermA)‖ ^ 2 ≤ Q i := by
    rw [deTurckLieTraceCoeff_eq_reindex_traceHessianCoeff (I := I) (M := M) g₀ g₁
        deTurckLieArm2DivSlotPermA (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermA)
        (traceHessianSlotPerm_inv_mul_apply deTurckLieArm2DivSlotPermA),
      normSq_iteratedCovGrad_reindexCoeffGen_eq]
    exact hH
  have hAT : ‖iteratedCovGrad (I := I) g₀ 4 2 i
      (deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ deTurckLieArm2DivSlotPermAT)‖ ^ 2 ≤ Q i := by
    rw [deTurckLieTraceCoeff_eq_reindex_traceHessianCoeff (I := I) (M := M) g₀ g₁
        deTurckLieArm2DivSlotPermAT (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermAT)
        (traceHessianSlotPerm_inv_mul_apply deTurckLieArm2DivSlotPermAT),
      normSq_iteratedCovGrad_reindexCoeffGen_eq]
    exact hH
  have hdecomp : iteratedCovGrad (I := I) g₀ 4 2 i
      (deTurckLieArm2PrincipalCoeff (I := I) g₀ g₁ g_bg)
      = iteratedCovGrad (I := I) g₀ 4 2 i
          (deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ deTurckLieArm2DivSlotPermA)
        + iteratedCovGrad (I := I) g₀ 4 2 i
          (deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ deTurckLieArm2DivSlotPermAT)
        - iteratedCovGrad (I := I) g₀ 4 2 i
          (traceHessianCoeff (I := I) (M := M) g₀ g₁) := by
    rw [deTurckLieArm2PrincipalCoeff, iteratedCovGrad_sub, iteratedCovGrad_add]
  rw [hdecomp]
  set X := iteratedCovGrad (I := I) g₀ 4 2 i
    (deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ deTurckLieArm2DivSlotPermA) with hX
  set Y := iteratedCovGrad (I := I) g₀ 4 2 i
    (deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ deTurckLieArm2DivSlotPermAT) with hY
  set Z := iteratedCovGrad (I := I) g₀ 4 2 i
    (traceHessianCoeff (I := I) (M := M) g₀ g₁) with hZ
  have htri : ‖X + Y - Z‖ ≤ ‖X‖ + ‖Y‖ + ‖Z‖ :=
    le_trans (norm_sub_le _ _) (add_le_add (norm_add_le _ _) le_rfl)
  nlinarith [htri, hA, hAT, hH, norm_nonneg X, norm_nonneg Y, norm_nonneg Z,
    norm_nonneg (X + Y - Z), sq_nonneg (‖X‖ - ‖Y‖), sq_nonneg (‖X‖ - ‖Z‖),
    sq_nonneg (‖Y‖ - ‖Z‖),
    mul_le_mul htri htri (norm_nonneg (X + Y - Z))
      (add_nonneg (add_nonneg (norm_nonneg X) (norm_nonneg Y)) (norm_nonneg Z))]

omit [BoundarylessManifold I M] in
theorem deTurckLieArm2PrincipalCoeff_realizedFam_rfns_order0_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (_hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 → ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
              ((deTurckLieArm2PrincipalCoeff (I := I) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg).toSection x) ≤ Λ := by
  obtain ⟨Λcom, hΛ_nn, hΛ⟩ :=
    exists_lichnerowicz_cometric_realizedFam_rfns_ballUniform (I := I) (M := M) g₀ a
      ha_super hR hδ₀
  refine ⟨10 * Λcom, by linarith, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball s hs x
  set g₁ : SmoothRiemannianMetric I M := realizedFam (I := I) g₀ T T' hδ hδ' s with hg₁
  have hH : riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
      ((traceHessianCoeff (I := I) (M := M) g₀ g₁).toSection x) ≤ Λcom := by
    rw [hg₁]
    exact (hΛ T T' hδ_le hδ hδ'_le hδ' hTball hT'ball s hs x).2
  have hA : riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
      ((deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁
        deTurckLieArm2DivSlotPermA).toSection x) ≤ Λcom := by
    rw [deTurckLieTraceCoeff_eq_reindex_traceHessianCoeff (I := I) (M := M) g₀ g₁
        deTurckLieArm2DivSlotPermA (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermA)
        (traceHessianSlotPerm_inv_mul_apply deTurckLieArm2DivSlotPermA),
      rfns_toSection_reindexCoeffGen_eq]
    exact hH
  have hAT : riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
      ((deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁
        deTurckLieArm2DivSlotPermAT).toSection x) ≤ Λcom := by
    rw [deTurckLieTraceCoeff_eq_reindex_traceHessianCoeff (I := I) (M := M) g₀ g₁
        deTurckLieArm2DivSlotPermAT (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermAT)
        (traceHessianSlotPerm_inv_mul_apply deTurckLieArm2DivSlotPermAT),
      rfns_toSection_reindexCoeffGen_eq]
    exact hH
  have hsec : (deTurckLieArm2PrincipalCoeff (I := I) g₀ g₁ g_bg).toSection x
      = (deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁
            deTurckLieArm2DivSlotPermA).toSection x
        + (deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁
            deTurckLieArm2DivSlotPermAT).toSection x
        - (traceHessianCoeff (I := I) (M := M) g₀ g₁).toSection x := by
    rw [deTurckLieArm2PrincipalCoeff, SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub,
      Pi.sub_apply, SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]
  rw [hsec, sub_eq_add_neg]
  have h1 := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 4 2 x
    ((deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁
        deTurckLieArm2DivSlotPermA).toSection x
      + (deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁
        deTurckLieArm2DivSlotPermAT).toSection x)
    (-(traceHessianCoeff (I := I) (M := M) g₀ g₁).toSection x)
  have h2 := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 4 2 x
    ((deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁
        deTurckLieArm2DivSlotPermA).toSection x)
    ((deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁
        deTurckLieArm2DivSlotPermAT).toSection x)
  have hneg := riemannianFiberNormSq_neg_local (I := I) (M := M) g₀ 4 2 x
    ((traceHessianCoeff (I := I) (M := M) g₀ g₁).toSection x)
  linarith [h1, h2, hneg, hA, hAT, hH]

end DifferentialGeometry.Integral.Connection

end
