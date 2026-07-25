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
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RiemannCoefficientPalatiniRefoldResidualFieldBallUniform
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RiemannCoefficientPalatiniRefoldResidualFieldL2JetWindow


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


omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] in
private lemma coeffOpApply_slotSwapField_eq_apply_of_symm (g₀ : SmoothRiemannianMetric I M)
    (D : SmoothCcTensor g₀ 2 2) (T : SmoothCcTensor g₀ 0 2)
    (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ T x v w = smoothCcTensorBilinForm (I := I) g₀ T x w v) :
    operatorFieldApply (I := I) (M := M) g₀ 2 2
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 2 D (ccInputSlotSwapField (I := I) (M := M) g₀)) T =
      operatorFieldApply (I := I) (M := M) g₀ 2 2 D T := by
  refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀ (fun x => ?_)
  have hswapfix : inputSlotSwapFib (I := I) (M := M) x
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from T.toSection x)
        (unitTensor (I := I) (M := M) x)) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from T.toSection x)
        (unitTensor (I := I) (M := M) x) := by
    apply Tensor0SSpace.toModel_injective
    beta_reduce
    rw [slotSwapFib_apply, Tensor0SSpace.toModel_ofModel]
    refine ContinuousMultilinearMap.ext (fun v => ?_)
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    have hbridge : Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from T.toSection x)
          (unitTensor (I := I) (M := M) x)) = unitModel (I := I) (M := M) g₀ 2 T x := rfl
    rw [hbridge]
    have hveta : (fun i => v ((Equiv.swap (0 : Fin 2) 1) i)) = ![v 1, v 0] := by
      funext i
      fin_cases i <;> rfl
    have hveta' : v = ![v 0, v 1] := by
      funext i
      fin_cases i <;> rfl
    rw [hveta]
    conv_rhs => rw [hveta']
    rw [unitModel_eq_ccTensorBilin_local (I := I) (M := M) g₀ T x (v 1) (v 0),
      unitModel_eq_ccTensorBilin_local (I := I) (M := M) g₀ T x (v 0) (v 1)]
    exact hTsymm x (v 1) (v 0)
  rw [show unitModel (I := I) (M := M) g₀ 2
      (operatorFieldApply (I := I) (M := M) g₀ 2 2
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 2 D (ccInputSlotSwapField (I := I) (M := M) g₀)) T) x =
    Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from D.toSection x)
        (inputSlotSwapFib (I := I) (M := M) x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from T.toSection x)
            (unitTensor (I := I) (M := M) x)))) from rfl]
  rw [hswapfix]
  rfl


theorem exists_riemannPalatini_refold_identity_data
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∃ qA qB : Fin 4 → Equiv.Perm (Fin 4),
      IsFramePairPartner qA qB ∧
      ∀ (T : SmoothCcTensor g₀ 0 2)
        (_hTsymm : ∀ (x : M) (v w : TangentSpace I x),
          smoothCcTensorBilinForm (I := I) g₀ T x v w = smoothCcTensorBilinForm (I := I) g₀ T x w v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        ∃ C0ra : ℝ → SmoothCcTensor g₀ 2 2,
          linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2 C0ra (δ := δ) (δ' := δ) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1,
            operatorFieldApply (I := I) (M := M) g₀ 2 2
                (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ s))
                (iteratedCovGrad (I := I) g₀ 0 2 0 T) =
              operatorFieldApply (I := I) (M := M) g₀ 2 2 (C0ra s)
                  (iteratedCovGrad (I := I) g₀ 0 2 0 T) +
                operatorFieldApply (I := I) (M := M) g₀ 4 2
                  ((2 : ℝ) • riemannPalatiniRefoldC2Family (I := I) (M := M) g₀ T hδ hδZ
                    qA qB s)
                  (iteratedCovGrad (I := I) g₀ 0 2 2 T)) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x ((C0ra s).toSection x) ≤
              Λ ^ 2) ∧
          (∀ i : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) 1,
            ‖iteratedCovGrad (I := I) g₀ 2 2 i (C0ra s)‖ ^ 2 ≤
              K i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2)) := by
  classical
  obtain ⟨ΛQ, hΛQ_nn, hcapQ⟩ :=
    exists_ricciArmOrder0AACommCoeffField_realizedFam_fiberNormSq_ballUniform (I := I) (M := M)
      g₀ a ha_super hR hδ₀
  obtain ⟨ΛB, hΛB_nn, hcapB⟩ :=
    exists_ricciArmOrder0BackgroundCurvatureCoeffField_realizedFam_riemannianFiberNormSq_ballUniform (I := I) (M := M)
      g₀ a ha_super hR hδ₀
  obtain ⟨ΛS, hΛS_nn, hcapS⟩ :=
    exists_ricciArmSharpGradKoszulResidualField_realizedFam_riemannianFiberNormSq_uniformBound (I := I) (M := M)
      g₀ a ha_super hR hδ₀
  obtain ⟨ΛF, hΛF_nn, hcapF⟩ :=
    exists_ricciArmRicciFoldRemainderField_realizedFam_riemannianFiberNormSq_uniformBound (I := I) (M := M)
      g₀ a ha_super hR hδ₀
  obtain ⟨KRm, hKRm_nn, hKRm⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 2 2
      (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)
  obtain ⟨KB0, hKB0_nn, hKB0⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 2 2
      (ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₀)
  obtain ⟨KQw, hKQw_nn, hwinQ⟩ :=
    exists_ricciArmOrder0AACommCoeffField_realizedFam_l2JetWindow (I := I) (M := M)
      g₀ a ha_super hR hδ₀
  obtain ⟨KBw, hKBw_nn, hwinB⟩ :=
    exists_ricciArmOrder0BgRCommCoeffField_realizedFam_backgroundDifference_l2JetWindow
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨KSw, hKSw_nn, hwinS⟩ :=
    exists_ricciArmSharpGradKoszulResidualField_realizedFam_l2JetWindow (I := I) (M := M)
      g₀ a ha_super hR hδ₀
  obtain ⟨KFw, hKFw_nn, hwinF⟩ :=
    exists_ricciArmRicciFoldRemainderField_realizedFam_l2JetWindow (I := I) (M := M)
      g₀ a ha_super hR hδ₀
  have hΛSQ_nn : (0 : ℝ) ≤
      2 * KRm + 8 * (2 * ΛQ + 2 * (2 * (2 * (2 * ΛB + 2 * KB0) + 2 * ΛS) + 2 * ΛF)) := by
    linarith [hΛQ_nn, hΛB_nn, hΛS_nn, hΛF_nn, hKRm_nn, hKB0_nn]
  refine ⟨Real.sqrt
      (2 * KRm + 8 * (2 * ΛQ + 2 * (2 * (2 * (2 * ΛB + 2 * KB0) + 2 * ΛS) + 2 * ΛF))),
    Real.sqrt_nonneg _,
    fun i => 2 * ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2
      + 8 * (2 * KQw i + 2 * (2 * (2 * KBw i + 2 * KSw i) + 2 * KFw i)),
    fun i => by
      have h5 : (0 : ℝ) ≤ ‖iteratedCovGrad (I := I) g₀ 2 2 i
          (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 := sq_nonneg _
      linarith [hKQw_nn i, hKBw_nn i, hKSw_nn i, hKFw_nn i],
    ![Equiv.swap (0 : Fin 4) 2, Equiv.swap (1 : Fin 4) 3,
      Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3, 1],
    fun k => Equiv.swap (0 : Fin 4) 1 *
      (![Equiv.swap (0 : Fin 4) 2, Equiv.swap (1 : Fin 4) 3,
        Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3, 1] k),
    fun _ => rfl, ?_⟩
  intro T hTsymm δ hδ_le hδ hδZ hball
  have hZball : ∀ j : ℕ, j ≤ a + 2 →
      ‖iteratedCovGrad (I := I) g₀ 0 2 j (0 : SmoothCcTensor g₀ 0 2)‖ ≤ R := by
    intro j hj
    have hzero : iteratedCovGrad (I := I) g₀ 0 2 j (0 : SmoothCcTensor g₀ 0 2) = 0 := by
      have h := iteratedCovGrad_sub (I := I) (g := g₀) (r := 0) (s := 2) (j := j) T T
      rw [sub_self, sub_self] at h
      exact h
    rw [hzero, norm_zero]
    exact hR
  refine ⟨fun s =>
    ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀
      + (2 : ℝ) •
        (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T 0 hδ hδZ s)
          + ((ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T 0 hδ hδZ s)
              - ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₀)
              + (1 / 2 : ℝ) • ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ s) (s • T)
              - ricciArmRicciFoldRemainderField (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ s) (s • T))),
    ?_, ?_, ?_, ?_⟩
  · exact threeArmHjoint_add_local (I := I) (M := M) g₀ _ _
      (threeArmHjoint_const_local (I := I) (M := M) g₀
        (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀))
      (threeArmHjoint_const_smul_local (I := I) (M := M) g₀ (2 : ℝ) _
        (threeArmHjoint_add_local (I := I) (M := M) g₀ _ _
          (ricciArmOrder0AACommCoeffField_realizedFam_threeArmHjoint (I := I) (M := M)
            g₀ T hδ hδZ)
          (threeArmHjoint_sub_local (I := I) (M := M) g₀ _ _
            (threeArmHjoint_add_local (I := I) (M := M) g₀ _ _
              (threeArmHjoint_sub_local (I := I) (M := M) g₀ _ _
                (ricciArmOrder0BgRCommCoeffField_realizedFam_threeArmHjoint (I := I) (M := M)
                  g₀ T hδ hδZ)
                (threeArmHjoint_const_local (I := I) (M := M) g₀
                  (ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₀)))
              (threeArmHjoint_const_smul_local (I := I) (M := M) g₀ (1 / 2 : ℝ) _
                (ricciArmSharpGradKoszulResidualField_realizedFam_threeArmHjoint
                  (I := I) (M := M) g₀ T hδ hδZ)))
            (ricciArmRicciFoldRemainderField_realizedFam_threeArmHjoint (I := I) (M := M)
              g₀ T hδ hδZ))))
  · intro s hs
    have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
    have hs_mem : s ∈ realizedSmallSet (δ := δ) (δ' := δ) :=
      Icc_subset_realizedSmallSet hδ_lt hδ_lt hs
    have hcP : convexPerturbation (I := I) g₀ T 0 s = s • T := by
      rw [convexPerturbation, smul_zero, zero_add]
    have htie : ∀ (y : M) (v w : TangentSpace I y),
        (realizedFam (I := I) g₀ T 0 hδ hδZ s).inner y v w =
          g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ (s • T) y v w := by
      intro y v w
      rw [← hcP]
      exact realizedFam_inner_of_mem (I := I) g₀ T 0 hδ hδZ hs_mem y v w
    have hPsymm : ∀ (x : M) (v w : TangentSpace I x),
        smoothCcTensorBilinForm (I := I) g₀ (s • T) x v w =
          smoothCcTensorBilinForm (I := I) g₀ (s • T) x w v := by
      intro x v w
      rw [ccTensorBilin_smul_local, ccTensorBilin_smul_local, hTsymm x v w]
    have hsymmT : ccTensor02Symm (I := I) (M := M) g₀ T = T :=
      symmS_eq_self_of_symm (I := I) (M := M) g₀ T hTsymm
    beta_reduce
    simp only [iteratedCovGrad_zero]
    have hfam : (2 : ℝ) • riemannPalatiniRefoldC2Family (I := I) (M := M) g₀ T hδ hδZ
        ![Equiv.swap (0 : Fin 4) 2, Equiv.swap (1 : Fin 4) 3,
          Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3, 1]
        (fun k => Equiv.swap (0 : Fin 4) 1 *
          (![Equiv.swap (0 : Fin 4) 2, Equiv.swap (1 : Fin 4) 3,
            Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3, 1] k)) s =
        (2 * s : ℝ) • curvatureActionKernelCoeffField (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ s)
          (ccTensorUnitValueSection (I := I) (M := M) g₀ T)
          (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ T)
          (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
          (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1 := by
      rw [riemannPalatiniRefoldC2Family_eq_symmS_kernel (I := I) (M := M) g₀ T hδ hδZ _ _ (fun _ => rfl) s,
        hsymmT, smul_smul]
      rfl
    rw [hfam, appCc_add_left, appCc_smul_left, appCc_smul_left]
    suffices hfold : (1 / 2 : ℝ) •
        (operatorFieldApply (I := I) (M := M) g₀ 2 2
            (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T 0 hδ hδZ s)) T
          - operatorFieldApply (I := I) (M := M) g₀ 2 2
              (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) T) =
        operatorFieldApply (I := I) (M := M) g₀ 2 2
            (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T 0 hδ hδZ s)
              + ((ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀
                    (realizedFam (I := I) g₀ T 0 hδ hδZ s)
                  - ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₀)
                  + (1 / 2 : ℝ) • ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀
                      (realizedFam (I := I) g₀ T 0 hδ hδZ s) (s • T)
                  - ricciArmRicciFoldRemainderField (I := I) (M := M) g₀
                      (realizedFam (I := I) g₀ T 0 hδ hδZ s) (s • T))) T
          + operatorFieldApply (I := I) (M := M) g₀ 4 2
              (curvatureActionKernelCoeffField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T 0 hδ hδZ s)
                (ccTensorUnitValueSection (I := I) (M := M) g₀ T)
                (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ T)
                (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
                (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1)
              (iteratedCovGrad (I := I) g₀ 0 2 2 (s • T)) by
      have h2 : operatorFieldApply (I := I) (M := M) g₀ 2 2
            (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T 0 hδ hδZ s)) T
          - operatorFieldApply (I := I) (M := M) g₀ 2 2
              (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) T =
          (2 : ℝ) • ((1 / 2 : ℝ) •
            (operatorFieldApply (I := I) (M := M) g₀ 2 2
                (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ s)) T
              - operatorFieldApply (I := I) (M := M) g₀ 2 2
                  (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) T)) := by
        rw [smul_smul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_smul]
      rw [hfold, iteratedCovGrad_smul_real, appCc_smul_right, smul_add, smul_smul] at h2
      rw [sub_eq_iff_eq_add] at h2
      rw [h2]
      abel
    have hprim :=
      ricciArmOrder0RiemannHalfBackgroundDifference_appCc_eq_residualFieldSum_add_refoldKernelSecondGradient
        (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s) (s • T) htie hPsymm T
    rw [appCc_add_left, appCc_sub_left, appCc_add_left,
      coeffOpApply_slotSwapField_eq_apply_of_symm (I := I) (M := M) g₀ _ T hTsymm] at hprim
    rw [appCc_add_left, appCc_sub_left, appCc_add_left]
    exact hprim
  · intro s hs x
    have hQ : riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
        ((ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ s)).toSection x) ≤ ΛQ :=
      hcapQ T hδ_le hδ hδZ hball s hs x
    have hB := hcapB T 0 hδ_le hδ hδ_le hδZ hball hZball s hs x
    have hS := hcapS T hδ_le hδ hδZ hball s hs x
    have hF := hcapF T hδ_le hδ hδZ hball s hs x
    have hRm := hKRm x
    have hB0 := hKB0 x
    beta_reduce
    rw [Real.sq_sqrt hΛSQ_nn]
    rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply,
      SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply]
    have houter := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 2 x
      ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀).toSection x)
      ((2 : ℝ) • ((ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ s)
        + ((ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T 0 hδ hδZ s)
            - ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₀)
            + (1 / 2 : ℝ) • ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T 0 hδ hδZ s) (s • T)
            - ricciArmRicciFoldRemainderField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T 0 hδ hδZ s) (s • T))).toSection x))
    have hsm : riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
        ((2 : ℝ) • ((ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T 0 hδ hδZ s)
          + ((ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T 0 hδ hδZ s)
              - ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₀)
              + (1 / 2 : ℝ) • ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ s) (s • T)
              - ricciArmRicciFoldRemainderField (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ s) (s • T))).toSection x)) =
        4 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
          ((ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T 0 hδ hδZ s)
          + ((ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T 0 hδ hδZ s)
              - ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₀)
              + (1 / 2 : ℝ) • ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ s) (s • T)
              - ricciArmRicciFoldRemainderField (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ s) (s • T))).toSection x) := by
      rw [riemannianFiberNormSq_smul (I := I) (M := M) g₀ 2 2 x]
      norm_num
    have hX : riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
        ((ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T 0 hδ hδZ s)
          + ((ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T 0 hδ hδZ s)
              - ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₀)
              + (1 / 2 : ℝ) • ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ s) (s • T)
              - ricciArmRicciFoldRemainderField (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ s) (s • T))).toSection x) ≤
        2 * ΛQ + 2 * (2 * (2 * (2 * ΛB + 2 * KB0) + 2 * ΛS) + 2 * ΛF) := by
      rw [show ((ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T 0 hδ hδZ s)
          + ((ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T 0 hδ hδZ s)
              - ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₀)
              + (1 / 2 : ℝ) • ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ s) (s • T)
              - ricciArmRicciFoldRemainderField (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ s) (s • T))).toSection x) =
          (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T 0 hδ hδZ s)).toSection x
          + ((((ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T 0 hδ hδZ s)).toSection x
              - (ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₀).toSection x)
              + (1 / 2 : ℝ) • (ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ s) (s • T)).toSection x)
            - (ricciArmRicciFoldRemainderField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T 0 hδ hδZ s) (s • T)).toSection x) from by
        simp only [SmoothCcTensor.toSection_add, SmoothCcTensor.toSection_sub,
          SmoothCcTensor.toSection_smul, ContMDiffSection.coe_add, ContMDiffSection.coe_sub,
          ContMDiffSection.coe_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply]]
      have h1 := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 2 x
        ((ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ s)).toSection x)
        (((((ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T 0 hδ hδZ s)).toSection x
            - (ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₀).toSection x)
            + (1 / 2 : ℝ) • (ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T 0 hδ hδZ s) (s • T)).toSection x)
          - (ricciArmRicciFoldRemainderField (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T 0 hδ hδZ s) (s • T)).toSection x))
      have h2 := riemannianFiberNormSq_sub_le (I := I) (M := M) g₀ 2 2 x
        ((((ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T 0 hδ hδZ s)).toSection x
            - (ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₀).toSection x)
            + (1 / 2 : ℝ) • (ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T 0 hδ hδZ s) (s • T)).toSection x))
        ((ricciArmRicciFoldRemainderField (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T 0 hδ hδZ s) (s • T)).toSection x)
      have h3 := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 2 x
        (((ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T 0 hδ hδZ s)).toSection x
          - (ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₀).toSection x))
        ((1 / 2 : ℝ) • (ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T 0 hδ hδZ s) (s • T)).toSection x)
      have h4 := riemannianFiberNormSq_sub_le (I := I) (M := M) g₀ 2 2 x
        ((ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ s)).toSection x)
        ((ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₀).toSection x)
      have h5 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
          ((1 / 2 : ℝ) • (ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T 0 hδ hδZ s) (s • T)).toSection x) =
          (1 / 4 : ℝ) * riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
            ((ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T 0 hδ hδZ s) (s • T)).toSection x) := by
        rw [riemannianFiberNormSq_smul (I := I) (M := M) g₀ 2 2 x]
        norm_num
      have h6 : (0 : ℝ) ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
          ((ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T 0 hδ hδZ s) (s • T)).toSection x) :=
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 2 x _
      linarith [hQ, hB, hS, hF, hB0, h1, h2, h3, h4, h5, h6, hΛS_nn]
    linarith [houter, hsm, hRm, hX]
  · intro i s hs
    have hQ := hwinQ T hδ_le hδ hδZ hball i s hs
    have hD := hwinB T hδ_le hδ hδZ hball i s hs
    have hS := hwinS T hδ_le hδ hδZ hball i s hs
    have hF := hwinF T hδ_le hδ hδZ hball i s hs
    beta_reduce
    rw [iteratedCovGrad_add, iteratedCovGrad_smul_real, iteratedCovGrad_add,
      iteratedCovGrad_sub, iteratedCovGrad_add, iteratedCovGrad_smul_real]
    set jc := iteratedCovGrad (I := I) g₀ 2 2 i
      (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) with hjc_def
    set jq := iteratedCovGrad (I := I) g₀ 2 2 i
      (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T 0 hδ hδZ s)) with hjq_def
    set jd := iteratedCovGrad (I := I) g₀ 2 2 i
      (ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ s)
        - ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₀) with hjd_def
    set js := iteratedCovGrad (I := I) g₀ 2 2 i
      (ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T 0 hδ hδZ s) (s • T)) with hjs_def
    set jr := iteratedCovGrad (I := I) g₀ 2 2 i
      (ricciArmRicciFoldRemainderField (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T 0 hδ hδZ s) (s • T)) with hjr_def
    have t1 := norm_add_sq_le_local (I := I) (M := M) g₀ jc
      ((2 : ℝ) • (jq + ((jd + (1 / 2 : ℝ) • js) - jr)))
    have t2 : ‖(2 : ℝ) • (jq + ((jd + (1 / 2 : ℝ) • js) - jr))‖ ^ 2 =
        4 * ‖jq + ((jd + (1 / 2 : ℝ) • js) - jr)‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      ring
    have t3 := norm_add_sq_le_local (I := I) (M := M) g₀ jq ((jd + (1 / 2 : ℝ) • js) - jr)
    have t4 : ‖(jd + (1 / 2 : ℝ) • js) - jr‖ ^ 2 ≤
        2 * ‖jd + (1 / 2 : ℝ) • js‖ ^ 2 + 2 * ‖jr‖ ^ 2 := by
      have h := norm_add_sq_le_local (I := I) (M := M) g₀ (jd + (1 / 2 : ℝ) • js) (-jr)
      rw [← sub_eq_add_neg, norm_neg] at h
      exact h
    have t5 := norm_add_sq_le_local (I := I) (M := M) g₀ jd ((1 / 2 : ℝ) • js)
    have t6 : ‖(1 / 2 : ℝ) • js‖ ^ 2 = (1 / 4) * ‖js‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      ring
    have hjs_nn : (0 : ℝ) ≤ ‖js‖ ^ 2 := sq_nonneg _
    have hW1 : (1 : ℝ) ≤ 1 + ∑ j ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 := by
      have hsum : (0 : ℝ) ≤ ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 :=
        Finset.sum_nonneg (fun j _ => sq_nonneg _)
      linarith
    have hcW : ‖jc‖ ^ 2 ≤ ‖jc‖ ^ 2 * (1 + ∑ j ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2) :=
      le_mul_of_one_le_right (sq_nonneg _) hW1
    linarith [t1, t2, t3, t4, t5, t6, hjs_nn, hQ, hD, hS, hF, hcW]


omit [BoundarylessManifold I M] in
theorem riemannPalatiniRefoldC2Family_riemannianFiberNormSq_le
    (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_half : δ ≤ 1 / 2)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ)
    (qA qB : Fin 4 → Equiv.Perm (Fin 4))
    (hq : IsFramePairPartner qA qB) :
    ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
        (((2 : ℝ) • riemannPalatiniRefoldC2Family (I := I) (M := M) g₀ T hδ hδZ qA qB
          s).toSection x) ≤
      (max (8 * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ))) 0) ^ 2 := by
  classical
  intro s hs x
  have h1mδ : (0 : ℝ) < 1 - δ := by linarith
  obtain ⟨nx, ex, hnx, horthx, hparsx, hexpx, hrfnsx⟩ :=
    tangent_frame_expansion (I := I) (M := M) g₀ x
  have hnx_pos : 0 < nx := by
    have h0 : Module.finrank ℝ E ≠ 0 := NeZero.ne _
    rw [hnx]
    exact Nat.pos_of_ne_zero h0
  have hδ0 : (0 : ℝ) ≤ δ := by
    have h := hδZ x (ex ⟨0, hnx_pos⟩) (ex ⟨0, hnx_pos⟩)
    have hunit : g₀.inner x (ex ⟨0, hnx_pos⟩) (ex ⟨0, hnx_pos⟩) = 1 := by
      rw [horthx ⟨0, hnx_pos⟩ ⟨0, hnx_pos⟩]
      simp
    rw [hunit, Real.sqrt_one, mul_one, mul_one] at h
    exact le_trans (abs_nonneg _) h
  have hs_mem : s ∈ realizedSmallSet (δ := δ) (δ' := δ) :=
    Icc_subset_realizedSmallSet hδ_lt hδ_lt hs
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      (realizedFam (I := I) g₀ T 0 hδ hδZ s).inner y v w =
        g₀.inner y v w +
          ccTensorBilinSymm (I := I) g₀
            (convexPerturbation (I := I) g₀ T 0 s) y v w :=
    fun y v w => realizedFam_inner_of_mem (I := I) g₀ T 0 hδ hδZ hs_mem y v w
  obtain ⟨hs0, hs1⟩ := hs
  have hδP : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T 0 s)) δ := by
    intro y v w
    have hraw := convexPerturbation_gFibreOpBound_abs (I := I) g₀ T 0 hδ hδZ s y v w
    have heq : |1 - s| * δ + |s| * δ = δ := by
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - s), abs_of_nonneg hs0]
      ring
    rwa [heq] at hraw
  have hmono_cap : ∀ σp : Equiv.Perm (Fin 4),
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
          ((curvatureActionMonomialCoeffField (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T 0 hδ hδZ s)
            (ccTensorUnitValueSection (I := I) (M := M) g₀
              (ccTensor02Symm (I := I) (M := M) g₀ T))
            (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀
              (ccTensor02Symm (I := I) (M := M) g₀ T)) σp).toSection x) ≤
        (deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ) ^ 2)) ^ 2 := by
    intro σp
    rw [curvatureRefoldMonomialCoeffField_toSection]
    exact riemannianFiberNormSq_curvatureRefoldMonomialBiContrFib_le (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s)
      (convexPerturbation (I := I) g₀ T 0 s) htie hδ_lt hδP
      (ccTensorUnitValueSection (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ T))
      hδ0 (toModel_unitValue_symmS_abs_le (I := I) (M := M) g₀ T hδ) σp x
  rw [riemannPalatiniRefoldC2Family_eq_symmS_kernel (I := I) (M := M) g₀ T hδ hδZ
    qA qB hq s]
  rw [smul_smul, SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
    riemannianFiberNormSq_smul (I := I) (M := M) g₀ 4 2 x]
  rw [curvatureActionKernelCoeffField, SmoothCcTensor.toSection_smul,
    SmoothCcTensor.toSection_sub, SmoothCcTensor.toSection_sub, SmoothCcTensor.toSection_add,
    ContMDiffSection.coe_smul, Pi.smul_apply, ContMDiffSection.coe_sub, Pi.sub_apply,
    ContMDiffSection.coe_sub, Pi.sub_apply, ContMDiffSection.coe_add, Pi.add_apply,
    riemannianFiberNormSq_smul (I := I) (M := M) g₀ 4 2 x]
  have hB := riemannianFiberNormSq_addsub4_le (I := I) (M := M) g₀ 4 2 x
    ((curvatureActionMonomialCoeffField (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s)
      (ccTensorUnitValueSection (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ T))
      (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀
        (ccTensor02Symm (I := I) (M := M) g₀ T)) (qA 0)).toSection x)
    ((curvatureActionMonomialCoeffField (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s)
      (ccTensorUnitValueSection (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ T))
      (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀
        (ccTensor02Symm (I := I) (M := M) g₀ T)) (qA 1)).toSection x)
    ((curvatureActionMonomialCoeffField (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s)
      (ccTensorUnitValueSection (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ T))
      (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀
        (ccTensor02Symm (I := I) (M := M) g₀ T)) (qA 2)).toSection x)
    ((curvatureActionMonomialCoeffField (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s)
      (ccTensorUnitValueSection (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ T))
      (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀
        (ccTensor02Symm (I := I) (M := M) g₀ T)) (qA 3)).toSection x)
  have hc0 := hmono_cap (qA 0)
  have hc1 := hmono_cap (qA 1)
  have hc2 := hmono_cap (qA 2)
  have hc3 := hmono_cap (qA 3)
  set fC : ℝ := deTurckArmFibreConst (Module.finrank ℝ E) with hfC_def
  have hfC_nn : (0 : ℝ) ≤ fC := deTurckArmFibreConst_nonneg _
  have hr1_nn : (0 : ℝ) ≤ δ / (1 - δ) := div_nonneg hδ0 (le_of_lt h1mδ)
  have hrate : δ / (1 - δ) ^ 2 ≤ 2 * (δ / (1 - δ)) := by
    rw [div_le_iff₀ (by positivity)]
    have hexp : 2 * (δ / (1 - δ)) * (1 - δ) ^ 2 = 2 * δ * (1 - δ) := by
      field_simp
    rw [hexp]
    nlinarith [mul_nonneg hδ0 (by linarith : (0 : ℝ) ≤ 1 - 2 * δ)]
  have hstep : 16 * (fC * (δ / (1 - δ) ^ 2)) ^ 2 ≤
      (8 * fC * (δ / (1 - δ))) ^ 2 := by
    have hfr2_nn : (0 : ℝ) ≤ fC * (δ / (1 - δ) ^ 2) :=
      mul_nonneg hfC_nn (div_nonneg hδ0 (sq_nonneg _))
    have hle : fC * (δ / (1 - δ) ^ 2) ≤ fC * (2 * (δ / (1 - δ))) :=
      mul_le_mul_of_nonneg_left hrate hfC_nn
    have hsq := pow_le_pow_left₀ hfr2_nn hle 2
    nlinarith [hsq]
  have hmax : max (8 * fC * (δ / (1 - δ))) 0 = 8 * fC * (δ / (1 - δ)) :=
    max_eq_left (mul_nonneg (mul_nonneg (by norm_num) hfC_nn) hr1_nn)
  rw [hmax]
  have hs2 : s ^ 2 ≤ 1 := by nlinarith [hs0, hs1]
  have hsum_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 4 2 x
    ((curvatureActionMonomialCoeffField (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s)
      (ccTensorUnitValueSection (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ T))
      (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀
        (ccTensor02Symm (I := I) (M := M) g₀ T)) (qA 0)).toSection x
    + (curvatureActionMonomialCoeffField (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s)
      (ccTensorUnitValueSection (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ T))
      (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀
        (ccTensor02Symm (I := I) (M := M) g₀ T)) (qA 1)).toSection x
    - (curvatureActionMonomialCoeffField (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s)
      (ccTensorUnitValueSection (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ T))
      (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀
        (ccTensor02Symm (I := I) (M := M) g₀ T)) (qA 2)).toSection x
    - (curvatureActionMonomialCoeffField (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s)
      (ccTensorUnitValueSection (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ T))
      (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀
        (ccTensor02Symm (I := I) (M := M) g₀ T)) (qA 3)).toSection x)
  nlinarith [hB, hc0, hc1, hc2, hc3, hs2, hsum_nn, hstep, hs0, hs1,
    sq_nonneg (fC * (δ / (1 - δ) ^ 2)),
    mul_nonneg (mul_nonneg hδ0 hδ0) (sq_nonneg (fC * (δ / (1 - δ) ^ 2)))]


theorem exists_riemannPalatiniRefoldC2Family_l2JetWindow
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) (qA qB : Fin 4 → Equiv.Perm (Fin 4))
    (hq : IsFramePairPartner qA qB) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (T : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ_half : δ ≤ 1 / 2)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
            (((2 : ℝ) • riemannPalatiniRefoldC2Family (I := I) (M := M) g₀ T hδ hδZ qA qB
              s).toSection x) ≤
          (max (8 * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ))) 0) ^ 2) ∧
        (∀ i : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) 1,
          ‖iteratedCovGrad (I := I) g₀ 4 2 i
            ((2 : ℝ) • riemannPalatiniRefoldC2Family (I := I) (M := M) g₀ T hδ hδZ qA qB
              s)‖ ^ 2 ≤
            K i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2)) := by
  classical
  obtain ⟨K0, hK0_nn, hK0⟩ :=
    exists_curvatureRefoldMonomialCoeffField_symmS_realizedFam_l2JetWindow (I := I) (M := M)
      g₀ a ha_super hR hδ₀ (qA 0)
  obtain ⟨K1, hK1_nn, hK1⟩ :=
    exists_curvatureRefoldMonomialCoeffField_symmS_realizedFam_l2JetWindow (I := I) (M := M)
      g₀ a ha_super hR hδ₀ (qA 1)
  obtain ⟨K2, hK2_nn, hK2⟩ :=
    exists_curvatureRefoldMonomialCoeffField_symmS_realizedFam_l2JetWindow (I := I) (M := M)
      g₀ a ha_super hR hδ₀ (qA 2)
  obtain ⟨K3, hK3_nn, hK3⟩ :=
    exists_curvatureRefoldMonomialCoeffField_symmS_realizedFam_l2JetWindow (I := I) (M := M)
      g₀ a ha_super hR hδ₀ (qA 3)
  refine ⟨fun i => 4 * (K0 i + K1 i + K2 i + K3 i), fun i => by
    have h0 := hK0_nn i; have h1 := hK1_nn i; have h2 := hK2_nn i; have h3 := hK3_nn i
    linarith, ?_⟩
  intro T δ hδ_le hδ_half hδ hδZ hball
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  refine ⟨riemannPalatiniRefoldC2Family_riemannianFiberNormSq_le (I := I) (M := M) g₀ T hδ_lt hδ_half hδ hδZ
    qA qB hq, ?_⟩
  intro i s hs
  obtain ⟨hs0, hs1⟩ := hs
  rw [riemannPalatiniRefoldC2Family_eq_symmS_kernel (I := I) (M := M) g₀ T hδ hδZ
    qA qB hq s]
  rw [curvatureActionKernelCoeffField, iteratedCovGrad_smul_real,
    iteratedCovGrad_smul_real, iteratedCovGrad_smul_real,
    iteratedCovGrad_sub, iteratedCovGrad_sub, iteratedCovGrad_add]
  set G0 := iteratedCovGrad (I := I) g₀ 4 2 i
    (curvatureActionMonomialCoeffField (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s)
      (ccTensorUnitValueSection (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ T))
      (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀
        (ccTensor02Symm (I := I) (M := M) g₀ T)) (qA 0)) with hG0_def
  set G1 := iteratedCovGrad (I := I) g₀ 4 2 i
    (curvatureActionMonomialCoeffField (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s)
      (ccTensorUnitValueSection (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ T))
      (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀
        (ccTensor02Symm (I := I) (M := M) g₀ T)) (qA 1)) with hG1_def
  set G2 := iteratedCovGrad (I := I) g₀ 4 2 i
    (curvatureActionMonomialCoeffField (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s)
      (ccTensorUnitValueSection (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ T))
      (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀
        (ccTensor02Symm (I := I) (M := M) g₀ T)) (qA 2)) with hG2_def
  set G3 := iteratedCovGrad (I := I) g₀ 4 2 i
    (curvatureActionMonomialCoeffField (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s)
      (ccTensorUnitValueSection (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ T))
      (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀
        (ccTensor02Symm (I := I) (M := M) g₀ T)) (qA 3)) with hG3_def
  have hcol : (2 : ℝ) • s • (1 / 2 : ℝ) • (G0 + G1 - G2 - G3) =
      s • (G0 + G1 - G2 - G3) := by
    rw [smul_smul, smul_smul]
    have h2s : (2 : ℝ) * s * (1 / 2) = s := by ring
    rw [h2s]
  rw [hcol]
  have hG0w := hK0 T hδ_le hδ hδZ hball i s ⟨hs0, hs1⟩
  have hG1w := hK1 T hδ_le hδ hδZ hball i s ⟨hs0, hs1⟩
  have hG2w := hK2 T hδ_le hδ hδZ hball i s ⟨hs0, hs1⟩
  have hG3w := hK3 T hδ_le hδ hδZ hball i s ⟨hs0, hs1⟩
  rw [← hG0_def] at hG0w
  rw [← hG1_def] at hG1w
  rw [← hG2_def] at hG2w
  rw [← hG3_def] at hG3w
  have hnorm1 : ‖s • (G0 + G1 - G2 - G3)‖ ≤ ‖G0‖ + ‖G1‖ + ‖G2‖ + ‖G3‖ := by
    have hs_abs : |s| ≤ 1 := by
      rw [abs_of_nonneg hs0]
      exact hs1
    have hsm : ‖s • (G0 + G1 - G2 - G3)‖ ≤ ‖G0 + G1 - G2 - G3‖ := by
      rw [norm_smul]
      refine mul_le_of_le_one_left (norm_nonneg _) ?_
      rw [Real.norm_eq_abs]
      exact hs_abs
    refine le_trans hsm ?_
    calc ‖G0 + G1 - G2 - G3‖ ≤ ‖G0 + G1 - G2‖ + ‖G3‖ := norm_sub_le _ _
      _ ≤ ‖G0 + G1‖ + ‖G2‖ + ‖G3‖ := by
          have h := norm_sub_le (G0 + G1) G2
          linarith
      _ ≤ ‖G0‖ + ‖G1‖ + ‖G2‖ + ‖G3‖ := by
          have h := norm_add_le G0 G1
          linarith
  have hsq : ‖s • (G0 + G1 - G2 - G3)‖ ^ 2 ≤ (‖G0‖ + ‖G1‖ + ‖G2‖ + ‖G3‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hnorm1 2
  have hcauchy : (‖G0‖ + ‖G1‖ + ‖G2‖ + ‖G3‖) ^ 2 ≤
      4 * (‖G0‖ ^ 2 + ‖G1‖ ^ 2 + ‖G2‖ ^ 2 + ‖G3‖ ^ 2) := by
    nlinarith [sq_nonneg (‖G0‖ - ‖G1‖), sq_nonneg (‖G0‖ - ‖G2‖), sq_nonneg (‖G0‖ - ‖G3‖),
      sq_nonneg (‖G1‖ - ‖G2‖), sq_nonneg (‖G1‖ - ‖G3‖), sq_nonneg (‖G2‖ - ‖G3‖)]
  refine le_trans hsq (le_trans hcauchy ?_)
  have hexp : 4 * (K0 i + K1 i + K2 i + K3 i) *
      (1 + ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2) =
      4 * (K0 i * (1 + ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2)
        + K1 i * (1 + ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2)
        + K2 i * (1 + ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2)
        + K3 i * (1 + ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2)) := by ring
  rw [hexp]
  linarith [hG0w, hG1w, hG2w, hG3w]


theorem exists_deTurckLieCovDerivRefoldC2Family_cap_l2JetWindow
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) (q : Fin 3 → Equiv.Perm (Fin 4)) (ε : Fin 3 → ℝ)
    (hε : ∀ i, |ε i| ≤ 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (T : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 4
          (deTurckLieCovDerivRefoldC2Family (I := I) (M := M) g₀ T hδ hδZ q ε)
          (δ := δ) (δ' := δ) ∧
        (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
            ((deTurckLieCovDerivRefoldC2Family (I := I) (M := M) g₀ T hδ hδZ q ε
              s).toSection x) ≤
          (max (3 * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ) ^ 2)) 0) ^ 2) ∧
        (∀ i : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) 1,
          ‖iteratedCovGrad (I := I) g₀ 4 2 i
            (deTurckLieCovDerivRefoldC2Family (I := I) (M := M) g₀ T hδ hδZ q ε s)‖ ^ 2 ≤
            K i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2)) := by
  classical
  obtain ⟨K0, hK0_nn, hK0⟩ :=
    exists_curvatureRefoldMonomialCoeffField_symmS_realizedFam_l2JetWindow (I := I) (M := M)
      g₀ a ha_super hR hδ₀ (q 0)
  obtain ⟨K1, hK1_nn, hK1⟩ :=
    exists_curvatureRefoldMonomialCoeffField_symmS_realizedFam_l2JetWindow (I := I) (M := M)
      g₀ a ha_super hR hδ₀ (q 1)
  obtain ⟨K2, hK2_nn, hK2⟩ :=
    exists_curvatureRefoldMonomialCoeffField_symmS_realizedFam_l2JetWindow (I := I) (M := M)
      g₀ a ha_super hR hδ₀ (q 2)
  refine ⟨fun i => 3 * (K0 i + K1 i + K2 i),
    fun i => by have h0 := hK0_nn i; have h1 := hK1_nn i; have h2 := hK2_nn i; linarith, ?_⟩
  intro T δ hδ_le hδ hδZ hball
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have h1mδ : (0 : ℝ) < 1 - δ := by linarith
  refine ⟨?_, ?_, ?_⟩
  · have hmono : ∀ σp : Equiv.Perm (Fin 4),
        ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 4 2 ℝ E)) ∞
          (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
            (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) p.1
            ((curvatureActionMonomialCoeffField (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T 0 hδ hδZ p.2)
              (ccTensorUnitValueSection (I := I) (M := M) g₀ T)
              (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ T) σp).toSection p.1))
          ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ)) :=
      fun σp => curvatureRefoldMonomialCoeffField_realizedFam_jointContMDiffOn
        (I := I) (M := M) g₀ T hδ hδZ
        (ccTensorUnitValueSection (I := I) (M := M) g₀ T)
        (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ T) σp
    have hpair : ∀ i : Fin 3,
        ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 4 2 ℝ E)) ∞
          (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
            (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) p.1
            (ε i • ((1 / 2 : ℝ) •
              ((curvatureActionMonomialCoeffField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T 0 hδ hδZ p.2)
                (ccTensorUnitValueSection (I := I) (M := M) g₀ T)
                (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ T)
                (q i)).toSection p.1
              + (curvatureActionMonomialCoeffField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T 0 hδ hδZ p.2)
                (ccTensorUnitValueSection (I := I) (M := M) g₀ T)
                (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ T)
                ((q i).trans (Equiv.swap (0 : Fin 4) 1))).toSection p.1))))
          ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ)) := by
      intro i
      have hadd := jointTotalSpaceRS_add_local (I := I) (M := M) (r := 4) (s := 2)
        (S := realizedSmallSet (δ := δ) (δ' := δ)) _ _ (hmono (q i))
        (hmono ((q i).trans (Equiv.swap (0 : Fin 4) 1)))
      have hhalf := jointTotalSpaceRS_const_smul_local (I := I) (M := M) (r := 4) (s := 2)
        (S := realizedSmallSet (δ := δ) (δ' := δ)) (1 / 2 : ℝ) _ hadd
      exact jointTotalSpaceRS_const_smul_local (I := I) (M := M) (r := 4) (s := 2)
        (S := realizedSmallSet (δ := δ) (δ' := δ)) (ε i) _ hhalf
    have hsum01 := jointTotalSpaceRS_add_local (I := I) (M := M) (r := 4) (s := 2)
      (S := realizedSmallSet (δ := δ) (δ' := δ)) _ _ (hpair 0) (hpair 1)
    have hsum := jointTotalSpaceRS_add_local (I := I) (M := M) (r := 4) (s := 2)
      (S := realizedSmallSet (δ := δ) (δ' := δ)) _ _ hsum01 (hpair 2)
    have hfam := jointTotalSpaceRS_smulFun_local (I := I) (M := M) (r := 4) (s := 2)
      (S := realizedSmallSet (δ := δ) (δ' := δ)) (f := fun t => t) contDiff_id _ hsum
    refine hfam.congr (fun p _ => ?_)
    refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
      (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) p.1 t) ?_
    rw [deTurckLieCovDerivRefoldC2Family]
    simp only [Fin.sum_univ_three, SmoothCcTensor.toSection_smul,
      SmoothCcTensor.toSection_add, ContMDiffSection.coe_smul, ContMDiffSection.coe_add,
      Pi.smul_apply, Pi.add_apply]
  · intro s hs x
    obtain ⟨nx, ex, hnx, horthx, hparsx, hexpx, hrfnsx⟩ :=
      tangent_frame_expansion (I := I) (M := M) g₀ x
    have hnx_pos : 0 < nx := by
      have h0 : Module.finrank ℝ E ≠ 0 := NeZero.ne _
      rw [hnx]
      exact Nat.pos_of_ne_zero h0
    have hδ0 : (0 : ℝ) ≤ δ := by
      have h := hδZ x (ex ⟨0, hnx_pos⟩) (ex ⟨0, hnx_pos⟩)
      have hunit : g₀.inner x (ex ⟨0, hnx_pos⟩) (ex ⟨0, hnx_pos⟩) = 1 := by
        rw [horthx ⟨0, hnx_pos⟩ ⟨0, hnx_pos⟩]
        simp
      rw [hunit, Real.sqrt_one, mul_one, mul_one] at h
      exact le_trans (abs_nonneg _) h
    have hs_mem : s ∈ realizedSmallSet (δ := δ) (δ' := δ) :=
      Icc_subset_realizedSmallSet hδ_lt hδ_lt hs
    have htie : ∀ (y : M) (v w : TangentSpace I y),
        (realizedFam (I := I) g₀ T 0 hδ hδZ s).inner y v w =
          g₀.inner y v w +
            ccTensorBilinSymm (I := I) g₀
              (convexPerturbation (I := I) g₀ T 0 s) y v w :=
      fun y v w => realizedFam_inner_of_mem (I := I) g₀ T 0 hδ hδZ hs_mem y v w
    obtain ⟨hs0, hs1⟩ := hs
    have hδP : metricCauchySchwarzBound (I := I) (M := M) g₀
        (ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T 0 s)) δ := by
      intro y v w
      have hraw := convexPerturbation_gFibreOpBound_abs (I := I) g₀ T 0 hδ hδZ s y v w
      have heq : |1 - s| * δ + |s| * δ = δ := by
        rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - s), abs_of_nonneg hs0]
        ring
      rwa [heq] at hraw
    have hmono_cap : ∀ σp : Equiv.Perm (Fin 4),
        riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
            ((curvatureActionMonomialCoeffField (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T 0 hδ hδZ s)
              (ccTensorUnitValueSection (I := I) (M := M) g₀
                (ccTensor02Symm (I := I) (M := M) g₀ T))
              (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀
                (ccTensor02Symm (I := I) (M := M) g₀ T)) σp).toSection x) ≤
          (deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ) ^ 2)) ^ 2 := by
      intro σp
      rw [curvatureRefoldMonomialCoeffField_toSection]
      exact riemannianFiberNormSq_curvatureRefoldMonomialBiContrFib_le (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T 0 hδ hδZ s)
        (convexPerturbation (I := I) g₀ T 0 s) htie hδ_lt hδP
        (ccTensorUnitValueSection (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ T))
        hδ0 (toModel_unitValue_symmS_abs_le (I := I) (M := M) g₀ T hδ) σp x
    have hterm_le : ∀ (c : ℝ), |c| ≤ 1 → ∀ σp : Equiv.Perm (Fin 4),
        riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
            (c • ((curvatureActionMonomialCoeffField (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T 0 hδ hδZ s)
              (ccTensorUnitValueSection (I := I) (M := M) g₀
                (ccTensor02Symm (I := I) (M := M) g₀ T))
              (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀
                (ccTensor02Symm (I := I) (M := M) g₀ T)) σp).toSection x)) ≤
          (deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ) ^ 2)) ^ 2 := by
      intro c hc σp
      rw [riemannianFiberNormSq_smul (I := I) (M := M) g₀ 4 2 x]
      have h1 := hmono_cap σp
      have hc2 : c ^ 2 ≤ 1 := by nlinarith [abs_nonneg c, sq_abs c, hc]
      have h0 := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 4 2 x
        ((curvatureActionMonomialCoeffField (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ s)
          (ccTensorUnitValueSection (I := I) (M := M) g₀
            (ccTensor02Symm (I := I) (M := M) g₀ T))
          (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀
            (ccTensor02Symm (I := I) (M := M) g₀ T)) σp).toSection x)
      nlinarith [h1, hc2, h0, sq_nonneg c]
    rw [deTurckLieCovDerivRefoldC2Family_eq_symmS_weight (I := I) (M := M) g₀ T hδ hδZ q ε s]
    rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
      riemannianFiberNormSq_smul (I := I) (M := M) g₀ 4 2 x]
    simp only [Fin.sum_univ_three, SmoothCcTensor.toSection_add,
      SmoothCcTensor.toSection_smul, ContMDiffSection.coe_add, ContMDiffSection.coe_smul,
      Pi.add_apply, Pi.smul_apply]
    have hr0 := hterm_le (ε 0) (hε 0) (q 0)
    have hr1 := hterm_le (ε 1) (hε 1) (q 1)
    have hr2 := hterm_le (ε 2) (hε 2) (q 2)
    have h3 := riemannianFiberNormSq_add3_le (I := I) (M := M) g₀ 4 2 x
      (ε 0 • ((curvatureActionMonomialCoeffField (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T 0 hδ hδZ s)
        (ccTensorUnitValueSection (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ T))
        (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀
          (ccTensor02Symm (I := I) (M := M) g₀ T)) (q 0)).toSection x))
      (ε 1 • ((curvatureActionMonomialCoeffField (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T 0 hδ hδZ s)
        (ccTensorUnitValueSection (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ T))
        (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀
          (ccTensor02Symm (I := I) (M := M) g₀ T)) (q 1)).toSection x))
      (ε 2 • ((curvatureActionMonomialCoeffField (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T 0 hδ hδZ s)
        (ccTensorUnitValueSection (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ T))
        (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀
          (ccTensor02Symm (I := I) (M := M) g₀ T)) (q 2)).toSection x))
    have hs2 : s ^ 2 ≤ 1 := by nlinarith [hs0, hs1]
    have hmax : max (3 * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ) ^ 2)) 0 =
        3 * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ) ^ 2) :=
      max_eq_left (mul_nonneg (mul_nonneg (by norm_num)
        (deTurckArmFibreConst_nonneg _)) (div_nonneg hδ0 (sq_nonneg _)))
    rw [hmax]
    have hsum_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 4 2 x
      (ε 0 • ((curvatureActionMonomialCoeffField (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T 0 hδ hδZ s)
        (ccTensorUnitValueSection (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ T))
        (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀
          (ccTensor02Symm (I := I) (M := M) g₀ T)) (q 0)).toSection x)
      + ε 1 • ((curvatureActionMonomialCoeffField (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T 0 hδ hδZ s)
        (ccTensorUnitValueSection (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ T))
        (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀
          (ccTensor02Symm (I := I) (M := M) g₀ T)) (q 1)).toSection x)
      + ε 2 • ((curvatureActionMonomialCoeffField (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T 0 hδ hδZ s)
        (ccTensorUnitValueSection (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ T))
        (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀
          (ccTensor02Symm (I := I) (M := M) g₀ T)) (q 2)).toSection x))
    nlinarith [hr0, hr1, hr2, h3, hs2, hsum_nn,
      sq_nonneg (deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ) ^ 2))]
  · intro i s hs
    rw [deTurckLieCovDerivRefoldC2Family_eq_symmS_weight (I := I) (M := M) g₀ T hδ hδZ q ε s,
      iteratedCovGrad_smul_real]
    simp only [Fin.sum_univ_three]
    rw [iteratedCovGrad_add, iteratedCovGrad_add, iteratedCovGrad_smul_real,
      iteratedCovGrad_smul_real, iteratedCovGrad_smul_real]
    have hG0 := hK0 T hδ_le hδ hδZ hball i s hs
    have hG1 := hK1 T hδ_le hδ hδZ hball i s hs
    have hG2 := hK2 T hδ_le hδ hδZ hball i s hs
    obtain ⟨hs0, hs1⟩ := hs
    set G0 := iteratedCovGrad (I := I) g₀ 4 2 i
      (curvatureActionMonomialCoeffField (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T 0 hδ hδZ s)
        (ccTensorUnitValueSection (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ T))
        (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀
          (ccTensor02Symm (I := I) (M := M) g₀ T)) (q 0)) with hG0_def
    set G1 := iteratedCovGrad (I := I) g₀ 4 2 i
      (curvatureActionMonomialCoeffField (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T 0 hδ hδZ s)
        (ccTensorUnitValueSection (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ T))
        (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀
          (ccTensor02Symm (I := I) (M := M) g₀ T)) (q 1)) with hG1_def
    set G2 := iteratedCovGrad (I := I) g₀ 4 2 i
      (curvatureActionMonomialCoeffField (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T 0 hδ hδZ s)
        (ccTensorUnitValueSection (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ T))
        (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀
          (ccTensor02Symm (I := I) (M := M) g₀ T)) (q 2)) with hG2_def
    have hnorm1 : ‖s • (ε 0 • G0 + ε 1 • G1 + ε 2 • G2)‖ ≤ ‖G0‖ + ‖G1‖ + ‖G2‖ := by
      have hsm : ∀ (c : ℝ), |c| ≤ 1 → ∀ (G : SmoothCcTensor g₀ 4 (2 + i)),
          ‖c • G‖ ≤ ‖G‖ := by
        intro c hc G
        rw [norm_smul]
        refine mul_le_of_le_one_left (norm_nonneg _) ?_
        rw [Real.norm_eq_abs]
        exact hc
      have hs_abs : |s| ≤ 1 := by
        rw [abs_of_nonneg hs0]
        exact hs1
      refine le_trans (hsm s hs_abs _) ?_
      refine le_trans (norm_add_le _ _) ?_
      have h01 : ‖ε 0 • G0 + ε 1 • G1‖ ≤ ‖G0‖ + ‖G1‖ := by
        refine le_trans (norm_add_le _ _) ?_
        exact add_le_add (hsm (ε 0) (hε 0) G0) (hsm (ε 1) (hε 1) G1)
      have h2 : ‖ε 2 • G2‖ ≤ ‖G2‖ := hsm (ε 2) (hε 2) G2
      linarith
    have hsq : ‖s • (ε 0 • G0 + ε 1 • G1 + ε 2 • G2)‖ ^ 2 ≤
        (‖G0‖ + ‖G1‖ + ‖G2‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm1 2
    have hwin_nn : (0 : ℝ) ≤ 1 + ∑ j ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 := by positivity
    refine le_trans hsq ?_
    nlinarith [hG0, hG1, hG2, sq_nonneg (‖G0‖ - ‖G1‖), sq_nonneg (‖G1‖ - ‖G2‖),
      sq_nonneg (‖G0‖ - ‖G2‖), norm_nonneg G0, norm_nonneg G1, norm_nonneg G2,
      hK0_nn i, hK1_nn i, hK2_nn i, hwin_nn]


theorem exists_deTurckLieCovDerivArm_curvatureRefold_data
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (T : SmoothCcTensor g₀ 0 2)
        (_hTsymm : ∀ (x : M) (v w : TangentSpace I x),
          smoothCcTensorBilinForm (I := I) g₀ T x v w = smoothCcTensorBilinForm (I := I) g₀ T x w v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        ∃ (C0da : ℝ → SmoothCcTensor g₀ 2 2) (C2da : ℝ → SmoothCcTensor g₀ 4 2),
          linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2 C0da (δ := δ) (δ' := δ) ∧
          linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 4 C2da (δ := δ) (δ' := δ) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1,
            operatorFieldApply (I := I) (M := M) g₀ 2 2
                (deTurckLieCovDerivArmField (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ s) g_bg)
                (iteratedCovGrad (I := I) g₀ 0 2 0 T) =
              operatorFieldApply (I := I) (M := M) g₀ 2 2 (C0da s)
                  (iteratedCovGrad (I := I) g₀ 0 2 0 T) +
                operatorFieldApply (I := I) (M := M) g₀ 4 2 (C2da s)
                  (iteratedCovGrad (I := I) g₀ 0 2 2 T)) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x ((C0da s).toSection x) ≤
              Λ ^ 2) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x ((C2da s).toSection x) ≤
              (max (3 * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ) ^ 2)) 0)
                ^ 2) ∧
          (∀ i : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) 1,
            ‖iteratedCovGrad (I := I) g₀ 2 2 i (C0da s)‖ ^ 2 ≤
              K i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2)) ∧
          (∀ i : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) 1,
            ‖iteratedCovGrad (I := I) g₀ 4 2 i (C2da s)‖ ^ 2 ≤
              K i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2)) := by
  classical
  obtain ⟨Λ, hΛ, KA, hKA, q, ε, hε, hmain⟩ :=
    exists_deTurckLieCovDerivArm_refold_identity_data (I := I) (M := M) g₀ g_bg a
      ha_super hR hδ₀
  obtain ⟨KB, hKB, hfam⟩ :=
    exists_deTurckLieCovDerivRefoldC2Family_cap_l2JetWindow (I := I) (M := M) g₀ a
      ha_super hR hδ₀ q ε hε
  refine ⟨Λ, hΛ, fun i => max (KA i) (KB i),
    fun i => le_trans (hKA i) (le_max_left _ _), ?_⟩
  intro T hTsymm δ hδ_le hδ hδZ hball
  obtain ⟨C0da, hjoint0, hid, hsup0, henv0⟩ := hmain T hTsymm hδ_le hδ hδZ hball
  obtain ⟨hjoint2, hcap2, henv2⟩ := hfam T hδ_le hδ hδZ hball
  refine ⟨C0da, deTurckLieCovDerivRefoldC2Family (I := I) (M := M) g₀ T hδ hδZ q ε,
    hjoint0, hjoint2, hid, hsup0, hcap2, ?_, ?_⟩
  · intro i s hs
    refine le_trans (henv0 i s hs) (mul_le_mul_of_nonneg_right (le_max_left _ _) ?_)
    positivity
  · intro i s hs
    refine le_trans (henv2 i s hs) (mul_le_mul_of_nonneg_right (le_max_right _ _) ?_)
    positivity


omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem deTurckVF_background_sub_eq_connDiff_trace
    (g₁ gA gB : SmoothRiemannianMetric I M) (x : M) :
    (PDE.DeTurck.deTurckVF (I := I) g₁ gA :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x -
      (PDE.DeTurck.deTurckVF (I := I) g₁ gB :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x =
      ∑ j : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x j k •
          PDE.DeTurck.connDiff (I := I) gB gA x
            (chartBasisVecFiber (I := I) x j x)
            (chartBasisVecFiber (I := I) x k x) := by
  classical
  rw [PDE.DeTurck.deTurckVF_apply_eq (I := I) g₁ gA x,
    PDE.DeTurck.deTurckVF_apply_eq (I := I) g₁ gB x,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [← smul_sub]
  congr 1
  rw [PDE.DeTurck.connDiff_cocycle (I := I) gB g₁ gA x
      (chartBasisVecFiber (I := I) x j x) (chartBasisVecFiber (I := I) x k x),
    add_sub_cancel_left]


theorem exists_deTurckLieEndoArm_backgroundDifference_perOrder_l2_tameEnvelope_generic
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ),
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (deTurckLieEndoArmField (I := I) (M := M) g₀ g₁ g_bg -
                deTurckLieEndoArmField (I := I) (M := M) g₀ g₁ g₀)‖ ^ 2 ≤
            K i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  set δ₁ : ℝ := max δ₀ 0 with hδ₁_def
  have hδ₁_lt : δ₁ < 1 := max_lt hδ₀ one_pos
  obtain ⟨C, hC_nn, hpt⟩ := bdEndoArmDiff_pointwise_gridWindow (I := I) (M := M) g₀ g_bg hδ₁_lt
  obtain ⟨Kg, hKg_nn, hKg⟩ := bdL2_tameEnvelope_of_gridWindow (I := I) (M := M) g₀ a ha_super hR
  refine ⟨fun i => C i * ∑ k ∈ Finset.range (i + 2), Kg k,
    fun i => mul_nonneg (hC_nn i) (Finset.sum_nonneg fun k _ => hKg_nn k), ?_⟩
  intro g₁ P δ hδ_le hδ htie hPball i
  have hwin_nn : (0 : ℝ) ≤ 1 + ∑ j ∈ Finset.range (i + 2),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 := by positivity
  have hsubj : deTurckLieEndoArmField (I := I) (M := M) g₀ g₁ g_bg -
      deTurckLieEndoArmField (I := I) (M := M) g₀ g₁ g₀ =
      deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g_bg -
        deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g₀ := by
    rw [endoArmField_eq_dLbCoeffField, endoArmField_eq_dLbCoeffField]
  by_cases hM : Nonempty M
  · obtain ⟨x₀⟩ := hM
    have hδ0 : 0 ≤ δ := bdDelta_nonneg (I := I) (M := M) g₀ x₀ P hδ
    have hδ_le' : δ ≤ δ₁ := le_trans hδ_le (le_max_left _ _)
    rw [hsubj]
    exact hKg P hPball i (C i) (hC_nn i)
      (deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g_bg -
        deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g₀)
      (fun x => hpt g₁ P htie hδ_le' hδ0 hδ i x)
  · haveI hM' : IsEmpty M := not_nonempty_iff.mp hM
    have hz : ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (deTurckLieEndoArmField (I := I) (M := M) g₀ g₁ g_bg -
          deTurckLieEndoArmField (I := I) (M := M) g₀ g₁ g₀)‖ = 0 :=
      bdNorm_zero_of_isEmpty (I := I) (M := M) g₀ 2 (2 + i) _
    rw [hz]
    have hK_nn : 0 ≤ C i * ∑ k ∈ Finset.range (i + 2), Kg k :=
      mul_nonneg (hC_nn i) (Finset.sum_nonneg fun k _ => hKg_nn k)
    nlinarith [hwin_nn, hK_nn]


theorem exists_deTurckLieEndoArm_backgroundDifference_l2JetWindow
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (T : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        ∀ i : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) 1,
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (deTurckLieEndoArmField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T 0 hδ hδZ s) g_bg
              - deTurckLieEndoArmField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀)‖ ^ 2 ≤
            K i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2) := by
  classical
  obtain ⟨K, hK_nn, hK⟩ :=
    exists_deTurckLieEndoArm_backgroundDifference_perOrder_l2_tameEnvelope_generic
      (I := I) (M := M) g₀ g_bg a ha_super hR hδ₀
  refine ⟨K, hK_nn, ?_⟩
  intro T δ hδ_le hδ hδZ hball i s hs
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hs_mem : s ∈ realizedSmallSet (δ := δ) (δ' := δ) :=
    Icc_subset_realizedSmallSet hδ_lt hδ_lt hs
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      (realizedFam (I := I) g₀ T 0 hδ hδZ s).inner y v w =
        g₀.inner y v w +
          ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T 0 s) y v w :=
    fun y v w => realizedFam_inner_of_mem (I := I) g₀ T 0 hδ hδZ hs_mem y v w
  obtain ⟨hs0, hs1⟩ := hs
  have habs : |s| ≤ 1 := by
    rw [abs_of_nonneg hs0]
    exact hs1
  have hδP : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T 0 s)) δ := by
    intro y v w
    have hraw := convexPerturbation_gFibreOpBound_abs (I := I) g₀ T 0 hδ hδZ s y v w
    have heq : |1 - s| * δ + |s| * δ = δ := by
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - s), abs_of_nonneg hs0]
      ring
    rwa [heq] at hraw
  have hcP : convexPerturbation (I := I) g₀ T 0 s = s • T := by
    rw [convexPerturbation, smul_zero, zero_add]
  have hPball : ∀ j : ℕ, j ≤ a + 2 →
      ‖iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T 0 s)‖ ≤ R := by
    intro j hj
    rw [hcP, iteratedCovGrad_smul_real, norm_smul, Real.norm_eq_abs]
    calc |s| * ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤
        1 * ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ :=
          mul_le_mul_of_nonneg_right habs (norm_nonneg _)
      _ = ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ := one_mul _
      _ ≤ R := hball j hj
  refine le_trans (hK (realizedFam (I := I) g₀ T 0 hδ hδZ s)
    (convexPerturbation (I := I) g₀ T 0 s) hδ_le hδP htie hPball i) ?_
  refine mul_le_mul_of_nonneg_left ?_ (hK_nn i)
  refine add_le_add le_rfl ?_
  refine Finset.sum_le_sum (fun j _ => ?_)
  rw [hcP, iteratedCovGrad_smul_real, norm_smul, Real.norm_eq_abs, mul_pow]
  have h1 : |s| ^ 2 ≤ 1 := by nlinarith [abs_nonneg s]
  nlinarith [sq_nonneg ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖, h1,
    norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 j T)]


theorem exists_deTurckLieEndoArm_backgroundDifference_order0_data
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (T : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2
          (fun s => deTurckLieEndoArmField (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T 0 hδ hδZ s) g_bg
            - deTurckLieEndoArmField (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀) (δ := δ) (δ' := δ) ∧
        (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
            ((deTurckLieEndoArmField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T 0 hδ hδZ s) g_bg
              - deTurckLieEndoArmField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀).toSection x) ≤ Λ ^ 2) ∧
        (∀ i : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) 1,
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (deTurckLieEndoArmField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T 0 hδ hδZ s) g_bg
              - deTurckLieEndoArmField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀)‖ ^ 2 ≤
            K i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2)) := by
  classical
  obtain ⟨Λbg, hΛbg_nn, hsup_bg⟩ :=
    deTurckLieDLbCoeffField_realizedFam_rfns_order0_ballUniform (I := I) (M := M)
      g₀ g_bg a ha_super hR hδ₀
  obtain ⟨Λz, hΛz_nn, hsup_z⟩ :=
    deTurckLieDLbCoeffField_realizedFam_rfns_order0_ballUniform (I := I) (M := M)
      g₀ g₀ a ha_super hR hδ₀
  obtain ⟨Ke, hKe_nn, henv⟩ :=
    exists_deTurckLieEndoArm_backgroundDifference_l2JetWindow (I := I) (M := M)
      g₀ g_bg a ha_super hR hδ₀
  have hS_nn : (0 : ℝ) ≤ 2 * Λbg + 2 * Λz := by linarith
  refine ⟨Real.sqrt (2 * Λbg + 2 * Λz), Real.sqrt_nonneg _, Ke, hKe_nn, ?_⟩
  intro T δ hδ_le hδ hδZ hball
  have hZball : ∀ j : ℕ, j ≤ a + 2 →
      ‖iteratedCovGrad (I := I) g₀ 0 2 j (0 : SmoothCcTensor g₀ 0 2)‖ ≤ R := by
    intro j hj
    have hzero : iteratedCovGrad (I := I) g₀ 0 2 j (0 : SmoothCcTensor g₀ 0 2) = 0 := by
      have h := iteratedCovGrad_sub (I := I) (g := g₀) (r := 0) (s := 2) (j := j) T T
      rw [sub_self, sub_self] at h
      exact h
    rw [hzero, norm_zero]
    exact hR
  refine ⟨?_, ?_, fun i s hs => henv T hδ_le hδ hδZ hball i s hs⟩
  · exact threeArmHjoint_sub_local (I := I) (M := M) g₀ _ _
      (endoArmField_realizedFam_threeArmHjoint (I := I) (M := M) g₀ T hδ hδZ g_bg)
      (endoArmField_realizedFam_threeArmHjoint (I := I) (M := M) g₀ T hδ hδZ g₀)
  · intro s hs x
    have h1 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
        ((deTurckLieEndoArmField (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ s) g_bg).toSection x) ≤ Λbg := by
      rw [endoArmField_eq_dLbCoeffField]
      exact hsup_bg T 0 hδ_le hδ hδ_le hδZ hball hZball s hs x
    have h2 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
        ((deTurckLieEndoArmField (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀).toSection x) ≤ Λz := by
      rw [endoArmField_eq_dLbCoeffField]
      exact hsup_z T 0 hδ_le hδ hδ_le hδZ hball hZball s hs x
    rw [Real.sq_sqrt hS_nn, SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub,
      Pi.sub_apply]
    refine le_trans (riemannianFiberNormSq_sub_le (I := I) (M := M) g₀ 2 2 x _ _) ?_
    linarith [h1, h2]


theorem covDerivConnDiff_realizedFam_zero_endpoint_eq_smul_covDerivSharp
    (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) (x : M)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    covDerivConnDiff (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ 0)
        (realizedFam (I := I) g₀ T 0 hδ hδZ s)
        (fun b => X b) (fun b => Y b) (fun b => Z b) x =
      s •
        ((LeviCivita (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ 0)).toFun
            (fun b : M =>
              DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I)
                (realizedFam (I := I) g₀ T 0 hδ hδZ s) b
                (linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ 0)
                  (realizedVelocityCc (I := I) g₀ T 0 hδ hδZ 0) b (Z b) (Y b))) x (X x)
          - DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I)
            (realizedFam (I := I) g₀ T 0 hδ hδZ s) x
            (linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ 0)
              (realizedVelocityCc (I := I) g₀ T 0 hδ hδZ 0) x (Z x)
              (covApply (LeviCivita (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ 0))
                (fun b => X b) (fun b => Y b) x))
          - DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I)
            (realizedFam (I := I) g₀ T 0 hδ hδZ s) x
            (linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ 0)
              (realizedVelocityCc (I := I) g₀ T 0 hδ hδZ 0) x
              (covApply (LeviCivita (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ 0))
                (fun b => X b) (fun b => Z b) x) (Y x))) := by
  classical
  have h0_mem : (0 : ℝ) ∈ realizedSmallSet (δ := δ) (δ' := δ) :=
    Icc_subset_realizedSmallSet hδ_lt hδ_lt ⟨le_refl (0 : ℝ), zero_le_one⟩
  have hs_mem : s ∈ realizedSmallSet (δ := δ) (δ' := δ) :=
    Icc_subset_realizedSmallSet hδ_lt hδ_lt hs
  have hexpand : covDerivConnDiff (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ 0)
      (realizedFam (I := I) g₀ T 0 hδ hδZ s)
      (fun b => X b) (fun b => Y b) (fun b => Z b) x =
      (LeviCivita (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ 0)).toFun
          (diffSec (LeviCivita (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ 0))
            (LeviCivita (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s))
            (fun b => Y b) (fun b => Z b)) x (X x)
        - PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s)
            (realizedFam (I := I) g₀ T 0 hδ hδZ 0) x (Z x)
            (covApply (LeviCivita (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ 0))
              (fun b => X b) (fun b => Y b) x)
        - PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s)
            (realizedFam (I := I) g₀ T 0 hδ hδZ 0) x
            (covApply (LeviCivita (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ 0))
              (fun b => X b) (fun b => Z b) x) (Y x) := rfl
  rw [hexpand]
  have hpoint : ∀ (b : M) (u ζ : TangentSpace I b),
      PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s)
        (realizedFam (I := I) g₀ T 0 hδ hδZ 0) b u ζ =
      s • DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I)
        (realizedFam (I := I) g₀ T 0 hδ hδZ s) b
        (linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ 0)
          (realizedVelocityCc (I := I) g₀ T 0 hδ hδZ 0) b u ζ) := by
    intro b u ζ
    have h := connDiff_realizedFam_eq_smul_sharp (I := I) g₀ T 0 hδ_lt hδ hδ_lt hδZ
      h0_mem hs_mem b u ζ
    rwa [sub_zero] at h
  by_cases hs0 : s = 0
  · subst hs0
    have hconn0 : ∀ (b : M) (u ζ : TangentSpace I b),
        PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ 0)
          (realizedFam (I := I) g₀ T 0 hδ hδZ 0) b u ζ = 0 := by
      intro b u ζ
      rw [PDE.DeTurck.connDiff_self]
      rfl
    have hdz : diffSec (LeviCivita (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ 0))
        (LeviCivita (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ 0))
        (fun b => Y b) (fun b => Z b) =
        (0 : ℝ) • fun b : M => X b := by
      funext b
      rw [Pi.smul_apply, zero_smul]
      exact hconn0 b (Z b) (Y b)
    rw [hdz]
    have hσX : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b (X b)) x :=
      (X.contMDiff x).mdifferentiableAt (by simp)
    have hsmul := (LeviCivita (I := I)
      (realizedFam (I := I) g₀ T 0 hδ hδZ 0)).isCovariantDerivativeOnUniv.smul_const
      (σ := fun b => X b) (x := x) (0 : ℝ) hσX (Set.mem_univ x)
    rw [hsmul, ContinuousLinearMap.smul_apply]
    rw [hconn0 x (Z x) (covApply (LeviCivita (I := I)
        (realizedFam (I := I) g₀ T 0 hδ hδZ 0)) (fun b => X b) (fun b => Y b) x),
      hconn0 x (covApply (LeviCivita (I := I)
        (realizedFam (I := I) g₀ T 0 hδ hδZ 0)) (fun b => X b) (fun b => Z b) x) (Y x)]
    rw [zero_smul, zero_smul]
    simp
  · have hconn_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b
          (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s)
            (realizedFam (I := I) g₀ T 0 hδ hδZ 0) b (Z b) (Y b))) :=
      PDE.DeTurck.connDiff_contMDiff (I := I)
        (realizedFam (I := I) g₀ T 0 hδ hδZ s) (realizedFam (I := I) g₀ T 0 hδ hδZ 0)
        Z.contMDiff Y.contMDiff
    have hΨ_eq : (fun b : M =>
        DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I)
          (realizedFam (I := I) g₀ T 0 hδ hδZ s) b
          (linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ 0)
            (realizedVelocityCc (I := I) g₀ T 0 hδ hδZ 0) b (Z b) (Y b))) =
        (fun b : M => s⁻¹ •
          PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s)
            (realizedFam (I := I) g₀ T 0 hδ hδZ 0) b (Z b) (Y b)) := by
      funext b
      rw [hpoint b (Z b) (Y b), smul_smul, inv_mul_cancel₀ hs0, one_smul]
    have hΨ_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b
          (DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I)
            (realizedFam (I := I) g₀ T 0 hδ hδZ s) b
            (linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ 0)
              (realizedVelocityCc (I := I) g₀ T 0 hδ hδZ 0) b (Z b) (Y b)))) := by
      have hsmul' := ContMDiff.smul_section
        (f := fun _ : M => s⁻¹)
        (s := fun b : M =>
          PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s)
            (realizedFam (I := I) g₀ T 0 hδ hδZ 0) b (Z b) (Y b))
        contMDiff_const hconn_smooth
      refine hsmul'.congr (fun b => ?_)
      refine congrArg (TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b) ?_
      change DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I)
        (realizedFam (I := I) g₀ T 0 hδ hδZ s) b
          (linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ 0)
            (realizedVelocityCc (I := I) g₀ T 0 hδ hδZ 0) b (Z b) (Y b)) =
        s⁻¹ • PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s)
          (realizedFam (I := I) g₀ T 0 hδ hδZ 0) b (Z b) (Y b)
      exact congrFun hΨ_eq b
    have hσ : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b
          (DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I)
            (realizedFam (I := I) g₀ T 0 hδ hδZ s) b
            (linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ 0)
              (realizedVelocityCc (I := I) g₀ T 0 hδ hδZ 0) b (Z b) (Y b)))) x :=
      (hΨ_smooth x).mdifferentiableAt (by simp)
    have hdiffSec : diffSec (LeviCivita (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ 0))
        (LeviCivita (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s))
        (fun b => Y b) (fun b => Z b) =
        s • (fun b : M =>
          DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I)
            (realizedFam (I := I) g₀ T 0 hδ hδZ s) b
            (linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ 0)
              (realizedVelocityCc (I := I) g₀ T 0 hδ hδZ 0) b (Z b) (Y b))) := by
      funext b
      rw [Pi.smul_apply]
      exact hpoint b (Z b) (Y b)
    rw [hdiffSec]
    have hsmul := (LeviCivita (I := I)
      (realizedFam (I := I) g₀ T 0 hδ hδZ 0)).isCovariantDerivativeOnUniv.smul_const
      (σ := fun b : M =>
        DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I)
          (realizedFam (I := I) g₀ T 0 hδ hδZ s) b
          (linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ 0)
            (realizedVelocityCc (I := I) g₀ T 0 hδ hδZ 0) b (Z b) (Y b)))
      (x := x) s hσ (Set.mem_univ x)
    rw [hsmul, ContinuousLinearMap.smul_apply]
    rw [hpoint x (Z x) (covApply (LeviCivita (I := I)
        (realizedFam (I := I) g₀ T 0 hδ hδZ 0)) (fun b => X b) (fun b => Y b) x),
      hpoint x (covApply (LeviCivita (I := I)
        (realizedFam (I := I) g₀ T 0 hδ hδZ 0)) (fun b => X b) (fun b => Z b) x) (Y x)]
    module

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
