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


omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma riemannianFiberNormSq_addsub4_le (g : SmoothRiemannianMetric I M)
    (r s : ℕ) (x : M) (u v w z : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (u + v - w - z) ≤
      4 * (riemannianFiberNormSq (I := I) (M := M) g r s x u +
        riemannianFiberNormSq (I := I) (M := M) g r s x v +
        riemannianFiberNormSq (I := I) (M := M) g r s x w +
        riemannianFiberNormSq (I := I) (M := M) g r s x z) := by
  have hsplit : u + v - w - z = (u + v) + -(w + z) := by abel
  rw [hsplit]
  have houter := riemannianFiberNormSq_add_le (I := I) (M := M) g r s x (u + v) (-(w + z))
  have hneg : riemannianFiberNormSq (I := I) (M := M) g r s x (-(w + z)) =
      riemannianFiberNormSq (I := I) (M := M) g r s x (w + z) := by
    rw [← neg_one_smul ℝ (w + z), riemannianFiberNormSq_smul]
    norm_num
  rw [hneg] at houter
  have huv := riemannianFiberNormSq_add_le (I := I) (M := M) g r s x u v
  have hwz := riemannianFiberNormSq_add_le (I := I) (M := M) g r s x w z
  linarith


omit [BoundarylessManifold I M] in
theorem riemannPalatiniRefoldC2Family_eq_symmS_kernel
    (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2) {δ : ℝ}
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ)
    (qA qB : Fin 4 → Equiv.Perm (Fin 4))
    (hq : IsFramePairPartner qA qB) (s : ℝ) :
    riemannPalatiniRefoldC2Family (I := I) (M := M) g₀ T hδ hδZ qA qB s =
      s • curvatureActionKernelCoeffField (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T 0 hδ hδZ s)
        (ccTensorUnitValueSection (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ T))
        (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀
          (ccTensor02Symm (I := I) (M := M) g₀ T))
        (qA 0) (qA 1) (qA 2) (qA 3) := by
  have h0 := curvatureRefoldMonomialCoeffField_unitValue_pair_eq_symmS (I := I) (M := M) g₀
    (realizedFam (I := I) g₀ T 0 hδ hδZ s) T (qA 0)
  have h1 := curvatureRefoldMonomialCoeffField_unitValue_pair_eq_symmS (I := I) (M := M) g₀
    (realizedFam (I := I) g₀ T 0 hδ hδZ s) T (qA 1)
  have h2 := curvatureRefoldMonomialCoeffField_unitValue_pair_eq_symmS (I := I) (M := M) g₀
    (realizedFam (I := I) g₀ T 0 hδ hδZ s) T (qA 2)
  have h3 := curvatureRefoldMonomialCoeffField_unitValue_pair_eq_symmS (I := I) (M := M) g₀
    (realizedFam (I := I) g₀ T 0 hδ hδZ s) T (qA 3)
  rw [riemannPalatiniRefoldC2Family, hq 0, hq 1, hq 2, hq 3]
  simp only [Equiv.Perm.mul_def, curvatureActionKernelCoeffField]
  rw [← h0, ← h1, ← h2, ← h3]
  module

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma ccTensorBilin_smul_local (g₀ : SmoothRiemannianMetric I M)
    (c : ℝ) (S : SmoothCcTensor g₀ 0 2) (b : M) (u w : TangentSpace I b) :
    smoothCcTensorBilinForm (I := I) g₀ (c • S) b u w =
      c * smoothCcTensorBilinForm (I := I) g₀ S b u w := by
  rw [ccTensorBilin_apply, ccTensorBilin_apply, ccTensorModel_smul,
    ContinuousMultilinearMap.smul_apply, smul_eq_mul]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma symmS_eq_self_of_symm (g₀ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2)
    (hsymm : ∀ (x : M) (u w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ S x u w = smoothCcTensorBilinForm (I := I) g₀ S x w u) :
    ccTensor02Symm (I := I) (M := M) g₀ S = S := by
  have hswap : domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) S = S := by
    refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀ (fun x => ?_)
    rw [domDomCongrSection_unitModel]
    refine ContinuousMultilinearMap.ext (fun v => ?_)
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    have hv : ∀ u w : TangentSpace I x,
        unitModel (I := I) (M := M) g₀ 2 S x ![u, w] =
          unitModel (I := I) (M := M) g₀ 2 S x ![w, u] := by
      intro u w
      rw [unitModel_eq_ccTensorBilin_local (I := I) (M := M) g₀ S x u w,
        unitModel_eq_ccTensorBilin_local (I := I) (M := M) g₀ S x w u]
      exact hsymm x u w
    have hveta : (fun i => v ((Equiv.swap (0 : Fin 2) 1) i)) = ![v 1, v 0] := by
      funext i
      fin_cases i <;> rfl
    have hveta' : v = ![v 0, v 1] := by
      funext i
      fin_cases i <;> rfl
    rw [hveta]
    conv_rhs => rw [hveta']
    exact hv (v 1) (v 0)
  have htwo : S + S = (2 : ℝ) • S := (two_smul ℝ S).symm
  rw [ccTensor02Symm, hswap, htwo, smul_smul,
    show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul]


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem threeArmHjoint_const_local (g₀ : SmoothRiemannianMetric I M) {r : ℕ}
    (F : SmoothCcTensor g₀ r 2) {δ δ' : ℝ} :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ r
      (fun _ : ℝ => F) (δ := δ) (δ' := δ') := by
  rw [linearizedRicciThreeArmHjoint]
  exact (F.toSection.contMDiff.comp contMDiff_fst).contMDiffOn

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem threeArmHjoint_const_smul_local (g₀ : SmoothRiemannianMetric I M) {r : ℕ}
    (c : ℝ) (A : ℝ → SmoothCcTensor g₀ r 2) {δ δ' : ℝ}
    (hA : linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ r A (δ := δ) (δ' := δ')) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ r
      (fun s => c • A s) (δ := δ) (δ' := δ') := by
  have hsm := jointTotalSpaceRS_const_smul_local (I := I) (M := M) (r := r) (s := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) c
    (fun p : M × ℝ => (A p.2).toSection p.1) hA
  refine hsm.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r 2 I z) p.1 t) ?_
  rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
lemma norm_add_sq_le_local (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (A B : SmoothCcTensor g r s) :
    ‖A + B‖ ^ 2 ≤ 2 * ‖A‖ ^ 2 + 2 * ‖B‖ ^ 2 := by
  have hn := norm_add_le A B
  nlinarith [mul_le_mul hn hn (norm_nonneg (A + B))
      (add_nonneg (norm_nonneg A) (norm_nonneg B)),
    sq_nonneg (‖A‖ - ‖B‖)]

private def backgroundRiemannCommWeightKernel (g₀ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 2 4 :=
  ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
    (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 (Equiv.swap (1 : Fin 6) 3)
      (slotExtendIter (I := I) (M := M) g₀ 0 4 2
        (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)))

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 12800000 in
omit [SigmaCompactSpace M] in
private lemma bdBgRArmWeight_toModel (g₀ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 2 I x) (m : Fin 4 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 4 I x from
          (backgroundRiemannCommWeightKernel (I := I) (M := M) g₀).toSection x) D) m =
      ∑ e : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel D
            ![(smoothOrthoFrame (I := I) g₀ x e x : E), (m 1 : E)] *
          g₀.inner x (riemannOp (LeviCivita (I := I) g₀) x (m 0) (m 2) (m 3))
            (smoothOrthoFrame (I := I) g₀ x e x) := by
  classical
  set Y : Tensor0SSpace 6 I x :=
    (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
      (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 (Equiv.swap (1 : Fin 6) 3)
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2
          (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀))).toSection x) D with hY_def
  have hYval : ∀ w : Fin 6 → TangentSpace I x,
      Tensor0SSpace.toModel Y w =
        Tensor0SSpace.toModel D ![w 0, w 3] *
          unitModel (I := I) (M := M) g₀ 4
            (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀) x ![w 2, w 1, w 4, w 5] := by
    intro w
    rw [hY_def]
    rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 (Equiv.swap (1 : Fin 6) 3)
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀))).toSection x) D) =
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
          tensorRS_domDomCongr (Equiv.swap (1 : Fin 6) 3)
            ((slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)).toSection x)) D) from by
      rw [rsDomDomCongrSection_toSection]]
    rw [toModel_rsDomDomCongr_apply (I := I) (M := M) (Equiv.swap (1 : Fin 6) 3)
      ((slotExtendIter (I := I) (M := M) g₀ 0 4 2
        (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)).toSection x) D]
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    rw [bdSlotExtendIter_two_toModel (I := I) (M := M) g₀
      (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀) x D
      (fun i => w ((Equiv.swap (1 : Fin 6) 3) i))]
    refine congrArg₂ (· * ·) ?_ ?_
    · refine congrArg _ ?_
      funext k
      fin_cases k <;> simp [Equiv.swap_apply_def]
    · refine congrArg _ ?_
      funext k
      fin_cases k <;> simp [Equiv.swap_apply_def]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 4 I x from
      (backgroundRiemannCommWeightKernel (I := I) (M := M) g₀).toSection x) D) =
      cometricDoubleTraceFib (I := I) g₀ 4 x Y from by
    rw [hY_def, backgroundRiemannCommWeightKernel]
    rw [appCcRS_toSection]
    rfl]
  rw [cometricDoubleTraceFib_toModel (I := I) g₀ 4 x Y]
  rw [modelDoubleTrace_apply (E := E) 4 (cometricLmodel (I := I) g₀ x)]
  rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) g₀ x
    (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
    (Tensor0SSpace.toModel Y) (fun j => (m j : E))]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [hYval]
  change Tensor0SSpace.toModel D
      ![((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E), (m 1 : E)] *
      unitModel (I := I) (M := M) g₀ 4
        (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀) x
        ![(m 0 : E), ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E),
          (m 2 : E), (m 3 : E)] = _
  rw [riemannLoweredCc_unitModel_apply (I := I) (M := M) g₀ g₀ g₀ x
    ![(m 0 : E), ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E),
      (m 2 : E), (m 3 : E)]]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 12800000 in
private theorem bdBgRComm_eq_refold (g₀ g : SmoothRiemannianMetric I M) :
    ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g =
      ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 2 (cometricDoubleTraceCc (I := I) (M := M) g₀ g 2)
        (backgroundRiemannCommWeightKernel (I := I) (M := M) g₀) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g).toSection x) D) =
      backgroundRiemannBiContrFib (I := I) g₀ g x D from rfl]
  rw [show backgroundRiemannBiContrFib (I := I) g₀ g x =
      backgroundRiemannBiContrFibFixedFrame (I := I) g₀ (smoothOrthoFrame (I := I) g x) x from rfl]
  rw [backgroundRiemannBiContrFibFixedFrame_toModel (I := I) g₀ (smoothOrthoFrame (I := I) g x) x D
    (fun j => (v j : E))]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 2 (cometricDoubleTraceCc (I := I) (M := M) g₀ g 2)
        (backgroundRiemannCommWeightKernel (I := I) (M := M) g₀)).toSection x) D) =
      cometricDoubleTraceFib (I := I) g 2 x
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 4 I x from
          (backgroundRiemannCommWeightKernel (I := I) (M := M) g₀).toSection x) D) from by
    rw [appCcRS_toSection]
    rfl]
  beta_reduce
  rw [cometricDoubleTraceFib_toModel (I := I) g 2 x]
  rw [modelDoubleTrace_apply (E := E) 2 (cometricLmodel (I := I) g x)]
  rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) g x
    (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
    (Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 4 I x from
        (backgroundRiemannCommWeightKernel (I := I) (M := M) g₀).toSection x) D))
    (fun j => (v j : E))]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [bdBgRArmWeight_toModel (I := I) (M := M) g₀ x D]
  change Tensor0SSpace.toModel D
      (Fin.cons (show E from riemannOp (LeviCivita (I := I) g₀) x
          (smoothOrthoFrame (I := I) g x c x) (v 0) (v 1))
        (Fin.cons ((smoothOrthoFrame (I := I) g x c x : TangentSpace I x) : E)
          (fun i : Fin 0 => i.elim0))) =
    ∑ e : Fin (Module.finrank ℝ E),
      Tensor0SSpace.toModel D
          (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g x c x : TangentSpace I x) : E)
              (fun i : Fin 0 => i.elim0))) *
        g₀.inner x (riemannOp (LeviCivita (I := I) g₀) x
            (smoothOrthoFrame (I := I) g x c x) (v 0) (v 1))
          (smoothOrthoFrame (I := I) g₀ x e x)
  have hu_exp : (show E from riemannOp (LeviCivita (I := I) g₀) x
      (smoothOrthoFrame (I := I) g x c x) (v 0) (v 1)) =
      ∑ e : Fin (Module.finrank ℝ E),
        g₀.inner x (riemannOp (LeviCivita (I := I) g₀) x
            (smoothOrthoFrame (I := I) g x c x) (v 0) (v 1))
          (smoothOrthoFrame (I := I) g₀ x e x) •
        ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E) := by
    rw [show (∑ e : Fin (Module.finrank ℝ E),
        g₀.inner x (riemannOp (LeviCivita (I := I) g₀) x
            (smoothOrthoFrame (I := I) g x c x) (v 0) (v 1))
          (smoothOrthoFrame (I := I) g₀ x e x) •
        ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)) =
        ((∑ e : Fin (Module.finrank ℝ E),
          g₀.inner x (riemannOp (LeviCivita (I := I) g₀) x
              (smoothOrthoFrame (I := I) g x c x) (v 0) (v 1))
            (smoothOrthoFrame (I := I) g₀ x e x) •
          smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E) from rfl]
    have hrep := bdOrthoFrame_center_repr (I := I) (M := M) g₀ x
      (riemannOp (LeviCivita (I := I) g₀) x (smoothOrthoFrame (I := I) g x c x) (v 0) (v 1))
    conv_lhs => rw [hrep]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [g₀.symm x (smoothOrthoFrame (I := I) g₀ x e x)
      (riemannOp (LeviCivita (I := I) g₀) x (smoothOrthoFrame (I := I) g x c x) (v 0) (v 1))]
  rw [hu_exp]
  rw [bdToModel_cons_sum_smul (E := E) x (Tensor0SSpace.toModel D)
    (Module.finrank ℝ E)
    (fun e => g₀.inner x (riemannOp (LeviCivita (I := I) g₀) x
        (smoothOrthoFrame (I := I) g x c x) (v 0) (v 1))
      (smoothOrthoFrame (I := I) g₀ x e x))
    (fun e => ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E))
    (Fin.cons ((smoothOrthoFrame (I := I) g x c x : TangentSpace I x) : E)
      (fun i : Fin 0 => i.elim0))]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [mul_comm]

def palatiniRicciFoldWeightBPerm : Equiv.Perm (Fin 6) :=
  ⟨fun i => (![5, 0, 2, 1, 4, 3] : Fin 6 → Fin 6) i,
   fun i => (![1, 3, 2, 5, 4, 0] : Fin 6 → Fin 6) i,
   by decide, by decide⟩

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem bdOrthoFrameBasis_at_center (g₀ : SmoothRiemannianMetric I M) (x : M) :
    ∃ bse : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x),
      ∀ i, bse i = smoothOrthoFrame (I := I) g₀ x i x := by
  classical
  have horth : ∀ a b : Fin (Module.finrank ℝ E),
      g₀.inner x (smoothOrthoFrame (I := I) g₀ x a x)
        (smoothOrthoFrame (I := I) g₀ x b x) = if a = b then 1 else 0 :=
    fun a b => smoothOrthoFrame_orthonormal_at_center (I := I) g₀ x a b
  have he_li : LinearIndependent ℝ
      (fun i => smoothOrthoFrame (I := I) g₀ x i x) := by
    rw [linearIndependent_iff']
    intro fs c hsum k hk_mem
    have h_zero : g₀.inner x (smoothOrthoFrame (I := I) g₀ x k x)
        (∑ j ∈ fs, c j • smoothOrthoFrame (I := I) g₀ x j x) = 0 := by
      rw [hsum]; simp
    rw [map_sum] at h_zero
    have h_pull : ∀ j ∈ fs, g₀.inner x (smoothOrthoFrame (I := I) g₀ x k x)
        (c j • smoothOrthoFrame (I := I) g₀ x j x) =
        c j * (if k = j then (1 : ℝ) else 0) := by
      intro j _
      rw [(g₀.inner x (smoothOrthoFrame (I := I) g₀ x k x)).map_smul (c j),
        smul_eq_mul, horth k j]
    rw [Finset.sum_congr rfl h_pull, Finset.sum_eq_single_of_mem k hk_mem] at h_zero
    · rwa [if_pos rfl, mul_one] at h_zero
    · intro j _ hjk
      rw [if_neg (fun h => hjk h.symm), mul_zero]
  have hcard : Fintype.card (Fin (Module.finrank ℝ E)) = Module.finrank ℝ E :=
    Fintype.card_fin _
  exact ⟨basisOfLinearIndependentOfCardEqFinrank he_li hcard,
    fun i => congrFun (coe_basisOfLinearIndependentOfCardEqFinrank he_li hcard) i⟩

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem bdOrthoFrame_expansion_at_center (g₀ : SmoothRiemannianMetric I M)
    (x : M) (u : TangentSpace I x) :
    u = ∑ i : Fin (Module.finrank ℝ E),
      g₀.inner x u (smoothOrthoFrame (I := I) g₀ x i x) •
        smoothOrthoFrame (I := I) g₀ x i x := by
  classical
  obtain ⟨bse, hbse⟩ := bdOrthoFrameBasis_at_center (I := I) (M := M) g₀ x
  have horth : ∀ a b : Fin (Module.finrank ℝ E),
      g₀.inner x (smoothOrthoFrame (I := I) g₀ x a x)
        (smoothOrthoFrame (I := I) g₀ x b x) = if a = b then 1 else 0 :=
    fun a b => smoothOrthoFrame_orthonormal_at_center (I := I) g₀ x a b
  have hcoeff : ∀ j : Fin (Module.finrank ℝ E),
      g₀.inner x u (smoothOrthoFrame (I := I) g₀ x j x) = bse.repr u j := by
    intro j
    rw [g₀.symm x u (smoothOrthoFrame (I := I) g₀ x j x)]
    conv_lhs => rw [← bse.sum_repr u]
    rw [map_sum]
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => by
      rw [(g₀.inner x (smoothOrthoFrame (I := I) g₀ x j x)).map_smul (bse.repr u i),
        smul_eq_mul, hbse i, horth j i])]
    rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ j)]
    · rw [if_pos rfl, mul_one]
    · intro i _ hij
      rw [if_neg (fun h => hij h.symm), mul_zero]
  calc u = ∑ i : Fin (Module.finrank ℝ E), bse.repr u i • bse i := (bse.sum_repr u).symm
    _ = ∑ i : Fin (Module.finrank ℝ E),
        g₀.inner x u (smoothOrthoFrame (I := I) g₀ x i x) •
          smoothOrthoFrame (I := I) g₀ x i x := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hcoeff i, hbse i]

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma bdCcTensorBilin_expand_left (g₀ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (x : M) (u w : TangentSpace I x) :
    smoothCcTensorBilinForm (I := I) g₀ S x u w =
      ∑ e : Fin (Module.finrank ℝ E),
        g₀.inner x u (smoothOrthoFrame (I := I) g₀ x e x) *
          smoothCcTensorBilinForm (I := I) g₀ S x (smoothOrthoFrame (I := I) g₀ x e x) w := by
  conv_lhs => rw [bdOrthoFrame_expansion_at_center (I := I) (M := M) g₀ x u]
  rw [map_sum (smoothCcTensorBilinForm (I := I) g₀ S x) _ Finset.univ, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [map_smul (smoothCcTensorBilinForm (I := I) g₀ S x), ContinuousLinearMap.smul_apply, smul_eq_mul]

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma bdCcTensorBilin_expand_right (g₀ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (x : M) (u w : TangentSpace I x) :
    smoothCcTensorBilinForm (I := I) g₀ S x u w =
      ∑ e : Fin (Module.finrank ℝ E),
        g₀.inner x w (smoothOrthoFrame (I := I) g₀ x e x) *
          smoothCcTensorBilinForm (I := I) g₀ S x u (smoothOrthoFrame (I := I) g₀ x e x) := by
  conv_lhs => rw [bdOrthoFrame_expansion_at_center (I := I) (M := M) g₀ x w]
  rw [map_sum (smoothCcTensorBilinForm (I := I) g₀ S x u) _ Finset.univ]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [map_smul (smoothCcTensorBilinForm (I := I) g₀ S x u), smul_eq_mul]

def palatiniRicciFoldWeightA (g₀ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) : SmoothCcTensor g₀ 0 4 :=
  ccOperatorFieldComp (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
    (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 (Equiv.swap (1 : Fin 6) 3)
      (ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 6
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2
          (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)) S))

def palatiniRicciFoldWeightB (g₀ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) : SmoothCcTensor g₀ 0 4 :=
  ccOperatorFieldComp (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
    (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 palatiniRicciFoldWeightBPerm
      (ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 6
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2
          (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)) S))

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 12800000 in
omit [SigmaCompactSpace M] in
private lemma bdRicciFoldWeight_unitModel_gen (g₀ : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 6)) (S : SmoothCcTensor g₀ 0 2) (x : M) (m : Fin 4 → E) :
    unitModel (I := I) (M := M) g₀ 4
        (ccOperatorFieldComp (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 σ
            (ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 6
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)) S))) x m =
      ∑ e : Fin (Module.finrank ℝ E),
        unitModel (I := I) (M := M) g₀ 2 S x
            ![((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
                (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E) m) :
                  Fin 6 → E) (σ 0)),
              ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
                (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E) m) :
                  Fin 6 → E) (σ 1))] *
          unitModel (I := I) (M := M) g₀ 4
            (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀) x
            ![((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
                (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E) m) :
                  Fin 6 → E) (σ 2)),
              ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
                (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E) m) :
                  Fin 6 → E) (σ 3)),
              ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
                (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E) m) :
                  Fin 6 → E) (σ 4)),
              ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
                (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E) m) :
                  Fin 6 → E) (σ 5))] := by
  classical
  set R4 : SmoothCcTensor g₀ 0 4 := riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀ with hR4_def
  set Sval : Tensor0SSpace 2 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from S.toSection x)
      (unitTensor (I := I) (M := M) x) with hSval_def
  set Y : Tensor0SSpace 6 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 6 I x from
      (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 σ
        (ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 6
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2 R4) S)).toSection x)
      (unitTensor (I := I) (M := M) x) with hY_def
  have hYval : ∀ w : Fin 6 → TangentSpace I x,
      Tensor0SSpace.toModel Y w =
        Tensor0SSpace.toModel Sval ![(w (σ 0) : E), (w (σ 1) : E)] *
          unitModel (I := I) (M := M) g₀ 4 R4 x
            ![(w (σ 2) : E), (w (σ 3) : E), (w (σ 4) : E), (w (σ 5) : E)] := by
    intro w
    rw [hY_def]
    rw [show ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 6 I x from
        (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 σ
          (ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 6
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2 R4) S)).toSection x)
        (unitTensor (I := I) (M := M) x)) =
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 6 I x from
          tensorRS_domDomCongr σ
            ((ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 6
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2 R4) S).toSection x))
          (unitTensor (I := I) (M := M) x)) from by
      rw [rsDomDomCongrSection_toSection]]
    rw [toModel_rsDomDomCongr_apply (I := I) (M := M) σ
      ((ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 6
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2 R4) S).toSection x)
      (unitTensor (I := I) (M := M) x)]
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    rw [show ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 6 I x from
        (ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 6
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2 R4) S).toSection x)
        (unitTensor (I := I) (M := M) x)) =
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2 R4).toSection x) Sval) from by
      rw [appCcRS_toSection]
      rfl]
    rw [bdSlotExtendIter_two_toModel (I := I) (M := M) g₀ R4 x Sval (fun i => w (σ i))]
    refine congrArg₂ (· * ·) ?_ ?_
    · refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl
    · rw [show unitModel (I := I) (M := M) g₀ 4 R4 x
          (fun k : Fin 4 => ((fun i => w (σ i)) (Fin.natAdd 2 k) : E)) =
          unitModel (I := I) (M := M) g₀ 4 R4 x
            ![(w (σ 2) : E), (w (σ 3) : E), (w (σ 4) : E), (w (σ 5) : E)] from by
        refine congrArg _ ?_
        funext k
        fin_cases k <;> rfl]
  rw [show unitModel (I := I) (M := M) g₀ 4
      (ccOperatorFieldComp (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 σ
          (ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 6
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2 R4) S))) x =
      Tensor0SSpace.toModel (cometricDoubleTraceFib (I := I) g₀ 4 x Y) from by
    rw [unitModel, hY_def]
    rw [appCcRS_toSection]
    rfl]
  rw [cometricDoubleTraceFib_toModel (I := I) g₀ 4 x Y]
  rw [modelDoubleTrace_apply (E := E) 4 (cometricLmodel (I := I) g₀ x)]
  rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) g₀ x
    (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
    (Tensor0SSpace.toModel Y) m]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [hYval]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 12800000 in
omit [SigmaCompactSpace M] in
private lemma bdRicciFoldWeights_unitModel_eq_kernel (g₀ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (x : M) (p q v0 v1 : TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 4
        (palatiniRicciFoldWeightA (I := I) (M := M) g₀ S +
          palatiniRicciFoldWeightB (I := I) (M := M) g₀ S) x
        ![(v0 : E), (v1 : E), (p : E), (q : E)] =
      smoothCcTensorBilinForm (I := I) g₀ S x (riemannOp (LeviCivita (I := I) g₀) x v0 p q) v1 +
        smoothCcTensorBilinForm (I := I) g₀ S x q (riemannOp (LeviCivita (I := I) g₀) x v0 p v1) := by
  classical
  rw [bdUnitModel_add (I := I) (M := M) g₀ 4
    (palatiniRicciFoldWeightA (I := I) (M := M) g₀ S) (palatiniRicciFoldWeightB (I := I) (M := M) g₀ S) x,
    ContinuousMultilinearMap.add_apply]
  have hA : unitModel (I := I) (M := M) g₀ 4 (palatiniRicciFoldWeightA (I := I) (M := M) g₀ S) x
      ![(v0 : E), (v1 : E), (p : E), (q : E)] =
      smoothCcTensorBilinForm (I := I) g₀ S x (riemannOp (LeviCivita (I := I) g₀) x v0 p q) v1 := by
    rw [show palatiniRicciFoldWeightA (I := I) (M := M) g₀ S =
        ccOperatorFieldComp (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 (Equiv.swap (1 : Fin 6) 3)
            (ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 6
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)) S)) from rfl]
    rw [bdRicciFoldWeight_unitModel_gen (I := I) (M := M) g₀ (Equiv.swap (1 : Fin 6) 3) S x
      ![(v0 : E), (v1 : E), (p : E), (q : E)]]
    rw [bdCcTensorBilin_expand_left (I := I) (M := M) g₀ S x
      (riemannOp (LeviCivita (I := I) g₀) x v0 p q) v1]
    refine Finset.sum_congr rfl fun e _ => ?_
    have h1 : unitModel (I := I) (M := M) g₀ 2 S x
        ![((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E)
            ((Equiv.swap (1 : Fin 6) 3) 0)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E)
            ((Equiv.swap (1 : Fin 6) 3) 1))] =
        unitModel (I := I) (M := M) g₀ 2 S x
          ![((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E), (v1 : E)] := by
      refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl
    have h2 : unitModel (I := I) (M := M) g₀ 4
        (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀) x
        ![((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E)
            ((Equiv.swap (1 : Fin 6) 3) 2)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E)
            ((Equiv.swap (1 : Fin 6) 3) 3)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E)
            ((Equiv.swap (1 : Fin 6) 3) 4)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E)
            ((Equiv.swap (1 : Fin 6) 3) 5))] =
        g₀.inner x (riemannOp (LeviCivita (I := I) g₀) x v0 p q)
          (smoothOrthoFrame (I := I) g₀ x e x) := by
      rw [show (![((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E)
            ((Equiv.swap (1 : Fin 6) 3) 2)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E)
            ((Equiv.swap (1 : Fin 6) 3) 3)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E)
            ((Equiv.swap (1 : Fin 6) 3) 4)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E)
            ((Equiv.swap (1 : Fin 6) 3) 5))] : Fin 4 → E) =
          ![(v0 : E), ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E),
            (p : E), (q : E)] from by
        funext k
        fin_cases k <;> rfl]
      rw [riemannLoweredCc_unitModel_apply (I := I) (M := M) g₀ g₀ g₀ x
        ![(v0 : E), ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E),
          (p : E), (q : E)]]
      rfl
    rw [h1, h2]
    rw [unitModel_eq_ccTensorBilin_local (I := I) (M := M) g₀ S x
      (smoothOrthoFrame (I := I) g₀ x e x) v1]
    ring
  have hB : unitModel (I := I) (M := M) g₀ 4 (palatiniRicciFoldWeightB (I := I) (M := M) g₀ S) x
      ![(v0 : E), (v1 : E), (p : E), (q : E)] =
      smoothCcTensorBilinForm (I := I) g₀ S x q (riemannOp (LeviCivita (I := I) g₀) x v0 p v1) := by
    rw [show palatiniRicciFoldWeightB (I := I) (M := M) g₀ S =
        ccOperatorFieldComp (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 palatiniRicciFoldWeightBPerm
            (ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 6
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)) S)) from rfl]
    rw [bdRicciFoldWeight_unitModel_gen (I := I) (M := M) g₀ palatiniRicciFoldWeightBPerm S x
      ![(v0 : E), (v1 : E), (p : E), (q : E)]]
    rw [bdCcTensorBilin_expand_right (I := I) (M := M) g₀ S x q
      (riemannOp (LeviCivita (I := I) g₀) x v0 p v1)]
    refine Finset.sum_congr rfl fun e _ => ?_
    have h1 : unitModel (I := I) (M := M) g₀ 2 S x
        ![((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E)
            (palatiniRicciFoldWeightBPerm 0)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E)
            (palatiniRicciFoldWeightBPerm 1))] =
        unitModel (I := I) (M := M) g₀ 2 S x
          ![(q : E), ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)] := by
      refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl
    have h2 : unitModel (I := I) (M := M) g₀ 4
        (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀) x
        ![((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E)
            (palatiniRicciFoldWeightBPerm 2)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E)
            (palatiniRicciFoldWeightBPerm 3)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E)
            (palatiniRicciFoldWeightBPerm 4)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E)
            (palatiniRicciFoldWeightBPerm 5))] =
        g₀.inner x (riemannOp (LeviCivita (I := I) g₀) x v0 p v1)
          (smoothOrthoFrame (I := I) g₀ x e x) := by
      rw [show (![((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E)
            (palatiniRicciFoldWeightBPerm 2)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E)
            (palatiniRicciFoldWeightBPerm 3)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E)
            (palatiniRicciFoldWeightBPerm 4)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E)
            (palatiniRicciFoldWeightBPerm 5))] : Fin 4 → E) =
          ![(v0 : E), ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E),
            (p : E), (v1 : E)] from by
        funext k
        fin_cases k <;> rfl]
      rw [riemannLoweredCc_unitModel_apply (I := I) (M := M) g₀ g₀ g₀ x
        ![(v0 : E), ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E),
          (p : E), (v1 : E)]]
      rfl
    rw [h1, h2]
    rw [show unitModel (I := I) (M := M) g₀ 2 S x
        ![(q : E), ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)] =
        smoothCcTensorBilinForm (I := I) g₀ S x q (smoothOrthoFrame (I := I) g₀ x e x) from
      unitModel_eq_ccTensorBilin_local (I := I) (M := M) g₀ S x q
        (smoothOrthoFrame (I := I) g₀ x e x)]
    ring
  rw [hA, hB]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 12800000 in
lemma bdRicciFold_eq_refold (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) :
    ricciArmRicciFoldRemainderField (I := I) (M := M) g₀ g₁ S =
      (-(1 / 2) : ℝ) •
        ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 (armPairTraceOpCc (I := I) (M := M) g₀ g₁)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (palatiniRicciFoldWeightA (I := I) (M := M) g₀ S +
                palatiniRicciFoldWeightB (I := I) (M := M) g₀ S))) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply tensorRSSpace_ext 2 2 x
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  beta_reduce
  have hRHSsmul : ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (((-(1 / 2) : ℝ) •
        ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 (armPairTraceOpCc (I := I) (M := M) g₀ g₁)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (palatiniRicciFoldWeightA (I := I) (M := M) g₀ S +
                palatiniRicciFoldWeightB (I := I) (M := M) g₀ S)))).toSection x)) D) =
      (-(1 / 2) : ℝ) • ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 (armPairTraceOpCc (I := I) (M := M) g₀ g₁)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (palatiniRicciFoldWeightA (I := I) (M := M) g₀ S +
                palatiniRicciFoldWeightB (I := I) (M := M) g₀ S)))).toSection x) D) := by
    rw [show ((((-(1 / 2) : ℝ) •
        ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 (armPairTraceOpCc (I := I) (M := M) g₀ g₁)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (palatiniRicciFoldWeightA (I := I) (M := M) g₀ S +
                palatiniRicciFoldWeightB (I := I) (M := M) g₀ S)))).toSection x)) =
        (-(1 / 2) : ℝ) •
          ((ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 (armPairTraceOpCc (I := I) (M := M) g₀ g₁)
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (palatiniRicciFoldWeightA (I := I) (M := M) g₀ S +
                  palatiniRicciFoldWeightB (I := I) (M := M) g₀ S)))).toSection x) from by
      rw [SmoothCcTensor.toSection_smul]; rfl]
    rfl
  rw [hRHSsmul, Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  rw [bdPairTraceOp_apply_toModel (I := I) (M := M) g₀ g₁
    (palatiniRicciFoldWeightA (I := I) (M := M) g₀ S + palatiniRicciFoldWeightB (I := I) (M := M) g₀ S)
    x D v]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (ricciArmRicciFoldRemainderField (I := I) (M := M) g₀ g₁ S).toSection x) D) =
      ricciFoldBiContrFib (I := I) g₀ g₁ S x D from rfl]
  rw [show ricciFoldBiContrFib (I := I) g₀ g₁ S x =
      ricciFoldBiContrFibFixedFrame (I := I) g₀ S (smoothOrthoFrame (I := I) g₁ x) x from rfl]
  rw [ricciFoldBiContrFibFixedFrame_toModel (I := I) g₀ S (smoothOrthoFrame (I := I) g₁ x) x D v]
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [ricciFoldKernelBilin_apply (I := I) g₀ S x
    (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x) (v 0) (v 1)]
  rw [show unitModel (I := I) (M := M) g₀ 4
      (palatiniRicciFoldWeightA (I := I) (M := M) g₀ S + palatiniRicciFoldWeightB (I := I) (M := M) g₀ S) x
      ![v 0, v 1, (smoothOrthoFrame (I := I) g₁ x a x : E),
        (smoothOrthoFrame (I := I) g₁ x b x : E)] =
      smoothCcTensorBilinForm (I := I) g₀ S x
          (riemannOp (LeviCivita (I := I) g₀) x (v 0) (smoothOrthoFrame (I := I) g₁ x a x)
            (smoothOrthoFrame (I := I) g₁ x b x)) (v 1) +
        smoothCcTensorBilinForm (I := I) g₀ S x (smoothOrthoFrame (I := I) g₁ x b x)
          (riemannOp (LeviCivita (I := I) g₀) x (v 0) (smoothOrthoFrame (I := I) g₁ x a x)
            (v 1)) from
    bdRicciFoldWeights_unitModel_eq_kernel (I := I) (M := M) g₀ S x
      (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x)
      (v 0) (v 1)]
  ring

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 12800000 in
omit [SigmaCompactSpace M] in
private lemma bdRicciFoldWeights_pair_smul (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (c : ℝ) :
    palatiniRicciFoldWeightA (I := I) (M := M) g₀ (c • T) +
      palatiniRicciFoldWeightB (I := I) (M := M) g₀ (c • T) =
      c • (palatiniRicciFoldWeightA (I := I) (M := M) g₀ T +
        palatiniRicciFoldWeightB (I := I) (M := M) g₀ T) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro t
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  have hdecomp := bdTensor0S_zero_rank_decomp (I := I) (M := M) x t
  rw [hdecomp, map_smul, map_smul]
  beta_reduce
  rw [Tensor0SSpace.toModel_smul, Tensor0SSpace.toModel_smul,
    ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.smul_apply]
  refine congrArg _ ?_
  change unitModel (I := I) (M := M) g₀ 4
      (palatiniRicciFoldWeightA (I := I) (M := M) g₀ (c • T) +
        palatiniRicciFoldWeightB (I := I) (M := M) g₀ (c • T)) x m =
    unitModel (I := I) (M := M) g₀ 4
      (c • (palatiniRicciFoldWeightA (I := I) (M := M) g₀ T +
        palatiniRicciFoldWeightB (I := I) (M := M) g₀ T)) x m
  rw [bdUnitModel_smul (I := I) (M := M) g₀ 4 c
    (palatiniRicciFoldWeightA (I := I) (M := M) g₀ T + palatiniRicciFoldWeightB (I := I) (M := M) g₀ T) x]
  rw [ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  rw [show m = ![m 0, m 1, m 2, m 3] from by
    funext k
    fin_cases k <;> rfl]
  rw [show unitModel (I := I) (M := M) g₀ 4
      (palatiniRicciFoldWeightA (I := I) (M := M) g₀ (c • T) +
        palatiniRicciFoldWeightB (I := I) (M := M) g₀ (c • T)) x ![m 0, m 1, m 2, m 3] =
      smoothCcTensorBilinForm (I := I) g₀ (c • T) x
          (riemannOp (LeviCivita (I := I) g₀) x (m 0) (m 2) (m 3)) (m 1) +
        smoothCcTensorBilinForm (I := I) g₀ (c • T) x (m 3)
          (riemannOp (LeviCivita (I := I) g₀) x (m 0) (m 2) (m 1)) from
    bdRicciFoldWeights_unitModel_eq_kernel (I := I) (M := M) g₀ (c • T) x
      (m 2) (m 3) (m 0) (m 1)]
  rw [show unitModel (I := I) (M := M) g₀ 4
      (palatiniRicciFoldWeightA (I := I) (M := M) g₀ T +
        palatiniRicciFoldWeightB (I := I) (M := M) g₀ T) x ![m 0, m 1, m 2, m 3] =
      smoothCcTensorBilinForm (I := I) g₀ T x
          (riemannOp (LeviCivita (I := I) g₀) x (m 0) (m 2) (m 3)) (m 1) +
        smoothCcTensorBilinForm (I := I) g₀ T x (m 3)
          (riemannOp (LeviCivita (I := I) g₀) x (m 0) (m 2) (m 1)) from
    bdRicciFoldWeights_unitModel_eq_kernel (I := I) (M := M) g₀ T x
      (m 2) (m 3) (m 0) (m 1)]
  rw [ccTensorBilin_smul_local, ccTensorBilin_smul_local]
  ring

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 12800000 in
omit [SigmaCompactSpace M] in
lemma bdRicciFoldXi_smul (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (c : ℝ) :
    rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
      (slotExtendIter (I := I) (M := M) g₀ 0 4 2
        (palatiniRicciFoldWeightA (I := I) (M := M) g₀ (c • T) +
          palatiniRicciFoldWeightB (I := I) (M := M) g₀ (c • T))) =
    c • rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
      (slotExtendIter (I := I) (M := M) g₀ 0 4 2
        (palatiniRicciFoldWeightA (I := I) (M := M) g₀ T +
          palatiniRicciFoldWeightB (I := I) (M := M) g₀ T)) := by
  classical
  rw [bdRicciFoldWeights_pair_smul (I := I) (M := M) g₀ T c]
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro w
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
      ((c • rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2
          (palatiniRicciFoldWeightA (I := I) (M := M) g₀ T +
            palatiniRicciFoldWeightB (I := I) (M := M) g₀ T))).toSection x)) D) =
      c • ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (palatiniRicciFoldWeightA (I := I) (M := M) g₀ T +
              palatiniRicciFoldWeightB (I := I) (M := M) g₀ T))).toSection x) D) from by
    rw [show (((c • rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2
          (palatiniRicciFoldWeightA (I := I) (M := M) g₀ T +
            palatiniRicciFoldWeightB (I := I) (M := M) g₀ T))).toSection x)) =
        c • ((rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (palatiniRicciFoldWeightA (I := I) (M := M) g₀ T +
              palatiniRicciFoldWeightB (I := I) (M := M) g₀ T))).toSection x) from by
      rw [SmoothCcTensor.toSection_smul]; rfl]
    rfl]
  beta_reduce
  rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  have hchain : ∀ (X : SmoothCcTensor g₀ 0 4),
      Tensor0SSpace.toModel
          ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X)).toSection x) D) w =
        Tensor0SSpace.toModel D
            ![(fun i => w (armPairTraceSlotPerm6 i)) 0, (fun i => w (armPairTraceSlotPerm6 i)) 1] *
          unitModel (I := I) (M := M) g₀ 4 X x
            (fun k : Fin 4 => (fun i => w (armPairTraceSlotPerm6 i)) (Fin.natAdd 2 k)) := by
    intro X
    rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X)).toSection x) D) =
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
          tensorRS_domDomCongr armPairTraceSlotPerm6
            ((slotExtendIter (I := I) (M := M) g₀ 0 4 2 X).toSection x)) D) from by
      rw [rsDomDomCongrSection_toSection]]
    rw [toModel_rsDomDomCongr_apply (I := I) (M := M) armPairTraceSlotPerm6
      ((slotExtendIter (I := I) (M := M) g₀ 0 4 2 X).toSection x) D]
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    exact bdSlotExtendIter_two_toModel (I := I) (M := M) g₀ X x D
      (fun i => w (armPairTraceSlotPerm6 i))
  rw [hchain (c • (palatiniRicciFoldWeightA (I := I) (M := M) g₀ T +
      palatiniRicciFoldWeightB (I := I) (M := M) g₀ T)),
    hchain (palatiniRicciFoldWeightA (I := I) (M := M) g₀ T +
      palatiniRicciFoldWeightB (I := I) (M := M) g₀ T)]
  rw [bdUnitModel_smul (I := I) (M := M) g₀ 4 c
    (palatiniRicciFoldWeightA (I := I) (M := M) g₀ T +
      palatiniRicciFoldWeightB (I := I) (M := M) g₀ T) x]
  rw [ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  ring

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem bdJointTotalSpace0S_smulFun_local {d : ℕ} {S : Set ℝ}
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (A : ∀ p : M × ℝ, Tensor0SSpace d I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SSpace d I z) p.1 (A p))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SSpace d I z) p.1 (f p.2 • A p))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) d
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt (Tensor0SModel d ℝ E)
    (fun z : M => Tensor0SSpace d I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SModel d ℝ E)
    (E := fun z : M => Tensor0SSpace d I z)).mp (hA p₀ hp₀)
  have hfm : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (fun p : M × ℝ => f p.2) :=
    hf.contMDiff.comp contMDiff_snd
  have hfj : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : M × ℝ => f p.2) ((Set.univ : Set M) ×ˢ S) p₀ :=
    (hfm.contMDiffAt).contMDiffWithinAt
  refine (hfj.smul hA'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact (e.linear ℝ hx).map_smul (f p.2) (A p)
  · exact (e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_smul
      (f p₀.2) (A p₀)

omit [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma connDiffQuadraticMonomial_chartBasis_eq (g₀ g₁ : SmoothRiemannianMetric I M)
    (α : M) {x : M} (hx : x ∈ chartLeviCivitaGoodSet (I := I) α)
    (j k u v : Fin (Module.finrank ℝ E)) :
    g₁.inner x
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            (chartBasisVecFiber (I := I) α j x) (chartBasisVecFiber (I := I) α k x))
          (chartBasisVecFiber (I := I) α u x))
        (chartBasisVecFiber (I := I) α v x) =
      ∑ c : Fin (Module.finrank ℝ E),
        (chartChristoffel (I := I) g₁ α k j c (extChartAt I α x) -
            chartChristoffel (I := I) g₀ α k j c (extChartAt I α x)) *
          ∑ d : Fin (Module.finrank ℝ E),
            (chartChristoffel (I := I) g₁ α u c d (extChartAt I α x) -
                chartChristoffel (I := I) g₀ α u c d (extChartAt I α x)) *
              chartGramMatrix (I := I) g₁ α x d v := by
  classical
  have houter : ∀ c : Fin (Module.finrank ℝ E),
      g₁.inner x
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            (chartBasisVecFiber (I := I) α c x) (chartBasisVecFiber (I := I) α u x))
          (chartBasisVecFiber (I := I) α v x) =
        ∑ d : Fin (Module.finrank ℝ E),
          (chartChristoffel (I := I) g₁ α u c d (extChartAt I α x) -
              chartChristoffel (I := I) g₀ α u c d (extChartAt I α x)) *
            chartGramMatrix (I := I) g₁ α x d v := by
    intro c
    rw [PDE.DeTurck.connDiff_chartBasis_pair_eq_sum (I := I) g₁ g₀ α hx c u,
      map_sum, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul,
      g_inner_eq_chartGramMatrix_basis (I := I) g₁ α x d v]
  rw [PDE.DeTurck.connDiff_chartBasis_pair_eq_sum (I := I) g₁ g₀ α hx j k,
    map_sum, ContinuousLinearMap.sum_apply, map_sum, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [map_smul, ContinuousLinearMap.smul_apply, map_smul, ContinuousLinearMap.smul_apply,
    smul_eq_mul, houter c]

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma palatiniRefoldGenJointGram_const_g0
    (g₀ : SmoothRiemannianMetric I M) (α : M) {S : Set ℝ} :
    ChartGramFamilyJointSmoothNondegenerate (I := I) (fun _ : ℝ => g₀) α S := by
  refine ⟨?_, ?_⟩
  · intro a b s₀ y₀ _hs hy
    have hsnd : ContDiffAt ℝ ∞ (Prod.snd : ℝ × E → E) (s₀, y₀) := contDiffAt_snd
    exact (((chartGramOnE_contDiffOn (I := I) g₀ α a b).mono interior_subset).contDiffAt
      (isOpen_interior.mem_nhds hy)).comp (s₀, y₀) hsnd
  · intro s₀ _ x hx
    exact chartGramMatrix_det_pos (I := I) g₀ α hx

omit [BoundarylessManifold I M] in
omit [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma bdChartChristoffel_g0_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (α : M) (i j k : Fin (Module.finrank ℝ E)) {S : Set ℝ} :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun p : M × ℝ => chartChristoffel (I := I) g₀ α i j k (extChartAt I α p.1))
      ((chartAt H α).source ×ˢ S) := by
  classical
  have hG := palatiniRefoldGenJointGram_const_g0 (I := I) g₀ α (S := S)
  have hmove : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => (p.2, extChartAt I α p.1))
      ((chartAt H α).source ×ˢ S) := by
    refine ContMDiffOn.prodMk contMDiffOn_snd ?_
    exact (contMDiffOn_extChartAt (I := I) (x := α)).comp contMDiffOn_fst (fun p hp => hp.1)
  intro p hp
  obtain ⟨hx, hs⟩ := hp
  have hxsrc : p.1 ∈ (extChartAt I α).source := by rw [extChartAt_source (I := I)]; exact hx
  have hy : extChartAt I α p.1 ∈ interior (extChartAt I α).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α
      ((extChartAt I α).map_source hxsrc)
  have hentry := gen_joint_christoffel (I := I) (fun _ : ℝ => g₀) α hG i j k hs hy
  have hentryM : ContMDiffAt (𝓘(ℝ, ℝ × E)) 𝓘(ℝ) ∞
      (fun r : ℝ × E => chartChristoffel (I := I) g₀ α i j k r.2) (p.2, extChartAt I α p.1) :=
    hentry.contMDiffAt
  have hmoveAt : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ × E)) ∞
      (fun p : M × ℝ => (p.2, extChartAt I α p.1))
      ((chartAt H α).source ×ˢ S) p := by
    have hm := hmove p ⟨hx, hs⟩
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hm
    exact hm
  exact (hentryM.comp_contMDiffWithinAt p hmoveAt).congr (fun q _ => rfl) rfl

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
private lemma bdRealizedFam_chartGramMatrix_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (α : M) (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun p : M × ℝ => chartGramMatrix (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' p.2) α p.1 i j)
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  have hG := realizedFam_genJointGram_free (I := I) g₀ T T' hδ hδ' α
  have hmove : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => (p.2, extChartAt I α p.1))
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
    refine ContMDiffOn.prodMk contMDiffOn_snd ?_
    exact (contMDiffOn_extChartAt (I := I) (x := α)).comp contMDiffOn_fst (fun p hp => hp.1)
  intro p hp
  obtain ⟨hx, hs⟩ := hp
  have hxsrc : p.1 ∈ (extChartAt I α).source := by rw [extChartAt_source (I := I)]; exact hx
  have hy : extChartAt I α p.1 ∈ interior (extChartAt I α).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α
      ((extChartAt I α).map_source hxsrc)
  have hentry := hG.1 i j hs hy
  have hentryM : ContMDiffAt (𝓘(ℝ, ℝ × E)) 𝓘(ℝ) ∞
      (fun r : ℝ × E => chartGramOnE (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' r.1) α i j r.2) (p.2, extChartAt I α p.1) :=
    hentry.contMDiffAt
  have hmoveAt : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ × E)) ∞
      (fun p : M × ℝ => (p.2, extChartAt I α p.1))
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) p := by
    have hm := hmove p ⟨hx, hs⟩
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hm
    exact hm
  refine (hentryM.comp_contMDiffWithinAt p hmoveAt).congr ?_ ?_
  · intro q hq
    have hqx : q.1 ∈ (extChartAt I α).source := by rw [extChartAt_source (I := I)]; exact hq.1
    rw [Function.comp_apply, chartGramOnE_def, (extChartAt I α).left_inv hqx]
  · rw [Function.comp_apply, chartGramOnE_def, (extChartAt I α).left_inv hxsrc]

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
private lemma connDiffQuadraticCommKernel_realizedFam_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (α : M) (m k u v : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun p : M × ℝ => connDiffIteratedCommKernelBilin (I := I) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1
        (chartBasisVecFiber (I := I) α m p.1) (chartBasisVecFiber (I := I) α k p.1)
        (chartBasisVecFiber (I := I) α u p.1) (chartBasisVecFiber (I := I) α v p.1))
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  classical
  have hΓd : ∀ i j c : Fin (Module.finrank ℝ E),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
        (fun p : M × ℝ =>
          chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) α i j c
              (extChartAt I α p.1) -
            chartChristoffel (I := I) g₀ α i j c (extChartAt I α p.1))
        ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := fun i j c =>
    (realizedFam_chartChristoffel_jointContMDiffOn (I := I) g₀ T T' hδ hδ' α i j c).sub
      (bdChartChristoffel_g0_jointContMDiffOn (I := I) g₀ α i j c)
  have hcomb : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun p : M × ℝ =>
        (∑ c : Fin (Module.finrank ℝ E),
          (chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) α m k c
                (extChartAt I α p.1) -
              chartChristoffel (I := I) g₀ α m k c (extChartAt I α p.1)) *
            ∑ d : Fin (Module.finrank ℝ E),
              (chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) α u c d
                    (extChartAt I α p.1) -
                  chartChristoffel (I := I) g₀ α u c d (extChartAt I α p.1)) *
                chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) α p.1 d v) -
        ∑ c : Fin (Module.finrank ℝ E),
          (chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) α u k c
                (extChartAt I α p.1) -
              chartChristoffel (I := I) g₀ α u k c (extChartAt I α p.1)) *
            ∑ d : Fin (Module.finrank ℝ E),
              (chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) α m c d
                    (extChartAt I α p.1) -
                  chartChristoffel (I := I) g₀ α m c d (extChartAt I α p.1)) *
                chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) α p.1 d v)
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
    refine ContMDiffOn.sub ?_ ?_
    · refine contMDiffOn_finset_sum (fun c _ => ?_)
      refine (hΓd m k c).mul ?_
      refine contMDiffOn_finset_sum (fun d _ => ?_)
      exact (hΓd u c d).mul
        (bdRealizedFam_chartGramMatrix_jointContMDiffOn (I := I) g₀ T T' hδ hδ' α d v)
    · refine contMDiffOn_finset_sum (fun c _ => ?_)
      refine (hΓd u k c).mul ?_
      refine contMDiffOn_finset_sum (fun d _ => ?_)
      exact (hΓd m c d).mul
        (bdRealizedFam_chartGramMatrix_jointContMDiffOn (I := I) g₀ T T' hδ hδ' α d v)
  refine hcomb.congr (fun p hp => ?_)
  have hxgood : p.1 ∈ chartLeviCivitaGoodSet (I := I) α := by
    rw [chartLeviCivitaGoodSet_eq_extChartAt_source (I := I) α, extChartAt_source (I := I)]
    exact hp.1
  rw [connDiffAACommKernelBilin_apply,
    connDiffQuadraticMonomial_chartBasis_eq (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2) α hxgood k m u v,
    connDiffQuadraticMonomial_chartBasis_eq (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2) α hxgood k u m v]

omit [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
private lemma bdAACommBiContrFib_toModel_chartα (g₀ g : SmoothRiemannianMetric I M)
    (α : M) {x : M}
    (hxbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel (connDiffAACommBiContrFib (I := I) g₀ g x D) v =
      ∑ m, ∑ n, chartInvGramMatrix (I := I) g α x m n *
        (∑ k, ∑ l, chartInvGramMatrix (I := I) g α x k l *
          (connDiffIteratedCommKernelBilin (I := I) g₀ g x
              (chartBasisVecFiber (I := I) α m x) (chartBasisVecFiber (I := I) α k x)
              (v 0) (v 1) *
            Tensor0SSpace.toModel D
              ![(chartBasisVecFiber (I := I) α n x : E),
                (chartBasisVecFiber (I := I) α l x : E)])) := by
  classical
  have hBf_on : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x (smoothOrthoFrame (I := I) g x i x) (smoothOrthoFrame (I := I) g x j x) =
        if i = j then (1 : ℝ) else 0 := fun i j =>
    smoothOrthoFrame_orthonormal_at_center (I := I) g x i j
  rw [show connDiffAACommBiContrFib (I := I) g₀ g x =
      connDiffAACommBiContrFibFixedFrame (I := I) g₀ g (smoothOrthoFrame (I := I) g x) x
    from rfl, connDiffAACommBiContrFibFixedFrame_toModel]
  have hsummand : ∀ a b : Fin (Module.finrank ℝ E),
      Tensor0SSpace.toModel D
          ![(smoothOrthoFrame (I := I) g x a x : E), (smoothOrthoFrame (I := I) g x b x : E)] *
        connDiffIteratedCommKernelBilin (I := I) g₀ g x
          (smoothOrthoFrame (I := I) g x a x) (smoothOrthoFrame (I := I) g x b x)
          (v 0) (v 1) =
      frameConnDiffAACommKernel (I := I) g₀ g x (v 0) (v 1)
          (smoothOrthoFrame (I := I) g x a x) (smoothOrthoFrame (I := I) g x b x) *
        (bilinFormToModel (TangentSpace I x)).symm (Tensor0SSpace.toModel D)
          (smoothOrthoFrame (I := I) g x a x) (smoothOrthoFrame (I := I) g x b x) := by
    intro a b
    rw [frameConnDiffAACommKernel_apply,
      bilinFormToModel_symm_apply (TangentSpace I x) (Tensor0SSpace.toModel D) _ _, mul_comm]
    rfl
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => hsummand a b))]
  rw [double_frame_bilin_trace_chartα (I := I) g α hxbase
    (frameConnDiffAACommKernel (I := I) g₀ g x (v 0) (v 1))
    ((bilinFormToModel (TangentSpace I x)).symm (Tensor0SSpace.toModel D))
    (fun a => smoothOrthoFrame (I := I) g x a x) hBf_on]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  refine Finset.sum_congr rfl (fun n _ => ?_)
  refine congrArg (fun t => chartInvGramMatrix (I := I) g α x m n * t) ?_
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine Finset.sum_congr rfl (fun l _ => ?_)
  refine congrArg (fun t => chartInvGramMatrix (I := I) g α x k l * t) ?_
  rw [frameConnDiffAACommKernel_apply,
    bilinFormToModel_symm_apply (TangentSpace I x) (Tensor0SSpace.toModel D) _ _]
  rfl

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
private lemma connDiffQuadraticCommBiContraction_applyY_chartCoord_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (Y : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun x : M => Tensor0SSpace 2 I x⟯)
    (α : M) (σc : Fin 2 → Fin (Module.finrank ℝ E)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun p : M × ℝ => Tensor0SSpace.toModel
        (connDiffAACommBiContrFib (I := I) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1 (Y p.1))
        ![(chartBasisVecFiber (I := I) α (σc 0) p.1 : E),
          (chartBasisVecFiber (I := I) α (σc 1) p.1 : E)])
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  classical
  have hYpair : ∀ n l : Fin (Module.finrank ℝ E),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
        (fun p : M × ℝ => Tensor0SSpace.toModel (Y p.1)
          ![(chartBasisVecFiber (I := I) α n p.1 : E),
            (chartBasisVecFiber (I := I) α l p.1 : E)])
        ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
    intro n l p₀ hp₀
    have hYon : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
          (E := fun z : M => Tensor0SSpace 2 I z) p.1 (Y p.1))
        ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
      (Y.contMDiff.comp_contMDiffOn contMDiffOn_fst).mono (Set.subset_univ _)
    have hv : ∀ i : Fin 2, ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1
          (chartBasisVecFiber (I := I) α
            ((![n, l] : Fin 2 → Fin (Module.finrank ℝ E)) i) p.1))
        ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) p₀ := fun i =>
      (chartBasisVec_jointContMDiffOn (I := I) α
        ((![n, l] : Fin 2 → Fin (Module.finrank ℝ E)) i) p₀
        ⟨hp₀.1, Set.mem_univ _⟩).mono (fun q hq => ⟨hq.1, Set.mem_univ _⟩)
    have happly := TensorMultilinear.contMDiffWithinAt_section_apply_prod (I := I) 2
      (fun b : M => Y b) (hYon p₀ hp₀)
      (fun i => fun b : M => chartBasisVecFiber (I := I) α
        ((![n, l] : Fin 2 → Fin (Module.finrank ℝ E)) i) b) hv
    refine happly.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with q _
      congr 1
      funext i
      fin_cases i <;> rfl
    · congr 1
      funext i
      fin_cases i <;> rfl
  have hcomb : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun p : M × ℝ => ∑ m, ∑ n, chartInvGramMatrix (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' p.2) α p.1 m n *
        (∑ k, ∑ l, chartInvGramMatrix (I := I)
            (realizedFam (I := I) g₀ T T' hδ hδ' p.2) α p.1 k l *
          (connDiffIteratedCommKernelBilin (I := I) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1
              (chartBasisVecFiber (I := I) α m p.1) (chartBasisVecFiber (I := I) α k p.1)
              ((![(chartBasisVecFiber (I := I) α (σc 0) p.1 : E),
                  (chartBasisVecFiber (I := I) α (σc 1) p.1 : E)] : Fin 2 → E) 0)
              ((![(chartBasisVecFiber (I := I) α (σc 0) p.1 : E),
                  (chartBasisVecFiber (I := I) α (σc 1) p.1 : E)] : Fin 2 → E) 1) *
            Tensor0SSpace.toModel (Y p.1)
              ![(chartBasisVecFiber (I := I) α n p.1 : E),
                (chartBasisVecFiber (I := I) α l p.1 : E)])))
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
    refine contMDiffOn_finset_sum (fun m _ => contMDiffOn_finset_sum (fun n _ => ?_))
    refine (realizedFam_chartInvGramMatrix_jointContMDiffOn_free (I := I) g₀ T T'
      hδ hδ' α m n).mul ?_
    refine contMDiffOn_finset_sum (fun k _ => contMDiffOn_finset_sum (fun l _ => ?_))
    refine (realizedFam_chartInvGramMatrix_jointContMDiffOn_free (I := I) g₀ T T'
      hδ hδ' α k l).mul ?_
    exact (connDiffQuadraticCommKernel_realizedFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ'
      α m k (σc 0) (σc 1)).mul (hYpair n l)
  refine hcomb.congr (fun p hp => ?_)
  have hxbase : p.1 ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source (I := I)]
    exact hp.1
  rw [bdAACommBiContrFib_toModel_chartα (I := I) (M := M) g₀
    (realizedFam (I := I) g₀ T T' hδ hδ' p.2) α hxbase]

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
private lemma bdAACommBiContrFibAppY_realizedFam_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (Y : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun x : M => Tensor0SSpace 2 I x⟯) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) p.1
        (connDiffAACommBiContrFib (I := I) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1 (Y p.1)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  classical
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
  set gfam : ℝ → SmoothRiemannianMetric I M :=
    fun s => realizedFam (I := I) g₀ T T' hδ hδ' s with hgfam
  set S := realizedSmallSet (δ := δ) (δ' := δ') with hS
  intro p₀ hp₀
  set α := p₀.1 with hα
  set e := trivializationAt (Tensor0SModel 2 ℝ E)
    (fun z : M => Tensor0SSpace 2 I z) α with he
  set Bcmm := continuousMultilinearMap_basis (𝕜 := ℝ) (F := E) (chartModelBasis E) 2 with hBcmm
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  have hαsrc : α ∈ (chartAt H α).source := mem_chart_source H α
  have hαbase : α ∈ e.baseSet := by
    rw [he]; exact mem_baseSet_trivializationAt _ _ α
  have hnhd : (chartAt H α).source ×ˢ S ∈ nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S) := by
    refine mem_nhdsWithin.mpr ⟨(chartAt H α).source ×ˢ S,
      (chartAt H α).open_source.prod realizedSmallSet_isOpen, ⟨hαsrc, hp₀.2⟩, fun q hq => hq.1⟩
  have hcoordEach : ∀ σc : Fin 2 → Fin (Module.finrank ℝ E),
      ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
        (fun p : M × ℝ => Bcmm.repr
          (e ⟨p.1, connDiffAACommBiContrFib (I := I) g₀ (gfam p.2) p.1 (Y p.1)⟩).2 σc)
        ((Set.univ : Set M) ×ˢ S) p₀ := by
    intro σc
    have hscal := connDiffQuadraticCommBiContraction_applyY_chartCoord_jointContMDiffOn
      (I := I) (M := M) g₀ T T' hδ hδ' Y α σc
    have hscalAt := (hscal p₀ ⟨hαsrc, hp₀.2⟩).mono_of_mem_nhdsWithin hnhd
    have hreadout : ∀ {q : M × ℝ}, q.1 ∈ e.baseSet →
        Bcmm.repr (e ⟨q.1, connDiffAACommBiContrFib (I := I) g₀
            (gfam q.2) q.1 (Y q.1)⟩).2 σc =
          Tensor0SSpace.toModel (connDiffAACommBiContrFib (I := I) g₀
              (gfam q.2) q.1 (Y q.1))
            ![(chartBasisVecFiber (I := I) α (σc 0) q.1 : E),
              (chartBasisVecFiber (I := I) α (σc 1) q.1 : E)] := by
      intro q hqbase
      rw [continuousMultilinearMap_basis_repr]
      have hcoe : (e ⟨q.1, connDiffAACommBiContrFib (I := I) g₀
          (gfam q.2) q.1 (Y q.1)⟩).2 =
          (e.linearMapAt ℝ q.1) (connDiffAACommBiContrFib (I := I) g₀
            (gfam q.2) q.1 (Y q.1)) :=
        (congrFun (Trivialization.coe_linearMapAt_of_mem (R := ℝ) (e := e) hqbase) _).symm
      rw [hcoe]
      have happly := TensorMultilinear.tensor0SBundle_linearMapAt_apply_of_mem (I := I) α q.1
        hqbase
        (connDiffAACommBiContrFib (I := I) g₀ (gfam q.2) q.1 (Y q.1))
        (fun j => (chartModelBasis E) (σc j))
      rw [tensor0SSpace_continuousLinearEquiv_symm_apply] at happly
      rw [happly]
      change Tensor0SSpace.toModel (connDiffAACommBiContrFib (I := I) g₀
          (gfam q.2) q.1 (Y q.1))
          (fun j => (trivializationAt E (TangentSpace I) α).symmL ℝ q.1
            ((chartModelBasis E) (σc j))) = _
      congr 1
      funext j
      fin_cases j <;> rfl
    refine hscalAt.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [hnhd] with q hq
      have hqbaseT : q.1 ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
        rw [trivializationAt_baseSet_eq_chartAt_source (I := I)]; exact hq.1
      have hqbase : q.1 ∈ e.baseSet := by rw [he]; exact hqbaseT
      exact hreadout hqbase
    · exact hreadout hαbase
  have hcoordVec : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, (Fin 2 → Fin (Module.finrank ℝ E)) → ℝ) ∞
      (fun p : M × ℝ => fun σc : Fin 2 → Fin (Module.finrank ℝ E) =>
        Bcmm.repr (e ⟨p.1, connDiffAACommBiContrFib (I := I) g₀
          (gfam p.2) p.1 (Y p.1)⟩).2 σc)
      ((Set.univ : Set M) ×ˢ S) p₀ :=
    contMDiffWithinAt_pi_space.mpr (fun σc => hcoordEach σc)
  have hfinal : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Tensor0SModel 2 ℝ E) ∞
      (fun p : M × ℝ => (e ⟨p.1, connDiffAACommBiContrFib (I := I) g₀
        (gfam p.2) p.1 (Y p.1)⟩).2)
      ((Set.univ : Set M) ×ˢ S) p₀ := by
    have hequiv := (Bcmm.equivFun.symm.toContinuousLinearEquiv.toContinuousLinearMap.contMDiffAt
      (x := Bcmm.equivFun
        (e ⟨p₀.1, connDiffAACommBiContrFib (I := I) g₀
          (gfam p₀.2) p₀.1 (Y p₀.1)⟩).2)).comp_contMDiffWithinAt
      p₀ hcoordVec
    refine hequiv.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with q _
      exact (Bcmm.equivFun.symm_apply_apply _).symm
    · exact (Bcmm.equivFun.symm_apply_apply _).symm
  exact hfinal


omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
theorem connDiffAACommBiContrFib_realizedFam_apply_section_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2) {δ : ℝ}
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ)
    (Y : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun x : M => Tensor0SSpace 2 I x⟯) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) p.1
        (connDiffAACommBiContrFib (I := I) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ p.2) p.1 (Y p.1)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ)) :=
  bdAACommBiContrFibAppY_realizedFam_jointContMDiffOn (I := I) (M := M) g₀ T 0 hδ hδZ Y


theorem ricciArmOrder0AACommCoeffField_realizedFam_threeArmHjoint
    (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2) {δ : ℝ}
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2
      (fun s => ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T 0 hδ hδZ s)) (δ := δ) (δ' := δ) := by
  classical
  have hCLM := contMDiffOn_clm_section_of_pointwise_joint_manifold_time (I := I) (M := M)
    (F₁ := Tensor0SModel 2 ℝ E) (V₁ := fun x : M => Tensor0SSpace 2 I x)
    (F₂ := Tensor0SModel 2 ℝ E) (V₂ := fun x : M => Tensor0SSpace 2 I x)
    (φ := fun p : M × ℝ => connDiffAACommBiContrFib (I := I) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ p.2) p.1)
    (S := realizedSmallSet (δ := δ) (δ' := δ))
    (fun Y => connDiffAACommBiContrFib_realizedFam_apply_section_jointContMDiffOn
      (I := I) (M := M) g₀ T hδ hδZ Y)
  refine hCLM.congr (fun p _ => ?_)
  rfl


theorem ricciArmOrder0BgRCommCoeffField_realizedFam_threeArmHjoint
    (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2) {δ : ℝ}
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2
      (fun s => ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T 0 hδ hδZ s)) (δ := δ) (δ' := δ) := by
  classical
  have hperY : ∀ (Y : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun x : M => Tensor0SSpace 2 I x⟯),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
          (E := fun z : M => Tensor0SSpace 2 I z) p.1
          (backgroundRiemannBiContrFib (I := I) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ p.2) p.1 (Y p.1)))
        ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ)) := by
    intro Y
    have hWapp : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 4 ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (Tensor0SModel 4 ℝ E)
          (E := fun z : M => Tensor0SSpace 4 I z) x
          ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 4 I x from
            (backgroundRiemannCommWeightKernel (I := I) (M := M) g₀).toSection x) (Y x))) :=
      ContMDiff.clm_bundle_apply (b := id)
        (backgroundRiemannCommWeightKernel (I := I) (M := M) g₀).toSection.contMDiff Y.contMDiff
    have hWjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel 4 ℝ E)) ∞
        (fun q : M × ℝ => TotalSpace.mk' (Tensor0SModel 4 ℝ E)
          (E := fun z : M => Tensor0SSpace 4 I z) q.1
          ((show Tensor0SSpace 2 I q.1 →L[ℝ] Tensor0SSpace 4 I q.1 from
            (backgroundRiemannCommWeightKernel (I := I) (M := M) g₀).toSection q.1) (Y q.1)))
        ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ)) :=
      (hWapp.comp_contMDiffOn contMDiffOn_fst).mono (Set.subset_univ _)
    have hcdtf := cometricDoubleTraceFib_realizedFam_jointContMDiffOn (I := I) (p := 2)
      g₀ T 0 hδ hδZ
      (fun q : M × ℝ => (show Tensor0SSpace 2 I q.1 →L[ℝ] Tensor0SSpace 4 I q.1 from
        (backgroundRiemannCommWeightKernel (I := I) (M := M) g₀).toSection q.1) (Y q.1)) hWjoint
    refine hcdtf.congr (fun q _ => ?_)
    refine congrArg (fun t => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
      (E := fun z : M => Tensor0SSpace 2 I z) q.1 t) ?_
    calc backgroundRiemannBiContrFib (I := I) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) q.1 (Y q.1)
        = (show Tensor0SSpace 2 I q.1 →L[ℝ] Tensor0SSpace 2 I q.1 from
            (ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T 0 hδ hδZ q.2)).toSection q.1) (Y q.1) := rfl
      _ = (show Tensor0SSpace 2 I q.1 →L[ℝ] Tensor0SSpace 2 I q.1 from
            (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 2
              (cometricDoubleTraceCc (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) 2)
              (backgroundRiemannCommWeightKernel (I := I) (M := M) g₀)).toSection q.1) (Y q.1) := by
          rw [bdBgRComm_eq_refold (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T 0 hδ hδZ q.2)]
      _ = cometricDoubleTraceFib (I := I)
            (realizedFam (I := I) g₀ T 0 hδ hδZ q.2) 2 q.1
            ((show Tensor0SSpace 2 I q.1 →L[ℝ] Tensor0SSpace 4 I q.1 from
              (backgroundRiemannCommWeightKernel (I := I) (M := M) g₀).toSection q.1) (Y q.1)) := by
          rw [appCcRS_toSection]
          rfl
  have hCLM := contMDiffOn_clm_section_of_pointwise_joint_manifold_time (I := I) (M := M)
    (F₁ := Tensor0SModel 2 ℝ E) (V₁ := fun x : M => Tensor0SSpace 2 I x)
    (F₂ := Tensor0SModel 2 ℝ E) (V₂ := fun x : M => Tensor0SSpace 2 I x)
    (φ := fun p : M × ℝ => backgroundRiemannBiContrFib (I := I) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ p.2) p.1)
    (S := realizedSmallSet (δ := δ) (δ' := δ)) hperY
  refine hCLM.congr (fun p _ => ?_)
  rfl

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
