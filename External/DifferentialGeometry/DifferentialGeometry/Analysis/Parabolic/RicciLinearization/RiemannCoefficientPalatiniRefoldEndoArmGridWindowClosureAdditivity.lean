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


omit [I.Boundaryless] in
theorem covDerivArmField_eq_dLaCoeffField
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    deTurckLieCovDerivArmField (I := I) (M := M) g₀ g₁ g_bg =
      deTurckLieConnDiffDerivCoeffField (I := I) (M := M) g₀ g₁ g_bg := by
  apply SmoothCcTensor.ext
  refine ContMDiffSection.ext (fun x => ?_)
  rfl


omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem endoArmField_eq_dLbCoeffField
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    deTurckLieEndoArmField (I := I) (M := M) g₀ g₁ g_bg =
      deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g_bg := by
  apply SmoothCcTensor.ext
  refine ContMDiffSection.ext (fun x => ?_)
  rfl


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem threeArmHjoint_add_local (g₀ : SmoothRiemannianMetric I M) {r : ℕ}
    (A B : ℝ → SmoothCcTensor g₀ r 2) {δ δ' : ℝ}
    (hA : linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ r A (δ := δ) (δ' := δ'))
    (hB : linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ r B (δ := δ) (δ' := δ')) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ r
      (fun s => A s + B s) (δ := δ) (δ' := δ') := by
  have hadd := jointTotalSpaceRS_add_local (I := I) (M := M) (r := r) (s := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun p : M × ℝ => (A p.2).toSection p.1)
    (fun p : M × ℝ => (B p.2).toSection p.1)
    hA hB
  refine hadd.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r 2 I z) p.1 t) ?_
  rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem threeArmHjoint_sub_local (g₀ : SmoothRiemannianMetric I M) {r : ℕ}
    (A B : ℝ → SmoothCcTensor g₀ r 2) {δ δ' : ℝ}
    (hA : linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ r A (δ := δ) (δ' := δ'))
    (hB : linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ r B (δ := δ) (δ' := δ')) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ r
      (fun s => A s - B s) (δ := δ) (δ' := δ') := by
  have hsub := jointTotalSpaceRS_sub_local (I := I) (M := M) (r := r) (s := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun p : M × ℝ => (A p.2).toSection p.1)
    (fun p : M × ℝ => (B p.2).toSection p.1)
    hA hB
  refine hsub.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r 2 I z) p.1 t) ?_
  rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]


theorem covDerivArmField_realizedFam_threeArmHjoint
    (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2) {δ : ℝ}
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ)
    (g_bg : SmoothRiemannianMetric I M) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2
      (fun s => deTurckLieCovDerivArmField (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T 0 hδ hδZ s) g_bg) (δ := δ) (δ' := δ) := by
  have h := dLaBiContrFib_realizedFam_jointContMDiffOn (I := I) (M := M)
    g₀ T 0 hδ hδZ g_bg
  refine h.congr (fun p _ => ?_)
  rfl


theorem endoArmField_realizedFam_threeArmHjoint
    (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2) {δ : ℝ}
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ)
    (g_bg : SmoothRiemannianMetric I M) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2
      (fun s => deTurckLieEndoArmField (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T 0 hδ hδZ s) g_bg) (δ := δ) (δ' := δ) := by
  have hC := deTurckLieCoeffField_realizedFam_jointContMDiff (I := I)
    g₀ T 0 hδ hδZ g_bg
  have hA := covDerivArmField_realizedFam_threeArmHjoint (I := I) (M := M)
    g₀ T hδ hδZ g_bg
  have hsub := jointTotalSpaceRS_sub_local (I := I) (M := M) (r := 2) (s := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ))
    (fun p : M × ℝ => (deTurckLieCoeffField (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ p.2) g_bg).toSection p.1)
    (fun p : M × ℝ => (deTurckLieCovDerivArmField (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ p.2) g_bg).toSection p.1)
    hC hA
  refine hsub.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 2 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace 2 2 I z) p.1 t) ?_
  change (deTurckLieEndoArmField (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ p.2) g_bg).toSection p.1 =
    (deTurckLieCoeffField (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T 0 hδ hδZ p.2) g_bg).toSection p.1
      - (deTurckLieCovDerivArmField (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T 0 hδ hδZ p.2) g_bg).toSection p.1
  have hsplit : deTurckLieEndoArmField (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ p.2) g_bg =
      deTurckLieCoeffField (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ p.2) g_bg
        - deTurckLieCovDerivArmField (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ p.2) g_bg := by
    rw [eq_sub_iff_add_eq, add_comm]
    exact (deTurckLieCoeffField_eq_covDerivArm_add_endoArm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ p.2) g_bg).symm
  rw [hsplit, SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]


omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem iteratedCovGrad_smul_real (g : SmoothRiemannianMetric I M) (r s j : ℕ)
    (c : ℝ) (w : SmoothCcTensor g r s) :
    iteratedCovGrad (I := I) g r s j (c • w) =
      c • iteratedCovGrad (I := I) g r s j w := by
  induction j with
  | zero => simp only [iteratedCovGrad_zero]
  | succ j ih => rw [iteratedCovGrad_succ, iteratedCovGrad_succ, ih, covGrad_smul]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem bdExists_fixedField_rfns_jet (g₀ : SmoothRiemannianMetric I M)
    (r s : ℕ) (F : SmoothCcTensor g₀ r s) :
    ∃ c : ℕ → ℝ, (∀ j, 0 ≤ c j) ∧ ∀ (j : ℕ) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ r (s + j) x
        ((iteratedCovGrad (I := I) g₀ r s j F).toSection x) ≤ c j := by
  have hex : ∀ j : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ r (s + j) x
        ((iteratedCovGrad (I := I) g₀ r s j F).toSection x) ≤ c :=
    fun j => exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ r (s + j)
      (iteratedCovGrad (I := I) g₀ r s j F)
  choose c hc_nn hc using hex
  exact ⟨c, hc_nn, fun j x => hc j x⟩

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma bdRfns_iCG_add_le (g : SmoothRiemannianMetric I M) (r s : ℕ) (j : ℕ)
    (A B : SmoothCcTensor g r s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r (s + j) x
        ((iteratedCovGrad (I := I) g r s j (A + B)).toSection x) ≤
      2 * riemannianFiberNormSq (I := I) (M := M) g r (s + j) x
          ((iteratedCovGrad (I := I) g r s j A).toSection x) +
        2 * riemannianFiberNormSq (I := I) (M := M) g r (s + j) x
          ((iteratedCovGrad (I := I) g r s j B).toSection x) := by
  have hsec : (iteratedCovGrad (I := I) g r s j (A + B)).toSection x =
      (iteratedCovGrad (I := I) g r s j A).toSection x +
        (iteratedCovGrad (I := I) g r s j B).toSection x := by
    rw [iteratedCovGrad_add, SmoothCcTensor.toSection_add]
    rfl
  rw [hsec]
  exact riemannianFiberNormSq_add_le (I := I) (M := M) g r (s + j) x _ _

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma bdAppCcRS_sub_right (g : SmoothRiemannianMetric I M) (a b c : ℕ)
    (Φ : SmoothCcTensor g b c) (W₁ W₂ : SmoothCcTensor g a b) :
    ccOperatorFieldComp (I := I) (M := M) g a b c Φ (W₁ - W₂) =
      ccOperatorFieldComp (I := I) (M := M) g a b c Φ W₁ - ccOperatorFieldComp (I := I) (M := M) g a b c Φ W₂ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  rw [show ((ccOperatorFieldComp (I := I) (M := M) g a b c Φ W₁ -
        ccOperatorFieldComp (I := I) (M := M) g a b c Φ W₂).toSection x) =
      (ccOperatorFieldComp (I := I) (M := M) g a b c Φ W₁).toSection x -
        (ccOperatorFieldComp (I := I) (M := M) g a b c Φ W₂).toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  rw [ContinuousLinearMap.sub_apply]
  rw [show ((ccOperatorFieldComp (I := I) (M := M) g a b c Φ (W₁ - W₂)).toSection x) D =
      ((show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φ.toSection x)
        ((show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from (W₁ - W₂).toSection x) D))
      from by
    rw [appCcRS_toSection]
    rfl]
  rw [show ((ccOperatorFieldComp (I := I) (M := M) g a b c Φ W₁).toSection x) D =
      ((show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φ.toSection x)
        ((show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from W₁.toSection x) D)) from by
    rw [appCcRS_toSection]
    rfl]
  rw [show ((ccOperatorFieldComp (I := I) (M := M) g a b c Φ W₂).toSection x) D =
      ((show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φ.toSection x)
        ((show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from W₂.toSection x) D)) from by
    rw [appCcRS_toSection]
    rfl]
  rw [show ((W₁ - W₂).toSection x) = W₁.toSection x - W₂.toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  rw [show ((show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from
      W₁.toSection x - W₂.toSection x) D) =
      (show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from W₁.toSection x) D -
        (show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from W₂.toSection x) D from rfl]
  rw [map_sub]

private def bdVFSec (g₁ gA gB : SmoothRiemannianMetric I M) :
    Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
  (PDE.DeTurck.deTurckVF (I := I) g₁ gA : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) -
    (PDE.DeTurck.deTurckVF (I := I) g₁ gB : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma bdVFSec_apply (g₁ gA gB : SmoothRiemannianMetric I M) (b : M) :
    bdVFSec (I := I) (M := M) g₁ gA gB b =
      (PDE.DeTurck.deTurckVF (I := I) g₁ gA :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) b -
        (PDE.DeTurck.deTurckVF (I := I) g₁ gB :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) b := by
  rw [bdVFSec, ContMDiffSection.coe_sub, Pi.sub_apply]

def bdXiFix (g₀ g_bg : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 3 :=
  connDiffLoweredCc (I := I) g₀ g₀ - connDiffLoweredCc (I := I) g₀ g_bg

private def bdOmegaGen (g₀ g₁ gc : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 1 :=
  ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 1 (cometricDoubleTraceCastG0 (I := I) g₀ g₁)
    (connDiffLoweredCc (I := I) g₀ g₁ - connDiffLoweredCc (I := I) g₀ gc)

def bdOmega (g₀ g₁ g_bg : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 1 :=
  ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 1 (cometricDoubleTraceCastG0 (I := I) g₀ g₁)
    (bdXiFix (I := I) (M := M) g₀ g_bg)

omit [NeZero (Module.finrank ℝ E)] in
private lemma bdOmega_eq_sub (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    bdOmega (I := I) (M := M) g₀ g₁ g_bg =
      bdOmegaGen (I := I) (M := M) g₀ g₁ g_bg - bdOmegaGen (I := I) (M := M) g₀ g₁ g₀ := by
  rw [bdOmegaGen, bdOmegaGen, ← bdAppCcRS_sub_right, bdOmega]
  congr 1
  rw [bdXiFix]
  abel

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma bdUnitModel_sub (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (A B : SmoothCcTensor g₀ 0 s) (x : M) :
    unitModel (I := I) (M := M) g₀ s (A - B) x =
      unitModel (I := I) (M := M) g₀ s A x - unitModel (I := I) (M := M) g₀ s B x := by
  simp only [unitModel]
  rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
    ContinuousLinearMap.sub_apply, Tensor0SSpace.toModel_sub]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma bdUnitModel_add (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (A B : SmoothCcTensor g₀ 0 s) (x : M) :
    unitModel (I := I) (M := M) g₀ s (A + B) x =
      unitModel (I := I) (M := M) g₀ s A x + unitModel (I := I) (M := M) g₀ s B x := by
  simp only [unitModel]
  rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply,
    ContinuousLinearMap.add_apply, Tensor0SSpace.toModel_add]

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma bdConnDiffLoweredCc_unitModel (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    unitModel (I := I) (M := M) g₀ 3 (connDiffLoweredCc (I := I) g₀ g₁) x =
      Tensor0SSpace.toModel (connDiffLoweredCovec (I := I) g₀ g₁ x) := by
  rw [unitModel]
  rw [show (connDiffLoweredCc (I := I) g₀ g₁).toSection x (unitTensor (I := I) (M := M) x) =
      (MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (connDiffLoweredField (I := I) g₀ g₁ x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))
      from rfl]
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  rfl

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma bdConnDiffLoweredCc_unitModel_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (m : Fin 3 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 3 (connDiffLoweredCc (I := I) g₀ g₁) x m =
      g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 0) (m 1)) (m 2) := by
  rw [bdConnDiffLoweredCc_unitModel]
  rfl

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma bdXiGen_unitModel_apply (g₀ g₁ gc : SmoothRiemannianMetric I M) (x : M)
    (m : Fin 3 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 3
        (connDiffLoweredCc (I := I) g₀ g₁ - connDiffLoweredCc (I := I) g₀ gc) x m =
      g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ gc x (m 0) (m 1)) (m 2) := by
  rw [bdUnitModel_sub, ContinuousMultilinearMap.sub_apply,
    bdConnDiffLoweredCc_unitModel_apply, bdConnDiffLoweredCc_unitModel_apply]
  rw [show g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 0) (m 1)) (m 2) -
        g₀.inner x (PDE.DeTurck.connDiff (I := I) gc g₀ x (m 0) (m 1)) (m 2) =
      g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 0) (m 1) -
        PDE.DeTurck.connDiff (I := I) gc g₀ x (m 0) (m 1)) (m 2) from by
    rw [map_sub, ContinuousLinearMap.sub_apply]]
  rw [connDiff_endpoint_cocycle (I := I) g₀ g₁ gc x (m 0) (m 1)]

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma bdOmegaGen_toSection_unit (g₀ g₁ gc : SmoothRiemannianMetric I M) (x : M) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 1 I x from
        (bdOmegaGen (I := I) (M := M) g₀ g₁ gc).toSection x)
      (unitTensor (I := I) (M := M) x) =
      cometricDoubleTraceFib (I := I) g₁ 1 x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
          (connDiffLoweredCc (I := I) g₀ g₁ - connDiffLoweredCc (I := I) g₀ gc).toSection x)
          (unitTensor (I := I) (M := M) x)) := by
  rw [bdOmegaGen, appCcRS_toSection]
  rfl

omit [SigmaCompactSpace M] in
private lemma bdOmegaGen_unitModel_apply (g₀ g₁ gc : SmoothRiemannianMetric I M) (x : M)
    (z : TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 1 (bdOmegaGen (I := I) (M := M) g₀ g₁ gc) x
        (fun _ : Fin 1 => z) =
      g₀.inner x ((PDE.DeTurck.deTurckVF (I := I) g₁ gc :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) z := by
  classical
  rw [unitModel, bdOmegaGen_toSection_unit]
  set D : Tensor0SSpace 3 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
      (connDiffLoweredCc (I := I) g₀ g₁ - connDiffLoweredCc (I := I) g₀ gc).toSection x)
      (unitTensor (I := I) (M := M) x) with hD
  have hdiag := cometricDoubleTraceFib_eq_orthoFrame_diag (I := I) g₁ 1 x
    (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x) D
  rw [hdiag]
  rw [show Tensor0SSpace.toModel
        (∑ i : Fin (Module.finrank ℝ E),
          tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x
            (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x D
              (smoothOrthoFrame (I := I) g₁ x i x))
            (smoothOrthoFrame (I := I) g₁ x i x)) =
      ∑ i : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x
            (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x D
              (smoothOrthoFrame (I := I) g₁ x i x))
            (smoothOrthoFrame (I := I) g₁ x i x)) from
    map_sum (tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) 1 x) _ _]
  rw [ContinuousMultilinearMap.sum_apply]
  have hterm : ∀ i : Fin (Module.finrank ℝ E),
      Tensor0SSpace.toModel
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x
            (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x D
              (smoothOrthoFrame (I := I) g₁ x i x))
            (smoothOrthoFrame (I := I) g₁ x i x)) (fun _ : Fin 1 => z) =
        g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ gc x
          (smoothOrthoFrame (I := I) g₁ x i x)
          (smoothOrthoFrame (I := I) g₁ x i x)) z := by
    intro i
    rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x D
        (smoothOrthoFrame (I := I) g₁ x i x))
      (v0 := smoothOrthoFrame (I := I) g₁ x i x) (vs := fun _ : Fin 1 => z)]
    rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := D) (v0 := smoothOrthoFrame (I := I) g₁ x i x)
      (vs := Fin.cons (show E from smoothOrthoFrame (I := I) g₁ x i x)
        (fun _ : Fin 1 => (show E from z)))]
    have hm : Tensor0SSpace.toModel D
        (Fin.cons (show E from smoothOrthoFrame (I := I) g₁ x i x)
          (Fin.cons (show E from smoothOrthoFrame (I := I) g₁ x i x)
            (fun _ : Fin 1 => (show E from z)))) =
        unitModel (I := I) (M := M) g₀ 3
          (connDiffLoweredCc (I := I) g₀ g₁ - connDiffLoweredCc (I := I) g₀ gc) x
          ![smoothOrthoFrame (I := I) g₁ x i x, smoothOrthoFrame (I := I) g₁ x i x, z] := by
      rw [unitModel, ← hD]
      congr 1
      funext k
      fin_cases k <;> rfl
    rw [hm, bdXiGen_unitModel_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  rw [show (∑ i : Fin (Module.finrank ℝ E),
        g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ gc x
          (smoothOrthoFrame (I := I) g₁ x i x)
          (smoothOrthoFrame (I := I) g₁ x i x)) z) =
      g₀.inner x (∑ i : Fin (Module.finrank ℝ E),
        PDE.DeTurck.connDiff (I := I) g₁ gc x
          (smoothOrthoFrame (I := I) g₁ x i x)
          (smoothOrthoFrame (I := I) g₁ x i x)) z from by
    rw [map_sum, ContinuousLinearMap.sum_apply]]
  rw [← PDE.DeTurck.deTurckVF_eq_orthoFrame_trace (I := I) g₁ gc x]

private lemma bdOmega_unitModel_apply (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (z : TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 1 (bdOmega (I := I) (M := M) g₀ g₁ g_bg) x
        (fun _ : Fin 1 => z) =
      g₀.inner x (bdVFSec (I := I) (M := M) g₁ g_bg g₀ x) z := by
  rw [bdOmega_eq_sub, bdUnitModel_sub, ContinuousMultilinearMap.sub_apply,
    bdOmegaGen_unitModel_apply, bdOmegaGen_unitModel_apply, bdVFSec_apply]
  rw [map_sub, ContinuousLinearMap.sub_apply]

def bdAlphaA (g₀ g₁ g_bg : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 2 :=
  domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
    (covGrad (I := I) (M := M) g₀ 0 1 (bdOmega (I := I) (M := M) g₀ g₁ g_bg))

def bdCA (g₀ g₁ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 1 2 :=
  cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
    (domDomCongrSection (I := I) g₀ (Equiv.swap (1 : Fin 3) 2)
      (connDiffLoweredCc (I := I) g₀ g₁))

def bdAlphaB (g₀ g₁ g_bg : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 2 :=
  ccOperatorFieldComp (I := I) (M := M) g₀ 0 1 2 (bdCA (I := I) (M := M) g₀ g₁)
    (bdOmega (I := I) (M := M) g₀ g₁ g_bg)

def bdAlpha (g₀ g₁ g_bg : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 2 :=
  bdAlphaA (I := I) (M := M) g₀ g₁ g_bg + bdAlphaB (I := I) (M := M) g₀ g₁ g_bg

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma bdTensor0SCovDeriv01_consEval_leibnizDefect
    (g₀ : SmoothRiemannianMetric I M) (V : Π b : M, Tensor0SSpace 1 I b) {x : M}
    (hV : TensorSectionMDiffAt (I := I) 1 V x)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (v : TangentSpace I x) :
    Tensor0SSpace.toModel
        (Tensor0SNabla.tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g₀) V x v)
        (Fin.cons (Y x) (fun i => Fin.elim0 i)) =
      directionalDeriv (I := I)
          (fun b : M =>
            Tensor0SSpace.toModel (V b) (Fin.cons (Y b) (fun i => Fin.elim0 i))) x v
        - Tensor0SSpace.toModel (V x)
            (Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => Y b) x v)
              (fun i => Fin.elim0 i)) := by
  classical
  have hpeel := tensor0SCovariantDerivative_succ_consEval_peel
    (I := I) (M := M) g₀ 0 V hV Y v (fun i => Fin.elim0 i)
  have hbase : Tensor0SSpace.toModel
      (Tensor0SNabla.tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g₀)
        (fun y : M => Tensor0SNabla.curriedSection I M V y (Y y)) x v)
      (fun i => Fin.elim0 i) =
      directionalDeriv (I := I)
        (fun b : M =>
          Tensor0SSpace.toModel (V b) (Fin.cons (Y b) (fun i => Fin.elim0 i))) x v := by
    rw [tensor0SCovariantDerivative_zero_toModel_apply (I := I) (M := M) g₀
      (fun b : M => Tensor0SNabla.curriedSection I M V b (Y b)) x v]
    have hfun : Tensor0SNabla.scalarFn I M
        (fun b : M => Tensor0SNabla.curriedSection I M V b (Y b)) =
        (fun b : M =>
          Tensor0SSpace.toModel (V b) (Fin.cons (Y b) (fun i => Fin.elim0 i))) := by
      funext b
      rw [scalarFn_eq_toModel_elim0 (I := I) (M := M)]
      rw [Tensor0SNabla.curriedSection_apply (s := 0) (T := V)]
      rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
        (T := V b) (v0 := Y b) (vs := (fun i => Fin.elim0 i))]
    rw [hfun]
  rw [hpeel, hbase]

open DifferentialGeometry.Analysis.Sobolev.TensorHilbert (g0FlatCLM cotangentToDual_g0FlatCLM inverseMetricSharpFib_g0FlatCLM) in
private lemma bdOmega_toSection_unit_eq_flat (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (x : M) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 1 I x from
        (bdOmega (I := I) (M := M) g₀ g₁ g_bg).toSection x)
      (unitTensor (I := I) (M := M) x) =
      g0FlatCLM (I := I) g₀ x (bdVFSec (I := I) (M := M) g₁ g_bg g₀ x) := by
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  have hm : m = fun _ : Fin 1 => m 0 := by
    funext k; fin_cases k; rfl
  rw [hm]
  have hL : Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 1 I x from
        (bdOmega (I := I) (M := M) g₀ g₁ g_bg).toSection x)
        (unitTensor (I := I) (M := M) x)) (fun _ : Fin 1 => m 0) =
      g₀.inner x (bdVFSec (I := I) (M := M) g₁ g_bg g₀ x) (m 0) :=
    bdOmega_unitModel_apply (I := I) (M := M) g₀ g₁ g_bg x (m 0)
  rw [hL]
  have hR : Tensor0SSpace.toModel
      (g0FlatCLM (I := I) g₀ x (bdVFSec (I := I) (M := M) g₁ g_bg g₀ x))
      (fun _ : Fin 1 => m 0) =
      cotangentToDual (I := I)
        (g0FlatCLM (I := I) g₀ x (bdVFSec (I := I) (M := M) g₁ g_bg g₀ x)) (m 0) := by
    rw [cotangentToDual_apply]
    rfl
  rw [hR, cotangentToDual_g0FlatCLM]

open DifferentialGeometry.Analysis.Sobolev.TensorHilbert (g0FlatCLM cotangentToDual_g0FlatCLM inverseMetricSharpFib_g0FlatCLM) in
private lemma bdUnitEvalSection_bdOmega_toModel (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (b : M) (z : TangentSpace I b) :
    Tensor0SSpace.toModel (unitEvalSection (I := I) (M := M) g₀ 1
        (bdOmega (I := I) (M := M) g₀ g₁ g_bg) b)
      (Fin.cons (show E from z) (fun i => Fin.elim0 i)) =
      g₀.inner b (bdVFSec (I := I) (M := M) g₁ g_bg g₀ b) z := by
  rw [unitEvalSection_apply]
  rw [show (unitZeroSec (I := I) (M := M) b) = unitTensor (I := I) (M := M) b from rfl]
  rw [bdOmega_toSection_unit_eq_flat]
  have h : Tensor0SSpace.toModel
      (g0FlatCLM (I := I) g₀ b (bdVFSec (I := I) (M := M) g₁ g_bg g₀ b))
      (Fin.cons (show E from z) (fun i => Fin.elim0 i)) =
      cotangentToDual (I := I)
        (g0FlatCLM (I := I) g₀ b (bdVFSec (I := I) (M := M) g₁ g_bg g₀ b)) z := by
    rw [cotangentToDual_apply]
    change Tensor0SSpace.toModel
        (g0FlatCLM (I := I) g₀ b (bdVFSec (I := I) (M := M) g₁ g_bg g₀ b))
        (Fin.cons (show E from z) (fun i => Fin.elim0 i)) =
      Tensor0SSpace.toModel
        (g0FlatCLM (I := I) g₀ b (bdVFSec (I := I) (M := M) g₁ g_bg g₀ b))
        (fun _ : Fin 1 => (show E from z))
    congr 1
    funext k
    refine Fin.cases rfl (fun j => j.elim0) k
  rw [h, cotangentToDual_g0FlatCLM]

private lemma bdAlphaA_unitModel_apply (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (u w : TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2 (bdAlphaA (I := I) (M := M) g₀ g₁ g_bg) x ![u, w] =
      g₀.inner x
        ((LeviCivita (I := I) g₀).toFun
          (fun b => bdVFSec (I := I) (M := M) g₁ g_bg g₀ b) x w) u := by
  classical
  obtain ⟨Y, hYx⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
    (F := E) (V := (TangentSpace I : M → Type _)) x u
  rw [bdAlphaA, domDomCongrSection_unitModel, ContinuousMultilinearMap.domDomCongr_apply]
  rw [show (fun i => (![u, w] : Fin 2 → TangentSpace I x) ((Equiv.swap (0 : Fin 2) 1) i)) =
      ![w, u] from by
    funext i; fin_cases i <;> simp]
  rw [unitModel]
  rw [covGrad_toSection_apply_eval (I := I) (M := M) g₀ 0 1
    (bdOmega (I := I) (M := M) g₀ g₁ g_bg) x (unitTensor (I := I) (M := M) x) ![w, u]]
  rw [show (![w, u] : Fin 2 → TangentSpace I x) 0 = w from rfl]
  rw [show Matrix.vecTail (![w, u] : Fin 2 → TangentSpace I x) = ![u] from by
    funext k
    refine Fin.cases rfl (fun j => j.elim0) k]
  rw [tensorCovDerivAt_def (I := I) (M := M) g₀ 0 1
    (bdOmega (I := I) (M := M) g₀ g₁ g_bg) x w]
  rw [show unitTensor (I := I) (M := M) x = unitZeroSec (I := I) (M := M) x from rfl]
  rw [covDeriv_unit_eval_eq_genVal (I := I) (M := M) g₀ 1
    (bdOmega (I := I) (M := M) g₀ g₁ g_bg).toSection x w]
  have hV : TensorSectionMDiffAt (I := I) 1
      (unitEvalSection (I := I) (M := M) g₀ 1 (bdOmega (I := I) (M := M) g₀ g₁ g_bg)) x :=
    ((contMDiff_unitEvalSection (I := I) (M := M) g₀ 1
      (bdOmega (I := I) (M := M) g₀ g₁ g_bg)) x).mdifferentiableAt (by simp)
  have hgen : (fun y : M =>
      (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 1 I y from
        (bdOmega (I := I) (M := M) g₀ g₁ g_bg).toSection y)
        (unitZeroSec (I := I) (M := M) y)) =
      unitEvalSection (I := I) (M := M) g₀ 1 (bdOmega (I := I) (M := M) g₀ g₁ g_bg) := rfl
  rw [hgen]
  rw [show (![u] : Fin 1 → TangentSpace I x) =
      Fin.cons (Y x) (fun i => Fin.elim0 i) from by
    funext k
    refine Fin.cases ?_ (fun j => j.elim0) k
    rw [hYx]; rfl]
  rw [bdTensor0SCovDeriv01_consEval_leibnizDefect (I := I) (M := M) g₀
    (unitEvalSection (I := I) (M := M) g₀ 1 (bdOmega (I := I) (M := M) g₀ g₁ g_bg)) hV Y w]
  have hscal : (fun b : M =>
      Tensor0SSpace.toModel
        (unitEvalSection (I := I) (M := M) g₀ 1 (bdOmega (I := I) (M := M) g₀ g₁ g_bg) b)
        (Fin.cons (Y b) (fun i => Fin.elim0 i))) =
      (fun b : M => g₀.inner b (bdVFSec (I := I) (M := M) g₁ g_bg g₀ b) (Y b)) := by
    funext b
    exact bdUnitEvalSection_bdOmega_toModel (I := I) (M := M) g₀ g₁ g_bg b (Y b)
  rw [hscal, directionalDeriv_eq]
  have hlei := leibniz_inner (I := I) (M := M) g₀
    (V := fun b => bdVFSec (I := I) (M := M) g₁ g_bg g₀ b) (W := fun b => Y b)
    (bdVFSec (I := I) (M := M) g₁ g_bg g₀).contMDiff Y.contMDiff (x := x) w
  rw [hlei]
  rw [show Tensor0SSpace.toModel
      (unitEvalSection (I := I) (M := M) g₀ 1 (bdOmega (I := I) (M := M) g₀ g₁ g_bg) x)
      (Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => Y b) x w)
        (fun i => Fin.elim0 i)) =
      g₀.inner x (bdVFSec (I := I) (M := M) g₁ g_bg g₀ x)
        ((LeviCivita (I := I) g₀).toFun (fun b => Y b) x w) from
    bdUnitEvalSection_bdOmega_toModel (I := I) (M := M) g₀ g₁ g_bg x _]
  rw [hYx]
  ring

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma bdInterior_product_toModel_eval (s : ℕ) (x : M) (v : TangentSpace I x)
    (D : Tensor0SSpace (s + 1) I x) (w : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel
        (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) s x v D) w =
      Tensor0SSpace.toModel D (Fin.cons (show E from v) (fun k => (show E from w k))) := by
  have h1 : Tensor0SSpace.toModel
      (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) s x v D) =
      Tensor0SBundle.model_interior_product (𝕜 := ℝ) (E := E) s (show E from v)
        (Tensor0SSpace.toModel D) := rfl
  rw [h1]
  rfl

open DifferentialGeometry.Analysis.Sobolev.TensorHilbert (g0FlatCLM cotangentToDual_g0FlatCLM inverseMetricSharpFib_g0FlatCLM) in
private lemma bdAlphaB_unitModel_apply (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (u w : TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2 (bdAlphaB (I := I) (M := M) g₀ g₁ g_bg) x ![u, w] =
      g₀.inner x
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (bdVFSec (I := I) (M := M) g₁ g_bg g₀ x) w) u := by
  classical
  rw [unitModel, bdAlphaB, appCcRS_toSection]
  rw [ContinuousLinearMap.comp_apply]
  rw [bdOmega_toSection_unit_eq_flat (I := I) (M := M) g₀ g₁ g_bg x]
  rw [bdCA, cometricRaiseSlot0Field_toSection]
  set D : Tensor0SSpace 3 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
      (domDomCongrSection (I := I) g₀ (Equiv.swap (1 : Fin 3) 2)
        (connDiffLoweredCc (I := I) g₀ g₁)).toSection x)
      (unitTensor (I := I) (M := M) x) with hD
  rw [cometricRaiseSlot0Fib_clm_apply (I := I) g₀ 1 x D
    (g0FlatCLM (I := I) g₀ x (bdVFSec (I := I) (M := M) g₁ g_bg g₀ x))]
  rw [inverseMetricSharpFib_g0FlatCLM (I := I) g₀ x (bdVFSec (I := I) (M := M) g₁ g_bg g₀ x)]
  rw [bdInterior_product_toModel_eval (I := I) (M := M) (1 + 1) x
    (bdVFSec (I := I) (M := M) g₁ g_bg g₀ x) D ![u, w]]
  have hDm : Tensor0SSpace.toModel D
      (Fin.cons (show E from bdVFSec (I := I) (M := M) g₁ g_bg g₀ x)
        (fun k : Fin 2 => (show E from (![u, w] : Fin 2 → TangentSpace I x) k))) =
      unitModel (I := I) (M := M) g₀ 3
        (domDomCongrSection (I := I) g₀ (Equiv.swap (1 : Fin 3) 2)
          (connDiffLoweredCc (I := I) g₀ g₁)) x
        ![bdVFSec (I := I) (M := M) g₁ g_bg g₀ x, u, w] := by
    rw [unitModel, ← hD]
    rfl
  rw [hDm, domDomCongrSection_unitModel, ContinuousMultilinearMap.domDomCongr_apply]
  rw [show (fun i => (![bdVFSec (I := I) (M := M) g₁ g_bg g₀ x, u, w] :
        Fin 3 → TangentSpace I x)
        ((Equiv.swap (1 : Fin 3) 2) i)) =
      ![bdVFSec (I := I) (M := M) g₁ g_bg g₀ x, w, u] from by
    funext i; fin_cases i <;> simp [Equiv.swap_apply_def]]
  rw [bdConnDiffLoweredCc_unitModel_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
private lemma bdLeviCivita_toFun_sub (g₀ : SmoothRiemannianMetric I M)
    (A B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (w : TangentSpace I x) :
    (LeviCivita (I := I) g₀).toFun (fun b => A b - B b) x w =
      (LeviCivita (I := I) g₀).toFun (fun b => A b) x w -
        (LeviCivita (I := I) g₀).toFun (fun b => B b) x w := by
  have hsub : (fun b : M => A b - B b) =
      (fun b : M => A b) + (fun b : M => ((-1 : ℝ) • B) b) := by
    funext b
    rw [Pi.add_apply, ContMDiffSection.coe_smul, Pi.smul_apply, neg_one_smul,
      sub_eq_add_neg]
  have hadd := (LeviCivita (I := I) g₀).isCovariantDerivativeOnUniv.add
    (σ := fun b : M => A b) (σ' := fun b : M => ((-1 : ℝ) • B) b) (x := x)
    (A.mdifferentiableAt (x := x)) (((-1 : ℝ) • B).mdifferentiableAt (x := x))
  have hsmul := (LeviCivita (I := I) g₀).isCovariantDerivativeOnUniv.smul_const
    (σ := fun b : M => B b) (a := (-1 : ℝ)) (x := x) (B.mdifferentiableAt (x := x))
  have hcoe : (fun b : M => ((-1 : ℝ) • B) b) = (-1 : ℝ) • (fun b : M => B b) := by
    funext b
    rw [ContMDiffSection.coe_smul]
  rw [hsub, hadd]
  rw [hcoe, hsmul]
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, neg_one_smul,
    sub_eq_add_neg]

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma bdWEndo_eq_covDeriv_add_connDiff (g₀ g₁ gc : SmoothRiemannianMetric I M)
    (x : M) (w : TangentSpace I x) :
    deTurckLieWEndo (I := I) g₁ gc x w =
      (LeviCivita (I := I) g₀).toFun
          (fun b => (PDE.DeTurck.deTurckVF (I := I) g₁ gc :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) b) x w +
        PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          ((PDE.DeTurck.deTurckVF (I := I) g₁ gc :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) w := by
  have hcd := PDE.DeTurck.connDiff_apply (I := I) g₁ g₀
    (σ := fun b => (PDE.DeTurck.deTurckVF (I := I) g₁ gc :
      Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) b) (x := x)
    (PDE.DeTurck.deTurckVF (I := I) g₁ gc :
      Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯).mdifferentiableAt w
  have hEndo : deTurckLieWEndo (I := I) g₁ gc x w =
      (LeviCivita (I := I) g₁).toFun
        (fun b => (PDE.DeTurck.deTurckVF (I := I) g₁ gc :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) b) x w := rfl
  rw [hEndo, hcd]
  abel

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma bdWEndo_sub_eq (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (w : TangentSpace I x) :
    deTurckLieWEndo (I := I) g₁ g_bg x w - deTurckLieWEndo (I := I) g₁ g₀ x w =
      (LeviCivita (I := I) g₀).toFun
          (fun b => bdVFSec (I := I) (M := M) g₁ g_bg g₀ b) x w +
        PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (bdVFSec (I := I) (M := M) g₁ g_bg g₀ x) w := by
  rw [bdWEndo_eq_covDeriv_add_connDiff (I := I) (M := M) g₀ g₁ g_bg x w,
    bdWEndo_eq_covDeriv_add_connDiff (I := I) (M := M) g₀ g₁ g₀ x w]
  have hLC : (LeviCivita (I := I) g₀).toFun
      (fun b => bdVFSec (I := I) (M := M) g₁ g_bg g₀ b) x w =
      (LeviCivita (I := I) g₀).toFun
          (fun b => (PDE.DeTurck.deTurckVF (I := I) g₁ g_bg :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) b) x w -
        (LeviCivita (I := I) g₀).toFun
          (fun b => (PDE.DeTurck.deTurckVF (I := I) g₁ g₀ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) b) x w := by
    have h := bdLeviCivita_toFun_sub (I := I) (M := M) g₀
      (PDE.DeTurck.deTurckVF (I := I) g₁ g_bg :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
      (PDE.DeTurck.deTurckVF (I := I) g₁ g₀ :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x w
    rw [← h]
    rfl
  have hcd : PDE.DeTurck.connDiff (I := I) g₁ g₀ x
      (bdVFSec (I := I) (M := M) g₁ g_bg g₀ x) w =
      PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          ((PDE.DeTurck.deTurckVF (I := I) g₁ g_bg :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) w -
        PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          ((PDE.DeTurck.deTurckVF (I := I) g₁ g₀ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) w := by
    rw [bdVFSec_apply, map_sub, ContinuousLinearMap.sub_apply]
  rw [hLC, hcd]
  abel

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma bdCotangentToDual_slotInsertEndoFib (x : M)
    (Λ : TangentSpace I x →L[ℝ] TangentSpace I x) (om : Tensor0SSpace 1 I x)
    (w : TangentSpace I x) :
    cotangentToDual (I := I)
        (slotInsertEndoFib (I := I) (M := M) 1 0 x Λ om) w =
      cotangentToDual (I := I) om (Λ w) := by
  rw [cotangentToDual_apply, cotangentToDual_apply]
  rw [show (slotInsertEndoFib (I := I) (M := M) 1 0 x Λ om) (fun _ : Fin 1 => w)
      = Tensor0SSpace.toModel (slotInsertEndoFib (I := I) (M := M) 1 0 x Λ om)
          (fun _ : Fin 1 => (show E from w)) from rfl]
  rw [slotInsertEndoFib_apply_eval]
  rw [show Function.update (fun _ : Fin 1 => (show E from w)) 0
        (Λ ((fun _ : Fin 1 => (show E from w)) 0)) =
      (fun _ : Fin 1 => (show E from Λ w)) from by
    funext k; fin_cases k; simp]
  rfl

omit [NeZero (Module.finrank ℝ E)] in
private lemma bdCotangentToDual_cometricRaise_bdAlpha
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) (om : Tensor0SSpace 1 I x)
    (w : TangentSpace I x) :
    cotangentToDual (I := I)
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
            (bdAlpha (I := I) (M := M) g₀ g₁ g_bg)).toSection x) om) w =
      unitModel (I := I) (M := M) g₀ 2 (bdAlpha (I := I) (M := M) g₀ g₁ g_bg) x
        ![inverseMetricSharpFib (I := I) g₀ x om, w] := by
  rw [cotangentToDual_apply]
  rw [cometricRaiseSlot0Field_toSection]
  rw [cometricRaiseSlot0Fib_clm_apply (I := I) g₀ 0 x _ om]
  rw [show (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (0 + 1) x
          (inverseMetricSharpFib (I := I) g₀ x om)
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (0 + 2) I x from
              (bdAlpha (I := I) (M := M) g₀ g₁ g_bg).toSection x)
            (unitTensor (I := I) (M := M) x)) (fun _ : Fin 1 => w) : ℝ) =
      Tensor0SSpace.toModel
        (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (0 + 1) x
          (inverseMetricSharpFib (I := I) g₀ x om)
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (0 + 2) I x from
              (bdAlpha (I := I) (M := M) g₀ g₁ g_bg).toSection x)
            (unitTensor (I := I) (M := M) x)))
        (fun _ : Fin 1 => w) from rfl]
  rw [bdInterior_product_toModel_eval (I := I) (M := M) (0 + 1) x
    (inverseMetricSharpFib (I := I) g₀ x om)
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (0 + 2) I x from
        (bdAlpha (I := I) (M := M) g₀ g₁ g_bg).toSection x)
      (unitTensor (I := I) (M := M) x)) (fun _ : Fin 1 => w)]
  rw [unitModel]
  congr 1
  funext k
  refine Fin.cases ?_ (fun j => ?_) k
  · rfl
  · refine Fin.cases ?_ (fun j' => j'.elim0) j
    rfl

theorem bdWEndoInsert_sub_eq_cometricRaise
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    deTurckLieWEndoInsert (I := I) (M := M) g₀ g₁ g_bg -
        deTurckLieWEndoInsert (I := I) (M := M) g₀ g₁ g₀ =
      cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
        (bdAlpha (I := I) (M := M) g₀ g₁ g_bg) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]
  apply tensorRSSpace_ext 1 1 x
  intro om
  apply cotangentToDualLinear_injective (I := I) (x := x)
  apply LinearMap.ext
  intro w
  rw [cotangentToDualLinear_apply, cotangentToDualLinear_apply]
  rw [bdCotangentToDual_cometricRaise_bdAlpha (I := I) (M := M) g₀ g₁ g_bg x om w]
  rw [show (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        ((deTurckLieWEndoInsert (I := I) (M := M) g₀ g₁ g_bg).toSection x -
          (deTurckLieWEndoInsert (I := I) (M := M) g₀ g₁ g₀).toSection x)) om =
      (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
          (deTurckLieWEndoInsert (I := I) (M := M) g₀ g₁ g_bg).toSection x) om -
        (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
          (deTurckLieWEndoInsert (I := I) (M := M) g₀ g₁ g₀).toSection x) om from rfl]
  rw [show (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (deTurckLieWEndoInsert (I := I) (M := M) g₀ g₁ g_bg).toSection x) om =
      slotInsertEndoFib (I := I) (M := M) 1 0 x
        (deTurckLieWEndo (I := I) g₁ g_bg x) om from rfl]
  rw [show (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (deTurckLieWEndoInsert (I := I) (M := M) g₀ g₁ g₀).toSection x) om =
      slotInsertEndoFib (I := I) (M := M) 1 0 x
        (deTurckLieWEndo (I := I) g₁ g₀ x) om from rfl]
  rw [show cotangentToDual (I := I)
        (slotInsertEndoFib (I := I) (M := M) 1 0 x
            (deTurckLieWEndo (I := I) g₁ g_bg x) om -
          slotInsertEndoFib (I := I) (M := M) 1 0 x
            (deTurckLieWEndo (I := I) g₁ g₀ x) om) w =
      cotangentToDual (I := I)
          (slotInsertEndoFib (I := I) (M := M) 1 0 x
            (deTurckLieWEndo (I := I) g₁ g_bg x) om) w -
        cotangentToDual (I := I)
          (slotInsertEndoFib (I := I) (M := M) 1 0 x
            (deTurckLieWEndo (I := I) g₁ g₀ x) om) w from by
    rw [show cotangentToDual (I := I)
          (slotInsertEndoFib (I := I) (M := M) 1 0 x
              (deTurckLieWEndo (I := I) g₁ g_bg x) om -
            slotInsertEndoFib (I := I) (M := M) 1 0 x
              (deTurckLieWEndo (I := I) g₁ g₀ x) om) =
        cotangentToDualLinear (I := I) (x := x)
          (slotInsertEndoFib (I := I) (M := M) 1 0 x
              (deTurckLieWEndo (I := I) g₁ g_bg x) om -
            slotInsertEndoFib (I := I) (M := M) 1 0 x
              (deTurckLieWEndo (I := I) g₁ g₀ x) om) from rfl]
    rw [map_sub]
    rfl]
  rw [bdCotangentToDual_slotInsertEndoFib (I := I) (M := M) x
    (deTurckLieWEndo (I := I) g₁ g_bg x) om w]
  rw [bdCotangentToDual_slotInsertEndoFib (I := I) (M := M) x
    (deTurckLieWEndo (I := I) g₁ g₀ x) om w]
  rw [show cotangentToDual (I := I) om (deTurckLieWEndo (I := I) g₁ g_bg x w) -
        cotangentToDual (I := I) om (deTurckLieWEndo (I := I) g₁ g₀ x w) =
      cotangentToDual (I := I) om
        (deTurckLieWEndo (I := I) g₁ g_bg x w - deTurckLieWEndo (I := I) g₁ g₀ x w) from by
    rw [show cotangentToDual (I := I) om
          (deTurckLieWEndo (I := I) g₁ g_bg x w - deTurckLieWEndo (I := I) g₁ g₀ x w) =
        cotangentToDualLinear (I := I) (x := x) om
          (deTurckLieWEndo (I := I) g₁ g_bg x w - deTurckLieWEndo (I := I) g₁ g₀ x w)
        from rfl]
    rw [map_sub]
    rfl]
  rw [bdWEndo_sub_eq (I := I) (M := M) g₀ g₁ g_bg x w]
  rw [bdAlpha, bdUnitModel_add, ContinuousMultilinearMap.add_apply,
    bdAlphaA_unitModel_apply (I := I) (M := M) g₀ g₁ g_bg x
      (inverseMetricSharpFib (I := I) g₀ x om) w,
    bdAlphaB_unitModel_apply (I := I) (M := M) g₀ g₁ g_bg x
      (inverseMetricSharpFib (I := I) g₀ x om) w]
  rw [show cotangentToDual (I := I) om
        ((LeviCivita (I := I) g₀).toFun
            (fun b => bdVFSec (I := I) (M := M) g₁ g_bg g₀ b) x w +
          PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            (bdVFSec (I := I) (M := M) g₁ g_bg g₀ x) w) =
      cotangentToDual (I := I) om
          ((LeviCivita (I := I) g₀).toFun
            (fun b => bdVFSec (I := I) (M := M) g₁ g_bg g₀ b) x w) +
        cotangentToDual (I := I) om
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            (bdVFSec (I := I) (M := M) g₁ g_bg g₀ x) w) from by
    rw [show ∀ v : TangentSpace I x, cotangentToDual (I := I) om v =
        cotangentToDualLinear (I := I) (x := x) om v from fun v => rfl]
    exact map_add _ _ _]
  rw [show cotangentToDual (I := I) om
        ((LeviCivita (I := I) g₀).toFun
          (fun b => bdVFSec (I := I) (M := M) g₁ g_bg g₀ b) x w) =
      g₀.inner x (inverseMetricSharpFib (I := I) g₀ x om)
        ((LeviCivita (I := I) g₀).toFun
          (fun b => bdVFSec (I := I) (M := M) g₁ g_bg g₀ b) x w) from by
    rw [show cotangentToDual (I := I) om
          ((LeviCivita (I := I) g₀).toFun
            (fun b => bdVFSec (I := I) (M := M) g₁ g_bg g₀ b) x w) =
        cotangentToDualLinear (I := I) (x := x) om
          ((LeviCivita (I := I) g₀).toFun
            (fun b => bdVFSec (I := I) (M := M) g₁ g_bg g₀ b) x w) from rfl]
    exact (inverseMetricSharpFib_inner (I := I) g₀ x om _).symm]
  rw [show cotangentToDual (I := I) om
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (bdVFSec (I := I) (M := M) g₁ g_bg g₀ x) w) =
      g₀.inner x (inverseMetricSharpFib (I := I) g₀ x om)
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (bdVFSec (I := I) (M := M) g₁ g_bg g₀ x) w) from by
    rw [show cotangentToDual (I := I) om
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            (bdVFSec (I := I) (M := M) g₁ g_bg g₀ x) w) =
        cotangentToDualLinear (I := I) (x := x) om
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            (bdVFSec (I := I) (M := M) g₁ g_bg g₀ x) w) from rfl]
    exact (inverseMetricSharpFib_inner (I := I) g₀ x om _).symm]
  rw [g₀.symm x (inverseMetricSharpFib (I := I) g₀ x om)
    ((LeviCivita (I := I) g₀).toFun
      (fun b => bdVFSec (I := I) (M := M) g₁ g_bg g₀ b) x w),
    g₀.symm x (inverseMetricSharpFib (I := I) g₀ x om)
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
        (bdVFSec (I := I) (M := M) g₁ g_bg g₀ x) w)]

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
