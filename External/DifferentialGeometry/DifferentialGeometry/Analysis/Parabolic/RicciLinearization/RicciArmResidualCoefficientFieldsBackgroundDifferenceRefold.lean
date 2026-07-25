import DifferentialGeometry.Geometry.Connection.TensorNabla.OperatorFieldSecondGradientRefold
import DifferentialGeometry.Geometry.Flow.DeTurckVFConnDiffVariation
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciThreeArmCorrectionFieldBound
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciLinearizationArmFields
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciPathPalatiniLinearization
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifference
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTower
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderDefs
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLieKernelL2JetBound
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.CurvatureRefoldMonomialFibreNormBound
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciLinearizationConnDiffCoefficients
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldInputSlotSymmetrization
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciArmResidualCoefficientFieldsMetricPerturbation
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciArmResidualCoefficientFieldsConnDiffCommutator
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciArmResidualCoefficientFieldsSharpGradientKoszul
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciArmResidualCoefficientFieldsRicciFold


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

section NormedBackgroundDifferenceRemainderField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

def backgroundRicciCommutatorDiffRefoldRemainderField (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 :=
  ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 2
      (ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₁
        - ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₀)
      (ccInputSlotSwapField (I := I) (M := M) g₀)
    + (1 / 2 : ℝ) • ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀ g₁
        (metricDifferenceCcTensor (I := I) (M := M) g₀ g₁)
    - ricciArmRicciFoldRemainderField (I := I) (M := M) g₀ g₁
        (metricDifferenceCcTensor (I := I) (M := M) g₀ g₁)


theorem bgRDiffRefoldRemainderField_self (g₀ : SmoothRiemannianMetric I M) :
    backgroundRicciCommutatorDiffRefoldRemainderField (I := I) (M := M) g₀ g₀ = 0 := by
  rw [backgroundRicciCommutatorDiffRefoldRemainderField, metricDifferenceCcTensor_self, sub_self,
    appCcRS_zero_left, ricciArmSharpGradKoszulResidualField_zero_weight,
    ricciArmRicciFoldRemainderField_zero_weight, smul_zero, add_zero, sub_zero]

end NormedBackgroundDifferenceRemainderField

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma inner_ext_vec (g : SmoothRiemannianMetric I M) (x : M) {a b : TangentSpace I x}
    (h : ∀ z : TangentSpace I x, g.inner x a z = g.inner x b z) : a = b := by
  apply (metricFlatMap (I := I) g x).injective
  apply LinearMap.ext
  intro z
  rw [metricFlatMap_apply, metricFlatMap_apply]
  exact h z

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma toModel_slotSwapFib_pair (x : M) (D : Tensor0SBundle.Tensor0SSpace 2 I x)
    (u w : E) :
    Tensor0SBundle.Tensor0SSpace.toModel (inputSlotSwapFib (I := I) (M := M) x D) ![u, w] =
      Tensor0SBundle.Tensor0SSpace.toModel D ![w, u] := by
  rw [slotSwapFib_apply, Tensor0SBundle.Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma unitModel_sub_loc (g : SmoothRiemannianMetric I M) (s : ℕ)
    (A B : SmoothCcTensor g 0 s) (x : M) :
    unitModel (I := I) (M := M) g s (A - B) x =
      unitModel (I := I) (M := M) g s A x - unitModel (I := I) (M := M) g s B x := by
  simp only [unitModel]
  rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
    ContinuousLinearMap.sub_apply, Tensor0SBundle.Tensor0SSpace.toModel_sub]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma unitModel_add_loc (g : SmoothRiemannianMetric I M) (s : ℕ)
    (A B : SmoothCcTensor g 0 s) (x : M) :
    unitModel (I := I) (M := M) g s (A + B) x =
      unitModel (I := I) (M := M) g s A x + unitModel (I := I) (M := M) g s B x := by
  simp only [unitModel]
  rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply,
    ContinuousLinearMap.add_apply, Tensor0SBundle.Tensor0SSpace.toModel_add]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma unitModel_smul_loc (g : SmoothRiemannianMetric I M) (s : ℕ) (c : ℝ)
    (A : SmoothCcTensor g 0 s) (x : M) :
    unitModel (I := I) (M := M) g s (c • A) x =
      c • unitModel (I := I) (M := M) g s A x := by
  simp only [unitModel]
  rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
    ContinuousLinearMap.smul_apply, Tensor0SBundle.Tensor0SSpace.toModel_smul]

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem foldOrthoFrame_basis_at_center (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ bse : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x),
      ∀ i, bse i = smoothOrthoFrame (I := I) g x i x := by
  classical
  have horth : ∀ a b : Fin (Module.finrank ℝ E),
      g.inner x (smoothOrthoFrame (I := I) g x a x)
        (smoothOrthoFrame (I := I) g x b x) = if a = b then 1 else 0 :=
    fun a b => smoothOrthoFrame_orthonormal_at_center (I := I) g x a b
  have he_li : LinearIndependent ℝ
      (fun i => smoothOrthoFrame (I := I) g x i x) := by
    rw [linearIndependent_iff']
    intro fs c hsum k hk_mem
    have h_zero : g.inner x (smoothOrthoFrame (I := I) g x k x)
        (∑ j ∈ fs, c j • smoothOrthoFrame (I := I) g x j x) = 0 := by
      rw [hsum]; simp
    rw [map_sum] at h_zero
    have h_pull : ∀ j ∈ fs, g.inner x (smoothOrthoFrame (I := I) g x k x)
        (c j • smoothOrthoFrame (I := I) g x j x) =
        c j * (if k = j then (1 : ℝ) else 0) := by
      intro j _
      rw [(g.inner x (smoothOrthoFrame (I := I) g x k x)).map_smul (c j),
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
private theorem foldOrthoFrame_expansion_at_center (g : SmoothRiemannianMetric I M)
    (x : M) (u : TangentSpace I x) :
    u = ∑ i : Fin (Module.finrank ℝ E),
      g.inner x u (smoothOrthoFrame (I := I) g x i x) •
        smoothOrthoFrame (I := I) g x i x := by
  classical
  obtain ⟨bse, hbse⟩ := foldOrthoFrame_basis_at_center (I := I) (M := M) g x
  have horth : ∀ a b : Fin (Module.finrank ℝ E),
      g.inner x (smoothOrthoFrame (I := I) g x a x)
        (smoothOrthoFrame (I := I) g x b x) = if a = b then 1 else 0 :=
    fun a b => smoothOrthoFrame_orthonormal_at_center (I := I) g x a b
  have hcoeff : ∀ j : Fin (Module.finrank ℝ E),
      g.inner x u (smoothOrthoFrame (I := I) g x j x) = bse.repr u j := by
    intro j
    rw [g.symm x u (smoothOrthoFrame (I := I) g x j x)]
    conv_lhs => rw [← bse.sum_repr u]
    rw [map_sum]
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => by
      rw [(g.inner x (smoothOrthoFrame (I := I) g x j x)).map_smul (bse.repr u i),
        smul_eq_mul, hbse i, horth j i])]
    rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ j)]
    · rw [if_pos rfl, mul_one]
    · intro i _ hij
      rw [if_neg (fun h => hij h.symm), mul_zero]
  calc u = ∑ i : Fin (Module.finrank ℝ E), bse.repr u i • bse i := (bse.sum_repr u).symm
    _ = ∑ i : Fin (Module.finrank ℝ E),
        g.inner x u (smoothOrthoFrame (I := I) g x i x) •
          smoothOrthoFrame (I := I) g x i x := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hcoeff i, hbse i]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
private lemma foldInvSharpKoszul_eq_connDiff (g₀ g₁ : SmoothRiemannianMetric I M)
    (X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    inverseMetricSharpFib (I := I) g₁ x
        (koszulCovGradCovec (I := I) (M := M) g₀ g₁ X Y x) =
      PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Y x) (X x) := by
  apply inner_ext_vec (I := I) (M := M) g₁ x
  intro z
  rw [inverseMetricSharpFib_inner (I := I) g₁ x _ z, cotangentToDualLinear_apply,
    koszulCovGradCovec_dual_apply (I := I) (M := M) g₀ g₁ X Y x z]

private lemma vec2_upd_zero {F : Type*} (a b z : F) :
    Function.update ![a, b] 0 z = ![z, b] := by
  funext k
  fin_cases k <;> simp [Function.update]

private lemma vec2_upd_one {F : Type*} (a b z : F) :
    Function.update ![a, b] 1 z = ![a, z] := by
  funext k
  fin_cases k <;> simp [Function.update]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma foldTensor0sClmExtUnit {s : ℕ} {x : M}
    {φ ψ : Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace s I x}
    (h : φ (unitZeroSec (I := I) (M := M) x) = ψ (unitZeroSec (I := I) (M := M) x)) :
    φ = ψ := by
  classical
  ext D
  rw [zeroTensor_eq_smul_unit (I := I) (M := M) x D, map_smul, map_smul, h]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma foldCoeff_eq_unitScalarRSLift (g₀ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2) (x : M) :
    (P.toSection x : Tensor0SBundle.TensorRSSpace 0 2 I x) =
      unitScalarRSLift (I := I) (M := M) x
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
          P.toSection x) (unitZeroSec (I := I) (M := M) x)) := by
  have h : (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
      P.toSection x) =
      (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        unitScalarRSLift (I := I) (M := M) x
          ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
              Tensor0SBundle.Tensor0SSpace 2 I x from P.toSection x)
            (unitZeroSec (I := I) (M := M) x))) := by
    apply foldTensor0sClmExtUnit (I := I) (M := M)
    rw [unitScalarRSLift_apply_unit]
  exact h

omit [NeZero (Module.finrank ℝ E)] in
private lemma foldG2_pair_antisym (g₀ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2)
    {X Y : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (x : M) (c d : TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 P) x
        ![X x, Y x, c, d]
      - unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 P) x
          ![Y x, X x, c, d] =
    -(smoothCcTensorBilinForm (I := I) g₀ P x (riemannOp (LeviCivita (I := I) g₀) x (X x) (Y x) c) d
      + smoothCcTensorBilinForm (I := I) g₀ P x c (riemannOp (LeviCivita (I := I) g₀) x (X x) (Y x) d)) := by
  classical
  have hicg : iteratedCovGrad (I := I) g₀ 0 2 2 P =
      covGrad (I := I) (M := M) g₀ 0 (2 + 1) (covGrad (I := I) (M := M) g₀ 0 2 P) := rfl
  have hconsXY : (![X x, Y x, c, d] : Fin 4 → TangentSpace I x) =
      Fin.cons (X x) (Fin.cons (Y x) ![c, d]) := by
    funext i
    fin_cases i <;> rfl
  have hconsYX : (![Y x, X x, c, d] : Fin 4 → TangentSpace I x) =
      Fin.cons (Y x) (Fin.cons (X x) ![c, d]) := by
    funext i
    fin_cases i <;> rfl
  have hXY := tensorSecondCovDeriv_eq_covGrad_succ_twoSlotEval_genVal (I := I) (M := M)
    g₀ 2 P hX hY x ![c, d]
  have hYX := tensorSecondCovDeriv_eq_covGrad_succ_twoSlotEval_genVal (I := I) (M := M)
    g₀ 2 P hY hX x ![c, d]
  have hUM : ∀ v : Fin 4 → TangentSpace I x,
      unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 P) x v =
      Tensor0SBundle.Tensor0SSpace.toModel
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
            Tensor0SBundle.Tensor0SSpace (2 + 1 + 1) I x from
          (covGrad (I := I) (M := M) g₀ 0 (2 + 1)
            (covGrad (I := I) (M := M) g₀ 0 2 P)).toSection x)
          (unitZeroSec (I := I) (M := M) x)) v := by
    intro v
    rw [unitModel, hicg]
    rfl
  rw [hUM ![X x, Y x, c, d], hUM ![Y x, X x, c, d], hconsXY, hconsYX, hXY, hYX]
  have hdiff : Tensor0SBundle.Tensor0SSpace.toModel
      ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        tensorSecondCovDeriv (I := I) g₀ 0 2 X Y (fun y : M => P.toSection y) x)
        (unitZeroSec (I := I) (M := M) x)) ![c, d]
      - Tensor0SBundle.Tensor0SSpace.toModel
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
          tensorSecondCovDeriv (I := I) g₀ 0 2 Y X (fun y : M => P.toSection y) x)
          (unitZeroSec (I := I) (M := M) x)) ![c, d]
      = Tensor0SBundle.Tensor0SSpace.toModel
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
          riemannOp (tensorCov (I := I) g₀ 0 2) x (X x) (Y x)
            ((P.toSection x : Tensor0SBundle.TensorRSSpace 0 2 I x)))
          (unitZeroSec (I := I) (M := M) x)) ![c, d] := by
    rw [← tensorSecondCovDeriv_antisymm_eq_riemannOp (I := I) g₀ 0 2 hX hY
      P.toSection.contMDiff]
    rw [show (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
          Tensor0SBundle.Tensor0SSpace 2 I x from
        (tensorSecondCovDeriv (I := I) g₀ 0 2 X Y (fun y : M => P.toSection y) x -
          tensorSecondCovDeriv (I := I) g₀ 0 2 Y X (fun y : M => P.toSection y) x)) =
      (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        tensorSecondCovDeriv (I := I) g₀ 0 2 X Y (fun y : M => P.toSection y) x) -
      (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        tensorSecondCovDeriv (I := I) g₀ 0 2 Y X (fun y : M => P.toSection y) x) from rfl]
    rw [ContinuousLinearMap.sub_apply, Tensor0SBundle.Tensor0SSpace.toModel_sub,
      ContinuousMultilinearMap.sub_apply]
  rw [hdiff]
  rw [show ((P.toSection x : Tensor0SBundle.TensorRSSpace 0 2 I x)) =
      unitScalarRSLift (I := I) (M := M) x
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
          P.toSection x) (unitZeroSec (I := I) (M := M) x)) from
    foldCoeff_eq_unitScalarRSLift (I := I) (M := M) g₀ P x]
  rw [riemannOp_tensorCov_unitScalarRSLift_unitEval (I := I) (M := M) g₀ 2 x (X x) (Y x)
    ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
      P.toSection x) (unitZeroSec (I := I) (M := M) x))]
  set Xb : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ := ⟨fun b => X b, hX⟩ with hXb_def
  set Yb : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ := ⟨fun b => Y b, hY⟩ with hYb_def
  set AP : Π y : M, Tensor0SBundle.Tensor0SSpace 2 I y := fun y =>
    (show Tensor0SBundle.Tensor0SSpace 0 I y →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I y from
      P.toSection y) (unitZeroSec (I := I) (M := M) y) with hAP_def
  have hAP_smooth : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) y (AP y)) := by
    exact ContMDiff.clm_bundle_apply (𝕜 := ℝ) (n := (∞ : WithTop ℕ∞))
      (F₁ := Tensor0SBundle.Tensor0SModel 0 ℝ E) (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E)
      (E₁ := fun z : M => Tensor0SBundle.Tensor0SSpace 0 I z)
      (E₂ := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z)
      (IM := I) (IB := I) (b := id)
      (ϕ := fun y : M =>
        (show Tensor0SBundle.Tensor0SSpace 0 I y →L[ℝ]
            Tensor0SBundle.Tensor0SSpace 2 I y from P.toSection y))
      (v := fun y : M => unitZeroSec (I := I) (M := M) y)
      P.toSection.contMDiff (unitZeroSec (I := I) (M := M)).contMDiff
  have hop : riemannOp (Tensor0SNabla.tensor0SCovariantDerivative I M 2
        (LeviCivita (I := I) g₀)) x (X x) (Y x) (AP x) =
      riemannSec (Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g₀))
        (fun b => Xb b) (fun b => Yb b) AP x :=
    riemannOp_apply_smooth
      (cov := Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g₀))
      hX hY hAP_smooth
  rw [show ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
        Tensor0SBundle.Tensor0SSpace 2 I x from P.toSection x)
        (unitZeroSec (I := I) (M := M) x)) = AP x from rfl]
  rw [hop]
  rw [riemannSec_tensor0SCov_apply_eval (I := I) (M := M) g₀ 2 Xb Yb AP hAP_smooth x ![c, d]]
  rw [Fin.sum_univ_two]
  rw [show (![c, d] : Fin 2 → TangentSpace I x) 0 = c from rfl,
    show (![c, d] : Fin 2 → TangentSpace I x) 1 = d from rfl,
    vec2_upd_zero, vec2_upd_one]
  have hbase : ∀ u : TangentSpace I x,
      baseSlotCurv (I := I) g₀ Xb Yb x u =
        riemannOp (LeviCivita (I := I) g₀) x (X x) (Y x) u := by
    intro u
    rw [baseSlotCurv]
    have hu := riemannOp_apply_smooth (cov := LeviCivita (I := I) g₀)
      (X := fun b => Xb b) (Y := fun b => Yb b)
      (Z := fun b => smoothExtensionTangent (I := I) x u b) (x := x)
      hX hY (smoothExtensionTangent_contMDiff (I := I) x u)
    beta_reduce at hu
    rw [smoothExtensionTangent_eq (I := I) x u] at hu
    exact hu.symm
  rw [hbase c, hbase d]
  have hAPtoModel : ∀ (m : Fin 2 → TangentSpace I x),
      Tensor0SBundle.Tensor0SSpace.toModel (AP x) (fun i => (m i : E)) =
        smoothCcTensorBilinForm (I := I) g₀ P x (m 0) (m 1) := by
    intro m
    have h1 : Tensor0SBundle.Tensor0SSpace.toModel (AP x) (fun i => (m i : E)) =
        unitModel (I := I) (M := M) g₀ 2 P x m := rfl
    rw [h1, show m = ![m 0, m 1] from funext (fun i => by fin_cases i <;> rfl),
      unitModel_eq_ccTensorBilin_local (I := I) (M := M) g₀ P x (m 0) (m 1)]
    rfl
  rw [show Tensor0SBundle.Tensor0SSpace.toModel (AP x)
        ![(riemannOp (LeviCivita (I := I) g₀) x (X x) (Y x) c : E), (d : E)] =
      smoothCcTensorBilinForm (I := I) g₀ P x (riemannOp (LeviCivita (I := I) g₀) x (X x) (Y x) c) d from
    hAPtoModel ![riemannOp (LeviCivita (I := I) g₀) x (X x) (Y x) c, d]]
  rw [show Tensor0SBundle.Tensor0SSpace.toModel (AP x)
        ![(c : E), (riemannOp (LeviCivita (I := I) g₀) x (X x) (Y x) d : E)] =
      smoothCcTensorBilinForm (I := I) g₀ P x c (riemannOp (LeviCivita (I := I) g₀) x (X x) (Y x) d) from
    hAPtoModel ![c, riemannOp (LeviCivita (I := I) g₀) x (X x) (Y x) d]]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma foldBilinSymm_eq_of_symm (g₀ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2)
    (hPsymm : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ P x v w = smoothCcTensorBilinForm (I := I) g₀ P x w v)
    (x : M) (v w : TangentSpace I x) :
    ccTensorBilinSymm (I := I) g₀ P x v w = smoothCcTensorBilinForm (I := I) g₀ P x v w := by
  rw [ccTensorBilinSymm_apply, ← hPsymm x v w]
  ring

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma foldSkew_pointwise (g₀ g₁ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
    (hPsymm : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ P x v w = smoothCcTensorBilinForm (I := I) g₀ P x w v)
    (x : M) (u p q z : TangentSpace I x) :
    g₁.inner x (riemannOp (LeviCivita (I := I) g₀) x u p q) z =
      - g₁.inner x q (riemannOp (LeviCivita (I := I) g₀) x u p z)
        + (smoothCcTensorBilinForm (I := I) g₀ P x q (riemannOp (LeviCivita (I := I) g₀) x u p z)
          + smoothCcTensorBilinForm (I := I) g₀ P x (riemannOp (LeviCivita (I := I) g₀) x u p q) z) := by
  have hskew := riemannOp_metric_skew (I := I) g₀ x u p q z
  have h1 := htie x (riemannOp (LeviCivita (I := I) g₀) x u p q) z
  have h2 := htie x q (riemannOp (LeviCivita (I := I) g₀) x u p z)
  rw [foldBilinSymm_eq_of_symm (I := I) (M := M) g₀ P hPsymm] at h1 h2
  have hg : g₀.inner x (riemannOp (LeviCivita (I := I) g₀) x u p q) z =
      - g₀.inner x q (riemannOp (LeviCivita (I := I) g₀) x u p z) := by
    linarith [hskew]
  rw [h1, hg]
  have h2' : g₀.inner x q (riemannOp (LeviCivita (I := I) g₀) x u p z) =
      g₁.inner x q (riemannOp (LeviCivita (I := I) g₀) x u p z)
        - smoothCcTensorBilinForm (I := I) g₀ P x q (riemannOp (LeviCivita (I := I) g₀) x u p z) := by
    rw [h2]; ring
  rw [h2']
  ring

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma foldCompleteness_slot2 (g₁ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SBundle.Tensor0SSpace 2 I x) (p omv : TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel D ![(p : E), (omv : E)] =
      ∑ b : Fin (Module.finrank ℝ E),
        g₁.inner x omv (smoothOrthoFrame (I := I) g₁ x b x) *
          Tensor0SBundle.Tensor0SSpace.toModel D
            ![(p : E), (smoothOrthoFrame (I := I) g₁ x b x : E)] := by
  classical
  have hexp : omv = ∑ b : Fin (Module.finrank ℝ E),
      g₁.inner x omv (smoothOrthoFrame (I := I) g₁ x b x) •
        smoothOrthoFrame (I := I) g₁ x b x :=
    foldOrthoFrame_expansion_at_center (I := I) (M := M) g₁ x omv
  have hkey : Tensor0SBundle.Tensor0SSpace.toModel D
      (Function.update (![(p : E), (p : E)] : Fin 2 → E) 1
        ((∑ b : Fin (Module.finrank ℝ E),
          g₁.inner x omv (smoothOrthoFrame (I := I) g₁ x b x) •
            smoothOrthoFrame (I := I) g₁ x b x : TangentSpace I x) : E)) =
      ∑ b : Fin (Module.finrank ℝ E),
        g₁.inner x omv (smoothOrthoFrame (I := I) g₁ x b x) *
          Tensor0SBundle.Tensor0SSpace.toModel D
            ![(p : E), (smoothOrthoFrame (I := I) g₁ x b x : E)] := by
    have hsum : Tensor0SBundle.Tensor0SSpace.toModel D
        (Function.update (![(p : E), (p : E)] : Fin 2 → E) 1
          (∑ b : Fin (Module.finrank ℝ E),
            g₁.inner x omv (smoothOrthoFrame (I := I) g₁ x b x) •
              ((smoothOrthoFrame (I := I) g₁ x b x : TangentSpace I x) : E))) =
        ∑ b : Fin (Module.finrank ℝ E),
          Tensor0SBundle.Tensor0SSpace.toModel D
            (Function.update (![(p : E), (p : E)] : Fin 2 → E) 1
              (g₁.inner x omv (smoothOrthoFrame (I := I) g₁ x b x) •
                ((smoothOrthoFrame (I := I) g₁ x b x : TangentSpace I x) : E))) :=
      (Tensor0SBundle.Tensor0SSpace.toModel D).toMultilinearMap.map_update_sum
        Finset.univ 1 (fun b => g₁.inner x omv (smoothOrthoFrame (I := I) g₁ x b x) •
          ((smoothOrthoFrame (I := I) g₁ x b x : TangentSpace I x) : E))
        (![(p : E), (p : E)] : Fin 2 → E)
    rw [show ((∑ b : Fin (Module.finrank ℝ E),
        g₁.inner x omv (smoothOrthoFrame (I := I) g₁ x b x) •
          smoothOrthoFrame (I := I) g₁ x b x : TangentSpace I x) : E) =
      ∑ b : Fin (Module.finrank ℝ E),
        g₁.inner x omv (smoothOrthoFrame (I := I) g₁ x b x) •
          ((smoothOrthoFrame (I := I) g₁ x b x : TangentSpace I x) : E) from rfl]
    rw [hsum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    have hsm : Tensor0SBundle.Tensor0SSpace.toModel D
        (Function.update (![(p : E), (p : E)] : Fin 2 → E) 1
          (g₁.inner x omv (smoothOrthoFrame (I := I) g₁ x b x) •
            ((smoothOrthoFrame (I := I) g₁ x b x : TangentSpace I x) : E))) =
        g₁.inner x omv (smoothOrthoFrame (I := I) g₁ x b x) •
          Tensor0SBundle.Tensor0SSpace.toModel D
            (Function.update (![(p : E), (p : E)] : Fin 2 → E) 1
              ((smoothOrthoFrame (I := I) g₁ x b x : TangentSpace I x) : E)) :=
      (Tensor0SBundle.Tensor0SSpace.toModel D).toMultilinearMap.map_update_smul
        (![(p : E), (p : E)] : Fin 2 → E) 1
        (g₁.inner x omv (smoothOrthoFrame (I := I) g₁ x b x))
        ((smoothOrthoFrame (I := I) g₁ x b x : TangentSpace I x) : E)
    rw [hsm, vec2_upd_one, smul_eq_mul]
  have hfinal : (![(p : E), (omv : E)] : Fin 2 → E) =
      Function.update (![(p : E), (p : E)] : Fin 2 → E) 1
        ((∑ b : Fin (Module.finrank ℝ E),
          g₁.inner x omv (smoothOrthoFrame (I := I) g₁ x b x) •
            smoothOrthoFrame (I := I) g₁ x b x : TangentSpace I x) : E) := by
    rw [vec2_upd_one]
    exact congrArg (fun t : TangentSpace I x => (![(p : E), (t : E)] : Fin 2 → E)) hexp
  rw [hfinal, hkey]

omit [NeZero (Module.finrank ℝ E)] in
private lemma foldCore_pointwise (g₀ g₁ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
    (Xs As Bs : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (x : M) (z : TangentSpace I x) :
    g₁.inner x (riemannOp (LeviCivita (I := I) g₁) x (Xs x) (As x) (Bs x)) z =
      g₁.inner x (riemannOp (LeviCivita (I := I) g₀) x (Xs x) (As x) (Bs x)) z
      + (1 / 2 : ℝ) *
          (unitModel (I := I) (M := M) g₀ 4
              (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) g₀ P)) x
              ![Xs x, As x, Bs x, z]
            - unitModel (I := I) (M := M) g₀ 4
                (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) g₀ P)) x
                ![As x, Xs x, Bs x, z]
            + unitModel (I := I) (M := M) g₀ 4
                (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) g₀ P)) x
                ![Xs x, Bs x, As x, z]
            + unitModel (I := I) (M := M) g₀ 4
                (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) g₀ P)) x
                ![As x, z, Xs x, Bs x]
            - unitModel (I := I) (M := M) g₀ 4
                (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) g₀ P)) x
                ![Xs x, z, As x, Bs x]
            - unitModel (I := I) (M := M) g₀ 4
                (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) g₀ P)) x
                ![As x, Bs x, Xs x, z])
      - g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Bs x) (As x))
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x z (Xs x))
      + g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Bs x) (Xs x))
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x z (As x)) := by
  classical
  have hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (fun b : M => Xs b)) := Xs.contMDiff
  have hA : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (fun b : M => As b)) := As.contMDiff
  have hB : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (fun b : M => Bs b)) := Bs.contMDiff
  have hop1 : riemannOp (LeviCivita (I := I) g₁) x (Xs x) (As x) (Bs x) =
      riemannSec (LeviCivita (I := I) g₁)
        (fun b : M => Xs b) (fun b : M => As b) (fun b : M => Bs b) x := by
    have h := riemannOp_apply_smooth (cov := LeviCivita (I := I) g₁)
      (X := fun b : M => Xs b) (Y := fun b : M => As b) (Z := fun b : M => Bs b) (x := x)
      hX hA hB
    exact h
  have hop0 : riemannOp (LeviCivita (I := I) g₀) x (Xs x) (As x) (Bs x) =
      riemannSec (LeviCivita (I := I) g₀)
        (fun b : M => Xs b) (fun b : M => As b) (fun b : M => Bs b) x := by
    have h := riemannOp_apply_smooth (cov := LeviCivita (I := I) g₀)
      (X := fun b : M => Xs b) (Y := fun b : M => As b) (Z := fun b : M => Bs b) (x := x)
      hX hA hB
    exact h
  have hfold := riemannSec_difference (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁)
    (X := fun b : M => Xs b) (Y := fun b : M => As b) (Z := fun b : M => Bs b)
    hX hA hB (LeviCivita_torsion_eq_zero (I := I) g₀) x
  have hinner := congrArg (fun t : TangentSpace I x => g₁.inner x t z) hfold
  simp only [map_add, map_sub, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply]
    at hinner
  have hc1 := covDerivConnDiff_g1inner_eq_half_secondCovGrad_sub_connDiffSq (I := I) (M := M)
    g₀ g₁ P htie Xs Bs As x z
  have hc2 := covDerivConnDiff_g1inner_eq_half_secondCovGrad_sub_connDiffSq (I := I) (M := M)
    g₀ g₁ P htie As Bs Xs x z
  have hcdd1 : covDerivConnDiff (I := I) g₀ g₁
      (fun b : M => Xs b) (fun b : M => As b) (fun b : M => Bs b) x =
      covDerivDiff (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁)
        (fun b : M => Xs b) (fun b : M => As b) (fun b : M => Bs b) x := rfl
  have hcdd2 : covDerivConnDiff (I := I) g₀ g₁
      (fun b : M => As b) (fun b : M => Xs b) (fun b : M => Bs b) x =
      covDerivDiff (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁)
        (fun b : M => As b) (fun b : M => Xs b) (fun b : M => Bs b) x := rfl
  rw [hcdd1] at hc1
  rw [hcdd2] at hc2
  have hsharpz1 : inverseMetricSharpFib (I := I) g₁ x
      (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Xs
        ⟨smoothExtensionTangent (I := I) x z,
          smoothExtensionTangent_contMDiff (I := I) x z⟩ x) =
      PDE.DeTurck.connDiff (I := I) g₁ g₀ x z (Xs x) := by
    rw [foldInvSharpKoszul_eq_connDiff (I := I) (M := M) g₀ g₁ Xs
      ⟨smoothExtensionTangent (I := I) x z,
        smoothExtensionTangent_contMDiff (I := I) x z⟩ x]
    rw [show ((⟨smoothExtensionTangent (I := I) x z,
        smoothExtensionTangent_contMDiff (I := I) x z⟩ :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) =
      smoothExtensionTangent (I := I) x z x from rfl]
    rw [smoothExtensionTangent_eq (I := I) x z]
  have hsharpz2 : inverseMetricSharpFib (I := I) g₁ x
      (koszulCovGradCovec (I := I) (M := M) g₀ g₁ As
        ⟨smoothExtensionTangent (I := I) x z,
          smoothExtensionTangent_contMDiff (I := I) x z⟩ x) =
      PDE.DeTurck.connDiff (I := I) g₁ g₀ x z (As x) := by
    rw [foldInvSharpKoszul_eq_connDiff (I := I) (M := M) g₀ g₁ As
      ⟨smoothExtensionTangent (I := I) x z,
        smoothExtensionTangent_contMDiff (I := I) x z⟩ x]
    rw [show ((⟨smoothExtensionTangent (I := I) x z,
        smoothExtensionTangent_contMDiff (I := I) x z⟩ :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) =
      smoothExtensionTangent (I := I) x z x from rfl]
    rw [smoothExtensionTangent_eq (I := I) x z]
  have hsharpAB : inverseMetricSharpFib (I := I) g₁ x
      (koszulCovGradCovec (I := I) (M := M) g₀ g₁ As Bs x) =
      PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Bs x) (As x) :=
    foldInvSharpKoszul_eq_connDiff (I := I) (M := M) g₀ g₁ As Bs x
  have hsharpXB : inverseMetricSharpFib (I := I) g₁ x
      (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Xs Bs x) =
      PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Bs x) (Xs x) :=
    foldInvSharpKoszul_eq_connDiff (I := I) (M := M) g₀ g₁ Xs Bs x
  rw [hsharpz1, hsharpAB] at hc1
  rw [hsharpz2, hsharpXB] at hc2
  have hdel1 : diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁)
      (fun b : M => As b) (fun b : M => Bs b) x =
      PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Bs x) (As x) := rfl
  have hdel2 : diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁)
      (fun b : M => Xs b) (fun b : M => Bs b) x =
      PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Bs x) (Xs x) := rfl
  have hDelta1 : CovariantDerivative.difference (LeviCivita (I := I) g₁)
      (LeviCivita (I := I) g₀) x
      (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁)
        (fun b : M => As b) (fun b : M => Bs b) x) ((fun b : M => Xs b) x) =
      PDE.DeTurck.connDiff (I := I) g₁ g₀ x
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Bs x) (As x)) (Xs x) := by
    rw [hdel1]
    rfl
  have hDelta2 : CovariantDerivative.difference (LeviCivita (I := I) g₁)
      (LeviCivita (I := I) g₀) x
      (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁)
        (fun b : M => Xs b) (fun b : M => Bs b) x) ((fun b : M => As b) x) =
      PDE.DeTurck.connDiff (I := I) g₁ g₀ x
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Bs x) (Xs x)) (As x) := by
    rw [hdel2]
    rfl
  rw [hDelta1, hDelta2] at hinner
  rw [hop1, hop0]
  rw [hinner, hc1, hc2]
  ring

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma foldToModel_slot2_neg (x : M) (D : Tensor0SBundle.Tensor0SSpace 2 I x)
    (p w : TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel D ![(p : E), (-w : E)] =
      - Tensor0SBundle.Tensor0SSpace.toModel D ![(p : E), (w : E)] := by
  have hbase : (![(p : E), (-w : E)] : Fin 2 → E) =
      Function.update (![(p : E), (w : E)] : Fin 2 → E) 1 ((-1 : ℝ) • (w : E)) := by
    rw [vec2_upd_one]
    funext i
    fin_cases i
    · rfl
    · change (-w : E) = (-1 : ℝ) • (w : E)
      rw [neg_one_smul]
  rw [hbase]
  have hsm := (Tensor0SBundle.Tensor0SSpace.toModel D).toMultilinearMap.map_update_smul
    (![(p : E), (w : E)] : Fin 2 → E) 1 (-1 : ℝ) ((w : E))
  rw [show (Tensor0SBundle.Tensor0SSpace.toModel D)
      (Function.update (![(p : E), (w : E)] : Fin 2 → E) 1 ((-1 : ℝ) • (w : E))) =
    (-1 : ℝ) • (Tensor0SBundle.Tensor0SSpace.toModel D)
      (Function.update (![(p : E), (w : E)] : Fin 2 → E) 1 ((w : E))) from hsm]
  rw [vec2_upd_one, smul_eq_mul]
  ring

omit [CompactSpace M] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
private lemma foldMovingTraceRow (g₀ g₁ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
    (hPsymm : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ P x v w = smoothCcTensorBilinForm (I := I) g₀ P x w v)
    (x : M) (D : Tensor0SBundle.Tensor0SSpace 2 I x) (u z : TangentSpace I x)
    (a : Fin (Module.finrank ℝ E)) :
    ∑ b : Fin (Module.finrank ℝ E),
      Tensor0SBundle.Tensor0SSpace.toModel D
          ![(smoothOrthoFrame (I := I) g₁ x a x : E),
            (smoothOrthoFrame (I := I) g₁ x b x : E)] *
        g₁.inner x (riemannOp (LeviCivita (I := I) g₀) x u
          (smoothOrthoFrame (I := I) g₁ x a x)
          (smoothOrthoFrame (I := I) g₁ x b x)) z =
      Tensor0SBundle.Tensor0SSpace.toModel D
          ![(smoothOrthoFrame (I := I) g₁ x a x : E),
            (riemannOp (LeviCivita (I := I) g₀) x
              (smoothOrthoFrame (I := I) g₁ x a x) u z : E)] +
      ∑ b : Fin (Module.finrank ℝ E),
        Tensor0SBundle.Tensor0SSpace.toModel D
            ![(smoothOrthoFrame (I := I) g₁ x a x : E),
              (smoothOrthoFrame (I := I) g₁ x b x : E)] *
          (smoothCcTensorBilinForm (I := I) g₀ P x (smoothOrthoFrame (I := I) g₁ x b x)
              (riemannOp (LeviCivita (I := I) g₀) x u
                (smoothOrthoFrame (I := I) g₁ x a x) z)
            + smoothCcTensorBilinForm (I := I) g₀ P x
                (riemannOp (LeviCivita (I := I) g₀) x u
                  (smoothOrthoFrame (I := I) g₁ x a x)
                  (smoothOrthoFrame (I := I) g₁ x b x)) z) := by
  classical
  set Ba := smoothOrthoFrame (I := I) g₁ x a x with hBa_def
  set Rz : TangentSpace I x := riemannOp (LeviCivita (I := I) g₀) x u Ba z with hRz_def
  have hstep : ∀ b : Fin (Module.finrank ℝ E),
      Tensor0SBundle.Tensor0SSpace.toModel D
          ![(Ba : E), (smoothOrthoFrame (I := I) g₁ x b x : E)] *
        g₁.inner x (riemannOp (LeviCivita (I := I) g₀) x u Ba
          (smoothOrthoFrame (I := I) g₁ x b x)) z =
      - (g₁.inner x Rz (smoothOrthoFrame (I := I) g₁ x b x) *
          Tensor0SBundle.Tensor0SSpace.toModel D
            ![(Ba : E), (smoothOrthoFrame (I := I) g₁ x b x : E)])
        + Tensor0SBundle.Tensor0SSpace.toModel D
            ![(Ba : E), (smoothOrthoFrame (I := I) g₁ x b x : E)] *
          (smoothCcTensorBilinForm (I := I) g₀ P x (smoothOrthoFrame (I := I) g₁ x b x) Rz
            + smoothCcTensorBilinForm (I := I) g₀ P x
                (riemannOp (LeviCivita (I := I) g₀) x u Ba
                  (smoothOrthoFrame (I := I) g₁ x b x)) z) := by
    intro b
    rw [foldSkew_pointwise (I := I) (M := M) g₀ g₁ P htie hPsymm x u Ba
      (smoothOrthoFrame (I := I) g₁ x b x) z]
    rw [g₁.symm x (smoothOrthoFrame (I := I) g₁ x b x) Rz]
    ring
  rw [Finset.sum_congr rfl (fun b _ => hstep b)]
  rw [Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_neg_distrib]
  rw [← foldCompleteness_slot2 (I := I) (M := M) g₁ x D Ba Rz]
  have hswap2 : riemannOp (LeviCivita (I := I) g₀) x Ba u z = -Rz := by
    rw [hRz_def]
    exact riemannOp_swap (cov := LeviCivita (I := I) g₀) x Ba u z
  rw [hswap2, foldToModel_slot2_neg (I := I) (M := M) x D Ba Rz]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma foldQuadruplePatterns (x : M) (p q c d : TangentSpace I x) :
    ((fun i => (Fin.cons (p : E) (Fin.cons (q : E) ![(c : E), (d : E)]) : Fin 4 → E)
        ((Equiv.swap (0 : Fin 4) 2) i)) = ![(c : E), (q : E), (p : E), (d : E)]) ∧
    ((fun i => (Fin.cons (p : E) (Fin.cons (q : E) ![(c : E), (d : E)]) : Fin 4 → E)
        ((Equiv.swap (1 : Fin 4) 3) i)) = ![(p : E), (d : E), (c : E), (q : E)]) ∧
    ((fun i => (Fin.cons (p : E) (Fin.cons (q : E) ![(c : E), (d : E)]) : Fin 4 → E)
        ((Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) i)) =
      ![(c : E), (d : E), (p : E), (q : E)]) ∧
    ((fun i => (Fin.cons (p : E) (Fin.cons (q : E) ![(c : E), (d : E)]) : Fin 4 → E)
        ((1 : Equiv.Perm (Fin 4)) i)) = ![(p : E), (q : E), (c : E), (d : E)]) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · funext i
      fin_cases i <;> rfl

omit [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma foldKernelTerm_eval (g₀ g₁ : SmoothRiemannianMetric I M)
    (Wsec : Π b : M, Tensor0SBundle.Tensor0SSpace 2 I b)
    (hWsec : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) b (Wsec b)))
    (G : SmoothCcTensor g₀ 0 4) (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 4 2
          (curvatureActionKernelCoeffField (I := I) (M := M) g₀ g₁ Wsec hWsec
            (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
            (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1) G) x v =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        Tensor0SBundle.Tensor0SSpace.toModel (Wsec x)
            ![(smoothOrthoFrame (I := I) g₁ x a x : E),
              (smoothOrthoFrame (I := I) g₁ x b x : E)] *
          ((1 / 2 : ℝ) *
            (unitModel (I := I) (M := M) g₀ 4 G x
                ![v 0, smoothOrthoFrame (I := I) g₁ x b x,
                  smoothOrthoFrame (I := I) g₁ x a x, v 1]
              + unitModel (I := I) (M := M) g₀ 4 G x
                  ![smoothOrthoFrame (I := I) g₁ x a x, v 1, v 0,
                    smoothOrthoFrame (I := I) g₁ x b x]
              - unitModel (I := I) (M := M) g₀ 4 G x
                  ![v 0, v 1, smoothOrthoFrame (I := I) g₁ x a x,
                    smoothOrthoFrame (I := I) g₁ x b x]
              - unitModel (I := I) (M := M) g₀ 4 G x
                  ![smoothOrthoFrame (I := I) g₁ x a x,
                    smoothOrthoFrame (I := I) g₁ x b x, v 0, v 1])) := by
  classical
  set Guv : Tensor0SBundle.Tensor0SSpace 4 I x :=
    (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 4 I x from
      G.toSection x) (unitTensor (I := I) (M := M) x) with hGuv_def
  have hopen : unitModel (I := I) (M := M) g₀ 2
      (operatorFieldApply (I := I) (M := M) g₀ 4 2
        (curvatureActionKernelCoeffField (I := I) (M := M) g₀ g₁ Wsec hWsec
          (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
          (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1) G) x v =
      Tensor0SBundle.Tensor0SSpace.toModel
        ((show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
          (curvatureActionKernelCoeffField (I := I) (M := M) g₀ g₁ Wsec hWsec
            (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
            (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1).toSection x) Guv) v := by
    rw [unitModel, appCc_toSection]
    rfl
  rw [hopen]
  rw [curvatureRefoldKernelCoeffField_toSection_eq_kernelFib_sum (I := I) (M := M)
    g₀ g₁ Wsec hWsec _ _ _ _ x]
  rw [ContinuousLinearMap.sum_apply, ← Tensor0SBundle.Tensor0SSpace.toModelL_apply, map_sum,
    ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [ContinuousLinearMap.sum_apply, Tensor0SBundle.Tensor0SSpace.toModelL_apply,
    ← Tensor0SBundle.Tensor0SSpace.toModelL_apply, map_sum,
    ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Tensor0SBundle.Tensor0SSpace.toModelL_apply]
  rw [curvatureActionKernelCLM]
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    Tensor0SBundle.Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply,
    Tensor0SBundle.Tensor0SSpace.toModel_sub, ContinuousMultilinearMap.sub_apply,
    Tensor0SBundle.Tensor0SSpace.toModel_sub, ContinuousMultilinearMap.sub_apply,
    Tensor0SBundle.Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]
  rw [curvatureRefoldMonomialFib_toModel, curvatureRefoldMonomialFib_toModel,
    curvatureRefoldMonomialFib_toModel, curvatureRefoldMonomialFib_toModel]
  have hbr : ∀ w : Fin 4 → TangentSpace I x,
      Tensor0SBundle.Tensor0SSpace.toModel Guv (fun i => (w i : E)) =
        unitModel (I := I) (M := M) g₀ 4 G x w := fun w => rfl
  set Ba := smoothOrthoFrame (I := I) g₁ x a x
  set Bb := smoothOrthoFrame (I := I) g₁ x b x
  have hA : Tensor0SBundle.Tensor0SSpace.toModel Guv
      (fun i => (Fin.cons ((Ba : E)) (Fin.cons ((Bb : E)) v) : Fin 4 → E)
        ((Equiv.swap (0 : Fin 4) 2) i)) =
      unitModel (I := I) (M := M) g₀ 4 G x ![v 0, Bb, Ba, v 1] := by
    rw [show (fun i => (Fin.cons ((Ba : E)) (Fin.cons ((Bb : E)) v) : Fin 4 → E)
        ((Equiv.swap (0 : Fin 4) 2) i)) =
      (fun i => (((![v 0, Bb, Ba, v 1] : Fin 4 → TangentSpace I x) i : E))) from by
        funext i
        fin_cases i <;> rfl]
    exact hbr ![v 0, Bb, Ba, v 1]
  have hB : Tensor0SBundle.Tensor0SSpace.toModel Guv
      (fun i => (Fin.cons ((Ba : E)) (Fin.cons ((Bb : E)) v) : Fin 4 → E)
        ((Equiv.swap (1 : Fin 4) 3) i)) =
      unitModel (I := I) (M := M) g₀ 4 G x ![Ba, v 1, v 0, Bb] := by
    rw [show (fun i => (Fin.cons ((Ba : E)) (Fin.cons ((Bb : E)) v) : Fin 4 → E)
        ((Equiv.swap (1 : Fin 4) 3) i)) =
      (fun i => (((![Ba, v 1, v 0, Bb] : Fin 4 → TangentSpace I x) i : E))) from by
        funext i
        fin_cases i <;> rfl]
    exact hbr ![Ba, v 1, v 0, Bb]
  have hC : Tensor0SBundle.Tensor0SSpace.toModel Guv
      (fun i => (Fin.cons ((Ba : E)) (Fin.cons ((Bb : E)) v) : Fin 4 → E)
        ((Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) i)) =
      unitModel (I := I) (M := M) g₀ 4 G x ![v 0, v 1, Ba, Bb] := by
    rw [show (fun i => (Fin.cons ((Ba : E)) (Fin.cons ((Bb : E)) v) : Fin 4 → E)
        ((Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) i)) =
      (fun i => (((![v 0, v 1, Ba, Bb] : Fin 4 → TangentSpace I x) i : E))) from by
        funext i
        fin_cases i <;> rfl]
    exact hbr ![v 0, v 1, Ba, Bb]
  have hD : Tensor0SBundle.Tensor0SSpace.toModel Guv
      (fun i => (Fin.cons ((Ba : E)) (Fin.cons ((Bb : E)) v) : Fin 4 → E)
        ((1 : Equiv.Perm (Fin 4)) i)) =
      unitModel (I := I) (M := M) g₀ 4 G x ![Ba, Bb, v 0, v 1] := by
    rw [show (fun i => (Fin.cons ((Ba : E)) (Fin.cons ((Bb : E)) v) : Fin 4 → E)
        ((1 : Equiv.Perm (Fin 4)) i)) =
      (fun i => (((![Ba, Bb, v 0, v 1] : Fin 4 → TangentSpace I x) i : E))) from by
        funext i
        fin_cases i <;> rfl]
    exact hbr ![Ba, Bb, v 0, v 1]
  rw [hA, hB, hC, hD]
  rw [smul_eq_mul]
  ring

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma foldDonorWeight_eq (g₀ : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g₀ 0 2) (x : M) (p q : TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2 W x
        (fun j : Fin 2 => if j = 0 then p else q) =
      Tensor0SBundle.Tensor0SSpace.toModel
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
          W.toSection x) (unitTensor (I := I) (M := M) x)) ![(p : E), (q : E)] := by
  rw [show (fun j : Fin 2 => if j = 0 then p else q) = ![p, q] from
    funext (fun j => by fin_cases j <;> rfl)]
  rfl

omit [I.Boundaryless] in
private lemma foldSwapBgR_eval (g₀ g₁ : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 2 2
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 2
            (ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₁
              - ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₀)
            (ccInputSlotSwapField (I := I) (M := M) g₀)) W) x v =
      (∑ c : Fin (Module.finrank ℝ E),
        Tensor0SBundle.Tensor0SSpace.toModel
            ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
                Tensor0SBundle.Tensor0SSpace 2 I x from
              W.toSection x) (unitTensor (I := I) (M := M) x))
            ![(smoothOrthoFrame (I := I) g₁ x c x : E),
              (riemannOp (LeviCivita (I := I) g₀) x
                (smoothOrthoFrame (I := I) g₁ x c x) (v 0) (v 1) : E)])
      - (∑ c : Fin (Module.finrank ℝ E),
        Tensor0SBundle.Tensor0SSpace.toModel
            ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
                Tensor0SBundle.Tensor0SSpace 2 I x from
              W.toSection x) (unitTensor (I := I) (M := M) x))
            ![(smoothOrthoFrame (I := I) g₀ x c x : E),
              (riemannOp (LeviCivita (I := I) g₀) x
                (smoothOrthoFrame (I := I) g₀ x c x) (v 0) (v 1) : E)]) := by
  classical
  set Wuv : Tensor0SBundle.Tensor0SSpace 2 I x :=
    (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
      W.toSection x) (unitTensor (I := I) (M := M) x) with hWuv_def
  have hopen : unitModel (I := I) (M := M) g₀ 2
      (operatorFieldApply (I := I) (M := M) g₀ 2 2
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 2
          (ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₁
            - ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₀)
          (ccInputSlotSwapField (I := I) (M := M) g₀)) W) x v =
      Tensor0SBundle.Tensor0SSpace.toModel
        ((show Tensor0SBundle.Tensor0SSpace 2 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
          ((ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₁
            - ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₀)).toSection x)
          (inputSlotSwapFib (I := I) (M := M) x Wuv)) v := by
    rw [unitModel, appCc_toSection]
    rfl
  rw [hopen]
  have hsub : ((ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₁
      - ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₀)).toSection x =
      (ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₁).toSection x
      - (ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₀).toSection x := by
    rw [SmoothCcTensor.toSection_sub]
    rfl
  rw [hsub]
  rw [show (show Tensor0SBundle.Tensor0SSpace 2 I x →L[ℝ]
        Tensor0SBundle.Tensor0SSpace 2 I x from
      ((ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₁).toSection x
        - (ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₀).toSection x)) =
    (show Tensor0SBundle.Tensor0SSpace 2 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
      (ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₁).toSection x)
    - (show Tensor0SBundle.Tensor0SSpace 2 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
      (ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₀).toSection x) from rfl]
  rw [ContinuousLinearMap.sub_apply, Tensor0SBundle.Tensor0SSpace.toModel_sub,
    ContinuousMultilinearMap.sub_apply]
  congr 1
  · rw [show (show Tensor0SBundle.Tensor0SSpace 2 I x →L[ℝ]
          Tensor0SBundle.Tensor0SSpace 2 I x from
        (ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₁).toSection x)
        (inputSlotSwapFib (I := I) (M := M) x Wuv) =
      backgroundRiemannBiContrFib (I := I) g₀ g₁ x (inputSlotSwapFib (I := I) (M := M) x Wuv) from rfl]
    rw [show backgroundRiemannBiContrFib (I := I) g₀ g₁ x =
      backgroundRiemannBiContrFibFixedFrame (I := I) g₀ (smoothOrthoFrame (I := I) g₁ x) x from rfl]
    rw [backgroundRiemannBiContrFibFixedFrame_toModel]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    exact toModel_slotSwapFib_pair (I := I) (M := M) x Wuv _ _
  · rw [show (show Tensor0SBundle.Tensor0SSpace 2 I x →L[ℝ]
          Tensor0SBundle.Tensor0SSpace 2 I x from
        (ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₀).toSection x)
        (inputSlotSwapFib (I := I) (M := M) x Wuv) =
      backgroundRiemannBiContrFib (I := I) g₀ g₀ x (inputSlotSwapFib (I := I) (M := M) x Wuv) from rfl]
    rw [show backgroundRiemannBiContrFib (I := I) g₀ g₀ x =
      backgroundRiemannBiContrFibFixedFrame (I := I) g₀ (smoothOrthoFrame (I := I) g₀ x) x from rfl]
    rw [backgroundRiemannBiContrFibFixedFrame_toModel]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    exact toModel_slotSwapFib_pair (I := I) (M := M) x Wuv _ _

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma unitModel_smul_apply_loc (g : SmoothRiemannianMetric I M) (s : ℕ) (c : ℝ)
    (A : SmoothCcTensor g 0 s) (x : M) (v : Fin s → TangentSpace I x) :
    unitModel (I := I) (M := M) g s (c • A) x v =
      c * unitModel (I := I) (M := M) g s A x v := by
  rw [unitModel_smul_loc, ContinuousMultilinearMap.smul_apply, smul_eq_mul]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma unitModel_sub_apply_loc (g : SmoothRiemannianMetric I M) (s : ℕ)
    (A B : SmoothCcTensor g 0 s) (x : M) (v : Fin s → TangentSpace I x) :
    unitModel (I := I) (M := M) g s (A - B) x v =
      unitModel (I := I) (M := M) g s A x v - unitModel (I := I) (M := M) g s B x v := by
  rw [unitModel_sub_loc, ContinuousMultilinearMap.sub_apply]

omit [NeZero (Module.finrank ℝ E)] in
private lemma foldPsi_eq_connDiff (g₀ g₁ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
    (hsymmS : ccTensor02Symm (I := I) (M := M) g₀ P = P)
    (x : M) (u ζ : TangentSpace I x) :
    sharpRaisedKoszulVec (I := I) g₀ g₁ P x u ζ =
      PDE.DeTurck.connDiff (I := I) g₁ g₀ x u ζ := by
  apply inner_ext_vec (I := I) (M := M) g₁ x
  intro z
  rw [sharpRaisedKoszulVec,
    DifferentialGeometry.Integral.DivergenceTheorem.inner_metricSharp (I := I) g₁ x _ z,
    linearizedKoszulCovec_apply,
    connDiffInner_g1_eq_half_covGradSymmS (I := I) g₀ g₁ P htie x u ζ z, hsymmS]

omit [NeZero (Module.finrank ℝ E)] in
private lemma foldQuadKernel_split (g₀ g₁ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
    (hsymmS : ccTensor02Symm (I := I) (M := M) g₀ P = P)
    (x : M) (p q v0 v1 : TangentSpace I x) :
    - g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q p)
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x v1 v0)
      + g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q v0)
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x v1 p) =
    connDiffIteratedCommKernelBilin (I := I) g₀ g₁ x p q v0 v1
      + sharpGradKoszulKernelBilin (I := I) g₀ g₁ P x p q v0 v1 := by
  rw [connDiffAACommKernelBilin_apply, sharpGradKoszulKernelBilin_apply]
  rw [foldPsi_eq_connDiff (I := I) (M := M) g₀ g₁ P htie hsymmS x q v0,
    foldPsi_eq_connDiff (I := I) (M := M) g₀ g₁ P htie hsymmS x q p]
  rw [show PDE.DeTurck.connDiff (I := I) g₁ g₀ x
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q v0) p =
      PDE.DeTurck.connDiff (I := I) g₁ g₀ x p
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q v0) from
    PDE.DeTurck.connDiff_symm (I := I) g₁ g₀ x _ p]
  rw [show PDE.DeTurck.connDiff (I := I) g₁ g₀ x
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q p) v0 =
      PDE.DeTurck.connDiff (I := I) g₁ g₀ x v0
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q p) from
    PDE.DeTurck.connDiff_symm (I := I) g₁ g₀ x _ v0]
  rw [show PDE.DeTurck.connDiff (I := I) g₁ g₀ x v1 v0 =
      PDE.DeTurck.connDiff (I := I) g₁ g₀ x v0 v1 from
    PDE.DeTurck.connDiff_symm (I := I) g₁ g₀ x v1 v0]
  rw [show PDE.DeTurck.connDiff (I := I) g₁ g₀ x v1 p =
      PDE.DeTurck.connDiff (I := I) g₁ g₀ x p v1 from
    PDE.DeTurck.connDiff_symm (I := I) g₁ g₀ x v1 p]
  ring

omit [I.Boundaryless] in
private lemma foldQtrue_eval (g₀ g₁ : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 2 2
          (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁) W) x v =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        Tensor0SBundle.Tensor0SSpace.toModel
            ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
                Tensor0SBundle.Tensor0SSpace 2 I x from
              W.toSection x) (unitTensor (I := I) (M := M) x))
            ![(smoothOrthoFrame (I := I) g₁ x a x : E),
              (smoothOrthoFrame (I := I) g₁ x b x : E)] *
          connDiffIteratedCommKernelBilin (I := I) g₀ g₁ x
            (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x)
            (v 0) (v 1) := by
  rw [show unitModel (I := I) (M := M) g₀ 2
      (operatorFieldApply (I := I) (M := M) g₀ 2 2
        (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁) W) x =
    Tensor0SBundle.Tensor0SSpace.toModel
      (connDiffAACommBiContrFib (I := I) g₀ g₁ x
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
            Tensor0SBundle.Tensor0SSpace 2 I x from
          W.toSection x) (unitTensor (I := I) (M := M) x))) from by
    rw [unitModel, appCc_toSection]
    rfl]
  rw [connDiffAACommBiContrFib_toModel]

private lemma foldSGK_eval (g₀ g₁ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2)
    (W : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 2 2
          (ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀ g₁ P) W) x v =
      (2 : ℝ) * ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        Tensor0SBundle.Tensor0SSpace.toModel
            ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
                Tensor0SBundle.Tensor0SSpace 2 I x from
              W.toSection x) (unitTensor (I := I) (M := M) x))
            ![(smoothOrthoFrame (I := I) g₁ x a x : E),
              (smoothOrthoFrame (I := I) g₁ x b x : E)] *
          sharpGradKoszulKernelBilin (I := I) g₀ g₁ P x
            (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x)
            (v 0) (v 1) := by
  rw [show unitModel (I := I) (M := M) g₀ 2
      (operatorFieldApply (I := I) (M := M) g₀ 2 2
        (ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀ g₁ P) W) x =
    Tensor0SBundle.Tensor0SSpace.toModel
      (sharpGradKoszulBiContrFib (I := I) g₀ g₁ P x
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
            Tensor0SBundle.Tensor0SSpace 2 I x from
          W.toSection x) (unitTensor (I := I) (M := M) x))) from by
    rw [unitModel, appCc_toSection]
    rfl]
  rw [sharpGradKoszulBiContrFib, sharpGradKoszulBiContrFibFixedFrame_toModel]

omit [I.Boundaryless] in
private lemma foldRF_eval (g₀ g₁ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2)
    (W : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 2 2
          (ricciArmRicciFoldRemainderField (I := I) (M := M) g₀ g₁ P) W) x v =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        Tensor0SBundle.Tensor0SSpace.toModel
            ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
                Tensor0SBundle.Tensor0SSpace 2 I x from
              W.toSection x) (unitTensor (I := I) (M := M) x))
            ![(smoothOrthoFrame (I := I) g₁ x a x : E),
              (smoothOrthoFrame (I := I) g₁ x b x : E)] *
          ricciFoldKernelBilin (I := I) g₀ P x
            (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x)
            (v 0) (v 1) := by
  rw [show unitModel (I := I) (M := M) g₀ 2
      (operatorFieldApply (I := I) (M := M) g₀ 2 2
        (ricciArmRicciFoldRemainderField (I := I) (M := M) g₀ g₁ P) W) x =
    Tensor0SBundle.Tensor0SSpace.toModel
      (ricciFoldBiContrFib (I := I) g₀ g₁ P x
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
            Tensor0SBundle.Tensor0SSpace 2 I x from
          W.toSection x) (unitTensor (I := I) (M := M) x))) from by
    rw [unitModel, appCc_toSection]
    rfl]
  rw [ricciFoldBiContrFib, ricciFoldBiContrFibFixedFrame_toModel]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma foldHtie_zero (g₀ : SmoothRiemannianMetric I M) :
    ∀ (y : M) (v w : TangentSpace I y),
      g₀.inner y v w = g₀.inner y v w +
        ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2) y v w := by
  intro y v w
  rw [ccTensorBilinSymm_apply, ccTensorBilin_zero_weight, ccTensorBilin_zero_weight]
  ring

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma foldPsymm_zero (g₀ : SmoothRiemannianMetric I M) :
    ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2) x v w =
        smoothCcTensorBilinForm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2) x w v := by
  intro x v w
  rw [ccTensorBilin_zero_weight, ccTensorBilin_zero_weight]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem foldAppCc_sub_left (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ₁ Φ₂ : SmoothCcTensor g r s) (W : SmoothCcTensor g 0 r) :
    operatorFieldApply (I := I) (M := M) g r s (Φ₁ - Φ₂) W =
      operatorFieldApply (I := I) (M := M) g r s Φ₁ W - operatorFieldApply (I := I) (M := M) g r s Φ₂ W := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((operatorFieldApply (I := I) (M := M) g r s Φ₁ W
      - operatorFieldApply (I := I) (M := M) g r s Φ₂ W).toSection x) =
      (operatorFieldApply (I := I) (M := M) g r s Φ₁ W).toSection x -
        (operatorFieldApply (I := I) (M := M) g r s Φ₂ W).toSection x from rfl]
  rw [appCc_toSection, appCc_toSection, appCc_toSection]
  rw [show ((Φ₁ - Φ₂).toSection x : TensorRSSpace r s I x) =
      Φ₁.toSection x - Φ₂.toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  rw [ContinuousLinearMap.sub_comp]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem foldSymmS_eq_self (g₀ : SmoothRiemannianMetric I M)
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


theorem ricciArmOrder0RiemannHalfBackgroundDifference_appCc_eq_residualFieldSum_add_refoldKernelSecondGradient
    (g₀ g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
    (hPsymm : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ P x v w = smoothCcTensorBilinForm (I := I) g₀ P x w v)
    (W : SmoothCcTensor g₀ 0 2) :
    (1 / 2 : ℝ) •
        (operatorFieldApply (I := I) (M := M) g₀ 2 2
            (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁) W
          - operatorFieldApply (I := I) (M := M) g₀ 2 2
              (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) W) =
      operatorFieldApply (I := I) (M := M) g₀ 2 2
          (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁
            + (ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 2
                  (ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₁
                    - ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₀)
                  (ccInputSlotSwapField (I := I) (M := M) g₀)
                + (1 / 2 : ℝ) •
                    ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀ g₁ P
                - ricciArmRicciFoldRemainderField (I := I) (M := M) g₀ g₁ P)) W
        + operatorFieldApply (I := I) (M := M) g₀ 4 2
            (curvatureActionKernelCoeffField (I := I) (M := M) g₀ g₁
              (ccTensorUnitValueSection (I := I) (M := M) g₀ W)
              (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ W)
              (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
              (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1)
            (iteratedCovGrad (I := I) g₀ 0 2 2 P) := by
  classical
  have hsymmS : ccTensor02Symm (I := I) (M := M) g₀ P = P :=
    foldSymmS_eq_self (I := I) (M := M) g₀ P hPsymm
  rw [appCc_add_left (I := I) (M := M) g₀ 2 2, foldAppCc_sub_left (I := I) (M := M) g₀ 2 2,
    appCc_add_left (I := I) (M := M) g₀ 2 2, appCc_smul_left (I := I) (M := M) g₀ 2 2]
  refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀ (fun x => ?_)
  refine ContinuousMultilinearMap.ext (fun v => ?_)
  rw [unitModel_smul_apply_loc (I := I) (M := M) g₀ 2 (1 / 2 : ℝ) _ x v,
    unitModel_sub_apply_loc (I := I) (M := M) g₀ 2 _ _ x v]
  rw [unitModel_add_loc (I := I) (M := M) g₀ 2 _ _ x, ContinuousMultilinearMap.add_apply,
    unitModel_add_loc (I := I) (M := M) g₀ 2 _ _ x, ContinuousMultilinearMap.add_apply,
    unitModel_sub_loc (I := I) (M := M) g₀ 2 _ _ x, ContinuousMultilinearMap.sub_apply,
    unitModel_add_loc (I := I) (M := M) g₀ 2 _ _ x, ContinuousMultilinearMap.add_apply,
    unitModel_smul_apply_loc (I := I) (M := M) g₀ 2 (1 / 2 : ℝ) _ x v]
  rw [ricciArmOrder0RiemannCoeff_appCc_eq (I := I) (M := M) g₀ g₁ W x v,
    ricciArmOrder0RiemannCoeff_appCc_eq (I := I) (M := M) g₀ g₀ W x v]
  rw [foldQtrue_eval (I := I) (M := M) g₀ g₁ W x v,
    foldSwapBgR_eval (I := I) (M := M) g₀ g₁ W x v,
    foldSGK_eval (I := I) (M := M) g₀ g₁ P W x v,
    foldRF_eval (I := I) (M := M) g₀ g₁ P W x v,
    foldKernelTerm_eval (I := I) (M := M) g₀ g₁
      (ccTensorUnitValueSection (I := I) (M := M) g₀ W)
      (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ W)
      (iteratedCovGrad (I := I) g₀ 0 2 2 P) x v]
  have hWkernel : ∀ a b : Fin (Module.finrank ℝ E),
      Tensor0SBundle.Tensor0SSpace.toModel
          (ccTensorUnitValueSection (I := I) (M := M) g₀ W x)
          ![(smoothOrthoFrame (I := I) g₁ x a x : E),
            (smoothOrthoFrame (I := I) g₁ x b x : E)] =
      Tensor0SBundle.Tensor0SSpace.toModel
          ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
              Tensor0SBundle.Tensor0SSpace 2 I x from
            W.toSection x) (unitTensor (I := I) (M := M) x))
          ![(smoothOrthoFrame (I := I) g₁ x a x : E),
            (smoothOrthoFrame (I := I) g₁ x b x : E)] := fun a b => rfl
  have hdonor1 : (2 : ℝ) * (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
      g₁.inner x
          (riemannOp (LeviCivita (I := I) g₁) x (v 0)
            (smoothOrthoFrame (I := I) g₁ x a x)
            (smoothOrthoFrame (I := I) g₁ x b x)) (v 1) *
        unitModel (I := I) (M := M) g₀ 2 W x
          (fun j => if j = 0 then smoothOrthoFrame (I := I) g₁ x a x
            else smoothOrthoFrame (I := I) g₁ x b x)) =
      (2 : ℝ) * (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        Tensor0SBundle.Tensor0SSpace.toModel
            ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
                Tensor0SBundle.Tensor0SSpace 2 I x from
              W.toSection x) (unitTensor (I := I) (M := M) x))
            ![(smoothOrthoFrame (I := I) g₁ x a x : E),
              (smoothOrthoFrame (I := I) g₁ x b x : E)] *
          g₁.inner x
            (riemannOp (LeviCivita (I := I) g₁) x (v 0)
              (smoothOrthoFrame (I := I) g₁ x a x)
              (smoothOrthoFrame (I := I) g₁ x b x)) (v 1)) := by
    congr 1
    refine Finset.sum_congr rfl (fun a _ => ?_)
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [foldDonorWeight_eq (I := I) (M := M) g₀ W x]
    ring
  have hdonor0 : (2 : ℝ) * (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
      g₀.inner x
          (riemannOp (LeviCivita (I := I) g₀) x (v 0)
            (smoothOrthoFrame (I := I) g₀ x a x)
            (smoothOrthoFrame (I := I) g₀ x b x)) (v 1) *
        unitModel (I := I) (M := M) g₀ 2 W x
          (fun j => if j = 0 then smoothOrthoFrame (I := I) g₀ x a x
            else smoothOrthoFrame (I := I) g₀ x b x)) =
      (2 : ℝ) * (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        Tensor0SBundle.Tensor0SSpace.toModel
            ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
                Tensor0SBundle.Tensor0SSpace 2 I x from
              W.toSection x) (unitTensor (I := I) (M := M) x))
            ![(smoothOrthoFrame (I := I) g₀ x a x : E),
              (smoothOrthoFrame (I := I) g₀ x b x : E)] *
          g₀.inner x
            (riemannOp (LeviCivita (I := I) g₀) x (v 0)
              (smoothOrthoFrame (I := I) g₀ x a x)
              (smoothOrthoFrame (I := I) g₀ x b x)) (v 1)) := by
    congr 1
    refine Finset.sum_congr rfl (fun a _ => ?_)
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [foldDonorWeight_eq (I := I) (M := M) g₀ W x]
    ring
  rw [hdonor1, hdonor0]
  have hker2 : (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
      Tensor0SBundle.Tensor0SSpace.toModel
          (ccTensorUnitValueSection (I := I) (M := M) g₀ W x)
          ![(smoothOrthoFrame (I := I) g₁ x a x : E),
            (smoothOrthoFrame (I := I) g₁ x b x : E)] *
        ((1 / 2 : ℝ) *
          (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 P) x
              ![v 0, smoothOrthoFrame (I := I) g₁ x b x,
                smoothOrthoFrame (I := I) g₁ x a x, v 1]
            + unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 P) x
                ![smoothOrthoFrame (I := I) g₁ x a x, v 1, v 0,
                  smoothOrthoFrame (I := I) g₁ x b x]
            - unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 P) x
                ![v 0, v 1, smoothOrthoFrame (I := I) g₁ x a x,
                  smoothOrthoFrame (I := I) g₁ x b x]
            - unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 P) x
                ![smoothOrthoFrame (I := I) g₁ x a x,
                  smoothOrthoFrame (I := I) g₁ x b x, v 0, v 1]))) =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        Tensor0SBundle.Tensor0SSpace.toModel
            ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
                Tensor0SBundle.Tensor0SSpace 2 I x from
              W.toSection x) (unitTensor (I := I) (M := M) x))
            ![(smoothOrthoFrame (I := I) g₁ x a x : E),
              (smoothOrthoFrame (I := I) g₁ x b x : E)] *
          ((1 / 2 : ℝ) *
            (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 P) x
                ![v 0, smoothOrthoFrame (I := I) g₁ x b x,
                  smoothOrthoFrame (I := I) g₁ x a x, v 1]
              + unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 P) x
                  ![smoothOrthoFrame (I := I) g₁ x a x, v 1, v 0,
                    smoothOrthoFrame (I := I) g₁ x b x]
              - unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 P) x
                  ![v 0, v 1, smoothOrthoFrame (I := I) g₁ x a x,
                    smoothOrthoFrame (I := I) g₁ x b x]
              - unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 P) x
                  ![smoothOrthoFrame (I := I) g₁ x a x,
                    smoothOrthoFrame (I := I) g₁ x b x, v 0, v 1])) :=
    Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => by
      rw [hWkernel a b]))
  rw [hker2]
  have hfold : ∀ a b : Fin (Module.finrank ℝ E),
      g₁.inner x (riemannOp (LeviCivita (I := I) g₁) x (v 0)
          (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x)) (v 1) =
        g₁.inner x (riemannOp (LeviCivita (I := I) g₀) x (v 0)
            (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x)) (v 1)
        + (1 / 2 : ℝ) *
            (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 P) x
                ![v 0, smoothOrthoFrame (I := I) g₁ x a x,
                  smoothOrthoFrame (I := I) g₁ x b x, v 1]
              - unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 P) x
                  ![smoothOrthoFrame (I := I) g₁ x a x, v 0,
                    smoothOrthoFrame (I := I) g₁ x b x, v 1])
        + (1 / 2 : ℝ) *
            (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 P) x
                ![v 0, smoothOrthoFrame (I := I) g₁ x b x,
                  smoothOrthoFrame (I := I) g₁ x a x, v 1]
              + unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 P) x
                  ![smoothOrthoFrame (I := I) g₁ x a x, v 1, v 0,
                    smoothOrthoFrame (I := I) g₁ x b x]
              - unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 P) x
                  ![v 0, v 1, smoothOrthoFrame (I := I) g₁ x a x,
                    smoothOrthoFrame (I := I) g₁ x b x]
              - unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 P) x
                  ![smoothOrthoFrame (I := I) g₁ x a x,
                    smoothOrthoFrame (I := I) g₁ x b x, v 0, v 1])
        + (connDiffIteratedCommKernelBilin (I := I) g₀ g₁ x
              (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x)
              (v 0) (v 1)
            + sharpGradKoszulKernelBilin (I := I) g₀ g₁ P x
                (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x)
                (v 0) (v 1)) := by
    intro a b
    have h := foldCore_pointwise (I := I) (M := M) g₀ g₁ P htie
      ⟨smoothExtensionTangent (I := I) x (v 0),
        smoothExtensionTangent_contMDiff (I := I) x (v 0)⟩
      ⟨smoothOrthoFrame (I := I) g₁ x a, smoothOrthoFrame_smooth (I := I) g₁ x a⟩
      ⟨smoothOrthoFrame (I := I) g₁ x b, smoothOrthoFrame_smooth (I := I) g₁ x b⟩
      x (v 1)
    rw [hsymmS] at h
    rw [show ((⟨smoothExtensionTangent (I := I) x (v 0),
        smoothExtensionTangent_contMDiff (I := I) x (v 0)⟩ :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) =
      smoothExtensionTangent (I := I) x (v 0) x from rfl] at h
    rw [show ((⟨smoothOrthoFrame (I := I) g₁ x a, smoothOrthoFrame_smooth (I := I) g₁ x a⟩ :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) =
      smoothOrthoFrame (I := I) g₁ x a x from rfl] at h
    rw [show ((⟨smoothOrthoFrame (I := I) g₁ x b, smoothOrthoFrame_smooth (I := I) g₁ x b⟩ :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) =
      smoothOrthoFrame (I := I) g₁ x b x from rfl] at h
    rw [smoothExtensionTangent_eq (I := I) x (v 0)] at h
    have hq := foldQuadKernel_split (I := I) (M := M) g₀ g₁ P htie hsymmS x
      (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x) (v 0) (v 1)
    linarith [h, hq]
  have hric : ∀ a b : Fin (Module.finrank ℝ E),
      (1 / 2 : ℝ) *
          (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 P) x
              ![v 0, smoothOrthoFrame (I := I) g₁ x a x,
                smoothOrthoFrame (I := I) g₁ x b x, v 1]
            - unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 P) x
                ![smoothOrthoFrame (I := I) g₁ x a x, v 0,
                  smoothOrthoFrame (I := I) g₁ x b x, v 1]) =
        ricciFoldKernelBilin (I := I) g₀ P x
          (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x)
          (v 0) (v 1) := by
    intro a b
    have h := foldG2_pair_antisym (I := I) (M := M) g₀ P
      (X := smoothExtensionTangent (I := I) x (v 0))
      (Y := smoothOrthoFrame (I := I) g₁ x a)
      (smoothExtensionTangent_contMDiff (I := I) x (v 0))
      (smoothOrthoFrame_smooth (I := I) g₁ x a)
      x (smoothOrthoFrame (I := I) g₁ x b x) (v 1)
    rw [smoothExtensionTangent_eq (I := I) x (v 0)] at h
    rw [ricciFoldKernelBilin_apply]
    linarith [h]
  have hcomb : ∀ a b : Fin (Module.finrank ℝ E),
      Tensor0SBundle.Tensor0SSpace.toModel
          ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
              Tensor0SBundle.Tensor0SSpace 2 I x from
            W.toSection x) (unitTensor (I := I) (M := M) x))
          ![(smoothOrthoFrame (I := I) g₁ x a x : E),
            (smoothOrthoFrame (I := I) g₁ x b x : E)] *
        g₁.inner x (riemannOp (LeviCivita (I := I) g₁) x (v 0)
          (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x)) (v 1) =
      Tensor0SBundle.Tensor0SSpace.toModel
          ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
              Tensor0SBundle.Tensor0SSpace 2 I x from
            W.toSection x) (unitTensor (I := I) (M := M) x))
          ![(smoothOrthoFrame (I := I) g₁ x a x : E),
            (smoothOrthoFrame (I := I) g₁ x b x : E)] *
        g₁.inner x (riemannOp (LeviCivita (I := I) g₀) x (v 0)
          (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x)) (v 1)
      + Tensor0SBundle.Tensor0SSpace.toModel
          ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
              Tensor0SBundle.Tensor0SSpace 2 I x from
            W.toSection x) (unitTensor (I := I) (M := M) x))
          ![(smoothOrthoFrame (I := I) g₁ x a x : E),
            (smoothOrthoFrame (I := I) g₁ x b x : E)] *
          ricciFoldKernelBilin (I := I) g₀ P x
            (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x)
            (v 0) (v 1)
      + Tensor0SBundle.Tensor0SSpace.toModel
          ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
              Tensor0SBundle.Tensor0SSpace 2 I x from
            W.toSection x) (unitTensor (I := I) (M := M) x))
          ![(smoothOrthoFrame (I := I) g₁ x a x : E),
            (smoothOrthoFrame (I := I) g₁ x b x : E)] *
          ((1 / 2 : ℝ) *
            (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 P) x
                ![v 0, smoothOrthoFrame (I := I) g₁ x b x,
                  smoothOrthoFrame (I := I) g₁ x a x, v 1]
              + unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 P) x
                  ![smoothOrthoFrame (I := I) g₁ x a x, v 1, v 0,
                    smoothOrthoFrame (I := I) g₁ x b x]
              - unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 P) x
                  ![v 0, v 1, smoothOrthoFrame (I := I) g₁ x a x,
                    smoothOrthoFrame (I := I) g₁ x b x]
              - unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 P) x
                  ![smoothOrthoFrame (I := I) g₁ x a x,
                    smoothOrthoFrame (I := I) g₁ x b x, v 0, v 1]))
      + (Tensor0SBundle.Tensor0SSpace.toModel
          ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
              Tensor0SBundle.Tensor0SSpace 2 I x from
            W.toSection x) (unitTensor (I := I) (M := M) x))
          ![(smoothOrthoFrame (I := I) g₁ x a x : E),
            (smoothOrthoFrame (I := I) g₁ x b x : E)] *
          connDiffIteratedCommKernelBilin (I := I) g₀ g₁ x
            (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x)
            (v 0) (v 1)
        + Tensor0SBundle.Tensor0SSpace.toModel
          ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
              Tensor0SBundle.Tensor0SSpace 2 I x from
            W.toSection x) (unitTensor (I := I) (M := M) x))
          ![(smoothOrthoFrame (I := I) g₁ x a x : E),
            (smoothOrthoFrame (I := I) g₁ x b x : E)] *
          sharpGradKoszulKernelBilin (I := I) g₀ g₁ P x
            (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x)
            (v 0) (v 1)) := by
    intro a b
    have e := hfold a b
    rw [hric a b] at e
    rw [e]
    ring
  have hS1 := Finset.sum_congr rfl (fun a (_ : a ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ E)))) =>
    Finset.sum_congr rfl (fun b (_ : b ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ E)))) =>
      hcomb a b))
  simp only [Finset.sum_add_distrib] at hS1
  have hrow1 : ∀ a : Fin (Module.finrank ℝ E),
      ∑ b : Fin (Module.finrank ℝ E),
        Tensor0SBundle.Tensor0SSpace.toModel
            ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
              Tensor0SBundle.Tensor0SSpace 2 I x from
            W.toSection x) (unitTensor (I := I) (M := M) x))
            ![(smoothOrthoFrame (I := I) g₁ x a x : E),
              (smoothOrthoFrame (I := I) g₁ x b x : E)] *
          g₁.inner x (riemannOp (LeviCivita (I := I) g₀) x (v 0)
            (smoothOrthoFrame (I := I) g₁ x a x)
            (smoothOrthoFrame (I := I) g₁ x b x)) (v 1) =
        Tensor0SBundle.Tensor0SSpace.toModel
            ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
              Tensor0SBundle.Tensor0SSpace 2 I x from
            W.toSection x) (unitTensor (I := I) (M := M) x))
            ![(smoothOrthoFrame (I := I) g₁ x a x : E),
              (riemannOp (LeviCivita (I := I) g₀) x
                (smoothOrthoFrame (I := I) g₁ x a x) (v 0) (v 1) : E)] +
        ∑ b : Fin (Module.finrank ℝ E),
          Tensor0SBundle.Tensor0SSpace.toModel
              ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
              Tensor0SBundle.Tensor0SSpace 2 I x from
            W.toSection x) (unitTensor (I := I) (M := M) x))
              ![(smoothOrthoFrame (I := I) g₁ x a x : E),
                (smoothOrthoFrame (I := I) g₁ x b x : E)] *
            (smoothCcTensorBilinForm (I := I) g₀ P x (smoothOrthoFrame (I := I) g₁ x b x)
                (riemannOp (LeviCivita (I := I) g₀) x (v 0)
                  (smoothOrthoFrame (I := I) g₁ x a x) (v 1))
              + smoothCcTensorBilinForm (I := I) g₀ P x
                  (riemannOp (LeviCivita (I := I) g₀) x (v 0)
                    (smoothOrthoFrame (I := I) g₁ x a x)
                    (smoothOrthoFrame (I := I) g₁ x b x)) (v 1)) :=
    fun a => foldMovingTraceRow (I := I) (M := M) g₀ g₁ P htie hPsymm x
      ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
              Tensor0SBundle.Tensor0SSpace 2 I x from
            W.toSection x) (unitTensor (I := I) (M := M) x)) (v 0) (v 1) a
  have hpt : ∀ a b : Fin (Module.finrank ℝ E),
      Tensor0SBundle.Tensor0SSpace.toModel
          ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
              Tensor0SBundle.Tensor0SSpace 2 I x from
            W.toSection x) (unitTensor (I := I) (M := M) x))
          ![(smoothOrthoFrame (I := I) g₁ x a x : E),
            (smoothOrthoFrame (I := I) g₁ x b x : E)] *
        (smoothCcTensorBilinForm (I := I) g₀ P x (smoothOrthoFrame (I := I) g₁ x b x)
            (riemannOp (LeviCivita (I := I) g₀) x (v 0)
              (smoothOrthoFrame (I := I) g₁ x a x) (v 1))
          + smoothCcTensorBilinForm (I := I) g₀ P x
              (riemannOp (LeviCivita (I := I) g₀) x (v 0)
                (smoothOrthoFrame (I := I) g₁ x a x)
                (smoothOrthoFrame (I := I) g₁ x b x)) (v 1)) =
      (-2 : ℝ) *
        (Tensor0SBundle.Tensor0SSpace.toModel
            ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
              Tensor0SBundle.Tensor0SSpace 2 I x from
            W.toSection x) (unitTensor (I := I) (M := M) x))
            ![(smoothOrthoFrame (I := I) g₁ x a x : E),
              (smoothOrthoFrame (I := I) g₁ x b x : E)] *
          ricciFoldKernelBilin (I := I) g₀ P x
            (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x)
            (v 0) (v 1)) := by
    intro a b
    rw [ricciFoldKernelBilin_apply]
    ring
  have hrowsum1 : (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
      Tensor0SBundle.Tensor0SSpace.toModel
          ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
              Tensor0SBundle.Tensor0SSpace 2 I x from
            W.toSection x) (unitTensor (I := I) (M := M) x))
          ![(smoothOrthoFrame (I := I) g₁ x a x : E),
            (smoothOrthoFrame (I := I) g₁ x b x : E)] *
        g₁.inner x (riemannOp (LeviCivita (I := I) g₀) x (v 0)
          (smoothOrthoFrame (I := I) g₁ x a x)
          (smoothOrthoFrame (I := I) g₁ x b x)) (v 1)) =
      (∑ a : Fin (Module.finrank ℝ E),
        Tensor0SBundle.Tensor0SSpace.toModel
            ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
              Tensor0SBundle.Tensor0SSpace 2 I x from
            W.toSection x) (unitTensor (I := I) (M := M) x))
            ![(smoothOrthoFrame (I := I) g₁ x a x : E),
              (riemannOp (LeviCivita (I := I) g₀) x
                (smoothOrthoFrame (I := I) g₁ x a x) (v 0) (v 1) : E)])
      + (-2 : ℝ) * (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        Tensor0SBundle.Tensor0SSpace.toModel
            ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
              Tensor0SBundle.Tensor0SSpace 2 I x from
            W.toSection x) (unitTensor (I := I) (M := M) x))
            ![(smoothOrthoFrame (I := I) g₁ x a x : E),
              (smoothOrthoFrame (I := I) g₁ x b x : E)] *
          ricciFoldKernelBilin (I := I) g₀ P x
            (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x)
            (v 0) (v 1)) := by
    rw [Finset.sum_congr rfl (fun a (_ : a ∈ Finset.univ) => hrow1 a)]
    rw [Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_congr rfl (fun a (_ : a ∈ Finset.univ) =>
      Finset.sum_congr rfl (fun b (_ : b ∈ Finset.univ) => hpt a b))]
    rw [Finset.sum_congr rfl (fun a (_ : a ∈ Finset.univ) =>
      (Finset.mul_sum Finset.univ _ (-2 : ℝ)).symm)]
    rw [(Finset.mul_sum Finset.univ _ (-2 : ℝ)).symm]
  have hrow0 : ∀ a : Fin (Module.finrank ℝ E),
      ∑ b : Fin (Module.finrank ℝ E),
        Tensor0SBundle.Tensor0SSpace.toModel
            ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
              Tensor0SBundle.Tensor0SSpace 2 I x from
            W.toSection x) (unitTensor (I := I) (M := M) x))
            ![(smoothOrthoFrame (I := I) g₀ x a x : E),
              (smoothOrthoFrame (I := I) g₀ x b x : E)] *
          g₀.inner x (riemannOp (LeviCivita (I := I) g₀) x (v 0)
            (smoothOrthoFrame (I := I) g₀ x a x)
            (smoothOrthoFrame (I := I) g₀ x b x)) (v 1) =
        Tensor0SBundle.Tensor0SSpace.toModel
            ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
              Tensor0SBundle.Tensor0SSpace 2 I x from
            W.toSection x) (unitTensor (I := I) (M := M) x))
            ![(smoothOrthoFrame (I := I) g₀ x a x : E),
              (riemannOp (LeviCivita (I := I) g₀) x
                (smoothOrthoFrame (I := I) g₀ x a x) (v 0) (v 1) : E)] := by
    intro a
    have h := foldMovingTraceRow (I := I) (M := M) g₀ g₀ (0 : SmoothCcTensor g₀ 0 2)
      (foldHtie_zero (I := I) (M := M) g₀) (foldPsymm_zero (I := I) (M := M) g₀) x
      ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
              Tensor0SBundle.Tensor0SSpace 2 I x from
            W.toSection x) (unitTensor (I := I) (M := M) x)) (v 0) (v 1) a
    have hz : (∑ b : Fin (Module.finrank ℝ E),
        Tensor0SBundle.Tensor0SSpace.toModel
            ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
              Tensor0SBundle.Tensor0SSpace 2 I x from
            W.toSection x) (unitTensor (I := I) (M := M) x))
            ![(smoothOrthoFrame (I := I) g₀ x a x : E),
              (smoothOrthoFrame (I := I) g₀ x b x : E)] *
          (smoothCcTensorBilinForm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2) x
              (smoothOrthoFrame (I := I) g₀ x b x)
              (riemannOp (LeviCivita (I := I) g₀) x (v 0)
                (smoothOrthoFrame (I := I) g₀ x a x) (v 1))
            + smoothCcTensorBilinForm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2) x
                (riemannOp (LeviCivita (I := I) g₀) x (v 0)
                  (smoothOrthoFrame (I := I) g₀ x a x)
                  (smoothOrthoFrame (I := I) g₀ x b x)) (v 1))) = 0 :=
      Finset.sum_eq_zero (fun b _ => by
        rw [ccTensorBilin_zero_weight, ccTensorBilin_zero_weight]
        ring)
    rw [h, hz, add_zero]
  have hrowsum0 := Finset.sum_congr rfl
    (fun a (_ : a ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ E)))) => hrow0 a)
  rw [hS1, hrowsum1, hrowsum0]
  ring

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
