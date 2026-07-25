import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.MetricDiffCovGradKoszul
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.ConnDiffCovGradBridge
import DifferentialGeometry.Geometry.Metric.InverseMetricField
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.InverseMetricFieldParallel
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CometricDoubleTraceField
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovGradSlotPermutationNaturality
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnDiffPalatini
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.RicciTraceCarrier
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.SlotFreeCurvatureOperatorField
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifferenceKoszulSecondCovGrad
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifferencePrincipalEndomorphismTrace


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck

section NormedSpaceModel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

noncomputable def ccTensor02Symm (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2) :
    SmoothCcTensor g₀ 0 2 :=
  (1 / 2 : ℝ) • (T + domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma unitModel_add2 (g₀ : SmoothRiemannianMetric I M)
    (S S' : SmoothCcTensor g₀ 0 2) (x : M) :
    unitModel (I := I) (M := M) g₀ 2 (S + S') x =
      unitModel (I := I) (M := M) g₀ 2 S x + unitModel (I := I) (M := M) g₀ 2 S' x := by
  simp only [unitModel]
  rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply,
    ContinuousLinearMap.add_apply, Tensor0SSpace.toModel_add]


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma unitModel_eq_ccTensorBilin (g₀ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (b : M) (u w : TangentSpace I b) :
    unitModel (I := I) (M := M) g₀ 2 S b ![u, w] = smoothCcTensorBilinForm (I := I) g₀ S b u w := by
  rw [ccTensorBilin_apply (I := I) g₀ S b u w, ccTensorModel]
  rw [show ccTensorMultilinear (I := I) g₀ S b =
      (show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace 2 I b from S.toSection b)
        (unitZeroSec (I := I) (M := M) b) from rfl]
  rw [unitModel]
  refine congrArg _ ?_
  funext k
  fin_cases k <;> rfl


omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma ccTensorBilin_domDomCongrSection_swap (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (b : M) (u w : TangentSpace I b) :
    smoothCcTensorBilinForm (I := I) g₀
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T) b u w =
      smoothCcTensorBilinForm (I := I) g₀ T b w u := by
  rw [← unitModel_eq_ccTensorBilin (I := I) (M := M) g₀ _ b u w,
      ← unitModel_eq_ccTensorBilin (I := I) (M := M) g₀ T b w u]
  rw [domDomCongrSection_unitModel (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T b,
      ContinuousMultilinearMap.domDomCongr_apply]
  congr 1
  funext k
  fin_cases k <;> simp [Equiv.swap_apply_left, Equiv.swap_apply_right]


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma ccTensorBilin_add (g₀ : SmoothRiemannianMetric I M)
    (S T : SmoothCcTensor g₀ 0 2) (b : M) (u w : TangentSpace I b) :
    smoothCcTensorBilinForm (I := I) g₀ (S + T) b u w =
      smoothCcTensorBilinForm (I := I) g₀ S b u w + smoothCcTensorBilinForm (I := I) g₀ T b u w := by
  rw [← unitModel_eq_ccTensorBilin (I := I) (M := M) g₀ (S + T) b u w,
      ← unitModel_eq_ccTensorBilin (I := I) (M := M) g₀ S b u w,
      ← unitModel_eq_ccTensorBilin (I := I) (M := M) g₀ T b u w]
  rw [unitModel_add2 (I := I) (M := M) g₀ S T b, ContinuousMultilinearMap.add_apply]


omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma ccTensorBilin_smul (g₀ : SmoothRiemannianMetric I M)
    (c : ℝ) (S : SmoothCcTensor g₀ 0 2) (b : M) (u w : TangentSpace I b) :
    smoothCcTensorBilinForm (I := I) g₀ (c • S) b u w =
      c * smoothCcTensorBilinForm (I := I) g₀ S b u w := by
  rw [ccTensorBilin_apply, ccTensorBilin_apply, ccTensorModel_smul,
    ContinuousMultilinearMap.smul_apply, smul_eq_mul]


omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem ccTensorBilin_symmS (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (b : M) (u w : TangentSpace I b) :
    smoothCcTensorBilinForm (I := I) g₀ (ccTensor02Symm (I := I) (M := M) g₀ T) b u w =
      ccTensorBilinSymm (I := I) g₀ T b u w := by
  rw [ccTensor02Symm, ccTensorBilin_smul, ccTensorBilin_add,
    ccTensorBilin_domDomCongrSection_swap (I := I) (M := M) g₀ T b u w,
    ccTensorBilinSymm_apply]


omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem symmS_hbil_of_realize (g₀ g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (hg₁ : ∀ (b : M) (u w : TangentSpace I b),
      g₁.inner b u w = g₀.inner b u w + ccTensorBilinSymm (I := I) g₀ T b u w)
    (b : M) (u w : TangentSpace I b) :
    smoothCcTensorBilinForm (I := I) g₀ (ccTensor02Symm (I := I) (M := M) g₀ T) b u w =
      g₁.inner b u w - g₀.inner b u w := by
  rw [ccTensorBilin_symmS (I := I) (M := M) g₀ T b u w, hg₁ b u w]
  ring


omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma unitModel_domDomCongrSection_swap_add (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2) (x : M) :
    unitModel (I := I) (M := M) g₀ 2
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) (T + T')) x =
      unitModel (I := I) (M := M) g₀ 2
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T) x +
        unitModel (I := I) (M := M) g₀ 2
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T') x := by
  rw [domDomCongrSection_unitModel, domDomCongrSection_unitModel, domDomCongrSection_unitModel,
    unitModel_add2]
  apply ContinuousMultilinearMap.ext
  intro m
  rw [ContinuousMultilinearMap.domDomCongr_apply, ContinuousMultilinearMap.add_apply,
    ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.domDomCongr_apply,
    ContinuousMultilinearMap.domDomCongr_apply]


omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma unitModel_domDomCongrSection_swap_smul (g₀ : SmoothRiemannianMetric I M)
    (c : ℝ) (T : SmoothCcTensor g₀ 0 2) (x : M) :
    unitModel (I := I) (M := M) g₀ 2
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) (c • T)) x =
      c • unitModel (I := I) (M := M) g₀ 2
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T) x := by
  rw [domDomCongrSection_unitModel, domDomCongrSection_unitModel]
  have hsmul : unitModel (I := I) (M := M) g₀ 2 (c • T) x =
      c • unitModel (I := I) (M := M) g₀ 2 T x := by
    simp only [unitModel]
    rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
      ContinuousLinearMap.smul_apply, Tensor0SSpace.toModel_smul]
  rw [hsmul]
  apply ContinuousMultilinearMap.ext
  intro m
  rw [ContinuousMultilinearMap.domDomCongr_apply, ContinuousMultilinearMap.smul_apply,
    ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.domDomCongr_apply]


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma unitModel_smul (g₀ : SmoothRiemannianMetric I M)
    (c : ℝ) (T : SmoothCcTensor g₀ 0 2) (x : M) :
    unitModel (I := I) (M := M) g₀ 2 (c • T) x =
      c • unitModel (I := I) (M := M) g₀ 2 T x := by
  simp only [unitModel]
  rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
    ContinuousLinearMap.smul_apply, Tensor0SSpace.toModel_smul]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem symmS_add (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2) :
    ccTensor02Symm (I := I) (M := M) g₀ (T + T') =
      ccTensor02Symm (I := I) (M := M) g₀ T + ccTensor02Symm (I := I) (M := M) g₀ T' := by
  apply smoothCcTensor_ext_of_unitModel
  intro x
  simp only [ccTensor02Symm, unitModel_smul, unitModel_add2, unitModel_domDomCongrSection_swap_add]
  module

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem symmS_smul (g₀ : SmoothRiemannianMetric I M) (c : ℝ) (T : SmoothCcTensor g₀ 0 2) :
    ccTensor02Symm (I := I) (M := M) g₀ (c • T) = c • ccTensor02Symm (I := I) (M := M) g₀ T := by
  apply smoothCcTensor_ext_of_unitModel
  intro x
  simp only [ccTensor02Symm, unitModel_smul, unitModel_add2, unitModel_domDomCongrSection_swap_smul]
  module

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem symmS_neg (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2) :
    ccTensor02Symm (I := I) (M := M) g₀ (-T) = -ccTensor02Symm (I := I) (M := M) g₀ T := by
  have h := symmS_smul (I := I) (M := M) g₀ (-1 : ℝ) T
  rw [neg_one_smul, neg_one_smul] at h
  exact h

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [BoundarylessManifold I M] in
theorem symmS_sub (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2) :
    ccTensor02Symm (I := I) (M := M) g₀ (T - T') =
      ccTensor02Symm (I := I) (M := M) g₀ T - ccTensor02Symm (I := I) (M := M) g₀ T' := by
  rw [sub_eq_add_neg, symmS_add, symmS_neg, sub_eq_add_neg]

end NormedSpaceModel

section InnerProductSpaceModel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private def alignedPrincipalEndoCrossMetric (g₀ gop gcov : SmoothRiemannianMetric I M)
    (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) : E →ₗ[ℝ] E where
  toFun := fun v => inverseMetricSharpFib (I := I) gop x
    (dualToCotangent (I := I)
      (((cotangentCov (LeviCivita (I := I) g₀)).toFun
        (fun b => cotangentToCLM (I := I)
          (koszulCovGradCovec (I := I) (M := M) g₀ gcov Z Y b)) x v :
        TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))
  map_add' := fun v v' => by
    rw [show (((cotangentCov (LeviCivita (I := I) g₀)).toFun
        (fun b => cotangentToCLM (I := I)
          (koszulCovGradCovec (I := I) (M := M) g₀ gcov Z Y b)) x (v + v') :
        TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)) =
      (((cotangentCov (LeviCivita (I := I) g₀)).toFun
        (fun b => cotangentToCLM (I := I)
          (koszulCovGradCovec (I := I) (M := M) g₀ gcov Z Y b)) x v :
        TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)) +
      (((cotangentCov (LeviCivita (I := I) g₀)).toFun
        (fun b => cotangentToCLM (I := I)
          (koszulCovGradCovec (I := I) (M := M) g₀ gcov Z Y b)) x v' :
        TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)) from by
      ext w; simp [map_add]]
    rw [dualToCotangent_addC]
    rw [map_add]
  map_smul' := fun c v => by
    rw [show (((cotangentCov (LeviCivita (I := I) g₀)).toFun
        (fun b => cotangentToCLM (I := I)
          (koszulCovGradCovec (I := I) (M := M) g₀ gcov Z Y b)) x (c • v) :
        TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)) =
      c • (((cotangentCov (LeviCivita (I := I) g₀)).toFun
        (fun b => cotangentToCLM (I := I)
          (koszulCovGradCovec (I := I) (M := M) g₀ gcov Z Y b)) x v :
        TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)) from by
      ext w; simp [map_smul]]
    rw [dualToCotangent_smulC]
    rw [map_smul]; rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
@[simp] private lemma alignedPrincipalEndoCcross_apply (g₀ gop gcov : SmoothRiemannianMetric I M)
    (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (v : TangentSpace I x) :
    alignedPrincipalEndoCrossMetric (I := I) (M := M) g₀ gop gcov Z Y x v =
      inverseMetricSharpFib (I := I) gop x
        (dualToCotangent (I := I)
          (((cotangentCov (LeviCivita (I := I) g₀)).toFun
            (fun b => cotangentToCLM (I := I)
              (koszulCovGradCovec (I := I) (M := M) g₀ gcov Z Y b)) x v :
            TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x))) := rfl

private def g1PrincipalVecCcross (g₀ gop gcov : SmoothRiemannianMetric I M)
    (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (v : TangentSpace I x) :
    TangentSpace I x :=
  inverseMetricSharpFib (I := I) gop x
    (dualToCotangent (I := I)
      (((cotangentCov (LeviCivita (I := I) gop)).toFun
        (fun b => cotangentToCLM (I := I)
          (koszulCovGradCovec (I := I) (M := M) g₀ gcov Z Y b)) x v :
        TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))

private def alignCorrVecCrossMetric (g₀ gop gcov : SmoothRiemannianMetric I M)
    (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (v : TangentSpace I x) :
    TangentSpace I x :=
  inverseMetricSharpFib (I := I) gop x
    (dualToCotangent (I := I)
      (-(LinearMap.toContinuousLinearMap
        { toFun := fun w => cotangentToCLM (I := I)
            (koszulCovGradCovec (I := I) (M := M) g₀ gcov Z Y x)
            (PDE.DeTurck.connDiff (I := I) gop g₀ x w v)
          map_add' := by
            intro w w'
            rw [show PDE.DeTurck.connDiff (I := I) gop g₀ x (w + w') v =
              PDE.DeTurck.connDiff (I := I) gop g₀ x w v +
                PDE.DeTurck.connDiff (I := I) gop g₀ x w' v from by rw [map_add]; rfl]
            rw [map_add]
          map_smul' := by
            intro c w
            rw [show PDE.DeTurck.connDiff (I := I) gop g₀ x (c • w) v =
              c • PDE.DeTurck.connDiff (I := I) gop g₀ x w v from by rw [map_smul]; rfl]
            rw [map_smul]; rfl } : TangentSpace I x →L[ℝ] ℝ)))

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma g1Principal_splitCcross
    (g₀ gop gcov : SmoothRiemannianMetric I M)
    (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (v : TangentSpace I x) :
    g1PrincipalVecCcross (I := I) (M := M) g₀ gop gcov Z Y x v =
      inverseMetricSharpFib (I := I) gop x
        (dualToCotangent (I := I)
          (((cotangentCov (LeviCivita (I := I) g₀)).toFun
            (fun b => cotangentToCLM (I := I)
              (koszulCovGradCovec (I := I) (M := M) g₀ gcov Z Y b)) x v :
            TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))
        + alignCorrVecCrossMetric (I := I) (M := M) g₀ gop gcov Z Y x v := by
  classical
  rw [g1PrincipalVecCcross, alignCorrVecCrossMetric]
  rw [← map_add]
  congr 1
  rw [← dualToCotangent_addC]
  congr 1
  ext w
  rw [LinearMap.add_apply]

  have hθ := koszulCovGradCovecCLM_mdiffAtCotangent (I := I) (M := M) g₀ gcov Z Y x
  have halign := cotangentCov_leviCivita_diff (I := I) (M := M) g₀ gop hθ v w
  rw [ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_coe]
  rw [show ((cotangentCov (LeviCivita (I := I) gop)).toFun
        (fun b => cotangentToCLM (I := I)
          (koszulCovGradCovec (I := I) (M := M) g₀ gcov Z Y b)) x v) w =
      ((cotangentCov (LeviCivita (I := I) g₀)).toFun
          (fun b => cotangentToCLM (I := I)
            (koszulCovGradCovec (I := I) (M := M) g₀ gcov Z Y b)) x v) w
        - cotangentToCLM (I := I)
            (koszulCovGradCovec (I := I) (M := M) g₀ gcov Z Y x)
            (PDE.DeTurck.connDiff (I := I) gop g₀ x w v) from by linarith [halign]]
  rw [show ((-(LinearMap.toContinuousLinearMap
        { toFun := fun w => cotangentToCLM (I := I)
            (koszulCovGradCovec (I := I) (M := M) g₀ gcov Z Y x)
            (PDE.DeTurck.connDiff (I := I) gop g₀ x w v)
          map_add' := by
            intro w w'
            rw [show PDE.DeTurck.connDiff (I := I) gop g₀ x (w + w') v =
              PDE.DeTurck.connDiff (I := I) gop g₀ x w v +
                PDE.DeTurck.connDiff (I := I) gop g₀ x w' v from by rw [map_add]; rfl]
            rw [map_add]
          map_smul' := by
            intro c w
            rw [show PDE.DeTurck.connDiff (I := I) gop g₀ x (c • w) v =
              c • PDE.DeTurck.connDiff (I := I) gop g₀ x w v from by rw [map_smul]; rfl]
            rw [map_smul]; rfl } : TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)) w) =
      -(cotangentToCLM (I := I)
        (koszulCovGradCovec (I := I) (M := M) g₀ gcov Z Y x)
        (PDE.DeTurck.connDiff (I := I) gop g₀ x w v)) from rfl]
  ring

omit [NeZero (Module.finrank ℝ E)] in
private lemma alignedPrincipalEndoCcross_inner_secondKoszul
    (g₀ gop gcov : SmoothRiemannianMetric I M) (S' : SmoothCcTensor g₀ 0 2)
    (hbil : ∀ (b : M) (u w : TangentSpace I b),
      smoothCcTensorBilinForm (I := I) g₀ S' b u w = gcov.inner b u w - g₀.inner b u w)
    (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (v ζ : TangentSpace I x) :
    gop.inner x (alignedPrincipalEndoCrossMetric (I := I) (M := M) g₀ gop gcov Z Y x v) ζ =
      (1 / 2 : ℝ) *
          (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S') x
              ![v, Z x, Y x, ζ]
            + unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S') x
                ![v, Y x, Z x, ζ]
            - unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S') x
                ![v, ζ, Z x, Y x])
        + (1 / 2 : ℝ) *
          (unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S') x
              ![(LeviCivita (I := I) g₀).toFun (fun b => Z b) x v, Y x, ζ]
            + unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S') x
                ![Z x, (LeviCivita (I := I) g₀).toFun (fun b => Y b) x v, ζ]
            + unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S') x
                ![(LeviCivita (I := I) g₀).toFun (fun b => Y b) x v, Z x, ζ]
            + unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S') x
                ![Y x, (LeviCivita (I := I) g₀).toFun (fun b => Z b) x v, ζ]
            - unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S') x
                ![ζ, (LeviCivita (I := I) g₀).toFun (fun b => Z b) x v, Y x]
            - unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S') x
                ![ζ, Z x, (LeviCivita (I := I) g₀).toFun (fun b => Y b) x v]) := by
  classical
  let Xf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) x v, smoothExtensionTangent_contMDiff (I := I) x v⟩
  have hXfx : Xf x = v := smoothExtensionTangent_eq (I := I) x v
  rw [alignedPrincipalEndoCcross_apply]
  rw [inverseMetricSharpFib_inner (I := I) gop x _ ζ, cotangentToDualLinear_apply]
  rw [← hXfx]
  have hbridge := koszulCovGradCovec_covDeriv_eq_secondCovGrad (I := I) (M := M) g₀ gcov S' hbil Xf Y Z x ζ
  rw [hXfx]
  rw [hXfx] at hbridge
  rw [hbridge]

omit [NeZero (Module.finrank ℝ E)] in
private lemma alignedPrincipalEndoCcross_trace_eq
    (g₀ gop gcov : SmoothRiemannianMetric I M) (S' : SmoothCcTensor g₀ 0 2)
    (hbil : ∀ (b : M) (u w : TangentSpace I b),
      smoothCcTensorBilinForm (I := I) g₀ S' b u w = gcov.inner b u w - g₀.inner b u w)
    (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    LinearMap.trace ℝ E (alignedPrincipalEndoCrossMetric (I := I) (M := M) g₀ gop gcov Z Y x) =
      unitModel (I := I) (M := M) g₀ 2
          (operatorFieldApply (I := I) (M := M) g₀ 4 2 (ricciArmPrincipalCoeff (I := I) (M := M) g₀ gop)
            (iteratedCovGrad (I := I) g₀ 0 2 2 S')) x ![Z x, Y x]
        + secondKoszulFrameRemainder (I := I) (M := M) g₀ gop S' Z Y x := by
  classical
  rw [← trace_eq_cometricLmodel_pairing_sum (I := I) (M := M) gop x
    (alignedPrincipalEndoCrossMetric (I := I) (M := M) g₀ gop gcov Z Y x)]
  rw [covDerivConnDiff_tracedPrincipal_eq_appCc (I := I) (M := M) g₀ gop S' x ![Z x, Y x]]
  rw [secondKoszulFrameRemainder]
  rw [show (∑ k : Fin (Module.finrank ℝ E),
        gop.inner x
          (alignedPrincipalEndoCrossMetric (I := I) (M := M) g₀ gop gcov Z Y x
            (cometricLmodel (I := I) gop x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k))))
          ((Module.finBasis ℝ E) k)) =
      ∑ k : Fin (Module.finrank ℝ E),
        ((1 / 2 : ℝ) *
          (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S') x
              ![cometricLmodel (I := I) gop x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k)), Z x, Y x, (Module.finBasis ℝ E) k]
            + unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S') x
                ![cometricLmodel (I := I) gop x
                    (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                      ((Module.finBasis ℝ E).cDualBasis k)), Y x, Z x, (Module.finBasis ℝ E) k]
            - unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S') x
                ![cometricLmodel (I := I) gop x
                    (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                      ((Module.finBasis ℝ E).cDualBasis k)), (Module.finBasis ℝ E) k, Z x, Y x])
        + (1 / 2 : ℝ) *
          (unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S') x
              ![(LeviCivita (I := I) g₀).toFun (fun b => Z b) x
                  (cometricLmodel (I := I) gop x
                    (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                      ((Module.finBasis ℝ E).cDualBasis k))), Y x, (Module.finBasis ℝ E) k]
            + unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S') x
                ![Z x, (LeviCivita (I := I) g₀).toFun (fun b => Y b) x
                    (cometricLmodel (I := I) gop x
                      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                        ((Module.finBasis ℝ E).cDualBasis k))), (Module.finBasis ℝ E) k]
            + unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S') x
                ![(LeviCivita (I := I) g₀).toFun (fun b => Y b) x
                    (cometricLmodel (I := I) gop x
                      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                        ((Module.finBasis ℝ E).cDualBasis k))), Z x, (Module.finBasis ℝ E) k]
            + unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S') x
                ![Y x, (LeviCivita (I := I) g₀).toFun (fun b => Z b) x
                    (cometricLmodel (I := I) gop x
                      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                        ((Module.finBasis ℝ E).cDualBasis k))), (Module.finBasis ℝ E) k]
            - unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S') x
                ![(Module.finBasis ℝ E) k, (LeviCivita (I := I) g₀).toFun (fun b => Z b) x
                    (cometricLmodel (I := I) gop x
                      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                        ((Module.finBasis ℝ E).cDualBasis k))), Y x]
            - unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S') x
                ![(Module.finBasis ℝ E) k, Z x,
                  (LeviCivita (I := I) g₀).toFun (fun b => Y b) x
                    (cometricLmodel (I := I) gop x
                      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                        ((Module.finBasis ℝ E).cDualBasis k)))])) from by
      refine Finset.sum_congr rfl fun k _ => ?_
      exact alignedPrincipalEndoCcross_inner_secondKoszul (I := I) (M := M) g₀ gop gcov S' hbil Z Y x
        (cometricLmodel (I := I) gop x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k))) ((Module.finBasis ℝ E) k)]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  congr 1

def alignmentTraceRemainderCross (g₀ gop gcov : SmoothRiemannianMetric I M)
    (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E),
    (chartModelBasis E).repr
      (alignCorrVecCrossMetric (I := I) (M := M) g₀ gop gcov Z Y x ((chartModelBasis E) i)) i

def palatiniTracedPrincipalRemainderCrossMetric (g₀ gop gcov : SmoothRiemannianMetric I M)
    (S' : SmoothCcTensor g₀ 0 2) (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) : ℝ :=
  secondKoszulFrameRemainder (I := I) (M := M) g₀ gop S' Z Y x
    + alignmentTraceRemainderCross (I := I) (M := M) g₀ gop gcov Z Y x


omit [NeZero (Module.finrank ℝ E)] in
theorem palatini_tracedPrincipal_cross_eq_combinedTrace
    (g₀ gop gcov : SmoothRiemannianMetric I M) (S' : SmoothCcTensor g₀ 0 2)
    (hbil : ∀ (b : M) (u w : TangentSpace I b),
      smoothCcTensorBilinForm (I := I) g₀ S' b u w = gcov.inner b u w - g₀.inner b u w)
    (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    (∑ i : Fin (Module.finrank ℝ E),
      (chartModelBasis E).repr
        (inverseMetricSharpFib (I := I) gop x
          (dualToCotangent (I := I)
            (((cotangentCov (LeviCivita (I := I) gop)).toFun
              (fun b => cotangentToCLM (I := I)
                (koszulCovGradCovec (I := I) (M := M) g₀ gcov Z Y b)) x
                  ((chartModelBasis E) i) :
              TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))) i) =
      unitModel (I := I) (M := M) g₀ 2
          (operatorFieldApply (I := I) (M := M) g₀ 4 2 (ricciArmPrincipalCoeff (I := I) (M := M) g₀ gop)
            (iteratedCovGrad (I := I) g₀ 0 2 2 S')) x ![Z x, Y x]
        + palatiniTracedPrincipalRemainderCrossMetric (I := I) (M := M) g₀ gop gcov S' Z Y x := by
  classical
  have hsumeq : (∑ i : Fin (Module.finrank ℝ E),
      (chartModelBasis E).repr
        (inverseMetricSharpFib (I := I) gop x
          (dualToCotangent (I := I)
            (((cotangentCov (LeviCivita (I := I) gop)).toFun
              (fun b => cotangentToCLM (I := I)
                (koszulCovGradCovec (I := I) (M := M) g₀ gcov Z Y b)) x
                  ((chartModelBasis E) i) :
              TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))) i) =
      ∑ i : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr
            (alignedPrincipalEndoCrossMetric (I := I) (M := M) g₀ gop gcov Z Y x
              ((chartModelBasis E) i)) i
          + (chartModelBasis E).repr
              (alignCorrVecCrossMetric (I := I) (M := M) g₀ gop gcov Z Y x
                ((chartModelBasis E) i)) i) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    have hsplit := g1Principal_splitCcross (I := I) (M := M) g₀ gop gcov Z Y x ((chartModelBasis E) i)
    rw [g1PrincipalVecCcross] at hsplit
    rw [hsplit]
    rw [map_add, Finsupp.add_apply]
    rw [← alignedPrincipalEndoCcross_apply]
  rw [hsumeq, Finset.sum_add_distrib]
  rw [trace_eq_basis_repr_sum (alignedPrincipalEndoCrossMetric (I := I) (M := M) g₀ gop gcov Z Y x)]
  rw [alignedPrincipalEndoCcross_trace_eq (I := I) (M := M) g₀ gop gcov S' hbil Z Y x]
  rw [palatiniTracedPrincipalRemainderCrossMetric, alignmentTraceRemainderCross]
  ring

def palatiniTracedPrincipalDiffRemainder (g₀ g₁ g₁' : SmoothRiemannianMetric I M)
    (S S' : SmoothCcTensor g₀ 0 2) (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) : ℝ :=
  palatiniTracedPrincipalRemainder (I := I) (M := M) g₀ g₁ S Z Y x
    - palatiniTracedPrincipalRemainderCrossMetric (I := I) (M := M) g₀ g₁ g₁' S' Z Y x


omit [NeZero (Module.finrank ℝ E)] in
theorem palatini_tracedPrincipalDiff_covector_eq_combinedTrace
    (g₀ g₁ g₁' : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    (hg₁ : ∀ (b : M) (u w : TangentSpace I b),
      g₁.inner b u w = g₀.inner b u w + ccTensorBilinSymm (I := I) g₀ T b u w)
    (hg₁' : ∀ (b : M) (u w : TangentSpace I b),
      g₁'.inner b u w = g₀.inner b u w + ccTensorBilinSymm (I := I) g₀ T' b u w)
    (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    (∑ i : Fin (Module.finrank ℝ E),
        (chartModelBasis E).repr
          (inverseMetricSharpFib (I := I) g₁ x
            (dualToCotangent (I := I)
              (((cotangentCov (LeviCivita (I := I) g₁)).toFun
                (fun b => cotangentToCLM (I := I)
                  (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) x
                    ((chartModelBasis E) i) :
                TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))) i)
      - (∑ i : Fin (Module.finrank ℝ E),
        (chartModelBasis E).repr
          (inverseMetricSharpFib (I := I) g₁ x
            (dualToCotangent (I := I)
              (((cotangentCov (LeviCivita (I := I) g₁)).toFun
                (fun b => cotangentToCLM (I := I)
                  (koszulCovGradCovec (I := I) (M := M) g₀ g₁' Z Y b)) x
                    ((chartModelBasis E) i) :
                TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))) i) =
      unitModel (I := I) (M := M) g₀ 2
          (operatorFieldApply (I := I) (M := M) g₀ 4 2 (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁)
            (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ (T - T')))) x ![Z x, Y x]
        + palatiniTracedPrincipalDiffRemainder (I := I) (M := M) g₀ g₁ g₁'
            (ccTensor02Symm (I := I) (M := M) g₀ T) (ccTensor02Symm (I := I) (M := M) g₀ T') Z Y x := by
  classical
  have hbil : ∀ (b : M) (u w : TangentSpace I b),
      smoothCcTensorBilinForm (I := I) g₀ (ccTensor02Symm (I := I) (M := M) g₀ T) b u w =
        g₁.inner b u w - g₀.inner b u w :=
    symmS_hbil_of_realize (I := I) (M := M) g₀ g₁ T hg₁
  have hbil' : ∀ (b : M) (u w : TangentSpace I b),
      smoothCcTensorBilinForm (I := I) g₀ (ccTensor02Symm (I := I) (M := M) g₀ T') b u w =
        g₁'.inner b u w - g₀.inner b u w :=
    symmS_hbil_of_realize (I := I) (M := M) g₀ g₁' T' hg₁'
  rw [palatini_tracedPrincipal_eq_combinedTrace (I := I) (M := M) g₀ g₁
        (ccTensor02Symm (I := I) (M := M) g₀ T) hbil Z Y x]
  rw [palatini_tracedPrincipal_cross_eq_combinedTrace (I := I) (M := M) g₀ g₁ g₁'
        (ccTensor02Symm (I := I) (M := M) g₀ T') hbil' Z Y x]
  rw [palatiniTracedPrincipalDiffRemainder]
  rw [symmS_sub (I := I) (M := M) g₀ T T']
  rw [iteratedCovGrad_sub (I := I) g₀ 0 2 2
        (ccTensor02Symm (I := I) (M := M) g₀ T) (ccTensor02Symm (I := I) (M := M) g₀ T')]

  have happCc_sub : operatorFieldApply (I := I) (M := M) g₀ 4 2 (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁)
        (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ T)
          - iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ T')) =
      operatorFieldApply (I := I) (M := M) g₀ 4 2 (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁)
          (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ T))
        - operatorFieldApply (I := I) (M := M) g₀ 4 2 (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁)
            (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ T')) := by
    rw [show (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ T)
          - iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ T')) =
        iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ T)
          + (-1 : ℝ) • iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ T') from by
      rw [neg_one_smul]; abel]
    rw [appCc_add_right, appCc_smul_right, neg_one_smul]
    abel
  rw [happCc_sub]
  have hsub : ∀ (a b : SmoothCcTensor g₀ 0 2),
      unitModel (I := I) (M := M) g₀ 2 (a - b) x ![Z x, Y x] =
        unitModel (I := I) (M := M) g₀ 2 a x ![Z x, Y x]
          - unitModel (I := I) (M := M) g₀ 2 b x ![Z x, Y x] := by
    intro a b
    rw [show a - b = a + (-1 : ℝ) • b from by rw [neg_one_smul]; abel,
        unitModel_add2, unitModel_smul]
    rw [ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.smul_apply]
    simp only [smul_eq_mul]
    ring
  rw [hsub]
  ring

def palatiniTracedPrincipalZRemainderCross (g₀ gop gcov : SmoothRiemannianMetric I M)
    (S' : SmoothCcTensor g₀ 0 2) (V W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) : ℝ :=
  (∑ i : Fin (Module.finrank ℝ E),
    (chartModelBasis E).repr
      (alignedPrincipalEndoCrossMetric (I := I) (M := M) g₀ gop gcov
          (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
            smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩)
          W x (V x)
        - alignedPrincipalEndoZSlot (I := I) (M := M) g₀ gop S' V W x ((chartModelBasis E) i)) i)
  + (∑ i : Fin (Module.finrank ℝ E),
    (chartModelBasis E).repr
      (alignCorrVecCrossMetric (I := I) (M := M) g₀ gop gcov
          (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
            smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩)
          W x (V x)) i)


omit [NeZero (Module.finrank ℝ E)] in
theorem palatini_tracedPrincipal_Zslot_cross_eq_combinedTrace
    (g₀ gop gcov : SmoothRiemannianMetric I M) (S' : SmoothCcTensor g₀ 0 2)
    (V W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    (∑ i : Fin (Module.finrank ℝ E),
      (chartModelBasis E).repr
        (inverseMetricSharpFib (I := I) gop x
          (dualToCotangent (I := I)
            (((cotangentCov (LeviCivita (I := I) gop)).toFun
              (fun b => cotangentToCLM (I := I)
                (koszulCovGradCovec (I := I) (M := M) g₀ gcov
                  (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
                    smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩) W b)) x (V x) :
              TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))) i) =
      unitModel (I := I) (M := M) g₀ 2
          (operatorFieldApply (I := I) (M := M) g₀ 4 2 (ricciArmPrincipalCoeffZSlot (I := I) (M := M) g₀ gop)
            (iteratedCovGrad (I := I) g₀ 0 2 2 S')) x ![V x, W x]
        + palatiniTracedPrincipalZRemainderCross (I := I) (M := M) g₀ gop gcov S' V W x := by
  classical
  rw [← alignedPrincipalEndoCZ_trace_eq (I := I) (M := M) g₀ gop S' V W x]
  rw [← trace_eq_basis_repr_sum (alignedPrincipalEndoZSlot (I := I) (M := M) g₀ gop S' V W x)]
  rw [palatiniTracedPrincipalZRemainderCross]
  have hsumeq : ∀ i : Fin (Module.finrank ℝ E),
      (chartModelBasis E).repr
        (inverseMetricSharpFib (I := I) gop x
          (dualToCotangent (I := I)
            (((cotangentCov (LeviCivita (I := I) gop)).toFun
              (fun b => cotangentToCLM (I := I)
                (koszulCovGradCovec (I := I) (M := M) g₀ gcov
                  (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
                    smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩) W b)) x (V x) :
              TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))) i =
        (chartModelBasis E).repr
            (alignedPrincipalEndoZSlot (I := I) (M := M) g₀ gop S' V W x ((chartModelBasis E) i)) i
          + ((chartModelBasis E).repr
              (alignedPrincipalEndoCrossMetric (I := I) (M := M) g₀ gop gcov
                  (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
                    smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩) W x (V x)
                - alignedPrincipalEndoZSlot (I := I) (M := M) g₀ gop S' V W x ((chartModelBasis E) i)) i
            + (chartModelBasis E).repr
                (alignCorrVecCrossMetric (I := I) (M := M) g₀ gop gcov
                  (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
                    smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩) W x (V x)) i) := by
    intro i
    set ei : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
      ⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
        smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩ with hei
    have hsplit := g1Principal_splitCcross (I := I) (M := M) g₀ gop gcov ei W x (V x)
    rw [g1PrincipalVecCcross] at hsplit
    rw [hsplit]
    rw [map_add, Finsupp.add_apply, ← alignedPrincipalEndoCcross_apply]
    rw [show (chartModelBasis E).repr
          (alignedPrincipalEndoCrossMetric (I := I) (M := M) g₀ gop gcov ei W x (V x)) i =
        (chartModelBasis E).repr
            (alignedPrincipalEndoZSlot (I := I) (M := M) g₀ gop S' V W x ((chartModelBasis E) i)) i
          + (chartModelBasis E).repr
              (alignedPrincipalEndoCrossMetric (I := I) (M := M) g₀ gop gcov ei W x (V x)
                - alignedPrincipalEndoZSlot (I := I) (M := M) g₀ gop S' V W x ((chartModelBasis E) i)) i from by
      rw [map_sub, Finsupp.sub_apply]; ring]
    rw [add_assoc]
  rw [Finset.sum_congr rfl fun i _ => hsumeq i]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]

def palatiniTracedPrincipalZDiffRemainder (g₀ g₁ g₁' : SmoothRiemannianMetric I M)
    (S S' : SmoothCcTensor g₀ 0 2) (V W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) : ℝ :=
  palatiniTracedPrincipalZRemainder (I := I) (M := M) g₀ g₁ S V W x
    - palatiniTracedPrincipalZRemainderCross (I := I) (M := M) g₀ g₁ g₁' S' V W x


omit [NeZero (Module.finrank ℝ E)] in
theorem palatini_tracedPrincipalDiff_Zslot_eq_combinedTrace
    (g₀ g₁ g₁' : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    (V W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    (∑ i : Fin (Module.finrank ℝ E),
        (chartModelBasis E).repr
          (inverseMetricSharpFib (I := I) g₁ x
            (dualToCotangent (I := I)
              (((cotangentCov (LeviCivita (I := I) g₁)).toFun
                (fun b => cotangentToCLM (I := I)
                  (koszulCovGradCovec (I := I) (M := M) g₀ g₁
                    (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
                      smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩) W b)) x (V x) :
                TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))) i)
      - (∑ i : Fin (Module.finrank ℝ E),
        (chartModelBasis E).repr
          (inverseMetricSharpFib (I := I) g₁ x
            (dualToCotangent (I := I)
              (((cotangentCov (LeviCivita (I := I) g₁)).toFun
                (fun b => cotangentToCLM (I := I)
                  (koszulCovGradCovec (I := I) (M := M) g₀ g₁'
                    (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
                      smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩) W b)) x (V x) :
                TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))) i) =
      unitModel (I := I) (M := M) g₀ 2
          (operatorFieldApply (I := I) (M := M) g₀ 4 2 (ricciArmPrincipalCoeffZSlot (I := I) (M := M) g₀ g₁)
            (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ (T - T')))) x ![V x, W x]
        + palatiniTracedPrincipalZDiffRemainder (I := I) (M := M) g₀ g₁ g₁'
            (ccTensor02Symm (I := I) (M := M) g₀ T) (ccTensor02Symm (I := I) (M := M) g₀ T') V W x := by
  classical
  rw [palatini_tracedPrincipal_Zslot_eq_combinedTrace (I := I) (M := M) g₀ g₁
        (ccTensor02Symm (I := I) (M := M) g₀ T) V W x]
  rw [palatini_tracedPrincipal_Zslot_cross_eq_combinedTrace (I := I) (M := M) g₀ g₁ g₁'
        (ccTensor02Symm (I := I) (M := M) g₀ T') V W x]
  rw [palatiniTracedPrincipalZDiffRemainder]
  rw [symmS_sub (I := I) (M := M) g₀ T T']
  rw [iteratedCovGrad_sub (I := I) g₀ 0 2 2
        (ccTensor02Symm (I := I) (M := M) g₀ T) (ccTensor02Symm (I := I) (M := M) g₀ T')]
  have happCc_sub : operatorFieldApply (I := I) (M := M) g₀ 4 2 (ricciArmPrincipalCoeffZSlot (I := I) (M := M) g₀ g₁)
        (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ T)
          - iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ T')) =
      operatorFieldApply (I := I) (M := M) g₀ 4 2 (ricciArmPrincipalCoeffZSlot (I := I) (M := M) g₀ g₁)
          (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ T))
        - operatorFieldApply (I := I) (M := M) g₀ 4 2 (ricciArmPrincipalCoeffZSlot (I := I) (M := M) g₀ g₁)
            (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ T')) := by
    rw [show (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ T)
          - iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ T')) =
        iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ T)
          + (-1 : ℝ) • iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ T') from by
      rw [neg_one_smul]; abel]
    rw [appCc_add_right, appCc_smul_right, neg_one_smul]
    abel
  rw [happCc_sub]
  have hsub : ∀ (a b : SmoothCcTensor g₀ 0 2),
      unitModel (I := I) (M := M) g₀ 2 (a - b) x ![V x, W x] =
        unitModel (I := I) (M := M) g₀ 2 a x ![V x, W x]
          - unitModel (I := I) (M := M) g₀ 2 b x ![V x, W x] := by
    intro a b
    rw [show a - b = a + (-1 : ℝ) • b from by rw [neg_one_smul]; abel,
        unitModel_add2, unitModel_smul]
    rw [ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.smul_apply]
    simp only [smul_eq_mul]
    ring
  rw [hsub]
  ring

noncomputable def reindexCoeffFib (σ' : Equiv.Perm (Fin 4)) (x : M)
    (A : Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x) :
    Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x :=
  A.comp
    ((Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) 4 x).symm.toContinuousLinearMap.comp
      (((ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E ℝ
            σ').toContinuousLinearEquiv.toContinuousLinearMap).comp
        (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) 4 x).toContinuousLinearMap))


omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem reindexCoeffFib_apply (σ' : Equiv.Perm (Fin 4)) (x : M)
    (A : Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x)
    (D : Tensor0SBundle.Tensor0SSpace 4 I x) :
    reindexCoeffFib (I := I) σ' x A D =
      A (Tensor0SBundle.Tensor0SSpace.ofModel
          (ContinuousMultilinearMap.domDomCongr σ'
            (Tensor0SBundle.Tensor0SSpace.toModel D))) := by
  rw [reindexCoeffFib, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply]
  congr 1


omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem reindexCoeffFib_add (σ' : Equiv.Perm (Fin 4)) (x : M)
    (A B : Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x)
    (D : Tensor0SBundle.Tensor0SSpace 4 I x) :
    reindexCoeffFib (I := I) σ' x (A + B) D =
      reindexCoeffFib (I := I) σ' x A D + reindexCoeffFib (I := I) σ' x B D := by
  rw [reindexCoeffFib_apply, reindexCoeffFib_apply, reindexCoeffFib_apply,
    ContinuousLinearMap.add_apply]

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem reindexCoeffFib_contMDiff (g₀ : SmoothRiemannianMetric I M)
    (R : SmoothCcTensor g₀ 4 2) (σ' : Equiv.Perm (Fin 4)) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 4 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) x
        (reindexCoeffFib (I := I) σ' x
          (show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
            R.toSection x))) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 4 ℝ E) (V₁ := fun x : M => Tensor0SBundle.Tensor0SSpace 4 I x)
    (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E) (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace 2 I x)
    (φ := fun x => reindexCoeffFib (I := I) σ' x
      (show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        R.toSection x))
  intro Y

  have hYσ : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 4 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 4 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 4 I z) x
        (Tensor0SBundle.Tensor0SSpace.ofModel
          (ContinuousMultilinearMap.domDomCongr σ'
            (Tensor0SBundle.Tensor0SSpace.toModel (Y x))))) := by
    refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
      (fun x => (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
          (ContinuousMultilinearMap.domDomCongr σ'
            (Tensor0SBundle.Tensor0SSpace.toModel (Y x))) :
            Tensor0SBundle.Tensor0SSpace 4 I x))).mpr ?_
    have hYcoord := (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
      (fun x => Y x)).mp Y.contMDiff
    intro τ x₀
    refine (hYcoord (τ ∘ σ') x₀).congr_of_eventuallyEq ?_
    filter_upwards [Filter.univ_mem] with x _
    rw [continuousMultilinearMap_basis_repr, continuousMultilinearMap_basis_repr]
    change (ContinuousMultilinearMap.domDomCongr σ'
        (Tensor0SBundle.Tensor0SSpace.toModel (Y x)))
        (fun j => (Bundle.Trivialization.symmL ℝ (trivializationAt E (TangentSpace I) x₀) x)
          ((Module.finBasis ℝ E) (τ j))) = _
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    rfl
  have hRY := ContMDiff.clm_bundle_apply (b := id) R.toSection.contMDiff hYσ
  refine hRY.congr (fun x => ?_)
  exact congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) x t)
    (reindexCoeffFib_apply (I := I) σ' x
      (show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        R.toSection x) (Y x)).symm

noncomputable def reindexCoeff (g₀ : SmoothRiemannianMetric I M)
    (R : SmoothCcTensor g₀ 4 2) (σ' : Equiv.Perm (Fin 4)) :
    SmoothCcTensor g₀ 4 2 where
  toSection :=
    { toFun := fun x : M =>
        (show Tensor0SBundle.TensorRSSpace 4 2 I x from
          reindexCoeffFib (I := I) σ' x
            (show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
              R.toSection x))
      contMDiff_toFun := reindexCoeffFib_contMDiff (I := I) (M := M) g₀ R σ' }
  hasCompactSupport := HasCompactSupport.of_compactSpace _


omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
@[simp] theorem reindexCoeff_toSection (g₀ : SmoothRiemannianMetric I M)
    (R : SmoothCcTensor g₀ 4 2) (σ' : Equiv.Perm (Fin 4)) (x : M) :
    (reindexCoeff (I := I) (M := M) g₀ R σ').toSection x =
      (show Tensor0SBundle.TensorRSSpace 4 2 I x from
        reindexCoeffFib (I := I) σ' x
          (show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
            R.toSection x)) := rfl

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem reindexCoeff_appCc_eq (g₀ : SmoothRiemannianMetric I M)
    (R : SmoothCcTensor g₀ 4 2) (σ' : Equiv.Perm (Fin 4))
    (W W' : SmoothCcTensor g₀ 0 4)
    (hWW' : ∀ x : M, unitModel (I := I) (M := M) g₀ 4 W' x =
      ContinuousMultilinearMap.domDomCongr σ' (unitModel (I := I) (M := M) g₀ 4 W x))
    (x : M) :
    unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 4 2 (reindexCoeff (I := I) (M := M) g₀ R σ') W) x =
      unitModel (I := I) (M := M) g₀ 2 (operatorFieldApply (I := I) (M := M) g₀ 4 2 R W') x := by
  rw [unitModel, unitModel, appCc_toSection, appCc_toSection,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  rw [reindexCoeff_toSection]

  rw [reindexCoeffFib_apply (I := I) σ' x
    (show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
      R.toSection x)
    ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 4 I x from
      W.toSection x) (unitTensor (I := I) (M := M) x))]

  have hWu : Tensor0SBundle.Tensor0SSpace.toModel
      ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 4 I x from
        W.toSection x) (unitTensor (I := I) (M := M) x)) =
      unitModel (I := I) (M := M) g₀ 4 W x := rfl
  have hW'u : (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 4 I x from
        W'.toSection x) (unitTensor (I := I) (M := M) x) =
      Tensor0SBundle.Tensor0SSpace.ofModel (unitModel (I := I) (M := M) g₀ 4 W' x) := by
    rw [show unitModel (I := I) (M := M) g₀ 4 W' x =
        Tensor0SBundle.Tensor0SSpace.toModel
          ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 4 I x from
            W'.toSection x) (unitTensor (I := I) (M := M) x)) from rfl,
      Tensor0SBundle.Tensor0SSpace.ofModel_toModel]
  rw [hWu, ← hWW' x, hW'u]

end InnerProductSpaceModel

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
