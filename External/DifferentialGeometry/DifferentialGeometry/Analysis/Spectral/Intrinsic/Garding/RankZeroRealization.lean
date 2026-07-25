import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.FaithfulH1Embedding
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.FractionalPower
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.IteratedCovGradHsJetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Regularity.EigenvectorTensorHsToWtwokTwo
import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.OperatorEquation
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.IntegratedOrder2Garding
import DifferentialGeometry.Geometry.Connection.Laplacian.RankZero
import DifferentialGeometry.Geometry.Operator.LaplacianBridge
import DifferentialGeometry.Geometry.Connection.ChartTensorNabla.Agreement.Tensor0SRSCovariantDerivativeAgreement
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.GradientField
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingCm
import DifferentialGeometry.Tensor.RSTensor.RankZero









noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E



noncomputable def scalarScaleLap (g : SmoothRiemannianMetric I M) :
    tensorHs (I := I) (M := M) g 0 0 2 →L[ℝ]
      tensorHs (I := I) (M := M) g 0 0 0 :=
  (tensorScaleLaplacian (I := I) (M := M)
    (g := g) (r := 0) (s := 0) 0).comp
      (tensorHs.castEquiv (I := I) (M := M)
        (g := g) (r := 0) (s := 0)
        (by norm_num : (2 : ℝ) = 0 + 2)).toContinuousLinearEquiv.toContinuousLinearMap

omit [BoundarylessManifold I M] in

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem scalarScaleLap_coeff
    (g : SmoothRiemannianMetric I M)
    (v : tensorHs (I := I) (M := M) g 0 0 2)
    (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
      (I := I) (M := M) g 0 0) :
    (scalarScaleLap (I := I) (M := M) g v).coeff i =
      -TensorEigenIdx.lambda (I := I) (M := M) i * v.coeff i := by
  simp only [scalarScaleLap, ContinuousLinearMap.comp_apply,
    tensorScaleLaplacian_coeff]
  change -TensorEigenIdx.lambda (I := I) (M := M) i *
      (tensorHs.castEquiv (I := I) (M := M)
        (g := g) (r := 0) (s := 0) _ v).coeff i =
    -TensorEigenIdx.lambda (I := I) (M := M) i * v.coeff i
  rw [tensorHs.castEquiv_coeff]




theorem scalarLapHs_core
    (g : SmoothRiemannianMetric I M)
    (m : ℝ) (S : SmoothCcTensor g 0 0) :
    tensorScaleLaplacian (I := I) (M := M)
        (g := g) (r := 0) (s := 0) m
        (ccTensorToHs (I := I) (M := M) g 0 (m + 2) S) =
      ccTensorToHs (I := I) (M := M) g 0 m
        (rawTensorConnLapSmooth (I := I) g 0 0 S) := by
  refine tensorHs.ext ?_
  funext i
  rw [tensorScaleLaplacian_coeff, ccTensorToHs_coeff,
    ccTensorToHs_coeff,
    rawLap_coeff (I := I) (M := M) g 0
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0) S i]



omit [CompactSpace M] in
theorem rawLap_cc_scalar
    (g : SmoothRiemannianMetric I M) (S : SmoothCcTensor g 0 0) (x : M) :
    TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞))
        (rawTensorConnLapSmooth (I := I) g 0 0 S).toSection x =
      DifferentialGeometry.Integral.DivergenceTheorem.Δ_g (I := I) g
        (TensorRSField.scalar0_smooth
          (n := (∞ : WithTop ℕ∞)) S.toSection) x := by
  let f := TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) S.toSection
  let hf := TensorRSField.scalar0_smooth
    (n := (∞ : WithTop ℕ∞)) S.toSection
  have hraw := rawLap_scalar (I := I) (M := M) g hf x
  have hlift :
      (Tensor0SField.fromScalarField (∞ : WithTop ℕ∞) f hf).toTensorRSField
          (∞ : WithTop ℕ∞) = S.toSection := by
    simpa only [f, hf] using
      (TensorRSField.lift_scalar0
        (n := (∞ : WithTop ℕ∞)) S.toSection)
  rw [hlift] at hraw
  change tensor0SSpace_evalScalar x
      ((rawTensorConnLapSmooth (I := I) g 0 0 S).toSection x
        (Tensor0SField.one0 (𝕜 := ℝ) (E := E) (H := H)
          (I := I) (M := M) (∞ : WithTop ℕ∞) x)) = _
  rw [rawTensorConnLapSmooth_toSection_apply (I := I) (M := M) g 0 0 S x,
    hraw, Tensor0SSpace.toRS0_apply]
  have hone : tensor0SSpace_evalScalar x
      (Tensor0SField.one0 (𝕜 := ℝ) (E := E) (H := H)
        (I := I) (M := M) (∞ : WithTop ℕ∞) x) = 1 := by
    rw [Tensor0SSpace.evalScalar_apply]
    exact Tensor0SField.one0_apply (𝕜 := ℝ) (E := E) (H := H)
      (I := I) (M := M) (∞ : WithTop ℕ∞) x Fin.elim0
  rw [hone, one_smul]
  change Tensor0SNabla.tensor0Iso I M x
      ((Tensor0SNabla.tensor0Iso I M x).symm
        (laplacian (I := I) (LeviCivita (I := I) g) g f x)) = _
  rw [ContinuousLinearEquiv.apply_symm_apply,
    DifferentialGeometry.Integral.Connection.laplacian_levi_eq
      (I := I) g hf x]

omit [BoundarylessManifold I M] in

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem norm_scalarLap_le
    (g : SmoothRiemannianMetric I M)
    (v : tensorHs (I := I) (M := M) g 0 0 2) :
    ‖scalarScaleLap (I := I) (M := M) g v‖ ≤ ‖v‖ := by
  change ‖scaleLaplacianFun (I := I) (M := M)
      (tensorHs.castEquiv (I := I) (M := M)
        (g := g) (r := 0) (s := 0) _ v)‖ ≤ ‖v‖
  calc
    _ ≤ ‖tensorHs.castEquiv (I := I) (M := M)
        (g := g) (r := 0) (s := 0) _ v‖ :=
      norm_scaleLaplacianFun_le (I := I) (M := M) _
    _ = ‖v‖ := (tensorHs.castEquiv (I := I) (M := M)
      (g := g) (r := 0) (s := 0) _).norm_map v



noncomputable def reprScalar0
    {g : SmoothRiemannianMetric I M}
    (v : tensorHs (I := I) (M := M) g 0 0 2)
    (hv : (Function.support v.coeff).Finite) : M → ℝ :=
  TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞))
    (tensorHsSmoothRepr (I := I) (M := M) v hv).toSection

omit [BoundarylessManifold I M] in


theorem reprScalar0_smooth
    {g : SmoothRiemannianMetric I M}
    (v : tensorHs (I := I) (M := M) g 0 0 2)
    (hv : (Function.support v.coeff).Finite) :
    ContMDiff I 𝓘(ℝ) ∞ (reprScalar0 (I := I) (M := M) v hv) :=
  TensorRSField.scalar0_smooth (n := (∞ : WithTop ℕ∞))
    (tensorHsSmoothRepr (I := I) (M := M) v hv).toSection

omit [BoundarylessManifold I M] in


theorem repr_eq_lift
    {g : SmoothRiemannianMetric I M}
    (v : tensorHs (I := I) (M := M) g 0 0 2)
    (hv : (Function.support v.coeff).Finite) :
    (Tensor0SField.fromScalarField ∞
      (reprScalar0 (I := I) (M := M) v hv)
      (reprScalar0_smooth (I := I) (M := M) v hv)).toTensorRSField ∞ =
        (tensorHsSmoothRepr (I := I) (M := M) v hv).toSection := by
  simpa [reprScalar0] using
    (TensorRSField.lift_scalar0 (n := (∞ : WithTop ℕ∞))
      (tensorHsSmoothRepr (I := I) (M := M) v hv).toSection)



theorem grad_repr_apply
    (g : SmoothRiemannianMetric I M)
    (v : tensorHs (I := I) (M := M) g 0 0 2)
    (hv : (Function.support v.coeff).Finite) (x : M)
    (X : TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 1 I x from
          (iteratedCovGrad (I := I) (M := M) g 0 0 1
            (tensorHsSmoothRepr (I := I) (M := M) v hv)).toSection x)
          (unitZeroSec (I := I) (M := M) x))
        (fun _ : Fin 1 => X) =
      duSec (I := I) (reprScalar0 (I := I) (M := M) v hv)
        (reprScalar0_smooth (I := I) (M := M) v hv) x
        (fun _ : Fin 1 => X) := by
  let A : Tensor0SField ∞ 0 (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) :=
    Tensor0SField.fromScalarField ∞
      (reprScalar0 (I := I) (M := M) v hv)
      (reprScalar0_smooth (I := I) (M := M) v hv)
  have hunit (y : M) :
      tensor0SSpace_evalScalar y (unitZeroSec (I := I) (M := M) y) = 1 := by
    rw [Tensor0SSpace.evalScalar_apply, unitZeroSec_apply]
    change ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) 1
      Fin.elim0 = 1
    rw [ContinuousMultilinearMap.constOfIsEmpty_apply]
  have hsection :
      (fun y : M =>
        (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 0 I y from
          (tensorHsSmoothRepr (I := I) (M := M) v hv).toSection y)
          (unitZeroSec (I := I) (M := M) y)) =
        fun y : M => A y := by
    funext y
    rw [← repr_eq_lift (I := I) (M := M) v hv,
      Tensor0SField.toRS0_apply, hunit, one_smul]
  have hscalar :
      Tensor0SNabla.scalarFn I M (fun y : M => A y) =
        reprScalar0 (I := I) (M := M) v hv := by
    funext y
    rw [Tensor0SNabla.scalarFn_eq_apply_zero]
    change Tensor0SField.toScalarField ∞ A y =
      reprScalar0 (I := I) (M := M) v hv y
    exact congrFun (Tensor0SField.toScalarField_fromScalarField ∞
      (reprScalar0 (I := I) (M := M) v hv)
      (reprScalar0_smooth (I := I) (M := M) v hv)) y
  rw [iteratedCovGrad_succ, iteratedCovGrad_zero]
  rw [covGrad_toSection_apply_eval (I := I) (M := M) g 0 0
    (tensorHsSmoothRepr (I := I) (M := M) v hv) x
    (unitZeroSec (I := I) (M := M) x) (fun _ : Fin 1 => X)]
  rw [tensorCovDerivAt_def,
    tensorRSCovariantDerivative_zeroS_unit_eval, hsection,
    Tensor0SNabla.tensor0SCovariantDerivative_apply_zero, hscalar,
    duSec_apply, differential1FormFun_apply_eq_extDerivFun]
  change Tensor0SNabla.tensor0Iso I M x
      ((Tensor0SNabla.tensor0Iso I M x).symm
        (extDerivFun (I := I)
          (reprScalar0 (I := I) (M := M) v hv) x X)) = _
  rw [ContinuousLinearEquiv.apply_symm_apply]



theorem grad2_repr_diag
    (g : SmoothRiemannianMetric I M)
    (v : tensorHs (I := I) (M := M) g 0 0 2)
    (hv : (Function.support v.coeff).Finite)
    (B : ContMDiffSection I E ∞ (TangentSpace I : M → Type _)) (x : M) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          (iteratedCovGrad (I := I) (M := M) g 0 0 2
            (tensorHsSmoothRepr (I := I) (M := M) v hv)).toSection x)
          (unitZeroSec (I := I) (M := M) x))
        (vec2 (I := I) (B x) (B x)) =
      hessianSec (I := I) (LeviCivita (I := I) g)
        (by
          simpa [LeviCivita] using
            (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
              (I := I) (M := M) g))
        (reprScalar0 (I := I) (M := M) v hv)
        (reprScalar0_smooth (I := I) (M := M) v hv) x
        (vec2 (I := I) (B x) (B x)) := by
  let hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (LeviCivita (I := I) g) ∞ := by
    simpa [LeviCivita] using
      (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
        (I := I) (M := M) g)
  let m0 : Fin 0 → TangentSpace I x := fun i => Fin.elim0 i
  have hslots :
      Fin.cons (B x) (Fin.cons (B x) m0) =
        vec2 (I := I) (B x) (B x) := by
    funext i
    fin_cases i <;> rfl
  have hiter :
      iteratedCovGrad (I := I) (M := M) g 0 0 2
          (tensorHsSmoothRepr (I := I) (M := M) v hv) =
        covGrad (I := I) (M := M) g 0 1
          (covGrad (I := I) (M := M) g 0 0
            (tensorHsSmoothRepr (I := I) (M := M) v hv)) := by
    rw [iteratedCovGrad_succ, iteratedCovGrad_succ, iteratedCovGrad_zero]
  have hbridge :=
    tensorSecondCovDeriv_eq_covGrad_succ_twoSlotEval_genVal
      (I := I) (M := M) g 0
      (tensorHsSmoothRepr (I := I) (M := M) v hv)
      (X := fun y => B y) (Y := fun y => B y)
      B.contMDiff B.contMDiff x m0
  rw [hiter, ← hslots]
  rw [hbridge]
  have hrepr : (fun y : M =>
        (tensorHsSmoothRepr (I := I) (M := M) v hv).toSection y) =
      fun y : M =>
        (Tensor0SField.fromScalarField ∞
          (reprScalar0 (I := I) (M := M) v hv)
          (reprScalar0_smooth (I := I) (M := M) v hv)).toTensorRSField ∞ y := by
    funext y
    exact congrArg (fun T => T y)
      (repr_eq_lift (I := I) (M := M) v hv).symm
  rw [hrepr]
  rw [tensorSecondCovDeriv_def,
    secondRS_scalar (I := I) (M := M) g hcov
      (reprScalar0_smooth (I := I) (M := M) v hv) B x]
  rw [hslots]
  rw [Tensor0SSpace.toRS0_apply]
  have hunit :
      tensor0SSpace_evalScalar x (unitZeroSec (I := I) (M := M) x) = 1 := by
    rw [Tensor0SSpace.evalScalar_apply, unitZeroSec_apply]
    change ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) 1
      Fin.elim0 = 1
    rw [ContinuousMultilinearMap.constOfIsEmpty_apply]
  rw [hunit, one_smul]
  change Tensor0SNabla.tensor0Iso I M x
      ((Tensor0SNabla.tensor0Iso I M x).symm
        (hessianSec (I := I) (LeviCivita (I := I) g) hcov
          (reprScalar0 (I := I) (M := M) v hv)
          (reprScalar0_smooth (I := I) (M := M) v hv) x
          (vec2 (I := I) (B x) (B x)))) = _
  rw [ContinuousLinearEquiv.apply_symm_apply]



theorem rawLap_repr_scalar
    (g : SmoothRiemannianMetric I M)
    (v : tensorHs (I := I) (M := M) g 0 0 2)
    (hv : (Function.support v.coeff).Finite) (x : M) :
    rawTensorConnLap (I := I) g 0 0
        (tensorHsSmoothRepr (I := I) (M := M) v hv).toSection x =
      Tensor0SSpace.toRS0
        ((Tensor0SNabla.tensor0Iso I M x).symm
          (laplacian (I := I) (LeviCivita (I := I) g) g
            (reprScalar0 (I := I) (M := M) v hv) x)) := by
  rw [← repr_eq_lift (I := I) (M := M) v hv]
  exact rawLap_scalar (I := I) (M := M) g
    (reprScalar0_smooth (I := I) (M := M) v hv) x



theorem rawLap_repr_toL2
    (g : SmoothRiemannianMetric I M)
    (v : tensorHs (I := I) (M := M) g 0 0 2)
    (hv : (Function.support v.coeff).Finite) :
    SmoothCcTensor.toL2
        (rawTensorConnLapSmooth (I := I) g 0 0
          (tensorHsSmoothRepr (I := I) (M := M) v hv)) =
      tensorHsToL2 (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0)
        (show (0 : ℝ) ≤ 0 by norm_num)
        (scalarScaleLap (I := I) (M := M) g v) := by
  let hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0
  apply (tensorResolventHilbertEigenbasisSigma (I := I) (M := M) hc).repr.injective
  ext i
  change tensorL2Coeff (I := I) (M := M) hc
      (SmoothCcTensor.toL2
        (rawTensorConnLapSmooth (I := I) g 0 0
          (tensorHsSmoothRepr (I := I) (M := M) v hv))) i =
    tensorL2Coeff (I := I) (M := M) hc
      (tensorHsToL2 (I := I) (M := M) hc
        (show (0 : ℝ) ≤ 0 by norm_num)
        (scalarScaleLap (I := I) (M := M) g v)) i
  rw [rawLap_coeff (I := I) (M := M) g 0 hc
      (tensorHsSmoothRepr (I := I) (M := M) v hv) i]
  have hrepr := tensorHsSmoothRepr_toL2 (I := I) (M := M)
    (show (0 : ℝ) ≤ 2 by norm_num) v hv
  rw [SmoothCcTensor.toL2_apply, hrepr, tensorHsToL2_tensorL2Coeff,
    tensorHsToL2_tensorL2Coeff, scalarScaleLap_coeff]



theorem rawLap_repr_norm
    (g : SmoothRiemannianMetric I M)
    (v : tensorHs (I := I) (M := M) g 0 0 2)
    (hv : (Function.support v.coeff).Finite) :
    ‖SmoothCcTensor.toL2
        (rawTensorConnLapSmooth (I := I) g 0 0
          (tensorHsSmoothRepr (I := I) (M := M) v hv))‖ ≤ ‖v‖ := by
  rw [rawLap_repr_toL2 (I := I) (M := M) g v hv,
    tensorHsToL2_apply]
  exact (tensorHs.norm_toL2Fun_ofCompact_le (I := I) (M := M)
    (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0)
    (show (0 : ℝ) ≤ 0 by norm_num)
    (scalarScaleLap (I := I) (M := M) g v)).trans
      (norm_scalarLap_le (I := I) (M := M) g v)




theorem grad_repr_norm
    (g : SmoothRiemannianMetric I M)
    (v : tensorHs (I := I) (M := M) g 0 0 2)
    (hv : (Function.support v.coeff).Finite) :
    ‖SmoothCcTensor.toL2
        (covGrad (I := I) (M := M) g 0 0
          (tensorHsSmoothRepr (I := I) (M := M) v hv))‖ ≤ ‖v‖ := by
  let S : SmoothCcTensor g 0 0 :=
    tensorHsSmoothRepr (I := I) (M := M) v hv
  rw [SmoothCcTensor.norm_toL2]
  have hgreen :
      ‖covGrad (I := I) (M := M) g 0 0 S‖ ^ 2 ≤
        ‖rawTensorConnLapSmooth (I := I) g 0 0 S‖ * ‖S‖ := by
    rw [SmoothCcTensor.norm_def (I := I) (M := M)
        (covGrad (I := I) (M := M) g 0 0 S),
      SmoothCcTensor.norm_def (I := I) (M := M)
        (rawTensorConnLapSmooth (I := I) g 0 0 S),
      SmoothCcTensor.norm_def (I := I) (M := M) S]
    exact covGrad_l2NormSq_le_rawConnLap_mul_self_gen
      (I := I) (M := M) g 0 S
  have hLap : ‖rawTensorConnLapSmooth (I := I) g 0 0 S‖ ≤ ‖v‖ := by
    rw [← SmoothCcTensor.norm_toL2]
    simpa [S] using rawLap_repr_norm (I := I) (M := M) g v hv
  have hS : ‖S‖ ≤ ‖v‖ := by
    rw [← SmoothCcTensor.norm_toL2]
    change ‖SmoothCcTensor.toL2
      (tensorHsSmoothRepr (I := I) (M := M) v hv)‖ ≤ ‖v‖
    rw [SmoothCcTensor.toL2_apply,
      tensorHsSmoothRepr_toL2 (I := I) (M := M)
        (show (0 : ℝ) ≤ 2 by norm_num) v hv,
      tensorHsToL2_apply]
    exact tensorHs.norm_toL2Fun_ofCompact_le (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0)
      (show (0 : ℝ) ≤ 2 by norm_num) v
  have hprod :
      ‖rawTensorConnLapSmooth (I := I) g 0 0 S‖ * ‖S‖ ≤ ‖v‖ ^ 2 := by
    calc
      _ ≤ ‖v‖ * ‖v‖ :=
        mul_le_mul hLap hS (norm_nonneg S) (norm_nonneg v)
      _ = ‖v‖ ^ 2 := by ring
  nlinarith [le_trans hgreen hprod,
    norm_nonneg (covGrad (I := I) (M := M) g 0 0 S), norm_nonneg v]

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
