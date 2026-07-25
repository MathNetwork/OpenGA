import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.Retag
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.CovDivergenceRoughLaplacianCommutation
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CometricDoubleTraceField
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CometricTraceRetag
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.SharpFlatEndoField
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.SlotExtendIterInsert
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradLinear
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CometricDifferenceSlotPairing
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricArmCoeffJetTower
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.SlotTransportPairing
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.ConnDiffCovGradBridge
import DifferentialGeometry.Geometry.Connection.TensorNabla.SlotInsertCovariantNaturality









noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Tensor0SBundle
open scoped Manifold Topology ContDiff RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E



noncomputable def traceCast
    (q h : SmoothRiemannianMetric I M) : SmoothCcTensor q 2 0 :=
  SmoothCcTensor.retagEquiv h q 2 0
    (cometricDoubleTraceField (I := I) h 0)



omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem trace_retag_eq
    (q h : SmoothRiemannianMetric I M) :
    traceCast (I := I) q h =
      ccOperatorFieldComp (I := I) (M := M) q 2 2 0
        (cometricDoubleTraceField (I := I) q 0)
        (slotExtend (I := I) (M := M) q 1 1
          (sharpFlatEndoCc (I := I) q h)) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  rw [traceCast, SmoothCcTensor.retag_toSection,
    appCcRS_toSection, cometricDoubleTraceField_toSection,
    slotExtend_toSection, sharpFlatEndoCc_toSection,
    ContinuousLinearMap.comp_apply]
  exact trace_slot_flat (I := I) q h x D


omit [NeZero (Module.finrank ℝ E)] in
omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem traceCast_self (q : SmoothRiemannianMetric I M) :
    traceCast (I := I) q q = cometricDoubleTraceField (I := I) q 0 := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [traceCast, SmoothCcTensor.retag_toSection]



noncomputable def scalarFluxCoeff
    (q h : SmoothRiemannianMetric I M) : SmoothCcTensor q 1 1 :=
  sharpFlatEndoCc (I := I) q h - sharpFlatEndoCc (I := I) q q


omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem scalarFlux_eval (q h : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) (w : TangentSpace I x) :
    cotangentToDual (I := I)
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
          (scalarFluxCoeff (I := I) q h).toSection x) om) w =
      cotangentToDual (I := I) om
        (metricComparisonDiffEndo (I := I) q h x w) := by
  rw [scalarFluxCoeff, SmoothCcTensor.toSection_sub,
    ContMDiffSection.coe_sub, Pi.sub_apply, ContinuousLinearMap.sub_apply]
  rw [show cotangentToDual (I := I)
        ((show Tensor0SSpace 1 I x from
          (sharpFlatEndoCc (I := I) q h).toSection x om) -
          (show Tensor0SSpace 1 I x from
            (sharpFlatEndoCc (I := I) q q).toSection x om)) w =
      cotangentToDual (I := I)
          ((show Tensor0SSpace 1 I x from
            (sharpFlatEndoCc (I := I) q h).toSection x om)) w -
        cotangentToDual (I := I)
          ((show Tensor0SSpace 1 I x from
            (sharpFlatEndoCc (I := I) q q).toSection x om)) w from by
    rw [← cotangentToDualLinear_apply, map_sub, LinearMap.sub_apply,
      cotangentToDualLinear_apply, cotangentToDualLinear_apply]]
  rw [sharpFlatEndo_eval (I := I) (M := M),
    sharpFlatEndo_eval (I := I) (M := M)]
  rw [gInvRaisedEndo_eq_diff_add_id (I := I) q h x w]
  have hself : metricComparisonEndo (I := I) q q x w = w := by
    rw [gInvRaisedEndo_apply, inverseMetricSharpFib_g0FlatCLM]
  rw [hself, map_add]
  ring



omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem cc_flux_slot (q h : SmoothRiemannianMetric I M)
    (A : SmoothCcTensor q 0 1) :
    operatorFieldApply (I := I) (M := M) q 1 1 (scalarFluxCoeff (I := I) q h) A =
      operatorFieldApply (I := I) (M := M) q 1 1
        (endoSlotZeroCcTensor (I := I) (M := M) q 0
          (gInvDiffRaisedEndoField (I := I) q h)) A := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply tensorRSSpace_ext 0 1 x
  intro z
  apply cotangentToDualLinear_injective (I := I) (x := x)
  apply LinearMap.ext
  intro w
  rw [cotangentToDualLinear_apply, cotangentToDualLinear_apply]
  rw [appCc_toSection, appCc_toSection, slotInsertEndoCc_toSection]
  change cotangentToDual (I := I)
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (scalarFluxCoeff (I := I) q h).toSection x)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 1 I x from
          A.toSection x) z)) w =
    cotangentToDual (I := I)
      (slotInsertEndoFib (I := I) (M := M) 1 0 x
        (metricComparisonDiffEndo (I := I) q h x)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 1 I x from
          A.toSection x) z)) w
  rw [scalarFlux_eval (I := I) (M := M),
    cotangent_slot_apply (I := I) (M := M)]



omit [BoundarylessManifold I M] in
theorem cc_top_pair
    (q h : SmoothRiemannianMetric I M)
    (k : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      h.inner y v w = q.inner y v w + k y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ)
    (hδ : metricCauchySchwarzBound (I := I) q k δ)
    (n : ℕ) (U : SmoothCcTensor q 0 0) :
    -tensorL2Inner (I := I) (M := M) q 0 (0 + n + 1)
        (iteratedCovGrad (I := I) q 0 0 (n + 1) U).toFun
        (operatorFieldApply (I := I) (M := M) q (0 + n + 1) (0 + n + 1)
          (endoSlotZeroCcTensor (I := I) (M := M) q (0 + n)
            (gInvDiffRaisedEndoField (I := I) q h))
          (iteratedCovGrad (I := I) q 0 0 (n + 1) U)).toFun ≤
      (δ / (1 - δ)) *
        ‖SmoothCcTensor.toL2
          (iteratedCovGrad (I := I) q 0 0 (n + 1) U)‖ ^ 2 := by
  let A : SmoothCcTensor q 0 (0 + n + 1) :=
    iteratedCovGrad (I := I) q 0 0 (n + 1) U
  let B : SmoothCcTensor q 0 (0 + n + 1) :=
    operatorFieldApply (I := I) (M := M) q (0 + n + 1) (0 + n + 1)
      (endoSlotZeroCcTensor (I := I) (M := M) q (0 + n)
        (gInvDiffRaisedEndoField (I := I) q h)) A
  have hBfun (x : M) :
      B.toFun x = TensorRSSpace.toModel
        (gInvDiffSlotApplied (I := I) q h (0 + n) x (A.toSection x)) := by
    rfl
  have hWS_int : MeasureTheory.Integrable
      (fun x => tensorInnerPointwise (I := I) (M := M) q 0 (0 + n + 1) x
        (TensorRSSpace.toModel (A.toSection x))
        (-TensorRSSpace.toModel
          (gInvDiffSlotApplied (I := I) q h (0 + n) x (A.toSection x))))
      (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure
        (I := I) (M := M) q) := by
    have hcross := SmoothCcTensor.integrable_inner_cross
      (I := I) (M := M) A B
    have heq :
        (fun x => tensorInnerPointwise (I := I) (M := M) q 0 (0 + n + 1) x
          (TensorRSSpace.toModel (A.toSection x))
          (-TensorRSSpace.toModel
            (gInvDiffSlotApplied (I := I) q h (0 + n) x (A.toSection x)))) =
          (fun x => -tensorInnerPointwise (I := I) (M := M) q 0 (0 + n + 1) x
            (A.toFun x) (B.toFun x)) := by
      funext x
      rw [← SmoothCcTensor.toFun_apply A x, ← hBfun x]
      rw [show -B.toFun x = (-1 : ℝ) • B.toFun x from
        (neg_one_smul ℝ (B.toFun x)).symm,
        tensorInnerPointwise_smul_right]
      ring
    rw [heq]
    exact hcross.neg
  have hWW_int : MeasureTheory.Integrable
      (fun x => tensorInnerPointwise (I := I) (M := M) q 0 (0 + n + 1) x
        (TensorRSSpace.toModel (A.toSection x))
        (TensorRSSpace.toModel (A.toSection x)))
      (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure
        (I := I) (M := M) q) := by
    simpa only [SmoothCcTensor.toFun_apply] using
      (SmoothCcTensor.integrable_inner_cross (I := I) (M := M) A A)
  have hneg := neg_gInvDiffSlot_le (I := I) (M := M)
    q h k htie hδ_lt hδ_nn hδ (0 + n) (fun x => A.toSection x) hWS_int hWW_int
  have hAfun :
      (fun x => TensorRSSpace.toModel (A.toSection x)) = A.toFun := rfl
  have hnegfun :
      (fun x => -TensorRSSpace.toModel
        (gInvDiffSlotApplied (I := I) q h (0 + n) x (A.toSection x))) = -B.toFun := by
    funext x
    rw [Pi.neg_apply, hBfun]
  rw [hAfun, hnegfun] at hneg
  have hminus :
      tensorL2Inner (I := I) (M := M) q 0 (0 + n + 1) A.toFun (-B.toFun) =
        -tensorL2Inner (I := I) (M := M) q 0 (0 + n + 1) A.toFun B.toFun := by
    rw [show -B.toFun = (-1 : ℝ) • B.toFun from
      (neg_one_smul ℝ B.toFun).symm,
      tensorL2Inner_smul_right]
    ring
  have hnorm :
      tensorL2Inner (I := I) (M := M) q 0 (0 + n + 1) A.toFun A.toFun =
        ‖SmoothCcTensor.toL2 A‖ ^ 2 := by
    have hAA : tensorL2Inner (I := I) (M := M) q 0 (0 + n + 1) A.toFun A.toFun =
        (⟪A, A⟫_ℝ : ℝ) :=
      (SmoothCcTensor.inner_def (I := I) (M := M) A A).symm
    rw [hAA, real_inner_self_eq_norm_sq, SmoothCcTensor.norm_toL2]
  rw [hminus, hnorm] at hneg
  simpa only [A, B] using hneg



omit [BoundarylessManifold I M] in
theorem cc_last_pair
    (q h : SmoothRiemannianMetric I M)
    (k : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      h.inner y v w = q.inner y v w + k y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ)
    (hδ : metricCauchySchwarzBound (I := I) q k δ)
    (n : ℕ) (U : SmoothCcTensor q 0 0) :
    -tensorL2Inner (I := I) (M := M) q 0 (1 + n)
        (castCcTensorRank (I := I) (M := M) q 0
          (by omega : 0 + (n + 1) = 1 + n)
          (iteratedCovGrad (I := I) q 0 0 (n + 1) U)).toFun
        (ccOperatorFieldComp (I := I) (M := M) q 0 (1 + n) (1 + n)
          (slotExtendIter (I := I) (M := M) q 1 1 n
            (endoSlotZeroCcTensor (I := I) (M := M) q 0
              (gInvDiffRaisedEndoField (I := I) q h)))
          (castCcTensorRank (I := I) (M := M) q 0
            (by omega : 0 + (n + 1) = 1 + n)
            (iteratedCovGrad (I := I) q 0 0 (n + 1) U))).toFun ≤
      (δ / (1 - δ)) *
        ‖SmoothCcTensor.toL2
          (castCcTensorRank (I := I) (M := M) q 0
            (by omega : 0 + (n + 1) = 1 + n)
            (iteratedCovGrad (I := I) q 0 0 (n + 1) U))‖ ^ 2 := by
  let A : SmoothCcTensor q 0 (1 + n) :=
    castCcTensorRank (I := I) (M := M) q 0
      (by omega : 0 + (n + 1) = 1 + n)
      (iteratedCovGrad (I := I) q 0 0 (n + 1) U)
  let B : SmoothCcTensor q 0 (1 + n) :=
    ccOperatorFieldComp (I := I) (M := M) q 0 (1 + n) (1 + n)
      (slotExtendIter (I := I) (M := M) q 1 1 n
        (endoSlotZeroCcTensor (I := I) (M := M) q 0
          (gInvDiffRaisedEndoField (I := I) q h))) A
  have hBsec (x : M) :
      B.toSection x = gInvDiffSlotAt (I := I) q h (1 + n) ⟨n, by omega⟩ x
        (A.toSection x) := by
    apply tensorRSSpace_ext 0 (1 + n) x
    intro d
    dsimp only [B]
    rw [app_slotExt_apply (I := I) (M := M)]
    rfl
  have hBfun (x : M) :
      B.toFun x = TensorRSSpace.toModel
        (gInvDiffSlotAt (I := I) q h (1 + n) ⟨n, by omega⟩ x
          (A.toSection x)) := by
    rw [SmoothCcTensor.toFun_apply, hBsec]
  have hWS_int : MeasureTheory.Integrable
      (fun x ↦ tensorInnerPointwise (I := I) (M := M) q 0 (1 + n) x
        (TensorRSSpace.toModel (A.toSection x))
        (-TensorRSSpace.toModel
          (gInvDiffSlotAt (I := I) q h (1 + n) ⟨n, by omega⟩ x
            (A.toSection x))))
      (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure
        (I := I) (M := M) q) := by
    have hcross := SmoothCcTensor.integrable_inner_cross
      (I := I) (M := M) A B
    have heq :
        (fun x ↦ tensorInnerPointwise (I := I) (M := M) q 0 (1 + n) x
          (TensorRSSpace.toModel (A.toSection x))
          (-TensorRSSpace.toModel
            (gInvDiffSlotAt (I := I) q h (1 + n) ⟨n, by omega⟩ x
              (A.toSection x)))) =
          (fun x ↦ -tensorInnerPointwise (I := I) (M := M) q 0 (1 + n) x
            (A.toFun x) (B.toFun x)) := by
      funext x
      rw [← SmoothCcTensor.toFun_apply A x, ← hBfun x]
      rw [show -B.toFun x = (-1 : ℝ) • B.toFun x from
        (neg_one_smul ℝ (B.toFun x)).symm,
        tensorInnerPointwise_smul_right]
      ring
    rw [heq]
    exact hcross.neg
  have hWW_int : MeasureTheory.Integrable
      (fun x ↦ tensorInnerPointwise (I := I) (M := M) q 0 (1 + n) x
        (TensorRSSpace.toModel (A.toSection x))
        (TensorRSSpace.toModel (A.toSection x)))
      (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure
        (I := I) (M := M) q) := by
    simpa only [SmoothCcTensor.toFun_apply] using
      (SmoothCcTensor.integrable_inner_cross (I := I) (M := M) A A)
  have hneg := negSlotAtL2_le (I := I) (M := M)
    q h k htie hδ_lt hδ_nn hδ (1 + n) ⟨n, by omega⟩
      (fun x ↦ A.toSection x) hWS_int hWW_int
  have hAfun :
      (fun x ↦ TensorRSSpace.toModel (A.toSection x)) = A.toFun := rfl
  have hnegfun :
      (fun x ↦ -TensorRSSpace.toModel
        (gInvDiffSlotAt (I := I) q h (1 + n) ⟨n, by omega⟩ x
          (A.toSection x))) = -B.toFun := by
    funext x
    rw [Pi.neg_apply, hBfun]
  rw [hAfun, hnegfun] at hneg
  have hminus :
      tensorL2Inner (I := I) (M := M) q 0 (1 + n) A.toFun (-B.toFun) =
        -tensorL2Inner (I := I) (M := M) q 0 (1 + n) A.toFun B.toFun := by
    rw [show -B.toFun = (-1 : ℝ) • B.toFun from
      (neg_one_smul ℝ B.toFun).symm,
      tensorL2Inner_smul_right]
    ring
  have hnorm :
      tensorL2Inner (I := I) (M := M) q 0 (1 + n) A.toFun A.toFun =
        ‖SmoothCcTensor.toL2 A‖ ^ 2 := by
    have hAA : tensorL2Inner (I := I) (M := M) q 0 (1 + n) A.toFun A.toFun =
        (⟪A, A⟫_ℝ : ℝ) :=
      (SmoothCcTensor.inner_def (I := I) (M := M) A A).symm
    rw [hAA, real_inner_self_eq_norm_sq, SmoothCcTensor.norm_toL2]
  rw [hminus, hnorm] at hneg
  simpa only [A, B] using hneg


noncomputable def scalarTraceCoeff
    (q h : SmoothRiemannianMetric I M) : SmoothCcTensor q 2 0 :=
  traceCast (I := I) q h - cometricDoubleTraceField (I := I) q 0



omit [BoundarylessManifold I M] in
theorem scalar_trace_factor
    (q h : SmoothRiemannianMetric I M) :
    scalarTraceCoeff (I := I) q h =
      ccOperatorFieldComp (I := I) (M := M) q 2 2 0
        (cometricDoubleTraceField (I := I) q 0)
        (slotExtend (I := I) (M := M) q 1 1
          (scalarFluxCoeff (I := I) q h)) := by
  rw [scalarTraceCoeff, scalarFluxCoeff, slotExtend_sub, ccOperatorFieldComp_sub_right]
  rw [← trace_retag_eq (I := I) (M := M) q h,
    ← trace_retag_eq (I := I) (M := M) q q, traceCast_self]



theorem scalar_flux_split
    (q h : SmoothRiemannianMetric I M) (U : SmoothCcTensor q 0 0) :
    operatorFieldApply (I := I) (M := M) q 2 0 (scalarTraceCoeff (I := I) q h)
        (iteratedCovGrad (I := I) q 0 0 2 U) =
      covDivergence (I := I) (M := M) q 0
          (operatorFieldApply (I := I) (M := M) q 1 1
            (scalarFluxCoeff (I := I) q h)
            (iteratedCovGrad (I := I) q 0 0 1 U)) -
        operatorFieldApply (I := I) (M := M) q 1 0
          (ccOperatorFieldComp (I := I) (M := M) q 1 2 0
            (cometricDoubleTraceField (I := I) q 0)
            (covGrad (I := I) (M := M) q 1 1
              (scalarFluxCoeff (I := I) q h)))
          (iteratedCovGrad (I := I) q 0 0 1 U) := by
  have htwo :
      covGrad (I := I) (M := M) q 0 1
          (iteratedCovGrad (I := I) q 0 0 1 U) =
        iteratedCovGrad (I := I) q 0 0 2 U := by
    exact (iteratedCovGrad_succ (I := I) q 0 0 1 U).symm
  have hdiv := covDiv_appCc (I := I) (M := M) q
    (scalarFluxCoeff (I := I) q h)
    (iteratedCovGrad (I := I) q 0 0 1 U)
  rw [htwo] at hdiv
  rw [scalar_trace_factor, hdiv]
  abel



theorem cc_pair_split
    (q h : SmoothRiemannianMetric I M) (X U : SmoothCcTensor q 0 0) :
    tensorL2Inner (I := I) (M := M) q 0 0
        X.toFun
        (operatorFieldApply (I := I) (M := M) q 2 0
          (scalarTraceCoeff (I := I) q h)
          (iteratedCovGrad (I := I) q 0 0 2 U)).toFun =
      -tensorL2Inner (I := I) (M := M) q 0 1
          (covGrad (I := I) (M := M) q 0 0
            X).toFun
          (operatorFieldApply (I := I) (M := M) q 1 1
            (endoSlotZeroCcTensor (I := I) (M := M) q 0
              (gInvDiffRaisedEndoField (I := I) q h))
            (iteratedCovGrad (I := I) q 0 0 1 U)).toFun -
        tensorL2Inner (I := I) (M := M) q 0 0
          X.toFun
          (operatorFieldApply (I := I) (M := M) q 1 0
            (ccOperatorFieldComp (I := I) (M := M) q 1 2 0
              (cometricDoubleTraceField (I := I) q 0)
              (covGrad (I := I) (M := M) q 1 1
                (scalarFluxCoeff (I := I) q h)))
            (iteratedCovGrad (I := I) q 0 0 1 U)).toFun := by
  let B₀ : SmoothCcTensor q 0 1 :=
    operatorFieldApply (I := I) (M := M) q 1 1
      (scalarFluxCoeff (I := I) q h)
      (iteratedCovGrad (I := I) q 0 0 1 U)
  let B : SmoothCcTensor q 0 1 :=
    operatorFieldApply (I := I) (M := M) q 1 1
      (endoSlotZeroCcTensor (I := I) (M := M) q 0
        (gInvDiffRaisedEndoField (I := I) q h))
      (iteratedCovGrad (I := I) q 0 0 1 U)
  let D : SmoothCcTensor q 0 0 :=
    operatorFieldApply (I := I) (M := M) q 1 0
      (ccOperatorFieldComp (I := I) (M := M) q 1 2 0
        (cometricDoubleTraceField (I := I) q 0)
        (covGrad (I := I) (M := M) q 1 1
          (scalarFluxCoeff (I := I) q h)))
      (iteratedCovGrad (I := I) q 0 0 1 U)
  have hB : B₀ = B := by
    exact cc_flux_slot (I := I) (M := M) q h
      (iteratedCovGrad (I := I) q 0 0 1 U)
  have hgreen :
      tensorL2Inner (I := I) (M := M) q 0 1
          (covGrad (I := I) (M := M) q 0 0 X).toFun B₀.toFun =
        -tensorL2Inner (I := I) (M := M) q 0 0 X.toFun
          (covDivergence (I := I) (M := M) q 0 B₀).toFun := by
    exact tensorL2Inner_covGrad_eq_neg_tensorL2Inner_covDivergence
      (I := I) (M := M) q 0 X B₀
  have hsub :
      tensorL2Inner (I := I) (M := M) q 0 0 X.toFun
          (covDivergence (I := I) (M := M) q 0 B₀ - D).toFun =
        tensorL2Inner (I := I) (M := M) q 0 0 X.toFun
            (covDivergence (I := I) (M := M) q 0 B₀).toFun -
          tensorL2Inner (I := I) (M := M) q 0 0 X.toFun D.toFun := by
    calc
      tensorL2Inner (I := I) (M := M) q 0 0 X.toFun
          (covDivergence (I := I) (M := M) q 0 B₀ - D).toFun =
          (⟪X, covDivergence (I := I) (M := M) q 0 B₀ - D⟫_ℝ : ℝ) :=
        (SmoothCcTensor.inner_def (I := I) (M := M) X
          (covDivergence (I := I) (M := M) q 0 B₀ - D)).symm
      _ = (⟪X, covDivergence (I := I) (M := M) q 0 B₀⟫_ℝ : ℝ) -
          (⟪X, D⟫_ℝ : ℝ) := by rw [inner_sub_right]
      _ = tensorL2Inner (I := I) (M := M) q 0 0 X.toFun
            (covDivergence (I := I) (M := M) q 0 B₀).toFun -
          tensorL2Inner (I := I) (M := M) q 0 0 X.toFun D.toFun := by
        rw [SmoothCcTensor.inner_def, SmoothCcTensor.inner_def]
  rw [scalar_flux_split (I := I) (M := M) q h U]
  change tensorL2Inner (I := I) (M := M) q 0 0 X.toFun
      (covDivergence (I := I) (M := M) q 0 B₀ - D).toFun = _
  rw [hsub]
  change tensorL2Inner (I := I) (M := M) q 0 0 X.toFun
        (covDivergence (I := I) (M := M) q 0 B₀).toFun -
      tensorL2Inner (I := I) (M := M) q 0 0 X.toFun D.toFun =
    -tensorL2Inner (I := I) (M := M) q 0 1
        (covGrad (I := I) (M := M) q 0 0 X).toFun B.toFun -
      tensorL2Inner (I := I) (M := M) q 0 0 X.toFun D.toFun
  rw [← hB]
  linarith



theorem cc_principal_pair
    (q h : SmoothRiemannianMetric I M)
    (k : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      h.inner y v w = q.inner y v w + k y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ)
    (hδ : metricCauchySchwarzBound (I := I) q k δ)
    (U : SmoothCcTensor q 0 0) :
    tensorL2Inner (I := I) (M := M) q 0 0 U.toFun
        (covDivergence (I := I) (M := M) q 0
          (operatorFieldApply (I := I) (M := M) q 1 1
            (scalarFluxCoeff (I := I) q h)
            (covGrad (I := I) (M := M) q 0 0 U))).toFun ≤
      (δ / (1 - δ)) *
        ‖SmoothCcTensor.toL2
          (covGrad (I := I) (M := M) q 0 0 U)‖ ^ 2 := by
  let A : SmoothCcTensor q 0 1 :=
    covGrad (I := I) (M := M) q 0 0 U
  let B : SmoothCcTensor q 0 1 :=
    operatorFieldApply (I := I) (M := M) q 1 1 (scalarFluxCoeff (I := I) q h) A
  have hBsec (x : M) :
      B.toSection x =
        gInvDiffSlotApplied (I := I) q h 0 x (A.toSection x) := by
    apply tensorRSSpace_ext 0 1 x
    intro z
    apply cotangentToDualLinear_injective (I := I) (x := x)
    apply LinearMap.ext
    intro w
    rw [cotangentToDualLinear_apply, cotangentToDualLinear_apply]
    change cotangentToDual (I := I)
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
          (scalarFluxCoeff (I := I) q h).toSection x)
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 1 I x from
            A.toSection x) z)) w =
      cotangentToDual (I := I)
        (slotInsertEndoFib (I := I) (M := M) 1 0 x
          (metricComparisonDiffEndo (I := I) q h x)
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 1 I x from
            A.toSection x) z)) w
    rw [scalarFlux_eval (I := I) (M := M),
      cotangent_slot_apply (I := I) (M := M)]
  have hBfun (x : M) :
      B.toFun x = TensorRSSpace.toModel
        (gInvDiffSlotApplied (I := I) q h 0 x (A.toSection x)) := by
    rw [SmoothCcTensor.toFun_apply, hBsec]
  have hWS_int : MeasureTheory.Integrable
      (fun x => tensorInnerPointwise (I := I) (M := M) q 0 1 x
        (TensorRSSpace.toModel (A.toSection x))
        (-TensorRSSpace.toModel
          (gInvDiffSlotApplied (I := I) q h 0 x (A.toSection x))))
      (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure
        (I := I) (M := M) q) := by
    have hcross := SmoothCcTensor.integrable_inner_cross
      (I := I) (M := M) A B
    have heq :
        (fun x => tensorInnerPointwise (I := I) (M := M) q 0 1 x
          (TensorRSSpace.toModel (A.toSection x))
          (-TensorRSSpace.toModel
            (gInvDiffSlotApplied (I := I) q h 0 x (A.toSection x)))) =
          (fun x => -tensorInnerPointwise (I := I) (M := M) q 0 1 x
            (A.toFun x) (B.toFun x)) := by
      funext x
      rw [← SmoothCcTensor.toFun_apply A x, ← hBfun x]
      rw [show -B.toFun x = (-1 : ℝ) • B.toFun x from
        (neg_one_smul ℝ (B.toFun x)).symm,
        tensorInnerPointwise_smul_right]
      ring
    rw [heq]
    exact hcross.neg
  have hWW_int : MeasureTheory.Integrable
      (fun x => tensorInnerPointwise (I := I) (M := M) q 0 1 x
        (TensorRSSpace.toModel (A.toSection x))
        (TensorRSSpace.toModel (A.toSection x)))
      (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure
        (I := I) (M := M) q) := by
    simpa only [SmoothCcTensor.toFun_apply] using
      (SmoothCcTensor.integrable_inner_cross (I := I) (M := M) A A)
  have hneg := neg_gInvDiffSlot_le (I := I) (M := M)
    q h k htie hδ_lt hδ_nn hδ 0 (fun x => A.toSection x) hWS_int hWW_int
  have hAfun :
      (fun x => TensorRSSpace.toModel (A.toSection x)) = A.toFun := rfl
  have hnegfun :
      (fun x => -TensorRSSpace.toModel
        (gInvDiffSlotApplied (I := I) q h 0 x (A.toSection x))) = -B.toFun := by
    funext x
    rw [Pi.neg_apply, hBfun]
  rw [hAfun, hnegfun] at hneg
  have hminus :
      tensorL2Inner (I := I) (M := M) q 0 1 A.toFun (-B.toFun) =
        -tensorL2Inner (I := I) (M := M) q 0 1 A.toFun B.toFun := by
    rw [show -B.toFun = (-1 : ℝ) • B.toFun from
      (neg_one_smul ℝ B.toFun).symm,
      tensorL2Inner_smul_right]
    ring
  have hnorm :
      tensorL2Inner (I := I) (M := M) q 0 1 A.toFun A.toFun =
        ‖SmoothCcTensor.toL2 A‖ ^ 2 := by
    have hAA : tensorL2Inner (I := I) (M := M) q 0 1 A.toFun A.toFun =
        (⟪A, A⟫_ℝ : ℝ) :=
      (SmoothCcTensor.inner_def (I := I) (M := M) A A).symm
    rw [hAA, real_inner_self_eq_norm_sq, SmoothCcTensor.norm_toL2]
  rw [hminus, hnorm] at hneg
  have hgreen :
      tensorL2Inner (I := I) (M := M) q 0 1 A.toFun B.toFun =
        -tensorL2Inner (I := I) (M := M) q 0 0 U.toFun
          (covDivergence (I := I) (M := M) q 0 B).toFun := by
    exact tensorL2Inner_covGrad_eq_neg_tensorL2Inner_covDivergence
      (I := I) (M := M) q 0 U B
  rw [hgreen, neg_neg] at hneg
  simpa only [A, B] using hneg



theorem cc_comm_pair (q h : SmoothRiemannianMetric I M) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ U : SmoothCcTensor q 0 0,
      |tensorL2Inner (I := I) (M := M) q 0 0
          (oneMinusConnLapSmoothIter (I := I) q 0 0 n U).toFun
          (operatorFieldApply (I := I) (M := M) q 2 0
            (scalarTraceCoeff (I := I) q h)
            (iteratedCovGrad (I := I) q 0 0 2 U)).toFun +
        tensorL2Inner (I := I) (M := M) q 0 (1 + n)
          (iteratedCovGrad (I := I) q 0 1 n
            (covGrad (I := I) (M := M) q 0 0 U)).toFun
          (ccOperatorFieldComp (I := I) (M := M) q 0 (1 + n) (1 + n)
            (slotExtendIter (I := I) (M := M) q 1 1 n
              (endoSlotZeroCcTensor (I := I) (M := M) q 0
                (gInvDiffRaisedEndoField (I := I) q h)))
            (iteratedCovGrad (I := I) q 0 1 n
              (covGrad (I := I) (M := M) q 0 0 U))).toFun| ≤
        C * ((∑ j ∈ Finset.range (n + 1),
            ‖iteratedCovGrad (I := I) q 0 0 j U‖) *
          (∑ j ∈ Finset.range (n + 2),
            ‖iteratedCovGrad (I := I) q 0 0 j U‖)) := by
  let C₀ : SmoothCcTensor q 1 1 :=
    endoSlotZeroCcTensor (I := I) (M := M) q 0
      (gInvDiffRaisedEndoField (I := I) q h)
  let Φ : SmoothCcTensor q 1 0 :=
    ccOperatorFieldComp (I := I) (M := M) q 1 2 0
      (cometricDoubleTraceField (I := I) q 0)
      (covGrad (I := I) (M := M) q 1 1
        (scalarFluxCoeff (I := I) q h))
  obtain ⟨Ct, hCt_nn, hCt⟩ :=
    slot_iterL_pair (I := I) (M := M) q 0 n C₀
  obtain ⟨Cd, hCd_nn, hCd⟩ :=
    iterL_pair_jet_le (I := I) (M := M) q 0 n Φ
  refine ⟨Ct + Cd, add_nonneg hCt_nn hCd_nn, fun U => ?_⟩
  let P : ℝ := tensorL2Inner (I := I) (M := M) q 0 0
    (oneMinusConnLapSmoothIter (I := I) q 0 0 n U).toFun
    (operatorFieldApply (I := I) (M := M) q 2 0
      (scalarTraceCoeff (I := I) q h)
      (iteratedCovGrad (I := I) q 0 0 2 U)).toFun
  let G : ℝ := tensorL2Inner (I := I) (M := M) q 0 1
    (covGrad (I := I) (M := M) q 0 0
      (oneMinusConnLapSmoothIter (I := I) q 0 0 n U)).toFun
    (operatorFieldApply (I := I) (M := M) q 1 1 C₀
      (covGrad (I := I) (M := M) q 0 0 U)).toFun
  let Htop : ℝ := tensorL2Inner (I := I) (M := M) q 0 (1 + n)
    (iteratedCovGrad (I := I) q 0 1 n
      (covGrad (I := I) (M := M) q 0 0 U)).toFun
    (ccOperatorFieldComp (I := I) (M := M) q 0 (1 + n) (1 + n)
      (slotExtendIter (I := I) (M := M) q 1 1 n C₀)
      (iteratedCovGrad (I := I) q 0 1 n
        (covGrad (I := I) (M := M) q 0 0 U))).toFun
  let D : ℝ := tensorL2Inner (I := I) (M := M) q 0 0
    (oneMinusConnLapSmoothIter (I := I) q 0 0 n U).toFun
    (operatorFieldApply (I := I) (M := M) q 1 0 Φ
      (covGrad (I := I) (M := M) q 0 0 U)).toFun
  let J : ℝ := (∑ j ∈ Finset.range (n + 1),
      ‖iteratedCovGrad (I := I) q 0 0 j U‖) *
    (∑ j ∈ Finset.range (n + 2),
      ‖iteratedCovGrad (I := I) q 0 0 j U‖)
  have htrans : |G - Htop| ≤ Ct * J := by
    simpa only [G, Htop, J, C₀, Nat.zero_add, appCcRS_zero_eq_appCc] using hCt U
  have hder : |D| ≤ Cd * J := by
    simpa only [D, J, Φ, Nat.zero_add] using hCd U
  have hgrad : iteratedCovGrad (I := I) q 0 0 1 U =
      covGrad (I := I) (M := M) q 0 0 U := rfl
  have hsplit : P = -G - D := by
    simpa only [P, G, D, C₀, Φ, hgrad] using
      cc_pair_split (I := I) (M := M) q h
        (oneMinusConnLapSmoothIter (I := I) q 0 0 n U) U
  have hid : P + Htop = -(G - Htop) - D := by
    linarith
  change |P + Htop| ≤ (Ct + Cd) * J
  rw [hid]
  calc
    |-(G - Htop) - D| = |-(G - Htop) + -D| := by rw [sub_eq_add_neg]
    _ ≤ |-(G - Htop)| + |-D| := abs_add_le _ _
    _ = |G - Htop| + |D| := by rw [abs_neg, abs_neg]
    _ ≤ Ct * J + Cd * J := add_le_add htrans hder
    _ = (Ct + Cd) * J := by ring



theorem cc_energy_diss
    (q h : SmoothRiemannianMetric I M)
    (k : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      h.inner y v w = q.inner y v w + k y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ)
    (hδ : metricCauchySchwarzBound (I := I) q k δ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ U : SmoothCcTensor q 0 0,
      tensorL2Inner (I := I) (M := M) q 0 0
          (oneMinusConnLapSmoothIter (I := I) q 0 0 n U).toFun
          (operatorFieldApply (I := I) (M := M) q 2 0
            (scalarTraceCoeff (I := I) q h)
            (iteratedCovGrad (I := I) q 0 0 2 U)).toFun ≤
        (δ / (1 - δ)) *
            ‖SmoothCcTensor.toL2
              (castCcTensorRank (I := I) (M := M) q 0
                (by omega : 0 + (n + 1) = 1 + n)
                (iteratedCovGrad (I := I) q 0 0 (n + 1) U))‖ ^ 2 +
          C * ((∑ j ∈ Finset.range (n + 1),
              ‖iteratedCovGrad (I := I) q 0 0 j U‖) *
            (∑ j ∈ Finset.range (n + 2),
              ‖iteratedCovGrad (I := I) q 0 0 j U‖)) := by
  obtain ⟨C, hC_nn, hC⟩ := cc_comm_pair (I := I) (M := M) q h n
  refine ⟨C, hC_nn, fun U => ?_⟩
  let A : SmoothCcTensor q 0 (1 + n) :=
    castCcTensorRank (I := I) (M := M) q 0
      (by omega : 0 + (n + 1) = 1 + n)
      (iteratedCovGrad (I := I) q 0 0 (n + 1) U)
  let P : ℝ := tensorL2Inner (I := I) (M := M) q 0 0
    (oneMinusConnLapSmoothIter (I := I) q 0 0 n U).toFun
    (operatorFieldApply (I := I) (M := M) q 2 0
      (scalarTraceCoeff (I := I) q h)
      (iteratedCovGrad (I := I) q 0 0 2 U)).toFun
  let Htop : ℝ := tensorL2Inner (I := I) (M := M) q 0 (1 + n) A.toFun
    (ccOperatorFieldComp (I := I) (M := M) q 0 (1 + n) (1 + n)
      (slotExtendIter (I := I) (M := M) q 1 1 n
        (endoSlotZeroCcTensor (I := I) (M := M) q 0
          (gInvDiffRaisedEndoField (I := I) q h))) A).toFun
  let J : ℝ := (∑ j ∈ Finset.range (n + 1),
      ‖iteratedCovGrad (I := I) q 0 0 j U‖) *
    (∑ j ∈ Finset.range (n + 2),
      ‖iteratedCovGrad (I := I) q 0 0 j U‖)
  have hfront :
      iteratedCovGrad (I := I) q 0 1 n
          (covGrad (I := I) (M := M) q 0 0 U) = A := by
    dsimp only [A]
    apply eq_of_heq
    exact HEq.trans
      (iteratedCovGrad_covGrad_comm_heq' (I := I) (M := M) q 0 0 n U)
      (castRankCc_db_heq (I := I) (M := M) q 0
        (by omega : 0 + (n + 1) = 1 + n)
        (iteratedCovGrad (I := I) q 0 0 (n + 1) U)).symm
  have hcomm : |P + Htop| ≤ C * J := by
    have h := hC U
    rw [hfront] at h
    simpa only [P, Htop, J] using h
  have hlast : -Htop ≤ (δ / (1 - δ)) * ‖SmoothCcTensor.toL2 A‖ ^ 2 := by
    simpa only [Htop, A] using
      cc_last_pair (I := I) (M := M) q h k htie hδ_lt hδ_nn hδ n U
  have hsum : P + Htop ≤ C * J :=
    le_trans (le_abs_self (P + Htop)) hcomm
  change P ≤ (δ / (1 - δ)) * ‖SmoothCcTensor.toL2 A‖ ^ 2 + C * J
  linarith



noncomputable def connTraceCoeff
    (q h : SmoothRiemannianMetric I M) : SmoothCcTensor q 1 0 :=
  ccOperatorFieldComp (I := I) (M := M) q 1 2 0 (traceCast (I := I) q h)
    (connDiffSection (I := I) h q)




noncomputable def scalarLapDiffCc
    (q h : SmoothRiemannianMetric I M) (U : SmoothCcTensor q 0 0) :
    SmoothCcTensor q 0 0 :=
  operatorFieldApply (I := I) (M := M) q 2 0 (scalarTraceCoeff (I := I) q h)
      (iteratedCovGrad (I := I) q 0 0 2 U) -
    operatorFieldApply (I := I) (M := M) q 1 0 (connTraceCoeff (I := I) q h)
      (iteratedCovGrad (I := I) q 0 0 1 U)



omit [NeZero (Module.finrank ℝ E)] in
theorem scalarLapDiff_add
    (q h : SmoothRiemannianMetric I M) (U V : SmoothCcTensor q 0 0) :
    scalarLapDiffCc (I := I) q h (U + V) =
      scalarLapDiffCc (I := I) q h U + scalarLapDiffCc (I := I) q h V := by
  simp only [scalarLapDiffCc, iteratedCovGrad_add, appCc_add_right]
  abel



omit [NeZero (Module.finrank ℝ E)] in
theorem scalarLapDiff_smul
    (q h : SmoothRiemannianMetric I M) (c : ℝ) (U : SmoothCcTensor q 0 0) :
    scalarLapDiffCc (I := I) q h (c • U) = c • scalarLapDiffCc (I := I) q h U := by
  simp only [scalarLapDiffCc, iteratedCovGrad_smul, appCc_smul_right]
  module



theorem cc_conn_pair (q h : SmoothRiemannianMetric I M) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ U : SmoothCcTensor q 0 0,
      |tensorL2Inner (I := I) (M := M) q 0 0
          (oneMinusConnLapSmoothIter (I := I) q 0 0 n U).toFun
          (operatorFieldApply (I := I) (M := M) q 1 0
            (connTraceCoeff (I := I) q h)
            (iteratedCovGrad (I := I) q 0 0 1 U)).toFun| ≤
        C * ((∑ j ∈ Finset.range (n + 1),
            ‖iteratedCovGrad (I := I) q 0 0 j U‖) *
          (∑ j ∈ Finset.range (n + 2),
            ‖iteratedCovGrad (I := I) q 0 0 j U‖)) := by
  simpa only [Nat.zero_add] using
    (iterL_pair_jet_le (I := I) (M := M) q 0 n
      (connTraceCoeff (I := I) q h))



theorem cc_lap_pair
    (q h : SmoothRiemannianMetric I M)
    (k : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      h.inner y v w = q.inner y v w + k y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ)
    (hδ : metricCauchySchwarzBound (I := I) q k δ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ U : SmoothCcTensor q 0 0,
      tensorL2Inner (I := I) (M := M) q 0 0
          (oneMinusConnLapSmoothIter (I := I) q 0 0 n U).toFun
          (scalarLapDiffCc (I := I) q h U).toFun ≤
        (δ / (1 - δ)) *
            ‖SmoothCcTensor.toL2
              (castCcTensorRank (I := I) (M := M) q 0
                (by omega : 0 + (n + 1) = 1 + n)
                (iteratedCovGrad (I := I) q 0 0 (n + 1) U))‖ ^ 2 +
          C * ((∑ j ∈ Finset.range (n + 1),
              ‖iteratedCovGrad (I := I) q 0 0 j U‖) *
            (∑ j ∈ Finset.range (n + 2),
              ‖iteratedCovGrad (I := I) q 0 0 j U‖)) := by
  obtain ⟨Cp, hCp_nn, hCp⟩ :=
    cc_energy_diss (I := I) (M := M) q h k htie hδ_lt hδ_nn hδ n
  obtain ⟨Cc, hCc_nn, hCc⟩ := cc_conn_pair (I := I) (M := M) q h n
  refine ⟨Cp + Cc, add_nonneg hCp_nn hCc_nn, fun U => ?_⟩
  let X : SmoothCcTensor q 0 0 :=
    oneMinusConnLapSmoothIter (I := I) q 0 0 n U
  let A : SmoothCcTensor q 0 0 :=
    operatorFieldApply (I := I) (M := M) q 2 0 (scalarTraceCoeff (I := I) q h)
      (iteratedCovGrad (I := I) q 0 0 2 U)
  let B : SmoothCcTensor q 0 0 :=
    operatorFieldApply (I := I) (M := M) q 1 0 (connTraceCoeff (I := I) q h)
      (iteratedCovGrad (I := I) q 0 0 1 U)
  let P : ℝ := tensorL2Inner (I := I) (M := M) q 0 0 X.toFun A.toFun
  let Q : ℝ := tensorL2Inner (I := I) (M := M) q 0 0 X.toFun B.toFun
  let D : ℝ := (δ / (1 - δ)) *
    ‖SmoothCcTensor.toL2
      (castCcTensorRank (I := I) (M := M) q 0
        (by omega : 0 + (n + 1) = 1 + n)
        (iteratedCovGrad (I := I) q 0 0 (n + 1) U))‖ ^ 2
  let J : ℝ :=
    (∑ j ∈ Finset.range (n + 1),
      ‖iteratedCovGrad (I := I) q 0 0 j U‖) *
    (∑ j ∈ Finset.range (n + 2),
      ‖iteratedCovGrad (I := I) q 0 0 j U‖)
  have hsplit :
      tensorL2Inner (I := I) (M := M) q 0 0 X.toFun
          (scalarLapDiffCc (I := I) q h U).toFun = P - Q := by
    rw [scalarLapDiffCc]
    calc
      tensorL2Inner (I := I) (M := M) q 0 0 X.toFun (A - B).toFun =
          (⟪X, A - B⟫_ℝ : ℝ) :=
        (SmoothCcTensor.inner_def (I := I) (M := M) X (A - B)).symm
      _ = (⟪X, A⟫_ℝ : ℝ) - (⟪X, B⟫_ℝ : ℝ) := by rw [inner_sub_right]
      _ = P - Q := by
        rw [SmoothCcTensor.inner_def, SmoothCcTensor.inner_def]
  have hp : P ≤ D + Cp * J := by
    simpa only [P, X, A, D, J] using hCp U
  have hq : -Q ≤ Cc * J := by
    exact le_trans (neg_le_abs Q) (by simpa only [Q, X, B, J] using hCc U)
  rw [show
    tensorL2Inner (I := I) (M := M) q 0 0
        (oneMinusConnLapSmoothIter (I := I) q 0 0 n U).toFun
        (scalarLapDiffCc (I := I) q h U).toFun = P - Q by
      simpa only [X] using hsplit]
  change P - Q ≤ D + (Cp + Cc) * J
  rw [sub_eq_add_neg]
  calc
    P + -Q ≤ (D + Cp * J) + Cc * J := add_le_add hp hq
    _ = D + (Cp + Cc) * J := by ring


omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem traceCast_apply
    (q h : SmoothRiemannianMetric I M) (W : SmoothCcTensor q 0 2) (x : M) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 0 I x from
            (operatorFieldApply (I := I) (M := M) q 2 0
              (traceCast (I := I) q h) W).toSection x)
          (unitZeroSec (I := I) (M := M) x))
        (fun i => Fin.elim0 i) =
      Tensor0SSpace.toModel
          (cometricDoubleTraceFib (I := I) h 0 x
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
                W.toSection x)
              (unitZeroSec (I := I) (M := M) x)))
        (fun i => Fin.elim0 i) := by
  rw [appCc_toSection, traceCast,
    SmoothCcTensor.retag_toSection, cometricDoubleTraceField_toSection]
  rfl



omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem scalarTrace_apply
    (q h : SmoothRiemannianMetric I M) (W : SmoothCcTensor q 0 2) (x : M) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 0 I x from
            (operatorFieldApply (I := I) (M := M) q 2 0
              (scalarTraceCoeff (I := I) q h) W).toSection x)
          (unitZeroSec (I := I) (M := M) x))
        (fun i => Fin.elim0 i) =
      Tensor0SSpace.toModel
          (cometricDoubleTraceFib (I := I) h 0 x
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
                W.toSection x)
              (unitZeroSec (I := I) (M := M) x)))
          (fun i => Fin.elim0 i) -
        Tensor0SSpace.toModel
          (cometricDoubleTraceFib (I := I) q 0 x
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
                W.toSection x)
              (unitZeroSec (I := I) (M := M) x)))
          (fun i => Fin.elim0 i) := by
  rw [scalarTraceCoeff, appCc_sub_left]
  have h_sec :
      (operatorFieldApply (I := I) (M := M) q 2 0 (traceCast (I := I) q h) W -
          operatorFieldApply (I := I) (M := M) q 2 0
            (cometricDoubleTraceField (I := I) q 0) W).toSection x =
        (operatorFieldApply (I := I) (M := M) q 2 0 (traceCast (I := I) q h) W).toSection x -
          (operatorFieldApply (I := I) (M := M) q 2 0
            (cometricDoubleTraceField (I := I) q 0) W).toSection x := rfl
  rw [h_sec]
  rw [ContinuousLinearMap.sub_apply, Tensor0SSpace.toModel_sub,
    ContinuousMultilinearMap.sub_apply]
  rw [traceCast_apply (I := I) (M := M) q h W x]
  rw [appCc_toSection, cometricDoubleTraceField_toSection]
  rfl



omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem connTrace_apply
    (q h : SmoothRiemannianMetric I M) (W : SmoothCcTensor q 0 1) (x : M) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 0 I x from
            (operatorFieldApply (I := I) (M := M) q 1 0
              (connTraceCoeff (I := I) q h) W).toSection x)
          (unitZeroSec (I := I) (M := M) x))
        (fun i => Fin.elim0 i) =
      Tensor0SSpace.toModel
          (cometricDoubleTraceFib (I := I) h 0 x
            ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
                connDiffFib (I := I) h q x)
              ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 1 I x from
                  W.toSection x)
                (unitZeroSec (I := I) (M := M) x))))
        (fun i => Fin.elim0 i) := by
  rw [connTraceCoeff, appCc_toSection, appCcRS_toSection, traceCast,
    SmoothCcTensor.retag_toSection, cometricDoubleTraceField_toSection,
    connDiffSection_toSection]
  rfl



omit [NeZero (Module.finrank ℝ E)] in
theorem scalarLapDiff_apply
    (q h : SmoothRiemannianMetric I M) (U : SmoothCcTensor q 0 0) (x : M) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 0 I x from
            (scalarLapDiffCc (I := I) q h U).toSection x)
          (unitZeroSec (I := I) (M := M) x))
        (fun i => Fin.elim0 i) =
      (Tensor0SSpace.toModel
          (cometricDoubleTraceFib (I := I) h 0 x
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
                (iteratedCovGrad (I := I) q 0 0 2 U).toSection x)
              (unitZeroSec (I := I) (M := M) x)))
          (fun i => Fin.elim0 i) -
        Tensor0SSpace.toModel
          (cometricDoubleTraceFib (I := I) q 0 x
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
                (iteratedCovGrad (I := I) q 0 0 2 U).toSection x)
              (unitZeroSec (I := I) (M := M) x)))
          (fun i => Fin.elim0 i)) -
        Tensor0SSpace.toModel
          (cometricDoubleTraceFib (I := I) h 0 x
            ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
                connDiffFib (I := I) h q x)
              ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 1 I x from
                  (iteratedCovGrad (I := I) q 0 0 1 U).toSection x)
                (unitZeroSec (I := I) (M := M) x))))
          (fun i => Fin.elim0 i) := by
  rw [scalarLapDiffCc]
  have h_sec :
      (operatorFieldApply (I := I) (M := M) q 2 0 (scalarTraceCoeff (I := I) q h)
            (iteratedCovGrad (I := I) q 0 0 2 U) -
          operatorFieldApply (I := I) (M := M) q 1 0 (connTraceCoeff (I := I) q h)
            (iteratedCovGrad (I := I) q 0 0 1 U)).toSection x =
        (operatorFieldApply (I := I) (M := M) q 2 0 (scalarTraceCoeff (I := I) q h)
            (iteratedCovGrad (I := I) q 0 0 2 U)).toSection x -
          (operatorFieldApply (I := I) (M := M) q 1 0 (connTraceCoeff (I := I) q h)
            (iteratedCovGrad (I := I) q 0 0 1 U)).toSection x := rfl
  rw [h_sec, ContinuousLinearMap.sub_apply, Tensor0SSpace.toModel_sub,
    ContinuousMultilinearMap.sub_apply]
  rw [scalarTrace_apply (I := I) (M := M) q h
      (iteratedCovGrad (I := I) q 0 0 2 U) x,
    connTrace_apply (I := I) (M := M) q h
      (iteratedCovGrad (I := I) q 0 0 1 U) x]

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
