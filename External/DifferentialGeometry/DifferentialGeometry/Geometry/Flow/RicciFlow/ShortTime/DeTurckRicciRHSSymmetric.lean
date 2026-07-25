import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.RemainderShortTimeExistence
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.DeTurckGeometricNonlinearity


namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle
open scoped Manifold ContDiff NNReal ENNReal Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.PDE
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem deTurckRicciRHS_symm
    (g_bg g : SmoothRiemannianMetric I M) (x : M) (v w : TangentSpace I x) :
    deTurckRicciRHS (I := I) g_bg g x v w =
      deTurckRicciRHS (I := I) g_bg g x w v := by
  simp only [deTurckRicciRHS, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, lieDerivMetricClm_apply]
  rw [ricciTensor_symm (I := I) (smoothRiemannianMetricToInfty (I := I) g) x v w,
    DeTurck.lieDerivMetric_isPointwiseSymm (I := I)
      (smoothRiemannianMetricToInfty (I := I) g)
      (DeTurck.deTurckVF (I := I) (smoothRiemannianMetricToInfty (I := I) g)
        (smoothRiemannianMetricToInfty (I := I) g_bg)) x v w]

noncomputable def deTurckRHSSectionBg (g_bg g : SmoothRiemannianMetric I M) :
    DifferentialGeometry.Integral.L2.SmoothCcTensor g_bg 0 2 where
  toSection := (deTurckRHSSection (I := I) g_bg g).toSection
  hasCompactSupport := (deTurckRHSSection (I := I) g_bg g).hasCompactSupport

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
@[simp] theorem deTurckRHSSectionBg_toSection
    (g_bg g : SmoothRiemannianMetric I M) :
    (deTurckRHSSectionBg (I := I) g_bg g).toSection =
      (deTurckRHSSection (I := I) g_bg g).toSection := rfl

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem deTurckRHSSectionBg_toModel_apply
    (g_bg g : SmoothRiemannianMetric I M) (x : M) (v : Fin 2 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((deTurckRHSSectionBg (I := I) g_bg g).toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) v =
      deTurckRicciRHS (I := I) g_bg g x (v 0) (v 1) :=
  deTurckRHSSection_toModel_apply (I := I) g_bg g x v

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem deTurckRHSSection_ccTensorBilinSymm_eq_deTurckRicciRHS
    (g_bg g : SmoothRiemannianMetric I M) (x : M) (v w : TangentSpace I x) :
    ccTensorBilinSymm (I := I) g_bg (deTurckRHSSectionBg (I := I) g_bg g) x v w =
      deTurckRicciRHS (I := I) g_bg g x v w := by
  rw [ccTensorBilinSymm_apply]
  rw [ccTensorBilin_apply, ccTensorBilin_apply]
  unfold ccTensorModel
  rw [ccTensorMultilinear_apply]
  rw [deTurckRHSSectionBg_toModel_apply, deTurckRHSSectionBg_toModel_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [deTurckRicciRHS_symm (I := I) g_bg g x w v]
  ring

end DifferentialGeometry.PDE.RicciFlow
