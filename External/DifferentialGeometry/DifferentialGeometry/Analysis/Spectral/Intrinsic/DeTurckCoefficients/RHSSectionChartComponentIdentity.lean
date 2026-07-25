import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.DeTurckRicciRHSSymmetric
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.LieMatrixChartBridge
import DifferentialGeometry.Geometry.Connection.ChartBridge.RiemannBasisIdentityOffCentre
import DifferentialGeometry.Geometry.Flow.LieDerivativeChartFrameIdentity
import DifferentialGeometry.Analysis.Elliptic.TensorRegularity.CovDeriv.SlotCorrectionComponent

noncomputable section

set_option maxHeartbeats 1600000

open Bundle Manifold Set Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral
namespace DeTurckCoefficients

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.DeTurck
open DifferentialGeometry.PDE.DeTurck.DeTurckLinearization
open DifferentialGeometry.Analysis.Sobolev.Tensor
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private theorem tensorChartComponentRaw_deTurckRHSSectionBg_eq_deTurckRicciRHS
    (g_bg g₁ : SmoothRiemannianMetric I M) (α : M)
    {b : M} (hb : b ∈ (chartAt H α).source)
    (Idx : Fin 0 → Fin (Module.finrank ℝ E))
    (Jdx : Fin 2 → Fin (Module.finrank ℝ E)) :
    tensorChartComponentRaw (I := I) (M := M) g_bg 0 2
        (deTurckRHSSectionBg (I := I) g_bg g₁) α Idx Jdx b =
      deTurckRicciRHS (I := I) g_bg g₁ b
        (chartBasisVecFiber (I := I) α (Jdx 0) b)
        (chartBasisVecFiber (I := I) α (Jdx 1) b) := by
  classical

  rw [tensorChartComponentRaw_eq_chartFrame (I := I) (M := M) g_bg 0 2
    (deTurckRHSSectionBg (I := I) g_bg g₁) α hb Idx Jdx]

  have hframe : chartFrameBasisModel (I := I) (M := M) α b 0 Idx =
      (ContinuousMultilinearMap.constOfIsEmpty ℝ
        (fun _ : Fin 0 => TangentSpace I b) (1 : ℝ)) := by
    apply ContinuousMultilinearMap.ext
    intro v
    have h := chartFrameBasisModel_apply (I := I) (M := M) α b 0 Idx v
    rw [Fin.prod_univ_zero] at h
    rw [ContinuousMultilinearMap.constOfIsEmpty_apply]
    exact h
  rw [hframe]

  have hmodel := deTurckRHSSection_toModel_apply (I := I) g_bg g₁ b
    (fun k : Fin 2 => chartBasisVecFiber (I := I) α (Jdx k) b)

  rw [show (deTurckRHSSectionBg (I := I) g_bg g₁).toSection b =
      (deTurckRHSSection (I := I) g_bg g₁).toSection b from rfl]

  have hdirect :
      ((deTurckRHSSection (I := I) g_bg g₁).toSection b
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I b) (1 : ℝ)) :
        ContinuousMultilinearMap ℝ (fun _ : Fin 2 => TangentSpace I b) ℝ)
        (fun k : Fin 2 => chartBasisVecFiber (I := I) α (Jdx k) b) =
      Tensor0SSpace.toModel
        ((deTurckRHSSection (I := I) g_bg g₁).toSection b
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I b) (1 : ℝ)))
        (fun k : Fin 2 => chartBasisVecFiber (I := I) α (Jdx k) b) := rfl
  rw [hdirect, hmodel]

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem tensorChartComponentRaw_deTurckRHSSectionBg_eq_chartRicciLie
    (g_bg g₁ : SmoothRiemannianMetric I M) (α : M)
    {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α)
    (Idx : Fin 0 → Fin (Module.finrank ℝ E))
    (Jdx : Fin 2 → Fin (Module.finrank ℝ E)) :
    tensorChartComponentRaw (I := I) (M := M) g_bg 0 2
        (deTurckRHSSectionBg (I := I) g_bg g₁) α Idx Jdx b =
      (-2 : ℝ) * chartRicciTensor (I := I) g₁ α (Jdx 0) (Jdx 1) (extChartAt I α b) +
        chartLieDeTurckComp (I := I) g₁ g_bg α (Jdx 0) (Jdx 1) (extChartAt I α b) := by
  classical
  have hb_src : b ∈ (chartAt H α).source :=
    chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hb
  set v₀ : TangentSpace I b := chartBasisVecFiber (I := I) α (Jdx 0) b with hv₀_def
  set v₁ : TangentSpace I b := chartBasisVecFiber (I := I) α (Jdx 1) b with hv₁_def

  rw [tensorChartComponentRaw_deTurckRHSSectionBg_eq_deTurckRicciRHS (I := I) (M := M) g_bg g₁ α
      hb_src Idx Jdx]
  rw [show chartBasisVecFiber (I := I) α (Jdx 0) b = v₀ from rfl,
    show chartBasisVecFiber (I := I) α (Jdx 1) b = v₁ from rfl]

  rw [deTurckRicciRHS, ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]

  have hRic :
      ricciTensor (I := I) (smoothRiemannianMetricToInfty (I := I) g₁) b v₀ v₁ =
        chartRicciTensor (I := I) g₁ α (Jdx 0) (Jdx 1) (extChartAt I α b) := by
    have h := ricciTensor_chartBasisVec_alpha_eq (I := I) g₁ α (Jdx 0) (Jdx 1) hb
    rw [hv₀_def, hv₁_def]
    exact h

  have hLie :
      lieDerivMetricClm (I := I) g₁
        (deTurckVF (I := I) (smoothRiemannianMetricToInfty (I := I) g₁)
          (smoothRiemannianMetricToInfty (I := I) g_bg)) b v₀ v₁ =
        chartLieDeTurckComp (I := I) g₁ g_bg α (Jdx 0) (Jdx 1) (extChartAt I α b) := by
    rw [lieDerivMetricClm_apply]
    have hmat := chartLieDerivMetricMatrix_eq_lieDerivMetric_chartBasis (I := I)
      (smoothRiemannianMetricToInfty (I := I) g₁)
      (deTurckVF (I := I) (smoothRiemannianMetricToInfty (I := I) g₁)
        (smoothRiemannianMetricToInfty (I := I) g_bg))
      α (Jdx 0) (Jdx 1) b hb
    rw [hv₀_def, hv₁_def, ← hmat]
    exact chartLieDerivMetricMatrix_deTurckVF_eq_chartLieDeTurckComp (I := I) g₁ g_bg α
      (Jdx 0) (Jdx 1) hb
  rw [hRic, hLie]

end DeTurckCoefficients
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
