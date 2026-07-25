import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.RHSPathOrderSplit
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.LieCorr0Field
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.LieOneReanchor









noncomputable section

set_option linter.style.setOption false
set_option backward.isDefEq.respectTransparency false

open Set Bundle Manifold Tensor0SBundle ContinuousLinearMap
open scoped Topology Manifold BigOperators ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients

open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.PDE.DeTurck.DeTurckLinearization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]
  [BoundarylessManifold I M]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M]
    [T2Space M] [I.Boundaryless] [BoundarylessManifold I M] in
private theorem unitModel_add_local
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S S' : SmoothCcTensor g 0 s) (x : M) :
    unitModel (I := I) (M := M) g s (S + S') x =
      unitModel (I := I) (M := M) g s S x +
        unitModel (I := I) (M := M) g s S' x := by
  rw [unitModel, unitModel, unitModel]
  have hsec : (S + S').toSection x = S.toSection x + S'.toSection x := by
    rw [SmoothCcTensor.toSection_add]
    rfl
  rw [show ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        (S + S').toSection x) (unitTensor (I := I) (M := M) x)) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from S.toSection x)
          (unitTensor (I := I) (M := M) x) +
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from S'.toSection x)
          (unitTensor (I := I) (M := M) x) from by
    rw [hsec]
    rfl]
  rw [Tensor0SSpace.toModel_add]

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in


theorem lieSlope_eq_arms
    (g₀ g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) (x : M) (i j : Fin (Module.finrank ℝ E)) :
    lieDeTurckChartSlope (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' g_bg x i j s
        (extChartAt I x x) =
      unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 2 2
              (deTurckLieCoeffField (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg +
                lieCorr0Field (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
              (iteratedCovGrad (I := I) g₀ 0 2 0
                (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) +
            operatorFieldApply (I := I) (M := M) g₀ 3 2
              (deTurckLieArm1Coeff (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
              (iteratedCovGrad (I := I) g₀ 0 2 1
                (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) +
            operatorFieldApply (I := I) (M := M) g₀ 4 2
              (deTurckLieArm2PrincipalCoeff (I := I) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
              (iteratedCovGrad (I := I) g₀ 0 2 2
                (ccTensor02Symm (I := I) (M := M) g₀ (T - T')))) x
          ![(chartModelBasis E) i, (chartModelBasis E) j] := by
  classical
  have hy : extChartAt I x x ∈ interior ((extChartAt I x).target : Set E) :=
    extChartAt_target_subset_interior_of_boundaryless
      (I := I) x (mem_extChartAt_target x)
  have hsplit := lieDeTurckChartSlope_eq_orderSplit (I := I) g₀ T T'
    hδ_lt hδ hδ'_lt hδ' g_bg x i j s hy
  have h0 := lie0_order0_eq (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' g_bg s x i j
  have h1 := lieOne_cov_eq_raw (I := I) g₀ g_bg T T'
    hδ_lt hδ hδ'_lt hδ' s x i j
  have h2 := lieTop_cov_eq_raw (I := I) g₀ T T'
    hδ_lt hδ hδ'_lt hδ' (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x i j
  rw [lieTopTail] at h2
  refine hsplit.trans ?_
  rw [unitModel_add_local (I := I) g₀ 2, unitModel_add_local (I := I) g₀ 2,
    ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.add_apply]
  linear_combination -h0 - h1 - h2

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients
