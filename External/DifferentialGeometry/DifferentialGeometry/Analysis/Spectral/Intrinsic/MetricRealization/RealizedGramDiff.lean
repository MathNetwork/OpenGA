import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.DeTurckGeometricNonlinearity






































noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral
namespace MetricRealization

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]



omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem ccTensorMultilinear_sub (g : SmoothRiemannianMetric I M)
    (S T : SmoothCcTensor g 0 2) (x : M) :
    (ccTensorMultilinear (I := I) g (S - T) x : Tensor0SSpace 2 I x)
      = (ccTensorMultilinear (I := I) g S x : Tensor0SSpace 2 I x)
        - (ccTensorMultilinear (I := I) g T x : Tensor0SSpace 2 I x) := by
  unfold ccTensorMultilinear
  rw [SmoothCcTensor.toSection_sub]
  change ((S.toSection - T.toSection) x)
      (ContinuousMultilinearMap.constOfIsEmpty ℝ
        (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))
    = (S.toSection x)
        (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))
      - (T.toSection x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))
  rw [ContMDiffSection.coe_sub, Pi.sub_apply, ContinuousLinearMap.sub_apply]


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem ccTensorModel_sub (g : SmoothRiemannianMetric I M)
    (S T : SmoothCcTensor g 0 2) (x : M) :
    ccTensorModel (I := I) g (S - T) x =
      ccTensorModel (I := I) g S x - ccTensorModel (I := I) g T x := by
  unfold ccTensorModel
  rw [ccTensorMultilinear_sub, Tensor0SSpace.toModel_sub]



omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem ccTensorBilin_sub (g : SmoothRiemannianMetric I M)
    (S T : SmoothCcTensor g 0 2) (x : M) (v w : TangentSpace I x) :
    smoothCcTensorBilinForm (I := I) g (S - T) x v w =
      smoothCcTensorBilinForm (I := I) g S x v w - smoothCcTensorBilinForm (I := I) g T x v w := by
  rw [ccTensorBilin_apply, ccTensorBilin_apply, ccTensorBilin_apply,
    ccTensorModel_sub, ContinuousMultilinearMap.sub_apply]



omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem ccTensorBilinSymm_sub (g : SmoothRiemannianMetric I M)
    (S T : SmoothCcTensor g 0 2) (x : M) (v w : TangentSpace I x) :
    ccTensorBilinSymm (I := I) g (S - T) x v w =
      ccTensorBilinSymm (I := I) g S x v w -
        ccTensorBilinSymm (I := I) g T x v w := by
  simp only [ccTensorBilinSymm_apply, ccTensorBilin_sub]
  ring



def realizableRepr (g_bg : SmoothRiemannianMetric I M) {σ : ℝ}
    {u : tensorHs (I := I) (M := M) g_bg 0 2 σ}
    (hu : isRealizableMetricPerturbationAt (I := I) g_bg u) :
    SmoothCcTensor g_bg 0 2 :=
  Analysis.Parabolic.TensorSpectral.tensorHsSmoothRepr
    (I := I) (M := M) u hu.choose



omit [BoundarylessManifold I M] in
theorem realizeMetricAt_inner_eq_repr (g_bg : SmoothRiemannianMetric I M) {σ : ℝ}
    {u : tensorHs (I := I) (M := M) g_bg 0 2 σ}
    (hu : isRealizableMetricPerturbationAt (I := I) g_bg u) (x : M) (v w : TangentSpace I x) :
    (realizeMetricAt (I := I) g_bg u).inner x v w =
      g_bg.inner x v w +
        ccTensorBilinSymm (I := I) g_bg (realizableRepr (I := I) g_bg hu) x v w := by
  classical
  obtain ⟨hu_fs, δ', hδ'_lt, hδ'⟩ := id hu
  rw [realizeMetricAt_inner_of_realizable (I := I) g_bg u hu_fs hδ'_lt hδ' x v w]
  rfl



















omit [BoundarylessManifold I M] in
theorem chartGramMatrix_realizeMetricAt_sub_eq_reprDiff
    (g_bg : SmoothRiemannianMetric I M) {σ : ℝ}
    {u₁ u₂ : tensorHs (I := I) (M := M) g_bg 0 2 σ}
    (hu₁ : isRealizableMetricPerturbationAt (I := I) g_bg u₁) (hu₂ : isRealizableMetricPerturbationAt (I := I) g_bg u₂)
    (α : M) (x : M) (i j : Fin (Module.finrank ℝ E)) :
    chartGramMatrix (I := I) (realizeMetricAt (I := I) g_bg u₁) α x i j -
        chartGramMatrix (I := I) (realizeMetricAt (I := I) g_bg u₂) α x i j =
      ccTensorBilinSymm (I := I) g_bg
        (realizableRepr (I := I) g_bg hu₁ - realizableRepr (I := I) g_bg hu₂) x
        (chartBasisVecFiber (I := I) α i x)
        (chartBasisVecFiber (I := I) α j x) := by
  rw [chartGramMatrix_apply, chartGramMatrix_apply,
    realizeMetricAt_inner_eq_repr (I := I) g_bg hu₁ x _ _,
    realizeMetricAt_inner_eq_repr (I := I) g_bg hu₂ x _ _,
    ccTensorBilinSymm_sub]
  ring




omit [BoundarylessManifold I M] in
theorem chartGramOnE_realizeMetricAt_sub_eq_reprDiff
    (g_bg : SmoothRiemannianMetric I M) {σ : ℝ}
    {u₁ u₂ : tensorHs (I := I) (M := M) g_bg 0 2 σ}
    (hu₁ : isRealizableMetricPerturbationAt (I := I) g_bg u₁) (hu₂ : isRealizableMetricPerturbationAt (I := I) g_bg u₂)
    (α : M) (i j : Fin (Module.finrank ℝ E)) (y : E) :
    chartGramOnE (I := I) (realizeMetricAt (I := I) g_bg u₁) α i j y -
        chartGramOnE (I := I) (realizeMetricAt (I := I) g_bg u₂) α i j y =
      ccTensorBilinSymm (I := I) g_bg
        (realizableRepr (I := I) g_bg hu₁ - realizableRepr (I := I) g_bg hu₂)
        ((extChartAt I α).symm y)
        (chartBasisVecFiber (I := I) α i ((extChartAt I α).symm y))
        (chartBasisVecFiber (I := I) α j ((extChartAt I α).symm y)) := by
  rw [chartGramOnE_def, chartGramOnE_def]
  exact chartGramMatrix_realizeMetricAt_sub_eq_reprDiff (I := I) g_bg hu₁ hu₂ α _ i j

end MetricRealization
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
