import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize
import DifferentialGeometry.Analysis.Elliptic.TensorRegularity.CovDeriv.SlotCorrectionComponent
import DifferentialGeometry.Geometry.Operator.Hessian


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
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
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


omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
theorem chartGramMatrix_realize_apply
    (g_bg : SmoothRiemannianMetric I M) (T : SmoothCcTensor g_bg 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g_bg (ccTensorBilinSymm (I := I) g_bg T) δ)
    (α x : M) (a b : Fin (Module.finrank ℝ E)) :
    chartGramMatrix (I := I) (tensorSectionRealizeMetric (I := I) g_bg T hδ_lt hδ) α x a b =
      chartGramMatrix (I := I) g_bg α x a b +
        ccTensorBilinSymm (I := I) g_bg T x
          (chartBasisVecFiber (I := I) α a x)
          (chartBasisVecFiber (I := I) α b x) := by
  rw [chartGramMatrix_apply, chartGramMatrix_apply,
    tensorSectionRealizeMetric_inner (I := I) g_bg T hδ_lt hδ x]

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
theorem chartGramOnE_realize_sub_eq_symm_rawComponent
    (g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g_bg 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g_bg (ccTensorBilinSymm (I := I) g_bg T) δ)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g_bg (ccTensorBilinSymm (I := I) g_bg T') δ)
    (α : M) (a b : Fin (Module.finrank ℝ E)) (y : E)
    (hp : (extChartAt I α).symm y ∈ (chartAt H α).source) :
    chartGramOnE (I := I) (tensorSectionRealizeMetric (I := I) g_bg T hδ_lt hδ) α a b y -
        chartGramOnE (I := I) (tensorSectionRealizeMetric (I := I) g_bg T' hδ_lt hδ') α a b y =
      (1 / 2 : ℝ) *
        (tensorChartComponentRaw (I := I) (M := M) g_bg 0 2 (T - T') α
            ![] ![a, b] ((extChartAt I α).symm y) +
          tensorChartComponentRaw (I := I) (M := M) g_bg 0 2 (T - T') α
            ![] ![b, a] ((extChartAt I α).symm y)) := by
  classical
  set p : M := (extChartAt I α).symm y with hp_def
  rw [chartGramOnE_def, chartGramOnE_def]
  rw [chartGramMatrix_realize_apply (I := I) g_bg T hδ_lt hδ α p a b,
    chartGramMatrix_realize_apply (I := I) g_bg T' hδ_lt hδ' α p a b]

  rw [show (chartGramMatrix (I := I) g_bg α p a b +
        ccTensorBilinSymm (I := I) g_bg T p
          (chartBasisVecFiber (I := I) α a p) (chartBasisVecFiber (I := I) α b p)) -
      (chartGramMatrix (I := I) g_bg α p a b +
        ccTensorBilinSymm (I := I) g_bg T' p
          (chartBasisVecFiber (I := I) α a p) (chartBasisVecFiber (I := I) α b p)) =
      ccTensorBilinSymm (I := I) g_bg T p
          (chartBasisVecFiber (I := I) α a p) (chartBasisVecFiber (I := I) α b p) -
        ccTensorBilinSymm (I := I) g_bg T' p
          (chartBasisVecFiber (I := I) α a p) (chartBasisVecFiber (I := I) α b p) by ring]

  rw [ccTensorBilinSymm_apply, ccTensorBilinSymm_apply]

  have hrawAB := tensorChartComponentRaw_eq_chartFrame (I := I) (M := M) g_bg 0 2
    (T - T') α hp (![] : Fin 0 → Fin (Module.finrank ℝ E))
    (![a, b] : Fin 2 → Fin (Module.finrank ℝ E))
  have hrawBA := tensorChartComponentRaw_eq_chartFrame (I := I) (M := M) g_bg 0 2
    (T - T') α hp (![] : Fin 0 → Fin (Module.finrank ℝ E))
    (![b, a] : Fin 2 → Fin (Module.finrank ℝ E))

  have hframe : chartFrameBasisModel (I := I) (M := M) α p 0
      (![] : Fin 0 → Fin (Module.finrank ℝ E)) =
      (ContinuousMultilinearMap.constOfIsEmpty ℝ
        (fun _ : Fin 0 => TangentSpace I p) (1 : ℝ)) := by
    apply ContinuousMultilinearMap.ext
    intro v
    have h := chartFrameBasisModel_apply (I := I) (M := M) α p 0
      (![] : Fin 0 → Fin (Module.finrank ℝ E)) v
    rw [Fin.prod_univ_zero] at h
    rw [ContinuousMultilinearMap.constOfIsEmpty_apply]
    exact h
  rw [hframe] at hrawAB hrawBA

  have hbilin : ∀ (i j : Fin (Module.finrank ℝ E)),
      ((T - T').toSection p
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I p) (1 : ℝ)) :
        ContinuousMultilinearMap ℝ (fun _ : Fin 2 => TangentSpace I p) ℝ)
          (fun k : Fin 2 =>
            chartBasisVecFiber (I := I) α ((![i, j] : Fin 2 → _) k) p) =
        smoothCcTensorBilinForm (I := I) g_bg T p
            (chartBasisVecFiber (I := I) α i p) (chartBasisVecFiber (I := I) α j p) -
          smoothCcTensorBilinForm (I := I) g_bg T' p
            (chartBasisVecFiber (I := I) α i p) (chartBasisVecFiber (I := I) α j p) := by
    intro i j
    have hvecAB : (fun k : Fin 2 =>
        chartBasisVecFiber (I := I) α ((![i, j] : Fin 2 → _) k) p) =
        ![chartBasisVecFiber (I := I) α i p, chartBasisVecFiber (I := I) α j p] := by
      funext k; fin_cases k <;> rfl
    rw [hvecAB, ccTensorBilin_apply, ccTensorBilin_apply]

    change Tensor0SSpace.toModel
        ((T - T').toSection p
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I p) (1 : ℝ)))
        ![chartBasisVecFiber (I := I) α i p, chartBasisVecFiber (I := I) α j p] = _
    rw [SmoothCcTensor.toSection_sub]
    simp only [ContMDiffSection.coe_sub, Pi.sub_apply]
    rfl
  rw [hrawAB, hrawBA, hbilin a b, hbilin b a]

  rw [ccTensorBilin_apply, ccTensorBilin_apply, ccTensorBilin_apply, ccTensorBilin_apply]
  ring

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
theorem chartGramOnE_realize_sub_eq_symm_rawComponent_two_witness
    (g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g_bg 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g_bg (ccTensorBilinSymm (I := I) g_bg T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g_bg (ccTensorBilinSymm (I := I) g_bg T') δ')
    (α : M) (a b : Fin (Module.finrank ℝ E)) (y : E)
    (hp : (extChartAt I α).symm y ∈ (chartAt H α).source) :
    chartGramOnE (I := I) (tensorSectionRealizeMetric (I := I) g_bg T hδ_lt hδ) α a b y -
        chartGramOnE (I := I) (tensorSectionRealizeMetric (I := I) g_bg T' hδ'_lt hδ') α a b y =
      (1 / 2 : ℝ) *
        (tensorChartComponentRaw (I := I) (M := M) g_bg 0 2 (T - T') α
            ![] ![a, b] ((extChartAt I α).symm y) +
          tensorChartComponentRaw (I := I) (M := M) g_bg 0 2 (T - T') α
            ![] ![b, a] ((extChartAt I α).symm y)) := by
  classical
  set p : M := (extChartAt I α).symm y with hp_def
  rw [chartGramOnE_def, chartGramOnE_def]
  rw [chartGramMatrix_realize_apply (I := I) g_bg T hδ_lt hδ α p a b,
    chartGramMatrix_realize_apply (I := I) g_bg T' hδ'_lt hδ' α p a b]
  rw [show (chartGramMatrix (I := I) g_bg α p a b +
        ccTensorBilinSymm (I := I) g_bg T p
          (chartBasisVecFiber (I := I) α a p) (chartBasisVecFiber (I := I) α b p)) -
      (chartGramMatrix (I := I) g_bg α p a b +
        ccTensorBilinSymm (I := I) g_bg T' p
          (chartBasisVecFiber (I := I) α a p) (chartBasisVecFiber (I := I) α b p)) =
      ccTensorBilinSymm (I := I) g_bg T p
          (chartBasisVecFiber (I := I) α a p) (chartBasisVecFiber (I := I) α b p) -
        ccTensorBilinSymm (I := I) g_bg T' p
          (chartBasisVecFiber (I := I) α a p) (chartBasisVecFiber (I := I) α b p) by ring]
  rw [ccTensorBilinSymm_apply, ccTensorBilinSymm_apply]
  have hrawAB := tensorChartComponentRaw_eq_chartFrame (I := I) (M := M) g_bg 0 2
    (T - T') α hp (![] : Fin 0 → Fin (Module.finrank ℝ E))
    (![a, b] : Fin 2 → Fin (Module.finrank ℝ E))
  have hrawBA := tensorChartComponentRaw_eq_chartFrame (I := I) (M := M) g_bg 0 2
    (T - T') α hp (![] : Fin 0 → Fin (Module.finrank ℝ E))
    (![b, a] : Fin 2 → Fin (Module.finrank ℝ E))
  have hframe : chartFrameBasisModel (I := I) (M := M) α p 0
      (![] : Fin 0 → Fin (Module.finrank ℝ E)) =
      (ContinuousMultilinearMap.constOfIsEmpty ℝ
        (fun _ : Fin 0 => TangentSpace I p) (1 : ℝ)) := by
    apply ContinuousMultilinearMap.ext
    intro v
    have h := chartFrameBasisModel_apply (I := I) (M := M) α p 0
      (![] : Fin 0 → Fin (Module.finrank ℝ E)) v
    rw [Fin.prod_univ_zero] at h
    rw [ContinuousMultilinearMap.constOfIsEmpty_apply]
    exact h
  rw [hframe] at hrawAB hrawBA
  have hbilin : ∀ (i j : Fin (Module.finrank ℝ E)),
      ((T - T').toSection p
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I p) (1 : ℝ)) :
        ContinuousMultilinearMap ℝ (fun _ : Fin 2 => TangentSpace I p) ℝ)
          (fun k : Fin 2 =>
            chartBasisVecFiber (I := I) α ((![i, j] : Fin 2 → _) k) p) =
        smoothCcTensorBilinForm (I := I) g_bg T p
            (chartBasisVecFiber (I := I) α i p) (chartBasisVecFiber (I := I) α j p) -
          smoothCcTensorBilinForm (I := I) g_bg T' p
            (chartBasisVecFiber (I := I) α i p) (chartBasisVecFiber (I := I) α j p) := by
    intro i j
    have hvecAB : (fun k : Fin 2 =>
        chartBasisVecFiber (I := I) α ((![i, j] : Fin 2 → _) k) p) =
        ![chartBasisVecFiber (I := I) α i p, chartBasisVecFiber (I := I) α j p] := by
      funext k; fin_cases k <;> rfl
    rw [hvecAB, ccTensorBilin_apply, ccTensorBilin_apply]
    change Tensor0SSpace.toModel
        ((T - T').toSection p
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I p) (1 : ℝ)))
        ![chartBasisVecFiber (I := I) α i p, chartBasisVecFiber (I := I) α j p] = _
    rw [SmoothCcTensor.toSection_sub]
    simp only [ContMDiffSection.coe_sub, Pi.sub_apply]
    rfl
  rw [hrawAB, hrawBA, hbilin a b, hbilin b a]
  rw [ccTensorBilin_apply, ccTensorBilin_apply, ccTensorBilin_apply, ccTensorBilin_apply]
  ring

end DeTurckCoefficients
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
