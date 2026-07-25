import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.AbstractChartPullCutoff
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.ChartPartial.ChartPartialUniformBound
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChristoffelCorrection.CovL2BoundFromH1
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChristoffelCorrection.ChristoffelBound
import DifferentialGeometry.Analysis.Elliptic.TensorRegularity.CovDeriv.ChartFormLowerOrder
import DifferentialGeometry.Analysis.Elliptic.Regularity.SmoothFChartResidual.BilinearBound


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

def cutoffCovDerivComponent
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (k : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  fun y : EuclN =>
    chartPushedRaw (I := I) (M := M) α
        (⇑(chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯)) y *
      tensorChartComponentProjection (E := E) r s Idx Jdx
        ((trivializationAt (TensorRSModel r s ℝ E)
            (fun z : M => TensorRSSpace r s I z) α).continuousLinearMapAt ℝ
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
          (chartTensorRSCovariantDerivative (I := I) r s g α S.toSection
            (chartBasisVecFiber (I := I) α k)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))))

noncomputable def cutoffCovNormSumFun
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M) : M → ℝ :=
  fun b : M =>
    ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
      Real.sqrt
        (∑ i : Fin (Module.finrank ℝ E),
          ‖chartRSTwistInv (I := I) (M := M) α b r s
              (TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s S b
                  (chartBasisVecFiber (I := I) α i b)))‖ ^ 2)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma tensorRS_baseSet_eq_chart_source' (α : M) (r s : ℕ) :
    (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).baseSet =
      (chartAt H α).source := by
  change ((trivializationAt (Tensor0SModel r ℝ E)
        (fun y : M => Tensor0SSpace r I y) α).baseSet) ∩
      ((trivializationAt (Tensor0SModel s ℝ E)
        (fun y : M => Tensor0SSpace s I y) α).baseSet) =
        (chartAt H α).source
  change (trivializationAt E (TangentSpace I) α).baseSet ∩
      (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source
  rw [Set.inter_self]
  rfl

omit [CompleteSpace E] in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma chartRSTwistInv_tensorCovDeriv_contMDiffOn'
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (i : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I (𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun b : M =>
        chartRSTwistInv (I := I) (M := M) α b r s
          (TensorRSSpace.toModel
            (tensorCovDerivAt (I := I) (M := M) g r s S b
              (chartBasisVecFiber (I := I) α i b))))
      ((chartAt H α).source) := by
  classical
  have htriv := tensorCovDeriv_chartBasis_trivImage_contMDiffOn
    (I := I) (M := M) g r s S α i
  rw [show (trivializationAt E (TangentSpace I) α).baseSet =
      (chartAt H α).source from rfl] at htriv
  refine htriv.congr (fun b hb => ?_)
  rw [← triv_continuousLinearMapAt_eq_chartRSTwistInv_toModel (I := I) (M := M)
    r s α hb
    (tensorCovDerivAt (I := I) (M := M) g r s S b
      (chartBasisVecFiber (I := I) α i b))]
  have hb_base : b ∈ (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).baseSet := by
    rw [tensorRS_baseSet_eq_chart_source' (I := I) (M := M) α r s]
    exact hb
  change (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).linearMapAt ℝ b
      (tensorCovDerivAt (I := I) (M := M) g r s S b
        (chartBasisVecFiber (I := I) α i b)) = _
  rw [Bundle.Trivialization.linearMapAt_apply, if_pos hb_base]

omit [CompleteSpace E] in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma cutoffCovNormSqSum_continuousOn_chart_source
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M) :
    ContinuousOn
      (fun b : M =>
        ∑ i : Fin (Module.finrank ℝ E),
          ‖chartRSTwistInv (I := I) (M := M) α b r s
              (TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s S b
                  (chartBasisVecFiber (I := I) α i b)))‖ ^ 2)
      ((chartAt H α).source) := by
  refine continuousOn_finset_sum _ (fun i _ => ?_)
  have hcov : ContinuousOn
      (fun b : M =>
        chartRSTwistInv (I := I) (M := M) α b r s
          (TensorRSSpace.toModel
            (tensorCovDerivAt (I := I) (M := M) g r s S b
              (chartBasisVecFiber (I := I) α i b))))
      ((chartAt H α).source) :=
    (chartRSTwistInv_tensorCovDeriv_contMDiffOn' (I := I) (M := M)
      g r s S α i).continuousOn
  exact (hcov.norm).pow 2

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma cutoffCovNormSumFun_continuous
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M) :
    Continuous (cutoffCovNormSumFun (I := I) (M := M) g r s S α) := by
  classical
  set χ : C^∞⟮I, M; ℝ⟯ := chartKernelCutoff (I := I) (M := M) α with hχ_def
  set w : M → ℝ := fun b : M =>
    Real.sqrt
      (∑ i : Fin (Module.finrank ℝ E),
        ‖chartRSTwistInv (I := I) (M := M) α b r s
            (TensorRSSpace.toModel
              (tensorCovDerivAt (I := I) (M := M) g r s S b
                (chartBasisVecFiber (I := I) α i b)))‖ ^ 2) with hw_def
  have hfun_eq : cutoffCovNormSumFun (I := I) (M := M) g r s S α =
      fun b : M => ((χ : C^∞⟮I, M; ℝ⟯) : M → ℝ) b • w b := by
    funext b
    rw [cutoffCovNormSumFun]
    rfl
  rw [hfun_eq]
  refine continuous_of_tsupport (fun x hx => ?_)
  have hx_supp : x ∈ tsupport ((χ : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
    tsupport_smul_subset_left
      (f := fun b : M => ((χ : C^∞⟮I, M; ℝ⟯) : M → ℝ) b) (g := w) hx
  have hx_src : x ∈ (chartAt H α).source :=
    chartKernelCutoff_tsupport_subset_source (I := I) (M := M) α hx_supp
  have hχ_contAt : ContinuousAt ((χ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x :=
    (χ.contMDiff.continuous).continuousAt
  have hw_contOn : ContinuousOn w ((chartAt H α).source) := by
    rw [hw_def]
    exact (cutoffCovNormSqSum_continuousOn_chart_source (I := I) (M := M)
      g r s S α).sqrt
  have hw_contAt : ContinuousAt w x :=
    hw_contOn.continuousAt ((chartAt H α).open_source.mem_nhds hx_src)
  exact hχ_contAt.smul hw_contAt

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
lemma cutoffCovNormSumFun_measurable
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M) :
    Measurable (cutoffCovNormSumFun (I := I) (M := M) g r s S α) :=
  (cutoffCovNormSumFun_continuous (I := I) (M := M) g r s S α).measurable

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma chartBasePoint_mem_goodSet'
    (α : M) {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∈
      chartLeviCivitaGoodSet (I := I) α := by
  have hsrc : (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∈
      (chartAt H α).source :=
    symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) α hy
  rw [mem_chartLeviCivitaGoodSet_iff_mem_extChartAt_source (I := I) α,
    extChartAt_source]
  exact hsrc

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
lemma cutoffCovDerivComponent_le_chartPushedRaw
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (k : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (y : EuclN) :
    ‖cutoffCovDerivComponent (I := I) (M := M) g r s S α k Idx Jdx y‖ ≤
      (chartComponentProjectionUniformBound (E := E) r s •
        chartPushedRaw (I := I) (M := M) α
          (cutoffCovNormSumFun (I := I) (M := M) g r s S α)) y := by
  classical
  set C_proj : ℝ := chartComponentProjectionUniformBound (E := E) r s
    with hC_proj_def
  have hC_proj_nn : 0 ≤ C_proj :=
    chartComponentProjectionUniformBound_nonneg (E := E) r s
  by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
  · set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y)
      with hb_def
    have hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α :=
      chartBasePoint_mem_goodSet' (I := I) (M := M) α hy
    have hb_src : b ∈ (chartAt H α).source := by
      have := symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) α hy
      rwa [← hb_def] at this
    have hχ_nn : 0 ≤ ((chartKernelCutoff (I := I) (M := M) α
        : C^∞⟮I, M; ℝ⟯) : M → ℝ) b :=
      (chartKernelCutoff_mem_Icc (I := I) (M := M) α b).1
    have hcut_eval : chartPushedRaw (I := I) (M := M) α
        (⇑(chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯)) y =
          ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b := by
      rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α
        (⇑(chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯)) hy]
    have hcov_eval : chartPushedRaw (I := I) (M := M) α
        (cutoffCovNormSumFun (I := I) (M := M) g r s S α) y =
          cutoffCovNormSumFun (I := I) (M := M) g r s S α b := by
      rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α
        (cutoffCovNormSumFun (I := I) (M := M) g r s S α) hy]
    have hcomp_eq :
        tensorChartComponentProjection (E := E) r s Idx Jdx
            ((trivializationAt (TensorRSModel r s ℝ E)
                (fun z : M => TensorRSSpace r s I z) α).continuousLinearMapAt ℝ b
              (chartTensorRSCovariantDerivative (I := I) r s g α S.toSection
                (chartBasisVecFiber (I := I) α k) b)) =
          tensorChartComponentProjection (E := E) r s Idx Jdx
            (chartRSTwistInv (I := I) (M := M) α b r s
              (TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s S b
                  (chartBasisVecFiber (I := I) α k b)))) := by
      rw [← tensorCovDerivAt_eq_chartTensorRSCovariantDerivative (I := I) (M := M)
        g r s S α k hb_good]
      rw [triv_continuousLinearMapAt_eq_chartRSTwistInv_toModel (I := I) (M := M)
        r s α hb_src
        (tensorCovDerivAt (I := I) (M := M) g r s S b
          (chartBasisVecFiber (I := I) α k b))]
    set X : TensorRSModel r s ℝ E :=
      chartRSTwistInv (I := I) (M := M) α b r s
        (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g r s S b
            (chartBasisVecFiber (I := I) α k b))) with hX_def
    have h_proj_le :
        ‖tensorChartComponentProjection (E := E) r s Idx Jdx X‖ ≤
          C_proj * ‖X‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right
          (tensorChartComponentProjection_norm_le_uniform (E := E) r s Idx Jdx)
          (norm_nonneg _))
    have h_norm_le_sqrt :
        ‖X‖ ≤
          Real.sqrt
            (∑ i : Fin (Module.finrank ℝ E),
              ‖chartRSTwistInv (I := I) (M := M) α b r s
                  (TensorRSSpace.toModel
                    (tensorCovDerivAt (I := I) (M := M) g r s S b
                      (chartBasisVecFiber (I := I) α i b)))‖ ^ 2) := by
      have hsq_le :
          ‖X‖ ^ 2 ≤
            ∑ i : Fin (Module.finrank ℝ E),
              ‖chartRSTwistInv (I := I) (M := M) α b r s
                  (TensorRSSpace.toModel
                    (tensorCovDerivAt (I := I) (M := M) g r s S b
                      (chartBasisVecFiber (I := I) α i b)))‖ ^ 2 :=
        Finset.single_le_sum
          (f := fun i : Fin (Module.finrank ℝ E) =>
            ‖chartRSTwistInv (I := I) (M := M) α b r s
                (TensorRSSpace.toModel
                  (tensorCovDerivAt (I := I) (M := M) g r s S b
                    (chartBasisVecFiber (I := I) α i b)))‖ ^ 2)
          (fun i _ => sq_nonneg _) (Finset.mem_univ k)
      have hX_eq : ‖X‖ = Real.sqrt (‖X‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
      rw [hX_eq]
      exact Real.sqrt_le_sqrt hsq_le
    unfold cutoffCovDerivComponent
    rw [hcomp_eq, hcut_eval]
    have h_norm_prod :
        ‖((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
            tensorChartComponentProjection (E := E) r s Idx Jdx X‖ =
          ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
            ‖tensorChartComponentProjection (E := E) r s Idx Jdx X‖ := by
      rw [norm_mul, Real.norm_of_nonneg hχ_nn]
    have hRHS_eq :
        (C_proj •
          chartPushedRaw (I := I) (M := M) α
            (cutoffCovNormSumFun (I := I) (M := M) g r s S α)) y =
          C_proj *
            (((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯)
                : M → ℝ) b *
              Real.sqrt
                (∑ i : Fin (Module.finrank ℝ E),
                  ‖chartRSTwistInv (I := I) (M := M) α b r s
                      (TensorRSSpace.toModel
                        (tensorCovDerivAt (I := I) (M := M) g r s S b
                          (chartBasisVecFiber (I := I) α i b)))‖ ^ 2)) := by
      change C_proj * chartPushedRaw (I := I) (M := M) α
        (cutoffCovNormSumFun (I := I) (M := M) g r s S α) y = _
      rw [hcov_eval]
      rfl
    rw [h_norm_prod, hRHS_eq]
    set w : ℝ :=
      Real.sqrt
        (∑ i : Fin (Module.finrank ℝ E),
          ‖chartRSTwistInv (I := I) (M := M) α b r s
              (TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s S b
                  (chartBasisVecFiber (I := I) α i b)))‖ ^ 2) with hw_def
    have hw_nn : 0 ≤ w := Real.sqrt_nonneg _
    have h_proj_le_w :
        ‖tensorChartComponentProjection (E := E) r s Idx Jdx X‖ ≤
          C_proj * w :=
      h_proj_le.trans
        (mul_le_mul_of_nonneg_left h_norm_le_sqrt hC_proj_nn)
    calc ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
            ‖tensorChartComponentProjection (E := E) r s Idx Jdx X‖
        ≤ ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
            (C_proj * w) :=
          mul_le_mul_of_nonneg_left h_proj_le_w hχ_nn
      _ = C_proj *
            (((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯)
                : M → ℝ) b * w) := by
          ring
  · have hcov_zero : chartPushedRaw (I := I) (M := M) α
        (cutoffCovNormSumFun (I := I) (M := M) g r s S α) y = 0 :=
      chartPushedRaw_apply_of_notMem (I := I) (M := M) α
        (cutoffCovNormSumFun (I := I) (M := M) g r s S α) hy
    have hcomp_zero : cutoffCovDerivComponent (I := I) (M := M)
        g r s S α k Idx Jdx y = 0 := by
      unfold cutoffCovDerivComponent
      rw [chartPushedRaw_apply_of_notMem (I := I) (M := M) α
        (⇑(chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯)) hy,
        zero_mul]
    rw [hcomp_zero, norm_zero]
    change (0 : ℝ) ≤ C_proj * chartPushedRaw (I := I) (M := M) α
      (cutoffCovNormSumFun (I := I) (M := M) g r s S α) y
    rw [hcov_zero, mul_zero]

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
