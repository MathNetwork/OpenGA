import DifferentialGeometry.Analysis.Elliptic.TensorRegularity.CovDeriv.ChartForm
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChristoffelCorrection.CovL2BoundFromH1
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChartComponent.ComponentL2BoundUniform
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.ChartGeometry.GoodSetMeasure
import DifferentialGeometry.Analysis.Sobolev.Manifold.MeasureBridgeUniform
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul


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

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma chartBasePoint_mem_goodSet
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

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma tensorRS_baseSet_eq_chart_source (α : M) (r s : ℕ) :
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

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma tangent_baseSet_eq_chart_source (α : M) :
    (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source :=
  rfl

omit [CompleteSpace E] in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma chartRSTwistInv_tensorCovDeriv_contMDiffOn
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
  rw [tangent_baseSet_eq_chart_source (I := I) (M := M) α] at htriv
  refine htriv.congr (fun b hb => ?_)
  rw [← triv_continuousLinearMapAt_eq_chartRSTwistInv_toModel (I := I) (M := M)
    r s α hb
    (tensorCovDerivAt (I := I) (M := M) g r s S b
      (chartBasisVecFiber (I := I) α i b))]
  have hb_base : b ∈ (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).baseSet := by
    rw [tensorRS_baseSet_eq_chart_source (I := I) (M := M) α r s]
    exact hb
  change (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).linearMapAt ℝ b
      (tensorCovDerivAt (I := I) (M := M) g r s S b
        (chartBasisVecFiber (I := I) α i b)) = _
  rw [Bundle.Trivialization.linearMapAt_apply, if_pos hb_base]

private noncomputable def covNormSumFun
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M) : M → ℝ :=
  fun b : M =>
    ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
      Real.sqrt
        (∑ i : Fin (Module.finrank ℝ E),
          ‖chartRSTwistInv (I := I) (M := M) α b r s
              (TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s S b
                  (chartBasisVecFiber (I := I) α i b)))‖ ^ 2)

omit [CompleteSpace E] in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma covNormSqSum_continuousOn_chart_source
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
    (chartRSTwistInv_tensorCovDeriv_contMDiffOn (I := I) (M := M)
      g r s S α i).continuousOn
  exact (hcov.norm).pow 2

omit [CompleteSpace E] in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma covNormSumFun_continuous
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M) :
    Continuous (covNormSumFun (I := I) (M := M) g r s S α) := by
  classical
  set ρ : C^∞⟮I, M; ℝ⟯ := chartAtlasPOU I M α with hρ_def
  set w : M → ℝ := fun b : M =>
    Real.sqrt
      (∑ i : Fin (Module.finrank ℝ E),
        ‖chartRSTwistInv (I := I) (M := M) α b r s
            (TensorRSSpace.toModel
              (tensorCovDerivAt (I := I) (M := M) g r s S b
                (chartBasisVecFiber (I := I) α i b)))‖ ^ 2) with hw_def
  have hfun_eq : covNormSumFun (I := I) (M := M) g r s S α =
      fun b : M => ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) b • w b := by
    funext b
    rw [covNormSumFun]
    rfl
  rw [hfun_eq]
  refine continuous_of_tsupport (fun x hx => ?_)
  have hx_supp : x ∈ tsupport ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
    tsupport_smul_subset_left
      (f := fun b : M => ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) b) (g := w) hx
  have hx_src : x ∈ (chartAt H α).source :=
    chartAtlasPOU_isSubordinate I M α hx_supp
  have hρ_contAt : ContinuousAt ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x :=
    (ρ.contMDiff.continuous).continuousAt
  have hw_contOn : ContinuousOn w ((chartAt H α).source) := by
    rw [hw_def]
    exact (covNormSqSum_continuousOn_chart_source (I := I) (M := M)
      g r s S α).sqrt
  have hw_contAt : ContinuousAt w x :=
    hw_contOn.continuousAt ((chartAt H α).open_source.mem_nhds hx_src)
  exact hρ_contAt.smul hw_contAt

omit [CompleteSpace E] in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma covNormSumFun_measurable
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M) :
    Measurable (covNormSumFun (I := I) (M := M) g r s S α) :=
  (covNormSumFun_continuous (I := I) (M := M) g r s S α).measurable

omit [CompleteSpace E] [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma covNormSumFun_tsupport_subset
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M) :
    tsupport (covNormSumFun (I := I) (M := M) g r s S α) ⊆
      tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
  classical
  have hfun_eq : covNormSumFun (I := I) (M := M) g r s S α =
      fun b : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b •
          Real.sqrt
            (∑ i : Fin (Module.finrank ℝ E),
              ‖chartRSTwistInv (I := I) (M := M) α b r s
                  (TensorRSSpace.toModel
                    (tensorCovDerivAt (I := I) (M := M) g r s S b
                      (chartBasisVecFiber (I := I) α i b)))‖ ^ 2) := by
    funext b
    rw [covNormSumFun]
    rfl
  rw [hfun_eq]
  exact tsupport_smul_subset_left
    (f := fun b : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b)
    (g := fun b : M =>
      Real.sqrt
        (∑ i : Fin (Module.finrank ℝ E),
          ‖chartRSTwistInv (I := I) (M := M) α b r s
              (TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s S b
                  (chartBasisVecFiber (I := I) α i b)))‖ ^ 2))

omit [CompactSpace M] in
omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma pou_covDerivComponent_le_chartPushedRaw
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (m : Fin (Module.finrank ℝ E)) (y : EuclN) :
    ‖chartPushedRaw (I := I) (M := M) α
          (⇑(chartAtlasPOU I M α)) y *
        tensorChartComponentProjection (E := E) r s Idx Jdx
          ((trivializationAt (TensorRSModel r s ℝ E)
              (fun z : M => TensorRSSpace r s I z) α).continuousLinearMapAt ℝ
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
            (chartTensorRSCovariantDerivative (I := I) r s g α S.toSection
              (chartBasisVecFiber (I := I) α m)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))))‖ ≤
      (chartComponentProjectionUniformBound (E := E) r s •
        chartPushedRaw (I := I) (M := M) α
          (covNormSumFun (I := I) (M := M) g r s S α)) y := by
  classical
  set C_proj : ℝ := chartComponentProjectionUniformBound (E := E) r s
    with hC_proj_def
  have hC_proj_nn : 0 ≤ C_proj :=
    chartComponentProjectionUniformBound_nonneg (E := E) r s
  by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
  · set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y)
      with hb_def
    have hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α :=
      chartBasePoint_mem_goodSet (I := I) (M := M) α hy
    have hb_src : b ∈ (chartAt H α).source := by
      have := symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) α hy
      rwa [← hb_def] at this
    have hρ_nn : 0 ≤ ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b :=
      (chartAtlasPOU I M).nonneg α b
    have hρ_le_one : ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b ≤ 1 :=
      (chartAtlasPOU I M).le_one α b
    have hpou_eval : chartPushedRaw (I := I) (M := M) α
        (⇑(chartAtlasPOU I M α)) y =
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b := by
      rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α
        (⇑(chartAtlasPOU I M α)) hy]
    have hcov_eval : chartPushedRaw (I := I) (M := M) α
        (covNormSumFun (I := I) (M := M) g r s S α) y =
          covNormSumFun (I := I) (M := M) g r s S α b := by
      rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α
        (covNormSumFun (I := I) (M := M) g r s S α) hy]
    have hcomp_eq :
        tensorChartComponentProjection (E := E) r s Idx Jdx
            ((trivializationAt (TensorRSModel r s ℝ E)
                (fun z : M => TensorRSSpace r s I z) α).continuousLinearMapAt ℝ b
              (chartTensorRSCovariantDerivative (I := I) r s g α S.toSection
                (chartBasisVecFiber (I := I) α m) b)) =
          tensorChartComponentProjection (E := E) r s Idx Jdx
            (chartRSTwistInv (I := I) (M := M) α b r s
              (TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s S b
                  (chartBasisVecFiber (I := I) α m b)))) := by
      rw [← tensorCovDerivAt_eq_chartTensorRSCovariantDerivative (I := I) (M := M)
        g r s S α m hb_good]
      rw [triv_continuousLinearMapAt_eq_chartRSTwistInv_toModel (I := I) (M := M)
        r s α hb_src
        (tensorCovDerivAt (I := I) (M := M) g r s S b
          (chartBasisVecFiber (I := I) α m b))]
    set X : TensorRSModel r s ℝ E :=
      chartRSTwistInv (I := I) (M := M) α b r s
        (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g r s S b
            (chartBasisVecFiber (I := I) α m b))) with hX_def
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
          (fun i _ => sq_nonneg _) (Finset.mem_univ m)
      have hX_eq : ‖X‖ = Real.sqrt (‖X‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
      rw [hX_eq]
      exact Real.sqrt_le_sqrt hsq_le
    rw [hcomp_eq, hpou_eval]
    have h_norm_prod :
        ‖((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
            tensorChartComponentProjection (E := E) r s Idx Jdx X‖ =
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
            ‖tensorChartComponentProjection (E := E) r s Idx Jdx X‖ := by
      rw [norm_mul, Real.norm_of_nonneg hρ_nn]
    have hRHS_eq :
        (C_proj •
          chartPushedRaw (I := I) (M := M) α
            (covNormSumFun (I := I) (M := M) g r s S α)) y =
          C_proj *
            (((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
              Real.sqrt
                (∑ i : Fin (Module.finrank ℝ E),
                  ‖chartRSTwistInv (I := I) (M := M) α b r s
                      (TensorRSSpace.toModel
                        (tensorCovDerivAt (I := I) (M := M) g r s S b
                          (chartBasisVecFiber (I := I) α i b)))‖ ^ 2)) := by
      change C_proj * chartPushedRaw (I := I) (M := M) α
        (covNormSumFun (I := I) (M := M) g r s S α) y = _
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
    calc ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
            ‖tensorChartComponentProjection (E := E) r s Idx Jdx X‖
        ≤ ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
            (C_proj * w) :=
          mul_le_mul_of_nonneg_left h_proj_le_w hρ_nn
      _ = C_proj *
            (((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b * w) := by
          ring
  · have hpou_zero : chartPushedRaw (I := I) (M := M) α
        (⇑(chartAtlasPOU I M α)) y = 0 :=
      chartPushedRaw_apply_of_notMem (I := I) (M := M) α
        (⇑(chartAtlasPOU I M α)) hy
    have hcov_zero : chartPushedRaw (I := I) (M := M) α
        (covNormSumFun (I := I) (M := M) g r s S α) y = 0 :=
      chartPushedRaw_apply_of_notMem (I := I) (M := M) α
        (covNormSumFun (I := I) (M := M) g r s S α) hy
    rw [hpou_zero, zero_mul, norm_zero]
    change (0 : ℝ) ≤ C_proj * chartPushedRaw (I := I) (M := M) α
      (covNormSumFun (I := I) (M := M) g r s S α) y
    rw [hcov_zero, mul_zero]

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma exists_const_eLpNorm_pou_covDerivComponent_le_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (S : SmoothCcTensorH1 g r s)
      (Idx : Fin r → Fin (Module.finrank ℝ E))
      (Jdx : Fin s → Fin (Module.finrank ℝ E))
      (m : Fin (Module.finrank ℝ E)),
      eLpNorm
        (fun y : EuclN =>
          chartPushedRaw (I := I) (M := M) α (⇑(chartAtlasPOU I M α)) y *
            tensorChartComponentProjection (E := E) r s Idx Jdx
              ((trivializationAt (TensorRSModel r s ℝ E)
                  (fun z : M => TensorRSSpace r s I z) α).continuousLinearMapAt ℝ
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
                (chartTensorRSCovariantDerivative (I := I) r s g α
                  S.toCcTensor.toSection
                  (chartBasisVecFiber (I := I) α m)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))))
        2 ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞) := by
  classical
  set C_proj : ℝ := chartComponentProjectionUniformBound (E := E) r s
    with hC_proj_def
  have hC_proj_nn : 0 ≤ C_proj :=
    chartComponentProjectionUniformBound_nonneg (E := E) r s
  set Kα : Set M :=
    tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) with hKα_def
  have hKα_compact : IsCompact Kα := (isClosed_tsupport _).isCompact
  have hKα_sub : Kα ⊆ (chartAt H α).source :=
    chartAtlasPOU_isSubordinate I M α
  have hp_one : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have hp_top : (2 : ℝ≥0∞) ≠ ⊤ := by decide
  obtain ⟨C_bridge, hC_bridge_pos, hC_bridge⟩ :=
    eLpNorm_chartPushedRaw_le_const_mul_eLpNorm_riemannianMeasure_uniform_of_subset
      (I := I) (M := M) g α hKα_compact hKα_sub hp_one hp_top
  obtain ⟨C_cov, hC_cov_nn, hC_cov⟩ :=
    exists_eLpNorm_chartPou_mul_sqrt_sum_chartRSTwistInv_cov_norm_sq_le_const_mul_h1Norm
      (I := I) (M := M) g r s α
  refine ⟨C_proj * (C_bridge * C_cov),
    mul_nonneg hC_proj_nn (mul_nonneg hC_bridge_pos.le hC_cov_nn), ?_⟩
  intro S Idx Jdx m
  set f : EuclN → ℝ := fun y : EuclN =>
    chartPushedRaw (I := I) (M := M) α (⇑(chartAtlasPOU I M α)) y *
      tensorChartComponentProjection (E := E) r s Idx Jdx
        ((trivializationAt (TensorRSModel r s ℝ E)
            (fun z : M => TensorRSSpace r s I z) α).continuousLinearMapAt ℝ
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
          (chartTensorRSCovariantDerivative (I := I) r s g α
            S.toCcTensor.toSection
            (chartBasisVecFiber (I := I) α m)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))))
    with hf_def
  set v : M → ℝ := covNormSumFun (I := I) (M := M) g r s S.toCcTensor α
    with hv_def
  set μ : Measure EuclN :=
    (volume : Measure EuclN).restrict (chartTargetEuclid (I := I) (M := M) α)
    with hμ_def
  have h_ptwise : ∀ y : EuclN,
      ‖f y‖ ≤ (C_proj • chartPushedRaw (I := I) (M := M) α v) y := by
    intro y
    rw [hf_def, hv_def, hC_proj_def]
    exact pou_covDerivComponent_le_chartPushedRaw (I := I) (M := M)
      g r s S.toCcTensor α Idx Jdx m y
  have h_mono :
      eLpNorm f 2 μ ≤
        eLpNorm (C_proj • chartPushedRaw (I := I) (M := M) α v) 2 μ :=
    eLpNorm_mono_real h_ptwise
  have h_smul :
      eLpNorm (C_proj • chartPushedRaw (I := I) (M := M) α v) 2 μ =
        ‖C_proj‖ₑ * eLpNorm (chartPushedRaw (I := I) (M := M) α v) 2 μ :=
    eLpNorm_const_smul C_proj (chartPushedRaw (I := I) (M := M) α v) 2 μ
  have hC_proj_enorm : ‖C_proj‖ₑ = ENNReal.ofReal C_proj := by
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg hC_proj_nn]
  have hv_meas : Measurable v :=
    covNormSumFun_measurable (I := I) (M := M) g r s S.toCcTensor α
  have hv_supp : tsupport v ⊆ Kα :=
    covNormSumFun_tsupport_subset (I := I) (M := M) g r s S.toCcTensor α
  have h_bridge :
      eLpNorm (chartPushedRaw (I := I) (M := M) α v) 2 μ ≤
        ENNReal.ofReal C_bridge *
          eLpNorm v 2
            (riemannianMeasure (I := I) g (chartAtlasPOU I M)) :=
    hC_bridge hv_meas hv_supp
  have h_meas_eq :
      riemannianMeasure (I := I) g (chartAtlasPOU I M) =
        riemannianVolumeMeasure (I := I) (M := M) g := rfl
  rw [h_meas_eq] at h_bridge
  have hv_eq : v = fun b : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
        Real.sqrt
          (∑ i : Fin (Module.finrank ℝ E),
            ‖chartRSTwistInv (I := I) (M := M) α b r s
                (TensorRSSpace.toModel
                  (tensorCovDerivAt (I := I) (M := M) g r s
                    S.toCcTensor b
                    (chartBasisVecFiber (I := I) α i b)))‖ ^ 2) := by
    rw [hv_def]
    funext b
    rw [covNormSumFun]
  have h_cov :
      eLpNorm v 2 (riemannianVolumeMeasure (I := I) (M := M) g) ≤
        ENNReal.ofReal C_cov * (‖S‖₊ : ℝ≥0∞) := by
    rw [hv_eq]
    exact hC_cov S
  calc eLpNorm f 2 μ
      ≤ eLpNorm (C_proj • chartPushedRaw (I := I) (M := M) α v) 2 μ := h_mono
    _ = ‖C_proj‖ₑ * eLpNorm (chartPushedRaw (I := I) (M := M) α v) 2 μ :=
        h_smul
    _ = ENNReal.ofReal C_proj *
          eLpNorm (chartPushedRaw (I := I) (M := M) α v) 2 μ := by
        rw [hC_proj_enorm]
    _ ≤ ENNReal.ofReal C_proj *
          (ENNReal.ofReal C_bridge *
            eLpNorm v 2 (riemannianVolumeMeasure (I := I) (M := M) g)) := by
        exact mul_le_mul_of_nonneg_left h_bridge (by positivity)
    _ ≤ ENNReal.ofReal C_proj *
          (ENNReal.ofReal C_bridge *
            (ENNReal.ofReal C_cov * (‖S‖₊ : ℝ≥0∞))) := by
        gcongr
    _ = ENNReal.ofReal (C_proj * (C_bridge * C_cov)) * (‖S‖₊ : ℝ≥0∞) := by
        rw [ENNReal.ofReal_mul hC_proj_nn,
          ENNReal.ofReal_mul hC_bridge_pos.le]
        ring

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem exists_const_sum_eLpNorm_pou_covDerivComponent_le_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (S : SmoothCcTensorH1 g r s)
      (Idx : Fin r → Fin (Module.finrank ℝ E))
      (Jdx : Fin s → Fin (Module.finrank ℝ E)),
      ∑ m : Fin (Module.finrank ℝ E),
        eLpNorm
          (fun y : EuclN =>
            chartPushedRaw (I := I) (M := M) α (⇑(chartAtlasPOU I M α)) y *
              tensorChartComponentProjection (E := E) r s Idx Jdx
                ((trivializationAt (TensorRSModel r s ℝ E)
                    (fun z : M => TensorRSSpace r s I z) α).continuousLinearMapAt ℝ
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
                  (chartTensorRSCovariantDerivative (I := I) r s g α
                    S.toCcTensor.toSection
                    (chartBasisVecFiber (I := I) α m)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))))
          2 ((volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞) := by
  classical
  obtain ⟨C₀, hC₀_nn, hC₀⟩ :=
    exists_const_eLpNorm_pou_covDerivComponent_le_uniform
      (I := I) (M := M) g r s α
  refine ⟨(Module.finrank ℝ E : ℝ) * C₀,
    mul_nonneg (Nat.cast_nonneg _) hC₀_nn, ?_⟩
  intro S Idx Jdx
  refine (Finset.sum_le_sum (fun m _ => hC₀ S Idx Jdx m)).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [show ENNReal.ofReal ((Module.finrank ℝ E : ℝ) * C₀) =
        (Module.finrank ℝ E : ℝ≥0∞) * ENNReal.ofReal C₀ by
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]]
  rw [mul_assoc]

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
