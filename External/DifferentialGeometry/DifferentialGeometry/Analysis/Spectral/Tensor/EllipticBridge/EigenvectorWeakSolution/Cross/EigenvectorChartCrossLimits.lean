import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Component.EigenvectorChartComponentL2
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.AbstractChartPullCutoff
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovGradCrossBridge
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovGradL2


noncomputable section

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators Matrix
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Tensor.TensorRSRiemannian
open TensorRSNabla
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Analysis.Laplacian.MetricExtension hiding chartTargetEuclid
open DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [NeZero (Module.finrank ℝ E)] in
private lemma covGrad_toFun_eq_zero_off_tsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (w : SmoothCcTensor g r s) {x : M} (hx : x ∉ tsupport w.toFun) :
    (covGrad (I := I) (M := M) g r s w).toFun x = 0 := by
  have hcov_zero :
      tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)
          (fun y : M => w.toSection y) x = 0 := by
    apply ContinuousLinearMap.ext
    intro v
    rw [ContinuousLinearMap.zero_apply]
    exact tensorCovDerivAt_eq_zero_off_tsupport (I := I) (M := M) g r s w hx v
  rw [SmoothCcTensor.toFun_apply, covGrad_toSection_apply, hcov_zero, map_zero,
    TensorRSSpace.toModel_zero]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma scalarSmul_toFun_eq_zero_off_tsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (w : SmoothCcTensor g r s) {x : M}
    (hx : x ∉ tsupport ((ζ : C^∞⟮I, M; ℝ⟯) : M → ℝ)) :
    (scalarSmul (I := I) (M := M) g r s ζ w).toFun x = 0 := by
  have hζx : ((ζ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 0 :=
    image_eq_zero_of_notMem_tsupport hx
  rw [scalarSmul_toFun_apply, hζx, zero_smul]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma scalarSmul_tsupport_subset
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (w : SmoothCcTensor g r s) :
    tsupport (scalarSmul (I := I) (M := M) g r s ζ w).toFun ⊆
      tsupport ((ζ : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
  refine closure_minimal ?_ (isClosed_tsupport _)
  intro x hx
  rw [Function.mem_support] at hx
  by_contra hx_notin
  exact hx (scalarSmul_toFun_eq_zero_off_tsupport (I := I) (M := M) g r s ζ w
    hx_notin)

omit [NeZero (Module.finrank ℝ E)] in
private lemma prependCovGradSlot_tsupport_subset
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (S : SmoothCcTensor g r s) :
    tsupport (prependCovGradSlot (I := I) (M := M) g r s ζ S).toFun ⊆
      tsupport ((ζ : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
  refine closure_minimal ?_ (isClosed_tsupport _)
  intro x hx
  rw [Function.mem_support] at hx
  by_contra hx_notin
  refine hx ?_
  have hsub : (prependCovGradSlot (I := I) (M := M) g r s ζ S).toFun x =
      (covGrad (I := I) (M := M) g r s
          (scalarSmul (I := I) (M := M) g r s ζ S)).toFun x -
        (scalarSmul (I := I) (M := M) g r (s + 1) ζ
          (covGrad (I := I) (M := M) g r s S)).toFun x := by
    rw [prependCovGradSlot, SmoothCcTensor.toFun_sub]
    rfl
  rw [hsub]
  have hfst : (covGrad (I := I) (M := M) g r s
      (scalarSmul (I := I) (M := M) g r s ζ S)).toFun x = 0 :=
    covGrad_toFun_eq_zero_off_tsupport (I := I) (M := M) g r s
      (scalarSmul (I := I) (M := M) g r s ζ S)
      (fun hx_mem => hx_notin
        (scalarSmul_tsupport_subset (I := I) (M := M) g r s ζ S hx_mem))
  have hsnd : (scalarSmul (I := I) (M := M) g r (s + 1) ζ
      (covGrad (I := I) (M := M) g r s S)).toFun x = 0 :=
    scalarSmul_toFun_eq_zero_off_tsupport (I := I) (M := M) g r (s + 1) ζ
      (covGrad (I := I) (M := M) g r s S) hx_notin
  rw [hfst, hsnd, sub_zero]

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorCovDerivCrossLeft_integral_eq_inner
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (w : SmoothCcTensorH1 g r s)
    (S : SmoothCcTensor g r s) :
    ∫ x, tensorCovDerivCrossLeft (I := I) (M := M) g r s ζ w.toCcTensor S x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ⟪tensorCovGradL2 (I := I) (M := M) g r s w,
        ((prependCovGradSlot (I := I) (M := M) g r s ζ S :
          SmoothCcTensor g r (s + 1)) : TensorL2 r (s + 1) g)⟫_ℝ := by
  rw [tensorCovGradL2_inner_smooth (I := I) (M := M) g r s w
    (prependCovGradSlot (I := I) (M := M) g r s ζ S)]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
  intro x
  rw [tensorCovDerivCrossLeft_eq_tensorInnerPointwise_grad
    (I := I) (M := M) g r s ζ w.toCcTensor S x]
  rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorCovDerivCrossLeft_integral_eq_chartPull
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (w : SmoothCcTensorH1 g r s) (S : SmoothCcTensor g r s) :
    ∫ x, tensorCovDerivCrossLeft (I := I) (M := M) g r s
          (chartAtlasPOU I M α) w.toCcTensor S x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          (∑ P : CompIdx E r (s + 1), ∑ Q : CompIdx E r (s + 1),
            covChartMetricGram (I := I) (M := M) g r (s + 1) α P Q y *
              ((tensorL2ChartComponentCutoff (I := I) (M := M) g r (s + 1)
                  (tensorCovGradL2 (I := I) (M := M) g r s w) α P :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y *
              tensorComponentEuclid (I := I) (M := M) g r (s + 1)
                (prependCovGradSlot (I := I) (M := M) g r s
                  (chartAtlasPOU I M α) S) α Q y)
        ∂(volume : Measure EuclN) := by
  rw [tensorCovDerivCrossLeft_integral_eq_inner (I := I) (M := M) g r s
    (chartAtlasPOU I M α) w S]
  exact tensorL2Inner_cutoff_chartKernelSupported_pull (I := I) (M := M)
    g r (s + 1) α (tensorCovGradL2 (I := I) (M := M) g r s w)
    (prependCovGradSlot (I := I) (M := M) g r s (chartAtlasPOU I M α) S)
    (prependCovGradSlot_tsupport_subset (I := I) (M := M) g r s
      (chartAtlasPOU I M α) S)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma gramMatrixAt_inv_symm
    (g : SmoothRiemannianMetric I M) (x : M)
    (k l : Fin (Module.finrank ℝ E)) :
    (gramMatrixAt (I := I) (M := M) g x)⁻¹ k l =
      (gramMatrixAt (I := I) (M := M) g x)⁻¹ l k := by
  have hHerm := gramMatrixAt_inv_isHermitian (I := I) (M := M) g x
  have h := hHerm.apply l k
  rwa [star_trivial] at h

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorCovDerivCrossRight_eq_crossLeft
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (w S : SmoothCcTensor g r s) (x : M) :
    tensorCovDerivCrossRight (I := I) (M := M) g r s ζ w S x =
      tensorCovDerivCrossLeft (I := I) (M := M) g r s ζ S w x := by
  classical
  rw [tensorCovDerivCrossRight_def, tensorCovDerivCrossLeft_def]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [gramMatrixAt_inv_symm (I := I) (M := M) g x i j,
    tensorInnerPointwise_symm (I := I) (M := M) g r s x
      (w.toFun x)
      (TensorRSSpace.toModel
        (tensorCovDerivAt (I := I) (M := M) g r s S x ((chartModelBasis E) j)))]

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorCovDerivCrossRight_integral_eq_inner
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (w : SmoothCcTensorH1 g r s)
    (S : SmoothCcTensor g r s) :
    ∫ x, tensorCovDerivCrossRight (I := I) (M := M) g r s ζ w.toCcTensor S x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ⟪((covGrad (I := I) (M := M) g r s S : SmoothCcTensor g r (s + 1)) :
          TensorL2 r (s + 1) g),
        ((prependCovGradSlot (I := I) (M := M) g r s ζ w.toCcTensor :
          SmoothCcTensor g r (s + 1)) : TensorL2 r (s + 1) g)⟫_ℝ := by
  rw [UniformSpace.Completion.inner_coe,
    SmoothCcTensor.inner_def
      (covGrad (I := I) (M := M) g r s S)
      (prependCovGradSlot (I := I) (M := M) g r s ζ w.toCcTensor),
    tensorL2Inner]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
  intro x
  rw [tensorCovDerivCrossRight_eq_crossLeft (I := I) (M := M) g r s ζ
      w.toCcTensor S x,
    tensorCovDerivCrossLeft_eq_tensorInnerPointwise_grad (I := I) (M := M)
      g r s ζ S w.toCcTensor x]
  rfl

theorem tensorCovGradL2_eigenvectorSmoothApprox_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    Filter.Tendsto
      (fun n => tensorCovGradL2 (I := I) (M := M) g r s
        (eigenvectorSmoothApprox (I := I) (M := M) g r s i n))
      atTop
      (𝓝 (tensorCovGradL2Compl (I := I) (M := M) g r s
        (eigenvectorResolvent (I := I) (M := M) g r s i))) := by
  have h_clm :=
    ((tensorCovGradL2Compl (I := I) (M := M) g r s).continuous.tendsto _).comp
      (eigenvectorSmoothApprox_tendsto (I := I) (M := M) g r s i)
  refine h_clm.congr ?_
  intro n
  rw [Function.comp_apply,
    tensorCovGradL2Compl_smoothToTensorH1Compl (I := I) (M := M) g r s
      (eigenvectorSmoothApprox (I := I) (M := M) g r s i n)]

def crossLeftLimitComponent
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : CompIdx E r (s + 1)) :
    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) :=
  tensorL2ChartComponentCutoff (I := I) (M := M) g r (s + 1)
    (tensorCovGradL2Compl (I := I) (M := M) g r s
      (eigenvectorResolvent (I := I) (M := M) g r s i))
    α P

theorem crossLeftComponent_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : CompIdx E r (s + 1)) :
    Filter.Tendsto
      (fun n => tensorL2ChartComponentCutoff (I := I) (M := M) g r (s + 1)
        (tensorCovGradL2 (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M) g r s i n))
        α P)
      atTop
      (𝓝 (crossLeftLimitComponent (I := I) (M := M) g r s i α P)) := by
  have h_clm :=
    ((tensorL2ChartComponentCutoffCLM (I := I) (M := M) g r (s + 1)
        α P).continuous.tendsto _).comp
      (tensorCovGradL2_eigenvectorSmoothApprox_tendsto
        (I := I) (M := M) g r s i)
  simp only [Function.comp_def, tensorL2ChartComponentCutoffCLM_apply] at h_clm
  exact h_clm

theorem tensorCovDerivCrossLeft_integral_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (S : SmoothCcTensor g r s) :
    Filter.Tendsto
      (fun n => ∫ x, tensorCovDerivCrossLeft (I := I) (M := M) g r s
          (chartAtlasPOU I M α)
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor
          S x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g))
      atTop
      (𝓝 (⟪tensorCovGradL2Compl (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s i),
          ((prependCovGradSlot (I := I) (M := M) g r s (chartAtlasPOU I M α) S :
            SmoothCcTensor g r (s + 1)) : TensorL2 r (s + 1) g)⟫_ℝ)) := by
  have h_clm :=
    ((innerSL ℝ
        ((prependCovGradSlot (I := I) (M := M) g r s (chartAtlasPOU I M α) S :
          SmoothCcTensor g r (s + 1)) :
          TensorL2 r (s + 1) g)).continuous.tendsto _).comp
      (tensorCovGradL2_eigenvectorSmoothApprox_tendsto
        (I := I) (M := M) g r s i)
  simp only [Function.comp_def, innerSL_apply_apply] at h_clm
  rw [real_inner_comm]
  refine h_clm.congr ?_
  intro n
  rw [tensorCovDerivCrossLeft_integral_eq_inner (I := I) (M := M) g r s
    (chartAtlasPOU I M α)
    (eigenvectorSmoothApprox (I := I) (M := M) g r s i n) S,
    real_inner_comm]

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
