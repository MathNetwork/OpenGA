import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciDifferenceMeanValue
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RealizedFamChartRicciDeriv
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RealizedFamLinearizedChristoffel
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciSecondOrderPart
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciLinearizationArmFields
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciLinearizationConnDiffCoefficients
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciLinearizationConnDiffUniformBounds
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciThreeArmCorrectionFieldTameEnvelope
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.CovGrad.SecondCovGradChartHessian
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.SmoothParametricCoeffIntegral
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceJetTower
import DifferentialGeometry.Geometry.Flow.DeTurckVFChartCoord
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.FiberNormSubadditivity
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingCm
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.ConvexPerturbationPointwiseC2
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.InverseMetricPerturbationFibreBound
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RealizedFamCurvatureJetBound
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.RealizeMetricChartGramDifference

set_option linter.style.multiGoal false


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle MeasureTheory intervalIntegral
open scoped Manifold Topology ContDiff BigOperators Matrix Interval

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M] in
theorem unitModel_basisChart_eq_tensorChartComponentRaw (g : SmoothRiemannianMetric I M)
    (s : ℕ) (W : SmoothCcTensor g 0 s) (x : M)
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    unitModel (I := I) (M := M) g s W x (fun k => chartModelBasis E (Jdx k)) =
      tensorChartComponentRaw (I := I) (M := M) g 0 s W x ![] Jdx x := by
  rw [tensorChartComponentRaw_def, tensorChartComponentProjection_apply]
  unfold tensorTrivProj
  rw [DifferentialGeometry.Tensor.tensorRS_trivAt_continuousLinearMapAt_apply_eq_self_on_locality
        (I := I) (M := M) 0 s x (b := x) rfl (mem_chart_source H x)
        (W.toSection x) (dualCoordinateProductMultilinearMap (E := E) 0 ![])]
  unfold unitModel
  congr 2

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M] in
theorem unitModel_basisChart_eq_tensorChartComponent (g : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g 0 2) (x : M) (k i : Fin (Module.finrank ℝ E)) :
    unitModel (I := I) (M := M) g 2 W x ![chartModelBasis E k, chartModelBasis E i] =
      tensorChartComponentRaw (I := I) (M := M) g 0 2 W x ![] ![k, i] x := by
  have h := unitModel_basisChart_eq_tensorChartComponentRaw (I := I) (M := M) g 2 W x ![k, i]
  have hfun : (fun j : Fin 2 => chartModelBasis E (![k, i] j)) =
      ![chartModelBasis E k, chartModelBasis E i] := by
    funext j; fin_cases j <;> rfl
  rwa [hfun] at h

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem cometricLmodel_covectorOfCLM_cDualBasis_eq_chartBasis_sum
    (g₁ : SmoothRiemannianMetric I M) (x : M) (k : Fin (Module.finrank ℝ E)) :
    cometricLmodel (I := I) g₁ x (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
        ((chartModelBasis E).cDualBasis k)) =
      ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k l • (chartModelBasis E l : TangentSpace I x) := by
  classical
  have hxbase : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x
  have hself : ∀ t : Fin (Module.finrank ℝ E),
      chartBasisVecFiber (I := I) x t x = chartModelBasis E t := fun t =>
    chartBasisVecFiber_self (I := I) x t
  apply DifferentialGeometry.Integral.DivergenceTheorem.metricFlatLinear_injective (I := I) g₁ x
  ext u
  change g₁.inner x (cometricLmodel (I := I) g₁ x
      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E) ((chartModelBasis E).cDualBasis k))) u =
    g₁.inner x (∑ l : Fin (Module.finrank ℝ E),
      chartInvGramMatrix (I := I) g₁ x x k l • (chartModelBasis E l : TangentSpace I x)) u
  rw [cometricLmodel_covectorOfCLM_inner (I := I) g₁ x ((chartModelBasis E).cDualBasis k) u]
  have hu : u = ∑ m : Fin (Module.finrank ℝ E),
      ((chartModelBasis E).repr
          ((trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ x u)) m •
        chartBasisVecFiber (I := I) x m x :=
    chartBasisVecFiber_recompose (I := I) x hxbase u
  set c : Fin (Module.finrank ℝ E) → ℝ := fun m =>
    ((chartModelBasis E).repr
        ((trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ x u)) m with hc_def
  have hRHS_inner :
      g₁.inner x (∑ l : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g₁ x x k l • (chartModelBasis E l : TangentSpace I x)) u =
        ∑ m : Fin (Module.finrank ℝ E),
          c m * (if k = m then (1 : ℝ) else 0) := by
    rw [map_sum, ContinuousLinearMap.sum_apply]
    rw [show ∑ l : Fin (Module.finrank ℝ E),
            (g₁.inner x (chartInvGramMatrix (I := I) g₁ x x k l •
                (chartModelBasis E l : TangentSpace I x))) u =
          ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g₁ x x k l *
              g₁.inner x (chartModelBasis E l : TangentSpace I x) u from ?_]
    swap
    · refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [show ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g₁ x x k l *
              g₁.inner x (chartModelBasis E l : TangentSpace I x) u =
          ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g₁ x x k l *
              g₁.inner x (chartModelBasis E l : TangentSpace I x)
                (∑ m : Fin (Module.finrank ℝ E), c m • chartBasisVecFiber (I := I) x m x) from ?_]
    swap
    · refine Finset.sum_congr rfl (fun l _ => ?_)
      refine congrArg (fun t : TangentSpace I x => chartInvGramMatrix (I := I) g₁ x x k l *
        g₁.inner x (chartModelBasis E l : TangentSpace I x) t) ?_
      exact hu
    rw [show ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g₁ x x k l *
              g₁.inner x (chartModelBasis E l : TangentSpace I x)
                (∑ m : Fin (Module.finrank ℝ E), c m • chartBasisVecFiber (I := I) x m x) =
          ∑ l : Fin (Module.finrank ℝ E),
            (∑ m : Fin (Module.finrank ℝ E),
              chartInvGramMatrix (I := I) g₁ x x k l * (c m *
                g₁.inner x (chartModelBasis E l : TangentSpace I x)
                  (chartBasisVecFiber (I := I) x m x))) from ?_]
    swap
    · refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [map_smul, smul_eq_mul]
    rw [Finset.sum_comm]
    rw [show ∑ m : Fin (Module.finrank ℝ E),
            (∑ l : Fin (Module.finrank ℝ E),
              chartInvGramMatrix (I := I) g₁ x x k l * (c m *
                g₁.inner x (chartModelBasis E l : TangentSpace I x)
                  (chartBasisVecFiber (I := I) x m x))) =
          ∑ m : Fin (Module.finrank ℝ E), c m *
            (∑ l : Fin (Module.finrank ℝ E),
              chartInvGramMatrix (I := I) g₁ x x k l *
                chartGramMatrix (I := I) g₁ x x l m) from ?_]
    swap
    · refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [show g₁.inner x (chartModelBasis E l : TangentSpace I x)
              (chartBasisVecFiber (I := I) x m x) =
            chartGramMatrix (I := I) g₁ x x l m from ?_]
      · ring
      · rw [show (chartModelBasis E l : TangentSpace I x) =
            chartBasisVecFiber (I := I) x l x from (hself l).symm]
        rw [g_inner_eq_chartGramMatrix_basis (I := I) g₁ x x l m]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    refine congrArg (fun t : ℝ => c m * t) ?_
    have hkron : (∑ l : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g₁ x x k l *
            chartGramMatrix (I := I) g₁ x x l m) =
        (chartInvGramMatrix (I := I) g₁ x x * chartGramMatrix (I := I) g₁ x x) k m := by
      rw [Matrix.mul_apply]
    rw [hkron, chartInvGramMatrix_mul_chartGramMatrix (I := I) g₁ x hxbase, Matrix.one_apply]
  rw [hRHS_inner]
  rw [show (chartModelBasis E).cDualBasis k (u : E) =
        ∑ m : Fin (Module.finrank ℝ E), c m *
          (chartModelBasis E).cDualBasis k (chartBasisVecFiber (I := I) x m x : E) from ?_]
  · refine Finset.sum_congr rfl (fun m _ => ?_)
    refine congrArg (fun t : ℝ => c m * t) ?_
    rw [show (chartBasisVecFiber (I := I) x m x : E) = (chartModelBasis E m : E) from
        congrArg (fun v : TangentSpace I x => (v : E)) (hself m)]
    rw [Module.Basis.cDualBasis_apply_self (chartModelBasis E) k m]
  · conv_lhs => rw [show (u : E) = ((∑ m : Fin (Module.finrank ℝ E),
          c m • chartBasisVecFiber (I := I) x m x : TangentSpace I x) : E) from
        congrArg (fun v : TangentSpace I x => (v : E)) hu]
    rw [show ((∑ m : Fin (Module.finrank ℝ E),
            c m • chartBasisVecFiber (I := I) x m x : TangentSpace I x) : E) =
          ∑ m : Fin (Module.finrank ℝ E),
            c m • (chartBasisVecFiber (I := I) x m x : E) from ?_]
    · rw [map_sum]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [map_smul, smul_eq_mul]
    · rfl

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem iteratedCovGrad2_chartComponent_readout (g₀ : SmoothRiemannianMetric I M)
    (h : SmoothCcTensor g₀ 0 2) (x : M)
    (Jdx : Fin (2 + 2) → Fin (Module.finrank ℝ E)) :
    tensorChartComponentRaw (I := I) (M := M) g₀ 0 (2 + 2)
        (iteratedCovGrad (I := I) g₀ 0 2 2 h) x ![] Jdx
        ((extChartAt I x).symm
          ((toEuclidean (E := E)).symm (toEuclidean (E := E) (extChartAt I x x)))) =
      euclidPartial (E := E) (Jdx 0)
          (fun y' =>
            euclidPartial (E := E) ((Matrix.vecTail Jdx) 0)
                (chartPushedRaw I x (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2
                  h x ![] (Matrix.vecTail (Matrix.vecTail Jdx)))) y'
              + covDerivLowerOrderTerm (I := I) (M := M) g₀ 0 2 h x
                  ((Matrix.vecTail Jdx) 0) ![]
                  (Matrix.vecTail (Matrix.vecTail Jdx)) y')
          (toEuclidean (E := E) (extChartAt I x x))
        + covDerivLowerOrderTerm (I := I) (M := M) g₀ 0 3
            (covGrad (I := I) (M := M) g₀ 0 2 h) x (Jdx 0) ![]
            (Matrix.vecTail Jdx) (toEuclidean (E := E) (extChartAt I x x)) := by
  have hmemsrc : x ∈ (chartAt H x).source := mem_chart_source H x
  have hy : toEuclidean (E := E) (extChartAt I x x) ∈
      chartTargetEuclid (I := I) (M := M) x :=
    toEuclidean_extChartAt_mem_chartTargetEuclid (I := I) (M := M) x hmemsrc
  exact chartCovariantSecondGrad_chartHessian_sub_correction (I := I) (M := M) g₀ h x
    ![] Jdx hy

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma euclidPartial_add_local
    (l : Fin (Module.finrank ℝ E))
    {f h : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ}
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hf : DifferentiableAt ℝ f y) (hh : DifferentiableAt ℝ h y) :
    euclidPartial (E := E) l (fun z => f z + h z) y =
      euclidPartial (E := E) l f y + euclidPartial (E := E) l h y := by
  rw [euclidPartial_def, euclidPartial_def, euclidPartial_def, fderiv_fun_add hf hh,
    ContinuousLinearMap.add_apply]

noncomputable def arm2ReadoutCovDerivPair (g₀ : SmoothRiemannianMetric I M)
    (h : SmoothCcTensor g₀ 0 2) (x : M)
    (Jdx : Fin (2 + 2) → Fin (Module.finrank ℝ E)) : ℝ :=
  euclidPartial (E := E) (Jdx 0)
      (fun y' => covDerivLowerOrderTerm (I := I) (M := M) g₀ 0 2 h x
        ((Matrix.vecTail Jdx) 0) ![]
        (Matrix.vecTail (Matrix.vecTail Jdx)) y')
      (toEuclidean (E := E) (extChartAt I x x))
    + covDerivLowerOrderTerm (I := I) (M := M) g₀ 0 3
        (covGrad (I := I) (M := M) g₀ 0 2 h) x (Jdx 0) ![]
        (Matrix.vecTail Jdx) (toEuclidean (E := E) (extChartAt I x x))

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem iteratedCovGrad1_chartComponent_readout (g₀ : SmoothRiemannianMetric I M)
    (h : SmoothCcTensor g₀ 0 2) (x : M)
    (Jdx : Fin (2 + 1) → Fin (Module.finrank ℝ E)) :
    tensorChartComponentRaw (I := I) (M := M) g₀ 0 (2 + 1)
        (iteratedCovGrad (I := I) g₀ 0 2 1 h) x ![] Jdx
        ((extChartAt I x).symm
          ((toEuclidean (E := E)).symm (toEuclidean (E := E) (extChartAt I x x)))) =
      euclidPartial (E := E) (Jdx 0)
          (chartPushedRaw I x (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2
            h x ![] (Matrix.vecTail Jdx)))
          (toEuclidean (E := E) (extChartAt I x x))
        + covDerivLowerOrderTerm (I := I) (M := M) g₀ 0 2 h x
            (Jdx 0) ![] (Matrix.vecTail Jdx)
            (toEuclidean (E := E) (extChartAt I x x)) := by
  have hmemsrc : x ∈ (chartAt H x).source := mem_chart_source H x
  have hy : toEuclidean (E := E) (extChartAt I x x) ∈
      chartTargetEuclid (I := I) (M := M) x :=
    toEuclidean_extChartAt_mem_chartTargetEuclid (I := I) (M := M) x hmemsrc
  have hcg : iteratedCovGrad (I := I) g₀ 0 2 1 h = covGrad (I := I) (M := M) g₀ 0 2 h := by
    rw [iteratedCovGrad_succ, iteratedCovGrad_zero]
  rw [hcg]
  exact tensorChartComponentRaw_covGrad (I := I) (M := M) g₀ 0 2 h x ![] Jdx hy

noncomputable def arm1ReadoutCovDeriv (g₀ : SmoothRiemannianMetric I M)
    (h : SmoothCcTensor g₀ 0 2) (x : M)
    (Jdx : Fin (2 + 1) → Fin (Module.finrank ℝ E)) : ℝ :=
  covDerivLowerOrderTerm (I := I) (M := M) g₀ 0 2 h x
    (Jdx 0) ![] (Matrix.vecTail Jdx) (toEuclidean (E := E) (extChartAt I x x))

def unitModel3SlotBilin
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (i j : Fin 3) (hij : i ≠ j) (base : Fin 3 → E) : E →L[ℝ] E →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun c => LinearMap.toContinuousLinearMap
        { toFun := fun v => f (Function.update (Function.update base i c) j v)
          map_add' := fun v1 v2 => by
            rw [f.map_update_add (Function.update base i c) j v1 v2]
          map_smul' := fun r v => by
            rw [f.map_update_smul (Function.update base i c) j r v]; rfl }
      map_add' := fun c1 c2 => by
        ext v
        change f (Function.update (Function.update base i (c1 + c2)) j v) =
          f (Function.update (Function.update base i c1) j v) +
          f (Function.update (Function.update base i c2) j v)
        rw [Function.update_comm hij c1 v base, Function.update_comm hij c2 v base,
          Function.update_comm hij (c1 + c2) v base]
        rw [f.map_update_add (Function.update base j v) i c1 c2]
      map_smul' := fun r c => by
        ext v
        change f (Function.update (Function.update base i (r • c)) j v) =
          r • f (Function.update (Function.update base i c) j v)
        rw [Function.update_comm hij c v base, Function.update_comm hij (r • c) v base]
        rw [f.map_update_smul (Function.update base j v) i r c] }

private lemma sum_pi_fin_succ' {n : ℕ} {β : Type*} [AddCommMonoid β]
    {N : ℕ} (g : (Fin (N + 1) → Fin n) → β) :
    (∑ p : Fin (N + 1) → Fin n, g p)
      = ∑ a : Fin n, ∑ q : Fin N → Fin n, g (Fin.cons a q) := by
  classical
  rw [← (Fin.consEquiv (fun _ : Fin (N + 1) => Fin n)).sum_comp g]
  rw [Fintype.sum_prod_type]
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M] in
private lemma covDerivLowerOrderTerm02_center_eq
    (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2) (x : M)
    (m p q : Fin (Module.finrank ℝ E)) :
    covDerivLowerOrderTerm (I := I) (M := M) g₀ 0 2 S x m ![] ![p, q]
        (toEuclidean (E := E) (extChartAt I x x)) =
      (- ∑ r : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g₀ x m p r (extChartAt I x x) *
            tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 S x ![] ![r, q] x)
      + (- ∑ r : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g₀ x m q r (extChartAt I x x) *
            tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 S x ![] ![p, r] x) := by
  classical
  have hmemsrc : x ∈ (chartAt H x).source := mem_chart_source H x
  have hround : (extChartAt I x).symm
      ((toEuclidean (E := E)).symm ((toEuclidean (E := E)) (extChartAt I x x))) = x :=
    symm_toEuclidean_symm_toEuclidean_extChartAt (I := I) (M := M) x hmemsrc
  have hcenter : (toEuclidean (E := E)) (extChartAt I x x) ∈
      chartTargetEuclid (I := I) (M := M) x :=
    toEuclidean_extChartAt_mem_chartTargetEuclid (I := I) (M := M) x hmemsrc
  have hbase : x ∈ (trivializationAt E (TangentSpace I) x).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact hmemsrc
  rw [covDerivLowerOrderTerm_def]
  rw [hround]
  haveI : Unique (Fin 0 → Fin (Module.finrank ℝ E)) :=
    ⟨⟨![]⟩, fun f => by funext j; exact absurd j.2 (by simp)⟩
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single (![] : Fin 0 → Fin (Module.finrank ℝ E))]
  · simp only [covDerivLowerOrderCoeff_def]
    simp only [Finset.univ_eq_empty, Finset.sum_empty, if_true, mul_one, zero_sub]
    have hout : ∀ J' : Fin 2 → Fin (Module.finrank ℝ E),
        (∑ l : Fin 2, outputSlotCoeff (I := I) (M := M) g₀ 2 x m l ![p, q] J'
            (toEuclidean (E := E) (extChartAt I x x))) =
          chartChristoffel (I := I) g₀ x p m (J' 0) (extChartAt I x x) *
              (if q = J' 1 then (1 : ℝ) else 0) +
            chartChristoffel (I := I) g₀ x q m (J' 1) (extChartAt I x x) *
              (if p = J' 0 then (1 : ℝ) else 0) := by
      intro J'
      rw [Fin.sum_univ_two]
      rw [outputSlotCoeff_eq_entry_mul_const (I := I) (M := M) g₀ 2 x m 0 ![p, q] J' hcenter,
        outputSlotCoeff_eq_entry_mul_const (I := I) (M := M) g₀ 2 x m 1 ![p, q] J' hcenter]
      rw [hround]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [chartLeviCivitaParallelCLM_coordEntry_eq_chartChristoffel (I := I) g₀ x hbase m (J' 0) p,
        chartLeviCivitaParallelCLM_coordEntry_eq_chartChristoffel (I := I) g₀ x hbase m (J' 1) q]
      have herase0 : (Finset.univ.erase (0 : Fin 2)) = {(1 : Fin 2)} := by decide
      have herase1 : (Finset.univ.erase (1 : Fin 2)) = {(0 : Fin 2)} := by decide
      rw [herase0, herase1]
      simp only [Finset.prod_singleton, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [Finset.sum_congr rfl (fun J' _ => by rw [hout J'] :
      ∀ J' ∈ Finset.univ,
        (-∑ x_2, outputSlotCoeff (I := I) (M := M) g₀ 2 x m x_2 ![p, q] J'
            (toEuclidean (E := E) (extChartAt I x x))) *
          tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 S x ![] J' x =
        (-(chartChristoffel (I := I) g₀ x p m (J' 0) (extChartAt I x x) *
              (if q = J' 1 then (1 : ℝ) else 0) +
            chartChristoffel (I := I) g₀ x q m (J' 1) (extChartAt I x x) *
              (if p = J' 0 then (1 : ℝ) else 0))) *
          tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 S x ![] J' x)]
    rw [← (finTwoArrowEquiv (Fin (Module.finrank ℝ E))).symm.sum_comp
      (fun J' : Fin 2 → Fin (Module.finrank ℝ E) =>
        (-(chartChristoffel (I := I) g₀ x p m (J' 0) (extChartAt I x x) *
              (if q = J' 1 then (1 : ℝ) else 0) +
            chartChristoffel (I := I) g₀ x q m (J' 1) (extChartAt I x x) *
              (if p = J' 0 then (1 : ℝ) else 0))) *
          tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 S x ![] J' x)]
    rw [Fintype.sum_prod_type]
    simp only [finTwoArrowEquiv_symm_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    have hsplit : ∀ a : Fin (Module.finrank ℝ E),
        (∑ b : Fin (Module.finrank ℝ E),
          -((chartChristoffel (I := I) g₀ x p m a (extChartAt I x x) *
                  (if q = b then (1 : ℝ) else 0)) +
              chartChristoffel (I := I) g₀ x q m b (extChartAt I x x) *
                (if p = a then (1 : ℝ) else 0)) *
            tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 S x ![] ![a, b] x) =
          (-(chartChristoffel (I := I) g₀ x p m a (extChartAt I x x) *
              tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 S x ![] ![a, q] x)) +
          (if p = a then (1 : ℝ) else 0) *
            (-∑ b : Fin (Module.finrank ℝ E),
              chartChristoffel (I := I) g₀ x q m b (extChartAt I x x) *
                tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 S x ![] ![a, b] x) := by
      intro a
      rw [show (∑ b : Fin (Module.finrank ℝ E),
            -((chartChristoffel (I := I) g₀ x p m a (extChartAt I x x) *
                    (if q = b then (1 : ℝ) else 0)) +
                chartChristoffel (I := I) g₀ x q m b (extChartAt I x x) *
                  (if p = a then (1 : ℝ) else 0)) *
              tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 S x ![] ![a, b] x) =
          (∑ b : Fin (Module.finrank ℝ E),
            -(chartChristoffel (I := I) g₀ x p m a (extChartAt I x x) *
                (if q = b then (1 : ℝ) else 0)) *
              tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 S x ![] ![a, b] x) +
          (∑ b : Fin (Module.finrank ℝ E),
            (if p = a then (1 : ℝ) else 0) *
              -(chartChristoffel (I := I) g₀ x q m b (extChartAt I x x) *
                tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 S x ![] ![a, b] x)) from by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun b _ => ?_); ring]
      congr 1
      · rw [Finset.sum_eq_single q]
        · rw [if_pos rfl]; ring
        · intro b _ hbq; rw [if_neg (fun h => hbq h.symm)]; ring
        · intro h; exact absurd (Finset.mem_univ q) h
      · rw [← Finset.mul_sum, Finset.sum_neg_distrib]
    rw [Finset.sum_congr rfl (fun a _ => hsplit a)]
    rw [Finset.sum_add_distrib]
    congr 1
    · rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [chartChristoffel_symm (I := I) g₀ x p m a (extChartAt I x x)]
    · rw [Finset.sum_eq_single p]
      · rw [if_pos rfl, one_mul]
        congr 1
        refine Finset.sum_congr rfl (fun b _ => ?_)
        rw [chartChristoffel_symm (I := I) g₀ x q m b (extChartAt I x x)]
      · intro a _ hap; rw [if_neg (fun h => hap h.symm), zero_mul]
      · intro h; exact absurd (Finset.mem_univ p) h
  · intro b _ hb
    exact absurd (Subsingleton.elim b ![]) hb
  · intro h; exact absurd (Finset.mem_univ _) h

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M] in
private lemma covDerivLowerOrderTerm03_center_hout
    (g₀ : SmoothRiemannianMetric I M) (x : M)
    (m b c d : Fin (Module.finrank ℝ E))
    (J' : Fin 3 → Fin (Module.finrank ℝ E)) :
    (∑ l : Fin 3, outputSlotCoeff (I := I) (M := M) g₀ 3 x m l ![b, c, d] J'
        (toEuclidean (E := E) (extChartAt I x x))) =
      chartChristoffel (I := I) g₀ x m b (J' 0) (extChartAt I x x) *
          ((if c = J' 1 then (1 : ℝ) else 0) * (if d = J' 2 then (1 : ℝ) else 0)) +
      chartChristoffel (I := I) g₀ x m c (J' 1) (extChartAt I x x) *
          ((if b = J' 0 then (1 : ℝ) else 0) * (if d = J' 2 then (1 : ℝ) else 0)) +
      chartChristoffel (I := I) g₀ x m d (J' 2) (extChartAt I x x) *
          ((if b = J' 0 then (1 : ℝ) else 0) * (if c = J' 1 then (1 : ℝ) else 0)) := by
  classical
  have hmemsrc : x ∈ (chartAt H x).source := mem_chart_source H x
  have hround : (extChartAt I x).symm
      ((toEuclidean (E := E)).symm ((toEuclidean (E := E)) (extChartAt I x x))) = x :=
    symm_toEuclidean_symm_toEuclidean_extChartAt (I := I) (M := M) x hmemsrc
  have hcenter : (toEuclidean (E := E)) (extChartAt I x x) ∈
      chartTargetEuclid (I := I) (M := M) x :=
    toEuclidean_extChartAt_mem_chartTargetEuclid (I := I) (M := M) x hmemsrc
  have hbase : x ∈ (trivializationAt E (TangentSpace I) x).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact hmemsrc
  rw [Fin.sum_univ_three]
  rw [outputSlotCoeff_eq_entry_mul_const (I := I) (M := M) g₀ 3 x m 0 ![b, c, d] J' hcenter,
    outputSlotCoeff_eq_entry_mul_const (I := I) (M := M) g₀ 3 x m 1 ![b, c, d] J' hcenter,
    outputSlotCoeff_eq_entry_mul_const (I := I) (M := M) g₀ 3 x m 2 ![b, c, d] J' hcenter]
  rw [hround]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  rw [chartLeviCivitaParallelCLM_coordEntry_eq_chartChristoffel (I := I) g₀ x hbase m (J' 0) b,
    chartLeviCivitaParallelCLM_coordEntry_eq_chartChristoffel (I := I) g₀ x hbase m (J' 1) c,
    chartLeviCivitaParallelCLM_coordEntry_eq_chartChristoffel (I := I) g₀ x hbase m (J' 2) d]
  have herase0 : (Finset.univ.erase (0 : Fin 3)) = {(1 : Fin 3), (2 : Fin 3)} := by decide
  have herase1 : (Finset.univ.erase (1 : Fin 3)) = {(0 : Fin 3), (2 : Fin 3)} := by decide
  have herase2 : (Finset.univ.erase (2 : Fin 3)) = {(0 : Fin 3), (1 : Fin 3)} := by decide
  rw [herase0, herase1, herase2]
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide)]
  simp only [Finset.prod_singleton, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  rw [chartChristoffel_symm (I := I) g₀ x b m (J' 0) (extChartAt I x x),
    chartChristoffel_symm (I := I) g₀ x c m (J' 1) (extChartAt I x x),
    chartChristoffel_symm (I := I) g₀ x d m (J' 2) (extChartAt I x x)]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma sum_fin3_collapse_gen
    (F : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → ℝ) :
    (∑ J' : Fin 3 → Fin (Module.finrank ℝ E), F (J' 0) (J' 1) (J' 2)) =
      ∑ a0 : Fin (Module.finrank ℝ E), ∑ a1 : Fin (Module.finrank ℝ E),
        ∑ a2 : Fin (Module.finrank ℝ E), F a0 a1 a2 := by
  classical
  rw [sum_pi_fin_succ']
  refine Finset.sum_congr rfl (fun a0 _ => ?_)
  rw [sum_pi_fin_succ']
  refine Finset.sum_congr rfl (fun a1 _ => ?_)
  refine Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin (Module.finrank ℝ E))) _ _ (fun q => ?_)
  simp only [Equiv.funUnique_apply, Fin.cons_zero,
    show ((1 : Fin 3) = (Fin.succ 0)) from rfl,
    show ((2 : Fin 3) = (Fin.succ 1)) from rfl,
    show ((1 : Fin 2) = (Fin.succ 0)) from rfl, Fin.cons_succ]
  rw [show (default : Fin 1) = (0 : Fin 1) from rfl]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M] in
private lemma covDerivLowerOrderTerm03_center_eq
    (g₀ : SmoothRiemannianMetric I M) (W : SmoothCcTensor g₀ 0 3) (x : M)
    (m b c d : Fin (Module.finrank ℝ E)) :
    covDerivLowerOrderTerm (I := I) (M := M) g₀ 0 3 W x m ![] ![b, c, d]
        (toEuclidean (E := E) (extChartAt I x x)) =
      (- ∑ r : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g₀ x m b r (extChartAt I x x) *
            tensorChartComponentRaw (I := I) (M := M) g₀ 0 3 W x ![] ![r, c, d] x)
      + (- ∑ r : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g₀ x m c r (extChartAt I x x) *
            tensorChartComponentRaw (I := I) (M := M) g₀ 0 3 W x ![] ![b, r, d] x)
      + (- ∑ r : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g₀ x m d r (extChartAt I x x) *
            tensorChartComponentRaw (I := I) (M := M) g₀ 0 3 W x ![] ![b, c, r] x) := by
  classical
  have hmemsrc : x ∈ (chartAt H x).source := mem_chart_source H x
  have hround : (extChartAt I x).symm
      ((toEuclidean (E := E)).symm ((toEuclidean (E := E)) (extChartAt I x x))) = x :=
    symm_toEuclidean_symm_toEuclidean_extChartAt (I := I) (M := M) x hmemsrc
  rw [covDerivLowerOrderTerm_def]
  rw [hround]
  haveI : Unique (Fin 0 → Fin (Module.finrank ℝ E)) :=
    ⟨⟨![]⟩, fun f => by funext j; exact absurd j.2 (by simp)⟩
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single (![] : Fin 0 → Fin (Module.finrank ℝ E))]
  · simp only [covDerivLowerOrderCoeff_def]
    simp only [Finset.univ_eq_empty, Finset.sum_empty, if_true, mul_one, zero_sub]
    rw [Finset.sum_congr rfl (fun J' _ => by
        rw [covDerivLowerOrderTerm03_center_hout (I := I) (M := M) g₀ x m b c d J'] :
      ∀ J' ∈ Finset.univ,
        (-∑ x_2, outputSlotCoeff (I := I) (M := M) g₀ 3 x m x_2 ![b, c, d] J'
            (toEuclidean (E := E) (extChartAt I x x))) *
          tensorChartComponentRaw (I := I) (M := M) g₀ 0 3 W x ![] J' x =
        (-(chartChristoffel (I := I) g₀ x m b (J' 0) (extChartAt I x x) *
              ((if c = J' 1 then (1 : ℝ) else 0) * (if d = J' 2 then (1 : ℝ) else 0)) +
            chartChristoffel (I := I) g₀ x m c (J' 1) (extChartAt I x x) *
              ((if b = J' 0 then (1 : ℝ) else 0) * (if d = J' 2 then (1 : ℝ) else 0)) +
            chartChristoffel (I := I) g₀ x m d (J' 2) (extChartAt I x x) *
              ((if b = J' 0 then (1 : ℝ) else 0) * (if c = J' 1 then (1 : ℝ) else 0)))) *
          tensorChartComponentRaw (I := I) (M := M) g₀ 0 3 W x ![] J' x)]
    rw [Finset.sum_congr rfl (fun J' _ =>
      show (-(chartChristoffel (I := I) g₀ x m b (J' 0) (extChartAt I x x) *
              ((if c = J' 1 then (1 : ℝ) else 0) * (if d = J' 2 then (1 : ℝ) else 0)) +
            chartChristoffel (I := I) g₀ x m c (J' 1) (extChartAt I x x) *
              ((if b = J' 0 then (1 : ℝ) else 0) * (if d = J' 2 then (1 : ℝ) else 0)) +
            chartChristoffel (I := I) g₀ x m d (J' 2) (extChartAt I x x) *
              ((if b = J' 0 then (1 : ℝ) else 0) * (if c = J' 1 then (1 : ℝ) else 0)))) *
          tensorChartComponentRaw (I := I) (M := M) g₀ 0 3 W x ![] J' x =
        (-(chartChristoffel (I := I) g₀ x m b (J' 0) (extChartAt I x x) *
            tensorChartComponentRaw (I := I) (M := M) g₀ 0 3 W x ![] ![J' 0, J' 1, J' 2] x) *
            ((if c = J' 1 then (1 : ℝ) else 0) * (if d = J' 2 then (1 : ℝ) else 0))) +
        (-(chartChristoffel (I := I) g₀ x m c (J' 1) (extChartAt I x x) *
            tensorChartComponentRaw (I := I) (M := M) g₀ 0 3 W x ![] ![J' 0, J' 1, J' 2] x) *
            ((if b = J' 0 then (1 : ℝ) else 0) * (if d = J' 2 then (1 : ℝ) else 0))) +
        (-(chartChristoffel (I := I) g₀ x m d (J' 2) (extChartAt I x x) *
            tensorChartComponentRaw (I := I) (M := M) g₀ 0 3 W x ![] ![J' 0, J' 1, J' 2] x) *
            ((if b = J' 0 then (1 : ℝ) else 0) * (if c = J' 1 then (1 : ℝ) else 0)))
        from by
          rw [show (![J' 0, J' 1, J' 2] : Fin 3 → Fin (Module.finrank ℝ E)) = J' from by
            funext j; fin_cases j <;> rfl]
          ring)]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    rw [sum_fin3_collapse_gen
        (fun a0 a1 a2 => -(chartChristoffel (I := I) g₀ x m b a0 (extChartAt I x x) *
          tensorChartComponentRaw (I := I) (M := M) g₀ 0 3 W x ![] ![a0, a1, a2] x) *
          ((if c = a1 then (1 : ℝ) else 0) * (if d = a2 then (1 : ℝ) else 0))),
      sum_fin3_collapse_gen
        (fun a0 a1 a2 => -(chartChristoffel (I := I) g₀ x m c a1 (extChartAt I x x) *
          tensorChartComponentRaw (I := I) (M := M) g₀ 0 3 W x ![] ![a0, a1, a2] x) *
          ((if b = a0 then (1 : ℝ) else 0) * (if d = a2 then (1 : ℝ) else 0))),
      sum_fin3_collapse_gen
        (fun a0 a1 a2 => -(chartChristoffel (I := I) g₀ x m d a2 (extChartAt I x x) *
          tensorChartComponentRaw (I := I) (M := M) g₀ 0 3 W x ![] ![a0, a1, a2] x) *
          ((if b = a0 then (1 : ℝ) else 0) * (if c = a1 then (1 : ℝ) else 0)))]
    congr 1
    congr 1
    · rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun a0 _ => ?_)
      rw [Finset.sum_eq_single c]
      · rw [Finset.sum_eq_single d]
        · rw [if_pos rfl, if_pos rfl]; ring
        · intro a2 _ ha2; rw [if_neg (show ¬ d = a2 from fun h => ha2 h.symm), mul_zero]; ring
        · intro h; exact absurd (Finset.mem_univ d) h
      · intro a1 _ ha1
        refine Finset.sum_eq_zero (fun a2 _ => ?_)
        rw [if_neg (show ¬ c = a1 from fun h => ha1 h.symm), zero_mul]; ring
      · intro h; exact absurd (Finset.mem_univ c) h
    · rw [← Finset.sum_neg_distrib]
      rw [Finset.sum_eq_single b]
      · refine Finset.sum_congr rfl (fun a1 _ => ?_)
        rw [Finset.sum_eq_single d]
        · rw [if_pos rfl, if_pos rfl]; ring
        · intro a2 _ ha2; rw [if_neg (show ¬ d = a2 from fun h => ha2 h.symm), mul_zero]; ring
        · intro h; exact absurd (Finset.mem_univ d) h
      · intro a0 _ ha0
        refine Finset.sum_eq_zero (fun a1 _ => ?_)
        refine Finset.sum_eq_zero (fun a2 _ => ?_)
        rw [if_neg (show ¬ b = a0 from fun h => ha0 h.symm), zero_mul]; ring
      · intro h; exact absurd (Finset.mem_univ b) h
    · rw [← Finset.sum_neg_distrib]
      rw [Finset.sum_eq_single b]
      · rw [Finset.sum_eq_single c]
        · refine Finset.sum_congr rfl (fun a2 _ => ?_)
          rw [if_pos rfl, if_pos rfl]; ring
        · intro a1 _ ha1
          refine Finset.sum_eq_zero (fun a2 _ => ?_)
          rw [if_neg (show ¬ c = a1 from fun h => ha1 h.symm), mul_zero]; ring
        · intro h; exact absurd (Finset.mem_univ c) h
      · intro a0 _ ha0
        refine Finset.sum_eq_zero (fun a1 _ => ?_)
        refine Finset.sum_eq_zero (fun a2 _ => ?_)
        rw [if_neg (show ¬ b = a0 from fun h => ha0 h.symm), zero_mul]; ring
      · intro h; exact absurd (Finset.mem_univ b) h
  · intro b' _ hb'
    exact absurd (Subsingleton.elim b' ![]) hb'
  · intro h; exact absurd (Finset.mem_univ _) h

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M] in
private lemma lowerOrderCoeff02_eqOn_chartChristoffelEuclid
    (g₀ : SmoothRiemannianMetric I M) (x : M)
    (m : Fin (Module.finrank ℝ E))
    (Jdx Jdx' : Fin 2 → Fin (Module.finrank ℝ E)) :
    Set.EqOn
      (covDerivLowerOrderCoeff (I := I) (M := M) g₀ 0 2 x m ![] ![] Jdx Jdx')
      (fun y =>
        - (chartChristoffelEuclid (I := I) g₀ x (Jdx 0) m (Jdx' 0) y *
              (if Jdx 1 = Jdx' 1 then (1 : ℝ) else 0)
            + chartChristoffelEuclid (I := I) g₀ x (Jdx 1) m (Jdx' 1) y *
              (if Jdx 0 = Jdx' 0 then (1 : ℝ) else 0)))
      (chartTargetEuclid (I := I) (M := M) x) := by
  classical
  intro y hy
  change covDerivLowerOrderCoeff (I := I) (M := M) g₀ 0 2 x m ![] ![] Jdx Jdx' y =
      - (chartChristoffelEuclid (I := I) g₀ x (Jdx 0) m (Jdx' 0) y *
            (if Jdx 1 = Jdx' 1 then (1 : ℝ) else 0)
          + chartChristoffelEuclid (I := I) g₀ x (Jdx 1) m (Jdx' 1) y *
            (if Jdx 0 = Jdx' 0 then (1 : ℝ) else 0))
  rw [covDerivLowerOrderCoeff_def]
  simp only [Finset.univ_eq_empty, Finset.sum_empty, if_true, mul_one, zero_sub]
  rw [Fin.sum_univ_two]
  rw [outputSlotCoeff_eq_entry_mul_const (I := I) (M := M) g₀ 2 x m 0 Jdx Jdx' hy,
    outputSlotCoeff_eq_entry_mul_const (I := I) (M := M) g₀ 2 x m 1 Jdx Jdx' hy]
  have hb_base : (extChartAt I x).symm ((toEuclidean (E := E)).symm y) ∈
      (trivializationAt E (TangentSpace I) x).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) x hy
  have hy_pre : (toEuclidean (E := E)).symm y ∈ (extChartAt I x).target := by
    rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
    exact hy
  have hphi_b : extChartAt I x
      ((extChartAt I x).symm ((toEuclidean (E := E)).symm y)) =
      (toEuclidean (E := E)).symm y :=
    (extChartAt I x).right_inv hy_pre
  rw [chartLeviCivitaParallelCLM_coordEntry_eq_chartChristoffel (I := I) g₀ x hb_base m (Jdx' 0) (Jdx 0),
    chartLeviCivitaParallelCLM_coordEntry_eq_chartChristoffel (I := I) g₀ x hb_base m (Jdx' 1) (Jdx 1)]
  rw [hphi_b]
  rw [show chartChristoffel (I := I) g₀ x (Jdx 0) m (Jdx' 0) ((toEuclidean (E := E)).symm y) =
      chartChristoffelEuclid (I := I) g₀ x (Jdx 0) m (Jdx' 0) y from rfl,
    show chartChristoffel (I := I) g₀ x (Jdx 1) m (Jdx' 1) ((toEuclidean (E := E)).symm y) =
      chartChristoffelEuclid (I := I) g₀ x (Jdx 1) m (Jdx' 1) y from rfl]
  have herase0 : (Finset.univ.erase (0 : Fin 2)) = {(1 : Fin 2)} := by decide
  have herase1 : (Finset.univ.erase (1 : Fin 2)) = {(0 : Fin 2)} := by decide
  rw [herase0, herase1]
  simp only [Finset.prod_singleton]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M] in
private lemma gradCoeff02_center_eq
    (g₀ : SmoothRiemannianMetric I M) (x : M)
    (m : Fin (Module.finrank ℝ E))
    (Jdx Jdx' : Fin 2 → Fin (Module.finrank ℝ E)) :
    secondCovDerivLO_gradCoeff (I := I) (M := M) g₀ 0 2 x m ![] ![] Jdx Jdx'
        (toEuclidean (E := E) (extChartAt I x x)) =
      - (chartChristoffel (I := I) g₀ x (Jdx 0) m (Jdx' 0) (extChartAt I x x) *
            (if Jdx 1 = Jdx' 1 then (1 : ℝ) else 0)
          + chartChristoffel (I := I) g₀ x (Jdx 1) m (Jdx' 1) (extChartAt I x x) *
            (if Jdx 0 = Jdx' 0 then (1 : ℝ) else 0)) := by
  classical
  have hcenter : (toEuclidean (E := E)) (extChartAt I x x) ∈
      chartTargetEuclid (I := I) (M := M) x :=
    toEuclidean_extChartAt_mem_chartTargetEuclid (I := I) (M := M) x (mem_chart_source H x)
  have hround : (extChartAt I x).symm
      ((toEuclidean (E := E)).symm ((toEuclidean (E := E)) (extChartAt I x x))) = x :=
    symm_toEuclidean_symm_toEuclidean_extChartAt (I := I) (M := M) x (mem_chart_source H x)
  have hsymm : ((toEuclidean (E := E)).symm ((toEuclidean (E := E)) (extChartAt I x x))) =
      extChartAt I x x := (toEuclidean (E := E)).symm_apply_apply _
  unfold secondCovDerivLO_gradCoeff
  rw [lowerOrderCoeff02_eqOn_chartChristoffelEuclid (I := I) (M := M) g₀ x m Jdx Jdx' hcenter]
  simp only [chartChristoffelEuclid_def, hsymm]

omit [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma valueCoeff02_center_eq
    (g₀ : SmoothRiemannianMetric I M) (x : M)
    (m a : Fin (Module.finrank ℝ E))
    (Jdx Jdx' : Fin 2 → Fin (Module.finrank ℝ E)) :
    secondCovDerivLO_valueCoeff (I := I) (M := M) g₀ 0 2 x m a ![] ![] Jdx Jdx'
        (toEuclidean (E := E) (extChartAt I x x)) =
      - (euclidPartial (E := E) a
              (chartChristoffelEuclid (I := I) g₀ x (Jdx 0) m (Jdx' 0))
              (toEuclidean (E := E) (extChartAt I x x)) *
            (if Jdx 1 = Jdx' 1 then (1 : ℝ) else 0)
          + euclidPartial (E := E) a
              (chartChristoffelEuclid (I := I) g₀ x (Jdx 1) m (Jdx' 1))
              (toEuclidean (E := E) (extChartAt I x x)) *
            (if Jdx 0 = Jdx' 0 then (1 : ℝ) else 0)) := by
  classical
  have hopen : IsOpen (chartTargetEuclid (I := I) (M := M) x) :=
    chartTargetEuclid_isOpen (I := I) (M := M) x
  have hcenter : (toEuclidean (E := E)) (extChartAt I x x) ∈
      chartTargetEuclid (I := I) (M := M) x :=
    toEuclidean_extChartAt_mem_chartTargetEuclid (I := I) (M := M) x (mem_chart_source H x)
  unfold secondCovDerivLO_valueCoeff
  have heq : Set.EqOn
      (covDerivLowerOrderCoeff (I := I) (M := M) g₀ 0 2 x m ![] ![] Jdx Jdx')
      (fun y =>
        - (chartChristoffelEuclid (I := I) g₀ x (Jdx 0) m (Jdx' 0) y *
              (if Jdx 1 = Jdx' 1 then (1 : ℝ) else 0)
            + chartChristoffelEuclid (I := I) g₀ x (Jdx 1) m (Jdx' 1) y *
              (if Jdx 0 = Jdx' 0 then (1 : ℝ) else 0)))
      (chartTargetEuclid (I := I) (M := M) x) :=
    lowerOrderCoeff02_eqOn_chartChristoffelEuclid (I := I) (M := M) g₀ x m Jdx Jdx'
  rw [euclidPartial_def,
    Filter.EventuallyEq.fderiv_eq (heq.eventuallyEq_of_mem (hopen.mem_nhds hcenter))]
  rw [← euclidPartial_def]
  have hd0 : DifferentiableAt ℝ
      (chartChristoffelEuclid (I := I) g₀ x (Jdx 0) m (Jdx' 0))
      (toEuclidean (E := E) (extChartAt I x x)) :=
    ((chartChristoffelEuclid_contDiffOn (I := I) g₀ x (Jdx 0) m (Jdx' 0)).differentiableOn
      (by norm_cast)).differentiableAt (hopen.mem_nhds hcenter)
  have hd1 : DifferentiableAt ℝ
      (chartChristoffelEuclid (I := I) g₀ x (Jdx 1) m (Jdx' 1))
      (toEuclidean (E := E) (extChartAt I x x)) :=
    ((chartChristoffelEuclid_contDiffOn (I := I) g₀ x (Jdx 1) m (Jdx' 1)).differentiableOn
      (by norm_cast)).differentiableAt (hopen.mem_nhds hcenter)
  rw [show (fun y =>
        - (chartChristoffelEuclid (I := I) g₀ x (Jdx 0) m (Jdx' 0) y *
              (if Jdx 1 = Jdx' 1 then (1 : ℝ) else 0)
            + chartChristoffelEuclid (I := I) g₀ x (Jdx 1) m (Jdx' 1) y *
              (if Jdx 0 = Jdx' 0 then (1 : ℝ) else 0))) =
      (fun y =>
        (chartChristoffelEuclid (I := I) g₀ x (Jdx 0) m (Jdx' 0) y *
            (- (if Jdx 1 = Jdx' 1 then (1 : ℝ) else 0)))
          + (chartChristoffelEuclid (I := I) g₀ x (Jdx 1) m (Jdx' 1) y *
            (- (if Jdx 0 = Jdx' 0 then (1 : ℝ) else 0)))) from by
    funext y; ring]
  rw [euclidPartial_add_local a
    (hd0.mul_const _) (hd1.mul_const _)]
  rw [euclidPartial_def, euclidPartial_def, fderiv_mul_const hd0 _, fderiv_mul_const hd1 _,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, smul_eq_mul,
    ← euclidPartial_def, ← euclidPartial_def]
  ring

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M] in
lemma arm1ReadoutCovDeriv_center_eq
    (g₀ : SmoothRiemannianMetric I M) (h : SmoothCcTensor g₀ 0 2) (x : M)
    (a b c : Fin (Module.finrank ℝ E)) :
    arm1ReadoutCovDeriv (I := I) (M := M) g₀ h x ![a, b, c] =
      (- ∑ r : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g₀ x a b r (extChartAt I x x) *
            tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![r, c] x)
      + (- ∑ r : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g₀ x a c r (extChartAt I x x) *
            tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![b, r] x) := by
  classical
  rw [arm1ReadoutCovDeriv]
  rw [show (Matrix.vecTail (![a, b, c] : Fin (2 + 1) → Fin (Module.finrank ℝ E))) = ![b, c] from by
    funext j; fin_cases j <;> rfl]
  rw [show (![a, b, c] : Fin (2 + 1) → Fin (Module.finrank ℝ E)) 0 = a from rfl]
  exact covDerivLowerOrderTerm02_center_eq (I := I) (M := M) g₀ h x a b c

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma euclidPartial_covDerivLowerOrderTerm02_center_eq_sum
    (g₀ : SmoothRiemannianMetric I M) (h : SmoothCcTensor g₀ 0 2) (x : M)
    (a b c d : Fin (Module.finrank ℝ E)) :
    euclidPartial (E := E) a
        (fun y' => covDerivLowerOrderTerm (I := I) (M := M) g₀ 0 2 h x b ![] ![c, d] y')
        (toEuclidean (E := E) (extChartAt I x x)) =
      ∑ p : (Fin 0 → Fin (Module.finrank ℝ E)) × (Fin 2 → Fin (Module.finrank ℝ E)),
        (secondCovDerivLO_valueCoeff (I := I) (M := M) g₀ 0 2 x b a ![] p.1 ![c, d] p.2
              (toEuclidean (E := E) (extChartAt I x x)) *
            rawComponentEuclid (I := I) (M := M) g₀ 0 2 x h p.1 p.2
              (toEuclidean (E := E) (extChartAt I x x)) +
          secondCovDerivLO_gradCoeff (I := I) (M := M) g₀ 0 2 x b ![] p.1 ![c, d] p.2
              (toEuclidean (E := E) (extChartAt I x x)) *
            euclidPartial (E := E) a
              (rawComponentEuclid (I := I) (M := M) g₀ 0 2 x h p.1 p.2)
              (toEuclidean (E := E) (extChartAt I x x))) := by
  classical
  have hopen : IsOpen (chartTargetEuclid (I := I) (M := M) x) :=
    chartTargetEuclid_isOpen (I := I) (M := M) x
  have hcenter : (toEuclidean (E := E)) (extChartAt I x x) ∈
      chartTargetEuclid (I := I) (M := M) x :=
    toEuclidean_extChartAt_mem_chartTargetEuclid (I := I) (M := M) x (mem_chart_source H x)
  have heq : Set.EqOn
      (fun y' => covDerivLowerOrderTerm (I := I) (M := M) g₀ 0 2 h x b ![] ![c, d] y')
      (fun y' => ∑ p : (Fin 0 → Fin (Module.finrank ℝ E)) ×
            (Fin 2 → Fin (Module.finrank ℝ E)),
          lowerOrderSummand (I := I) (M := M) g₀ 0 2 x h b ![] ![c, d] p y')
      (chartTargetEuclid (I := I) (M := M) x) := by
    intro y _
    exact covDerivLowerOrderTerm_eq_sum_lowerOrderSummand
      (I := I) (M := M) g₀ 0 2 x h b ![] ![c, d] y
  rw [euclidPartial_def,
    Filter.EventuallyEq.fderiv_eq (heq.eventuallyEq_of_mem (hopen.mem_nhds hcenter)),
    ← euclidPartial_def]
  have hsummand_diff : ∀ p : (Fin 0 → Fin (Module.finrank ℝ E)) ×
        (Fin 2 → Fin (Module.finrank ℝ E)),
      DifferentiableAt ℝ (lowerOrderSummand (I := I) (M := M) g₀ 0 2 x h b ![] ![c, d] p)
        (toEuclidean (E := E) (extChartAt I x x)) := by
    intro p
    exact ((lowerOrderSummand_contDiffOn (I := I) (M := M) g₀ 0 2 x h b ![] ![c, d] p).differentiableOn
      (by norm_cast)).differentiableAt (hopen.mem_nhds hcenter)
  rw [euclidPartial_finsetSum a Finset.univ (fun p _ => hsummand_diff p)]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  exact euclidPartial_lowerOrderSummand_apply (I := I) (M := M) g₀ 0 2 x h b a ![] ![c, d] p hcenter

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma sum_two_slot_indicator_collapse
    (Cc Cd : Fin (Module.finrank ℝ E) → ℝ)
    (F : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ)
    (c d : Fin (Module.finrank ℝ E)) :
    (∑ J' : Fin 2 → Fin (Module.finrank ℝ E),
        (Cc (J' 0) * (if d = J' 1 then (1 : ℝ) else 0) +
          Cd (J' 1) * (if c = J' 0 then (1 : ℝ) else 0)) *
          F (J' 0) (J' 1)) =
      (∑ a0 : Fin (Module.finrank ℝ E), Cc a0 * F a0 d) +
        (∑ a1 : Fin (Module.finrank ℝ E), Cd a1 * F c a1) := by
  classical
  rw [← (finTwoArrowEquiv (Fin (Module.finrank ℝ E))).symm.sum_comp
    (fun J' : Fin 2 → Fin (Module.finrank ℝ E) =>
      (Cc (J' 0) * (if d = J' 1 then (1 : ℝ) else 0) +
        Cd (J' 1) * (if c = J' 0 then (1 : ℝ) else 0)) *
        F (J' 0) (J' 1))]
  rw [Fintype.sum_prod_type]
  simp only [finTwoArrowEquiv_symm_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hinner : ∀ a0 : Fin (Module.finrank ℝ E),
      (∑ a1 : Fin (Module.finrank ℝ E),
        (Cc a0 * (if d = a1 then (1 : ℝ) else 0) +
          Cd a1 * (if c = a0 then (1 : ℝ) else 0)) * F a0 a1) =
        Cc a0 * F a0 d +
          (if c = a0 then (1 : ℝ) else 0) * (∑ a1 : Fin (Module.finrank ℝ E), Cd a1 * F a0 a1) := by
    intro a0
    rw [show (∑ a1 : Fin (Module.finrank ℝ E),
          (Cc a0 * (if d = a1 then (1 : ℝ) else 0) +
            Cd a1 * (if c = a0 then (1 : ℝ) else 0)) * F a0 a1) =
        (∑ a1 : Fin (Module.finrank ℝ E),
          Cc a0 * (if d = a1 then (1 : ℝ) else 0) * F a0 a1) +
        (∑ a1 : Fin (Module.finrank ℝ E),
          (if c = a0 then (1 : ℝ) else 0) * (Cd a1 * F a0 a1)) from by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun a1 _ => ?_); ring]
    congr 1
    · rw [Finset.sum_eq_single d]
      · rw [if_pos rfl]; ring
      · intro a1 _ ha1; rw [if_neg (fun h => ha1 h.symm)]; ring
      · intro h; exact absurd (Finset.mem_univ d) h
    · rw [← Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun a0 _ => hinner a0)]
  rw [Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single c]
  · rw [if_pos rfl, one_mul]
  · intro a0 _ ha0; rw [if_neg (fun h => ha0 h.symm), zero_mul]
  · intro h; exact absurd (Finset.mem_univ c) h

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma arm2ReadoutPairTerm1_center_eq
    (g₀ : SmoothRiemannianMetric I M) (h : SmoothCcTensor g₀ 0 2) (x : M)
    (a b c d : Fin (Module.finrank ℝ E)) :
    euclidPartial (E := E) a
        (fun y' => covDerivLowerOrderTerm (I := I) (M := M) g₀ 0 2 h x b ![] ![c, d] y')
        (toEuclidean (E := E) (extChartAt I x x)) =
      ((- ∑ r : Fin (Module.finrank ℝ E),
            euclidPartial (E := E) a
                (chartChristoffelEuclid (I := I) g₀ x c b r)
                (toEuclidean (E := E) (extChartAt I x x)) *
              tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![r, d] x)
        + (- ∑ r : Fin (Module.finrank ℝ E),
            euclidPartial (E := E) a
                (chartChristoffelEuclid (I := I) g₀ x d b r)
                (toEuclidean (E := E) (extChartAt I x x)) *
              tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![c, r] x))
      + ((- ∑ r : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g₀ x c b r (extChartAt I x x) *
              euclidPartial (E := E) a
                (chartPushedRaw I x (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![r, d]))
                (toEuclidean (E := E) (extChartAt I x x)))
        + (- ∑ r : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g₀ x d b r (extChartAt I x x) *
              euclidPartial (E := E) a
                (chartPushedRaw I x (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![c, r]))
                (toEuclidean (E := E) (extChartAt I x x)))) := by
  classical
  set Y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    toEuclidean (E := E) (extChartAt I x x) with hY
  have hcenter : Y ∈ chartTargetEuclid (I := I) (M := M) x := by
    rw [hY]; exact toEuclidean_extChartAt_mem_chartTargetEuclid (I := I) (M := M) x (mem_chart_source H x)
  have hopen : IsOpen (chartTargetEuclid (I := I) (M := M) x) :=
    chartTargetEuclid_isOpen (I := I) (M := M) x
  rw [euclidPartial_covDerivLowerOrderTerm02_center_eq_sum (I := I) (M := M) g₀ h x a b c d]
  haveI : Unique (Fin 0 → Fin (Module.finrank ℝ E)) :=
    ⟨⟨![]⟩, fun f => by funext j; exact absurd j.2 (by simp)⟩
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single (![] : Fin 0 → Fin (Module.finrank ℝ E))]
  · have hraweq : ∀ J' : Fin 2 → Fin (Module.finrank ℝ E),
        rawComponentEuclid (I := I) (M := M) g₀ 0 2 x h ![] J' Y =
          tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] J' x := by
      intro J'
      rw [hY, rawComponentEuclid_def,
        symm_toEuclidean_symm_toEuclidean_extChartAt (I := I) (M := M) x (mem_chart_source H x)]
    have hdReq : ∀ J' : Fin 2 → Fin (Module.finrank ℝ E),
        euclidPartial (E := E) a (rawComponentEuclid (I := I) (M := M) g₀ 0 2 x h ![] J') Y =
          euclidPartial (E := E) a
            (chartPushedRaw I x (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] J')) Y := by
      intro J'
      have heqraw : Set.EqOn (rawComponentEuclid (I := I) (M := M) g₀ 0 2 x h ![] J')
          (chartPushedRaw I x (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] J'))
          (chartTargetEuclid (I := I) (M := M) x) :=
        rawComponentEuclid_eqOn_chartPushed (I := I) (M := M) g₀ 0 2 x h ![] J'
      rw [euclidPartial_def, euclidPartial_def,
        Filter.EventuallyEq.fderiv_eq (heqraw.eventuallyEq_of_mem (hopen.mem_nhds hcenter))]
    have hsummand : ∀ J' : Fin 2 → Fin (Module.finrank ℝ E),
        secondCovDerivLO_valueCoeff (I := I) (M := M) g₀ 0 2 x b a ![] ![] ![c, d] J' Y *
            rawComponentEuclid (I := I) (M := M) g₀ 0 2 x h ![] J' Y +
          secondCovDerivLO_gradCoeff (I := I) (M := M) g₀ 0 2 x b ![] ![] ![c, d] J' Y *
            euclidPartial (E := E) a (rawComponentEuclid (I := I) (M := M) g₀ 0 2 x h ![] J') Y =
          (((fun r => - euclidPartial (E := E) a (chartChristoffelEuclid (I := I) g₀ x c b r) Y) (J' 0) *
                (if d = J' 1 then (1 : ℝ) else 0) +
              (fun r => - euclidPartial (E := E) a (chartChristoffelEuclid (I := I) g₀ x d b r) Y) (J' 1) *
                (if c = J' 0 then (1 : ℝ) else 0)) *
            (fun p q => tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![p, q] x) (J' 0) (J' 1)) +
          (((fun r => - chartChristoffel (I := I) g₀ x c b r (extChartAt I x x)) (J' 0) *
                (if d = J' 1 then (1 : ℝ) else 0) +
              (fun r => - chartChristoffel (I := I) g₀ x d b r (extChartAt I x x)) (J' 1) *
                (if c = J' 0 then (1 : ℝ) else 0)) *
            (fun p q => euclidPartial (E := E) a
              (chartPushedRaw I x (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![p, q])) Y)
              (J' 0) (J' 1)) := by
      intro J'
      have hv := valueCoeff02_center_eq (I := I) (M := M) g₀ x b a ![c, d] J'
      have hg := gradCoeff02_center_eq (I := I) (M := M) g₀ x b ![c, d] J'
      have hJeq : (![J' 0, J' 1] : Fin 2 → Fin (Module.finrank ℝ E)) = J' := by
        funext j; fin_cases j <;> rfl
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, ← hY] at hv hg
      rw [hv, hg, hraweq J', hdReq J']
      simp only [hJeq]
      ring
    rw [Finset.sum_congr rfl (fun J' _ => hsummand J')]
    rw [Finset.sum_add_distrib]
    rw [sum_two_slot_indicator_collapse
        (fun r => - euclidPartial (E := E) a (chartChristoffelEuclid (I := I) g₀ x c b r) Y)
        (fun r => - euclidPartial (E := E) a (chartChristoffelEuclid (I := I) g₀ x d b r) Y)
        (fun p q => tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![p, q] x) c d,
      sum_two_slot_indicator_collapse
        (fun r => - chartChristoffel (I := I) g₀ x c b r (extChartAt I x x))
        (fun r => - chartChristoffel (I := I) g₀ x d b r (extChartAt I x x))
        (fun p q => euclidPartial (E := E) a
          (chartPushedRaw I x (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![p, q])) Y) c d]
    rw [← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib,
      ← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib]
    refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) (congrArg₂ (· + ·) ?_ ?_) <;>
      refine Finset.sum_congr rfl (fun r _ => ?_) <;> ring
  · intro b' _ hb'
    exact absurd (Subsingleton.elim b' ![]) hb'
  · intro hcontra; exact absurd (Finset.mem_univ _) hcontra

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma rawCompCovGrad03_center_eq
    (g₀ : SmoothRiemannianMetric I M) (h : SmoothCcTensor g₀ 0 2) (x : M)
    (p q r : Fin (Module.finrank ℝ E)) :
    tensorChartComponentRaw (I := I) (M := M) g₀ 0 3
        (covGrad (I := I) (M := M) g₀ 0 2 h) x ![] ![p, q, r] x =
      euclidPartial (E := E) p
          (chartPushedRaw I x (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![q, r]))
          (toEuclidean (E := E) (extChartAt I x x))
        + ((- ∑ t : Fin (Module.finrank ℝ E),
              chartChristoffel (I := I) g₀ x p q t (extChartAt I x x) *
                tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![t, r] x)
          + (- ∑ t : Fin (Module.finrank ℝ E),
              chartChristoffel (I := I) g₀ x p r t (extChartAt I x x) *
                tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![q, t] x)) := by
  classical
  have hcenter : (toEuclidean (E := E)) (extChartAt I x x) ∈
      chartTargetEuclid (I := I) (M := M) x :=
    toEuclidean_extChartAt_mem_chartTargetEuclid (I := I) (M := M) x (mem_chart_source H x)
  have hround : (extChartAt I x).symm
      ((toEuclidean (E := E)).symm ((toEuclidean (E := E)) (extChartAt I x x))) = x :=
    symm_toEuclidean_symm_toEuclidean_extChartAt (I := I) (M := M) x (mem_chart_source H x)
  rw [show tensorChartComponentRaw (I := I) (M := M) g₀ 0 3
        (covGrad (I := I) (M := M) g₀ 0 2 h) x ![] ![p, q, r] x =
      tensorChartComponentRaw (I := I) (M := M) g₀ 0 3
        (covGrad (I := I) (M := M) g₀ 0 2 h) x ![] ![p, q, r]
        ((extChartAt I x).symm
          ((toEuclidean (E := E)).symm ((toEuclidean (E := E)) (extChartAt I x x)))) from by
    rw [hround] ]
  rw [tensorChartComponentRaw_covGrad (I := I) (M := M) g₀ 0 2 h x ![] ![p, q, r] hcenter]
  rw [show (Matrix.vecTail (![p, q, r] : Fin (2 + 1) → Fin (Module.finrank ℝ E))) = ![q, r] from by
    funext j; fin_cases j <;> rfl]
  rw [show (![p, q, r] : Fin (2 + 1) → Fin (Module.finrank ℝ E)) 0 = p from rfl]
  rw [covDerivLowerOrderTerm02_center_eq (I := I) (M := M) g₀ h x p q r]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma arm2ReadoutPairTerm2_center_eq
    (g₀ : SmoothRiemannianMetric I M) (h : SmoothCcTensor g₀ 0 2) (x : M)
    (a b c d : Fin (Module.finrank ℝ E)) :
    covDerivLowerOrderTerm (I := I) (M := M) g₀ 0 3
        (covGrad (I := I) (M := M) g₀ 0 2 h) x a ![] ![b, c, d]
        (toEuclidean (E := E) (extChartAt I x x)) =
      (- ∑ r : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g₀ x a b r (extChartAt I x x) *
            (euclidPartial (E := E) r
                (chartPushedRaw I x (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![c, d]))
                (toEuclidean (E := E) (extChartAt I x x))
              + ((- ∑ t : Fin (Module.finrank ℝ E),
                    chartChristoffel (I := I) g₀ x r c t (extChartAt I x x) *
                      tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![t, d] x)
                + (- ∑ t : Fin (Module.finrank ℝ E),
                    chartChristoffel (I := I) g₀ x r d t (extChartAt I x x) *
                      tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![c, t] x))))
      + (- ∑ r : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g₀ x a c r (extChartAt I x x) *
            (euclidPartial (E := E) b
                (chartPushedRaw I x (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![r, d]))
                (toEuclidean (E := E) (extChartAt I x x))
              + ((- ∑ t : Fin (Module.finrank ℝ E),
                    chartChristoffel (I := I) g₀ x b r t (extChartAt I x x) *
                      tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![t, d] x)
                + (- ∑ t : Fin (Module.finrank ℝ E),
                    chartChristoffel (I := I) g₀ x b d t (extChartAt I x x) *
                      tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![r, t] x))))
      + (- ∑ r : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g₀ x a d r (extChartAt I x x) *
            (euclidPartial (E := E) b
                (chartPushedRaw I x (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![c, r]))
                (toEuclidean (E := E) (extChartAt I x x))
              + ((- ∑ t : Fin (Module.finrank ℝ E),
                    chartChristoffel (I := I) g₀ x b c t (extChartAt I x x) *
                      tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![t, r] x)
                + (- ∑ t : Fin (Module.finrank ℝ E),
                    chartChristoffel (I := I) g₀ x b r t (extChartAt I x x) *
                      tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![c, t] x)))) := by
  classical
  rw [covDerivLowerOrderTerm03_center_eq (I := I) (M := M) g₀
    (covGrad (I := I) (M := M) g₀ 0 2 h) x a b c d]
  rw [show (∑ r : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g₀ x a b r (extChartAt I x x) *
          tensorChartComponentRaw (I := I) (M := M) g₀ 0 3
            (covGrad (I := I) (M := M) g₀ 0 2 h) x ![] ![r, c, d] x) =
      ∑ r : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g₀ x a b r (extChartAt I x x) *
          (euclidPartial (E := E) r
              (chartPushedRaw I x (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![c, d]))
              (toEuclidean (E := E) (extChartAt I x x))
            + ((- ∑ t : Fin (Module.finrank ℝ E),
                  chartChristoffel (I := I) g₀ x r c t (extChartAt I x x) *
                    tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![t, d] x)
              + (- ∑ t : Fin (Module.finrank ℝ E),
                  chartChristoffel (I := I) g₀ x r d t (extChartAt I x x) *
                    tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![c, t] x))) from by
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [rawCompCovGrad03_center_eq (I := I) (M := M) g₀ h x r c d] ]
  rw [show (∑ r : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g₀ x a c r (extChartAt I x x) *
          tensorChartComponentRaw (I := I) (M := M) g₀ 0 3
            (covGrad (I := I) (M := M) g₀ 0 2 h) x ![] ![b, r, d] x) =
      ∑ r : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g₀ x a c r (extChartAt I x x) *
          (euclidPartial (E := E) b
              (chartPushedRaw I x (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![r, d]))
              (toEuclidean (E := E) (extChartAt I x x))
            + ((- ∑ t : Fin (Module.finrank ℝ E),
                  chartChristoffel (I := I) g₀ x b r t (extChartAt I x x) *
                    tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![t, d] x)
              + (- ∑ t : Fin (Module.finrank ℝ E),
                  chartChristoffel (I := I) g₀ x b d t (extChartAt I x x) *
                    tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![r, t] x))) from by
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [rawCompCovGrad03_center_eq (I := I) (M := M) g₀ h x b r d] ]
  rw [show (∑ r : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g₀ x a d r (extChartAt I x x) *
          tensorChartComponentRaw (I := I) (M := M) g₀ 0 3
            (covGrad (I := I) (M := M) g₀ 0 2 h) x ![] ![b, c, r] x) =
      ∑ r : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g₀ x a d r (extChartAt I x x) *
          (euclidPartial (E := E) b
              (chartPushedRaw I x (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![c, r]))
              (toEuclidean (E := E) (extChartAt I x x))
            + ((- ∑ t : Fin (Module.finrank ℝ E),
                  chartChristoffel (I := I) g₀ x b c t (extChartAt I x x) *
                    tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![t, r] x)
              + (- ∑ t : Fin (Module.finrank ℝ E),
                  chartChristoffel (I := I) g₀ x b r t (extChartAt I x x) *
                    tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![c, t] x))) from by
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [rawCompCovGrad03_center_eq (I := I) (M := M) g₀ h x b c r] ]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma arm2ReadoutCovDerivPair_center_eq
    (g₀ : SmoothRiemannianMetric I M) (h : SmoothCcTensor g₀ 0 2) (x : M)
    (a b c d : Fin (Module.finrank ℝ E)) :
    arm2ReadoutCovDerivPair (I := I) (M := M) g₀ h x ![a, b, c, d] =
      (((- ∑ r : Fin (Module.finrank ℝ E),
              euclidPartial (E := E) a
                  (chartChristoffelEuclid (I := I) g₀ x c b r)
                  (toEuclidean (E := E) (extChartAt I x x)) *
                tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![r, d] x)
          + (- ∑ r : Fin (Module.finrank ℝ E),
              euclidPartial (E := E) a
                  (chartChristoffelEuclid (I := I) g₀ x d b r)
                  (toEuclidean (E := E) (extChartAt I x x)) *
                tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![c, r] x))
        + ((- ∑ r : Fin (Module.finrank ℝ E),
              chartChristoffel (I := I) g₀ x c b r (extChartAt I x x) *
                euclidPartial (E := E) a
                  (chartPushedRaw I x (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![r, d]))
                  (toEuclidean (E := E) (extChartAt I x x)))
          + (- ∑ r : Fin (Module.finrank ℝ E),
              chartChristoffel (I := I) g₀ x d b r (extChartAt I x x) *
                euclidPartial (E := E) a
                  (chartPushedRaw I x (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![c, r]))
                  (toEuclidean (E := E) (extChartAt I x x)))))
      + ((- ∑ r : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g₀ x a b r (extChartAt I x x) *
              (euclidPartial (E := E) r
                  (chartPushedRaw I x (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![c, d]))
                  (toEuclidean (E := E) (extChartAt I x x))
                + ((- ∑ t : Fin (Module.finrank ℝ E),
                      chartChristoffel (I := I) g₀ x r c t (extChartAt I x x) *
                        tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![t, d] x)
                  + (- ∑ t : Fin (Module.finrank ℝ E),
                      chartChristoffel (I := I) g₀ x r d t (extChartAt I x x) *
                        tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![c, t] x))))
        + ((- ∑ r : Fin (Module.finrank ℝ E),
              chartChristoffel (I := I) g₀ x a c r (extChartAt I x x) *
                (euclidPartial (E := E) b
                    (chartPushedRaw I x (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![r, d]))
                    (toEuclidean (E := E) (extChartAt I x x))
                  + ((- ∑ t : Fin (Module.finrank ℝ E),
                        chartChristoffel (I := I) g₀ x b r t (extChartAt I x x) *
                          tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![t, d] x)
                    + (- ∑ t : Fin (Module.finrank ℝ E),
                        chartChristoffel (I := I) g₀ x b d t (extChartAt I x x) *
                          tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![r, t] x))))
          + (- ∑ r : Fin (Module.finrank ℝ E),
              chartChristoffel (I := I) g₀ x a d r (extChartAt I x x) *
                (euclidPartial (E := E) b
                    (chartPushedRaw I x (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![c, r]))
                    (toEuclidean (E := E) (extChartAt I x x))
                  + ((- ∑ t : Fin (Module.finrank ℝ E),
                        chartChristoffel (I := I) g₀ x b c t (extChartAt I x x) *
                          tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![t, r] x)
                    + (- ∑ t : Fin (Module.finrank ℝ E),
                        chartChristoffel (I := I) g₀ x b r t (extChartAt I x x) *
                          tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![c, t] x)))))) := by
  classical
  rw [arm2ReadoutCovDerivPair]
  rw [show (Matrix.vecTail (![a, b, c, d] : Fin (2 + 2) → Fin (Module.finrank ℝ E))) = ![b, c, d] from by
    funext j; fin_cases j <;> rfl]
  rw [show (Matrix.vecTail (![b, c, d] : Fin (2 + 1) → Fin (Module.finrank ℝ E))) = ![c, d] from by
    funext j; fin_cases j <;> rfl]
  rw [show (![a, b, c, d] : Fin (2 + 2) → Fin (Module.finrank ℝ E)) 0 = a from rfl]
  rw [show (![b, c, d] : Fin (2 + 1) → Fin (Module.finrank ℝ E)) 0 = b from rfl]
  rw [arm2ReadoutPairTerm1_center_eq (I := I) (M := M) g₀ h x a b c d]
  rw [arm2ReadoutPairTerm2_center_eq (I := I) (M := M) g₀ h x a b c d]
  ring

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
