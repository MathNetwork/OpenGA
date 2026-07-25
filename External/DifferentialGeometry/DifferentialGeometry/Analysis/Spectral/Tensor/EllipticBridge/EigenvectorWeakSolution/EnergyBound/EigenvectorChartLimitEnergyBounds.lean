import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.EnergyBound.EigenvectorChartGradientEnergyBound
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Cross.EigenvectorChartCrossLimits
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.LowerOrder.EigenvectorChartLowerOrderLimits
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Cross.EigenvectorChartCrossRightDiv

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators
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
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in

private lemma eigenvalue_pos
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    0 < i.fst.val :=
  (tensorResolvent_eigenvalue_mem_unit_interval (I := I) (M := M) g r s
    (tensorResolventEigenbasisVec_mem (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M)
        g r s) i)
    (by
      intro h_zero
      have h_norm :
          ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖ = 1 :=
        (tensorResolventEigenbasisVec_orthonormal (I := I) (M := M)
          (g := g) (r := r) (s := s)
          (tensorResolventL2_isCompactOperator (I := I) (M := M)
            g r s)).norm_eq_one i
      rw [h_zero, norm_zero] at h_norm
      exact one_ne_zero h_norm.symm)).1

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in

private lemma eLpNorm_lpClass_eq_ofReal_norm
    (α : M) (w : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
    eLpNorm ((w : EuclN → ℝ)) 2
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α))
      = ENNReal.ofReal ‖w‖ := by
  have h_eq : eLpNorm ((w : EuclN → ℝ)) 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) =
      eLpNorm ((w : EuclN → ℝ)) 2 (chartL2Measure (I := I) (M := M) α) := rfl
  rw [h_eq, Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top w)]

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in

private lemma partialLpLimit_eq_clm
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    partialLpLimit (I := I) (M := M) g r s i α P k =
      eigenvectorChartPartialCLM (I := I) (M := M) g r s α P k
        (eigenvectorResolvent (I := I) (M := M) g r s i) := by
  rw [partialLpLimit, eigenvectorChartPartialLp,
    smul_smul,
    mul_inv_cancel₀ (eigenvalue_pos (I := I) (M := M) g r s i).ne',
    one_smul]

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in

private lemma partialLpLimit_norm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    ‖partialLpLimit (I := I) (M := M) g r s i α P k‖ ≤
      ‖eigenvectorChartPartialCLM (I := I) (M := M) g r s α P k‖ *
        ‖eigenvectorResolvent (I := I) (M := M) g r s i‖ := by
  rw [partialLpLimit_eq_clm (I := I) (M := M) g r s i α P k]
  exact (eigenvectorChartPartialCLM (I := I) (M := M) g r s α P k).le_opNorm _

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 800000 in
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in

theorem partialLpLimit_eLpNorm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (i : TensorEigenIdx (I := I) (M := M) g r s),
      eLpNorm ((partialLpLimit (I := I) (M := M)
            g r s i α P k :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal
            (C * Real.sqrt (i.fst.val)) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖ := by
  classical
  refine ⟨‖eigenvectorChartPartialCLM (I := I) (M := M) g r s α P k‖,
    norm_nonneg (eigenvectorChartPartialCLM (I := I) (M := M) g r s α P k),
    fun i => ?_⟩
  rw [eLpNorm_lpClass_eq_ofReal_norm (I := I) (M := M) α
    (partialLpLimit (I := I) (M := M) g r s i α P k)]
  have h_bound :
      ‖partialLpLimit (I := I) (M := M) g r s i α P k‖ ≤
        ‖eigenvectorChartPartialCLM (I := I) (M := M) g r s α P k‖ *
            Real.sqrt (i.fst.val) *
          ‖tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M)
              g r s) i‖ := by
    calc ‖partialLpLimit (I := I) (M := M) g r s i α P k‖
        ≤ ‖eigenvectorChartPartialCLM (I := I) (M := M) g r s α P k‖ *
            ‖eigenvectorResolvent (I := I) (M := M) g r s i‖ :=
          partialLpLimit_norm_le (I := I) (M := M) g r s i α P k
      _ ≤ ‖eigenvectorChartPartialCLM (I := I) (M := M) g r s α P k‖ *
            (Real.sqrt (i.fst.val) *
              ‖tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖) :=
          mul_le_mul_of_nonneg_left
            (eigenvectorResolvent_h1Norm_le (I := I) (M := M)
              g r s i)
            (norm_nonneg (eigenvectorChartPartialCLM (I := I) (M := M)
              g r s α P k))
      _ = ‖eigenvectorChartPartialCLM (I := I) (M := M) g r s α P k‖ *
            Real.sqrt (i.fst.val) *
          ‖tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M)
              g r s) i‖ := by
          ring
  have h_factor_nn :
      0 ≤ ‖eigenvectorChartPartialCLM (I := I) (M := M) g r s α P k‖ *
        Real.sqrt (i.fst.val) :=
    mul_nonneg
      (norm_nonneg (eigenvectorChartPartialCLM (I := I) (M := M) g r s α P k))
      (Real.sqrt_nonneg _)
  rw [← ENNReal.ofReal_mul h_factor_nn]
  exact ENNReal.ofReal_le_ofReal h_bound

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in

private lemma cutoffPartialLpLimit_eq_clm
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    cutoffPartialLpLimit (I := I) (M := M) g r s i α P k =
      eigenvectorCutoffChartPartialCLM (I := I) (M := M) g r s α P k
        (eigenvectorResolvent (I := I) (M := M) g r s i) := by
  rw [cutoffPartialLpLimit,
    eigenvectorCutoffChartPartialLp, smul_smul,
    mul_inv_cancel₀ (eigenvalue_pos (I := I) (M := M) g r s i).ne',
    one_smul]

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in

private lemma cutoffPartialLpLimit_norm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    ‖cutoffPartialLpLimit (I := I) (M := M) g r s i α P k‖ ≤
      ‖eigenvectorCutoffChartPartialCLM (I := I) (M := M) g r s α P k‖ *
        ‖eigenvectorResolvent (I := I) (M := M) g r s i‖ := by
  rw [cutoffPartialLpLimit_eq_clm (I := I) (M := M) g r s i α P k]
  exact (eigenvectorCutoffChartPartialCLM (I := I) (M := M)
    g r s α P k).le_opNorm _

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 800000 in
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in

theorem cutoffPartialLpLimit_eLpNorm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (i : TensorEigenIdx (I := I) (M := M) g r s),
      eLpNorm ((cutoffPartialLpLimit (I := I) (M := M)
            g r s i α P k :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal
            (C * Real.sqrt (i.fst.val)) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖ := by
  classical
  refine ⟨‖eigenvectorCutoffChartPartialCLM (I := I) (M := M) g r s α P k‖,
    norm_nonneg (eigenvectorCutoffChartPartialCLM (I := I) (M := M)
      g r s α P k),
    fun i => ?_⟩
  rw [eLpNorm_lpClass_eq_ofReal_norm (I := I) (M := M) α
    (cutoffPartialLpLimit (I := I) (M := M) g r s i α P k)]
  have h_bound :
      ‖cutoffPartialLpLimit (I := I) (M := M) g r s i α P k‖ ≤
        ‖eigenvectorCutoffChartPartialCLM (I := I) (M := M) g r s α P k‖ *
            Real.sqrt (i.fst.val) *
          ‖tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M)
              g r s) i‖ := by
    calc ‖cutoffPartialLpLimit (I := I) (M := M) g r s i α P k‖
        ≤ ‖eigenvectorCutoffChartPartialCLM (I := I) (M := M)
              g r s α P k‖ *
            ‖eigenvectorResolvent (I := I) (M := M) g r s i‖ :=
          cutoffPartialLpLimit_norm_le (I := I) (M := M)
            g r s i α P k
      _ ≤ ‖eigenvectorCutoffChartPartialCLM (I := I) (M := M)
              g r s α P k‖ *
            (Real.sqrt (i.fst.val) *
              ‖tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖) :=
          mul_le_mul_of_nonneg_left
            (eigenvectorResolvent_h1Norm_le (I := I) (M := M)
              g r s i)
            (norm_nonneg (eigenvectorCutoffChartPartialCLM (I := I) (M := M)
              g r s α P k))
      _ = ‖eigenvectorCutoffChartPartialCLM (I := I) (M := M)
              g r s α P k‖ *
            Real.sqrt (i.fst.val) *
          ‖tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M)
              g r s) i‖ := by
          ring
  have h_factor_nn :
      0 ≤ ‖eigenvectorCutoffChartPartialCLM (I := I) (M := M)
          g r s α P k‖ * Real.sqrt (i.fst.val) :=
    mul_nonneg
      (norm_nonneg (eigenvectorCutoffChartPartialCLM (I := I) (M := M)
        g r s α P k))
      (Real.sqrt_nonneg _)
  rw [← ENNReal.ofReal_mul h_factor_nn]
  exact ENNReal.ofReal_le_ofReal h_bound

section ElaborationTest

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (α : M) (P : TensorCompIdx (E := E) r s)
  (P' : TensorCompIdx (E := E) r (s + 1))
  (k : Fin (Module.finrank ℝ E))

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
example :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (i : TensorEigenIdx (I := I) (M := M) g r s),
      eLpNorm ((partialLpLimit (I := I) (M := M)
            g r s i α P k :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal (C * Real.sqrt (i.fst.val)) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖ :=
  partialLpLimit_eLpNorm_le (I := I) (M := M) g r s α P k

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
example :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (i : TensorEigenIdx (I := I) (M := M) g r s),
      eLpNorm ((cutoffPartialLpLimit (I := I) (M := M)
            g r s i α P k :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal (C * Real.sqrt (i.fst.val)) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖ :=
  cutoffPartialLpLimit_eLpNorm_le (I := I) (M := M) g r s α P k

end ElaborationTest

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
