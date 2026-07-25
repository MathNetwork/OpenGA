import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.RHS.ChartRHSBounds.EigenvectorChartRHSWkpNormEnergyBound
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.RHS.DifferentiatedRHS.EigenvectorChartRHSDiffWkpNorm
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.RHS.DifferentiatedRHS.EigenvectorChartRHSDiffWkpNormEnergyBoundFinsetSumScaledBound
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.RHS.DifferentiatedRHS.EigenvectorChartRHSDiffWkpNormEnergyBoundPerKEnergyBound

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

omit [CompleteSpace E] in
private lemma vec_norm_eq_one
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    ‖tensorResolventEigenbasisVec (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M)
          g r s) i‖ = 1 :=
  (tensorResolventEigenbasisVec_orthonormal (I := I) (M := M)
    (g := g) (r := r) (s := s)
    (tensorResolventL2_isCompactOperator (I := I) (M := M)
      g r s)).norm_eq_one i

omit [CompleteSpace E] in
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
      have h_norm := vec_norm_eq_one (I := I) (M := M) g r s i
      rw [h_zero, norm_zero] at h_norm
      exact one_ne_zero h_norm.symm)).1

omit [CompleteSpace E] in
private lemma eigenvalue_le_one
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    i.fst.val ≤ 1 :=
  (tensorResolvent_eigenvalue_mem_unit_interval (I := I) (M := M) g r s
    (tensorResolventEigenbasisVec_mem (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M)
        g r s) i)
    (by
      intro h_zero
      have h_norm := vec_norm_eq_one (I := I) (M := M) g r s i
      rw [h_zero, norm_zero] at h_norm
      exact one_ne_zero h_norm.symm)).2

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1000000 in

omit [CompleteSpace E] in
private lemma rhsZeroAggregate_le_energy_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (Ceig : ℝ) (hCeig_nn : 0 ≤ Ceig)
    (hCeig_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s) (K' : ℕ),
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
          (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
            g r s i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal Ceig *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖)
    (CresH : ℝ) (hCresH_nn : 0 ≤ CresH)
    (hCresH_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s) (K' : ℕ),
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K' + 1) 2
          (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
              (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                (eigenvectorResolvent (I := I) (M := M) g r s i))
              β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) β)
        ≤ ENNReal.ofReal CresH *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖)
    (CresL : ℝ) (hCresL_nn : 0 ≤ CresL)
    (hCresL_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s) (K' : ℕ),
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
              (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                (eigenvectorResolvent (I := I) (M := M) g r s i))
              β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) β)
        ≤ ENNReal.ofReal CresL *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖)
    (Cpar : ℝ) (hCpar_nn : 0 ≤ Cpar)
    (hCpar_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (P : TensorCompIdx (E := E) r s) (k : Fin (Module.finrank ℝ E)) (K' : ℕ),
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((partialLpLimit (I := I) (M := M)
              g r s i α P k :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal Cpar *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖)
    (Ccom : ℝ) (hCcom_nn : 0 ≤ Ccom)
    (hCcom_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (p : TensorCompIdx (E := E) r s) (K' : ℕ),
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((componentLpLimit (I := I) (M := M)
              g r s i α p :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal Ccom *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖)
    (CcR : ℝ) (hCcR_nn : 0 ≤ CcR)
    (hCcR_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (P : TensorCompIdx (E := E) r s) (K' : ℕ),
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((crossRightLimitComponent (I := I) (M := M)
              g r s i α P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal CcR *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖)
    (Ccut : ℝ) (hCcut_nn : 0 ≤ Ccut)
    (hCcut_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (P : TensorCompIdx (E := E) r s) (l : Fin (Module.finrank ℝ E)) (K' : ℕ),
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((cutoffPartialLpLimit (I := I) (M := M)
              g r s i α P l :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal Ccut *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (i : TensorEigenIdx (I := I) (M := M) g r s) (K' : ℕ),
        rhsZeroAggregate (I := I) (M := M) g r s i α P₀ K'
          ≤ ENNReal.ofReal C *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖ := by
  classical
  set TCard : ℕ → ℕ := fun β_ext =>
    (transportChartCenters (I := I) (M := M) α).card with hTCard_def
  set Cqtot : ℝ := (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) * CresH
    with hCqtot_def
  set Cmid_α : ℝ := (transportChartCenters (I := I) (M := M) α).sum fun β =>
        Cqtot + ((transportChartCenters (I := I) (M := M) β).card : ℝ) * Cqtot
    with hCmid_α_def
  set Clow_α : ℝ :=
    ((transportChartCenters (I := I) (M := M) α).card : ℝ) *
      ((Fintype.card (TensorCompIdx (E := E) r s) : ℝ) * CresL) with hClow_α_def
  set Cpar' : ℝ := (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) *
        ((Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * Cpar) with hCpar'_def
  set Ccom' : ℝ := (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) * Ccom
    with hCcom'_def
  set CcR' : ℝ := (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) * CcR
    with hCcR'_def
  set Ccut' : ℝ := (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) *
        ((Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * Ccut) with hCcut'_def
  set Cagg : ℝ := Ceig + Cmid_α + Clow_α + Cpar' + Ccom' + CcR' + Ccut'
    with hCagg_def
  have hCqtot_nn : 0 ≤ Cqtot := by
    have : (0 : ℝ) ≤ (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) := by
      exact_mod_cast Nat.zero_le _
    exact mul_nonneg this hCresH_nn
  have hCmid_α_nn : 0 ≤ Cmid_α := by
    refine Finset.sum_nonneg (fun β _ => ?_)
    have h1 : (0 : ℝ) ≤ ((transportChartCenters (I := I) (M := M) β).card : ℝ) := by
      exact_mod_cast Nat.zero_le _
    exact add_nonneg hCqtot_nn (mul_nonneg h1 hCqtot_nn)
  have hClow_α_nn : 0 ≤ Clow_α := by
    have hT : (0 : ℝ) ≤ ((transportChartCenters (I := I) (M := M) α).card : ℝ) := by
      exact_mod_cast Nat.zero_le _
    have hQ : (0 : ℝ) ≤ (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) := by
      exact_mod_cast Nat.zero_le _
    exact mul_nonneg hT (mul_nonneg hQ hCresL_nn)
  have hCpar'_nn : 0 ≤ Cpar' := by
    have hQ : (0 : ℝ) ≤ (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) := by
      exact_mod_cast Nat.zero_le _
    have hk : (0 : ℝ) ≤ (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) := by
      exact_mod_cast Nat.zero_le _
    exact mul_nonneg hQ (mul_nonneg hk hCpar_nn)
  have hCcom'_nn : 0 ≤ Ccom' := by
    have hQ : (0 : ℝ) ≤ (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) := by
      exact_mod_cast Nat.zero_le _
    exact mul_nonneg hQ hCcom_nn
  have hCcR'_nn : 0 ≤ CcR' := by
    have hQ : (0 : ℝ) ≤ (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) := by
      exact_mod_cast Nat.zero_le _
    exact mul_nonneg hQ hCcR_nn
  have hCcut'_nn : 0 ≤ Ccut' := by
    have hQ : (0 : ℝ) ≤ (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) := by
      exact_mod_cast Nat.zero_le _
    have hk : (0 : ℝ) ≤ (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) := by
      exact_mod_cast Nat.zero_le _
    exact mul_nonneg hQ (mul_nonneg hk hCcut_nn)
  have hCagg_nn : 0 ≤ Cagg := by
    refine add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg
      (add_nonneg ?_ hCmid_α_nn) hClow_α_nn) hCpar'_nn) hCcom'_nn) hCcR'_nn) hCcut'_nn
    exact hCeig_nn
  refine ⟨Cagg, hCagg_nn, fun i K' => ?_⟩
  set Rhs : ℝ≥0∞ := ENNReal.ofReal
      ‖tensorResolventEigenbasisVec (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M)
          g r s) i‖ with hRhs_def
  have hS1 :
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
          (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
            g r s i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal Ceig * Rhs := hCeig_bd i K'
  have hS2_inner : ∀ β ∈ transportChartCenters (I := I) (M := M) α,
      ((∑ Q : TensorCompIdx (E := E) r s,
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K' + 1) 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent (I := I) (M := M) g r s i))
                  β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                  EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β))
        + ∑ β' ∈ transportChartCenters (I := I) (M := M) β,
            ∑ Q : TensorCompIdx (E := E) r s,
              iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K' + 1) 2
                (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                    (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                      (eigenvectorResolvent (I := I) (M := M) g r s i))
                    β' Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) :
                    EuclN → ℝ) y)
                (chartTargetEuclid (I := I) (M := M) β'))
        ≤ ENNReal.ofReal
            (Cqtot + ((transportChartCenters (I := I) (M := M) β).card : ℝ) *
              Cqtot) * Rhs := by
    intro β _hβ
    have h_inner_β :
        (∑ Q : TensorCompIdx (E := E) r s,
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K' + 1) 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent (I := I) (M := M) g r s i))
                  β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                  EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β))
          ≤ ENNReal.ofReal Cqtot * Rhs := by
      have h_each : ∀ Q ∈ (Finset.univ : Finset (TensorCompIdx (E := E) r s)),
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K' + 1) 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent (I := I) (M := M) g r s i))
                  β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                  EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β)
            ≤ ENNReal.ofReal CresH * Rhs := fun Q _hQ => hCresH_bd i β Q K'
      have h_sum := finsetSum_eNNReal_ofReal_mul_le
        (Finset.univ : Finset (TensorCompIdx (E := E) r s))
        (fun Q => iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K' + 1) 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent (I := I) (M := M) g r s i))
                β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β))
        (fun _Q => CresH) Rhs (fun _ _ => hCresH_nn) h_each
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h_sum
      exact h_sum.trans_eq (by rw [hCqtot_def])
    have h_inner_β' :
        (∑ β' ∈ transportChartCenters (I := I) (M := M) β,
          ∑ Q : TensorCompIdx (E := E) r s,
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K' + 1) 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent (I := I) (M := M) g r s i))
                  β' Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) :
                  EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β'))
        ≤ ENNReal.ofReal
            (((transportChartCenters (I := I) (M := M) β).card : ℝ) * Cqtot) *
            Rhs := by
      have h_perβ' : ∀ β' ∈ transportChartCenters (I := I) (M := M) β,
          (∑ Q : TensorCompIdx (E := E) r s,
              iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K' + 1) 2
                (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                    (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                      (eigenvectorResolvent (I := I) (M := M) g r s i))
                    β' Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) :
                    EuclN → ℝ) y)
                (chartTargetEuclid (I := I) (M := M) β'))
            ≤ ENNReal.ofReal Cqtot * Rhs := by
        intro β' _hβ'
        have h_each : ∀ Q ∈ (Finset.univ : Finset (TensorCompIdx (E := E) r s)),
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K' + 1) 2
                (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                    (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                      (eigenvectorResolvent (I := I) (M := M) g r s i))
                    β' Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) :
                    EuclN → ℝ) y)
                (chartTargetEuclid (I := I) (M := M) β')
              ≤ ENNReal.ofReal CresH * Rhs := fun Q _hQ => hCresH_bd i β' Q K'
        have h_sum := finsetSum_eNNReal_ofReal_mul_le
          (Finset.univ : Finset (TensorCompIdx (E := E) r s))
          (fun Q => iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K' + 1) 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent (I := I) (M := M) g r s i))
                  β' Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) :
                  EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β'))
          (fun _Q => CresH) Rhs (fun _ _ => hCresH_nn) h_each
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h_sum
        exact h_sum.trans_eq (by rw [hCqtot_def])
      have h_sum := finsetSum_eNNReal_ofReal_mul_le
        (transportChartCenters (I := I) (M := M) β)
        (fun β' => ∑ Q : TensorCompIdx (E := E) r s,
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K' + 1) 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent (I := I) (M := M) g r s i))
                  β' Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) :
                  EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β'))
        (fun _β' => Cqtot) Rhs (fun _ _ => hCqtot_nn) h_perβ'
      rw [Finset.sum_const, nsmul_eq_mul] at h_sum
      exact h_sum
    have h_total :=
      add_le_add h_inner_β h_inner_β'
    refine h_total.trans (le_of_eq ?_)
    have hN : 0 ≤ ((transportChartCenters (I := I) (M := M) β).card : ℝ) := by
      exact_mod_cast Nat.zero_le _
    rw [ENNReal.ofReal_add hCqtot_nn (mul_nonneg hN hCqtot_nn), add_mul]
  have hS2 :
      (∑ β ∈ transportChartCenters (I := I) (M := M) α,
        ((∑ Q : TensorCompIdx (E := E) r s,
              iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K' + 1) 2
                (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                    (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                      (eigenvectorResolvent (I := I) (M := M) g r s i))
                    β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                    EuclN → ℝ) y)
                (chartTargetEuclid (I := I) (M := M) β))
          + ∑ β' ∈ transportChartCenters (I := I) (M := M) β,
              ∑ Q : TensorCompIdx (E := E) r s,
                iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K' + 1) 2
                  (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                      (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                        (eigenvectorResolvent (I := I) (M := M)
                          g r s i))
                      β' Q :
                      Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) :
                      EuclN → ℝ) y)
                  (chartTargetEuclid (I := I) (M := M) β')))
      ≤ ENNReal.ofReal Cmid_α * Rhs := by
    have h_perβ_nn :
        ∀ β ∈ transportChartCenters (I := I) (M := M) α,
          0 ≤ Cqtot +
              ((transportChartCenters (I := I) (M := M) β).card : ℝ) * Cqtot := by
      intro β _hβ
      have hN : (0 : ℝ) ≤
          ((transportChartCenters (I := I) (M := M) β).card : ℝ) := by
        exact_mod_cast Nat.zero_le _
      exact add_nonneg hCqtot_nn (mul_nonneg hN hCqtot_nn)
    have h_sum := finsetSum_eNNReal_ofReal_mul_le
      (transportChartCenters (I := I) (M := M) α)
      (fun β => (∑ Q : TensorCompIdx (E := E) r s,
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K' + 1) 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent (I := I) (M := M) g r s i))
                  β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                  EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β))
        + ∑ β' ∈ transportChartCenters (I := I) (M := M) β,
            ∑ Q : TensorCompIdx (E := E) r s,
              iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K' + 1) 2
                (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                    (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                      (eigenvectorResolvent (I := I) (M := M)
                        g r s i))
                    β' Q :
                    Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) :
                    EuclN → ℝ) y)
                (chartTargetEuclid (I := I) (M := M) β'))
      (fun β => Cqtot +
        ((transportChartCenters (I := I) (M := M) β).card : ℝ) * Cqtot)
      Rhs h_perβ_nn hS2_inner
    exact h_sum.trans_eq (by rw [hCmid_α_def])
  have hS3 :
      (∑ β ∈ transportChartCenters (I := I) (M := M) α,
        ∑ Q : TensorCompIdx (E := E) r s,
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent (I := I) (M := M) g r s i))
                β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β))
      ≤ ENNReal.ofReal Clow_α * Rhs := by
    have h_perβ : ∀ β ∈ transportChartCenters (I := I) (M := M) α,
        (∑ Q : TensorCompIdx (E := E) r s,
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent (I := I) (M := M) g r s i))
                  β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                  EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β))
          ≤ ENNReal.ofReal
              ((Fintype.card (TensorCompIdx (E := E) r s) : ℝ) * CresL) * Rhs := by
      intro β _hβ
      have h_each : ∀ Q ∈ (Finset.univ : Finset (TensorCompIdx (E := E) r s)),
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent (I := I) (M := M) g r s i))
                  β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                  EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β)
            ≤ ENNReal.ofReal CresL * Rhs := fun Q _hQ => hCresL_bd i β Q K'
      have h_sum := finsetSum_eNNReal_ofReal_mul_le
        (Finset.univ : Finset (TensorCompIdx (E := E) r s))
        (fun Q => iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent (I := I) (M := M) g r s i))
                β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β))
        (fun _Q => CresL) Rhs (fun _ _ => hCresL_nn) h_each
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h_sum
      exact h_sum
    have hQ_nn : (0 : ℝ) ≤
        (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) * CresL := by
      have hQ : (0 : ℝ) ≤ (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) := by
        exact_mod_cast Nat.zero_le _
      exact mul_nonneg hQ hCresL_nn
    have h_sum := finsetSum_eNNReal_ofReal_mul_le
      (transportChartCenters (I := I) (M := M) α)
      (fun β => ∑ Q : TensorCompIdx (E := E) r s,
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent (I := I) (M := M) g r s i))
                β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β))
      (fun _β => (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) * CresL)
      Rhs (fun _ _ => hQ_nn) h_perβ
    rw [Finset.sum_const, nsmul_eq_mul] at h_sum
    exact h_sum.trans_eq (by rw [hClow_α_def])
  have hS4 :
      (∑ P : TensorCompIdx (E := E) r s,
        ∑ k : Fin (Module.finrank ℝ E),
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
            (fun y => ((partialLpLimit (I := I) (M := M)
                g r s i α P k :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α))
      ≤ ENNReal.ofReal Cpar' * Rhs := by
    have h_perP : ∀ P ∈ (Finset.univ : Finset (TensorCompIdx (E := E) r s)),
        (∑ k : Fin (Module.finrank ℝ E),
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
              (fun y => ((partialLpLimit (I := I) (M := M)
                  g r s i α P k :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal
              ((Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * Cpar) * Rhs := by
      intro P _hP
      have h_each : ∀ k ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ E))),
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
              (fun y => ((partialLpLimit (I := I) (M := M)
                  g r s i α P k :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal Cpar * Rhs := fun k _hk => hCpar_bd i P k K'
      have h_sum := finsetSum_eNNReal_ofReal_mul_le
        (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
        (fun k => iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
            (fun y => ((partialLpLimit (I := I) (M := M)
                g r s i α P k :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α))
        (fun _k => Cpar) Rhs (fun _ _ => hCpar_nn) h_each
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h_sum
      exact h_sum
    have hk_nn : (0 : ℝ) ≤
        (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * Cpar := by
      have hk : (0 : ℝ) ≤ (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) := by
        exact_mod_cast Nat.zero_le _
      exact mul_nonneg hk hCpar_nn
    have h_sum := finsetSum_eNNReal_ofReal_mul_le
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun P => ∑ k : Fin (Module.finrank ℝ E),
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
            (fun y => ((partialLpLimit (I := I) (M := M)
                g r s i α P k :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α))
      (fun _P => (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * Cpar)
      Rhs (fun _ _ => hk_nn) h_perP
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h_sum
    exact h_sum.trans_eq (by rw [hCpar'_def])
  have hS5 :
      (∑ p : TensorCompIdx (E := E) r s,
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((componentLpLimit (I := I) (M := M)
              g r s i α p :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
            EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α))
      ≤ ENNReal.ofReal Ccom' * Rhs := by
    have h_each : ∀ p ∈ (Finset.univ : Finset (TensorCompIdx (E := E) r s)),
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
            (fun y => ((componentLpLimit (I := I) (M := M)
                g r s i α p :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal Ccom * Rhs := fun p _hp => hCcom_bd i p K'
    have h_sum := finsetSum_eNNReal_ofReal_mul_le
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun p => iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((componentLpLimit (I := I) (M := M)
              g r s i α p :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
            EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α))
      (fun _p => Ccom) Rhs (fun _ _ => hCcom_nn) h_each
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h_sum
    exact h_sum.trans_eq (by rw [hCcom'_def])
  have hS6 :
      (∑ P : TensorCompIdx (E := E) r s,
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((crossRightLimitComponent (I := I) (M := M)
              g r s i α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
            EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α))
      ≤ ENNReal.ofReal CcR' * Rhs := by
    have h_each : ∀ P ∈ (Finset.univ : Finset (TensorCompIdx (E := E) r s)),
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
            (fun y => ((crossRightLimitComponent (I := I) (M := M)
                g r s i α P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal CcR * Rhs := fun P _hP => hCcR_bd i P K'
    have h_sum := finsetSum_eNNReal_ofReal_mul_le
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun P => iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((crossRightLimitComponent (I := I) (M := M)
              g r s i α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
            EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α))
      (fun _P => CcR) Rhs (fun _ _ => hCcR_nn) h_each
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h_sum
    exact h_sum.trans_eq (by rw [hCcR'_def])
  have hS7 :
      (∑ P : TensorCompIdx (E := E) r s,
        ∑ l : Fin (Module.finrank ℝ E),
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
            (fun y => ((cutoffPartialLpLimit (I := I) (M := M)
                g r s i α P l :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α))
      ≤ ENNReal.ofReal Ccut' * Rhs := by
    have h_perP : ∀ P ∈ (Finset.univ : Finset (TensorCompIdx (E := E) r s)),
        (∑ l : Fin (Module.finrank ℝ E),
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
              (fun y => ((cutoffPartialLpLimit (I := I) (M := M)
                  g r s i α P l :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal
              ((Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * Ccut) * Rhs := by
      intro P _hP
      have h_each : ∀ l ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ E))),
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
              (fun y => ((cutoffPartialLpLimit (I := I) (M := M)
                  g r s i α P l :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal Ccut * Rhs := fun l _hl => hCcut_bd i P l K'
      have h_sum := finsetSum_eNNReal_ofReal_mul_le
        (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
        (fun l => iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
            (fun y => ((cutoffPartialLpLimit (I := I) (M := M)
                g r s i α P l :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α))
        (fun _l => Ccut) Rhs (fun _ _ => hCcut_nn) h_each
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h_sum
      exact h_sum
    have hk_nn : (0 : ℝ) ≤
        (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * Ccut := by
      have hk : (0 : ℝ) ≤ (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) := by
        exact_mod_cast Nat.zero_le _
      exact mul_nonneg hk hCcut_nn
    have h_sum := finsetSum_eNNReal_ofReal_mul_le
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun P => ∑ l : Fin (Module.finrank ℝ E),
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
            (fun y => ((cutoffPartialLpLimit (I := I) (M := M)
                g r s i α P l :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α))
      (fun _P => (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * Ccut)
      Rhs (fun _ _ => hk_nn) h_perP
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h_sum
    exact h_sum.trans_eq (by rw [hCcut'_def])
  rw [rhsZeroAggregate]
  have hp1 : 0 ≤ Ceig + Cmid_α := add_nonneg hCeig_nn hCmid_α_nn
  have hp2 : 0 ≤ Ceig + Cmid_α + Clow_α := add_nonneg hp1 hClow_α_nn
  have hp3 : 0 ≤ Ceig + Cmid_α + Clow_α + Cpar' := add_nonneg hp2 hCpar'_nn
  have hp4 : 0 ≤ Ceig + Cmid_α + Clow_α + Cpar' + Ccom' :=
    add_nonneg hp3 hCcom'_nn
  have hp5 : 0 ≤ Ceig + Cmid_α + Clow_α + Cpar' + Ccom' + CcR' :=
    add_nonneg hp4 hCcR'_nn
  have h_expand :
      ENNReal.ofReal Cagg
        = ENNReal.ofReal Ceig + ENNReal.ofReal Cmid_α + ENNReal.ofReal Clow_α
          + ENNReal.ofReal Cpar' + ENNReal.ofReal Ccom' + ENNReal.ofReal CcR'
          + ENNReal.ofReal Ccut' := by
    rw [hCagg_def, ENNReal.ofReal_add hp5 hCcut'_nn,
      ENNReal.ofReal_add hp4 hCcR'_nn,
      ENNReal.ofReal_add hp3 hCcom'_nn,
      ENNReal.ofReal_add hp2 hCpar'_nn,
      ENNReal.ofReal_add hp1 hClow_α_nn,
      ENNReal.ofReal_add hCeig_nn hCmid_α_nn]
  rw [h_expand, add_mul, add_mul, add_mul, add_mul, add_mul, add_mul]
  refine add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
    (add_le_add ?_ hS2) hS3) hS4) hS5) hS6) hS7
  exact hS1

omit [CompleteSpace E] in
private lemma diffRHSHead_le_energy_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (Citer : ℝ) (hCiter_nn : 0 ≤ Citer)
    (hCiter_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s) (j : ℕ)
      (idx : Fin j → Fin (Module.finrank ℝ E)) (K' : ℕ),
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (2 + K') 2
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ j idx)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal Citer *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖)
    (i : TensorEigenIdx (I := I) (M := M) g r s) (m K : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E)) :
    diffRHSHead (I := I) (M := M) g r s i α P₀ m K l
      ≤ ENNReal.ofReal
          (((Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) + 1) * Citer) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M)
              g r s) i‖ := by
  classical
  set Rhs : ℝ≥0∞ := ENNReal.ofReal
      ‖tensorResolventEigenbasisVec (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M)
          g r s) i‖ with hRhs_def
  rw [diffRHSHead]
  have h_each :
      ∀ a ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ E))),
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (2 + K) 2
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
          (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal Citer * Rhs := fun a _ha =>
    hCiter_bd i (m + 1) (Fin.cons a (Fin.init l)) K
  have h_first :
      (∑ a : Fin (Module.finrank ℝ E),
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (2 + K) 2
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
            (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal
            ((Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * Citer) * Rhs := by
    have h_sum := finsetSum_eNNReal_ofReal_mul_le
      (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
      (fun a => iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (2 + K) 2
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
          (chartTargetEuclid (I := I) (M := M) α))
      (fun _ => Citer) Rhs (fun _ _ => hCiter_nn) h_each
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h_sum
    exact h_sum
  have h_second :
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (2 + K) 2
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ m (Fin.init l))
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal Citer * Rhs := hCiter_bd i m (Fin.init l) K
  have h_total :
      (∑ a : Fin (Module.finrank ℝ E),
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (2 + K) 2
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
            (chartTargetEuclid (I := I) (M := M) α))
        + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (2 + K) 2
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s i α P₀ m (Fin.init l))
            (chartTargetEuclid (I := I) (M := M) α)
      ≤ ENNReal.ofReal
          ((Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * Citer) * Rhs
        + ENNReal.ofReal Citer * Rhs := add_le_add h_first h_second
  refine h_total.trans (le_of_eq ?_)
  have hQ_nn : (0 : ℝ) ≤
      (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * Citer := by
    have hQ : (0 : ℝ) ≤ (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) := by
      exact_mod_cast Nat.zero_le _
    exact mul_nonneg hQ hCiter_nn
  rw [← add_mul, ← ENNReal.ofReal_add hQ_nn hCiter_nn]
  congr 2
  ring

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1000000 in

omit [CompleteSpace E] in
theorem diffRHSAggregate_le_energy_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin m → Fin (Module.finrank ℝ E))
    (h_eig : ∃ Ceig : ℝ, 0 ≤ Ceig ∧
      ∀ (i : TensorEigenIdx (I := I) (M := M) g r s) (K' : ℕ),
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
            (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
              g r s i α P₀)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal Ceig *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖)
    (h_resHigh : ∃ CresH : ℝ, 0 ≤ CresH ∧
      ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
        (β : M) (Q : TensorCompIdx (E := E) r s) (K' : ℕ),
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K' + 1) 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent (I := I) (M := M) g r s i))
                β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β)
          ≤ ENNReal.ofReal CresH *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖)
    (h_resLow : ∃ CresL : ℝ, 0 ≤ CresL ∧
      ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
        (β : M) (Q : TensorCompIdx (E := E) r s) (K' : ℕ),
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent (I := I) (M := M) g r s i))
                β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β)
          ≤ ENNReal.ofReal CresL *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖)
    (h_partial : ∃ Cpar : ℝ, 0 ≤ Cpar ∧
      ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
        (P : TensorCompIdx (E := E) r s) (k : Fin (Module.finrank ℝ E)) (K' : ℕ),
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
            (fun y => ((partialLpLimit (I := I) (M := M)
                g r s i α P k :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal Cpar *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖)
    (h_component : ∃ Ccom : ℝ, 0 ≤ Ccom ∧
      ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
        (p : TensorCompIdx (E := E) r s) (K' : ℕ),
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
            (fun y => ((componentLpLimit (I := I) (M := M)
                g r s i α p :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal Ccom *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖)
    (h_crossRight : ∃ CcR : ℝ, 0 ≤ CcR ∧
      ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
        (P : TensorCompIdx (E := E) r s) (K' : ℕ),
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
            (fun y => ((crossRightLimitComponent (I := I) (M := M)
                g r s i α P :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal CcR *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖)
    (h_cutoff : ∃ Ccut : ℝ, 0 ≤ Ccut ∧
      ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
        (P : TensorCompIdx (E := E) r s) (l : Fin (Module.finrank ℝ E)) (K' : ℕ),
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
            (fun y => ((cutoffPartialLpLimit (I := I) (M := M)
                g r s i α P l :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal Ccut *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖)
    (h_iter : ∃ Citer : ℝ, 0 ≤ Citer ∧
      ∀ (i : TensorEigenIdx (I := I) (M := M) g r s) (j : ℕ)
        (idx : Fin j → Fin (Module.finrank ℝ E)) (K' : ℕ),
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (2 + K') 2
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s i α P₀ j idx)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal Citer *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        diffRHSAggregate (I := I) (M := M) g r s i α P₀ m K l
          ≤ ENNReal.ofReal (C * (i.fst.val)⁻¹) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖ := by
  classical
  obtain ⟨Ceig, hCeig_nn, hCeig_bd⟩ := h_eig
  obtain ⟨CresH, hCresH_nn, hCresH_bd⟩ := h_resHigh
  obtain ⟨CresL, hCresL_nn, hCresL_bd⟩ := h_resLow
  obtain ⟨Cpar, hCpar_nn, hCpar_bd⟩ := h_partial
  obtain ⟨Ccom, hCcom_nn, hCcom_bd⟩ := h_component
  obtain ⟨CcR, hCcR_nn, hCcR_bd⟩ := h_crossRight
  obtain ⟨Ccut, hCcut_nn, hCcut_bd⟩ := h_cutoff
  obtain ⟨Citer, hCiter_nn, hCiter_bd⟩ := h_iter
  obtain ⟨Cbase, hCbase_nn, hCbase_bd⟩ :=
    rhsZeroAggregate_le_energy_uniform (I := I) (M := M)
      g r s α P₀
      Ceig hCeig_nn hCeig_bd
      CresH hCresH_nn hCresH_bd
      CresL hCresL_nn hCresL_bd
      Cpar hCpar_nn hCpar_bd
      Ccom hCcom_nn hCcom_bd
      CcR hCcR_nn hCcR_bd
      Ccut hCcut_nn hCcut_bd
  set Chead : ℝ := ((Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) + 1) * Citer
    with hChead_def
  have hChead_nn : 0 ≤ Chead := by
    have hQ : (0 : ℝ) ≤ (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) := by
      exact_mod_cast Nat.zero_le _
    have : (0 : ℝ) ≤ (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) + 1 := by
      linarith
    exact mul_nonneg this hCiter_nn
  set Ctotal : ℝ := Cbase + (m : ℝ) * Chead with hCtotal_def
  have hCtotal_nn : 0 ≤ Ctotal := by
    have hm : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.zero_le _
    exact add_nonneg hCbase_nn (mul_nonneg hm hChead_nn)
  refine ⟨Ctotal, hCtotal_nn, fun i => ?_⟩
  have hμ_pos : 0 < i.fst.val :=
    eigenvalue_pos (I := I) (M := M) g r s i
  have hμ_le_one : i.fst.val ≤ 1 :=
    eigenvalue_le_one (I := I) (M := M) g r s i
  have hμ_inv_nn : 0 ≤ (i.fst.val)⁻¹ := le_of_lt (inv_pos.mpr hμ_pos)
  have hμ_inv_ge_one : (1 : ℝ) ≤ (i.fst.val)⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hμ_pos]; simpa using hμ_le_one
  set Rhs : ℝ≥0∞ := ENNReal.ofReal
      ‖tensorResolventEigenbasisVec (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M)
          g r s) i‖ with hRhs_def
  have h_bare : ∀ (m' K' : ℕ) (l' : Fin m' → Fin (Module.finrank ℝ E)),
      diffRHSAggregate (I := I) (M := M) g r s i α P₀ m' K' l'
        ≤ ENNReal.ofReal (Cbase + (m' : ℝ) * Chead) * Rhs := by
    intro m' K' l'
    induction m' generalizing K' with
    | zero =>
        rw [show diffRHSAggregate (I := I) (M := M)
              g r s i α P₀ 0 K' l' =
            rhsZeroAggregate (I := I) (M := M)
              g r s i α P₀ K' from rfl]
        have h_base := hCbase_bd i K'
        have h_simp : (Cbase + ((0 : ℕ) : ℝ) * Chead) = Cbase := by
          simp
        rw [h_simp]
        exact h_base
    | succ m'' ih =>
        rw [show diffRHSAggregate (I := I) (M := M)
              g r s i α P₀ (m'' + 1) K' l' =
            diffRHSHead (I := I) (M := M) g r s i α P₀ m'' K' l' +
              diffRHSAggregate (I := I) (M := M)
                g r s i α P₀ m'' (K' + 1) (Fin.init l') from rfl]
        have h_head := diffRHSHead_le_energy_uniform (I := I) (M := M)
          g r s α P₀ Citer hCiter_nn hCiter_bd i m'' K' l'
        have h_rec := ih (K' + 1) (Fin.init l')
        have h_combine :
            diffRHSHead (I := I) (M := M) g r s i α P₀ m'' K' l'
              + diffRHSAggregate (I := I) (M := M)
                  g r s i α P₀ m'' (K' + 1) (Fin.init l')
            ≤ ENNReal.ofReal Chead * Rhs
                + ENNReal.ofReal (Cbase + (m'' : ℝ) * Chead) * Rhs :=
          add_le_add h_head h_rec
        refine h_combine.trans (le_of_eq ?_)
        have hCprev_nn : 0 ≤ Cbase + (m'' : ℝ) * Chead := by
          have hm'' : (0 : ℝ) ≤ (m'' : ℝ) := by exact_mod_cast Nat.zero_le _
          exact add_nonneg hCbase_nn (mul_nonneg hm'' hChead_nn)
        rw [← add_mul, ← ENNReal.ofReal_add hChead_nn hCprev_nn]
        congr 2
        push_cast
        ring
  have h_at_m := h_bare m K l
  refine h_at_m.trans ?_
  gcongr
  nlinarith [hCtotal_nn, hμ_inv_ge_one]

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
