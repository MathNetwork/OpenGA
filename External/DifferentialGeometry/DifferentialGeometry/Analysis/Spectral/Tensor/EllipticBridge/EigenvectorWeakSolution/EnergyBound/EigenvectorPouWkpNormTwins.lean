import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.CovGrad.EigenvectorCovGradComponent
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Cutoff.CutoffChartComponentWkpNorm
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Multiplication.MultiplyQuantK
import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.IteratedSobolevQuant
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.EnergyBound.EigenvectorPouWkpNormTwinsChartComponentNormAggregate
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.EnergyBound.EigenvectorPouWkpNormTwinsChartWeakPartial
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.EnergyBound.EigenvectorPouWkpNormTwinsLeibnizCross
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.EnergyBound.EigenvectorPouWkpNormTwinsChristoffel

noncomputable section

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators Matrix
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

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

private lemma wkpNorm_sub_le
    {d : ℕ} [NeZero d] {k : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (hΩ : IsOpen Ω) {u v : EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : MemWkp (d := d) k 2 u Ω) (hv : MemWkp (d := d) k 2 v Ω) :
    iteratedWeakSobolevNorm (d := d) k 2 (fun y => u y - v y) Ω ≤
      iteratedWeakSobolevNorm (d := d) k 2 u Ω + iteratedWeakSobolevNorm (d := d) k 2 v Ω := by
  classical
  have h_fun : (fun y => u y - v y) = (fun y => u y + (fun y => - v y) y) := by
    funext y; ring
  rw [h_fun]
  have hv_neg : MemWkp (d := d) k 2 (fun y => - v y) Ω :=
    MemWkp.neg (d := d) (by norm_num) hΩ hv
  refine le_trans (wkpNorm_add_le (d := d) (by norm_num) hΩ hu hv_neg) ?_
  have h_neg_eq : iteratedWeakSobolevNorm (d := d) k 2 (fun y => - v y) Ω =
      iteratedWeakSobolevNorm (d := d) k 2 v Ω := by
    have h_smul : (fun y => - v y) = (fun y => (-1 : ℝ) * v y) := by
      funext y; ring
    rw [h_smul, wkpNorm_const_smul (d := d) (by norm_num) hΩ hv (-1)]
    simp
  rw [h_neg_eq]

omit [CompleteSpace E] in

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma eigenIdx_val_pos
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    0 < i.fst.val := by
  obtain ⟨u, hu_mem, hu_ne⟩ := i.fst.hasEigenvalue.exists_hasEigenvector
  have hu_in : u ∈ tensorResolventEigenspace
      (I := I) (M := M) g r s i.fst.val := hu_mem
  exact (tensorResolvent_eigenvalue_mem_unit_interval
    (I := I) (M := M) g r s hu_in hu_ne).1

section Unconditional

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

omit [CompleteSpace E] in
theorem eigenvectorVec_pou_wkpNorm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) (N : ℕ)
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) N 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β))
    (β : M) (Q : TensorCompIdx (E := E) r s) :
    ∃ C : ℝ, 0 ≤ C ∧
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) N 2
          (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
              (tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i) β Q :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) β)
        ≤ ENNReal.ofReal C *
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) N 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent (I := I) (M := M) g r s i))
                β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β) := by
  classical
  refine ⟨‖(i.fst.val)⁻¹‖, norm_nonneg _, ?_⟩
  exact (eigenvectorVec_pou_memWkp_and_wkpNorm_le (I := I) (M := M)
    g r s i N β Q (h_pou β Q)).2

omit [CompleteSpace E] in
theorem eigenvectorVec_pou_wkpNorm_le_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (N : ℕ)
    (h_pou : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) N 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β))
    (β : M) (Q : TensorCompIdx (E := E) r s) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) N 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (tensorResolventEigenbasisVec (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator (I := I) (M := M)
                    g r s) i) β Q :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β)
          ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * C) *
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) N 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent (I := I) (M := M) g r s i))
                  β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                  EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β) := by
  classical
  refine ⟨1, zero_le_one, fun i => ?_⟩
  have hμ_pos : 0 < i.fst.val := eigenIdx_val_pos (I := I) (M := M) g r s i
  have hμ_inv_nn : 0 ≤ (i.fst.val)⁻¹ := le_of_lt (inv_pos.mpr hμ_pos)
  have hμ_norm : ‖(i.fst.val)⁻¹‖ = (i.fst.val)⁻¹ := Real.norm_of_nonneg hμ_inv_nn
  have h_le := (eigenvectorVec_pou_memWkp_and_wkpNorm_le (I := I)
    (M := M) g r s i N β Q (h_pou i β Q)).2
  rw [mul_one]
  rwa [hμ_norm] at h_le

omit [CompleteSpace E] in
theorem eigenvectorCovGrad_pou_wkpNorm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) (K : ℕ)
    (h_pou_phi : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β))
    (β : M) (Q' : TensorCompIdx (E := E) r (s + 1)) :
    ∃ C : ℝ, 0 ≤ C ∧
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r (s + 1)
              (tensorCovGradL2Compl (I := I) (M := M) g r s
                (eigenvectorResolvent (I := I) (M := M) g r s i))
              β Q' : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) β)
        ≤ ENNReal.ofReal C *
          ((∑ Q : TensorCompIdx (E := E) r s,
              iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K + 1) 2
                (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                    (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                      (eigenvectorResolvent (I := I) (M := M)
                        g r s i))
                    β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                    EuclN → ℝ) y)
                (chartTargetEuclid (I := I) (M := M) β))
            + ∑ β' ∈ transportChartCenters (I := I) (M := M) β,
                ∑ Q : TensorCompIdx (E := E) r s,
                  iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K + 1) 2
                    (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                        (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                          (eigenvectorResolvent (I := I) (M := M)
                            g r s i))
                        β' Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) :
                        EuclN → ℝ) y)
                    (chartTargetEuclid (I := I) (M := M) β')) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) β with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) β
  set P : TensorCompIdx (E := E) r s := (Q'.1, Matrix.vecTail Q'.2) with hP_def
  set Saggr : ℝ≥0∞ := covGradAggregate (I := I) (M := M) g r s i K β
    with hSaggr_def
  obtain ⟨h1_mem, C1, hC1_nn, hC1_bd⟩ :=
    eigenvectorChartWeakPartial_memWkp_and_wkpNorm_le (I := I)
      (M := M) g r s i K h_pou_phi β P (Q'.2 0)
  obtain ⟨h2_mem, C2, hC2_nn, hC2_bd⟩ :=
    covGradPouLeibnizCrossLimit_memWkp_and_wkpNorm_le (I := I)
      (M := M) g r s i K h_pou_phi β P (Q'.2 0)
  obtain ⟨h3_mem, C3, hC3_nn, hC3_bd⟩ :=
    covGradChristoffelLimit_memWkp_and_wkpNorm_le (I := I) (M := M)
      g r s i K h_pou_phi β P (Q'.2 0)
  have h_sub_mem : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y =>
        eigenvectorChartWeakPartial (I := I) (M := M)
            g r s i β P (Q'.2 0) y
          - covGradPouLeibnizCrossLimit (I := I) (M := M)
              g r s i β P (Q'.2 0) y) Ω :=
    MemWkp.sub (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h1_mem h2_mem
  have h_sum_mem : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y =>
        eigenvectorChartWeakPartial (I := I) (M := M)
            g r s i β P (Q'.2 0) y
          - covGradPouLeibnizCrossLimit (I := I) (M := M)
              g r s i β P (Q'.2 0) y
          + covGradChristoffelLimit (I := I) (M := M)
              g r s i β P (Q'.2 0) y) Ω :=
    MemWkp.add (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_sub_mem h3_mem
  have h_sum_norm_le : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
      (fun y =>
        eigenvectorChartWeakPartial (I := I) (M := M)
            g r s i β P (Q'.2 0) y
          - covGradPouLeibnizCrossLimit (I := I) (M := M)
              g r s i β P (Q'.2 0) y
          + covGradChristoffelLimit (I := I) (M := M)
              g r s i β P (Q'.2 0) y) Ω
      ≤ ENNReal.ofReal (C1 + C2 + C3) * Saggr := by
    have h_tri : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
        (fun y =>
          eigenvectorChartWeakPartial (I := I) (M := M)
              g r s i β P (Q'.2 0) y
            - covGradPouLeibnizCrossLimit (I := I) (M := M)
                g r s i β P (Q'.2 0) y
            + covGradChristoffelLimit (I := I) (M := M)
                g r s i β P (Q'.2 0) y) Ω
        ≤ (iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (eigenvectorChartWeakPartial (I := I) (M := M)
                g r s i β P (Q'.2 0)) Ω
            + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
                (covGradPouLeibnizCrossLimit (I := I) (M := M)
                  g r s i β P (Q'.2 0)) Ω)
          + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (covGradChristoffelLimit (I := I) (M := M)
                g r s i β P (Q'.2 0)) Ω :=
      le_trans (wkpNorm_add_le (d := Module.finrank ℝ E)
        (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_sub_mem h3_mem)
        (add_le_add
          (wkpNorm_sub_le (d := Module.finrank ℝ E) hΩ_open h1_mem h2_mem)
          (le_refl (iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (covGradChristoffelLimit (I := I) (M := M)
              g r s i β P (Q'.2 0)) Ω)))
    refine le_trans h_tri ?_
    have h_each : (iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (eigenvectorChartWeakPartial (I := I) (M := M)
              g r s i β P (Q'.2 0)) Ω
          + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (covGradPouLeibnizCrossLimit (I := I) (M := M)
                g r s i β P (Q'.2 0)) Ω)
        + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (covGradChristoffelLimit (I := I) (M := M)
              g r s i β P (Q'.2 0)) Ω
        ≤ (ENNReal.ofReal C1 * Saggr + ENNReal.ofReal C2 * Saggr)
          + ENNReal.ofReal C3 * Saggr :=
      add_le_add (add_le_add hC1_bd hC2_bd) hC3_bd
    refine le_trans h_each (le_of_eq ?_)
    rw [ENNReal.ofReal_add (by positivity) hC3_nn,
      ENNReal.ofReal_add hC1_nn hC2_nn]
    ring
  have h_ae := eigenvectorCovGrad_pou_chartComponent_ae_eq
    (I := I) (M := M) g r s i β Q'
  have h_smul := Lp.coeFn_smul (i.fst.val)⁻¹
    (tensorL2ChartComponent (I := I) (M := M) g r (s + 1)
      (tensorCovGradL2Compl (I := I) (M := M) g r s
        (eigenvectorResolvent (I := I) (M := M) g r s i)) β Q')
  have h_scaled_ae : (fun y => (i.fst.val)⁻¹ *
        ((tensorL2ChartComponent (I := I) (M := M) g r (s + 1)
          (tensorCovGradL2Compl (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s i))
          β Q' : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
      =ᵐ[(volume : Measure EuclN).restrict Ω]
      (fun y =>
        eigenvectorChartWeakPartial (I := I) (M := M)
            g r s i β P (Q'.2 0) y
          - covGradPouLeibnizCrossLimit (I := I) (M := M)
              g r s i β P (Q'.2 0) y
          + covGradChristoffelLimit (I := I) (M := M)
              g r s i β P (Q'.2 0) y) := by
    have h_combined : (fun y => (i.fst.val)⁻¹ *
          ((tensorL2ChartComponent (I := I) (M := M) g r (s + 1)
            (tensorCovGradL2Compl (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q' : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
            EuclN → ℝ) y)
        =ᵐ[chartL2Measure (I := I) (M := M) β]
        (fun y =>
          eigenvectorChartWeakPartial (I := I) (M := M)
              g r s i β P (Q'.2 0) y
            - covGradPouLeibnizCrossLimit (I := I) (M := M)
                g r s i β P (Q'.2 0) y
            + covGradChristoffelLimit (I := I) (M := M)
                g r s i β P (Q'.2 0) y) := by
      filter_upwards [h_smul, h_ae] with y hy_smul hy_ae
      rw [← hy_ae, hy_smul, Pi.smul_apply, smul_eq_mul]
    exact h_combined
  have h_scaled_mem : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => (i.fst.val)⁻¹ *
        ((tensorL2ChartComponent (I := I) (M := M) g r (s + 1)
          (tensorCovGradL2Compl (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s i))
          β Q' : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) Ω :=
    (MemWkp_congr_ae (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_scaled_ae).mpr h_sum_mem
  have h_scaled_norm : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
      (fun y => (i.fst.val)⁻¹ *
        ((tensorL2ChartComponent (I := I) (M := M) g r (s + 1)
          (tensorCovGradL2Compl (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s i))
          β Q' : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) Ω
      ≤ ENNReal.ofReal (C1 + C2 + C3) * Saggr := by
    rw [wkpNorm_congr_ae (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_scaled_ae]
    exact h_sum_norm_le
  have hμ_ne : i.fst.val ≠ 0 := i.fst.val_ne_zero
  have h_chart_eq_scaled : (fun y => ((tensorL2ChartComponent (I := I) (M := M)
        g r (s + 1)
        (tensorCovGradL2Compl (I := I) (M := M) g r s
          (eigenvectorResolvent (I := I) (M := M) g r s i)) β Q' :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) =
      (fun y => i.fst.val * ((i.fst.val)⁻¹ *
        ((tensorL2ChartComponent (I := I) (M := M) g r (s + 1)
          (tensorCovGradL2Compl (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s i))
          β Q' : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)) := by
    funext y
    rw [mul_inv_cancel_left₀ hμ_ne]
  refine ⟨‖i.fst.val‖ * (C1 + C2 + C3),
    mul_nonneg (norm_nonneg _) (by positivity), ?_⟩
  rw [show ((∑ Q : TensorCompIdx (E := E) r s,
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K + 1) 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent (I := I) (M := M)
                    g r s i))
                β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β))
        + ∑ β' ∈ transportChartCenters (I := I) (M := M) β,
            ∑ Q : TensorCompIdx (E := E) r s,
              iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K + 1) 2
                (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                    (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                      (eigenvectorResolvent (I := I) (M := M)
                        g r s i))
                    β' Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) :
                    EuclN → ℝ) y)
                (chartTargetEuclid (I := I) (M := M) β')) = Saggr from rfl]
  rw [h_chart_eq_scaled]
  calc
    iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
        (fun y => i.fst.val * ((i.fst.val)⁻¹ *
          ((tensorL2ChartComponent (I := I) (M := M) g r (s + 1)
            (tensorCovGradL2Compl (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q' : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)) Ω
        = ‖i.fst.val‖ₑ *
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (fun y => (i.fst.val)⁻¹ *
                ((tensorL2ChartComponent (I := I) (M := M) g r (s + 1)
                  (tensorCovGradL2Compl (I := I) (M := M) g r s
                    (eigenvectorResolvent (I := I) (M := M)
                      g r s i))
                  β Q' : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                  EuclN → ℝ) y) Ω :=
      wkpNorm_const_smul (d := Module.finrank ℝ E)
        (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_scaled_mem i.fst.val
    _ ≤ ‖i.fst.val‖ₑ * (ENNReal.ofReal (C1 + C2 + C3) * Saggr) :=
      mul_le_mul_of_nonneg_left h_scaled_norm (zero_le _)
    _ = ENNReal.ofReal (‖i.fst.val‖ * (C1 + C2 + C3)) * Saggr := by
      rw [← mul_assoc, ← ofReal_norm (x := i.fst.val),
        ← ENNReal.ofReal_mul (norm_nonneg _)]

omit [CompleteSpace E] in
theorem eigenvectorCovGrad_pou_wkpNorm_le_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (K : ℕ)
    (h_pou_phi : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β))
    (β : M) (Q' : TensorCompIdx (E := E) r (s + 1)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r (s + 1)
                (tensorCovGradL2Compl (I := I) (M := M) g r s
                  (eigenvectorResolvent (I := I) (M := M) g r s i))
                β Q' : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β)
          ≤ ENNReal.ofReal C *
            ((∑ Q : TensorCompIdx (E := E) r s,
                iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K + 1) 2
                  (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                      (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                        (eigenvectorResolvent (I := I) (M := M)
                          g r s i))
                      β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                      EuclN → ℝ) y)
                  (chartTargetEuclid (I := I) (M := M) β))
              + ∑ β' ∈ transportChartCenters (I := I) (M := M) β,
                  ∑ Q : TensorCompIdx (E := E) r s,
                    iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K + 1) 2
                      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                            (eigenvectorResolvent (I := I) (M := M)
                              g r s i))
                          β' Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) :
                          EuclN → ℝ) y)
                      (chartTargetEuclid (I := I) (M := M) β')) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) β with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) β
  set P : TensorCompIdx (E := E) r s := (Q'.1, Matrix.vecTail Q'.2) with hP_def
  obtain ⟨D1, hD1_nn, hD1_bd⟩ :=
    eigenvectorChartWeakPartial_wkpNorm_le_uniform (I := I)
      (M := M) g r s K h_pou_phi β P (Q'.2 0)
  obtain ⟨D2, hD2_nn, hD2_bd⟩ :=
    covGradPouLeibnizCrossLimit_wkpNorm_le_uniform (I := I)
      (M := M) g r s K h_pou_phi β P (Q'.2 0)
  obtain ⟨D3, hD3_nn, hD3_bd⟩ :=
    covGradChristoffelLimit_wkpNorm_le_uniform (I := I) (M := M)
      g r s K h_pou_phi β P (Q'.2 0)
  refine ⟨D1 + D2 + D3, by positivity, fun i => ?_⟩
  set Saggr : ℝ≥0∞ := covGradAggregate (I := I) (M := M) g r s i K β
    with hSaggr_def
  have hμ_pos : 0 < i.fst.val := eigenIdx_val_pos (I := I) (M := M) g r s i
  have hμ_ne : i.fst.val ≠ 0 := ne_of_gt hμ_pos
  have hμ_inv_nn : 0 ≤ (i.fst.val)⁻¹ := le_of_lt (inv_pos.mpr hμ_pos)
  have h1_mem : MemWkp (d := Module.finrank ℝ E) K 2
      (eigenvectorChartWeakPartial (I := I) (M := M)
        g r s i β P (Q'.2 0))
      Ω :=
    (eigenvectorChartWeakPartial_memWkp_and_wkpNorm_le (I := I)
      (M := M) g r s i K (h_pou_phi i) β P (Q'.2 0)).1
  have h2_mem : MemWkp (d := Module.finrank ℝ E) K 2
      (covGradPouLeibnizCrossLimit (I := I) (M := M)
        g r s i β P (Q'.2 0))
      Ω :=
    (covGradPouLeibnizCrossLimit_memWkp_and_wkpNorm_le (I := I)
      (M := M) g r s i K (h_pou_phi i) β P (Q'.2 0)).1
  have h3_mem : MemWkp (d := Module.finrank ℝ E) K 2
      (covGradChristoffelLimit (I := I) (M := M)
        g r s i β P (Q'.2 0))
      Ω :=
    (covGradChristoffelLimit_memWkp_and_wkpNorm_le (I := I) (M := M)
      g r s i K (h_pou_phi i) β P (Q'.2 0)).1
  have hD1_bd_i := hD1_bd i
  have hD2_bd_i := hD2_bd i
  have hD3_bd_i := hD3_bd i
  rw [← hSaggr_def] at hD1_bd_i hD2_bd_i hD3_bd_i
  have h_sub_mem : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y =>
        eigenvectorChartWeakPartial (I := I) (M := M)
            g r s i β P (Q'.2 0) y
          - covGradPouLeibnizCrossLimit (I := I) (M := M)
              g r s i β P (Q'.2 0) y) Ω :=
    MemWkp.sub (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h1_mem h2_mem
  have h_sum_mem : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y =>
        eigenvectorChartWeakPartial (I := I) (M := M)
            g r s i β P (Q'.2 0) y
          - covGradPouLeibnizCrossLimit (I := I) (M := M)
              g r s i β P (Q'.2 0) y
          + covGradChristoffelLimit (I := I) (M := M)
              g r s i β P (Q'.2 0) y) Ω :=
    MemWkp.add (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_sub_mem h3_mem
  have h_sum_norm_le : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
      (fun y =>
        eigenvectorChartWeakPartial (I := I) (M := M)
            g r s i β P (Q'.2 0) y
          - covGradPouLeibnizCrossLimit (I := I) (M := M)
              g r s i β P (Q'.2 0) y
          + covGradChristoffelLimit (I := I) (M := M)
              g r s i β P (Q'.2 0) y) Ω
      ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * (D1 + D2 + D3)) * Saggr := by
    have h_tri : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
        (fun y =>
          eigenvectorChartWeakPartial (I := I) (M := M)
              g r s i β P (Q'.2 0) y
            - covGradPouLeibnizCrossLimit (I := I) (M := M)
                g r s i β P (Q'.2 0) y
            + covGradChristoffelLimit (I := I) (M := M)
                g r s i β P (Q'.2 0) y) Ω
        ≤ (iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (eigenvectorChartWeakPartial (I := I) (M := M)
                g r s i β P (Q'.2 0)) Ω
            + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
                (covGradPouLeibnizCrossLimit (I := I) (M := M)
                  g r s i β P (Q'.2 0)) Ω)
          + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (covGradChristoffelLimit (I := I) (M := M)
                g r s i β P (Q'.2 0)) Ω :=
      le_trans (wkpNorm_add_le (d := Module.finrank ℝ E)
        (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_sub_mem h3_mem)
        (add_le_add
          (wkpNorm_sub_le (d := Module.finrank ℝ E) hΩ_open h1_mem h2_mem)
          (le_refl (iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (covGradChristoffelLimit (I := I) (M := M)
              g r s i β P (Q'.2 0)) Ω)))
    refine le_trans h_tri ?_
    have h_each : (iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (eigenvectorChartWeakPartial (I := I) (M := M)
              g r s i β P (Q'.2 0)) Ω
          + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (covGradPouLeibnizCrossLimit (I := I) (M := M)
                g r s i β P (Q'.2 0)) Ω)
        + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (covGradChristoffelLimit (I := I) (M := M)
              g r s i β P (Q'.2 0)) Ω
        ≤ (ENNReal.ofReal ((i.fst.val)⁻¹ * D1) * Saggr
            + ENNReal.ofReal ((i.fst.val)⁻¹ * D2) * Saggr)
          + ENNReal.ofReal ((i.fst.val)⁻¹ * D3) * Saggr :=
      add_le_add (add_le_add hD1_bd_i hD2_bd_i) hD3_bd_i
    refine le_trans h_each (le_of_eq ?_)
    rw [← add_mul, ← add_mul,
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    ring_nf
  have h_ae := eigenvectorCovGrad_pou_chartComponent_ae_eq
    (I := I) (M := M) g r s i β Q'
  have h_smul := Lp.coeFn_smul (i.fst.val)⁻¹
    (tensorL2ChartComponent (I := I) (M := M) g r (s + 1)
      (tensorCovGradL2Compl (I := I) (M := M) g r s
        (eigenvectorResolvent (I := I) (M := M) g r s i)) β Q')
  have h_scaled_ae : (fun y => (i.fst.val)⁻¹ *
        ((tensorL2ChartComponent (I := I) (M := M) g r (s + 1)
          (tensorCovGradL2Compl (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s i))
          β Q' : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
      =ᵐ[(volume : Measure EuclN).restrict Ω]
      (fun y =>
        eigenvectorChartWeakPartial (I := I) (M := M)
            g r s i β P (Q'.2 0) y
          - covGradPouLeibnizCrossLimit (I := I) (M := M)
              g r s i β P (Q'.2 0) y
          + covGradChristoffelLimit (I := I) (M := M)
              g r s i β P (Q'.2 0) y) := by
    have h_combined : (fun y => (i.fst.val)⁻¹ *
          ((tensorL2ChartComponent (I := I) (M := M) g r (s + 1)
            (tensorCovGradL2Compl (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q' : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
            EuclN → ℝ) y)
        =ᵐ[chartL2Measure (I := I) (M := M) β]
        (fun y =>
          eigenvectorChartWeakPartial (I := I) (M := M)
              g r s i β P (Q'.2 0) y
            - covGradPouLeibnizCrossLimit (I := I) (M := M)
                g r s i β P (Q'.2 0) y
            + covGradChristoffelLimit (I := I) (M := M)
                g r s i β P (Q'.2 0) y) := by
      filter_upwards [h_smul, h_ae] with y hy_smul hy_ae
      rw [← hy_ae, hy_smul, Pi.smul_apply, smul_eq_mul]
    exact h_combined
  have h_scaled_mem : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => (i.fst.val)⁻¹ *
        ((tensorL2ChartComponent (I := I) (M := M) g r (s + 1)
          (tensorCovGradL2Compl (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s i))
          β Q' : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) Ω :=
    (MemWkp_congr_ae (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_scaled_ae).mpr h_sum_mem
  have h_scaled_norm : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
      (fun y => (i.fst.val)⁻¹ *
        ((tensorL2ChartComponent (I := I) (M := M) g r (s + 1)
          (tensorCovGradL2Compl (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s i))
          β Q' : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) Ω
      ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * (D1 + D2 + D3)) * Saggr := by
    rw [wkpNorm_congr_ae (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_scaled_ae]
    exact h_sum_norm_le
  have h_chart_eq_scaled : (fun y => ((tensorL2ChartComponent (I := I) (M := M)
        g r (s + 1)
        (tensorCovGradL2Compl (I := I) (M := M) g r s
          (eigenvectorResolvent (I := I) (M := M) g r s i)) β Q' :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) =
      (fun y => i.fst.val * ((i.fst.val)⁻¹ *
        ((tensorL2ChartComponent (I := I) (M := M) g r (s + 1)
          (tensorCovGradL2Compl (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s i))
          β Q' : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)) := by
    funext y
    rw [mul_inv_cancel_left₀ hμ_ne]
  rw [show ((∑ Q : TensorCompIdx (E := E) r s,
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K + 1) 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent (I := I) (M := M)
                    g r s i))
                β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β))
        + ∑ β' ∈ transportChartCenters (I := I) (M := M) β,
            ∑ Q : TensorCompIdx (E := E) r s,
              iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K + 1) 2
                (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                    (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                      (eigenvectorResolvent (I := I) (M := M)
                        g r s i))
                    β' Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) :
                    EuclN → ℝ) y)
                (chartTargetEuclid (I := I) (M := M) β')) = Saggr from rfl]
  rw [h_chart_eq_scaled]
  calc
    iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
        (fun y => i.fst.val * ((i.fst.val)⁻¹ *
          ((tensorL2ChartComponent (I := I) (M := M) g r (s + 1)
            (tensorCovGradL2Compl (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q' : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)) Ω
        = ‖i.fst.val‖ₑ *
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (fun y => (i.fst.val)⁻¹ *
                ((tensorL2ChartComponent (I := I) (M := M) g r (s + 1)
                  (tensorCovGradL2Compl (I := I) (M := M) g r s
                    (eigenvectorResolvent (I := I) (M := M)
                      g r s i))
                  β Q' : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                  EuclN → ℝ) y) Ω :=
      wkpNorm_const_smul (d := Module.finrank ℝ E)
        (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_scaled_mem i.fst.val
    _ ≤ ‖i.fst.val‖ₑ *
          (ENNReal.ofReal ((i.fst.val)⁻¹ * (D1 + D2 + D3)) * Saggr) :=
      mul_le_mul_of_nonneg_left h_scaled_norm (zero_le _)
    _ = ENNReal.ofReal (D1 + D2 + D3) * Saggr := by
      rw [← mul_assoc, ← ofReal_norm (x := i.fst.val),
        ← ENNReal.ofReal_mul (norm_nonneg _),
        Real.norm_of_nonneg (le_of_lt hμ_pos), ← mul_assoc,
        mul_inv_cancel₀ hμ_ne, one_mul]

end Unconditional

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
