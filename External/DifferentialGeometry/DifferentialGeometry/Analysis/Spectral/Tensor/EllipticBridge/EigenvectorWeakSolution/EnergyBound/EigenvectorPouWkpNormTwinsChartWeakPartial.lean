import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.CovGrad.EigenvectorCovGradComponent
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Cutoff.CutoffChartComponentWkpNorm
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Multiplication.MultiplyQuantK
import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.IteratedSobolevQuant
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.EnergyBound.EigenvectorPouWkpNormTwinsChartComponentNormAggregate

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

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

omit [CompleteSpace E] in
lemma eigenvectorChartWeakPartial_memWkp_and_wkpNorm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) (K : ℕ)
    (h_pou_phi : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β))
    (β : M) (P : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    MemWkp (d := Module.finrank ℝ E) K 2
        (eigenvectorChartWeakPartial (I := I) (M := M)
          g r s i β P k)
        (chartTargetEuclid (I := I) (M := M) β) ∧
      ∃ C : ℝ, 0 ≤ C ∧
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (eigenvectorChartWeakPartial (I := I) (M := M)
              g r s i β P k)
            (chartTargetEuclid (I := I) (M := M) β)
          ≤ ENNReal.ofReal C *
            covGradAggregate (I := I) (M := M) g r s i K β := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) β with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) β
  obtain ⟨hu, hu_norm⟩ := eigenvectorVec_pou_memWkp_and_wkpNorm_le
    (I := I) (M := M) g r s i (K + 1) β P (h_pou_phi β P)
  have hg_weak : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k
      (eigenvectorChartWeakPartial (I := I) (M := M) g r s i β P k)
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
            i) β P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) Ω :=
    eigenvectorChartWeakPartial_hasWeakPartialDeriv (I := I) (M := M)
      g r s i β P k
  have hg_loc : LocallyIntegrable
      (eigenvectorChartWeakPartial (I := I) (M := M) g r s i β P k)
      ((volume : Measure EuclN).restrict Ω) := by
    have h_memLp : MemLp (eigenvectorChartWeakPartial (I := I)
        (M := M) g r s i β P k) 2
        ((volume : Measure EuclN).restrict Ω) := by
      rw [eigenvectorChartWeakPartial]
      exact Lp.memLp _
    exact h_memLp.locallyIntegrable (by norm_num)
  have hu_W1 : DeGiorgi.MemW1p 2
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
            i) β P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) Ω :=
    hu.memW1p
  have h_chosen_weak : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k
      (chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i) β P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) Ω)
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
            i) β P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) Ω :=
    chosenWeakPartial'_isWeakPartial_of_mem (d := Module.finrank ℝ E) hu_W1 k
  have h_chosen_loc : LocallyIntegrable
      (chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i) β P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) Ω)
      ((volume : Measure EuclN).restrict Ω) :=
    (chosenWeakPartial'_memLp_of_mem (d := Module.finrank ℝ E)
      hu_W1 k).locallyIntegrable (by norm_num)
  have h_ae : eigenvectorChartWeakPartial (I := I) (M := M)
        g r s i β P k
      =ᵐ[(volume : Measure EuclN).restrict Ω]
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i) β P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) Ω :=
    DeGiorgi.HasWeakPartialDeriv.ae_eq (d := Module.finrank ℝ E) hΩ_open
      hg_weak h_chosen_weak hg_loc h_chosen_loc
  have h_chosen_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i) β P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) Ω) Ω :=
    hu.chosenWeakPartial_mem k
  have h_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (eigenvectorChartWeakPartial (I := I) (M := M)
        g r s i β P k) Ω :=
    (MemWkp_congr_ae (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae).mpr h_chosen_memWkp
  refine ⟨h_memWkp, ‖(i.fst.val)⁻¹‖, norm_nonneg _, ?_⟩
  rw [wkpNorm_congr_ae (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae]
  calc
    iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
        (chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
          (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
              (tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i) β P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) Ω) Ω
        ≤ iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K + 1) 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (tensorResolventEigenbasisVec (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator (I := I) (M := M)
                    g r s) i) β P :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) Ω :=
      wkpNorm_chosenWeakPartial_le_wkpNorm_succ (d := Module.finrank ℝ E) K
        hΩ_open _ k
    _ ≤ ENNReal.ofReal ‖(i.fst.val)⁻¹‖ *
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K + 1) 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent (I := I) (M := M) g r s i))
                β P : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β) := hu_norm
    _ ≤ ENNReal.ofReal ‖(i.fst.val)⁻¹‖ *
          covGradAggregate (I := I) (M := M) g r s i K β :=
      mul_le_mul_of_nonneg_left
        (chartCompNorm_center_le_covGradAggregate (I := I) (M := M)
          g r s i K β P) (zero_le _)

omit [CompleteSpace E] in
lemma eigenvectorChartWeakPartial_wkpNorm_le_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (K : ℕ)
    (h_pou_phi : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β))
    (β : M) (P : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (eigenvectorChartWeakPartial (I := I) (M := M)
              g r s i β P k)
            (chartTargetEuclid (I := I) (M := M) β)
          ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * C) *
            covGradAggregate (I := I) (M := M) g r s i K β := by
  classical
  refine ⟨1, zero_le_one, fun i => ?_⟩
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) β with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) β
  have hμ_pos : 0 < i.fst.val := eigenIdx_val_pos (I := I) (M := M) g r s i
  have hμ_inv_nn : 0 ≤ (i.fst.val)⁻¹ := le_of_lt (inv_pos.mpr hμ_pos)
  have hμ_norm : ‖(i.fst.val)⁻¹‖ = (i.fst.val)⁻¹ := Real.norm_of_nonneg hμ_inv_nn
  obtain ⟨hu, hu_norm⟩ := eigenvectorVec_pou_memWkp_and_wkpNorm_le
    (I := I) (M := M) g r s i (K + 1) β P (h_pou_phi i β P)
  have hg_weak : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k
      (eigenvectorChartWeakPartial (I := I) (M := M) g r s i β P k)
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
            i) β P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) Ω :=
    eigenvectorChartWeakPartial_hasWeakPartialDeriv (I := I) (M := M)
      g r s i β P k
  have hg_loc : LocallyIntegrable
      (eigenvectorChartWeakPartial (I := I) (M := M) g r s i β P k)
      ((volume : Measure EuclN).restrict Ω) := by
    have h_memLp : MemLp (eigenvectorChartWeakPartial (I := I)
        (M := M) g r s i β P k) 2
        ((volume : Measure EuclN).restrict Ω) := by
      rw [eigenvectorChartWeakPartial]
      exact Lp.memLp _
    exact h_memLp.locallyIntegrable (by norm_num)
  have hu_W1 : DeGiorgi.MemW1p 2
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
            i) β P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) Ω :=
    hu.memW1p
  have h_chosen_weak : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k
      (chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i) β P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) Ω)
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
            i) β P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) Ω :=
    chosenWeakPartial'_isWeakPartial_of_mem (d := Module.finrank ℝ E) hu_W1 k
  have h_chosen_loc : LocallyIntegrable
      (chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i) β P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) Ω)
      ((volume : Measure EuclN).restrict Ω) :=
    (chosenWeakPartial'_memLp_of_mem (d := Module.finrank ℝ E)
      hu_W1 k).locallyIntegrable (by norm_num)
  have h_ae : eigenvectorChartWeakPartial (I := I) (M := M)
        g r s i β P k
      =ᵐ[(volume : Measure EuclN).restrict Ω]
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i) β P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) Ω :=
    DeGiorgi.HasWeakPartialDeriv.ae_eq (d := Module.finrank ℝ E) hΩ_open
      hg_weak h_chosen_weak hg_loc h_chosen_loc
  rw [wkpNorm_congr_ae (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae, mul_one]
  calc
    iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
        (chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
          (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
              (tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i) β P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) Ω) Ω
        ≤ iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K + 1) 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (tensorResolventEigenbasisVec (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator (I := I) (M := M)
                    g r s) i) β P :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) Ω :=
      wkpNorm_chosenWeakPartial_le_wkpNorm_succ (d := Module.finrank ℝ E) K
        hΩ_open _ k
    _ ≤ ENNReal.ofReal ‖(i.fst.val)⁻¹‖ *
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K + 1) 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent (I := I) (M := M) g r s i))
                β P : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β) := hu_norm
    _ ≤ ENNReal.ofReal ‖(i.fst.val)⁻¹‖ *
          covGradAggregate (I := I) (M := M) g r s i K β :=
      mul_le_mul_of_nonneg_left
        (chartCompNorm_center_le_covGradAggregate (I := I) (M := M)
          g r s i K β P) (zero_le _)
    _ = ENNReal.ofReal (i.fst.val)⁻¹ *
          covGradAggregate (I := I) (M := M) g r s i K β := by
      rw [hμ_norm]

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
