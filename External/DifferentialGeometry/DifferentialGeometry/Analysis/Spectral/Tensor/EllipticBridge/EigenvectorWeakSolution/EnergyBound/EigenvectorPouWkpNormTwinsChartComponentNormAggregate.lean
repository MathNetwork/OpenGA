import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.CovGrad.EigenvectorCovGradComponent
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Cutoff.CutoffChartComponentWkpNorm
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Multiplication.MultiplyQuantK
import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.IteratedSobolevQuant

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

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

omit [CompleteSpace E] in
lemma eigenvectorVec_pou_memWkp_and_wkpNorm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) (N : ℕ)
    (β : M) (Q : TensorCompIdx (E := E) r s)
    (h_res : MemWkp (d := Module.finrank ℝ E) N 2
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s i))
          β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
      (chartTargetEuclid (I := I) (M := M) β)) :
    MemWkp (d := Module.finrank ℝ E) N 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i) β Q :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β) ∧
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) N 2
          (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
              (tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i) β Q :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) β)
        ≤ ENNReal.ofReal ‖(i.fst.val)⁻¹‖ *
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) N 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent (I := I) (M := M) g r s i))
                β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) β with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) β
  have h_chart_eq := eigenvector_chartComponent_eq (I := I) (M := M)
    g r s i β Q
  have h_ae : (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
        (tensorResolventEigenbasisVec (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
          i) β Q :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
      =ᵐ[(volume : Measure EuclN).restrict Ω]
      (fun y => (i.fst.val)⁻¹ *
        ((tensorL2ChartComponent (I := I) (M := M) g r s
          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s i))
          β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) := by
    have h_smul := Lp.coeFn_smul (i.fst.val)⁻¹
      (tensorL2ChartComponent (I := I) (M := M) g r s
        (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
          (eigenvectorResolvent (I := I) (M := M) g r s i)) β Q)
    have h_smul' : (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
            i) β Q :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        =ᵐ[chartL2Measure (I := I) (M := M) β]
        (fun y => (i.fst.val)⁻¹ •
          ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
            EuclN → ℝ) y) := by
      rw [h_chart_eq]
      exact h_smul
    filter_upwards [h_smul'] with y hy
    rw [hy, smul_eq_mul]
  have h_mem : MemWkp (d := Module.finrank ℝ E) N 2
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
            i) β Q :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) Ω :=
    (MemWkp_congr_ae (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae).mpr
      (MemWkp.const_smul (d := Module.finrank ℝ E)
        (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_res (i.fst.val)⁻¹)
  refine ⟨h_mem, ?_⟩
  have h_norm_eq : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) N 2
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
            i) β Q :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) Ω =
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) N 2
        (fun y => (i.fst.val)⁻¹ *
          ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
            EuclN → ℝ) y) Ω :=
    wkpNorm_congr_ae (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae
  rw [h_norm_eq,
    wkpNorm_const_smul (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_res (i.fst.val)⁻¹]
  refine le_of_eq ?_
  rw [← ofReal_norm]

def chartCompNorm
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) (K : ℕ)
    (β' : M) (Q : TensorCompIdx (E := E) r s) : ℝ≥0∞ :=
  iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K + 1) 2
    (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
        (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
          (eigenvectorResolvent (I := I) (M := M) g r s i))
        β' Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) : EuclN → ℝ) y)
    (chartTargetEuclid (I := I) (M := M) β')

def covGradAggregate
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) (K : ℕ) (β : M) : ℝ≥0∞ :=
  (∑ Q : TensorCompIdx (E := E) r s,
      chartCompNorm (I := I) (M := M) g r s i K β Q)
    + ∑ β' ∈ transportChartCenters (I := I) (M := M) β,
        ∑ Q : TensorCompIdx (E := E) r s,
          chartCompNorm (I := I) (M := M) g r s i K β' Q

omit [CompleteSpace E] in
lemma chartCompNorm_center_le_covGradAggregate
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) (K : ℕ)
    (β : M) (Q : TensorCompIdx (E := E) r s) :
    chartCompNorm (I := I) (M := M) g r s i K β Q
      ≤ covGradAggregate (I := I) (M := M) g r s i K β := by
  classical
  refine le_trans ?_ le_self_add
  exact Finset.single_le_sum
    (f := fun Q' : TensorCompIdx (E := E) r s =>
      chartCompNorm (I := I) (M := M) g r s i K β Q')
    (fun _ _ => zero_le _) (Finset.mem_univ Q)

omit [CompleteSpace E] in
lemma chartCompNorm_transport_le_covGradAggregate
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) (K : ℕ)
    {β β' : M} (hβ' : β' ∈ transportChartCenters (I := I) (M := M) β)
    (Q : TensorCompIdx (E := E) r s) :
    chartCompNorm (I := I) (M := M) g r s i K β' Q
      ≤ covGradAggregate (I := I) (M := M) g r s i K β := by
  classical
  refine le_trans ?_ le_add_self
  refine le_trans ?_
    (Finset.single_le_sum
      (f := fun β'' : M =>
        ∑ Q' : TensorCompIdx (E := E) r s,
          chartCompNorm (I := I) (M := M) g r s i K β'' Q')
      (fun _ _ => zero_le _) hβ')
  exact Finset.single_le_sum
    (f := fun Q' : TensorCompIdx (E := E) r s =>
      chartCompNorm (I := I) (M := M) g r s i K β' Q')
    (fun _ _ => zero_le _) (Finset.mem_univ Q)

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
