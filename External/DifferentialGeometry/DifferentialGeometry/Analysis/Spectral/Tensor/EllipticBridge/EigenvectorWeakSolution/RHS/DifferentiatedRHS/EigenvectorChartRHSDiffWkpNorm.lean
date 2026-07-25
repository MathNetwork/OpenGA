import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.RHS.ChartRHSBounds.EigenvectorChartRHSWkpNorm
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.RHS.DifferentiatedRHS.EigenvectorChartRHSDiffStepWkpNorm
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.RHS.DifferentiatedRHS.EigenvectorDifferentiatedRHSWkpNorm
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Iterated.EigenvectorIteratedDatum
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.RHS.DifferentiatedRHS.EigenvectorDifferentiatedRHSMemW1p
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.RHS.DifferentiatedRHS.EigenvectorDifferentiatedRHS
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Regularity.EigenvectorArbitraryKRegularity


noncomputable section

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

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
open DifferentialGeometry.Tensor.TensorRSRiemannian
open TensorRSNabla
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

section MainBound


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


omit [CompleteSpace E] in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma eigenIdx_val_le_one
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    i.fst.val ≤ 1 := by
  obtain ⟨u, hu_mem, hu_ne⟩ := i.fst.hasEigenvalue.exists_hasEigenvector
  have hu_in : u ∈ tensorResolventEigenspace
      (I := I) (M := M) g r s i.fst.val := hu_mem
  exact (tensorResolvent_eigenvalue_mem_unit_interval
    (I := I) (M := M) g r s hu_in hu_ne).2

end MainBound

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in

def rhsZeroAggregate
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (K : ℕ) : ℝ≥0∞ :=
  iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M)
              g r s) i) α P₀ :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      (chartTargetEuclid (I := I) (M := M) α)
    + (∑ β ∈ transportChartCenters (I := I) (M := M) α,
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
                  (fun y => ((tensorL2ChartComponent (I := I) (M := M)
                      g r s
                      (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                        (eigenvectorResolvent (I := I) (M := M)
                          g r s i))
                      β' Q :
                      Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) :
                      EuclN → ℝ) y)
                  (chartTargetEuclid (I := I) (M := M) β')))
    + (∑ β ∈ transportChartCenters (I := I) (M := M) α,
        ∑ Q : TensorCompIdx (E := E) r s,
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent (I := I) (M := M)
                    g r s i))
                β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β))
    + (∑ P : TensorCompIdx (E := E) r s,
        ∑ k : Fin (Module.finrank ℝ E),
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((partialLpLimit (I := I) (M := M)
                g r s i α P k :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α))
    + (∑ p : TensorCompIdx (E := E) r s,
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (fun y => ((componentLpLimit (I := I) (M := M)
              g r s i α p :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
            EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α))
    + (∑ P : TensorCompIdx (E := E) r s,
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (fun y => ((crossRightLimitComponent (I := I) (M := M)
              g r s i α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
            EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α))
    + (∑ P : TensorCompIdx (E := E) r s,
        ∑ l : Fin (Module.finrank ℝ E),
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((cutoffPartialLpLimit (I := I) (M := M)
                g r s i α P l :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α))

def diffRHSHead
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E)) : ℝ≥0∞ :=
  (∑ a : Fin (Module.finrank ℝ E),
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (2 + K) 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
        (chartTargetEuclid (I := I) (M := M) α))
    + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (2 + K) 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ m (Fin.init l))
        (chartTargetEuclid (I := I) (M := M) α)

def diffRHSAggregate
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin m → Fin (Module.finrank ℝ E)) : ℝ≥0∞ :=
  match m, l with
  | 0, _ => rhsZeroAggregate (I := I) (M := M) g r s i α P₀ K
  | m + 1, l =>
      diffRHSHead (I := I) (M := M) g r s i α P₀ m K l +
        diffRHSAggregate g r s i α P₀ m (K + 1) (Fin.init l)

omit [CompleteSpace E] in
private theorem diffRHSAggregate_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (K : ℕ)
    (l : Fin 0 → Fin (Module.finrank ℝ E)) :
    diffRHSAggregate (I := I) (M := M) g r s i α P₀ 0 K l =
      rhsZeroAggregate (I := I) (M := M) g r s i α P₀ K := rfl

omit [CompleteSpace E] in
private theorem diffRHSAggregate_succ
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E)) :
    diffRHSAggregate (I := I) (M := M) g r s i α P₀ (m + 1) K l =
      diffRHSHead (I := I) (M := M) g r s i α P₀ m K l +
        diffRHSAggregate (I := I) (M := M) g r s i α P₀ m (K + 1)
          (Fin.init l) := rfl

omit [CompleteSpace E] in
lemma rhsDiff_ae_zero_off_chartPouKernel
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (m : ℕ) (l : Fin m → Fin (Module.finrank ℝ E)) :
    eigenvectorChartRHSDiff (I := I) (M := M) g r s i α P₀ m l
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α)] (fun _ : EuclN => (0 : ℝ)) := by
  cases m with
  | zero =>
      rw [eigenvectorChartRHSDiff_zero]
      exact eigenvectorChartRHS_ae_zero_off_chartPouKernel
        (I := I) (M := M) g r s i α P₀
  | succ m =>
      have hV_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α) :=
        (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet.diff
          (chartPouKernel_measurableSet (I := I) (M := M) α)
      rw [Filter.EventuallyEq, ae_restrict_iff' hV_meas]
      refine Filter.Eventually.of_forall (fun y hy => ?_)
      exact eigenvectorChartRHSDiff_succ_eq_zero_off_chartPouKernel
        (I := I) (M := M) g r s i α P₀ m l hy.2

omit [CompleteSpace E] in
private lemma iteratedPartial_memWkp_two_add
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (K : ℕ) :
    ∀ (j : ℕ) (idx : Fin j → Fin (Module.finrank ℝ E)),
      MemWkp (d := Module.finrank ℝ E) (2 + K) 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ j idx)
        (chartTargetEuclid (I := I) (M := M) α) := by
  intro j idx
  have h_comp : MemWkp (d := Module.finrank ℝ E) ((2 + K) + j) 2
      (eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀)
      (chartTargetEuclid (I := I) (M := M) α) :=
    eigenvector_chartComponent_memWkp_arbitrary (I := I) (M := M)
      g r s i ((2 + K) + j) α P₀
  exact eigenvectorChartIteratedPartial_memWkp_of_memWkp (I := I)
    (M := M) g r s i α P₀ j (2 + K) h_comp idx

omit [CompleteSpace E] in
theorem eigenvectorChartRHSDiff_wkpNorm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin m → Fin (Module.finrank ℝ E))
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (m + 1 + K) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    ∃ C : ℝ, 0 ≤ C ∧
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (eigenvectorChartRHSDiff (I := I) (M := M)
            g r s i α P₀ m l)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * C) *
          diffRHSAggregate (I := I) (M := M)
            g r s i α P₀ m K l := by
  classical
  have hμ_pos : 0 < i.fst.val := eigenIdx_val_pos (I := I) (M := M) g r s i
  have hμ_le_one : i.fst.val ≤ 1 := eigenIdx_val_le_one (I := I) (M := M) g r s i
  have hμ_inv_nn : 0 ≤ (i.fst.val)⁻¹ := le_of_lt (inv_pos.mpr hμ_pos)
  have hμ_inv_ge_one : (1 : ℝ) ≤ (i.fst.val)⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hμ_pos]; simpa using hμ_le_one
  induction m generalizing K with
  | zero =>
      rw [eigenvectorChartRHSDiff_zero]
      have h_pou' : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
          MemWkp (d := Module.finrank ℝ E) (K + 1) 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent (I := I) (M := M) g r s i))
                β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β) := by
        intro β Q
        have h_idx : (0 : ℕ) + 1 + K = K + 1 := by omega
        rw [← h_idx]
        exact h_pou β Q
      obtain ⟨C, hC_nn, hC_bd⟩ := eigenvectorChartRHS_wkpNorm_le
        (I := I) (M := M) g r s i α P₀ K h_pou'
      refine ⟨C, hC_nn, ?_⟩
      rw [diffRHSAggregate_zero]
      show iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (eigenvectorChartRHS (I := I) (M := M) g r s i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * C) *
          rhsZeroAggregate (I := I) (M := M) g r s i α P₀ K
      exact hC_bd
  | succ m ih =>
      have h_snoc :
          eigenvectorChartRHSDiff (I := I) (M := M)
              g r s i α P₀ (m + 1) l =
            eigenvectorChartRHSDiff (I := I) (M := M)
              g r s i α P₀ (m + 1)
              (Fin.snoc (Fin.init l) (l (Fin.last m))) := by
        rw [Fin.snoc_init_self]
      rw [h_snoc]
      rw [← eigenvectorChartIteratedStep_eq_rhsDiff_succ (I := I)
        (M := M) g r s i α P₀ m (Fin.init l) (l (Fin.last m))]
      have h_iter : ∀ (j : ℕ) (idx : Fin j → Fin (Module.finrank ℝ E)),
          MemWkp (d := Module.finrank ℝ E) (2 + K) 2
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s i α P₀ j idx)
            (chartTargetEuclid (I := I) (M := M) α) :=
        iteratedPartial_memWkp_two_add (I := I) (M := M)
          g r s i α P₀ K
      have h_pou_prev : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
          MemWkp (d := Module.finrank ℝ E) (m + 1 + (K + 1)) 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent (I := I) (M := M) g r s i))
                β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β) := by
        intro β Q
        have h_idx : m + 1 + (K + 1) = m + 1 + 1 + K := by omega
        rw [h_idx]
        exact h_pou β Q
      have h_prev : MemWkp (d := Module.finrank ℝ E) (K + 1) 2
          (eigenvectorChartRHSDiff (I := I) (M := M)
            g r s i α P₀ m (Fin.init l))
          (chartTargetEuclid (I := I) (M := M) α) :=
        eigenvectorChartRHSDiff_memWkp (I := I) (M := M)
          g r s i α P₀ m (K + 1) (Fin.init l) h_pou_prev
      have h_prev_zero :
          eigenvectorChartRHSDiff (I := I) (M := M)
              g r s i α P₀ m (Fin.init l)
            =ᵐ[(volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α \
                chartPouKernel (I := I) (M := M) α)]
            (fun _ : EuclN => (0 : ℝ)) :=
        rhsDiff_ae_zero_off_chartPouKernel (I := I) (M := M)
          g r s i α P₀ m (Fin.init l)
      obtain ⟨Cstep, hCstep_nn, hCstep_bd⟩ :=
        eigenvectorChartIteratedStep_wkpNorm_le (I := I) (M := M)
          g r s i α P₀ m K (Fin.init l)
          (fChartEffPrev := eigenvectorChartRHSDiff (I := I) (M := M)
            g r s i α P₀ m (Fin.init l))
          (l (Fin.last m)) h_iter h_prev h_prev_zero
      obtain ⟨Cih, hCih_nn, hCih_bd⟩ := ih (K + 1) (Fin.init l) h_pou_prev
      refine ⟨max Cstep (2 * Cstep * Cih), le_max_of_le_left hCstep_nn, ?_⟩
      set H := diffRHSHead (I := I) (M := M) g r s i α P₀ m K
        (Fin.snoc (Fin.init l) (l (Fin.last m))) with hH_def
      set D := diffRHSAggregate (I := I) (M := M)
        g r s i α P₀ m (K + 1) (Fin.init l) with hD_def
      set Pprev := eigenvectorChartRHSDiff (I := I) (M := M)
        g r s i α P₀ m (Fin.init l) with hPprev_def
      have h_num_split :
          diffNumeratorAggregateK (I := I) (M := M)
              g r s i α P₀ m K
              (Fin.snoc (Fin.init l) (l (Fin.last m))) Pprev =
            H
              + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K + 1) 2 Pprev
                  (chartTargetEuclid (I := I) (M := M) α)
              + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 Pprev
                  (chartTargetEuclid (I := I) (M := M) α) := by
        rw [hH_def]; rfl
      rw [h_num_split] at hCstep_bd
      have h_prev_mono :
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 Pprev
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K + 1) 2 Pprev
                (chartTargetEuclid (I := I) (M := M) α) :=
        wkpNorm_mono_order (d := Module.finrank ℝ E) (Nat.le_succ K) _ _
      have h_ih_bd :
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K + 1) 2 Pprev
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * Cih) * D := hCih_bd
      have h_prev_succ_le :
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K + 1) 2 Pprev
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * Cih) * D := h_ih_bd
      have h_prev_K_le :
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 Pprev
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * Cih) * D :=
        le_trans h_prev_mono h_ih_bd
      have h_aggr_le :
          H
              + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K + 1) 2 Pprev
                  (chartTargetEuclid (I := I) (M := M) α)
              + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 Pprev
                  (chartTargetEuclid (I := I) (M := M) α)
            ≤ H + ENNReal.ofReal ((i.fst.val)⁻¹ * Cih) * D
                + ENNReal.ofReal ((i.fst.val)⁻¹ * Cih) * D :=
        add_le_add (add_le_add (le_refl H) h_prev_succ_le) h_prev_K_le
      have h_step_chained :
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (eigenvectorChartIteratedStep (I := I) (M := M)
                g r s i α P₀ m (Fin.init l) Pprev (l (Fin.last m)))
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal Cstep *
              (H + ENNReal.ofReal ((i.fst.val)⁻¹ * Cih) * D
                + ENNReal.ofReal ((i.fst.val)⁻¹ * Cih) * D) :=
        le_trans hCstep_bd (mul_le_mul' (le_refl _) h_aggr_le)
      refine le_trans h_step_chained ?_
      have h_target_aggr :
          diffRHSAggregate (I := I) (M := M)
              g r s i α P₀ (m + 1) K l
            = H + D := by
        rw [diffRHSAggregate_succ, hH_def, hD_def, Fin.snoc_init_self]
      rw [h_target_aggr]
      set C' : ℝ := max Cstep (2 * Cstep * Cih) with hC'_def
      have hCih_nn' : 0 ≤ Cih := hCih_nn
      have hC'_nn : 0 ≤ C' := le_max_of_le_left hCstep_nn
      rw [mul_add, mul_add, mul_add, add_assoc]
      have h_head_le :
          ENNReal.ofReal Cstep * H
            ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * C') * H := by
        gcongr
        have h1 : Cstep ≤ C' := le_max_left _ _
        nlinarith [h1, hμ_inv_ge_one, hC'_nn, hCstep_nn]
      have h_tail_one :
          ENNReal.ofReal Cstep * (ENNReal.ofReal ((i.fst.val)⁻¹ * Cih) * D)
            ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * C' / 2) * D := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hCstep_nn]
        gcongr
        have h2C : 2 * Cstep * Cih ≤ C' := le_max_right _ _
        have h_cs_ci_nn : 0 ≤ Cstep * Cih := mul_nonneg hCstep_nn hCih_nn'
        nlinarith [h2C, hμ_inv_ge_one, hμ_inv_nn, h_cs_ci_nn]
      have h_tail_combine :
          ENNReal.ofReal ((i.fst.val)⁻¹ * C' / 2) * D
              + ENNReal.ofReal ((i.fst.val)⁻¹ * C' / 2) * D
            = ENNReal.ofReal ((i.fst.val)⁻¹ * C') * D := by
        rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 2
        ring
      have h_tail_le :
          ENNReal.ofReal Cstep * (ENNReal.ofReal ((i.fst.val)⁻¹ * Cih) * D)
              + ENNReal.ofReal Cstep *
                  (ENNReal.ofReal ((i.fst.val)⁻¹ * Cih) * D)
            ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * C') * D := by
        rw [← h_tail_combine]
        exact add_le_add h_tail_one h_tail_one
      exact add_le_add h_head_le h_tail_le


omit [CompleteSpace E] in
theorem eigenvectorChartRHSDiff_wkpNorm_le_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin m → Fin (Module.finrank ℝ E))
    (h_pou : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (m + 1 + K) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (eigenvectorChartRHSDiff (I := I) (M := M)
              g r s i α P₀ m l)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * C) *
            diffRHSAggregate (I := I) (M := M)
              g r s i α P₀ m K l := by
  classical
  induction m generalizing K with
  | zero =>
      have h_pou' : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
          (β : M) (Q : TensorCompIdx (E := E) r s),
          MemWkp (d := Module.finrank ℝ E) (K + 1) 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent (I := I) (M := M) g r s i))
                β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β) := by
        intro i β Q
        have h_idx : (0 : ℕ) + 1 + K = K + 1 := by omega
        rw [← h_idx]
        exact h_pou i β Q
      obtain ⟨C, hC_nn, hC_bd⟩ := eigenvectorChartRHS_wkpNorm_le_uniform
        (I := I) (M := M) g r s α P₀ K h_pou'
      refine ⟨C, hC_nn, fun i => ?_⟩
      rw [eigenvectorChartRHSDiff_zero,
        diffRHSAggregate_zero]
      show iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (eigenvectorChartRHS (I := I) (M := M) g r s i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * C) *
          rhsZeroAggregate (I := I) (M := M) g r s i α P₀ K
      exact hC_bd i
  | succ m ih =>
      set fPrev : TensorEigenIdx (I := I) (M := M) g r s → EuclN → ℝ :=
        fun i => eigenvectorChartRHSDiff (I := I) (M := M)
          g r s i α P₀ m (Fin.init l) with hfPrev_def
      have h_pou_prev : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
          (β : M) (Q : TensorCompIdx (E := E) r s),
          MemWkp (d := Module.finrank ℝ E) (m + 1 + (K + 1)) 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent (I := I) (M := M) g r s i))
                β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β) := by
        intro i β Q
        have h_idx : m + 1 + (K + 1) = m + 1 + 1 + K := by omega
        rw [h_idx]
        exact h_pou i β Q
      have h_iter : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
          (j : ℕ) (idx : Fin j → Fin (Module.finrank ℝ E)),
          MemWkp (d := Module.finrank ℝ E) (2 + K) 2
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s i α P₀ j idx)
            (chartTargetEuclid (I := I) (M := M) α) :=
        fun i => iteratedPartial_memWkp_two_add (I := I) (M := M)
          g r s i α P₀ K
      have h_prev : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
          MemWkp (d := Module.finrank ℝ E) (K + 1) 2 (fPrev i)
            (chartTargetEuclid (I := I) (M := M) α) := by
        intro i
        rw [hfPrev_def]
        exact eigenvectorChartRHSDiff_memWkp (I := I) (M := M)
          g r s i α P₀ m (K + 1) (Fin.init l) (h_pou_prev i)
      have h_prev_zero : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
          (fPrev i) =ᵐ[(volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α \
                chartPouKernel (I := I) (M := M) α)]
            (fun _ : EuclN => (0 : ℝ)) := by
        intro i
        rw [hfPrev_def]
        exact rhsDiff_ae_zero_off_chartPouKernel (I := I) (M := M)
          g r s i α P₀ m (Fin.init l)
      obtain ⟨Cstep, hCstep_nn, hCstep_bd⟩ :=
        eigenvectorChartIteratedStep_wkpNorm_le_uniform (I := I)
          (M := M) g r s α P₀ m K (Fin.init l) (l (Fin.last m))
          (fChartEffPrev := fPrev) h_iter h_prev h_prev_zero
      obtain ⟨Cih, hCih_nn, hCih_bd⟩ := ih (K + 1) (Fin.init l) h_pou_prev
      refine ⟨max Cstep (2 * Cstep * Cih), le_max_of_le_left hCstep_nn,
        fun i => ?_⟩
      have hμ_pos : 0 < i.fst.val := eigenIdx_val_pos (I := I) (M := M) g r s i
      have hμ_le_one : i.fst.val ≤ 1 :=
        eigenIdx_val_le_one (I := I) (M := M) g r s i
      have hμ_inv_nn : 0 ≤ (i.fst.val)⁻¹ := le_of_lt (inv_pos.mpr hμ_pos)
      have hμ_inv_ge_one : (1 : ℝ) ≤ (i.fst.val)⁻¹ := by
        rw [le_inv_comm₀ (by norm_num) hμ_pos]; simpa using hμ_le_one
      have h_snoc :
          eigenvectorChartRHSDiff (I := I) (M := M)
              g r s i α P₀ (m + 1) l =
            eigenvectorChartRHSDiff (I := I) (M := M)
              g r s i α P₀ (m + 1)
              (Fin.snoc (Fin.init l) (l (Fin.last m))) := by
        rw [Fin.snoc_init_self]
      rw [h_snoc]
      rw [← eigenvectorChartIteratedStep_eq_rhsDiff_succ (I := I)
        (M := M) g r s i α P₀ m (Fin.init l) (l (Fin.last m))]
      set H := diffRHSHead (I := I) (M := M) g r s i α P₀ m K
        (Fin.snoc (Fin.init l) (l (Fin.last m))) with hH_def
      set D := diffRHSAggregate (I := I) (M := M)
        g r s i α P₀ m (K + 1) (Fin.init l) with hD_def
      set Pprev := eigenvectorChartRHSDiff (I := I) (M := M)
        g r s i α P₀ m (Fin.init l) with hPprev_def
      have hCstep_bd_i := hCstep_bd i
      have hfPrev_i : fPrev i = Pprev := by rw [hfPrev_def, hPprev_def]
      rw [hfPrev_i] at hCstep_bd_i
      have h_num_split :
          diffNumeratorAggregateK (I := I) (M := M)
              g r s i α P₀ m K
              (Fin.snoc (Fin.init l) (l (Fin.last m))) Pprev =
            H
              + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K + 1) 2 Pprev
                  (chartTargetEuclid (I := I) (M := M) α)
              + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 Pprev
                  (chartTargetEuclid (I := I) (M := M) α) := by
        rw [hH_def]; rfl
      rw [h_num_split] at hCstep_bd_i
      have h_prev_mono :
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 Pprev
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K + 1) 2 Pprev
                (chartTargetEuclid (I := I) (M := M) α) :=
        wkpNorm_mono_order (d := Module.finrank ℝ E) (Nat.le_succ K) _ _
      have h_ih_bd :
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K + 1) 2 Pprev
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * Cih) * D := hCih_bd i
      have h_prev_K_le :
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 Pprev
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * Cih) * D :=
        le_trans h_prev_mono h_ih_bd
      have h_aggr_le :
          H
              + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K + 1) 2 Pprev
                  (chartTargetEuclid (I := I) (M := M) α)
              + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 Pprev
                  (chartTargetEuclid (I := I) (M := M) α)
            ≤ H + ENNReal.ofReal ((i.fst.val)⁻¹ * Cih) * D
                + ENNReal.ofReal ((i.fst.val)⁻¹ * Cih) * D :=
        add_le_add (add_le_add (le_refl H) h_ih_bd) h_prev_K_le
      have h_step_chained :
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (eigenvectorChartIteratedStep (I := I) (M := M)
                g r s i α P₀ m (Fin.init l) Pprev (l (Fin.last m)))
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal Cstep *
              (H + ENNReal.ofReal ((i.fst.val)⁻¹ * Cih) * D
                + ENNReal.ofReal ((i.fst.val)⁻¹ * Cih) * D) :=
        le_trans hCstep_bd_i (mul_le_mul' (le_refl _) h_aggr_le)
      refine le_trans h_step_chained ?_
      have h_target_aggr :
          diffRHSAggregate (I := I) (M := M)
              g r s i α P₀ (m + 1) K l
            = H + D := by
        rw [diffRHSAggregate_succ, hH_def, hD_def, Fin.snoc_init_self]
      rw [h_target_aggr]
      set C' : ℝ := max Cstep (2 * Cstep * Cih) with hC'_def
      have hCih_nn' : 0 ≤ Cih := hCih_nn
      have hC'_nn : 0 ≤ C' := le_max_of_le_left hCstep_nn
      rw [mul_add, mul_add, mul_add, add_assoc]
      have h_head_le :
          ENNReal.ofReal Cstep * H
            ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * C') * H := by
        gcongr
        have h1 : Cstep ≤ C' := le_max_left _ _
        nlinarith [h1, hμ_inv_ge_one, hC'_nn, hCstep_nn]
      have h_tail_one :
          ENNReal.ofReal Cstep * (ENNReal.ofReal ((i.fst.val)⁻¹ * Cih) * D)
            ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * C' / 2) * D := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hCstep_nn]
        gcongr
        have h2C : 2 * Cstep * Cih ≤ C' := le_max_right _ _
        have h_cs_ci_nn : 0 ≤ Cstep * Cih := mul_nonneg hCstep_nn hCih_nn'
        nlinarith [h2C, hμ_inv_ge_one, hμ_inv_nn, h_cs_ci_nn]
      have h_tail_combine :
          ENNReal.ofReal ((i.fst.val)⁻¹ * C' / 2) * D
              + ENNReal.ofReal ((i.fst.val)⁻¹ * C' / 2) * D
            = ENNReal.ofReal ((i.fst.val)⁻¹ * C') * D := by
        rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 2
        ring
      have h_tail_le :
          ENNReal.ofReal Cstep * (ENNReal.ofReal ((i.fst.val)⁻¹ * Cih) * D)
              + ENNReal.ofReal Cstep *
                  (ENNReal.ofReal ((i.fst.val)⁻¹ * Cih) * D)
            ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * C') * D := by
        rw [← h_tail_combine]
        exact add_le_add h_tail_one h_tail_one
      exact add_le_add h_head_le h_tail_le

omit [CompleteSpace E] in
theorem eigenvectorChartRHSDiff_eLpNorm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (l : Fin m → Fin (Module.finrank ℝ E))
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (m + 1 + 0) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    ∃ C : ℝ, 0 ≤ C ∧
      eLpNorm (eigenvectorChartRHSDiff (I := I) (M := M)
          g r s i α P₀ m l)
          2 ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * C) *
          diffRHSAggregate (I := I) (M := M) g r s i α P₀ m 0 l := by
  obtain ⟨C, hC_nn, hC_bd⟩ := eigenvectorChartRHSDiff_wkpNorm_le
    (I := I) (M := M) g r s i α P₀ m 0 l h_pou
  refine ⟨C, hC_nn, ?_⟩
  rwa [wkpNorm_zero (d := Module.finrank ℝ E)] at hC_bd

omit [CompleteSpace E] in
theorem eigenvectorChartRHSDiff_eLpNorm_le_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (l : Fin m → Fin (Module.finrank ℝ E))
    (h_pou : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (m + 1 + 0) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm (eigenvectorChartRHSDiff (I := I) (M := M)
            g r s i α P₀ m l)
            2 ((volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * C) *
            diffRHSAggregate (I := I) (M := M)
              g r s i α P₀ m 0 l := by
  obtain ⟨C, hC_nn, hC_bd⟩ := eigenvectorChartRHSDiff_wkpNorm_le_uniform
    (I := I) (M := M) g r s α P₀ m 0 l h_pou
  refine ⟨C, hC_nn, fun i => ?_⟩
  have hC_bd_i := hC_bd i
  rwa [wkpNorm_zero (d := Module.finrank ℝ E)] at hC_bd_i

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
