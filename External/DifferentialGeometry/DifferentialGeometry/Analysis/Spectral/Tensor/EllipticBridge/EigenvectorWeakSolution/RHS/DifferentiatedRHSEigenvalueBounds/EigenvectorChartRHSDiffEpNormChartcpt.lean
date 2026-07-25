import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.RHS.DifferentiatedRHS.EigenvectorChartRHSDiffWkpNormEnergyBound
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Iterated.EigenvectorIteratedRegularityHigherQuant

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
private lemma iteratedPartial_wkpNorm_le_of_chart_perK
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (Ceig : ℕ → ℝ) (eEig : ℕ → ℕ)
    (hCeig_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s) (K' : ℕ),
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
          (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
            g r s i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (Ceig K' * (i.fst.val)⁻¹ ^ (eEig K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖) :
    ∀ (i : TensorEigenIdx (I := I) (M := M) g r s) (j : ℕ),
      j ≤ m + 1 →
      ∀ (idx : Fin j → Fin (Module.finrank ℝ E)) (K' : ℕ),
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (2 + K') 2
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s i α P₀ j idx)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal (Ceig (K' + m + 3) *
              (i.fst.val)⁻¹ ^ (eEig (K' + m + 3))) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖ := by
  classical
  intro i j hj idx K'
  have h_chart_cpt :
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K' + m + 3) 2
          (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
            g r s i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (Ceig (K' + m + 3) *
            (i.fst.val)⁻¹ ^ (eEig (K' + m + 3))) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖ :=
    hCeig_bd i (K' + m + 3)
  have h_chart_cpt_memWkp :
      MemWkp (d := Module.finrank ℝ E) ((2 + K') + j) 2
          (eigenvectorChartComponentFun (I := I) (M := M)
            g r s i α P₀)
          (chartTargetEuclid (I := I) (M := M) α) :=
    eigenvector_chartComponent_memWkp_arbitrary (I := I) (M := M)
      g r s i ((2 + K') + j) α P₀
  obtain ⟨_, h_partial⟩ :=
    eigenvectorChartIteratedPartial_wkpNorm_le_of_memWkp
      (I := I) (M := M) g r s i α P₀ j (2 + K') h_chart_cpt_memWkp idx
  have h_order_le : (2 + K') + j ≤ K' + m + 3 := by omega
  have h_mono :
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) ((2 + K') + j) 2
          (eigenvectorChartComponentFun (I := I) (M := M)
            g r s i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K' + m + 3) 2
            (eigenvectorChartComponentFun (I := I) (M := M)
              g r s i α P₀)
            (chartTargetEuclid (I := I) (M := M) α) :=
    wkpNorm_mono_order (d := Module.finrank ℝ E) h_order_le _ _
  exact h_partial.trans (h_mono.trans h_chart_cpt)

set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 2000000 in

omit [CompleteSpace E] in
theorem eigenvectorChartRHSDiff_eLpNorm_le_chartcpt
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (l : Fin m → Fin (Module.finrank ℝ E))
    (h_pou : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (m + 1 + 0) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
            EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β))
    (Ceig : ℕ → ℝ) (eEig : ℕ → ℕ) (hCeig_nn : ∀ K', 0 ≤ Ceig K')
    (hCeig_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s) (K' : ℕ),
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
          (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
            g r s i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (Ceig K' * (i.fst.val)⁻¹ ^ (eEig K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖)
    (CresH : ℕ → ℝ) (eResH : ℕ → ℕ) (hCresH_nn : ∀ K', 0 ≤ CresH K')
    (hCresH_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s) (K' : ℕ),
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K' + 1) 2
          (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
              (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                (eigenvectorResolvent (I := I) (M := M) g r s i))
              β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) β)
        ≤ ENNReal.ofReal (CresH K' * (i.fst.val)⁻¹ ^ (eResH K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖)
    (CresL : ℕ → ℝ) (eResL : ℕ → ℕ) (hCresL_nn : ∀ K', 0 ≤ CresL K')
    (hCresL_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s) (K' : ℕ),
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
              (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                (eigenvectorResolvent (I := I) (M := M) g r s i))
              β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) β)
        ≤ ENNReal.ofReal (CresL K' * (i.fst.val)⁻¹ ^ (eResL K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖)
    (Cpar : ℕ → ℝ) (ePar : ℕ → ℕ) (hCpar_nn : ∀ K', 0 ≤ Cpar K')
    (hCpar_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (P : TensorCompIdx (E := E) r s) (k : Fin (Module.finrank ℝ E)) (K' : ℕ),
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((partialLpLimit (I := I) (M := M)
              g r s i α P k :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (Cpar K' * (i.fst.val)⁻¹ ^ (ePar K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖)
    (Ccom : ℕ → ℝ) (eCom : ℕ → ℕ) (hCcom_nn : ∀ K', 0 ≤ Ccom K')
    (hCcom_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (p : TensorCompIdx (E := E) r s) (K' : ℕ),
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((componentLpLimit (I := I) (M := M)
              g r s i α p :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (Ccom K' * (i.fst.val)⁻¹ ^ (eCom K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖)
    (CcR : ℕ → ℝ) (eCcR : ℕ → ℕ) (hCcR_nn : ∀ K', 0 ≤ CcR K')
    (hCcR_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (P : TensorCompIdx (E := E) r s) (K' : ℕ),
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((crossRightLimitComponent (I := I) (M := M)
              g r s i α P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (CcR K' * (i.fst.val)⁻¹ ^ (eCcR K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖)
    (Ccut : ℕ → ℝ) (eCcut : ℕ → ℕ) (hCcut_nn : ∀ K', 0 ≤ Ccut K')
    (hCcut_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (P : TensorCompIdx (E := E) r s) (k : Fin (Module.finrank ℝ E)) (K' : ℕ),
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((cutoffPartialLpLimit (I := I) (M := M)
              g r s i α P k :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (Ccut K' * (i.fst.val)⁻¹ ^ (eCcut K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖) :
    ∃ (C : ℝ) (e : ℕ), 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm (eigenvectorChartRHSDiff (I := I) (M := M)
            g r s i α P₀ m l) 2
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal (C * (i.fst.val)⁻¹ ^ e) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖ := by
  classical
  obtain ⟨Cwk, hCwk_nn, hCwk_bd⟩ :=
    eigenvectorChartRHSDiff_eLpNorm_le_uniform (I := I) (M := M)
      g r s α P₀ m l h_pou
  set Citer : ℕ → ℝ := fun K' => Ceig (K' + m + 3) with hCiter_def
  set eIter : ℕ → ℕ := fun K' => eEig (K' + m + 3) with heIter_def
  have hCiter_nn : ∀ K', 0 ≤ Citer K' := fun K' => hCeig_nn (K' + m + 3)
  have hCiter_bd :
      ∀ (i : TensorEigenIdx (I := I) (M := M) g r s) (j : ℕ),
        j ≤ m + 1 →
        ∀ (idx : Fin j → Fin (Module.finrank ℝ E)) (K' : ℕ),
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (2 + K') 2
              (eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s i α P₀ j idx)
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal (Citer K' * (i.fst.val)⁻¹ ^ (eIter K')) *
              ENNReal.ofReal
                ‖tensorResolventEigenbasisVec (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator (I := I) (M := M)
                    g r s) i‖ :=
    iteratedPartial_wkpNorm_le_of_chart_perK (I := I) (M := M)
      g r s α P₀ m Ceig eEig hCeig_bd
  obtain ⟨Caggr, eAggr, hCaggr_nn, hCaggr_bd⟩ :=
    diffRHSAggregate_le_energy_perK (I := I) (M := M)
      g r s α P₀ m 0 l
      Ceig eEig hCeig_nn hCeig_bd
      CresH eResH hCresH_nn hCresH_bd
      CresL eResL hCresL_nn hCresL_bd
      Cpar ePar hCpar_nn hCpar_bd
      Ccom eCom hCcom_nn hCcom_bd
      CcR eCcR hCcR_nn hCcR_bd
      Ccut eCcut hCcut_nn hCcut_bd
      Citer eIter hCiter_nn hCiter_bd
  refine ⟨Cwk * Caggr, eAggr + 1, mul_nonneg hCwk_nn hCaggr_nn, fun i => ?_⟩
  have hμ_unit : i.fst.val ∈ Set.Ioc (0 : ℝ) 1 := by
    have h_norm :
        ‖tensorResolventEigenbasisVec (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M)
            g r s) i‖ = 1 :=
      (tensorResolventEigenbasisVec_orthonormal (I := I) (M := M)
        (g := g) (r := r) (s := s)
        (tensorResolventL2_isCompactOperator (I := I) (M := M)
          g r s)).norm_eq_one i
    exact tensorResolvent_eigenvalue_mem_unit_interval (I := I) (M := M) g r s
      (tensorResolventEigenbasisVec_mem (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M)
          g r s) i)
      (by
        intro h_zero
        rw [h_zero, norm_zero] at h_norm
        exact one_ne_zero h_norm.symm)
  have hμ_pos : 0 < i.fst.val := hμ_unit.1
  have hμ_le_one : i.fst.val ≤ 1 := hμ_unit.2
  have hμ_inv_nn : 0 ≤ (i.fst.val)⁻¹ := le_of_lt (inv_pos.mpr hμ_pos)
  have hμ_inv_ge_one : (1 : ℝ) ≤ (i.fst.val)⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hμ_pos]; simpa using hμ_le_one
  set Rhs : ℝ≥0∞ := ENNReal.ofReal
      ‖tensorResolventEigenbasisVec (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M)
          g r s) i‖ with hRhs_def
  calc eLpNorm (eigenvectorChartRHSDiff (I := I) (M := M)
          g r s i α P₀ m l) 2
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α))
      ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * Cwk) *
          diffRHSAggregate (I := I) (M := M)
            g r s i α P₀ m 0 l := hCwk_bd i
    _ ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * Cwk) *
          (ENNReal.ofReal (Caggr * (i.fst.val)⁻¹ ^ eAggr) * Rhs) :=
        mul_le_mul' (le_refl _) (hCaggr_bd i)
    _ = ENNReal.ofReal ((Cwk * Caggr) * (i.fst.val)⁻¹ ^ (eAggr + 1)) * Rhs := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        rw [pow_succ, mul_comm ((i.fst.val)⁻¹ ^ eAggr) (i.fst.val)⁻¹]
        ring

set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 2000000 in

omit [CompleteSpace E] in
theorem eigenvectorChartRHSDiff_wkpNormOne_le_chartcpt
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (l : Fin m → Fin (Module.finrank ℝ E))
    (h_pou : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (m + 1 + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
            EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β))
    (Ceig : ℕ → ℝ) (eEig : ℕ → ℕ) (hCeig_nn : ∀ K', 0 ≤ Ceig K')
    (hCeig_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s) (K' : ℕ),
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
          (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
            g r s i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (Ceig K' * (i.fst.val)⁻¹ ^ (eEig K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖)
    (CresH : ℕ → ℝ) (eResH : ℕ → ℕ) (hCresH_nn : ∀ K', 0 ≤ CresH K')
    (hCresH_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s) (K' : ℕ),
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K' + 1) 2
          (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
              (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                (eigenvectorResolvent (I := I) (M := M) g r s i))
              β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) β)
        ≤ ENNReal.ofReal (CresH K' * (i.fst.val)⁻¹ ^ (eResH K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖)
    (CresL : ℕ → ℝ) (eResL : ℕ → ℕ) (hCresL_nn : ∀ K', 0 ≤ CresL K')
    (hCresL_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s) (K' : ℕ),
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
              (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                (eigenvectorResolvent (I := I) (M := M) g r s i))
              β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) β)
        ≤ ENNReal.ofReal (CresL K' * (i.fst.val)⁻¹ ^ (eResL K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖)
    (Cpar : ℕ → ℝ) (ePar : ℕ → ℕ) (hCpar_nn : ∀ K', 0 ≤ Cpar K')
    (hCpar_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (P : TensorCompIdx (E := E) r s) (k : Fin (Module.finrank ℝ E)) (K' : ℕ),
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((partialLpLimit (I := I) (M := M)
              g r s i α P k :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (Cpar K' * (i.fst.val)⁻¹ ^ (ePar K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖)
    (Ccom : ℕ → ℝ) (eCom : ℕ → ℕ) (hCcom_nn : ∀ K', 0 ≤ Ccom K')
    (hCcom_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (p : TensorCompIdx (E := E) r s) (K' : ℕ),
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((componentLpLimit (I := I) (M := M)
              g r s i α p :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (Ccom K' * (i.fst.val)⁻¹ ^ (eCom K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖)
    (CcR : ℕ → ℝ) (eCcR : ℕ → ℕ) (hCcR_nn : ∀ K', 0 ≤ CcR K')
    (hCcR_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (P : TensorCompIdx (E := E) r s) (K' : ℕ),
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((crossRightLimitComponent (I := I) (M := M)
              g r s i α P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (CcR K' * (i.fst.val)⁻¹ ^ (eCcR K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖)
    (Ccut : ℕ → ℝ) (eCcut : ℕ → ℕ) (hCcut_nn : ∀ K', 0 ≤ Ccut K')
    (hCcut_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (P : TensorCompIdx (E := E) r s) (k : Fin (Module.finrank ℝ E)) (K' : ℕ),
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
          (fun y => ((cutoffPartialLpLimit (I := I) (M := M)
              g r s i α P k :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (Ccut K' * (i.fst.val)⁻¹ ^ (eCcut K')) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖) :
    ∃ (C : ℝ) (e : ℕ), 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) 1 2
            (eigenvectorChartRHSDiff (I := I) (M := M)
              g r s i α P₀ m l)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal (C * (i.fst.val)⁻¹ ^ e) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖ := by
  classical
  obtain ⟨Cwk, hCwk_nn, hCwk_bd⟩ :=
    eigenvectorChartRHSDiff_wkpNorm_le_uniform (I := I) (M := M)
      g r s α P₀ m 1 l h_pou
  set Citer : ℕ → ℝ := fun K' => Ceig (K' + m + 3) with hCiter_def
  set eIter : ℕ → ℕ := fun K' => eEig (K' + m + 3) with heIter_def
  have hCiter_nn : ∀ K', 0 ≤ Citer K' := fun K' => hCeig_nn (K' + m + 3)
  have hCiter_bd :
      ∀ (i : TensorEigenIdx (I := I) (M := M) g r s) (j : ℕ),
        j ≤ m + 1 →
        ∀ (idx : Fin j → Fin (Module.finrank ℝ E)) (K' : ℕ),
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (2 + K') 2
              (eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s i α P₀ j idx)
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal (Citer K' * (i.fst.val)⁻¹ ^ (eIter K')) *
              ENNReal.ofReal
                ‖tensorResolventEigenbasisVec (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator (I := I) (M := M)
                    g r s) i‖ :=
    iteratedPartial_wkpNorm_le_of_chart_perK (I := I) (M := M)
      g r s α P₀ m Ceig eEig hCeig_bd
  obtain ⟨Caggr, eAggr, hCaggr_nn, hCaggr_bd⟩ :=
    diffRHSAggregate_le_energy_perK (I := I) (M := M)
      g r s α P₀ m 1 l
      Ceig eEig hCeig_nn hCeig_bd
      CresH eResH hCresH_nn hCresH_bd
      CresL eResL hCresL_nn hCresL_bd
      Cpar ePar hCpar_nn hCpar_bd
      Ccom eCom hCcom_nn hCcom_bd
      CcR eCcR hCcR_nn hCcR_bd
      Ccut eCcut hCcut_nn hCcut_bd
      Citer eIter hCiter_nn hCiter_bd
  refine ⟨Cwk * Caggr, eAggr + 1, mul_nonneg hCwk_nn hCaggr_nn, fun i => ?_⟩
  have hμ_unit : i.fst.val ∈ Set.Ioc (0 : ℝ) 1 := by
    have h_norm :
        ‖tensorResolventEigenbasisVec (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M)
            g r s) i‖ = 1 :=
      (tensorResolventEigenbasisVec_orthonormal (I := I) (M := M)
        (g := g) (r := r) (s := s)
        (tensorResolventL2_isCompactOperator (I := I) (M := M)
          g r s)).norm_eq_one i
    exact tensorResolvent_eigenvalue_mem_unit_interval (I := I) (M := M) g r s
      (tensorResolventEigenbasisVec_mem (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M)
          g r s) i)
      (by
        intro h_zero
        rw [h_zero, norm_zero] at h_norm
        exact one_ne_zero h_norm.symm)
  have hμ_pos : 0 < i.fst.val := hμ_unit.1
  have hμ_le_one : i.fst.val ≤ 1 := hμ_unit.2
  have hμ_inv_nn : 0 ≤ (i.fst.val)⁻¹ := le_of_lt (inv_pos.mpr hμ_pos)
  set Rhs : ℝ≥0∞ := ENNReal.ofReal
      ‖tensorResolventEigenbasisVec (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M)
          g r s) i‖ with hRhs_def
  calc iteratedWeakSobolevNorm (d := Module.finrank ℝ E) 1 2
          (eigenvectorChartRHSDiff (I := I) (M := M)
            g r s i α P₀ m l)
          (chartTargetEuclid (I := I) (M := M) α)
      ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * Cwk) *
          diffRHSAggregate (I := I) (M := M)
            g r s i α P₀ m 1 l := hCwk_bd i
    _ ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * Cwk) *
          (ENNReal.ofReal (Caggr * (i.fst.val)⁻¹ ^ eAggr) * Rhs) :=
        mul_le_mul' (le_refl _) (hCaggr_bd i)
    _ = ENNReal.ofReal ((Cwk * Caggr) * (i.fst.val)⁻¹ ^ (eAggr + 1)) * Rhs := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        rw [pow_succ, mul_comm ((i.fst.val)⁻¹ ^ eAggr) (i.fst.val)⁻¹]
        ring

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry
