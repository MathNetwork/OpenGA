import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.EnergyBound.EigenvectorChartCptResolvBounds
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.EnergyBound.EigenvectorPouWkpNormTwins
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Cross.EigenvectorChartCrossRightLimit
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Cutoff.CutoffChartComponentWkpNorm

noncomputable section

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1000000

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
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [CompleteSpace E] in

private lemma mu_mul_inv_pow_le_inv_pow_local
    {μ : ℝ} (hμ_pos : 0 < μ) (hμ_le_one : μ ≤ 1) (eN : ℕ) :
    μ * μ⁻¹ ^ eN ≤ μ⁻¹ ^ eN := by
  have hμ_inv_nn : 0 ≤ μ⁻¹ := le_of_lt (inv_pos.mpr hμ_pos)
  have hμ_inv_pow_nn : 0 ≤ μ⁻¹ ^ eN := pow_nonneg hμ_inv_nn _
  have h : μ * μ⁻¹ ^ eN ≤ 1 * μ⁻¹ ^ eN :=
    mul_le_mul_of_nonneg_right hμ_le_one hμ_inv_pow_nn
  simpa using h

section Unconditional

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

omit [CompleteSpace E] in
private lemma vec_norm_eq_one_local
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
private lemma eigenval_pos_local
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    0 < i.fst.val :=
  (tensorResolvent_eigenvalue_mem_unit_interval (I := I) (M := M) g r s
    (tensorResolventEigenbasisVec_mem (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M)
        g r s) i)
    (by
      intro h_zero
      have h_norm := vec_norm_eq_one_local
        (I := I) (M := M) g r s i
      rw [h_zero, norm_zero] at h_norm
      exact one_ne_zero h_norm.symm)).1

omit [CompleteSpace E] in
private lemma eigenval_le_one_local
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    i.fst.val ≤ 1 :=
  (tensorResolvent_eigenvalue_mem_unit_interval (I := I) (M := M) g r s
    (tensorResolventEigenbasisVec_mem (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M)
        g r s) i)
    (by
      intro h_zero
      have h_norm := vec_norm_eq_one_local
        (I := I) (M := M) g r s i
      rw [h_zero, norm_zero] at h_norm
      exact one_ne_zero h_norm.symm)).2

omit [CompleteSpace E] in
private lemma eigenvectorVec_pou_memWkp_local
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
    MemWkp (d := Module.finrank ℝ E) N 2
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M)
              g r s) i) β Q :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
      (chartTargetEuclid (I := I) (M := M) β) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) β with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) β
  have h_res := h_pou β Q
  have h_chart_eq := eigenvector_chartComponent_eq (I := I) (M := M)
    g r s i β Q
  have h_ae : (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
        (tensorResolventEigenbasisVec (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M)
            g r s) i) β Q :
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
            (tensorResolventL2_isCompactOperator (I := I) (M := M)
              g r s) i) β Q :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        =ᵐ[chartL2Measure (I := I) (M := M) β]
        (fun y => (i.fst.val)⁻¹ •
          ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) := by
      rw [h_chart_eq]
      exact h_smul
    filter_upwards [h_smul'] with y hy
    rw [hy, smul_eq_mul]
  exact (MemWkp_congr_ae (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae).mpr
    (MemWkp.const_smul (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_res (i.fst.val)⁻¹)

omit [CompleteSpace E] in
private lemma resolvent_eq_mul_eigenvector_local
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    TensorH1ComplToTensorL2 (I := I) (M := M) g r s
        (eigenvectorResolvent (I := I) (M := M) g r s i) =
      i.fst.val •
        tensorResolventEigenbasisVec (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M)
            g r s) i := by
  have hμ_ne : i.fst.val ≠ 0 := i.fst.val_ne_zero
  rw [eigenvector_eq_resolvent_smul (I := I) (M := M) g r s i,
    smul_smul, mul_inv_cancel₀ hμ_ne, one_smul]

omit [CompleteSpace E] in
private lemma resolvent_cutoff_chartComponent_eq_smul
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s) :
    tensorL2ChartComponentCutoff (I := I) (M := M) g r s
        (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
          (eigenvectorResolvent (I := I) (M := M) g r s i)) α P =
      i.fst.val •
        tensorL2ChartComponentCutoff (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M)
              g r s) i) α P := by
  rw [← tensorL2ChartComponentCutoffCLM_apply (I := I) (M := M) g r s α P
      (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
        (eigenvectorResolvent (I := I) (M := M) g r s i)),
    resolvent_eq_mul_eigenvector_local (I := I) (M := M) g r s i,
    map_smul, tensorL2ChartComponentCutoffCLM_apply]

omit [CompleteSpace E] in
private lemma crossRightLimitComponent_coe_ae_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s) :
    (fun y => ((crossRightLimitComponent (I := I) (M := M)
          g r s i α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      =ᵐ[(volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      (fun y => i.fst.val *
        ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i) α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) := by
  have h_smul := Lp.coeFn_smul i.fst.val
    (tensorL2ChartComponentCutoff (I := I) (M := M) g r s
      (tensorResolventEigenbasisVec (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M)
          g r s) i) α P)
  have h_eq : (fun y => ((crossRightLimitComponent (I := I) (M := M)
        g r s i α P :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      =ᵐ[chartL2Measure (I := I) (M := M) α]
      (fun y => i.fst.val •
        ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M)
              g r s) i) α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) := by
    rw [crossRightLimitComponent,
      resolvent_cutoff_chartComponent_eq_smul
        (I := I) (M := M) g r s i α P]
    exact h_smul
  filter_upwards [h_eq] with y hy
  rw [hy, smul_eq_mul]

set_option maxHeartbeats 3200000 in

omit [CompleteSpace E] in
theorem eigenvector_crossRightLimit_perK_from_uniform_β_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (N : ℕ)
    (CN : ℝ) (hCN_nn : 0 ≤ CN) (eN : ℕ)
    (hCN_bd : ∀ (α : M) (P₀ : TensorCompIdx (E := E) r s)
        (i : TensorEigenIdx (I := I) (M := M) g r s),
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) N 2
          (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
            g r s i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖)
    (h_pou_resolv : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s) (K' : ℕ)
        (β : M) (Q : TensorCompIdx (E := E) r s),
      K' ≤ N →
      MemWkp (d := Module.finrank ℝ E) K' 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β))
    (α : M) :
    ∃ (C : ℕ → ℝ), (∀ K', 0 ≤ C K') ∧
      ∀ (K' : ℕ), K' ≤ N →
        ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
          (P : TensorCompIdx (E := E) r s),
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
              (fun y => ((crossRightLimitComponent (I := I) (M := M)
                  g r s i α P :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                  EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal (C K' * (i.fst.val)⁻¹ ^ eN) *
              ENNReal.ofReal
                ‖tensorResolventEigenbasisVec (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator (I := I) (M := M)
                    g r s) i‖ := by
  classical
  set d : ℕ := Module.finrank ℝ E with hd_def
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  set Cu : TensorCompIdx (E := E) r s → ℕ → ℝ := fun P k =>
    (wkpNorm_tensorL2ChartComponentCutoff_le_of_pou_uniform
      (I := I) (M := M) g r s α P k).choose with hCu_def
  have hCu_nn : ∀ P k, 0 ≤ Cu P k := fun P k =>
    (wkpNorm_tensorL2ChartComponentCutoff_le_of_pou_uniform
      (I := I) (M := M) g r s α P k).choose_spec.1
  have hCu_bd : ∀ P k (u : TensorL2 r s g),
      (∀ (β : M) (Q : TensorCompIdx (E := E) r s),
        MemWkp (d := d) k 2
          (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s u β Q :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) β)) →
      iteratedWeakSobolevNorm (d := d) k 2
          (fun y => ((tensorL2ChartComponentCutoff (I := I) (M := M)
            g r s u α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (Cu P k) *
          (∑ β ∈ transportChartCenters (I := I) (M := M) α,
            ∑ Q : TensorCompIdx (E := E) r s,
              iteratedWeakSobolevNorm (d := d) k 2
                (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                    u β Q :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                  EuclN → ℝ) y)
                (chartTargetEuclid (I := I) (M := M) β)) := fun P k u h_pou_u =>
    (wkpNorm_tensorL2ChartComponentCutoff_le_of_pou_uniform
      (I := I) (M := M) g r s α P k).choose_spec.2 u h_pou_u
  set Cu_max : ℕ → ℝ := fun k =>
    1 + ∑ P : TensorCompIdx (E := E) r s, Cu P k with hCu_max_def
  have hCu_max_nn : ∀ k, 0 ≤ Cu_max k := fun k => by
    rw [hCu_max_def]
    have h_sum_nn : 0 ≤ ∑ P : TensorCompIdx (E := E) r s, Cu P k :=
      Finset.sum_nonneg (fun P _ => hCu_nn P k)
    linarith
  have hCu_le_max : ∀ P k, Cu P k ≤ Cu_max k := by
    intro P k
    rw [hCu_max_def]
    have h_single : Cu P k ≤ ∑ P' : TensorCompIdx (E := E) r s, Cu P' k :=
      Finset.single_le_sum (f := fun P' => Cu P' k)
        (fun P' _ => hCu_nn P' k) (Finset.mem_univ P)
    linarith
  set S : M → Finset M := fun α' => transportChartCenters (I := I) (M := M) α'
    with hS_def
  set CT : ℕ := (S α).card *
    (Finset.univ : Finset (TensorCompIdx (E := E) r s)).card with hCT_def
  have hCT_real_nn : (0 : ℝ) ≤ (CT : ℝ) := Nat.cast_nonneg _
  set C : ℕ → ℝ := fun K' => Cu_max K' * (CT : ℝ) * CN with hC_def
  have hC_nn : ∀ K', 0 ≤ C K' := fun K' => by
    rw [hC_def]
    have h1 : 0 ≤ Cu_max K' * (CT : ℝ) := mul_nonneg (hCu_max_nn _) hCT_real_nn
    exact mul_nonneg h1 hCN_nn
  refine ⟨C, hC_nn, ?_⟩
  intro K' hK' i P
  have hμ_pos : 0 < i.fst.val :=
    eigenval_pos_local (I := I) (M := M) g r s i
  have hμ_le_one : i.fst.val ≤ 1 :=
    eigenval_le_one_local (I := I) (M := M) g r s i
  have h_pou_eigen : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := d) K' 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i) β Q :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β) :=
    fun β Q => eigenvectorVec_pou_memWkp_local
      (I := I) (M := M) g r s i K'
      (fun β' Q' => h_pou_resolv i K' β' Q' hK') β Q
  have h_cutoff_mem : MemWkp (d := d) K' 2
      (fun y => ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M)
              g r s) i) α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω :=
    tensorL2ChartComponentCutoff_memWkp_of_pou (I := I) (M := M) g r s
      (tensorResolventEigenbasisVec (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M)
          g r s) i) α P K'
      h_pou_eigen
  have h_ae_atom := crossRightLimitComponent_coe_ae_eq
    (I := I) (M := M) g r s i α P
  have h_norm_eq : iteratedWeakSobolevNorm (d := d) K' 2
      (fun y => ((crossRightLimitComponent (I := I) (M := M)
          g r s i α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω
      = iteratedWeakSobolevNorm (d := d) K' 2
        (fun y => i.fst.val *
          ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
              (tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i) α P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y) Ω :=
    wkpNorm_congr_ae (d := d)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae_atom
  have h_smul_eq : iteratedWeakSobolevNorm (d := d) K' 2
      (fun y => i.fst.val *
        ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i) α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
            EuclN → ℝ) y) Ω
      = ‖i.fst.val‖ₑ *
        iteratedWeakSobolevNorm (d := d) K' 2
          (fun y => ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
              (tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i) α P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y) Ω :=
    wkpNorm_const_smul (d := d)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_cutoff_mem i.fst.val
  have h_cutoff_le : iteratedWeakSobolevNorm (d := d) K' 2
      (fun y => ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M)
              g r s) i) α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω
      ≤ ENNReal.ofReal (Cu P K') *
        (∑ β ∈ S α, ∑ Q : TensorCompIdx (E := E) r s,
          iteratedWeakSobolevNorm (d := d) K' 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (tensorResolventEigenbasisVec (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator
                    (I := I) (M := M) g r s) i) β Q :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β)) :=
    hCu_bd P K' (tensorResolventEigenbasisVec (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M)
          g r s) i)
      h_pou_eigen
  have h_each_cpt_le : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      iteratedWeakSobolevNorm (d := d) K' 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i) β Q :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)
      ≤ ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M)
              g r s) i‖ := by
    intro β Q
    exact eigenvector_chartComponent_perK_from_uniform_β_unconditional
      (I := I) (M := M) g r s N CN hCN_nn eN hCN_bd β Q K' hK' i
  set RHS_each : ℝ≥0∞ := ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
    ENNReal.ofReal
      ‖tensorResolventEigenbasisVec (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M)
          g r s) i‖
    with hRHS_each_def
  have h_double_sum_le :
      (∑ β ∈ S α, ∑ Q : TensorCompIdx (E := E) r s,
        iteratedWeakSobolevNorm (d := d) K' 2
          (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
              (tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i) β Q :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) β))
      ≤ (CT : ℝ≥0∞) * RHS_each := by
    calc (∑ β ∈ S α, ∑ Q : TensorCompIdx (E := E) r s,
            iteratedWeakSobolevNorm (d := d) K' 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (tensorResolventEigenbasisVec (I := I) (M := M)
                    (tensorResolventL2_isCompactOperator
                      (I := I) (M := M) g r s) i) β Q :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β))
        ≤ ∑ _β ∈ S α, ∑ _Q : TensorCompIdx (E := E) r s, RHS_each :=
          Finset.sum_le_sum (fun β _hβ =>
            Finset.sum_le_sum (fun Q _hQ => h_each_cpt_le β Q))
      _ = (CT : ℝ≥0∞) * RHS_each := by
          simp only [Finset.sum_const, hCT_def, nsmul_eq_mul, Nat.cast_mul]
          ring
  have h_cutoff_max_le : iteratedWeakSobolevNorm (d := d) K' 2
      (fun y => ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M)
              g r s) i) α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω
      ≤ ENNReal.ofReal (Cu_max K') *
        (∑ β ∈ S α, ∑ Q : TensorCompIdx (E := E) r s,
          iteratedWeakSobolevNorm (d := d) K' 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (tensorResolventEigenbasisVec (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator
                    (I := I) (M := M) g r s) i) β Q :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β)) := by
    refine h_cutoff_le.trans ?_
    exact mul_le_mul_of_nonneg_right
      (ENNReal.ofReal_le_ofReal (hCu_le_max P K')) (zero_le _)
  have h_cutoff_le_final : iteratedWeakSobolevNorm (d := d) K' 2
      (fun y => ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M)
              g r s) i) α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω
      ≤ ENNReal.ofReal (Cu_max K') * ((CT : ℝ≥0∞) * RHS_each) := by
    refine h_cutoff_max_le.trans ?_
    exact mul_le_mul_of_nonneg_left h_double_sum_le (zero_le _)
  rw [h_norm_eq, h_smul_eq]
  have h_norm_eq_val : ‖i.fst.val‖ₑ = ENNReal.ofReal i.fst.val := by
    rw [Real.enorm_eq_ofReal hμ_pos.le]
  rw [h_norm_eq_val]
  have h_step_chain :
      ENNReal.ofReal i.fst.val *
        iteratedWeakSobolevNorm (d := d) K' 2
          (fun y => ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
              (tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i) α P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω
      ≤ ENNReal.ofReal i.fst.val *
          (ENNReal.ofReal (Cu_max K') * ((CT : ℝ≥0∞) * RHS_each)) :=
    mul_le_mul_of_nonneg_left h_cutoff_le_final (zero_le _)
  have hCu_max_nn_K' : 0 ≤ Cu_max K' := hCu_max_nn _
  have h_packCT : (CT : ℝ≥0∞) = ENNReal.ofReal (CT : ℝ) := by
    simp [hCT_def, ENNReal.ofReal_natCast]
  have h_pack_left :
      ENNReal.ofReal i.fst.val *
        (ENNReal.ofReal (Cu_max K') *
          ((CT : ℝ≥0∞) *
            (ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
              ENNReal.ofReal
                ‖tensorResolventEigenbasisVec (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator
                    (I := I) (M := M) g r s) i‖))) =
      ENNReal.ofReal (i.fst.val * Cu_max K' * (CT : ℝ) *
          (CN * (i.fst.val)⁻¹ ^ eN)) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M)
              g r s) i‖ := by
    rw [h_packCT]
    have hμ_nn : (0 : ℝ) ≤ i.fst.val := hμ_pos.le
    have hCN_pow_nn : (0 : ℝ) ≤ CN * (i.fst.val)⁻¹ ^ eN := by
      have hinv_nn : (0 : ℝ) ≤ (i.fst.val)⁻¹ := le_of_lt (inv_pos.mpr hμ_pos)
      exact mul_nonneg hCN_nn (pow_nonneg hinv_nn _)
    have hμCu_nn : (0 : ℝ) ≤ i.fst.val * Cu_max K' :=
      mul_nonneg hμ_nn hCu_max_nn_K'
    have hμCuCT_nn : (0 : ℝ) ≤ i.fst.val * Cu_max K' * (CT : ℝ) :=
      mul_nonneg hμCu_nn hCT_real_nn
    have hμCu_real_eq :
        ENNReal.ofReal i.fst.val * ENNReal.ofReal (Cu_max K') =
          ENNReal.ofReal (i.fst.val * Cu_max K') :=
      (ENNReal.ofReal_mul hμ_nn).symm
    have hCT_real_eq :
        ENNReal.ofReal (i.fst.val * Cu_max K') * ENNReal.ofReal (CT : ℝ) =
          ENNReal.ofReal (i.fst.val * Cu_max K' * (CT : ℝ)) :=
      (ENNReal.ofReal_mul hμCu_nn).symm
    have hCN_pow_eq :
        ENNReal.ofReal (i.fst.val * Cu_max K' * (CT : ℝ)) *
            ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) =
          ENNReal.ofReal (i.fst.val * Cu_max K' * (CT : ℝ) *
            (CN * (i.fst.val)⁻¹ ^ eN)) :=
      (ENNReal.ofReal_mul hμCuCT_nn).symm
    calc
      ENNReal.ofReal i.fst.val *
          (ENNReal.ofReal (Cu_max K') *
            (ENNReal.ofReal (CT : ℝ) *
              (ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
                ENNReal.ofReal
                  ‖tensorResolventEigenbasisVec (I := I) (M := M)
                    (tensorResolventL2_isCompactOperator
                      (I := I) (M := M) g r s) i‖)))
          = (ENNReal.ofReal i.fst.val * ENNReal.ofReal (Cu_max K')) *
              (ENNReal.ofReal (CT : ℝ) *
                (ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
                  ENNReal.ofReal
                    ‖tensorResolventEigenbasisVec (I := I) (M := M)
                      (tensorResolventL2_isCompactOperator
                        (I := I) (M := M) g r s) i‖)) := by
            ring
      _ = ENNReal.ofReal (i.fst.val * Cu_max K') *
            (ENNReal.ofReal (CT : ℝ) *
              (ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
                ENNReal.ofReal
                  ‖tensorResolventEigenbasisVec (I := I) (M := M)
                    (tensorResolventL2_isCompactOperator
                      (I := I) (M := M) g r s) i‖)) := by
            rw [hμCu_real_eq]
      _ = (ENNReal.ofReal (i.fst.val * Cu_max K') * ENNReal.ofReal (CT : ℝ)) *
            (ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
              ENNReal.ofReal
                ‖tensorResolventEigenbasisVec (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator
                    (I := I) (M := M) g r s) i‖) := by
            ring
      _ = ENNReal.ofReal (i.fst.val * Cu_max K' * (CT : ℝ)) *
            (ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
              ENNReal.ofReal
                ‖tensorResolventEigenbasisVec (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator
                    (I := I) (M := M) g r s) i‖) := by
            rw [hCT_real_eq]
      _ = (ENNReal.ofReal (i.fst.val * Cu_max K' * (CT : ℝ)) *
              ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN)) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator
                  (I := I) (M := M) g r s) i‖ := by
            ring
      _ = ENNReal.ofReal (i.fst.val * Cu_max K' * (CT : ℝ) *
            (CN * (i.fst.val)⁻¹ ^ eN)) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator
                  (I := I) (M := M) g r s) i‖ := by
            rw [hCN_pow_eq]
  have h_scalar_le :
      i.fst.val * Cu_max K' * (CT : ℝ) * (CN * (i.fst.val)⁻¹ ^ eN) ≤
        C K' * (i.fst.val)⁻¹ ^ eN := by
    rw [hC_def]
    have h_reorder :
        i.fst.val * Cu_max K' * (CT : ℝ) * (CN * (i.fst.val)⁻¹ ^ eN) =
          (Cu_max K' * (CT : ℝ) * CN) * (i.fst.val * (i.fst.val)⁻¹ ^ eN) := by
      ring
    rw [h_reorder]
    have hCC_nn : 0 ≤ Cu_max K' * (CT : ℝ) * CN := by
      have h1 : 0 ≤ Cu_max K' * (CT : ℝ) := mul_nonneg hCu_max_nn_K' hCT_real_nn
      exact mul_nonneg h1 hCN_nn
    exact mul_le_mul_of_nonneg_left
      (mu_mul_inv_pow_le_inv_pow_local hμ_pos hμ_le_one eN) hCC_nn
  have h_packed_le :
      ENNReal.ofReal (i.fst.val * Cu_max K' * (CT : ℝ) *
          (CN * (i.fst.val)⁻¹ ^ eN)) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M)
              g r s) i‖
      ≤ ENNReal.ofReal (C K' * (i.fst.val)⁻¹ ^ eN) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M)
              g r s) i‖ := by
    refine mul_le_mul_of_nonneg_right ?_ (zero_le _)
    exact ENNReal.ofReal_le_ofReal h_scalar_le
  calc
    ENNReal.ofReal i.fst.val *
        iteratedWeakSobolevNorm (d := d) K' 2
          (fun y => ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
              (tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i) α P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y) Ω
        ≤ ENNReal.ofReal i.fst.val *
            (ENNReal.ofReal (Cu_max K') * ((CT : ℝ≥0∞) * RHS_each)) := h_step_chain
    _ = ENNReal.ofReal (i.fst.val * Cu_max K' * (CT : ℝ) *
            (CN * (i.fst.val)⁻¹ ^ eN)) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖ := h_pack_left
    _ ≤ ENNReal.ofReal (C K' * (i.fst.val)⁻¹ ^ eN) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖ := h_packed_le

end Unconditional

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
