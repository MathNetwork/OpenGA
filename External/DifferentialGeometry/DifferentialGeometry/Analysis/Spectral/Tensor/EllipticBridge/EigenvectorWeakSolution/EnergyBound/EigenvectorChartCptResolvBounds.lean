import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.RHS.DifferentiatedRHS.EigenvectorDifferentiatedRHS
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.EnergyBound.EigenvectorPouWkpNormTwins
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Smooth.SmoothApprox
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.RHS.ChartRHSBounds.EigenvectorChartRHSEpNorm

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

private lemma mu_mul_inv_pow_le_inv_pow
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
theorem eigenvector_chartComponent_perK_from_uniform_β_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (N : ℕ)
    (CN : ℝ) (_hCN_nn : 0 ≤ CN) (eN : ℕ)
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
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    ∀ (K' : ℕ), K' ≤ N →
      ∀ (i : TensorEigenIdx (I := I) (M := M) g r s),
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
            (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
              g r s i α P₀)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖ := by
  intro K' hK' i
  have h_mono : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
        (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
          g r s i α P₀)
        (chartTargetEuclid (I := I) (M := M) α)
      ≤ iteratedWeakSobolevNorm (d := Module.finrank ℝ E) N 2
        (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
          g r s i α P₀)
        (chartTargetEuclid (I := I) (M := M) α) :=
    wkpNorm_mono_order (d := Module.finrank ℝ E) hK'
      (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
        g r s i α P₀)
      (chartTargetEuclid (I := I) (M := M) α)
  exact h_mono.trans (hCN_bd α P₀ i)

omit [CompleteSpace E] in
private lemma resolvent_eq_mul_eigenvector
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
private lemma resolvent_chartComponent_eq_smul
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (β : M) (Q : TensorCompIdx (E := E) r s) :
    tensorL2ChartComponent (I := I) (M := M) g r s
        (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
          (eigenvectorResolvent (I := I) (M := M) g r s i)) β Q =
      i.fst.val •
        tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M)
              g r s) i) β Q := by
  rw [resolvent_eq_mul_eigenvector (I := I) (M := M) g r s i]
  exact tensorL2ChartComponent_smul (I := I) (M := M) g r s i.fst.val
    (tensorResolventEigenbasisVec (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M)
        g r s) i) β Q

omit [CompleteSpace E] in
private lemma resolvent_chartComponent_coe_ae_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (β : M) (Q : TensorCompIdx (E := E) r s) :
    (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s i))
          β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
      =ᵐ[(volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) β)]
      (fun y => i.fst.val *
        eigenvectorChartComponentFun_unconditional (I := I) (M := M)
          g r s i β Q y) := by
  have h_smul := Lp.coeFn_smul i.fst.val
    (tensorL2ChartComponent (I := I) (M := M) g r s
      (tensorResolventEigenbasisVec (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M)
          g r s) i) β Q)
  have h_eq : (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s i))
          β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
      =ᵐ[chartL2Measure (I := I) (M := M) β]
      (fun y => i.fst.val •
        eigenvectorChartComponentFun_unconditional (I := I) (M := M)
          g r s i β Q y) := by
    rw [resolvent_chartComponent_eq_smul
      (I := I) (M := M) g r s i β Q]
    exact h_smul
  filter_upwards [h_eq] with y hy
  rw [hy, smul_eq_mul]

omit [CompleteSpace E] in
private lemma eigenvectorChartComponentFun_memWkp_of_resolv
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (β : M) (Q : TensorCompIdx (E := E) r s) (K' : ℕ)
    (h_resolv : MemWkp (d := Module.finrank ℝ E) K' 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    MemWkp (d := Module.finrank ℝ E) K' 2
      (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
        g r s i β Q)
      (chartTargetEuclid (I := I) (M := M) β) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) β with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) β
  have h_scaled : MemWkp (d := Module.finrank ℝ E) K' 2
      (fun y => (i.fst.val)⁻¹ *
        ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
            EuclN → ℝ) y) Ω :=
    MemWkp.const_smul (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_resolv (i.fst.val)⁻¹
  have h_ae : (fun y => (i.fst.val)⁻¹ *
        ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
            EuclN → ℝ) y)
      =ᵐ[(volume : Measure EuclN).restrict Ω]
      (fun y => eigenvectorChartComponentFun_unconditional (I := I) (M := M)
        g r s i β Q y) := by
    have h_resc := resolvent_chartComponent_coe_ae_eq
      (I := I) (M := M) g r s i β Q
    have hμ_ne : i.fst.val ≠ 0 := i.fst.val_ne_zero
    filter_upwards [h_resc] with y hy
    rw [hy]
    field_simp
  exact (MemWkp_congr_ae (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae).mp h_scaled

omit [CompleteSpace E] in
theorem eigenvector_resolventHigh_perK_from_uniform_β_unconditional
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
      K' + 1 ≤ N →
      MemWkp (d := Module.finrank ℝ E) (K' + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    ∀ (K' : ℕ), K' + 1 ≤ N →
      ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
        (β : M) (Q : TensorCompIdx (E := E) r s),
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K' + 1) 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent (I := I) (M := M) g r s i))
                β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β)
          ≤ ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖ := by
  classical
  intro K' hK' i β Q
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) β with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) β
  have hμ_pos : 0 < i.fst.val := eigenval_pos_local
    (I := I) (M := M) g r s i
  have hμ_le_one : i.fst.val ≤ 1 := eigenval_le_one_local
    (I := I) (M := M) g r s i
  have h_resolv_mem : MemWkp (d := Module.finrank ℝ E) (K' + 1) 2
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s i))
          β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
      Ω :=
    h_pou_resolv i K' β Q hK'
  have h_eig_mem : MemWkp (d := Module.finrank ℝ E) (K' + 1) 2
      (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
        g r s i β Q) Ω :=
    eigenvectorChartComponentFun_memWkp_of_resolv
      (I := I) (M := M) g r s i β Q (K' + 1) h_resolv_mem
  have h_ae := resolvent_chartComponent_coe_ae_eq
    (I := I) (M := M) g r s i β Q
  have h_norm_eq : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K' + 1) 2
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s i))
          β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) Ω
      = iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K' + 1) 2
        (fun y => i.fst.val *
          eigenvectorChartComponentFun_unconditional (I := I) (M := M)
            g r s i β Q y) Ω :=
    wkpNorm_congr_ae (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae
  have h_smul_eq : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K' + 1) 2
      (fun y => i.fst.val *
        eigenvectorChartComponentFun_unconditional (I := I) (M := M)
          g r s i β Q y) Ω
      = ‖i.fst.val‖ₑ *
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K' + 1) 2
          (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
            g r s i β Q) Ω :=
    wkpNorm_const_smul (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_eig_mem i.fst.val
  have h_eig_bd : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K' + 1) 2
      (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
        g r s i β Q) Ω
      ≤ ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M)
              g r s) i‖ :=
    eigenvector_chartComponent_perK_from_uniform_β_unconditional
      (I := I) (M := M) g r s N CN hCN_nn eN hCN_bd β Q (K' + 1) hK' i
  rw [h_norm_eq, h_smul_eq]
  have h_norm_eq_val : ‖i.fst.val‖ₑ = ENNReal.ofReal i.fst.val := by
    rw [Real.enorm_eq_ofReal hμ_pos.le]
  rw [h_norm_eq_val]
  have h_step1 :
      ENNReal.ofReal i.fst.val *
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K' + 1) 2
          (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
            g r s i β Q) Ω
      ≤ ENNReal.ofReal i.fst.val *
          (ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖) :=
    mul_le_mul_of_nonneg_left h_eig_bd (zero_le _)
  have h_mul_assoc :
      ENNReal.ofReal i.fst.val *
        (ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖) =
      ENNReal.ofReal (i.fst.val * (CN * (i.fst.val)⁻¹ ^ eN)) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M)
              g r s) i‖ := by
    rw [← mul_assoc, ← ENNReal.ofReal_mul hμ_pos.le]
  have h_step2 :
      ENNReal.ofReal (i.fst.val * (CN * (i.fst.val)⁻¹ ^ eN)) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M)
              g r s) i‖
      ≤ ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M)
              g r s) i‖ := by
    refine mul_le_mul_of_nonneg_right ?_ (zero_le _)
    refine ENNReal.ofReal_le_ofReal ?_
    have h_reorder : i.fst.val * (CN * (i.fst.val)⁻¹ ^ eN)
        = CN * (i.fst.val * (i.fst.val)⁻¹ ^ eN) := by ring
    rw [h_reorder]
    have h_mu_bd := mu_mul_inv_pow_le_inv_pow hμ_pos hμ_le_one eN
    exact mul_le_mul_of_nonneg_left h_mu_bd hCN_nn
  calc
    ENNReal.ofReal i.fst.val *
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K' + 1) 2
          (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
            g r s i β Q) Ω
        ≤ ENNReal.ofReal i.fst.val *
            (ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
              ENNReal.ofReal
                ‖tensorResolventEigenbasisVec (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator
                    (I := I) (M := M) g r s) i‖) :=
      h_step1
    _ = ENNReal.ofReal (i.fst.val * (CN * (i.fst.val)⁻¹ ^ eN)) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖ :=
      h_mul_assoc
    _ ≤ ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖ :=
      h_step2

omit [CompleteSpace E] in
theorem eigenvector_resolventLow_perK_from_uniform_β_unconditional
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
        (chartTargetEuclid (I := I) (M := M) β)) :
    ∀ (K' : ℕ), K' ≤ N →
      ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
        (β : M) (Q : TensorCompIdx (E := E) r s),
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent (I := I) (M := M) g r s i))
                β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β)
          ≤ ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖ := by
  classical
  intro K' hK' i β Q
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) β with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) β
  have hμ_pos : 0 < i.fst.val := eigenval_pos_local
    (I := I) (M := M) g r s i
  have hμ_le_one : i.fst.val ≤ 1 := eigenval_le_one_local
    (I := I) (M := M) g r s i
  have h_resolv_mem : MemWkp (d := Module.finrank ℝ E) K' 2
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s i))
          β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
      Ω :=
    h_pou_resolv i K' β Q hK'
  have h_eig_mem : MemWkp (d := Module.finrank ℝ E) K' 2
      (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
        g r s i β Q) Ω :=
    eigenvectorChartComponentFun_memWkp_of_resolv
      (I := I) (M := M) g r s i β Q K' h_resolv_mem
  have h_ae := resolvent_chartComponent_coe_ae_eq
    (I := I) (M := M) g r s i β Q
  have h_norm_eq : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s i))
          β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) Ω
      = iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
        (fun y => i.fst.val *
          eigenvectorChartComponentFun_unconditional (I := I) (M := M)
            g r s i β Q y) Ω :=
    wkpNorm_congr_ae (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae
  have h_smul_eq : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
      (fun y => i.fst.val *
        eigenvectorChartComponentFun_unconditional (I := I) (M := M)
          g r s i β Q y) Ω
      = ‖i.fst.val‖ₑ *
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
          (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
            g r s i β Q) Ω :=
    wkpNorm_const_smul (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_eig_mem i.fst.val
  have h_eig_bd : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
      (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
        g r s i β Q) Ω
      ≤ ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M)
              g r s) i‖ :=
    eigenvector_chartComponent_perK_from_uniform_β_unconditional
      (I := I) (M := M) g r s N CN hCN_nn eN hCN_bd β Q K' hK' i
  rw [h_norm_eq, h_smul_eq]
  have h_norm_eq_val : ‖i.fst.val‖ₑ = ENNReal.ofReal i.fst.val := by
    rw [Real.enorm_eq_ofReal hμ_pos.le]
  rw [h_norm_eq_val]
  have h_step1 :
      ENNReal.ofReal i.fst.val *
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
          (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
            g r s i β Q) Ω
      ≤ ENNReal.ofReal i.fst.val *
          (ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖) :=
    mul_le_mul_of_nonneg_left h_eig_bd (zero_le _)
  have h_mul_assoc :
      ENNReal.ofReal i.fst.val *
        (ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖) =
      ENNReal.ofReal (i.fst.val * (CN * (i.fst.val)⁻¹ ^ eN)) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M)
              g r s) i‖ := by
    rw [← mul_assoc, ← ENNReal.ofReal_mul hμ_pos.le]
  have h_step2 :
      ENNReal.ofReal (i.fst.val * (CN * (i.fst.val)⁻¹ ^ eN)) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M)
              g r s) i‖
      ≤ ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M)
              g r s) i‖ := by
    refine mul_le_mul_of_nonneg_right ?_ (zero_le _)
    refine ENNReal.ofReal_le_ofReal ?_
    have h_reorder : i.fst.val * (CN * (i.fst.val)⁻¹ ^ eN)
        = CN * (i.fst.val * (i.fst.val)⁻¹ ^ eN) := by ring
    rw [h_reorder]
    have h_mu_bd := mu_mul_inv_pow_le_inv_pow hμ_pos hμ_le_one eN
    exact mul_le_mul_of_nonneg_left h_mu_bd hCN_nn
  calc
    ENNReal.ofReal i.fst.val *
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K' 2
          (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
            g r s i β Q) Ω
        ≤ ENNReal.ofReal i.fst.val *
            (ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
              ENNReal.ofReal
                ‖tensorResolventEigenbasisVec (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator
                    (I := I) (M := M) g r s) i‖) :=
      h_step1
    _ = ENNReal.ofReal (i.fst.val * (CN * (i.fst.val)⁻¹ ^ eN)) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖ :=
      h_mul_assoc
    _ ≤ ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖ :=
      h_step2

end Unconditional

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
