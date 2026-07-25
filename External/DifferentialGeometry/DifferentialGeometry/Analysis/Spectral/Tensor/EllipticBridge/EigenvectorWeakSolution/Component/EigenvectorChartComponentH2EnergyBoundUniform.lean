import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Component.EigenvectorChartComponentH2EnergyBound
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Iterated.EigenvectorIteratedData
import DifferentialGeometry.Analysis.Spectral.Tensor.NormEstimates.TensorChartComponentSobolevBound


noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

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
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma chartTargetEuclid_eq (α : M) :
    (chartTargetEuclid (I := I) (M := M) α : Set EuclN) =
      DifferentialGeometry.Analysis.Laplacian.MetricExtension.chartTargetEuclid
        (I := I) (M := M) α := rfl

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma chartPouKernel_eq_empty_of_pou_zero {α : M}
    (h_zero : ∀ x : M,
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 0) :
    chartPouKernel (I := I) (M := M) α = (∅ : Set EuclN) := by
  classical
  have h_supp_empty :
      Function.support (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) = ∅ := by
    ext x
    simp [Function.mem_support, h_zero x]
  have h_tsupp_empty :
      tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) = ∅ := by
    unfold tsupport
    rw [h_supp_empty]
    exact closure_empty
  unfold chartPouKernel
  rw [h_tsupp_empty]
  rw [Set.image_empty, Set.image_empty]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma chartPouKernel_eq_empty_of_notMem_activeFinset
    {α : M} (hα : α ∉ chartAtlasPOU_activeFinset I M) :
    chartPouKernel (I := I) (M := M) α = (∅ : Set EuclN) :=
  chartPouKernel_eq_empty_of_pou_zero
    (chartAtlasPOU_eq_zero_of_notMem_activeFinset (I := I) (M := M) hα)

omit [CompleteSpace E] in
private lemma eigenvectorChartComponentFun_ae_zero_of_notMem_activeFinset
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    {α : M} (hα : α ∉ chartAtlasPOU_activeFinset I M)
    (P₀ : TensorCompIdx (E := E) r s) :
    eigenvectorChartComponentFun_unconditional (I := I) (M := M) g r s i α P₀
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)] (fun _ : EuclN => (0 : ℝ)) := by
  classical
  have h_kernel_empty :
      chartPouKernel (I := I) (M := M) α = (∅ : Set EuclN) :=
    chartPouKernel_eq_empty_of_notMem_activeFinset (I := I) (M := M) hα
  have h_ae := eigenvectorChartComponentFun_ae_zero_off_chartPouKernel
    (I := I) (M := M) g r s i α P₀
  have h_target_eq := chartTargetEuclid_eq (I := I) (M := M) α
  have h_set_eq :
      DifferentialGeometry.Analysis.Laplacian.MetricExtension.chartTargetEuclid
            (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α =
        chartTargetEuclid (I := I) (M := M) α := by
    rw [h_kernel_empty, Set.diff_empty, ← h_target_eq]
  rw [h_set_eq] at h_ae
  exact h_ae

omit [CompleteSpace E] in
private lemma wkpNorm_two_eigenvectorChartComponentFun_eq_zero_of_notMem_activeFinset
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    {α : M} (hα : α ∉ chartAtlasPOU_activeFinset I M)
    (P₀ : TensorCompIdx (E := E) r s) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 2 2
        (eigenvectorChartComponentFun_unconditional (I := I) (M := M) g r s i α P₀)
        (chartTargetEuclid (I := I) (M := M) α) = 0 := by
  classical
  have h_chart_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α
  have h_ae_zero :=
    eigenvectorChartComponentFun_ae_zero_of_notMem_activeFinset
      (I := I) (M := M) g r s i hα P₀
  have h_swap :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) 2 2
          (eigenvectorChartComponentFun_unconditional (I := I) (M := M) g r s i α P₀)
          (chartTargetEuclid (I := I) (M := M) α) =
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) 2 2
          (fun _ : EuclN => (0 : ℝ))
          (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_congr_ae
      (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2) h_chart_open
      h_ae_zero
  rw [h_swap]
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_zero_fun_zero
    (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2) h_chart_open

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in

private noncomputable def perAlphaPCConstant
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) : ℝ :=
  Classical.choose
    (eigenvector_chartComponent_wkpNorm_two_energy_le
      (I := I) (M := M) g r s α P₀)

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in

omit [CompleteSpace E] in
private lemma perAlphaPCConstant_nonneg
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    0 ≤ perAlphaPCConstant (I := I) (M := M) g r s α P₀ :=
  (Classical.choose_spec
    (eigenvector_chartComponent_wkpNorm_two_energy_le
      (I := I) (M := M) g r s α P₀)).1

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in

omit [CompleteSpace E] in
private lemma perAlphaPCConstant_bound
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 2 2
        (eigenvectorChartComponentFun_unconditional (I := I) (M := M) g r s i α P₀)
        (chartTargetEuclid (I := I) (M := M) α)
      ≤ ENNReal.ofReal
          (perAlphaPCConstant (I := I) (M := M) g r s α P₀ *
            (i.fst.val)⁻¹) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M)
              g r s) i‖ :=
  (Classical.choose_spec
    (eigenvector_chartComponent_wkpNorm_two_energy_le
      (I := I) (M := M) g r s α P₀)).2 i

private noncomputable def totalActivePCConstant
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ℝ :=
  ∑ α ∈ chartAtlasPOU_activeFinset I M,
    ∑ P₀ : TensorCompIdx (E := E) r s,
      perAlphaPCConstant (I := I) (M := M) g r s α P₀

omit [CompleteSpace E] in
private lemma totalActivePCConstant_nonneg
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    0 ≤ totalActivePCConstant (I := I) (M := M) g r s := by
  classical
  unfold totalActivePCConstant
  refine Finset.sum_nonneg fun α _ => ?_
  exact Finset.sum_nonneg fun P₀ _ =>
    perAlphaPCConstant_nonneg (I := I) (M := M) g r s α P₀

omit [CompleteSpace E] in
private lemma perAlphaPCConstant_le_totalActivePCConstant
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {α : M} (hα : α ∈ chartAtlasPOU_activeFinset I M)
    (P₀ : TensorCompIdx (E := E) r s) :
    perAlphaPCConstant (I := I) (M := M) g r s α P₀ ≤
      totalActivePCConstant (I := I) (M := M) g r s := by
  classical
  unfold totalActivePCConstant
  have h_inner_le :
      perAlphaPCConstant (I := I) (M := M) g r s α P₀ ≤
        ∑ Q : TensorCompIdx (E := E) r s,
          perAlphaPCConstant (I := I) (M := M) g r s α Q :=
    Finset.single_le_sum
      (f := fun Q : TensorCompIdx (E := E) r s =>
        perAlphaPCConstant (I := I) (M := M) g r s α Q)
      (fun Q _ =>
        perAlphaPCConstant_nonneg (I := I) (M := M) g r s α Q)
      (Finset.mem_univ P₀)
  have h_outer_le :
      (∑ Q : TensorCompIdx (E := E) r s,
          perAlphaPCConstant (I := I) (M := M) g r s α Q) ≤
        ∑ β ∈ chartAtlasPOU_activeFinset I M,
          ∑ Q : TensorCompIdx (E := E) r s,
            perAlphaPCConstant (I := I) (M := M) g r s β Q :=
    Finset.single_le_sum
      (f := fun β : M =>
        ∑ Q : TensorCompIdx (E := E) r s,
          perAlphaPCConstant (I := I) (M := M) g r s β Q)
      (fun β _ => Finset.sum_nonneg fun Q _ =>
        perAlphaPCConstant_nonneg (I := I) (M := M) g r s β Q) hα
  exact h_inner_le.trans h_outer_le

set_option maxHeartbeats 800000 in
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in

omit [CompleteSpace E] in
theorem eigenvector_chartComponent_wkpNorm_two_energy_le_uniform_β_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (α : M) (P₀ : TensorCompIdx (E := E) r s)
        (i : TensorEigenIdx (I := I) (M := M) g r s),
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := Module.finrank ℝ E) 2 2
            (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
              g r s i α P₀)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal
              (C * (i.fst.val)⁻¹) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖ := by
  classical
  refine ⟨totalActivePCConstant (I := I) (M := M) g r s,
    totalActivePCConstant_nonneg (I := I) (M := M) g r s, ?_⟩
  intro α P₀ i
  by_cases hα : α ∈ chartAtlasPOU_activeFinset I M
  · have h_per :=
      perAlphaPCConstant_bound (I := I) (M := M) g r s α P₀ i
    have h_C_le :
        perAlphaPCConstant (I := I) (M := M) g r s α P₀ ≤
          totalActivePCConstant (I := I) (M := M) g r s :=
      perAlphaPCConstant_le_totalActivePCConstant
        (I := I) (M := M) g r s hα P₀
    have hμ_pos : 0 < i.fst.val := by
      have h_norm := tensorResolventEigenbasisVec_orthonormal
        (I := I) (M := M) (g := g) (r := r) (s := s)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
      have h_one :
          ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖ = 1 :=
        h_norm.norm_eq_one i
      have h_nonzero :
          tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i ≠ 0 := by
        intro h_zero
        rw [h_zero, norm_zero] at h_one
        exact one_ne_zero h_one.symm
      exact (tensorResolvent_eigenvalue_mem_unit_interval (I := I) (M := M)
        g r s
        (tensorResolventEigenbasisVec_mem (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M)
            g r s) i)
        h_nonzero).1
    have hμinv_nn : 0 ≤ (i.fst.val)⁻¹ := (inv_pos.mpr hμ_pos).le
    have h_per_const_nn :
        0 ≤ perAlphaPCConstant (I := I) (M := M) g r s α P₀ :=
      perAlphaPCConstant_nonneg (I := I) (M := M) g r s α P₀
    have h_real_le :
        perAlphaPCConstant (I := I) (M := M) g r s α P₀ *
            (i.fst.val)⁻¹ ≤
          totalActivePCConstant (I := I) (M := M) g r s *
            (i.fst.val)⁻¹ :=
      mul_le_mul_of_nonneg_right h_C_le hμinv_nn
    have h_const_le :
        ENNReal.ofReal
            (perAlphaPCConstant (I := I) (M := M) g r s α P₀ *
              (i.fst.val)⁻¹) ≤
          ENNReal.ofReal
            (totalActivePCConstant (I := I) (M := M) g r s *
              (i.fst.val)⁻¹) :=
      ENNReal.ofReal_le_ofReal h_real_le
    have h_envelope :
        ENNReal.ofReal
            (perAlphaPCConstant (I := I) (M := M) g r s α P₀ *
              (i.fst.val)⁻¹) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖ ≤
        ENNReal.ofReal
            (totalActivePCConstant (I := I) (M := M) g r s *
              (i.fst.val)⁻¹) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖ :=
      mul_le_mul_of_nonneg_right h_const_le (zero_le _)
    exact h_per.trans h_envelope
  · have h_zero :=
      wkpNorm_two_eigenvectorChartComponentFun_eq_zero_of_notMem_activeFinset
        (I := I) (M := M) g r s i hα P₀
    rw [h_zero]
    exact zero_le _

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
