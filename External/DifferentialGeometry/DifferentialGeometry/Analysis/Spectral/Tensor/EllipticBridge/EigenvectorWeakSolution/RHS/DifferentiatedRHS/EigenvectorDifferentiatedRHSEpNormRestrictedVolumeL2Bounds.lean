import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.RHS.DifferentiatedRHS.EigenvectorDifferentiatedRHS
import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.IteratedSobolevQuant


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
open DifferentialGeometry.Tensor.TensorRSRiemannian
open TensorRSNabla
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl
open DifferentialGeometry.Analysis.Sobolev.Chart
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in

lemma eLpNorm_volume_restrict_contDiffOn_mul_le
    (α : M)
    {c : EuclN → ℝ}
    (hc : ContDiffOn ℝ ∞ c (chartTargetEuclid (I := I) (M := M) α))
    {K : Set EuclN} (hK_compact : IsCompact K) (hK_meas : MeasurableSet K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    (w : EuclN → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      eLpNorm (fun y => c y * w y) 2 ((volume : Measure EuclN).restrict K)
        ≤ ENNReal.ofReal C *
          eLpNorm w 2 ((volume : Measure EuclN).restrict K) := by
  classical
  set μ : Measure EuclN := (volume : Measure EuclN).restrict K with hμ_def
  have hcontOn_K : ContinuousOn c K := hc.continuousOn.mono hK_in
  have hbdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ‖c y‖ ≤ C := by
    by_cases hK_empty : K = ∅
    · exact ⟨0, le_refl _, fun y hy => absurd (hK_empty ▸ hy) (Set.notMem_empty y)⟩
    · obtain ⟨C₀, hC₀⟩ := hK_compact.bddAbove_image hcontOn_K.norm
      exact ⟨max C₀ 0, le_max_right _ _,
        fun y hy => (hC₀ ⟨y, hy, rfl⟩).trans (le_max_left _ _)⟩
  obtain ⟨C, hC_nn, hC_bd⟩ := hbdd
  refine ⟨C, hC_nn, ?_⟩
  have h_dom : ∀ᵐ y ∂μ, ‖c y * w y‖ ≤ ‖(C : ℝ) • w y‖ := by
    rw [hμ_def, ae_restrict_iff' hK_meas]
    refine Filter.Eventually.of_forall (fun y hyK => ?_)
    have hlhs : ‖c y * w y‖ = ‖c y‖ * ‖w y‖ := norm_mul _ _
    have hrhs : ‖(C : ℝ) • w y‖ = C * ‖w y‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC_nn]
    rw [hlhs, hrhs]
    exact mul_le_mul_of_nonneg_right (hC_bd y hyK) (norm_nonneg _)
  have h_mono :
      eLpNorm (fun y => c y * w y) 2 μ ≤ eLpNorm (fun y => (C : ℝ) • w y) 2 μ :=
    eLpNorm_mono_ae (μ := μ) h_dom
  have h_smul :
      eLpNorm (fun y => (C : ℝ) • w y) 2 μ
        = ENNReal.ofReal C * eLpNorm w 2 μ := by
    have h := eLpNorm_const_smul (μ := μ) (p := 2) (C : ℝ) w
    rw [Real.enorm_of_nonneg hC_nn] at h
    simpa only [Pi.smul_apply] using h
  calc
    eLpNorm (fun y => c y * w y) 2 μ
        ≤ eLpNorm (fun y => (C : ℝ) • w y) 2 μ := h_mono
    _ = ENNReal.ofReal C * eLpNorm w 2 μ := h_smul

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  [CompactSpace M] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] in

lemma eLpNorm_sum_le_const_mul_aggregate
    {ι : Type*} [Fintype ι] {μ : Measure EuclN} (F : ι → EuclN → ℝ)
    (A : ℝ≥0∞)
    (hF : ∀ j : ι, MemLp (F j) 2 μ)
    (hbd : ∀ j : ι, ∃ C : ℝ, 0 ≤ C ∧ eLpNorm (F j) 2 μ ≤ ENNReal.ofReal C * A) :
    ∃ C : ℝ, 0 ≤ C ∧
      eLpNorm (fun y => ∑ j : ι, F j y) 2 μ ≤ ENNReal.ofReal C * A := by
  classical
  choose Cf hCf_nn hCf using hbd
  refine ⟨(∑ j : ι, Cf j) * (Fintype.card ι : ℝ),
    mul_nonneg (Finset.sum_nonneg (fun j _ => hCf_nn j)) (by positivity), ?_⟩
  have h_fun : (fun y => ∑ j : ι, F j y) = ∑ j : ι, F j := by
    funext y
    exact (Finset.sum_apply y Finset.univ F).symm
  rw [h_fun]
  have h_tri : eLpNorm (∑ j : ι, F j) 2 μ ≤ ∑ j : ι, eLpNorm (F j) 2 μ :=
    eLpNorm_sum_le (fun j _ => (hF j).aestronglyMeasurable) (by norm_num)
  have h_step : ∑ j : ι, eLpNorm (F j) 2 μ
      ≤ ∑ _j : ι, ENNReal.ofReal (∑ k : ι, Cf k) * A := by
    refine Finset.sum_le_sum (fun j _ => ?_)
    refine (hCf j).trans ?_
    gcongr
    exact Finset.single_le_sum (fun k _ => hCf_nn k) (Finset.mem_univ j)
  have h_const : ∑ _j : ι, ENNReal.ofReal (∑ k : ι, Cf k) * A
      = (Fintype.card ι : ℝ≥0∞) *
          (ENNReal.ofReal (∑ k : ι, Cf k) * A) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h_cast : (Fintype.card ι : ℝ≥0∞) * ENNReal.ofReal (∑ k : ι, Cf k)
      = ENNReal.ofReal ((∑ j : ι, Cf j) * (Fintype.card ι : ℝ)) := by
    rw [mul_comm (∑ j : ι, Cf j), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_natCast]
  calc
    eLpNorm (∑ j : ι, F j) 2 μ
        ≤ ∑ j : ι, eLpNorm (F j) 2 μ := h_tri
    _ ≤ ∑ _j : ι, ENNReal.ofReal (∑ k : ι, Cf k) * A := h_step
    _ = (Fintype.card ι : ℝ≥0∞) *
          (ENNReal.ofReal (∑ k : ι, Cf k) * A) := h_const
    _ = ((Fintype.card ι : ℝ≥0∞) * ENNReal.ofReal (∑ k : ι, Cf k)) * A := by
        rw [mul_assoc]
    _ = ENNReal.ofReal ((∑ j : ι, Cf j) * (Fintype.card ι : ℝ)) * A := by
        rw [h_cast]

section MainBoundUniform

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in

omit [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma eLpNorm_volume_restrict_contDiffOn_mul_le_uniform
    (α : M)
    {c : EuclN → ℝ}
    (hc : ContDiffOn ℝ ∞ c (chartTargetEuclid (I := I) (M := M) α))
    {K : Set EuclN} (hK_compact : IsCompact K) (hK_meas : MeasurableSet K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : EuclN → ℝ,
      eLpNorm (fun y => c y * w y) 2 ((volume : Measure EuclN).restrict K)
        ≤ ENNReal.ofReal C *
          eLpNorm w 2 ((volume : Measure EuclN).restrict K) := by
  classical
  set μ : Measure EuclN := (volume : Measure EuclN).restrict K with hμ_def
  have hcontOn_K : ContinuousOn c K := hc.continuousOn.mono hK_in
  have hbdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ‖c y‖ ≤ C := by
    by_cases hK_empty : K = ∅
    · exact ⟨0, le_refl _, fun y hy => absurd (hK_empty ▸ hy) (Set.notMem_empty y)⟩
    · obtain ⟨C₀, hC₀⟩ := hK_compact.bddAbove_image hcontOn_K.norm
      exact ⟨max C₀ 0, le_max_right _ _,
        fun y hy => (hC₀ ⟨y, hy, rfl⟩).trans (le_max_left _ _)⟩
  obtain ⟨C, hC_nn, hC_bd⟩ := hbdd
  refine ⟨C, hC_nn, fun w => ?_⟩
  have h_dom : ∀ᵐ y ∂μ, ‖c y * w y‖ ≤ ‖(C : ℝ) • w y‖ := by
    rw [hμ_def, ae_restrict_iff' hK_meas]
    refine Filter.Eventually.of_forall (fun y hyK => ?_)
    have hlhs : ‖c y * w y‖ = ‖c y‖ * ‖w y‖ := norm_mul _ _
    have hrhs : ‖(C : ℝ) • w y‖ = C * ‖w y‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC_nn]
    rw [hlhs, hrhs]
    exact mul_le_mul_of_nonneg_right (hC_bd y hyK) (norm_nonneg _)
  have h_mono :
      eLpNorm (fun y => c y * w y) 2 μ ≤ eLpNorm (fun y => (C : ℝ) • w y) 2 μ :=
    eLpNorm_mono_ae (μ := μ) h_dom
  have h_smul :
      eLpNorm (fun y => (C : ℝ) • w y) 2 μ
        = ENNReal.ofReal C * eLpNorm w 2 μ := by
    have h := eLpNorm_const_smul (μ := μ) (p := 2) (C : ℝ) w
    rw [Real.enorm_of_nonneg hC_nn] at h
    simpa only [Pi.smul_apply] using h
  calc
    eLpNorm (fun y => c y * w y) 2 μ
        ≤ eLpNorm (fun y => (C : ℝ) • w y) 2 μ := h_mono
    _ = ENNReal.ofReal C * eLpNorm w 2 μ := h_smul

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in

lemma eLpNorm_sum_le_const_mul_aggregate_uniform
    {ι : Type*} [Fintype ι] {ν : Type*} {μ : Measure EuclN}
    (F : ι → ν → EuclN → ℝ) (A : ν → ℝ≥0∞)
    (hF : ∀ (j : ι) (n : ν), MemLp (F j n) 2 μ)
    (hbd : ∀ j : ι, ∃ C : ℝ, 0 ≤ C ∧
      ∀ n : ν, eLpNorm (F j n) 2 μ ≤ ENNReal.ofReal C * A n) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ n : ν,
        eLpNorm (fun y => ∑ j : ι, F j n y) 2 μ ≤ ENNReal.ofReal C * A n := by
  classical
  choose Cf hCf_nn hCf using hbd
  refine ⟨(∑ j : ι, Cf j) * (Fintype.card ι : ℝ),
    mul_nonneg (Finset.sum_nonneg (fun j _ => hCf_nn j)) (by positivity),
    fun n => ?_⟩
  have h_fun : (fun y => ∑ j : ι, F j n y) = ∑ j : ι, F j n := by
    funext y
    exact (Finset.sum_apply y Finset.univ (fun j => F j n)).symm
  rw [h_fun]
  have h_tri : eLpNorm (∑ j : ι, F j n) 2 μ ≤ ∑ j : ι, eLpNorm (F j n) 2 μ :=
    eLpNorm_sum_le (fun j _ => (hF j n).aestronglyMeasurable) (by norm_num)
  have h_step : ∑ j : ι, eLpNorm (F j n) 2 μ
      ≤ ∑ _j : ι, ENNReal.ofReal (∑ k : ι, Cf k) * A n := by
    refine Finset.sum_le_sum (fun j _ => ?_)
    refine (hCf j n).trans ?_
    gcongr
    exact Finset.single_le_sum (fun k _ => hCf_nn k) (Finset.mem_univ j)
  have h_const : ∑ _j : ι, ENNReal.ofReal (∑ k : ι, Cf k) * A n
      = (Fintype.card ι : ℝ≥0∞) *
          (ENNReal.ofReal (∑ k : ι, Cf k) * A n) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h_cast : (Fintype.card ι : ℝ≥0∞) * ENNReal.ofReal (∑ k : ι, Cf k)
      = ENNReal.ofReal ((∑ j : ι, Cf j) * (Fintype.card ι : ℝ)) := by
    rw [mul_comm (∑ j : ι, Cf j), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_natCast]
  calc
    eLpNorm (∑ j : ι, F j n) 2 μ
        ≤ ∑ j : ι, eLpNorm (F j n) 2 μ := h_tri
    _ ≤ ∑ _j : ι, ENNReal.ofReal (∑ k : ι, Cf k) * A n := h_step
    _ = (Fintype.card ι : ℝ≥0∞) *
          (ENNReal.ofReal (∑ k : ι, Cf k) * A n) := h_const
    _ = ((Fintype.card ι : ℝ≥0∞) * ENNReal.ofReal (∑ k : ι, Cf k)) * A n := by
        rw [mul_assoc]
    _ = ENNReal.ofReal ((∑ j : ι, Cf j) * (Fintype.card ι : ℝ)) * A n := by
        rw [h_cast]

end MainBoundUniform

section SharpAtomBounds

omit [CompleteSpace E] in

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma chosenWp_memLp_volume_restrict
    (b : Fin (Module.finrank ℝ E)) (w : EuclN → ℝ) {Ω K : Set EuclN}
    (hK_meas : MeasurableSet K) (hK_in : K ⊆ Ω) :
    MemLp (chosenWeakPartial' (d := Module.finrank ℝ E) 2 b w Ω) 2
      ((volume : Measure EuclN).restrict K) := by
  classical
  have h_global : MemLp (chosenWeakPartial' (d := Module.finrank ℝ E) 2 b w Ω)
      2 ((volume : Measure EuclN).restrict Ω) := by
    by_cases hw : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 w Ω
    · exact chosenWeakPartial'_memLp_of_mem hw b
    · rw [chosenWeakPartial'_of_not_mem hw b]
      exact MemLp.zero
  have h_eq : ((volume : Measure EuclN).restrict Ω).restrict K =
      (volume : Measure EuclN).restrict K := by
    rw [Measure.restrict_restrict hK_meas]
    exact congrArg _ (Set.inter_eq_self_of_subset_left hK_in)
  exact h_eq ▸ h_global.restrict K

end SharpAtomBounds

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
