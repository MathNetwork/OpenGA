import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.RHS.DifferentiatedRHS.EigenvectorDifferentiatedRHSWkpNorm
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.RHS.DifferentiatedRHS.EigenvectorDifferentiatedRHSWkp

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

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [CompleteSpace E] in
private lemma wkpNorm_coef_mul_factor_le
    (α : M) (K : ℕ)
    {coef factor : EuclN → ℝ}
    (hcoef_chart : ContDiffOn ℝ (⊤ : ℕ∞) coef
      (chartTargetEuclid (I := I) (M := M) α))
    (hfactor_memWkp : MemWkp (d := Module.finrank ℝ E) K 2 factor
      (chartTargetEuclid (I := I) (M := M) α))
    (hfactor_ae_zero : factor =ᵐ[(volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α \
        chartPouKernel (I := I) (M := M) α)] (fun _ => (0 : ℝ))) :
    MemWkp (d := Module.finrank ℝ E) K 2
        (fun y => coef y * factor y) (chartTargetEuclid (I := I) (M := M) α) ∧
      ∃ C : ℝ, 0 ≤ C ∧
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y => coef y * factor y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal C *
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 factor
              (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  set Kα : Set EuclN := chartPouKernel (I := I) (M := M) α with hKα_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hΩ_meas : MeasurableSet Ω := hΩ_open.measurableSet
  have hKα_compact : IsCompact Kα := chartPouKernel_isCompact (I := I) (M := M) α
  have hKα_in : Kα ⊆ Ω :=
    chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
  obtain ⟨δ, χ, hδ_pos, hδ_in, hχ_smooth, hχ_cs, _hχ_range, hχ_one, hχ_tsupp⟩ :=
    exists_smooth_cutoff_with_neighborhood (d := Module.finrank ℝ E)
      hKα_compact hΩ_open hKα_in
  have hχ_coef_smooth : ContDiff ℝ (⊤ : ℕ∞) (fun y => χ y * coef y) := by
    have h_open_compl : IsOpen ((tsupport χ)ᶜ) :=
      (isClosed_tsupport _).isOpen_compl
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy_supp : y ∈ tsupport χ
    · have hy_chart : y ∈ Ω := hχ_tsupp hy_supp
      exact hχ_smooth.contDiffAt.mul
        ((hcoef_chart y hy_chart).contDiffAt (hΩ_open.mem_nhds hy_chart))
    · have h_eq_zero : (fun y => χ y * coef y)
          =ᶠ[𝓝 y] (fun _ : EuclN => (0 : ℝ)) := by
        filter_upwards [h_open_compl.mem_nhds hy_supp] with z hz
        rw [image_eq_zero_of_notMem_tsupport hz, zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq h_eq_zero
  have hχ_coef_cs : HasCompactSupport (fun y => χ y * coef y) :=
    HasCompactSupport.mul_right hχ_cs
  obtain ⟨C₀, hC₀_nn, hC₀_bd⟩ :=
    exists_uniform_iteratedFDeriv_bound_of_smooth_compactSupport
      (d := Module.finrank ℝ E) hχ_coef_smooth hχ_coef_cs K
  have h_prod_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => (χ y * coef y) * factor y) Ω :=
    MemWkp.smul_smooth_bounded (d := Module.finrank ℝ E) K
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open hχ_coef_smooth
      (fun j _hj y _hy => hC₀_bd y j _hj) hfactor_memWkp
  obtain ⟨Kc, _hKc_pos, hKc_bd⟩ :=
    wkpNorm_smul_smooth_bounded_le (d := Module.finrank ℝ E) K
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by norm_num) hΩ_open hχ_coef_smooth
      hC₀_nn (fun j _hj y _hy => hC₀_bd y j _hj)
  set Cδ : Set EuclN := Metric.cthickening δ Kα with hCδ_def
  have hCδ_closed : IsClosed Cδ := Metric.isClosed_cthickening
  have hCδ_meas : MeasurableSet Cδ := hCδ_closed.measurableSet
  have h_ae_eq : (fun y => (χ y * coef y) * factor y)
      =ᵐ[(volume : Measure EuclN).restrict Ω]
      (fun y => coef y * factor y) := by
    have h_eq_on_Cδ : (fun y => (χ y * coef y) * factor y)
        =ᵐ[(volume : Measure EuclN).restrict Cδ]
        (fun y => coef y * factor y) := by
      refine (ae_restrict_iff' hCδ_meas).mpr ?_
      refine Filter.Eventually.of_forall fun y hy => ?_
      have hχy : χ y = 1 := hχ_one y hy
      change (χ y * coef y) * factor y = coef y * factor y
      rw [hχy]; ring
    have hKα_in_Cδ : Kα ⊆ Cδ := Metric.self_subset_cthickening _
    have h_diff_sub : Ω \ Cδ ⊆ Ω \ Kα := fun y hy =>
      ⟨hy.1, fun hyK => hy.2 (hKα_in_Cδ hyK)⟩
    have h_factor_ae_zero_diff : factor =ᵐ[(volume : Measure EuclN).restrict
        (Ω \ Cδ)] (fun _ => (0 : ℝ)) := by
      have h_abs : (volume : Measure EuclN).restrict (Ω \ Cδ) ≪
          (volume : Measure EuclN).restrict (Ω \ Kα) :=
        MeasureTheory.Measure.absolutelyContinuous_of_le
          (MeasureTheory.Measure.restrict_mono h_diff_sub le_rfl)
      exact h_abs.ae_le hfactor_ae_zero
    have h_eq_on_diff : (fun y => (χ y * coef y) * factor y)
        =ᵐ[(volume : Measure EuclN).restrict (Ω \ Cδ)]
        (fun y => coef y * factor y) := by
      filter_upwards [h_factor_ae_zero_diff] with y hy
      show (χ y * coef y) * factor y = coef y * factor y
      rw [hy]; ring
    have h_eq_on_inter : (fun y => (χ y * coef y) * factor y)
        =ᵐ[(volume : Measure EuclN).restrict (Ω ∩ Cδ)]
        (fun y => coef y * factor y) := by
      have h_abs : (volume : Measure EuclN).restrict (Ω ∩ Cδ) ≪
          (volume : Measure EuclN).restrict Cδ :=
        MeasureTheory.Measure.absolutelyContinuous_of_le
          (MeasureTheory.Measure.restrict_mono Set.inter_subset_right le_rfl)
      exact h_abs.ae_le h_eq_on_Cδ
    have h_diff_meas : MeasurableSet (Ω \ Cδ) := hΩ_meas.diff hCδ_meas
    have h_cover : Ω = (Ω ∩ Cδ) ∪ (Ω \ Cδ) := by
      ext y; constructor
      · intro hy
        by_cases h : y ∈ Cδ
        · exact Or.inl ⟨hy, h⟩
        · exact Or.inr ⟨hy, h⟩
      · rintro (⟨hy, _⟩ | ⟨hy, _⟩) <;> exact hy
    have h_disj : Disjoint (Ω ∩ Cδ) (Ω \ Cδ) :=
      Set.disjoint_left.mpr fun y hy hy' => hy'.2 hy.2
    have hΩ_restrict_eq : (volume : Measure EuclN).restrict Ω =
        (volume : Measure EuclN).restrict ((Ω ∩ Cδ) ∪ (Ω \ Cδ)) := by
      rw [← h_cover]
    rw [hΩ_restrict_eq, MeasureTheory.Measure.restrict_union h_disj h_diff_meas]
    exact (MeasureTheory.ae_add_measure_iff).mpr ⟨h_eq_on_inter, h_eq_on_diff⟩
  have h_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => coef y * factor y) Ω :=
    (MemWkp_congr_ae (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae_eq).mp h_prod_memWkp
  refine ⟨h_memWkp, Kc, le_of_lt _hKc_pos, ?_⟩
  have h_norm_eq : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
      (fun y => coef y * factor y) Ω =
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
        (fun y => (χ y * coef y) * factor y) Ω :=
    (wkpNorm_congr_ae (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae_eq).symm
  rw [h_norm_eq]
  exact hKc_bd hfactor_memWkp

omit [CompleteSpace E] in
private lemma wkpNorm_coef_mul_factor_le_uniform
    (α : M) (K : ℕ)
    {coef : EuclN → ℝ}
    (hcoef_chart : ContDiffOn ℝ (⊤ : ℕ∞) coef
      (chartTargetEuclid (I := I) (M := M) α)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ factor : EuclN → ℝ,
      MemWkp (d := Module.finrank ℝ E) K 2 factor
          (chartTargetEuclid (I := I) (M := M) α) →
      (factor =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α)] (fun _ => (0 : ℝ))) →
      MemWkp (d := Module.finrank ℝ E) K 2
          (fun y => coef y * factor y)
          (chartTargetEuclid (I := I) (M := M) α) ∧
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y => coef y * factor y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal C *
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 factor
              (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  set Kα : Set EuclN := chartPouKernel (I := I) (M := M) α with hKα_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hΩ_meas : MeasurableSet Ω := hΩ_open.measurableSet
  have hKα_compact : IsCompact Kα := chartPouKernel_isCompact (I := I) (M := M) α
  have hKα_in : Kα ⊆ Ω :=
    chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
  obtain ⟨δ, χ, hδ_pos, hδ_in, hχ_smooth, hχ_cs, _hχ_range, hχ_one, hχ_tsupp⟩ :=
    exists_smooth_cutoff_with_neighborhood (d := Module.finrank ℝ E)
      hKα_compact hΩ_open hKα_in
  have hχ_coef_smooth : ContDiff ℝ (⊤ : ℕ∞) (fun y => χ y * coef y) := by
    have h_open_compl : IsOpen ((tsupport χ)ᶜ) :=
      (isClosed_tsupport _).isOpen_compl
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy_supp : y ∈ tsupport χ
    · have hy_chart : y ∈ Ω := hχ_tsupp hy_supp
      exact hχ_smooth.contDiffAt.mul
        ((hcoef_chart y hy_chart).contDiffAt (hΩ_open.mem_nhds hy_chart))
    · have h_eq_zero : (fun y => χ y * coef y)
          =ᶠ[𝓝 y] (fun _ : EuclN => (0 : ℝ)) := by
        filter_upwards [h_open_compl.mem_nhds hy_supp] with z hz
        rw [image_eq_zero_of_notMem_tsupport hz, zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq h_eq_zero
  have hχ_coef_cs : HasCompactSupport (fun y => χ y * coef y) :=
    HasCompactSupport.mul_right hχ_cs
  obtain ⟨C₀, hC₀_nn, hC₀_bd⟩ :=
    exists_uniform_iteratedFDeriv_bound_of_smooth_compactSupport
      (d := Module.finrank ℝ E) hχ_coef_smooth hχ_coef_cs K
  obtain ⟨Kc, _hKc_pos, hKc_bd⟩ :=
    wkpNorm_smul_smooth_bounded_le (d := Module.finrank ℝ E) K
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by norm_num) hΩ_open hχ_coef_smooth
      hC₀_nn (fun j _hj y _hy => hC₀_bd y j _hj)
  set Cδ : Set EuclN := Metric.cthickening δ Kα with hCδ_def
  have hCδ_closed : IsClosed Cδ := Metric.isClosed_cthickening
  have hCδ_meas : MeasurableSet Cδ := hCδ_closed.measurableSet
  refine ⟨Kc, le_of_lt _hKc_pos, fun factor hfactor_memWkp hfactor_ae_zero => ?_⟩
  have h_prod_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => (χ y * coef y) * factor y) Ω :=
    MemWkp.smul_smooth_bounded (d := Module.finrank ℝ E) K
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open hχ_coef_smooth
      (fun j _hj y _hy => hC₀_bd y j _hj) hfactor_memWkp
  have h_ae_eq : (fun y => (χ y * coef y) * factor y)
      =ᵐ[(volume : Measure EuclN).restrict Ω]
      (fun y => coef y * factor y) := by
    have h_eq_on_Cδ : (fun y => (χ y * coef y) * factor y)
        =ᵐ[(volume : Measure EuclN).restrict Cδ]
        (fun y => coef y * factor y) := by
      refine (ae_restrict_iff' hCδ_meas).mpr ?_
      refine Filter.Eventually.of_forall fun y hy => ?_
      have hχy : χ y = 1 := hχ_one y hy
      change (χ y * coef y) * factor y = coef y * factor y
      rw [hχy]; ring
    have hKα_in_Cδ : Kα ⊆ Cδ := Metric.self_subset_cthickening _
    have h_diff_sub : Ω \ Cδ ⊆ Ω \ Kα := fun y hy =>
      ⟨hy.1, fun hyK => hy.2 (hKα_in_Cδ hyK)⟩
    have h_factor_ae_zero_diff : factor =ᵐ[(volume : Measure EuclN).restrict
        (Ω \ Cδ)] (fun _ => (0 : ℝ)) := by
      have h_abs : (volume : Measure EuclN).restrict (Ω \ Cδ) ≪
          (volume : Measure EuclN).restrict (Ω \ Kα) :=
        MeasureTheory.Measure.absolutelyContinuous_of_le
          (MeasureTheory.Measure.restrict_mono h_diff_sub le_rfl)
      exact h_abs.ae_le hfactor_ae_zero
    have h_eq_on_diff : (fun y => (χ y * coef y) * factor y)
        =ᵐ[(volume : Measure EuclN).restrict (Ω \ Cδ)]
        (fun y => coef y * factor y) := by
      filter_upwards [h_factor_ae_zero_diff] with y hy
      show (χ y * coef y) * factor y = coef y * factor y
      rw [hy]; ring
    have h_eq_on_inter : (fun y => (χ y * coef y) * factor y)
        =ᵐ[(volume : Measure EuclN).restrict (Ω ∩ Cδ)]
        (fun y => coef y * factor y) := by
      have h_abs : (volume : Measure EuclN).restrict (Ω ∩ Cδ) ≪
          (volume : Measure EuclN).restrict Cδ :=
        MeasureTheory.Measure.absolutelyContinuous_of_le
          (MeasureTheory.Measure.restrict_mono Set.inter_subset_right le_rfl)
      exact h_abs.ae_le h_eq_on_Cδ
    have h_diff_meas : MeasurableSet (Ω \ Cδ) := hΩ_meas.diff hCδ_meas
    have h_cover : Ω = (Ω ∩ Cδ) ∪ (Ω \ Cδ) := by
      ext y; constructor
      · intro hy
        by_cases h : y ∈ Cδ
        · exact Or.inl ⟨hy, h⟩
        · exact Or.inr ⟨hy, h⟩
      · rintro (⟨hy, _⟩ | ⟨hy, _⟩) <;> exact hy
    have h_disj : Disjoint (Ω ∩ Cδ) (Ω \ Cδ) :=
      Set.disjoint_left.mpr fun y hy hy' => hy'.2 hy.2
    have hΩ_restrict_eq : (volume : Measure EuclN).restrict Ω =
        (volume : Measure EuclN).restrict ((Ω ∩ Cδ) ∪ (Ω \ Cδ)) := by
      rw [← h_cover]
    rw [hΩ_restrict_eq, MeasureTheory.Measure.restrict_union h_disj h_diff_meas]
    exact (MeasureTheory.ae_add_measure_iff).mpr ⟨h_eq_on_inter, h_eq_on_diff⟩
  have h_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => coef y * factor y) Ω :=
    (MemWkp_congr_ae (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae_eq).mp h_prod_memWkp
  refine ⟨h_memWkp, ?_⟩
  have h_norm_eq : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
      (fun y => coef y * factor y) Ω =
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
        (fun y => (χ y * coef y) * factor y) Ω :=
    (wkpNorm_congr_ae (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae_eq).symm
  rw [h_norm_eq]
  exact hKc_bd hfactor_memWkp

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma memWkp_finset_sum
    {α : M} {K : ℕ} {ι : Type*} (s : Finset ι)
    {f : ι → EuclN → ℝ}
    (hf : ∀ i ∈ s, MemWkp (d := Module.finrank ℝ E) K 2 (f i)
      (chartTargetEuclid (I := I) (M := M) α)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ∑ i ∈ s, f i y) (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact MemWkp_zero_fun (d := Module.finrank ℝ E)
        (by norm_num : (1 : ℝ≥0∞) ≤ 2) h_open
  | insert i s his ih =>
      have hi : MemWkp (d := Module.finrank ℝ E) K 2 (f i)
          (chartTargetEuclid (I := I) (M := M) α) :=
        hf i (Finset.mem_insert_self _ _)
      have hsum := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
      have h_eq : (fun y => ∑ j ∈ insert i s, f j y) =
          (fun y => f i y + ∑ j ∈ s, f j y) := by
        funext y; rw [Finset.sum_insert his]
      rw [h_eq]
      exact MemWkp.add (d := Module.finrank ℝ E)
        (by norm_num : (1 : ℝ≥0∞) ≤ 2) h_open hi hsum

omit [CompleteSpace E] [CompactSpace M] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] in

omit [NeZero (Module.finrank ℝ E)] in
lemma one_div_densityOnEuclid_contDiffOn_chartTargetEuclid
    (g : SmoothRiemannianMetric I M) (α : M) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun y => 1 / densityOnEuclid (I := I) g α y)
      (chartTargetEuclid (I := I) (M := M) α) :=
  contDiffOn_const.div (densityOnEuclid_contDiffOn (I := I) g α)
    (fun _ hy => (densityOnEuclid_pos (I := I) g α hy).ne')

omit [CompleteSpace E] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in

omit [NeZero (Module.finrank ℝ E)] in
private lemma layerA_coeff_contDiffOn_chartTargetEuclid
    (g : SmoothRiemannianMetric I M) (α : M)
    (lₙ : Fin (Module.finrank ℝ E)) (a b : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y => (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b lₙ) y)
          (EuclideanSpace.single b 1))
      (chartTargetEuclid (I := I) (M := M) α) := by
  have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_diffOn : ContDiffOn ℝ (⊤ : ℕ∞)
      (weightedInvGramDerivOnEuclid (I := I) g α a b lₙ)
      (chartTargetEuclid (I := I) (M := M) α) :=
    weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α a b lₙ
  have h_fderiv : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y => fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b lₙ) y)
      (chartTargetEuclid (I := I) (M := M) α) :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen h_open).1 h_diffOn).2
  have h_eval : ContDiff ℝ (⊤ : ℕ∞)
      (fun (L : EuclN →L[ℝ] ℝ) => L (EuclideanSpace.single b 1)) :=
    (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single b (1 : ℝ))).contDiff
  exact h_eval.contDiffOn.comp h_fderiv (mapsTo_univ _ _)

omit [CompleteSpace E] in
lemma eigenvectorChartRHSDiffNumerator_ae_zero_off_chartPouKernel
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    {fChartEffPrev : EuclN → ℝ}
    (h_prev_zero : fChartEffPrev =ᵐ[(volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α \
        chartPouKernel (I := I) (M := M) α)]
      (fun _ => (0 : ℝ))) :
    eigenvectorChartRHSDiffNumerator (I := I) (M := M)
        g r s i α P₀ m l fChartEffPrev
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α)]
      (fun _ : EuclN => (0 : ℝ)) := by
  classical
  have hA_ae : ∀ a : Fin (Module.finrank ℝ E),
      eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l))
        =ᵐ[(volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α \
            chartPouKernel (I := I) (M := M) α)]
        (fun _ => (0 : ℝ)) := fun a =>
    eigenvectorChartIteratedPartial_ae_zero_off_chartPouKernel
      (I := I) (M := M) g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l))
  have hB_ae : ∀ a b : Fin (Module.finrank ℝ E),
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
        (chartTargetEuclid (I := I) (M := M) α)
        =ᵐ[(volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α \
            chartPouKernel (I := I) (M := M) α)]
        (fun _ => (0 : ℝ)) := fun a b =>
    chosenWeakPartial'_ae_zero_off_chartPouKernel_of_ae_zero
      (I := I) (M := M) α (hA_ae a) b
  have hC_ae := eigenvectorChartIteratedPartial_ae_zero_off_chartPouKernel
    (I := I) (M := M) g r s i α P₀ m (Fin.init l)
  have hE_ae := chosenWeakPartial'_ae_zero_off_chartPouKernel_of_ae_zero
    (I := I) (M := M) α h_prev_zero (l (Fin.last m))
  have hA_sum_ae : (fun y => ∑ a : Fin (Module.finrank ℝ E),
      ∑ b : Fin (Module.finrank ℝ E),
        (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
              (l (Fin.last m))) y)
            (EuclideanSpace.single b 1) *
          eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α)]
      (fun _ => (0 : ℝ)) := by
    have h_all : ∀ᵐ y ∂((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α)),
        ∀ a : Fin (Module.finrank ℝ E),
          eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y = 0 := by
      rw [Filter.eventually_all]
      intro a
      exact hA_ae a
    filter_upwards [h_all] with y hy
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
    change (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
          (l (Fin.last m))) y)
        (EuclideanSpace.single b 1) *
      eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y = 0
    rw [hy a]; ring
  have hB_sum_ae : (fun y => ∑ a : Fin (Module.finrank ℝ E),
      ∑ b : Fin (Module.finrank ℝ E),
        weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
          chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
            (chartTargetEuclid (I := I) (M := M) α) y)
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α)]
      (fun _ => (0 : ℝ)) := by
    have h_all : ∀ᵐ y ∂((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α)),
        ∀ a : Fin (Module.finrank ℝ E), ∀ b : Fin (Module.finrank ℝ E),
          chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
            (chartTargetEuclid (I := I) (M := M) α) y = 0 := by
      rw [Filter.eventually_all]
      intro a
      rw [Filter.eventually_all]
      intro b
      exact hB_ae a b
    filter_upwards [h_all] with y hy
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
    change weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
        (chartTargetEuclid (I := I) (M := M) α) y = 0
    rw [hy a b]; ring
  have hC_term_ae : (fun y =>
      densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
        eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ m (Fin.init l) y)
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α)]
      (fun _ => (0 : ℝ)) := by
    filter_upwards [hC_ae] with y hy
    show densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
      eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s i α P₀ m (Fin.init l) y = 0
    rw [hy]; ring
  have hD_term_ae : (fun y =>
      densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y * fChartEffPrev y)
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α)]
      (fun _ => (0 : ℝ)) := by
    filter_upwards [h_prev_zero] with y hy
    show densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
      fChartEffPrev y = 0
    rw [hy]; ring
  have hE_term_ae : (fun y =>
      densityOnEuclid (I := I) g α y *
        chosenWeakPartial' (d := Module.finrank ℝ E) 2 (l (Fin.last m))
          fChartEffPrev (chartTargetEuclid (I := I) (M := M) α) y)
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α)]
      (fun _ => (0 : ℝ)) := by
    filter_upwards [hE_ae] with y hy
    show densityOnEuclid (I := I) g α y *
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 (l (Fin.last m))
        fChartEffPrev (chartTargetEuclid (I := I) (M := M) α) y = 0
    rw [hy]; ring
  filter_upwards [hA_sum_ae, hB_sum_ae, hC_term_ae, hD_term_ae, hE_term_ae]
    with y hA hB hC hD hE
  show eigenvectorChartRHSDiffNumerator (I := I) (M := M)
      g r s i α P₀ m l fChartEffPrev y = 0
  unfold eigenvectorChartRHSDiffNumerator
  rw [hA, hB, hC, hD, hE]; ring

omit [CompleteSpace E] in
lemma eigenvectorChartRHSDiffNumerator_memWkp_of_iter
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    {fChartEffPrev : EuclN → ℝ}
    (h_iter : ∀ (j : ℕ) (idx : Fin j → Fin (Module.finrank ℝ E)),
      MemWkp (d := Module.finrank ℝ E) (2 + K) 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ j idx)
        (chartTargetEuclid (I := I) (M := M) α))
    (h_prev : MemWkp (d := Module.finrank ℝ E) (K + 1) 2 fChartEffPrev
      (chartTargetEuclid (I := I) (M := M) α))
    (h_prev_zero : fChartEffPrev =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α)] (fun _ => (0 : ℝ))) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (eigenvectorChartRHSDiffNumerator (I := I) (M := M)
        g r s i α P₀ m l fChartEffPrev)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hA : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ∑ a : Fin (Module.finrank ℝ E),
        ∑ b : Fin (Module.finrank ℝ E),
          (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
                (l (Fin.last m))) y)
              (EuclideanSpace.single b 1) *
            eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
      (chartTargetEuclid (I := I) (M := M) α) := by
    have h_pair : ∀ a b : Fin (Module.finrank ℝ E),
        MemWkp (d := Module.finrank ℝ E) K 2
          (fun y =>
            (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
                  (l (Fin.last m))) y)
                (EuclideanSpace.single b 1) *
              eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
          (chartTargetEuclid (I := I) (M := M) α) := by
      intro a b
      have h_factor_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
          (chartTargetEuclid (I := I) (M := M) α) :=
        (h_iter (m + 1) (Fin.cons a (Fin.init l))).le_of_le (by omega)
      have h_factor_ae_zero :=
        eigenvectorChartIteratedPartial_ae_zero_off_chartPouKernel
          (I := I) (M := M) g r s i α P₀ (m + 1)
          (Fin.cons a (Fin.init l))
      exact (wkpNorm_coef_mul_factor_le (I := I) (M := M) α K
        (layerA_coeff_contDiffOn_chartTargetEuclid (I := I) (M := M)
          g α (l (Fin.last m)) a b) h_factor_memWkp h_factor_ae_zero).1
    have h_inner : ∀ a : Fin (Module.finrank ℝ E),
        MemWkp (d := Module.finrank ℝ E) K 2
          (fun y => ∑ b : Fin (Module.finrank ℝ E),
            (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
                  (l (Fin.last m))) y)
                (EuclideanSpace.single b 1) *
              eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
          (chartTargetEuclid (I := I) (M := M) α) := fun a =>
      memWkp_finset_sum (I := I) (M := M) (α := α) (K := K) Finset.univ
        (fun b _hb => h_pair a b)
    exact memWkp_finset_sum (I := I) (M := M) (α := α) (K := K) Finset.univ
      (fun a _ha => h_inner a)
  have hB : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ∑ a : Fin (Module.finrank ℝ E),
        ∑ b : Fin (Module.finrank ℝ E),
          weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
            chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
              (eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
              (chartTargetEuclid (I := I) (M := M) α) y)
      (chartTargetEuclid (I := I) (M := M) α) := by
    have h_pair : ∀ a b : Fin (Module.finrank ℝ E),
        MemWkp (d := Module.finrank ℝ E) K 2
          (fun y =>
            weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
              chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
                (eigenvectorChartIteratedPartial (I := I) (M := M)
                  g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
                (chartTargetEuclid (I := I) (M := M) α) y)
          (chartTargetEuclid (I := I) (M := M) α) := by
      intro a b
      have h_inner_memWkp_succ : MemWkp (d := Module.finrank ℝ E) (K + 1) 2
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
          (chartTargetEuclid (I := I) (M := M) α) :=
        (h_iter (m + 1) (Fin.cons a (Fin.init l))).le_of_le (by omega)
      have h_factor_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
          (chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
            (chartTargetEuclid (I := I) (M := M) α))
          (chartTargetEuclid (I := I) (M := M) α) :=
        h_inner_memWkp_succ.chosenWeakPartial_mem b
      have h_inner_ae :=
        eigenvectorChartIteratedPartial_ae_zero_off_chartPouKernel
          (I := I) (M := M) g r s i α P₀ (m + 1)
          (Fin.cons a (Fin.init l))
      have h_factor_ae_zero :=
        chosenWeakPartial'_ae_zero_off_chartPouKernel_of_ae_zero
          (I := I) (M := M) α h_inner_ae b
      exact (wkpNorm_coef_mul_factor_le (I := I) (M := M) α K
        (weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α a b
          (l (Fin.last m))) h_factor_memWkp h_factor_ae_zero).1
    have h_inner : ∀ a : Fin (Module.finrank ℝ E),
        MemWkp (d := Module.finrank ℝ E) K 2
          (fun y => ∑ b : Fin (Module.finrank ℝ E),
            weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
              chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
                (eigenvectorChartIteratedPartial (I := I) (M := M)
                  g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
                (chartTargetEuclid (I := I) (M := M) α) y)
          (chartTargetEuclid (I := I) (M := M) α) := fun a =>
      memWkp_finset_sum (I := I) (M := M) (α := α) (K := K) Finset.univ
        (fun b _hb => h_pair a b)
    exact memWkp_finset_sum (I := I) (M := M) (α := α) (K := K) Finset.univ
      (fun a _ha => h_inner a)
  have hC : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y =>
        densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
          eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ m (Fin.init l) y)
      (chartTargetEuclid (I := I) (M := M) α) := by
    have h_factor_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ m (Fin.init l))
        (chartTargetEuclid (I := I) (M := M) α) :=
      (h_iter m (Fin.init l)).le_of_le (by omega)
    have h_factor_ae_zero :=
      eigenvectorChartIteratedPartial_ae_zero_off_chartPouKernel
        (I := I) (M := M) g r s i α P₀ m (Fin.init l)
    exact (wkpNorm_coef_mul_factor_le (I := I) (M := M) α K
      (densityDerivOnEuclid_contDiffOn (I := I) g α (l (Fin.last m)))
      h_factor_memWkp h_factor_ae_zero).1
  have hD : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y =>
        densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y * fChartEffPrev y)
      (chartTargetEuclid (I := I) (M := M) α) :=
    (wkpNorm_coef_mul_factor_le (I := I) (M := M) α K
      (densityDerivOnEuclid_contDiffOn (I := I) g α (l (Fin.last m)))
      (h_prev.le_of_le (by omega)) h_prev_zero).1
  have hE : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y =>
        densityOnEuclid (I := I) g α y *
          chosenWeakPartial' (d := Module.finrank ℝ E) 2 (l (Fin.last m))
            fChartEffPrev (chartTargetEuclid (I := I) (M := M) α) y)
      (chartTargetEuclid (I := I) (M := M) α) := by
    have h_factor_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
        (chosenWeakPartial' (d := Module.finrank ℝ E) 2 (l (Fin.last m))
          fChartEffPrev (chartTargetEuclid (I := I) (M := M) α))
        (chartTargetEuclid (I := I) (M := M) α) :=
      h_prev.chosenWeakPartial_mem (l (Fin.last m))
    have h_factor_ae_zero :=
      chosenWeakPartial'_ae_zero_off_chartPouKernel_of_ae_zero
        (I := I) (M := M) α h_prev_zero (l (Fin.last m))
    exact (wkpNorm_coef_mul_factor_le (I := I) (M := M) α K
      (densityOnEuclid_contDiffOn (I := I) g α)
      h_factor_memWkp h_factor_ae_zero).1
  have h_step1 := MemWkp.add (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) h_open hA hB
  have h_step2 := MemWkp.sub (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) h_open h_step1 hC
  have h_step3 := MemWkp.add (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) h_open h_step2 hD
  have h_step4 := MemWkp.add (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) h_open h_step3 hE
  have h_eq : (fun y =>
      ((((∑ a : Fin (Module.finrank ℝ E),
        ∑ b : Fin (Module.finrank ℝ E),
          (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
                (l (Fin.last m))) y)
              (EuclideanSpace.single b 1) *
            eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y) +
        (∑ a : Fin (Module.finrank ℝ E),
          ∑ b : Fin (Module.finrank ℝ E),
            weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
              chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
                (eigenvectorChartIteratedPartial (I := I) (M := M)
                  g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
                (chartTargetEuclid (I := I) (M := M) α) y)) -
        densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
          eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ m (Fin.init l) y) +
        densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
          fChartEffPrev y) +
        densityOnEuclid (I := I) g α y *
          chosenWeakPartial' (d := Module.finrank ℝ E) 2 (l (Fin.last m))
            fChartEffPrev (chartTargetEuclid (I := I) (M := M) α) y) =
      eigenvectorChartRHSDiffNumerator (I := I) (M := M)
        g r s i α P₀ m l fChartEffPrev := by
    funext y
    rfl
  rw [← h_eq]
  exact h_step4

section DivDensityBoundUnconditional

omit [CompleteSpace E] in
theorem eigenvectorChartRHSDiffNumerator_div_density_wkpNorm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (fChartEffPrev : EuclN → ℝ)
    (h_iter : ∀ (j : ℕ) (idx : Fin j → Fin (Module.finrank ℝ E)),
      MemWkp (d := Module.finrank ℝ E) (2 + K) 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ j idx)
        (chartTargetEuclid (I := I) (M := M) α))
    (h_prev : MemWkp (d := Module.finrank ℝ E) (K + 1) 2 fChartEffPrev
      (chartTargetEuclid (I := I) (M := M) α))
    (h_prev_zero : fChartEffPrev =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α)] (fun _ => (0 : ℝ))) :
    ∃ C : ℝ, 0 ≤ C ∧
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (fun y =>
            eigenvectorChartRHSDiffNumerator (I := I) (M := M)
              g r s i α P₀ m l fChartEffPrev y /
            densityOnEuclid (I := I) g α y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal C *
          diffNumeratorAggregateK (I := I) (M := M)
            g r s i α P₀ m K l fChartEffPrev := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  set A := diffNumeratorAggregateK (I := I) (M := M)
    g r s i α P₀ m K l fChartEffPrev with hA_def
  set numFun : EuclN → ℝ := eigenvectorChartRHSDiffNumerator
    (I := I) (M := M) g r s i α P₀ m l fChartEffPrev with hnumFun_def
  have h_eq : (fun y => numFun y / densityOnEuclid (I := I) g α y) =
      (fun y => (1 / densityOnEuclid (I := I) g α y) * numFun y) := by
    funext y
    rw [one_div, mul_comm, ← div_eq_mul_inv]
  rw [h_eq]
  obtain ⟨C₁, hC₁_nn, hC₁⟩ := eigenvectorChartRHSDiffNumerator_wkpNorm_le
    (I := I) (M := M) g r s i α P₀ m K l fChartEffPrev
    h_iter h_prev h_prev_zero
  rw [← hΩ_def, ← hA_def, ← hnumFun_def] at hC₁
  have h_num_memWkp : MemWkp (d := Module.finrank ℝ E) K 2 numFun Ω := by
    rw [hnumFun_def, ← hΩ_def] at *
    exact eigenvectorChartRHSDiffNumerator_memWkp_of_iter
      (I := I) (M := M) g r s i α P₀ m K l
      h_iter h_prev h_prev_zero
  have h_num_ae_zero :
      numFun =ᵐ[(volume : Measure EuclN).restrict
        (Ω \ chartPouKernel (I := I) (M := M) α)] (fun _ : EuclN => (0 : ℝ)) := by
    rw [hnumFun_def, hΩ_def]
    exact eigenvectorChartRHSDiffNumerator_ae_zero_off_chartPouKernel
      (I := I) (M := M) g r s i α P₀ m l h_prev_zero
  obtain ⟨_h_prod_mem, C₂, hC₂_nn, hC₂⟩ := wkpNorm_coef_mul_factor_le
    (I := I) (M := M) α K
    (one_div_densityOnEuclid_contDiffOn_chartTargetEuclid (I := I) (M := M) g α)
    h_num_memWkp h_num_ae_zero
  rw [← hΩ_def] at hC₂
  refine ⟨C₂ * C₁, mul_nonneg hC₂_nn hC₁_nn, ?_⟩
  calc
    iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
        (fun y => (1 / densityOnEuclid (I := I) g α y) * numFun y) Ω
        ≤ ENNReal.ofReal C₂ * iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 numFun Ω :=
          hC₂
    _ ≤ ENNReal.ofReal C₂ * (ENNReal.ofReal C₁ * A) := by
          gcongr
    _ = ENNReal.ofReal (C₂ * C₁) * A := by
          rw [ENNReal.ofReal_mul hC₂_nn, mul_assoc]

omit [CompleteSpace E] in
theorem eigenvectorChartRHSDiffNumerator_div_density_wkpNorm_le_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (fChartEffPrev : TensorEigenIdx (I := I) (M := M) g r s → EuclN → ℝ)
    (h_iter : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
        (j : ℕ) (idx : Fin j → Fin (Module.finrank ℝ E)),
      MemWkp (d := Module.finrank ℝ E) (2 + K) 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ j idx)
        (chartTargetEuclid (I := I) (M := M) α))
    (h_prev : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2 (fChartEffPrev i)
        (chartTargetEuclid (I := I) (M := M) α))
    (h_prev_zero : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      (fChartEffPrev i) =ᵐ[(volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α \
            chartPouKernel (I := I) (M := M) α)] (fun _ => (0 : ℝ))) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y =>
              eigenvectorChartRHSDiffNumerator (I := I) (M := M)
                g r s i α P₀ m l (fChartEffPrev i) y /
              densityOnEuclid (I := I) g α y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal C *
            diffNumeratorAggregateK (I := I) (M := M)
              g r s i α P₀ m K l (fChartEffPrev i) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  obtain ⟨C₁, hC₁_nn, hC₁⟩ :=
    eigenvectorChartRHSDiffNumerator_wkpNorm_le_uniform
      (I := I) (M := M) g r s α P₀ m K l fChartEffPrev
      h_iter h_prev h_prev_zero
  obtain ⟨C₂, hC₂_nn, hC₂⟩ := wkpNorm_coef_mul_factor_le_uniform
    (I := I) (M := M) α K
    (one_div_densityOnEuclid_contDiffOn_chartTargetEuclid (I := I) (M := M) g α)
  refine ⟨C₂ * C₁, mul_nonneg hC₂_nn hC₁_nn, fun i => ?_⟩
  set A := diffNumeratorAggregateK (I := I) (M := M)
    g r s i α P₀ m K l (fChartEffPrev i) with hA_def
  set numFun : EuclN → ℝ := eigenvectorChartRHSDiffNumerator
    (I := I) (M := M) g r s i α P₀ m l (fChartEffPrev i) with hnumFun_def
  have h_eq : (fun y => numFun y / densityOnEuclid (I := I) g α y) =
      (fun y => (1 / densityOnEuclid (I := I) g α y) * numFun y) := by
    funext y
    rw [one_div, mul_comm, ← div_eq_mul_inv]
  rw [h_eq]
  have hC₁_i : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 numFun Ω
      ≤ ENNReal.ofReal C₁ * A := by
    have := hC₁ i
    rw [← hnumFun_def, ← hΩ_def, ← hA_def] at this
    exact this
  have h_num_memWkp : MemWkp (d := Module.finrank ℝ E) K 2 numFun Ω := by
    rw [hnumFun_def, hΩ_def]
    exact eigenvectorChartRHSDiffNumerator_memWkp_of_iter
      (I := I) (M := M) g r s i α P₀ m K l
      (h_iter i) (h_prev i) (h_prev_zero i)
  have h_num_ae_zero :
      numFun =ᵐ[(volume : Measure EuclN).restrict
        (Ω \ chartPouKernel (I := I) (M := M) α)] (fun _ : EuclN => (0 : ℝ)) := by
    rw [hnumFun_def, hΩ_def]
    exact eigenvectorChartRHSDiffNumerator_ae_zero_off_chartPouKernel
      (I := I) (M := M) g r s i α P₀ m l (h_prev_zero i)
  have hC₂_i := (hC₂ numFun h_num_memWkp h_num_ae_zero).2
  rw [← hΩ_def] at hC₂_i
  calc
    iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
        (fun y => (1 / densityOnEuclid (I := I) g α y) * numFun y) Ω
        ≤ ENNReal.ofReal C₂ * iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 numFun Ω :=
          hC₂_i
    _ ≤ ENNReal.ofReal C₂ * (ENNReal.ofReal C₁ * A) := by
          gcongr
    _ = ENNReal.ofReal (C₂ * C₁) * A := by
          rw [ENNReal.ofReal_mul hC₂_nn, mul_assoc]

end DivDensityBoundUnconditional

section IteratedStepBoundUnconditional

omit [CompleteSpace E] in
theorem eigenvectorChartIteratedStep_wkpNorm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    {fChartEffPrev : EuclN → ℝ}
    (l : Fin (Module.finrank ℝ E))
    (h_iter : ∀ (j : ℕ) (idx : Fin j → Fin (Module.finrank ℝ E)),
      MemWkp (d := Module.finrank ℝ E) (2 + K) 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ j idx)
        (chartTargetEuclid (I := I) (M := M) α))
    (h_prev : MemWkp (d := Module.finrank ℝ E) (K + 1) 2 fChartEffPrev
      (chartTargetEuclid (I := I) (M := M) α))
    (h_prev_zero : fChartEffPrev =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α)] (fun _ => (0 : ℝ))) :
    ∃ C : ℝ, 0 ≤ C ∧
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (eigenvectorChartIteratedStep (I := I) (M := M)
            g r s i α P₀ m dirs fChartEffPrev l)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal C *
          diffNumeratorAggregateK (I := I) (M := M)
            g r s i α P₀ m K (Fin.snoc dirs l) fChartEffPrev := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  set Q : EuclN → ℝ := fun y =>
    eigenvectorChartRHSDiffNumerator (I := I) (M := M)
      g r s i α P₀ m (Fin.snoc dirs l) fChartEffPrev y /
    densityOnEuclid (I := I) g α y with hQ_def
  have h_step_eq :
      eigenvectorChartIteratedStep (I := I) (M := M)
        g r s i α P₀ m dirs fChartEffPrev l =
      Set.indicator (chartPouKernel (I := I) (M := M) α) Q := by
    unfold eigenvectorChartIteratedStep
    have h_num := eigenvectorChartIteratedStepNumerator_eq_rhsDiffNumerator
      (I := I) (M := M) g r s i α P₀ m dirs fChartEffPrev l
    funext y
    simp only [hQ_def]
    rw [h_num]
  have hQ_ae_zero : Q =ᵐ[(volume : Measure EuclN).restrict
      (Ω \ chartPouKernel (I := I) (M := M) α)]
      (fun _ : EuclN => (0 : ℝ)) := by
    rw [hQ_def, hΩ_def]
    exact eigenvectorChartRHSDiffNumerator_div_density_ae_zero_off_chartPouKernel
      (I := I) (M := M) g r s i α P₀ m (Fin.snoc dirs l) h_prev_zero
  have h_indicator_ae_eq_Q :
      Set.indicator (chartPouKernel (I := I) (M := M) α) Q =ᵐ[
        (volume : Measure EuclN).restrict Ω] Q := by
    set Kα : Set EuclN := chartPouKernel (I := I) (M := M) α with hKα_def
    have hΩ_meas : MeasurableSet Ω :=
      (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
    have hKα_meas : MeasurableSet Kα :=
      chartPouKernel_measurableSet (I := I) (M := M) α
    have h_inter_meas : MeasurableSet (Ω ∩ Kα) := hΩ_meas.inter hKα_meas
    have h_eq_on_inter : Set.indicator Kα Q =ᵐ[
        (volume : Measure EuclN).restrict (Ω ∩ Kα)] Q := by
      refine (ae_restrict_iff' h_inter_meas).mpr ?_
      refine Filter.Eventually.of_forall fun y hy => ?_
      exact Set.indicator_of_mem hy.2 _
    have h_diff_meas : MeasurableSet (Ω \ Kα) := hΩ_meas.diff hKα_meas
    have h_indicator_ae_zero : Set.indicator Kα Q =ᵐ[
        (volume : Measure EuclN).restrict (Ω \ Kα)]
        (fun _ : EuclN => (0 : ℝ)) := by
      refine (ae_restrict_iff' h_diff_meas).mpr ?_
      refine Filter.Eventually.of_forall fun y hy => ?_
      exact Set.indicator_of_notMem hy.2 _
    have h_eq_on_diff : Set.indicator Kα Q =ᵐ[
        (volume : Measure EuclN).restrict (Ω \ Kα)] Q := by
      filter_upwards [h_indicator_ae_zero, hQ_ae_zero] with y h0 hQ0
      rw [h0, hQ0]
    have h_cover : Ω = (Ω ∩ Kα) ∪ (Ω \ Kα) := by
      ext y; constructor
      · intro hy
        by_cases h : y ∈ Kα
        · exact Or.inl ⟨hy, h⟩
        · exact Or.inr ⟨hy, h⟩
      · rintro (⟨hy, _⟩ | ⟨hy, _⟩) <;> exact hy
    have h_disj : Disjoint (Ω ∩ Kα) (Ω \ Kα) :=
      Set.disjoint_left.mpr fun y hy hy' => hy'.2 hy.2
    have hΩ_restrict_eq : (volume : Measure EuclN).restrict Ω =
        (volume : Measure EuclN).restrict ((Ω ∩ Kα) ∪ (Ω \ Kα)) := by
      rw [← h_cover]
    rw [hΩ_restrict_eq, MeasureTheory.Measure.restrict_union h_disj h_diff_meas]
    exact (MeasureTheory.ae_add_measure_iff).mpr ⟨h_eq_on_inter, h_eq_on_diff⟩
  have h_norm_eq : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
      (eigenvectorChartIteratedStep (I := I) (M := M)
        g r s i α P₀ m dirs fChartEffPrev l) Ω =
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 Q Ω := by
    rw [h_step_eq]
    exact wkpNorm_congr_ae (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (chartTargetEuclid_isOpen (I := I) (M := M) α) h_indicator_ae_eq_Q
  obtain ⟨C, hC_nn, hC⟩ :=
    eigenvectorChartRHSDiffNumerator_div_density_wkpNorm_le
      (I := I) (M := M) g r s i α P₀ m K (Fin.snoc dirs l) fChartEffPrev
      h_iter h_prev h_prev_zero
  refine ⟨C, hC_nn, ?_⟩
  rw [← hΩ_def] at hC
  rw [h_norm_eq, hQ_def]
  exact hC

omit [CompleteSpace E] in
theorem eigenvectorChartIteratedStep_wkpNorm_le_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (l : Fin (Module.finrank ℝ E))
    (fChartEffPrev : TensorEigenIdx (I := I) (M := M) g r s → EuclN → ℝ)
    (h_iter : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
        (j : ℕ) (idx : Fin j → Fin (Module.finrank ℝ E)),
      MemWkp (d := Module.finrank ℝ E) (2 + K) 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ j idx)
        (chartTargetEuclid (I := I) (M := M) α))
    (h_prev : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2 (fChartEffPrev i)
        (chartTargetEuclid (I := I) (M := M) α))
    (h_prev_zero : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      (fChartEffPrev i) =ᵐ[(volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α \
            chartPouKernel (I := I) (M := M) α)] (fun _ => (0 : ℝ))) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (eigenvectorChartIteratedStep (I := I) (M := M)
              g r s i α P₀ m dirs (fChartEffPrev i) l)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal C *
            diffNumeratorAggregateK (I := I) (M := M)
              g r s i α P₀ m K (Fin.snoc dirs l) (fChartEffPrev i) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  obtain ⟨C, hC_nn, hC⟩ :=
    eigenvectorChartRHSDiffNumerator_div_density_wkpNorm_le_uniform
      (I := I) (M := M) g r s α P₀ m K (Fin.snoc dirs l) fChartEffPrev
      h_iter h_prev h_prev_zero
  refine ⟨C, hC_nn, fun i => ?_⟩
  set Q : EuclN → ℝ := fun y =>
    eigenvectorChartRHSDiffNumerator (I := I) (M := M)
      g r s i α P₀ m (Fin.snoc dirs l) (fChartEffPrev i) y /
    densityOnEuclid (I := I) g α y with hQ_def
  have h_step_eq :
      eigenvectorChartIteratedStep (I := I) (M := M)
        g r s i α P₀ m dirs (fChartEffPrev i) l =
      Set.indicator (chartPouKernel (I := I) (M := M) α) Q := by
    unfold eigenvectorChartIteratedStep
    have h_num := eigenvectorChartIteratedStepNumerator_eq_rhsDiffNumerator
      (I := I) (M := M) g r s i α P₀ m dirs (fChartEffPrev i) l
    funext y
    simp only [hQ_def]
    rw [h_num]
  have hQ_ae_zero : Q =ᵐ[(volume : Measure EuclN).restrict
      (Ω \ chartPouKernel (I := I) (M := M) α)]
      (fun _ : EuclN => (0 : ℝ)) := by
    rw [hQ_def, hΩ_def]
    exact eigenvectorChartRHSDiffNumerator_div_density_ae_zero_off_chartPouKernel
      (I := I) (M := M) g r s i α P₀ m (Fin.snoc dirs l)
      (h_prev_zero i)
  have h_indicator_ae_eq_Q :
      Set.indicator (chartPouKernel (I := I) (M := M) α) Q =ᵐ[
        (volume : Measure EuclN).restrict Ω] Q := by
    set Kα : Set EuclN := chartPouKernel (I := I) (M := M) α with hKα_def
    have hΩ_meas : MeasurableSet Ω :=
      (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
    have hKα_meas : MeasurableSet Kα :=
      chartPouKernel_measurableSet (I := I) (M := M) α
    have h_inter_meas : MeasurableSet (Ω ∩ Kα) := hΩ_meas.inter hKα_meas
    have h_eq_on_inter : Set.indicator Kα Q =ᵐ[
        (volume : Measure EuclN).restrict (Ω ∩ Kα)] Q := by
      refine (ae_restrict_iff' h_inter_meas).mpr ?_
      refine Filter.Eventually.of_forall fun y hy => ?_
      exact Set.indicator_of_mem hy.2 _
    have h_diff_meas : MeasurableSet (Ω \ Kα) := hΩ_meas.diff hKα_meas
    have h_indicator_ae_zero : Set.indicator Kα Q =ᵐ[
        (volume : Measure EuclN).restrict (Ω \ Kα)]
        (fun _ : EuclN => (0 : ℝ)) := by
      refine (ae_restrict_iff' h_diff_meas).mpr ?_
      refine Filter.Eventually.of_forall fun y hy => ?_
      exact Set.indicator_of_notMem hy.2 _
    have h_eq_on_diff : Set.indicator Kα Q =ᵐ[
        (volume : Measure EuclN).restrict (Ω \ Kα)] Q := by
      filter_upwards [h_indicator_ae_zero, hQ_ae_zero] with y h0 hQ0
      rw [h0, hQ0]
    have h_cover : Ω = (Ω ∩ Kα) ∪ (Ω \ Kα) := by
      ext y; constructor
      · intro hy
        by_cases h : y ∈ Kα
        · exact Or.inl ⟨hy, h⟩
        · exact Or.inr ⟨hy, h⟩
      · rintro (⟨hy, _⟩ | ⟨hy, _⟩) <;> exact hy
    have h_disj : Disjoint (Ω ∩ Kα) (Ω \ Kα) :=
      Set.disjoint_left.mpr fun y hy hy' => hy'.2 hy.2
    have hΩ_restrict_eq : (volume : Measure EuclN).restrict Ω =
        (volume : Measure EuclN).restrict ((Ω ∩ Kα) ∪ (Ω \ Kα)) := by
      rw [← h_cover]
    rw [hΩ_restrict_eq, MeasureTheory.Measure.restrict_union h_disj h_diff_meas]
    exact (MeasureTheory.ae_add_measure_iff).mpr ⟨h_eq_on_inter, h_eq_on_diff⟩
  have h_norm_eq : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
      (eigenvectorChartIteratedStep (I := I) (M := M)
        g r s i α P₀ m dirs (fChartEffPrev i) l) Ω =
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 Q Ω := by
    rw [h_step_eq]
    exact wkpNorm_congr_ae (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (chartTargetEuclid_isOpen (I := I) (M := M) α) h_indicator_ae_eq_Q
  have hC_i := hC i
  rw [← hΩ_def] at hC_i
  rw [h_norm_eq, hQ_def]
  exact hC_i

end IteratedStepBoundUnconditional

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
