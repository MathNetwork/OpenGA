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

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompleteSpace E]
  [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma memWkp_finset_sum
    {α : M} {K : ℕ} {ι : Type*} (T : Finset ι)
    {F : ι → EuclN → ℝ}
    (hF : ∀ i ∈ T, MemWkp (d := Module.finrank ℝ E) K 2 (F i)
      (chartTargetEuclid (I := I) (M := M) α)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ∑ i ∈ T, F i y) (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  induction T using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact MemWkp_zero_fun (d := Module.finrank ℝ E)
        (by norm_num : (1 : ℝ≥0∞) ≤ 2) h_open
  | insert i T hi ih =>
      have hi_mem : MemWkp (d := Module.finrank ℝ E) K 2 (F i)
          (chartTargetEuclid (I := I) (M := M) α) :=
        hF i (Finset.mem_insert_self _ _)
      have hsum := ih (fun j hj => hF j (Finset.mem_insert_of_mem hj))
      have h_eq : (fun y => ∑ j ∈ insert i T, F j y) =
          (fun y => F i y + ∑ j ∈ T, F j y) := by
        funext y; rw [Finset.sum_insert hi]
      rw [h_eq]
      exact MemWkp.add (d := Module.finrank ℝ E)
        (by norm_num : (1 : ℝ≥0∞) ≤ 2) h_open hi_mem hsum

omit [CompleteSpace E] in
private lemma wkpNorm_coef_mul_factor_le
    (α : M) (K : ℕ)
    {coef factor : EuclN → ℝ}
    (hcoef_chart : ContDiffOn ℝ (⊤ : ℕ∞) coef
      (chartTargetEuclid (I := I) (M := M) α))
    (hfactor_memWkp : MemWkp (d := Module.finrank ℝ E) K 2 factor
      (chartTargetEuclid (I := I) (M := M) α))
    (hfactor_ae_zero : ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
      y ∉ chartPouKernel (I := I) (M := M) α → factor y = 0) :
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
  obtain ⟨Kc, hKc_pos, hKc_bd⟩ :=
    wkpNorm_smul_smooth_bounded_le (d := Module.finrank ℝ E) K
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by norm_num) hΩ_open hχ_coef_smooth
      hC₀_nn (fun j _hj y _hy => hC₀_bd y j _hj)
  set Cδ : Set EuclN := Metric.cthickening δ Kα with hCδ_def
  have hCδ_closed : IsClosed Cδ := Metric.isClosed_cthickening
  have hCδ_meas : MeasurableSet Cδ := hCδ_closed.measurableSet
  have hfactor_ae_zero' : ∀ᵐ y ∂((volume : Measure EuclN).restrict Ω),
      y ∉ Kα → factor y = 0 := by
    have h := hfactor_ae_zero
    rw [chartL2Measure] at h
    exact h
  have h_ae_eq : (fun y => (χ y * coef y) * factor y)
      =ᵐ[(volume : Measure EuclN).restrict Ω]
      (fun y => coef y * factor y) := by
    have h_eq_on_inter : (fun y => (χ y * coef y) * factor y)
        =ᵐ[(volume : Measure EuclN).restrict (Ω ∩ Cδ)]
        (fun y => coef y * factor y) := by
      refine (ae_restrict_iff' (hΩ_meas.inter hCδ_meas)).mpr ?_
      refine Filter.Eventually.of_forall fun y hy => ?_
      have hχy : χ y = 1 := hχ_one y hy.2
      change (χ y * coef y) * factor y = coef y * factor y
      rw [hχy]; ring
    have hKα_in_Cδ : Kα ⊆ Cδ := Metric.self_subset_cthickening _
    have h_eq_on_diff : (fun y => (χ y * coef y) * factor y)
        =ᵐ[(volume : Measure EuclN).restrict (Ω \ Cδ)]
        (fun y => coef y * factor y) := by
      have h_diff_in_Ω : (volume : Measure EuclN).restrict (Ω \ Cδ) ≤
          (volume : Measure EuclN).restrict Ω :=
        Measure.restrict_mono Set.diff_subset le_rfl
      have h_factor_diff : ∀ᵐ y ∂((volume : Measure EuclN).restrict (Ω \ Cδ)),
          factor y = 0 := by
        have h_lift : ∀ᵐ y ∂((volume : Measure EuclN).restrict (Ω \ Cδ)),
            y ∉ Kα → factor y = 0 :=
          (Measure.absolutelyContinuous_of_le h_diff_in_Ω).ae_le hfactor_ae_zero'
        have h_off : ∀ᵐ _y ∂((volume : Measure EuclN).restrict (Ω \ Cδ)),
            _y ∈ Ω \ Cδ := ae_restrict_mem (hΩ_meas.diff hCδ_meas)
        filter_upwards [h_lift, h_off] with y hy hy_mem
        exact hy (fun hyK => hy_mem.2 (hKα_in_Cδ hyK))
      filter_upwards [h_factor_diff] with y hy
      show (χ y * coef y) * factor y = coef y * factor y
      rw [hy]; ring
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
    rw [hΩ_restrict_eq, Measure.restrict_union h_disj h_diff_meas]
    exact (ae_add_measure_iff).mpr ⟨h_eq_on_inter, h_eq_on_diff⟩
  have h_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => coef y * factor y) Ω :=
    (MemWkp_congr_ae (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae_eq).mp h_prod_memWkp
  refine ⟨h_memWkp, Kc, le_of_lt hKc_pos, ?_⟩
  have h_norm_eq : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
      (fun y => coef y * factor y) Ω =
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
        (fun y => (χ y * coef y) * factor y) Ω :=
    (wkpNorm_congr_ae (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae_eq).symm
  rw [h_norm_eq]
  exact hKc_bd hfactor_memWkp

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
private lemma wkpNorm_coef_mul_factor_le_uniform
    (K : ℕ) (α : M) {coef : EuclN → ℝ}
    (hcoef_chart : ContDiffOn ℝ (⊤ : ℕ∞) coef
      (chartTargetEuclid (I := I) (M := M) α)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ factor : EuclN → ℝ,
        MemWkp (d := Module.finrank ℝ E) K 2 factor
          (chartTargetEuclid (I := I) (M := M) α) →
        (∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
          y ∉ chartPouKernel (I := I) (M := M) α → factor y = 0) →
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
  obtain ⟨Kc, hKc_pos, hKc_bd⟩ :=
    wkpNorm_smul_smooth_bounded_le (d := Module.finrank ℝ E) K
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by norm_num) hΩ_open hχ_coef_smooth
      hC₀_nn (fun j _hj y _hy => hC₀_bd y j _hj)
  refine ⟨Kc, le_of_lt hKc_pos, fun factor hfactor_memWkp hfactor_ae_zero => ?_⟩
  set Cδ : Set EuclN := Metric.cthickening δ Kα with hCδ_def
  have hCδ_closed : IsClosed Cδ := Metric.isClosed_cthickening
  have hCδ_meas : MeasurableSet Cδ := hCδ_closed.measurableSet
  have hfactor_ae_zero' : ∀ᵐ y ∂((volume : Measure EuclN).restrict Ω),
      y ∉ Kα → factor y = 0 := by
    have h := hfactor_ae_zero
    rw [chartL2Measure] at h
    exact h
  have h_ae_eq : (fun y => (χ y * coef y) * factor y)
      =ᵐ[(volume : Measure EuclN).restrict Ω]
      (fun y => coef y * factor y) := by
    have h_eq_on_inter : (fun y => (χ y * coef y) * factor y)
        =ᵐ[(volume : Measure EuclN).restrict (Ω ∩ Cδ)]
        (fun y => coef y * factor y) := by
      refine (ae_restrict_iff' (hΩ_meas.inter hCδ_meas)).mpr ?_
      refine Filter.Eventually.of_forall fun y hy => ?_
      have hχy : χ y = 1 := hχ_one y hy.2
      change (χ y * coef y) * factor y = coef y * factor y
      rw [hχy]; ring
    have hKα_in_Cδ : Kα ⊆ Cδ := Metric.self_subset_cthickening _
    have h_eq_on_diff : (fun y => (χ y * coef y) * factor y)
        =ᵐ[(volume : Measure EuclN).restrict (Ω \ Cδ)]
        (fun y => coef y * factor y) := by
      have h_diff_in_Ω : (volume : Measure EuclN).restrict (Ω \ Cδ) ≤
          (volume : Measure EuclN).restrict Ω :=
        Measure.restrict_mono Set.diff_subset le_rfl
      have h_factor_diff : ∀ᵐ y ∂((volume : Measure EuclN).restrict (Ω \ Cδ)),
          factor y = 0 := by
        have h_lift : ∀ᵐ y ∂((volume : Measure EuclN).restrict (Ω \ Cδ)),
            y ∉ Kα → factor y = 0 :=
          (Measure.absolutelyContinuous_of_le h_diff_in_Ω).ae_le hfactor_ae_zero'
        have h_off : ∀ᵐ _y ∂((volume : Measure EuclN).restrict (Ω \ Cδ)),
            _y ∈ Ω \ Cδ := ae_restrict_mem (hΩ_meas.diff hCδ_meas)
        filter_upwards [h_lift, h_off] with y hy hy_mem
        exact hy (fun hyK => hy_mem.2 (hKα_in_Cδ hyK))
      filter_upwards [h_factor_diff] with y hy
      show (χ y * coef y) * factor y = coef y * factor y
      rw [hy]; ring
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
    rw [hΩ_restrict_eq, Measure.restrict_union h_disj h_diff_meas]
    exact (ae_add_measure_iff).mpr ⟨h_eq_on_inter, h_eq_on_diff⟩
  have h_norm_eq : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
      (fun y => coef y * factor y) Ω =
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
        (fun y => (χ y * coef y) * factor y) Ω :=
    (wkpNorm_congr_ae (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae_eq).symm
  rw [h_norm_eq]
  exact hKc_bd hfactor_memWkp

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

omit [CompleteSpace E] in
lemma covGradChristoffelLimit_memWkp_and_wkpNorm_le
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
        (covGradChristoffelLimit (I := I) (M := M) g r s i β P k)
        (chartTargetEuclid (I := I) (M := M) β) ∧
      ∃ C : ℝ, 0 ≤ C ∧
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (covGradChristoffelLimit (I := I) (M := M)
              g r s i β P k)
            (chartTargetEuclid (I := I) (M := M) β)
          ≤ ENNReal.ofReal C *
            covGradAggregate (I := I) (M := M) g r s i K β := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) β with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) β
  set Saggr : ℝ≥0∞ := covGradAggregate (I := I) (M := M) g r s i K β
    with hSaggr_def
  set F : TensorCompIdx (E := E) r s → EuclN → ℝ :=
    fun p y =>
      Set.indicator (chartPouKernel (I := I) (M := M) β)
          (covDerivLowerOrderCoeff (I := I) (M := M)
            g r s β k P.1 p.1 P.2 p.2) y *
        (tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
            i) β p :
          EuclN → ℝ) y with hF_def
  have h_summand : ∀ p : TensorCompIdx (E := E) r s,
      MemWkp (d := Module.finrank ℝ E) K 2 (F p) Ω ∧
        ∃ C : ℝ, 0 ≤ C ∧
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (F p) Ω
            ≤ ENNReal.ofReal C * Saggr := by
    intro p
    obtain ⟨hfactor_memWkp, hfactor_norm⟩ :=
      eigenvectorVec_pou_memWkp_and_wkpNorm_le (I := I) (M := M)
        g r s i K β p ((h_pou_phi β p).le_of_le (Nat.le_succ K))
    have hfactor_ae_zero : ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) β),
        y ∉ chartPouKernel (I := I) (M := M) β →
          (tensorL2ChartComponent (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i) β p :
            EuclN → ℝ) y = 0 :=
      tensorL2ChartComponent_ae_zero_off_chartPouKernel (I := I) (M := M)
        g r s (tensorResolventEigenbasisVec (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s) i)
        β p
    obtain ⟨h_no_indicator_memWkp, Ccoef, hCcoef_nn, hCcoef_bd⟩ :=
      wkpNorm_coef_mul_factor_le (I := I) (M := M) β K
        (covDerivLowerOrderCoeff_contDiffOn (I := I) (M := M)
          g r s β k P.1 p.1 P.2 p.2)
        hfactor_memWkp hfactor_ae_zero
    have h_ae : (fun y =>
          covDerivLowerOrderCoeff (I := I) (M := M)
              g r s β k P.1 p.1 P.2 p.2 y *
            (tensorL2ChartComponent (I := I) (M := M) g r s
              (tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i) β p :
              EuclN → ℝ) y)
        =ᵐ[(volume : Measure EuclN).restrict Ω] (F p) := by
      have hfactor_ae_zero' : ∀ᵐ y ∂((volume : Measure EuclN).restrict Ω),
          y ∉ chartPouKernel (I := I) (M := M) β →
            (tensorL2ChartComponent (I := I) (M := M) g r s
              (tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i) β p :
              EuclN → ℝ) y = 0 := hfactor_ae_zero
      filter_upwards [hfactor_ae_zero'] with y hy
      show covDerivLowerOrderCoeff (I := I) (M := M)
              g r s β k P.1 p.1 P.2 p.2 y *
            (tensorL2ChartComponent (I := I) (M := M) g r s
              (tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i) β p :
              EuclN → ℝ) y = F p y
      simp only [hF_def]
      by_cases hyK : y ∈ chartPouKernel (I := I) (M := M) β
      · rw [Set.indicator_of_mem hyK]
      · rw [Set.indicator_of_notMem hyK, zero_mul, hy hyK, mul_zero]
    have hF_memWkp : MemWkp (d := Module.finrank ℝ E) K 2 (F p) Ω :=
      (MemWkp_congr_ae (d := Module.finrank ℝ E)
        (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae).mp h_no_indicator_memWkp
    refine ⟨hF_memWkp, Ccoef * ‖(i.fst.val)⁻¹‖,
      mul_nonneg hCcoef_nn (norm_nonneg _), ?_⟩
    rw [← wkpNorm_congr_ae (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae]
    calc
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (fun y =>
            covDerivLowerOrderCoeff (I := I) (M := M)
                g r s β k P.1 p.1 P.2 p.2 y *
              (tensorL2ChartComponent (I := I) (M := M) g r s
                (tensorResolventEigenbasisVec (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator (I := I) (M := M)
                    g r s) i) β p :
                EuclN → ℝ) y) Ω
          ≤ ENNReal.ofReal Ccoef *
              iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
                (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                    (tensorResolventEigenbasisVec (I := I) (M := M)
                      (tensorResolventL2_isCompactOperator (I := I)
                        (M := M) g r s) i)
                    β p : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                    EuclN → ℝ) y) Ω :=
        hCcoef_bd
      _ ≤ ENNReal.ofReal Ccoef *
            (ENNReal.ofReal ‖(i.fst.val)⁻¹‖ *
              iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
                (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                    (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                      (eigenvectorResolvent (I := I) (M := M)
                        g r s i))
                    β p : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                    EuclN → ℝ) y)
                (chartTargetEuclid (I := I) (M := M) β)) :=
        mul_le_mul_of_nonneg_left hfactor_norm (zero_le _)
      _ ≤ ENNReal.ofReal Ccoef *
            (ENNReal.ofReal ‖(i.fst.val)⁻¹‖ *
              chartCompNorm (I := I) (M := M) g r s i K β p) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (wkpNorm_mono_order (d := Module.finrank ℝ E)
              (Nat.le_succ K) _ _) (zero_le _)) (zero_le _)
      _ ≤ ENNReal.ofReal Ccoef *
            (ENNReal.ofReal ‖(i.fst.val)⁻¹‖ * Saggr) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (chartCompNorm_center_le_covGradAggregate (I := I)
              (M := M) g r s i K β p) (zero_le _)) (zero_le _)
      _ = ENNReal.ofReal (Ccoef * ‖(i.fst.val)⁻¹‖) * Saggr := by
        rw [ENNReal.ofReal_mul hCcoef_nn]; ring
  have h_sum_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ∑ p : TensorCompIdx (E := E) r s, F p y) Ω :=
    memWkp_finset_sum (I := I) (M := M) Finset.univ
      (fun p _ => (h_summand p).1)
  have h_christoffel_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (covGradChristoffelLimit (I := I) (M := M)
        g r s i β P k) Ω := by
    have h_unfold : (covGradChristoffelLimit (I := I) (M := M)
        g r s i β P k) =
        (fun y => ∑ p : TensorCompIdx (E := E) r s, F p y) := rfl
    rw [h_unfold]
    exact h_sum_memWkp
  choose Cf hCf_nn hCf_bd using fun p => (h_summand p).2
  refine ⟨h_christoffel_memWkp,
    ∑ p : TensorCompIdx (E := E) r s, Cf p,
    Finset.sum_nonneg (fun p _ => hCf_nn p), ?_⟩
  have h_unfold : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
      (covGradChristoffelLimit (I := I) (M := M) g r s i β P k) Ω =
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
        (fun y => ∑ p : TensorCompIdx (E := E) r s, F p y) Ω := rfl
  rw [h_unfold]
  calc
    iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
        (fun y => ∑ p : TensorCompIdx (E := E) r s, F p y) Ω
        ≤ ∑ p : TensorCompIdx (E := E) r s,
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (F p) Ω :=
      wkpNorm_sum_le (d := Module.finrank ℝ E)
        (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open Finset.univ F
        (fun p _ => (h_summand p).1)
    _ ≤ ∑ p : TensorCompIdx (E := E) r s, ENNReal.ofReal (Cf p) * Saggr :=
      Finset.sum_le_sum (fun p _ => hCf_bd p)
    _ = (∑ p : TensorCompIdx (E := E) r s, ENNReal.ofReal (Cf p)) * Saggr := by
      rw [← Finset.sum_mul]
    _ = ENNReal.ofReal (∑ p : TensorCompIdx (E := E) r s, Cf p) * Saggr := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun p _ => hCf_nn p)]

omit [CompleteSpace E] in
lemma covGradChristoffelLimit_wkpNorm_le_uniform
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
            (covGradChristoffelLimit (I := I) (M := M)
              g r s i β P k)
            (chartTargetEuclid (I := I) (M := M) β)
          ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * C) *
            covGradAggregate (I := I) (M := M) g r s i K β := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) β with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) β
  have h_coef_uniform : ∀ p : TensorCompIdx (E := E) r s,
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ factor : EuclN → ℝ,
          MemWkp (d := Module.finrank ℝ E) K 2 factor Ω →
          (∀ᵐ y ∂(chartL2Measure (I := I) (M := M) β),
            y ∉ chartPouKernel (I := I) (M := M) β → factor y = 0) →
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (fun y => covDerivLowerOrderCoeff (I := I) (M := M)
                  g r s β k P.1 p.1 P.2 p.2 y * factor y) Ω
            ≤ ENNReal.ofReal C *
              iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 factor Ω := fun p =>
    wkpNorm_coef_mul_factor_le_uniform (I := I) (M := M) K β
      (covDerivLowerOrderCoeff_contDiffOn (I := I) (M := M)
        g r s β k P.1 p.1 P.2 p.2)
  choose Ccoef hCcoef_nn hCcoef_bd using h_coef_uniform
  refine ⟨∑ p : TensorCompIdx (E := E) r s, Ccoef p,
    Finset.sum_nonneg (fun p _ => hCcoef_nn p), fun i => ?_⟩
  have hμ_pos : 0 < i.fst.val := eigenIdx_val_pos (I := I) (M := M) g r s i
  have hμ_inv_nn : 0 ≤ (i.fst.val)⁻¹ := le_of_lt (inv_pos.mpr hμ_pos)
  have hμ_norm : ‖(i.fst.val)⁻¹‖ = (i.fst.val)⁻¹ := Real.norm_of_nonneg hμ_inv_nn
  set Saggr : ℝ≥0∞ := covGradAggregate (I := I) (M := M) g r s i K β
    with hSaggr_def
  set F : TensorCompIdx (E := E) r s → EuclN → ℝ :=
    fun p y =>
      Set.indicator (chartPouKernel (I := I) (M := M) β)
          (covDerivLowerOrderCoeff (I := I) (M := M)
            g r s β k P.1 p.1 P.2 p.2) y *
        (tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
            i) β p :
          EuclN → ℝ) y with hF_def
  have h_summand : ∀ p : TensorCompIdx (E := E) r s,
      MemWkp (d := Module.finrank ℝ E) K 2 (F p) Ω ∧
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (F p) Ω
          ≤ ENNReal.ofReal (Ccoef p * ‖(i.fst.val)⁻¹‖) * Saggr := by
    intro p
    obtain ⟨hfactor_memWkp, hfactor_norm⟩ :=
      eigenvectorVec_pou_memWkp_and_wkpNorm_le (I := I) (M := M)
        g r s i K β p ((h_pou_phi i β p).le_of_le (Nat.le_succ K))
    have hfactor_ae_zero : ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) β),
        y ∉ chartPouKernel (I := I) (M := M) β →
          (tensorL2ChartComponent (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i) β p :
            EuclN → ℝ) y = 0 :=
      tensorL2ChartComponent_ae_zero_off_chartPouKernel (I := I) (M := M)
        g r s (tensorResolventEigenbasisVec (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s) i)
        β p
    have h_no_indicator_memWkp := (wkpNorm_coef_mul_factor_le (I := I) (M := M)
      β K
      (covDerivLowerOrderCoeff_contDiffOn (I := I) (M := M)
        g r s β k P.1 p.1 P.2 p.2)
      hfactor_memWkp hfactor_ae_zero).1
    have h_ae : (fun y =>
          covDerivLowerOrderCoeff (I := I) (M := M)
              g r s β k P.1 p.1 P.2 p.2 y *
            (tensorL2ChartComponent (I := I) (M := M) g r s
              (tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i) β p :
              EuclN → ℝ) y)
        =ᵐ[(volume : Measure EuclN).restrict Ω] (F p) := by
      have hfactor_ae_zero' : ∀ᵐ y ∂((volume : Measure EuclN).restrict Ω),
          y ∉ chartPouKernel (I := I) (M := M) β →
            (tensorL2ChartComponent (I := I) (M := M) g r s
              (tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i) β p :
              EuclN → ℝ) y = 0 := hfactor_ae_zero
      filter_upwards [hfactor_ae_zero'] with y hy
      show covDerivLowerOrderCoeff (I := I) (M := M)
              g r s β k P.1 p.1 P.2 p.2 y *
            (tensorL2ChartComponent (I := I) (M := M) g r s
              (tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i) β p :
              EuclN → ℝ) y = F p y
      simp only [hF_def]
      by_cases hyK : y ∈ chartPouKernel (I := I) (M := M) β
      · rw [Set.indicator_of_mem hyK]
      · rw [Set.indicator_of_notMem hyK, zero_mul, hy hyK, mul_zero]
    have hF_memWkp : MemWkp (d := Module.finrank ℝ E) K 2 (F p) Ω :=
      (MemWkp_congr_ae (d := Module.finrank ℝ E)
        (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae).mp h_no_indicator_memWkp
    refine ⟨hF_memWkp, ?_⟩
    rw [← wkpNorm_congr_ae (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae]
    calc
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (fun y =>
            covDerivLowerOrderCoeff (I := I) (M := M)
                g r s β k P.1 p.1 P.2 p.2 y *
              (tensorL2ChartComponent (I := I) (M := M) g r s
                (tensorResolventEigenbasisVec (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator (I := I) (M := M)
                    g r s) i) β p :
                EuclN → ℝ) y) Ω
          ≤ ENNReal.ofReal (Ccoef p) *
              iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
                (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                    (tensorResolventEigenbasisVec (I := I) (M := M)
                      (tensorResolventL2_isCompactOperator (I := I)
                        (M := M) g r s) i)
                    β p : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                    EuclN → ℝ) y) Ω :=
        hCcoef_bd p _ hfactor_memWkp hfactor_ae_zero
      _ ≤ ENNReal.ofReal (Ccoef p) *
            (ENNReal.ofReal ‖(i.fst.val)⁻¹‖ *
              iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
                (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                    (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                      (eigenvectorResolvent (I := I) (M := M)
                        g r s i))
                    β p : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                    EuclN → ℝ) y)
                (chartTargetEuclid (I := I) (M := M) β)) :=
        mul_le_mul_of_nonneg_left hfactor_norm (zero_le _)
      _ ≤ ENNReal.ofReal (Ccoef p) *
            (ENNReal.ofReal ‖(i.fst.val)⁻¹‖ *
              chartCompNorm (I := I) (M := M) g r s i K β p) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (wkpNorm_mono_order (d := Module.finrank ℝ E)
              (Nat.le_succ K) _ _) (zero_le _)) (zero_le _)
      _ ≤ ENNReal.ofReal (Ccoef p) *
            (ENNReal.ofReal ‖(i.fst.val)⁻¹‖ * Saggr) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (chartCompNorm_center_le_covGradAggregate (I := I)
              (M := M) g r s i K β p) (zero_le _)) (zero_le _)
      _ = ENNReal.ofReal (Ccoef p * ‖(i.fst.val)⁻¹‖) * Saggr := by
        rw [ENNReal.ofReal_mul (hCcoef_nn p)]; ring
  have h_sum_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ∑ p : TensorCompIdx (E := E) r s, F p y) Ω :=
    memWkp_finset_sum (I := I) (M := M) Finset.univ
      (fun p _ => (h_summand p).1)
  have h_unfold : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
      (covGradChristoffelLimit (I := I) (M := M)
        g r s i β P k) Ω =
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
        (fun y => ∑ p : TensorCompIdx (E := E) r s, F p y) Ω := rfl
  rw [h_unfold]
  calc
    iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
        (fun y => ∑ p : TensorCompIdx (E := E) r s, F p y) Ω
        ≤ ∑ p : TensorCompIdx (E := E) r s,
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (F p) Ω :=
      wkpNorm_sum_le (d := Module.finrank ℝ E)
        (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open Finset.univ F
        (fun p _ => (h_summand p).1)
    _ ≤ ∑ p : TensorCompIdx (E := E) r s,
          ENNReal.ofReal (Ccoef p * ‖(i.fst.val)⁻¹‖) * Saggr :=
      Finset.sum_le_sum (fun p _ => (h_summand p).2)
    _ = (∑ p : TensorCompIdx (E := E) r s,
          ENNReal.ofReal (Ccoef p * ‖(i.fst.val)⁻¹‖)) * Saggr := by
      rw [← Finset.sum_mul]
    _ = ENNReal.ofReal ((i.fst.val)⁻¹ *
          ∑ p : TensorCompIdx (E := E) r s, Ccoef p) * Saggr := by
      have h_real : (∑ p : TensorCompIdx (E := E) r s,
            Ccoef p * ‖(i.fst.val)⁻¹‖)
          = (i.fst.val)⁻¹ * ∑ p : TensorCompIdx (E := E) r s, Ccoef p := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun p _ => by rw [hμ_norm, mul_comm])
      rw [← ENNReal.ofReal_sum_of_nonneg
        (fun p _ => mul_nonneg (hCcoef_nn p) (norm_nonneg _)), h_real]

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
