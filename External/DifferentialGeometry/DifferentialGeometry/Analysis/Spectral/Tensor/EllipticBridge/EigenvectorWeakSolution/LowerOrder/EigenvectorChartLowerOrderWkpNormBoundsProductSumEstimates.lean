import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.RHS.ChartRHSBounds.EigenvectorChartRHSMemWkp
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.LowerOrder.EigenvectorChartLowerOrderLimits
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Multiplication.MultiplyQuantK
import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.IteratedSobolevQuant

noncomputable section

open Bundle Manifold MeasureTheory Set Filter Topology
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

section LowerOrderWkpNormBounds

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (i : TensorEigenIdx (I := I) (M := M) g r s)

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
lemma wkpNorm_indicatorFactor_mul_atom_le
    (α : M) (K : ℕ) {coef G : EuclN → ℝ}
    (hcoef : ContDiffOn ℝ (⊤ : ℕ∞) coef
      (chartTargetEuclid (I := I) (M := M) α))
    (hG_memWkp : MemWkp (d := Module.finrank ℝ E) K 2 G
      (chartTargetEuclid (I := I) (M := M) α))
    (hG_zero : ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
      y ∉ chartPouKernel (I := I) (M := M) α → G y = 0) :
    MemWkp (d := Module.finrank ℝ E) K 2
        (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α) coef y * G y)
        (chartTargetEuclid (I := I) (M := M) α) ∧
      ∃ C : ℝ, 0 ≤ C ∧
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α) coef y *
              G y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal C *
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 G
              (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  obtain ⟨h_mul_memWkp, C, hC_nn, hC_bd⟩ :=
    wkpNorm_coef_mul_factor_le (I := I) (M := M) α K hcoef hG_memWkp hG_zero
  have hG_zero' : ∀ᵐ y ∂((volume : Measure EuclN).restrict Ω),
      y ∉ chartPouKernel (I := I) (M := M) α → G y = 0 := by
    have h := hG_zero
    rw [chartL2Measure] at h
    exact h
  have h_prod_eq : (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α)
        coef y * G y)
      =ᵐ[(volume : Measure EuclN).restrict Ω] (fun y => coef y * G y) := by
    filter_upwards [hG_zero'] with y hy
    by_cases hyK : y ∈ chartPouKernel (I := I) (M := M) α
    · rw [Set.indicator_of_mem hyK]
    · rw [Set.indicator_of_notMem hyK, zero_mul, hy hyK, mul_zero]
  refine ⟨(MemWkp_congr_ae (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_prod_eq).mpr h_mul_memWkp,
    C, hC_nn, ?_⟩
  rw [wkpNorm_congr_ae (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_prod_eq]
  exact hC_bd

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M]
  [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
lemma memWkp_finsetSum
    {α : M} {K : ℕ} {ι : Type*} (T : Finset ι)
    {F : ι → EuclN → ℝ}
    (hF : ∀ j ∈ T, MemWkp (d := Module.finrank ℝ E) K 2 (F j)
      (chartTargetEuclid (I := I) (M := M) α)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ∑ j ∈ T, F j y) (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  induction T using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact MemWkp_zero_fun (d := Module.finrank ℝ E)
        (by norm_num : (1 : ℝ≥0∞) ≤ 2) h_open
  | insert j T hj ih =>
      have hj_mem : MemWkp (d := Module.finrank ℝ E) K 2 (F j)
          (chartTargetEuclid (I := I) (M := M) α) :=
        hF j (Finset.mem_insert_self _ _)
      have hsum := ih (fun j' hj' => hF j' (Finset.mem_insert_of_mem hj'))
      have h_eq : (fun y => ∑ j' ∈ insert j T, F j' y) =
          (fun y => F j y + ∑ j' ∈ T, F j' y) := by
        funext y; rw [Finset.sum_insert hj]
      rw [h_eq]
      exact MemWkp.add (d := Module.finrank ℝ E)
        (by norm_num : (1 : ℝ≥0∞) ≤ 2) h_open hj_mem hsum

omit [CompleteSpace E] [IsManifold I ∞ M] [CompactSpace M] [T2Space M]
  [SigmaCompactSpace M] in

omit [NeZero (Module.finrank ℝ E)] in
lemma wkpNorm_finsetSum_le_const_mul_atomSum
    {α : M} {K : ℕ} {ι κ : Type*}
    (S : Finset ι) (T : Finset κ) (F : ι → EuclN → ℝ) (atom : κ → EuclN → ℝ)
    (proj : ι → κ) (hproj : ∀ j ∈ S, proj j ∈ T)
    (C : ℝ) (_hC_nn : 0 ≤ C)
    (hF : ∀ j ∈ S, MemWkp (d := Module.finrank ℝ E) K 2 (F j)
      (chartTargetEuclid (I := I) (M := M) α))
    (h_bd : ∀ j ∈ S,
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (F j)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal C *
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (atom (proj j))
            (chartTargetEuclid (I := I) (M := M) α)) :
    iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
        (fun y => ∑ j ∈ S, F j y) (chartTargetEuclid (I := I) (M := M) α)
      ≤ ENNReal.ofReal (C * S.card)
        * ∑ p ∈ T, iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (atom p)
            (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_tri := wkpNorm_sum_le (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) h_open S F hF
  have h_step : ∑ j ∈ S, iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (F j)
        (chartTargetEuclid (I := I) (M := M) α)
      ≤ ∑ _j ∈ S, ENNReal.ofReal C
        * ∑ p ∈ T, iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (atom p)
            (chartTargetEuclid (I := I) (M := M) α) := by
    refine Finset.sum_le_sum (fun j hj => ?_)
    refine (h_bd j hj).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (zero_le _)
    exact Finset.single_le_sum
      (f := fun p => iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (atom p)
        (chartTargetEuclid (I := I) (M := M) α))
      (fun p _ => zero_le _) (hproj j hj)
  have h_const : ∑ _j ∈ S, ENNReal.ofReal C
        * ∑ p ∈ T, iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (atom p)
            (chartTargetEuclid (I := I) (M := M) α)
      = (S.card : ℝ≥0∞) * (ENNReal.ofReal C
        * ∑ p ∈ T, iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (atom p)
            (chartTargetEuclid (I := I) (M := M) α)) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have h_cast : (S.card : ℝ≥0∞) * ENNReal.ofReal C
      = ENNReal.ofReal (C * S.card) := by
    rw [mul_comm C, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
  calc
    iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
        (fun y => ∑ j ∈ S, F j y) (chartTargetEuclid (I := I) (M := M) α)
        ≤ ∑ j ∈ S, iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (F j)
            (chartTargetEuclid (I := I) (M := M) α) := h_tri
    _ ≤ ∑ _j ∈ S, ENNReal.ofReal C
          * ∑ p ∈ T, iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (atom p)
              (chartTargetEuclid (I := I) (M := M) α) := h_step
    _ = (S.card : ℝ≥0∞) * (ENNReal.ofReal C
          * ∑ p ∈ T, iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (atom p)
              (chartTargetEuclid (I := I) (M := M) α)) := h_const
    _ = ((S.card : ℝ≥0∞) * ENNReal.ofReal C)
          * ∑ p ∈ T, iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (atom p)
              (chartTargetEuclid (I := I) (M := M) α) := by rw [mul_assoc]
    _ = ENNReal.ofReal (C * S.card)
          * ∑ p ∈ T, iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (atom p)
              (chartTargetEuclid (I := I) (M := M) α) := by rw [h_cast]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in

private lemma memWkp_of_weakPartial_of_memWkp_succ
    {K : ℕ} {Ω : Set EuclN} (hΩ : IsOpen Ω)
    (k : Fin (Module.finrank ℝ E))
    {gpart u : EuclN → ℝ}
    (hgpart_memLp : MemLp gpart 2 ((volume : Measure EuclN).restrict Ω))
    (hgpart_weak : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k
      gpart u Ω)
    (hu : MemWkp (d := Module.finrank ℝ E) (K + 1) 2 u Ω) :
    MemWkp (d := Module.finrank ℝ E) K 2 gpart Ω := by
  classical
  have hu_w1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 u Ω := hu.memW1p
  have h_chosen_weak : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k
      (chosenWeakPartial' (d := Module.finrank ℝ E) 2 k u Ω) u Ω :=
    chosenWeakPartial'_isWeakPartial_of_mem hu_w1p k
  have h_chosen_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (chosenWeakPartial' (d := Module.finrank ℝ E) 2 k u Ω) Ω :=
    hu.chosenWeakPartial_mem k
  have hgpart_loc : LocallyIntegrable gpart
      ((volume : Measure EuclN).restrict Ω) :=
    hgpart_memLp.locallyIntegrable (by norm_num)
  have h_chosen_loc : LocallyIntegrable
      (chosenWeakPartial' (d := Module.finrank ℝ E) 2 k u Ω)
      ((volume : Measure EuclN).restrict Ω) :=
    h_chosen_memWkp.memLp.locallyIntegrable (by norm_num)
  have h_ae : gpart =ᵐ[(volume : Measure EuclN).restrict Ω]
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 k u Ω :=
    DeGiorgi.HasWeakPartialDeriv.ae_eq hΩ hgpart_weak h_chosen_weak
      hgpart_loc h_chosen_loc
  exact (MemWkp_congr_ae (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ h_ae).mpr h_chosen_memWkp

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in

lemma hasWeakPartialDeriv_ae_zero_off_of_ae_zero_off
    {Ω : Set EuclN} (hΩ_open : IsOpen Ω)
    (k : Fin (Module.finrank ℝ E))
    {Kc : Set EuclN} (hKc_closed : IsClosed Kc)
    {gp u : EuclN → ℝ}
    (hgp_memLp : MemLp gp 2 ((volume : Measure EuclN).restrict Ω))
    (hgp_weak : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k
      gp u Ω)
    (hu_w1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 u Ω)
    (hu_zero : ∀ᵐ y ∂((volume : Measure EuclN).restrict Ω),
      y ∉ Kc → u y = 0) :
    ∀ᵐ y ∂((volume : Measure EuclN).restrict Ω),
      y ∉ Kc → gp y = 0 := by
  classical
  set V : Set EuclN := Ω \ Kc with hV_def
  have hV_open : IsOpen V := hΩ_open.sdiff hKc_closed
  have hV_sub : V ⊆ Ω := Set.diff_subset
  have hV_meas : MeasurableSet V := hV_open.measurableSet
  have hΩ_meas : MeasurableSet Ω := hΩ_open.measurableSet
  have hu_zero_V : u =ᵐ[(volume : Measure EuclN).restrict V]
      (fun _ : EuclN => (0 : ℝ)) := by
    have h_lift : ∀ᵐ y ∂((volume : Measure EuclN).restrict V),
        y ∉ Kc → u y = 0 :=
      (Measure.absolutelyContinuous_of_le
        (Measure.restrict_mono hV_sub le_rfl)).ae_le hu_zero
    have h_mem : ∀ᵐ y ∂((volume : Measure EuclN).restrict V), y ∈ V :=
      ae_restrict_mem hV_meas
    filter_upwards [h_lift, h_mem] with y hy hy_mem
    exact hy hy_mem.2
  have hu_w1p_V : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 u V :=
    MemW1p.mono_set hV_open hV_sub hu_w1p
  have h_chosen_zero : chosenWeakPartial' (d := Module.finrank ℝ E) 2 k u V
      =ᵐ[(volume : Measure EuclN).restrict V] (fun _ : EuclN => (0 : ℝ)) :=
    chosenWeakPartial'_ae_zero_of_ae_zero (d := Module.finrank ℝ E)
      (by norm_num) hV_open hu_zero_V k
  have h_chosen_weak : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k
      (chosenWeakPartial' (d := Module.finrank ℝ E) 2 k u V) u V :=
    chosenWeakPartial'_isWeakPartial_of_mem hu_w1p_V k
  have hgp_weak_V : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k
      gp u V :=
    DeGiorgi.HasWeakPartialDeriv.restrict hV_open hV_sub hgp_weak
  have hgp_loc_V : LocallyIntegrable gp
      ((volume : Measure EuclN).restrict V) :=
    (hgp_memLp.mono_measure (Measure.restrict_mono hV_sub le_rfl)).locallyIntegrable
      (by norm_num)
  have h_chosen_loc_V : LocallyIntegrable
      (chosenWeakPartial' (d := Module.finrank ℝ E) 2 k u V)
      ((volume : Measure EuclN).restrict V) :=
    (chosenWeakPartial'_memLp_of_mem hu_w1p_V k).locallyIntegrable (by norm_num)
  have h_gp_eq : gp =ᵐ[(volume : Measure EuclN).restrict V]
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 k u V :=
    DeGiorgi.HasWeakPartialDeriv.ae_eq hV_open hgp_weak_V h_chosen_weak
      hgp_loc_V h_chosen_loc_V
  have hgp_zero_V : gp =ᵐ[(volume : Measure EuclN).restrict V]
      (fun _ : EuclN => (0 : ℝ)) := h_gp_eq.trans h_chosen_zero
  have hgp_zero_V' : ∀ᵐ y ∂(volume : Measure EuclN),
      y ∈ V → gp y = 0 := by
    have h := (ae_restrict_iff' hV_meas).mp hgp_zero_V
    filter_upwards [h] with y hy hy_mem
    exact hy hy_mem
  refine (ae_restrict_iff' hΩ_meas).mpr ?_
  filter_upwards [hgp_zero_V'] with y hy hy_mem hy_notKc
  exact hy ⟨hy_mem, hy_notKc⟩

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in

lemma exists_uniform_const_of_finite_wkpNorm_bounds
    {α : M} {K : ℕ} {ι κ : Type*} [Finite ι]
    (F : ι → EuclN → ℝ) (atom : κ → EuclN → ℝ) (proj : ι → κ)
    (h_data : ∀ j : ι, ∃ C : ℝ, 0 ≤ C ∧
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (F j)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal C *
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (atom (proj j))
            (chartTargetEuclid (I := I) (M := M) α)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ι,
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (F j)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal C *
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (atom (proj j))
            (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  refine ⟨∑ j : ι, (h_data j).choose, ?_, ?_⟩
  · exact Finset.sum_nonneg (fun j _ => (h_data j).choose_spec.1)
  · intro j
    refine (h_data j).choose_spec.2.trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (zero_le _)
    refine ENNReal.ofReal_le_ofReal ?_
    exact Finset.single_le_sum
      (f := fun j' => (h_data j').choose)
      (fun j' _ => (h_data j').choose_spec.1) (Finset.mem_univ j)

end LowerOrderWkpNormBounds

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
