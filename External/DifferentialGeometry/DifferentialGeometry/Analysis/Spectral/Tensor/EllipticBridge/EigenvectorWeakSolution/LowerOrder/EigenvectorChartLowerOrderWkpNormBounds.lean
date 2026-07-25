import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.RHS.ChartRHSBounds.EigenvectorChartRHSMemWkp
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.LowerOrder.EigenvectorChartLowerOrderLimits
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Multiplication.MultiplyQuantK
import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.IteratedSobolevQuant
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.LowerOrder.EigenvectorChartLowerOrderWkpNormBoundsProductSumEstimates
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.LowerOrder.EigenvectorChartLowerOrderWkpNormBoundsLimitVanishingOffKernel
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.LowerOrder.EigenvectorChartLowerOrderWkpNormBoundsPerEigenvector

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

section LowerOrderWkpNormBoundsUniform

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)

omit [CompleteSpace E] in
private lemma wkpNorm_coef_mul_factor_le_uniform
    (α : M) (K : ℕ) {coef : EuclN → ℝ}
    (hcoef_chart : ContDiffOn ℝ (⊤ : ℕ∞) coef
      (chartTargetEuclid (I := I) (M := M) α)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {factor : EuclN → ℝ},
      MemWkp (d := Module.finrank ℝ E) K 2 factor
          (chartTargetEuclid (I := I) (M := M) α) →
      (∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
        y ∉ chartPouKernel (I := I) (M := M) α → factor y = 0) →
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
  obtain ⟨Kc, hKc_pos, hKc_bd⟩ :=
    wkpNorm_smul_smooth_bounded_le (d := Module.finrank ℝ E) K
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by norm_num) hΩ_open hχ_coef_smooth
      hC₀_nn (fun j _hj y _hy => hC₀_bd y j _hj)
  refine ⟨Kc, le_of_lt hKc_pos, ?_⟩
  intro factor hfactor_memWkp hfactor_ae_zero
  have h_prod_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => (χ y * coef y) * factor y) Ω :=
    MemWkp.smul_smooth_bounded (d := Module.finrank ℝ E) K
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open hχ_coef_smooth
      (fun j _hj y _hy => hC₀_bd y j _hj) hfactor_memWkp
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
  refine ⟨h_memWkp, ?_⟩
  have h_norm_eq : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
      (fun y => coef y * factor y) Ω =
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
        (fun y => (χ y * coef y) * factor y) Ω :=
    (wkpNorm_congr_ae (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae_eq).symm
  rw [h_norm_eq]
  exact hKc_bd hfactor_memWkp

omit [CompleteSpace E] in
private lemma wkpNorm_indicatorFactor_mul_atom_le_uniform
    (α : M) (K : ℕ) {coef : EuclN → ℝ}
    (hcoef : ContDiffOn ℝ (⊤ : ℕ∞) coef
      (chartTargetEuclid (I := I) (M := M) α)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {G : EuclN → ℝ},
      MemWkp (d := Module.finrank ℝ E) K 2 G
          (chartTargetEuclid (I := I) (M := M) α) →
      (∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
        y ∉ chartPouKernel (I := I) (M := M) α → G y = 0) →
      MemWkp (d := Module.finrank ℝ E) K 2
          (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α) coef y *
            G y)
          (chartTargetEuclid (I := I) (M := M) α) ∧
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
  obtain ⟨C, hC_nn, hC_bd⟩ :=
    wkpNorm_coef_mul_factor_le_uniform (I := I) (M := M) α K hcoef
  refine ⟨C, hC_nn, ?_⟩
  intro G hG_memWkp hG_zero
  obtain ⟨h_mul_memWkp, hC_bd'⟩ := hC_bd hG_memWkp hG_zero
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
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_prod_eq).mpr h_mul_memWkp, ?_⟩
  rw [wkpNorm_congr_ae (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_prod_eq]
  exact hC_bd'

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in

private lemma exists_uniform_const_of_finite_wkpNorm_bounds_uniform
    {α : M} {K : ℕ} {δ ι κ : Type*} [Finite ι]
    (F : δ → ι → EuclN → ℝ) (atom : δ → κ → EuclN → ℝ) (proj : ι → κ)
    (Cf : ι → ℝ) (hCf_nn : ∀ j : ι, 0 ≤ Cf j)
    (h_data : ∀ (d : δ), ∀ j : ι,
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (F d j)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (Cf j) *
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (atom d (proj j))
            (chartTargetEuclid (I := I) (M := M) α)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (d : δ), ∀ j : ι,
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (F d j)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal C *
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (atom d (proj j))
            (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  refine ⟨∑ j : ι, Cf j, Finset.sum_nonneg (fun j _ => hCf_nn j), ?_⟩
  intro d j
  refine (h_data d j).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (zero_le _)
  refine ENNReal.ofReal_le_ofReal ?_
  exact Finset.single_le_sum
    (f := fun j' => Cf j') (fun j' _ => hCf_nn j') (Finset.mem_univ j)

omit [CompleteSpace E] in
theorem wkpNorm_covPrincipalRotationCoeffLimit_le_uniform_unconditional
    (K : ℕ) (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (h_pou : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (covPrincipalRotationCoeffLimit (I := I) (M := M)
              g r s i α P₀ : EuclN → ℝ)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal C *
            (∑ P : TensorCompIdx (E := E) r s,
              ∑ k : Fin (Module.finrank ℝ E),
                iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
                  (fun y => ((partialLpLimit (I := I) (M := M)
                      g r s i α P k :
                    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                    EuclN → ℝ) y)
                  (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  set Cf : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
      × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) → ℝ := fun x =>
    (wkpNorm_indicatorFactor_mul_atom_le_uniform (I := I) (M := M) α K
      (principalRotationFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ x.1 x.2.1 x.2.2.1 x.2.2.2)).choose
    with hCf_def
  have hCf_spec : ∀ x : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
      × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
      0 ≤ Cf x ∧ ∀ {G : EuclN → ℝ},
        MemWkp (d := Module.finrank ℝ E) K 2 G Ω →
        (∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
          y ∉ chartPouKernel (I := I) (M := M) α → G y = 0) →
        MemWkp (d := Module.finrank ℝ E) K 2
            (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α)
              (principalRotationFactor (I := I) (M := M)
                g r s α P₀ x.1 x.2.1 x.2.2.1 x.2.2.2) y * G y) Ω ∧
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α)
                (principalRotationFactor (I := I) (M := M)
                  g r s α P₀ x.1 x.2.1 x.2.2.1 x.2.2.2) y * G y) Ω
            ≤ ENNReal.ofReal (Cf x) *
              iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 G Ω :=
    fun x =>
      (wkpNorm_indicatorFactor_mul_atom_le_uniform (I := I) (M := M) α K
        (principalRotationFactor_contDiffOn (I := I) (M := M)
          g r s α P₀ x.1 x.2.1 x.2.2.1 x.2.2.2)).choose_spec
  set F : TensorEigenIdx (I := I) (M := M) g r s →
      (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
        × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E))
      → EuclN → ℝ :=
    fun i x y =>
      Set.indicator (chartPouKernel (I := I) (M := M) α)
          (principalRotationFactor (I := I) (M := M)
            g r s α P₀ x.1 x.2.1 x.2.2.1 x.2.2.2) y *
        ((partialLpLimit (I := I) (M := M) g r s i α x.1 x.2.2.1 :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hF_def
  set partAtom : TensorEigenIdx (I := I) (M := M) g r s →
      (TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)) → EuclN → ℝ :=
    fun i pk y =>
    ((partialLpLimit (I := I) (M := M) g r s i α pk.1 pk.2 :
      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hpartAtom_def
  obtain ⟨Csum, hCsum_nn, hCsum_bd⟩ :=
    exists_uniform_const_of_finite_wkpNorm_bounds_uniform (I := I) (M := M)
      (α := α) (K := K) F partAtom (fun x => (x.1, x.2.2.1)) Cf
      (fun x => (hCf_spec x).1)
      (fun i x => by
        have hatom := (hCf_spec x).2
          (partialLpLimit_memWkp (I := I) (M := M)
            g r s i α x.1 x.2.2.1 K (h_pou i))
          (partialLpLimit_ae_zero_off_chartPouKernel (I := I) (M := M)
            g r s i α x.1 x.2.2.1 K (h_pou i))
        exact hatom.2)
  refine ⟨Csum * (Finset.univ : Finset (TensorCompIdx (E := E) r s
      × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
      × Fin (Module.finrank ℝ E))).card, by positivity, fun i => ?_⟩
  have h_memWkp : ∀ x : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
      × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
      MemWkp (d := Module.finrank ℝ E) K 2 (F i x) Ω := by
    intro x
    have hatom := (hCf_spec x).2
      (partialLpLimit_memWkp (I := I) (M := M)
        g r s i α x.1 x.2.2.1 K (h_pou i))
      (partialLpLimit_ae_zero_off_chartPouKernel (I := I) (M := M)
        g r s i α x.1 x.2.2.1 K (h_pou i))
    exact hatom.1
  have h_bound :
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (fun y => ∑ x : TensorCompIdx (E := E) r s
            × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
            × Fin (Module.finrank ℝ E), F i x y) Ω
        ≤ ENNReal.ofReal (Csum * (Finset.univ :
            Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
              × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E))).card)
          * ∑ pk : TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E),
              iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (partAtom i pk) Ω :=
    wkpNorm_finsetSum_le_const_mul_atomSum (I := I) (M := M)
      (α := α) (K := K) Finset.univ Finset.univ (F i) (partAtom i)
      (fun x => (x.1, x.2.2.1)) (fun x _ => Finset.mem_univ _)
      Csum hCsum_nn
      (fun x _ => h_memWkp x)
      (fun x _ => hCsum_bd i x)
  have h_eq : (fun y => ∑ x : TensorCompIdx (E := E) r s
      × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
      × Fin (Module.finrank ℝ E), F i x y)
      = (fun y => ∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                Set.indicator (chartPouKernel (I := I) (M := M) α)
                    (principalRotationFactor (I := I) (M := M)
                      g r s α P₀ P Q k l) y *
                  (partialLpLimit (I := I) (M := M) g r s i α P k :
                    EuclN → ℝ) y) := by
    funext y
    rw [hF_def]
    simp only [Fintype.sum_prod_type]
  have h_atom_eq : ∑ pk : TensorCompIdx (E := E) r s
      × Fin (Module.finrank ℝ E), iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
        (partAtom i pk) Ω
      = ∑ P : TensorCompIdx (E := E) r s,
          ∑ k : Fin (Module.finrank ℝ E),
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (fun y => ((partialLpLimit (I := I) (M := M)
                  g r s i α P k :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
              Ω := by
    rw [Fintype.sum_prod_type]
  rw [show (covPrincipalRotationCoeffLimit (I := I) (M := M)
        g r s i α P₀ : EuclN → ℝ)
      = (fun y => ∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                Set.indicator (chartPouKernel (I := I) (M := M) α)
                    (principalRotationFactor (I := I) (M := M)
                      g r s α P₀ P Q k l) y *
                  (partialLpLimit (I := I) (M := M) g r s i α P k :
                    EuclN → ℝ) y) from rfl]
  rw [← h_eq, hΩ_def, ← h_atom_eq]
  exact h_bound

omit [CompleteSpace E] in
theorem wkpNorm_covLowerOrderRotationValueCoeffLimit_le_uniform_unconditional
    (K : ℕ) (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (h_pou : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (covLowerOrderRotationValueCoeffLimit (I := I) (M := M)
              g r s i α P₀ : EuclN → ℝ)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal C *
            ((∑ P : TensorCompIdx (E := E) r s,
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
                    (chartTargetEuclid (I := I) (M := M) α))) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  set CfP : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) → ℝ := fun x =>
    (wkpNorm_indicatorFactor_mul_atom_le_uniform (I := I) (M := M) α K
      (valuePartialFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ x.1 x.2.1 x.2.2.1 x.2.2.2)).choose
    with hCfP_def
  have hCfP_spec : ∀ x : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)),
      0 ≤ CfP x ∧ ∀ {G : EuclN → ℝ},
        MemWkp (d := Module.finrank ℝ E) K 2 G Ω →
        (∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
          y ∉ chartPouKernel (I := I) (M := M) α → G y = 0) →
        MemWkp (d := Module.finrank ℝ E) K 2
            (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α)
              (valuePartialFactor (I := I) (M := M)
                g r s α P₀ x.1 x.2.1 x.2.2.1 x.2.2.2) y * G y) Ω ∧
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α)
                (valuePartialFactor (I := I) (M := M)
                  g r s α P₀ x.1 x.2.1 x.2.2.1 x.2.2.2) y * G y) Ω
            ≤ ENNReal.ofReal (CfP x) *
              iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 G Ω :=
    fun x =>
      (wkpNorm_indicatorFactor_mul_atom_le_uniform (I := I) (M := M) α K
        (valuePartialFactor_contDiffOn (I := I) (M := M)
          g r s α P₀ x.1 x.2.1 x.2.2.1 x.2.2.2)).choose_spec
  set CfC : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s) → ℝ := fun x =>
    (wkpNorm_indicatorFactor_mul_atom_le_uniform (I := I) (M := M) α K
      (valueComponentFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2)).choose
    with hCfC_def
  have hCfC_spec : ∀ x : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s),
      0 ≤ CfC x ∧ ∀ {G : EuclN → ℝ},
        MemWkp (d := Module.finrank ℝ E) K 2 G Ω →
        (∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
          y ∉ chartPouKernel (I := I) (M := M) α → G y = 0) →
        MemWkp (d := Module.finrank ℝ E) K 2
            (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α)
              (valueComponentFactor (I := I) (M := M)
                g r s α P₀ x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) y * G y) Ω ∧
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α)
                (valueComponentFactor (I := I) (M := M)
                  g r s α P₀ x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) y * G y) Ω
            ≤ ENNReal.ofReal (CfC x) *
              iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 G Ω :=
    fun x =>
      (wkpNorm_indicatorFactor_mul_atom_le_uniform (I := I) (M := M) α K
        (valueComponentFactor_contDiffOn (I := I) (M := M)
          g r s α P₀ x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2)).choose_spec
  set Fpart : TensorEigenIdx (I := I) (M := M) g r s → (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) → EuclN → ℝ :=
    fun i x y =>
      Set.indicator (chartPouKernel (I := I) (M := M) α)
          (valuePartialFactor (I := I) (M := M)
            g r s α P₀ x.1 x.2.1 x.2.2.1 x.2.2.2) y *
        ((partialLpLimit (I := I) (M := M) g r s i α x.1 x.2.2.1 :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hFpart_def
  set Fcomp : TensorEigenIdx (I := I) (M := M) g r s → (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s) → EuclN → ℝ :=
    fun i x y =>
      Set.indicator (chartPouKernel (I := I) (M := M) α)
          (valueComponentFactor (I := I) (M := M)
            g r s α P₀ x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) y *
        ((componentLpLimit (I := I) (M := M) g r s i α x.2.2.2.2 :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hFcomp_def
  set partAtom : TensorEigenIdx (I := I) (M := M) g r s →
      (TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)) → EuclN → ℝ :=
    fun i pk y =>
    ((partialLpLimit (I := I) (M := M) g r s i α pk.1 pk.2 :
      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hpartAtom_def
  set compAtom : TensorEigenIdx (I := I) (M := M) g r s →
      TensorCompIdx (E := E) r s → EuclN → ℝ :=
    fun i p y =>
    ((componentLpLimit (I := I) (M := M) g r s i α p :
      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hcompAtom_def
  obtain ⟨Cpart, hCpart_nn, hCpart_bd⟩ :=
    exists_uniform_const_of_finite_wkpNorm_bounds_uniform (I := I) (M := M)
      (α := α) (K := K) Fpart partAtom (fun x => (x.1, x.2.2.1)) CfP
      (fun x => (hCfP_spec x).1)
      (fun i x => by
        have hatom := (hCfP_spec x).2
          (partialLpLimit_memWkp (I := I) (M := M)
            g r s i α x.1 x.2.2.1 K (h_pou i))
          (partialLpLimit_ae_zero_off_chartPouKernel (I := I) (M := M)
            g r s i α x.1 x.2.2.1 K (h_pou i))
        exact hatom.2)
  obtain ⟨Ccomp, hCcomp_nn, hCcomp_bd⟩ :=
    exists_uniform_const_of_finite_wkpNorm_bounds_uniform (I := I) (M := M)
      (α := α) (K := K) Fcomp compAtom (fun x => x.2.2.2.2) CfC
      (fun x => (hCfC_spec x).1)
      (fun i x => by
        have hatom := (hCfC_spec x).2
          (componentLpLimit_memWkp (I := I) (M := M)
            g r s i α x.2.2.2.2 K (h_pou i))
          (componentLpLimit_ae_zero_off_chartPouKernel (I := I) (M := M)
            g r s i α x.2.2.2.2)
        exact hatom.2)
  refine ⟨max
      (Cpart * (Finset.univ : Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E))).card)
      (Ccomp * (Finset.univ : Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s)).card),
    le_trans (by positivity) (le_max_left _ _), fun i => ?_⟩
  set Cmax : ℝ := max
      (Cpart * (Finset.univ : Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E))).card)
      (Ccomp * (Finset.univ : Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s)).card) with hCmax_def
  have h_part_memWkp : ∀ x : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)),
      MemWkp (d := Module.finrank ℝ E) K 2 (Fpart i x) Ω := by
    intro x
    have hatom := (hCfP_spec x).2
      (partialLpLimit_memWkp (I := I) (M := M)
        g r s i α x.1 x.2.2.1 K (h_pou i))
      (partialLpLimit_ae_zero_off_chartPouKernel (I := I) (M := M)
        g r s i α x.1 x.2.2.1 K (h_pou i))
    exact hatom.1
  have h_comp_memWkp : ∀ x : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) K 2 (Fcomp i x) Ω := by
    intro x
    have hatom := (hCfC_spec x).2
      (componentLpLimit_memWkp (I := I) (M := M)
        g r s i α x.2.2.2.2 K (h_pou i))
      (componentLpLimit_ae_zero_off_chartPouKernel (I := I) (M := M)
        g r s i α x.2.2.2.2)
    exact hatom.1
  have h_part_bound :
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (fun y => ∑ x : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)), Fpart i x y) Ω
        ≤ ENNReal.ofReal (Cpart * (Finset.univ : Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E))).card)
          * ∑ pk : TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E),
              iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (partAtom i pk) Ω :=
    wkpNorm_finsetSum_le_const_mul_atomSum (I := I) (M := M)
      (α := α) (K := K) Finset.univ Finset.univ (Fpart i) (partAtom i)
      (fun x => (x.1, x.2.2.1)) (fun x _ => Finset.mem_univ _)
      Cpart hCpart_nn
      (fun x _ => h_part_memWkp x)
      (fun x _ => hCpart_bd i x)
  have h_comp_bound :
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (fun y => ∑ x : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s), Fcomp i x y) Ω
        ≤ ENNReal.ofReal (Ccomp * (Finset.univ : Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s)).card)
          * ∑ p : TensorCompIdx (E := E) r s,
              iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (compAtom i p) Ω :=
    wkpNorm_finsetSum_le_const_mul_atomSum (I := I) (M := M)
      (α := α) (K := K) Finset.univ Finset.univ (Fcomp i) (compAtom i)
      (fun x => x.2.2.2.2) (fun x _ => Finset.mem_univ _)
      Ccomp hCcomp_nn
      (fun x _ => h_comp_memWkp x)
      (fun x _ => hCcomp_bd i x)
  have h_part_eq : (fun y => ∑ x : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)), Fpart i x y)
      = (fun y => ∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                Set.indicator (chartPouKernel (I := I) (M := M) α)
                    (valuePartialFactor (I := I) (M := M)
                      g r s α P₀ P Q k l) y *
                  (partialLpLimit (I := I) (M := M) g r s i α P k :
                    EuclN → ℝ) y) := by
    funext y
    rw [hFpart_def]
    simp only [Fintype.sum_prod_type]
  have h_comp_eq : (fun y => ∑ x : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s), Fcomp i x y)
      = (fun y => ∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                ∑ p : TensorCompIdx (E := E) r s,
                  Set.indicator (chartPouKernel (I := I) (M := M) α)
                      (valueComponentFactor (I := I) (M := M)
                        g r s α P₀ P Q k l p) y *
                    (componentLpLimit (I := I) (M := M) g r s i α p :
                      EuclN → ℝ) y) := by
    funext y
    rw [hFcomp_def]
    simp only [Fintype.sum_prod_type]
  have h_part_atom_eq : ∑ pk : TensorCompIdx (E := E) r s
      × Fin (Module.finrank ℝ E), iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
        (partAtom i pk) Ω
      = ∑ P : TensorCompIdx (E := E) r s,
          ∑ k : Fin (Module.finrank ℝ E),
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (fun y => ((partialLpLimit (I := I) (M := M)
                  g r s i α P k :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
              Ω := by
    rw [Fintype.sum_prod_type]
  have hpart : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
        (fun y => ∑ x : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)), Fpart i x y) Ω
      ≤ ENNReal.ofReal Cmax *
        ∑ P : TensorCompIdx (E := E) r s,
          ∑ k : Fin (Module.finrank ℝ E),
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (fun y => ((partialLpLimit (I := I) (M := M)
                  g r s i α P k :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
              Ω := by
    rw [← h_part_atom_eq]
    refine h_part_bound.trans ?_
    exact mul_le_mul_of_nonneg_right
      (ENNReal.ofReal_le_ofReal (le_max_left _ _)) (zero_le _)
  have hcomp : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
        (fun y => ∑ x : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s), Fcomp i x y) Ω
      ≤ ENNReal.ofReal Cmax *
        ∑ p : TensorCompIdx (E := E) r s,
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((componentLpLimit (I := I) (M := M)
                g r s i α p :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
            Ω := by
    refine h_comp_bound.trans ?_
    exact mul_le_mul_of_nonneg_right
      (ENNReal.ofReal_le_ofReal (le_max_right _ _)) (zero_le _)
  have h_part_group_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ∑ x : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)), Fpart i x y) Ω :=
    memWkp_finsetSum (I := I) (M := M) _ (fun x _ => h_part_memWkp x)
  have h_comp_group_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ∑ x : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s), Fcomp i x y) Ω :=
    memWkp_finsetSum (I := I) (M := M) _ (fun x _ => h_comp_memWkp x)
  rw [show (covLowerOrderRotationValueCoeffLimit (I := I) (M := M)
        g r s i α P₀ : EuclN → ℝ)
      = (fun y => (∑ P : TensorCompIdx (E := E) r s,
            ∑ Q : TensorCompIdx (E := E) r s,
              ∑ k : Fin (Module.finrank ℝ E),
                ∑ l : Fin (Module.finrank ℝ E),
                  Set.indicator (chartPouKernel (I := I) (M := M) α)
                      (valuePartialFactor (I := I) (M := M)
                        g r s α P₀ P Q k l) y *
                    (partialLpLimit (I := I) (M := M) g r s i α P k :
                      EuclN → ℝ) y)
          + ∑ P : TensorCompIdx (E := E) r s,
              ∑ Q : TensorCompIdx (E := E) r s,
                ∑ k : Fin (Module.finrank ℝ E),
                  ∑ l : Fin (Module.finrank ℝ E),
                    ∑ p : TensorCompIdx (E := E) r s,
                      Set.indicator (chartPouKernel (I := I) (M := M) α)
                          (valueComponentFactor (I := I) (M := M)
                            g r s α P₀ P Q k l p) y *
                        (componentLpLimit (I := I) (M := M)
                          g r s i α p : EuclN → ℝ) y) from rfl]
  have h_bridge : (fun y => (∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                Set.indicator (chartPouKernel (I := I) (M := M) α)
                    (valuePartialFactor (I := I) (M := M)
                      g r s α P₀ P Q k l) y *
                  (partialLpLimit (I := I) (M := M) g r s i α P k :
                    EuclN → ℝ) y)
        + ∑ P : TensorCompIdx (E := E) r s,
            ∑ Q : TensorCompIdx (E := E) r s,
              ∑ k : Fin (Module.finrank ℝ E),
                ∑ l : Fin (Module.finrank ℝ E),
                  ∑ p : TensorCompIdx (E := E) r s,
                    Set.indicator (chartPouKernel (I := I) (M := M) α)
                        (valueComponentFactor (I := I) (M := M)
                          g r s α P₀ P Q k l p) y *
                      (componentLpLimit (I := I) (M := M)
                        g r s i α p : EuclN → ℝ) y)
      = (fun y => (∑ x : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)), Fpart i x y)
          + ∑ x : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s), Fcomp i x y) := by
    funext y
    rw [← congrFun h_part_eq y, ← congrFun h_comp_eq y]
  rw [h_bridge]
  calc
    iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
        (fun y => (∑ x : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)), Fpart i x y)
        + ∑ x : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s), Fcomp i x y) Ω
        ≤ iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (fun y => ∑ x : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)), Fpart i x y) Ω
          + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (fun y => ∑ x : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s), Fcomp i x y) Ω :=
        wkpNorm_add_le (d := Module.finrank ℝ E)
          (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open
          h_part_group_memWkp h_comp_group_memWkp
    _ ≤ ENNReal.ofReal Cmax *
          (∑ P : TensorCompIdx (E := E) r s,
            ∑ k : Fin (Module.finrank ℝ E),
              iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
                (fun y => ((partialLpLimit (I := I) (M := M)
                    g r s i α P k :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                  EuclN → ℝ) y) Ω)
        + ENNReal.ofReal Cmax *
          (∑ p : TensorCompIdx (E := E) r s,
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (fun y => ((componentLpLimit (I := I) (M := M)
                  g r s i α p :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                EuclN → ℝ) y) Ω) :=
        add_le_add hpart hcomp
    _ = ENNReal.ofReal Cmax *
          ((∑ P : TensorCompIdx (E := E) r s,
              ∑ k : Fin (Module.finrank ℝ E),
                iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
                  (fun y => ((partialLpLimit (I := I) (M := M)
                      g r s i α P k :
                    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                    EuclN → ℝ) y) Ω)
            + (∑ p : TensorCompIdx (E := E) r s,
                iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
                  (fun y => ((componentLpLimit (I := I) (M := M)
                      g r s i α p :
                    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                    EuclN → ℝ) y) Ω)) := by
      rw [mul_add]

omit [CompleteSpace E] in
theorem wkpNorm_weightedGradCoeffDivLimit_le_uniform_unconditional
    (K : ℕ) (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E))
    (h_pou : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (weightedGradCoeffDivLimit (I := I) (M := M)
              g r s i α P₀ l : EuclN → ℝ)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal C *
            ((∑ p : TensorCompIdx (E := E) r s,
                iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
                  (fun y => ((componentLpLimit (I := I) (M := M)
                      g r s i α p :
                    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                    EuclN → ℝ) y)
                  (chartTargetEuclid (I := I) (M := M) α))
              + (∑ p : TensorCompIdx (E := E) r s,
                  ∑ l' : Fin (Module.finrank ℝ E),
                    iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
                      (fun y => ((partialLpLimit (I := I) (M := M)
                          g r s i α p l' :
                        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                        EuclN → ℝ) y)
                      (chartTargetEuclid (I := I) (M := M) α))) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  set CfC : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s) → ℝ := fun x =>
    (wkpNorm_indicatorFactor_mul_atom_le_uniform (I := I) (M := M) α K
      (euclidPartial_weightedGradFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ l x.1 x.2.1 x.2.2.1 x.2.2.2)).choose
    with hCfC_def
  have hCfC_spec : ∀ x : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s),
      0 ≤ CfC x ∧ ∀ {G : EuclN → ℝ},
        MemWkp (d := Module.finrank ℝ E) K 2 G Ω →
        (∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
          y ∉ chartPouKernel (I := I) (M := M) α → G y = 0) →
        MemWkp (d := Module.finrank ℝ E) K 2
            (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α)
              (euclidPartial (E := E) l
                (weightedGradFactor (I := I) (M := M)
                  g r s α P₀ l x.1 x.2.1 x.2.2.1 x.2.2.2)) y * G y) Ω ∧
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α)
                (euclidPartial (E := E) l
                  (weightedGradFactor (I := I) (M := M)
                    g r s α P₀ l x.1 x.2.1 x.2.2.1 x.2.2.2)) y * G y) Ω
            ≤ ENNReal.ofReal (CfC x) *
              iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 G Ω :=
    fun x =>
      (wkpNorm_indicatorFactor_mul_atom_le_uniform (I := I) (M := M) α K
        (euclidPartial_weightedGradFactor_contDiffOn (I := I) (M := M)
          g r s α P₀ l x.1 x.2.1 x.2.2.1 x.2.2.2)).choose_spec
  set CfP : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s) → ℝ := fun x =>
    (wkpNorm_indicatorFactor_mul_atom_le_uniform (I := I) (M := M) α K
      (weightedGradFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ l x.1 x.2.1 x.2.2.1 x.2.2.2)).choose
    with hCfP_def
  have hCfP_spec : ∀ x : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s),
      0 ≤ CfP x ∧ ∀ {G : EuclN → ℝ},
        MemWkp (d := Module.finrank ℝ E) K 2 G Ω →
        (∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
          y ∉ chartPouKernel (I := I) (M := M) α → G y = 0) →
        MemWkp (d := Module.finrank ℝ E) K 2
            (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α)
              (weightedGradFactor (I := I) (M := M)
                g r s α P₀ l x.1 x.2.1 x.2.2.1 x.2.2.2) y * G y) Ω ∧
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α)
                (weightedGradFactor (I := I) (M := M)
                  g r s α P₀ l x.1 x.2.1 x.2.2.1 x.2.2.2) y * G y) Ω
            ≤ ENNReal.ofReal (CfP x) *
              iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 G Ω :=
    fun x =>
      (wkpNorm_indicatorFactor_mul_atom_le_uniform (I := I) (M := M) α K
        (weightedGradFactor_contDiffOn (I := I) (M := M)
          g r s α P₀ l x.1 x.2.1 x.2.2.1 x.2.2.2)).choose_spec
  set Fcomp : TensorEigenIdx (I := I) (M := M) g r s → (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s) → EuclN → ℝ :=
    fun i x y =>
      Set.indicator (chartPouKernel (I := I) (M := M) α)
          (euclidPartial (E := E) l
            (weightedGradFactor (I := I) (M := M)
              g r s α P₀ l x.1 x.2.1 x.2.2.1 x.2.2.2)) y *
        ((componentLpLimit (I := I) (M := M) g r s i α x.2.2.2 :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hFcomp_def
  set Fpart : TensorEigenIdx (I := I) (M := M) g r s → (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s) → EuclN → ℝ :=
    fun i x y =>
      Set.indicator (chartPouKernel (I := I) (M := M) α)
          (weightedGradFactor (I := I) (M := M)
            g r s α P₀ l x.1 x.2.1 x.2.2.1 x.2.2.2) y *
        ((partialLpLimit (I := I) (M := M) g r s i α x.2.2.2 l :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hFpart_def
  set compAtom : TensorEigenIdx (I := I) (M := M) g r s →
      TensorCompIdx (E := E) r s → EuclN → ℝ :=
    fun i p y =>
    ((componentLpLimit (I := I) (M := M) g r s i α p :
      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hcompAtom_def
  set partAtom : TensorEigenIdx (I := I) (M := M) g r s →
      (TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)) → EuclN → ℝ :=
    fun i pl y =>
    ((partialLpLimit (I := I) (M := M) g r s i α pl.1 pl.2 :
      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hpartAtom_def
  obtain ⟨Ccomp, hCcomp_nn, hCcomp_bd⟩ :=
    exists_uniform_const_of_finite_wkpNorm_bounds_uniform (I := I) (M := M)
      (α := α) (K := K) Fcomp compAtom (fun x => x.2.2.2) CfC
      (fun x => (hCfC_spec x).1)
      (fun i x => by
        have hatom := (hCfC_spec x).2
          (componentLpLimit_memWkp (I := I) (M := M)
            g r s i α x.2.2.2 K (h_pou i))
          (componentLpLimit_ae_zero_off_chartPouKernel (I := I) (M := M)
            g r s i α x.2.2.2)
        exact hatom.2)
  obtain ⟨Cpart, hCpart_nn, hCpart_bd⟩ :=
    exists_uniform_const_of_finite_wkpNorm_bounds_uniform (I := I) (M := M)
      (α := α) (K := K) Fpart partAtom (fun x => (x.2.2.2, l)) CfP
      (fun x => (hCfP_spec x).1)
      (fun i x => by
        have hatom := (hCfP_spec x).2
          (partialLpLimit_memWkp (I := I) (M := M)
            g r s i α x.2.2.2 l K (h_pou i))
          (partialLpLimit_ae_zero_off_chartPouKernel (I := I) (M := M)
            g r s i α x.2.2.2 l K (h_pou i))
        exact hatom.2)
  refine ⟨max
      (Ccomp * (Finset.univ : Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s)).card)
      (Cpart * (Finset.univ : Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s)).card),
    le_trans (by positivity) (le_max_left _ _), fun i => ?_⟩
  set Cmax : ℝ := max
      (Ccomp * (Finset.univ : Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s)).card)
      (Cpart * (Finset.univ : Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s)).card) with hCmax_def
  have h_comp_memWkp : ∀ x : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) K 2 (Fcomp i x) Ω := by
    intro x
    have hatom := (hCfC_spec x).2
      (componentLpLimit_memWkp (I := I) (M := M)
        g r s i α x.2.2.2 K (h_pou i))
      (componentLpLimit_ae_zero_off_chartPouKernel (I := I) (M := M)
        g r s i α x.2.2.2)
    exact hatom.1
  have h_part_memWkp : ∀ x : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) K 2 (Fpart i x) Ω := by
    intro x
    have hatom := (hCfP_spec x).2
      (partialLpLimit_memWkp (I := I) (M := M)
        g r s i α x.2.2.2 l K (h_pou i))
      (partialLpLimit_ae_zero_off_chartPouKernel (I := I) (M := M)
        g r s i α x.2.2.2 l K (h_pou i))
    exact hatom.1
  have h_comp_bound :
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (fun y => ∑ x : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s), Fcomp i x y) Ω
        ≤ ENNReal.ofReal (Ccomp * (Finset.univ : Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s)).card)
          * ∑ p : TensorCompIdx (E := E) r s,
              iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (compAtom i p) Ω :=
    wkpNorm_finsetSum_le_const_mul_atomSum (I := I) (M := M)
      (α := α) (K := K) Finset.univ Finset.univ (Fcomp i) (compAtom i)
      (fun x => x.2.2.2) (fun x _ => Finset.mem_univ _)
      Ccomp hCcomp_nn
      (fun x _ => h_comp_memWkp x)
      (fun x _ => hCcomp_bd i x)
  have h_part_bound :
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (fun y => ∑ x : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s), Fpart i x y) Ω
        ≤ ENNReal.ofReal (Cpart * (Finset.univ : Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s)).card)
          * ∑ pl : TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E),
              iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (partAtom i pl) Ω :=
    wkpNorm_finsetSum_le_const_mul_atomSum (I := I) (M := M)
      (α := α) (K := K) Finset.univ Finset.univ (Fpart i) (partAtom i)
      (fun x => (x.2.2.2, l)) (fun x _ => Finset.mem_univ _)
      Cpart hCpart_nn
      (fun x _ => h_part_memWkp x)
      (fun x _ => hCpart_bd i x)
  have h_comp_eq : (fun y => ∑ x : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s), Fcomp i x y)
      = (fun y => ∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ p : TensorCompIdx (E := E) r s,
                Set.indicator (chartPouKernel (I := I) (M := M) α)
                    (euclidPartial (E := E) l
                      (weightedGradFactor (I := I) (M := M)
                        g r s α P₀ l P Q k p)) y *
                  (componentLpLimit (I := I) (M := M) g r s i α p :
                    EuclN → ℝ) y) := by
    funext y
    rw [hFcomp_def]
    simp only [Fintype.sum_prod_type]
  have h_part_eq : (fun y => ∑ x : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s), Fpart i x y)
      = (fun y => ∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ p : TensorCompIdx (E := E) r s,
                Set.indicator (chartPouKernel (I := I) (M := M) α)
                    (weightedGradFactor (I := I) (M := M)
                      g r s α P₀ l P Q k p) y *
                  (partialLpLimit (I := I) (M := M) g r s i α p l :
                    EuclN → ℝ) y) := by
    funext y
    rw [hFpart_def]
    simp only [Fintype.sum_prod_type]
  have h_part_atom_eq : ∑ pl : TensorCompIdx (E := E) r s
      × Fin (Module.finrank ℝ E), iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
        (partAtom i pl) Ω
      = ∑ p : TensorCompIdx (E := E) r s,
          ∑ l' : Fin (Module.finrank ℝ E),
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (fun y => ((partialLpLimit (I := I) (M := M)
                  g r s i α p l' :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
              Ω := by
    rw [Fintype.sum_prod_type]
  have hcomp : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
        (fun y => ∑ x : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s), Fcomp i x y) Ω
      ≤ ENNReal.ofReal Cmax *
        ∑ p : TensorCompIdx (E := E) r s,
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((componentLpLimit (I := I) (M := M)
                g r s i α p :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
            Ω := by
    refine h_comp_bound.trans ?_
    exact mul_le_mul_of_nonneg_right
      (ENNReal.ofReal_le_ofReal (le_max_left _ _)) (zero_le _)
  have hpart : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
        (fun y => ∑ x : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s), Fpart i x y) Ω
      ≤ ENNReal.ofReal Cmax *
        ∑ p : TensorCompIdx (E := E) r s,
          ∑ l' : Fin (Module.finrank ℝ E),
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (fun y => ((partialLpLimit (I := I) (M := M)
                  g r s i α p l' :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
              Ω := by
    rw [← h_part_atom_eq]
    refine h_part_bound.trans ?_
    exact mul_le_mul_of_nonneg_right
      (ENNReal.ofReal_le_ofReal (le_max_right _ _)) (zero_le _)
  have h_comp_group_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ∑ x : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s), Fcomp i x y) Ω :=
    memWkp_finsetSum (I := I) (M := M) _ (fun x _ => h_comp_memWkp x)
  have h_part_group_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ∑ x : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s), Fpart i x y) Ω :=
    memWkp_finsetSum (I := I) (M := M) _ (fun x _ => h_part_memWkp x)
  rw [show (weightedGradCoeffDivLimit (I := I) (M := M)
        g r s i α P₀ l : EuclN → ℝ)
      = (fun y => (∑ P : TensorCompIdx (E := E) r s,
            ∑ Q : TensorCompIdx (E := E) r s,
              ∑ k : Fin (Module.finrank ℝ E),
                ∑ p : TensorCompIdx (E := E) r s,
                  Set.indicator (chartPouKernel (I := I) (M := M) α)
                      (euclidPartial (E := E) l
                        (weightedGradFactor (I := I) (M := M)
                          g r s α P₀ l P Q k p)) y *
                    (componentLpLimit (I := I) (M := M) g r s i α p :
                      EuclN → ℝ) y)
          + ∑ P : TensorCompIdx (E := E) r s,
              ∑ Q : TensorCompIdx (E := E) r s,
                ∑ k : Fin (Module.finrank ℝ E),
                  ∑ p : TensorCompIdx (E := E) r s,
                    Set.indicator (chartPouKernel (I := I) (M := M) α)
                        (weightedGradFactor (I := I) (M := M)
                          g r s α P₀ l P Q k p) y *
                      (partialLpLimit (I := I) (M := M) g r s i α p l :
                        EuclN → ℝ) y) from rfl]
  have h_bridge : (fun y => (∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ p : TensorCompIdx (E := E) r s,
                Set.indicator (chartPouKernel (I := I) (M := M) α)
                    (euclidPartial (E := E) l
                      (weightedGradFactor (I := I) (M := M)
                        g r s α P₀ l P Q k p)) y *
                  (componentLpLimit (I := I) (M := M) g r s i α p :
                    EuclN → ℝ) y)
        + ∑ P : TensorCompIdx (E := E) r s,
            ∑ Q : TensorCompIdx (E := E) r s,
              ∑ k : Fin (Module.finrank ℝ E),
                ∑ p : TensorCompIdx (E := E) r s,
                  Set.indicator (chartPouKernel (I := I) (M := M) α)
                      (weightedGradFactor (I := I) (M := M)
                        g r s α P₀ l P Q k p) y *
                    (partialLpLimit (I := I) (M := M) g r s i α p l :
                      EuclN → ℝ) y)
      = (fun y => (∑ x : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s), Fcomp i x y)
          + ∑ x : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s), Fpart i x y) := by
    funext y
    rw [← congrFun h_comp_eq y, ← congrFun h_part_eq y]
  rw [h_bridge]
  calc
    iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
        (fun y => (∑ x : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s), Fcomp i x y)
        + ∑ x : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s), Fpart i x y) Ω
        ≤ iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (fun y => ∑ x : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s), Fcomp i x y) Ω
          + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (fun y => ∑ x : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s), Fpart i x y) Ω :=
        wkpNorm_add_le (d := Module.finrank ℝ E)
          (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open
          h_comp_group_memWkp h_part_group_memWkp
    _ ≤ ENNReal.ofReal Cmax *
          (∑ p : TensorCompIdx (E := E) r s,
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (fun y => ((componentLpLimit (I := I) (M := M)
                  g r s i α p :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                EuclN → ℝ) y) Ω)
        + ENNReal.ofReal Cmax *
          (∑ p : TensorCompIdx (E := E) r s,
            ∑ l' : Fin (Module.finrank ℝ E),
              iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
                (fun y => ((partialLpLimit (I := I) (M := M)
                    g r s i α p l' :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                  EuclN → ℝ) y) Ω) :=
        add_le_add hcomp hpart
    _ = ENNReal.ofReal Cmax *
          ((∑ p : TensorCompIdx (E := E) r s,
              iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
                (fun y => ((componentLpLimit (I := I) (M := M)
                    g r s i α p :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                  EuclN → ℝ) y) Ω)
            + (∑ p : TensorCompIdx (E := E) r s,
                ∑ l' : Fin (Module.finrank ℝ E),
                  iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
                    (fun y => ((partialLpLimit (I := I) (M := M)
                        g r s i α p l' :
                      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                      EuclN → ℝ) y) Ω)) := by
      rw [mul_add]

end LowerOrderWkpNormBoundsUniform

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
