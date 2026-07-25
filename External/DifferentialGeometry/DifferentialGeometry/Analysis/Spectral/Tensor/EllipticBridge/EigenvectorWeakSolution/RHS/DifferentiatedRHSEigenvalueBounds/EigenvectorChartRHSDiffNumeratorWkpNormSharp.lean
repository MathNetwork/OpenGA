import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.RHS.DifferentiatedRHS.EigenvectorDifferentiatedRHSEpNorm
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.RHS.DifferentiatedRHS.EigenvectorDifferentiatedRHSWkpNorm
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Iterated.EigenvectorIteratedRegularityHigherQuant
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Regularity.EigenvectorArbitraryKRegularity
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Iterated.EigenvectorIteratedData


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
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl
open DifferentialGeometry.Analysis.Sobolev.Chart
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [CompleteSpace E] in
lemma sharp_wkpNorm_coef_mul_factor_le_uniform
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
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hΩ_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    hΩ_open.measurableSet
  have hKα_compact : IsCompact (chartPouKernel (I := I) (M := M) α) :=
    chartPouKernel_isCompact (I := I) (M := M) α
  have hKα_in : chartPouKernel (I := I) (M := M) α ⊆
      chartTargetEuclid (I := I) (M := M) α :=
    chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
  obtain ⟨δ, χ, _hδ_pos, _hδ_in, hχ_smooth, hχ_cs, _hχ_range, hχ_one, hχ_tsupp⟩ :=
    exists_smooth_cutoff_with_neighborhood (d := Module.finrank ℝ E)
      hKα_compact hΩ_open hKα_in
  have hχ_coef_smooth : ContDiff ℝ (⊤ : ℕ∞) (fun y => χ y * coef y) := by
    have h_open_compl : IsOpen ((tsupport χ)ᶜ) :=
      (isClosed_tsupport _).isOpen_compl
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy_supp : y ∈ tsupport χ
    · have hy_chart : y ∈ chartTargetEuclid (I := I) (M := M) α := hχ_tsupp hy_supp
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
  set Cδ : Set EuclN := Metric.cthickening δ (chartPouKernel (I := I) (M := M) α)
    with hCδ_def
  have hCδ_closed : IsClosed Cδ := Metric.isClosed_cthickening
  have hCδ_meas : MeasurableSet Cδ := hCδ_closed.measurableSet
  refine ⟨Kc, le_of_lt hKc_pos, fun factor hfactor_memWkp hfactor_ae_zero => ?_⟩
  have h_prod_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => (χ y * coef y) * factor y)
      (chartTargetEuclid (I := I) (M := M) α) :=
    MemWkp.smul_smooth_bounded (d := Module.finrank ℝ E) K
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open hχ_coef_smooth
      (fun j _hj y _hy => hC₀_bd y j _hj) hfactor_memWkp
  have h_ae_eq : (fun y => (χ y * coef y) * factor y)
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)]
      (fun y => coef y * factor y) := by
    have h_eq_on_Cδ : (fun y => (χ y * coef y) * factor y)
        =ᵐ[(volume : Measure EuclN).restrict Cδ]
        (fun y => coef y * factor y) := by
      refine (ae_restrict_iff' hCδ_meas).mpr ?_
      refine Filter.Eventually.of_forall fun y hy => ?_
      have hχy : χ y = 1 := hχ_one y hy
      change (χ y * coef y) * factor y = coef y * factor y
      rw [hχy]; ring
    have hKα_in_Cδ : chartPouKernel (I := I) (M := M) α ⊆ Cδ :=
      Metric.self_subset_cthickening _
    have h_diff_sub : chartTargetEuclid (I := I) (M := M) α \ Cδ ⊆
        chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α := fun y hy =>
      ⟨hy.1, fun hyK => hy.2 (hKα_in_Cδ hyK)⟩
    have h_factor_ae_zero_diff : factor =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \ Cδ)] (fun _ => (0 : ℝ)) := by
      have h_abs : (volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α \ Cδ) ≪
          (volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α \
            chartPouKernel (I := I) (M := M) α) :=
        MeasureTheory.Measure.absolutelyContinuous_of_le
          (MeasureTheory.Measure.restrict_mono h_diff_sub le_rfl)
      exact h_abs.ae_le hfactor_ae_zero
    have h_eq_on_diff : (fun y => (χ y * coef y) * factor y)
        =ᵐ[(volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α \ Cδ)]
        (fun y => coef y * factor y) := by
      filter_upwards [h_factor_ae_zero_diff] with y hy
      show (χ y * coef y) * factor y = coef y * factor y
      rw [hy]; ring
    have h_eq_on_inter : (fun y => (χ y * coef y) * factor y)
        =ᵐ[(volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α ∩ Cδ)]
        (fun y => coef y * factor y) := by
      have h_abs : (volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α ∩ Cδ) ≪
          (volume : Measure EuclN).restrict Cδ :=
        MeasureTheory.Measure.absolutelyContinuous_of_le
          (MeasureTheory.Measure.restrict_mono Set.inter_subset_right le_rfl)
      exact h_abs.ae_le h_eq_on_Cδ
    have h_diff_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α \ Cδ) :=
      hΩ_meas.diff hCδ_meas
    have h_cover : chartTargetEuclid (I := I) (M := M) α =
        (chartTargetEuclid (I := I) (M := M) α ∩ Cδ) ∪
          (chartTargetEuclid (I := I) (M := M) α \ Cδ) := by
      ext y; constructor
      · intro hy
        by_cases h : y ∈ Cδ
        · exact Or.inl ⟨hy, h⟩
        · exact Or.inr ⟨hy, h⟩
      · rintro (⟨hy, _⟩ | ⟨hy, _⟩) <;> exact hy
    have h_disj : Disjoint
        (chartTargetEuclid (I := I) (M := M) α ∩ Cδ)
        (chartTargetEuclid (I := I) (M := M) α \ Cδ) :=
      Set.disjoint_left.mpr fun y hy hy' => hy'.2 hy.2
    have hΩ_restrict_eq : (volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α) =
        (volume : Measure EuclN).restrict
          ((chartTargetEuclid (I := I) (M := M) α ∩ Cδ) ∪
            (chartTargetEuclid (I := I) (M := M) α \ Cδ)) := by
      rw [← h_cover]
    rw [hΩ_restrict_eq, MeasureTheory.Measure.restrict_union h_disj h_diff_meas]
    exact (MeasureTheory.ae_add_measure_iff).mpr ⟨h_eq_on_inter, h_eq_on_diff⟩
  have h_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => coef y * factor y) (chartTargetEuclid (I := I) (M := M) α) :=
    (MemWkp_congr_ae (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae_eq).mp h_prod_memWkp
  refine ⟨h_memWkp, ?_⟩
  have h_norm_eq : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
      (fun y => coef y * factor y) (chartTargetEuclid (I := I) (M := M) α) =
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
        (fun y => (χ y * coef y) * factor y)
        (chartTargetEuclid (I := I) (M := M) α) :=
    (wkpNorm_congr_ae (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae_eq).symm
  rw [h_norm_eq]
  exact hKc_bd hfactor_memWkp

omit [CompleteSpace E] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] in
private lemma sharp_memWkp_finset_sum
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

omit [CompleteSpace E] in

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma sharp_wkpNorm_sub_le
    {K : ℕ} {Ω : Set EuclN}
    (hΩ : IsOpen Ω) {u v : EuclN → ℝ}
    (hu : MemWkp (d := Module.finrank ℝ E) K 2 u Ω)
    (hv : MemWkp (d := Module.finrank ℝ E) K 2 v Ω) :
    iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (fun y => u y - v y) Ω ≤
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 u Ω
        + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 v Ω := by
  classical
  have h_fun : (fun y => u y - v y) = (fun y => u y + (fun y => - v y) y) := by
    funext y; ring
  rw [h_fun]
  have hv_neg : MemWkp (d := Module.finrank ℝ E) K 2 (fun y => - v y) Ω :=
    MemWkp.neg (d := Module.finrank ℝ E) (by norm_num) hΩ hv
  refine le_trans (wkpNorm_add_le (d := Module.finrank ℝ E) (by norm_num) hΩ hu hv_neg) ?_
  have h_neg_eq : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (fun y => - v y) Ω =
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 v Ω := by
    have h_smul : (fun y => - v y) = (fun y => (-1 : ℝ) * v y) := by
      funext y; ring
    rw [h_smul, wkpNorm_const_smul (d := Module.finrank ℝ E) (by norm_num) hΩ hv (-1)]
    simp
  rw [h_neg_eq]

omit [CompleteSpace E] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in

omit [NeZero (Module.finrank ℝ E)] in
private lemma sharp_layerA_coeff_contDiffOn
    (g : SmoothRiemannianMetric I M) (α : M) (m : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (a b : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y => (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
            (l (Fin.last m))) y)
          (EuclideanSpace.single b 1))
      (chartTargetEuclid (I := I) (M := M) α) := by
  have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_diffOn : ContDiffOn ℝ (⊤ : ℕ∞)
      (weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)))
      (chartTargetEuclid (I := I) (M := M) α) :=
    weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α a b (l (Fin.last m))
  have h_fderiv : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y => fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
          (l (Fin.last m))) y)
      (chartTargetEuclid (I := I) (M := M) α) :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen h_open).1 h_diffOn).2
  have h_eval : ContDiff ℝ (⊤ : ℕ∞)
      (fun (L : EuclN →L[ℝ] ℝ) => L (EuclideanSpace.single b 1)) :=
    (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single b (1 : ℝ))).contDiff
  exact h_eval.contDiffOn.comp h_fderiv (mapsTo_univ _ _)

omit [CompleteSpace E] in
lemma sharp_eigen_inv_one_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    1 ≤ (i.fst.val)⁻¹ := by
  have h_norm :
      ‖tensorResolventEigenbasisVec (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M)
          g r s) i‖ = 1 :=
    (tensorResolventEigenbasisVec_orthonormal (I := I) (M := M)
      (g := g) (r := r) (s := s)
      (tensorResolventL2_isCompactOperator (I := I) (M := M)
        g r s)).norm_eq_one i
  have hμ_unit : i.fst.val ∈ Set.Ioc (0 : ℝ) 1 :=
    tensorResolvent_eigenvalue_mem_unit_interval (I := I) (M := M) g r s
      (tensorResolventEigenbasisVec_mem (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M)
          g r s) i)
      (by
        intro h_zero
        rw [h_zero, norm_zero] at h_norm
        exact one_ne_zero h_norm.symm)
  exact (one_le_inv₀ hμ_unit.1).mpr hμ_unit.2

omit [CompleteSpace E] in
lemma sharp_ofReal_const_pow_eigen_inv_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    {C : ℝ} (hC_nn : 0 ≤ C) {k e : ℕ} (hke : k ≤ e) :
    ENNReal.ofReal (C * (i.fst.val)⁻¹ ^ k) ≤
      ENNReal.ofReal (C * (i.fst.val)⁻¹ ^ e) := by
  refine ENNReal.ofReal_le_ofReal ?_
  refine mul_le_mul_of_nonneg_left ?_ hC_nn
  exact pow_le_pow_right₀
    (sharp_eigen_inv_one_le (I := I) (M := M) g r s i) hke

omit [CompleteSpace E] in
private lemma sharp_iter_memWkp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (j K : ℕ)
    (idx : Fin j → Fin (Module.finrank ℝ E)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s i α P₀ j idx)
      (chartTargetEuclid (I := I) (M := M) α) := by
  have h_chart_cpt : MemWkp (d := Module.finrank ℝ E) (K + j) 2
      (eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀)
      (chartTargetEuclid (I := I) (M := M) α) :=
    eigenvector_chartComponent_memWkp_arbitrary (I := I) (M := M)
      g r s i (K + j) α P₀
  exact (eigenvectorChartIteratedPartial_wkpNorm_le_of_memWkp
    (I := I) (M := M) g r s i α P₀ j K h_chart_cpt idx).1

omit [CompleteSpace E] in
lemma sharp_invGramDerivCoeff_mul_iteratedPartial_wkpNorm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (CatomA : ℝ) (eAtomA : ℕ) (hCatomA_nn : 0 ≤ CatomA)
    (hAtomA_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
        (a : Fin (Module.finrank ℝ E)),
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (CatomA * (i.fst.val)⁻¹ ^ eAtomA) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y => ∑ a : Fin (Module.finrank ℝ E),
              ∑ b : Fin (Module.finrank ℝ E),
                (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
                      (l (Fin.last m))) y)
                    (EuclideanSpace.single b 1) *
                  eigenvectorChartIteratedPartial (I := I) (M := M)
                    g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal (C * CatomA * (i.fst.val)⁻¹ ^ eAtomA) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖ := by
  classical
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  let n : ℕ := Module.finrank ℝ E
  have h_per_pair_exists : ∀ a b : Fin n, ∃ C : ℝ, 0 ≤ C ∧ ∀ factor : EuclN → ℝ,
      MemWkp (d := Module.finrank ℝ E) K 2 factor
          (chartTargetEuclid (I := I) (M := M) α) →
      (factor =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α)] (fun _ => (0 : ℝ))) →
      MemWkp (d := Module.finrank ℝ E) K 2
          (fun y => (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
                  (l (Fin.last m))) y)
                (EuclideanSpace.single b 1) * factor y)
          (chartTargetEuclid (I := I) (M := M) α) ∧
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y => (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
                    (l (Fin.last m))) y)
                  (EuclideanSpace.single b 1) * factor y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal C *
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 factor
              (chartTargetEuclid (I := I) (M := M) α) :=
    fun a b => sharp_wkpNorm_coef_mul_factor_le_uniform (I := I) (M := M) α K
      (sharp_layerA_coeff_contDiffOn (I := I) (M := M) g α m l a b)
  let Kab : Fin n → Fin n → ℝ := fun a b => (h_per_pair_exists a b).choose
  have hKab_nn : ∀ a b : Fin n, 0 ≤ Kab a b :=
    fun a b => (h_per_pair_exists a b).choose_spec.1
  have hKab_bd : ∀ a b : Fin n, ∀ factor : EuclN → ℝ,
      MemWkp (d := Module.finrank ℝ E) K 2 factor
          (chartTargetEuclid (I := I) (M := M) α) →
      (factor =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α)] (fun _ => (0 : ℝ))) →
      MemWkp (d := Module.finrank ℝ E) K 2
          (fun y => (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
                  (l (Fin.last m))) y)
                (EuclideanSpace.single b 1) * factor y)
          (chartTargetEuclid (I := I) (M := M) α) ∧
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y => (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
                    (l (Fin.last m))) y)
                  (EuclideanSpace.single b 1) * factor y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal (Kab a b) *
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 factor
              (chartTargetEuclid (I := I) (M := M) α) :=
    fun a b => (h_per_pair_exists a b).choose_spec.2
  let Csum : ℝ := ∑ a : Fin n, ∑ b : Fin n, Kab a b
  have hCsum_nn : 0 ≤ Csum :=
    Finset.sum_nonneg fun a _ =>
      Finset.sum_nonneg fun b _ => hKab_nn a b
  refine ⟨Csum, hCsum_nn, fun i => ?_⟩
  have h_iter_mem : ∀ a : Fin n,
      MemWkp (d := Module.finrank ℝ E) K 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
        (chartTargetEuclid (I := I) (M := M) α) := fun a =>
    sharp_iter_memWkp (I := I) (M := M) g r s i α P₀ (m + 1) K
      (Fin.cons a (Fin.init l))
  have h_iter_ae_zero : ∀ a : Fin n,
      eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l))
        =ᵐ[(volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α \
            chartPouKernel (I := I) (M := M) α)] (fun _ => (0 : ℝ)) := fun a =>
    eigenvectorChartIteratedPartial_ae_zero_off_chartPouKernel
      (I := I) (M := M) g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l))
  have h_per_pair_bd : ∀ a b : Fin n,
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (fun y => (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
                  (l (Fin.last m))) y)
                (EuclideanSpace.single b 1) *
            eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (Kab a b * CatomA * (i.fst.val)⁻¹ ^ eAtomA) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖ := by
    intro a b
    obtain ⟨_h_mem, h_bd⟩ := hKab_bd a b _ (h_iter_mem a) (h_iter_ae_zero a)
    refine le_trans h_bd ?_
    refine le_trans (mul_le_mul' (le_refl _) (hAtomA_bd i a)) ?_
    rw [← mul_assoc, ← ENNReal.ofReal_mul (hKab_nn a b),
      mul_assoc (Kab a b) CatomA]
  have h_per_pair_mem : ∀ a b : Fin n,
      MemWkp (d := Module.finrank ℝ E) K 2
        (fun y => (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
                (l (Fin.last m))) y)
              (EuclideanSpace.single b 1) *
          eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
        (chartTargetEuclid (I := I) (M := M) α) :=
    fun a b => (hKab_bd a b _ (h_iter_mem a) (h_iter_ae_zero a)).1
  have h_inner_mem : ∀ a : Fin n,
      MemWkp (d := Module.finrank ℝ E) K 2
        (fun y => ∑ b : Fin n,
          (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
                (l (Fin.last m))) y)
              (EuclideanSpace.single b 1) *
            eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
        (chartTargetEuclid (I := I) (M := M) α) :=
    fun a => sharp_memWkp_finset_sum (α := α) (K := K) Finset.univ
      (fun b _ => h_per_pair_mem a b)
  have h_inner_tri : ∀ a : Fin n,
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (fun y => ∑ b : Fin n,
            (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
                  (l (Fin.last m))) y)
                (EuclideanSpace.single b 1) *
              eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ∑ b : Fin n,
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y => (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
                    (l (Fin.last m))) y)
                  (EuclideanSpace.single b 1) *
              eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
            (chartTargetEuclid (I := I) (M := M) α) :=
    fun a => wkpNorm_sum_le (d := Module.finrank ℝ E) (by norm_num) hΩ_open
      Finset.univ _ (fun b _ => h_per_pair_mem a b)
  have h_outer_tri :
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (fun y => ∑ a : Fin n, ∑ b : Fin n,
            (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
                  (l (Fin.last m))) y)
                (EuclideanSpace.single b 1) *
              eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ∑ a : Fin n,
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y => ∑ b : Fin n,
              (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
                    (l (Fin.last m))) y)
                  (EuclideanSpace.single b 1) *
                eigenvectorChartIteratedPartial (I := I) (M := M)
                  g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
            (chartTargetEuclid (I := I) (M := M) α) :=
    wkpNorm_sum_le (d := Module.finrank ℝ E) (by norm_num) hΩ_open Finset.univ
      _ (fun a _ => h_inner_mem a)
  refine le_trans h_outer_tri ?_
  refine le_trans (Finset.sum_le_sum (fun a _ =>
    (h_inner_tri a).trans (Finset.sum_le_sum (fun b _ => h_per_pair_bd a b)))) ?_
  have h1 : (0 : ℝ) ≤ (i.fst.val)⁻¹ := by
    have := sharp_eigen_inv_one_le (I := I) (M := M) g r s i
    linarith
  have h2 : 0 ≤ (i.fst.val)⁻¹ ^ eAtomA := pow_nonneg h1 _
  have hk_nn_full : ∀ a b : Fin n,
      0 ≤ Kab a b * CatomA * (i.fst.val)⁻¹ ^ eAtomA := fun a b =>
    mul_nonneg (mul_nonneg (hKab_nn a b) hCatomA_nn) h2
  have hpull1 :
      ∑ a : Fin n, ∑ b : Fin n,
          ENNReal.ofReal (Kab a b * CatomA * (i.fst.val)⁻¹ ^ eAtomA) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖
        = (∑ a : Fin n, ∑ b : Fin n,
            ENNReal.ofReal (Kab a b * CatomA * (i.fst.val)⁻¹ ^ eAtomA)) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖ := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_mul]
  have hpull2 :
      ∑ a : Fin n, ∑ b : Fin n,
          ENNReal.ofReal (Kab a b * CatomA * (i.fst.val)⁻¹ ^ eAtomA)
        = ENNReal.ofReal
            (∑ a : Fin n, ∑ b : Fin n,
              Kab a b * CatomA * (i.fst.val)⁻¹ ^ eAtomA) := by
    rw [show (∑ a : Fin n, ∑ b : Fin n,
              ENNReal.ofReal (Kab a b * CatomA * (i.fst.val)⁻¹ ^ eAtomA)) =
            ∑ a : Fin n, ENNReal.ofReal
              (∑ b : Fin n, Kab a b * CatomA * (i.fst.val)⁻¹ ^ eAtomA) from ?_,
        ← ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)
          (fun a _ => Finset.sum_nonneg (fun b _ => hk_nn_full a b))]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)
      (fun b _ => hk_nn_full a b)]
  have hcollapse : ∑ a : Fin n, ∑ b : Fin n,
        Kab a b * CatomA * (i.fst.val)⁻¹ ^ eAtomA =
      Csum * CatomA * (i.fst.val)⁻¹ ^ eAtomA := by
    change ∑ a : Fin n, ∑ b : Fin n,
        Kab a b * CatomA * (i.fst.val)⁻¹ ^ eAtomA =
      (∑ a : Fin n, ∑ b : Fin n, Kab a b) * CatomA * (i.fst.val)⁻¹ ^ eAtomA
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_mul, Finset.sum_mul]
  rw [hpull1, hpull2, hcollapse]

omit [CompleteSpace E] in
lemma sharp_invGramCoeff_mul_iteratedPartialWeakDeriv_wkpNorm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (CatomB : ℝ) (eAtomB : ℕ) (hCatomB_nn : 0 ≤ CatomB)
    (hAtomB_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
        (a b : Fin (Module.finrank ℝ E)),
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
            (d := Module.finrank ℝ E) 2 b
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
            (chartTargetEuclid (I := I) (M := M) α))
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (CatomB * (i.fst.val)⁻¹ ^ eAtomB) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y => ∑ a : Fin (Module.finrank ℝ E),
              ∑ b : Fin (Module.finrank ℝ E),
                weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
                  DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
                    (d := Module.finrank ℝ E) 2 b
                    (eigenvectorChartIteratedPartial (I := I) (M := M)
                      g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
                    (chartTargetEuclid (I := I) (M := M) α) y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal (C * CatomB * (i.fst.val)⁻¹ ^ eAtomB) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖ := by
  classical
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  let n : ℕ := Module.finrank ℝ E
  have h_per_pair_exists : ∀ a b : Fin n, ∃ C : ℝ, 0 ≤ C ∧ ∀ factor : EuclN → ℝ,
      MemWkp (d := Module.finrank ℝ E) K 2 factor
          (chartTargetEuclid (I := I) (M := M) α) →
      (factor =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α)] (fun _ => (0 : ℝ))) →
      MemWkp (d := Module.finrank ℝ E) K 2
          (fun y => weightedInvGramDerivOnEuclid (I := I) g α a b
              (l (Fin.last m)) y * factor y)
          (chartTargetEuclid (I := I) (M := M) α) ∧
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y => weightedInvGramDerivOnEuclid (I := I) g α a b
                (l (Fin.last m)) y * factor y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal C *
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 factor
              (chartTargetEuclid (I := I) (M := M) α) :=
    fun a b => sharp_wkpNorm_coef_mul_factor_le_uniform (I := I) (M := M) α K
      (weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α a b (l (Fin.last m)))
  let Kab : Fin n → Fin n → ℝ := fun a b => (h_per_pair_exists a b).choose
  have hKab_nn : ∀ a b : Fin n, 0 ≤ Kab a b :=
    fun a b => (h_per_pair_exists a b).choose_spec.1
  have hKab_bd : ∀ a b : Fin n, ∀ factor : EuclN → ℝ,
      MemWkp (d := Module.finrank ℝ E) K 2 factor
          (chartTargetEuclid (I := I) (M := M) α) →
      (factor =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α)] (fun _ => (0 : ℝ))) →
      MemWkp (d := Module.finrank ℝ E) K 2
          (fun y => weightedInvGramDerivOnEuclid (I := I) g α a b
              (l (Fin.last m)) y * factor y)
          (chartTargetEuclid (I := I) (M := M) α) ∧
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y => weightedInvGramDerivOnEuclid (I := I) g α a b
                (l (Fin.last m)) y * factor y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal (Kab a b) *
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 factor
              (chartTargetEuclid (I := I) (M := M) α) :=
    fun a b => (h_per_pair_exists a b).choose_spec.2
  let Csum : ℝ := ∑ a : Fin n, ∑ b : Fin n, Kab a b
  have hCsum_nn : 0 ≤ Csum :=
    Finset.sum_nonneg fun a _ =>
      Finset.sum_nonneg fun b _ => hKab_nn a b
  refine ⟨Csum, hCsum_nn, fun i => ?_⟩
  have h_inner_memWkp_succ : ∀ a : Fin n,
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
        (chartTargetEuclid (I := I) (M := M) α) := fun a =>
    sharp_iter_memWkp (I := I) (M := M) g r s i α P₀ (m + 1) (K + 1)
      (Fin.cons a (Fin.init l))
  have h_chosen_mem : ∀ a b : Fin n,
      MemWkp (d := Module.finrank ℝ E) K 2
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          (d := Module.finrank ℝ E) 2 b
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
          (chartTargetEuclid (I := I) (M := M) α))
        (chartTargetEuclid (I := I) (M := M) α) :=
    fun a b => (h_inner_memWkp_succ a).chosenWeakPartial_mem b
  have h_iter_ae_zero : ∀ a : Fin n,
      eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l))
        =ᵐ[(volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α \
            chartPouKernel (I := I) (M := M) α)] (fun _ => (0 : ℝ)) := fun a =>
    eigenvectorChartIteratedPartial_ae_zero_off_chartPouKernel
      (I := I) (M := M) g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l))
  have h_chosen_ae_zero : ∀ a b : Fin n,
      DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          (d := Module.finrank ℝ E) 2 b
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
          (chartTargetEuclid (I := I) (M := M) α)
        =ᵐ[(volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α \
            chartPouKernel (I := I) (M := M) α)] (fun _ => (0 : ℝ)) :=
    fun a b => chosenWeakPartial'_ae_zero_off_chartPouKernel_of_ae_zero
      (I := I) (M := M) α (h_iter_ae_zero a) b
  have h_per_pair_bd : ∀ a b : Fin n,
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (fun y => weightedInvGramDerivOnEuclid (I := I) g α a b
              (l (Fin.last m)) y *
            DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
              (d := Module.finrank ℝ E) 2 b
              (eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
              (chartTargetEuclid (I := I) (M := M) α) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (Kab a b * CatomB * (i.fst.val)⁻¹ ^ eAtomB) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖ := by
    intro a b
    obtain ⟨_h_mem, h_bd⟩ := hKab_bd a b _ (h_chosen_mem a b) (h_chosen_ae_zero a b)
    refine le_trans h_bd ?_
    refine le_trans (mul_le_mul' (le_refl _) (hAtomB_bd i a b)) ?_
    rw [← mul_assoc, ← ENNReal.ofReal_mul (hKab_nn a b),
      mul_assoc (Kab a b) CatomB]
  have h_per_pair_mem : ∀ a b : Fin n,
      MemWkp (d := Module.finrank ℝ E) K 2
        (fun y => weightedInvGramDerivOnEuclid (I := I) g α a b
            (l (Fin.last m)) y *
          DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
            (d := Module.finrank ℝ E) 2 b
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
            (chartTargetEuclid (I := I) (M := M) α) y)
        (chartTargetEuclid (I := I) (M := M) α) :=
    fun a b => (hKab_bd a b _ (h_chosen_mem a b) (h_chosen_ae_zero a b)).1
  have h_inner_mem : ∀ a : Fin n,
      MemWkp (d := Module.finrank ℝ E) K 2
        (fun y => ∑ b : Fin n,
          weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
            DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
              (d := Module.finrank ℝ E) 2 b
              (eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
              (chartTargetEuclid (I := I) (M := M) α) y)
        (chartTargetEuclid (I := I) (M := M) α) :=
    fun a => sharp_memWkp_finset_sum (α := α) (K := K) Finset.univ
      (fun b _ => h_per_pair_mem a b)
  have h_inner_tri : ∀ a : Fin n,
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (fun y => ∑ b : Fin n,
            weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
              DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
                (d := Module.finrank ℝ E) 2 b
                (eigenvectorChartIteratedPartial (I := I) (M := M)
                  g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
                (chartTargetEuclid (I := I) (M := M) α) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ∑ b : Fin n,
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y => weightedInvGramDerivOnEuclid (I := I) g α a b
                (l (Fin.last m)) y *
              DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
                (d := Module.finrank ℝ E) 2 b
                (eigenvectorChartIteratedPartial (I := I) (M := M)
                  g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
                (chartTargetEuclid (I := I) (M := M) α) y)
            (chartTargetEuclid (I := I) (M := M) α) :=
    fun a => wkpNorm_sum_le (d := Module.finrank ℝ E) (by norm_num) hΩ_open
      Finset.univ _ (fun b _ => h_per_pair_mem a b)
  have h_outer_tri :
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (fun y => ∑ a : Fin n, ∑ b : Fin n,
            weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
              DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
                (d := Module.finrank ℝ E) 2 b
                (eigenvectorChartIteratedPartial (I := I) (M := M)
                  g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
                (chartTargetEuclid (I := I) (M := M) α) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ∑ a : Fin n,
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y => ∑ b : Fin n,
              weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
                DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
                  (d := Module.finrank ℝ E) 2 b
                  (eigenvectorChartIteratedPartial (I := I) (M := M)
                    g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
                  (chartTargetEuclid (I := I) (M := M) α) y)
            (chartTargetEuclid (I := I) (M := M) α) :=
    wkpNorm_sum_le (d := Module.finrank ℝ E) (by norm_num) hΩ_open Finset.univ
      _ (fun a _ => h_inner_mem a)
  refine le_trans h_outer_tri ?_
  refine le_trans (Finset.sum_le_sum (fun a _ =>
    (h_inner_tri a).trans (Finset.sum_le_sum (fun b _ => h_per_pair_bd a b)))) ?_
  have h1 : (0 : ℝ) ≤ (i.fst.val)⁻¹ := by
    have := sharp_eigen_inv_one_le (I := I) (M := M) g r s i
    linarith
  have h2 : 0 ≤ (i.fst.val)⁻¹ ^ eAtomB := pow_nonneg h1 _
  have hk_nn_full : ∀ a b : Fin n,
      0 ≤ Kab a b * CatomB * (i.fst.val)⁻¹ ^ eAtomB := fun a b =>
    mul_nonneg (mul_nonneg (hKab_nn a b) hCatomB_nn) h2
  have hpull1 :
      ∑ a : Fin n, ∑ b : Fin n,
          ENNReal.ofReal (Kab a b * CatomB * (i.fst.val)⁻¹ ^ eAtomB) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖
        = (∑ a : Fin n, ∑ b : Fin n,
            ENNReal.ofReal (Kab a b * CatomB * (i.fst.val)⁻¹ ^ eAtomB)) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖ := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_mul]
  have hpull2 :
      ∑ a : Fin n, ∑ b : Fin n,
          ENNReal.ofReal (Kab a b * CatomB * (i.fst.val)⁻¹ ^ eAtomB)
        = ENNReal.ofReal
            (∑ a : Fin n, ∑ b : Fin n,
              Kab a b * CatomB * (i.fst.val)⁻¹ ^ eAtomB) := by
    rw [show (∑ a : Fin n, ∑ b : Fin n,
              ENNReal.ofReal (Kab a b * CatomB * (i.fst.val)⁻¹ ^ eAtomB)) =
            ∑ a : Fin n, ENNReal.ofReal
              (∑ b : Fin n, Kab a b * CatomB * (i.fst.val)⁻¹ ^ eAtomB) from ?_,
        ← ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)
          (fun a _ => Finset.sum_nonneg (fun b _ => hk_nn_full a b))]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)
      (fun b _ => hk_nn_full a b)]
  have hcollapse : ∑ a : Fin n, ∑ b : Fin n,
        Kab a b * CatomB * (i.fst.val)⁻¹ ^ eAtomB =
      Csum * CatomB * (i.fst.val)⁻¹ ^ eAtomB := by
    change ∑ a : Fin n, ∑ b : Fin n,
        Kab a b * CatomB * (i.fst.val)⁻¹ ^ eAtomB =
      (∑ a : Fin n, ∑ b : Fin n, Kab a b) * CatomB * (i.fst.val)⁻¹ ^ eAtomB
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_mul, Finset.sum_mul]
  rw [hpull1, hpull2, hcollapse]

omit [CompleteSpace E] in
lemma sharp_densityDeriv_mul_iteratedPartial_wkpNorm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (CatomC : ℝ) (eAtomC : ℕ) (_hCatomC_nn : 0 ≤ CatomC)
    (hAtomC_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s),
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ m (Fin.init l))
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (CatomC * (i.fst.val)⁻¹ ^ eAtomC) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y =>
              densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
                eigenvectorChartIteratedPartial (I := I) (M := M)
                  g r s i α P₀ m (Fin.init l) y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal (C * CatomC * (i.fst.val)⁻¹ ^ eAtomC) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖ := by
  classical
  obtain ⟨Kc, hKc_nn, hKc⟩ := sharp_wkpNorm_coef_mul_factor_le_uniform
    (I := I) (M := M) α K
    (densityDerivOnEuclid_contDiffOn (I := I) g α (l (Fin.last m)))
  refine ⟨Kc, hKc_nn, fun i => ?_⟩
  have h_iter_mem : MemWkp (d := Module.finrank ℝ E) K 2
      (eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s i α P₀ m (Fin.init l))
      (chartTargetEuclid (I := I) (M := M) α) :=
    sharp_iter_memWkp (I := I) (M := M) g r s i α P₀ m K (Fin.init l)
  have h_iter_ae_zero :
      eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ m (Fin.init l)
        =ᵐ[(volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α \
            chartPouKernel (I := I) (M := M) α)] (fun _ => (0 : ℝ)) :=
    eigenvectorChartIteratedPartial_ae_zero_off_chartPouKernel
      (I := I) (M := M) g r s i α P₀ m (Fin.init l)
  obtain ⟨_h_mem, h_bd⟩ := hKc _ h_iter_mem h_iter_ae_zero
  refine le_trans h_bd ?_
  refine le_trans (mul_le_mul' (le_refl _) (hAtomC_bd i)) ?_
  rw [← mul_assoc, ← ENNReal.ofReal_mul hKc_nn, mul_assoc Kc CatomC]

omit [CompleteSpace E] in
lemma sharp_densityDeriv_mul_prevChartFun_wkpNorm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (_P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (fChartEffPrev : TensorEigenIdx (I := I) (M := M) g r s → EuclN → ℝ)
    (h_prev_mem : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      MemWkp (d := Module.finrank ℝ E) K 2 (fChartEffPrev i)
        (chartTargetEuclid (I := I) (M := M) α))
    (h_prev_zero : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      fChartEffPrev i =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α)] (fun _ => (0 : ℝ)))
    (CatomD : ℝ) (eAtomD : ℕ) (_hCatomD_nn : 0 ≤ CatomD)
    (hAtomD_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s),
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (fChartEffPrev i)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (CatomD * (i.fst.val)⁻¹ ^ eAtomD) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y =>
              densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
                fChartEffPrev i y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal (C * CatomD * (i.fst.val)⁻¹ ^ eAtomD) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖ := by
  classical
  obtain ⟨Kc, hKc_nn, hKc⟩ := sharp_wkpNorm_coef_mul_factor_le_uniform
    (I := I) (M := M) α K
    (densityDerivOnEuclid_contDiffOn (I := I) g α (l (Fin.last m)))
  refine ⟨Kc, hKc_nn, fun i => ?_⟩
  obtain ⟨_h_mem, h_bd⟩ := hKc _ (h_prev_mem i) (h_prev_zero i)
  refine le_trans h_bd ?_
  refine le_trans (mul_le_mul' (le_refl _) (hAtomD_bd i)) ?_
  rw [← mul_assoc, ← ENNReal.ofReal_mul hKc_nn, mul_assoc Kc CatomD]

omit [CompleteSpace E] in
lemma sharp_density_mul_prevChartFunWeakDeriv_wkpNorm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (_P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (fChartEffPrev : TensorEigenIdx (I := I) (M := M) g r s → EuclN → ℝ)
    (h_prev_mem_succ : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2 (fChartEffPrev i)
        (chartTargetEuclid (I := I) (M := M) α))
    (h_prev_zero : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      fChartEffPrev i =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α)] (fun _ => (0 : ℝ)))
    (CatomE : ℝ) (eAtomE : ℕ) (_hCatomE_nn : 0 ≤ CatomE)
    (hAtomE_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s),
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
            (d := Module.finrank ℝ E) 2 (l (Fin.last m))
            (fChartEffPrev i)
            (chartTargetEuclid (I := I) (M := M) α))
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (CatomE * (i.fst.val)⁻¹ ^ eAtomE) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y =>
              densityOnEuclid (I := I) g α y *
                DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
                  (d := Module.finrank ℝ E) 2 (l (Fin.last m))
                  (fChartEffPrev i) (chartTargetEuclid (I := I) (M := M) α) y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal (C * CatomE * (i.fst.val)⁻¹ ^ eAtomE) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖ := by
  classical
  obtain ⟨Kc, hKc_nn, hKc⟩ := sharp_wkpNorm_coef_mul_factor_le_uniform
    (I := I) (M := M) α K (densityOnEuclid_contDiffOn (I := I) g α)
  refine ⟨Kc, hKc_nn, fun i => ?_⟩
  have h_chosen_mem : MemWkp (d := Module.finrank ℝ E) K 2
      (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) 2 (l (Fin.last m))
        (fChartEffPrev i) (chartTargetEuclid (I := I) (M := M) α))
      (chartTargetEuclid (I := I) (M := M) α) :=
    (h_prev_mem_succ i).chosenWeakPartial_mem (l (Fin.last m))
  have h_chosen_ae_zero :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          (d := Module.finrank ℝ E) 2 (l (Fin.last m))
          (fChartEffPrev i) (chartTargetEuclid (I := I) (M := M) α)
        =ᵐ[(volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α \
            chartPouKernel (I := I) (M := M) α)] (fun _ => (0 : ℝ)) :=
    chosenWeakPartial'_ae_zero_off_chartPouKernel_of_ae_zero
      (I := I) (M := M) α (h_prev_zero i) (l (Fin.last m))
  obtain ⟨_h_mem, h_bd⟩ := hKc _ h_chosen_mem h_chosen_ae_zero
  refine le_trans h_bd ?_
  refine le_trans (mul_le_mul' (le_refl _) (hAtomE_bd i)) ?_
  rw [← mul_assoc, ← ENNReal.ofReal_mul hKc_nn, mul_assoc Kc CatomE]

set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 2000000 in

omit [CompleteSpace E] in
theorem eigenvectorChartRHSDiffNumerator_wkpNorm_le_chartcpt_sharp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (fChartEffPrev : TensorEigenIdx (I := I) (M := M) g r s → EuclN → ℝ)
    (CatomA : ℝ) (eAtomA : ℕ) (hCatomA_nn : 0 ≤ CatomA)
    (hAtomA_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
        (a : Fin (Module.finrank ℝ E)),
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (CatomA * (i.fst.val)⁻¹ ^ eAtomA) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖)
    (CatomB : ℝ) (eAtomB : ℕ) (hCatomB_nn : 0 ≤ CatomB)
    (hAtomB_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
        (a b : Fin (Module.finrank ℝ E)),
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
            (d := Module.finrank ℝ E) 2 b
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
            (chartTargetEuclid (I := I) (M := M) α))
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (CatomB * (i.fst.val)⁻¹ ^ eAtomB) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖)
    (CatomC : ℝ) (eAtomC : ℕ) (hCatomC_nn : 0 ≤ CatomC)
    (hAtomC_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s),
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ m (Fin.init l))
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (CatomC * (i.fst.val)⁻¹ ^ eAtomC) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖)
    (CatomD : ℝ) (eAtomD : ℕ) (hCatomD_nn : 0 ≤ CatomD)
    (hAtomD_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s),
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (fChartEffPrev i)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (CatomD * (i.fst.val)⁻¹ ^ eAtomD) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖)
    (CatomE : ℝ) (eAtomE : ℕ) (hCatomE_nn : 0 ≤ CatomE)
    (hAtomE_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s),
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
            (d := Module.finrank ℝ E) 2 (l (Fin.last m))
            (fChartEffPrev i)
            (chartTargetEuclid (I := I) (M := M) α))
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (CatomE * (i.fst.val)⁻¹ ^ eAtomE) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖)
    (h_prev_mem_succ : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2 (fChartEffPrev i)
        (chartTargetEuclid (I := I) (M := M) α))
    (h_prev_zero : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      fChartEffPrev i =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α)] (fun _ => (0 : ℝ))) :
    ∃ (C : ℝ) (e : ℕ), 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y => eigenvectorChartRHSDiffNumerator (I := I) (M := M)
              g r s i α P₀ m l (fChartEffPrev i) y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal (C * (i.fst.val)⁻¹ ^ e) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖ := by
  classical
  have h_prev_mem_K : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      MemWkp (d := Module.finrank ℝ E) K 2 (fChartEffPrev i)
        (chartTargetEuclid (I := I) (M := M) α) := fun i =>
    (h_prev_mem_succ i).le_of_le (by omega)
  obtain ⟨CA, hCA_nn, hCA⟩ :=
    sharp_invGramDerivCoeff_mul_iteratedPartial_wkpNorm_le (I := I) (M := M) g r s α P₀ m K l
      CatomA eAtomA hCatomA_nn hAtomA_bd
  obtain ⟨CB, hCB_nn, hCB⟩ :=
    sharp_invGramCoeff_mul_iteratedPartialWeakDeriv_wkpNorm_le (I := I) (M := M) g r s α P₀ m K l
      CatomB eAtomB hCatomB_nn hAtomB_bd
  obtain ⟨CC, hCC_nn, hCC⟩ :=
    sharp_densityDeriv_mul_iteratedPartial_wkpNorm_le (I := I) (M := M) g r s α P₀ m K l
      CatomC eAtomC hCatomC_nn hAtomC_bd
  obtain ⟨CD, hCD_nn, hCD⟩ :=
    sharp_densityDeriv_mul_prevChartFun_wkpNorm_le (I := I) (M := M) g r s α P₀ m K l
      fChartEffPrev h_prev_mem_K h_prev_zero CatomD eAtomD hCatomD_nn hAtomD_bd
  obtain ⟨CE, hCE_nn, hCE⟩ :=
    sharp_density_mul_prevChartFunWeakDeriv_wkpNorm_le (I := I) (M := M) g r s α P₀ m K l
      fChartEffPrev h_prev_mem_succ h_prev_zero CatomE eAtomE hCatomE_nn hAtomE_bd
  set e : ℕ := max (max eAtomA (max eAtomB eAtomC)) (max eAtomD eAtomE)
    with he_def
  have heA : eAtomA ≤ e := le_max_of_le_left (le_max_left _ _)
  have heB : eAtomB ≤ e := le_max_of_le_left (le_trans (le_max_left _ _)
    (le_max_right _ _))
  have heC : eAtomC ≤ e := le_max_of_le_left (le_trans (le_max_right _ _)
    (le_max_right _ _))
  have heD : eAtomD ≤ e := le_max_of_le_right (le_max_left _ _)
  have heE : eAtomE ≤ e := le_max_of_le_right (le_max_right _ _)
  have hCA_prod_nn : 0 ≤ CA * CatomA := mul_nonneg hCA_nn hCatomA_nn
  have hCB_prod_nn : 0 ≤ CB * CatomB := mul_nonneg hCB_nn hCatomB_nn
  have hCC_prod_nn : 0 ≤ CC * CatomC := mul_nonneg hCC_nn hCatomC_nn
  have hCD_prod_nn : 0 ≤ CD * CatomD := mul_nonneg hCD_nn hCatomD_nn
  have hCE_prod_nn : 0 ≤ CE * CatomE := mul_nonneg hCE_nn hCatomE_nn
  refine ⟨CA * CatomA + CB * CatomB + CC * CatomC + CD * CatomD + CE * CatomE,
    e, by positivity, fun i => ?_⟩
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  set Rhs : ℝ≥0∞ := ENNReal.ofReal
      ‖tensorResolventEigenbasisVec (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M)
          g r s) i‖ with hRhs_def
  set layerA : EuclN → ℝ := fun y => ∑ a : Fin (Module.finrank ℝ E),
    ∑ b : Fin (Module.finrank ℝ E),
      (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
            (l (Fin.last m))) y)
          (EuclideanSpace.single b 1) *
        eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y with hlayerA_def
  set layerB : EuclN → ℝ := fun y => ∑ a : Fin (Module.finrank ℝ E),
    ∑ b : Fin (Module.finrank ℝ E),
      weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
        DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          (d := Module.finrank ℝ E) 2 b
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
          (chartTargetEuclid (I := I) (M := M) α) y with hlayerB_def
  set layerC : EuclN → ℝ := fun y =>
    densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
      eigenvectorChartIteratedPartial (I := I) (M := M) g r s i α P₀
        m (Fin.init l) y with hlayerC_def
  set layerD : EuclN → ℝ := fun y =>
    densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
      fChartEffPrev i y with hlayerD_def
  set layerE : EuclN → ℝ := fun y =>
    densityOnEuclid (I := I) g α y *
      DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) 2 (l (Fin.last m))
        (fChartEffPrev i) (chartTargetEuclid (I := I) (M := M) α) y
    with hlayerE_def
  have h_num_eq : (fun y => eigenvectorChartRHSDiffNumerator
      (I := I) (M := M)
      g r s i α P₀ m l (fChartEffPrev i) y) =
      fun y => layerA y + layerB y - layerC y + layerD y + layerE y := by
    funext y
    show eigenvectorChartRHSDiffNumerator (I := I) (M := M)
        g r s i α P₀ m l (fChartEffPrev i) y =
      layerA y + layerB y - layerC y + layerD y + layerE y
    rw [hlayerA_def, hlayerB_def, hlayerC_def, hlayerD_def, hlayerE_def,
      eigenvectorChartRHSDiffNumerator]
  have hA_mem : MemWkp (d := Module.finrank ℝ E) K 2 layerA
      (chartTargetEuclid (I := I) (M := M) α) := by
    rw [hlayerA_def]
    refine sharp_memWkp_finset_sum (α := α) (K := K) Finset.univ
      (fun a _ => ?_)
    refine sharp_memWkp_finset_sum (α := α) (K := K) Finset.univ
      (fun b _ => ?_)
    obtain ⟨_Kc_ab, _hKc_ab_nn, hKc_ab⟩ := sharp_wkpNorm_coef_mul_factor_le_uniform
      (I := I) (M := M) α K
      (sharp_layerA_coeff_contDiffOn (I := I) (M := M) g α m l a b)
    exact (hKc_ab _
      (sharp_iter_memWkp (I := I) (M := M) g r s i α P₀ (m + 1) K
        (Fin.cons a (Fin.init l)))
      (eigenvectorChartIteratedPartial_ae_zero_off_chartPouKernel
        (I := I) (M := M) g r s i α P₀ (m + 1)
        (Fin.cons a (Fin.init l)))).1
  have hB_mem : MemWkp (d := Module.finrank ℝ E) K 2 layerB
      (chartTargetEuclid (I := I) (M := M) α) := by
    rw [hlayerB_def]
    refine sharp_memWkp_finset_sum (α := α) (K := K) Finset.univ
      (fun a _ => ?_)
    refine sharp_memWkp_finset_sum (α := α) (K := K) Finset.univ
      (fun b _ => ?_)
    obtain ⟨_Kc_ab, _hKc_ab_nn, hKc_ab⟩ := sharp_wkpNorm_coef_mul_factor_le_uniform
      (I := I) (M := M) α K
      (weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α a b (l (Fin.last m)))
    have h_chosen_mem : MemWkp (d := Module.finrank ℝ E) K 2
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          (d := Module.finrank ℝ E) 2 b
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
          (chartTargetEuclid (I := I) (M := M) α))
        (chartTargetEuclid (I := I) (M := M) α) :=
      (sharp_iter_memWkp (I := I) (M := M) g r s i α P₀ (m + 1)
        (K + 1) (Fin.cons a (Fin.init l))).chosenWeakPartial_mem b
    have h_chosen_ae_zero :
        DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
            (d := Module.finrank ℝ E) 2 b
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
            (chartTargetEuclid (I := I) (M := M) α)
          =ᵐ[(volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α \
              chartPouKernel (I := I) (M := M) α)] (fun _ => (0 : ℝ)) :=
      chosenWeakPartial'_ae_zero_off_chartPouKernel_of_ae_zero
        (I := I) (M := M) α
        (eigenvectorChartIteratedPartial_ae_zero_off_chartPouKernel
          (I := I) (M := M) g r s i α P₀ (m + 1)
          (Fin.cons a (Fin.init l))) b
    exact (hKc_ab _ h_chosen_mem h_chosen_ae_zero).1
  have hC_mem : MemWkp (d := Module.finrank ℝ E) K 2 layerC
      (chartTargetEuclid (I := I) (M := M) α) := by
    rw [hlayerC_def]
    obtain ⟨_Kc, _hKc_nn, hKc⟩ := sharp_wkpNorm_coef_mul_factor_le_uniform
      (I := I) (M := M) α K
      (densityDerivOnEuclid_contDiffOn (I := I) g α (l (Fin.last m)))
    exact (hKc _
      (sharp_iter_memWkp (I := I) (M := M) g r s i α P₀ m K
        (Fin.init l))
      (eigenvectorChartIteratedPartial_ae_zero_off_chartPouKernel
        (I := I) (M := M) g r s i α P₀ m (Fin.init l))).1
  have hD_mem : MemWkp (d := Module.finrank ℝ E) K 2 layerD
      (chartTargetEuclid (I := I) (M := M) α) := by
    rw [hlayerD_def]
    obtain ⟨_Kc, _hKc_nn, hKc⟩ := sharp_wkpNorm_coef_mul_factor_le_uniform
      (I := I) (M := M) α K
      (densityDerivOnEuclid_contDiffOn (I := I) g α (l (Fin.last m)))
    exact (hKc _ (h_prev_mem_K i) (h_prev_zero i)).1
  have hE_mem : MemWkp (d := Module.finrank ℝ E) K 2 layerE
      (chartTargetEuclid (I := I) (M := M) α) := by
    rw [hlayerE_def]
    obtain ⟨_Kc, _hKc_nn, hKc⟩ := sharp_wkpNorm_coef_mul_factor_le_uniform
      (I := I) (M := M) α K (densityOnEuclid_contDiffOn (I := I) g α)
    have h_chosen_mem : MemWkp (d := Module.finrank ℝ E) K 2
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          (d := Module.finrank ℝ E) 2 (l (Fin.last m))
          (fChartEffPrev i) (chartTargetEuclid (I := I) (M := M) α))
        (chartTargetEuclid (I := I) (M := M) α) :=
      (h_prev_mem_succ i).chosenWeakPartial_mem (l (Fin.last m))
    have h_chosen_ae_zero :
        DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
            (d := Module.finrank ℝ E) 2 (l (Fin.last m))
            (fChartEffPrev i) (chartTargetEuclid (I := I) (M := M) α)
          =ᵐ[(volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α \
              chartPouKernel (I := I) (M := M) α)] (fun _ => (0 : ℝ)) :=
      chosenWeakPartial'_ae_zero_off_chartPouKernel_of_ae_zero
        (I := I) (M := M) α (h_prev_zero i) (l (Fin.last m))
    exact (hKc _ h_chosen_mem h_chosen_ae_zero).1
  have hCA_e : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 layerA
      (chartTargetEuclid (I := I) (M := M) α) ≤
      ENNReal.ofReal (CA * CatomA * (i.fst.val)⁻¹ ^ e) * Rhs := by
    refine le_trans (hCA i) (mul_le_mul' ?_ (le_refl _))
    exact sharp_ofReal_const_pow_eigen_inv_le (I := I) (M := M)
      g r s i hCA_prod_nn heA
  have hCB_e : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 layerB
      (chartTargetEuclid (I := I) (M := M) α) ≤
      ENNReal.ofReal (CB * CatomB * (i.fst.val)⁻¹ ^ e) * Rhs := by
    refine le_trans (hCB i) (mul_le_mul' ?_ (le_refl _))
    exact sharp_ofReal_const_pow_eigen_inv_le (I := I) (M := M)
      g r s i hCB_prod_nn heB
  have hCC_e : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 layerC
      (chartTargetEuclid (I := I) (M := M) α) ≤
      ENNReal.ofReal (CC * CatomC * (i.fst.val)⁻¹ ^ e) * Rhs := by
    refine le_trans (hCC i) (mul_le_mul' ?_ (le_refl _))
    exact sharp_ofReal_const_pow_eigen_inv_le (I := I) (M := M)
      g r s i hCC_prod_nn heC
  have hCD_e : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 layerD
      (chartTargetEuclid (I := I) (M := M) α) ≤
      ENNReal.ofReal (CD * CatomD * (i.fst.val)⁻¹ ^ e) * Rhs := by
    refine le_trans (hCD i) (mul_le_mul' ?_ (le_refl _))
    exact sharp_ofReal_const_pow_eigen_inv_le (I := I) (M := M)
      g r s i hCD_prod_nn heD
  have hCE_e : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 layerE
      (chartTargetEuclid (I := I) (M := M) α) ≤
      ENNReal.ofReal (CE * CatomE * (i.fst.val)⁻¹ ^ e) * Rhs := by
    refine le_trans (hCE i) (mul_le_mul' ?_ (le_refl _))
    exact sharp_ofReal_const_pow_eigen_inv_le (I := I) (M := M)
      g r s i hCE_prod_nn heE
  rw [h_num_eq]
  set sAB : EuclN → ℝ := fun y => layerA y + layerB y with hsAB_def
  set sABC : EuclN → ℝ := fun y => sAB y - layerC y with hsABC_def
  set sABCD : EuclN → ℝ := fun y => sABC y + layerD y with hsABCD_def
  have hAB_mem : MemWkp (d := Module.finrank ℝ E) K 2 sAB
      (chartTargetEuclid (I := I) (M := M) α) :=
    MemWkp.add (d := Module.finrank ℝ E) (by norm_num) hΩ_open hA_mem hB_mem
  have hABC_mem : MemWkp (d := Module.finrank ℝ E) K 2 sABC
      (chartTargetEuclid (I := I) (M := M) α) :=
    MemWkp.sub (d := Module.finrank ℝ E) (by norm_num) hΩ_open hAB_mem hC_mem
  have hABCD_mem : MemWkp (d := Module.finrank ℝ E) K 2 sABCD
      (chartTargetEuclid (I := I) (M := M) α) :=
    MemWkp.add (d := Module.finrank ℝ E) (by norm_num) hΩ_open hABC_mem hD_mem
  have h_sAB_le : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 sAB
      (chartTargetEuclid (I := I) (M := M) α) ≤
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 layerA
          (chartTargetEuclid (I := I) (M := M) α)
        + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 layerB
          (chartTargetEuclid (I := I) (M := M) α) :=
    wkpNorm_add_le (d := Module.finrank ℝ E) (by norm_num) hΩ_open hA_mem hB_mem
  have h_sABC_le : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 sABC
      (chartTargetEuclid (I := I) (M := M) α) ≤
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 sAB
          (chartTargetEuclid (I := I) (M := M) α)
        + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 layerC
          (chartTargetEuclid (I := I) (M := M) α) :=
    sharp_wkpNorm_sub_le hΩ_open hAB_mem hC_mem
  have h_sABCD_le : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 sABCD
      (chartTargetEuclid (I := I) (M := M) α) ≤
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 sABC
          (chartTargetEuclid (I := I) (M := M) α)
        + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 layerD
          (chartTargetEuclid (I := I) (M := M) α) :=
    wkpNorm_add_le (d := Module.finrank ℝ E) (by norm_num) hΩ_open hABC_mem hD_mem
  have h_split : (fun y => layerA y + layerB y - layerC y + layerD y
        + layerE y) = (fun y => sABCD y + layerE y) := by
    funext y
    rw [hsABCD_def, hsABC_def, hsAB_def]
  have h_tri :
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (fun y => layerA y + layerB y - layerC y + layerD y + layerE y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 layerA
            (chartTargetEuclid (I := I) (M := M) α)
          + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 layerB
            (chartTargetEuclid (I := I) (M := M) α)
          + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 layerC
            (chartTargetEuclid (I := I) (M := M) α)
          + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 layerD
            (chartTargetEuclid (I := I) (M := M) α)
          + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 layerE
            (chartTargetEuclid (I := I) (M := M) α) := by
    rw [h_split]
    have h_outer : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
        (fun y => sABCD y + layerE y)
        (chartTargetEuclid (I := I) (M := M) α) ≤
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 sABCD
            (chartTargetEuclid (I := I) (M := M) α)
          + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 layerE
            (chartTargetEuclid (I := I) (M := M) α) :=
      wkpNorm_add_le (d := Module.finrank ℝ E) (by norm_num) hΩ_open
        hABCD_mem hE_mem
    refine le_trans h_outer ?_
    refine add_le_add ?_ (le_refl _)
    refine le_trans h_sABCD_le ?_
    refine add_le_add ?_ (le_refl _)
    refine le_trans h_sABC_le ?_
    refine add_le_add ?_ (le_refl _)
    exact h_sAB_le
  refine le_trans h_tri ?_
  have h_five :
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 layerA
          (chartTargetEuclid (I := I) (M := M) α)
        + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 layerB
          (chartTargetEuclid (I := I) (M := M) α)
        + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 layerC
          (chartTargetEuclid (I := I) (M := M) α)
        + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 layerD
          (chartTargetEuclid (I := I) (M := M) α)
        + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 layerE
          (chartTargetEuclid (I := I) (M := M) α)
      ≤ ENNReal.ofReal (CA * CatomA * (i.fst.val)⁻¹ ^ e) * Rhs +
        ENNReal.ofReal (CB * CatomB * (i.fst.val)⁻¹ ^ e) * Rhs +
        ENNReal.ofReal (CC * CatomC * (i.fst.val)⁻¹ ^ e) * Rhs +
        ENNReal.ofReal (CD * CatomD * (i.fst.val)⁻¹ ^ e) * Rhs +
        ENNReal.ofReal (CE * CatomE * (i.fst.val)⁻¹ ^ e) * Rhs :=
    add_le_add (add_le_add (add_le_add (add_le_add hCA_e hCB_e) hCC_e) hCD_e)
      hCE_e
  refine le_trans h_five ?_
  set μi : ℝ := (i.fst.val)⁻¹ ^ e with hμi_def
  have hμi_nn : 0 ≤ μi := by
    rw [hμi_def]
    have h1 : 1 ≤ (i.fst.val)⁻¹ :=
      sharp_eigen_inv_one_le (I := I) (M := M) g r s i
    have : 0 ≤ (i.fst.val)⁻¹ := le_trans zero_le_one h1
    exact pow_nonneg this _
  have h_pull :
      ENNReal.ofReal (CA * CatomA * (i.fst.val)⁻¹ ^ e) * Rhs +
        ENNReal.ofReal (CB * CatomB * (i.fst.val)⁻¹ ^ e) * Rhs +
        ENNReal.ofReal (CC * CatomC * (i.fst.val)⁻¹ ^ e) * Rhs +
        ENNReal.ofReal (CD * CatomD * (i.fst.val)⁻¹ ^ e) * Rhs +
        ENNReal.ofReal (CE * CatomE * (i.fst.val)⁻¹ ^ e) * Rhs
        = ENNReal.ofReal ((CA * CatomA + CB * CatomB + CC * CatomC +
            CD * CatomD + CE * CatomE) * (i.fst.val)⁻¹ ^ e) * Rhs := by
    have hp1 : 0 ≤ CA * CatomA + CB * CatomB := add_nonneg hCA_prod_nn hCB_prod_nn
    have hp2 : 0 ≤ CA * CatomA + CB * CatomB + CC * CatomC :=
      add_nonneg hp1 hCC_prod_nn
    have hp3 : 0 ≤ CA * CatomA + CB * CatomB + CC * CatomC + CD * CatomD :=
      add_nonneg hp2 hCD_prod_nn
    have h_sum_ofReal :
        ENNReal.ofReal (CA * CatomA * (i.fst.val)⁻¹ ^ e) +
          ENNReal.ofReal (CB * CatomB * (i.fst.val)⁻¹ ^ e) +
          ENNReal.ofReal (CC * CatomC * (i.fst.val)⁻¹ ^ e) +
          ENNReal.ofReal (CD * CatomD * (i.fst.val)⁻¹ ^ e) +
          ENNReal.ofReal (CE * CatomE * (i.fst.val)⁻¹ ^ e)
          = ENNReal.ofReal ((CA * CatomA + CB * CatomB + CC * CatomC +
              CD * CatomD + CE * CatomE) * (i.fst.val)⁻¹ ^ e) := by
      rw [add_mul, add_mul, add_mul, add_mul,
        ENNReal.ofReal_add (by positivity) (mul_nonneg hCE_prod_nn hμi_nn),
        ENNReal.ofReal_add (by positivity) (mul_nonneg hCD_prod_nn hμi_nn),
        ENNReal.ofReal_add (by positivity) (mul_nonneg hCC_prod_nn hμi_nn),
        ENNReal.ofReal_add (mul_nonneg hCA_prod_nn hμi_nn)
          (mul_nonneg hCB_prod_nn hμi_nn)]
    calc ENNReal.ofReal (CA * CatomA * (i.fst.val)⁻¹ ^ e) * Rhs +
            ENNReal.ofReal (CB * CatomB * (i.fst.val)⁻¹ ^ e) * Rhs +
            ENNReal.ofReal (CC * CatomC * (i.fst.val)⁻¹ ^ e) * Rhs +
            ENNReal.ofReal (CD * CatomD * (i.fst.val)⁻¹ ^ e) * Rhs +
            ENNReal.ofReal (CE * CatomE * (i.fst.val)⁻¹ ^ e) * Rhs
        = (ENNReal.ofReal (CA * CatomA * (i.fst.val)⁻¹ ^ e) +
            ENNReal.ofReal (CB * CatomB * (i.fst.val)⁻¹ ^ e) +
            ENNReal.ofReal (CC * CatomC * (i.fst.val)⁻¹ ^ e) +
            ENNReal.ofReal (CD * CatomD * (i.fst.val)⁻¹ ^ e) +
            ENNReal.ofReal (CE * CatomE * (i.fst.val)⁻¹ ^ e)) * Rhs := by
          rw [add_mul, add_mul, add_mul, add_mul]
      _ = ENNReal.ofReal ((CA * CatomA + CB * CatomB + CC * CatomC +
              CD * CatomD + CE * CatomE) * (i.fst.val)⁻¹ ^ e) * Rhs := by
          rw [h_sum_ofReal]
  rw [h_pull]

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
