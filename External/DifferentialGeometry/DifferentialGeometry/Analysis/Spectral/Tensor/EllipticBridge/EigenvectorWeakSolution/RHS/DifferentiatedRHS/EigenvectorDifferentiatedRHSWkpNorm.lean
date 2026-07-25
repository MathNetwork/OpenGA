import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.RHS.DifferentiatedRHS.EigenvectorDifferentiatedRHSEpNorm
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Iterated.EigenvectorIteratedData
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Multiplication.MultiplyQuantK
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

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma wkpNorm_sum_le_const_mul_aggregate
    {α : M} {K : ℕ} {ι : Type*} [Fintype ι] (F : ι → EuclN → ℝ)
    (A : ℝ≥0∞)
    (hF : ∀ j : ι, MemWkp (d := Module.finrank ℝ E) K 2 (F j)
      (chartTargetEuclid (I := I) (M := M) α))
    (hbd : ∀ j : ι, ∃ C : ℝ, 0 ≤ C ∧
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (F j)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal C * A) :
    ∃ C : ℝ, 0 ≤ C ∧
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (fun y => ∑ j : ι, F j y) (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal C * A := by
  classical
  have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  choose Cf hCf_nn hCf using hbd
  refine ⟨(∑ j : ι, Cf j) * (Fintype.card ι : ℝ),
    mul_nonneg (Finset.sum_nonneg (fun j _ => hCf_nn j)) (by positivity), ?_⟩
  have h_tri : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
      (fun y => ∑ j : ι, F j y) (chartTargetEuclid (I := I) (M := M) α)
      ≤ ∑ j : ι, iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (F j)
          (chartTargetEuclid (I := I) (M := M) α) :=
    wkpNorm_sum_le (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) h_open Finset.univ F
      (fun j _ => hF j)
  have h_step : ∑ j : ι, iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (F j)
        (chartTargetEuclid (I := I) (M := M) α)
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
    iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
        (fun y => ∑ j : ι, F j y) (chartTargetEuclid (I := I) (M := M) α)
        ≤ ∑ j : ι, iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (F j)
            (chartTargetEuclid (I := I) (M := M) α) := h_tri
    _ ≤ ∑ _j : ι, ENNReal.ofReal (∑ k : ι, Cf k) * A := h_step
    _ = (Fintype.card ι : ℝ≥0∞) *
          (ENNReal.ofReal (∑ k : ι, Cf k) * A) := h_const
    _ = ((Fintype.card ι : ℝ≥0∞) * ENNReal.ofReal (∑ k : ι, Cf k)) * A := by
        rw [mul_assoc]
    _ = ENNReal.ofReal ((∑ j : ι, Cf j) * (Fintype.card ι : ℝ)) * A := by
        rw [h_cast]

private lemma wkpNorm_sub_le
    {d : ℕ} [NeZero d] {k : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (hΩ : IsOpen Ω) {u v : EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : MemWkp (d := d) k 2 u Ω) (hv : MemWkp (d := d) k 2 v Ω) :
    iteratedWeakSobolevNorm (d := d) k 2 (fun y => u y - v y) Ω ≤
      iteratedWeakSobolevNorm (d := d) k 2 u Ω + iteratedWeakSobolevNorm (d := d) k 2 v Ω := by
  classical
  have h_fun : (fun y => u y - v y) = (fun y => u y + (fun y => - v y) y) := by
    funext y; ring
  rw [h_fun]
  have hv_neg : MemWkp (d := d) k 2 (fun y => - v y) Ω :=
    MemWkp.neg (d := d) (by norm_num) hΩ hv
  refine le_trans (wkpNorm_add_le (d := d) (by norm_num) hΩ hu hv_neg) ?_
  have h_neg_eq : iteratedWeakSobolevNorm (d := d) k 2 (fun y => - v y) Ω =
      iteratedWeakSobolevNorm (d := d) k 2 v Ω := by
    have h_smul : (fun y => - v y) = (fun y => (-1 : ℝ) * v y) := by
      funext y; ring
    rw [h_smul, wkpNorm_const_smul (d := d) (by norm_num) hΩ hv (-1)]
    simp
  rw [h_neg_eq]

section LayerBounds

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (i : TensorEigenIdx (I := I) (M := M) g r s)
  (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
  (l : Fin (m + 1) → Fin (Module.finrank ℝ E))

omit [CompleteSpace E] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in

omit [NeZero (Module.finrank ℝ E)] in
private lemma layerA_coeff_contDiffOn
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

end LayerBounds

section MainBoundUniform

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
private lemma wkpNorm_sum_le_const_mul_aggregate_uniform
    {α : M} {K : ℕ} {ι : Type*} [Fintype ι] {ν : Type*} (F : ι → ν → EuclN → ℝ)
    (A : ν → ℝ≥0∞)
    (hF : ∀ (j : ι) (n : ν), MemWkp (d := Module.finrank ℝ E) K 2 (F j n)
      (chartTargetEuclid (I := I) (M := M) α))
    (hbd : ∀ j : ι, ∃ C : ℝ, 0 ≤ C ∧
      ∀ n : ν, iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (F j n)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal C * A n) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ n : ν, iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (fun y => ∑ j : ι, F j n y) (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal C * A n := by
  classical
  have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  choose Cf hCf_nn hCf using hbd
  refine ⟨(∑ j : ι, Cf j) * (Fintype.card ι : ℝ),
    mul_nonneg (Finset.sum_nonneg (fun j _ => hCf_nn j)) (by positivity),
    fun n => ?_⟩
  have h_tri : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
      (fun y => ∑ j : ι, F j n y) (chartTargetEuclid (I := I) (M := M) α)
      ≤ ∑ j : ι, iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (F j n)
          (chartTargetEuclid (I := I) (M := M) α) :=
    wkpNorm_sum_le (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) h_open Finset.univ (fun j => F j n)
      (fun j _ => hF j n)
  have h_step : ∑ j : ι, iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (F j n)
        (chartTargetEuclid (I := I) (M := M) α)
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
    iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
        (fun y => ∑ j : ι, F j n y) (chartTargetEuclid (I := I) (M := M) α)
        ≤ ∑ j : ι, iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (F j n)
            (chartTargetEuclid (I := I) (M := M) α) := h_tri
    _ ≤ ∑ _j : ι, ENNReal.ofReal (∑ k : ι, Cf k) * A n := h_step
    _ = (Fintype.card ι : ℝ≥0∞) *
          (ENNReal.ofReal (∑ k : ι, Cf k) * A n) := h_const
    _ = ((Fintype.card ι : ℝ≥0∞) * ENNReal.ofReal (∑ k : ι, Cf k)) * A n := by
        rw [mul_assoc]
    _ = ENNReal.ofReal ((∑ j : ι, Cf j) * (Fintype.card ι : ℝ)) * A n := by
        rw [h_cast]

end MainBoundUniform

def diffNumeratorAggregateK
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (fChartEffPrev : EuclN → ℝ) : ℝ≥0∞ :=
  (∑ a : Fin (Module.finrank ℝ E),
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (2 + K) 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
        (chartTargetEuclid (I := I) (M := M) α))
    + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (2 + K) 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ m (Fin.init l))
        (chartTargetEuclid (I := I) (M := M) α)
    + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K + 1) 2 fChartEffPrev
        (chartTargetEuclid (I := I) (M := M) α)
    + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 fChartEffPrev
        (chartTargetEuclid (I := I) (M := M) α)

section AtomBoundsUnconditional

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (i : TensorEigenIdx (I := I) (M := M) g r s)
  (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
  (l : Fin (m + 1) → Fin (Module.finrank ℝ E))

omit [CompleteSpace E] in
private lemma wkpNorm_iteratedPartial_succ_le
    (a : Fin (Module.finrank ℝ E)) :
    iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
        (chartTargetEuclid (I := I) (M := M) α)
      ≤ iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (2 + K) 2
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
          (chartTargetEuclid (I := I) (M := M) α) :=
  wkpNorm_mono_order (d := Module.finrank ℝ E) (by omega) _ _

omit [CompleteSpace E] in
private lemma wkpNorm_iteratedPartial_le :
    iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ m (Fin.init l))
        (chartTargetEuclid (I := I) (M := M) α)
      ≤ iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (2 + K) 2
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ m (Fin.init l))
          (chartTargetEuclid (I := I) (M := M) α) :=
  wkpNorm_mono_order (d := Module.finrank ℝ E) (by omega) _ _

omit [CompleteSpace E] in
private lemma wkpNorm_chosenWeakPartial_iteratedPartial_succ_le
    (a b : Fin (Module.finrank ℝ E)) :
    iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
        (chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
          (chartTargetEuclid (I := I) (M := M) α))
        (chartTargetEuclid (I := I) (M := M) α)
      ≤ iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (2 + K) 2
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
          (chartTargetEuclid (I := I) (M := M) α) := by
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  refine le_trans (wkpNorm_chosenWeakPartial_le (d := Module.finrank ℝ E)
    K hΩ_open _ b) ?_
  exact wkpNorm_mono_order (d := Module.finrank ℝ E) (by omega) _ _

end AtomBoundsUnconditional

section LayerBoundsUnconditional

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (i : TensorEigenIdx (I := I) (M := M) g r s)
  (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
  (l : Fin (m + 1) → Fin (Module.finrank ℝ E))

omit [CompleteSpace E] in
private lemma eigenvectorChartRHSDiffNumerator_layerA_wkpNorm_le
    (fChartEffPrev : EuclN → ℝ)
    (h_iter : ∀ a : Fin (Module.finrank ℝ E),
      MemWkp (d := Module.finrank ℝ E) (2 + K) 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
        (chartTargetEuclid (I := I) (M := M) α)) :
    MemWkp (d := Module.finrank ℝ E) K 2
        (fun y => ∑ a : Fin (Module.finrank ℝ E),
          ∑ b : Fin (Module.finrank ℝ E),
            (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
                  (l (Fin.last m))) y)
                (EuclideanSpace.single b 1) *
              eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
        (chartTargetEuclid (I := I) (M := M) α) ∧
      ∃ C : ℝ, 0 ≤ C ∧
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y => ∑ a : Fin (Module.finrank ℝ E),
              ∑ b : Fin (Module.finrank ℝ E),
                (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
                      (l (Fin.last m))) y)
                    (EuclideanSpace.single b 1) *
                  eigenvectorChartIteratedPartial (I := I) (M := M)
                    g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal C *
            diffNumeratorAggregateK (I := I) (M := M)
              g r s i α P₀ m K l fChartEffPrev := by
  classical
  set A := diffNumeratorAggregateK (I := I) (M := M)
    g r s i α P₀ m K l fChartEffPrev with hA_def
  have h_pair : ∀ a b : Fin (Module.finrank ℝ E),
      MemWkp (d := Module.finrank ℝ E) K 2
          (fun y =>
            (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
                  (l (Fin.last m))) y)
                (EuclideanSpace.single b 1) *
              eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
          (chartTargetEuclid (I := I) (M := M) α) ∧
        ∃ C : ℝ, 0 ≤ C ∧
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (fun y =>
                (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
                      (l (Fin.last m))) y)
                    (EuclideanSpace.single b 1) *
                  eigenvectorChartIteratedPartial (I := I) (M := M)
                    g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal C * A := by
    intro a b
    have h_factor_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
        (chartTargetEuclid (I := I) (M := M) α) :=
      (h_iter a).le_of_le (by omega)
    have h_factor_ae_zero :=
      eigenvectorChartIteratedPartial_ae_zero_off_chartPouKernel
        (I := I) (M := M) g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l))
    obtain ⟨h_mem, C₀, hC₀_nn, hC₀⟩ := wkpNorm_coef_mul_factor_le
      (I := I) (M := M) α K (layerA_coeff_contDiffOn (I := I) (M := M)
        g α m l a b) h_factor_memWkp h_factor_ae_zero
    refine ⟨h_mem, C₀, hC₀_nn, le_trans hC₀ ?_⟩
    gcongr
    refine le_trans (wkpNorm_iteratedPartial_succ_le
      (I := I) (M := M) g r s i α P₀ m K l a) ?_
    rw [hA_def, diffNumeratorAggregateK]
    refine le_trans (Finset.single_le_sum (f := fun a =>
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (2 + K) 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
        (chartTargetEuclid (I := I) (M := M) α))
      (fun k _ => zero_le _) (Finset.mem_univ a)) ?_
    exact le_trans le_self_add (le_trans le_self_add le_self_add)
  have h_inner : ∀ a : Fin (Module.finrank ℝ E),
      (MemWkp (d := Module.finrank ℝ E) K 2
          (fun y => ∑ b : Fin (Module.finrank ℝ E),
            (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
                  (l (Fin.last m))) y)
                (EuclideanSpace.single b 1) *
              eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
          (chartTargetEuclid (I := I) (M := M) α)) ∧
        _ := fun a =>
    ⟨memWkp_finset_sum (I := I) (M := M)
      (α := α) (K := K) (s := Finset.univ)
      (f := fun b y =>
        (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
              (l (Fin.last m))) y)
            (EuclideanSpace.single b 1) *
          eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
      (fun b _ => (h_pair a b).1),
    wkpNorm_sum_le_const_mul_aggregate (I := I) (M := M)
      (α := α) (K := K)
      (fun b y =>
        (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
              (l (Fin.last m))) y)
            (EuclideanSpace.single b 1) *
          eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
      A (fun b => (h_pair a b).1) (fun b => (h_pair a b).2)⟩
  exact ⟨memWkp_finset_sum (I := I) (M := M)
    (α := α) (K := K) (s := Finset.univ)
    (f := fun a y => ∑ b : Fin (Module.finrank ℝ E),
      (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
            (l (Fin.last m))) y)
          (EuclideanSpace.single b 1) *
        eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
    (fun a _ => (h_inner a).1),
  wkpNorm_sum_le_const_mul_aggregate (I := I) (M := M)
    (α := α) (K := K)
    (fun a y => ∑ b : Fin (Module.finrank ℝ E),
      (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
            (l (Fin.last m))) y)
          (EuclideanSpace.single b 1) *
        eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
    A (fun a => (h_inner a).1) (fun a => (h_inner a).2)⟩

omit [CompleteSpace E] in
private lemma eigenvectorChartRHSDiffNumerator_layerB_wkpNorm_le
    (fChartEffPrev : EuclN → ℝ)
    (h_iter : ∀ a : Fin (Module.finrank ℝ E),
      MemWkp (d := Module.finrank ℝ E) (2 + K) 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
        (chartTargetEuclid (I := I) (M := M) α)) :
    MemWkp (d := Module.finrank ℝ E) K 2
        (fun y => ∑ a : Fin (Module.finrank ℝ E),
          ∑ b : Fin (Module.finrank ℝ E),
            weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
              chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
                (eigenvectorChartIteratedPartial (I := I) (M := M)
                  g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
                (chartTargetEuclid (I := I) (M := M) α) y)
        (chartTargetEuclid (I := I) (M := M) α) ∧
      ∃ C : ℝ, 0 ≤ C ∧
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y => ∑ a : Fin (Module.finrank ℝ E),
              ∑ b : Fin (Module.finrank ℝ E),
                weightedInvGramDerivOnEuclid (I := I) g α a b
                    (l (Fin.last m)) y *
                  chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
                    (eigenvectorChartIteratedPartial (I := I) (M := M)
                      g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
                    (chartTargetEuclid (I := I) (M := M) α) y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal C *
            diffNumeratorAggregateK (I := I) (M := M)
              g r s i α P₀ m K l fChartEffPrev := by
  classical
  set A := diffNumeratorAggregateK (I := I) (M := M)
    g r s i α P₀ m K l fChartEffPrev with hA_def
  have h_pair : ∀ a b : Fin (Module.finrank ℝ E),
      MemWkp (d := Module.finrank ℝ E) K 2
          (fun y =>
            weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
              chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
                (eigenvectorChartIteratedPartial (I := I) (M := M)
                  g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
                (chartTargetEuclid (I := I) (M := M) α) y)
          (chartTargetEuclid (I := I) (M := M) α) ∧
        ∃ C : ℝ, 0 ≤ C ∧
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (fun y =>
                weightedInvGramDerivOnEuclid (I := I) g α a b
                    (l (Fin.last m)) y *
                  chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
                    (eigenvectorChartIteratedPartial (I := I) (M := M)
                      g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
                    (chartTargetEuclid (I := I) (M := M) α) y)
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal C * A := by
    intro a b
    have h_inner_memWkp_succ : MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
        (chartTargetEuclid (I := I) (M := M) α) :=
      (h_iter a).le_of_le (by omega)
    have h_factor_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
        (chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
          (chartTargetEuclid (I := I) (M := M) α))
        (chartTargetEuclid (I := I) (M := M) α) :=
      h_inner_memWkp_succ.chosenWeakPartial_mem b
    have h_inner_ae :=
      eigenvectorChartIteratedPartial_ae_zero_off_chartPouKernel
        (I := I) (M := M) g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l))
    have h_factor_ae_zero :=
      chosenWeakPartial'_ae_zero_off_chartPouKernel_of_ae_zero
        (I := I) (M := M) α h_inner_ae b
    obtain ⟨h_mem, C₀, hC₀_nn, hC₀⟩ := wkpNorm_coef_mul_factor_le
      (I := I) (M := M) α K
      (weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α a b (l (Fin.last m)))
      h_factor_memWkp h_factor_ae_zero
    refine ⟨h_mem, C₀, hC₀_nn, le_trans hC₀ ?_⟩
    gcongr
    refine le_trans (wkpNorm_chosenWeakPartial_iteratedPartial_succ_le
      (I := I) (M := M) g r s i α P₀ m K l a b) ?_
    rw [hA_def, diffNumeratorAggregateK]
    refine le_trans (Finset.single_le_sum (f := fun a =>
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (2 + K) 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
        (chartTargetEuclid (I := I) (M := M) α))
      (fun k _ => zero_le _) (Finset.mem_univ a)) ?_
    exact le_trans le_self_add (le_trans le_self_add le_self_add)
  have h_inner : ∀ a : Fin (Module.finrank ℝ E),
      (MemWkp (d := Module.finrank ℝ E) K 2
          (fun y => ∑ b : Fin (Module.finrank ℝ E),
            weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
              chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
                (eigenvectorChartIteratedPartial (I := I) (M := M)
                  g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
                (chartTargetEuclid (I := I) (M := M) α) y)
          (chartTargetEuclid (I := I) (M := M) α)) ∧
        _ := fun a =>
    ⟨memWkp_finset_sum (I := I) (M := M)
      (α := α) (K := K) (s := Finset.univ)
      (f := fun b y =>
        weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
          chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
            (chartTargetEuclid (I := I) (M := M) α) y)
      (fun b _ => (h_pair a b).1),
    wkpNorm_sum_le_const_mul_aggregate (I := I) (M := M)
      (α := α) (K := K)
      (fun b y =>
        weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
          chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
            (chartTargetEuclid (I := I) (M := M) α) y)
      A (fun b => (h_pair a b).1) (fun b => (h_pair a b).2)⟩
  exact ⟨memWkp_finset_sum (I := I) (M := M)
    (α := α) (K := K) (s := Finset.univ)
    (f := fun a y => ∑ b : Fin (Module.finrank ℝ E),
      weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
        chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
          (chartTargetEuclid (I := I) (M := M) α) y)
    (fun a _ => (h_inner a).1),
  wkpNorm_sum_le_const_mul_aggregate (I := I) (M := M)
    (α := α) (K := K)
    (fun a y => ∑ b : Fin (Module.finrank ℝ E),
      weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
        chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
          (chartTargetEuclid (I := I) (M := M) α) y)
    A (fun a => (h_inner a).1) (fun a => (h_inner a).2)⟩

omit [CompleteSpace E] in
private lemma eigenvectorChartRHSDiffNumerator_layerC_wkpNorm_le
    (fChartEffPrev : EuclN → ℝ)
    (h_iter_m : MemWkp (d := Module.finrank ℝ E) (2 + K) 2
      (eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s i α P₀ m (Fin.init l))
      (chartTargetEuclid (I := I) (M := M) α)) :
    MemWkp (d := Module.finrank ℝ E) K 2
        (fun y =>
          densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
            eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s i α P₀ m (Fin.init l) y)
        (chartTargetEuclid (I := I) (M := M) α) ∧
      ∃ C : ℝ, 0 ≤ C ∧
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y =>
              densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
                eigenvectorChartIteratedPartial (I := I) (M := M)
                  g r s i α P₀ m (Fin.init l) y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal C *
            diffNumeratorAggregateK (I := I) (M := M)
              g r s i α P₀ m K l fChartEffPrev := by
  classical
  set A := diffNumeratorAggregateK (I := I) (M := M)
    g r s i α P₀ m K l fChartEffPrev with hA_def
  have h_factor_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s i α P₀ m (Fin.init l))
      (chartTargetEuclid (I := I) (M := M) α) :=
    h_iter_m.le_of_le (by omega)
  have h_factor_ae_zero :=
    eigenvectorChartIteratedPartial_ae_zero_off_chartPouKernel
      (I := I) (M := M) g r s i α P₀ m (Fin.init l)
  obtain ⟨h_mem, C₀, hC₀_nn, hC₀⟩ := wkpNorm_coef_mul_factor_le
    (I := I) (M := M) α K
    (densityDerivOnEuclid_contDiffOn (I := I) g α (l (Fin.last m)))
    h_factor_memWkp h_factor_ae_zero
  refine ⟨h_mem, C₀, hC₀_nn, le_trans hC₀ ?_⟩
  gcongr
  refine le_trans (wkpNorm_iteratedPartial_le
    (I := I) (M := M) g r s i α P₀ m K l) ?_
  rw [hA_def, diffNumeratorAggregateK]
  exact le_trans le_add_self (le_trans le_self_add le_self_add)

omit [CompleteSpace E] in
private lemma eigenvectorChartRHSDiffNumerator_layerD_wkpNorm_le
    {fChartEffPrev : EuclN → ℝ}
    (h_prev : MemWkp (d := Module.finrank ℝ E) (K + 1) 2 fChartEffPrev
      (chartTargetEuclid (I := I) (M := M) α))
    (h_prev_zero : fChartEffPrev =ᵐ[(volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α \
        chartPouKernel (I := I) (M := M) α)] (fun _ => (0 : ℝ))) :
    MemWkp (d := Module.finrank ℝ E) K 2
        (fun y =>
          densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
            fChartEffPrev y)
        (chartTargetEuclid (I := I) (M := M) α) ∧
      ∃ C : ℝ, 0 ≤ C ∧
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y =>
              densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
                fChartEffPrev y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal C *
            diffNumeratorAggregateK (I := I) (M := M)
              g r s i α P₀ m K l fChartEffPrev := by
  classical
  set A := diffNumeratorAggregateK (I := I) (M := M)
    g r s i α P₀ m K l fChartEffPrev with hA_def
  have h_factor_memWkp : MemWkp (d := Module.finrank ℝ E) K 2 fChartEffPrev
      (chartTargetEuclid (I := I) (M := M) α) :=
    h_prev.le_of_le (by omega)
  obtain ⟨h_mem, C₀, hC₀_nn, hC₀⟩ := wkpNorm_coef_mul_factor_le
    (I := I) (M := M) α K
    (densityDerivOnEuclid_contDiffOn (I := I) g α (l (Fin.last m)))
    h_factor_memWkp h_prev_zero
  refine ⟨h_mem, C₀, hC₀_nn, le_trans hC₀ ?_⟩
  gcongr
  rw [hA_def, diffNumeratorAggregateK]
  exact le_add_self

omit [CompleteSpace E] in
private lemma eigenvectorChartRHSDiffNumerator_layerE_wkpNorm_le
    {fChartEffPrev : EuclN → ℝ}
    (h_prev : MemWkp (d := Module.finrank ℝ E) (K + 1) 2 fChartEffPrev
      (chartTargetEuclid (I := I) (M := M) α))
    (h_prev_zero : fChartEffPrev =ᵐ[(volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α \
        chartPouKernel (I := I) (M := M) α)] (fun _ => (0 : ℝ))) :
    MemWkp (d := Module.finrank ℝ E) K 2
        (fun y =>
          densityOnEuclid (I := I) g α y *
            chosenWeakPartial' (d := Module.finrank ℝ E) 2 (l (Fin.last m))
              fChartEffPrev (chartTargetEuclid (I := I) (M := M) α) y)
        (chartTargetEuclid (I := I) (M := M) α) ∧
      ∃ C : ℝ, 0 ≤ C ∧
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y =>
              densityOnEuclid (I := I) g α y *
                chosenWeakPartial' (d := Module.finrank ℝ E) 2 (l (Fin.last m))
                  fChartEffPrev (chartTargetEuclid (I := I) (M := M) α) y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal C *
            diffNumeratorAggregateK (I := I) (M := M)
              g r s i α P₀ m K l fChartEffPrev := by
  classical
  set A := diffNumeratorAggregateK (I := I) (M := M)
    g r s i α P₀ m K l fChartEffPrev with hA_def
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_factor_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (chosenWeakPartial' (d := Module.finrank ℝ E) 2 (l (Fin.last m))
        fChartEffPrev (chartTargetEuclid (I := I) (M := M) α))
      (chartTargetEuclid (I := I) (M := M) α) :=
    h_prev.chosenWeakPartial_mem (l (Fin.last m))
  have h_factor_ae_zero :=
    chosenWeakPartial'_ae_zero_off_chartPouKernel_of_ae_zero
      (I := I) (M := M) α h_prev_zero (l (Fin.last m))
  obtain ⟨h_mem, C₀, hC₀_nn, hC₀⟩ := wkpNorm_coef_mul_factor_le
    (I := I) (M := M) α K
    (densityOnEuclid_contDiffOn (I := I) g α)
    h_factor_memWkp h_factor_ae_zero
  refine ⟨h_mem, C₀, hC₀_nn, le_trans hC₀ ?_⟩
  gcongr
  refine le_trans (wkpNorm_chosenWeakPartial_le (d := Module.finrank ℝ E)
    K hΩ_open _ (l (Fin.last m))) ?_
  rw [hA_def, diffNumeratorAggregateK]
  exact le_trans le_add_self le_self_add

end LayerBoundsUnconditional

section MainBoundUnconditional

omit [CompleteSpace E] in
theorem eigenvectorChartRHSDiffNumerator_wkpNorm_le
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
          (eigenvectorChartRHSDiffNumerator (I := I) (M := M)
            g r s i α P₀ m l fChartEffPrev)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal C *
          diffNumeratorAggregateK (I := I) (M := M)
            g r s i α P₀ m K l fChartEffPrev := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  set A := diffNumeratorAggregateK (I := I) (M := M)
    g r s i α P₀ m K l fChartEffPrev with hA_def
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
        chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
          (chartTargetEuclid (I := I) (M := M) α) y with hlayerB_def
  set layerC : EuclN → ℝ := fun y =>
    densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
      eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s i α P₀ m (Fin.init l) y with hlayerC_def
  set layerD : EuclN → ℝ := fun y =>
    densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
      fChartEffPrev y with hlayerD_def
  set layerE : EuclN → ℝ := fun y =>
    densityOnEuclid (I := I) g α y *
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 (l (Fin.last m))
        fChartEffPrev (chartTargetEuclid (I := I) (M := M) α) y
    with hlayerE_def
  have h_num_eq : eigenvectorChartRHSDiffNumerator (I := I) (M := M)
      g r s i α P₀ m l fChartEffPrev =
      fun y => layerA y + layerB y - layerC y + layerD y + layerE y := by
    funext y
    rw [eigenvectorChartRHSDiffNumerator]
  obtain ⟨hA_mem, CA, hCA_nn, hCA⟩ :=
    eigenvectorChartRHSDiffNumerator_layerA_wkpNorm_le
      (I := I) (M := M) g r s i α P₀ m K l fChartEffPrev
      (fun a => h_iter (m + 1) (Fin.cons a (Fin.init l)))
  obtain ⟨hB_mem, CB, hCB_nn, hCB⟩ :=
    eigenvectorChartRHSDiffNumerator_layerB_wkpNorm_le
      (I := I) (M := M) g r s i α P₀ m K l fChartEffPrev
      (fun a => h_iter (m + 1) (Fin.cons a (Fin.init l)))
  obtain ⟨hC_mem, CC, hCC_nn, hCC⟩ :=
    eigenvectorChartRHSDiffNumerator_layerC_wkpNorm_le
      (I := I) (M := M) g r s i α P₀ m K l fChartEffPrev
      (h_iter m (Fin.init l))
  obtain ⟨hD_mem, CD, hCD_nn, hCD⟩ :=
    eigenvectorChartRHSDiffNumerator_layerD_wkpNorm_le
      (I := I) (M := M) g r s i α P₀ m K l h_prev h_prev_zero
  obtain ⟨hE_mem, CE, hCE_nn, hCE⟩ :=
    eigenvectorChartRHSDiffNumerator_layerE_wkpNorm_le
      (I := I) (M := M) g r s i α P₀ m K l h_prev h_prev_zero
  rw [← hΩ_def, ← hA_def] at hCA hCB hCC hCD hCE
  rw [← hΩ_def] at hA_mem hB_mem hC_mem hD_mem hE_mem
  refine ⟨CA + CB + CC + CD + CE, by positivity, ?_⟩
  rw [h_num_eq]
  set sAB : EuclN → ℝ := fun y => layerA y + layerB y with hsAB_def
  set sABC : EuclN → ℝ := fun y => sAB y - layerC y with hsABC_def
  set sABCD : EuclN → ℝ := fun y => sABC y + layerD y with hsABCD_def
  have hAB_mem : MemWkp (d := Module.finrank ℝ E) K 2 sAB Ω :=
    MemWkp.add (d := Module.finrank ℝ E) (by norm_num) hΩ_open hA_mem hB_mem
  have hABC_mem : MemWkp (d := Module.finrank ℝ E) K 2 sABC Ω :=
    MemWkp.sub (d := Module.finrank ℝ E) (by norm_num) hΩ_open hAB_mem hC_mem
  have hABCD_mem : MemWkp (d := Module.finrank ℝ E) K 2 sABCD Ω :=
    MemWkp.add (d := Module.finrank ℝ E) (by norm_num) hΩ_open hABC_mem hD_mem
  have h_sAB_le : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 sAB Ω ≤
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 layerA Ω
        + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 layerB Ω :=
    wkpNorm_add_le (d := Module.finrank ℝ E) (by norm_num) hΩ_open hA_mem hB_mem
  have h_sABC_le : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 sABC Ω ≤
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 sAB Ω
        + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 layerC Ω :=
    wkpNorm_sub_le (d := Module.finrank ℝ E) hΩ_open hAB_mem hC_mem
  have h_sABCD_le : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 sABCD Ω ≤
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 sABC Ω
        + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 layerD Ω :=
    wkpNorm_add_le (d := Module.finrank ℝ E) (by norm_num) hΩ_open hABC_mem hD_mem
  have h_split : (fun y => layerA y + layerB y - layerC y + layerD y
        + layerE y) = (fun y => sABCD y + layerE y) := by
    funext y
    rw [hsABCD_def, hsABC_def, hsAB_def]
  have h_tri :
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (fun y => layerA y + layerB y - layerC y + layerD y + layerE y) Ω
        ≤ iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 layerA Ω
          + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 layerB Ω
          + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 layerC Ω
          + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 layerD Ω
          + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 layerE Ω := by
    rw [h_split]
    have h_outer : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
        (fun y => sABCD y + layerE y) Ω ≤
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 sABCD Ω
          + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 layerE Ω :=
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
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 layerA Ω
        + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 layerB Ω
        + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 layerC Ω
        + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 layerD Ω
        + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 layerE Ω
      ≤ ENNReal.ofReal CA * A + ENNReal.ofReal CB * A + ENNReal.ofReal CC * A
        + ENNReal.ofReal CD * A + ENNReal.ofReal CE * A :=
    add_le_add (add_le_add (add_le_add (add_le_add hCA hCB) hCC) hCD) hCE
  refine le_trans h_five ?_
  rw [ENNReal.ofReal_add (by positivity) hCE_nn,
    ENNReal.ofReal_add (by positivity) hCD_nn,
    ENNReal.ofReal_add (by positivity) hCC_nn,
    ENNReal.ofReal_add hCA_nn hCB_nn]
  rw [add_mul, add_mul, add_mul, add_mul]

end MainBoundUnconditional

section MainBoundUniformUnconditional

omit [CompleteSpace E] in
private lemma eigenvectorChartRHSDiffNumerator_layerA_wkpNorm_le_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (fChartEffPrev : TensorEigenIdx (I := I) (M := M) g r s → EuclN → ℝ)
    (h_iter : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
        (a : Fin (Module.finrank ℝ E)),
      MemWkp (d := Module.finrank ℝ E) (2 + K) 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
        (chartTargetEuclid (I := I) (M := M) α)) :
    (∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        MemWkp (d := Module.finrank ℝ E) K 2
          (fun y => ∑ a : Fin (Module.finrank ℝ E),
            ∑ b : Fin (Module.finrank ℝ E),
              (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
                    (l (Fin.last m))) y)
                  (EuclideanSpace.single b 1) *
                eigenvectorChartIteratedPartial (I := I) (M := M)
                  g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
          (chartTargetEuclid (I := I) (M := M) α)) ∧
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
            ≤ ENNReal.ofReal C *
              diffNumeratorAggregateK (I := I) (M := M)
                g r s i α P₀ m K l (fChartEffPrev i) := by
  classical
  have h_pair : ∀ a b : Fin (Module.finrank ℝ E),
      (∀ i : TensorEigenIdx (I := I) (M := M) g r s,
          MemWkp (d := Module.finrank ℝ E) K 2
            (fun y =>
              (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
                    (l (Fin.last m))) y)
                  (EuclideanSpace.single b 1) *
                eigenvectorChartIteratedPartial (I := I) (M := M)
                  g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
            (chartTargetEuclid (I := I) (M := M) α)) ∧
        ∃ C : ℝ, 0 ≤ C ∧
          ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
                (fun y =>
                  (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
                        (l (Fin.last m))) y)
                      (EuclideanSpace.single b 1) *
                    eigenvectorChartIteratedPartial (I := I) (M := M)
                      g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
                (chartTargetEuclid (I := I) (M := M) α)
              ≤ ENNReal.ofReal C *
                diffNumeratorAggregateK (I := I) (M := M)
                  g r s i α P₀ m K l (fChartEffPrev i) := by
    intro a b
    obtain ⟨C₀, hC₀_nn, hC₀⟩ := wkpNorm_coef_mul_factor_le_uniform
      (I := I) (M := M) α K
      (layerA_coeff_contDiffOn (I := I) (M := M) g α m l a b)
    refine ⟨fun i => ?_, C₀, hC₀_nn, fun i => ?_⟩
    · exact (hC₀ _
        ((h_iter i a).le_of_le (by omega))
        (eigenvectorChartIteratedPartial_ae_zero_off_chartPouKernel
          (I := I) (M := M) g r s i α P₀ (m + 1)
          (Fin.cons a (Fin.init l)))).1
    · refine le_trans ((hC₀ _
        ((h_iter i a).le_of_le (by omega))
        (eigenvectorChartIteratedPartial_ae_zero_off_chartPouKernel
          (I := I) (M := M) g r s i α P₀ (m + 1)
          (Fin.cons a (Fin.init l)))).2) ?_
      gcongr
      refine le_trans (wkpNorm_iteratedPartial_succ_le
        (I := I) (M := M) g r s i α P₀ m K l a) ?_
      rw [diffNumeratorAggregateK]
      refine le_trans (Finset.single_le_sum (f := fun a =>
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (2 + K) 2
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
          (chartTargetEuclid (I := I) (M := M) α))
        (fun k _ => zero_le _) (Finset.mem_univ a)) ?_
      exact le_trans le_self_add (le_trans le_self_add le_self_add)
  have h_inner : ∀ a : Fin (Module.finrank ℝ E),
      (∀ i : TensorEigenIdx (I := I) (M := M) g r s,
          MemWkp (d := Module.finrank ℝ E) K 2
            (fun y => ∑ b : Fin (Module.finrank ℝ E),
              (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
                    (l (Fin.last m))) y)
                  (EuclideanSpace.single b 1) *
                eigenvectorChartIteratedPartial (I := I) (M := M)
                  g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
            (chartTargetEuclid (I := I) (M := M) α)) ∧
        ∃ C : ℝ, 0 ≤ C ∧ ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (fun y => ∑ b : Fin (Module.finrank ℝ E),
                (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
                      (l (Fin.last m))) y)
                    (EuclideanSpace.single b 1) *
                  eigenvectorChartIteratedPartial (I := I) (M := M)
                    g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal C *
              diffNumeratorAggregateK (I := I) (M := M)
                g r s i α P₀ m K l (fChartEffPrev i) := fun a =>
    ⟨fun i => memWkp_finset_sum (I := I) (M := M)
      (α := α) (K := K) (s := Finset.univ)
      (f := fun b y =>
        (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
              (l (Fin.last m))) y)
            (EuclideanSpace.single b 1) *
          eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
      (fun b _ => (h_pair a b).1 i),
    wkpNorm_sum_le_const_mul_aggregate_uniform (I := I) (M := M)
      (α := α) (K := K) (ι := Fin (Module.finrank ℝ E))
      (ν := TensorEigenIdx (I := I) (M := M) g r s)
      (fun b => fun i => fun y =>
        (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
              (l (Fin.last m))) y)
            (EuclideanSpace.single b 1) *
          eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
      (fun i => diffNumeratorAggregateK (I := I) (M := M)
        g r s i α P₀ m K l (fChartEffPrev i))
      (fun b i => (h_pair a b).1 i) (fun b => (h_pair a b).2)⟩
  exact ⟨fun i => memWkp_finset_sum (I := I) (M := M)
    (α := α) (K := K) (s := Finset.univ)
    (f := fun a y => ∑ b : Fin (Module.finrank ℝ E),
      (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
            (l (Fin.last m))) y)
          (EuclideanSpace.single b 1) *
        eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
    (fun a _ => (h_inner a).1 i),
  wkpNorm_sum_le_const_mul_aggregate_uniform (I := I) (M := M)
    (α := α) (K := K) (ι := Fin (Module.finrank ℝ E))
    (ν := TensorEigenIdx (I := I) (M := M) g r s)
    (fun a => fun i => fun y => ∑ b : Fin (Module.finrank ℝ E),
      (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
            (l (Fin.last m))) y)
          (EuclideanSpace.single b 1) *
        eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
    (fun i => diffNumeratorAggregateK (I := I) (M := M)
      g r s i α P₀ m K l (fChartEffPrev i))
    (fun a i => (h_inner a).1 i) (fun a => (h_inner a).2)⟩

omit [CompleteSpace E] in
private lemma eigenvectorChartRHSDiffNumerator_layerB_wkpNorm_le_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (fChartEffPrev : TensorEigenIdx (I := I) (M := M) g r s → EuclN → ℝ)
    (h_iter : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
        (a : Fin (Module.finrank ℝ E)),
      MemWkp (d := Module.finrank ℝ E) (2 + K) 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
        (chartTargetEuclid (I := I) (M := M) α)) :
    (∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        MemWkp (d := Module.finrank ℝ E) K 2
          (fun y => ∑ a : Fin (Module.finrank ℝ E),
            ∑ b : Fin (Module.finrank ℝ E),
              weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
                chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
                  (eigenvectorChartIteratedPartial (I := I) (M := M)
                    g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
                  (chartTargetEuclid (I := I) (M := M) α) y)
          (chartTargetEuclid (I := I) (M := M) α)) ∧
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (fun y => ∑ a : Fin (Module.finrank ℝ E),
                ∑ b : Fin (Module.finrank ℝ E),
                  weightedInvGramDerivOnEuclid (I := I) g α a b
                      (l (Fin.last m)) y *
                    chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
                      (eigenvectorChartIteratedPartial (I := I) (M := M)
                        g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
                      (chartTargetEuclid (I := I) (M := M) α) y)
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal C *
              diffNumeratorAggregateK (I := I) (M := M)
                g r s i α P₀ m K l (fChartEffPrev i) := by
  classical
  have h_pair : ∀ a b : Fin (Module.finrank ℝ E),
      (∀ i : TensorEigenIdx (I := I) (M := M) g r s,
          MemWkp (d := Module.finrank ℝ E) K 2
            (fun y =>
              weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
                chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
                  (eigenvectorChartIteratedPartial (I := I) (M := M)
                    g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
                  (chartTargetEuclid (I := I) (M := M) α) y)
            (chartTargetEuclid (I := I) (M := M) α)) ∧
        ∃ C : ℝ, 0 ≤ C ∧
          ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
                (fun y =>
                  weightedInvGramDerivOnEuclid (I := I) g α a b
                      (l (Fin.last m)) y *
                    chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
                      (eigenvectorChartIteratedPartial (I := I) (M := M)
                        g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
                      (chartTargetEuclid (I := I) (M := M) α) y)
                (chartTargetEuclid (I := I) (M := M) α)
              ≤ ENNReal.ofReal C *
                diffNumeratorAggregateK (I := I) (M := M)
                  g r s i α P₀ m K l (fChartEffPrev i) := by
    intro a b
    obtain ⟨C₀, hC₀_nn, hC₀⟩ := wkpNorm_coef_mul_factor_le_uniform
      (I := I) (M := M) α K
      (weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α a b (l (Fin.last m)))
    have h_factor : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        MemWkp (d := Module.finrank ℝ E) K 2
            (chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
              (eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
              (chartTargetEuclid (I := I) (M := M) α))
            (chartTargetEuclid (I := I) (M := M) α) ∧
          chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
              (eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
              (chartTargetEuclid (I := I) (M := M) α)
            =ᵐ[(volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α \
                chartPouKernel (I := I) (M := M) α)] (fun _ => (0 : ℝ)) := by
      intro i
      refine ⟨((h_iter i a).le_of_le (by omega)).chosenWeakPartial_mem b, ?_⟩
      exact chosenWeakPartial'_ae_zero_off_chartPouKernel_of_ae_zero
        (I := I) (M := M) α
        (eigenvectorChartIteratedPartial_ae_zero_off_chartPouKernel
          (I := I) (M := M) g r s i α P₀ (m + 1)
          (Fin.cons a (Fin.init l))) b
    refine ⟨fun i => (hC₀ _ (h_factor i).1 (h_factor i).2).1,
      C₀, hC₀_nn, fun i => ?_⟩
    refine le_trans ((hC₀ _ (h_factor i).1 (h_factor i).2).2) ?_
    gcongr
    refine le_trans (wkpNorm_chosenWeakPartial_iteratedPartial_succ_le
      (I := I) (M := M) g r s i α P₀ m K l a b) ?_
    rw [diffNumeratorAggregateK]
    refine le_trans (Finset.single_le_sum (f := fun a =>
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (2 + K) 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
        (chartTargetEuclid (I := I) (M := M) α))
      (fun k _ => zero_le _) (Finset.mem_univ a)) ?_
    exact le_trans le_self_add (le_trans le_self_add le_self_add)
  have h_inner : ∀ a : Fin (Module.finrank ℝ E),
      (∀ i : TensorEigenIdx (I := I) (M := M) g r s,
          MemWkp (d := Module.finrank ℝ E) K 2
            (fun y => ∑ b : Fin (Module.finrank ℝ E),
              weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
                chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
                  (eigenvectorChartIteratedPartial (I := I) (M := M)
                    g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
                  (chartTargetEuclid (I := I) (M := M) α) y)
            (chartTargetEuclid (I := I) (M := M) α)) ∧
        ∃ C : ℝ, 0 ≤ C ∧ ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (fun y => ∑ b : Fin (Module.finrank ℝ E),
                weightedInvGramDerivOnEuclid (I := I) g α a b
                    (l (Fin.last m)) y *
                  chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
                    (eigenvectorChartIteratedPartial (I := I) (M := M)
                      g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
                    (chartTargetEuclid (I := I) (M := M) α) y)
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal C *
              diffNumeratorAggregateK (I := I) (M := M)
                g r s i α P₀ m K l (fChartEffPrev i) := fun a =>
    ⟨fun i => memWkp_finset_sum (I := I) (M := M)
      (α := α) (K := K) (s := Finset.univ)
      (f := fun b y =>
        weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
          chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
            (chartTargetEuclid (I := I) (M := M) α) y)
      (fun b _ => (h_pair a b).1 i),
    wkpNorm_sum_le_const_mul_aggregate_uniform (I := I) (M := M)
      (α := α) (K := K) (ι := Fin (Module.finrank ℝ E))
      (ν := TensorEigenIdx (I := I) (M := M) g r s)
      (fun b => fun i => fun y =>
        weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
          chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
            (chartTargetEuclid (I := I) (M := M) α) y)
      (fun i => diffNumeratorAggregateK (I := I) (M := M)
        g r s i α P₀ m K l (fChartEffPrev i))
      (fun b i => (h_pair a b).1 i) (fun b => (h_pair a b).2)⟩
  exact ⟨fun i => memWkp_finset_sum (I := I) (M := M)
    (α := α) (K := K) (s := Finset.univ)
    (f := fun a y => ∑ b : Fin (Module.finrank ℝ E),
      weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
        chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
          (chartTargetEuclid (I := I) (M := M) α) y)
    (fun a _ => (h_inner a).1 i),
  wkpNorm_sum_le_const_mul_aggregate_uniform (I := I) (M := M)
    (α := α) (K := K) (ι := Fin (Module.finrank ℝ E))
    (ν := TensorEigenIdx (I := I) (M := M) g r s)
    (fun a => fun i => fun y => ∑ b : Fin (Module.finrank ℝ E),
      weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
        chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
          (chartTargetEuclid (I := I) (M := M) α) y)
    (fun i => diffNumeratorAggregateK (I := I) (M := M)
      g r s i α P₀ m K l (fChartEffPrev i))
    (fun a i => (h_inner a).1 i) (fun a => (h_inner a).2)⟩

omit [CompleteSpace E] in
private lemma eigenvectorChartRHSDiffNumerator_layerC_wkpNorm_le_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (fChartEffPrev : TensorEigenIdx (I := I) (M := M) g r s → EuclN → ℝ)
    (h_iter_m : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      MemWkp (d := Module.finrank ℝ E) (2 + K) 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ m (Fin.init l))
        (chartTargetEuclid (I := I) (M := M) α)) :
    (∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        MemWkp (d := Module.finrank ℝ E) K 2
          (fun y =>
            densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
              eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s i α P₀ m (Fin.init l) y)
          (chartTargetEuclid (I := I) (M := M) α)) ∧
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (fun y =>
                densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
                  eigenvectorChartIteratedPartial (I := I) (M := M)
                    g r s i α P₀ m (Fin.init l) y)
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal C *
              diffNumeratorAggregateK (I := I) (M := M)
                g r s i α P₀ m K l (fChartEffPrev i) := by
  classical
  obtain ⟨C₀, hC₀_nn, hC₀⟩ := wkpNorm_coef_mul_factor_le_uniform
    (I := I) (M := M) α K
    (densityDerivOnEuclid_contDiffOn (I := I) g α (l (Fin.last m)))
  have h_factor : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      MemWkp (d := Module.finrank ℝ E) K 2
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ m (Fin.init l))
          (chartTargetEuclid (I := I) (M := M) α) ∧
        eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ m (Fin.init l)
          =ᵐ[(volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α \
              chartPouKernel (I := I) (M := M) α)] (fun _ => (0 : ℝ)) := by
    intro i
    exact ⟨(h_iter_m i).le_of_le (by omega),
      eigenvectorChartIteratedPartial_ae_zero_off_chartPouKernel
        (I := I) (M := M) g r s i α P₀ m (Fin.init l)⟩
  refine ⟨fun i => (hC₀ _ (h_factor i).1 (h_factor i).2).1,
    C₀, hC₀_nn, fun i => ?_⟩
  refine le_trans ((hC₀ _ (h_factor i).1 (h_factor i).2).2) ?_
  gcongr
  refine le_trans (wkpNorm_iteratedPartial_le
    (I := I) (M := M) g r s i α P₀ m K l) ?_
  rw [diffNumeratorAggregateK]
  exact le_trans le_add_self (le_trans le_self_add le_self_add)

omit [CompleteSpace E] in
private lemma eigenvectorChartRHSDiffNumerator_layerD_wkpNorm_le_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (fChartEffPrev : TensorEigenIdx (I := I) (M := M) g r s → EuclN → ℝ)
    (h_prev : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2 (fChartEffPrev i)
        (chartTargetEuclid (I := I) (M := M) α))
    (h_prev_zero : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      (fChartEffPrev i) =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α)] (fun _ => (0 : ℝ))) :
    (∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        MemWkp (d := Module.finrank ℝ E) K 2
          (fun y =>
            densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
              fChartEffPrev i y)
          (chartTargetEuclid (I := I) (M := M) α)) ∧
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (fun y =>
                densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
                  fChartEffPrev i y)
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal C *
              diffNumeratorAggregateK (I := I) (M := M)
                g r s i α P₀ m K l (fChartEffPrev i) := by
  classical
  obtain ⟨C₀, hC₀_nn, hC₀⟩ := wkpNorm_coef_mul_factor_le_uniform
    (I := I) (M := M) α K
    (densityDerivOnEuclid_contDiffOn (I := I) g α (l (Fin.last m)))
  have h_factor : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      MemWkp (d := Module.finrank ℝ E) K 2 (fChartEffPrev i)
        (chartTargetEuclid (I := I) (M := M) α) := fun i =>
    (h_prev i).le_of_le (by omega)
  refine ⟨fun i => (hC₀ _ (h_factor i) (h_prev_zero i)).1,
    C₀, hC₀_nn, fun i => ?_⟩
  refine le_trans ((hC₀ _ (h_factor i) (h_prev_zero i)).2) ?_
  gcongr
  rw [diffNumeratorAggregateK]
  exact le_add_self

omit [CompleteSpace E] in
private lemma eigenvectorChartRHSDiffNumerator_layerE_wkpNorm_le_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (fChartEffPrev : TensorEigenIdx (I := I) (M := M) g r s → EuclN → ℝ)
    (h_prev : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2 (fChartEffPrev i)
        (chartTargetEuclid (I := I) (M := M) α))
    (h_prev_zero : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      (fChartEffPrev i) =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α)] (fun _ => (0 : ℝ))) :
    (∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        MemWkp (d := Module.finrank ℝ E) K 2
          (fun y =>
            densityOnEuclid (I := I) g α y *
              chosenWeakPartial' (d := Module.finrank ℝ E) 2 (l (Fin.last m))
                (fChartEffPrev i) (chartTargetEuclid (I := I) (M := M) α) y)
          (chartTargetEuclid (I := I) (M := M) α)) ∧
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (fun y =>
                densityOnEuclid (I := I) g α y *
                  chosenWeakPartial' (d := Module.finrank ℝ E) 2 (l (Fin.last m))
                    (fChartEffPrev i) (chartTargetEuclid (I := I) (M := M) α) y)
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal C *
              diffNumeratorAggregateK (I := I) (M := M)
                g r s i α P₀ m K l (fChartEffPrev i) := by
  classical
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  obtain ⟨C₀, hC₀_nn, hC₀⟩ := wkpNorm_coef_mul_factor_le_uniform
    (I := I) (M := M) α K
    (densityOnEuclid_contDiffOn (I := I) g α)
  have h_factor : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      MemWkp (d := Module.finrank ℝ E) K 2
          (chosenWeakPartial' (d := Module.finrank ℝ E) 2 (l (Fin.last m))
            (fChartEffPrev i) (chartTargetEuclid (I := I) (M := M) α))
          (chartTargetEuclid (I := I) (M := M) α) ∧
        chosenWeakPartial' (d := Module.finrank ℝ E) 2 (l (Fin.last m))
            (fChartEffPrev i) (chartTargetEuclid (I := I) (M := M) α)
          =ᵐ[(volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α \
              chartPouKernel (I := I) (M := M) α)] (fun _ => (0 : ℝ)) := by
    intro i
    refine ⟨(h_prev i).chosenWeakPartial_mem (l (Fin.last m)), ?_⟩
    exact chosenWeakPartial'_ae_zero_off_chartPouKernel_of_ae_zero
      (I := I) (M := M) α (h_prev_zero i) (l (Fin.last m))
  refine ⟨fun i => (hC₀ _ (h_factor i).1 (h_factor i).2).1,
    C₀, hC₀_nn, fun i => ?_⟩
  refine le_trans ((hC₀ _ (h_factor i).1 (h_factor i).2).2) ?_
  gcongr
  refine le_trans (wkpNorm_chosenWeakPartial_le (d := Module.finrank ℝ E)
    K hΩ_open _ (l (Fin.last m))) ?_
  rw [diffNumeratorAggregateK]
  exact le_trans le_add_self le_self_add

omit [CompleteSpace E] in
theorem eigenvectorChartRHSDiffNumerator_wkpNorm_le_uniform
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
            (eigenvectorChartRHSDiffNumerator (I := I) (M := M)
              g r s i α P₀ m l (fChartEffPrev i))
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal C *
            diffNumeratorAggregateK (I := I) (M := M)
              g r s i α P₀ m K l (fChartEffPrev i) := by
  classical
  obtain ⟨hA_mem, CA, hCA_nn, hCA⟩ :=
    eigenvectorChartRHSDiffNumerator_layerA_wkpNorm_le_uniform
      (I := I) (M := M) g r s α P₀ m K l fChartEffPrev
      (fun i a => h_iter i (m + 1) (Fin.cons a (Fin.init l)))
  obtain ⟨hB_mem, CB, hCB_nn, hCB⟩ :=
    eigenvectorChartRHSDiffNumerator_layerB_wkpNorm_le_uniform
      (I := I) (M := M) g r s α P₀ m K l fChartEffPrev
      (fun i a => h_iter i (m + 1) (Fin.cons a (Fin.init l)))
  obtain ⟨hC_mem, CC, hCC_nn, hCC⟩ :=
    eigenvectorChartRHSDiffNumerator_layerC_wkpNorm_le_uniform
      (I := I) (M := M) g r s α P₀ m K l fChartEffPrev
      (fun i => h_iter i m (Fin.init l))
  obtain ⟨hD_mem, CD, hCD_nn, hCD⟩ :=
    eigenvectorChartRHSDiffNumerator_layerD_wkpNorm_le_uniform
      (I := I) (M := M) g r s α P₀ m K l fChartEffPrev h_prev h_prev_zero
  obtain ⟨hE_mem, CE, hCE_nn, hCE⟩ :=
    eigenvectorChartRHSDiffNumerator_layerE_wkpNorm_le_uniform
      (I := I) (M := M) g r s α P₀ m K l fChartEffPrev h_prev h_prev_zero
  refine ⟨CA + CB + CC + CD + CE, by positivity, fun i => ?_⟩
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  set A := diffNumeratorAggregateK (I := I) (M := M)
    g r s i α P₀ m K l (fChartEffPrev i) with hA_def
  set layerA : EuclN → ℝ := fun y => ∑ a : Fin (Module.finrank ℝ E),
    ∑ b : Fin (Module.finrank ℝ E),
      (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
            (l (Fin.last m))) y)
          (EuclideanSpace.single b 1) *
        eigenvectorChartIteratedPartial (I := I) (M := M) g r s i α P₀
          (m + 1) (Fin.cons a (Fin.init l)) y with hlayerA_def
  set layerB : EuclN → ℝ := fun y => ∑ a : Fin (Module.finrank ℝ E),
    ∑ b : Fin (Module.finrank ℝ E),
      weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
        chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
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
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 (l (Fin.last m))
        (fChartEffPrev i) (chartTargetEuclid (I := I) (M := M) α) y
    with hlayerE_def
  have h_num_eq : eigenvectorChartRHSDiffNumerator (I := I) (M := M)
      g r s i α P₀ m l (fChartEffPrev i) =
      fun y => layerA y + layerB y - layerC y + layerD y + layerE y := by
    funext y
    rw [eigenvectorChartRHSDiffNumerator]
  have hA_mem_i := hA_mem i
  have hB_mem_i := hB_mem i
  have hC_mem_i := hC_mem i
  have hD_mem_i := hD_mem i
  have hE_mem_i := hE_mem i
  have hCA_i := hCA i
  have hCB_i := hCB i
  have hCC_i := hCC i
  have hCD_i := hCD i
  have hCE_i := hCE i
  rw [← hA_def] at hCA_i hCB_i hCC_i hCD_i hCE_i
  rw [← hlayerA_def] at hA_mem_i hCA_i
  rw [← hlayerB_def] at hB_mem_i hCB_i
  rw [← hlayerC_def] at hC_mem_i hCC_i
  rw [← hlayerD_def] at hD_mem_i hCD_i
  rw [← hlayerE_def] at hE_mem_i hCE_i
  rw [h_num_eq]
  set sAB : EuclN → ℝ := fun y => layerA y + layerB y with hsAB_def
  set sABC : EuclN → ℝ := fun y => sAB y - layerC y with hsABC_def
  set sABCD : EuclN → ℝ := fun y => sABC y + layerD y with hsABCD_def
  have hAB_mem : MemWkp (d := Module.finrank ℝ E) K 2 sAB Ω :=
    MemWkp.add (d := Module.finrank ℝ E) (by norm_num) hΩ_open hA_mem_i hB_mem_i
  have hABC_mem : MemWkp (d := Module.finrank ℝ E) K 2 sABC Ω :=
    MemWkp.sub (d := Module.finrank ℝ E) (by norm_num) hΩ_open hAB_mem hC_mem_i
  have hABCD_mem : MemWkp (d := Module.finrank ℝ E) K 2 sABCD Ω :=
    MemWkp.add (d := Module.finrank ℝ E) (by norm_num) hΩ_open hABC_mem hD_mem_i
  have h_sAB_le : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 sAB Ω ≤
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 layerA Ω
        + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 layerB Ω :=
    wkpNorm_add_le (d := Module.finrank ℝ E) (by norm_num) hΩ_open
      hA_mem_i hB_mem_i
  have h_sABC_le : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 sABC Ω ≤
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 sAB Ω
        + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 layerC Ω :=
    wkpNorm_sub_le (d := Module.finrank ℝ E) hΩ_open hAB_mem hC_mem_i
  have h_sABCD_le : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 sABCD Ω ≤
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 sABC Ω
        + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 layerD Ω :=
    wkpNorm_add_le (d := Module.finrank ℝ E) (by norm_num) hΩ_open
      hABC_mem hD_mem_i
  have h_split : (fun y => layerA y + layerB y - layerC y + layerD y
        + layerE y) = (fun y => sABCD y + layerE y) := by
    funext y
    rw [hsABCD_def, hsABC_def, hsAB_def]
  have h_tri :
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (fun y => layerA y + layerB y - layerC y + layerD y + layerE y) Ω
        ≤ iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 layerA Ω
          + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 layerB Ω
          + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 layerC Ω
          + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 layerD Ω
          + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 layerE Ω := by
    rw [h_split]
    have h_outer : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
        (fun y => sABCD y + layerE y) Ω ≤
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 sABCD Ω
          + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 layerE Ω :=
      wkpNorm_add_le (d := Module.finrank ℝ E) (by norm_num) hΩ_open
        hABCD_mem hE_mem_i
    refine le_trans h_outer ?_
    refine add_le_add ?_ (le_refl _)
    refine le_trans h_sABCD_le ?_
    refine add_le_add ?_ (le_refl _)
    refine le_trans h_sABC_le ?_
    refine add_le_add ?_ (le_refl _)
    exact h_sAB_le
  refine le_trans h_tri ?_
  have h_five :
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 layerA Ω
        + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 layerB Ω
        + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 layerC Ω
        + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 layerD Ω
        + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 layerE Ω
      ≤ ENNReal.ofReal CA * A + ENNReal.ofReal CB * A + ENNReal.ofReal CC * A
        + ENNReal.ofReal CD * A + ENNReal.ofReal CE * A :=
    add_le_add (add_le_add (add_le_add (add_le_add hCA_i hCB_i) hCC_i) hCD_i)
      hCE_i
  refine le_trans h_five ?_
  rw [ENNReal.ofReal_add (by positivity) hCE_nn,
    ENNReal.ofReal_add (by positivity) hCD_nn,
    ENNReal.ofReal_add (by positivity) hCC_nn,
    ENNReal.ofReal_add hCA_nn hCB_nn]
  rw [add_mul, add_mul, add_mul, add_mul]

end MainBoundUniformUnconditional

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
