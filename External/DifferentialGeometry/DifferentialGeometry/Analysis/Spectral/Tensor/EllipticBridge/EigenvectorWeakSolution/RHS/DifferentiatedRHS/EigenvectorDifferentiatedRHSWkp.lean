import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Iterated.EigenvectorIteratedDatum
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Multiplication.MultiplyQuantK


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

private abbrev Kα (α : M) : Set EuclN :=
  chartPouKernel (I := I) (M := M) α

private abbrev Ωα (α : M) : Set EuclN :=
  chartTargetEuclid (I := I) (M := M) α

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma Kα_compact (α : M) : IsCompact (Kα (I := I) (M := M) α) :=
  chartPouKernel_isCompact (I := I) (M := M) α

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma Kα_meas (α : M) : MeasurableSet (Kα (I := I) (M := M) α) :=
  chartPouKernel_measurableSet (I := I) (M := M) α

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma Kα_subset_Ωα (α : M) :
    Kα (I := I) (M := M) α ⊆ Ωα (I := I) (M := M) α :=
  chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma Ωα_isOpen (α : M) : IsOpen (Ωα (I := I) (M := M) α) :=
  chartTargetEuclid_isOpen (I := I) (M := M) α

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
private lemma memWkp_coef_mul_factor
    (α : M) (K : ℕ)
    {coef factor : EuclN → ℝ}
    (hcoef_chart : ContDiffOn ℝ (⊤ : ℕ∞) coef (Ωα (I := I) (M := M) α))
    (hfactor_memWkp : MemWkp (d := Module.finrank ℝ E) K 2 factor
      (Ωα (I := I) (M := M) α))
    (hfactor_ae_zero : factor =ᵐ[(volume : Measure EuclN).restrict
      (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)]
      (fun _ => (0 : ℝ))) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => coef y * factor y) (Ωα (I := I) (M := M) α) := by
  classical
  obtain ⟨δ, χ, hδ_pos, hδ_in, hχ_smooth, hχ_cs, _hχ_range, hχ_one, hχ_tsupp⟩ :=
    exists_smooth_cutoff_with_neighborhood (d := Module.finrank ℝ E)
      (Kα_compact (I := I) (M := M) α)
      (Ωα_isOpen (I := I) (M := M) α)
      (Kα_subset_Ωα (I := I) (M := M) α)
  have hχ_coef_smooth : ContDiff ℝ (⊤ : ℕ∞) (fun y => χ y * coef y) := by
    have h_open_chart : IsOpen (Ωα (I := I) (M := M) α) :=
      Ωα_isOpen (I := I) (M := M) α
    have h_open_compl : IsOpen ((tsupport χ)ᶜ) :=
      (isClosed_tsupport _).isOpen_compl
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy_supp : y ∈ tsupport χ
    · have hy_chart : y ∈ Ωα (I := I) (M := M) α := hχ_tsupp hy_supp
      exact hχ_smooth.contDiffAt.mul
        ((hcoef_chart y hy_chart).contDiffAt (h_open_chart.mem_nhds hy_chart))
    · have h_eq_zero : (fun y => χ y * coef y)
          =ᶠ[𝓝 y] (fun _ : EuclN => (0 : ℝ)) := by
        filter_upwards [h_open_compl.mem_nhds hy_supp] with z hz
        rw [image_eq_zero_of_notMem_tsupport hz, zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq h_eq_zero
  have hχ_coef_cs : HasCompactSupport (fun y => χ y * coef y) :=
    HasCompactSupport.mul_right hχ_cs
  obtain ⟨C, _hC_nn, hC_bd⟩ :=
    exists_uniform_iteratedFDeriv_bound_of_smooth_compactSupport
      (d := Module.finrank ℝ E) hχ_coef_smooth hχ_coef_cs K
  have h_prod_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => (χ y * coef y) * factor y) (Ωα (I := I) (M := M) α) :=
    MemWkp.smul_smooth_bounded (d := Module.finrank ℝ E) K
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (Ωα_isOpen (I := I) (M := M) α) hχ_coef_smooth
      (fun j _hj y _hy => hC_bd y j _hj) hfactor_memWkp
  set Cδ : Set EuclN := Metric.cthickening δ (Kα (I := I) (M := M) α)
    with hCδ_def
  have hCδ_in_target : Cδ ⊆ Ωα (I := I) (M := M) α := hδ_in
  have h_ae_eq : (fun y => (χ y * coef y) * factor y)
      =ᵐ[(volume : Measure EuclN).restrict (Ωα (I := I) (M := M) α)]
      (fun y => coef y * factor y) := by
    set Ω : Set EuclN := Ωα (I := I) (M := M) α with hΩ_def
    have hΩ_meas : MeasurableSet Ω :=
      (Ωα_isOpen (I := I) (M := M) α).measurableSet
    have hCδ_closed : IsClosed Cδ := Metric.isClosed_cthickening
    have hCδ_meas : MeasurableSet Cδ := hCδ_closed.measurableSet
    have h_eq_on_Cδ : (fun y => (χ y * coef y) * factor y)
        =ᵐ[(volume : Measure EuclN).restrict Cδ]
        (fun y => coef y * factor y) := by
      refine (ae_restrict_iff' hCδ_meas).mpr ?_
      refine Filter.Eventually.of_forall fun y hy => ?_
      have hχy : χ y = 1 := hχ_one y hy
      change (χ y * coef y) * factor y = coef y * factor y
      rw [hχy]; ring
    have hKα_in_Cδ : Kα (I := I) (M := M) α ⊆ Cδ :=
      Metric.self_subset_cthickening _
    have h_diff_sub : Ω \ Cδ ⊆ Ω \ Kα (I := I) (M := M) α := fun y hy =>
      ⟨hy.1, fun hyK => hy.2 (hKα_in_Cδ hyK)⟩
    have h_factor_ae_zero_diff : factor =ᵐ[(volume : Measure EuclN).restrict
        (Ω \ Cδ)] (fun _ => (0 : ℝ)) := by
      have h_abs : (volume : Measure EuclN).restrict (Ω \ Cδ) ≪
          (volume : Measure EuclN).restrict (Ω \ Kα (I := I) (M := M) α) :=
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
  exact (MemWkp_congr_ae (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) (Ωα_isOpen (I := I) (M := M) α) h_ae_eq).mp
    h_prod_memWkp

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma memWkp_finset_sum
    {α : M} {K : ℕ} {ι : Type*} (s : Finset ι)
    {f : ι → EuclN → ℝ}
    (hf : ∀ i ∈ s, MemWkp (d := Module.finrank ℝ E) K 2 (f i)
      (Ωα (I := I) (M := M) α)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ∑ i ∈ s, f i y) (Ωα (I := I) (M := M) α) := by
  classical
  have h_open : IsOpen (Ωα (I := I) (M := M) α) := Ωα_isOpen (I := I) (M := M) α
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact MemWkp_zero_fun (d := Module.finrank ℝ E)
        (by norm_num : (1 : ℝ≥0∞) ≤ 2) h_open
  | insert i s his ih =>
      have hi : MemWkp (d := Module.finrank ℝ E) K 2 (f i)
          (Ωα (I := I) (M := M) α) := hf i (Finset.mem_insert_self _ _)
      have hsum := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
      have h_eq : (fun y => ∑ j ∈ insert i s, f j y) =
          (fun y => f i y + ∑ j ∈ s, f j y) := by
        funext y; rw [Finset.sum_insert his]
      rw [h_eq]
      exact MemWkp.add (d := Module.finrank ℝ E)
        (by norm_num : (1 : ℝ≥0∞) ≤ 2) h_open hi hsum

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
private lemma layer_D_memWkp
    (g : SmoothRiemannianMetric I M) (α : M) (K : ℕ)
    (lₙ : Fin (Module.finrank ℝ E))
    {fChartEffPrev : EuclN → ℝ}
    (h_prev_memWkp_K :
      MemWkp (d := Module.finrank ℝ E) K 2 fChartEffPrev
        (Ωα (I := I) (M := M) α))
    (h_prev_ae_zero : fChartEffPrev =ᵐ[(volume : Measure EuclN).restrict
      (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)]
      (fun _ => (0 : ℝ))) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => densityDerivOnEuclid (I := I) g α lₙ y * fChartEffPrev y)
      (Ωα (I := I) (M := M) α) :=
  memWkp_coef_mul_factor (I := I) (M := M) α K
    (densityDerivOnEuclid_contDiffOn (I := I) g α lₙ)
    h_prev_memWkp_K h_prev_ae_zero

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
private lemma layer_E_memWkp
    (g : SmoothRiemannianMetric I M) (α : M) (K : ℕ)
    (lₙ : Fin (Module.finrank ℝ E))
    {fChartEffPrev : EuclN → ℝ}
    (h_prev_memWkp_succ :
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2 fChartEffPrev
        (Ωα (I := I) (M := M) α))
    (h_prev_ae_zero : fChartEffPrev =ᵐ[(volume : Measure EuclN).restrict
      (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)]
      (fun _ => (0 : ℝ))) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y =>
        densityOnEuclid (I := I) g α y *
        chosenWeakPartial' (d := Module.finrank ℝ E) 2 lₙ
          fChartEffPrev (Ωα (I := I) (M := M) α) y)
      (Ωα (I := I) (M := M) α) := by
  have h_factor_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (chosenWeakPartial' (d := Module.finrank ℝ E) 2 lₙ
        fChartEffPrev (Ωα (I := I) (M := M) α))
      (Ωα (I := I) (M := M) α) :=
    h_prev_memWkp_succ.chosenWeakPartial_mem lₙ
  have h_factor_ae_zero :=
    chosenWeakPartial'_ae_zero_off_chartPouKernel_of_ae_zero
      (I := I) (M := M) α h_prev_ae_zero lₙ
  exact memWkp_coef_mul_factor (I := I) (M := M) α K
    (densityOnEuclid_contDiffOn (I := I) g α)
    h_factor_memWkp h_factor_ae_zero

omit [CompleteSpace E] [CompactSpace M] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] in

omit [NeZero (Module.finrank ℝ E)] in
private lemma one_div_densityOnEuclid_contDiffOn
    (g : SmoothRiemannianMetric I M) (α : M) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun y => 1 / densityOnEuclid (I := I) g α y)
      (Ωα (I := I) (M := M) α) :=
  contDiffOn_const.div (densityOnEuclid_contDiffOn (I := I) g α)
    (fun _ hy => (densityOnEuclid_pos (I := I) g α hy).ne')

omit [CompleteSpace E] in
private lemma iteratedPartial_ae_zero_off_Kα_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (m : ℕ) (l : Fin m → Fin (Module.finrank ℝ E)) :
    eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s i α P₀ m l
      =ᵐ[(volume : Measure EuclN).restrict
        (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)]
      (fun _ : EuclN => (0 : ℝ)) :=
  eigenvectorChartIteratedPartial_ae_zero_off_chartPouKernel
    (I := I) (M := M) g r s i α P₀ m l

omit [CompleteSpace E] in
private lemma layer_A_pair_memWkp_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (a b : Fin (Module.finrank ℝ E))
    (h_comp_succ_K :
      MemWkp (d := Module.finrank ℝ E) ((m + 1) + K) 2
        (eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀)
        (Ωα (I := I) (M := M) α)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y =>
        (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
              (l (Fin.last m))) y)
            (EuclideanSpace.single b 1) *
        eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
      (Ωα (I := I) (M := M) α) := by
  classical
  have h_coef_smooth : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y => (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
            (l (Fin.last m))) y)
          (EuclideanSpace.single b 1))
      (Ωα (I := I) (M := M) α) := by
    have h_open : IsOpen (Ωα (I := I) (M := M) α) :=
      Ωα_isOpen (I := I) (M := M) α
    have h_diffOn : ContDiffOn ℝ (⊤ : ℕ∞)
        (weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)))
        (Ωα (I := I) (M := M) α) :=
      weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α a b (l (Fin.last m))
    have h_fderiv : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun y => fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
            (l (Fin.last m))) y)
        (Ωα (I := I) (M := M) α) :=
      ((contDiffOn_infty_iff_fderiv_of_isOpen h_open).1 h_diffOn).2
    have h_eval : ContDiff ℝ (⊤ : ℕ∞)
        (fun (L : EuclN →L[ℝ] ℝ) => L (EuclideanSpace.single b 1)) :=
      (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single b (1 : ℝ))).contDiff
    exact h_eval.contDiffOn.comp h_fderiv (mapsTo_univ _ _)
  have h_factor_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
      (Ωα (I := I) (M := M) α) := by
    have h_comp_K_plus : MemWkp (d := Module.finrank ℝ E) (K + (m + 1)) 2
        (eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀)
        (Ωα (I := I) (M := M) α) := by
      have h_eq : K + (m + 1) = (m + 1) + K := by ring
      rw [h_eq]; exact h_comp_succ_K
    exact eigenvectorChartIteratedPartial_memWkp_of_memWkp
      (I := I) (M := M) g r s i α P₀ (m + 1) K h_comp_K_plus
      (Fin.cons a (Fin.init l))
  have h_factor_ae_zero := iteratedPartial_ae_zero_off_Kα_unconditional
    (I := I) (M := M) g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l))
  exact memWkp_coef_mul_factor (I := I) (M := M) α K h_coef_smooth
    h_factor_memWkp h_factor_ae_zero

omit [CompleteSpace E] in
private lemma layer_A_memWkp_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (h_comp_succ_K :
      MemWkp (d := Module.finrank ℝ E) ((m + 1) + K) 2
        (eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀)
        (Ωα (I := I) (M := M) α)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ∑ a : Fin (Module.finrank ℝ E),
        ∑ b : Fin (Module.finrank ℝ E),
          (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
                (l (Fin.last m))) y)
              (EuclideanSpace.single b 1) *
            eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
      (Ωα (I := I) (M := M) α) := by
  classical
  have h_inner : ∀ a : Fin (Module.finrank ℝ E),
      MemWkp (d := Module.finrank ℝ E) K 2
        (fun y => ∑ b : Fin (Module.finrank ℝ E),
          (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
                (l (Fin.last m))) y)
              (EuclideanSpace.single b 1) *
            eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
        (Ωα (I := I) (M := M) α) := by
    intro a
    exact memWkp_finset_sum (I := I) (M := M)
      (α := α) (K := K) (s := Finset.univ)
      (f := fun b y =>
        (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
              (l (Fin.last m))) y)
            (EuclideanSpace.single b 1) *
          eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
      (fun b _hb => layer_A_pair_memWkp_unconditional (I := I) (M := M)
        g r s i α P₀ m K l a b h_comp_succ_K)
  exact memWkp_finset_sum (I := I) (M := M)
    (α := α) (K := K) (s := Finset.univ)
    (f := fun a y => ∑ b : Fin (Module.finrank ℝ E),
      (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
            (l (Fin.last m))) y)
          (EuclideanSpace.single b 1) *
        eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
    (fun a _ha => h_inner a)

omit [CompleteSpace E] in
private lemma layer_B_pair_memWkp_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (a b : Fin (Module.finrank ℝ E))
    (h_comp_m_plus_2_K :
      MemWkp (d := Module.finrank ℝ E) ((m + 2) + K) 2
        (eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀)
        (Ωα (I := I) (M := M) α)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y =>
        weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
        chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
          (Ωα (I := I) (M := M) α) y)
      (Ωα (I := I) (M := M) α) := by
  classical
  have h_coef_smooth : ContDiffOn ℝ (⊤ : ℕ∞)
      (weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)))
      (Ωα (I := I) (M := M) α) :=
    weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α a b (l (Fin.last m))
  have h_inner_memWkp_succ : MemWkp (d := Module.finrank ℝ E) (K + 1) 2
      (eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
      (Ωα (I := I) (M := M) α) := by
    have h_comp_K_plus : MemWkp (d := Module.finrank ℝ E) ((K + 1) + (m + 1)) 2
        (eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀)
        (Ωα (I := I) (M := M) α) := by
      have h_eq : (K + 1) + (m + 1) = (m + 2) + K := by ring
      rw [h_eq]; exact h_comp_m_plus_2_K
    exact eigenvectorChartIteratedPartial_memWkp_of_memWkp
      (I := I) (M := M) g r s i α P₀ (m + 1) (K + 1) h_comp_K_plus
      (Fin.cons a (Fin.init l))
  have h_factor_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
        (Ωα (I := I) (M := M) α))
      (Ωα (I := I) (M := M) α) :=
    h_inner_memWkp_succ.chosenWeakPartial_mem b
  have h_inner_ae := iteratedPartial_ae_zero_off_Kα_unconditional
    (I := I) (M := M) g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l))
  have h_factor_ae_zero :=
    chosenWeakPartial'_ae_zero_off_chartPouKernel_of_ae_zero
      (I := I) (M := M) α h_inner_ae b
  exact memWkp_coef_mul_factor (I := I) (M := M) α K h_coef_smooth
    h_factor_memWkp h_factor_ae_zero

omit [CompleteSpace E] in
private lemma layer_B_memWkp_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (h_comp_m_plus_2_K :
      MemWkp (d := Module.finrank ℝ E) ((m + 2) + K) 2
        (eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀)
        (Ωα (I := I) (M := M) α)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ∑ a : Fin (Module.finrank ℝ E),
        ∑ b : Fin (Module.finrank ℝ E),
          weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
            chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
              (eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
              (Ωα (I := I) (M := M) α) y)
      (Ωα (I := I) (M := M) α) := by
  classical
  have h_inner : ∀ a : Fin (Module.finrank ℝ E),
      MemWkp (d := Module.finrank ℝ E) K 2
        (fun y => ∑ b : Fin (Module.finrank ℝ E),
          weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
            chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
              (eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
              (Ωα (I := I) (M := M) α) y)
        (Ωα (I := I) (M := M) α) := by
    intro a
    exact memWkp_finset_sum (I := I) (M := M)
      (α := α) (K := K) (s := Finset.univ)
      (f := fun b y =>
        weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
          chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
            (Ωα (I := I) (M := M) α) y)
      (fun b _hb => layer_B_pair_memWkp_unconditional (I := I) (M := M)
        g r s i α P₀ m K l a b h_comp_m_plus_2_K)
  exact memWkp_finset_sum (I := I) (M := M)
    (α := α) (K := K) (s := Finset.univ)
    (f := fun a y => ∑ b : Fin (Module.finrank ℝ E),
      weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
        chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
          (Ωα (I := I) (M := M) α) y)
    (fun a _ha => h_inner a)

omit [CompleteSpace E] in
private lemma layer_C_memWkp_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (h_comp_m_K :
      MemWkp (d := Module.finrank ℝ E) (m + K) 2
        (eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀)
        (Ωα (I := I) (M := M) α)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y =>
        densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
        eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ m (Fin.init l) y)
      (Ωα (I := I) (M := M) α) := by
  classical
  have h_coef_smooth : ContDiffOn ℝ (⊤ : ℕ∞)
      (densityDerivOnEuclid (I := I) g α (l (Fin.last m)))
      (Ωα (I := I) (M := M) α) :=
    densityDerivOnEuclid_contDiffOn (I := I) g α (l (Fin.last m))
  have h_factor_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s i α P₀ m (Fin.init l))
      (Ωα (I := I) (M := M) α) := by
    have h_comp_K_plus : MemWkp (d := Module.finrank ℝ E) (K + m) 2
        (eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀)
        (Ωα (I := I) (M := M) α) := by
      have h_eq : K + m = m + K := by ring
      rw [h_eq]; exact h_comp_m_K
    exact eigenvectorChartIteratedPartial_memWkp_of_memWkp
      (I := I) (M := M) g r s i α P₀ m K h_comp_K_plus (Fin.init l)
  have h_factor_ae_zero := iteratedPartial_ae_zero_off_Kα_unconditional
    (I := I) (M := M) g r s i α P₀ m (Fin.init l)
  exact memWkp_coef_mul_factor (I := I) (M := M) α K h_coef_smooth
    h_factor_memWkp h_factor_ae_zero

omit [CompleteSpace E] in
lemma eigenvectorChartRHSDiffNumerator_memWkp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    {fChartEffPrev : EuclN → ℝ}
    (h_comp : MemWkp (d := Module.finrank ℝ E) (m + 2 + K) 2
      (eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀)
      (Ωα (I := I) (M := M) α))
    (h_prev_memWkp_succ :
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2 fChartEffPrev
        (Ωα (I := I) (M := M) α))
    (h_prev_ae_zero : fChartEffPrev =ᵐ[(volume : Measure EuclN).restrict
      (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)]
      (fun _ => (0 : ℝ))) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (eigenvectorChartRHSDiffNumerator (I := I) (M := M)
        g r s i α P₀ m l fChartEffPrev)
      (Ωα (I := I) (M := M) α) := by
  classical
  have h_open : IsOpen (Ωα (I := I) (M := M) α) := Ωα_isOpen (I := I) (M := M) α
  have h_comp_succ_K : MemWkp (d := Module.finrank ℝ E) ((m + 1) + K) 2
      (eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀)
      (Ωα (I := I) (M := M) α) :=
    h_comp.le_of_le (by omega)
  have h_comp_m_K : MemWkp (d := Module.finrank ℝ E) (m + K) 2
      (eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀)
      (Ωα (I := I) (M := M) α) :=
    h_comp.le_of_le (by omega)
  have h_comp_m_plus_2_K : MemWkp (d := Module.finrank ℝ E) ((m + 2) + K) 2
      (eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀)
      (Ωα (I := I) (M := M) α) :=
    h_comp.le_of_le (by omega)
  have hA := layer_A_memWkp_unconditional (I := I) (M := M) g r s i α P₀ m K l
    h_comp_succ_K
  have hB := layer_B_memWkp_unconditional (I := I) (M := M) g r s i α P₀ m K l
    h_comp_m_plus_2_K
  have hC := layer_C_memWkp_unconditional (I := I) (M := M) g r s i α P₀ m K l
    h_comp_m_K
  have h_prev_memWkp_K : MemWkp (d := Module.finrank ℝ E) K 2 fChartEffPrev
      (Ωα (I := I) (M := M) α) := h_prev_memWkp_succ.le_of_le (by omega)
  have hD := layer_D_memWkp (I := I) (M := M) g α K (l (Fin.last m))
    h_prev_memWkp_K h_prev_ae_zero
  have hE := layer_E_memWkp (I := I) (M := M) g α K (l (Fin.last m))
    h_prev_memWkp_succ h_prev_ae_zero
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
                (Ωα (I := I) (M := M) α) y)) -
        densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
          eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ m (Fin.init l) y) +
        densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
          fChartEffPrev y) +
        densityOnEuclid (I := I) g α y *
          chosenWeakPartial' (d := Module.finrank ℝ E) 2 (l (Fin.last m))
            fChartEffPrev (Ωα (I := I) (M := M) α) y) =
      eigenvectorChartRHSDiffNumerator (I := I) (M := M)
        g r s i α P₀ m l fChartEffPrev := by
    funext y
    rfl
  rw [← h_eq]
  exact h_step4

omit [CompleteSpace E] in
private lemma eigenvectorChartRHSDiffNumerator_unconditional_ae_zero_off_Kα
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    {fChartEffPrev : EuclN → ℝ}
    (h_prev_ae_zero : fChartEffPrev =ᵐ[(volume : Measure EuclN).restrict
      (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)]
      (fun _ => (0 : ℝ))) :
    eigenvectorChartRHSDiffNumerator (I := I) (M := M)
        g r s i α P₀ m l fChartEffPrev
      =ᵐ[(volume : Measure EuclN).restrict
        (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)]
      (fun _ : EuclN => (0 : ℝ)) := by
  classical
  have hA_ae : ∀ a : Fin (Module.finrank ℝ E),
      eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l))
        =ᵐ[(volume : Measure EuclN).restrict
          (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)]
        (fun _ => (0 : ℝ)) := fun a =>
    iteratedPartial_ae_zero_off_Kα_unconditional (I := I) (M := M)
      g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l))
  have hB_ae : ∀ a b : Fin (Module.finrank ℝ E),
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
        (Ωα (I := I) (M := M) α)
        =ᵐ[(volume : Measure EuclN).restrict
          (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)]
        (fun _ => (0 : ℝ)) := fun a b =>
    chosenWeakPartial'_ae_zero_off_chartPouKernel_of_ae_zero
      (I := I) (M := M) α (hA_ae a) b
  have hC_ae := iteratedPartial_ae_zero_off_Kα_unconditional
    (I := I) (M := M) g r s i α P₀ m (Fin.init l)
  have hE_ae := chosenWeakPartial'_ae_zero_off_chartPouKernel_of_ae_zero
    (I := I) (M := M) α h_prev_ae_zero (l (Fin.last m))
  have hA_sum_ae : (fun y => ∑ a : Fin (Module.finrank ℝ E),
      ∑ b : Fin (Module.finrank ℝ E),
        (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
              (l (Fin.last m))) y)
            (EuclideanSpace.single b 1) *
          eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
      =ᵐ[(volume : Measure EuclN).restrict
        (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)]
      (fun _ => (0 : ℝ)) := by
    have h_all : ∀ᵐ y ∂((volume : Measure EuclN).restrict
        (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)),
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
            (Ωα (I := I) (M := M) α) y)
      =ᵐ[(volume : Measure EuclN).restrict
        (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)]
      (fun _ => (0 : ℝ)) := by
    have h_all : ∀ᵐ y ∂((volume : Measure EuclN).restrict
        (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)),
        ∀ a : Fin (Module.finrank ℝ E), ∀ b : Fin (Module.finrank ℝ E),
          chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
            (Ωα (I := I) (M := M) α) y = 0 := by
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
        (Ωα (I := I) (M := M) α) y = 0
    rw [hy a b]; ring
  have hC_term_ae : (fun y =>
      densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
        eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ m (Fin.init l) y)
      =ᵐ[(volume : Measure EuclN).restrict
        (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)]
      (fun _ => (0 : ℝ)) := by
    filter_upwards [hC_ae] with y hy
    show densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
      eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s i α P₀ m (Fin.init l) y = 0
    rw [hy]; ring
  have hD_term_ae : (fun y =>
      densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y * fChartEffPrev y)
      =ᵐ[(volume : Measure EuclN).restrict
        (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)]
      (fun _ => (0 : ℝ)) := by
    filter_upwards [h_prev_ae_zero] with y hy
    show densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
      fChartEffPrev y = 0
    rw [hy]; ring
  have hE_term_ae : (fun y =>
      densityOnEuclid (I := I) g α y *
        chosenWeakPartial' (d := Module.finrank ℝ E) 2 (l (Fin.last m))
          fChartEffPrev (Ωα (I := I) (M := M) α) y)
      =ᵐ[(volume : Measure EuclN).restrict
        (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)]
      (fun _ => (0 : ℝ)) := by
    filter_upwards [hE_ae] with y hy
    show densityOnEuclid (I := I) g α y *
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 (l (Fin.last m))
        fChartEffPrev (Ωα (I := I) (M := M) α) y = 0
    rw [hy]; ring
  filter_upwards [hA_sum_ae, hB_sum_ae, hC_term_ae, hD_term_ae, hE_term_ae]
    with y hA hB hC hD hE
  show eigenvectorChartRHSDiffNumerator (I := I) (M := M)
      g r s i α P₀ m l fChartEffPrev y = 0
  unfold eigenvectorChartRHSDiffNumerator
  rw [hA, hB, hC, hD, hE]; ring

omit [CompleteSpace E] in
lemma eigenvectorChartRHSDiffNumerator_div_density_memWkp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    {fChartEffPrev : EuclN → ℝ}
    (h_comp : MemWkp (d := Module.finrank ℝ E) (m + 2 + K) 2
      (eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀)
      (Ωα (I := I) (M := M) α))
    (h_prev_memWkp_succ :
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2 fChartEffPrev
        (Ωα (I := I) (M := M) α))
    (h_prev_ae_zero : fChartEffPrev =ᵐ[(volume : Measure EuclN).restrict
      (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)]
      (fun _ => (0 : ℝ))) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y =>
        eigenvectorChartRHSDiffNumerator (I := I) (M := M)
          g r s i α P₀ m l fChartEffPrev y /
        densityOnEuclid (I := I) g α y)
      (Ωα (I := I) (M := M) α) := by
  classical
  have h_eq : (fun y =>
      eigenvectorChartRHSDiffNumerator (I := I) (M := M)
        g r s i α P₀ m l fChartEffPrev y /
      densityOnEuclid (I := I) g α y) =
      (fun y => (1 / densityOnEuclid (I := I) g α y) *
        eigenvectorChartRHSDiffNumerator (I := I) (M := M)
          g r s i α P₀ m l fChartEffPrev y) := by
    funext y
    rw [one_div, mul_comm, ← div_eq_mul_inv]
  rw [h_eq]
  have h_num_memWkp := eigenvectorChartRHSDiffNumerator_memWkp
    (I := I) (M := M) g r s i α P₀ m K l
    h_comp h_prev_memWkp_succ h_prev_ae_zero
  have h_num_ae_zero := eigenvectorChartRHSDiffNumerator_unconditional_ae_zero_off_Kα
    (I := I) (M := M) g r s i α P₀ m l h_prev_ae_zero
  exact memWkp_coef_mul_factor (I := I) (M := M) α K
    (one_div_densityOnEuclid_contDiffOn (I := I) (M := M) g α)
    h_num_memWkp h_num_ae_zero

omit [CompleteSpace E] in
lemma eigenvectorChartRHSDiffNumerator_div_density_ae_zero_off_chartPouKernel
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    {fChartEffPrev : EuclN → ℝ}
    (h_prev_ae_zero : fChartEffPrev =ᵐ[(volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α \
        chartPouKernel (I := I) (M := M) α)]
      (fun _ => (0 : ℝ))) :
    (fun y =>
        eigenvectorChartRHSDiffNumerator (I := I) (M := M)
          g r s i α P₀ m l fChartEffPrev y /
        densityOnEuclid (I := I) g α y)
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α)]
      (fun _ : EuclN => (0 : ℝ)) := by
  have h_num_ae_zero := eigenvectorChartRHSDiffNumerator_unconditional_ae_zero_off_Kα
    (I := I) (M := M) g r s i α P₀ m l h_prev_ae_zero
  filter_upwards [h_num_ae_zero] with y hy
  show eigenvectorChartRHSDiffNumerator (I := I) (M := M)
      g r s i α P₀ m l fChartEffPrev y /
    densityOnEuclid (I := I) g α y = 0
  rw [hy]; simp

section ElaborationTests

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (i : TensorEigenIdx (I := I) (M := M) g r s)

example (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    {fChartEffPrev : EuclN → ℝ}
    (h_comp : MemWkp (d := Module.finrank ℝ E) (m + 2 + K) 2
      (eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀)
      (chartTargetEuclid (I := I) (M := M) α))
    (h_prev_memWkp_succ :
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2 fChartEffPrev
        (chartTargetEuclid (I := I) (M := M) α))
    (h_prev_ae_zero : fChartEffPrev =ᵐ[(volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α \
        chartPouKernel (I := I) (M := M) α)]
      (fun _ => (0 : ℝ))) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (eigenvectorChartRHSDiffNumerator (I := I) (M := M)
        g r s i α P₀ m l fChartEffPrev)
      (chartTargetEuclid (I := I) (M := M) α) :=
  eigenvectorChartRHSDiffNumerator_memWkp (I := I) (M := M)
    g r s i α P₀ m K l h_comp h_prev_memWkp_succ h_prev_ae_zero

example (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    {fChartEffPrev : EuclN → ℝ}
    (h_comp : MemWkp (d := Module.finrank ℝ E) (m + 2 + K) 2
      (eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀)
      (chartTargetEuclid (I := I) (M := M) α))
    (h_prev_memWkp_succ :
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2 fChartEffPrev
        (chartTargetEuclid (I := I) (M := M) α))
    (h_prev_ae_zero : fChartEffPrev =ᵐ[(volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α \
        chartPouKernel (I := I) (M := M) α)]
      (fun _ => (0 : ℝ))) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y =>
        eigenvectorChartRHSDiffNumerator (I := I) (M := M)
          g r s i α P₀ m l fChartEffPrev y /
        densityOnEuclid (I := I) g α y)
      (chartTargetEuclid (I := I) (M := M) α) :=
  eigenvectorChartRHSDiffNumerator_div_density_memWkp (I := I) (M := M)
    g r s i α P₀ m K l h_comp h_prev_memWkp_succ h_prev_ae_zero

end ElaborationTests

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
