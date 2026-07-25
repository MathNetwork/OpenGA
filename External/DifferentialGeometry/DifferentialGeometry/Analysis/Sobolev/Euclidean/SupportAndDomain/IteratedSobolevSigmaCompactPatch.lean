import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.IteratedSobolev
import Mathlib.MeasureTheory.Function.LpSpace.Complete


noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Euclidean

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
lemma exists_monotone_precompact_open_exhaustion
    {Ω : Set E} (hΩ_open : IsOpen Ω) :
    ∃ Ω_seq : ℕ → Set E,
      (∀ n, IsOpen (Ω_seq n)) ∧
      (∀ n, IsCompact (closure (Ω_seq n))) ∧
      (∀ n, closure (Ω_seq n) ⊆ Ω) ∧
      (Monotone Ω_seq) ∧
      (⋃ n, Ω_seq n) = Ω := by
  classical
  haveI : LocallyCompactSpace ↥Ω := hΩ_open.locallyCompactSpace
  haveI : SecondCountableTopology ↥Ω := inferInstance
  haveI : SigmaCompactSpace ↥Ω :=
    sigmaCompactSpace_of_locallyCompact_secondCountable
  set K_sub : ℕ → Set ↥Ω := compactCovering ↥Ω with hK_sub_def
  have hK_sub_compact : ∀ n, IsCompact (K_sub n) := isCompact_compactCovering ↥Ω
  have hK_sub_mono : Monotone K_sub := monotone_accumulate
  have hK_sub_union : (⋃ n, K_sub n) = Set.univ := iUnion_compactCovering ↥Ω
  set K : ℕ → Set E := fun n => ((↑) : ↥Ω → E) '' K_sub n with hK_def
  have hK_compact : ∀ n, IsCompact (K n) := fun n =>
    (hK_sub_compact n).image continuous_subtype_val
  have hK_in_Ω : ∀ n, K n ⊆ Ω := by
    intro n y hy
    obtain ⟨z, _, hz_eq⟩ := hy
    rw [← hz_eq]
    exact z.2
  have hK_mono : Monotone K := fun m n hmn => Set.image_mono (hK_sub_mono hmn)
  have hK_union : (⋃ n, K n) = Ω := by
    apply Set.eq_of_subset_of_subset
    · rw [Set.iUnion_subset_iff]
      exact fun n => hK_in_Ω n
    · intro y hy
      let z : ↥Ω := ⟨y, hy⟩
      have hz_in_univ : z ∈ (⋃ n, K_sub n) := by rw [hK_sub_union]; trivial
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hz_in_univ
      exact Set.mem_iUnion.mpr ⟨n, z, hn, rfl⟩
  have h_get_open : ∀ n, ∃ r : ℝ, 0 < r ∧ Metric.cthickening r (K n) ⊆ Ω := by
    intro n
    exact (hK_compact n).exists_cthickening_subset_open hΩ_open (hK_in_Ω n)
  choose r hr_pos hr_sub using h_get_open
  set Ω_seq : ℕ → Set E := fun n =>
    ⋃ m ∈ Finset.range (n + 1), Metric.thickening (r m) (K m) with hΩ_seq_def
  have hΩ_seq_open : ∀ n, IsOpen (Ω_seq n) := by
    intro n
    refine isOpen_biUnion (fun m _ => ?_)
    exact Metric.isOpen_thickening
  have hΩ_seq_mono : Monotone Ω_seq := by
    intro a b hab
    refine biUnion_subset_biUnion_left ?_
    intro m hm
    rw [Finset.mem_coe, Finset.mem_range] at hm ⊢
    omega
  have h_closure_sub : ∀ n,
      closure (Ω_seq n) ⊆ ⋃ m ∈ Finset.range (n + 1), Metric.cthickening (r m) (K m) := by
    intro n
    have h_finite : (Finset.range (n + 1) : Set ℕ).Finite := (Finset.range (n + 1)).finite_toSet
    have h_closure_eq :
        closure (⋃ m ∈ Finset.range (n + 1), Metric.thickening (r m) (K m)) =
        ⋃ m ∈ Finset.range (n + 1), closure (Metric.thickening (r m) (K m)) :=
      h_finite.closure_biUnion _
    change closure (⋃ m ∈ Finset.range (n + 1), Metric.thickening (r m) (K m)) ⊆ _
    rw [h_closure_eq]
    refine iUnion₂_mono (fun m _ => ?_)
    exact Metric.closure_thickening_subset_cthickening _ _
  have hΩ_seq_closure_compact : ∀ n, IsCompact (closure (Ω_seq n)) := by
    intro n
    have h_in_compact :
        closure (Ω_seq n) ⊆ ⋃ m ∈ Finset.range (n + 1), Metric.cthickening (r m) (K m) :=
      h_closure_sub n
    have h_each_compact : ∀ m ∈ Finset.range (n + 1),
        IsCompact (Metric.cthickening (r m) (K m)) := by
      intro m _
      exact (hK_compact m).cthickening
    have h_union_compact :
        IsCompact (⋃ m ∈ Finset.range (n + 1), Metric.cthickening (r m) (K m)) :=
      (Finset.range (n + 1)).isCompact_biUnion h_each_compact
    exact h_union_compact.of_isClosed_subset isClosed_closure h_in_compact
  have hΩ_seq_closure_in_Ω : ∀ n, closure (Ω_seq n) ⊆ Ω := by
    intro n
    refine (h_closure_sub n).trans ?_
    refine Set.iUnion₂_subset (fun m _ => ?_)
    exact hr_sub m
  have hΩ_seq_union : (⋃ n, Ω_seq n) = Ω := by
    apply Set.eq_of_subset_of_subset
    · rw [Set.iUnion_subset_iff]
      intro n y hy
      simp only [Ω_seq, mem_iUnion] at hy
      obtain ⟨m, _, hy_in⟩ := hy
      have : Metric.thickening (r m) (K m) ⊆ Metric.cthickening (r m) (K m) :=
        Metric.thickening_subset_cthickening _ _
      exact hr_sub m (this hy_in)
    · intro y hy
      rw [← hK_union] at hy
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hy
      refine Set.mem_iUnion.mpr ⟨n, ?_⟩
      simp only [Ω_seq, mem_iUnion]
      refine ⟨n, Finset.self_mem_range_succ n, ?_⟩
      exact Metric.self_subset_thickening (hr_pos n) (K n) hn
  exact ⟨Ω_seq, hΩ_seq_open, hΩ_seq_closure_compact,
    hΩ_seq_closure_in_Ω, hΩ_seq_mono, hΩ_seq_union⟩

def patchedFunction
    (Ω_seq : ℕ → Set E) (g_seq : ℕ → E → ℝ) : E → ℝ := by
  classical
  exact fun x =>
    if h : ∃ n, x ∈ Ω_seq n then g_seq (Nat.find h) x else 0

omit [NeZero d] in
lemma patchedFunction_ae_eq_on_each
    {Ω_seq : ℕ → Set E}
    (hΩ_seq_open : ∀ n, IsOpen (Ω_seq n))
    (hΩ_seq_mono : Monotone Ω_seq)
    {g_seq : ℕ → E → ℝ}
    (hg_seq_ae_coherent :
      ∀ m n, m ≤ n →
        g_seq n =ᵐ[volume.restrict (Ω_seq m)] g_seq m)
    (n : ℕ) :
    patchedFunction Ω_seq g_seq =ᵐ[volume.restrict (Ω_seq n)] g_seq n := by
  classical
  induction n with
  | zero =>
      have h_pointwise : ∀ x ∈ Ω_seq 0,
          patchedFunction Ω_seq g_seq x = g_seq 0 x := by
        intro x hx
        have hpred : ∃ n, x ∈ Ω_seq n := ⟨0, hx⟩
        have h_min : Nat.find hpred ≤ 0 := Nat.find_min' hpred hx
        have h_find_zero : Nat.find hpred = 0 := Nat.le_zero.mp h_min
        unfold patchedFunction
        rw [dif_pos hpred, h_find_zero]
      rw [Filter.EventuallyEq, ae_restrict_iff' (hΩ_seq_open 0).measurableSet]
      exact Filter.Eventually.of_forall h_pointwise
  | succ n ih =>
      have hΩ_seq_n_meas : MeasurableSet (Ω_seq n) := (hΩ_seq_open n).measurableSet
      have hΩ_seq_succ_meas : MeasurableSet (Ω_seq (n+1)) :=
        (hΩ_seq_open (n+1)).measurableSet
      have h_set_eq : Ω_seq (n+1) = Ω_seq n ∪ (Ω_seq (n+1) \ Ω_seq n) := by
        rw [union_diff_self]
        exact (union_eq_right.mpr (hΩ_seq_mono (Nat.le_succ n))).symm
      have h_ae_on_left :
          patchedFunction Ω_seq g_seq =ᵐ[volume.restrict (Ω_seq n)] g_seq (n+1) := by
        have h_ae_coh : g_seq (n+1) =ᵐ[volume.restrict (Ω_seq n)] g_seq n :=
          hg_seq_ae_coherent n (n+1) (Nat.le_succ n)
        exact ih.trans h_ae_coh.symm
      have h_ae_on_right :
          patchedFunction Ω_seq g_seq
            =ᵐ[volume.restrict (Ω_seq (n+1) \ Ω_seq n)] g_seq (n+1) := by
        have h_pointwise : ∀ x ∈ Ω_seq (n+1) \ Ω_seq n,
            patchedFunction Ω_seq g_seq x = g_seq (n+1) x := by
          intro x ⟨hx_succ, hx_not⟩
          have hpred : ∃ n, x ∈ Ω_seq n := ⟨n+1, hx_succ⟩
          have h_le : Nat.find hpred ≤ n+1 := Nat.find_min' hpred hx_succ
          have h_not_le : ¬ Nat.find hpred ≤ n := by
            intro h_le_n
            have h_in_find : x ∈ Ω_seq (Nat.find hpred) := Nat.find_spec hpred
            have h_sub : Ω_seq (Nat.find hpred) ⊆ Ω_seq n := hΩ_seq_mono h_le_n
            exact hx_not (h_sub h_in_find)
          have h_eq : Nat.find hpred = n + 1 :=
            Nat.le_antisymm h_le (Nat.lt_of_not_le h_not_le)
          unfold patchedFunction
          rw [dif_pos hpred, h_eq]
        have hΩ_diff_meas : MeasurableSet (Ω_seq (n+1) \ Ω_seq n) :=
          hΩ_seq_succ_meas.diff hΩ_seq_n_meas
        rw [Filter.EventuallyEq, ae_restrict_iff' hΩ_diff_meas]
        exact Filter.Eventually.of_forall h_pointwise
      rw [Filter.EventuallyEq]
      rw [show Ω_seq (n+1) = Ω_seq n ∪ (Ω_seq (n+1) \ Ω_seq n) from h_set_eq]
      rw [ae_restrict_union_eq]
      exact ⟨h_ae_on_left, h_ae_on_right⟩

omit [NeZero d] in
lemma exists_global_of_ae_coherent_monotone
    {p : ℝ≥0∞} (_hp_one : 1 ≤ p) (_hp_top : p ≠ ⊤)
    {Ω : Set E} (_hΩ_open : IsOpen Ω)
    {Ω_seq : ℕ → Set E}
    (hΩ_seq_open : ∀ n, IsOpen (Ω_seq n))
    (hΩ_seq_mono : Monotone Ω_seq)
    (hΩ_seq_union : (⋃ n, Ω_seq n) = Ω)
    {g_seq : ℕ → E → ℝ}
    (hg_seq_memLp : ∀ n, MemLp (g_seq n) p (volume.restrict (Ω_seq n)))
    (hg_seq_ae_coherent :
      ∀ m n, m ≤ n →
        g_seq n =ᵐ[volume.restrict (Ω_seq m)] g_seq m)
    (h_eLpNorm_bound : ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ n,
        eLpNorm (g_seq n) p (volume.restrict (Ω_seq n)) ≤ C) :
    ∃ g : E → ℝ,
      (∀ n, g =ᵐ[volume.restrict (Ω_seq n)] g_seq n) ∧
      MemLp g p (volume.restrict Ω) := by
  classical
  refine ⟨patchedFunction Ω_seq g_seq, ?_, ?_⟩
  · exact fun n =>
      patchedFunction_ae_eq_on_each hΩ_seq_open hΩ_seq_mono hg_seq_ae_coherent n
  · obtain ⟨C, hC_lt_top, hC_bound⟩ := h_eLpNorm_bound
    have h_g_aem_on_each : ∀ n,
        AEStronglyMeasurable (patchedFunction Ω_seq g_seq)
          (volume.restrict (Ω_seq n)) := fun n =>
      (hg_seq_memLp n).aestronglyMeasurable.congr
        (patchedFunction_ae_eq_on_each hΩ_seq_open hΩ_seq_mono
          hg_seq_ae_coherent n).symm
    have h_g_aem_Ω : AEStronglyMeasurable (patchedFunction Ω_seq g_seq)
        (volume.restrict Ω) := by
      rw [← hΩ_seq_union]
      exact aestronglyMeasurable_iUnion_iff.mpr h_g_aem_on_each
    set g : E → ℝ := patchedFunction Ω_seq g_seq with hg_def
    have h_indicator_tendsto : ∀ᵐ x : E ∂(volume.restrict Ω),
        Filter.Tendsto (fun n => (Ω_seq n).indicator g x)
          Filter.atTop (nhds (g x)) := by
      refine Filter.Eventually.of_forall ?_
      intro x
      by_cases hx_in : ∃ n, x ∈ Ω_seq n
      · obtain ⟨N, hxN⟩ := hx_in
        have h_eventually : ∀ᶠ n in Filter.atTop, x ∈ Ω_seq n :=
          Filter.eventually_atTop.mpr ⟨N, fun n hn => hΩ_seq_mono hn hxN⟩
        have h_eq_eventually : ∀ᶠ n in Filter.atTop,
            (fun _ : ℕ => g x) n = (Ω_seq n).indicator g x := by
          filter_upwards [h_eventually] with n hxn
          exact (Set.indicator_of_mem hxn _).symm
        exact (tendsto_const_nhds (x := g x)).congr' h_eq_eventually
      · have h_all_not : ∀ n, x ∉ Ω_seq n := fun n hxn => hx_in ⟨n, hxn⟩
        have h_const_zero : ∀ n, (Ω_seq n).indicator g x = 0 := fun n =>
          Set.indicator_of_notMem (h_all_not n) _
        have h_g_zero : g x = 0 := by
          change patchedFunction Ω_seq g_seq x = 0
          unfold patchedFunction
          simp [hx_in]
        rw [h_g_zero]
        refine tendsto_const_nhds.congr (fun n => ?_)
        exact (h_const_zero n).symm
    have h_indicator_bound : ∀ n,
        eLpNorm ((Ω_seq n).indicator g) p (volume.restrict Ω) ≤ C := by
      intro n
      have hΩ_seq_n_meas : MeasurableSet (Ω_seq n) := (hΩ_seq_open n).measurableSet
      have h_eq : eLpNorm ((Ω_seq n).indicator g) p (volume.restrict Ω) =
          eLpNorm g p (volume.restrict (Ω_seq n)) := by
        rw [eLpNorm_indicator_eq_eLpNorm_restrict hΩ_seq_n_meas]
        congr 1
        rw [Measure.restrict_restrict hΩ_seq_n_meas]
        congr 1
        rw [Set.inter_eq_left]
        rw [← hΩ_seq_union]
        exact subset_iUnion _ n
      rw [h_eq]
      have h_ae : g =ᵐ[volume.restrict (Ω_seq n)] g_seq n :=
        patchedFunction_ae_eq_on_each hΩ_seq_open hΩ_seq_mono
          hg_seq_ae_coherent n
      rw [eLpNorm_congr_ae h_ae]
      exact hC_bound n
    have h_indicator_aem : ∀ n,
        AEStronglyMeasurable ((Ω_seq n).indicator g) (volume.restrict Ω) := by
      intro n
      refine AEStronglyMeasurable.indicator ?_ (hΩ_seq_open n).measurableSet
      exact h_g_aem_Ω
    have h_eLpNorm_g_le_C : eLpNorm g p (volume.restrict Ω) ≤ C := by
      have h_bound_eventually : ∀ᶠ n in Filter.atTop,
          eLpNorm ((Ω_seq n).indicator g) p (volume.restrict Ω) ≤ C :=
        Filter.Eventually.of_forall h_indicator_bound
      exact MeasureTheory.Lp.eLpNorm_le_of_ae_tendsto
        (u := Filter.atTop) (f := fun n => (Ω_seq n).indicator g) (g := g)
        h_bound_eventually h_indicator_aem h_indicator_tendsto
    exact ⟨h_g_aem_Ω, lt_of_le_of_lt h_eLpNorm_g_le_C hC_lt_top⟩

omit [NeZero d] in
theorem MemWkp_of_sigma_compact_cover_and_globalLp_zero
    {p : ℝ≥0∞} (_hp_one : 1 ≤ p) (_hp_top : p ≠ ⊤)
    {Ω : Set E} (_hΩ_open : IsOpen Ω) {u : E → ℝ}
    (h_globalLp : MemLp u p ((volume : Measure E).restrict Ω))
    (_h_local : ∀ Ω' : Set E,
       IsOpen Ω' → IsCompact (closure Ω') → closure Ω' ⊆ Ω →
       MemWkp (d := d) 0 p u Ω') :
    MemWkp (d := d) 0 p u Ω := by
  rw [MemWkp_zero]
  exact h_globalLp

end Euclidean
end Sobolev
end Analysis
end DifferentialGeometry
