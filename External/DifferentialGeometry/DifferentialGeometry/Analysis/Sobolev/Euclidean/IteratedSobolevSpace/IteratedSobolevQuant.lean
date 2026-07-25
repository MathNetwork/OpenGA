import DifferentialGeometry.Analysis.Sobolev.Euclidean.SupportAndDomain.IteratedSobolevSupportPromotion


noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Euclidean

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
theorem wkpNorm_succ_le
    (k : ℕ) (p : ℝ≥0∞) (Ω : Set E) (u : E → ℝ) :
    iteratedWeakSobolevNorm (d := d) (k + 1) p u Ω ≤
      eLpNorm u p (volume.restrict Ω) +
      ∑ i : Fin d,
        iteratedWeakSobolevNorm (d := d) k p (chosenWeakPartial' (d := d) p i u Ω) Ω :=
  le_of_eq (wkpNorm_succ_eq_eLpNorm_add_sum_partial (d := d) k p Ω u)

omit [NeZero d] in
theorem wkpNorm_le_wkpNorm_succ_sum
    (k : ℕ) (p : ℝ≥0∞) (Ω : Set E) (u : E → ℝ) :
    eLpNorm u p (volume.restrict Ω) +
      ∑ i : Fin d,
        iteratedWeakSobolevNorm (d := d) k p (chosenWeakPartial' (d := d) p i u Ω) Ω ≤
      iteratedWeakSobolevNorm (d := d) (k + 1) p u Ω :=
  le_of_eq (wkpNorm_succ_eq_eLpNorm_add_sum_partial (d := d) k p Ω u).symm

omit [NeZero d] in
theorem wkpNorm_succ_le_wkpNorm_add_sum_partial
    (k : ℕ) (p : ℝ≥0∞) (Ω : Set E) (u : E → ℝ) :
    iteratedWeakSobolevNorm (d := d) (k + 1) p u Ω ≤
      iteratedWeakSobolevNorm (d := d) k p u Ω +
      ∑ i : Fin d,
        iteratedWeakSobolevNorm (d := d) k p (chosenWeakPartial' (d := d) p i u Ω) Ω := by
  classical
  rw [wkpNorm_succ_eq_eLpNorm_add_sum_partial (d := d) k p Ω u]
  refine add_le_add ?_ (le_refl _)
  have h0 : iteratedWeakSobolevNorm (d := d) 0 p u Ω ≤ iteratedWeakSobolevNorm (d := d) k p u Ω :=
    wkpNorm_mono_order (d := d) (Nat.zero_le k) u Ω
  rwa [wkpNorm_zero (d := d) p u Ω] at h0

omit [NeZero d] in
theorem eLpNorm_le_wkpNorm
    (k : ℕ) (p : ℝ≥0∞) (Ω : Set E) (u : E → ℝ) :
    eLpNorm u p (volume.restrict Ω) ≤ iteratedWeakSobolevNorm (d := d) k p u Ω := by
  have h0 : iteratedWeakSobolevNorm (d := d) 0 p u Ω ≤ iteratedWeakSobolevNorm (d := d) k p u Ω :=
    wkpNorm_mono_order (d := d) (Nat.zero_le k) u Ω
  rwa [wkpNorm_zero (d := d) p u Ω] at h0

omit [NeZero d] in
theorem wkpNorm_chosenWeakPartial_le
    (k : ℕ) {p : ℝ≥0∞} {Ω : Set E} (hΩ : IsOpen Ω) (u : E → ℝ) (i : Fin d) :
    iteratedWeakSobolevNorm (d := d) k p (chosenWeakPartial' (d := d) p i u Ω) Ω ≤
      iteratedWeakSobolevNorm (d := d) (k + 1) p u Ω :=
  wkpNorm_chosenWeakPartial_le_wkpNorm_succ (d := d) k hΩ u i

omit [NeZero d] in
private theorem memWkp_finset_sum
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set E} (hΩ : IsOpen Ω)
    {ι : Type*} (s : Finset ι) (f : ι → E → ℝ)
    (hf : ∀ i ∈ s, MemWkp (d := d) k p (f i) Ω) :
    MemWkp (d := d) k p (fun x => ∑ i ∈ s, f i x) Ω := by
  classical
  induction s using Finset.induction with
  | empty =>
      simpa using MemWkp_zero_fun (d := d) hp hΩ
  | insert a t ha iht =>
      have h_split : (fun x => ∑ i ∈ insert a t, f i x) =
          (fun x => f a x + ∑ i ∈ t, f i x) := by
        funext x; rw [Finset.sum_insert ha]
      rw [h_split]
      refine MemWkp.add (d := d) hp hΩ (hf a (Finset.mem_insert_self a t)) ?_
      exact iht (fun i hi => hf i (Finset.mem_insert_of_mem hi))

omit [NeZero d] in
theorem wkpNorm_sum_le
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set E} (hΩ : IsOpen Ω)
    {ι : Type*} (s : Finset ι) (f : ι → E → ℝ)
    (hf : ∀ i ∈ s, MemWkp (d := d) k p (f i) Ω) :
    iteratedWeakSobolevNorm (d := d) k p (fun x => ∑ i ∈ s, f i x) Ω ≤
      ∑ i ∈ s, iteratedWeakSobolevNorm (d := d) k p (f i) Ω := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp only [Finset.sum_empty]
      rw [wkpNorm_zero_fun_zero (d := d) hp hΩ]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      have h_split : (fun x => ∑ i ∈ insert a s, f i x) =
          (fun x => f a x + ∑ i ∈ s, f i x) := by
        funext x
        rw [Finset.sum_insert ha]
      rw [h_split]
      have ha_mem : MemWkp (d := d) k p (f a) Ω :=
        hf a (Finset.mem_insert_self a s)
      have hs_mem : ∀ i ∈ s, MemWkp (d := d) k p (f i) Ω :=
        fun i hi => hf i (Finset.mem_insert_of_mem hi)
      have h_sum_mem : MemWkp (d := d) k p (fun x => ∑ i ∈ s, f i x) Ω :=
        memWkp_finset_sum (d := d) hp hΩ s f hs_mem
      have h_triangle :=
        wkpNorm_add_le (d := d) hp hΩ ha_mem h_sum_mem
      exact h_triangle.trans (add_le_add (le_refl _) (ih hs_mem))

omit [NeZero d] in
private theorem chosenWeakPartial'_extend_zero_ae
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ⊤) {Ω V : Set E}
    (hΩ : IsOpen Ω) (hV : IsOpen V) (hΩV : Ω ⊆ V)
    {u : E → ℝ} (hu : DeGiorgi.MemW1p (d := d) p u Ω)
    (hu_supp : tsupport u ⊆ Ω) (hu_compact : HasCompactSupport u) (i : Fin d) :
    chosenWeakPartial' (d := d) p i u V
      =ᵐ[volume.restrict V]
      Ω.indicator (chosenWeakPartial' (d := d) p i u Ω) := by
  classical
  have hu_W1_Ω : MemWkp (d := d) 1 p u Ω := MemWkp.one_iff_memW1p.mpr hu
  have hu_W1_V : MemWkp (d := d) 1 p u V :=
    MemWkp.extend_zero (d := d) hp hp_top hΩ hV hΩV hu_W1_Ω hu_supp hu_compact
  have hu_V : DeGiorgi.MemW1p (d := d) p u V := MemWkp.one_iff_memW1p.mp hu_W1_V
  set g_Ω : E → ℝ := chosenWeakPartial' (d := d) p i u Ω with hg_Ω_def
  set g_V : E → ℝ := chosenWeakPartial' (d := d) p i u V with hg_V_def
  have hg_V_ae_g_Ω : g_V =ᵐ[volume.restrict Ω] g_Ω := by
    have h_g_Ω_weak : DeGiorgi.HasWeakPartialDeriv i g_Ω u Ω :=
      chosenWeakPartial'_isWeakPartial_of_mem hu i
    have h_g_V_weak : DeGiorgi.HasWeakPartialDeriv i g_V u V :=
      chosenWeakPartial'_isWeakPartial_of_mem hu_V i
    have h_g_V_weak_Ω : DeGiorgi.HasWeakPartialDeriv i g_V u Ω :=
      DeGiorgi.HasWeakPartialDeriv.restrict hΩ hΩV h_g_V_weak
    have h_g_Ω_loc : LocallyIntegrable g_Ω (volume.restrict Ω) :=
      (chosenWeakPartial'_memLp_of_mem hu i).locallyIntegrable hp
    have h_g_V_loc : LocallyIntegrable g_V (volume.restrict Ω) := by
      have h_mem : MemLp g_V p (volume.restrict V) :=
        chosenWeakPartial'_memLp_of_mem hu_V i
      exact (h_mem.mono_measure (Measure.restrict_mono_set volume hΩV)).locallyIntegrable hp
    exact DeGiorgi.HasWeakPartialDeriv.ae_eq hΩ h_g_V_weak_Ω h_g_Ω_weak
      h_g_V_loc h_g_Ω_loc
  have hg_V_zero_diff : g_V =ᵐ[volume.restrict (V \ Ω)] (fun _ : E => (0 : ℝ)) := by
    have h_g_V_zero : g_V =ᵐ[volume.restrict (V \ tsupport u)]
        (fun _ : E => (0 : ℝ)) :=
      chosenWeakPartial'_ae_zero_on_sdiff_tsupport hp hV hu_V i
    exact ae_restrict_of_ae_restrict_of_subset
      (Set.diff_subset_diff_right hu_supp) h_g_V_zero
  have h_meas_Ω : MeasurableSet Ω := hΩ.measurableSet
  have h_on_Ω : g_V =ᵐ[volume.restrict Ω] Ω.indicator g_Ω := by
    have h_ind_eq : Ω.indicator g_Ω =ᵐ[volume.restrict Ω] g_Ω := by
      refine (ae_restrict_iff' h_meas_Ω).mpr ?_
      exact Filter.Eventually.of_forall fun x hx => Set.indicator_of_mem hx _
    exact hg_V_ae_g_Ω.trans h_ind_eq.symm
  have h_on_diff : g_V =ᵐ[volume.restrict (V \ Ω)] Ω.indicator g_Ω := by
    have h_ind_zero : Ω.indicator g_Ω =ᵐ[volume.restrict (V \ Ω)]
        (fun _ : E => (0 : ℝ)) := by
      have h_meas_diff : MeasurableSet (V \ Ω) := hV.measurableSet.diff h_meas_Ω
      refine (ae_restrict_iff' h_meas_diff).mpr ?_
      exact Filter.Eventually.of_forall fun x hx =>
        Set.indicator_of_notMem hx.2 _
    exact hg_V_zero_diff.trans h_ind_zero.symm
  have h_union : V = Ω ∪ (V \ Ω) := by
    ext x; constructor
    · intro hx
      by_cases hxΩ : x ∈ Ω
      · exact Or.inl hxΩ
      · exact Or.inr ⟨hx, hxΩ⟩
    · rintro (hx | ⟨hx, -⟩)
      · exact hΩV hx
      · exact hx
  rw [h_union]
  exact (ae_restrict_union_iff Ω (V \ Ω) (fun x => g_V x = Ω.indicator g_Ω x)).mpr
    ⟨h_on_Ω, h_on_diff⟩

omit [NeZero d] in
private theorem chosenWeakPartial'_indicator_aux
    {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set E} (hΩ : IsOpen Ω)
    {u : E → ℝ} (hu : DeGiorgi.MemW1p (d := d) p u Ω)
    (hu_supp : tsupport u ⊆ Ω) (hu_compact : HasCompactSupport u) (i : Fin d) :
    HasCompactSupport ((tsupport u).indicator (chosenWeakPartial' (d := d) p i u Ω))
      ∧ tsupport ((tsupport u).indicator (chosenWeakPartial' (d := d) p i u Ω)) ⊆ Ω
      ∧ (tsupport u).indicator (chosenWeakPartial' (d := d) p i u Ω)
          =ᵐ[volume.restrict Ω] chosenWeakPartial' (d := d) p i u Ω := by
  classical
  set g_Ω : E → ℝ := chosenWeakPartial' (d := d) p i u Ω with hg_Ω_def
  set g_mod : E → ℝ := (tsupport u).indicator g_Ω with hg_mod_def
  have h_tsupp_u_closed : IsClosed (tsupport u) := isClosed_tsupport _
  have h_tsupp_u_compact : IsCompact (tsupport u) := hu_compact
  have h_supp_subset : Function.support g_mod ⊆ tsupport u := by
    intro x hx
    by_contra hx_not
    exact hx (Set.indicator_of_notMem hx_not _)
  have h_tsupp_subset : tsupport g_mod ⊆ tsupport u :=
    (closure_mono h_supp_subset).trans (by rw [h_tsupp_u_closed.closure_eq])
  refine ⟨?_, ?_, ?_⟩
  · exact h_tsupp_u_compact.of_isClosed_subset (isClosed_tsupport _) h_tsupp_subset
  · exact h_tsupp_subset.trans hu_supp
  · have h_meas_tsupp : MeasurableSet (tsupport u) :=
      h_tsupp_u_closed.measurableSet
    have h_ae_tsupp : g_mod =ᵐ[volume.restrict (tsupport u)] g_Ω := by
      refine (ae_restrict_iff' h_meas_tsupp).mpr ?_
      exact Filter.Eventually.of_forall fun x hx => Set.indicator_of_mem hx _
    have h_ae_diff : g_mod =ᵐ[volume.restrict (Ω \ tsupport u)] g_Ω := by
      have h_g_Ω_zero : g_Ω =ᵐ[volume.restrict (Ω \ tsupport u)]
          (fun _ : E => (0 : ℝ)) :=
        chosenWeakPartial'_ae_zero_on_sdiff_tsupport hp hΩ hu i
      have h_g_mod_zero : g_mod =ᵐ[volume.restrict (Ω \ tsupport u)]
          (fun _ : E => (0 : ℝ)) := by
        have h_meas : MeasurableSet (Ω \ tsupport u) :=
          hΩ.measurableSet.diff h_meas_tsupp
        refine (ae_restrict_iff' h_meas).mpr ?_
        exact Filter.Eventually.of_forall fun x hx =>
          Set.indicator_of_notMem hx.2 _
      exact h_g_mod_zero.trans h_g_Ω_zero.symm
    have h_union : Ω = tsupport u ∪ (Ω \ tsupport u) := by
      ext x; constructor
      · intro hx
        by_cases hx' : x ∈ tsupport u
        · exact Or.inl hx'
        · exact Or.inr ⟨hx, hx'⟩
      · rintro (hx | ⟨hx, -⟩)
        · exact hu_supp hx
        · exact hx
    rw [h_union]
    exact (ae_restrict_union_iff (tsupport u) (Ω \ tsupport u)
      (fun x => g_mod x = g_Ω x)).mpr ⟨h_ae_tsupp, h_ae_diff⟩

omit [NeZero d] in
private theorem indicator_ae_congr_of_ae_restrict
    {Ω V : Set E} (hΩ : IsOpen Ω) (hV : IsOpen V) (hΩV : Ω ⊆ V)
    {f g : E → ℝ} (hfg : f =ᵐ[volume.restrict Ω] g) :
    Ω.indicator f =ᵐ[volume.restrict V] Ω.indicator g := by
  classical
  have h_meas_Ω : MeasurableSet Ω := hΩ.measurableSet
  have h_on_Ω : Ω.indicator f =ᵐ[volume.restrict Ω] Ω.indicator g := by
    have hf_eq : Ω.indicator f =ᵐ[volume.restrict Ω] f :=
      (ae_restrict_iff' h_meas_Ω).mpr
        (Filter.Eventually.of_forall fun x hx => Set.indicator_of_mem hx _)
    have hg_eq : Ω.indicator g =ᵐ[volume.restrict Ω] g :=
      (ae_restrict_iff' h_meas_Ω).mpr
        (Filter.Eventually.of_forall fun x hx => Set.indicator_of_mem hx _)
    exact hf_eq.trans (hfg.trans hg_eq.symm)
  have h_on_diff : Ω.indicator f =ᵐ[volume.restrict (V \ Ω)] Ω.indicator g := by
    have h_meas_diff : MeasurableSet (V \ Ω) := hV.measurableSet.diff h_meas_Ω
    refine (ae_restrict_iff' h_meas_diff).mpr ?_
    refine Filter.Eventually.of_forall fun x hx => ?_
    rw [Set.indicator_of_notMem hx.2, Set.indicator_of_notMem hx.2]
  have h_union : V = Ω ∪ (V \ Ω) := by
    ext x; constructor
    · intro hx
      by_cases hxΩ : x ∈ Ω
      · exact Or.inl hxΩ
      · exact Or.inr ⟨hx, hxΩ⟩
    · rintro (hx | ⟨hx, -⟩)
      · exact hΩV hx
      · exact hx
  rw [h_union]
  exact (ae_restrict_union_iff Ω (V \ Ω)
    (fun x => Ω.indicator f x = Ω.indicator g x)).mpr ⟨h_on_Ω, h_on_diff⟩

omit [NeZero d] in
private theorem iterWeakPartial_extend_zero_ae
    {j : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ⊤) {Ω V : Set E}
    (hΩ : IsOpen Ω) (hV : IsOpen V) (hΩV : Ω ⊆ V)
    (α : Fin j → Fin d) {u : E → ℝ} (hu : MemWkp (d := d) j p u Ω)
    (hu_supp : tsupport u ⊆ Ω) (hu_compact : HasCompactSupport u) :
    iterWeakPartial (d := d) p j α u V
      =ᵐ[volume.restrict V]
      Ω.indicator (iterWeakPartial (d := d) p j α u Ω) := by
  classical
  induction j generalizing u with
  | zero =>
      simp only [iterWeakPartial_zero]
      have h_meas_Ω : MeasurableSet Ω := hΩ.measurableSet
      have h_on_Ω : u =ᵐ[volume.restrict Ω] Ω.indicator u :=
        (ae_restrict_iff' h_meas_Ω).mpr
          (Filter.Eventually.of_forall fun x hx => (Set.indicator_of_mem hx _).symm)
      have h_on_diff : u =ᵐ[volume.restrict (V \ Ω)] Ω.indicator u := by
        have h_meas_diff : MeasurableSet (V \ Ω) := hV.measurableSet.diff h_meas_Ω
        refine (ae_restrict_iff' h_meas_diff).mpr ?_
        refine Filter.Eventually.of_forall fun x hx => ?_
        have hx_not_supp : x ∉ tsupport u := fun h => hx.2 (hu_supp h)
        rw [Set.indicator_of_notMem hx.2,
          image_eq_zero_of_notMem_tsupport hx_not_supp]
      have h_union : V = Ω ∪ (V \ Ω) := by
        ext x; constructor
        · intro hx
          by_cases hxΩ : x ∈ Ω
          · exact Or.inl hxΩ
          · exact Or.inr ⟨hx, hxΩ⟩
        · rintro (hx | ⟨hx, -⟩)
          · exact hΩV hx
          · exact hx
      rw [h_union]
      exact (ae_restrict_union_iff Ω (V \ Ω)
        (fun x => u x = Ω.indicator u x)).mpr ⟨h_on_Ω, h_on_diff⟩
  | succ j ih =>
      rw [iterWeakPartial_succ, iterWeakPartial_succ]
      have hu_W1_Ω : DeGiorgi.MemW1p (d := d) p u Ω := hu.memW1p
      set g_Ω : E → ℝ := chosenWeakPartial' (d := d) p (α 0) u Ω with hg_Ω_def
      set g_V : E → ℝ := chosenWeakPartial' (d := d) p (α 0) u V with hg_V_def
      obtain ⟨hw_compact, hw_supp, hw_ae⟩ :=
        chosenWeakPartial'_indicator_aux (d := d) hp hΩ hu_W1_Ω hu_supp hu_compact (α 0)
      set w : E → ℝ := (tsupport u).indicator g_Ω with hw_def
      have hg_Ω_mem : MemWkp (d := d) j p g_Ω Ω := hu.chosenWeakPartial_mem (α 0)
      have hw_mem : MemWkp (d := d) j p w Ω :=
        (MemWkp_congr_ae (d := d) hp hΩ hw_ae).mpr hg_Ω_mem
      have h_chosen_ext : g_V =ᵐ[volume.restrict V] Ω.indicator g_Ω :=
        chosenWeakPartial'_extend_zero_ae (d := d) hp hp_top hΩ hV hΩV
          hu_W1_Ω hu_supp hu_compact (α 0)
      have h_w_ind_ae : Ω.indicator w =ᵐ[volume.restrict V] Ω.indicator g_Ω :=
        indicator_ae_congr_of_ae_restrict hΩ hV hΩV hw_ae
      have h_chosen_ext_w : g_V =ᵐ[volume.restrict V] Ω.indicator w :=
        h_chosen_ext.trans h_w_ind_ae.symm
      have h_ind_w_eq_w : Ω.indicator w = w := by
        funext x
        by_cases hxΩ : x ∈ Ω
        · rw [Set.indicator_of_mem hxΩ]
        · have hx_not : x ∉ tsupport w := fun h => hxΩ (hw_supp h)
          rw [Set.indicator_of_notMem hxΩ,
            image_eq_zero_of_notMem_tsupport hx_not]
      rw [h_ind_w_eq_w] at h_chosen_ext_w
      have h_iter_input :
          iterWeakPartial (d := d) p j (fun t : Fin j => α t.succ) g_V V
            =ᵐ[volume.restrict V]
          iterWeakPartial (d := d) p j (fun t : Fin j => α t.succ) w V :=
        iterWeakPartial_ae_congr (d := d) hp hV j (fun t : Fin j => α t.succ)
          h_chosen_ext_w
      have h_iter_w :
          iterWeakPartial (d := d) p j (fun t : Fin j => α t.succ) w V
            =ᵐ[volume.restrict V]
          Ω.indicator (iterWeakPartial (d := d) p j (fun t : Fin j => α t.succ) w Ω) :=
        ih (fun t : Fin j => α t.succ) hw_mem hw_supp hw_compact
      have h_iter_wΩ :
          iterWeakPartial (d := d) p j (fun t : Fin j => α t.succ) w Ω
            =ᵐ[volume.restrict Ω]
          iterWeakPartial (d := d) p j (fun t : Fin j => α t.succ) g_Ω Ω :=
        iterWeakPartial_ae_congr (d := d) hp hΩ j (fun t : Fin j => α t.succ) hw_ae
      have h_ind_iter :
          Ω.indicator (iterWeakPartial (d := d) p j (fun t : Fin j => α t.succ) w Ω)
            =ᵐ[volume.restrict V]
          Ω.indicator (iterWeakPartial (d := d) p j (fun t : Fin j => α t.succ) g_Ω Ω) :=
        indicator_ae_congr_of_ae_restrict hΩ hV hΩV h_iter_wΩ
      exact (h_iter_input.trans h_iter_w).trans h_ind_iter

omit [NeZero d] in
theorem wkpNorm_extend_zero
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ⊤) {Ω V : Set E}
    (hΩ : IsOpen Ω) (hV : IsOpen V) (hΩV : Ω ⊆ V)
    {u : E → ℝ} (hu : MemWkp (d := d) k p u Ω)
    (hu_supp : tsupport u ⊆ Ω) (hu_compact : HasCompactSupport u) :
    iteratedWeakSobolevNorm (d := d) k p u V = iteratedWeakSobolevNorm (d := d) k p u Ω := by
  classical
  unfold iteratedWeakSobolevNorm
  refine Finset.sum_congr rfl ?_
  intro j hj
  refine Finset.sum_congr rfl ?_
  intro α _
  have hj_le : j ≤ k := by
    rw [Finset.mem_range] at hj; omega
  have h_uWj : MemWkp (d := d) j p u Ω := MemWkp.le_of_le hj_le hu
  have h_iter_ae :=
    iterWeakPartial_extend_zero_ae (d := d) hp hp_top hΩ hV hΩV α
      h_uWj hu_supp hu_compact
  rw [eLpNorm_congr_ae h_iter_ae]
  have h_meas_Ω : MeasurableSet Ω := hΩ.measurableSet
  rw [eLpNorm_indicator_eq_eLpNorm_restrict h_meas_Ω,
    Measure.restrict_restrict_of_subset hΩV]

section SupportPromotion

theorem wkpNorm_le_of_memWkp_precompact_of_ae_zero_off_compact
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ⊤)
    {Ω Ω' K : Set E} {u : E → ℝ}
    (hΩ_open : IsOpen Ω) (hΩ'_open : IsOpen Ω')
    (hK_compact : IsCompact K) (hKΩ' : K ⊆ Ω')
    (hΩ'_cl : closure Ω' ⊆ Ω)
    (hu_ae_zero : u =ᵐ[(volume : Measure E).restrict (Ω \ K)] 0)
    (hu_precompact : MemWkp (d := d) k p u Ω') :
    ∃ K_prom : ℝ, 0 < K_prom ∧
      iteratedWeakSobolevNorm (d := d) k p u Ω ≤
        ENNReal.ofReal K_prom * iteratedWeakSobolevNorm (d := d) k p u Ω' := by
  classical
  have hΩ'Ω : Ω' ⊆ Ω := subset_closure.trans hΩ'_cl
  obtain ⟨δ, χ, hδ_pos, _hδ_sub, hχ_smooth, hχ_compact, _hχ_range,
      hχ_one, hχ_supp⟩ :=
    exists_smooth_cutoff_with_neighborhood (d := d) hK_compact hΩ'_open hKΩ'
  set N : Set E := Metric.cthickening δ K with hN_def
  have hN_closed : IsClosed N := Metric.isClosed_cthickening
  have hN_meas : MeasurableSet N := hN_closed.measurableSet
  have hK_sub_N : K ⊆ N := Metric.self_subset_cthickening K
  set v : E → ℝ := fun x => χ x * u x with hv_def
  obtain ⟨C, hC_nn, hC_bound⟩ :=
    exists_uniform_iteratedFDeriv_bound_of_smooth_compactSupport (d := d)
      hχ_smooth hχ_compact k
  obtain ⟨K_prom, hK_prom_pos, hK_prom_bound⟩ :=
    wkpNorm_smul_smooth_bounded_le (d := d) k hp hp_top hΩ'_open hχ_smooth hC_nn
      (fun j hj x hx => hC_bound x j hj)
  refine ⟨K_prom, hK_prom_pos, ?_⟩
  have hv_memWkp_Ω' : MemWkp (d := d) k p v Ω' :=
    MemWkp.smul_smooth_bounded (d := d) k hp hΩ'_open hχ_smooth
      (fun j _hj x _hx => hC_bound x j _hj) hu_precompact
  have hv_tsupp : tsupport v ⊆ Ω' :=
    (tsupport_smul_subset_left χ u).trans hχ_supp
  have hv_compact : HasCompactSupport v := hχ_compact.mul_right
  have hv_ae_eq_u : v =ᵐ[(volume : Measure E).restrict Ω] u := by
    have h_split : Ω = (Ω ∩ N) ∪ (Ω \ N) := by
      rw [Set.inter_union_diff]
    have h_on_inter : v =ᵐ[(volume : Measure E).restrict (Ω ∩ N)] u := by
      refine (ae_restrict_iff' (hΩ_open.measurableSet.inter hN_meas)).mpr ?_
      refine Filter.Eventually.of_forall fun x hx => ?_
      simp only [hv_def, hχ_one x hx.2, one_mul]
    have h_on_diff : v =ᵐ[(volume : Measure E).restrict (Ω \ N)] u := by
      have h_sub : Ω \ N ⊆ Ω \ K := Set.diff_subset_diff_right hK_sub_N
      have hu_zero_diff : u =ᵐ[(volume : Measure E).restrict (Ω \ N)] 0 :=
        hu_ae_zero.filter_mono
          (ae_mono (Measure.restrict_mono_set volume h_sub))
      filter_upwards [hu_zero_diff] with x hx
      simp only [hv_def, hx, Pi.zero_apply, mul_zero]
    have h_union : v =ᵐ[(volume : Measure E).restrict ((Ω ∩ N) ∪ (Ω \ N))] u := by
      rw [Filter.EventuallyEq, ae_restrict_union_eq]
      exact ⟨h_on_inter, h_on_diff⟩
    rwa [← h_split] at h_union
  calc
    iteratedWeakSobolevNorm (d := d) k p u Ω
        = iteratedWeakSobolevNorm (d := d) k p v Ω :=
          (wkpNorm_congr_ae (d := d) hp hΩ_open hv_ae_eq_u).symm
    _ = iteratedWeakSobolevNorm (d := d) k p v Ω' :=
          wkpNorm_extend_zero (d := d) hp hp_top hΩ'_open hΩ_open hΩ'Ω
            hv_memWkp_Ω' hv_tsupp hv_compact
    _ ≤ ENNReal.ofReal K_prom * iteratedWeakSobolevNorm (d := d) k p u Ω' :=
          hK_prom_bound hu_precompact

theorem wkpNorm_le_of_memWkp_precompact_of_ae_zero_off_compact_uniform
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ⊤)
    {Ω Ω' K : Set E}
    (hΩ_open : IsOpen Ω) (hΩ'_open : IsOpen Ω')
    (hK_compact : IsCompact K) (hKΩ' : K ⊆ Ω')
    (hΩ'_cl : closure Ω' ⊆ Ω) :
    ∃ K_prom : ℝ, 0 < K_prom ∧
      ∀ u : E → ℝ,
        u =ᵐ[(volume : Measure E).restrict (Ω \ K)] 0 →
        MemWkp (d := d) k p u Ω' →
        iteratedWeakSobolevNorm (d := d) k p u Ω ≤
          ENNReal.ofReal K_prom * iteratedWeakSobolevNorm (d := d) k p u Ω' := by
  classical
  have hΩ'Ω : Ω' ⊆ Ω := subset_closure.trans hΩ'_cl
  obtain ⟨δ, χ, hδ_pos, _hδ_sub, hχ_smooth, hχ_compact, _hχ_range,
      hχ_one, hχ_supp⟩ :=
    exists_smooth_cutoff_with_neighborhood (d := d) hK_compact hΩ'_open hKΩ'
  set N : Set E := Metric.cthickening δ K with hN_def
  have hN_closed : IsClosed N := Metric.isClosed_cthickening
  have hN_meas : MeasurableSet N := hN_closed.measurableSet
  have hK_sub_N : K ⊆ N := Metric.self_subset_cthickening K
  obtain ⟨C, hC_nn, hC_bound⟩ :=
    exists_uniform_iteratedFDeriv_bound_of_smooth_compactSupport (d := d)
      hχ_smooth hχ_compact k
  obtain ⟨K_prom, hK_prom_pos, hK_prom_bound⟩ :=
    wkpNorm_smul_smooth_bounded_le (d := d) k hp hp_top hΩ'_open hχ_smooth hC_nn
      (fun j hj x hx => hC_bound x j hj)
  refine ⟨K_prom, hK_prom_pos, fun u hu_ae_zero hu_precompact => ?_⟩
  set v : E → ℝ := fun x => χ x * u x with hv_def
  have hv_memWkp_Ω' : MemWkp (d := d) k p v Ω' :=
    MemWkp.smul_smooth_bounded (d := d) k hp hΩ'_open hχ_smooth
      (fun j _hj x _hx => hC_bound x j _hj) hu_precompact
  have hv_tsupp : tsupport v ⊆ Ω' :=
    (tsupport_smul_subset_left χ u).trans hχ_supp
  have hv_compact : HasCompactSupport v := hχ_compact.mul_right
  have hv_ae_eq_u : v =ᵐ[(volume : Measure E).restrict Ω] u := by
    have h_split : Ω = (Ω ∩ N) ∪ (Ω \ N) := by
      rw [Set.inter_union_diff]
    have h_on_inter : v =ᵐ[(volume : Measure E).restrict (Ω ∩ N)] u := by
      refine (ae_restrict_iff' (hΩ_open.measurableSet.inter hN_meas)).mpr ?_
      refine Filter.Eventually.of_forall fun x hx => ?_
      simp only [hv_def, hχ_one x hx.2, one_mul]
    have h_on_diff : v =ᵐ[(volume : Measure E).restrict (Ω \ N)] u := by
      have h_sub : Ω \ N ⊆ Ω \ K := Set.diff_subset_diff_right hK_sub_N
      have hu_zero_diff : u =ᵐ[(volume : Measure E).restrict (Ω \ N)] 0 :=
        hu_ae_zero.filter_mono
          (ae_mono (Measure.restrict_mono_set volume h_sub))
      filter_upwards [hu_zero_diff] with x hx
      simp only [hv_def, hx, Pi.zero_apply, mul_zero]
    have h_union : v =ᵐ[(volume : Measure E).restrict ((Ω ∩ N) ∪ (Ω \ N))] u := by
      rw [Filter.EventuallyEq, ae_restrict_union_eq]
      exact ⟨h_on_inter, h_on_diff⟩
    rwa [← h_split] at h_union
  calc
    iteratedWeakSobolevNorm (d := d) k p u Ω
        = iteratedWeakSobolevNorm (d := d) k p v Ω :=
          (wkpNorm_congr_ae (d := d) hp hΩ_open hv_ae_eq_u).symm
    _ = iteratedWeakSobolevNorm (d := d) k p v Ω' :=
          wkpNorm_extend_zero (d := d) hp hp_top hΩ'_open hΩ_open hΩ'Ω
            hv_memWkp_Ω' hv_tsupp hv_compact
    _ ≤ ENNReal.ofReal K_prom * iteratedWeakSobolevNorm (d := d) k p u Ω' :=
          hK_prom_bound hu_precompact

end SupportPromotion

end Euclidean
end Sobolev
end Analysis
end DifferentialGeometry
