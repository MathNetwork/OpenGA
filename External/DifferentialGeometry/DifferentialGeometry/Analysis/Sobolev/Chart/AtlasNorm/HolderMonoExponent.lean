import DifferentialGeometry.Analysis.Sobolev.Manifold.IteratedSobolevEmbedding
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp


noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Chart

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩

namespace HolderPerChart

variable [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]

open DifferentialGeometry.Analysis.Sobolev.Euclidean

private noncomputable def K (α : M) :
    Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
  toEuclidean ''
    ((extChartAt I α) ''
      (tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) : M → ℝ)))

omit [I.Boundaryless] in
private lemma K_isCompact [CompactSpace M] (α : M) :
    IsCompact (K (I := I) (M := M) α) :=
  (ChartTower.toEuclidean_extChartAt_tsupport_pou_compact_subset
    (I := I) (M := M) α).1

omit [I.Boundaryless] in
private lemma K_isClosed [CompactSpace M] (α : M) :
    IsClosed (K (I := I) (M := M) α) :=
  (K_isCompact (I := I) (M := M) α).isClosed

omit [I.Boundaryless] in
private lemma K_meas [CompactSpace M] (α : M) :
    MeasurableSet (K (I := I) (M := M) α) :=
  (K_isClosed (I := I) (M := M) α).measurableSet

omit [I.Boundaryless] in
private lemma K_volume_lt_top [CompactSpace M] (α : M) :
    MeasureTheory.volume (K (I := I) (M := M) α) ≠ ⊤ :=
  (K_isCompact (I := I) (M := M) α).measure_lt_top.ne

omit [I.Boundaryless] in
private lemma K_subset_target [CompactSpace M] (α : M) :
    K (I := I) (M := M) α ⊆ chartTargetEuclid (I := I) (M := M) α :=
  (ChartTower.toEuclidean_extChartAt_tsupport_pou_compact_subset
    (I := I) (M := M) α).2

private noncomputable def fRaw (α : M) (u : M → ℝ) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
  chartPushedRaw (I := I) (M := M) α
    (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) x * u x)

omit [I.Boundaryless] in
private lemma fRaw_tsupport_subset_K [CompactSpace M] (α : M) (u : M → ℝ) :
    tsupport (fRaw (I := I) (M := M) α u) ⊆ K (I := I) (M := M) α :=
  ChartTower.tsupport_chartPushedRaw_pou_mul_subset (I := I) (M := M) α u

omit [I.Boundaryless] in
private lemma chartPushed_ae_eq_fRaw [CompactSpace M] (α : M) (u : M → ℝ) :
    chartPushed (I := I) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u
      =ᵐ[(MeasureTheory.volume :
            MeasureTheory.Measure
              (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      fRaw (I := I) (M := M) α u :=
  chartPushed_eq_chartPushedRaw_pou_ae (I := I) (M := M)
    (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u

private lemma iterWeakPartial_cross_exponent_ae_eq
    {d : ℕ} [NeZero d]
    {p p' : ℝ≥0∞} (hp_one : 1 ≤ p) (hp'_one : 1 ≤ p')
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ_open : IsOpen Ω)
    {j : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hfp : MemWkp (d := d) j p f Ω) (hfp' : MemWkp (d := d) j p' f Ω)
    (β : Fin j → Fin d) :
    iterWeakPartial (d := d) p j β f Ω
      =ᵐ[(MeasureTheory.volume :
            MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))).restrict Ω]
      iterWeakPartial (d := d) p' j β f Ω := by
  induction j generalizing f with
  | zero =>
      simp only [iterWeakPartial_zero]
      exact Filter.EventuallyEq.rfl
  | succ j ih =>
      rw [iterWeakPartial_succ, iterWeakPartial_succ]
      have hfp_W1 : DeGiorgi.MemW1p p f Ω := by
        rw [MemWkp_succ] at hfp; exact hfp.1
      have hfp'_W1 : DeGiorgi.MemW1p p' f Ω := by
        rw [MemWkp_succ] at hfp'; exact hfp'.1
      have h_chosen_ae : chosenWeakPartial' (d := d) p (β 0) f Ω
          =ᵐ[(MeasureTheory.volume :
                MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))).restrict Ω]
          chosenWeakPartial' (d := d) p' (β 0) f Ω :=
        DifferentialGeometry.Analysis.Sobolev.Chart.EuclideanIterated.chosenWeakPartial'_cross_exponent_ae_eq
          (d := d) hp_one hp'_one hΩ_open hfp_W1 hfp'_W1 (β 0)
      have hg_memWkp_p : MemWkp (d := d) j p
          (chosenWeakPartial' (d := d) p (β 0) f Ω) Ω := by
        rw [MemWkp_succ] at hfp; exact hfp.2 (β 0)
      have hg_memWkp_p' : MemWkp (d := d) j p'
          (chosenWeakPartial' (d := d) p' (β 0) f Ω) Ω := by
        rw [MemWkp_succ] at hfp'; exact hfp'.2 (β 0)
      have hg_memWkp_p_of_p' : MemWkp (d := d) j p
          (chosenWeakPartial' (d := d) p' (β 0) f Ω) Ω :=
        (MemWkp_congr_ae (d := d) hp_one hΩ_open h_chosen_ae).mp hg_memWkp_p
      have h_bridge1 : iterWeakPartial (d := d) p j (fun i : Fin j => β i.succ)
            (chosenWeakPartial' (d := d) p (β 0) f Ω) Ω
          =ᵐ[(MeasureTheory.volume :
                MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))).restrict Ω]
          iterWeakPartial (d := d) p j (fun i : Fin j => β i.succ)
            (chosenWeakPartial' (d := d) p' (β 0) f Ω) Ω :=
        iterWeakPartial_ae_congr (d := d) hp_one hΩ_open j
          (fun i : Fin j => β i.succ) h_chosen_ae
      have h_bridge2 := ih (f := chosenWeakPartial' (d := d) p' (β 0) f Ω)
        hg_memWkp_p_of_p' hg_memWkp_p' (fun i : Fin j => β i.succ)
      exact h_bridge1.trans h_bridge2

private lemma iterWeakPartial_ae_zero_on_sdiff_K
    {d : ℕ} [NeZero d]
    {p : ℝ≥0∞} (hp_one : 1 ≤ p)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ_open : IsOpen Ω)
    {K : Set (EuclideanSpace ℝ (Fin d))} (hK_closed : IsClosed K)
    {j : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf_supp : tsupport f ⊆ K)
    (hf_mem : MemWkp (d := d) j p f Ω) (β : Fin j → Fin d) :
    iterWeakPartial (d := d) p j β f Ω
      =ᵐ[(MeasureTheory.volume :
            MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))).restrict (Ω \ K)]
      (fun _ => (0 : ℝ)) := by
  induction j generalizing f with
  | zero =>
      simp only [iterWeakPartial_zero]
      have hKmeas : MeasurableSet K := hK_closed.measurableSet
      have hΩmeas : MeasurableSet Ω := hΩ_open.measurableSet
      refine (ae_restrict_iff' (hΩmeas.diff hKmeas)).mpr ?_
      refine Filter.Eventually.of_forall ?_
      intro x hx
      have hx_notK : x ∉ K := hx.2
      have hx_notsupp : x ∉ tsupport f := fun h => hx_notK (hf_supp h)
      exact image_eq_zero_of_notMem_tsupport hx_notsupp
  | succ j ih =>
      rw [iterWeakPartial_succ]
      have hfW1p : DeGiorgi.MemW1p p f Ω := by
        rw [MemWkp_succ] at hf_mem; exact hf_mem.1
      have h_chosen_mem : MemWkp (d := d) j p
          (chosenWeakPartial' (d := d) p (β 0) f Ω) Ω := by
        rw [MemWkp_succ] at hf_mem; exact hf_mem.2 (β 0)
      have h_partial_ae_zero_off_supp :
          chosenWeakPartial' (d := d) p (β 0) f Ω
            =ᵐ[(MeasureTheory.volume :
                  MeasureTheory.Measure
                    (EuclideanSpace ℝ (Fin d))).restrict (Ω \ tsupport f)]
            (fun _ => (0 : ℝ)) :=
        chosenWeakPartial'_ae_zero_on_sdiff_tsupport (d := d) hp_one hΩ_open
          hfW1p (β 0)
      have h_subset : Ω \ K ⊆ Ω \ tsupport f := by
        intro x hx
        refine ⟨hx.1, ?_⟩
        intro hxsupp
        exact hx.2 (hf_supp hxsupp)
      have h_partial_ae_zero_off_K :
          chosenWeakPartial' (d := d) p (β 0) f Ω
            =ᵐ[(MeasureTheory.volume :
                  MeasureTheory.Measure
                    (EuclideanSpace ℝ (Fin d))).restrict (Ω \ K)]
            (fun _ => (0 : ℝ)) :=
        MeasureTheory.ae_restrict_of_ae_restrict_of_subset h_subset
          h_partial_ae_zero_off_supp
      have hKmeas : MeasurableSet K := hK_closed.measurableSet
      set g : EuclideanSpace ℝ (Fin d) → ℝ :=
        chosenWeakPartial' (d := d) p (β 0) f Ω with hg_def
      set gK : EuclideanSpace ℝ (Fin d) → ℝ := K.indicator g with hgK_def
      have h_gK_supp : tsupport gK ⊆ K := by
        have h_supp_sub : Function.support gK ⊆ K := by
          intro x hx
          by_contra hxK
          exact hx (Set.indicator_of_notMem hxK _)
        calc tsupport gK = closure (Function.support gK) := rfl
          _ ⊆ closure K := closure_mono h_supp_sub
          _ = K := hK_closed.closure_eq
      have h_g_eq_gK : g =ᵐ[(MeasureTheory.volume :
            MeasureTheory.Measure
              (EuclideanSpace ℝ (Fin d))).restrict Ω] gK := by
        rw [hgK_def]
        have hΩmeas : MeasurableSet Ω := hΩ_open.measurableSet
        have hΩKmeas : MeasurableSet (Ω \ K) := hΩmeas.diff hKmeas
        have h_partial_zero_off_K :
            ∀ᵐ x ∂((MeasureTheory.volume :
                MeasureTheory.Measure
                  (EuclideanSpace ℝ (Fin d))).restrict (Ω \ K)), g x = 0 := by
          filter_upwards [h_partial_ae_zero_off_K] with x hx
          simpa using hx
        rw [(MeasureTheory.ae_restrict_iff' hΩKmeas)] at h_partial_zero_off_K
        rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' hΩmeas]
        filter_upwards [h_partial_zero_off_K] with x hx hx_Ω
        by_cases h_in_K : x ∈ K
        · simp [Set.indicator_of_mem h_in_K]
        · have hx_diff : x ∈ Ω \ K := ⟨hx_Ω, h_in_K⟩
          have hgx : g x = 0 := hx hx_diff
          simp [Set.indicator_of_notMem h_in_K, hgx]
      have h_gK_memWkp : MemWkp (d := d) j p gK Ω :=
        (MemWkp_congr_ae (d := d) hp_one hΩ_open h_g_eq_gK).mp h_chosen_mem
      have h_iter_gK : iterWeakPartial (d := d) p j
            (fun i : Fin j => β i.succ) gK Ω
          =ᵐ[(MeasureTheory.volume :
                MeasureTheory.Measure
                  (EuclideanSpace ℝ (Fin d))).restrict (Ω \ K)]
          (fun _ => (0 : ℝ)) :=
        ih (f := gK) h_gK_supp h_gK_memWkp (fun i : Fin j => β i.succ)
      have h_iter_g_vs_gK_onΩ : iterWeakPartial (d := d) p j
            (fun i : Fin j => β i.succ) g Ω
          =ᵐ[(MeasureTheory.volume :
                MeasureTheory.Measure
                  (EuclideanSpace ℝ (Fin d))).restrict Ω]
          iterWeakPartial (d := d) p j (fun i : Fin j => β i.succ) gK Ω :=
        iterWeakPartial_ae_congr (d := d) hp_one hΩ_open j
          (fun i : Fin j => β i.succ) h_g_eq_gK
      have h_iter_g_vs_gK_onΩK : iterWeakPartial (d := d) p j
            (fun i : Fin j => β i.succ) g Ω
          =ᵐ[(MeasureTheory.volume :
                MeasureTheory.Measure
                  (EuclideanSpace ℝ (Fin d))).restrict (Ω \ K)]
          iterWeakPartial (d := d) p j (fun i : Fin j => β i.succ) gK Ω :=
        MeasureTheory.ae_restrict_of_ae_restrict_of_subset
          (s := Ω \ K) (t := Ω) (Set.diff_subset) h_iter_g_vs_gK_onΩ
      exact h_iter_g_vs_gK_onΩK.trans h_iter_gK

private lemma iterWeakPartial_ae_eq_indicator
    {d : ℕ} [NeZero d]
    {p : ℝ≥0∞} (hp_one : 1 ≤ p)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ_open : IsOpen Ω)
    {K : Set (EuclideanSpace ℝ (Fin d))} (hK_closed : IsClosed K)
    {j : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf_supp : tsupport f ⊆ K)
    (hf_mem : MemWkp (d := d) j p f Ω) (β : Fin j → Fin d) :
    iterWeakPartial (d := d) p j β f Ω
      =ᵐ[(MeasureTheory.volume :
            MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))).restrict Ω]
      K.indicator (iterWeakPartial (d := d) p j β f Ω) := by
  have hKmeas : MeasurableSet K := hK_closed.measurableSet
  have hΩmeas : MeasurableSet Ω := hΩ_open.measurableSet
  have hΩKmeas : MeasurableSet (Ω \ K) := hΩmeas.diff hKmeas
  have h_zero_off : iterWeakPartial (d := d) p j β f Ω
      =ᵐ[(MeasureTheory.volume :
            MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))).restrict (Ω \ K)]
      (fun _ => (0 : ℝ)) :=
    iterWeakPartial_ae_zero_on_sdiff_K (d := d) hp_one hΩ_open hK_closed
      hf_supp hf_mem β
  have h_zero_off' : ∀ᵐ x ∂((MeasureTheory.volume :
        MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))).restrict (Ω \ K)),
      iterWeakPartial (d := d) p j β f Ω x = 0 := by
    filter_upwards [h_zero_off] with x hx
    simpa using hx
  rw [MeasureTheory.ae_restrict_iff' hΩKmeas] at h_zero_off'
  rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' hΩmeas]
  filter_upwards [h_zero_off'] with x hx hx_Ω
  by_cases h_in_K : x ∈ K
  · simp [Set.indicator_of_mem h_in_K]
  · have hx_diff : x ∈ Ω \ K := ⟨hx_Ω, h_in_K⟩
    have hfx : iterWeakPartial (d := d) p j β f Ω x = 0 := hx hx_diff
    simp [Set.indicator_of_notMem h_in_K, hfx]

private lemma eLpNorm_iterWeakPartial_mono_exponent
    {d : ℕ} [NeZero d]
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ_open : IsOpen Ω)
    {K : Set (EuclideanSpace ℝ (Fin d))} (hK_closed : IsClosed K)
    (hK_subset : K ⊆ Ω)
    {p p' : ℝ≥0∞} (hp_one : 1 ≤ p) (hp'_one : 1 ≤ p')
    (hp'_le_p : p' ≤ p)
    {k : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hfp : MemWkp (d := d) k p f Ω) (hfp' : MemWkp (d := d) k p' f Ω)
    (hf_supp : tsupport f ⊆ K)
    {j : ℕ} (hjk : j ≤ k) (β : Fin j → Fin d) :
    eLpNorm (iterWeakPartial (d := d) p' j β f Ω) p'
        ((MeasureTheory.volume :
            MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))).restrict Ω) ≤
      MeasureTheory.volume K ^ (1 / p'.toReal - 1 / p.toReal) *
        eLpNorm (iterWeakPartial (d := d) p j β f Ω) p
          ((MeasureTheory.volume :
              MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))).restrict Ω) := by
  have hKmeas : MeasurableSet K := hK_closed.measurableSet
  have hfp_j : MemWkp (d := d) j p f Ω := MemWkp.le_of_le hjk hfp
  have hfp'_j : MemWkp (d := d) j p' f Ω := MemWkp.le_of_le hjk hfp'
  have h_iter_cross : iterWeakPartial (d := d) p' j β f Ω
      =ᵐ[(MeasureTheory.volume :
            MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))).restrict Ω]
      iterWeakPartial (d := d) p j β f Ω :=
    (iterWeakPartial_cross_exponent_ae_eq (d := d) hp_one hp'_one hΩ_open
      hfp_j hfp'_j β).symm
  have h_eq1 : eLpNorm (iterWeakPartial (d := d) p' j β f Ω) p'
        ((MeasureTheory.volume :
            MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))).restrict Ω) =
      eLpNorm (iterWeakPartial (d := d) p j β f Ω) p'
        ((MeasureTheory.volume :
            MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))).restrict Ω) :=
    eLpNorm_congr_ae h_iter_cross
  rw [h_eq1]
  have h_iter_ae_eq_indicator : iterWeakPartial (d := d) p j β f Ω
      =ᵐ[(MeasureTheory.volume :
            MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))).restrict Ω]
      K.indicator (iterWeakPartial (d := d) p j β f Ω) :=
    iterWeakPartial_ae_eq_indicator (d := d) hp_one hΩ_open hK_closed
      hf_supp hfp_j β
  have h_eq2 : eLpNorm (iterWeakPartial (d := d) p j β f Ω) p'
        ((MeasureTheory.volume :
            MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))).restrict Ω) =
      eLpNorm (K.indicator (iterWeakPartial (d := d) p j β f Ω)) p'
        ((MeasureTheory.volume :
            MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))).restrict Ω) :=
    eLpNorm_congr_ae h_iter_ae_eq_indicator
  have h_eq3 : eLpNorm (iterWeakPartial (d := d) p j β f Ω) p
        ((MeasureTheory.volume :
            MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))).restrict Ω) =
      eLpNorm (K.indicator (iterWeakPartial (d := d) p j β f Ω)) p
        ((MeasureTheory.volume :
            MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))).restrict Ω) :=
    eLpNorm_congr_ae h_iter_ae_eq_indicator
  rw [h_eq2, h_eq3]
  have h_indic_p' :
      eLpNorm (K.indicator (iterWeakPartial (d := d) p j β f Ω)) p'
        ((MeasureTheory.volume :
            MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))).restrict Ω) =
      eLpNorm (iterWeakPartial (d := d) p j β f Ω) p'
        (((MeasureTheory.volume :
            MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))).restrict Ω).restrict K) :=
    eLpNorm_indicator_eq_eLpNorm_restrict hKmeas
  have h_indic_p :
      eLpNorm (K.indicator (iterWeakPartial (d := d) p j β f Ω)) p
        ((MeasureTheory.volume :
            MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))).restrict Ω) =
      eLpNorm (iterWeakPartial (d := d) p j β f Ω) p
        (((MeasureTheory.volume :
            MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))).restrict Ω).restrict K) :=
    eLpNorm_indicator_eq_eLpNorm_restrict hKmeas
  rw [h_indic_p', h_indic_p]
  have h_meas_eq :
      ((MeasureTheory.volume :
          MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))).restrict Ω).restrict K =
      (MeasureTheory.volume :
          MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))).restrict K := by
    rw [Measure.restrict_restrict hKmeas]
    congr 1
    exact Set.inter_eq_left.mpr hK_subset
  rw [h_meas_eq]
  have h_aem : AEStronglyMeasurable (iterWeakPartial (d := d) p j β f Ω)
      ((MeasureTheory.volume :
          MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))).restrict K) := by
    have h_aem_Ω : AEStronglyMeasurable (iterWeakPartial (d := d) p j β f Ω)
        ((MeasureTheory.volume :
            MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))).restrict Ω) :=
      (iterWeakPartial_memLp_of_memWkp (d := d) (p := p) hfp_j β).aestronglyMeasurable
    have hK_sub_via : (MeasureTheory.volume :
            MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))).restrict K ≤
        (MeasureTheory.volume :
            MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))).restrict Ω :=
      Measure.restrict_mono_set MeasureTheory.volume hK_subset
    exact h_aem_Ω.mono_measure hK_sub_via
  have h_holder := MeasureTheory.eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (p := p') (q := p) (μ := (MeasureTheory.volume :
        MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))).restrict K)
    (f := iterWeakPartial (d := d) p j β f Ω) hp'_le_p h_aem
  have h_meas_univ_K : ((MeasureTheory.volume :
        MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))).restrict K) Set.univ =
      MeasureTheory.volume K := by
    rw [Measure.restrict_apply MeasurableSet.univ]
    simp
  rw [h_meas_univ_K] at h_holder
  calc eLpNorm (iterWeakPartial (d := d) p j β f Ω) p'
        ((MeasureTheory.volume :
            MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))).restrict K)
      ≤ eLpNorm (iterWeakPartial (d := d) p j β f Ω) p
          ((MeasureTheory.volume :
              MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))).restrict K) *
        MeasureTheory.volume K ^ (1 / p'.toReal - 1 / p.toReal) := h_holder
    _ = MeasureTheory.volume K ^ (1 / p'.toReal - 1 / p.toReal) *
          eLpNorm (iterWeakPartial (d := d) p j β f Ω) p
            ((MeasureTheory.volume :
                MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))).restrict K) := by
        rw [mul_comm]

private lemma exponent_nonneg
    {p p' : ℝ≥0∞} (hp_one : 1 ≤ p) (hp'_one : 1 ≤ p')
    (hp'_le_p : p' ≤ p) (hp_top : p ≠ ⊤) :
    (0 : ℝ) ≤ 1 / p'.toReal - 1 / p.toReal := by
  have hp'_top : p' ≠ ⊤ := by
    intro h
    rw [h] at hp'_le_p
    exact hp_top (top_le_iff.mp hp'_le_p)
  have hp_pos : (0 : ℝ) < p.toReal := by
    have h1 : (1 : ℝ) ≤ p.toReal := by
      have := ENNReal.toReal_mono hp_top hp_one
      simpa using this
    linarith
  have hp'_pos : (0 : ℝ) < p'.toReal := by
    have h1 : (1 : ℝ) ≤ p'.toReal := by
      have := ENNReal.toReal_mono hp'_top hp'_one
      simpa using this
    linarith
  have hp'_le_real : p'.toReal ≤ p.toReal := ENNReal.toReal_mono hp_top hp'_le_p
  have h_inv : 1 / p.toReal ≤ 1 / p'.toReal :=
    one_div_le_one_div_of_le hp'_pos hp'_le_real
  linarith

theorem wkpNorm_chartPushed_mono_exponent_holder
    [CompactSpace M] [NeZero (Module.finrank ℝ E)]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (k : ℕ) (α : M)
    {p p' : ℝ≥0∞} (hp_one : 1 ≤ p) (hp'_one : 1 ≤ p')
    (hp'_le_p : p' ≤ p) (hp_top : p ≠ ⊤) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : M → ℝ,
        MemWkpChart (I := I) (M := M) g k p u →
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) k p'
            (chartPushed (I := I) (M := M)
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal C *
              iteratedWeakSobolevNorm (d := Module.finrank ℝ E) k p
                (chartPushed (I := I) (M := M)
                  (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
                (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set Ω : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
    chartTargetEuclid (I := I) (M := M) α with hΩ_def
  set Kset : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
    K (I := I) (M := M) α with hKset_def
  have hΩ_open : IsOpen Ω :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hK_closed : IsClosed Kset := K_isClosed (I := I) (M := M) α
  have hK_subset : Kset ⊆ Ω := K_subset_target (I := I) (M := M) α
  have hK_vol_lt_top : MeasureTheory.volume Kset ≠ ⊤ :=
    K_volume_lt_top (I := I) (M := M) α
  set δ : ℝ := 1 / p'.toReal - 1 / p.toReal with hδ_def
  have hδ_nn : 0 ≤ δ := exponent_nonneg hp_one hp'_one hp'_le_p hp_top
  set Cenn : ℝ≥0∞ := MeasureTheory.volume Kset ^ δ with hCenn_def
  have hCenn_ne_top : Cenn ≠ ⊤ := by
    rw [hCenn_def]
    exact ENNReal.rpow_ne_top_of_nonneg hδ_nn hK_vol_lt_top
  refine ⟨Cenn.toReal, ENNReal.toReal_nonneg, ?_⟩
  intro u hu_mem
  set f : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
    chartPushed (I := I) (M := M)
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u with hf_def
  set fR : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
    fRaw (I := I) (M := M) α u with hfR_def
  have h_f_eq_fR : f =ᵐ[(MeasureTheory.volume :
        MeasureTheory.Measure
          (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict Ω] fR := by
    rw [hf_def, hfR_def]
    exact chartPushed_ae_eq_fRaw (I := I) (M := M) α u
  have h_fR_supp : tsupport fR ⊆ Kset := by
    rw [hfR_def, hKset_def]
    exact fRaw_tsupport_subset_K (I := I) (M := M) α u
  have h_Cenn_eq_ofReal : Cenn = ENNReal.ofReal Cenn.toReal := by
    rw [ENNReal.ofReal_toReal hCenn_ne_top]
  have h_wkpNorm_p'_eq : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) k p' f Ω =
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) k p' fR Ω :=
    wkpNorm_congr_ae (d := Module.finrank ℝ E) hp'_one hΩ_open h_f_eq_fR
  have h_wkpNorm_p_eq : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) k p f Ω =
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) k p fR Ω :=
    wkpNorm_congr_ae (d := Module.finrank ℝ E) hp_one hΩ_open h_f_eq_fR
  rw [h_wkpNorm_p'_eq, h_wkpNorm_p_eq]
  have h_fR_memWkp_p : MemWkp (d := Module.finrank ℝ E) k p fR Ω := by
    rw [hfR_def]
    exact ChartTower.memWkp_chartPushedRaw_pou_mul_of_memWkpChart
      (I := I) (M := M) g hp_one hu_mem α
  have h_fR_memWkp_p' : MemWkp (d := Module.finrank ℝ E) k p' fR Ω := by
    have hp'_top_or_eq : p' ≠ ⊤ := by
      intro h
      rw [h] at hp'_le_p
      exact hp_top (top_le_iff.mp hp'_le_p)
    exact EuclideanIteratedMonoExp.memWkp_mono_exponent_of_tsupport_subset
      (d := Module.finrank ℝ E) k hΩ_open hK_closed hK_vol_lt_top
      hp'_one hp'_le_p h_fR_supp h_fR_memWkp_p
  rw [show (DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
      (d := Module.finrank ℝ E) k p' fR Ω) =
      ∑ j ∈ Finset.range (k + 1),
        ∑ β : Fin j → Fin (Module.finrank ℝ E),
          eLpNorm (iterWeakPartial (d := Module.finrank ℝ E) p' j β fR Ω) p'
            ((MeasureTheory.volume :
                MeasureTheory.Measure
                  (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict Ω) from rfl]
  rw [show (DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
      (d := Module.finrank ℝ E) k p fR Ω) =
      ∑ j ∈ Finset.range (k + 1),
        ∑ β : Fin j → Fin (Module.finrank ℝ E),
          eLpNorm (iterWeakPartial (d := Module.finrank ℝ E) p j β fR Ω) p
            ((MeasureTheory.volume :
                MeasureTheory.Measure
                  (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict Ω) from rfl]
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro j hj
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro β _
  have hj_le_k : j ≤ k := by
    rw [Finset.mem_range] at hj; omega
  have h_per := eLpNorm_iterWeakPartial_mono_exponent
    (d := Module.finrank ℝ E) hΩ_open hK_closed hK_subset
    hp_one hp'_one hp'_le_p h_fR_memWkp_p h_fR_memWkp_p' h_fR_supp hj_le_k β
  have h_Cenn_id : MeasureTheory.volume Kset ^ (1 / p'.toReal - 1 / p.toReal) =
      ENNReal.ofReal Cenn.toReal := by
    rw [← hδ_def, ← hCenn_def, ← h_Cenn_eq_ofReal]
  calc eLpNorm (iterWeakPartial (d := Module.finrank ℝ E) p' j β fR Ω) p'
        ((MeasureTheory.volume :
            MeasureTheory.Measure
              (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict Ω)
      ≤ MeasureTheory.volume Kset ^ (1 / p'.toReal - 1 / p.toReal) *
          eLpNorm (iterWeakPartial (d := Module.finrank ℝ E) p j β fR Ω) p
            ((MeasureTheory.volume :
                MeasureTheory.Measure
                  (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict Ω) := h_per
    _ = ENNReal.ofReal Cenn.toReal *
          eLpNorm (iterWeakPartial (d := Module.finrank ℝ E) p j β fR Ω) p
            ((MeasureTheory.volume :
                MeasureTheory.Measure
                  (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict Ω) := by
        rw [h_Cenn_id]

end HolderPerChart
end Chart
end Sobolev
end Analysis
end DifferentialGeometry
