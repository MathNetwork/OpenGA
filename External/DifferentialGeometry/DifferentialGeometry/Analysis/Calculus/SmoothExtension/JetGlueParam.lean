import DifferentialGeometry.Analysis.Calculus.SmoothExtension.IteratedFDerivProdMatch
import Mathlib.Analysis.Calculus.TangentCone.Real


























noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace DifferentialGeometry
namespace Analysis
namespace SmoothExtension

variable {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]









theorem contDiffOn_glue_of_seam_param
    {V : Set E} (hV : IsOpen V) (fL fR : ℝ × E → F)
    (hL : ContDiffOn ℝ ∞ fL (Set.Iic (0:ℝ) ×ˢ V))
    (hR : ContDiffOn ℝ ∞ fR (Set.Ici (0:ℝ) ×ˢ V))
    (hmatch : ∀ (n : ℕ) (z : E), z ∈ V →
      iteratedFDerivWithin ℝ n fL (Set.Iic (0:ℝ) ×ˢ V) (0, z)
        = iteratedFDerivWithin ℝ n fR (Set.Ici (0:ℝ) ×ˢ V) (0, z)) :
    ContDiffOn ℝ ∞ (fun q : ℝ × E => if q.1 ≤ 0 then fL q else fR q)
      ((Set.univ : Set ℝ) ×ˢ V) := by
  set sL : Set (ℝ × E) := Set.Iic (0:ℝ) ×ˢ V with hsL_def
  set sR : Set (ℝ × E) := Set.Ici (0:ℝ) ×ˢ V with hsR_def
  set f : ℝ × E → F := fun q => if q.1 ≤ 0 then fL q else fR q with hf_def
  set pL : (ℝ × E) → FormalMultilinearSeries ℝ (ℝ × E) F :=
    ftaylorSeriesWithin ℝ fL sL with hpL_def
  set pR : (ℝ × E) → FormalMultilinearSeries ℝ (ℝ × E) F :=
    ftaylorSeriesWithin ℝ fR sR with hpR_def
  set p : (ℝ × E) → FormalMultilinearSeries ℝ (ℝ × E) F :=
    fun q => if q.1 ≤ 0 then pL q else pR q with hp_def
  have hUDL : UniqueDiffOn ℝ sL := UniqueDiffOn.prod (uniqueDiffOn_Iic 0) hV.uniqueDiffOn
  have hUDR : UniqueDiffOn ℝ sR := UniqueDiffOn.prod (uniqueDiffOn_Ici 0) hV.uniqueDiffOn
  have hTL : HasFTaylorSeriesUpToOn ∞ fL pL sL := hL.ftaylorSeriesWithin hUDL
  have hTR : HasFTaylorSeriesUpToOn ∞ fR pR sR := hR.ftaylorSeriesWithin hUDR

  have hmatchP : ∀ (n : ℕ) (z : E), z ∈ V → pL (0, z) n = pR (0, z) n := by
    intro n z hz
    simpa only [hpL_def, hpR_def, ftaylorSeriesWithin] using hmatch n z hz

  have hEqL : ∀ m : ℕ, Set.EqOn (fun y => p y m) (fun y => pL y m) sL := by
    rintro m ⟨y1, y2⟩ hy
    obtain ⟨hy1, _⟩ := hy
    simp only [hp_def, if_pos (Set.mem_Iic.mp hy1)]

  have hEqR : ∀ m : ℕ, Set.EqOn (fun y => p y m) (fun y => pR y m) sR := by
    rintro m ⟨y1, y2⟩ hy
    obtain ⟨hy1, hy2⟩ := hy
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hy1) with hy0 | hy0
    ·
      subst hy0
      simp only [hp_def, if_pos (le_refl (0:ℝ)), hmatchP m y2 hy2]
    ·
      simp only [hp_def, if_neg (not_le.mpr hy0)]

  have hzero : ∀ x : ℝ × E, x ∈ ((Set.univ : Set ℝ) ×ˢ V) → (p x 0).curry0 = f x := by
    rintro ⟨x1, x2⟩ hx
    obtain ⟨_, hx2⟩ := hx
    by_cases hx1 : x1 ≤ 0
    · have hval : (pL (x1, x2) 0).curry0 = fL (x1, x2) := hTL.zero_eq (x1, x2) ⟨hx1, hx2⟩
      simp only [hp_def, hf_def, if_pos hx1, hval]
    · have hx1' : (0:ℝ) ≤ x1 := le_of_lt (not_le.mp hx1)
      have hval : (pR (x1, x2) 0).curry0 = fR (x1, x2) := hTR.zero_eq (x1, x2) ⟨hx1', hx2⟩
      simp only [hp_def, hf_def, if_neg hx1, hval]
  have hm_lt : ∀ m : ℕ, (m : WithTop ℕ∞) < ∞ := fun m => by
    exact_mod_cast (Nat.cast_lt.mpr m.lt_succ_self).trans_le le_top

  have hderiv : ∀ (m : ℕ) (x : ℝ × E), x ∈ ((Set.univ : Set ℝ) ×ˢ V) →
      HasFDerivWithinAt (fun y => p y m) (p x m.succ).curryLeft ((Set.univ : Set ℝ) ×ˢ V) x := by
    rintro m ⟨x1, x2⟩ hx
    obtain ⟨_, hx2⟩ := hx
    have hpL_succ : ∀ y : ℝ × E, y.1 ≤ 0 → p y m.succ = pL y m.succ :=
      fun y hy => by simp only [hp_def, if_pos hy]
    have hpR_succ : ∀ y : ℝ × E, 0 < y.1 → p y m.succ = pR y m.succ :=
      fun y hy => by simp only [hp_def, if_neg (not_le.mpr hy)]
    rcases lt_trichotomy x1 0 with hx1 | hx1 | hx1
    ·
      have hxle : x1 ≤ 0 := le_of_lt hx1
      have hdL : HasFDerivWithinAt (fun y => pL y m) (pL (x1, x2) m.succ).curryLeft sL (x1, x2) :=
        hTL.fderivWithin m (hm_lt m) (x1, x2) ⟨hxle, hx2⟩
      have hsub : Set.Iio (0:ℝ) ×ˢ V ⊆ sL := Set.prod_mono Set.Iio_subset_Iic_self (Set.Subset.refl V)
      have hnhds : Set.Iio (0:ℝ) ×ˢ V ∈ 𝓝 ((x1, x2) : ℝ × E) :=
        (isOpen_Iio.prod hV).mem_nhds ⟨hx1, hx2⟩
      have hdL' : HasFDerivAt (fun y => pL y m) (pL (x1, x2) m.succ).curryLeft (x1, x2) :=
        (hdL.mono hsub).hasFDerivAt hnhds
      have hee : (fun y => p y m) =ᶠ[𝓝 ((x1, x2) : ℝ × E)] (fun y => pL y m) :=
        eventuallyEq_of_mem hnhds (fun y hy => hEqL m (hsub hy))
      have hfd : HasFDerivAt (fun y => p y m) (pL (x1, x2) m.succ).curryLeft (x1, x2) :=
        hdL'.congr_of_eventuallyEq hee
      rw [hpL_succ (x1, x2) hxle]
      exact hfd.hasFDerivWithinAt
    ·
      subst hx1
      have hdL0 : HasFDerivWithinAt (fun y => pL y m) (pL ((0:ℝ), x2) m.succ).curryLeft sL
          ((0:ℝ), x2) := hTL.fderivWithin m (hm_lt m) ((0:ℝ), x2) ⟨Set.self_mem_Iic, hx2⟩
      have hdL0' : HasFDerivWithinAt (fun y => p y m) (pL ((0:ℝ), x2) m.succ).curryLeft sL
          ((0:ℝ), x2) := hdL0.congr (hEqL m) (hEqL m ⟨Set.self_mem_Iic, hx2⟩)
      have hdR0 : HasFDerivWithinAt (fun y => pR y m) (pR ((0:ℝ), x2) m.succ).curryLeft sR
          ((0:ℝ), x2) := hTR.fderivWithin m (hm_lt m) ((0:ℝ), x2) ⟨Set.self_mem_Ici, hx2⟩
      have hval : (pR ((0:ℝ), x2) m.succ).curryLeft = (pL ((0:ℝ), x2) m.succ).curryLeft := by
        rw [hmatchP m.succ x2 hx2]
      have hdR0' : HasFDerivWithinAt (fun y => p y m) (pL ((0:ℝ), x2) m.succ).curryLeft sR
          ((0:ℝ), x2) := by
        rw [← hval]
        exact hdR0.congr (hEqR m) (hEqR m ⟨Set.self_mem_Ici, hx2⟩)
      have hunion : HasFDerivWithinAt (fun y => p y m) (pL ((0:ℝ), x2) m.succ).curryLeft
          (sL ∪ sR) ((0:ℝ), x2) := hdL0'.union hdR0'
      have hsetUnion : sL ∪ sR = (Set.univ : Set ℝ) ×ˢ V := by
        rw [hsL_def, hsR_def, ← Set.union_prod, Set.Iic_union_Ici]
      rw [hsetUnion] at hunion
      rw [hpL_succ ((0:ℝ), x2) (le_refl (0:ℝ))]
      exact hunion
    ·
      have hxge : (0:ℝ) ≤ x1 := le_of_lt hx1
      have hdR : HasFDerivWithinAt (fun y => pR y m) (pR (x1, x2) m.succ).curryLeft sR (x1, x2) :=
        hTR.fderivWithin m (hm_lt m) (x1, x2) ⟨hxge, hx2⟩
      have hsub : Set.Ioi (0:ℝ) ×ˢ V ⊆ sR := Set.prod_mono Set.Ioi_subset_Ici_self (Set.Subset.refl V)
      have hnhds : Set.Ioi (0:ℝ) ×ˢ V ∈ 𝓝 ((x1, x2) : ℝ × E) :=
        (isOpen_Ioi.prod hV).mem_nhds ⟨hx1, hx2⟩
      have hdR' : HasFDerivAt (fun y => pR y m) (pR (x1, x2) m.succ).curryLeft (x1, x2) :=
        (hdR.mono hsub).hasFDerivAt hnhds
      have hee : (fun y => p y m) =ᶠ[𝓝 ((x1, x2) : ℝ × E)] (fun y => pR y m) :=
        eventuallyEq_of_mem hnhds (fun y hy => hEqR m (hsub hy))
      have hfd : HasFDerivAt (fun y => p y m) (pR (x1, x2) m.succ).curryLeft (x1, x2) :=
        hdR'.congr_of_eventuallyEq hee
      rw [hpR_succ (x1, x2) hx1]
      exact hfd.hasFDerivWithinAt

  have hTaylor : HasFTaylorSeriesUpToOn ∞ f p ((Set.univ : Set ℝ) ×ˢ V) :=
    (hasFTaylorSeriesUpToOn_top_iff' (le_refl _)).mpr
      ⟨fun x hx => hzero x hx, fun m x hx => hderiv m x hx⟩
  exact hTaylor.contDiffOn















theorem iteratedFDerivWithin_seam_match {V : Set E} (hV : IsOpen V) :
    ∀ (n : ℕ) {fL fR : ℝ × E → F},
      ContDiffOn ℝ ∞ fL (Set.Iic (0:ℝ) ×ˢ V) →
      ContDiffOn ℝ ∞ fR (Set.Ici (0:ℝ) ×ˢ V) →
      (∀ (i : ℕ), ∀ w ∈ V,
        iteratedDerivWithin i (fun t => fL (t, w)) (Set.Iic 0) 0
          = iteratedDerivWithin i (fun t => fR (t, w)) (Set.Ici 0) 0) →
      ∀ {z : E}, z ∈ V →
        iteratedFDerivWithin ℝ n fL (Set.Iic (0:ℝ) ×ˢ V) (0, z)
          = iteratedFDerivWithin ℝ n fR (Set.Ici (0:ℝ) ×ˢ V) (0, z) := by
  intro n
  induction n with
  | zero =>
    intro fL fR _ _ hjet z hz
    ext m
    rw [iteratedFDerivWithin_zero_apply, iteratedFDerivWithin_zero_apply]
    have h := hjet 0 z hz
    simpa only [iteratedDerivWithin_zero] using h
  | succ n IH =>
    intro fL fR hL hR hjet z hz
    set sL : Set (ℝ × E) := Set.Iic (0:ℝ) ×ˢ V with hsL_def
    set sR : Set (ℝ × E) := Set.Ici (0:ℝ) ×ˢ V with hsR_def
    have hUDL : UniqueDiffOn ℝ sL := UniqueDiffOn.prod (uniqueDiffOn_Iic 0) hV.uniqueDiffOn
    have hUDR : UniqueDiffOn ℝ sR := UniqueDiffOn.prod (uniqueDiffOn_Ici 0) hV.uniqueDiffOn
    have hSLclo : sL ⊆ closure (interior sL) := by
      have hsub : Set.Iio (0:ℝ) ×ˢ V ⊆ interior sL := by
        rw [hsL_def, interior_prod_eq, interior_Iic, hV.interior_eq]
      refine fun q hq => closure_mono hsub ?_
      rw [hsL_def] at hq
      rw [closure_prod_eq, closure_Iio]
      exact ⟨hq.1, subset_closure hq.2⟩
    have hSRclo : sR ⊆ closure (interior sR) := by
      have hsub : Set.Ioi (0:ℝ) ×ˢ V ⊆ interior sR := by
        rw [hsR_def, interior_prod_eq, interior_Ici, hV.interior_eq]
      refine fun q hq => closure_mono hsub ?_
      rw [hsR_def] at hq
      rw [closure_prod_eq, closure_Ioi]
      exact ⟨hq.1, subset_closure hq.2⟩
    have hmemL : ((0:ℝ), z) ∈ sL := ⟨Set.self_mem_Iic, hz⟩
    have hmemR : ((0:ℝ), z) ∈ sR := ⟨Set.self_mem_Ici, hz⟩

    simp only [iteratedFDerivWithin_succ_eq_comp_left, Function.comp_apply]
    congr 1
    refine ContinuousLinearMap.ext (fun p => ?_)
    obtain ⟨t, e⟩ := p
    have hsplit : (t, e) = t • ((1:ℝ), (0:E)) + ((0:ℝ), e) := by
      simp [Prod.smul_mk, Prod.mk_add_mk]

    have htrans : fderivWithin ℝ (iteratedFDerivWithin ℝ n fL sL) sL (0, z) ((1:ℝ), (0:E))
        = fderivWithin ℝ (iteratedFDerivWithin ℝ n fR sR) sR (0, z) ((1:ℝ), (0:E)) := by
      rw [fderivWithin_iteratedFDerivWithin_apply_eq hUDL hSLclo n hL ((1:ℝ), (0:E)) (0, z) hmemL,
        fderivWithin_iteratedFDerivWithin_apply_eq hUDR hSRclo n hR ((1:ℝ), (0:E)) (0, z) hmemR]
      have hDtL : ContDiffOn ℝ ∞ (fun y => fderivWithin ℝ fL sL y ((1:ℝ), (0:E))) sL :=
        (hL.fderivWithin hUDL (by exact_mod_cast le_top)).clm_apply contDiffOn_const
      have hDtR : ContDiffOn ℝ ∞ (fun y => fderivWithin ℝ fR sR y ((1:ℝ), (0:E))) sR :=
        (hR.fderivWithin hUDR (by exact_mod_cast le_top)).clm_apply contDiffOn_const
      have hjet' : ∀ (i : ℕ), ∀ w ∈ V,
          iteratedDerivWithin i (fun s => fderivWithin ℝ fL sL (s, w) ((1:ℝ), (0:E)))
              (Set.Iic 0) 0
            = iteratedDerivWithin i (fun s => fderivWithin ℝ fR sR (s, w) ((1:ℝ), (0:E)))
              (Set.Ici 0) 0 := by
        intro i w hw
        have hcongrL : Set.EqOn (fun s => fderivWithin ℝ fL sL (s, w) ((1:ℝ), (0:E)))
            (derivWithin (fun s => fL (s, w)) (Set.Iic 0)) (Set.Iic 0) := by
          intro s hs
          have hmaps : Set.MapsTo (fun r : ℝ => (r, w)) (Set.Iic 0) sL := fun r hr => ⟨hr, hw⟩
          have hpairc : HasDerivWithinAt (fun r : ℝ => (r, w)) ((1:ℝ), (0:E)) (Set.Iic 0) s :=
            (hasDerivWithinAt_id s (Set.Iic 0)).prodMk (hasDerivWithinAt_const s _ w)
          have hLfd : HasFDerivWithinAt fL (fderivWithin ℝ fL sL (s, w)) sL (s, w) :=
            ((hL (s, w) (hmaps hs)).differentiableWithinAt (by simp)).hasFDerivWithinAt
          have hcomp : HasDerivWithinAt (fun r : ℝ => fL (r, w))
              (fderivWithin ℝ fL sL (s, w) ((1:ℝ), (0:E))) (Set.Iic 0) s :=
            hLfd.comp_hasDerivWithinAt s hpairc hmaps
          exact (hcomp.derivWithin (uniqueDiffOn_Iic 0 s hs)).symm
        have hcongrR : Set.EqOn (fun s => fderivWithin ℝ fR sR (s, w) ((1:ℝ), (0:E)))
            (derivWithin (fun s => fR (s, w)) (Set.Ici 0)) (Set.Ici 0) := by
          intro s hs
          have hmaps : Set.MapsTo (fun r : ℝ => (r, w)) (Set.Ici 0) sR := fun r hr => ⟨hr, hw⟩
          have hpairc : HasDerivWithinAt (fun r : ℝ => (r, w)) ((1:ℝ), (0:E)) (Set.Ici 0) s :=
            (hasDerivWithinAt_id s (Set.Ici 0)).prodMk (hasDerivWithinAt_const s _ w)
          have hRfd : HasFDerivWithinAt fR (fderivWithin ℝ fR sR (s, w)) sR (s, w) :=
            ((hR (s, w) (hmaps hs)).differentiableWithinAt (by simp)).hasFDerivWithinAt
          have hcomp : HasDerivWithinAt (fun r : ℝ => fR (r, w))
              (fderivWithin ℝ fR sR (s, w) ((1:ℝ), (0:E))) (Set.Ici 0) s :=
            hRfd.comp_hasDerivWithinAt s hpairc hmaps
          exact (hcomp.derivWithin (uniqueDiffOn_Ici 0 s hs)).symm
        rw [iteratedDerivWithin_congr hcongrL Set.self_mem_Iic, ← iteratedDerivWithin_succ',
          iteratedDerivWithin_congr hcongrR Set.self_mem_Ici, ← iteratedDerivWithin_succ']
        exact hjet (i + 1) w hw
      exact IH hDtL hDtR hjet' hz

    have hseam : fderivWithin ℝ (iteratedFDerivWithin ℝ n fL sL) sL (0, z) ((0:ℝ), e)
        = fderivWithin ℝ (iteratedFDerivWithin ℝ n fR sR) sR (0, z) ((0:ℝ), e) := by
      set ι : E → ℝ × E := fun v => (0, v) with hι_def
      set gL : ℝ × E → (ℝ × E) [×n]→L[ℝ] F := iteratedFDerivWithin ℝ n fL sL with hgL_def
      set gR : ℝ × E → (ℝ × E) [×n]→L[ℝ] F := iteratedFDerivWithin ℝ n fR sR with hgR_def
      have hιmapsL : Set.MapsTo ι V sL := fun v hv => ⟨Set.self_mem_Iic, hv⟩
      have hιmapsR : Set.MapsTo ι V sR := fun v hv => ⟨Set.self_mem_Ici, hv⟩
      have hιfd : HasFDerivWithinAt ι (ContinuousLinearMap.inr ℝ ℝ E) V z := by
        simpa [hι_def] using (ContinuousLinearMap.inr ℝ ℝ E).hasFDerivWithinAt
      have hιdiff : DifferentiableWithinAt ℝ ι V z := hιfd.differentiableWithinAt
      have hgLdiff : DifferentiableWithinAt ℝ gL sL (0, z) :=
        (hL.differentiableOn_iteratedFDerivWithin (by exact_mod_cast ENat.coe_lt_top n) hUDL)
          (0, z) hmemL
      have hgRdiff : DifferentiableWithinAt ℝ gR sR (0, z) :=
        (hR.differentiableOn_iteratedFDerivWithin (by exact_mod_cast ENat.coe_lt_top n) hUDR)
          (0, z) hmemR
      have hEqV : Set.EqOn (gL ∘ ι) (gR ∘ ι) V := by
        intro v hv
        simp only [hgL_def, hgR_def, hι_def, Function.comp_apply]
        exact IH hL hR hjet hv
      have hchainL : fderivWithin ℝ (gL ∘ ι) V z
          = (fderivWithin ℝ gL sL (0, z)).comp (ContinuousLinearMap.inr ℝ ℝ E) := by
        rw [fderivWithin_comp z hgLdiff hιdiff hιmapsL (hV.uniqueDiffOn z hz),
          hιfd.fderivWithin (hV.uniqueDiffOn z hz)]
      have hchainR : fderivWithin ℝ (gR ∘ ι) V z
          = (fderivWithin ℝ gR sR (0, z)).comp (ContinuousLinearMap.inr ℝ ℝ E) := by
        rw [fderivWithin_comp z hgRdiff hιdiff hιmapsR (hV.uniqueDiffOn z hz),
          hιfd.fderivWithin (hV.uniqueDiffOn z hz)]
      have hcongr : fderivWithin ℝ (gL ∘ ι) V z = fderivWithin ℝ (gR ∘ ι) V z :=
        fderivWithin_congr hEqV (hEqV hz)
      have hcomp_eq : (fderivWithin ℝ gL sL (0, z)).comp (ContinuousLinearMap.inr ℝ ℝ E)
          = (fderivWithin ℝ gR sR (0, z)).comp (ContinuousLinearMap.inr ℝ ℝ E) := by
        rw [← hchainL, ← hchainR]; exact hcongr
      have happ := congrArg (fun L => L e) hcomp_eq
      simpa only [hgL_def, hgR_def, ContinuousLinearMap.coe_comp', Function.comp_apply,
        ContinuousLinearMap.inr_apply] using happ
    rw [hsplit, map_add, map_add, map_smul, map_smul, htrans, hseam]









theorem contDiffOn_glue_of_jet_param
    {V : Set E} (hV : IsOpen V) (fL fR : ℝ × E → F)
    (hL : ContDiffOn ℝ ∞ fL (Set.Iic (0:ℝ) ×ˢ V))
    (hR : ContDiffOn ℝ ∞ fR (Set.Ici (0:ℝ) ×ˢ V))
    (hjet : ∀ (i : ℕ), ∀ w ∈ V,
      iteratedDerivWithin i (fun t => fL (t, w)) (Set.Iic 0) 0
        = iteratedDerivWithin i (fun t => fR (t, w)) (Set.Ici 0) 0) :
    ContDiffOn ℝ ∞ (fun q : ℝ × E => if q.1 ≤ 0 then fL q else fR q)
      ((Set.univ : Set ℝ) ×ˢ V) :=
  contDiffOn_glue_of_seam_param hV fL fR hL hR
    (fun n _z hz => iteratedFDerivWithin_seam_match hV n hL hR hjet hz)

end SmoothExtension
end Analysis
end DifferentialGeometry

end
