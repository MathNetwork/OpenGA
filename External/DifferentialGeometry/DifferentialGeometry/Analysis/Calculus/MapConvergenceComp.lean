import DifferentialGeometry.Analysis.Calculus.MapConvergenceDeriv
import DifferentialGeometry.Analysis.Calculus.PiDeriv
import DifferentialGeometry.Analysis.Calculus.RingInverseDeriv
import Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno
import Mathlib.Topology.MetricSpace.Thickening

set_option autoImplicit false
set_option linter.style.longLine false











namespace DifferentialGeometry
namespace HCGCompactness

open Filter Topology
open scoped ContDiff

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]




theorem MapCPConvOn.tendstoUniformlyOn_iteratedFDeriv
    {U K : Set E} {p : ℕ} {Φ : ℕ → E → F} {Φinf : E → F}
    (hU : IsOpen U) (hKU : K ⊆ U) (h : MapCPConvOn K p Φ Φinf)
    (hΦ : ∀ k, ContDiffOn ℝ (p : ℕ∞) (Φ k) U)
    (hΦinf : ContDiffOn ℝ (p : ℕ∞) Φinf U) {r : ℕ} (hr : r ≤ p) :
    TendstoUniformlyOn
      (fun k x => iteratedFDeriv ℝ r (Φ k) x)
      (fun x => iteratedFDeriv ℝ r Φinf x) atTop K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨k0, hk0⟩ := h (ε / 2) (by positivity)
  rw [eventually_atTop]
  refine ⟨k0, fun k hk x hx => ?_⟩
  have hxU : x ∈ U := hKU hx
  have hsub : iteratedFDeriv ℝ r (fun y => Φ k y - Φinf y) x
      = iteratedFDeriv ℝ r (Φ k) x - iteratedFDeriv ℝ r Φinf x := by
    exact iteratedFDeriv_sub_apply (𝕜 := ℝ) (i := r) (x := x)
      (((hΦ k).contDiffAt (hU.mem_nhds hxU)).of_le (by exact_mod_cast hr))
      ((hΦinf.contDiffAt (hU.mem_nhds hxU)).of_le (by exact_mod_cast hr))
  have hb := hk0 k hk r hr x hx
  rw [mapDerivNorm, hsub] at hb
  rw [dist_eq_norm, norm_sub_rev]
  exact lt_of_le_of_lt hb (by linarith)


theorem MapCPConvOn.comp_tendsto_atTop {K : Set E} {p : ℕ}
    {Φ : ℕ → E → F} {Φinf : E → F} (h : MapCPConvOn K p Φ Φinf)
    {τ : ℕ → ℕ} (hτ : Tendsto τ atTop atTop) :
    MapCPConvOn K p (fun k => Φ (τ k)) Φinf := by
  intro ε hε
  obtain ⟨k0, hk0⟩ := h ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hτ.eventually_ge_atTop k0)
  exact ⟨N, fun k hk r hr x hx => hk0 (τ k) (hN k hk) r hr x hx⟩


theorem MapCInfConvOnCompacts.comp_tendsto_atTop {U : Set E}
    {Φ : ℕ → E → F} {Φinf : E → F} (h : MapCInfConvOnCompacts U Φ Φinf)
    {τ : ℕ → ℕ} (hτ : Tendsto τ atTop atTop) :
    MapCInfConvOnCompacts U (fun k => Φ (τ k)) Φinf :=
  fun K hK hKU p => (h K hK hKU p).comp_tendsto_atTop hτ

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in



theorem mapCInf_pair_tail
    {U : Set E} {Φ : ℕ → ℕ → E → G} {Φinf : E → G}
    (hconv : ∀ kn ln : ℕ → ℕ,
      Tendsto kn atTop atTop → Tendsto ln atTop atTop →
        MapCInfConvOnCompacts U (fun n => Φ (kn n) (ln n)) Φinf)
    {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U) (p : ℕ) :
    ∀ ε > 0, ∃ N : ℕ, ∀ k ≥ N, ∀ l ≥ N, ∀ j ≤ p, ∀ x ∈ K,
      mapDerivNorm j (Φ k l) Φinf x ≤ ε := by
  classical
  intro ε hε
  by_contra hbad
  push Not at hbad
  choose k hk hbad using hbad
  choose l hl hbad using hbad
  choose j hj hbad using hbad
  choose x hx hbad using hbad
  have hk_top : Tendsto k atTop atTop :=
    tendsto_atTop_mono hk tendsto_id
  have hl_top : Tendsto l atTop atTop :=
    tendsto_atTop_mono hl tendsto_id
  obtain ⟨N, hN⟩ := hconv k l hk_top hl_top K hK hKU p ε hε
  exact not_lt_of_ge
    (hN N le_rfl (j N) (hj N) (x N) (hx N)) (hbad N)



theorem exists_three_tail {P : Nat → Nat → Nat → Prop}
    (h : ∀ an bn cn : Nat → Nat,
      Tendsto an atTop atTop → Tendsto bn atTop atTop →
        Tendsto cn atTop atTop →
          ∀ᶠ m in atTop, P (an m) (bn m) (cn m)) :
    ∃ N : Nat, ∀ a ≥ N, ∀ b ≥ N, ∀ c ≥ N, P a b c := by
  classical
  by_contra hbad
  push Not at hbad
  choose a ha hbad using hbad
  choose b hb hbad using hbad
  choose c hc hbad using hbad
  have ha_top : Tendsto a atTop atTop :=
    tendsto_atTop_mono ha tendsto_id
  have hb_top : Tendsto b atTop atTop :=
    tendsto_atTop_mono hb tendsto_id
  have hc_top : Tendsto c atTop atTop :=
    tendsto_atTop_mono hc tendsto_id
  obtain ⟨N, hN⟩ := eventually_atTop.mp (h a b c ha_top hb_top hc_top)
  exact hbad N (hN N le_rfl)



theorem MapCInfConvOnCompacts.eventually_mapsTo
    {U : Set E} {Φ : Nat → E → F} {Φinf : E → F}
    (hconv : MapCInfConvOnCompacts U Φ Φinf)
    {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U)
    (hΦinf : ContinuousOn Φinf K)
    {V : Set F} (hV : IsOpen V) (hmap : Set.MapsTo Φinf K V) :
    ∀ᶠ n in atTop, Set.MapsTo (Φ n) K V := by
  have hKimage : IsCompact (Φinf '' K) :=
    hK.image_of_continuousOn hΦinf
  have hKV : Φinf '' K ⊆ V := Set.image_subset_iff.mpr hmap
  obtain ⟨delta, hdelta, hthick⟩ :=
    hKimage.exists_thickening_subset_open hV hKV
  have htu := tendstoUniformlyOn_of_cPConv (hconv K hK hKU 0)
  rw [Metric.tendstoUniformlyOn_iff] at htu
  filter_upwards [htu delta hdelta] with n hn
  intro x hx
  apply hthick
  rw [Metric.mem_thickening_iff]
  exact ⟨Φinf x, ⟨x, hx, rfl⟩, by
    simpa only [dist_comm] using hn x hx⟩




theorem MapCInfConvOnCompacts.three_tail
    {U : Set E} {Φ : ℕ → ℕ → ℕ → E → F} {Φinf : E → F}
    (hconv : ∀ an bn cn : ℕ → ℕ,
      Tendsto an atTop atTop → Tendsto bn atTop atTop →
        Tendsto cn atTop atTop →
      MapCInfConvOnCompacts U
        (fun n => Φ (an n) (bn n) (cn n)) Φinf)
    {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U) (p : ℕ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ a ≥ N, ∀ b ≥ N, ∀ c ≥ N,
      ∀ r ≤ p, ∀ x ∈ K, mapDerivNorm r (Φ a b c) Φinf x ≤ ε := by
  classical
  by_contra hbad
  push Not at hbad
  choose a ha hbad using hbad
  choose b hb hbad using hbad
  choose c hc hbad using hbad
  choose r hr hbad using hbad
  choose x hx hbad using hbad
  have ha_top : Tendsto a atTop atTop :=
    tendsto_atTop_mono ha tendsto_id
  have hb_top : Tendsto b atTop atTop :=
    tendsto_atTop_mono hb tendsto_id
  have hc_top : Tendsto c atTop atTop :=
    tendsto_atTop_mono hc tendsto_id
  have hΦ := hconv a b c ha_top hb_top hc_top
  obtain ⟨N, hN⟩ := hΦ K hK hKU p ε hε
  exact not_lt_of_ge
    (hN N le_rfl (r N) (hr N) (x N) (hx N)) (hbad N)




theorem exists_cInf_finite
    {ι : Type*} [Finite ι]
    (U : ι → Set E) (Φ : ι → ℕ → E → F)
    (Q : ι → (E → F) → Prop)
    (hstep : ∀ i (τ : ℕ → ℕ), StrictMono τ →
      ∃ (σ : ℕ → ℕ) (Φinf : E → F), StrictMono σ ∧
        MapCInfConvOnCompacts (U i)
          (fun n => Φ i (τ (σ n))) Φinf ∧ Q i Φinf) :
    ∃ (ψ : ℕ → ℕ), StrictMono ψ ∧
      ∀ i, ∃ Φinf : E → F,
        MapCInfConvOnCompacts (U i) (fun n => Φ i (ψ n)) Φinf ∧ Q i Φinf := by
  classical
  letI := Fintype.ofFinite ι
  have aux : ∀ s : Finset ι,
      ∃ (ψ : ℕ → ℕ), StrictMono ψ ∧
        ∀ i ∈ s, ∃ Φinf : E → F,
          MapCInfConvOnCompacts (U i) (fun n => Φ i (ψ n)) Φinf ∧ Q i Φinf := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        exact ⟨id, strictMono_id, by simp⟩
    | @insert a s ha ih =>
        obtain ⟨τ, hτ, hconv⟩ := ih
        obtain ⟨σ, Φa, hσ, hΦa, hQa⟩ := hstep a τ hτ
        refine ⟨τ ∘ σ, hτ.comp hσ, ?_⟩
        intro i hi
        rw [Finset.mem_insert] at hi
        rcases hi with rfl | hi
        · exact ⟨Φa, by simpa only [Function.comp_apply] using hΦa, hQa⟩
        · obtain ⟨Φinf, hΦinf, hQinf⟩ := hconv i hi
          exact ⟨Φinf, by
            simpa only [Function.comp_apply] using
              hΦinf.comp_tendsto_atTop hσ.tendsto_atTop, hQinf⟩
  obtain ⟨ψ, hψ, hconv⟩ := aux Finset.univ
  exact ⟨ψ, hψ, fun i => hconv i (Finset.mem_univ i)⟩


theorem MapCInfConvOnCompacts.tendstoUniformlyOn_iteratedFDeriv
    {U K : Set E} {Φ : ℕ → E → F} {Φinf : E → F}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (h : MapCInfConvOnCompacts U Φ Φinf)
    (hΦ : ∀ k, ContDiffOn ℝ (∞ : WithTop ℕ∞) (Φ k) U)
    (hΦinf : ContDiffOn ℝ (∞ : WithTop ℕ∞) Φinf U) (r : ℕ) :
    TendstoUniformlyOn
      (fun k x => iteratedFDeriv ℝ r (Φ k) x)
      (fun x => iteratedFDeriv ℝ r Φinf x) atTop K := by
  exact (h K hK hKU r).tendstoUniformlyOn_iteratedFDeriv hU hKU
    (fun k => (hΦ k).of_le (by exact_mod_cast le_top))
    (hΦinf.of_le (by exact_mod_cast le_top)) le_rfl


theorem mapCPConvOn_of_tendstoUniformlyOn {U K : Set E} {p : ℕ}
    {Φ : ℕ → E → F} {Φinf : E → F} (hU : IsOpen U) (hKU : K ⊆ U)
    (hΦ : ∀ k, ContDiffOn ℝ (p : ℕ∞) (Φ k) U)
    (hΦinf : ContDiffOn ℝ (p : ℕ∞) Φinf U)
    (htu : ∀ r : ℕ, r ≤ p →
      TendstoUniformlyOn (fun k x => iteratedFDeriv ℝ r (Φ k) x)
        (fun x => iteratedFDeriv ℝ r Φinf x) atTop K) :
    MapCPConvOn K p Φ Φinf := by
  intro ε hε
  have key : ∀ r : ℕ, r ≤ p →
      ∀ᶠ k in atTop, ∀ x ∈ K, mapDerivNorm r (Φ k) Φinf x ≤ ε := by
    intro r hr
    have h := (Metric.tendstoUniformlyOn_iff.mp (htu r hr)) ε hε
    filter_upwards [h] with k hk x hx
    have hxU : x ∈ U := hKU hx
    have hsub : iteratedFDeriv ℝ r (fun y => Φ k y - Φinf y) x
        = iteratedFDeriv ℝ r (Φ k) x - iteratedFDeriv ℝ r Φinf x := by
      exact iteratedFDeriv_sub_apply (𝕜 := ℝ) (i := r) (x := x)
        (((hΦ k).contDiffAt (hU.mem_nhds hxU)).of_le (by exact_mod_cast hr))
        ((hΦinf.contDiffAt (hU.mem_nhds hxU)).of_le (by exact_mod_cast hr))
    have hdist := hk x hx
    rw [dist_eq_norm, ← norm_sub_rev] at hdist
    rw [mapDerivNorm, hsub]
    exact hdist.le
  have hfin : ∀ᶠ k in atTop, ∀ r ∈ Set.Iic p, ∀ x ∈ K,
      mapDerivNorm r (Φ k) Φinf x ≤ ε :=
    (Set.finite_Iic p).eventually_all.2 (fun r hr => key r (Set.mem_Iic.mp hr))
  obtain ⟨k0, hk0⟩ := eventually_atTop.mp hfin
  exact ⟨k0, fun k hk r hr x hx => hk0 k hk r (Set.mem_Iic.mpr hr) x hx⟩

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℝ F] in



theorem TendstoUniformlyOn.isLittleO_sub_const
    {K : Set E} {Fseq : ℕ → E → F} {Flim : E → F}
    (h : TendstoUniformlyOn Fseq Flim atTop K) :
    (fun q : ℕ × E => Fseq q.1 q.2 - Flim q.2)
      =o[atTop ×ˢ Filter.principal K] (fun _ : ℕ × E => (1 : ℝ)) := by
  rw [Asymptotics.isLittleO_one_iff ℝ]
  rw [Metric.tendsto_nhds]
  intro ε hε
  rw [eventually_prod_principal_iff]
  exact ((Metric.tendstoUniformlyOn_iff.mp h) ε hε).mono fun k hk x hx => by
    simpa [dist_eq_norm, norm_sub_rev] using hk x hx

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in


theorem isBoundedUnder_prod_principal_of_forall_le {K : Set E} {u : ℕ × E → ℝ}
    (h : ∃ C : ℝ, ∀ k x, x ∈ K → u (k, x) ≤ C) :
    (atTop ×ˢ Filter.principal K).IsBoundedUnder (· ≤ ·) u := by
  rcases h with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  rw [eventually_map, eventually_prod_principal_iff]
  exact Eventually.of_forall fun k x hx => hC k x hx

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in


theorem isBoundedUnder_prod_principal_of_eventually_forall_le {K : Set E} {u : ℕ × E → ℝ}
    (h : ∃ C : ℝ, ∀ᶠ k in atTop, ∀ x ∈ K, u (k, x) ≤ C) :
    (atTop ×ˢ Filter.principal K).IsBoundedUnder (· ≤ ·) u := by
  rcases h with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  rw [eventually_map, eventually_prod_principal_iff]
  exact hC

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℝ F] in


theorem TendstoUniformlyOn.eventually_norm_le
    {K : Set E} {Fseq : ℕ → E → F} {Flim : E → F}
    (h : TendstoUniformlyOn Fseq Flim atTop K)
    {C : ℝ} (hC : ∀ x ∈ K, ‖Flim x‖ ≤ C) :
    ∀ᶠ k in atTop, ∀ x ∈ K, ‖Fseq k x‖ ≤ C + 1 := by
  have h1 := (Metric.tendstoUniformlyOn_iff.mp h) 1 (by norm_num : (0 : ℝ) < 1)
  filter_upwards [h1] with k hk x hx
  have hdist : dist (Flim x) (Fseq k x) < 1 := hk x hx
  have htri : ‖Fseq k x‖ ≤ ‖Flim x‖ + dist (Flim x) (Fseq k x) := by
    calc
      ‖Fseq k x‖ ≤ ‖Flim x‖ + ‖Fseq k x - Flim x‖ := by
        simpa [dist_zero_right, dist_eq_norm, add_comm, add_left_comm, add_assoc]
          using dist_triangle (Fseq k x) (Flim x) (0 : F)
      _ = ‖Flim x‖ + dist (Flim x) (Fseq k x) := by
        rw [dist_eq_norm, norm_sub_rev]
  nlinarith [hC x hx, hdist.le]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in




theorem MapCInfConvOnCompacts.tendstoUniformlyOn_iteratedFDeriv_comp_moving
    {K : Set E} {V K' : Set F}
    {A : ℕ → F → G} {Ainf : F → G} {B : ℕ → E → F} {Binf : E → F}
    (hV : IsOpen V) (hK' : IsCompact K') (hK'V : K' ⊆ V)
    (hA : MapCInfConvOnCompacts V A Ainf)
    (hAc : ∀ k, ContDiffOn ℝ (∞ : WithTop ℕ∞) (A k) V)
    (hAinfc : ContDiffOn ℝ (∞ : WithTop ℕ∞) Ainf V)
    (hB : TendstoUniformlyOn B Binf atTop K)
    (hBK' : ∀ᶠ k in atTop, Set.MapsTo (B k) K K')
    (hBinfK' : Set.MapsTo Binf K K') (r : ℕ) :
    TendstoUniformlyOn
      (fun k x => iteratedFDeriv ℝ r (A k) (B k x))
      (fun x => iteratedFDeriv ℝ r Ainf (Binf x)) atTop K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hAder :
      TendstoUniformlyOn
        (fun k y => iteratedFDeriv ℝ r (A k) y)
        (fun y => iteratedFDeriv ℝ r Ainf y) atTop K' :=
    hA.tendstoUniformlyOn_iteratedFDeriv hV hK' hK'V hAc hAinfc r
  have hDcont : ContinuousOn (fun y => iteratedFDeriv ℝ r Ainf y) K' :=
    ((ContinuousOn.continuousOn_iteratedFDeriv hAinfc hV
      (by exact_mod_cast le_top)).mono hK'V)
  have hDuc : UniformContinuousOn (fun y => iteratedFDeriv ℝ r Ainf y) K' :=
    hK'.uniformContinuousOn_of_continuous hDcont
  have hDcomp :
      TendstoUniformlyOn
        (fun k x => iteratedFDeriv ℝ r Ainf (B k x))
        (fun x => iteratedFDeriv ℝ r Ainf (Binf x)) atTop K :=
    UniformContinuousOn.comp_tendstoUniformlyOn_eventually hBK' hBinfK' hDuc hB
  rw [Metric.tendstoUniformlyOn_iff] at hAder hDcomp
  obtain ⟨NA, hNA⟩ := eventually_atTop.mp (hAder (ε / 2) (by positivity))
  obtain ⟨NB, hNB⟩ := eventually_atTop.mp (hDcomp (ε / 2) (by positivity))
  obtain ⟨NM, hNM⟩ := eventually_atTop.mp hBK'
  rw [eventually_atTop]
  refine ⟨max (max NA NB) NM, fun k hk x hx => ?_⟩
  have hkA : NA ≤ k := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hk)
  have hkB : NB ≤ k := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hk)
  have hkM : NM ≤ k := le_trans (le_max_right _ _) hk
  have hBxK' : B k x ∈ K' := hNM k hkM hx
  calc
    dist (iteratedFDeriv ℝ r Ainf (Binf x))
        (iteratedFDeriv ℝ r (A k) (B k x))
        ≤ dist (iteratedFDeriv ℝ r Ainf (Binf x))
              (iteratedFDeriv ℝ r Ainf (B k x))
          + dist (iteratedFDeriv ℝ r Ainf (B k x))
              (iteratedFDeriv ℝ r (A k) (B k x)) := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := by
        exact add_lt_add (hNB k hkB x hx) (hNA k hkA (B k x) hBxK')
    _ = ε := by ring



theorem MapCPConvOn.comp_cInf
    {U K : Set E} {V : Set F} {p : ℕ} (hU : IsOpen U) (hV : IsOpen V)
    [ProperSpace F]
    {B : ℕ → E → F} {Binf : E → F} {A : ℕ → F → G} {Ainf : F → G}
    (hK : IsCompact K) (hKU : K ⊆ U)
    (hB : MapCPConvOn K p B Binf)
    (hA : MapCInfConvOnCompacts V A Ainf)
    (hBc : ∀ k, ContDiffOn ℝ (∞ : WithTop ℕ∞) (B k) U)
    (hBinfc : ContDiffOn ℝ (∞ : WithTop ℕ∞) Binf U)
    (hAc : ∀ k, ContDiffOn ℝ (∞ : WithTop ℕ∞) (A k) V)
    (hAinfc : ContDiffOn ℝ (∞ : WithTop ℕ∞) Ainf V)
    (hmap : Set.MapsTo Binf U V) (hmapk : ∀ k, Set.MapsTo (B k) U V) :
    MapCPConvOn K p (fun k x => A k (B k x)) (fun x => Ainf (Binf x)) := by
  have hBinf_cont : ContinuousOn Binf U := hBinfc.continuousOn
  have hBKcpt : IsCompact (Binf '' K) := hK.image_of_continuousOn (hBinf_cont.mono hKU)
  have hBKV : Binf '' K ⊆ V := by
    rintro y ⟨x, hx, rfl⟩
    exact hmap (hKU hx)
  obtain ⟨δ₀, hδ₀pos, hδ₀V⟩ := hBKcpt.exists_cthickening_subset_open hV hBKV
  set K' : Set F := Metric.cthickening δ₀ (Binf '' K) with hK'def
  have hK'cpt : IsCompact K' := hBKcpt.cthickening
  have hK'V : K' ⊆ V := hδ₀V
  have hB0 : TendstoUniformlyOn B Binf atTop K :=
    tendstoUniformlyOn_of_cPConv (hB.mono_order (Nat.zero_le p))
  rw [Metric.tendstoUniformlyOn_iff] at hB0
  obtain ⟨NB, hNB⟩ := eventually_atTop.mp (hB0 δ₀ hδ₀pos)
  have hBK' : ∀ᶠ k in atTop, Set.MapsTo (B k) K K' := by
    rw [eventually_atTop]
    refine ⟨NB, fun k hk x hx => ?_⟩
    have hclose : dist (Binf x) (B k x) < δ₀ := hNB k hk x hx
    exact Metric.mem_cthickening_of_dist_le (B k x) (Binf x) δ₀ (Binf '' K)
      ⟨x, hx, rfl⟩ (by rw [dist_comm]; exact le_of_lt hclose)
  have hBinfK' : Set.MapsTo Binf K K' := by
    intro x hx
    exact Metric.self_subset_cthickening _ ⟨x, hx, rfl⟩
  refine mapCPConvOn_of_tendstoUniformlyOn hU hKU
    (fun k => ContDiffOn.comp ((hAc k).of_le (by exact_mod_cast le_top))
      ((hBc k).of_le (by exact_mod_cast le_top)) (hmapk k))
    (ContDiffOn.comp (hAinfc.of_le (by exact_mod_cast le_top))
      (hBinfc.of_le (by exact_mod_cast le_top)) hmap) ?_
  intro r hr
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  let l : Filter (ℕ × E) := atTop ×ˢ Filter.principal K
  let p₁ : ℕ × E → FormalMultilinearSeries ℝ F G :=
    fun q => ftaylorSeries ℝ (A q.1) (B q.1 q.2)
  let p₂ : ℕ × E → FormalMultilinearSeries ℝ F G :=
    fun q => ftaylorSeries ℝ Ainf (Binf q.2)
  let q₁ : ℕ × E → FormalMultilinearSeries ℝ E F :=
    fun q => ftaylorSeries ℝ (B q.1) q.2
  let q₂ : ℕ × E → FormalMultilinearSeries ℝ E F :=
    fun q => ftaylorSeries ℝ Binf q.2
  have hAeval : ∀ i : ℕ,
      TendstoUniformlyOn
        (fun k x => iteratedFDeriv ℝ i (A k) (B k x))
        (fun x => iteratedFDeriv ℝ i Ainf (Binf x)) atTop K :=
    fun i => hA.tendstoUniformlyOn_iteratedFDeriv_comp_moving hV hK'cpt hK'V
      hAc hAinfc (tendstoUniformlyOn_of_cPConv (hB.mono_order (Nat.zero_le p)))
      hBK' hBinfK' i
  have hBder : ∀ i : ℕ, i ≤ p →
      TendstoUniformlyOn
        (fun k x => iteratedFDeriv ℝ i (B k) x)
        (fun x => iteratedFDeriv ℝ i Binf x) atTop K :=
    fun i hi => hB.tendstoUniformlyOn_iteratedFDeriv hU hKU
      (fun k => (hBc k).of_le (by exact_mod_cast le_top))
      (hBinfc.of_le (by exact_mod_cast le_top)) hi
  have hcompLittle :
      (fun q : ℕ × E =>
        iteratedFDeriv ℝ r (fun x => A q.1 (B q.1 x)) q.2 -
          iteratedFDeriv ℝ r (fun x => Ainf (Binf x)) q.2)
        =o[l] (fun _ : ℕ × E => (1 : ℝ)) := by
    have htaylor :
        (fun q : ℕ × E =>
          iteratedFDeriv ℝ r (fun x => A q.1 (B q.1 x)) q.2 -
            iteratedFDeriv ℝ r (fun x => Ainf (Binf x)) q.2)
          =ᶠ[l] fun q =>
            (p₁ q).taylorComp (q₁ q) r - (p₂ q).taylorComp (q₂ q) r := by
      change ∀ᶠ q in atTop ×ˢ Filter.principal K,
        (fun q : ℕ × E =>
          iteratedFDeriv ℝ r (fun x => A q.1 (B q.1 x)) q.2 -
            iteratedFDeriv ℝ r (fun x => Ainf (Binf x)) q.2)
          q = ((p₁ q).taylorComp (q₁ q) r - (p₂ q).taylorComp (q₂ q) r)
      rw [eventually_prod_principal_iff]
      refine Eventually.of_forall fun k x hx => ?_
      have hxU : x ∈ U := hKU hx
      have hBkV : B k x ∈ V := hmapk k hxU
      have hBinfV : Binf x ∈ V := hmap hxU
      dsimp [p₁, p₂, q₁, q₂]
      have hcur :
          iteratedFDeriv ℝ r (fun x => A k (B k x)) x =
            (ftaylorSeries ℝ (A k) (B k x)).taylorComp (ftaylorSeries ℝ (B k) x) r := by
        simpa [Function.comp_def] using
          (iteratedFDeriv_comp
          ((hAc k).contDiffAt (hV.mem_nhds hBkV))
          ((hBc k).contDiffAt (hU.mem_nhds hxU))
          (by exact_mod_cast le_top : (r : WithTop ℕ∞) ≤ ∞))
      have hlim :
          iteratedFDeriv ℝ r (fun x => Ainf (Binf x)) x =
            (ftaylorSeries ℝ Ainf (Binf x)).taylorComp (ftaylorSeries ℝ Binf x) r := by
        simpa [Function.comp_def] using
          (iteratedFDeriv_comp
          (hAinfc.contDiffAt (hV.mem_nhds hBinfV))
          (hBinfc.contDiffAt (hU.mem_nhds hxU))
          (by exact_mod_cast le_top : (r : WithTop ℕ∞) ≤ ∞))
      rw [hcur, hlim]
    refine htaylor.trans_isLittleO ?_
    refine FormalMultilinearSeries.taylorComp_sub_taylorComp_isLittleO ?hp ?hpf ?hq1 ?hq2 ?hqf
    · intro i hi
      obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ y ∈ K', ‖iteratedFDeriv ℝ i Ainf y‖ ≤ C := by
        obtain ⟨C, hC⟩ := hK'cpt.bddAbove_image
          ((ContinuousOn.continuousOn_iteratedFDeriv hAinfc hV
            (by exact_mod_cast le_top)).norm.mono hK'V)
        exact ⟨C, fun y hy => hC ⟨y, hy, rfl⟩⟩
      exact isBoundedUnder_prod_principal_of_eventually_forall_le
        ⟨C + 1, TendstoUniformlyOn.eventually_norm_le (hAeval i)
          (fun x hx => hC (Binf x) (hBinfK' hx))⟩
    · intro i hi
      exact TendstoUniformlyOn.isLittleO_sub_const (hAeval i)
    · intro i hi
      obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ x ∈ K, ‖iteratedFDeriv ℝ i Binf x‖ ≤ C := by
        obtain ⟨C, hC⟩ := hK.bddAbove_image
          ((ContinuousOn.continuousOn_iteratedFDeriv hBinfc hU
            (by exact_mod_cast le_top)).norm.mono hKU)
        exact ⟨C, fun x hx => hC ⟨x, hx, rfl⟩⟩
      exact isBoundedUnder_prod_principal_of_eventually_forall_le
        ⟨C + 1, TendstoUniformlyOn.eventually_norm_le (hBder i (hi.trans hr)) hC⟩
    · intro i hi
      obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ x ∈ K, ‖iteratedFDeriv ℝ i Binf x‖ ≤ C := by
        obtain ⟨C, hC⟩ := hK.bddAbove_image
          ((ContinuousOn.continuousOn_iteratedFDeriv hBinfc hU
            (by exact_mod_cast le_top)).norm.mono hKU)
        exact ⟨C, fun x hx => hC ⟨x, hx, rfl⟩⟩
      exact isBoundedUnder_prod_principal_of_forall_le
        ⟨C, fun _ x hx => hC x hx⟩
    · intro i hi
      exact TendstoUniformlyOn.isLittleO_sub_const (hBder i (hi.trans hr))
  have htend : Tendsto
      (fun q : ℕ × E =>
        iteratedFDeriv ℝ r (fun x => A q.1 (B q.1 x)) q.2 -
          iteratedFDeriv ℝ r (fun x => Ainf (Binf x)) q.2)
      l (𝓝 0) := (Asymptotics.isLittleO_one_iff ℝ).mp hcompLittle
  rw [Metric.tendsto_nhds] at htend
  have htail : ∀ᶠ (x : ℕ × E) in atTop ×ˢ Filter.principal K,
      dist
        (iteratedFDeriv ℝ r (fun x_1 => A x.1 (B x.1 x_1)) x.2 -
          iteratedFDeriv ℝ r (fun x => Ainf (Binf x)) x.2) 0 < ε :=
    htend ε hε
  rw [eventually_prod_principal_iff] at htail
  exact htail.mono fun k hk x hx => by
    simpa [dist_eq_norm, norm_sub_rev] using hk x hx



theorem MapCInfConvOnCompacts.comp
    {U : Set E} {V : Set F} (hU : IsOpen U) (hV : IsOpen V)
    [ProperSpace F]
    {B : ℕ → E → F} {Binf : E → F} {A : ℕ → F → G} {Ainf : F → G}
    (hB : MapCInfConvOnCompacts U B Binf)
    (hA : MapCInfConvOnCompacts V A Ainf)
    (hBc : ∀ k, ContDiffOn ℝ (∞ : WithTop ℕ∞) (B k) U)
    (hBinfc : ContDiffOn ℝ (∞ : WithTop ℕ∞) Binf U)
    (hAc : ∀ k, ContDiffOn ℝ (∞ : WithTop ℕ∞) (A k) V)
    (hAinfc : ContDiffOn ℝ (∞ : WithTop ℕ∞) Ainf V)
    (hmap : Set.MapsTo Binf U V) (hmapk : ∀ k, Set.MapsTo (B k) U V) :
    MapCInfConvOnCompacts U (fun k x => A k (B k x)) (fun x => Ainf (Binf x)) := by
  intro K hK hKU p
  exact MapCPConvOn.comp_cInf hU hV hK hKU (hB K hK hKU p) hA
    hBc hBinfc hAc hAinfc hmap hmapk

section BasicClosures

variable {E' P Q : Type*}
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q]



theorem mapCInfConv_const {U : Set E'} (Φ : E' → P) :
    MapCInfConvOnCompacts U (fun _ : ℕ => Φ) Φ := by
  intro K _ _ p ε hε
  exact ⟨0, fun k _ r _ x _ => by
    simpa [mapDerivNorm, sub_self] using hε.le⟩



theorem MapCInfConvOnCompacts.precomp
    {D : Set E'} {U : Set P} (hD : IsOpen D) (hU : IsOpen U)
    [ProperSpace P]
    {A : Nat → P → Q} {Ainf : P → Q}
    (hA : MapCInfConvOnCompacts U A Ainf)
    {f : E' → P} (hf : ContDiffOn ℝ (∞ : WithTop ℕ∞) f D)
    (hmap : Set.MapsTo f D U)
    (hAc : ∀ n, ContDiffOn ℝ (∞ : WithTop ℕ∞) (A n) U)
    (hAinfC : ContDiffOn ℝ (∞ : WithTop ℕ∞) Ainf U) :
    MapCInfConvOnCompacts D
      (fun n x => A n (f x)) (fun x => Ainf (f x)) :=
  MapCInfConvOnCompacts.comp hD hU (mapCInfConv_const f) hA
    (fun _ => hf) hf hAc hAinfC hmap (fun _ => hmap)



theorem MapCPConvOn.prodMk {U K : Set E'} {p : ℕ} (hU : IsOpen U) (hKU : K ⊆ U)
    {u : ℕ → E' → P} {uinf : E' → P} {v : ℕ → E' → Q} {vinf : E' → Q}
    (hu : MapCPConvOn K p u uinf) (hv : MapCPConvOn K p v vinf)
    (huc : ∀ k, ContDiffOn ℝ (∞ : WithTop ℕ∞) (u k) U)
    (huinfc : ContDiffOn ℝ (∞ : WithTop ℕ∞) uinf U)
    (hvc : ∀ k, ContDiffOn ℝ (∞ : WithTop ℕ∞) (v k) U)
    (hvinfc : ContDiffOn ℝ (∞ : WithTop ℕ∞) vinf U) :
    MapCPConvOn K p (fun k y => (u k y, v k y)) (fun y => (uinf y, vinf y)) := by
  intro ε hε
  obtain ⟨k1, hk1⟩ := hu ε hε
  obtain ⟨k2, hk2⟩ := hv ε hε
  refine ⟨max k1 k2, fun k hk r hr x hx => ?_⟩
  have hxU : x ∈ U := hKU hx
  have hle : ((r : ℕ∞) : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by exact_mod_cast le_top
  have hcu : ContDiffAt ℝ (r : ℕ∞) (fun y => u k y - uinf y) x :=
    (((huc k).sub huinfc).contDiffAt (hU.mem_nhds hxU)).of_le hle
  have hcv : ContDiffAt ℝ (r : ℕ∞) (fun y => v k y - vinf y) x :=
    (((hvc k).sub hvinfc).contDiffAt (hU.mem_nhds hxU)).of_le hle
  have heq : (fun y => (u k y, v k y) - (uinf y, vinf y))
      = fun y => (u k y - uinf y, v k y - vinf y) := by
    funext y; simp [Prod.mk_sub_mk]
  have hkey : mapDerivNorm r (fun y => (u k y, v k y)) (fun y => (uinf y, vinf y)) x
      = max (mapDerivNorm r (u k) uinf x) (mapDerivNorm r (v k) vinf x) := by
    simp only [mapDerivNorm]
    rw [heq, iteratedFDeriv_prodMk hcu hcv le_rfl,
      ContinuousMultilinearMap.opNorm_prod]
  rw [hkey]
  exact max_le (hk1 k (le_trans (le_max_left k1 k2) hk) r hr x hx)
    (hk2 k (le_trans (le_max_right k1 k2) hk) r hr x hx)



theorem mapCInfConv_prodMk {U : Set E'} (hU : IsOpen U)
    {u : ℕ → E' → P} {uinf : E' → P} {v : ℕ → E' → Q} {vinf : E' → Q}
    (hu : MapCInfConvOnCompacts U u uinf) (hv : MapCInfConvOnCompacts U v vinf)
    (huc : ∀ k, ContDiffOn ℝ (∞ : WithTop ℕ∞) (u k) U)
    (huinfc : ContDiffOn ℝ (∞ : WithTop ℕ∞) uinf U)
    (hvc : ∀ k, ContDiffOn ℝ (∞ : WithTop ℕ∞) (v k) U)
    (hvinfc : ContDiffOn ℝ (∞ : WithTop ℕ∞) vinf U) :
    MapCInfConvOnCompacts U (fun k y => (u k y, v k y)) (fun y => (uinf y, vinf y)) := by
  intro K hK hKU p
  exact MapCPConvOn.prodMk hU hKU (hu K hK hKU p) (hv K hK hKU p)
    huc huinfc hvc hvinfc




theorem mapCInfConv_pi {ι : Type*} [Fintype ι] {U : Set E'} (hU : IsOpen U)
    {v : ι → ℕ → E' → Q} {vinf : ι → E' → Q}
    (hv : ∀ i, MapCInfConvOnCompacts U (v i) (vinf i))
    (hvc : ∀ i k, ContDiffOn ℝ (∞ : WithTop ℕ∞) (v i k) U)
    (hvinfc : ∀ i, ContDiffOn ℝ (∞ : WithTop ℕ∞) (vinf i) U) :
    MapCInfConvOnCompacts U (fun k y i => v i k y) (fun y i => vinf i y) := by
  intro K hK hKU p ε hε
  choose k0 hk0 using fun i => hv i K hK hKU p ε hε
  refine ⟨Finset.univ.sup k0, fun k hk r hr x hx => ?_⟩
  have hxU : x ∈ U := hKU hx
  have hle : ((r : ℕ∞) : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by exact_mod_cast le_top
  have hcd : ∀ i, ContDiffAt ℝ ((r : ℕ∞) : WithTop ℕ∞) (fun y => v i k y - vinf i y) x :=
    fun i => (((hvc i k).sub (hvinfc i)).contDiffAt (hU.mem_nhds hxU)).of_le hle
  have heq : (fun y => (fun i => v i k y) - fun i => vinf i y)
      = fun y (i : ι) => v i k y - vinf i y := rfl
  have hkey : mapDerivNorm r (fun y i => v i k y) (fun y i => vinf i y) x
      = ‖fun i => iteratedFDeriv ℝ r (fun y => v i k y - vinf i y) x‖ := by
    simp only [mapDerivNorm]
    rw [heq, iteratedFDeriv_pi hcd le_rfl, ContinuousMultilinearMap.opNorm_pi]
  rw [hkey, pi_norm_le_iff_of_nonneg hε.le]
  intro i
  exact hk0 i k (le_trans (Finset.le_sup (Finset.mem_univ i)) hk) r hr x hx





theorem mapCInfConv_clm {F' G' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    [NormedAddCommGroup G'] [NormedSpace ℝ G']
    {U : Set E'} (hU : IsOpen U) (L : F' →L[ℝ] G')
    {u : ℕ → E' → F'} {uinf : E' → F'}
    (hu : MapCInfConvOnCompacts U u uinf)
    (huc : ∀ k, ContDiffOn ℝ (∞ : WithTop ℕ∞) (u k) U)
    (huinfc : ContDiffOn ℝ (∞ : WithTop ℕ∞) uinf U) :
    MapCInfConvOnCompacts U (fun k y => L (u k y)) (fun y => L (uinf y)) := by
  intro K hK hKU p ε hε
  have hL1 : (0 : ℝ) < ‖L‖ + 1 := by positivity
  obtain ⟨k0, hk0⟩ := hu K hK hKU p (ε / (‖L‖ + 1)) (div_pos hε hL1)
  refine ⟨k0, fun k hk r hr x hx => ?_⟩
  have hxU : x ∈ U := hKU hx
  have hle : ((r : ℕ∞) : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by exact_mod_cast le_top
  have hcd : ContDiffAt ℝ ((r : ℕ∞) : WithTop ℕ∞) (fun y => u k y - uinf y) x :=
    (((huc k).sub huinfc).contDiffAt (hU.mem_nhds hxU)).of_le hle
  have heq : (fun y => L (u k y) - L (uinf y)) = ⇑L ∘ fun y => u k y - uinf y := by
    funext y; simp [Function.comp_apply, map_sub]
  have hbase : ‖iteratedFDeriv ℝ r (fun y => u k y - uinf y) x‖ ≤ ε / (‖L‖ + 1) :=
    hk0 k hk r hr x hx
  simp only [mapDerivNorm]
  rw [heq, ContinuousLinearMap.iteratedFDeriv_comp_left L hcd le_rfl]
  calc ‖L.compContinuousMultilinearMap (iteratedFDeriv ℝ r (fun y => u k y - uinf y) x)‖
      ≤ ‖L‖ * ‖iteratedFDeriv ℝ r (fun y => u k y - uinf y) x‖ :=
        ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
    _ ≤ (‖L‖ + 1) * (ε / (‖L‖ + 1)) := by
        refine mul_le_mul (by linarith [norm_nonneg L]) hbase (norm_nonneg _) hL1.le
    _ = ε := mul_div_cancel₀ ε (ne_of_gt hL1)



theorem MapCInfConvOnCompacts.pullbackForm
    {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [ProperSpace ((W →L[ℝ] W →L[ℝ] ℝ) × (V →L[ℝ] W))]
    {U : Set E'} (hU : IsOpen U)
    {B : ℕ → E' → W →L[ℝ] W →L[ℝ] ℝ} {Binf : E' → W →L[ℝ] W →L[ℝ] ℝ}
    {D : ℕ → E' → V →L[ℝ] W} {Dinf : E' → V →L[ℝ] W}
    (hB : MapCInfConvOnCompacts U B Binf)
    (hD : MapCInfConvOnCompacts U D Dinf)
    (hBc : ∀ k, ContDiffOn ℝ (∞ : WithTop ℕ∞) (B k) U)
    (hBinfC : ContDiffOn ℝ (∞ : WithTop ℕ∞) Binf U)
    (hDc : ∀ k, ContDiffOn ℝ (∞ : WithTop ℕ∞) (D k) U)
    (hDinfC : ContDiffOn ℝ (∞ : WithTop ℕ∞) Dinf U) :
    MapCInfConvOnCompacts U
      (fun k z => pullbackForm (B k z, D k z))
      (fun z => pullbackForm (Binf z, Dinf z)) := by
  have hpair : MapCInfConvOnCompacts U
      (fun k z => (B k z, D k z)) (fun z => (Binf z, Dinf z)) :=
    mapCInfConv_prodMk hU hB hD hBc hBinfC hDc hDinfC
  apply MapCInfConvOnCompacts.comp hU isOpen_univ hpair
    (mapCInfConv_const (U := Set.univ)
      (_root_.DifferentialGeometry.HCGCompactness.pullbackForm (E := V) (F := W)))
  · exact fun k => (hBc k).prodMk (hDc k)
  · exact hBinfC.prodMk hDinfC
  · exact fun _ => pullbackForm.contDiff.contDiffOn
  · exact pullbackForm.contDiff.contDiffOn
  · exact fun _ _ => Set.mem_univ _
  · exact fun _ _ _ => Set.mem_univ _

end BasicClosures



theorem MapCInfConvOnCompacts.ringInv
    {E R : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedRing R] [NormedAlgebra ℝ R] [HasSummableGeomSeries R]
    [ProperSpace R]
    {U : Set E} (hU : IsOpen U)
    {A : ℕ → E → R} {Ainf : E → R}
    (hA : MapCInfConvOnCompacts U A Ainf)
    (hAc : ∀ k, ContDiffOn ℝ (∞ : WithTop ℕ∞) (A k) U)
    (hAinfc : ContDiffOn ℝ (∞ : WithTop ℕ∞) Ainf U)
    (hunit : ∀ k x, x ∈ U → IsUnit (A k x))
    (hunitInf : ∀ x, x ∈ U → IsUnit (Ainf x)) :
    MapCInfConvOnCompacts U
      (fun k x => Ring.inverse (A k x))
      (fun x => Ring.inverse (Ainf x)) := by
  apply MapCInfConvOnCompacts.comp hU Units.isOpen hA
    (mapCInfConv_const (U := {y : R | IsUnit y}) Ring.inverse)
    hAc hAinfc
    (fun _ => contDiffOn_ringInverse (𝕜 := ℝ) (∞ : WithTop ℕ∞))
    (contDiffOn_ringInverse (𝕜 := ℝ) (∞ : WithTop ℕ∞))
  · exact fun x hx => hunitInf x hx
  · exact fun k x hx => hunit k x hx

end HCGCompactness
end DifferentialGeometry
