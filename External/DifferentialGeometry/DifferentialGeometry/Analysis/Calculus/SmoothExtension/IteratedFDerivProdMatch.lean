import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.TangentCone.Prod

noncomputable section
open Set Filter Topology
open scoped ContDiff

namespace DifferentialGeometry
namespace Analysis

section DirectionalCommutation

theorem fderivWithin_iteratedFDerivWithin_apply_eq {G W : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {s : Set G} (hs : UniqueDiffOn ℝ s) (hs' : s ⊆ closure (interior s))
    (n : ℕ) {f : G → W} (hf : ContDiffOn ℝ ∞ f s) (u : G) :
    ∀ x ∈ s, fderivWithin ℝ (iteratedFDerivWithin ℝ n f s) s x u
      = iteratedFDerivWithin ℝ n (fun y => fderivWithin ℝ f s y u) s x := by
  induction n with
  | zero =>

    intro x hx
    rw [iteratedFDerivWithin_zero_eq_comp,
      LinearIsometryEquiv.comp_fderivWithin _ (hs x hx)]
    ext m
    rw [ContinuousLinearMap.comp_apply, iteratedFDerivWithin_zero_apply]
    rfl
  | succ n IH =>
    intro x hx

    set H := iteratedFDerivWithin ℝ n f s with hH_def

    set e := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => G) W).symm with he_def

    have hLHS : fderivWithin ℝ (iteratedFDerivWithin ℝ (n + 1) f s) s x u
        = e (fderivWithin ℝ (fderivWithin ℝ H s) s x u) := by
      rw [iteratedFDerivWithin_succ_eq_comp_left]
      rw [e.comp_fderivWithin (f := fderivWithin ℝ H s) (hs x hx)]
      rfl

    have hIHeq : Set.EqOn (iteratedFDerivWithin ℝ n (fun y => fderivWithin ℝ f s y u) s)
        (fun y => fderivWithin ℝ H s y u) s := fun y hy => (IH y hy).symm
    have hRHS : iteratedFDerivWithin ℝ (n + 1) (fun y => fderivWithin ℝ f s y u) s x
        = e (fderivWithin ℝ (fun y => fderivWithin ℝ H s y u) s x) := by
      rw [iteratedFDerivWithin_succ_eq_comp_left, Function.comp_apply,
        fderivWithin_congr hIHeq (hIHeq hx)]

    rw [hLHS, hRHS]
    congr 1

    have hHC2 : ContDiffWithinAt ℝ 2 H s x := by
      refine (hf x hx).iteratedFDerivWithin_right hs ?_ hx
      have h2n : (2 : WithTop ℕ∞) + (n : WithTop ℕ∞) = ((2 + n : ℕ∞) : WithTop ℕ∞) := by norm_cast
      rw [h2n]; exact_mod_cast le_top
    have hn2 : minSmoothness ℝ 2 ≤ (2 : WithTop ℕ∞) := le_of_eq minSmoothness_of_isRCLikeNormedField
    have hsymH : IsSymmSndFDerivWithinAt ℝ H s x :=
      hHC2.isSymmSndFDerivWithinAt hn2 hs (hs' hx) hx
    have hHdiff : DifferentiableWithinAt ℝ (fderivWithin ℝ H s) s x :=
      (hHC2.fderivWithin_right hs (m := 1) le_rfl hx).differentiableWithinAt (by simp)
    have hflip : fderivWithin ℝ (fun y => fderivWithin ℝ H s y u) s x
        = (fderivWithin ℝ (fderivWithin ℝ H s) s x).flip u := by
      rw [fderivWithin_clm_apply (hs x hx) hHdiff (differentiableWithinAt_const u),
        fderivWithin_const_apply, ContinuousLinearMap.comp_zero, zero_add]
    refine ContinuousLinearMap.ext (fun v => ?_)
    rw [hflip, ContinuousLinearMap.flip_apply]
    exact hsymH.eq u v

end DirectionalCommutation

section ProdMatch

variable {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem iteratedFDerivWithin_prod_match_zero_of_jet_vanish
    {D : ℝ × E → F} {V : Set E} (hV : IsOpen V)
    (hD : ContDiffOn ℝ ∞ D (Set.Ici (0:ℝ) ×ˢ V))
    (hjet : ∀ i : ℕ, ∀ w ∈ V,
      iteratedDerivWithin i (fun t => D (t, w)) (Set.Ici 0) 0 = 0)
    (n : ℕ) {z : E} (hz : z ∈ V) :
    iteratedFDerivWithin ℝ n D (Set.Ici (0:ℝ) ×ˢ V) (0, z) = 0 := by
  set S : Set (ℝ × E) := Set.Ici (0:ℝ) ×ˢ V with hS_def
  have hUD : UniqueDiffOn ℝ S := UniqueDiffOn.prod (uniqueDiffOn_Ici 0) hV.uniqueDiffOn

  have hSclo : S ⊆ closure (interior S) := by
    have hsub : Set.Ioi (0:ℝ) ×ˢ V ⊆ interior S := by
      rw [hS_def, interior_prod_eq, interior_Ici, hV.interior_eq]
    refine fun p hp => closure_mono hsub ?_
    rw [hS_def] at hp
    rw [closure_prod_eq, closure_Ioi]
    exact ⟨hp.1, subset_closure hp.2⟩

  clear_value S
  induction n generalizing D z with
  | zero =>

    have h0 : D (0, z) = 0 := by
      have := hjet 0 z hz
      rwa [iteratedDerivWithin_zero] at this
    ext m
    rw [iteratedFDerivWithin_zero_apply, h0]
    simp
  | succ n IH =>

    have hmem : ((0:ℝ), z) ∈ S := by rw [hS_def]; exact ⟨Set.self_mem_Ici, hz⟩
    rw [iteratedFDerivWithin_succ_eq_comp_left, Function.comp_apply]
    have hsuff : fderivWithin ℝ (iteratedFDerivWithin ℝ n D S) S (0, z) = 0 := by

      refine ContinuousLinearMap.ext (fun p => ?_)
      obtain ⟨t, e⟩ := p
      have hsplit : (t, e) = t • ((1:ℝ), (0:E)) + ((0:ℝ), e) := by
        simp [Prod.smul_mk, Prod.mk_add_mk]
      rw [show (0 : (ℝ × E) →L[ℝ] ((ℝ × E) [×n]→L[ℝ] F)) (t, e) = 0 from rfl, hsplit, map_add,
        map_smul]

      have htrans : fderivWithin ℝ (iteratedFDerivWithin ℝ n D S) S (0, z) ((1:ℝ), (0:E)) = 0 := by
        rw [fderivWithin_iteratedFDerivWithin_apply_eq hUD hSclo n hD ((1:ℝ), (0:E)) (0, z) hmem]

        have hDt : ContDiffOn ℝ ∞ (fun y => fderivWithin ℝ D S y ((1:ℝ), (0:E))) S := by
          have hfd : ContDiffOn ℝ ∞ (fderivWithin ℝ D S) S :=
            hD.fderivWithin hUD (by exact_mod_cast le_top)
          exact hfd.clm_apply contDiffOn_const

        have hjett : ∀ i : ℕ, ∀ w ∈ V,
            iteratedDerivWithin i (fun t => fderivWithin ℝ D S (t, w) ((1:ℝ), (0:E)))
              (Set.Ici 0) 0 = 0 := by
          intro i w hw

          have hcongr : Set.EqOn
              (fun t => fderivWithin ℝ D S (t, w) ((1:ℝ), (0:E)))
              (derivWithin (fun t => D (t, w)) (Set.Ici 0)) (Set.Ici 0) := by
            intro t ht
            have hmaps : Set.MapsTo (fun r : ℝ => (r, w)) (Set.Ici 0) S :=
              fun r hr => by rw [hS_def]; exact ⟨hr, hw⟩
            have hpairc : HasDerivWithinAt (fun r : ℝ => (r, w)) ((1:ℝ), (0:E)) (Set.Ici 0) t :=
              (hasDerivWithinAt_id t (Set.Ici 0)).prodMk (hasDerivWithinAt_const t _ w)
            have hDfd : HasFDerivWithinAt D (fderivWithin ℝ D S (t, w)) S (t, w) :=
              ((hD (t, w) (hmaps ht)).differentiableWithinAt (by simp)).hasFDerivWithinAt
            have hcomp : HasDerivWithinAt (fun r : ℝ => D (r, w))
                (fderivWithin ℝ D S (t, w) ((1:ℝ), (0:E))) (Set.Ici 0) t :=
              (hDfd.comp_hasDerivWithinAt t hpairc hmaps)
            exact (hcomp.derivWithin (uniqueDiffOn_Ici 0 t ht)).symm
          rw [iteratedDerivWithin_congr hcongr Set.self_mem_Ici,
            ← iteratedDerivWithin_succ']
          exact hjet (i + 1) w hw
        exact IH hjett hz hDt

      have hseam : fderivWithin ℝ (iteratedFDerivWithin ℝ n D S) S (0, z) ((0:ℝ), e) = 0 := by

        set ι : E → ℝ × E := fun v => (0, v) with hι_def
        set g : ℝ × E → (ℝ × E) [×n]→L[ℝ] F := iteratedFDerivWithin ℝ n D S with hg_def
        have hιmaps : Set.MapsTo ι V S := fun v hv => by
          rw [hS_def, hι_def]; exact ⟨Set.self_mem_Ici, hv⟩
        have hιfd : HasFDerivWithinAt ι (ContinuousLinearMap.inr ℝ ℝ E) V z := by
          simpa [hι_def] using (ContinuousLinearMap.inr ℝ ℝ E).hasFDerivWithinAt
        have hιdiff : DifferentiableWithinAt ℝ ι V z := hιfd.differentiableWithinAt
        have hgdiff : DifferentiableWithinAt ℝ g S (0, z) :=
          (hD.differentiableOn_iteratedFDerivWithin (by exact_mod_cast ENat.coe_lt_top n) hUD)
            (0, z) hmem

        have hcompzero : fderivWithin ℝ (g ∘ ι) V z = 0 := by
          have hEq : Set.EqOn (g ∘ ι) (fun _ => 0) V := by
            intro v hv
            simpa [hg_def, hι_def, Function.comp_apply] using IH hjet hv hD
          rw [fderivWithin_congr hEq (hEq hz), fderivWithin_const_apply]

        have hchain : fderivWithin ℝ (g ∘ ι) V z
            = (fderivWithin ℝ g S (0, z)).comp (ContinuousLinearMap.inr ℝ ℝ E) := by
          rw [fderivWithin_comp z hgdiff hιdiff hιmaps (hV.uniqueDiffOn z hz),
            hιfd.fderivWithin (hV.uniqueDiffOn z hz)]
        have happ := congrArg (fun L => L e) (hchain.symm.trans hcompzero)
        simpa [hg_def, ContinuousLinearMap.inr_apply] using happ
      rw [htrans, hseam, smul_zero, add_zero]
    rw [hsuff]
    simp only [LinearIsometryEquiv.map_zero]

theorem iteratedFDerivWithin_prod_match
    {Φ ψ : ℝ × E → F} {V : Set E} (hV : IsOpen V)
    (hΦ : ContDiffOn ℝ ∞ Φ (Set.Ici (0:ℝ) ×ˢ V)) (hψ : ContDiffOn ℝ ∞ ψ (Set.Ici (0:ℝ) ×ˢ V))
    (htjet : ∀ i : ℕ, Set.EqOn (fun w => iteratedDerivWithin i (fun t => Φ (t, w)) (Set.Ici 0) 0)
                               (fun w => iteratedDerivWithin i (fun t => ψ (t, w)) (Set.Ici 0) 0) V)
    (n : ℕ) {z : E} (hz : z ∈ V) :
    iteratedFDerivWithin ℝ n Φ (Set.Ici (0:ℝ) ×ˢ V) (0, z)
      = iteratedFDerivWithin ℝ n ψ (Set.Ici (0:ℝ) ×ˢ V) (0, z) := by

  set S : Set (ℝ × E) := Set.Ici (0:ℝ) ×ˢ V with hS_def
  have hUD : UniqueDiffOn ℝ S := UniqueDiffOn.prod (uniqueDiffOn_Ici 0) hV.uniqueDiffOn
  have hmem : ((0:ℝ), z) ∈ S := ⟨Set.self_mem_Ici, hz⟩
  have hΦn : ContDiffWithinAt ℝ n Φ S (0, z) :=
    (hΦ (0, z) hmem).of_le (by exact_mod_cast le_top)
  have hψn : ContDiffWithinAt ℝ n ψ S (0, z) :=
    (hψ (0, z) hmem).of_le (by exact_mod_cast le_top)

  have hsub : iteratedFDerivWithin ℝ n (Φ - ψ) S (0, z)
      = iteratedFDerivWithin ℝ n Φ S (0, z) - iteratedFDerivWithin ℝ n ψ S (0, z) :=
    iteratedFDerivWithin_sub_apply hΦn hψn hUD hmem

  have hD : ContDiffOn ℝ ∞ (Φ - ψ) S := hΦ.sub hψ

  have hjet : ∀ i : ℕ, ∀ w ∈ V,
      iteratedDerivWithin i (fun t => (Φ - ψ) (t, w)) (Set.Ici 0) 0 = 0 := by
    intro i w hw
    have hΦw : ContDiffWithinAt ℝ i (fun t => Φ (t, w)) (Set.Ici 0) 0 := by
      have hcomp : ContDiffWithinAt ℝ ∞ (fun t : ℝ => Φ (t, w)) (Set.Ici 0) 0 := by
        have hmaps : Set.MapsTo (fun t : ℝ => (t, w)) (Set.Ici 0) S :=
          fun t ht => ⟨ht, hw⟩
        have hpair : ContDiffWithinAt ℝ ∞ (fun t : ℝ => (t, w)) (Set.Ici 0) 0 :=
          (contDiff_id.prodMk contDiff_const).contDiffWithinAt
        exact (hΦ (0, w) ⟨Set.self_mem_Ici, hw⟩).comp 0 hpair hmaps
      exact hcomp.of_le (by exact_mod_cast le_top)
    have hψw : ContDiffWithinAt ℝ i (fun t => ψ (t, w)) (Set.Ici 0) 0 := by
      have hcomp : ContDiffWithinAt ℝ ∞ (fun t : ℝ => ψ (t, w)) (Set.Ici 0) 0 := by
        have hmaps : Set.MapsTo (fun t : ℝ => (t, w)) (Set.Ici 0) S :=
          fun t ht => ⟨ht, hw⟩
        have hpair : ContDiffWithinAt ℝ ∞ (fun t : ℝ => (t, w)) (Set.Ici 0) 0 :=
          (contDiff_id.prodMk contDiff_const).contDiffWithinAt
        exact (hψ (0, w) ⟨Set.self_mem_Ici, hw⟩).comp 0 hpair hmaps
      exact hcomp.of_le (by exact_mod_cast le_top)
    have hsubt : (fun t => (Φ - ψ) (t, w)) = (fun t => Φ (t, w)) - (fun t => ψ (t, w)) := by
      funext t; simp [Pi.sub_apply]
    have htjetw : iteratedDerivWithin i (fun t => Φ (t, w)) (Set.Ici 0) 0
        = iteratedDerivWithin i (fun t => ψ (t, w)) (Set.Ici 0) 0 := htjet i hw
    rw [hsubt, iteratedDerivWithin_sub Set.self_mem_Ici (uniqueDiffOn_Ici 0) hΦw hψw,
      htjetw, sub_self]

  have hzero : iteratedFDerivWithin ℝ n (Φ - ψ) S (0, z) = 0 :=
    iteratedFDerivWithin_prod_match_zero_of_jet_vanish hV hD hjet n hz
  rw [hzero] at hsub
  exact sub_eq_zero.mp hsub.symm

end ProdMatch

end Analysis
end DifferentialGeometry
