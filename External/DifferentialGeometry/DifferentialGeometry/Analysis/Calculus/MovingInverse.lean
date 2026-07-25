import DifferentialGeometry.Analysis.Calculus.MovingImplicit
import Mathlib.Topology.OpenPartialHomeomorph.Continuity

set_option autoImplicit false









noncomputable section

open Filter Set
open scoped ContDiff Topology

namespace DifferentialGeometry
namespace Analysis

open HCGCompactness

private theorem fderiv_inv_of_local
    {X : Type*}
    [NormedAddCommGroup X] [NormedSpace Real X]
    {f g : X → X} {x y : X}
    (hf : DifferentiableAt Real f x)
    (hg : DifferentiableAt Real g y)
    (hxy : f x = y) (hyx : g y = x)
    (hleft : Filter.EventuallyEq (nhds x) (fun z ↦ g (f z)) id)
    (hright : Filter.EventuallyEq (nhds y) (fun z ↦ f (g z)) id) :
    (fderiv Real f x).IsInvertible := by
  let A : X →L[Real] X := fderiv Real f x
  let B : X →L[Real] X := fderiv Real g y
  have hgfx : HasFDerivAt g B (f x) := by
    simpa only [B, hxy] using hg.hasFDerivAt
  have hfgy : HasFDerivAt f A (g y) := by
    simpa only [A, hyx] using hf.hasFDerivAt
  have hBA' : HasFDerivAt (fun z ↦ g (f z)) (B.comp A) x := by
    exact hgfx.comp x hf.hasFDerivAt
  have hAB' : HasFDerivAt (fun z ↦ f (g z)) (A.comp B) y := by
    exact hfgy.comp y hg.hasFDerivAt
  have hBA : B.comp A = ContinuousLinearMap.id Real X :=
    (hBA'.congr_of_eventuallyEq hleft.symm).unique
      (hasFDerivAt_id (𝕜 := Real) x)
  have hAB : A.comp B = ContinuousLinearMap.id Real X :=
    (hAB'.congr_of_eventuallyEq hright.symm).unique
      (hasFDerivAt_id (𝕜 := Real) y)
  exact ContinuousLinearMap.IsInvertible.of_inverse hAB hBA

private theorem partial_sub_snd
    {X : Type*}
    [NormedAddCommGroup X] [NormedSpace Real X]
    {f : X → X} {p x : X}
    (hf : DifferentiableAt Real f x) :
    partialFDeriv₂ (fun z : X × X ↦ f z.2 - z.1) p x =
      fderiv Real f x := by
  have hcomp : HasFDerivAt (fun z : X × X ↦ f z.2)
      ((fderiv Real f x).comp (ContinuousLinearMap.snd Real X X)) (p, x) := by
    simpa using hf.hasFDerivAt.comp (p, x) hasFDerivAt_snd
  have hderiv : fderiv Real (fun z : X × X ↦ f z.2 - z.1) (p, x) =
      (fderiv Real f x).comp (ContinuousLinearMap.snd Real X X) -
        ContinuousLinearMap.fst Real X X :=
    (hcomp.sub hasFDerivAt_fst).fderiv
  rw [partialFDeriv₂, hderiv]
  ext v
  simp

namespace OpenPartialHomeomorph




theorem exists_symm_convOn_ball
    {X : Type*}
    [NormedAddCommGroup X] [NormedSpace Real X]
    [FiniteDimensional Real X]
    {e : Nat → OpenPartialHomeomorph X X}
    {eInf : OpenPartialHomeomorph X X}
    {Q : Set X} {delta : Real}
    (hQ : IsOpen Q)
    (hforward : MapCInfConvOnCompacts Q
      (fun n ↦ (e n : X → X)) eInf)
    (hsource : Filter.Eventually
      (fun n : Nat ↦ closure Q ⊆ (e n).source) Filter.atTop)
    (hstage_cd : ∀ n, ContDiffOn Real ∞ (e n : X → X) Q)
    (hdelta : 0 < delta)
    (htarget : ∀ n, Metric.closedBall 0 delta ⊆ (e n).target)
    (htargetInf : Metric.closedBall 0 delta ⊆ eInf.target)
    (hInf_cd : ContDiffOn Real ∞ eInf (interior eInf.source))
    (hInf_symm_cd : ContDiffOn Real ∞ eInf.symm (Metric.ball 0 delta))
    (hbase : eInf.symm 0 ∈ Q) :
    ∃ delta₀ : Real,
      0 < delta₀ ∧ delta₀ < delta ∧
      eInf.symm '' Metric.closedBall 0 delta₀ ⊆ Q ∧
      Filter.Eventually
        (fun n : Nat ↦ Set.MapsTo (e n).symm
          (Metric.closedBall 0 delta₀) Q) Filter.atTop ∧
      MapCInfConvOnCompacts (Metric.ball 0 delta₀)
        (fun n ↦ ((e n).symm : X → X)) eInf.symm := by
  have hzero_closed : (0 : X) ∈ Metric.closedBall 0 delta := by
    simp only [Metric.mem_closedBall, dist_self, hdelta.le]
  have hzero_target : (0 : X) ∈ eInf.target := htargetInf hzero_closed
  have hbase_source : eInf.symm 0 ∈ eInf.source := eInf.map_target hzero_target
  have hzero_ball : (0 : X) ∈ Metric.ball 0 delta := by
    simpa only [Metric.mem_ball, dist_self] using hdelta
  have hsymm_at : ContDiffAt Real ∞ (eInf.symm : X → X) 0 :=
    hInf_symm_cd.contDiffAt (Metric.isOpen_ball.mem_nhds hzero_ball)
  have hpre : eInf.symm ⁻¹' (Q ∩ eInf.source) ∈ nhds (0 : X) :=
    hsymm_at.continuousAt
      ((hQ.inter eInf.open_source).mem_nhds ⟨hbase, hbase_source⟩)
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp hpre
  let r₀ : Real := min r (delta / 2)
  have hr₀ : 0 < r₀ := by
    exact lt_min hr (half_pos hdelta)
  have hr₀r : r₀ ≤ r := min_le_left _ _
  have hr₀delta : r₀ < delta :=
    (min_le_right r (delta / 2)).trans_lt (half_lt_self hdelta)
  let S : Set X := Q ∩ eInf.source
  let W₀ : Set X := Metric.ball 0 r₀
  let D : Set (X × X) := W₀ ×ˢ S
  let F : Nat → X × X → X := fun n z ↦ e n z.2 - z.1
  let FInf : X × X → X := fun z ↦ eInf z.2 - z.1
  let PhiInf : X → X := eInf.symm
  have hS_open : IsOpen S := hQ.inter eInf.open_source
  have hW₀_open : IsOpen W₀ := Metric.isOpen_ball
  have hD_open : IsOpen D := hW₀_open.prod hS_open
  have hW₀_map : Set.MapsTo PhiInf W₀ S := by
    intro w hw
    exact hrsub (Metric.ball_subset_ball hr₀r hw)
  have hzero_W₀ : (0 : X) ∈ W₀ := by
    simpa only [W₀, Metric.mem_ball, dist_self] using hr₀
  have hK_W₀ : ({0} : Set X) ⊆ W₀ := by
    intro w hw
    have hwzero : w = 0 := by
      simpa only [Set.mem_singleton_iff] using hw
    subst w
    exact hzero_W₀
  have hInf_source_cd : ContDiffOn Real ∞ (eInf : X → X) eInf.source := by
    simpa only [eInf.open_source.interior_eq] using hInf_cd
  have hInf_S_cd : ContDiffOn Real ∞ (eInf : X → X) S :=
    hInf_source_cd.mono inter_subset_right
  have hstage_S_cd : ∀ n, ContDiffOn Real ∞ (e n : X → X) S :=
    fun n ↦ (hstage_cd n).mono inter_subset_left
  have hF_cd : ∀ n, ContDiffOn Real ∞ (F n) D := by
    intro n
    exact ((hstage_S_cd n).comp contDiff_snd.contDiffOn
      (fun z hz ↦ hz.2)).sub contDiff_fst.contDiffOn
  have hFInf_cd : ContDiffOn Real ∞ FInf D :=
    (hInf_S_cd.comp contDiff_snd.contDiffOn
      (fun z hz ↦ hz.2)).sub contDiff_fst.contDiffOn
  have hPhiInf_cd : ContDiffOn Real ∞ PhiInf W₀ := by
    apply hInf_symm_cd.mono
    intro w hw
    exact Metric.ball_subset_ball hr₀delta.le hw
  have hgraph : Set.MapsTo (fun w ↦ (w, PhiInf w)) W₀ D := by
    intro w hw
    exact ⟨hw, hW₀_map hw⟩
  have hroot : ∀ w ∈ W₀, FInf (w, PhiInf w) = 0 := by
    intro w hw
    have hwdelta : w ∈ Metric.closedBall (0 : X) delta := by
      rw [Metric.mem_closedBall]
      exact (Metric.mem_ball.mp
        (Metric.ball_subset_ball hr₀delta.le hw)).le
    have hwt : w ∈ eInf.target := htargetInf hwdelta
    dsimp only [FInf, PhiInf]
    rw [eInf.right_inv hwt, sub_self]
  have hinv : ∀ w ∈ ({0} : Set X),
      (partialFDeriv₂ FInf w (PhiInf w)).IsInvertible := by
    intro w hw
    have hwzero : w = 0 := by simpa only [Set.mem_singleton_iff] using hw
    subst w
    have hfAt : DifferentiableAt Real (eInf : X → X) (eInf.symm 0) :=
      (hInf_source_cd.contDiffAt
        (eInf.open_source.mem_nhds hbase_source)).differentiableAt (by simp)
    have hgAt : DifferentiableAt Real (eInf.symm : X → X) 0 :=
      hsymm_at.differentiableAt (by simp)
    have hforward_zero : eInf (eInf.symm 0) = 0 := eInf.right_inv hzero_target
    have hderiv_inv : (fderiv Real (eInf : X → X) (eInf.symm 0)).IsInvertible :=
      fderiv_inv_of_local hfAt hgAt hforward_zero rfl
        (eInf.eventually_left_inverse hbase_source)
        (eInf.eventually_right_inverse hzero_target)
    change (partialFDeriv₂ (fun z : X × X ↦ eInf z.2 - z.1)
      0 (eInf.symm 0)).IsInvertible
    rw [partial_sub_snd hfAt]
    exact hderiv_inv
  obtain ⟨T⟩ := exists_compactRootTube hD_open hW₀_open
    isCompact_singleton hK_W₀ hFInf_cd hPhiInf_cd hgraph hroot hinv
  have hforward_S : MapCInfConvOnCompacts S
      (fun n ↦ (e n : X → X)) eInf := by
    intro K hK hKS p
    exact hforward K hK (hKS.trans inter_subset_left) p
  have hsnd_conv : MapCInfConvOnCompacts D
      (fun _ : Nat ↦ (fun z : X × X ↦ z.2)) (fun z : X × X ↦ z.2) :=
    mapCInfConv_const (U := D) (fun z : X × X ↦ z.2)
  have he_snd_conv : MapCInfConvOnCompacts D
      (fun n z ↦ e n z.2) (fun z ↦ eInf z.2) :=
    MapCInfConvOnCompacts.comp hD_open hS_open hsnd_conv hforward_S
      (fun _ ↦ contDiff_snd.contDiffOn) contDiff_snd.contDiffOn
      hstage_S_cd hInf_S_cd
      (fun z hz ↦ hz.2) (fun _ z hz ↦ hz.2)
  have hfst_conv : MapCInfConvOnCompacts D
      (fun _ : Nat ↦ (fun z : X × X ↦ z.1)) (fun z : X × X ↦ z.1) :=
    mapCInfConv_const (U := D) (fun z : X × X ↦ z.1)
  have hpair_conv : MapCInfConvOnCompacts D
      (fun n z ↦ (e n z.2, z.1)) (fun z ↦ (eInf z.2, z.1)) :=
    mapCInfConv_prodMk hD_open he_snd_conv hfst_conv
      (fun n ↦ (hstage_S_cd n).comp contDiff_snd.contDiffOn
        (fun z hz ↦ hz.2))
      (hInf_S_cd.comp contDiff_snd.contDiffOn (fun z hz ↦ hz.2))
      (fun _ ↦ contDiff_fst.contDiffOn) contDiff_fst.contDiffOn
  let subMap : X × X → X := fun z ↦ z.1 - z.2
  have hsub_cd : ContDiffOn Real ∞ subMap Set.univ :=
    contDiff_fst.contDiffOn.sub contDiff_snd.contDiffOn
  have hF_conv : MapCInfConvOnCompacts D F FInf := by
    have hcomp := MapCInfConvOnCompacts.comp hD_open isOpen_univ hpair_conv
      (mapCInfConv_const (U := Set.univ) subMap)
      (fun n ↦ (hstage_S_cd n).comp contDiff_snd.contDiffOn
          (fun z hz ↦ hz.2) |>.prodMk contDiff_fst.contDiffOn)
      ((hInf_S_cd.comp contDiff_snd.contDiffOn
          (fun z hz ↦ hz.2)).prodMk contDiff_fst.contDiffOn)
      (fun _ ↦ hsub_cd) hsub_cd
      (fun _ _ ↦ Set.mem_univ _) (fun _ _ _ ↦ Set.mem_univ _)
    simpa only [F, FInf, subMap] using hcomp
  obtain ⟨Nroot, Phi, hPhi_conv, hPhi_cd, hspec, huniq⟩ :=
    T.exists_root_cInf hF_cd hF_conv
  have hzero_TW : (0 : X) ∈ T.W := T.K_subset_W (by simp)
  obtain ⟨b, hb, hbsub⟩ :=
    Metric.mem_nhds_iff.mp (T.isOpen_W.mem_nhds hzero_TW)
  let delta₀ : Real := min (b / 2) (delta / 2)
  have hdelta₀ : 0 < delta₀ := lt_min (half_pos hb) (half_pos hdelta)
  have hdelta₀b : delta₀ < b :=
    (min_le_left (b / 2) (delta / 2)).trans_lt (half_lt_self hb)
  have hdelta₀delta : delta₀ < delta :=
    (min_le_right (b / 2) (delta / 2)).trans_lt (half_lt_self hdelta)
  have hclosed_TW : Metric.closedBall (0 : X) delta₀ ⊆ T.W := by
    intro w hw
    apply hbsub
    rw [Metric.mem_ball]
    exact (Metric.mem_closedBall.mp hw).trans_lt hdelta₀b
  have hball_TW : Metric.ball (0 : X) delta₀ ⊆ T.W :=
    (Metric.ball_subset_closedBall.trans hclosed_TW)
  have hInf_maps : eInf.symm '' Metric.closedBall (0 : X) delta₀ ⊆ Q := by
    rintro _ ⟨w, hw, rfl⟩
    have hwW₀ : w ∈ W₀ := T.closure_W_subset (subset_closure (hclosed_TW hw))
    exact (hW₀_map hwW₀).1
  obtain ⟨Nsource, hNsource⟩ := eventually_atTop.mp hsource
  let N : Nat := max Nroot Nsource
  have hselected_Q : ∀ n ≥ N, Set.MapsTo (Phi n)
      (Metric.closedBall (0 : X) delta₀) Q := by
    intro n hn w hw
    have hnroot : Nroot ≤ n := (Nat.le_max_left _ _).trans hn
    have hwTW : w ∈ T.W := hclosed_TW hw
    have hwclosure : w ∈ closure T.W := subset_closure hwTW
    have hsp := hspec n hnroot w hwclosure
    have hpairD : (w, Phi n w) ∈ D := by
      apply T.tube_subset w hwclosure
      rw [Metric.mem_closedBall]
      exact hsp.1.le.trans (by linarith [T.rho_pos])
    exact hpairD.2.1
  have heq_closed : ∀ n ≥ N, Set.EqOn (Phi n) (e n).symm
      (Metric.closedBall (0 : X) delta₀) := by
    intro n hn w hw
    have hnroot : Nroot ≤ n := (Nat.le_max_left _ _).trans hn
    have hnsource : Nsource ≤ n := (Nat.le_max_right _ _).trans hn
    have hPhiQ : Phi n w ∈ Q := hselected_Q n hn hw
    have hPhiSource : Phi n w ∈ (e n).source :=
      hNsource n hnsource (subset_closure hPhiQ)
    have hwTarget : w ∈ (e n).target := by
      apply htarget n
      rw [Metric.mem_closedBall]
      exact (Metric.mem_closedBall.mp hw).trans hdelta₀delta.le
    have hwTW : w ∈ T.W := hclosed_TW hw
    have hroot_n := (hspec n hnroot w (subset_closure hwTW)).2.1
    have hew : e n (Phi n w) = w := by
      exact sub_eq_zero.mp hroot_n
    exact ((e n).eq_symm_apply hPhiSource hwTarget).mpr hew
  have hmaps_eventually : Filter.Eventually
      (fun n : Nat ↦ Set.MapsTo (e n).symm
        (Metric.closedBall (0 : X) delta₀) Q) Filter.atTop := by
    apply eventually_atTop.mpr
    refine ⟨N, fun n hn w hw ↦ ?_⟩
    rw [← heq_closed n hn hw]
    exact hselected_Q n hn hw
  have hPhi_ball : MapCInfConvOnCompacts (Metric.ball (0 : X) delta₀)
      Phi PhiInf := by
    intro K hK hKball p
    exact hPhi_conv K hK (hKball.trans hball_TW) p
  have heq_eventually : Filter.Eventually
      (fun n : Nat ↦ Set.EqOn ((e n).symm : X → X) (Phi n)
        (Metric.ball (0 : X) delta₀)) Filter.atTop := by
    apply eventually_atTop.mpr
    refine ⟨N, fun n hn w hw ↦ ?_⟩
    exact (heq_closed n hn (Metric.ball_subset_closedBall hw)).symm
  have hinv_conv : MapCInfConvOnCompacts (Metric.ball (0 : X) delta₀)
      (fun n ↦ ((e n).symm : X → X)) eInf.symm := by
    simpa only [PhiInf] using hPhi_ball.congr_eventually Metric.isOpen_ball
      heq_eventually (fun _ _ ↦ rfl)
  exact ⟨delta₀, hdelta₀, hdelta₀delta, hInf_maps,
    hmaps_eventually, hinv_conv⟩





theorem exists_symm_cInf
    {X : Type*}
    [NormedAddCommGroup X] [NormedSpace Real X]
    [FiniteDimensional Real X]
    {e : Nat → OpenPartialHomeomorph X X}
    {eInf : OpenPartialHomeomorph X X}
    {Q K : Set X}
    (hQ : IsOpen Q) (hK : IsCompact K)
    (hforward : MapCInfConvOnCompacts Q
      (fun n ↦ (e n : X → X)) eInf)
    (hsource : Filter.Eventually
      (fun n : Nat ↦ closure Q ⊆ (e n).source) Filter.atTop)
    (hstage_cd : ∀ n, ContDiffOn Real ∞ (e n : X → X) Q)
    (hInf_cd : ContDiffOn Real ∞ (eInf : X → X) Q)
    (hInf_symm_cd : ContDiffOn Real ∞
      (eInf.symm : X → X) eInf.target)
    (hKt : K ⊆ eInf.target)
    (hKQ : eInf.symm '' K ⊆ Q) :
    ∃ V : Set X,
      IsOpen V ∧ IsCompact (closure V) ∧ K ⊆ V ∧
      closure V ⊆ eInf.target ∧
      eInf.symm '' closure V ⊆ Q ∧
      Filter.Eventually
        (fun n : Nat ↦ closure V ⊆ (e n).target ∧
          Set.MapsTo (e n).symm (closure V) Q) Filter.atTop ∧
      MapCInfConvOnCompacts V
        (fun n ↦ ((e n).symm : X → X)) eInf.symm := by
  let G : Set X := eInf.target ∩ eInf.symm ⁻¹' Q
  have hGopen : IsOpen G := by
    exact hInf_symm_cd.continuousOn.isOpen_inter_preimage
      eInf.open_target hQ
  have hKG : K ⊆ G := by
    intro w hw
    exact ⟨hKt hw, hKQ ⟨w, hw, rfl⟩⟩
  obtain ⟨W₀, hW₀open, hKW₀, hW₀G, hW₀compact⟩ :=
    exists_open_between_and_isCompact_closure hK hGopen hKG
  let D : Set (X × X) := W₀ ×ˢ Q
  let F : Nat → X × X → X := fun n z ↦ e n z.2 - z.1
  let FInf : X × X → X := fun z ↦ eInf z.2 - z.1
  let PhiInf : X → X := eInf.symm
  have hW₀target : W₀ ⊆ eInf.target := by
    intro w hw
    exact (hW₀G (subset_closure hw)).1
  have hW₀map : Set.MapsTo PhiInf W₀ Q := by
    intro w hw
    exact (hW₀G (subset_closure hw)).2
  have hDopen : IsOpen D := hW₀open.prod hQ
  have hF_cd : ∀ n, ContDiffOn Real ∞ (F n) D := by
    intro n
    exact ((hstage_cd n).comp contDiff_snd.contDiffOn
      (fun z hz ↦ hz.2)).sub contDiff_fst.contDiffOn
  have hFInf_cd : ContDiffOn Real ∞ FInf D :=
    (hInf_cd.comp contDiff_snd.contDiffOn
      (fun z hz ↦ hz.2)).sub contDiff_fst.contDiffOn
  have hPhiInf_cd : ContDiffOn Real ∞ PhiInf W₀ :=
    hInf_symm_cd.mono hW₀target
  have hgraph : Set.MapsTo (fun w ↦ (w, PhiInf w)) W₀ D := by
    intro w hw
    exact ⟨hw, hW₀map hw⟩
  have hroot : ∀ w ∈ W₀, FInf (w, PhiInf w) = 0 := by
    intro w hw
    dsimp only [FInf, PhiInf]
    rw [eInf.right_inv (hW₀target hw), sub_self]
  have hinv : ∀ w ∈ K,
      (partialFDeriv₂ FInf w (PhiInf w)).IsInvertible := by
    intro w hw
    have hwTarget : w ∈ eInf.target := hKt hw
    have hpreQ : eInf.symm w ∈ Q := hKQ ⟨w, hw, rfl⟩
    have hpreSource : eInf.symm w ∈ eInf.source :=
      eInf.map_target hwTarget
    have hfAt : DifferentiableAt Real (eInf : X → X) (eInf.symm w) :=
      (hInf_cd.contDiffAt (hQ.mem_nhds hpreQ)).differentiableAt (by simp)
    have hgAt : DifferentiableAt Real (eInf.symm : X → X) w :=
      (hInf_symm_cd.contDiffAt
        (eInf.open_target.mem_nhds hwTarget)).differentiableAt (by simp)
    have hderiv_inv :
        (fderiv Real (eInf : X → X) (eInf.symm w)).IsInvertible :=
      fderiv_inv_of_local hfAt hgAt (eInf.right_inv hwTarget) rfl
        (eInf.eventually_left_inverse hpreSource)
        (eInf.eventually_right_inverse hwTarget)
    change (partialFDeriv₂ (fun z : X × X ↦ eInf z.2 - z.1)
      w (eInf.symm w)).IsInvertible
    rw [partial_sub_snd hfAt]
    exact hderiv_inv
  obtain ⟨T⟩ := exists_compactRootTube hDopen hW₀open hK hKW₀
    hFInf_cd hPhiInf_cd hgraph hroot hinv
  have hsnd_conv : MapCInfConvOnCompacts D
      (fun _ : Nat ↦ (fun z : X × X ↦ z.2))
      (fun z : X × X ↦ z.2) :=
    mapCInfConv_const (U := D) (fun z : X × X ↦ z.2)
  have he_snd_conv : MapCInfConvOnCompacts D
      (fun n z ↦ e n z.2) (fun z ↦ eInf z.2) :=
    MapCInfConvOnCompacts.comp hDopen hQ hsnd_conv hforward
      (fun _ ↦ contDiff_snd.contDiffOn) contDiff_snd.contDiffOn
      hstage_cd hInf_cd
      (fun z hz ↦ hz.2) (fun _ z hz ↦ hz.2)
  have hfst_conv : MapCInfConvOnCompacts D
      (fun _ : Nat ↦ (fun z : X × X ↦ z.1))
      (fun z : X × X ↦ z.1) :=
    mapCInfConv_const (U := D) (fun z : X × X ↦ z.1)
  have hpair_conv : MapCInfConvOnCompacts D
      (fun n z ↦ (e n z.2, z.1)) (fun z ↦ (eInf z.2, z.1)) :=
    mapCInfConv_prodMk hDopen he_snd_conv hfst_conv
      (fun n ↦ (hstage_cd n).comp contDiff_snd.contDiffOn
        (fun z hz ↦ hz.2))
      (hInf_cd.comp contDiff_snd.contDiffOn (fun z hz ↦ hz.2))
      (fun _ ↦ contDiff_fst.contDiffOn) contDiff_fst.contDiffOn
  let subMap : X × X → X := fun z ↦ z.1 - z.2
  have hsub_cd : ContDiffOn Real ∞ subMap Set.univ :=
    contDiff_fst.contDiffOn.sub contDiff_snd.contDiffOn
  have hF_conv : MapCInfConvOnCompacts D F FInf := by
    have hcomp := MapCInfConvOnCompacts.comp hDopen isOpen_univ hpair_conv
      (mapCInfConv_const (U := Set.univ) subMap)
      (fun n ↦ (hstage_cd n).comp contDiff_snd.contDiffOn
          (fun z hz ↦ hz.2) |>.prodMk contDiff_fst.contDiffOn)
      ((hInf_cd.comp contDiff_snd.contDiffOn
          (fun z hz ↦ hz.2)).prodMk contDiff_fst.contDiffOn)
      (fun _ ↦ hsub_cd) hsub_cd
      (fun _ _ ↦ Set.mem_univ _) (fun _ _ _ ↦ Set.mem_univ _)
    simpa only [F, FInf, subMap] using hcomp
  obtain ⟨Nroot, Phi, hPhi_conv, _hPhi_cd, hspec, _huniq⟩ :=
    T.exists_root_cInf hF_cd hF_conv
  obtain ⟨V, hVopen, hKV, hVT, hVcompact⟩ :=
    exists_open_between_and_isCompact_closure hK T.isOpen_W T.K_subset_W
  have hVtarget : closure V ⊆ eInf.target := by
    intro w hw
    have hwW₀ : w ∈ W₀ :=
      T.closure_W_subset (subset_closure (hVT hw))
    exact hW₀target hwW₀
  have hVmap : eInf.symm '' closure V ⊆ Q := by
    rintro _ ⟨w, hw, rfl⟩
    have hwW₀ : w ∈ W₀ :=
      T.closure_W_subset (subset_closure (hVT hw))
    exact hW₀map hwW₀
  obtain ⟨Nsource, hNsource⟩ := eventually_atTop.mp hsource
  let N : Nat := max Nroot Nsource
  have hselected_Q : ∀ n ≥ N, Set.MapsTo (Phi n) (closure V) Q := by
    intro n hn w hw
    have hnroot : Nroot ≤ n := (Nat.le_max_left _ _).trans hn
    have hwTW : w ∈ T.W := hVT hw
    have hsp := hspec n hnroot w (subset_closure hwTW)
    have hpairD : (w, Phi n w) ∈ D := by
      apply T.tube_subset w (subset_closure hwTW)
      rw [Metric.mem_closedBall]
      exact hsp.1.le.trans (by linarith [T.rho_pos])
    exact hpairD.2
  have hstage_target : ∀ n ≥ N, closure V ⊆ (e n).target := by
    intro n hn w hw
    have hnroot : Nroot ≤ n := (Nat.le_max_left _ _).trans hn
    have hnsource : Nsource ≤ n := (Nat.le_max_right _ _).trans hn
    have hPhiQ : Phi n w ∈ Q := hselected_Q n hn hw
    have hPhiSource : Phi n w ∈ (e n).source :=
      hNsource n hnsource (subset_closure hPhiQ)
    have hroot_n := (hspec n hnroot w (subset_closure (hVT hw))).2.1
    have hew : e n (Phi n w) = w := sub_eq_zero.mp hroot_n
    rw [← hew]
    exact (e n).map_source hPhiSource
  have heq_closed : ∀ n ≥ N,
      Set.EqOn (Phi n) (e n).symm (closure V) := by
    intro n hn w hw
    have hnroot : Nroot ≤ n := (Nat.le_max_left _ _).trans hn
    have hnsource : Nsource ≤ n := (Nat.le_max_right _ _).trans hn
    have hPhiQ : Phi n w ∈ Q := hselected_Q n hn hw
    have hPhiSource : Phi n w ∈ (e n).source :=
      hNsource n hnsource (subset_closure hPhiQ)
    have hroot_n := (hspec n hnroot w (subset_closure (hVT hw))).2.1
    have hew : e n (Phi n w) = w := sub_eq_zero.mp hroot_n
    exact ((e n).eq_symm_apply hPhiSource (hstage_target n hn hw)).mpr hew
  have hstage : Filter.Eventually
      (fun n : Nat ↦ closure V ⊆ (e n).target ∧
        Set.MapsTo (e n).symm (closure V) Q) Filter.atTop := by
    apply eventually_atTop.mpr
    refine ⟨N, fun n hn ↦ ⟨hstage_target n hn, ?_⟩⟩
    intro w hw
    rw [← heq_closed n hn hw]
    exact hselected_Q n hn hw
  have hPhi_V : MapCInfConvOnCompacts V Phi PhiInf := by
    intro K' hK' hK'V p
    exact hPhi_conv K' hK'
      (hK'V.trans (subset_closure.trans hVT)) p
  have heq_eventually : Filter.Eventually
      (fun n : Nat ↦ Set.EqOn ((e n).symm : X → X) (Phi n) V)
      Filter.atTop := by
    apply eventually_atTop.mpr
    refine ⟨N, fun n hn w hw ↦ ?_⟩
    exact (heq_closed n hn (subset_closure hw)).symm
  have hinv_conv : MapCInfConvOnCompacts V
      (fun n ↦ ((e n).symm : X → X)) eInf.symm := by
    simpa only [PhiInf] using hPhi_V.congr_eventually hVopen
      heq_eventually (fun _ _ ↦ rfl)
  exact ⟨V, hVopen, hVcompact, hKV, hVtarget, hVmap, hstage, hinv_conv⟩

end OpenPartialHomeomorph
end Analysis
end DifferentialGeometry
