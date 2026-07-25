import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Subpath
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Connected.LocPathConnected
import DifferentialGeometry.Geometry.Topology.UniversalCover.Basic





























open Set Function Filter
open scoped Topology ContDiff

noncomputable section

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Topology
namespace UniversalCover

variable {X : Type*} [TopologicalSpace X] [Inhabited X]
  [ConnectedSpace X] [LocPathConnectedSpace X]
  [DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnectedSpace X]













omit [ConnectedSpace X] [LocPathConnectedSpace X] [SemilocallySimplyConnectedSpace X] in
theorem uc_sheet_bijection_on_good_U
    (p : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X)
    (U : Set X) (hU : IsOpen U) (hp : p.1 ∈ U)
    (hUpc : IsPathConnected U)
    (hUloops : ∀ γ : _root_.Path p.1 p.1,
      (∀ t, γ t ∈ U) →
        (⟦γ⟧ : _root_.Path.Homotopic.Quotient p.1 p.1) =
          ⟦_root_.Path.refl p.1⟧) :
    Set.BijOn (proj :
        DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X → X)
      (basicOpen p U hU hp) U := by
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨η, hηU, _⟩ := hq
    have : η 1 ∈ U := hηU 1
    simpa [proj, Path.target] using this
  · intro q hq q' hq' hqq'
    obtain ⟨xq, cq⟩ := q
    obtain ⟨xq', cq'⟩ := q'
    obtain ⟨η, hηU, hqeq⟩ := hq
    obtain ⟨η', hη'U, hq'eq⟩ := hq'
    have hxy : xq = xq' := hqq'
    subst hxy
    refine Sigma.ext rfl ?_
    simp only [heq_eq_eq] at hqeq hq'eq ⊢
    rw [hqeq, hq'eq]
    congr 1
    have hloop_inU : ∀ t, (η.trans η'.symm) t ∈ U := by
      intro t
      rw [Path.trans_apply]
      split_ifs with h
      · exact hηU _
      · rw [Path.symm_apply]; exact hη'U _
    have hloop : (⟦η.trans η'.symm⟧ : Path.Homotopic.Quotient p.1 p.1) =
        ⟦Path.refl p.1⟧ := hUloops _ hloop_inU
    have hbase : Path.Homotopic.Quotient.trans
        (Path.Homotopic.Quotient.mk η)
        (Path.Homotopic.Quotient.symm (Path.Homotopic.Quotient.mk η')) =
        Path.Homotopic.Quotient.refl p.1 := by
      have h := hloop
      change Path.Homotopic.Quotient.mk (η.trans η'.symm) =
             Path.Homotopic.Quotient.mk (Path.refl p.1) at h
      rw [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm,
          Path.Homotopic.Quotient.mk_refl] at h
      exact h
    have h₁ : Path.Homotopic.Quotient.mk η =
        Path.Homotopic.Quotient.trans
          (Path.Homotopic.Quotient.mk η)
          (Path.Homotopic.Quotient.trans
            (Path.Homotopic.Quotient.symm (Path.Homotopic.Quotient.mk η'))
            (Path.Homotopic.Quotient.mk η')) := by
      rw [Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.trans_refl]
    calc Path.Homotopic.Quotient.mk η
        = Path.Homotopic.Quotient.trans
            (Path.Homotopic.Quotient.mk η)
            (Path.Homotopic.Quotient.trans
              (Path.Homotopic.Quotient.symm (Path.Homotopic.Quotient.mk η'))
              (Path.Homotopic.Quotient.mk η')) := h₁
      _ = Path.Homotopic.Quotient.trans
            (Path.Homotopic.Quotient.trans
              (Path.Homotopic.Quotient.mk η)
              (Path.Homotopic.Quotient.symm (Path.Homotopic.Quotient.mk η')))
            (Path.Homotopic.Quotient.mk η') := by
            rw [Path.Homotopic.Quotient.trans_assoc]
      _ = Path.Homotopic.Quotient.trans
            (Path.Homotopic.Quotient.refl p.1)
            (Path.Homotopic.Quotient.mk η') := by rw [hbase]
      _ = Path.Homotopic.Quotient.mk η' := by
            rw [Path.Homotopic.Quotient.refl_trans]
  · intro y hy
    have hjoined : JoinedIn U p.1 y := hUpc.joinedIn _ hp _ hy
    refine ⟨⟨y, p.2.trans (Path.Homotopic.Quotient.mk hjoined.somePath)⟩, ?_, rfl⟩
    refine ⟨hjoined.somePath, ?_, rfl⟩
    exact fun t => hjoined.somePath_mem t





omit [Inhabited X] [ConnectedSpace X] in
private theorem uc_good_nhd_exists (x : X) :
    ∃ (U : Set X), IsOpen U ∧ x ∈ U ∧ IsPathConnected U ∧
      ∀ γ : _root_.Path x x, (∀ t, γ t ∈ U) →
        (⟦γ⟧ : _root_.Path.Homotopic.Quotient x x) = ⟦_root_.Path.refl x⟧ := by
  obtain ⟨U₀, hU₀nhd, hU₀loops⟩ :=
    DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnectedSpace.out
      (X := X) x
  obtain ⟨U, ⟨hUopen, hxU, hUpc⟩, hUsub⟩ :=
    (isOpen_isPathConnected_basis x).mem_iff.mp hU₀nhd
  refine ⟨U, hUopen, hxU, hUpc, ?_⟩
  intro γ hγU
  refine hU₀loops γ ?_
  intro y hy
  obtain ⟨t, ht⟩ := hy
  have : γ t ∈ U := by simpa [Path.coe_toContinuousMap] using hγU t
  exact hUsub (ht ▸ this)


omit [ConnectedSpace X] [LocPathConnectedSpace X] [SemilocallySimplyConnectedSpace X] in
private theorem uc_sheet_disjoint
    {U : Set X} (hU : IsOpen U)
    {p₁ p₂ :
        DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X}
    (hp₁U : p₁.1 ∈ U) (hp₂U : p₂.1 ∈ U)
    (hp_eq : p₁.1 = p₂.1)
    (hUloops : ∀ γ : _root_.Path p₁.1 p₁.1, (∀ t, γ t ∈ U) →
        (⟦γ⟧ : _root_.Path.Homotopic.Quotient p₁.1 p₁.1) =
          ⟦_root_.Path.refl p₁.1⟧)
    (hne : p₁ ≠ p₂) :
    Disjoint (basicOpen p₁ U hU hp₁U) (basicOpen p₂ U hU hp₂U) := by
  rw [Set.disjoint_iff_inter_eq_empty]
  refine Set.eq_empty_iff_forall_notMem.mpr ?_
  intro q ⟨⟨η₁, hη₁U, hq₁⟩, ⟨η₂, hη₂U, hq₂⟩⟩
  apply hne
  obtain ⟨xp₁, c₁⟩ := p₁
  obtain ⟨xp₂, c₂⟩ := p₂
  simp only at hp_eq
  subst hp_eq
  refine Sigma.ext rfl ?_
  simp only [heq_eq_eq] at hq₁ hq₂ ⊢
  have hloopU : ∀ t, (η₂.trans η₁.symm) t ∈ U := by
    intro t
    rw [Path.trans_apply]
    split_ifs with h
    · exact hη₂U _
    · rw [Path.symm_apply]; exact hη₁U _
  have hloop_null :
      (⟦η₂.trans η₁.symm⟧ : _root_.Path.Homotopic.Quotient xp₁ xp₁) =
        ⟦_root_.Path.refl xp₁⟧ := hUloops _ hloopU
  have hbase : c₁.trans (_root_.Path.Homotopic.Quotient.mk η₁) =
      c₂.trans (_root_.Path.Homotopic.Quotient.mk η₂) := hq₁.symm.trans hq₂
  have hloop_q :
      _root_.Path.Homotopic.Quotient.trans
          (_root_.Path.Homotopic.Quotient.mk η₂)
          (_root_.Path.Homotopic.Quotient.symm
            (_root_.Path.Homotopic.Quotient.mk η₁)) =
      _root_.Path.Homotopic.Quotient.refl xp₁ := by
    have h := hloop_null
    change _root_.Path.Homotopic.Quotient.mk (η₂.trans η₁.symm) =
           _root_.Path.Homotopic.Quotient.mk (_root_.Path.refl xp₁) at h
    rw [_root_.Path.Homotopic.Quotient.mk_trans,
        _root_.Path.Homotopic.Quotient.mk_symm,
        _root_.Path.Homotopic.Quotient.mk_refl] at h
    exact h
  calc c₁
      = (c₁.trans (_root_.Path.Homotopic.Quotient.mk η₁)).trans
          (_root_.Path.Homotopic.Quotient.symm
            (_root_.Path.Homotopic.Quotient.mk η₁)) := by
            rw [_root_.Path.Homotopic.Quotient.trans_assoc,
                _root_.Path.Homotopic.Quotient.trans_symm,
                _root_.Path.Homotopic.Quotient.trans_refl]
    _ = (c₂.trans (_root_.Path.Homotopic.Quotient.mk η₂)).trans
          (_root_.Path.Homotopic.Quotient.symm
            (_root_.Path.Homotopic.Quotient.mk η₁)) := by rw [hbase]
    _ = c₂.trans
          (_root_.Path.Homotopic.Quotient.trans
            (_root_.Path.Homotopic.Quotient.mk η₂)
            (_root_.Path.Homotopic.Quotient.symm
              (_root_.Path.Homotopic.Quotient.mk η₁))) :=
            _root_.Path.Homotopic.Quotient.trans_assoc c₂ _ _
    _ = c₂.trans (_root_.Path.Homotopic.Quotient.refl xp₁) := by rw [hloop_q]
    _ = c₂ := _root_.Path.Homotopic.Quotient.trans_refl c₂


omit [ConnectedSpace X] [LocPathConnectedSpace X] [SemilocallySimplyConnectedSpace X] in
private theorem uc_sheet_exhaust
    (x : X) {U : Set X} (hU : IsOpen U) (hxU : x ∈ U) (hUpc : IsPathConnected U)
    (q : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X)
    (hq : q.1 ∈ U) :
    ∃ (p : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X)
      (hp_eq : p.1 = x),
      q ∈ basicOpen p U hU (hp_eq.symm ▸ hxU) := by
  have hjoined : JoinedIn U x q.1 := hUpc.joinedIn _ hxU _ hq
  set ζ : _root_.Path x q.1 := hjoined.somePath
  have hζU : ∀ t, ζ t ∈ U := fun t => hjoined.somePath_mem t
  refine ⟨⟨x, q.2.trans (_root_.Path.Homotopic.Quotient.mk ζ.symm)⟩, rfl, ?_⟩
  refine ⟨ζ, hζU, ?_⟩
  rw [_root_.Path.Homotopic.Quotient.trans_assoc]
  conv_lhs => rw [← _root_.Path.Homotopic.Quotient.trans_refl q.2]
  congr 1
  rw [show (_root_.Path.Homotopic.Quotient.mk ζ.symm) =
      _root_.Path.Homotopic.Quotient.symm (_root_.Path.Homotopic.Quotient.mk ζ) from rfl,
    _root_.Path.Homotopic.Quotient.symm_trans]


omit [ConnectedSpace X] [SemilocallySimplyConnectedSpace X] in
private theorem uc_sheet_proj_isOpenMap
    {p : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X}
    {U : Set X} (hU : IsOpen U) (hp : p.1 ∈ U)
    {O : Set
        (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X)}
    (hOopen : IsOpen O) (hOsub : O ⊆ basicOpen p U hU hp) :
    IsOpen ((proj :
        DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X → X)
        '' O) := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨q, hqO, rfl⟩
  have hqUp : q ∈ basicOpen p U hU hp := hOsub hqO
  have hqU : q.1 ∈ U := by
    obtain ⟨η, hη, _⟩ := hqUp
    simpa [proj] using hη 1
  have hO_nhd : O ∈ nhds q := hOopen.mem_nhds hqO
  have hbasis := (basis_assemble (X := X)).nhds_hasBasis (a := q)
  obtain ⟨S, ⟨⟨r, V, hVopen, hrV, rfl⟩, hqV⟩, hVsub⟩ := hbasis.mem_iff.mp hO_nhd
  obtain ⟨W, hWopen, hqW, _hWsub, hWpc, hWshrink⟩ :=
    basis_intersection (p₁ := r) (p₂ := p) (r := q)
      hVopen hrV hU hp ⟨hqV, hqUp⟩
  have hsub : basicOpen q W hWopen hqW ⊆ O :=
    (hWshrink).trans (fun s hs => hVsub hs.1)
  refine Filter.mem_of_superset (hWopen.mem_nhds hqW) ?_
  intro z hzW
  have hjoined : JoinedIn W q.1 z := hWpc.joinedIn _ hqW _ hzW
  refine ⟨⟨z, q.2.trans (_root_.Path.Homotopic.Quotient.mk hjoined.somePath)⟩, ?_, rfl⟩
  apply hsub
  refine ⟨hjoined.somePath, hjoined.somePath_mem, rfl⟩

set_option linter.dupNamespace false in















omit [ConnectedSpace X] in
theorem UniversalCover.proj_isCoveringMap :
    IsCoveringMap (proj :
      DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X → X) := by
  intro x
  obtain ⟨U, hUopen, hxU, hUpc, hUloops⟩ := uc_good_nhd_exists (X := X) x
  set Fx : Set
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X) :=
    (proj :
        DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X → X)
      ⁻¹' {x} with hFxdef
  have hp1_eq (p : Fx) : (p.1 : _).1 = x := p.2
  have hp1_mem (p : Fx) : (p.1 : _).1 ∈ U := by rw [hp1_eq p]; exact hxU
  let sheet : Fx → Set
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X) :=
    fun p => basicOpen p.1 U hUopen (hp1_mem p)
  have hsheet_open : ∀ p : Fx, IsOpen (sheet p) := fun p =>
    TopologicalSpace.GenerateOpen.basic _ ⟨p.1, U, hUopen, hp1_mem p, rfl⟩
  have hsheet_sub_preU : ∀ p : Fx, sheet p ⊆
      (proj :
        DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X → X)
        ⁻¹' U := by
    intro p q hq
    obtain ⟨η, hη, _⟩ := hq
    have := hη 1
    simpa [proj] using this
  have hself_in_sheet : ∀ p : Fx, p.1 ∈ sheet p := by
    intro p
    refine ⟨_root_.Path.refl p.1.1, fun _ => hp1_mem p, ?_⟩
    have hmkrefl :
        (_root_.Path.Homotopic.Quotient.mk (_root_.Path.refl p.1.1) :
            _root_.Path.Homotopic.Quotient p.1.1 p.1.1)
          = _root_.Path.Homotopic.Quotient.refl p.1.1 :=
      _root_.Path.Homotopic.Quotient.mk_refl p.1.1
    rw [hmkrefl]
    exact (_root_.Path.Homotopic.Quotient.trans_refl p.1.2).symm
  have hsheet_disj : Pairwise (Disjoint on sheet) := by
    intro p₁ p₂ hp
    have hne : p₁.1 ≠ p₂.1 := fun h => hp (Subtype.ext h)
    have heq : p₁.1.1 = p₂.1.1 := (hp1_eq p₁).trans (hp1_eq p₂).symm
    have hloops₁ : ∀ γ : _root_.Path p₁.1.1 p₁.1.1, (∀ t, γ t ∈ U) →
        (⟦γ⟧ : _root_.Path.Homotopic.Quotient p₁.1.1 p₁.1.1) =
          ⟦_root_.Path.refl p₁.1.1⟧ := by
      have hbase : p₁.1.1 = x := hp1_eq p₁
      intro γ hγ
      revert γ
      rw [hbase]
      exact hUloops
    exact uc_sheet_disjoint hUopen (hp1_mem p₁) (hp1_mem p₂) heq hloops₁ hne
  have hsheet_exhaust : ∀ q ∈ (proj :
      DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X → X)
      ⁻¹' U, ∃ p : Fx, q ∈ sheet p := by
    intro q hq
    obtain ⟨p, hp_eq, hqsheet⟩ := uc_sheet_exhaust (X := X) x hUopen hxU hUpc q hq
    have hp_mem : p ∈ Fx := by simpa [proj] using hp_eq
    refine ⟨⟨p, hp_mem⟩, ?_⟩
    exact hqsheet
  have hsheet_bij : ∀ p : Fx, Set.BijOn proj (sheet p) U := by
    intro p
    refine uc_sheet_bijection_on_good_U p.1 U hUopen (hp1_mem p) hUpc ?_
    intro γ hγ
    have hbase : p.1.1 = x := hp1_eq p
    revert γ
    rw [hbase]
    exact hUloops
  have hsheet_inj : ∀ p : Fx, (sheet p).InjOn proj := fun p => (hsheet_bij p).2.1
  have hsheet_surj : ∀ p : Fx, (sheet p).SurjOn proj U := fun p => (hsheet_bij p).2.2
  haveI hFx_disc : DiscreteTopology Fx := by
    rw [discreteTopology_iff_isOpen_singleton]
    intro p
    have hsingleton_eq :
        ({p} : Set Fx) = Subtype.val ⁻¹' (sheet p) := by
      ext q
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      refine ⟨?_, ?_⟩
      · intro hqp
        rw [hqp]
        exact hself_in_sheet p
      · intro hqp
        by_contra hne
        have hne' : q ≠ p := hne
        have hdisj : Disjoint (sheet q) (sheet p) := hsheet_disj hne'
        rw [Set.disjoint_iff_inter_eq_empty] at hdisj
        have hq_in_own : q.1 ∈ sheet q := hself_in_sheet q
        have hqinter : q.1 ∈ sheet q ∩ sheet p := ⟨hq_in_own, hqp⟩
        rw [hdisj] at hqinter
        exact hqinter
    rw [hsingleton_eq]
    exact (hsheet_open p).preimage continuous_subtype_val
  refine ⟨hFx_disc, U, hxU, hUopen, hUopen.preimage proj_continuous, ?_⟩
  classical
  let theSheet : ((proj :
      DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X → X)
      ⁻¹' U) → Fx := fun q => (hsheet_exhaust q.1 q.2).choose
  have htheSheet_mem : ∀ q, q.1 ∈ sheet (theSheet q) := fun q =>
    (hsheet_exhaust q.1 q.2).choose_spec
  have htheSheet_uniq : ∀ (q : _) (p : Fx),
      q.1 ∈ sheet p → theSheet q = p := by
    intro q p hqp
    by_contra hne
    have hdisj : Disjoint (sheet (theSheet q)) (sheet p) := hsheet_disj hne
    rw [Set.disjoint_iff_inter_eq_empty] at hdisj
    have hmem : q.1 ∈ sheet (theSheet q) ∩ sheet p := ⟨htheSheet_mem q, hqp⟩
    rw [hdisj] at hmem
    exact hmem
  let theInv : (U × Fx) → ((proj :
      DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X → X)
      ⁻¹' U) := fun yp =>
    ⟨(hsheet_surj yp.2 yp.1.2).choose, by
      have := (hsheet_surj yp.2 yp.1.2).choose_spec.1
      exact hsheet_sub_preU yp.2 this⟩
  have htheInv_mem : ∀ yp, (theInv yp).1 ∈ sheet yp.2 := fun yp =>
    (hsheet_surj yp.2 yp.1.2).choose_spec.1
  have htheInv_proj : ∀ yp, proj (theInv yp).1 = yp.1.1 := fun yp =>
    (hsheet_surj yp.2 yp.1.2).choose_spec.2
  let fwd : ((proj :
      DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X → X)
      ⁻¹' U) → (U × Fx) :=
    fun q => (⟨q.1.1, q.2⟩, theSheet q)
  let inv : (U × Fx) → ((proj :
      DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X → X)
      ⁻¹' U) := theInv
  have h_left_inv : ∀ q, inv (fwd q) = q := by
    intro q
    apply Subtype.ext
    have hmem1 := htheInv_mem (⟨q.1.1, q.2⟩, theSheet q)
    have hproj1 := htheInv_proj (⟨q.1.1, q.2⟩, theSheet q)
    have hmem2 := htheSheet_mem q
    apply (hsheet_inj (theSheet q)) hmem1 hmem2 hproj1
  have h_right_inv : ∀ yp, fwd (inv yp) = yp := by
    rintro ⟨⟨y, hy⟩, p⟩
    have hproj : proj (inv (⟨y, hy⟩, p)).1 = y := htheInv_proj (⟨y, hy⟩, p)
    have hsheet_mem : (inv (⟨y, hy⟩, p)).1 ∈ sheet p := htheInv_mem (⟨y, hy⟩, p)
    have h_eq_sheet : theSheet (inv (⟨y, hy⟩, p)) = p :=
      htheSheet_uniq _ p hsheet_mem
    apply Prod.ext
    · apply Subtype.ext
      simpa [fwd] using hproj
    · simpa [fwd] using h_eq_sheet
  have hfwd_cont : Continuous fwd := by
    apply Continuous.prodMk
    · apply continuous_induced_rng.mpr
      exact (proj_continuous (X := X)).comp continuous_subtype_val
    · rw [continuous_discrete_rng]
      intro p
      have h_eq : (theSheet ⁻¹' {p} :
          Set ((proj :
              DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X
              → X) ⁻¹' U)) =
          Subtype.val ⁻¹' sheet p := by
        ext q
        simp only [Set.mem_preimage, Set.mem_singleton_iff]
        constructor
        · intro hq
          rw [← hq]
          exact htheSheet_mem q
        · intro hq
          exact htheSheet_uniq q p hq
      rw [h_eq]
      exact (hsheet_open p).preimage continuous_subtype_val
  have hinv_cont : Continuous inv := by
    apply continuous_induced_rng.mpr
    have hcont : Continuous fun yp : U × Fx => (inv yp).1 := by
      apply continuous_prod_of_discrete_right.mpr
      intro p
      refine continuous_iff_continuousAt.mpr ?_
      intro y₀
      rw [ContinuousAt, Filter.tendsto_def]
      intro W hW
      set q₀ := (inv (y₀, p)).1
      have hq₀_in_sheet : q₀ ∈ sheet p := htheInv_mem (y₀, p)
      have hproj_q₀ : proj q₀ = y₀.1 := htheInv_proj (y₀, p)
      rw [mem_nhds_iff] at hW
      obtain ⟨W', hW'sub, hW'open, hq₀W'⟩ := hW
      set W'' := W' ∩ sheet p
      have hW''open : IsOpen W'' := hW'open.inter (hsheet_open p)
      have hq₀W'' : q₀ ∈ W'' := ⟨hq₀W', hq₀_in_sheet⟩
      have hprojW''_open : IsOpen (proj '' W'') :=
        uc_sheet_proj_isOpenMap hUopen (hp1_mem p) hW''open
          (Set.inter_subset_right)
      have hy₀_inW'' : y₀.1 ∈ proj '' W'' := ⟨q₀, hq₀W'', hproj_q₀⟩
      refine Filter.mem_of_superset
        ((continuous_subtype_val.continuousAt
          (x := y₀)).preimage_mem_nhds
          (hprojW''_open.mem_nhds hy₀_inW'')) ?_
      intro y hy
      obtain ⟨q', hq'W'', hq'proj⟩ := hy
      have h_eq : (inv (y, p)).1 = q' := by
        apply hsheet_inj p (htheInv_mem (y, p)) hq'W''.2
        rw [htheInv_proj (y, p), hq'proj]
      change (inv (y, p)).1 ∈ W
      rw [h_eq]
      exact hW'sub hq'W''.1
    exact hcont
  let eqv : ((proj :
      DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X → X)
      ⁻¹' U) ≃ (U × Fx) :=
  { toFun := fwd, invFun := inv, left_inv := h_left_inv, right_inv := h_right_inv }
  let homeo : ((proj :
      DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X → X)
      ⁻¹' U) ≃ₜ (U × Fx) :=
  { toEquiv := eqv, continuous_toFun := hfwd_cont, continuous_invFun := hinv_cont }
  refine ⟨homeo, ?_⟩
  intro q
  rfl



def basePoint :
    DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X :=
  ⟨(default : X),
    _root_.Path.Homotopic.Quotient.mk (_root_.Path.refl (default : X))⟩



def uc_subpathLift {x : X} (γ : _root_.Path (default : X) x)
    (s : unitInterval) :
    DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X :=
  ⟨γ s,
    (_root_.Path.Homotopic.Quotient.mk (γ.subpath 0 s)).cast γ.source.symm rfl⟩








omit [ConnectedSpace X] [SemilocallySimplyConnectedSpace X] in
theorem uc_subpathLift_continuous {x : X} (γ : _root_.Path (default : X) x) :
    Continuous (uc_subpathLift γ) := by
  refine continuous_iff_continuousAt.mpr fun s₀ => ?_
  rw [ContinuousAt, Filter.tendsto_def]
  intro N hN
  obtain ⟨S, ⟨⟨p, V, hVopen, hpV, rfl⟩, hTs₀S⟩, hSN⟩ :=
    (basis_assemble (X := X)).nhds_hasBasis.mem_iff.mp hN
  obtain ⟨η₀, hη₀V, hη₀eq⟩ := hTs₀S
  simp only [uc_subpathLift] at hη₀eq
  have hcont_fam :
      Continuous (fun st : unitInterval × unitInterval =>
        γ.subpath s₀ st.1 st.2) := by
    have hmap : Continuous
        (fun st : unitInterval × unitInterval =>
          (s₀, st.1, st.2) : unitInterval × unitInterval →
            unitInterval × unitInterval × unitInterval) := by
      exact (continuous_const.prodMk (continuous_fst.prodMk continuous_snd))
    exact γ.subpath_continuous_family.comp hmap
  have hopen : IsOpen
      {st : unitInterval × unitInterval | γ.subpath s₀ st.1 st.2 ∈ V} :=
    hVopen.preimage hcont_fam
  have hsub : ({s₀} ×ˢ (Set.univ : Set unitInterval)) ⊆
      {st : unitInterval × unitInterval | γ.subpath s₀ st.1 st.2 ∈ V} := by
    rintro ⟨s, t⟩ ⟨hs, -⟩
    simp only [Set.mem_singleton_iff] at hs
    simp only [Set.mem_setOf_eq, hs, Path.subpath_self, Path.refl_apply]
    have : γ s₀ ∈ V := by
      have h := hη₀V 1
      rw [Path.target] at h
      exact h
    exact this
  obtain ⟨J, K, hJopen, _hKopen, hs₀J, _hKuniv, hJK⟩ :=
    generalized_tube_lemma (isCompact_singleton (x := s₀)) (isCompact_univ) hopen hsub
  have hs₀J' : s₀ ∈ J := hs₀J rfl
  have hsubV : ∀ s ∈ J, ∀ t, γ.subpath s₀ s t ∈ V := by
    intro s hs t
    have : (s, t) ∈ J ×ˢ K := ⟨hs, _hKuniv (Set.mem_univ t)⟩
    exact hJK this
  refine Filter.mem_of_superset (hJopen.mem_nhds hs₀J') ?_
  intro s hsJ
  apply hSN
  refine ⟨η₀.trans (γ.subpath s₀ s), ?_, ?_⟩
  · intro t
    rw [Path.trans_apply]
    split_ifs with h
    · exact hη₀V _
    · rw [Path.subpath]
      exact hsubV s hsJ _
  · change (_root_.Path.Homotopic.Quotient.mk (γ.subpath 0 s)).cast γ.source.symm rfl =
      p.2.trans (_root_.Path.Homotopic.Quotient.mk (η₀.trans (γ.subpath s₀ s)))
    have hadd :
        (_root_.Path.Homotopic.Quotient.mk (γ.subpath 0 s)
            : _root_.Path.Homotopic.Quotient (γ 0) (γ s)) =
          (_root_.Path.Homotopic.Quotient.mk (γ.subpath 0 s₀)).trans
            (_root_.Path.Homotopic.Quotient.mk (γ.subpath s₀ s)) := by
      rw [← _root_.Path.Homotopic.Quotient.mk_trans]
      exact (_root_.Path.Homotopic.Quotient.eq.mpr
        ⟨Path.Homotopy.subpathTransSubpath γ 0 s₀ s⟩).symm
    have hcast :
        (_root_.Path.Homotopic.Quotient.mk (γ.subpath 0 s)).cast γ.source.symm rfl =
          ((_root_.Path.Homotopic.Quotient.mk (γ.subpath 0 s₀)).cast γ.source.symm rfl).trans
            (_root_.Path.Homotopic.Quotient.mk (γ.subpath s₀ s)) := by
      rw [hadd]
      rfl
    rw [hcast, hη₀eq, _root_.Path.Homotopic.Quotient.mk_trans]
    exact _root_.Path.Homotopic.Quotient.trans_assoc _ _ _


omit [ConnectedSpace X] [LocPathConnectedSpace X] [SemilocallySimplyConnectedSpace X] in
theorem uc_subpathLift_zero {x : X} (γ : _root_.Path (default : X) x) :
    uc_subpathLift γ 0 = basePoint := by
  change (⟨γ 0,
      (_root_.Path.Homotopic.Quotient.mk (γ.subpath 0 0)).cast γ.source.symm rfl⟩ :
    DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X) = basePoint
  have h0 : (γ 0 : X) = default := γ.source
  refine Sigma.ext h0 ?_
  rw [show (basePoint (X := X)).2 =
      _root_.Path.Homotopic.Quotient.mk (Path.refl (default : X)) from rfl,
    ← _root_.Path.Homotopic.Quotient.mk_cast]
  refine Path.Homotopic.hpath_hext ?_
  intro t
  rw [Path.cast_coe, Path.refl_apply, Path.subpath, Path.coe_mk_mk,
    Function.comp_apply, Set.Icc.convexCombo_eq]
  exact γ.source


omit [ConnectedSpace X] [LocPathConnectedSpace X] [SemilocallySimplyConnectedSpace X] in
theorem uc_subpathLift_one {x : X} (γ : _root_.Path (default : X) x) :
    uc_subpathLift γ 1 =
      ⟨x, _root_.Path.Homotopic.Quotient.mk γ⟩ := by
  change (⟨γ 1,
      (_root_.Path.Homotopic.Quotient.mk (γ.subpath 0 1)).cast γ.source.symm rfl⟩ :
    DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X) =
    ⟨x, _root_.Path.Homotopic.Quotient.mk γ⟩
  have h1 : (γ 1 : X) = x := γ.target
  refine Sigma.ext h1 ?_
  rw [← _root_.Path.Homotopic.Quotient.mk_cast]
  refine Path.Homotopic.hpath_hext ?_
  intro t
  rw [Path.cast_coe, Path.subpath, Path.coe_mk_mk, Function.comp_apply,
    Set.Icc.convexCombo_zero_one]


omit [ConnectedSpace X] [LocPathConnectedSpace X] [SemilocallySimplyConnectedSpace X] in
theorem uc_subpathLift_proj {x : X} (γ : _root_.Path (default : X) x)
    (s : unitInterval) : proj (uc_subpathLift γ s) = γ s := rfl





omit [ConnectedSpace X] [SemilocallySimplyConnectedSpace X] in
theorem uc_joined_basePoint
    (q : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X) :
    Joined (basePoint (X := X)) q := by
  obtain ⟨x, c⟩ := q
  obtain ⟨γ, rfl⟩ := _root_.Path.Homotopic.Quotient.mk_surjective c
  exact ⟨{
    toFun := uc_subpathLift γ
    continuous_toFun := uc_subpathLift_continuous γ
    source' := uc_subpathLift_zero γ
    target' := uc_subpathLift_one γ }⟩

set_option linter.dupNamespace false in




instance UniversalCover.pathConnectedSpace :
    PathConnectedSpace
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X) where
  nonempty := ⟨basePoint⟩
  joined x y := (uc_joined_basePoint x).symm.trans (uc_joined_basePoint y)








omit [ConnectedSpace X] in
theorem uc_basePoint_loops_nullhomotopic
    (δ : _root_.Path (basePoint (X := X)) basePoint) :
    _root_.Path.Homotopic δ (_root_.Path.refl basePoint) := by
  have hproj : proj (basePoint (X := X)) = default := rfl
  set γX : C(unitInterval, X) :=
    ⟨proj ∘ δ, proj_continuous.comp δ.continuous⟩ with hγXdef
  have hcov : IsCoveringMap
      (proj : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X → X) :=
    UniversalCover.proj_isCoveringMap
  set γ : _root_.Path (default : X) default :=
    { toFun := proj ∘ δ
      continuous_toFun := proj_continuous.comp δ.continuous
      source' := by
        change proj (δ 0) = default
        rw [δ.source]; rfl
      target' := by
        change proj (δ 1) = default
        rw [δ.target]; rfl } with hγdef
  have hδlift : (⟨δ, δ.continuous⟩ : C(unitInterval,
      DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X)) =
      hcov.liftPath γX basePoint (by simp [hγXdef, proj, δ.source]) := by
    rw [hcov.eq_liftPath_iff']
    refine ⟨?_, ?_⟩
    · ext t; rfl
    · exact δ.source
  have hSlift : (⟨uc_subpathLift γ, uc_subpathLift_continuous γ⟩ : C(unitInterval,
      DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X)) =
      hcov.liftPath γX basePoint (by simp [hγXdef, proj, δ.source]) := by
    rw [hcov.eq_liftPath_iff']
    refine ⟨?_, ?_⟩
    · ext t
      simp only [ContinuousMap.coe_mk, Function.comp_apply, hγXdef]
      exact uc_subpathLift_proj γ t
    · exact uc_subpathLift_zero γ
  have hδeq : (δ : unitInterval →
      DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X) =
      uc_subpathLift γ := by
    have := hδlift.trans hSlift.symm
    exact congrArg (fun f : C(unitInterval, _) => (f : unitInterval → _)) this
  have hend : (basePoint (X := X)) =
      (⟨default, _root_.Path.Homotopic.Quotient.mk γ⟩ :
        DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X) := by
    have h1 : δ 1 = uc_subpathLift γ 1 := congrFun hδeq 1
    rw [uc_subpathLift_one] at h1
    rw [← h1, δ.target]
  have hclass : (_root_.Path.Homotopic.Quotient.mk (_root_.Path.refl (default : X))) =
      _root_.Path.Homotopic.Quotient.mk γ := by
    have hsnd := (Sigma.ext_iff.mp hend).2
    exact eq_of_heq hsnd
  have hmapInj := hcov.injective_path_homotopic_map basePoint basePoint
  rw [← _root_.Path.Homotopic.Quotient.eq]
  apply hmapInj
  change (_root_.Path.Homotopic.Quotient.mk δ).map ⟨proj, proj_continuous⟩ =
    (_root_.Path.Homotopic.Quotient.mk (_root_.Path.refl basePoint)).map ⟨proj, proj_continuous⟩
  rw [← _root_.Path.Homotopic.Quotient.mk_map, ← _root_.Path.Homotopic.Quotient.mk_map]
  have hδmap : (_root_.Path.Homotopic.Quotient.mk
      (δ.map (proj_continuous (X := X)))) =
      _root_.Path.Homotopic.Quotient.mk γ := by
    refine _root_.Path.Homotopic.Quotient.eq.mpr ?_
    exact ⟨Path.Homotopy.refl _⟩
  have hreflmap : (_root_.Path.Homotopic.Quotient.mk
      ((_root_.Path.refl (basePoint (X := X))).map (proj_continuous (X := X)))) =
      _root_.Path.Homotopic.Quotient.mk (_root_.Path.refl (default : X)) := by
    refine _root_.Path.Homotopic.Quotient.eq.mpr ?_
    exact ⟨Path.Homotopy.refl _⟩
  rw [hδmap, hreflmap, hclass]

set_option linter.dupNamespace false in





instance UniversalCover.simplyConnectedSpace :
    SimplyConnectedSpace
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X) := by
  rw [simply_connected_iff_loops_nullhomotopic]
  refine ⟨inferInstance, fun e γ => ?_⟩
  set β : _root_.Path (basePoint (X := X)) e := (uc_joined_basePoint e).somePath with hβ
  set δ : _root_.Path (basePoint (X := X)) basePoint :=
    β.trans (γ.trans β.symm) with hδ
  have hδnull := uc_basePoint_loops_nullhomotopic δ
  rw [← _root_.Path.Homotopic.Quotient.eq] at hδnull ⊢
  have hδquot :
      (_root_.Path.Homotopic.Quotient.mk δ) =
        (_root_.Path.Homotopic.Quotient.mk β).trans
          ((_root_.Path.Homotopic.Quotient.mk γ).trans
            (_root_.Path.Homotopic.Quotient.symm
              (_root_.Path.Homotopic.Quotient.mk β))) := by
    rw [hδ]
    simp only [_root_.Path.Homotopic.Quotient.mk_trans, _root_.Path.Homotopic.Quotient.mk_symm]
  rw [hδquot, _root_.Path.Homotopic.Quotient.mk_refl] at hδnull
  rw [_root_.Path.Homotopic.Quotient.mk_refl]
  set B := _root_.Path.Homotopic.Quotient.mk β with hB
  set G := _root_.Path.Homotopic.Quotient.mk γ with hG
  have key : (B.symm.trans (B.trans (G.trans B.symm))).trans B = G := by
    rw [← _root_.Path.Homotopic.Quotient.trans_assoc,
      ← _root_.Path.Homotopic.Quotient.trans_assoc,
      _root_.Path.Homotopic.Quotient.symm_trans,
      _root_.Path.Homotopic.Quotient.refl_trans,
      _root_.Path.Homotopic.Quotient.trans_assoc,
      _root_.Path.Homotopic.Quotient.symm_trans,
      _root_.Path.Homotopic.Quotient.trans_refl]
  calc G
      = (B.symm.trans (B.trans (G.trans B.symm))).trans B := key.symm
    _ = (B.symm.trans (_root_.Path.Homotopic.Quotient.refl basePoint)).trans B := by
          rw [hδnull]
    _ = _root_.Path.Homotopic.Quotient.refl e := by
          rw [_root_.Path.Homotopic.Quotient.trans_refl,
            _root_.Path.Homotopic.Quotient.symm_trans]

end UniversalCover
end Topology
end Riemannian
end Geometry
end DifferentialGeometry

end
