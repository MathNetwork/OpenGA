import DifferentialGeometry.Geometry.Topology.SemilocallySimplyConnected
import DifferentialGeometry.Geometry.Topology.UniversalCover.TruncateHomotopy
import Mathlib.Topology.Bases
import Mathlib.Topology.Connected.LocPathConnected
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.Subpath
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas























open Set Function

noncomputable section

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Topology
namespace UniversalCover









theorem uc_pi1_countable_basis_refinement
    (X : Type*) [TopologicalSpace X] [Nonempty X]
    [SecondCountableTopology X]
    [LocPathConnectedSpace X]
    [DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnectedSpace X] :
    ∃ B : ℕ → Set X,
      (∀ n, IsOpen (B n)) ∧
      (∀ n, IsPathConnected (B n)) ∧
      (∀ n, ∀ (x : X) (_ : x ∈ B n) (γ : _root_.Path x x),
        Set.range γ.toContinuousMap ⊆ B n →
          (⟦γ⟧ : _root_.Path.Homotopic.Quotient x x) = ⟦_root_.Path.refl x⟧) ∧
      TopologicalSpace.IsTopologicalBasis (Set.range B) := by
  classical
  let Good : Set (Set X) :=
    { V : Set X |
        IsOpen V ∧ IsPathConnected V ∧
        ∃ y ∈ V, ∃ Wy ∈ nhds y, V ⊆ Wy ∧
          (∀ γ : _root_.Path y y,
              Set.range γ.toContinuousMap ⊆ Wy →
                (⟦γ⟧ : _root_.Path.Homotopic.Quotient y y)
                  = ⟦_root_.Path.refl y⟧) }
  have hGood_null :
      ∀ V ∈ Good, ∀ (x : X) (_ : x ∈ V) (γ : _root_.Path x x),
        Set.range γ.toContinuousMap ⊆ V →
          (⟦γ⟧ : _root_.Path.Homotopic.Quotient x x) = ⟦_root_.Path.refl x⟧ := by
    rintro V ⟨_hVopen, hVpc, y, hyV, Wy, _hWynhd, hVWy, hWynull⟩ x hxV γ hγV
    have hγV' : ∀ t : unitInterval, γ t ∈ V := by
      intro t
      have ht : (γ t : X) ∈ Set.range γ.toContinuousMap :=
        ⟨t, by simp [Path.coe_toContinuousMap]⟩
      exact hγV ht
    obtain ⟨α, hα⟩ : JoinedIn V y x := hVpc.joinedIn y hyV x hxV
    set δ : _root_.Path y y := α.trans (γ.trans α.symm) with hδdef
    have hδRange : Set.range δ.toContinuousMap ⊆ Wy := by
      have hα_range : Set.range (α : unitInterval → X) ⊆ V := by
        rintro _ ⟨t, rfl⟩; exact hα t
      have hαsymm_range : Set.range (α.symm : unitInterval → X) ⊆ V := by
        rw [Path.symm_range]; exact hα_range
      have hγ_range : Set.range (γ : unitInterval → X) ⊆ V := by
        rintro _ ⟨t, rfl⟩; exact hγV' t
      have hinner : Set.range ((γ.trans α.symm) : unitInterval → X) ⊆ V := by
        rw [Path.trans_range]
        exact Set.union_subset hγ_range hαsymm_range
      have houter : Set.range (δ : unitInterval → X) ⊆ V := by
        change Set.range ((α.trans (γ.trans α.symm)) : unitInterval → X) ⊆ V
        rw [Path.trans_range]
        exact Set.union_subset hα_range hinner
      intro z hz
      rcases hz with ⟨t, ht⟩
      have hzV : z ∈ Set.range (δ : unitInterval → X) :=
        ⟨t, by simpa [Path.coe_toContinuousMap] using ht⟩
      exact hVWy (houter hzV)
    have hδnull :
        (⟦δ⟧ : _root_.Path.Homotopic.Quotient y y)
            = ⟦_root_.Path.refl y⟧ := hWynull δ hδRange
    set A : _root_.Path.Homotopic.Quotient y x := ⟦α⟧ with hAdef
    set G : _root_.Path.Homotopic.Quotient x x := ⟦γ⟧ with hGdef
    set Asym : _root_.Path.Homotopic.Quotient x y :=
      _root_.Path.Homotopic.Quotient.symm A with hAsymdef
    have hδ_quot :
        (⟦δ⟧ : _root_.Path.Homotopic.Quotient y y)
          = _root_.Path.Homotopic.Quotient.trans A
              (_root_.Path.Homotopic.Quotient.trans G Asym) := by
      have e1 :
          (⟦α.trans (γ.trans α.symm)⟧ : _root_.Path.Homotopic.Quotient y y)
            = _root_.Path.Homotopic.Quotient.trans
                (⟦α⟧ : _root_.Path.Homotopic.Quotient y x)
                (⟦γ.trans α.symm⟧ : _root_.Path.Homotopic.Quotient x y) :=
        _root_.Path.Homotopic.Quotient.mk_trans α (γ.trans α.symm)
      have e2 :
          (⟦γ.trans α.symm⟧ : _root_.Path.Homotopic.Quotient x y)
            = _root_.Path.Homotopic.Quotient.trans
                (⟦γ⟧ : _root_.Path.Homotopic.Quotient x x)
                (⟦α.symm⟧ : _root_.Path.Homotopic.Quotient x y) :=
        _root_.Path.Homotopic.Quotient.mk_trans γ α.symm
      have e3 :
          (⟦α.symm⟧ : _root_.Path.Homotopic.Quotient x y)
            = _root_.Path.Homotopic.Quotient.symm
                (⟦α⟧ : _root_.Path.Homotopic.Quotient y x) :=
        _root_.Path.Homotopic.Quotient.mk_symm α
      change (⟦α.trans (γ.trans α.symm)⟧ : _root_.Path.Homotopic.Quotient y y)
            = _root_.Path.Homotopic.Quotient.trans A
                (_root_.Path.Homotopic.Quotient.trans G
                  (_root_.Path.Homotopic.Quotient.symm A))
      rw [e1, e2, e3]
    have href :
        (⟦_root_.Path.refl y⟧ : _root_.Path.Homotopic.Quotient y y)
          = _root_.Path.Homotopic.Quotient.refl y :=
      _root_.Path.Homotopic.Quotient.mk_refl y
    have hconj :
        _root_.Path.Homotopic.Quotient.trans A
            (_root_.Path.Homotopic.Quotient.trans G Asym)
          = _root_.Path.Homotopic.Quotient.refl y := by
      rw [← hδ_quot, hδnull, href]
    have hAsymA :
        _root_.Path.Homotopic.Quotient.trans Asym A
          = _root_.Path.Homotopic.Quotient.refl x := by
      simp [hAsymdef, _root_.Path.Homotopic.Quotient.symm_trans]
    have h_AG_eq_A :
        _root_.Path.Homotopic.Quotient.trans A G = A := by
      have hassoc :
          _root_.Path.Homotopic.Quotient.trans
              (_root_.Path.Homotopic.Quotient.trans A G) Asym
            = _root_.Path.Homotopic.Quotient.trans A
                (_root_.Path.Homotopic.Quotient.trans G Asym) :=
        _root_.Path.Homotopic.Quotient.trans_assoc A G Asym
      have h_AGAsym_refl :
          _root_.Path.Homotopic.Quotient.trans
              (_root_.Path.Homotopic.Quotient.trans A G) Asym
            = _root_.Path.Homotopic.Quotient.refl y := by
        rw [hassoc]; exact hconj
      have step :
          _root_.Path.Homotopic.Quotient.trans
              (_root_.Path.Homotopic.Quotient.trans
                (_root_.Path.Homotopic.Quotient.trans A G) Asym) A
            = _root_.Path.Homotopic.Quotient.trans
                (_root_.Path.Homotopic.Quotient.refl y) A := by
        rw [h_AGAsym_refl]
      have hAG_simpl :
          _root_.Path.Homotopic.Quotient.trans
              (_root_.Path.Homotopic.Quotient.trans
                (_root_.Path.Homotopic.Quotient.trans A G) Asym) A
            = _root_.Path.Homotopic.Quotient.trans A G := by
        calc _root_.Path.Homotopic.Quotient.trans
              (_root_.Path.Homotopic.Quotient.trans
                (_root_.Path.Homotopic.Quotient.trans A G) Asym) A
            = _root_.Path.Homotopic.Quotient.trans
                (_root_.Path.Homotopic.Quotient.trans A G)
                (_root_.Path.Homotopic.Quotient.trans Asym A) := by
              rw [_root_.Path.Homotopic.Quotient.trans_assoc]
          _ = _root_.Path.Homotopic.Quotient.trans
                (_root_.Path.Homotopic.Quotient.trans A G)
                (_root_.Path.Homotopic.Quotient.refl x) := by rw [hAsymA]
          _ = _root_.Path.Homotopic.Quotient.trans A G :=
              _root_.Path.Homotopic.Quotient.trans_refl _
      have h_refl_A :
          _root_.Path.Homotopic.Quotient.trans
              (_root_.Path.Homotopic.Quotient.refl y) A = A :=
        _root_.Path.Homotopic.Quotient.refl_trans A
      rw [← hAG_simpl, step, h_refl_A]
    have hG_eq :
        G = _root_.Path.Homotopic.Quotient.trans Asym
              (_root_.Path.Homotopic.Quotient.trans A G) := by
      calc G
          = _root_.Path.Homotopic.Quotient.trans
              (_root_.Path.Homotopic.Quotient.refl x) G :=
            (_root_.Path.Homotopic.Quotient.refl_trans G).symm
        _ = _root_.Path.Homotopic.Quotient.trans
              (_root_.Path.Homotopic.Quotient.trans Asym A) G := by rw [hAsymA]
        _ = _root_.Path.Homotopic.Quotient.trans Asym
              (_root_.Path.Homotopic.Quotient.trans A G) := by
            rw [_root_.Path.Homotopic.Quotient.trans_assoc]
    rw [hG_eq, h_AG_eq_A]; exact hAsymA
  have hGood_basis : TopologicalSpace.IsTopologicalBasis Good := by
    apply TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
    · intro V hV; exact hV.1
    · intro x W hxW hWopen
      obtain ⟨Wx, hWxNhd, hWxNull⟩ :=
        DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnectedSpace.out
          (X := X) x
      have hWxW : Wx ∩ W ∈ nhds x := Filter.inter_mem hWxNhd (hWopen.mem_nhds hxW)
      have hbasis := isOpen_isPathConnected_basis (x := x)
      obtain ⟨V, ⟨hVopen, hxV, hVpc⟩, hVsub⟩ := hbasis.mem_iff.mp hWxW
      refine ⟨V, ?_, hxV, hVsub.trans Set.inter_subset_right⟩
      refine ⟨hVopen, hVpc, x, hxV, Wx, hWxNhd, ?_, ?_⟩
      · exact fun z hz => (hVsub hz).1
      · intro γ hγ; exact hWxNull γ hγ
  obtain ⟨s, hs_sub, hs_count, hs_basis⟩ := hGood_basis.exists_countable
  have hs_nonempty : s.Nonempty := by
    have huniv : (⋃₀ s) = (Set.univ : Set X) := hs_basis.sUnion_eq
    obtain ⟨x₀⟩ := ‹Nonempty X›
    have hx₀ : x₀ ∈ ⋃₀ s := by rw [huniv]; trivial
    rcases hx₀ with ⟨V, hVs, _⟩; exact ⟨V, hVs⟩
  obtain ⟨B, hBrange⟩ := hs_count.exists_eq_range hs_nonempty
  refine ⟨B, ?_, ?_, ?_, ?_⟩
  · intro n
    have : B n ∈ s := by rw [hBrange]; exact ⟨n, rfl⟩
    exact (hs_sub this).1
  · intro n
    have : B n ∈ s := by rw [hBrange]; exact ⟨n, rfl⟩
    exact (hs_sub this).2.1
  · intro n x hxBn γ hγ
    have hBnGood : B n ∈ Good := hs_sub (by rw [hBrange]; exact ⟨n, rfl⟩)
    exact hGood_null (B n) hBnGood x hxBn γ hγ
  · rw [← hBrange]; exact hs_basis




theorem uc_pi1_countable_anchors
    (X : Type*) [TopologicalSpace X] [Nonempty X]
    (B : ℕ → Set X) :
    ∃ anchor : ℕ × ℕ → X,
      ∀ p : ℕ × ℕ, (B p.1 ∩ B p.2).Nonempty → anchor p ∈ B p.1 ∩ B p.2 := by
  classical
  refine ⟨fun p => if h : (B p.1 ∩ B p.2).Nonempty then h.choose
                   else Classical.arbitrary X, ?_⟩
  intro p hp
  simp only [hp, dif_pos]
  exact hp.choose_spec






theorem uc_pi1_countable_lebesgue_subdivision
    (X : Type*) [TopologicalSpace X]
    (B : ℕ → Set X) (hBopen : ∀ n, IsOpen (B n))
    (hBcov : (⋃ n, B n) = Set.univ)
    {x : X} (γ : _root_.Path x x) :
    ∃ (k : ℕ) (t : Fin (k + 1) → unitInterval) (idx : Fin k → ℕ),
      t 0 = 0 ∧ t (Fin.last k) = 1 ∧
      (∀ i : Fin k, (t i.castSucc : ℝ) ≤ (t i.succ : ℝ)) ∧
      (∀ i : Fin k,
        ∀ s : unitInterval,
          (t i.castSucc : ℝ) ≤ (s : ℝ) → (s : ℝ) ≤ (t i.succ : ℝ) →
            γ s ∈ B (idx i)) := by
  classical
  have hγ : Continuous (γ : unitInterval → X) := map_continuous γ
  have hUopen : ∀ n, IsOpen (γ ⁻¹' B n) := fun n => (hBopen n).preimage hγ
  have hUcov : (Set.univ : Set unitInterval) ⊆ ⋃ n, γ ⁻¹' B n := by
    intro s _
    have : (γ s : X) ∈ (⋃ n, B n) := by rw [hBcov]; trivial
    rcases Set.mem_iUnion.mp this with ⟨n, hn⟩
    exact Set.mem_iUnion.mpr ⟨n, hn⟩
  have hcpt : IsCompact (Set.univ : Set unitInterval) :=
    CompactSpace.isCompact_univ
  obtain ⟨δ, hδpos, hδ⟩ :=
    lebesgue_number_lemma_of_metric hcpt hUopen hUcov
  set k : ℕ := ⌊1 / δ⌋₊ + 1 with hkdef
  have hkpos : 0 < k := Nat.succ_pos _
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hkpos
  have hkinv : 1 / (k : ℝ) < δ := by
    have hk_gt : (1 / δ : ℝ) < (k : ℝ) := by
      have := Nat.lt_floor_add_one (1 / δ)
      simpa [hkdef, Nat.cast_add, Nat.cast_one] using this
    have hδ_inv_pos : 0 < 1 / δ := by positivity
    have : 1 / (k : ℝ) < 1 / (1 / δ) := by
      apply one_div_lt_one_div_of_lt hδ_inv_pos hk_gt
    simpa using this
  have hmem : ∀ i : Fin (k + 1), (i : ℝ) / k ∈ unitInterval := by
    intro i
    refine ⟨div_nonneg (by positivity) hkR.le, ?_⟩
    have hle : (i : ℕ) ≤ k := Nat.lt_succ_iff.mp i.isLt
    have : ((i : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hle
    exact (div_le_one hkR).mpr this
  let t : Fin (k + 1) → unitInterval := fun i => ⟨(i : ℝ) / k, hmem i⟩
  have hchoose : ∀ i : Fin k, ∃ n, ∀ s : unitInterval,
      (t i.castSucc : ℝ) ≤ (s : ℝ) → (s : ℝ) ≤ (t i.succ : ℝ) →
        γ s ∈ B n := by
    intro i
    have hmemU : t i.castSucc ∈ (Set.univ : Set unitInterval) := Set.mem_univ _
    obtain ⟨n, hn⟩ := hδ (t i.castSucc) hmemU
    refine ⟨n, ?_⟩
    intro s hs₁ hs₂
    have hd : dist s (t i.castSucc) < δ := by
      rw [Subtype.dist_eq]
      have hcast :
          (t i.castSucc : ℝ) = ((i : ℕ) : ℝ) / k := by
        simp [t]
      have hsucc :
          (t i.succ : ℝ) = (((i : ℕ) + 1 : ℕ) : ℝ) / k := by
        simp [t, Fin.val_succ]
      have hdiff : (t i.succ : ℝ) - (t i.castSucc : ℝ) = 1 / k := by
        rw [hcast, hsucc]
        push_cast
        field_simp
        ring
      have habs : |(s : ℝ) - (t i.castSucc : ℝ)| ≤ 1 / k := by
        rw [abs_le]
        refine ⟨?_, ?_⟩
        · linarith
        · have : (s : ℝ) ≤ (t i.castSucc : ℝ) + 1 / k := by linarith
          linarith
      have : |(s : ℝ) - (t i.castSucc : ℝ)| < δ := lt_of_le_of_lt habs hkinv
      simpa [Real.dist_eq] using this
    have hball : s ∈ Metric.ball (t i.castSucc) δ := hd
    exact hn hball
  let idx : Fin k → ℕ := fun i => (hchoose i).choose
  have hidx : ∀ i : Fin k, ∀ s : unitInterval,
      (t i.castSucc : ℝ) ≤ (s : ℝ) → (s : ℝ) ≤ (t i.succ : ℝ) →
        γ s ∈ B (idx i) := fun i => (hchoose i).choose_spec
  refine ⟨k, t, idx, ?_, ?_, ?_, hidx⟩
  · apply Subtype.ext
    simp [t]
  · apply Subtype.ext
    change ((Fin.last k : ℕ) : ℝ) / k = 1
    rw [Fin.val_last]
    exact div_self hkR.ne'
  · intro i
    have hcast : (t i.castSucc : ℝ) = ((i : ℕ) : ℝ) / k := by
      simp [t]
    have hsucc : (t i.succ : ℝ) = (((i : ℕ) + 1 : ℕ) : ℝ) / k := by
      simp [t, Fin.val_succ]
    rw [hcast, hsucc]
    apply div_le_div_of_nonneg_right _ hkR.le
    · exact_mod_cast Nat.le_succ _




theorem uc_pi1_countable_piece_homotopy
    (X : Type*) [TopologicalSpace X]
    [DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnectedSpace X]
    (B : ℕ → Set X)
    (hBnull : ∀ n, ∀ (x : X) (_ : x ∈ B n) (γ : _root_.Path x x),
        Set.range γ.toContinuousMap ⊆ B n →
          (⟦γ⟧ : _root_.Path.Homotopic.Quotient x x) = ⟦_root_.Path.refl x⟧)
    (n : ℕ) {a b : X} (γ₁ γ₂ : _root_.Path a b)
    (_h₁ : Set.range γ₁.toContinuousMap ⊆ B n)
    (_h₂ : Set.range γ₂.toContinuousMap ⊆ B n) :
    (⟦γ₁⟧ : _root_.Path.Homotopic.Quotient a b) = ⟦γ₂⟧ := by
  have hr₁ : Set.range (γ₁ : unitInterval → X) ⊆ B n := by
    intro y hy
    rcases hy with ⟨t, ht⟩
    refine _h₁ ⟨t, ?_⟩
    simpa [Path.coe_toContinuousMap] using ht
  have hr₂ : Set.range (γ₂ : unitInterval → X) ⊆ B n := by
    intro y hy
    rcases hy with ⟨t, ht⟩
    refine _h₂ ⟨t, ?_⟩
    simpa [Path.coe_toContinuousMap] using ht
  have haB : a ∈ B n := by
    have h0 : (γ₁ 0 : X) ∈ Set.range (γ₁ : unitInterval → X) := ⟨0, rfl⟩
    have : (γ₁ 0 : X) ∈ B n := hr₁ h0
    simpa using this
  set δ : _root_.Path a a := γ₁.trans γ₂.symm with hδdef
  have hδrange : Set.range δ.toContinuousMap ⊆ B n := by
    intro y hy
    rcases hy with ⟨t, ht⟩
    have hy' : y ∈ Set.range (δ : unitInterval → X) :=
      ⟨t, by simpa [Path.coe_toContinuousMap] using ht⟩
    have hrange : Set.range (δ : unitInterval → X)
        = Set.range (γ₁ : unitInterval → X)
            ∪ Set.range (γ₂.symm : unitInterval → X) := by
      simpa [hδdef] using Path.trans_range γ₁ γ₂.symm
    rw [hrange] at hy'
    rcases hy' with hy₁ | hy₂
    · exact hr₁ hy₁
    · have : y ∈ Set.range (γ₂ : unitInterval → X) := by
        rwa [Path.symm_range] at hy₂
      exact hr₂ this
  have hnull :
      (⟦δ⟧ : _root_.Path.Homotopic.Quotient a a) = ⟦_root_.Path.refl a⟧ :=
    hBnull n a haB δ hδrange
  let Trans : _root_.Path.Homotopic.Quotient a b →
              _root_.Path.Homotopic.Quotient b a →
              _root_.Path.Homotopic.Quotient a a :=
    _root_.Path.Homotopic.Quotient.trans
  set A : _root_.Path.Homotopic.Quotient a b := ⟦γ₁⟧ with hAdef
  set Bq : _root_.Path.Homotopic.Quotient a b := ⟦γ₂⟧ with hBdef
  let Bsym : _root_.Path.Homotopic.Quotient b a :=
    _root_.Path.Homotopic.Quotient.symm Bq
  have h1 :
      (⟦δ⟧ : _root_.Path.Homotopic.Quotient a a)
        = _root_.Path.Homotopic.Quotient.trans A Bsym := by
    have eq₁ :
        (⟦γ₁.trans γ₂.symm⟧ : _root_.Path.Homotopic.Quotient a a)
          = _root_.Path.Homotopic.Quotient.trans
              (⟦γ₁⟧ : _root_.Path.Homotopic.Quotient a b)
              (⟦γ₂.symm⟧ : _root_.Path.Homotopic.Quotient b a) :=
      _root_.Path.Homotopic.Quotient.mk_trans γ₁ γ₂.symm
    have eq₂ :
        (⟦γ₂.symm⟧ : _root_.Path.Homotopic.Quotient b a)
          = _root_.Path.Homotopic.Quotient.symm
              (⟦γ₂⟧ : _root_.Path.Homotopic.Quotient a b) :=
      _root_.Path.Homotopic.Quotient.mk_symm γ₂
    change (⟦γ₁.trans γ₂.symm⟧ : _root_.Path.Homotopic.Quotient a a)
        = _root_.Path.Homotopic.Quotient.trans A
            (_root_.Path.Homotopic.Quotient.symm Bq)
    rw [eq₁, eq₂]
  have h2 :
      (⟦_root_.Path.refl a⟧ : _root_.Path.Homotopic.Quotient a a)
        = _root_.Path.Homotopic.Quotient.refl a :=
    _root_.Path.Homotopic.Quotient.mk_refl a
  have hkey :
      _root_.Path.Homotopic.Quotient.trans A Bsym
        = _root_.Path.Homotopic.Quotient.refl a := by
    rw [← h1, ← h2]; exact hnull
  have hsymm :
      _root_.Path.Homotopic.Quotient.trans Bsym Bq
        = _root_.Path.Homotopic.Quotient.refl b :=
    _root_.Path.Homotopic.Quotient.symm_trans Bq
  calc A
      = _root_.Path.Homotopic.Quotient.trans A
          (_root_.Path.Homotopic.Quotient.refl b) :=
        (_root_.Path.Homotopic.Quotient.trans_refl A).symm
    _ = _root_.Path.Homotopic.Quotient.trans A
          (_root_.Path.Homotopic.Quotient.trans Bsym Bq) := by rw [hsymm]
    _ = _root_.Path.Homotopic.Quotient.trans
          (_root_.Path.Homotopic.Quotient.trans A Bsym) Bq := by
        rw [_root_.Path.Homotopic.Quotient.trans_assoc]
    _ = _root_.Path.Homotopic.Quotient.trans
          (_root_.Path.Homotopic.Quotient.refl a) Bq := by rw [hkey]
    _ = Bq := _root_.Path.Homotopic.Quotient.refl_trans Bq





lemma uc_pi1_countable_concat_quot_congr
    {Y : Type*} [TopologicalSpace Y] {n : ℕ} {p : Fin (n + 1) → Y}
    (F G : (i : Fin n) → _root_.Path (p i.castSucc) (p i.succ))
    (h : ∀ i : Fin n,
      (⟦F i⟧ : _root_.Path.Homotopic.Quotient (p i.castSucc) (p i.succ))
        = ⟦G i⟧) :
    (⟦_root_.Path.concat p F⟧
        : _root_.Path.Homotopic.Quotient (p 0) (p (Fin.last n)))
      = ⟦_root_.Path.concat p G⟧ := by
  have hH : ∀ i : Fin n, (F i).Homotopic (G i) := by
    intro i
    have := h i
    rwa [Quotient.eq] at this
  exact Quotient.sound
    (_root_.Path.Homotopic.concat_hcomp (n := n) p F G hH)










lemma uc_pi1_countable_telescope
    {Y : Type*} [TopologicalSpace Y] :
    ∀ {k : ℕ} (p q : Fin (k + 1) → Y)
      (F : (i : Fin k) → _root_.Path (p i.castSucc) (p i.succ))
      (G : (i : Fin k) → _root_.Path (q i.castSucc) (q i.succ))
      (c : (i : Fin (k + 1)) → _root_.Path (p i) (q i)),
      (∀ i : Fin k,
        _root_.Path.Homotopic.Quotient.trans
            (⟦F i⟧ : _root_.Path.Homotopic.Quotient (p i.castSucc) (p i.succ))
            (⟦c i.succ⟧ : _root_.Path.Homotopic.Quotient (p i.succ) (q i.succ))
          = _root_.Path.Homotopic.Quotient.trans
              (⟦c i.castSucc⟧
                : _root_.Path.Homotopic.Quotient (p i.castSucc) (q i.castSucc))
              (⟦G i⟧ : _root_.Path.Homotopic.Quotient (q i.castSucc) (q i.succ))) →
      _root_.Path.Homotopic.Quotient.trans
          (⟦c 0⟧ : _root_.Path.Homotopic.Quotient (p 0) (q 0))
          (⟦_root_.Path.concat q G⟧
            : _root_.Path.Homotopic.Quotient (q 0) (q (Fin.last k)))
        = _root_.Path.Homotopic.Quotient.trans
            (⟦_root_.Path.concat p F⟧
              : _root_.Path.Homotopic.Quotient (p 0) (p (Fin.last k)))
            (⟦c (Fin.last k)⟧
              : _root_.Path.Homotopic.Quotient (p (Fin.last k)) (q (Fin.last k))) := by
  intro k
  induction k with
  | zero =>
    intro p q F G c _hsq
    have hpc : (⟦_root_.Path.concat p F⟧
        : _root_.Path.Homotopic.Quotient (p 0) (p (Fin.last 0)))
        = _root_.Path.Homotopic.Quotient.refl (p 0) := by
      rw [_root_.Path.concat_zero]; exact _root_.Path.Homotopic.Quotient.mk_refl _
    have hqc : (⟦_root_.Path.concat q G⟧
        : _root_.Path.Homotopic.Quotient (q 0) (q (Fin.last 0)))
        = _root_.Path.Homotopic.Quotient.refl (q 0) := by
      rw [_root_.Path.concat_zero]; exact _root_.Path.Homotopic.Quotient.mk_refl _
    change _root_.Path.Homotopic.Quotient.trans
        (⟦c 0⟧ : _root_.Path.Homotopic.Quotient (p 0) (q 0))
        (⟦_root_.Path.concat q G⟧
          : _root_.Path.Homotopic.Quotient (q 0) (q (Fin.last 0)))
      = _root_.Path.Homotopic.Quotient.trans
          (⟦_root_.Path.concat p F⟧
            : _root_.Path.Homotopic.Quotient (p 0) (p (Fin.last 0)))
          (⟦c 0⟧ : _root_.Path.Homotopic.Quotient (p 0) (q 0))
    rw [hpc, hqc]
    simp
  | succ n ih =>
    intro p q F G c hsq
    have hpsucc :
        (⟦_root_.Path.concat p F⟧
            : _root_.Path.Homotopic.Quotient (p 0) (p (Fin.last (n + 1))))
          = _root_.Path.Homotopic.Quotient.trans
              (⟦_root_.Path.concat (p ∘ Fin.castSucc)
                  (fun i => F i.castSucc)⟧
                : _root_.Path.Homotopic.Quotient
                    ((p ∘ Fin.castSucc) 0) ((p ∘ Fin.castSucc) (Fin.last n)))
              (⟦F (Fin.last n)⟧
                : _root_.Path.Homotopic.Quotient
                    (p (Fin.last n).castSucc) (p (Fin.last n).succ)) := by
      have := _root_.Path.concat_succ (n := n) p F
      rw [this]
      exact _root_.Path.Homotopic.Quotient.mk_trans _ _
    have hqsucc :
        (⟦_root_.Path.concat q G⟧
            : _root_.Path.Homotopic.Quotient (q 0) (q (Fin.last (n + 1))))
          = _root_.Path.Homotopic.Quotient.trans
              (⟦_root_.Path.concat (q ∘ Fin.castSucc)
                  (fun i => G i.castSucc)⟧
                : _root_.Path.Homotopic.Quotient
                    ((q ∘ Fin.castSucc) 0) ((q ∘ Fin.castSucc) (Fin.last n)))
              (⟦G (Fin.last n)⟧
                : _root_.Path.Homotopic.Quotient
                    (q (Fin.last n).castSucc) (q (Fin.last n).succ)) := by
      have := _root_.Path.concat_succ (n := n) q G
      rw [this]
      exact _root_.Path.Homotopic.Quotient.mk_trans _ _
    have ihapp := ih (p ∘ Fin.castSucc) (q ∘ Fin.castSucc)
      (fun i => F i.castSucc) (fun i => G i.castSucc)
      (fun i : Fin (n + 1) => (c i.castSucc :
        _root_.Path ((p ∘ Fin.castSucc) i) ((q ∘ Fin.castSucc) i)))
      (by intro i; exact hsq i.castSucc)
    have hsqlast := hsq (Fin.last n)
    have ihapp' :
        _root_.Path.Homotopic.Quotient.trans
            (⟦c 0⟧ : _root_.Path.Homotopic.Quotient
              ((p ∘ Fin.castSucc) 0) ((q ∘ Fin.castSucc) 0))
            (⟦_root_.Path.concat (q ∘ Fin.castSucc) (fun i => G i.castSucc)⟧
              : _root_.Path.Homotopic.Quotient
                  ((q ∘ Fin.castSucc) 0) ((q ∘ Fin.castSucc) (Fin.last n)))
          = _root_.Path.Homotopic.Quotient.trans
              (⟦_root_.Path.concat (p ∘ Fin.castSucc) (fun i => F i.castSucc)⟧
                : _root_.Path.Homotopic.Quotient
                    ((p ∘ Fin.castSucc) 0) ((p ∘ Fin.castSucc) (Fin.last n)))
              (⟦c (Fin.last n).castSucc⟧
                : _root_.Path.Homotopic.Quotient
                    (p (Fin.last n).castSucc) (q (Fin.last n).castSucc)) := ihapp
    rw [hpsucc, hqsucc]
    refine Eq.trans
      (_root_.Path.Homotopic.Quotient.trans_assoc
        (⟦c 0⟧) (⟦_root_.Path.concat (q ∘ Fin.castSucc) (fun i => G i.castSucc)⟧)
        (⟦G (Fin.last n)⟧)).symm ?_
    refine Eq.trans
      (congrArg
        (fun z => _root_.Path.Homotopic.Quotient.trans z (⟦G (Fin.last n)⟧))
        ihapp') ?_
    refine Eq.trans
      (_root_.Path.Homotopic.Quotient.trans_assoc
        (⟦_root_.Path.concat (p ∘ Fin.castSucc) (fun i => F i.castSucc)⟧)
        (⟦c (Fin.last n).castSucc⟧) (⟦G (Fin.last n)⟧)) ?_
    refine Eq.trans
      (congrArg
        (fun z => _root_.Path.Homotopic.Quotient.trans
          (⟦_root_.Path.concat (p ∘ Fin.castSucc) (fun i => F i.castSucc)⟧) z)
        hsqlast.symm) ?_
    exact (_root_.Path.Homotopic.Quotient.trans_assoc
      (⟦_root_.Path.concat (p ∘ Fin.castSucc) (fun i => F i.castSucc)⟧)
      (⟦F (Fin.last n)⟧) (⟦c (Fin.last n).succ⟧)).symm























theorem fundamentalGroup_countable_surjection_of_nullHomotopic_basis
    (X : Type*) [TopologicalSpace X]
    [SecondCountableTopology X] [ConnectedSpace X] [LocPathConnectedSpace X]
    [DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnectedSpace X]
    (x : X)
    (B : ℕ → Set X)
    (hBopen : ∀ n, IsOpen (B n))
    (hBpc : ∀ n, IsPathConnected (B n))
    (hBnull : ∀ n, ∀ (y : X) (_ : y ∈ B n) (γ : _root_.Path y y),
      Set.range γ.toContinuousMap ⊆ B n →
        (⟦γ⟧ : _root_.Path.Homotopic.Quotient y y) = ⟦_root_.Path.refl y⟧)
    (hBbasis : TopologicalSpace.IsTopologicalBasis (Set.range B))
    (hpcInter :
      ∀ (m n : ℕ),
        ∀ a, a ∈ B m → a ∈ B n → ∀ b, b ∈ B m → b ∈ B n →
          JoinedIn (B m ∩ B n) a b) :
    ∃ (S : Type) (_ : Countable S) (f : S → FundamentalGroup X x),
      Function.Surjective f := by
  classical
  haveI : Nonempty X := ⟨x⟩
  haveI : PathConnectedSpace X := PathConnectedSpace.of_locPathConnectedSpace
  have hBcov : (⋃ n, B n) = (Set.univ : Set X) := by
    have hsu : ⋃₀ (Set.range B) = (Set.univ : Set X) := hBbasis.sUnion_eq
    rw [Set.sUnion_range] at hsu; exact hsu
  obtain ⟨anchor, hanchor⟩ := uc_pi1_countable_anchors X B
  let S : Type := Σ k : ℕ, Fin k → ℕ
  haveI hScount : Countable S := inferInstance
  let polyVertex : ∀ {k : ℕ}, (Fin k → ℕ) → Fin (k + 1) → X :=
    fun {k} idx i =>
      if h : 0 < (i : ℕ) ∧ (i : ℕ) < k then
        anchor (idx ⟨(i : ℕ) - 1, by omega⟩, idx ⟨(i : ℕ), h.2⟩)
      else x
  have polyVertex_zero :
      ∀ {k : ℕ} (idx : Fin k → ℕ),
        polyVertex idx (0 : Fin (k + 1)) = x := by
    intro k idx
    simp [polyVertex]
  have polyVertex_last :
      ∀ {k : ℕ} (idx : Fin k → ℕ),
        polyVertex idx (Fin.last k) = x := by
    intro k idx
    simp [polyVertex, Fin.val_last]
  let f : S → FundamentalGroup X x := fun s =>
    let k := s.fst
    let idx := s.snd
    if hvalid :
        ∀ i : Fin k,
          (polyVertex idx i.castSucc ∈ B (idx i)) ∧
          (polyVertex idx i.succ ∈ B (idx i)) then
      let seg : (i : Fin k) → _root_.Path
          (polyVertex idx i.castSucc) (polyVertex idx i.succ) :=
        fun i =>
          ((hBpc (idx i)).joinedIn _ (hvalid i).1 _ (hvalid i).2).somePath
      let p₀ : Fin (k + 1) → X := fun j => polyVertex idx j
      let polyLoop : _root_.Path x x :=
        (_root_.Path.concat p₀ seg).cast
          (show x = p₀ 0 from (polyVertex_zero idx).symm)
          (show x = p₀ (Fin.last k) from (polyVertex_last idx).symm)
      FundamentalGroup.fromPath ⟦polyLoop⟧
    else
      FundamentalGroup.fromPath ⟦_root_.Path.refl x⟧
  refine ⟨S, hScount, f, ?_⟩
  intro g
  let q : _root_.Path.Homotopic.Quotient x x := FundamentalGroup.toPath g
  obtain ⟨γ, hγ⟩ : ∃ γ : _root_.Path x x,
      (⟦γ⟧ : _root_.Path.Homotopic.Quotient x x) = q :=
    Quotient.exists_rep q
  obtain ⟨k, t, idx, ht0, htlast, htmono', hidx⟩ :=
    uc_pi1_countable_lebesgue_subdivision X B hBopen hBcov γ
  have htmono : Monotone t := by
    apply Fin.monotone_iff_le_succ.mpr
    intro i
    exact Subtype.coe_le_coe.mp (htmono' i)
  refine ⟨⟨k, idx⟩, ?_⟩
  have hγ0 : γ (t 0 : unitInterval) = x := by rw [ht0]; exact γ.source
  have hγlast : γ (t (Fin.last k) : unitInterval) = x := by
    rw [htlast]; exact γ.target
  have hExtend : ∀ i : Fin (k + 1),
      γ.extend ((t i : unitInterval) : ℝ) = γ (t i : unitInterval) :=
    fun i => _root_.Path.extend_extends' γ (t i : (Icc (0 : ℝ) 1 : Set ℝ))
  have htle : ∀ i : Fin k,
      ((t i.castSucc : unitInterval) : ℝ) ≤ ((t i.succ : unitInterval) : ℝ) :=
    fun i => htmono' i
  have hγ_castSucc_in : ∀ i : Fin k, γ (t i.castSucc) ∈ B (idx i) :=
    fun i => hidx i (t i.castSucc) (le_refl _) (htle i)
  have hγ_succ_in : ∀ i : Fin k, γ (t i.succ) ∈ B (idx i) :=
    fun i => hidx i (t i.succ) (htle i) (le_refl _)
  let T : (i : Fin k) →
      _root_.Path (γ.extend ((t i.castSucc : unitInterval) : ℝ))
                  (γ.extend ((t i.succ : unitInterval) : ℝ)) :=
    fun i => γ.truncateOfLE (htle i)
  have ha_eq : x = γ.extend ((t 0 : unitInterval) : ℝ) := by rw [ht0]; simp
  have hb_eq : x = γ.extend ((t (Fin.last k) : unitInterval) : ℝ) := by
    rw [htlast]; simp
  let concatT : _root_.Path x x :=
    (concatTrans (p := fun i => γ.extend ((t i : unitInterval) : ℝ)) T).cast
      ha_eq hb_eq
  have hγ_concatT : γ.Homotopic concatT :=
    Path.trans_truncate_homotopic γ t ht0 htlast htmono
  have hquot_γ_concatT :
      (⟦γ⟧ : _root_.Path.Homotopic.Quotient x x) = ⟦concatT⟧ :=
    Quotient.sound hγ_concatT
  have hT_range : ∀ i : Fin k,
      ∀ s : unitInterval, (T i s : X) ∈ B (idx i) := by
    intro i s
    set u : ℝ := min (max (s : ℝ) ((t i.castSucc : unitInterval) : ℝ))
        ((t i.succ : unitInterval) : ℝ) with hudef
    have hu_lo : ((t i.castSucc : unitInterval) : ℝ) ≤ u := by
      rw [hudef]; exact le_min (le_max_right _ _) (htle i)
    have hu_hi : u ≤ ((t i.succ : unitInterval) : ℝ) := by
      rw [hudef]; exact min_le_right _ _
    have hu_mem : u ∈ (Icc 0 1 : Set ℝ) := by
      refine ⟨?_, ?_⟩
      · exact (t i.castSucc : unitInterval).2.1.trans hu_lo
      · exact hu_hi.trans (t i.succ : unitInterval).2.2
    have hTval : ((T i) s : X) = γ ⟨u, hu_mem⟩ := by
      have hcoe : ((T i) s : X) = ((γ.truncate
          ((t i.castSucc : unitInterval) : ℝ)
          ((t i.succ : unitInterval) : ℝ)) s : X) := by
        simp [T, _root_.Path.truncateOfLE]
      have hext : γ.extend u = γ ⟨u, hu_mem⟩ := _root_.Path.extend_apply _ hu_mem
      have htr : ((γ.truncate
          ((t i.castSucc : unitInterval) : ℝ)
          ((t i.succ : unitInterval) : ℝ)) s : X) = γ.extend u := by
        simp [_root_.Path.truncate, hudef]
      rw [hcoe, htr, hext]
    rw [hTval]
    exact hidx i ⟨u, hu_mem⟩ hu_lo hu_hi
  have hcast_val : ∀ i : Fin k, (i.castSucc : ℕ) = (i : ℕ) := fun i => rfl
  have hsucc_val : ∀ i : Fin k, (i.succ : ℕ) = (i : ℕ) + 1 := fun i => rfl
  have hVertex_castSucc : ∀ i : Fin k,
      polyVertex idx i.castSucc ∈ B (idx i) := by
    intro i
    have hi_lt_k : (i : ℕ) < k := i.isLt
    by_cases h0 : (i : ℕ) = 0
    · have hpv : polyVertex idx i.castSucc = x := by
        change (if h : 0 < (i.castSucc : ℕ) ∧ (i.castSucc : ℕ) < k
              then anchor _ else x) = x
        rw [dif_neg]
        intro ⟨hpos, _⟩
        rw [hcast_val] at hpos
        omega
      rw [hpv]
      have ht_eq : t i.castSucc = t 0 := by
        apply congrArg
        apply Fin.ext
        change (i.castSucc : ℕ) = (0 : Fin (k + 1)).val
        rw [hcast_val, h0]; rfl
      have hxγ : γ (t i.castSucc) = x := by rw [ht_eq, hγ0]
      rw [← hxγ]
      exact hγ_castSucc_in i
    · have hpos : 0 < (i.castSucc : ℕ) := by rw [hcast_val]; omega
      have hlt_k : (i.castSucc : ℕ) < k := by rw [hcast_val]; exact hi_lt_k
      have hi_prev_lt_k : (i : ℕ) - 1 < k := by omega
      let ip : Fin k := ⟨(i : ℕ) - 1, hi_prev_lt_k⟩
      have hip_succ_val : (ip.succ : ℕ) = (i : ℕ) := by
        change (ip : ℕ) + 1 = (i : ℕ)
        change (i : ℕ) - 1 + 1 = (i : ℕ)
        omega
      have ht_ip_succ_eq : t ip.succ = t i.castSucc := by
        apply congrArg
        apply Fin.ext
        rw [hip_succ_val, hcast_val]
      have ht_ip_castSucc_le : ((t ip.castSucc : unitInterval) : ℝ)
          ≤ ((t i.castSucc : unitInterval) : ℝ) := by
        apply Subtype.coe_le_coe.mpr
        apply htmono
        change ip.castSucc ≤ i.castSucc
        apply Fin.mk_le_mk.mpr
        change (i : ℕ) - 1 ≤ (i : ℕ)
        omega
      have hγ_at_ip : γ (t i.castSucc) ∈ B (idx ip) := by
        refine hidx ip (t i.castSucc) ht_ip_castSucc_le ?_
        rw [← ht_ip_succ_eq]
      have hγ_at_i : γ (t i.castSucc) ∈ B (idx i) := hγ_castSucc_in i
      have hnonempty : (B (idx ip) ∩ B (idx i)).Nonempty :=
        ⟨γ (t i.castSucc), hγ_at_ip, hγ_at_i⟩
      have hanchor_mem : anchor (idx ip, idx i)
          ∈ B (idx ip) ∩ B (idx i) :=
        hanchor (idx ip, idx i) hnonempty
      have hpv : polyVertex idx i.castSucc
          = anchor (idx ⟨(i.castSucc : ℕ) - 1,
              by rw [hcast_val]; omega⟩, idx ⟨(i.castSucc : ℕ), hlt_k⟩) := by
        change (if h : 0 < (i.castSucc : ℕ) ∧ (i.castSucc : ℕ) < k
              then anchor (idx ⟨(i.castSucc : ℕ) - 1, by omega⟩,
                idx ⟨(i.castSucc : ℕ), h.2⟩) else x)
            = anchor _
        rw [dif_pos ⟨hpos, hlt_k⟩]
      rw [hpv]
      have hidx_eq1 : (⟨(i.castSucc : ℕ) - 1,
          by rw [hcast_val]; omega⟩ : Fin k) = ip := by
        apply Fin.ext
        change (i.castSucc : ℕ) - 1 = (i : ℕ) - 1
        rw [hcast_val]
      have hidx_eq2 : (⟨(i.castSucc : ℕ), hlt_k⟩ : Fin k) = i := by
        apply Fin.ext; rw [hcast_val]
      rw [hidx_eq1, hidx_eq2]
      exact hanchor_mem.2
  have hVertex_succ : ∀ i : Fin k,
      polyVertex idx i.succ ∈ B (idx i) := by
    intro i
    have hi_lt_k : (i : ℕ) < k := i.isLt
    have hsucc_lt : (i.succ : ℕ) ≤ k := Nat.lt_succ_iff.mp i.succ.isLt
    by_cases hk : (i : ℕ) + 1 = k
    · have hpv : polyVertex idx i.succ = x := by
        change (if h : 0 < (i.succ : ℕ) ∧ (i.succ : ℕ) < k
              then anchor _ else x) = x
        rw [dif_neg]
        intro ⟨_, hlt⟩
        rw [hsucc_val] at hlt
        omega
      rw [hpv]
      have ht_eq : t i.succ = t (Fin.last k) := by
        apply congrArg; apply Fin.ext
        rw [Fin.val_last, hsucc_val]; exact hk
      have hxγ : γ (t i.succ) = x := by rw [ht_eq, hγlast]
      rw [← hxγ]
      exact hγ_succ_in i
    · have hi_next_lt_k : (i : ℕ) + 1 < k := by
        rw [← hsucc_val] at hk ⊢
        omega
      have hpos : 0 < (i.succ : ℕ) := by rw [hsucc_val]; omega
      have hlt : (i.succ : ℕ) < k := by rw [hsucc_val]; exact hi_next_lt_k
      let i_next : Fin k := ⟨(i : ℕ) + 1, hi_next_lt_k⟩
      have hin_castSucc_val : (i_next.castSucc : ℕ) = (i : ℕ) + 1 := by rfl
      have ht_in_castSucc_eq : t i_next.castSucc = t i.succ := by
        apply congrArg; apply Fin.ext
        rw [hin_castSucc_val, hsucc_val]
      have ht_in_succ_ge : ((t i.succ : unitInterval) : ℝ)
          ≤ ((t i_next.succ : unitInterval) : ℝ) := by
        apply Subtype.coe_le_coe.mpr
        apply htmono
        change i.succ ≤ i_next.succ
        apply Fin.mk_le_mk.mpr
        change (i : ℕ) + 1 ≤ (i : ℕ) + 1 + 1
        omega
      have hγ_at_in : γ (t i.succ) ∈ B (idx i_next) := by
        refine hidx i_next (t i.succ) ?_ ht_in_succ_ge
        rw [← ht_in_castSucc_eq]
      have hγ_at_i : γ (t i.succ) ∈ B (idx i) := hγ_succ_in i
      have hnonempty : (B (idx i) ∩ B (idx i_next)).Nonempty :=
        ⟨γ (t i.succ), hγ_at_i, hγ_at_in⟩
      have hanchor_mem : anchor (idx i, idx i_next)
          ∈ B (idx i) ∩ B (idx i_next) :=
        hanchor (idx i, idx i_next) hnonempty
      have hpv : polyVertex idx i.succ
          = anchor (idx ⟨(i.succ : ℕ) - 1,
              by rw [hsucc_val]; omega⟩, idx ⟨(i.succ : ℕ), hlt⟩) := by
        change (if h : 0 < (i.succ : ℕ) ∧ (i.succ : ℕ) < k
              then anchor (idx ⟨(i.succ : ℕ) - 1, by omega⟩,
                idx ⟨(i.succ : ℕ), h.2⟩) else x)
            = anchor _
        rw [dif_pos ⟨hpos, hlt⟩]
      rw [hpv]
      have hidx_eq1 : (⟨(i.succ : ℕ) - 1,
          by rw [hsucc_val]; omega⟩ : Fin k) = i := by
        apply Fin.ext
        change (i.succ : ℕ) - 1 = (i : ℕ)
        rw [hsucc_val]; omega
      have hidx_eq2 : (⟨(i.succ : ℕ), hlt⟩ : Fin k) = i_next := by
        apply Fin.ext
        change (i.succ : ℕ) = (i : ℕ) + 1
        rw [hsucc_val]
      rw [hidx_eq1, hidx_eq2]
      exact hanchor_mem.1
  have hvalid : ∀ i : Fin k,
      (polyVertex idx i.castSucc ∈ B (idx i)) ∧
      (polyVertex idx i.succ ∈ B (idx i)) :=
    fun i => ⟨hVertex_castSucc i, hVertex_succ i⟩
  let seg : (i : Fin k) → _root_.Path
      (polyVertex idx i.castSucc) (polyVertex idx i.succ) :=
    fun i =>
      ((hBpc (idx i)).joinedIn _ (hvalid i).1 _ (hvalid i).2).somePath
  have hseg_range : ∀ i : Fin k, ∀ s : unitInterval,
      (seg i s : X) ∈ B (idx i) := by
    intro i s
    exact ((hBpc (idx i)).joinedIn _ (hvalid i).1 _ (hvalid i).2).somePath_mem s
  let p₀ : Fin (k + 1) → X := fun j => polyVertex idx j
  let polyLoop : _root_.Path x x :=
    (_root_.Path.concat p₀ seg).cast
      (show x = p₀ 0 from (polyVertex_zero idx).symm)
      (show x = p₀ (Fin.last k) from (polyVertex_last idx).symm)
  have hf_unfold : f ⟨k, idx⟩ = FundamentalGroup.fromPath ⟦polyLoop⟧ := by
    change (if hv :
        ∀ i : Fin k,
          (polyVertex idx i.castSucc ∈ B (idx i)) ∧
          (polyVertex idx i.succ ∈ B (idx i)) then
      let seg' : (i : Fin k) → _root_.Path
          (polyVertex idx i.castSucc) (polyVertex idx i.succ) :=
        fun i =>
          ((hBpc (idx i)).joinedIn _ (hv i).1 _ (hv i).2).somePath
      let p₀' : Fin (k + 1) → X := fun j => polyVertex idx j
      let polyLoop' : _root_.Path x x :=
        (_root_.Path.concat p₀' seg').cast
          (show x = p₀' 0 from (polyVertex_zero idx).symm)
          (show x = p₀' (Fin.last k) from (polyVertex_last idx).symm)
      FundamentalGroup.fromPath ⟦polyLoop'⟧
    else
      FundamentalGroup.fromPath ⟦_root_.Path.refl x⟧)
      = FundamentalGroup.fromPath ⟦polyLoop⟧
    rw [dif_pos hvalid]
  rw [hf_unfold]
  have hg_unfold : g = FundamentalGroup.fromPath q := rfl
  rw [hg_unfold]
  have hgoal_red :
      (⟦polyLoop⟧ : _root_.Path.Homotopic.Quotient x x) = q ↔
        (⟦polyLoop⟧ : _root_.Path.Homotopic.Quotient x x) = ⟦concatT⟧ := by
    rw [← hγ, hquot_γ_concatT]
  suffices hquot : (⟦polyLoop⟧ : _root_.Path.Homotopic.Quotient x x) = ⟦concatT⟧ by
    have : (⟦polyLoop⟧ : _root_.Path.Homotopic.Quotient x x) = q :=
      hgoal_red.mpr hquot
    exact congrArg FundamentalGroup.fromPath this
  let γv : Fin (k + 1) → X := fun i => γ.extend ((t i : unitInterval) : ℝ)
  have hγv_eq : ∀ i : Fin (k + 1), γv i = γ (t i) := fun i => hExtend i
  have hp0 : p₀ (0 : Fin (k + 1)) = x := polyVertex_zero idx
  have hplast : p₀ (Fin.last k) = x := polyVertex_last idx
  have hγv0 : γv (0 : Fin (k + 1)) = x := by
    change γ.extend ((t 0 : unitInterval) : ℝ) = x; rw [← ha_eq]
  have hγvlast : γv (Fin.last k) = x := by
    change γ.extend ((t (Fin.last k) : unitInterval) : ℝ) = x; rw [← hb_eq]
  have hγv_castSucc_in : ∀ i : Fin k, γv i.castSucc ∈ B (idx i) := by
    intro i; rw [hγv_eq]; exact hγ_castSucc_in i
  have hγv_succ_in : ∀ i : Fin k, γv i.succ ∈ B (idx i) := by
    intro i; rw [hγv_eq]; exact hγ_succ_in i
  have hp0_castSucc_in : ∀ i : Fin k, p₀ i.castSucc ∈ B (idx i) :=
    fun i => hVertex_castSucc i
  have hp0_succ_in : ∀ i : Fin k, p₀ i.succ ∈ B (idx i) :=
    fun i => hVertex_succ i
  have hconn :
      ∃ c : (i : Fin (k + 1)) → _root_.Path (p₀ i) (γv i),
        (∀ i : Fin k, ∀ s : unitInterval, (c i.castSucc s : X) ∈ B (idx i)) ∧
        (∀ i : Fin k, ∀ s : unitInterval, (c i.succ s : X) ∈ B (idx i)) ∧
        (c 0 = (_root_.Path.refl x).cast hp0 hγv0) ∧
        (c (Fin.last k) = (_root_.Path.refl x).cast hplast hγvlast) := by
    have buildVertex : ∀ j : Fin (k + 1),
        ∃ cj : _root_.Path (p₀ j) (γv j),
          (∀ (hj : (j : ℕ) < k) (s : unitInterval),
            (cj s : X) ∈ B (idx ⟨(j : ℕ), hj⟩)) ∧
          (∀ (hj : 0 < (j : ℕ)) (s : unitInterval),
            (cj s : X) ∈ B (idx ⟨(j : ℕ) - 1, by omega⟩)) ∧
          (∀ (_hbd : (j : ℕ) = 0 ∨ (j : ℕ) = k),
            ∃ (hpjx : p₀ j = x) (hgjx : γv j = x),
              cj = (_root_.Path.refl x).cast hpjx hgjx) := by
      intro j
      by_cases hb0 : (j : ℕ) = 0
      · have hjeq : j = (0 : Fin (k + 1)) := Fin.ext (by rw [hb0]; rfl)
        have hpj : p₀ j = x := by rw [hjeq]; exact hp0
        have hgj : γv j = x := by rw [hjeq]; exact hγv0
        refine ⟨(_root_.Path.refl x).cast hpj hgj, ?_, ?_, ?_⟩
        · intro hj s
          have hval : ((((_root_.Path.refl x).cast hpj hgj) s) : X) = x := by
            rw [_root_.Path.cast_coe]; rfl
          rw [hval]
          have hidx0 : (⟨(j : ℕ), hj⟩ : Fin k).castSucc = (j : Fin (k + 1)) := by
            apply Fin.ext; rfl
          have hpv : p₀ (⟨(j : ℕ), hj⟩ : Fin k).castSucc = x := by
            rw [hidx0, hpj]
          have := hp0_castSucc_in ⟨(j : ℕ), hj⟩
          rwa [hpv] at this
        · intro hj s; omega
        · intro _hbd; exact ⟨hpj, hgj, rfl⟩
      · by_cases hblast : (j : ℕ) = k
        · have hjeq : j = Fin.last k := Fin.ext (by rw [hblast, Fin.val_last])
          have hpj : p₀ j = x := by rw [hjeq]; exact hplast
          have hgj : γv j = x := by rw [hjeq]; exact hγvlast
          refine ⟨(_root_.Path.refl x).cast hpj hgj, ?_, ?_, ?_⟩
          · intro hj s; omega
          · intro hj s
            have hval : ((((_root_.Path.refl x).cast hpj hgj) s) : X) = x := by
              rw [_root_.Path.cast_coe]; rfl
            rw [hval]
            have hjb_lt : (j : ℕ) - 1 < k := by omega
            have hidxs : (⟨(j : ℕ) - 1, hjb_lt⟩ : Fin k).succ = (j : Fin (k + 1)) := by
              apply Fin.ext
              change ((j : ℕ) - 1) + 1 = (j : ℕ); omega
            have hpv : p₀ (⟨(j : ℕ) - 1, hjb_lt⟩ : Fin k).succ = x := by
              rw [hidxs, hpj]
            have := hp0_succ_in ⟨(j : ℕ) - 1, hjb_lt⟩
            rwa [hpv] at this
          · intro _hbd; exact ⟨hpj, hgj, rfl⟩
        · have hjpos : 0 < (j : ℕ) := Nat.pos_of_ne_zero hb0
          have hjlt : (j : ℕ) < k := by have := j.isLt; omega
          have hjb_lt : (j : ℕ) - 1 < k := by omega
          set jf : Fin k := ⟨(j : ℕ), hjlt⟩ with hjf_def
          set jb : Fin k := ⟨(j : ℕ) - 1, hjb_lt⟩ with hjb_def
          have hjf_cast : jf.castSucc = (j : Fin (k + 1)) := by apply Fin.ext; rfl
          have hjb_succ : jb.succ = (j : Fin (k + 1)) := by
            apply Fin.ext
            change ((j : ℕ) - 1) + 1 = (j : ℕ); omega
          have hp0_in_f : p₀ j ∈ B (idx jf) := by
            have := hp0_castSucc_in jf; rwa [hjf_cast] at this
          have hp0_in_b : p₀ j ∈ B (idx jb) := by
            have := hp0_succ_in jb; rwa [hjb_succ] at this
          have hgv_in_f : γv j ∈ B (idx jf) := by
            have := hγv_castSucc_in jf; rwa [hjf_cast] at this
          have hgv_in_b : γv j ∈ B (idx jb) := by
            have := hγv_succ_in jb; rwa [hjb_succ] at this
          have hjoin : JoinedIn (B (idx jb) ∩ B (idx jf)) (p₀ j) (γv j) :=
            hpcInter (idx jb) (idx jf) (p₀ j) hp0_in_b hp0_in_f
              (γv j) hgv_in_b hgv_in_f
          refine ⟨hjoin.somePath, ?_, ?_, ?_⟩
          · intro hj s
            have hidxeq : (⟨(j : ℕ), hj⟩ : Fin k) = jf := by apply Fin.ext; rfl
            rw [hidxeq]; exact (hjoin.somePath_mem s).2
          · intro hj s
            have hidxeq : (⟨(j : ℕ) - 1, by omega⟩ : Fin k) = jb := by
              apply Fin.ext; rfl
            rw [hidxeq]; exact (hjoin.somePath_mem s).1
          · intro hbd; omega
    choose c hc_f hc_b hc_bdry using buildVertex
    refine ⟨c, ?_, ?_, ?_, ?_⟩
    · intro i s
      have hlt : ((i.castSucc : Fin (k + 1)) : ℕ) < k := by
        change (i : ℕ) < k; exact i.isLt
      have := hc_f i.castSucc hlt s
      have hidxeq : (⟨((i.castSucc : Fin (k + 1)) : ℕ), hlt⟩ : Fin k) = i := by
        apply Fin.ext; rfl
      rwa [hidxeq] at this
    · intro i s
      have hpos : 0 < ((i.succ : Fin (k + 1)) : ℕ) := by
        change 0 < (i : ℕ) + 1; omega
      have := hc_b i.succ hpos s
      have hidxeq : (⟨((i.succ : Fin (k + 1)) : ℕ) - 1, by
          change (i : ℕ) + 1 - 1 < k; omega⟩ : Fin k) = i := by
        apply Fin.ext
        change (i : ℕ) + 1 - 1 = (i : ℕ); omega
      rwa [hidxeq] at this
    · obtain ⟨hpjx, hgjx, heq⟩ := hc_bdry 0 (Or.inl rfl)
      rw [heq]
    · obtain ⟨hpjx, hgjx, heq⟩ := hc_bdry (Fin.last k) (Or.inr (by simp [Fin.val_last]))
      rw [heq]
  obtain ⟨c, hc_cs, hc_su, hc0, hclast⟩ := hconn
  let T' : (i : Fin k) → _root_.Path (γv i.castSucc) (γv i.succ) := fun i => T i
  have range_subset_of_mem :
      ∀ {a b : X} (u : _root_.Path a b) (n : ℕ),
        (∀ s : unitInterval, (u s : X) ∈ B n) →
        Set.range u.toContinuousMap ⊆ B n := by
    intro a b u n hu z hz
    rcases hz with ⟨s, hs⟩
    have : (u s : X) ∈ B n := hu s
    simpa [Path.coe_toContinuousMap] using hs ▸ this
  have hT'_range : ∀ i : Fin k,
      Set.range (T' i).toContinuousMap ⊆ B (idx i) :=
    fun i => range_subset_of_mem (T' i) (idx i) (fun s => hT_range i s)
  have hseg_range' : ∀ i : Fin k,
      Set.range (seg i).toContinuousMap ⊆ B (idx i) :=
    fun i => range_subset_of_mem (seg i) (idx i) (fun s => hseg_range i s)
  have hc_cs_range : ∀ i : Fin k,
      Set.range (c i.castSucc).toContinuousMap ⊆ B (idx i) :=
    fun i => range_subset_of_mem (c i.castSucc) (idx i) (hc_cs i)
  have hc_su_range : ∀ i : Fin k,
      Set.range (c i.succ).toContinuousMap ⊆ B (idx i) :=
    fun i => range_subset_of_mem (c i.succ) (idx i) (hc_su i)
  have htrans_range_subset :
      ∀ {a b d : X} (u : _root_.Path a b) (v : _root_.Path b d) (n : ℕ),
        Set.range u.toContinuousMap ⊆ B n →
        Set.range v.toContinuousMap ⊆ B n →
        Set.range (u.trans v).toContinuousMap ⊆ B n := by
    intro a b d u v n hu hv z hz
    rcases hz with ⟨s, hs⟩
    have hz' : z ∈ Set.range ((u.trans v) : unitInterval → X) :=
      ⟨s, by simpa [Path.coe_toContinuousMap] using hs⟩
    rw [Path.trans_range] at hz'
    rcases hz' with h1 | h2
    · rcases h1 with ⟨s', hs'⟩
      exact hu ⟨s', by simpa [Path.coe_toContinuousMap] using hs'⟩
    · rcases h2 with ⟨s', hs'⟩
      exact hv ⟨s', by simpa [Path.coe_toContinuousMap] using hs'⟩
  have hsquare : ∀ i : Fin k,
      _root_.Path.Homotopic.Quotient.trans
          (⟦seg i⟧ : _root_.Path.Homotopic.Quotient (p₀ i.castSucc) (p₀ i.succ))
          (⟦c i.succ⟧ : _root_.Path.Homotopic.Quotient (p₀ i.succ) (γv i.succ))
        = _root_.Path.Homotopic.Quotient.trans
            (⟦c i.castSucc⟧
              : _root_.Path.Homotopic.Quotient (p₀ i.castSucc) (γv i.castSucc))
            (⟦T' i⟧ : _root_.Path.Homotopic.Quotient (γv i.castSucc) (γv i.succ)) := by
    intro i
    have hpiece :
        (⟦(seg i).trans (c i.succ)⟧
            : _root_.Path.Homotopic.Quotient (p₀ i.castSucc) (γv i.succ))
          = ⟦(c i.castSucc).trans (T' i)⟧ :=
      uc_pi1_countable_piece_homotopy X B hBnull (idx i)
        ((seg i).trans (c i.succ)) ((c i.castSucc).trans (T' i))
        (htrans_range_subset (seg i) (c i.succ) (idx i)
          (hseg_range' i) (hc_su_range i))
        (htrans_range_subset (c i.castSucc) (T' i) (idx i)
          (hc_cs_range i) (hT'_range i))
    exact (_root_.Path.Homotopic.Quotient.mk_trans (seg i) (c i.succ)).symm.trans
      (hpiece.trans (_root_.Path.Homotopic.Quotient.mk_trans (c i.castSucc) (T' i)))
  have htel :
      _root_.Path.Homotopic.Quotient.trans
          (⟦c 0⟧ : _root_.Path.Homotopic.Quotient (p₀ 0) (γv 0))
          (⟦_root_.Path.concat γv T'⟧
            : _root_.Path.Homotopic.Quotient (γv 0) (γv (Fin.last k)))
        = _root_.Path.Homotopic.Quotient.trans
            (⟦_root_.Path.concat p₀ seg⟧
              : _root_.Path.Homotopic.Quotient (p₀ 0) (p₀ (Fin.last k)))
            (⟦c (Fin.last k)⟧
              : _root_.Path.Homotopic.Quotient (p₀ (Fin.last k)) (γv (Fin.last k))) :=
    uc_pi1_countable_telescope p₀ γv seg T' c hsquare
  have htel' :
      (⟦(c 0).trans (_root_.Path.concat γv T')⟧
        : _root_.Path.Homotopic.Quotient (p₀ 0) (γv (Fin.last k)))
        = ⟦(_root_.Path.concat p₀ seg).trans (c (Fin.last k))⟧ :=
    (_root_.Path.Homotopic.Quotient.mk_trans (c 0) (_root_.Path.concat γv T')).trans
      (htel.trans
        (_root_.Path.Homotopic.Quotient.mk_trans
          (_root_.Path.concat p₀ seg) (c (Fin.last k))).symm)
  have qtrans_cast :
      ∀ {a₁ a₂ b₁ b₂ d₁ d₂ : X}
        (A : _root_.Path.Homotopic.Quotient a₂ b₂)
        (Bq : _root_.Path.Homotopic.Quotient b₂ d₂)
        (ha : a₁ = a₂) (hb : b₁ = b₂) (hd : d₁ = d₂),
        _root_.Path.Homotopic.Quotient.cast
            (_root_.Path.Homotopic.Quotient.trans A Bq) ha hd
          = _root_.Path.Homotopic.Quotient.trans
              (_root_.Path.Homotopic.Quotient.cast A ha hb)
              (_root_.Path.Homotopic.Quotient.cast Bq hb hd) := by
    intro a₁ a₂ b₁ b₂ d₁ d₂ A Bq ha hb hd
    induction A using Quotient.ind with | _ a =>
    induction Bq using Quotient.ind with | _ b =>
    rfl
  have htelcast :
      _root_.Path.Homotopic.Quotient.trans
          (_root_.Path.Homotopic.Quotient.cast
            (⟦c 0⟧ : _root_.Path.Homotopic.Quotient (p₀ 0) (γv 0)) hp0.symm hγv0.symm)
          (_root_.Path.Homotopic.Quotient.cast
            (⟦_root_.Path.concat γv T'⟧
              : _root_.Path.Homotopic.Quotient (γv 0) (γv (Fin.last k)))
            hγv0.symm hb_eq)
        = _root_.Path.Homotopic.Quotient.trans
            (_root_.Path.Homotopic.Quotient.cast
              (⟦_root_.Path.concat p₀ seg⟧
                : _root_.Path.Homotopic.Quotient (p₀ 0) (p₀ (Fin.last k)))
              hp0.symm hplast.symm)
            (_root_.Path.Homotopic.Quotient.cast
              (⟦c (Fin.last k)⟧
                : _root_.Path.Homotopic.Quotient (p₀ (Fin.last k)) (γv (Fin.last k)))
              hplast.symm hb_eq) := by
    have hbase :
        _root_.Path.Homotopic.Quotient.cast
            (⟦(c 0).trans (_root_.Path.concat γv T')⟧
              : _root_.Path.Homotopic.Quotient (p₀ 0) (γv (Fin.last k))) hp0.symm hb_eq
          = _root_.Path.Homotopic.Quotient.cast
              (⟦(_root_.Path.concat p₀ seg).trans (c (Fin.last k))⟧
                : _root_.Path.Homotopic.Quotient (p₀ 0) (γv (Fin.last k))) hp0.symm hb_eq :=
      congrArg
        (fun w => _root_.Path.Homotopic.Quotient.cast w hp0.symm hb_eq) htel'
    exact hbase
  have hc0cast :
      _root_.Path.Homotopic.Quotient.cast
          (⟦c 0⟧ : _root_.Path.Homotopic.Quotient (p₀ 0) (γv 0)) hp0.symm hγv0.symm
        = _root_.Path.Homotopic.Quotient.refl x := by
    rw [hc0]
    change (⟦((_root_.Path.refl x).cast hp0 hγv0).cast hp0.symm hγv0.symm⟧
        : _root_.Path.Homotopic.Quotient x x) = ⟦_root_.Path.refl x⟧
    exact congrArg (fun p : _root_.Path x x => (⟦p⟧ : _root_.Path.Homotopic.Quotient x x))
      (Path.ext rfl)
  have hclastcast :
      _root_.Path.Homotopic.Quotient.cast
          (⟦c (Fin.last k)⟧
            : _root_.Path.Homotopic.Quotient (p₀ (Fin.last k)) (γv (Fin.last k)))
          hplast.symm hb_eq
        = _root_.Path.Homotopic.Quotient.refl x := by
    rw [hclast]
    change (⟦((_root_.Path.refl x).cast hplast hγvlast).cast hplast.symm hb_eq⟧
        : _root_.Path.Homotopic.Quotient x x) = ⟦_root_.Path.refl x⟧
    exact congrArg (fun p : _root_.Path x x => (⟦p⟧ : _root_.Path.Homotopic.Quotient x x))
      (Path.ext rfl)
  rw [hc0cast, hclastcast,
      _root_.Path.Homotopic.Quotient.refl_trans,
      _root_.Path.Homotopic.Quotient.trans_refl] at htelcast
  have hLq : _root_.Path.Homotopic.Quotient.cast
      (⟦_root_.Path.concat γv T'⟧
        : _root_.Path.Homotopic.Quotient (γv 0) (γv (Fin.last k))) hγv0.symm hb_eq
        = (⟦concatT⟧ : _root_.Path.Homotopic.Quotient x x) := by
    change (⟦(_root_.Path.concat γv T').cast hγv0.symm hb_eq⟧
        : _root_.Path.Homotopic.Quotient x x) = ⟦concatT⟧
    exact congrArg (fun p : _root_.Path x x => (⟦p⟧ : _root_.Path.Homotopic.Quotient x x))
      (Path.ext rfl)
  have hRq : _root_.Path.Homotopic.Quotient.cast
      (⟦_root_.Path.concat p₀ seg⟧
        : _root_.Path.Homotopic.Quotient (p₀ 0) (p₀ (Fin.last k))) hp0.symm hplast.symm
        = (⟦polyLoop⟧ : _root_.Path.Homotopic.Quotient x x) := by
    change (⟦(_root_.Path.concat p₀ seg).cast hp0.symm hplast.symm⟧
        : _root_.Path.Homotopic.Quotient x x) = ⟦polyLoop⟧
    exact congrArg (fun p : _root_.Path x x => (⟦p⟧ : _root_.Path.Homotopic.Quotient x x))
      (Path.ext rfl)
  rw [hLq, hRq] at htelcast
  exact htelcast.symm

end UniversalCover
end Topology
end Riemannian
end Geometry
end DifferentialGeometry

end
