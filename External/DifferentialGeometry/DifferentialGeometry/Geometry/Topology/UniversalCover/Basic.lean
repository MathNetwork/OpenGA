import Mathlib.Topology.Bases
import Mathlib.Topology.Connected.LocPathConnected
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Homotopy.Path
import DifferentialGeometry.Geometry.Topology.SemilocallySimplyConnected




















open Set Function Filter
open scoped Topology ContDiff

noncomputable section

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Topology
namespace UniversalCover

variable {X : Type*} [TopologicalSpace X] [Inhabited X]




def _root_.DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover
    (X : Type*) [TopologicalSpace X] [Inhabited X] : Type _ :=
  (x : X) × _root_.Path.Homotopic.Quotient (default : X) x



def proj :
    DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X → X :=
  Sigma.fst





def basicOpen
    (p : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X)
    (U : Set X) (_hU : IsOpen U) (_hp : p.1 ∈ U) :
    Set (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X) :=
  { q | ∃ η : _root_.Path p.1 q.1,
          (∀ t, η t ∈ U) ∧
            q.2 =
              (p.2.trans
                ((_root_.Path.Homotopic.Quotient.mk η :
                    _root_.Path.Homotopic.Quotient p.1 q.1))) }



instance topology :
    TopologicalSpace
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X) :=
  TopologicalSpace.generateFrom
    { S | ∃ (p : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X)
            (U : Set X) (hU : IsOpen U) (hp : p.1 ∈ U),
              S = basicOpen p U hU hp }






theorem basis_trans_shift
    {p q r : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X}
    {U U' : Set X} (hU : IsOpen U) (hp : p.1 ∈ U)
    (hU' : IsOpen U') (hq : q.1 ∈ U') (hsub : U' ⊆ U)
    (hqp : q ∈ basicOpen p U hU hp)
    (hrq : r ∈ basicOpen q U' hU' hq) :
    r ∈ basicOpen p U hU hp := by
  obtain ⟨η, hη, hq2⟩ := hqp
  obtain ⟨η', hη', hr2⟩ := hrq
  refine ⟨η.trans η', ?_, ?_⟩
  · intro t
    have hmem : (η.trans η') t ∈ Set.range η ∪ Set.range η' := by
      have hrng : Set.range (η.trans η') = Set.range η ∪ Set.range η' :=
        Path.trans_range η η'
      have htmem : (η.trans η') t ∈ Set.range (η.trans η') := Set.mem_range_self _
      rw [hrng] at htmem
      exact htmem
    rcases hmem with hin | hin
    · obtain ⟨s, hs⟩ := hin
      exact hs ▸ hη s
    · obtain ⟨s, hs⟩ := hin
      exact hsub (hs ▸ hη' s)
  · have hmk :
        (_root_.Path.Homotopic.Quotient.mk (η.trans η') :
            _root_.Path.Homotopic.Quotient p.1 r.1)
          = (_root_.Path.Homotopic.Quotient.mk η).trans
              (_root_.Path.Homotopic.Quotient.mk η') :=
      _root_.Path.Homotopic.Quotient.mk_trans η η'
    rw [hmk, hr2, hq2]
    exact (_root_.Path.Homotopic.Quotient.trans_assoc p.2
      (_root_.Path.Homotopic.Quotient.mk η)
      (_root_.Path.Homotopic.Quotient.mk η'))






theorem basis_intersection
    [LocPathConnectedSpace X]
    {p₁ p₂ r : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X}
    {U₁ U₂ : Set X} (hU₁ : IsOpen U₁) (hp₁ : p₁.1 ∈ U₁)
    (hU₂ : IsOpen U₂) (hp₂ : p₂.1 ∈ U₂)
    (hr : r ∈ basicOpen p₁ U₁ hU₁ hp₁ ∩ basicOpen p₂ U₂ hU₂ hp₂) :
    ∃ (V : Set X) (hV : IsOpen V) (hrV : r.1 ∈ V),
      V ⊆ U₁ ∩ U₂ ∧ IsPathConnected V ∧
        basicOpen r V hV hrV ⊆
          basicOpen p₁ U₁ hU₁ hp₁ ∩ basicOpen p₂ U₂ hU₂ hp₂ := by
  obtain ⟨⟨η₁, hη₁, hr2_1⟩, ⟨η₂, hη₂, hr2_2⟩⟩ := hr
  have hrU₁ : r.1 ∈ U₁ := by
    have h1 := hη₁ 1
    simpa using h1
  have hrU₂ : r.1 ∈ U₂ := by
    have h1 := hη₂ 1
    simpa using h1
  have hrU : r.1 ∈ U₁ ∩ U₂ := ⟨hrU₁, hrU₂⟩
  have hUcap_open : IsOpen (U₁ ∩ U₂) := hU₁.inter hU₂
  obtain ⟨V, ⟨hVopen, hrV, hVpc⟩, hVsub⟩ :=
    (isOpen_isPathConnected_basis r.1).mem_iff.mp (hUcap_open.mem_nhds hrU)
  refine ⟨V, hVopen, hrV, hVsub, hVpc, ?_⟩
  intro s hs
  obtain ⟨ζ, hζ, hs2⟩ := hs
  refine ⟨?_, ?_⟩
  · refine ⟨η₁.trans ζ, ?_, ?_⟩
    · intro t
      have hmem : (η₁.trans ζ) t ∈ Set.range η₁ ∪ Set.range ζ := by
        have hrng : Set.range (η₁.trans ζ) = Set.range η₁ ∪ Set.range ζ :=
          Path.trans_range η₁ ζ
        have htmem : (η₁.trans ζ) t ∈ Set.range (η₁.trans ζ) := Set.mem_range_self _
        rw [hrng] at htmem; exact htmem
      rcases hmem with ⟨u, hu⟩ | ⟨u, hu⟩
      · exact hu ▸ hη₁ u
      · exact (hVsub (hu ▸ hζ u)).1
    · have hmk :
          (_root_.Path.Homotopic.Quotient.mk (η₁.trans ζ) :
              _root_.Path.Homotopic.Quotient p₁.1 s.1)
            = (_root_.Path.Homotopic.Quotient.mk η₁).trans
                (_root_.Path.Homotopic.Quotient.mk ζ) :=
        _root_.Path.Homotopic.Quotient.mk_trans η₁ ζ
      rw [hmk, hs2, hr2_1]
      exact (_root_.Path.Homotopic.Quotient.trans_assoc p₁.2
        (_root_.Path.Homotopic.Quotient.mk η₁)
        (_root_.Path.Homotopic.Quotient.mk ζ))
  · refine ⟨η₂.trans ζ, ?_, ?_⟩
    · intro t
      have hmem : (η₂.trans ζ) t ∈ Set.range η₂ ∪ Set.range ζ := by
        have hrng : Set.range (η₂.trans ζ) = Set.range η₂ ∪ Set.range ζ :=
          Path.trans_range η₂ ζ
        have htmem : (η₂.trans ζ) t ∈ Set.range (η₂.trans ζ) := Set.mem_range_self _
        rw [hrng] at htmem; exact htmem
      rcases hmem with ⟨u, hu⟩ | ⟨u, hu⟩
      · exact hu ▸ hη₂ u
      · exact (hVsub (hu ▸ hζ u)).2
    · have hmk :
          (_root_.Path.Homotopic.Quotient.mk (η₂.trans ζ) :
              _root_.Path.Homotopic.Quotient p₂.1 s.1)
            = (_root_.Path.Homotopic.Quotient.mk η₂).trans
                (_root_.Path.Homotopic.Quotient.mk ζ) :=
        _root_.Path.Homotopic.Quotient.mk_trans η₂ ζ
      rw [hmk, hs2, hr2_2]
      exact (_root_.Path.Homotopic.Quotient.trans_assoc p₂.2
        (_root_.Path.Homotopic.Quotient.mk η₂)
        (_root_.Path.Homotopic.Quotient.mk ζ))




theorem basis_covers
    (q : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X) :
    ∃ (p : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X)
      (U : Set X) (hU : IsOpen U) (hp : p.1 ∈ U),
        q ∈ basicOpen p U hU hp := by
  refine ⟨q, Set.univ, isOpen_univ, Set.mem_univ _, ?_⟩
  refine ⟨_root_.Path.refl q.1, fun _ => Set.mem_univ _, ?_⟩
  have hmkrefl :
      (_root_.Path.Homotopic.Quotient.mk (_root_.Path.refl q.1) :
          _root_.Path.Homotopic.Quotient q.1 q.1)
        = _root_.Path.Homotopic.Quotient.refl q.1 :=
    _root_.Path.Homotopic.Quotient.mk_refl q.1
  rw [hmkrefl]
  exact (_root_.Path.Homotopic.Quotient.trans_refl q.2).symm





theorem basis_assemble
    [LocPathConnectedSpace X] :
    TopologicalSpace.IsTopologicalBasis
      { S : Set (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X) |
          ∃ (p : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X)
            (U : Set X) (hU : IsOpen U) (hp : p.1 ∈ U),
              S = basicOpen p U hU hp } := by
  refine
    { exists_subset_inter := ?_
      sUnion_eq := ?_
      eq_generateFrom := rfl }
  · rintro t₁ ⟨p₁, U₁, hU₁, hp₁, rfl⟩ t₂ ⟨p₂, U₂, hU₂, hp₂, rfl⟩ x hx
    obtain ⟨V, hVopen, hxV, _hVsub, _hVpc, hVin⟩ :=
      basis_intersection (p₁ := p₁) (p₂ := p₂) (r := x)
        hU₁ hp₁ hU₂ hp₂ hx
    refine ⟨basicOpen x V hVopen hxV, ⟨x, V, hVopen, hxV, rfl⟩, ?_, hVin⟩
    refine ⟨_root_.Path.refl x.1, fun _ => hxV, ?_⟩
    have hmkrefl :
        (_root_.Path.Homotopic.Quotient.mk (_root_.Path.refl x.1) :
            _root_.Path.Homotopic.Quotient x.1 x.1)
          = _root_.Path.Homotopic.Quotient.refl x.1 :=
      _root_.Path.Homotopic.Quotient.mk_refl x.1
    rw [hmkrefl]
    exact (_root_.Path.Homotopic.Quotient.trans_refl x.2).symm
  · apply Set.eq_univ_of_forall
    intro q
    obtain ⟨p, U, hU, hp, hmem⟩ := basis_covers q
    exact ⟨basicOpen p U hU hp, ⟨p, U, hU, hp, rfl⟩, hmem⟩




theorem proj_continuous [LocPathConnectedSpace X] :
    Continuous
      (proj :
        DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X → X) := by
  refine continuous_iff_continuousAt.mpr fun q => ?_
  rw [ContinuousAt, Filter.tendsto_def]
  intro U hU
  rw [mem_nhds_iff] at hU
  obtain ⟨W, hWU, hWopen, hqW⟩ := hU
  have hbasic_open : IsOpen (basicOpen q W hWopen hqW) :=
    TopologicalSpace.GenerateOpen.basic _ ⟨q, W, hWopen, hqW, rfl⟩
  have hqmem : q ∈ basicOpen q W hWopen hqW := by
    refine ⟨_root_.Path.refl q.1, fun _ => hqW, ?_⟩
    have hmkrefl :
        (_root_.Path.Homotopic.Quotient.mk (_root_.Path.refl q.1) :
            _root_.Path.Homotopic.Quotient q.1 q.1)
          = _root_.Path.Homotopic.Quotient.refl q.1 :=
      _root_.Path.Homotopic.Quotient.mk_refl q.1
    rw [hmkrefl]
    exact (_root_.Path.Homotopic.Quotient.trans_refl q.2).symm
  have hsub : basicOpen q W hWopen hqW ⊆ proj ⁻¹' U := by
    intro s hs
    obtain ⟨η, hη, _⟩ := hs
    have hη1 : η 1 ∈ W := hη 1
    have hs1 : s.1 ∈ W := by simpa using hη1
    exact hWU hs1
  exact Filter.mem_of_superset (hbasic_open.mem_nhds hqmem) hsub

end UniversalCover
end Topology
end Riemannian
end Geometry
end DifferentialGeometry

end
