import Mathlib.Topology.Connected.LocPathConnected
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
import Mathlib.Topology.OpenPartialHomeomorph.Constructions


open Set Function Filter Metric Bundle Manifold
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Topology

class SemilocallySimplyConnectedSpace (X : Type*) [TopologicalSpace X] :
    Prop where

  out : ∀ x : X, ∃ U ∈ nhds x, ∀ γ : _root_.Path x x,
          Set.range γ.toContinuousMap ⊆ U →
            (⟦γ⟧ : _root_.Path.Homotopic.Quotient x x) = ⟦_root_.Path.refl x⟧

theorem contractible_loops_nullhomotopic_in_subset
    {X : Type*} [TopologicalSpace X]
    {U : Set X} (_hUopen : IsOpen U) [ContractibleSpace U]
    {x : X} (_hxU : x ∈ U)
    (γ : _root_.Path x x)
    (hγU : Set.range γ.toContinuousMap ⊆ U) :
    (⟦γ⟧ : _root_.Path.Homotopic.Quotient x x) = ⟦_root_.Path.refl x⟧ := by
  have hSC : IsSimplyConnected U := (inferInstance : SimplyConnectedSpace U)
  have hmem : ∀ t, γ t ∈ U := by
    intro t
    have ht : γ t ∈ Set.range γ.toContinuousMap := by
      refine ⟨t, ?_⟩
      simp [Path.coe_toContinuousMap]
    exact hγU ht
  obtain ⟨F, _⟩ :=
    (isSimplyConnected_iff_exists_homotopy_refl_forall_mem.mp hSC).2 x γ hmem
  exact Quotient.sound ⟨F⟩

section ChartContractible

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

include I in

omit [InnerProductSpace ℝ E] [IsManifold I ∞ M] in
theorem manifold_exists_contractible_open_nhd (x : M) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ ContractibleSpace U := by
  set e : OpenPartialHomeomorph M E :=
    (chartAt H x).transHomeomorph I.toHomeomorph with he_def
  have he_source : e.source = (chartAt H x).source := rfl
  set c : E := e x with hc_def
  have hxsrc : x ∈ e.source := by
    rw [he_source]; exact mem_chart_source H x
  have hc_target : c ∈ e.target := e.map_source hxsrc
  have h_target_open : IsOpen e.target := e.open_target
  obtain ⟨r, hr_pos, hr_sub⟩ :=
    Metric.isOpen_iff.mp h_target_open c hc_target
  set B : Set E := Metric.ball c r with hB_def
  set U : Set M := e.source ∩ e ⁻¹' B with hU_def
  have hU_open : IsOpen U := e.isOpen_inter_preimage Metric.isOpen_ball
  have hxU : x ∈ U := by
    refine ⟨hxsrc, ?_⟩
    change e x ∈ B
    simp [hB_def, ← hc_def, Metric.mem_ball, dist_self, hr_pos]
  have heImage : e '' U = B := by
    ext b
    refine ⟨?_, ?_⟩
    · rintro ⟨m, ⟨_, hmB⟩, rfl⟩
      exact hmB
    · intro hb
      have hbT : b ∈ e.target := hr_sub hb
      refine ⟨e.symm b, ⟨e.map_target hbT, ?_⟩, e.right_inv hbT⟩
      change e (e.symm b) ∈ B
      rw [e.right_inv hbT]
      exact hb
  have hU_sub : U ⊆ e.source := Set.inter_subset_left
  let φ : U ≃ₜ B := e.homeomorphOfImageSubsetSource hU_sub heImage
  have hB_contr : ContractibleSpace B := Metric.contractibleSpace_ball hr_pos
  have hU_contr : ContractibleSpace U := φ.contractibleSpace
  exact ⟨U, hU_open, hxU, hU_contr⟩

include I in

omit [InnerProductSpace ℝ E] [IsManifold I ∞ M] in
theorem manifold_semilocallySimplyConnectedSpace :
    SemilocallySimplyConnectedSpace M := ⟨by
  intro x
  obtain ⟨U, hU_open, hxU, hU_contr⟩ := manifold_exists_contractible_open_nhd (I := I) x
  refine ⟨U, hU_open.mem_nhds hxU, fun γ hγU => ?_⟩
  exact contractible_loops_nullhomotopic_in_subset hU_open hxU γ hγU⟩

end ChartContractible

end Topology
end Riemannian
end Geometry
end DifferentialGeometry
