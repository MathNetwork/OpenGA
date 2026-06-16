import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Sets.OpenCover
import OpenGALib.Manifold.Charts.CoordinateBall

/-!
# Precompact coordinate balls and locally finite refinements

Covering infrastructure beneath partitions of unity and exhaustions. A
*precompact coordinate ball* is the source of a coordinate-ball chart with
compact closure; on a topological `n`-manifold (Hausdorff, second-countable,
charted over `EuclideanSpace ℝ (Fin n)`) these form a countable basis, and
together with paracompactness every open cover admits a countable, locally
finite refinement by precompact coordinate balls subordinate to it.

The development is layered: the basis results need only the ambient topology
and a chart; the refinement adds paracompactness, factored through an abstract
basis-refinement lemma (`exists_countable_locallyFinite_refinement_of_isTopologicalBasis`)
reusable for any topological basis.

## Main definitions

* `Manifold.IsPrecompactCoordinateBall` — source of a coordinate-ball chart with compact closure.

## Main results

* `Manifold.IsPrecompactCoordinateBall.isOpen` — a precompact coordinate ball is open.
* `Manifold.isTopologicalBasis_isPrecompactCoordinateBall` — precompact coordinate balls form a basis.
* `Manifold.exists_countable_precompact_coordinate_ball_basis` — that basis can be taken countable.
* `Manifold.paracompactSpace_of_manifold` — a topological manifold is paracompact.
* `Manifold.exists_countable_locally_finite_precompact_coordinate_ball_refinement` —
  every open cover has a countable locally finite refinement by precompact coordinate balls.

Provenance: SmoothManifoldsLee a5f308c — Lemma_1_10, Theorem_1_15.
-/

open Set TopologicalSpace
open scoped Topology

universe u v

namespace Manifold

section Basis

variable {n : ℕ} {M : Type u} [TopologicalSpace M]

/-- **Math.** A set `s ⊆ M` is a *precompact coordinate ball*: it is the source of
some coordinate-ball chart and its closure is compact. -/
def IsPrecompactCoordinateBall (n : ℕ) (s : Set M) : Prop :=
  (∃ e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)),
    e.source = s ∧ e.IsCoordinateBall) ∧
      IsCompact (closure s)

/-- **Math.** A precompact coordinate ball is open. -/
theorem IsPrecompactCoordinateBall.isOpen {s : Set M}
    (hs : IsPrecompactCoordinateBall n s) : IsOpen s := by
  rcases hs.1 with ⟨e, rfl, -⟩
  simpa using e.open_source

/-- **Math.** A precompact coordinate ball has compact closure. -/
theorem IsPrecompactCoordinateBall.isCompact_closure {s : Set M}
    (hs : IsPrecompactCoordinateBall n s) : IsCompact (closure s) :=
  hs.2

variable [T2Space M] [SecondCountableTopology M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

omit [SecondCountableTopology M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] in
/-- **Math.** Restricting a chart to a Euclidean open ball whose closed ball is
compactly contained in the chart target produces a precompact coordinate ball in
`M`. -/
theorem isPrecompactCoordinateBall_chart_preimage_metric_ball
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) {c : EuclideanSpace ℝ (Fin n)}
    {r : ℝ} (hr : 0 < r) (hclosed : Metric.closedBall c r ⊆ e.target) :
    IsPrecompactCoordinateBall n (e.symm '' Metric.ball c r) := by
  let e' := e.trans (OpenPartialHomeomorph.ofSet (Metric.ball c r) Metric.isOpen_ball)
  have hball_target : Metric.ball c r ⊆ e.target := by
    exact (Metric.ball_subset_closedBall : Metric.ball c r ⊆ Metric.closedBall c r).trans hclosed
  have hsource : e'.source = e.symm '' Metric.ball c r := by
    -- The restricted chart is defined exactly on the inverse image of the chosen ball.
    dsimp [e']
    exact (e.symm_image_eq_source_inter_preimage hball_target).symm
  have htarget : e'.target = Metric.ball c r := by
    -- On the target side, the restriction keeps precisely the chosen Euclidean ball.
    dsimp [e']
    exact inter_eq_left.2 hball_target
  have hcompactCarrier : IsCompact (e.symm '' Metric.closedBall c r) := by
    -- The closed ball is compact in Euclidean space, and the inverse chart is continuous on it.
    exact (isCompact_closedBall (x := c) (r := r)).image_of_continuousOn
      (e.continuousOn_symm.mono hclosed)
  have hclosureCompact : IsCompact (closure (e.symm '' Metric.ball c r)) := by
    -- The closure stays inside the compact pullback of the closed Euclidean ball.
    exact hcompactCarrier.closure_of_subset
      (Set.image_mono (Metric.ball_subset_closedBall : Metric.ball c r ⊆ Metric.closedBall c r))
  refine ⟨?_, hclosureCompact⟩
  refine ⟨e', hsource, ?_⟩
  exact OpenPartialHomeomorph.isCoordinateBall_of_target_eq_ball e' c r hr htarget

omit [SecondCountableTopology M] in
/-- **Math.** Every point of an open set lies in a precompact coordinate ball
contained in that open set. -/
theorem exists_isPrecompactCoordinateBall_subset_of_mem_open {x : M}
    {u : Set M} (hx : x ∈ u) (hu : IsOpen u) :
    ∃ s : Set M, IsPrecompactCoordinateBall n s ∧ x ∈ s ∧ s ⊆ u := by
  let e := chartAt (EuclideanSpace ℝ (Fin n)) x
  let y : EuclideanSpace ℝ (Fin n) := e x
  let w : Set (EuclideanSpace ℝ (Fin n)) := e '' (e.source ∩ u)
  have hxsource : x ∈ e.source := mem_chart_source _ x
  have hyw : y ∈ w := by
    refine ⟨x, ⟨hxsource, hx⟩, rfl⟩
  have hw_open : IsOpen w := by
    -- The image of the open neighborhood inside the chart source is open in Euclidean space.
    simpa [w] using e.isOpen_image_source_inter hu
  obtain ⟨r, hr, hclosed⟩ :
      ∃ r : ℝ, 0 < r ∧ Metric.closedBall y r ⊆ w := by
    -- Choose a small closed Euclidean ball around the charted point inside that open image.
    exact Metric.nhds_basis_closedBall.mem_iff.1 (hw_open.mem_nhds hyw)
  have hw_target : w ⊆ e.target := by
    -- The chart image of any subset of the source stays in the chart target.
    simpa [w] using (Set.image_mono (show e.source ∩ u ⊆ e.source from inter_subset_left)).trans
      e.image_source_eq_target.subset
  let s : Set M := e.symm '' Metric.ball y r
  have hs_precompact : IsPrecompactCoordinateBall n s := by
    -- Pull back the chosen Euclidean ball through the chart.
    simpa [s, y] using isPrecompactCoordinateBall_chart_preimage_metric_ball
      (n := n) e hr (hclosed.trans hw_target)
  have hxs : x ∈ s := by
    -- The charted point lies in every positive-radius ball centered at itself.
    refine ⟨y, Metric.mem_ball_self hr, ?_⟩
    simpa [y] using e.left_inv hxsource
  have hs_subset_source_u : s ⊆ e.source ∩ u := by
    -- The pulled-back ball lies inside the original open neighborhood because its image does.
    have hball_w : Metric.ball y r ⊆ w := by
      exact (Metric.ball_subset_closedBall : Metric.ball y r ⊆ Metric.closedBall y r).trans hclosed
    change e.symm '' Metric.ball y r ⊆ e.source ∩ u
    refine (Set.image_mono hball_w).trans ?_
    have himage : e.symm '' w = e.source ∩ u := by
      simpa [w] using e.symm_image_image_of_subset_source
        (s := e.source ∩ u) (show e.source ∩ u ⊆ e.source from inter_subset_left)
    exact himage.subset
  exact ⟨s, hs_precompact, hxs, fun z hz ↦ (hs_subset_source_u hz).2⟩

omit [SecondCountableTopology M] in
/-- **Math.** Precompact coordinate balls form a topological basis on a topological
manifold. -/
theorem isTopologicalBasis_isPrecompactCoordinateBall :
    IsTopologicalBasis { s : Set M | IsPrecompactCoordinateBall n s } := by
  -- The local chart construction gives a basis element inside every open neighborhood.
  refine isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · intro s hs
    exact hs.isOpen
  · intro x u hx hu
    obtain ⟨s, hs, hxs, hsu⟩ := exists_isPrecompactCoordinateBall_subset_of_mem_open
      (n := n) hx hu
    exact ⟨s, hs, hxs, hsu⟩

/-- **Math.** Lemma 1.10: every topological manifold has a *countable* topological
basis consisting of precompact coordinate balls. -/
theorem exists_countable_precompact_coordinate_ball_basis :
    ∃ b : Set (Set M),
      b.Countable ∧ IsTopologicalBasis b ∧ ∀ s ∈ b, IsPrecompactCoordinateBall n s := by
  let B : Set (Set M) := { s : Set M | IsPrecompactCoordinateBall n s }
  have hB : IsTopologicalBasis B := isTopologicalBasis_isPrecompactCoordinateBall (n := n)
  -- Once the local basis is available, second countability lets us thin it to a countable subbasis.
  obtain ⟨b, hbB, hbCountable, hbBasis⟩ := hB.exists_countable
  exact ⟨b, hbCountable, hbBasis, fun s hs ↦ hbB hs⟩

end Basis

section Refinement

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

include n in
/-- **Math.** A topological manifold is paracompact. -/
theorem paracompactSpace_of_manifold : ParacompactSpace M := by
  letI : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  letI : SigmaCompactSpace M := sigmaCompactSpace_of_locallyCompact_secondCountable
  infer_instance

/-- **Math.** Companion bridge: given an open cover of a locally compact,
sigma-compact, Hausdorff space and any basis for its topology, there is a countable
locally finite refinement by basis elements subordinate to the cover. -/
theorem exists_countable_locallyFinite_refinement_of_isTopologicalBasis {X : Type u}
    [TopologicalSpace X] [LocallyCompactSpace X] [SigmaCompactSpace X] [T2Space X]
    {ι : Type v} {U : ι → Opens X}
    (hU : IsOpenCover U) {B : Set (Set X)} (hB : IsTopologicalBasis B) :
    ∃ (κ : Type u), Countable κ ∧ ∃ V : κ → Opens X,
      IsOpenCover V ∧ LocallyFinite (fun j ↦ (V j : Set X)) ∧
        (∀ j, (V j : Set X) ∈ B) ∧
          (∀ j, ∃ i, (V j : Set X) ⊆ U i) := by
  -- Choose, at each point, one member of the original cover that contains that point.
  choose i hi using fun x : X ↦ hU.exists_mem_nhds x
  have hBU :
      ∀ x : X,
        (𝓝 x).HasBasis
          (fun s : Set X ↦ s ∈ B ∧ x ∈ s ∧ s ⊆ U (i x))
          id := by
    intro x
    let hxB : (𝓝 x).HasBasis (fun s : Set X ↦ s ∈ B ∧ x ∈ s) id := hB.nhds_hasBasis
    simpa [and_assoc] using hxB.restrict_subset (hi x)
  -- Feed the subordinate neighborhood bases into the standard locally finite refinement theorem.
  rcases refinement_of_locallyCompact_sigmaCompact_of_nhds_basis hBU with
    ⟨κ, c, W, hW_basis, hW_cover, hW_locallyFinite⟩
  have hκ : Countable κ := by
    simpa [Set.countable_univ_iff] using
      hW_locallyFinite.countable_univ fun j ↦ ⟨c j, (hW_basis j).2.1⟩
  refine ⟨κ, hκ, ?_⟩
  refine ⟨fun j ↦ ⟨W j, hB.isOpen (hW_basis j).1⟩, ?_, hW_locallyFinite, ?_, ?_⟩
  · exact IsOpenCover.of_sets (fun j ↦ hB.isOpen (hW_basis j).1) hW_cover
  · exact fun j ↦ (hW_basis j).1
  · exact fun j ↦ ⟨i (c j), (hW_basis j).2.2⟩

/-- **Math.** Theorem 1.15: given an open cover of a topological manifold, there is a
countable locally finite refinement by precompact coordinate balls subordinate to
the cover. -/
theorem exists_countable_locally_finite_precompact_coordinate_ball_refinement
    {ι : Type v} {U : ι → Opens M} (hU : IsOpenCover U) :
    ∃ (κ : Type u), Countable κ ∧ ∃ V : κ → Opens M,
      IsOpenCover V ∧ LocallyFinite (fun j ↦ (V j : Set M)) ∧
        (∀ j, IsPrecompactCoordinateBall n (V j : Set M)) ∧
          (∀ j, ∃ i, (V j : Set M) ⊆ U i) := by
  -- Start from the countable basis of precompact coordinate balls supplied earlier.
  have hBasis :
      ∃ B : Set (Set M),
        B.Countable ∧ IsTopologicalBasis B ∧ ∀ s ∈ B, IsPrecompactCoordinateBall n s :=
    exists_countable_precompact_coordinate_ball_basis
  rcases hBasis with ⟨B, -, hB_basis, hB_precompact⟩
  -- Apply the abstract refinement theorem to this specific basis.
  have hRefinement :
      ∃ (κ : Type u), Countable κ ∧ ∃ V : κ → Opens M,
        IsOpenCover V ∧ LocallyFinite (fun j ↦ (V j : Set M)) ∧
          (∀ j, (V j : Set M) ∈ B) ∧
            (∀ j, ∃ i, (V j : Set M) ⊆ U i) :=
    by
      letI : LocallyCompactSpace M :=
        ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
      letI : SigmaCompactSpace M := sigmaCompactSpace_of_locallyCompact_secondCountable
      exact exists_countable_locallyFinite_refinement_of_isTopologicalBasis hU hB_basis
  rcases hRefinement with
    ⟨κ, hκ, V, hV_cover, hV_locallyFinite, hV_mem, hV_subordinate⟩
  refine ⟨κ, hκ, V, hV_cover, hV_locallyFinite, ?_, hV_subordinate⟩
  intro j
  exact hB_precompact _ (hV_mem j)

end Refinement

end Manifold
