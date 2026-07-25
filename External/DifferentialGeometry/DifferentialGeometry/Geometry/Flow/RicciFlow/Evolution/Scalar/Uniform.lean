import DifferentialGeometry.Geometry.Flow.RicciFlow.Basic.Core

set_option autoImplicit false










noncomputable section

open Filter Set
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [CompactSpace M]
variable [SigmaCompactSpace M] [T2Space M]

omit [CompactSpace M] [SigmaCompactSpace M] [T2Space M] in



private theorem time_patch
    (f : Real → M → Real) (K : Set Real)
    (hf : ContinuousOn (fun p : Real × M => f p.1 p.2)
      (K ×ˢ (Set.univ : Set M)))
    (t0 : Real) (hK : K ∈ 𝓝 t0) (x : M)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ V : Set Real, V ∈ 𝓝 t0 ∧
      ∃ W : Set M, IsOpen W ∧ x ∈ W ∧
        ∀ t ∈ V, ∀ y ∈ W,
          |f t y - f t0 y| < epsilon := by
  classical
  let F : Real × M → Real := fun p => f p.1 p.2
  have hdom : K ×ˢ (Set.univ : Set M) ∈ 𝓝 (t0, x) :=
    prod_mem_nhds hK Filter.univ_mem
  have hmove : ContinuousAt F (t0, x) := by
    have ht0K : t0 ∈ K := mem_of_mem_nhds hK
    exact (hf (t0, x) ⟨ht0K, Set.mem_univ x⟩).continuousAt hdom
  have hfix :
      ContinuousAt (fun p : Real × M => f t0 p.2) (t0, x) := by
    have hmap :
        ContinuousAt (fun p : Real × M => (t0, p.2)) (t0, x) :=
      continuousAt_const.prodMk continuousAt_snd
    exact ContinuousAt.comp'
      (f := fun p : Real × M => (t0, p.2))
      (g := fun p : Real × M => f p.1 p.2) hmove hmap
  have hdiff :
      ContinuousAt
        (fun p : Real × M =>
          f p.1 p.2 - f t0 p.2) (t0, x) := by
    simpa only [F] using hmove.sub hfix
  have hsmall :
      {p : Real × M |
        |f p.1 p.2 - f t0 p.2| < epsilon} ∈ 𝓝 (t0, x) := by
    exact hdiff.abs.eventually_lt_const (by simpa only [sub_self, abs_zero] using hepsilon)
  obtain ⟨V, W, hVOpen, hTV, hWOpen, hxW, hVW⟩ :=
    mem_nhds_prod_iff'.mp hsmall
  refine ⟨V, hVOpen.mem_nhds hTV, W, hWOpen, hxW, ?_⟩
  intro t ht y hy
  have hty : (t, y) ∈ V ×ˢ W := ⟨ht, hy⟩
  exact hVW hty



omit [SigmaCompactSpace M] in
theorem scalar_unif
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : D.RegularTime)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∀ᶠ t in 𝓝 (T : Real), ∀ x : M,
      |S.scalar t x - S.scalar (T : Real) x| < epsilon := by
  classical
  have hcarrier : D.carrier ∈ 𝓝 (T : Real) :=
    mem_of_superset (D.regular_isOpen.mem_nhds T.2) D.regular_subset
  choose V hV W hWOpen hxW hloc using
    fun x : M => time_patch S.scalar D.carrier hS.scalarCont
      (T : Real) hcarrier x hepsilon
  obtain ⟨F, _, hF⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set M)).elim_nhds_subcover W
      (fun x _ => (hWOpen x).mem_nhds (hxW x))
  have htime :
      ∀ᶠ t in 𝓝 (T : Real), ∀ x ∈ F, t ∈ V x := by
    exact
      (Finset.eventually_all
        (I := F)
        (l := 𝓝 (T : Real))
        (p := fun x t => t ∈ V x)).2
        (fun x _ => hV x)
  filter_upwards [htime] with t ht
  intro y
  obtain ⟨x, hxF, hyW⟩ :=
    Set.mem_iUnion₂.mp (hF (Set.mem_univ y))
  exact hloc x t (ht x hxF) y hyW

end DifferentialGeometry.PDE.RicciFlow

end
