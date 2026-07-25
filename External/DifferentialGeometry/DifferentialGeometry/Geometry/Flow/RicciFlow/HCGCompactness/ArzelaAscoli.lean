import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Metrizable.ContinuousMap
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.Topology.UniformSpace.CompleteSeparated
import Mathlib.Topology.UniformSpace.Real

set_option autoImplicit false

















namespace DifferentialGeometry
namespace HCGCompactness

open Filter Set Topology
open scoped Topology

variable {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X]
  [SigmaCompactSpace X] [T2Space X]





omit [T2Space X] in
theorem arzelaAscoli_subseq_tendsto
    (f : Nat -> C(X, Real))
    (hequi : Equicontinuous (fun k => (f k : X -> Real)))
    (hbdd : forall x : X, BddAbove (Set.range fun k => |f k x|)) :
    exists (phi : Nat -> Nat) (g : C(X, Real)),
      StrictMono phi ∧ Tendsto (fun n => f (phi n)) atTop (𝓝 g) := by
  classical
  haveI : WeaklyLocallyCompactSpace X := inferInstance
  haveI : CompactlyCoherentSpace X := inferInstance
  have hclosedEmbedding :
      IsClosedEmbedding
        (UniformOnFun.ofFun {K : Set X | IsCompact K} ∘
          (fun g : C(X, Real) => (g : X -> Real))) := by
    refine ⟨?_, ?_⟩
    · simpa [ContinuousMap.toUniformOnFunIsCompact, Function.comp_def] using
        (ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact
          (α := X) (β := Real)).isEmbedding
    · rw [show
          Set.range
              (UniformOnFun.ofFun {K : Set X | IsCompact K} ∘
                (fun g : C(X, Real) => (g : X -> Real))) =
            {g : UniformOnFun X Real {K : Set X | IsCompact K} |
              Continuous (UniformOnFun.toFun {K : Set X | IsCompact K} g)} by
          simpa [ContinuousMap.toUniformOnFunIsCompact, Function.comp_def] using
            (ContinuousMap.range_toUniformOnFunIsCompact (α := X) (β := Real))]
      exact UniformOnFun.isClosed_setOf_continuous
        (β := Real) (𝔖 := {K : Set X | IsCompact K})
        CompactlyCoherentSpace.isCoherentWith
  have hEq :
      forall K : Set X, K ∈ ({K : Set X | IsCompact K}) ->
        EquicontinuousOn
          ((fun g : C(X, Real) => (g : X -> Real)) ∘
            ((↑) : {g : C(X, Real) // g ∈ Set.range f} -> C(X, Real))) K := by
    intro K _hK
    let idx : {g : C(X, Real) // g ∈ Set.range f} -> Nat :=
      fun g => Classical.choose g.2
    have hidx :
        forall g : {g : C(X, Real) // g ∈ Set.range f}, f (idx g) = g.1 :=
      fun g => Classical.choose_spec g.2
    have hglobal :
        Equicontinuous (fun g : {g : C(X, Real) // g ∈ Set.range f} =>
          (g.1 : X -> Real)) := by
      have hsub := hequi.comp idx
      have hfun :
          ((fun k : Nat => (f k : X -> Real)) ∘ idx) =
            (fun g : {g : C(X, Real) // g ∈ Set.range f} => (g.1 : X -> Real)) := by
        funext g x
        change f (idx g) x = g.1 x
        rw [hidx g]
      simpa [hfun] using hsub
    simpa [Function.comp_def] using hglobal.equicontinuousOn K
  have hPoint :
      forall K : Set X, K ∈ ({K : Set X | IsCompact K}) ->
        forall x : X, x ∈ K ->
        exists Q : Set Real, IsCompact Q ∧
          forall i : C(X, Real), i ∈ (Set.range f : Set C(X, Real)) ->
            ((fun g : C(X, Real) => (g : X -> Real)) i) x ∈ Q := by
    intro _K _hK x _hx
    rcases hbdd x with ⟨M, hM⟩
    refine ⟨Set.Icc (-M) M, isCompact_Icc, ?_⟩
    intro i hi
    rcases hi with ⟨k, rfl⟩
    have hAbs : |f k x| <= M := hM ⟨k, rfl⟩
    constructor
    · exact le_trans (neg_le_neg hAbs) (neg_abs_le (f k x))
    · exact le_trans (le_abs_self (f k x)) hAbs
  have hcompact : IsCompact (closure (Set.range f : Set C(X, Real))) := by
    exact
      ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
        (X := X) (α := Real) (ι := C(X, Real))
        (𝔖 := {K : Set X | IsCompact K})
        (F := fun g : C(X, Real) => (g : X -> Real))
        (fun K hK => hK) hclosedEmbedding
        (s := Set.range f) hEq hPoint
  have hmem : forall n : Nat, f n ∈ closure (Set.range f : Set C(X, Real)) :=
    fun n => subset_closure ⟨n, rfl⟩
  rcases hcompact.tendsto_subseq hmem with ⟨g, _hg, phi, hphi, htendsto⟩
  exact ⟨phi, g, hphi, by simpa [Function.comp_def] using htendsto⟩



omit [T2Space X] in
theorem arzelaAscoli_subseq_tendstoUniformlyOnCompacts
    (f : Nat -> C(X, Real))
    (hequi : Equicontinuous (fun k => (f k : X -> Real)))
    (hbdd : forall x : X, BddAbove (Set.range fun k => |f k x|)) :
    exists (phi : Nat -> Nat) (g : C(X, Real)),
      StrictMono phi ∧
        forall K : Set X, IsCompact K ->
          TendstoUniformlyOn (fun n => f (phi n)) g atTop K := by
  rcases arzelaAscoli_subseq_tendsto (X := X) f hequi hbdd with
    ⟨phi, g, hphi, htendsto⟩
  exact
    ⟨phi, g, hphi,
      (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp htendsto)⟩

section VectorTarget

variable {V : Type*} [NormedAddCommGroup V] [ProperSpace V]

omit [SigmaCompactSpace X] [T2Space X] in









theorem arzelaAscoli_isCompact_closure
    (f : Nat -> C(X, V))
    (hequi : Equicontinuous (fun k => (f k : X -> V)))
    (hbdd : forall x : X, exists M : Real, forall k : Nat, ‖f k x‖ <= M) :
    IsCompact (closure (Set.range f : Set C(X, V))) := by
  classical
  haveI : WeaklyLocallyCompactSpace X := inferInstance
  haveI : CompactlyCoherentSpace X := inferInstance
  have hclosedEmbedding :
      IsClosedEmbedding
        (UniformOnFun.ofFun {K : Set X | IsCompact K} ∘
          (fun g : C(X, V) => (g : X -> V))) := by
    refine ⟨?_, ?_⟩
    · simpa [ContinuousMap.toUniformOnFunIsCompact, Function.comp_def] using
        (ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact
          (α := X) (β := V)).isEmbedding
    · rw [show
          Set.range
              (UniformOnFun.ofFun {K : Set X | IsCompact K} ∘
                (fun g : C(X, V) => (g : X -> V))) =
            {g : UniformOnFun X V {K : Set X | IsCompact K} |
              Continuous (UniformOnFun.toFun {K : Set X | IsCompact K} g)} by
          simpa [ContinuousMap.toUniformOnFunIsCompact, Function.comp_def] using
            (ContinuousMap.range_toUniformOnFunIsCompact (α := X) (β := V))]
      exact UniformOnFun.isClosed_setOf_continuous
        (β := V) (𝔖 := {K : Set X | IsCompact K})
        CompactlyCoherentSpace.isCoherentWith
  have hEq :
      forall K : Set X, K ∈ ({K : Set X | IsCompact K}) ->
        EquicontinuousOn
          ((fun g : C(X, V) => (g : X -> V)) ∘
            ((↑) : {g : C(X, V) // g ∈ Set.range f} -> C(X, V))) K := by
    intro K _hK
    let idx : {g : C(X, V) // g ∈ Set.range f} -> Nat :=
      fun g => Classical.choose g.2
    have hidx :
        forall g : {g : C(X, V) // g ∈ Set.range f}, f (idx g) = g.1 :=
      fun g => Classical.choose_spec g.2
    have hglobal :
        Equicontinuous (fun g : {g : C(X, V) // g ∈ Set.range f} =>
          (g.1 : X -> V)) := by
      have hsub := hequi.comp idx
      have hfun :
          ((fun k : Nat => (f k : X -> V)) ∘ idx) =
            (fun g : {g : C(X, V) // g ∈ Set.range f} => (g.1 : X -> V)) := by
        funext g x
        change f (idx g) x = g.1 x
        rw [hidx g]
      simpa [hfun] using hsub
    simpa [Function.comp_def] using hglobal.equicontinuousOn K
  have hPoint :
      forall K : Set X, K ∈ ({K : Set X | IsCompact K}) ->
        forall x : X, x ∈ K ->
        exists Q : Set V, IsCompact Q ∧
          forall i : C(X, V), i ∈ (Set.range f : Set C(X, V)) ->
            ((fun g : C(X, V) => (g : X -> V)) i) x ∈ Q := by
    intro _K _hK x _hx
    rcases hbdd x with ⟨M, hM⟩
    refine ⟨Metric.closedBall 0 M, isCompact_closedBall 0 M, ?_⟩
    intro i hi
    rcases hi with ⟨k, rfl⟩
    exact mem_closedBall_zero_iff.mpr (hM k)
  exact
    ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
      (X := X) (α := V) (ι := C(X, V))
      (𝔖 := {K : Set X | IsCompact K})
      (F := fun g : C(X, V) => (g : X -> V))
      (fun K hK => hK) hclosedEmbedding
      (s := Set.range f) hEq hPoint

omit [T2Space X] in



theorem arzelaAscoli_subseq_vec
    (f : Nat -> C(X, V))
    (hequi : Equicontinuous (fun k => (f k : X -> V)))
    (hbdd : forall x : X, exists M : Real, forall k : Nat, ‖f k x‖ <= M) :
    exists (phi : Nat -> Nat) (g : C(X, V)),
      StrictMono phi ∧
        forall K : Set X, IsCompact K ->
          TendstoUniformlyOn (fun n => f (phi n)) g atTop K := by
  have hmem : forall n : Nat, f n ∈ closure (Set.range f : Set C(X, V)) :=
    fun n => subset_closure ⟨n, rfl⟩
  rcases (arzelaAscoli_isCompact_closure f hequi hbdd).tendsto_subseq hmem with
    ⟨g, _hg, phi, hphi, htendsto⟩
  exact
    ⟨phi, g, hphi,
      ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp
        (by simpa [Function.comp_def] using htendsto)⟩

end VectorTarget

end HCGCompactness
end DifferentialGeometry
