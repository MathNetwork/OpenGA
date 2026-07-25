import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricCompactness

set_option autoImplicit false
set_option linter.style.longLine false





















noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff

variable {E : Type uE} [NormedAddCommGroup E]
variable [InnerProductSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]



theorem ExhaustsByOpen.comp_subseq {M : Type*} [TopologicalSpace M]
    {U : Nat -> Set M} (hU : ExhaustsByOpen U)
    {φ : Nat -> Nat} (hφ : StrictMono φ) :
    ExhaustsByOpen (fun k => U (φ k)) := by
  refine ⟨fun k => hU.isOpen (φ k),
    fun k => hU.subset_of_le (hφ.monotone (Nat.le_succ k)), ?_⟩
  intro K hK
  obtain ⟨k0, hk0⟩ := hU.subset K hK
  exact ⟨k0, fun k hk => hk0 (φ k) (le_trans hk (hφ.id_le k))⟩

namespace PointedRiemannianCGMaps



def compSubseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianCGMaps (I := I) X L subseq)
    (φ : Nat -> Nat) (hφ : StrictMono φ) :
    PointedRiemannianCGMaps (I := I) X L (subseq ∘ φ) where
  partialDiffeomorph k := Φ.partialDiffeomorph (φ k)
  source_exhausts := by
    letI : TopologicalSpace L.M := L.topology
    letI : ChartedSpace H L.M := L.charted
    exact Φ.source_exhausts.comp_subseq hφ
  base_mem k := Φ.base_mem (φ k)
  basepoint_map k := Φ.basepoint_map (φ k)



def ofSubseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (f : Nat -> Nat)
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    (Φ : PointedRiemannianCGMaps (I := I) (X.subseq f) L id) :
    PointedRiemannianCGMaps (I := I) X L f where
  partialDiffeomorph := Φ.partialDiffeomorph
  source_exhausts := Φ.source_exhausts
  base_mem := Φ.base_mem
  basepoint_map := Φ.basepoint_map



omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
@[simp] theorem compSubseq_source
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianCGMaps (I := I) X L subseq)
    (φ : Nat -> Nat) (hφ : StrictMono φ) (k : Nat) :
    (Φ.compSubseq φ hφ).source k = Φ.source (φ k) := rfl

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
@[simp] theorem ofSubseq_source
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (f : Nat -> Nat)
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    (Φ : PointedRiemannianCGMaps (I := I) (X.subseq f) L id)
    (k : Nat) :
    (Φ.ofSubseq f).source k = Φ.source k := rfl

end PointedRiemannianCGMaps

namespace MetricSourceData







def compSubseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    {Φ : PointedRiemannianCGMaps (I := I) X L subseq}
    (φ : Nat -> Nat) (hφ : StrictMono φ) (k : Nat)
    (D : MetricSourceData (I := I) Φ (φ k)) :
    MetricSourceData (I := I) (Φ.compSubseq φ hφ) k where
  topology := D.topology
  charted := D.charted
  t2 := D.t2
  smooth := D.smooth
  sigmaCompact := D.sigmaCompact
  limitMetric := D.limitMetric
  pullbackMetric := D.pullbackMetric
  referenceMetric := D.referenceMetric
  compact_preimage := D.compact_preimage
  limit_inner := D.limit_inner
  pullback_inner := D.pullback_inner



def ofSubseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (f : Nat -> Nat)
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {Φ : PointedRiemannianCGMaps (I := I) (X.subseq f) L id}
    (k : Nat) (D : MetricSourceData (I := I) Φ k) :
    MetricSourceData (I := I) (Φ.ofSubseq f) k where
  topology := D.topology
  charted := D.charted
  t2 := D.t2
  smooth := D.smooth
  sigmaCompact := D.sigmaCompact
  limitMetric := D.limitMetric
  pullbackMetric := D.pullbackMetric
  referenceMetric := D.referenceMetric
  compact_preimage := D.compact_preimage
  limit_inner := D.limit_inner
  pullback_inner := D.pullback_inner



omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
@[simp] theorem compSubseq_supOn
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    {Φ : PointedRiemannianCGMaps (I := I) X L subseq}
    (φ : Nat -> Nat) (hφ : StrictMono φ) (k : Nat)
    (D : MetricSourceData (I := I) Φ (φ k)) (K : Set L.M) (p : Nat) :
    (MetricSourceData.compSubseq (I := I) φ hφ k D).derivNormSupOn (I := I) K p =
      D.derivNormSupOn (I := I) K p := rfl

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
@[simp] theorem ofSubseq_supOn
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (f : Nat -> Nat)
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {Φ : PointedRiemannianCGMaps (I := I) (X.subseq f) L id}
    (k : Nat) (D : MetricSourceData (I := I) Φ k)
    (K : Set L.M) (p : Nat) :
    (MetricSourceData.ofSubseq (I := I) f k D).derivNormSupOn (I := I) K p =
      D.derivNormSupOn (I := I) K p := rfl

end MetricSourceData

namespace MetricCGConvergenceData





def compSubseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    {Φ : PointedRiemannianCGMaps (I := I) X L subseq}
    (Cd : MetricCGConvergenceData (I := I) Φ)
    (φ : Nat -> Nat) (hφ : StrictMono φ) :
    MetricCGConvergenceData (I := I) (Φ.compSubseq φ hφ) where
  domain k := MetricSourceData.compSubseq (I := I) φ hφ k (Cd.domain (φ k))
  converges := by
    intro K hK p ε hε
    obtain ⟨k0, hk0⟩ := Cd.converges K hK p ε hε
    exact ⟨k0, fun k hk => hk0 (φ k) (le_trans hk (hφ.id_le k))⟩



def ofSubseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (f : Nat -> Nat)
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {Φ : PointedRiemannianCGMaps (I := I) (X.subseq f) L id}
    (Cd : MetricCGConvergenceData (I := I) Φ) :
    MetricCGConvergenceData (I := I) (Φ.ofSubseq f) where
  domain k := MetricSourceData.ofSubseq (I := I) f k (Cd.domain k)
  converges := by
    intro K hK p ε hε
    simpa only [PointedRiemannianCGMaps.ofSubseq_source,
      MetricSourceData.ofSubseq_supOn] using Cd.converges K hK p ε hε

end MetricCGConvergenceData

namespace PointedRiemannianCGConverges



def compSubseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    {Φ : PointedRiemannianCGMaps (I := I) X L subseq}
    (C : PointedRiemannianCGConverges (I := I) X L subseq Φ)
    (φ : Nat -> Nat) (hφ : StrictMono φ) :
    PointedRiemannianCGConverges (I := I) X L (subseq ∘ φ) (Φ.compSubseq φ hφ) where
  metrics := C.metrics.compSubseq φ hφ



def ofSubseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (f : Nat -> Nat)
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {Φ : PointedRiemannianCGMaps (I := I) (X.subseq f) L id}
    (C : PointedRiemannianCGConverges (I := I) (X.subseq f) L id Φ) :
    PointedRiemannianCGConverges (I := I) X L f (Φ.ofSubseq f) where
  metrics := C.metrics.ofSubseq f

end PointedRiemannianCGConverges

namespace MetricCompactnessConclusion






def compSubseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (mc : MetricCompactnessConclusion (I := I) X)
    (φ : Nat -> Nat) (hφ : StrictMono φ) :
    MetricCompactnessConclusion (I := I) X where
  subseq := mc.subseq ∘ φ
  strictMono := mc.strictMono.comp hφ
  limit := mc.limit
  limit_complete := mc.limit_complete
  maps := mc.maps.compSubseq φ hφ
  convergence := mc.convergence.compSubseq φ hφ


omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
@[simp] theorem compSubseq_subseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (mc : MetricCompactnessConclusion (I := I) X)
    (φ : Nat -> Nat) (hφ : StrictMono φ) :
    (mc.compSubseq φ hφ).subseq = mc.subseq ∘ φ := rfl


omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
@[simp] theorem compSubseq_limit
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (mc : MetricCompactnessConclusion (I := I) X)
    (φ : Nat -> Nat) (hφ : StrictMono φ) :
    (mc.compSubseq φ hφ).limit = mc.limit := rfl

end MetricCompactnessConclusion

end HCGCompactness
end DifferentialGeometry
