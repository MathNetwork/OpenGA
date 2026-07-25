import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.BoundedGeometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.PointedConvergence

set_option autoImplicit false
set_option linter.style.longLine false










noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff

variable {E : Type uE} [NormedAddCommGroup E]
variable [NormedSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]



structure PointedRiemannianCGMaps
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (L : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (subseq : Nat -> Nat) where
  partialDiffeomorph :
    forall k : Nat,
      letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : TopologicalSpace (X.obj (subseq k)).M :=
        (X.obj (subseq k)).topology
      letI : ChartedSpace H (X.obj (subseq k)).M :=
        (X.obj (subseq k)).charted
      PartialDiffeomorph I I L.M (X.obj (subseq k)).M (∞ : WithTop ℕ∞)
  source_exhausts :
    letI : TopologicalSpace L.M := L.topology
    letI : ChartedSpace H L.M := L.charted
    ExhaustsByOpen (fun k =>
      letI : TopologicalSpace (X.obj (subseq k)).M :=
        (X.obj (subseq k)).topology
      letI : ChartedSpace H (X.obj (subseq k)).M :=
        (X.obj (subseq k)).charted
      (partialDiffeomorph k).source)
  base_mem :
    forall k : Nat,
      letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : TopologicalSpace (X.obj (subseq k)).M :=
        (X.obj (subseq k)).topology
      letI : ChartedSpace H (X.obj (subseq k)).M :=
        (X.obj (subseq k)).charted
      L.basepoint ∈ (partialDiffeomorph k).source
  basepoint_map :
    forall k : Nat,
      letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : TopologicalSpace (X.obj (subseq k)).M :=
        (X.obj (subseq k)).topology
      letI : ChartedSpace H (X.obj (subseq k)).M :=
        (X.obj (subseq k)).charted
      partialDiffeomorph k L.basepoint = (X.obj (subseq k)).basepoint

namespace PointedRiemannianCGMaps

def source
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianCGMaps (I := I) X L subseq) (k : Nat) : Set L.M := by
  letI : TopologicalSpace L.M := L.topology
  letI : ChartedSpace H L.M := L.charted
  letI : TopologicalSpace (X.obj (subseq k)).M :=
    (X.obj (subseq k)).topology
  letI : ChartedSpace H (X.obj (subseq k)).M :=
    (X.obj (subseq k)).charted
  exact (Φ.partialDiffeomorph k).source

def target
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianCGMaps (I := I) X L subseq) (k : Nat) :
    Set ((X.obj (subseq k)).M) := by
  letI : TopologicalSpace L.M := L.topology
  letI : ChartedSpace H L.M := L.charted
  letI : TopologicalSpace (X.obj (subseq k)).M :=
    (X.obj (subseq k)).topology
  letI : ChartedSpace H (X.obj (subseq k)).M :=
    (X.obj (subseq k)).charted
  exact (Φ.partialDiffeomorph k).target

def map
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianCGMaps (I := I) X L subseq) (k : Nat) :
    L.M -> (X.obj (subseq k)).M := by
  letI : TopologicalSpace L.M := L.topology
  letI : ChartedSpace H L.M := L.charted
  letI : TopologicalSpace (X.obj (subseq k)).M :=
    (X.obj (subseq k)).topology
  letI : ChartedSpace H (X.obj (subseq k)).M :=
    (X.obj (subseq k)).charted
  exact fun x => (Φ.partialDiffeomorph k) x

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem source_open
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianCGMaps (I := I) X L subseq) (k : Nat) :
    letI : TopologicalSpace L.M := L.topology
    IsOpen (Φ.source k) := by
  letI : TopologicalSpace L.M := L.topology
  letI : ChartedSpace H L.M := L.charted
  letI : TopologicalSpace (X.obj (subseq k)).M :=
    (X.obj (subseq k)).topology
  letI : ChartedSpace H (X.obj (subseq k)).M :=
    (X.obj (subseq k)).charted
  exact (Φ.partialDiffeomorph k).open_source

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem target_open
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianCGMaps (I := I) X L subseq) (k : Nat) :
    letI : TopologicalSpace (X.obj (subseq k)).M := (X.obj (subseq k)).topology
    IsOpen (Φ.target k) := by
  letI : TopologicalSpace L.M := L.topology
  letI : ChartedSpace H L.M := L.charted
  letI : TopologicalSpace (X.obj (subseq k)).M :=
    (X.obj (subseq k)).topology
  letI : ChartedSpace H (X.obj (subseq k)).M :=
    (X.obj (subseq k)).charted
  exact (Φ.partialDiffeomorph k).open_target

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem source_subset
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianCGMaps (I := I) X L subseq)
    {K : Set L.M}
    (hK :
      letI : TopologicalSpace L.M := L.topology
      IsCompact K) :
    exists k0 : Nat, forall k : Nat, k0 <= k -> K ⊆ Φ.source k := by
  letI : TopologicalSpace L.M := L.topology
  exact Φ.source_exhausts.subset K hK



def unrepoint
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (b : forall i : Nat, (X.obj i).M)
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianCGMaps (I := I) (X.repoint b) L subseq)
    (hbase : forall k : Nat,
      letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : TopologicalSpace (X.obj (subseq k)).M :=
        (X.obj (subseq k)).topology
      letI : ChartedSpace H (X.obj (subseq k)).M :=
        (X.obj (subseq k)).charted
      Φ.partialDiffeomorph k L.basepoint = (X.obj (subseq k)).basepoint) :
    PointedRiemannianCGMaps (I := I) X L subseq where
  partialDiffeomorph := Φ.partialDiffeomorph
  source_exhausts := Φ.source_exhausts
  base_mem := Φ.base_mem
  basepoint_map := hbase

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
@[simp] theorem unrepoint_source
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (b : forall i : Nat, (X.obj i).M)
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianCGMaps (I := I) (X.repoint b) L subseq)
    (hbase : forall k : Nat,
      letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : TopologicalSpace (X.obj (subseq k)).M :=
        (X.obj (subseq k)).topology
      letI : ChartedSpace H (X.obj (subseq k)).M :=
        (X.obj (subseq k)).charted
      Φ.partialDiffeomorph k L.basepoint = (X.obj (subseq k)).basepoint)
    (k : Nat) :
    (Φ.unrepoint b hbase).source k = Φ.source k := rfl

end PointedRiemannianCGMaps



def metricSourceOpen
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianCGMaps (I := I) X L subseq) (k : Nat) :
    letI : TopologicalSpace L.M := L.topology
    TopologicalSpace.Opens L.M := by
  letI : TopologicalSpace L.M := L.topology
  exact ⟨Φ.source k, Φ.source_open k⟩



def metricTargetOpen
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianCGMaps (I := I) X L subseq) (k : Nat) :
    letI : TopologicalSpace (X.obj (subseq k)).M :=
      (X.obj (subseq k)).topology
    TopologicalSpace.Opens ((X.obj (subseq k)).M) := by
  letI : TopologicalSpace (X.obj (subseq k)).M :=
    (X.obj (subseq k)).topology
  exact ⟨Φ.target k, Φ.target_open k⟩


abbrev MetricSourceDomain
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianCGMaps (I := I) X L subseq) (k : Nat) :=
  letI : TopologicalSpace L.M := L.topology
  (metricSourceOpen (I := I) Φ k : Type _)


abbrev MetricTargetDomain
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianCGMaps (I := I) X L subseq) (k : Nat) :=
  letI : TopologicalSpace (X.obj (subseq k)).M :=
    (X.obj (subseq k)).topology
  (metricTargetOpen (I := I) Φ k : Type _)


@[implicit_reducible]
noncomputable def metricSourceDomTop
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianCGMaps (I := I) X L subseq) (k : Nat) :
    TopologicalSpace (MetricSourceDomain (I := I) Φ k) := by
  letI : TopologicalSpace L.M := L.topology
  change TopologicalSpace (metricSourceOpen (I := I) Φ k)
  infer_instance



@[implicit_reducible]
noncomputable def metricSourceDomCharted
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianCGMaps (I := I) X L subseq) (k : Nat) :
    letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) :=
      metricSourceDomTop (I := I) Φ k
    ChartedSpace H (MetricSourceDomain (I := I) Φ k) := by
  letI : TopologicalSpace L.M := L.topology
  letI : ChartedSpace H L.M := L.charted
  letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) :=
    metricSourceDomTop (I := I) Φ k
  change ChartedSpace H (metricSourceOpen (I := I) Φ k)
  exact TopologicalSpace.Opens.instChartedSpace (H := H) (M := L.M)
    (s := metricSourceOpen (I := I) Φ k)



@[implicit_reducible]
noncomputable def metricSourceDomT2
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianCGMaps (I := I) X L subseq) (k : Nat) :
    letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) :=
      metricSourceDomTop (I := I) Φ k
    T2Space (MetricSourceDomain (I := I) Φ k) := by
  letI : TopologicalSpace L.M := L.topology
  letI : T2Space L.M := L.t2
  letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) :=
    metricSourceDomTop (I := I) Φ k
  change T2Space {x : L.M // x ∈ Φ.source k}
  infer_instance



@[implicit_reducible]
noncomputable def metricSourceDomSmooth
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianCGMaps (I := I) X L subseq) (k : Nat) :
    letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) :=
      metricSourceDomTop (I := I) Φ k
    letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) :=
      metricSourceDomCharted (I := I) Φ k
    IsManifold I ∞ (MetricSourceDomain (I := I) Φ k) := by
  letI : TopologicalSpace L.M := L.topology
  letI : ChartedSpace H L.M := L.charted
  letI : IsManifold I ∞ L.M := L.smooth
  letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) :=
    metricSourceDomTop (I := I) Φ k
  letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) :=
    metricSourceDomCharted (I := I) Φ k
  change IsManifold I ∞ (metricSourceOpen (I := I) Φ k)
  exact { (metricSourceOpen (I := I) Φ k).instHasGroupoid (contDiffGroupoid ∞ I) with }



omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem metricSourceDomSigmaOf
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianCGMaps (I := I) X L subseq) (k : Nat)
    (hσ : letI : TopologicalSpace L.M := L.topology; IsSigmaCompact (Φ.source k)) :
    letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) :=
      metricSourceDomTop (I := I) Φ k
    SigmaCompactSpace (MetricSourceDomain (I := I) Φ k) := by
  letI : TopologicalSpace L.M := L.topology
  letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) :=
    metricSourceDomTop (I := I) Φ k
  change SigmaCompactSpace {x : L.M // x ∈ Φ.source k}
  exact isSigmaCompact_iff_sigmaCompactSpace.mp hσ


@[implicit_reducible]
noncomputable def metricTargetDomTop
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianCGMaps (I := I) X L subseq) (k : Nat) :
    TopologicalSpace (MetricTargetDomain (I := I) Φ k) := by
  letI : TopologicalSpace (X.obj (subseq k)).M :=
    (X.obj (subseq k)).topology
  change TopologicalSpace (metricTargetOpen (I := I) Φ k)
  infer_instance



@[implicit_reducible]
noncomputable def metricTargetDomCharted
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianCGMaps (I := I) X L subseq) (k : Nat) :
    letI : TopologicalSpace (MetricTargetDomain (I := I) Φ k) :=
      metricTargetDomTop (I := I) Φ k
    ChartedSpace H (MetricTargetDomain (I := I) Φ k) := by
  letI : TopologicalSpace (X.obj (subseq k)).M :=
    (X.obj (subseq k)).topology
  letI : ChartedSpace H (X.obj (subseq k)).M :=
    (X.obj (subseq k)).charted
  letI : TopologicalSpace (MetricTargetDomain (I := I) Φ k) :=
    metricTargetDomTop (I := I) Φ k
  change ChartedSpace H (metricTargetOpen (I := I) Φ k)
  exact TopologicalSpace.Opens.instChartedSpace (H := H)
    (M := (X.obj (subseq k)).M) (s := metricTargetOpen (I := I) Φ k)



@[implicit_reducible]
noncomputable def metricTargetDomT2
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianCGMaps (I := I) X L subseq) (k : Nat) :
    letI : TopologicalSpace (MetricTargetDomain (I := I) Φ k) :=
      metricTargetDomTop (I := I) Φ k
    T2Space (MetricTargetDomain (I := I) Φ k) := by
  letI : TopologicalSpace (X.obj (subseq k)).M :=
    (X.obj (subseq k)).topology
  letI : T2Space (X.obj (subseq k)).M := (X.obj (subseq k)).t2
  letI : TopologicalSpace (MetricTargetDomain (I := I) Φ k) :=
    metricTargetDomTop (I := I) Φ k
  change T2Space {x : (X.obj (subseq k)).M // x ∈ Φ.target k}
  infer_instance



@[implicit_reducible]
noncomputable def metricTargetDomSmooth
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianCGMaps (I := I) X L subseq) (k : Nat) :
    letI : TopologicalSpace (MetricTargetDomain (I := I) Φ k) :=
      metricTargetDomTop (I := I) Φ k
    letI : ChartedSpace H (MetricTargetDomain (I := I) Φ k) :=
      metricTargetDomCharted (I := I) Φ k
    IsManifold I ∞ (MetricTargetDomain (I := I) Φ k) := by
  letI : TopologicalSpace (X.obj (subseq k)).M :=
    (X.obj (subseq k)).topology
  letI : ChartedSpace H (X.obj (subseq k)).M :=
    (X.obj (subseq k)).charted
  letI : IsManifold I ∞ (X.obj (subseq k)).M := (X.obj (subseq k)).smooth
  letI : TopologicalSpace (MetricTargetDomain (I := I) Φ k) :=
    metricTargetDomTop (I := I) Φ k
  letI : ChartedSpace H (MetricTargetDomain (I := I) Φ k) :=
    metricTargetDomCharted (I := I) Φ k
  change IsManifold I ∞ (metricTargetOpen (I := I) Φ k)
  exact { (metricTargetOpen (I := I) Φ k).instHasGroupoid (contDiffGroupoid ∞ I) with }



omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem metricTargetDomSigmaOf
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianCGMaps (I := I) X L subseq) (k : Nat)
    (hσ :
      letI : TopologicalSpace (X.obj (subseq k)).M :=
        (X.obj (subseq k)).topology
      IsSigmaCompact (Φ.target k)) :
    letI : TopologicalSpace (MetricTargetDomain (I := I) Φ k) :=
      metricTargetDomTop (I := I) Φ k
    SigmaCompactSpace (MetricTargetDomain (I := I) Φ k) := by
  letI : TopologicalSpace (X.obj (subseq k)).M :=
    (X.obj (subseq k)).topology
  letI : TopologicalSpace (MetricTargetDomain (I := I) Φ k) :=
    metricTargetDomTop (I := I) Φ k
  change SigmaCompactSpace {x : (X.obj (subseq k)).M // x ∈ Φ.target k}
  exact isSigmaCompact_iff_sigmaCompactSpace.mp hσ

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
private theorem metricContMDiffOpenCod
    {M N : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold I ∞ M] [IsManifold I ∞ N]
    {U : TopologicalSpace.Opens N}
    {f : M -> U}
    (hf : ContMDiff I I (∞ : WithTop ℕ∞) (fun x : M => (f x : N))) :
    ContMDiff I I (∞ : WithTop ℕ∞) f := by
  haveI : IsManifold I ∞ U :=
    { U.instHasGroupoid (contDiffGroupoid ∞ I) with }
  rw [contMDiff_iff_target] at hf ⊢
  constructor
  · exact Continuous.subtype_mk hf.1 (fun x => (f x).2)
  · intro y
    have hy := hf.2 (y : N)
    simpa [Function.comp_def, extChartAt, TopologicalSpace.Opens.chartAt_eq] using hy



noncomputable def metricSourceTargetDiff
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianCGMaps (I := I) X L subseq) (k : Nat) :
    letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) :=
      metricSourceDomTop (I := I) Φ k
    letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) :=
      metricSourceDomCharted (I := I) Φ k
    letI : TopologicalSpace (MetricTargetDomain (I := I) Φ k) :=
      metricTargetDomTop (I := I) Φ k
    letI : ChartedSpace H (MetricTargetDomain (I := I) Φ k) :=
      metricTargetDomCharted (I := I) Φ k
    Diffeomorph I I (MetricSourceDomain (I := I) Φ k)
      (MetricTargetDomain (I := I) Φ k) (∞ : WithTop ℕ∞) := by
  letI : TopologicalSpace L.M := L.topology
  letI : ChartedSpace H L.M := L.charted
  letI : IsManifold I ∞ L.M := L.smooth
  letI : TopologicalSpace (X.obj (subseq k)).M :=
    (X.obj (subseq k)).topology
  letI : ChartedSpace H (X.obj (subseq k)).M :=
    (X.obj (subseq k)).charted
  letI : IsManifold I ∞ (X.obj (subseq k)).M :=
    (X.obj (subseq k)).smooth
  letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) :=
    metricSourceDomTop (I := I) Φ k
  letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) :=
    metricSourceDomCharted (I := I) Φ k
  letI : IsManifold I ∞ (MetricSourceDomain (I := I) Φ k) :=
    metricSourceDomSmooth (I := I) Φ k
  letI : TopologicalSpace (MetricTargetDomain (I := I) Φ k) :=
    metricTargetDomTop (I := I) Φ k
  letI : ChartedSpace H (MetricTargetDomain (I := I) Φ k) :=
    metricTargetDomCharted (I := I) Φ k
  letI : IsManifold I ∞ (MetricTargetDomain (I := I) Φ k) :=
    metricTargetDomSmooth (I := I) Φ k
  let e := Φ.partialDiffeomorph k
  refine
    { toEquiv := e.toPartialEquiv.toEquiv
      contMDiff_toFun := ?_
      contMDiff_invFun := ?_ }
  · have hbase :
        ContMDiff I I (∞ : WithTop ℕ∞)
          (fun x : MetricSourceDomain (I := I) Φ k => e (x : L.M)) := by
      intro x
      have hx : (x : L.M) ∈ e.source := x.2
      have hAt :
          ContMDiffAt I I (∞ : WithTop ℕ∞) (fun y : L.M => e y) (x : L.M) :=
        e.contMDiffOn_toFun.contMDiffAt (e.open_source.mem_nhds hx)
      exact (contMDiffAt_subtype_iff
        (U := metricSourceOpen (I := I) Φ k)
        (f := fun y : L.M => e y) (x := x)).2 hAt
    exact metricContMDiffOpenCod (I := I) (U := metricTargetOpen (I := I) Φ k) hbase
  · have hbase :
        ContMDiff I I (∞ : WithTop ℕ∞)
          (fun y : MetricTargetDomain (I := I) Φ k =>
            e.toPartialEquiv.symm (y : (X.obj (subseq k)).M)) := by
      intro y
      have hy : (y : (X.obj (subseq k)).M) ∈ e.target := y.2
      have hAt :
          ContMDiffAt I I (∞ : WithTop ℕ∞)
            (fun z : (X.obj (subseq k)).M => e.toPartialEquiv.symm z)
            (y : (X.obj (subseq k)).M) :=
        e.contMDiffOn_invFun.contMDiffAt (e.open_target.mem_nhds hy)
      exact (contMDiffAt_subtype_iff
        (U := metricTargetOpen (I := I) Φ k)
        (f := fun z : (X.obj (subseq k)).M => e.toPartialEquiv.symm z) (x := y)).2 hAt
    exact metricContMDiffOpenCod (I := I) (U := metricSourceOpen (I := I) Φ k) hbase

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
@[simp]
theorem metricSourceTargetDiff_apply
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianCGMaps (I := I) X L subseq) (k : Nat)
    (x : MetricSourceDomain (I := I) Φ k) :
    letI : TopologicalSpace L.M := L.topology
    letI : ChartedSpace H L.M := L.charted
    letI : TopologicalSpace (X.obj (subseq k)).M := (X.obj (subseq k)).topology
    letI : ChartedSpace H (X.obj (subseq k)).M := (X.obj (subseq k)).charted
    letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) :=
      metricSourceDomTop (I := I) Φ k
    letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) :=
      metricSourceDomCharted (I := I) Φ k
    letI : TopologicalSpace (MetricTargetDomain (I := I) Φ k) :=
      metricTargetDomTop (I := I) Φ k
    letI : ChartedSpace H (MetricTargetDomain (I := I) Φ k) :=
      metricTargetDomCharted (I := I) Φ k
    (metricSourceTargetDiff (I := I) Φ k x : (X.obj (subseq k)).M) =
      Φ.map k (x : L.M) := by
  rfl



omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem metricSourceTargetDiff_mfderiv
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianCGMaps (I := I) X L subseq) (k : Nat) :
    letI : TopologicalSpace L.M := L.topology
    letI : ChartedSpace H L.M := L.charted
    letI : IsManifold I ∞ L.M := L.smooth
    letI : TopologicalSpace (X.obj (subseq k)).M := (X.obj (subseq k)).topology
    letI : ChartedSpace H (X.obj (subseq k)).M := (X.obj (subseq k)).charted
    letI : IsManifold I ∞ (X.obj (subseq k)).M := (X.obj (subseq k)).smooth
    letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) :=
      metricSourceDomTop (I := I) Φ k
    letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) :=
      metricSourceDomCharted (I := I) Φ k
    letI : IsManifold I ∞ (MetricSourceDomain (I := I) Φ k) :=
      metricSourceDomSmooth (I := I) Φ k
    letI : TopologicalSpace (MetricTargetDomain (I := I) Φ k) :=
      metricTargetDomTop (I := I) Φ k
    letI : ChartedSpace H (MetricTargetDomain (I := I) Φ k) :=
      metricTargetDomCharted (I := I) Φ k
    letI : IsManifold I ∞ (MetricTargetDomain (I := I) Φ k) :=
      metricTargetDomSmooth (I := I) Φ k
    ∀ (x : MetricSourceDomain (I := I) Φ k) (v : TangentSpace I x),
      mfderiv I I (metricSourceTargetDiff (I := I) Φ k) x v =
        mfderiv I I (Φ.map k) (x : L.M) v := by
  letI : TopologicalSpace L.M := L.topology
  letI : ChartedSpace H L.M := L.charted
  letI : IsManifold I ∞ L.M := L.smooth
  letI : TopologicalSpace (X.obj (subseq k)).M := (X.obj (subseq k)).topology
  letI : ChartedSpace H (X.obj (subseq k)).M := (X.obj (subseq k)).charted
  letI : IsManifold I ∞ (X.obj (subseq k)).M := (X.obj (subseq k)).smooth
  letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) :=
    metricSourceDomTop (I := I) Φ k
  letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) :=
    metricSourceDomCharted (I := I) Φ k
  letI : IsManifold I ∞ (MetricSourceDomain (I := I) Φ k) :=
    metricSourceDomSmooth (I := I) Φ k
  letI : TopologicalSpace (MetricTargetDomain (I := I) Φ k) :=
    metricTargetDomTop (I := I) Φ k
  letI : ChartedSpace H (MetricTargetDomain (I := I) Φ k) :=
    metricTargetDomCharted (I := I) Φ k
  letI : IsManifold I ∞ (MetricTargetDomain (I := I) Φ k) :=
    metricTargetDomSmooth (I := I) Φ k
  intro x v
  let F := metricSourceTargetDiff (I := I) Φ k
  have hFd : MDifferentiableAt I I (F : MetricSourceDomain (I := I) Φ k ->
      MetricTargetDomain (I := I) Φ k) x :=
    F.contMDiff.contMDiffAt.mdifferentiableAt (by decide)
  have hvalT : MDifferentiableAt I I
      (Subtype.val : MetricTargetDomain (I := I) Φ k -> (X.obj (subseq k)).M) (F x) :=
    ContMDiffAt.mdifferentiableAt
      ((contMDiff_subtype_val (I := I) (n := (∞ : WithTop ℕ∞))
        (U := metricTargetOpen (I := I) Φ k)).contMDiffAt)
      (by decide)
  have hvalS : MDifferentiableAt I I
      (Subtype.val : MetricSourceDomain (I := I) Φ k -> L.M) x :=
    ContMDiffAt.mdifferentiableAt
      ((contMDiff_subtype_val (I := I) (n := (∞ : WithTop ℕ∞))
        (U := metricSourceOpen (I := I) Φ k)).contMDiffAt)
      (by decide)
  have hmap : MDifferentiableAt I I (Φ.map k) (x : L.M) :=
    ((Φ.partialDiffeomorph k).contMDiffOn_toFun.contMDiffAt
      ((Φ.partialDiffeomorph k).open_source.mem_nhds x.2)).mdifferentiableAt (by decide)
  have hleft := mfderiv_comp x hvalT hFd
  have hright := mfderiv_comp x hmap hvalS
  have hfun :
      (fun y : MetricSourceDomain (I := I) Φ k => ((F y :
        MetricTargetDomain (I := I) Φ k) : (X.obj (subseq k)).M)) =
        fun y : MetricSourceDomain (I := I) Φ k => Φ.map k (y : L.M) := by
    funext y
    exact metricSourceTargetDiff_apply (I := I) Φ k y
  have heq : mfderiv I I
      (fun y : MetricSourceDomain (I := I) Φ k => ((F y :
        MetricTargetDomain (I := I) Φ k) : (X.obj (subseq k)).M)) x =
      mfderiv I I (fun y : MetricSourceDomain (I := I) Φ k => Φ.map k (y : L.M)) x := by
    rw [hfun]
  have happ := DFunLike.congr_fun (hleft.symm.trans (heq.trans hright)) v
  change
      (mfderiv I I
          (Subtype.val : MetricTargetDomain (I := I) Φ k -> (X.obj (subseq k)).M) (F x))
        (mfderiv I I (F : MetricSourceDomain (I := I) Φ k ->
          MetricTargetDomain (I := I) Φ k) x v) =
      (mfderiv I I (Φ.map k) (x : L.M))
        (mfderiv I I (Subtype.val : MetricSourceDomain (I := I) Φ k -> L.M) x v) at happ
  have htarget :
      (mfderiv I I
          (Subtype.val : MetricTargetDomain (I := I) Φ k -> (X.obj (subseq k)).M) (F x))
        (mfderiv I I (F : MetricSourceDomain (I := I) Φ k ->
          MetricTargetDomain (I := I) Φ k) x v) =
        mfderiv I I (F : MetricSourceDomain (I := I) Φ k ->
          MetricTargetDomain (I := I) Φ k) x v := by
    simpa only using mfderiv_subtype_val_apply (I := I)
      (metricTargetOpen (I := I) Φ k) (F x)
      (mfderiv I I (F : MetricSourceDomain (I := I) Φ k ->
        MetricTargetDomain (I := I) Φ k) x v)
  have hsource :
      mfderiv I I (Subtype.val : MetricSourceDomain (I := I) Φ k -> L.M) x v = v := by
    simpa only using mfderiv_subtype_val_apply (I := I)
      (metricSourceOpen (I := I) Φ k) x v
  rw [htarget, hsource] at happ
  exact happ

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
@[simp]
theorem metricSourceTargetDiff_symm_apply
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianCGMaps (I := I) X L subseq) (k : Nat)
    (y : MetricTargetDomain (I := I) Φ k) :
    letI : TopologicalSpace L.M := L.topology
    letI : ChartedSpace H L.M := L.charted
    letI : TopologicalSpace (X.obj (subseq k)).M := (X.obj (subseq k)).topology
    letI : ChartedSpace H (X.obj (subseq k)).M := (X.obj (subseq k)).charted
    letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) :=
      metricSourceDomTop (I := I) Φ k
    letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) :=
      metricSourceDomCharted (I := I) Φ k
    letI : TopologicalSpace (MetricTargetDomain (I := I) Φ k) :=
      metricTargetDomTop (I := I) Φ k
    letI : ChartedSpace H (MetricTargetDomain (I := I) Φ k) :=
      metricTargetDomCharted (I := I) Φ k
    ((metricSourceTargetDiff (I := I) Φ k).symm y : L.M) =
      (Φ.partialDiffeomorph k).toPartialEquiv.symm (y : (X.obj (subseq k)).M) := by
  rfl

def metricSourceCompactSet
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianCGMaps (I := I) X L subseq) (k : Nat)
    (K : Set L.M) : Set (MetricSourceDomain (I := I) Φ k) :=
  {x | (x : L.M) ∈ K}



omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem metricSourceCompactSet_isCompact
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianCGMaps (I := I) X L subseq) (k : Nat)
    {K : Set L.M}
    (hK :
      letI : TopologicalSpace L.M := L.topology
      IsCompact K)
    (hKsrc :
      letI : TopologicalSpace L.M := L.topology
      K ⊆ Φ.source k) :
    letI : TopologicalSpace L.M := L.topology
    IsCompact (metricSourceCompactSet (I := I) Φ k K) := by
  letI : TopologicalSpace L.M := L.topology
  change IsCompact ((Subtype.val : MetricSourceDomain (I := I) Φ k -> L.M) ⁻¹' K)
  rw [Subtype.isCompact_iff]
  have hImage :
      Subtype.val '' ((Subtype.val : MetricSourceDomain (I := I) Φ k -> L.M) ⁻¹' K) =
        K := by
    ext x
    constructor
    · rintro ⟨y, hyK, rfl⟩
      exact hyK
    · intro hxK
      exact ⟨⟨x, hKsrc hxK⟩, hxK, rfl⟩
  rw [hImage]
  exact hK


structure MetricSourceData
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianCGMaps (I := I) X L subseq) (k : Nat) where
  topology : TopologicalSpace (MetricSourceDomain (I := I) Φ k)
  charted : ChartedSpace H (MetricSourceDomain (I := I) Φ k)
  t2 : T2Space (MetricSourceDomain (I := I) Φ k)
  smooth : IsManifold I ∞ (MetricSourceDomain (I := I) Φ k)
  sigmaCompact : SigmaCompactSpace (MetricSourceDomain (I := I) Φ k)
  limitMetric :
    letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) := topology
    letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) := charted
    SmoothRiemannianMetric I (MetricSourceDomain (I := I) Φ k)
  pullbackMetric :
    letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) := topology
    letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) := charted
    SmoothRiemannianMetric I (MetricSourceDomain (I := I) Φ k)
  referenceMetric :
    letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) := topology
    letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) := charted
    SmoothRiemannianMetric I (MetricSourceDomain (I := I) Φ k)
  compact_preimage :
    letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) := topology
    letI : TopologicalSpace L.M := L.topology
    forall K : Set L.M, IsCompact K ->
      K ⊆ Φ.source k ->
      IsCompact (metricSourceCompactSet (I := I) Φ k K)
  limit_inner :
    letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) := topology
    letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) := charted
    letI : TopologicalSpace L.M := L.topology
    letI : ChartedSpace H L.M := L.charted
    letI : T2Space L.M := L.t2
    letI : IsManifold I ∞ L.M := L.smooth
    letI : SigmaCompactSpace L.M := L.sigmaCompact
    forall (x : MetricSourceDomain (I := I) Φ k) (v w : TangentSpace I x),
      limitMetric.inner x v w =
        L.metric.inner (x : L.M)
          ((mfderiv I I (fun y : MetricSourceDomain (I := I) Φ k => (y : L.M)) x) v)
          ((mfderiv I I (fun y : MetricSourceDomain (I := I) Φ k => (y : L.M)) x) w)
  pullback_inner :
    letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) := topology
    letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) := charted
    letI : TopologicalSpace L.M := L.topology
    letI : ChartedSpace H L.M := L.charted
    letI : T2Space L.M := L.t2
    letI : IsManifold I ∞ L.M := L.smooth
    letI : SigmaCompactSpace L.M := L.sigmaCompact
    letI : TopologicalSpace (X.obj (subseq k)).M :=
      (X.obj (subseq k)).topology
    letI : ChartedSpace H (X.obj (subseq k)).M :=
      (X.obj (subseq k)).charted
    letI : T2Space (X.obj (subseq k)).M :=
      (X.obj (subseq k)).t2
    letI : IsManifold I ∞ (X.obj (subseq k)).M :=
      (X.obj (subseq k)).smooth
    letI : SigmaCompactSpace (X.obj (subseq k)).M :=
      (X.obj (subseq k)).sigmaCompact
    forall (x : MetricSourceDomain (I := I) Φ k) (v w : TangentSpace I x),
      pullbackMetric.inner x v w =
        (X.obj (subseq k)).metric.inner
          (Φ.map k (x : L.M))
          ((mfderiv I I
            (fun y : MetricSourceDomain (I := I) Φ k => Φ.map k (y : L.M)) x) v)
          ((mfderiv I I
            (fun y : MetricSourceDomain (I := I) Φ k => Φ.map k (y : L.M)) x) w)

namespace MetricSourceData



def unrepoint
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (b : forall i : Nat, (X.obj i).M)
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    {Φ : PointedRiemannianCGMaps (I := I) (X.repoint b) L subseq}
    (hbase : forall k : Nat,
      letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : TopologicalSpace (X.obj (subseq k)).M :=
        (X.obj (subseq k)).topology
      letI : ChartedSpace H (X.obj (subseq k)).M :=
        (X.obj (subseq k)).charted
      Φ.partialDiffeomorph k L.basepoint = (X.obj (subseq k)).basepoint)
    (k : Nat) (D : MetricSourceData (I := I) Φ k) :
    MetricSourceData (I := I) (Φ.unrepoint b hbase) k where
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




noncomputable def ofCanonical
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    {Φ : PointedRiemannianCGMaps (I := I) X L subseq}
    {k : Nat}
    (sigmaCompact :
      letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) :=
        metricSourceDomTop (I := I) Φ k
      SigmaCompactSpace (MetricSourceDomain (I := I) Φ k))
    (limitMetric :
      letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) :=
        metricSourceDomTop (I := I) Φ k
      letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) :=
        metricSourceDomCharted (I := I) Φ k
      letI : IsManifold I ∞ (MetricSourceDomain (I := I) Φ k) :=
        metricSourceDomSmooth (I := I) Φ k
      SmoothRiemannianMetric I (MetricSourceDomain (I := I) Φ k))
    (pullbackMetric :
      letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) :=
        metricSourceDomTop (I := I) Φ k
      letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) :=
        metricSourceDomCharted (I := I) Φ k
      letI : IsManifold I ∞ (MetricSourceDomain (I := I) Φ k) :=
        metricSourceDomSmooth (I := I) Φ k
      SmoothRiemannianMetric I (MetricSourceDomain (I := I) Φ k))
    (referenceMetric :
      letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) :=
        metricSourceDomTop (I := I) Φ k
      letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) :=
        metricSourceDomCharted (I := I) Φ k
      letI : IsManifold I ∞ (MetricSourceDomain (I := I) Φ k) :=
        metricSourceDomSmooth (I := I) Φ k
      SmoothRiemannianMetric I (MetricSourceDomain (I := I) Φ k))
    (limit_inner :
      letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) :=
        metricSourceDomTop (I := I) Φ k
      letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) :=
        metricSourceDomCharted (I := I) Φ k
      letI : IsManifold I ∞ (MetricSourceDomain (I := I) Φ k) :=
        metricSourceDomSmooth (I := I) Φ k
      letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : T2Space L.M := L.t2
      letI : IsManifold I ∞ L.M := L.smooth
      letI : SigmaCompactSpace L.M := L.sigmaCompact
      forall (x : MetricSourceDomain (I := I) Φ k) (v w : TangentSpace I x),
        limitMetric.inner x v w =
          L.metric.inner (x : L.M)
            ((mfderiv I I (fun y : MetricSourceDomain (I := I) Φ k => (y : L.M)) x) v)
            ((mfderiv I I (fun y : MetricSourceDomain (I := I) Φ k => (y : L.M)) x) w))
    (pullback_inner :
      letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) :=
        metricSourceDomTop (I := I) Φ k
      letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) :=
        metricSourceDomCharted (I := I) Φ k
      letI : IsManifold I ∞ (MetricSourceDomain (I := I) Φ k) :=
        metricSourceDomSmooth (I := I) Φ k
      letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : T2Space L.M := L.t2
      letI : IsManifold I ∞ L.M := L.smooth
      letI : SigmaCompactSpace L.M := L.sigmaCompact
      letI : TopologicalSpace (X.obj (subseq k)).M :=
        (X.obj (subseq k)).topology
      letI : ChartedSpace H (X.obj (subseq k)).M :=
        (X.obj (subseq k)).charted
      letI : T2Space (X.obj (subseq k)).M := (X.obj (subseq k)).t2
      letI : IsManifold I ∞ (X.obj (subseq k)).M :=
        (X.obj (subseq k)).smooth
      letI : SigmaCompactSpace (X.obj (subseq k)).M :=
        (X.obj (subseq k)).sigmaCompact
      forall (x : MetricSourceDomain (I := I) Φ k) (v w : TangentSpace I x),
        pullbackMetric.inner x v w =
          (X.obj (subseq k)).metric.inner
            (Φ.map k (x : L.M))
            ((mfderiv I I
              (fun y : MetricSourceDomain (I := I) Φ k => Φ.map k (y : L.M)) x) v)
            ((mfderiv I I
              (fun y : MetricSourceDomain (I := I) Φ k => Φ.map k (y : L.M)) x) w)) :
    MetricSourceData (I := I) Φ k where
  topology := metricSourceDomTop (I := I) Φ k
  charted := metricSourceDomCharted (I := I) Φ k
  t2 := metricSourceDomT2 (I := I) Φ k
  smooth := metricSourceDomSmooth (I := I) Φ k
  sigmaCompact := sigmaCompact
  limitMetric := limitMetric
  pullbackMetric := pullbackMetric
  referenceMetric := referenceMetric
  compact_preimage := by
    intro K hK hKsrc
    exact metricSourceCompactSet_isCompact (I := I) Φ k hK hKsrc
  limit_inner := limit_inner
  pullback_inner := pullback_inner




noncomputable def ofRestrictPullback
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    {Φ : PointedRiemannianCGMaps (I := I) X L subseq}
    {k : Nat}
    (hσsrc : letI : TopologicalSpace L.M := L.topology; IsSigmaCompact (Φ.source k))
    (hσtgt :
      letI : TopologicalSpace (X.obj (subseq k)).M :=
        (X.obj (subseq k)).topology
      IsSigmaCompact (Φ.target k))
    (referenceMetric :
      letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) :=
        metricSourceDomTop (I := I) Φ k
      letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) :=
        metricSourceDomCharted (I := I) Φ k
      letI : IsManifold I ∞ (MetricSourceDomain (I := I) Φ k) :=
        metricSourceDomSmooth (I := I) Φ k
      SmoothRiemannianMetric I (MetricSourceDomain (I := I) Φ k)) :
    MetricSourceData (I := I) Φ k := by
  letI : TopologicalSpace L.M := L.topology
  letI : ChartedSpace H L.M := L.charted
  letI : T2Space L.M := L.t2
  letI : IsManifold I ∞ L.M := L.smooth
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) L.M := by
    change IsManifold I ∞ L.M
    infer_instance
  letI : SigmaCompactSpace L.M := L.sigmaCompact
  letI : TopologicalSpace (X.obj (subseq k)).M :=
    (X.obj (subseq k)).topology
  letI : ChartedSpace H (X.obj (subseq k)).M :=
    (X.obj (subseq k)).charted
  letI : T2Space (X.obj (subseq k)).M := (X.obj (subseq k)).t2
  letI : IsManifold I ∞ (X.obj (subseq k)).M :=
    (X.obj (subseq k)).smooth
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.obj (subseq k)).M := by
    change IsManifold I ∞ (X.obj (subseq k)).M
    infer_instance
  letI : SigmaCompactSpace (X.obj (subseq k)).M :=
    (X.obj (subseq k)).sigmaCompact
  letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) :=
    metricSourceDomTop (I := I) Φ k
  letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) :=
    metricSourceDomCharted (I := I) Φ k
  letI : T2Space (MetricSourceDomain (I := I) Φ k) := metricSourceDomT2 (I := I) Φ k
  letI : IsManifold I ∞ (MetricSourceDomain (I := I) Φ k) :=
    metricSourceDomSmooth (I := I) Φ k
  letI : SigmaCompactSpace (MetricSourceDomain (I := I) Φ k) :=
    metricSourceDomSigmaOf (I := I) Φ k hσsrc
  letI : TopologicalSpace (MetricTargetDomain (I := I) Φ k) :=
    metricTargetDomTop (I := I) Φ k
  letI : ChartedSpace H (MetricTargetDomain (I := I) Φ k) :=
    metricTargetDomCharted (I := I) Φ k
  letI : T2Space (MetricTargetDomain (I := I) Φ k) := metricTargetDomT2 (I := I) Φ k
  letI : IsManifold I ∞ (MetricTargetDomain (I := I) Φ k) :=
    metricTargetDomSmooth (I := I) Φ k
  letI : SigmaCompactSpace (MetricTargetDomain (I := I) Φ k) :=
    metricTargetDomSigmaOf (I := I) Φ k hσtgt
  refine MetricSourceData.ofCanonical (I := I)
    (Φ := Φ) (k := k)
    (metricSourceDomSigmaOf (I := I) Φ k hσsrc)
    (by
      let sourceSigma : SigmaCompactSpace (metricSourceOpen (I := I) Φ k) := by
        change SigmaCompactSpace (MetricSourceDomain (I := I) Φ k)
        exact metricSourceDomSigmaOf (I := I) Φ k hσsrc
      let sourceT2 : T2Space (metricSourceOpen (I := I) Φ k) := by
        change T2Space (MetricSourceDomain (I := I) Φ k)
        exact metricSourceDomT2 (I := I) Φ k
      exact
        @SmoothRiemannianMetric.restrictOpen E inferInstance inferInstance H inferInstance I
          L.M L.topology L.charted L.smooth inferInstance
          L.metric (metricSourceOpen (I := I) Φ k) sourceSigma sourceT2)
    (by
      let sourceSigma : SigmaCompactSpace (metricSourceOpen (I := I) Φ k) := by
        change SigmaCompactSpace (MetricSourceDomain (I := I) Φ k)
        exact metricSourceDomSigmaOf (I := I) Φ k hσsrc
      let sourceT2 : T2Space (metricSourceOpen (I := I) Φ k) := by
        change T2Space (MetricSourceDomain (I := I) Φ k)
        exact metricSourceDomT2 (I := I) Φ k
      let targetSigma : SigmaCompactSpace (metricTargetOpen (I := I) Φ k) := by
        change SigmaCompactSpace (MetricTargetDomain (I := I) Φ k)
        exact metricTargetDomSigmaOf (I := I) Φ k hσtgt
      let targetT2 : T2Space (metricTargetOpen (I := I) Φ k) := by
        change T2Space (MetricTargetDomain (I := I) Φ k)
        exact metricTargetDomT2 (I := I) Φ k
      let targetMetric : SmoothRiemannianMetric I (metricTargetOpen (I := I) Φ k) :=
        @SmoothRiemannianMetric.restrictOpen E inferInstance inferInstance H inferInstance I
          (X.obj (subseq k)).M (X.obj (subseq k)).topology
          (X.obj (subseq k)).charted (X.obj (subseq k)).smooth inferInstance
          (X.obj (subseq k)).metric (metricTargetOpen (I := I) Φ k)
          targetSigma targetT2
      exact
        @Diffeomorph.pullbackMetric E inferInstance inferInstance inferInstance H inferInstance I
          (MetricSourceDomain (I := I) Φ k) (metricSourceDomTop (I := I) Φ k)
          (metricSourceDomCharted (I := I) Φ k) (metricSourceDomSmooth (I := I) Φ k)
          (MetricTargetDomain (I := I) Φ k) (metricTargetDomTop (I := I) Φ k)
          (metricTargetDomCharted (I := I) Φ k) (metricTargetDomSmooth (I := I) Φ k)
          sourceSigma sourceT2 targetMetric (metricSourceTargetDiff (I := I) Φ k))
    referenceMetric
    ?_ ?_
  · intro x v w
    change L.metric.inner (x : L.M) v w =
      L.metric.inner (x : L.M)
        ((mfderiv I I (fun y : MetricSourceDomain (I := I) Φ k => (y : L.M)) x) v)
        ((mfderiv I I (fun y : MetricSourceDomain (I := I) Φ k => (y : L.M)) x) w)
    have hvinc :
        (mfderiv I I (fun y : MetricSourceDomain (I := I) Φ k => (y : L.M)) x) v = v := by
      simpa only using
        mfderiv_subtype_val_apply (I := I) (metricSourceOpen (I := I) Φ k) x v
    have hwinc :
        (mfderiv I I (fun y : MetricSourceDomain (I := I) Φ k => (y : L.M)) x) w = w := by
      simpa only using
        mfderiv_subtype_val_apply (I := I) (metricSourceOpen (I := I) Φ k) x w
    rw [hvinc, hwinc]
  · intro x v w
    rw [Diffeomorph.pullbackMetric_inner]
    change (X.obj (subseq k)).metric.inner
        ((metricSourceTargetDiff (I := I) Φ k x : MetricTargetDomain (I := I) Φ k) :
          (X.obj (subseq k)).M)
        ((mfderiv I I (metricSourceTargetDiff (I := I) Φ k) x) v)
        ((mfderiv I I (metricSourceTargetDiff (I := I) Φ k) x) w) =
      (X.obj (subseq k)).metric.inner
        (Φ.map k (x : L.M))
        ((mfderiv I I
          (fun y : MetricSourceDomain (I := I) Φ k => Φ.map k (y : L.M)) x) v)
        ((mfderiv I I
          (fun y : MetricSourceDomain (I := I) Φ k => Φ.map k (y : L.M)) x) w)
    have hchain :
        mfderiv I I
            (fun y : MetricSourceDomain (I := I) Φ k =>
              ((metricSourceTargetDiff (I := I) Φ k y : MetricTargetDomain (I := I) Φ k) :
                (X.obj (subseq k)).M)) x =
          (mfderiv I I
              (fun y : MetricTargetDomain (I := I) Φ k => (y : (X.obj (subseq k)).M))
              (metricSourceTargetDiff (I := I) Φ k x)).comp
            (mfderiv I I (metricSourceTargetDiff (I := I) Φ k) x) := by
      have hval :
          MDifferentiableAt I I
            (fun y : MetricTargetDomain (I := I) Φ k => (y : (X.obj (subseq k)).M))
            (metricSourceTargetDiff (I := I) Φ k x) := by
        exact ContMDiffAt.mdifferentiableAt
          ((contMDiff_subtype_val (I := I) (n := (∞ : WithTop ℕ∞))
            (U := metricTargetOpen (I := I) Φ k)).contMDiffAt)
          (by simp)
      have hdiff :
          MDifferentiableAt I I (metricSourceTargetDiff (I := I) Φ k)
            x :=
        (metricSourceTargetDiff (I := I) Φ k).contMDiff.contMDiffAt.mdifferentiableAt
          (by simp)
      simpa [Function.comp_def] using
        (mfderiv_comp (I := I) (I' := I) (I'' := I) x hval hdiff)
    have hv :
        mfderiv I I
            (fun y : MetricSourceDomain (I := I) Φ k =>
              ((metricSourceTargetDiff (I := I) Φ k y : MetricTargetDomain (I := I) Φ k) :
                (X.obj (subseq k)).M)) x v =
          mfderiv I I (metricSourceTargetDiff (I := I) Φ k) x v := by
      rw [hchain, ContinuousLinearMap.comp_apply]
      have htarget :
          (mfderiv I I
              (fun y : MetricTargetDomain (I := I) Φ k => (y : (X.obj (subseq k)).M))
              (metricSourceTargetDiff (I := I) Φ k x))
            ((mfderiv I I (metricSourceTargetDiff (I := I) Φ k) x) v) =
            (mfderiv I I (metricSourceTargetDiff (I := I) Φ k) x) v := by
        simpa only using
          mfderiv_subtype_val_apply (I := I) (metricTargetOpen (I := I) Φ k)
            (metricSourceTargetDiff (I := I) Φ k x)
            ((mfderiv I I (metricSourceTargetDiff (I := I) Φ k) x) v)
      exact htarget
    have hw :
        mfderiv I I
            (fun y : MetricSourceDomain (I := I) Φ k =>
              ((metricSourceTargetDiff (I := I) Φ k y : MetricTargetDomain (I := I) Φ k) :
                (X.obj (subseq k)).M)) x w =
          mfderiv I I (metricSourceTargetDiff (I := I) Φ k) x w := by
      rw [hchain, ContinuousLinearMap.comp_apply]
      have htarget :
          (mfderiv I I
              (fun y : MetricTargetDomain (I := I) Φ k => (y : (X.obj (subseq k)).M))
              (metricSourceTargetDiff (I := I) Φ k x))
            ((mfderiv I I (metricSourceTargetDiff (I := I) Φ k) x) w) =
            (mfderiv I I (metricSourceTargetDiff (I := I) Φ k) x) w := by
        simpa only using
          mfderiv_subtype_val_apply (I := I) (metricTargetOpen (I := I) Φ k)
            (metricSourceTargetDiff (I := I) Φ k x)
            ((mfderiv I I (metricSourceTargetDiff (I := I) Φ k) x) w)
      exact htarget
    have hxmap :
        ((metricSourceTargetDiff (I := I) Φ k x : MetricTargetDomain (I := I) Φ k) :
          (X.obj (subseq k)).M) = Φ.map k (x : L.M) :=
      metricSourceTargetDiff_apply (I := I) Φ k x
    have hfun :
        (fun y : MetricSourceDomain (I := I) Φ k =>
          ((metricSourceTargetDiff (I := I) Φ k y : MetricTargetDomain (I := I) Φ k) :
            (X.obj (subseq k)).M)) =
          fun y : MetricSourceDomain (I := I) Φ k => Φ.map k (y : L.M) := by
      funext y
      exact metricSourceTargetDiff_apply (I := I) Φ k y
    rw [hxmap, ← hv, ← hw, hfun]
    rfl

noncomputable def derivNormSupOn
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    {k : Nat}
    {Φ : PointedRiemannianCGMaps (I := I) X L subseq}
    (D : MetricSourceData (I := I) Φ k)
    (K : Set L.M) (p : Nat) : Real := by
  letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) := D.topology
  letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) := D.charted
  letI : T2Space (MetricSourceDomain (I := I) Φ k) := D.t2
  letI : IsManifold I ∞ (MetricSourceDomain (I := I) Φ k) := D.smooth
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1)
      (MetricSourceDomain (I := I) Φ k) := by
    change IsManifold I ∞ (MetricSourceDomain (I := I) Φ k)
    infer_instance
  letI : SigmaCompactSpace (MetricSourceDomain (I := I) Φ k) := D.sigmaCompact
  exact metricDerivNormSupOn (I := I)
    (metricSourceCompactSet (I := I) Φ k K) p
    D.pullbackMetric D.limitMetric D.referenceMetric

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
@[simp] theorem unrepoint_supOn
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (b : forall i : Nat, (X.obj i).M)
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    {Φ : PointedRiemannianCGMaps (I := I) (X.repoint b) L subseq}
    (hbase : forall k : Nat,
      letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : TopologicalSpace (X.obj (subseq k)).M :=
        (X.obj (subseq k)).topology
      letI : ChartedSpace H (X.obj (subseq k)).M :=
        (X.obj (subseq k)).charted
      Φ.partialDiffeomorph k L.basepoint = (X.obj (subseq k)).basepoint)
    (k : Nat) (D : MetricSourceData (I := I) Φ k)
    (K : Set L.M) (p : Nat) :
    (D.unrepoint b hbase k).derivNormSupOn (I := I) K p =
      D.derivNormSupOn (I := I) K p := rfl

end MetricSourceData



def MetricSourceCPConvOn
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianCGMaps (I := I) X L subseq)
    (D : forall k : Nat, MetricSourceData (I := I) Φ k)
    (K : Set L.M)
    (_hK : letI : TopologicalSpace L.M := L.topology; IsCompact K)
    (p : Nat) : Prop :=
  forall ε : Real, 0 < ε ->
    exists k0 : Nat, forall k : Nat, k0 <= k ->
      K ⊆ Φ.source k /\ (D k).derivNormSupOn (I := I) K p < ε



structure MetricCGConvergenceData
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianCGMaps (I := I) X L subseq) where
  domain : forall k : Nat, MetricSourceData (I := I) Φ k
  converges :
    forall K : Set L.M,
      forall hK : letI : TopologicalSpace L.M := L.topology; IsCompact K,
      forall p : Nat, MetricSourceCPConvOn (I := I) Φ domain K hK p

namespace MetricCGConvergenceData




def unrepoint
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (b : forall i : Nat, (X.obj i).M)
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    {Φ : PointedRiemannianCGMaps (I := I) (X.repoint b) L subseq}
    (hbase : forall k : Nat,
      letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : TopologicalSpace (X.obj (subseq k)).M :=
        (X.obj (subseq k)).topology
      letI : ChartedSpace H (X.obj (subseq k)).M :=
        (X.obj (subseq k)).charted
      Φ.partialDiffeomorph k L.basepoint = (X.obj (subseq k)).basepoint)
    (Cd : MetricCGConvergenceData (I := I) Φ) :
    MetricCGConvergenceData (I := I) (Φ.unrepoint b hbase) where
  domain k := (Cd.domain k).unrepoint b hbase k
  converges := by
    intro K hK p ε hε
    simpa only [PointedRiemannianCGMaps.unrepoint_source,
      MetricSourceData.unrepoint_supOn] using Cd.converges K hK p ε hε




noncomputable def of_derivNormSupOn
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    {Φ : PointedRiemannianCGMaps (I := I) X L subseq}
    {D : forall k : Nat, MetricSourceData (I := I) Φ k}
    (hconv : forall K : Set L.M,
      forall _hK : letI : TopologicalSpace L.M := L.topology; IsCompact K,
      forall p : Nat,
        forall ε : Real, 0 < ε ->
          exists k0 : Nat, forall k : Nat, k0 <= k ->
            (D k).derivNormSupOn (I := I) K p < ε) :
    MetricCGConvergenceData (I := I) Φ where
  domain := D
  converges := by
    intro K hK p ε hε
    obtain ⟨kSrc, hSrc⟩ := Φ.source_subset hK
    obtain ⟨kConv, hConv⟩ := hconv K hK p ε hε
    refine ⟨max kSrc kConv, fun k hk => ?_⟩
    refine ⟨hSrc k (le_trans (Nat.le_max_left kSrc kConv) hk), ?_⟩
    exact hConv k (le_trans (Nat.le_max_right kSrc kConv) hk)




noncomputable def ofRestrictPullback
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    {Φ : PointedRiemannianCGMaps (I := I) X L subseq}
    (hσsrc : forall k : Nat,
      letI : TopologicalSpace L.M := L.topology
      IsSigmaCompact (Φ.source k))
    (hσtgt : forall k : Nat,
      letI : TopologicalSpace (X.obj (subseq k)).M :=
        (X.obj (subseq k)).topology
      IsSigmaCompact (Φ.target k))
    (referenceMetric : forall k : Nat,
      letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) :=
        metricSourceDomTop (I := I) Φ k
      letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) :=
        metricSourceDomCharted (I := I) Φ k
      letI : IsManifold I ∞ (MetricSourceDomain (I := I) Φ k) :=
        metricSourceDomSmooth (I := I) Φ k
      SmoothRiemannianMetric I (MetricSourceDomain (I := I) Φ k))
    (hconv : forall K : Set L.M,
      forall _hK : letI : TopologicalSpace L.M := L.topology; IsCompact K,
      forall p : Nat,
        forall ε : Real, 0 < ε ->
          exists k0 : Nat, forall k : Nat, k0 <= k ->
            ((MetricSourceData.ofRestrictPullback (I := I)
              (Φ := Φ) (k := k) (hσsrc k) (hσtgt k)
              (referenceMetric k)).derivNormSupOn (I := I) K p) < ε) :
    MetricCGConvergenceData (I := I) Φ :=
  MetricCGConvergenceData.of_derivNormSupOn (I := I)
    (D := fun k => MetricSourceData.ofRestrictPullback (I := I)
      (Φ := Φ) (k := k) (hσsrc k) (hσtgt k) (referenceMetric k))
    hconv

end MetricCGConvergenceData



structure PointedRiemannianCGConverges
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (L : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (subseq : Nat -> Nat)
    (Φ : PointedRiemannianCGMaps (I := I) X L subseq) where
  metrics : MetricCGConvergenceData (I := I) Φ

namespace PointedRiemannianCGConverges



def unrepoint
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (b : forall i : Nat, (X.obj i).M)
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    {Φ : PointedRiemannianCGMaps (I := I) (X.repoint b) L subseq}
    (hbase : forall k : Nat,
      letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : TopologicalSpace (X.obj (subseq k)).M :=
        (X.obj (subseq k)).topology
      letI : ChartedSpace H (X.obj (subseq k)).M :=
        (X.obj (subseq k)).charted
      Φ.partialDiffeomorph k L.basepoint = (X.obj (subseq k)).basepoint)
    (C : PointedRiemannianCGConverges (I := I) (X.repoint b) L subseq Φ) :
    PointedRiemannianCGConverges (I := I) X L subseq (Φ.unrepoint b hbase) where
  metrics := C.metrics.unrepoint b hbase



noncomputable def of_derivNormSupOn
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianCGMaps (I := I) X L subseq)
    {D : forall k : Nat, MetricSourceData (I := I) Φ k}
    (hconv : forall K : Set L.M,
      forall _hK : letI : TopologicalSpace L.M := L.topology; IsCompact K,
      forall p : Nat,
        forall ε : Real, 0 < ε ->
          exists k0 : Nat, forall k : Nat, k0 <= k ->
            (D k).derivNormSupOn (I := I) K p < ε) :
    PointedRiemannianCGConverges (I := I) X L subseq Φ where
  metrics := MetricCGConvergenceData.of_derivNormSupOn (I := I) hconv



noncomputable def ofRestrictPullback
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianCGMaps (I := I) X L subseq)
    (hσsrc : forall k : Nat,
      letI : TopologicalSpace L.M := L.topology
      IsSigmaCompact (Φ.source k))
    (hσtgt : forall k : Nat,
      letI : TopologicalSpace (X.obj (subseq k)).M :=
        (X.obj (subseq k)).topology
      IsSigmaCompact (Φ.target k))
    (referenceMetric : forall k : Nat,
      letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) :=
        metricSourceDomTop (I := I) Φ k
      letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) :=
        metricSourceDomCharted (I := I) Φ k
      letI : IsManifold I ∞ (MetricSourceDomain (I := I) Φ k) :=
        metricSourceDomSmooth (I := I) Φ k
      SmoothRiemannianMetric I (MetricSourceDomain (I := I) Φ k))
    (hconv : forall K : Set L.M,
      forall _hK : letI : TopologicalSpace L.M := L.topology; IsCompact K,
      forall p : Nat,
        forall ε : Real, 0 < ε ->
          exists k0 : Nat, forall k : Nat, k0 <= k ->
            ((MetricSourceData.ofRestrictPullback (I := I)
              (Φ := Φ) (k := k) (hσsrc k) (hσtgt k)
              (referenceMetric k)).derivNormSupOn (I := I) K p) < ε) :
    PointedRiemannianCGConverges (I := I) X L subseq Φ where
  metrics := MetricCGConvergenceData.ofRestrictPullback (I := I)
    hσsrc hσtgt referenceMetric hconv

end PointedRiemannianCGConverges


structure MetricCompactnessConclusion
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) where
  subseq : Nat -> Nat
  strictMono : StrictMono subseq
  limit : PointedRiemannianManifold.{u, uE, uH} (I := I)
  limit_complete : MetricComplete (I := I) limit
  maps : PointedRiemannianCGMaps (I := I) X limit subseq
  convergence : PointedRiemannianCGConverges (I := I) X limit subseq maps
















def metricCompactness
    [I.Boundaryless]
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (_hcomplete : SeqMetricComplete (I := I) X)
    (_hgeom : SeqBoundedGeometry (I := I) X)
    (_hinj : BaseInjBound (I := I) X) :
    MetricCompactnessConclusion (I := I) X := by




  sorry

end HCGCompactness
end DifferentialGeometry
