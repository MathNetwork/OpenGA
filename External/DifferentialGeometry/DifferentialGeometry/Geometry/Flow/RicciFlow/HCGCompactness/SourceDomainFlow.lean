import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.SolutionPullback
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.SolutionRestrictOpen
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.PointedConvergence

set_option autoImplicit false
set_option linter.style.longLine false






















noncomputable section

open Set Function Filter Bundle Manifold Tensor0SBundle
open scoped Manifold Topology ContDiff
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow (SolutionOn IsSolutionOn)

namespace DifferentialGeometry
namespace HCGCompactness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]






noncomputable def sourceFlow
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq) (k : Nat)
    (hσsrc : letI : TopologicalSpace P.M := P.topology; IsSigmaCompact (Φ.source k))
    (hσtgt :
      letI : TopologicalSpace (X.term (subseq k)).M :=
        (X.term (subseq k)).topology
      IsSigmaCompact (Φ.target k)) :
    letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
    letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
    letI : T2Space (SourceDomain (I := I) Φ k) := sourceDomT2 (I := I) Φ k
    letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
    letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) :=
      sourceDomSigmaOf (I := I) Φ k hσsrc
    letI : IsManifold I 1 (SourceDomain (I := I) Φ k) :=
      IsManifold.of_le (I := I) (M := SourceDomain (I := I) Φ k) (n := (∞ : WithTop ℕ∞))
        (by decide : (1 : WithTop ℕ∞) ≤ ∞)
    letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (SourceDomain (I := I) Φ k) := by
      change IsManifold I ∞ (SourceDomain (I := I) Φ k)
      infer_instance
    SolutionOn (I := I) (M := SourceDomain (I := I) Φ k) X.D := by
  letI : TopologicalSpace (X.term (subseq k)).M :=
    (X.term (subseq k)).topology
  letI : ChartedSpace H (X.term (subseq k)).M :=
    (X.term (subseq k)).charted
  letI : T2Space (X.term (subseq k)).M := (X.term (subseq k)).t2
  letI : IsManifold I ∞ (X.term (subseq k)).M :=
    (X.term (subseq k)).smooth
  letI : IsManifold I 1 (X.term (subseq k)).M :=
    IsManifold.of_le (I := I) (M := (X.term (subseq k)).M) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  letI : IsManifold I 2 (X.term (subseq k)).M :=
    IsManifold.of_le (I := I) (M := (X.term (subseq k)).M) (n := (∞ : WithTop ℕ∞))
      (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.term (subseq k)).M := by
    change IsManifold I ∞ (X.term (subseq k)).M
    infer_instance
  letI : SigmaCompactSpace (X.term (subseq k)).M :=
    (X.term (subseq k)).sigmaCompact
  letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
  letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
  letI : T2Space (SourceDomain (I := I) Φ k) := sourceDomT2 (I := I) Φ k
  letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
  letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) :=
    sourceDomSigmaOf (I := I) Φ k hσsrc

  letI : SigmaCompactSpace ↥(targetOpen (I := I) Φ k) :=
    targetDomSigmaOf (I := I) Φ k hσtgt
  letI : T2Space ↥(targetOpen (I := I) Φ k) := targetDomT2 (I := I) Φ k
  letI : IsManifold I 1 ↥(targetOpen (I := I) Φ k) :=
    IsManifold.of_le (I := I) (M := ↥(targetOpen (I := I) Φ k)) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) ↥(targetOpen (I := I) Φ k) := by
    change IsManifold I ∞ ↥(targetOpen (I := I) Φ k)
    infer_instance

  letI : TopologicalSpace (TargetDomain (I := I) Φ k) := targetDomTop (I := I) Φ k
  letI : ChartedSpace H (TargetDomain (I := I) Φ k) := targetDomCharted (I := I) Φ k
  letI : IsManifold I ∞ (TargetDomain (I := I) Φ k) := targetDomSmooth (I := I) Φ k
  letI : IsManifold I 1 (TargetDomain (I := I) Φ k) :=
    IsManifold.of_le (I := I) (M := TargetDomain (I := I) Φ k) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (TargetDomain (I := I) Φ k) := by
    change IsManifold I ∞ (TargetDomain (I := I) Φ k)
    infer_instance
  letI : SigmaCompactSpace (TargetDomain (I := I) Φ k) :=
    targetDomSigmaOf (I := I) Φ k hσtgt
  letI : T2Space (TargetDomain (I := I) Φ k) := targetDomT2 (I := I) Φ k
  exact
    DifferentialGeometry.PDE.RicciFlow.solutionOn_pullback (I := I)
      (solutionOn_restrictOpen (I := I) (X.term (subseq k)).S (targetOpen (I := I) Φ k))
      (sourceTargetDiff (I := I) Φ k)



omit [NeZero (Module.finrank ℝ E)] in
theorem isSolutionOn_sourceFlow
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq) (k : Nat)
    (hσsrc : letI : TopologicalSpace P.M := P.topology; IsSigmaCompact (Φ.source k))
    (hσtgt :
      letI : TopologicalSpace (X.term (subseq k)).M :=
        (X.term (subseq k)).topology
      IsSigmaCompact (Φ.target k)) :
    letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
    letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
    letI : T2Space (SourceDomain (I := I) Φ k) := sourceDomT2 (I := I) Φ k
    letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
    letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) :=
      sourceDomSigmaOf (I := I) Φ k hσsrc
    letI : IsManifold I 1 (SourceDomain (I := I) Φ k) :=
      IsManifold.of_le (I := I) (M := SourceDomain (I := I) Φ k) (n := (∞ : WithTop ℕ∞))
        (by decide : (1 : WithTop ℕ∞) ≤ ∞)
    letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (SourceDomain (I := I) Φ k) := by
      change IsManifold I ∞ (SourceDomain (I := I) Φ k)
      infer_instance
    IsSolutionOn (I := I) (sourceFlow (I := I) Φ k hσsrc hσtgt) := by
  letI : TopologicalSpace (X.term (subseq k)).M :=
    (X.term (subseq k)).topology
  letI : ChartedSpace H (X.term (subseq k)).M :=
    (X.term (subseq k)).charted
  letI : T2Space (X.term (subseq k)).M := (X.term (subseq k)).t2
  letI : IsManifold I ∞ (X.term (subseq k)).M :=
    (X.term (subseq k)).smooth
  letI : IsManifold I 1 (X.term (subseq k)).M :=
    IsManifold.of_le (I := I) (M := (X.term (subseq k)).M) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  letI : IsManifold I 2 (X.term (subseq k)).M :=
    IsManifold.of_le (I := I) (M := (X.term (subseq k)).M) (n := (∞ : WithTop ℕ∞))
      (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.term (subseq k)).M := by
    change IsManifold I ∞ (X.term (subseq k)).M
    infer_instance
  letI : SigmaCompactSpace (X.term (subseq k)).M :=
    (X.term (subseq k)).sigmaCompact
  letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
  letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
  letI : T2Space (SourceDomain (I := I) Φ k) := sourceDomT2 (I := I) Φ k
  letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
  letI : IsManifold I 1 (SourceDomain (I := I) Φ k) :=
    IsManifold.of_le (I := I) (M := SourceDomain (I := I) Φ k) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  letI : IsManifold I 2 (SourceDomain (I := I) Φ k) :=
    IsManifold.of_le (I := I) (M := SourceDomain (I := I) Φ k) (n := (∞ : WithTop ℕ∞))
      (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (SourceDomain (I := I) Φ k) := by
    change IsManifold I ∞ (SourceDomain (I := I) Φ k)
    infer_instance
  letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) :=
    sourceDomSigmaOf (I := I) Φ k hσsrc

  letI : SigmaCompactSpace ↥(targetOpen (I := I) Φ k) :=
    targetDomSigmaOf (I := I) Φ k hσtgt
  letI : T2Space ↥(targetOpen (I := I) Φ k) := targetDomT2 (I := I) Φ k
  letI : IsManifold I 1 ↥(targetOpen (I := I) Φ k) :=
    IsManifold.of_le (I := I) (M := ↥(targetOpen (I := I) Φ k)) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) ↥(targetOpen (I := I) Φ k) := by
    change IsManifold I ∞ ↥(targetOpen (I := I) Φ k)
    infer_instance

  letI : TopologicalSpace (TargetDomain (I := I) Φ k) := targetDomTop (I := I) Φ k
  letI : ChartedSpace H (TargetDomain (I := I) Φ k) := targetDomCharted (I := I) Φ k
  letI : T2Space (TargetDomain (I := I) Φ k) := targetDomT2 (I := I) Φ k
  letI : IsManifold I ∞ (TargetDomain (I := I) Φ k) := targetDomSmooth (I := I) Φ k
  letI : IsManifold I 1 (TargetDomain (I := I) Φ k) :=
    IsManifold.of_le (I := I) (M := TargetDomain (I := I) Φ k) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  letI : IsManifold I 2 (TargetDomain (I := I) Φ k) :=
    IsManifold.of_le (I := I) (M := TargetDomain (I := I) Φ k) (n := (∞ : WithTop ℕ∞))
      (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (TargetDomain (I := I) Φ k) := by
    change IsManifold I ∞ (TargetDomain (I := I) Φ k)
    infer_instance
  letI : SigmaCompactSpace (TargetDomain (I := I) Φ k) :=
    targetDomSigmaOf (I := I) Φ k hσtgt
  exact
    DifferentialGeometry.PDE.RicciFlow.isSolutionOn_pullback (I := I)
      (solutionOn_restrictOpen (I := I) (X.term (subseq k)).S (targetOpen (I := I) Φ k))
      (isSolutionOn_restrictOpen (I := I) (X.term (subseq k)).S
        (X.term (subseq k)).isSolution (targetOpen (I := I) Φ k))
      (sourceTargetDiff (I := I) Φ k)





omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem sourceFlow_metric_eq
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq) (k : Nat)
    (hσsrc : letI : TopologicalSpace P.M := P.topology; IsSigmaCompact (Φ.source k))
    (hσtgt :
      letI : TopologicalSpace (X.term (subseq k)).M :=
        (X.term (subseq k)).topology
      IsSigmaCompact (Φ.target k))
    (referenceMetric :
      letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
      letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
      letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
      Real -> SmoothRiemannianMetric I (SourceDomain (I := I) Φ k))
    (gInf : letI : TopologicalSpace P.M := P.topology;
      letI : ChartedSpace H P.M := P.charted; letI : IsManifold I ∞ P.M := P.smooth;
      Real -> SmoothRiemannianMetric I P.M)
    (t : Real) :
    letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
    letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
    letI : T2Space (SourceDomain (I := I) Φ k) := sourceDomT2 (I := I) Φ k
    letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
    letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) :=
      sourceDomSigmaOf (I := I) Φ k hσsrc
    letI : IsManifold I 1 (SourceDomain (I := I) Φ k) :=
      IsManifold.of_le (I := I) (M := SourceDomain (I := I) Φ k) (n := (∞ : WithTop ℕ∞))
        (by decide : (1 : WithTop ℕ∞) ≤ ∞)
    letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (SourceDomain (I := I) Φ k) := by
      change IsManifold I ∞ (SourceDomain (I := I) Φ k)
      infer_instance
    (sourceFlow (I := I) Φ k hσsrc hσtgt).family.metric t
      = (SourceDomainMetricData.ofRestrictPullback (I := I) hσsrc hσtgt referenceMetric gInf).pullbackMetric t := by
  rfl












section RestrictOpenEquiv

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]






omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem metricUniformEquivalentOn_restrictOpen
    (K : Set M) (gRef h : SmoothRiemannianMetric I M) (C : Real)
    (hEq : MetricUniformEquivalentOn (I := I) K gRef h C)
    (U : TopologicalSpace.Opens M) [SigmaCompactSpace U] [T2Space U]
    {V : Set U} (hV : ∀ x ∈ V, (x : M) ∈ K) :
    MetricUniformEquivalentOn (I := I) V
      (gRef.restrictOpen (I := I) U) (h.restrictOpen (I := I) U) C := by
  refine ⟨hEq.1, fun x hx v => ?_⟩
  simp only [SmoothRiemannianMetric.restrictOpen_inner]
  exact hEq.2 (x : M) (hV x hx) v




omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem metricUniformEquivalentOnWindow_restrictOpen
    (K : Set M) (β ψ : Real) (gRef : SmoothRiemannianMetric I M)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M) (B : Real -> Real)
    (hEq : MetricUniformEquivalentOnWindow (I := I) K β ψ gRef gSeq B)
    (U : TopologicalSpace.Opens M) [SigmaCompactSpace U] [T2Space U]
    {V : Set U} (hV : ∀ x ∈ V, (x : M) ∈ K) :
    MetricUniformEquivalentOnWindow (I := I) V β ψ
      (gRef.restrictOpen (I := I) U)
      (fun i t => (gSeq i t).restrictOpen (I := I) U) B := by
  intro i t ht
  exact metricUniformEquivalentOn_restrictOpen (I := I) K gRef (gSeq i t) (B t)
    (hEq i t ht) U hV

end RestrictOpenEquiv

end HCGCompactness
end DifferentialGeometry

end
