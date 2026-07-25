import DifferentialGeometry.Geometry.Curvature.Metric
import DifferentialGeometry.Geometry.Comparison.Volume.BallVolume
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.InjectivityRadius

set_option autoImplicit false
set_option linter.style.longLine false










noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}

section FixedMetric

variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]




noncomputable def curvCovDerivStep
    (g : SmoothRiemannianMetric I M) (a : Nat)
    (A :
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (a + 4)) :
    Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (a + 5) := by
  haveI : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  haveI : IsManifold I 2 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    change IsManifold I ∞ M
    infer_instance
  let cov := DifferentialGeometry.Integral.Connection.metricCov (I := I) (M := M) g
  let hcov := DifferentialGeometry.Integral.Connection.metricCov_smooth (I := I) (M := M) g
  let hreg :=
    Tensor0SBundle.totalNabla0S_reg (E := E) (H := H)
      (I := I) (M := M) (a + 4) cov hcov A
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, cov, hcov, hreg]
    using
      Tensor0SBundle.totalNabla0S (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (a + 4) cov A hreg



noncomputable def curvCovDeriv
    (g : SmoothRiemannianMetric I M) :
    (k : Nat) ->
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (k + 4) :=
  Nat.rec
    (motive := fun k : Nat =>
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (k + 4))
    (by
      haveI : IsManifold I 1 M :=
        IsManifold.of_le (I := I) (M := M) (n := ∞)
          (by decide : (1 : WithTop ℕ∞) ≤ ∞)
      haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
        change IsManifold I ∞ M
        infer_instance
      exact DifferentialGeometry.Integral.Connection.metricRm04 (I := I) (M := M) g)
    (fun k A =>
      by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          curvCovDerivStep (I := I) g k A)


noncomputable def curvDerivNormSq
    (k : Nat) (g : SmoothRiemannianMetric I M) (x : M) : Real :=
  Tensor0SBundle.normSq0S (I := I) g x (k + 4)
    (curvCovDeriv (I := I) (M := M) g k x)


noncomputable def curvDerivNorm
    (k : Nat) (g : SmoothRiemannianMetric I M) (x : M) : Real :=
  Real.sqrt (curvDerivNormSq (I := I) (M := M) k g x)

end FixedMetric


def HasCurvDerivBound
    (X : PointedRiemannianManifold.{u, uE, uH} (I := I)) (k : Nat)
    (C : Real) : Prop :=
  letI : TopologicalSpace X.M := X.topology
  letI : ChartedSpace H X.M := X.charted
  letI : IsManifold I ∞ X.M := X.smooth
  letI : SigmaCompactSpace X.M := X.sigmaCompact
  letI : T2Space X.M := X.t2
  forall x : X.M, curvDerivNorm (I := I) k X.metric x <= C



theorem rm04Bound_of_curv0
    (X : PointedRiemannianManifold.{u, uE, uH} (I := I)) {C : Real}
    (hX : HasCurvDerivBound (I := I) X 0 C) :
    letI : TopologicalSpace X.M := X.topology
    letI : ChartedSpace H X.M := X.charted
    letI : IsManifold I ∞ X.M := X.smooth
    letI : SigmaCompactSpace X.M := X.sigmaCompact
    letI : T2Space X.M := X.t2
    Geometry.Riemannian.VolumeComparison.Rm04GlobalBound
      (I := I) (M := X.M) X.metric C := by
  letI : TopologicalSpace X.M := X.topology
  letI : ChartedSpace H X.M := X.charted
  letI : IsManifold I ∞ X.M := X.smooth
  letI : SigmaCompactSpace X.M := X.sigmaCompact
  letI : T2Space X.M := X.t2
  intro x
  simpa [Geometry.Riemannian.VolumeComparison.Rm04GlobalBound,
    HasCurvDerivBound, curvDerivNorm, curvDerivNormSq, curvCovDeriv,
    DifferentialGeometry.Integral.Connection.metricRm04_apply] using hX x



structure BoundedGeometry
    (X : PointedRiemannianManifold.{u, uE, uH} (I := I)) where
  C : Nat -> Real
  nonneg : forall k : Nat, 0 <= C k
  bound : forall k : Nat, HasCurvDerivBound (I := I) X k (C k)



theorem rm04Bound_of_geom
    {X : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    (hX : BoundedGeometry (I := I) X) :
    letI : TopologicalSpace X.M := X.topology
    letI : ChartedSpace H X.M := X.charted
    letI : IsManifold I ∞ X.M := X.smooth
    letI : SigmaCompactSpace X.M := X.sigmaCompact
    letI : T2Space X.M := X.t2
    Geometry.Riemannian.VolumeComparison.Rm04GlobalBound
      (I := I) (M := X.M) X.metric (hX.C 0) :=
  rm04Bound_of_curv0 (I := I) X (hX.bound 0)



structure SeqBoundedGeometry
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) where
  C : Nat -> Real
  nonneg : forall k : Nat, 0 <= C k
  bound : forall i k : Nat, HasCurvDerivBound (I := I) (X.obj i) k (C k)

namespace SeqBoundedGeometry


def subseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hX : SeqBoundedGeometry (I := I) X) (f : Nat -> Nat) :
    SeqBoundedGeometry (I := I) (X.subseq f) where
  C := hX.C
  nonneg := hX.nonneg
  bound := by
    intro i k
    simpa [PointedRiemannianSeq.subseq] using hX.bound (f i) k

end SeqBoundedGeometry



theorem rm04Bound_of_seq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hX : SeqBoundedGeometry (I := I) X) (i : Nat) :
    letI : TopologicalSpace (X.obj i).M := (X.obj i).topology
    letI : ChartedSpace H (X.obj i).M := (X.obj i).charted
    letI : IsManifold I ∞ (X.obj i).M := (X.obj i).smooth
    letI : SigmaCompactSpace (X.obj i).M := (X.obj i).sigmaCompact
    letI : T2Space (X.obj i).M := (X.obj i).t2
    Geometry.Riemannian.VolumeComparison.Rm04GlobalBound
      (I := I) (M := (X.obj i).M) (X.obj i).metric (hX.C 0) :=
  rm04Bound_of_curv0 (I := I) (X.obj i) (hX.bound i 0)


def HasSpacetimeCurvBound
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) (C : Real) : Prop :=
  forall t : Real, t ∈ D.carrier ->
    forall x : F.M, F.rmNormSq (I := I) t x <= C




def HasSpacetimeCurvDerivBound
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) (k : Nat) (C : Real) : Prop :=
  letI : TopologicalSpace F.M := F.topology
  letI : ChartedSpace H F.M := F.charted
  letI : IsManifold I ∞ F.M := F.smooth
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) F.M := by
    change IsManifold I ∞ F.M
    infer_instance
  letI : SigmaCompactSpace F.M := F.sigmaCompact
  letI : T2Space F.M := F.t2
  forall t : Real, t ∈ D.carrier ->
    forall x : F.M, curvDerivNorm (I := I) k (F.S.family.metric t) x <= C


structure SpacetimeCurvBound
    (X : PointedFlowSeq.{u, uE, uH} (I := I)) where
  C : Real
  nonneg : 0 <= C
  bound : forall i : Nat, HasSpacetimeCurvBound (I := I) (X.term i) C





structure FlowDerivBounds
    (X : PointedFlowSeq.{u, uE, uH} (I := I)) where
  C : Nat -> Real
  nonneg : forall k : Nat, 0 <= C k
  bound : forall i k : Nat, HasSpacetimeCurvDerivBound (I := I) (X.term i) k (C k)






structure FlowDerivativeInput
    (X : PointedFlowSeq.{u, uE, uH} (I := I)) where
  spacetime : FlowDerivBounds (I := I) X
  at_zero_geom : SeqBoundedGeometry (I := I) (X.atZero (I := I))

end HCGCompactness
end DifferentialGeometry
