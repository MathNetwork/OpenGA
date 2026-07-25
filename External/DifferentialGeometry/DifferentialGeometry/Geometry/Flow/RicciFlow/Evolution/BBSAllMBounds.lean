import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MovingShiProducer

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle
open DifferentialGeometry.Integral.Connection
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M]
variable [SigmaCompactSpace M] [T2Space M] [CompactSpace M]
  [BoundarylessManifold I M]




theorem bbsAllMBounds
    {alpha omega : Real} {hAlphaOmega : alpha < omega}
    (S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega hAlphaOmega))
    (hS : IsSolutionOn (I := I) S)
    (hdim : Module.finrank Real E = 3)
    (Rm04 : Real -> Tensor04Section (I := I) (M := M))
    (hRm : forall t : RealTimeInterval.FlowTime
      (RealTimeInterval.closedOpen alpha omega hAlphaOmega),
      Rm04RealizesConnection (I := I)
        (S.family.metric (t : Real)) (S.family.connection (t : Real)) (Rm04 (t : Real)))
    (hbound : exists K : Real, forall (t : Real) (x : M),
      alpha <= t -> t < omega ->
        normSq0S (I := I) (S.base.metric t) x 4 (Rm04 t x) <= K) :
    forall m : Nat, exists C : Real, forall (t : Real) (x : M),
      (alpha + omega) / 2 <= t -> t < omega ->
        nablaKRm04NormSqIntrinsic (I := I) S m t x <= C := by
  intro m
  have hBeta : (alpha + omega) / 2 ∈ Set.Ioo alpha omega := by
    constructor <;> linarith
  have hRmRaw : ∀ t ∈ Set.Ico alpha omega,
      Rm04RealizesConnection (I := I) (S.base.metric t)
        (metricCov (I := I) (M := M) (S.base.metric t)) (Rm04 t) := by
    intro t ht
    have h := hRm ⟨t, ht⟩
    simpa [SolutionOn.family, SolutionFamily.connection, metricCov] using h
  have hboundCan := rm04_bound_can (I := I) Rm04 hRmRaw hbound
  obtain ⟨C, _hC, hC⟩ := movingRmBoundSol (I := I)
    ((alpha + omega) / 2) hBeta m hdim hS hboundCan
  refine ⟨C, ?_⟩
  intro t x htBeta htOmega
  exact hC t ⟨htBeta, htOmega⟩ m le_rfl t ⟨htBeta, le_rfl⟩ x

end DifferentialGeometry.PDE.RicciFlow
