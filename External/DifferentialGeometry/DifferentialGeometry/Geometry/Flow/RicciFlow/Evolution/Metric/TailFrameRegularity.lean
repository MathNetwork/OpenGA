import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.SolutionTimeRestrict
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Connection.MetricCovDerivProducer
import DifferentialGeometry.Geometry.Curvature.MetricLeviCivitaReconcile

set_option autoImplicit false









noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Filter Set
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Integral.Connection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M]
variable [SigmaCompactSpace M] [T2Space M]
variable [I.Boundaryless] [BoundarylessManifold I M]

omit [I.Boundaryless] in


omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem ricciFrame_mdiffAt
    {Idx : Type} [Fintype Idx]
    (g : SmoothRiemannianMetric I M)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    {u : Set M}
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u) (i j : Idx) :
    MDifferentiableAt I (modelWithCornersSelf Real Real)
      (fun y : M => metricRicciAt (I := I) g y
        (vec2 (I := I) (frame i y) (frame j y))) x := by
  obtain ⟨sec, hsec⟩ := hframe.exists_contMDiffSection_eqOn_nhd hu hx
  have hscalar :
      ContMDiff I (modelWithCornersSelf Real Real) ∞
        (fun y : M => ricciTensor (I := I) g y (sec i y) (sec j y)) :=
    ricciTensor_pairing_contMDiff (I := I) g (sec i).contMDiff (sec j).contMDiff
  have hsmooth :
      ContMDiffAt I (modelWithCornersSelf Real Real) ∞
        (fun y : M => metricRicciAt (I := I) g y
          (vec2 (I := I) (frame i y) (frame j y))) x := by
    refine (hscalar x).congr_of_eventuallyEq ?_
    filter_upwards [hsec] with y hy
    rw [hy i, hy j, metricRicciAt_apply_eq_ricciTensor]
  exact hsmooth.mdifferentiableAt (by simp)



omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem tailFrameSpaceReg
    {Idx : Type} [Fintype Idx] [DecidableEq Idx]
    {u : Set M}
    {alpha t0 omega : Real} {hAlphaOmega : alpha < omega}
    {S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega hAlphaOmega)}
    (hS : IsSolutionOn (I := I) S)
    (hAlphaT0 : alpha < t0) (hT0Omega : t0 < omega)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u)
    (hu : IsOpen u) :
    MetricFrameSpacetimeRegularityInFrameOnLocal
      (I := I)
      (S.timeRestrict (RealTimeInterval.closedOpen t0 omega hT0Omega))
      (localFrameInv (E := E) (I := I)
        (S.timeRestrict (RealTimeInterval.closedOpen t0 omega hT0Omega)) frame hframe)
      (localFrameInvDt (E := E) (I := I)
        (S.timeRestrict (RealTimeInterval.closedOpen t0 omega hT0Omega)) frame hframe)
      frame u := by
  let D' := RealTimeInterval.closedOpen t0 omega hT0Omega
  let S' := S.timeRestrict D'
  have hS' : IsSolutionOn (I := I) S' := by
    simpa [S', D'] using isSoln_tailRestrict (I := I) hS hAlphaT0 hT0Omega
  have htime :
      MetricFrameTimeRegularityInFrameOnLocal
        (I := I) S'
        (localFrameInv (E := E) (I := I) S' frame hframe)
        (localFrameInvDt (E := E) (I := I) S' frame hframe) frame u := by
    simpa [S', D'] using
      tailFrameTimeReg (I := I) hS hAlphaT0 hT0Omega frame hframe
  have hSmooth : forall a b : Idx, forall t, t ∈ D'.regular -> forall x : M, x ∈ u ->
      ContMDiffAt ((modelWithCornersSelf Real Real).prod I)
        (modelWithCornersSelf Real Real) 2
        (fun p : Real × M =>
          (S'.family.metric p.1).inner p.2 (frame a p.2) (frame b p.2)) (t, x) := by
    intro a b t ht x hx
    have hcomp := hS'.smoothMetric.frameCompSmooth (Idx := Idx) frame hframe a b
    exact (hcomp.contMDiffAt ((D'.regular_isOpen.prod hu).mem_nhds ⟨ht, hx⟩)).of_le
      (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  have hFdiff : forall a b : Idx, forall s, s ∈ D'.carrier -> forall x : M, x ∈ u ->
      MDifferentiableAt I (modelWithCornersSelf Real Real)
        (fun y : M => (S'.family.metric s).inner y (frame a y) (frame b y)) x := by
    intro a b s hs x hx
    have hsOld : s ∈ (RealTimeInterval.closedOpen alpha omega hAlphaOmega).regular :=
      ⟨lt_of_lt_of_le hAlphaT0 hs.1, hs.2⟩
    have hslice :
        ContMDiffOn I ((modelWithCornersSelf Real Real).prod I) ∞
          (fun y : M => (s, y)) u :=
      (contMDiffOn_const (c := s)).prodMk contMDiffOn_id
    have hcomp :=
      (hS.smoothMetric.frameCompSmooth (Idx := Idx) frame hframe a b).comp hslice
        (fun y hy => ⟨hsOld, hy⟩)
    have hdiff := (hcomp.contMDiffAt (hu.mem_nhds hx)).mdifferentiableAt (by simp)
    simpa [Function.comp_def, S', SolutionOn.timeRestrict, SolutionOn.family] using hdiff
  have hFtdiff : forall a b : Idx, forall t, t ∈ D'.regular -> forall x : M, x ∈ u ->
      MDifferentiableAt I (modelWithCornersSelf Real Real)
        (fun y : M => ricciCompInFrame (I := I) S' frame t y a b) x := by
    intro a b t _ht x hx
    simpa [ricciCompInFrame, SolutionOn.ricciAt, SolutionFamily.ricciAt] using
      ricciFrame_mdiffAt (I := I) (g := S'.family.metric t) frame hframe hu hx a b
  have hspace : forall a b : Idx,
      FixedBaseExtDerivTimeDerivativeOnRegular (I := I) D'.carrier D'.regular u
        (fun s y => (S'.family.metric s).inner y (frame a y) (frame b y))
        (fun t y => (-2 : Real) * ricciCompInFrame (I := I) S' frame t y a b) := by
    intro a b
    exact metricFrameComp_fixedBaseSwap_of_solution (I := I) S' hS' frame a b
      (hSmooth a b) (hFdiff a b)
      (fun t ht x hx => (mdifferentiableAt_const (c := (-2 : Real))).mul
        (hFtdiff a b t ht x hx))
  have hmetricSmooth : forall i j : Idx,
      ContMDiffOn ((modelWithCornersSelf Real Real).prod I)
        (modelWithCornersSelf Real Real) ∞
        (fun p : Real × M => metricCompInFrame (I := I) S' frame p.1 p.2 i j)
        (D'.carrier ×ˢ u) := by
    intro i j
    have hsub : D'.carrier ×ˢ u ⊆
        (RealTimeInterval.closedOpen alpha omega hAlphaOmega).regular ×ˢ u := by
      intro p hp
      exact ⟨⟨lt_of_lt_of_le hAlphaT0 hp.1.1, hp.1.2⟩, hp.2⟩
    have hcomp :=
      (hS.smoothMetric.frameCompSmooth (Idx := Idx) frame hframe i j).mono hsub
    simpa [metricCompInFrame, S', D', SolutionOn.timeRestrict, SolutionOn.family] using hcomp
  refine
    { toMetricFrameTimeRegularityInFrameOnLocal := htime
      frameMetricSpacetimeSmooth := hmetricSmooth
      frameMetricExtDerivTimeDerivative := ?_ }
  intro t x hx d a b
  have hderiv := hspace a b (t : Real) t.2 x hx (frame d x)
  have heq :
      extDerivFun (I := I)
          (fun y : M => (-2 : Real) * ricciCompInFrame (I := I) S' frame (t : Real) y a b)
          x (frame d x) =
        (-2 : Real) * extDerivFun (I := I)
          (fun y : M => ricciCompInFrame (I := I) S' frame (t : Real) y a b)
          x (frame d x) := by
    rw [extDerivFun_const_mul (I := I) (-2 : Real)
      (hFtdiff a b (t : Real) t.2 x hx)]
    rfl
  exact hderiv.congr_deriv heq

end DifferentialGeometry.PDE.RicciFlow
