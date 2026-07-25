import Mathlib.Analysis.Calculus.ContDiff.Operations
import DifferentialGeometry.Geometry.Flow.RicciFlow.Basic
import DifferentialGeometry.Geometry.Connection.MetricCompatibility
import DifferentialGeometry.Geometry.Coordinates.Christoffel

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedFintypeInType false










noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff BigOperators Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

section Components

variable {Idx : Type*} [Fintype Idx]
variable {u : Set M}


def metricCompInFrame
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (i j : Idx) : Real :=
  (S.family.metric t).inner x (frame i x) (frame j x)

omit [Fintype Idx] in
omit [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem metricCompInFrame_apply
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (i j : Idx) :
    metricCompInFrame (I := I) S frame t x i j =
      (S.family.metric t).inner x (frame i x) (frame j x) := by
  rfl


omit [Fintype Idx] in
omit [SigmaCompactSpace M] in
theorem metricCompInFrame_hasDerivWithinAt
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x : M) (i j : Idx) :
    HasDerivWithinAt
      (fun s : Real => metricCompInFrame (I := I) S frame s x i j)
      ((-2 : Real) * ricciCompInFrame (I := I) S frame (t : Real) x i j)
      D.carrier
      (t : Real) := by
  simpa [metricCompInFrame, ricciCompInFrame] using
    metric_derivWithin_eq_neg_two_ricci (I := I) S hS t x
      (frame i x) (frame j x)



omit [SigmaCompactSpace M] in
theorem coordMetricSmooth
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (x₀ : M) (i j : CoordinateIdx (𝕜 := Real) E) :
    ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
      (fun p : Real × M =>
        metricCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀)
          p.1 p.2 i j)
      (D.regular ×ˢ coordinateFrameSet (I := I) x₀) := by
  simpa [metricCompInFrame] using
    hS.smoothMetric.frameCompSmooth
      (coordinateFrameAt (I := I) x₀)
      (coordinateFrameAt_isLocalFrame (I := I) x₀) i j



omit [SigmaCompactSpace M] in
theorem coordMetricSmoothAt
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (x₀ : M) (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M)
    (hx : x ∈ coordinateFrameSet (I := I) x₀)
    (i j : CoordinateIdx (𝕜 := Real) E) :
    ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
      (fun p : Real × M =>
        metricCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀)
          p.1 p.2 i j)
      ((t : Real), x) := by
  exact
    (coordMetricSmooth (I := I) S hS x₀ i j).contMDiffAt
      (prod_mem_nhds (D.regular_isOpen.mem_nhds t.2)
        ((coordinateFrameSet_open (I := I) x₀).mem_nhds hx))








omit [SigmaCompactSpace M] in
theorem coordMetricContOn
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (x₀ : M) (i j : CoordinateIdx (𝕜 := Real) E) :
    ContinuousOn
      (fun p : Real × M =>
        metricCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀) p.1 p.2 i j)
      (D.carrier ×ˢ coordinateFrameSet (I := I) x₀) := by
  classical
  rw [continuousOn_iff_continuous_restrict]
  set s : Set (Real × M) :=
    D.carrier ×ˢ coordinateFrameSet (I := I) x₀ with hs
  have hτ : Continuous (fun q : ↥s => ((q : Real × M)).1) :=
    continuous_fst.comp continuous_subtype_val
  have hb : Continuous (fun q : ↥s => ((q : Real × M)).2) :=
    continuous_snd.comp continuous_subtype_val
  have hτK : ∀ q : ↥s, ((q : Real × M)).1 ∈ D.carrier := fun q => q.2.1
  have hv : ∀ k : Fin 2,
      Continuous (fun q : ↥s =>
        TotalSpace.mk' E (E := fun y : M => TangentSpace I y)
          ((q : Real × M)).2
          (coordinateFrameAt (I := I) x₀ (if k = 0 then i else j) ((q : Real × M)).2)) := by
    intro k
    rw [continuous_iff_continuousAt]
    intro q
    have hframe := (coordinateFrameAt_isLocalFrame (I := I) x₀).contMDiffAt
      (coordinateFrameSet_open (I := I) x₀) q.2.2 (if k = 0 then i else j)
    exact ContinuousAt.comp
      (g := fun y : M => TotalSpace.mk' E (E := fun y : M => TangentSpace I y) y
        (coordinateFrameAt (I := I) x₀ (if k = 0 then i else j) y))
      hframe.continuousAt hb.continuousAt
  have heval :=
    (hS.smoothMetric.metricTensor_cont).eval_continuous (P := ↥s) hτ hτK hb hv
  refine heval.congr (fun q => ?_)
  rw [Tensor0SBundle.metricTensorField_apply]
  simp [metricCompInFrame]





@[deprecated "use InvMetricLocal on the actual local frame domain" (since := "2026-05-22")]
def InverseMetricComponentsInFrameOn [DecidableEq Idx]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) : Prop :=
  forall t x i j,
    (∑ k : Idx,
        gInv t x i k * metricCompInFrame (I := I) S frame t x k j) =
        (if i = j then 1 else 0) ∧
      (∑ k : Idx,
        metricCompInFrame (I := I) S frame t x i k * gInv t x k j) =
        (if i = j then 1 else 0)


def InvMetricLocal [DecidableEq Idx]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (u : Set M) : Prop :=
  forall t x, x ∈ u -> forall i j,
    (∑ k : Idx,
        gInv t x i k * metricCompInFrame (I := I) S frame t x k j) =
        (if i = j then 1 else 0) ∧
      (∑ k : Idx,
        metricCompInFrame (I := I) S frame t x i k * gInv t x k j) =
        (if i = j then 1 else 0)






@[deprecated "use pointwise inverse symmetry or derive it from MetricInverseInBasis_gen" (since := "2026-05-22")]
def SymmetricInverseMetricComponentsInFrameOn
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx) : Prop :=
  forall t x i j, gInv t x i j = gInv t x j i





omit [SigmaCompactSpace M] [T2Space M] in
@[deprecated "derive pointwise symmetry from MetricInverseInBasis_gen or InvMetricLocal" (since := "2026-05-22")]
theorem gInv_symm [DecidableEq Idx]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hinv : InverseMetricComponentsInFrameOn (I := I) S gInv frame) :
    SymmetricInverseMetricComponentsInFrameOn gInv := by
  intro t x i j
  exact DifferentialGeometry.Integral.Connection.invComp_symm
    (I := I) (g := S.family.metric t)
    (gInv := fun x i j => gInv t x i j) frame
    (by
      intro y a b
      simpa [metricCompInFrame] using hinv t y a b)
    x i j


def InverseMetricDerivativeComponentsOn
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (gInvDt : Real -> M -> Idx -> Idx -> Real) : Prop :=
  forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M) (i j : Idx),
    HasDerivWithinAt
      (fun s : Real => gInv s x i j)
      (gInvDt (t : Real) x i j)
      D.carrier
      (t : Real)










structure MetricFrameTimeRegularityInFrameOnLocal
    [DecidableEq Idx]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (gInvDt : Real -> M -> Idx -> Idx -> Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (u : Set M) : Prop where
  metricSmooth :
    forall x : M, x ∈ u -> forall i j : Idx,
      ContDiffOn Real ∞
        (fun t : Real => metricCompInFrame (I := I) S frame t x i j)
        D.carrier


  nondegenerateGram :
    InvMetricLocal (I := I) S gInv frame u
  inverseMetricDerivative :
    InverseMetricDerivativeComponentsOn (D := D) gInv gInvDt
  uniqueTimeDerivatives :
    forall t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D,
      UniqueDiffWithinAt Real D.carrier (t : Real)







structure MetricFrameSpacetimeRegularityInFrameOnLocal
    [DecidableEq Idx]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (gInvDt : Real -> M -> Idx -> Idx -> Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (u : Set M) : Prop extends
      MetricFrameTimeRegularityInFrameOnLocal
        (I := I) S gInv gInvDt frame u where
  frameMetricSpacetimeSmooth :
    forall i j : Idx,
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => metricCompInFrame (I := I) S frame p.1 p.2 i j)
        (D.carrier ×ˢ u)
  frameMetricExtDerivTimeDerivative :
    forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M), x ∈ u ->
      forall d a b : Idx,
        HasDerivWithinAt
          (fun s : Real =>
            extDerivFun (I := I)
              (fun y : M => metricCompInFrame (I := I) S frame s y a b)
              x (frame d x))
          ((-2 : Real) *
            extDerivFun (I := I)
              (fun y : M => ricciCompInFrame (I := I) S frame (t : Real) y a b)
              x (frame d x))
          D.carrier
          (t : Real)


end Components

end DifferentialGeometry.PDE.RicciFlow
