import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Connection.Producers
import DifferentialGeometry.Bundle.PartialMfderiv.FixedBase
import DifferentialGeometry.Geometry.Connection.TensorNabla.CotangentExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.BlackBox

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false



















noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Filter
open scoped Manifold ContDiff BigOperators Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [InnerProductSpace Real E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

variable {Idx : Type} [Fintype Idx] [DecidableEq Idx]
variable {u : Set M}






omit [FiniteDimensional ℝ E] [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem metricInner_mdiffAt
    (g : SmoothRiemannianMetric I M)
    {Y Z : Π b : M, TangentSpace I b}
    (hY : ContMDiff I (I.prod 𝓘(Real, E)) ∞
      (fun b : M => TotalSpace.mk' E (E := fun x : M => TangentSpace I x) b (Y b)))
    (hZ : ContMDiff I (I.prod 𝓘(Real, E)) ∞
      (fun b : M => TotalSpace.mk' E (E := fun x : M => TangentSpace I x) b (Z b)))
    (x : M) :
    MDifferentiableAt I 𝓘(Real, Real) (fun b : M => g.inner b (Y b) (Z b)) x := by
  have hg : ContMDiff I (I.prod 𝓘(Real, E →L[Real] E →L[Real] Real)) ∞
      (fun b : M => TotalSpace.mk' (E →L[Real] E →L[Real] Real)
        (E := fun x : M => TangentSpace I x →L[Real] TangentSpace I x →L[Real] Real) b
        (g.inner b)) := g.contMDiff
  have hgY : ContMDiff I (I.prod 𝓘(Real, E →L[Real] Real)) ∞
      (fun b : M => TotalSpace.mk' (E →L[Real] Real)
        (E := fun x : M => TangentSpace I x →L[Real] Real) b (g.inner b (Y b))) :=
    ContMDiff.clm_bundle_apply
      (E₁ := fun x : M => TangentSpace I x)
      (E₂ := fun x : M => TangentSpace I x →L[Real] Real)
      (b := fun b : M => b)
      (ϕ := fun b => g.inner b) (v := fun b => Y b) hg hY
  exact ((DifferentialGeometry.Integral.Connection.cotangentCov_pairing_contMDiff hgY hZ)
    x).mdifferentiableAt (by simp)








omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [Fintype Idx] [DecidableEq Idx] in
omit [SigmaCompactSpace M] in
theorem metricFrameComp_fixedBaseSwap_of_solution
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (a b : Idx)
    (hSmooth : ∀ t, t ∈ D.regular -> ∀ x : M, x ∈ u ->
      ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) 2
        (fun p : Real × M => (S.family.metric p.1).inner p.2 (frame a p.2) (frame b p.2))
        (t, x))
    (hFdiff : ∀ s, s ∈ D.carrier -> ∀ x : M, x ∈ u ->
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => (S.family.metric s).inner y (frame a y) (frame b y)) x)
    (hFtdiff : ∀ t, t ∈ D.regular -> ∀ x : M, x ∈ u ->
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => (-2 : Real) * ricciCompInFrame (I := I) S frame t y a b) x) :
    FixedBaseExtDerivTimeDerivativeOnRegular (I := I) D.carrier D.regular u
      (fun s y => (S.family.metric s).inner y (frame a y) (frame b y))
      (fun t y => (-2 : Real) * ricciCompInFrame (I := I) S frame t y a b) := by
  refine fixedBaseOnReg_of_timeDerivWithin (I := I)
    (D.regular_subset) (fun {t} ht => D.regular_mem_nhds ht)
    hSmooth hFdiff hFtdiff ?hTime

  intro t ht x
  have heq := hS.equation ⟨t, ht⟩ x (frame a x) (frame b x)
  simpa [ricciCompInFrame] using heq












omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [Fintype Idx] [DecidableEq Idx] in
omit [SigmaCompactSpace M] in
theorem metricCovDerivDeriv_of_solution
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hSmooth : ∀ a b : Idx, ∀ t, t ∈ D.regular -> ∀ x : M, x ∈ u ->
      ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) 2
        (fun p : Real × M => (S.family.metric p.1).inner p.2 (frame a p.2) (frame b p.2))
        (t, x))
    (hFdiff : ∀ a b : Idx, ∀ s, s ∈ D.carrier -> ∀ x : M, x ∈ u ->
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => (S.family.metric s).inner y (frame a y) (frame b y)) x)
    (hFtdiff : ∀ a b : Idx, ∀ t, t ∈ D.regular -> ∀ x : M, x ∈ u ->
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => ricciCompInFrame (I := I) S frame t y a b) x) :
    MetricCovDerivDerivativeComponentsInFrameOnLocal (I := I) S frame u
      (fun t x d a b => (-2 : Real) * ricciCovDerivCompInFrame (I := I) S frame t x d a b) := by
  intro t x hx d a b


  have h1 := (metricFrameComp_fixedBaseSwap_of_solution (I := I) S hS frame a b
    (hSmooth a b) (hFdiff a b)
    (fun t' ht' x' hx' => (mdifferentiableAt_const (c := (-2 : Real))).mul
      (hFtdiff a b t' ht' x' hx'))) (t : Real) t.2 x hx (frame d x)

  have h2 := hS.equation t x
    ((S.family.connection (t : Real) (frame a) x) (frame d x)) (frame b x)
  have h3 := hS.equation t x
    (frame a x) ((S.family.connection (t : Real) (frame b) x) (frame d x))
  have hcomb := (h1.sub h2).sub h3

  have hval :
      extDerivFun (I := I)
            (fun y : M => -2 * ricciCompInFrame (I := I) S frame (t : Real) y a b) x (frame d x) -
          (-2 : Real) * RicciAtFamily.toTensorField (I := I) S.ricciAt (t : Real) x
            ((S.family.connection (t : Real) (frame a) x) (frame d x)) (frame b x) -
          (-2 : Real) * RicciAtFamily.toTensorField (I := I) S.ricciAt (t : Real) x
            (frame a x) ((S.family.connection (t : Real) (frame b) x) (frame d x)) =
        (-2 : Real) * ricciCovDerivCompInFrame (I := I) S frame (t : Real) x d a b := by
    rw [extDerivFun_const_mul (I := I) (-2 : Real)
      (hFtdiff a b (t : Real) t.2 x hx)]
    simp only [ricciCovDerivCompInFrame, RicciAtFamily.toTensorField_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  show HasDerivWithinAt
      (fun s : Real => metricCovDerivCompInFrameAtBase (I := I) S frame (t : Real) s x d a b)
      ((-2 : Real) * ricciCovDerivCompInFrame (I := I) S frame (t : Real) x d a b)
      D.carrier (t : Real)
  exact hval ▸ hcomb






def connectionVariationBlackBox_of_solution
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hSmooth : ∀ a b : Idx, ∀ t, t ∈ D.regular -> ∀ x : M, x ∈ u ->
      ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) 2
        (fun p : Real × M => (S.family.metric p.1).inner p.2 (frame a p.2) (frame b p.2)) (t, x))
    (hFdiff : ∀ a b : Idx, ∀ s, s ∈ D.carrier -> ∀ x : M, x ∈ u ->
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => (S.family.metric s).inner y (frame a y) (frame b y)) x)
    (hFtdiff : ∀ a b : Idx, ∀ t, t ∈ D.regular -> ∀ x : M, x ∈ u ->
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => ricciCompInFrame (I := I) S frame t y a b) x) :
    ConnectionVariationBlackBoxInFrameOn (I := I) S frame u
      (fun t x d a b => ricciCovDerivCompInFrame (I := I) S frame t x d a b) where
  metricCovDerivDt := fun t x d a b => (-2 : Real) * ricciCovDerivCompInFrame (I := I) S frame t x d a b
  metricCovDerivDerivative :=
    metricCovDerivDeriv_of_solution (I := I) S hS frame hSmooth hFdiff hFtdiff
  metricCovDerivRicciFlow := fun _ _ _ _ _ => rfl





omit [DecidableEq Idx] in
omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem christoffelEvolution_of_solution
    [DecidableEq Idx]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (gInvDt : Real -> M -> Idx -> Idx -> Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u) (hu : IsOpen u)
    (hmetricFrame : MetricFrameTimeRegularityInFrameOnLocal (I := I) S gInv gInvDt frame u)
    (hSmooth : ∀ a b : Idx, ∀ t, t ∈ D.regular -> ∀ x : M, x ∈ u ->
      ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) 2
        (fun p : Real × M => (S.family.metric p.1).inner p.2 (frame a p.2) (frame b p.2)) (t, x))
    (hFdiff : ∀ a b : Idx, ∀ s, s ∈ D.carrier -> ∀ x : M, x ∈ u ->
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => (S.family.metric s).inner y (frame a y) (frame b y)) x)
    (hFtdiff : ∀ a b : Idx, ∀ t, t ∈ D.regular -> ∀ x : M, x ∈ u ->
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => ricciCompInFrame (I := I) S frame t y a b) x) :
    ChristoffelEvolutionEquationInFrameOn (I := I) S gInv frame hframe
      (fun t x d a b => ricciCovDerivCompInFrame (I := I) S frame t x d a b) :=
  christoffelEvolution_of_blackBox (I := I) S hS gInv gInvDt frame hframe hu
    (fun t x d a b => ricciCovDerivCompInFrame (I := I) S frame t x d a b)
    hmetricFrame
    (connectionVariationBlackBox_of_solution (I := I) S hS frame hSmooth hFdiff hFtdiff)

end DifferentialGeometry.PDE.RicciFlow
