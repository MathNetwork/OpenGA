import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.SolutionTimeRestrict
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Connection.MetricCovDerivProducer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Metric.TailFrameRegularity
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
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private theorem ricciFrameDiffAt
    {Idx : Type} [Fintype Idx]
    (g : SmoothRiemannianMetric I M)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    {u : Set M}
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u) (i j : Idx) :
    MDifferentiableAt I 𝓘(Real, Real)
      (fun y : M => metricRicciAt (I := I) g y
        (vec2 (I := I) (frame i y) (frame j y))) x := by
  obtain ⟨sec, hsec⟩ := hframe.exists_contMDiffSection_eqOn_nhd hu hx
  have hscalar :
      ContMDiff I 𝓘(Real, Real) ∞
        (fun y : M => ricciTensor (I := I) g y (sec i y) (sec j y)) :=
    ricciTensor_pairing_contMDiff (I := I) g (sec i).contMDiff (sec j).contMDiff
  have hsmooth :
      ContMDiffAt I 𝓘(Real, Real) ∞
        (fun y : M => metricRicciAt (I := I) g y
          (vec2 (I := I) (frame i y) (frame j y))) x := by
    refine (hscalar x).congr_of_eventuallyEq ?_
    filter_upwards [hsec] with y hy
    rw [hy i, hy j, metricRicciAt_apply_eq_ricciTensor]
  exact hsmooth.mdifferentiableAt (by simp)





omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem tailChristoffel
    {Idx : Type} [Fintype Idx] [DecidableEq Idx]
    {u : Set M}
    {alpha t₀ omega : Real} {hαω : alpha < omega}
    {S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega hαω)}
    (hS : IsSolutionOn (I := I) S)
    (hαt₀ : alpha < t₀) (ht₀ω : t₀ < omega)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u)
    (hu : IsOpen u) :
    ∃ hframe1 : IsLocalFrameOn I E (1 : WithTop ℕ∞) frame u,
      ChristoffelEvolutionEquationInFrameOn (I := I)
        (S.timeRestrict (RealTimeInterval.closedOpen t₀ omega ht₀ω))
        (localFrameInv (E := E) (I := I)
          (S.timeRestrict (RealTimeInterval.closedOpen t₀ omega ht₀ω)) frame hframe)
        frame hframe1
        (fun (t : Real) (x : M) (d a b : Idx) => ricciCovDerivCompInFrame (I := I)
          (S.timeRestrict (RealTimeInterval.closedOpen t₀ omega ht₀ω))
          frame t x d a b) := by
  let hframe1 : IsLocalFrameOn I E (1 : WithTop ℕ∞) frame u :=
    { linearIndependent := hframe.linearIndependent
      generating := hframe.generating
      contMDiffOn := fun i => (hframe.contMDiffOn i).of_le
        (by decide : (1 : WithTop ℕ∞) ≤ ∞) }
  refine ⟨hframe1, ?_⟩
  let D' := RealTimeInterval.closedOpen t₀ omega ht₀ω
  let S' := S.timeRestrict D'
  have hS' : IsSolutionOn (I := I) S' := by
    simpa [S', D'] using isSoln_tailRestrict (I := I) hS hαt₀ ht₀ω
  have htime :
      MetricFrameTimeRegularityInFrameOnLocal
        (I := I) S'
        (localFrameInv (E := E) (I := I) S' frame hframe)
        (localFrameInvDt (E := E) (I := I) S' frame hframe) frame u := by
    simpa [S', D'] using tailFrameTimeReg (I := I) hS hαt₀ ht₀ω frame hframe
  have hSmooth : ∀ a b : Idx, ∀ t, t ∈ D'.regular -> ∀ x : M, x ∈ u ->
      ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) 2
        (fun p : Real × M =>
          (S'.family.metric p.1).inner p.2 (frame a p.2) (frame b p.2)) (t, x) := by
    intro a b t ht x hx
    have hcomp := hS'.smoothMetric.frameCompSmooth (Idx := Idx) frame hframe a b
    have hmem : (t, x) ∈ D'.regular ×ˢ u := ⟨ht, hx⟩
    have hn : D'.regular ×ˢ u ∈ 𝓝 (t, x) :=
      (D'.regular_isOpen.prod hu).mem_nhds hmem
    have hat := hcomp.contMDiffAt hn
    exact hat.of_le (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  have hFdiff : ∀ a b : Idx, ∀ s, s ∈ D'.carrier -> ∀ x : M, x ∈ u ->
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => (S'.family.metric s).inner y (frame a y) (frame b y)) x := by
    intro a b s hs x hx
    have hsOld : s ∈ (RealTimeInterval.closedOpen alpha omega hαω).regular :=
      ⟨lt_of_lt_of_le hαt₀ hs.1, hs.2⟩
    have hslice :
        ContMDiffOn I (𝓘(Real, Real).prod I) ∞
          (fun y : M => (s, y)) u :=
      (contMDiffOn_const (c := s)).prodMk contMDiffOn_id
    have hcomp :
        ContMDiffOn I 𝓘(Real, Real) ∞
          ((fun p : Real × M =>
              (S.family.metric p.1).inner p.2 (frame a p.2) (frame b p.2)) ∘
            fun y : M => (s, y)) u :=
      (hS.smoothMetric.frameCompSmooth (Idx := Idx) frame hframe a b).comp hslice
        (fun y hy => ⟨hsOld, hy⟩)
    have hdiff := (hcomp.contMDiffAt (hu.mem_nhds hx)).mdifferentiableAt (by simp)
    simpa [Function.comp_def, S', SolutionOn.timeRestrict, SolutionOn.family] using hdiff
  have hFtdiff : ∀ a b : Idx, ∀ t, t ∈ D'.regular -> ∀ x : M, x ∈ u ->
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => ricciCompInFrame (I := I) S' frame t y a b) x := by
    intro a b t _ht x hx
    simpa [ricciCompInFrame, SolutionOn.ricciAt, SolutionFamily.ricciAt] using
      ricciFrameDiffAt (I := I) (g := S'.family.metric t)
        frame hframe hu hx a b
  simpa [S', D'] using
    christoffelEvolution_of_solution (I := I) (Idx := Idx) S' hS'
      (localFrameInv (E := E) (I := I) S' frame hframe)
      (localFrameInvDt (E := E) (I := I) S' frame hframe)
      frame hframe1 hu htime hSmooth hFdiff hFtdiff



omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem tailChristoffelReg
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
    ∃ hframe1 : IsLocalFrameOn I E (1 : WithTop ℕ∞) frame u,
      MetricFrameSpacetimeRegularityInFrameOnLocal
          (I := I)
          (S.timeRestrict (RealTimeInterval.closedOpen t0 omega hT0Omega))
          (localFrameInv (E := E) (I := I)
            (S.timeRestrict (RealTimeInterval.closedOpen t0 omega hT0Omega)) frame hframe)
          (localFrameInvDt (E := E) (I := I)
            (S.timeRestrict (RealTimeInterval.closedOpen t0 omega hT0Omega)) frame hframe)
          frame u ∧
        ChristoffelEvolutionEquationInFrameOn (I := I)
          (S.timeRestrict (RealTimeInterval.closedOpen t0 omega hT0Omega))
          (localFrameInv (E := E) (I := I)
            (S.timeRestrict (RealTimeInterval.closedOpen t0 omega hT0Omega)) frame hframe)
          frame hframe1
          (fun (t : Real) (x : M) (d a b : Idx) =>
            ricciCovDerivCompInFrame (I := I)
              (S.timeRestrict (RealTimeInterval.closedOpen t0 omega hT0Omega))
              frame t x d a b) := by
  obtain ⟨hframe1, hchr⟩ :=
    tailChristoffel (I := I) (Idx := Idx) hS hAlphaT0 hT0Omega frame hframe hu
  refine ⟨hframe1, ?_, hchr⟩
  exact tailFrameSpaceReg (I := I) hS hAlphaT0 hT0Omega frame hframe hu




omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem tailChrOrtho
    {Idx : Type} [Fintype Idx] [DecidableEq Idx]
    {u : Set M}
    {alpha t₀ omega : Real} {hαω : alpha < omega}
    {S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega hαω)}
    (hS : IsSolutionOn (I := I) S)
    (hαt₀ : alpha < t₀) (ht₀ω : t₀ < omega)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u)
    (hu : IsOpen u)
    (t : RealTimeInterval.RegularTime
      (RealTimeInterval.closedOpen t₀ omega ht₀ω))
    (horth : ∀ y : M, y ∈ u -> ∀ i j : Idx,
      ((S.timeRestrict (RealTimeInterval.closedOpen t₀ omega ht₀ω)).base.metric
          (t : Real)).inner y (frame i y) (frame j y) =
        if i = j then (1 : Real) else 0) :
    ∃ hframe1 : IsLocalFrameOn I E (1 : WithTop ℕ∞) frame u,
      ∃ chrDt : Real -> M -> Idx -> Idx -> Idx -> Real,
        (∀ y : M, y ∈ u -> ∀ i j k : Idx,
          HasDerivWithinAt
            (fun s : Real =>
              DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
                ((S.timeRestrict
                  (RealTimeInterval.closedOpen t₀ omega ht₀ω)).family.connection s)
                frame hframe1 y i j k)
            (chrDt (t : Real) y i j k)
            (RealTimeInterval.closedOpen t₀ omega ht₀ω).carrier (t : Real)) ∧
        (∀ y : M, y ∈ u -> ∀ i j k : Idx,
          chrDt (t : Real) y i j k =
            -ricciCovDerivCompInFrame (I := I)
                (S.timeRestrict (RealTimeInterval.closedOpen t₀ omega ht₀ω))
                frame (t : Real) y i j k
            -ricciCovDerivCompInFrame (I := I)
                (S.timeRestrict (RealTimeInterval.closedOpen t₀ omega ht₀ω))
                frame (t : Real) y j i k
            +ricciCovDerivCompInFrame (I := I)
                (S.timeRestrict (RealTimeInterval.closedOpen t₀ omega ht₀ω))
                frame (t : Real) y k i j) := by
  classical
  let D' := RealTimeInterval.closedOpen t₀ omega ht₀ω
  let S' := S.timeRestrict D'
  obtain ⟨hframe1, hgamma⟩ :=
    tailChristoffel (I := I) (Idx := Idx) hS hαt₀ ht₀ω frame hframe hu
  let gInv := localFrameInv (E := E) (I := I) S' frame hframe
  let nablaRic := fun (r : Real) (y : M) (d a b : Idx) =>
    ricciCovDerivCompInFrame (I := I) S' frame r y d a b
  let chrDt := fun (r : Real) (y : M) (i j k : Idx) =>
    christoffelEvolutionRHSInFrame (M := M) gInv nablaRic r y i j k
  refine ⟨hframe1, chrDt, ?_, ?_⟩
  · intro y hy i j k
    simpa only [chrDt, gInv, nablaRic, S', D'] using hgamma t y hy i j k
  · intro y hy i j k
    have hinvId : ∀ e l : Idx, gInv (t : Real) y e l =
        if e = l then (1 : Real) else 0 := by
      intro e l
      have hleft :=
        (localFrameInv_real (I := I) S' frame hframe (t : Real) y hy e l).1
      have horth' : ∀ a b : Idx,
          metricCompInFrame (I := I) S' frame (t : Real) y a b =
            if a = b then (1 : Real) else 0 := by
        intro a b
        simpa only [metricCompInFrame, SolutionOn.family_metric, S', D'] using
          horth y hy a b
      simpa only [horth', mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, if_true] using hleft
    simpa only [chrDt, nablaRic, S', D'] using
      christoffelRHS_id (M := M) gInv nablaRic hinvId i j k

end DifferentialGeometry.PDE.RicciFlow
