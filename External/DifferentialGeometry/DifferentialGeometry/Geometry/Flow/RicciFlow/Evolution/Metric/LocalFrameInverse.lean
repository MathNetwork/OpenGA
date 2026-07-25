import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Metric.InverseSmooth










noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle
open DifferentialGeometry.Integral.Connection
open scoped Manifold ContDiff BigOperators Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M]
variable [SigmaCompactSpace M] [T2Space M]

section Components

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
variable {n : WithTop ℕ∞} {u : Set M}



noncomputable def localFrameInv
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx → (x : M) → TangentSpace I x)
    (hframe : IsLocalFrameOn I E n frame u) :
    Real → DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx :=
  by
    classical
    exact fun t x i j =>
      if hx : x ∈ u then
        basisInvMetric (I := I) (M := M) (S.family.metric t) x
          (hframe.toBasisAt hx) i j
      else 0

omit [Fintype Idx] [DecidableEq Idx] in
omit [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem localFrameInv_of_mem
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx → (x : M) → TangentSpace I x)
    (hframe : IsLocalFrameOn I E n frame u)
    {x : M} (hx : x ∈ u) (t : Real) (i j : Idx) :
    localFrameInv (I := I) S frame hframe t x i j =
      basisInvMetric (I := I) (M := M) (S.family.metric t) x
        (hframe.toBasisAt hx) i j := by
  simp [localFrameInv, hx]



omit [SigmaCompactSpace M] [T2Space M] in
theorem localFrameInv_real
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx → (x : M) → TangentSpace I x)
    (hframe : IsLocalFrameOn I E n frame u) :
    InvMetricLocal (I := I) S (localFrameInv (I := I) S frame hframe) frame u := by
  intro t x hx i j
  have hreal :=
    basisInvMetric_real (I := I) (M := M) (g := S.family.metric t) (x := x)
      (basis := hframe.toBasisAt hx)
  simpa [metricCompInFrame, localFrameInv_of_mem (I := I) S frame hframe hx,
    hframe.toBasisAt_coe] using hreal i j

omit [SigmaCompactSpace M] [T2Space M] in
private theorem frameGram_time
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx → (x : M) → TangentSpace I x)
    {K : Set Real} (x : M)
    (hmetric : ∀ i j : Idx, ContDiffOn Real ∞
      (fun t : Real => metricCompInFrame (I := I) S frame t x i j) K) :
    ContDiffOn Real ∞
      (fun t : Real => frameGramCLM (I := I) S frame (t, x)) K := by
  classical
  unfold frameGramCLM
  apply ContDiffOn.sum
  intro i _hi
  apply ContDiffOn.sum
  intro j _hj
  exact (hmetric i j).smul contDiffOn_const

omit [Fintype Idx] [DecidableEq Idx] in


omit [SigmaCompactSpace M] [T2Space M] in
theorem localFrameInv_time
    [Finite Idx]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx → (x : M) → TangentSpace I x)
    (hframe : IsLocalFrameOn I E n frame u)
    {K : Set Real}
    (hmetric : ∀ x : M, x ∈ u → ∀ i j : Idx, ContDiffOn Real ∞
      (fun t : Real => metricCompInFrame (I := I) S frame t x i j) K)
    (x : M) (i j : Idx) :
    ContDiffOn Real ∞
      (fun t : Real => localFrameInv (I := I) S frame hframe t x i j) K := by
  classical
  letI := Fintype.ofFinite Idx
  by_cases hx : x ∈ u
  · have hgram := frameGram_time (I := I) S frame x (hmetric x hx)
    have hinvSmooth : ContDiffOn Real ∞
        (fun t : Real => ContinuousLinearMap.inverse
          (frameGramCLM (I := I) S frame (t, x))) K := by
      intro t ht
      have hinv :=
        frameGramCLM_isInvertible_at (I := I) S
          (localFrameInv (I := I) S frame hframe) frame (t, x)
          (fun a b => (localFrameInv_real (I := I) S frame hframe t x hx a b).1)
          (fun a b => (localFrameInv_real (I := I) S frame hframe t x hx a b).2)
      have hinvAt : ContDiffAt Real ∞ ContinuousLinearMap.inverse
          (frameGramCLM (I := I) S frame (t, x)) :=
        hinv.contDiffAt_map_inverse
      simpa [Function.comp_def] using
        hinvAt.comp_contDiffWithinAt t (hgram t ht)
    have happ : ContDiffOn Real ∞
        (fun t : Real => ContinuousLinearMap.inverse
          (frameGramCLM (I := I) S frame (t, x)) (Pi.single j 1)) K :=
      hinvSmooth.clm_apply contDiffOn_const
    have hcoord : ContDiffOn Real ∞
        (fun t : Real => ContinuousLinearMap.inverse
          (frameGramCLM (I := I) S frame (t, x)) (Pi.single j 1) i) K :=
      (contDiffOn_const (c := LinearMap.toContinuousLinearMap
        (LinearMap.proj (R := Real) (φ := fun _ : Idx => Real) i))).clm_apply happ
    refine hcoord.congr ?_
    intro t _ht
    rw [frameGInvCLM_eq_inverse_at (I := I) S
      (localFrameInv (I := I) S frame hframe) frame (t, x)
      (fun a b => (localFrameInv_real (I := I) S frame hframe t x hx a b).1)
      (fun a b => (localFrameInv_real (I := I) S frame hframe t x hx a b).2)]
    simpa using
      (sum_mul_pi_single (Idx := Idx)
        (fun k => localFrameInv (I := I) S frame hframe t x i k) j).symm
  · simpa [localFrameInv, hx] using
      (contDiffOn_const (c := (0 : Real)) :
        ContDiffOn Real ∞ (fun _ : Real => (0 : Real)) K)


noncomputable def localFrameInvDt
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx → (x : M) → TangentSpace I x)
    (hframe : IsLocalFrameOn I E n frame u) :
    Real → M → Idx → Idx → Real :=
  fun t x i j => derivWithin
    (fun s : Real => localFrameInv (I := I) S frame hframe s x i j)
    D.carrier t



omit [SigmaCompactSpace M] [T2Space M] in
theorem localFrameTimeReg
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx → (x : M) → TangentSpace I x)
    (hframe : IsLocalFrameOn I E n frame u)
    (hmetric : ∀ x : M, x ∈ u → ∀ i j : Idx, ContDiffOn Real ∞
      (fun t : Real => metricCompInFrame (I := I) S frame t x i j) D.carrier)
    (hunique : ∀ t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D,
      UniqueDiffWithinAt Real D.carrier (t : Real)) :
    MetricFrameTimeRegularityInFrameOnLocal
      (I := I) S (localFrameInv (I := I) S frame hframe)
      (localFrameInvDt (I := I) S frame hframe) frame u where
  metricSmooth := hmetric
  nondegenerateGram := localFrameInv_real (I := I) S frame hframe
  inverseMetricDerivative := by
    intro t x i j
    have hdiff :=
      (localFrameInv_time (I := I) S frame hframe hmetric x i j).differentiableOn
        (by simp) (t : Real) (D.regular_subset t.2)
    simpa [localFrameInvDt] using hdiff.hasDerivWithinAt
  uniqueTimeDerivatives := hunique

end Components

end DifferentialGeometry.PDE.RicciFlow
