import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Scalar.Basic

set_option autoImplicit false
set_option linter.style.longLine false







noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

section TraceRoute

variable {Idx : Type*} [Fintype Idx]

def scalarTraceInFrame
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) :
    Real -> M -> Real :=
  fun t x =>
    ∑ i : Idx, ∑ j : Idx,
      gInv t x i j * ricciCompInFrame (I := I) S frame t x i j

omit [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem scalarTraceInFrame_apply
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) :
    scalarTraceInFrame (I := I) S gInv frame t x =
      ∑ i : Idx, ∑ j : Idx,
        gInv t x i j * ricciCompInFrame (I := I) S frame t x i j := by
  rfl





theorem trace_sq_le_card_mul_sum_sq_two
    (A : Idx -> Idx -> Real) :
    (∑ i : Idx, A i i) ^ 2 <=
      (Fintype.card Idx : Real) * (∑ i : Idx, ∑ j : Idx, A i j ^ 2) := by
  classical
  have hcs :
      (∑ i : Idx, A i i) ^ 2 <=
        (Fintype.card Idx : Real) * (∑ i : Idx, A i i ^ 2) := by
    simpa using
      (sq_sum_le_card_mul_sum_sq
        (s := (Finset.univ : Finset Idx)) (f := fun i => A i i))
  have hdiag :
      (∑ i : Idx, A i i ^ 2) <=
        (∑ i : Idx, ∑ j : Idx, A i j ^ 2) := by
    refine Finset.sum_le_sum ?_
    intro i _hi
    exact Finset.single_le_sum
      (fun j _hj => sq_nonneg (A i j)) (Finset.mem_univ i)
  exact hcs.trans (mul_le_mul_of_nonneg_left hdiag (Nat.cast_nonneg _))



theorem trace_sq_div_rank_le_sum_sq_two
    [Nonempty Idx] (A : Idx -> Idx -> Real) :
    (1 / (Fintype.card Idx : Real)) * (∑ i : Idx, A i i) ^ 2 <=
      ∑ i : Idx, ∑ j : Idx, A i j ^ 2 := by
  classical
  have hcard : 0 < (Fintype.card Idx : Real) := by
    exact Nat.cast_pos.mpr Fintype.card_pos
  have h :=
    trace_sq_le_card_mul_sum_sq_two (Idx := Idx) A
  have hdiv :
      (∑ i : Idx, A i i) ^ 2 / (Fintype.card Idx : Real) <=
        ∑ i : Idx, ∑ j : Idx, A i j ^ 2 := by
    rw [div_le_iff₀ hcard]
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  simpa [div_eq_mul_inv, one_div, mul_comm, mul_left_comm, mul_assoc] using hdiv



def scalarTraceDerivRHSInFrame
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (t : Real) (x : M) : Real :=
  ∑ i : Idx, ∑ j : Idx,
    (inverseMetricEvolutionRHSInFrame (I := I) S gInv frame t x i j *
        ricciCompInFrame (I := I) S frame t x i j +
      gInv t x i j *
        ricciEvolutionRHSInFrame (I := I) S Rm04 gInv frame roughLapRic t x i j)



def ScalarLaplacianTraceInFrame
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (scalarLap : Real -> M -> Real) : Prop :=
  ∀ t x,
    scalarLap t x =
      ∑ i : Idx, ∑ j : Idx, gInv t x i j * roughLapRic t x i j



def scalarLaplacianTraceInFrame
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real) :
    Real -> M -> Real :=
  fun t x => ∑ i : Idx, ∑ j : Idx, gInv t x i j * roughLapRic t x i j

omit [TopologicalSpace M] [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem scalarLaplacianTraceInFrame_apply
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (t : Real) (x : M) :
    scalarLaplacianTraceInFrame (M := M) gInv roughLapRic t x =
      ∑ i : Idx, ∑ j : Idx, gInv t x i j * roughLapRic t x i j := by
  rfl



omit [TopologicalSpace M] [SigmaCompactSpace M] [T2Space M] in
theorem scalarLaplacianTraceInFrame_realizes
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real) :
    ScalarLaplacianTraceInFrame (M := M) gInv roughLapRic
      (scalarLaplacianTraceInFrame (M := M) gInv roughLapRic) := by
  intro t x
  rfl




omit [SigmaCompactSpace M] [T2Space M] in
theorem scalarLaplacianTraceInFrame_realizes_heatOperator_of_laplacianAt
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (T : Real)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (h : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      scalarLaplacianTraceInFrame (M := M) gInv roughLapRic t x =
        DifferentialGeometry.Integral.Connection.laplacianAt (I := I) G t
          (scalarTraceInFrame (I := I) S gInv frame t) x) :
    ScalarLaplacianRealizesHeatOperatorOn (I := I) G T
      (scalarTraceInFrame (I := I) S gInv frame)
      (scalarLaplacianTraceInFrame (M := M) gInv roughLapRic) :=
  ScalarLaplacianRealizesHeatOperatorOn.of_laplacianAt
    (I := I) (G := G) (T := T)
    (scalar := scalarTraceInFrame (I := I) S gInv frame)
    (scalarLap := scalarLaplacianTraceInFrame (M := M) gInv roughLapRic) h







omit [SigmaCompactSpace M] [T2Space M] in
@[deprecated "use a local or pointwise scalar trace statement instead" (since := "2026-05-22")]
theorem scalarLaplacianTraceInFrame_realizes_heatOperator_of_hessianTrace
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    {u : Set M}
    (S : SolutionOn (I := I) (M := M) D)
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (T : Real)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hcover : forall x : M, x ∈ u)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (scalarHess : Real -> (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (htrace : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      DifferentialGeometry.Integral.Connection.ScalarLaplacianRealizesTraceAtInBasis (I := I)
        (G.connection t) (G.metric t)
        (hframe.toBasisAt (hcover x))
        (gInv t x) (scalarTraceInFrame (I := I) S gInv frame t)
        (scalarHess t x))
    (hcomp : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      forall i j : Idx,
        scalarHess t x (DifferentialGeometry.Integral.Connection.vec2 (I := I) (frame i x) (frame j x)) =
          roughLapRic t x i j) :
    ScalarLaplacianRealizesHeatOperatorOn (I := I) G T
      (scalarTraceInFrame (I := I) S gInv frame)
      (scalarLaplacianTraceInFrame (M := M) gInv roughLapRic) := by
  refine scalarLaplacianTraceInFrame_realizes_heatOperator_of_laplacianAt
    (I := I) S G T gInv frame roughLapRic ?_
  intro t ht x
  let basis := hframe.toBasisAt (hcover x)
  have hmetric :
      DifferentialGeometry.Integral.Connection.metricTrace0S2InBasis (I := I) basis (gInv t x)
          (scalarHess t x) Fin.elim0 =
        scalarLaplacianTraceInFrame (M := M) gInv roughLapRic t x := by
    unfold DifferentialGeometry.Integral.Connection.metricTrace0S2InBasis scalarLaplacianTraceInFrame
    refine Finset.sum_congr rfl fun i _hi => ?_
    refine Finset.sum_congr rfl fun j _hj => ?_
    congr 1
    have hinput :
        DifferentialGeometry.Integral.Connection.metricTraceInput (I := I) (basis i) (basis j) Fin.elim0 =
          DifferentialGeometry.Integral.Connection.vec2 (I := I) (frame i x) (frame j x) := by
      have hbi : basis i = frame i x := by
        simp [basis, IsLocalFrameOn.toBasisAt_coe]
      have hbj : basis j = frame j x := by
        simp [basis, IsLocalFrameOn.toBasisAt_coe]
      rw [hbi, hbj]
      funext q
      fin_cases q
      · simp [DifferentialGeometry.Integral.Connection.metricTraceInput, DifferentialGeometry.Integral.Connection.vec2, DifferentialGeometry.Integral.Connection.vec2]
      · rfl
    rw [hinput, hcomp t ht x i j]
  have htrace_tx := htrace t ht x
  unfold DifferentialGeometry.Integral.Connection.ScalarLaplacianRealizesTraceAtInBasis at htrace_tx
  calc
    scalarLaplacianTraceInFrame (M := M) gInv roughLapRic t x =
        DifferentialGeometry.Integral.Connection.metricTrace0S2InBasis (I := I) basis (gInv t x)
          (scalarHess t x) Fin.elim0 := hmetric.symm
    _ = DifferentialGeometry.Integral.Connection.laplacianAt (I := I) G t
          (scalarTraceInFrame (I := I) S gInv frame t) x := by
        unfold DifferentialGeometry.Integral.Connection.laplacianAt
        exact htrace_tx.symm



def RicciTraceNormCauchySchwarzInFrame
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (n : Real) : Prop :=
  forall t : Real, forall x : M,
    (1 / n) * (scalarTraceInFrame (I := I) S gInv frame t x) ^ 2 <=
      ricciNormSqInFrame (I := I) S gInv frame t x



omit [SigmaCompactSpace M] [T2Space M] in
theorem scalar_metricInverseInBasis_of_solution_frame
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    {u : Set M}
    [DecidableEq Idx]
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hinv : InvMetricLocal (I := I) S gInv frame u)
    (t : Real) {x : M} (hx : x ∈ u) :
    MetricInverseInBasis_gen
      (I := I) (M := M) (S.family.metric t) x
      (hframe.toBasisAt hx) (fun i j : Idx => gInv t x i j) := by
  intro i j
  constructor
  · simpa [metricCompInFrame, IsLocalFrameOn.toBasisAt_coe] using
      (hinv t x hx i j).1
  · simpa [metricCompInFrame, IsLocalFrameOn.toBasisAt_coe] using
      (hinv t x hx i j).2



omit [SigmaCompactSpace M] in
theorem scalarTraceInFrame_eq_metricTracePair
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    {u : Set M}
    [DecidableEq Idx]
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hinv : InvMetricLocal (I := I) S gInv frame u)
    (t : Real) {x : M} (hx : x ∈ u) :
    scalarTraceInFrame (I := I) S gInv frame t x =
      DifferentialGeometry.Integral.Connection.metricTracePair0SAt (I := I) (S.family.metric t) (S.ricci t x) := by
  classical
  let basis := hframe.toBasisAt hx
  have hinvAt :
      MetricInverseInBasis_gen
        (I := I) (M := M) (S.family.metric t) x
        basis (fun i j : Idx => gInv t x i j) :=
    scalar_metricInverseInBasis_of_solution_frame
      (I := I) S gInv frame hframe hinv t hx
  rw [DifferentialGeometry.Integral.Connection.metricTracePair0SAt_eq_sum_basis
    (I := I) (S.family.metric t) basis (fun i j : Idx => gInv t x i j) hinvAt]
  simp [scalarTraceInFrame, ricciCompInFrame, basis, IsLocalFrameOn.toBasisAt_coe]



omit [SigmaCompactSpace M] in
theorem ricciNormSqInFrame_eq_normSq0S
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    {u : Set M}
    [DecidableEq Idx]
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hinv : InvMetricLocal (I := I) S gInv frame u)
    (t : Real) {x : M} (hx : x ∈ u) :
    ricciNormSqInFrame (I := I) S gInv frame t x =
      normSq0S (I := I) (S.family.metric t) x 2 (S.ricci t x) := by
  classical
  let basis := hframe.toBasisAt hx
  have hinvAt :
      MetricInverseInBasis_gen
        (I := I) (M := M) (S.family.metric t) x
        basis (fun i j : Idx => gInv t x i j) :=
    scalar_metricInverseInBasis_of_solution_frame
      (I := I) S gInv frame hframe hinv t hx
  exact ricciNormSq_basis (I := I) S gInv frame basis hinvAt
    (by intro i; simp [basis, IsLocalFrameOn.toBasisAt_coe])



omit [SigmaCompactSpace M] [T2Space M] in
theorem raisedRicciCompInFrame_eq_of_orthonormal_inv
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [DecidableEq Idx]
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hInvDelta : forall t x i j,
      gInv t x i j = if i = j then 1 else 0)
    (t : Real) (x : M) (i j : Idx) :
    raisedRicciCompInFrame (I := I) S gInv frame t x i j =
      ricciCompInFrame (I := I) S frame t x i j := by
  classical
  unfold raisedRicciCompInFrame DifferentialGeometry.Integral.Connection.raisedRicciComponentsInFrame
    ricciTwoTensorField
  simp [hInvDelta]



omit [SigmaCompactSpace M] [T2Space M] in
theorem scalarTraceInFrame_eq_trace_of_orthonormal_inv
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [DecidableEq Idx]
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hInvDelta : forall t x i j,
      gInv t x i j = if i = j then 1 else 0)
    (t : Real) (x : M) :
    scalarTraceInFrame (I := I) S gInv frame t x =
      ∑ i : Idx, ricciCompInFrame (I := I) S frame t x i i := by
  classical
  unfold scalarTraceInFrame
  simp [hInvDelta]


omit [SigmaCompactSpace M] [T2Space M] in
theorem ricciNormSqInFrame_eq_sum_sq_of_orthonormal_inv
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [DecidableEq Idx]
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hInvDelta : forall t x i j,
      gInv t x i j = if i = j then 1 else 0)
    (t : Real) (x : M) :
    ricciNormSqInFrame (I := I) S gInv frame t x =
      ∑ i : Idx, ∑ j : Idx,
        ricciCompInFrame (I := I) S frame t x i j ^ 2 := by
  classical
  unfold ricciNormSqInFrame DifferentialGeometry.Integral.Connection.ricciNormSqInFrame
  refine Finset.sum_congr rfl fun i _hi => ?_
  refine Finset.sum_congr rfl fun j _hj => ?_
  change
    ricciTwoTensorField (I := I) S t x (frame i x) (frame j x) *
        raisedRicciCompInFrame (I := I) S gInv frame t x i j =
      ricciCompInFrame (I := I) S frame t x i j ^ 2
  rw [raisedRicciCompInFrame_eq_of_orthonormal_inv
    (I := I) S gInv frame hInvDelta t x i j]
  simp [ricciTwoTensorField, ricciCompInFrame]
  ring


omit [SigmaCompactSpace M] [T2Space M] in
theorem ricciNormSqInFrame_ge_scalarTrace_sq_div_rank_of_orthonormal_inv
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [DecidableEq Idx] [Nonempty Idx]
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hInvDelta : forall t x i j,
      gInv t x i j = if i = j then 1 else 0)
    (t : Real) (x : M) :
    (1 / (Fintype.card Idx : Real)) *
        (scalarTraceInFrame (I := I) S gInv frame t x) ^ 2 <=
      ricciNormSqInFrame (I := I) S gInv frame t x := by
  classical
  rw [scalarTraceInFrame_eq_trace_of_orthonormal_inv
      (I := I) S gInv frame hInvDelta t x,
    ricciNormSqInFrame_eq_sum_sq_of_orthonormal_inv
      (I := I) S gInv frame hInvDelta t x]
  exact trace_sq_div_rank_le_sum_sq_two
    (Idx := Idx) (fun i j => ricciCompInFrame (I := I) S frame t x i j)

namespace RicciTraceNormCauchySchwarzInFrame



omit [SigmaCompactSpace M] [T2Space M] in
theorem of_orthonormal_inv
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [DecidableEq Idx] [Nonempty Idx]
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (n : Real)
    (hInvDelta : forall t x i j,
      gInv t x i j = if i = j then 1 else 0)
    (hn : n = (Fintype.card Idx : Real)) :
    RicciTraceNormCauchySchwarzInFrame (I := I) S gInv frame n := by
  subst n
  intro t x
  exact ricciNormSqInFrame_ge_scalarTrace_sq_div_rank_of_orthonormal_inv
    (I := I) S gInv frame hInvDelta t x



omit [SigmaCompactSpace M] in
@[deprecated "use a local or pointwise frame statement instead" (since := "2026-05-22")]
theorem of_metric_inverse_frame
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    {u : Set M}
    [DecidableEq Idx] [Nonempty Idx]
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hcover : forall x : M, x ∈ u)
    (hinv : InvMetricLocal (I := I) S gInv frame u)
    (n : Real)
    (hn : n = (Fintype.card Idx : Real)) :
    RicciTraceNormCauchySchwarzInFrame (I := I) S gInv frame n := by
  subst n
  intro t x
  have hx : x ∈ u := hcover x
  let basis := hframe.toBasisAt hx
  have hinvAt :
      MetricInverseInBasis_gen
        (I := I) (M := M) (S.family.metric t) x
        basis (fun i j : Idx => gInv t x i j) :=
    scalar_metricInverseInBasis_of_solution_frame
      (I := I) S gInv frame hframe hinv t hx
  rw [scalarTraceInFrame_eq_metricTracePair
      (I := I) S gInv frame hframe hinv t hx,
    ricciNormSqInFrame_eq_normSq0S
      (I := I) S gInv frame hframe hinv t hx]
  exact DifferentialGeometry.Integral.Connection.metricTracePair0SAt_sq_div_rank_le_normSq0S
    (I := I) (S.family.metric t) basis (fun i j : Idx => gInv t x i j)
    hinvAt (S.ricci t x)

end RicciTraceNormCauchySchwarzInFrame

end TraceRoute

end DifferentialGeometry.PDE.RicciFlow
