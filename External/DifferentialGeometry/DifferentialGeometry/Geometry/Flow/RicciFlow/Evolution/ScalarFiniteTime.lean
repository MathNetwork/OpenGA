import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ScalarLowerBound

set_option autoImplicit false
set_option linter.style.longLine false











noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Set
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]




def scalarBlowupTime (n c0 : Real) : Real :=
  n / (2 * c0)


def ScalarBoundedAboveOnSlab (scalar : Real -> M -> Real) (T : Real) : Prop :=
  exists B : Real, forall t : Real, t ∈ Set.Icc 0 T -> forall x : M, scalar t x <= B



def ScalarLowerBarrierBoundUpToPole
    (scalar : Real -> M -> Real) (n c0 omega : Real) : Prop :=
  forall T : Real, 0 < T -> T < omega -> T < scalarBlowupTime n c0 ->
    forall x : M, scalarLowerBarrier n c0 T <= scalar T x

theorem scalarBlowupTime_pos
    {n c0 : Real} (hn : 0 < n) (hc0 : 0 < c0) :
    0 < scalarBlowupTime n c0 := by
  unfold scalarBlowupTime
  exact div_pos hn (mul_pos two_pos hc0)

theorem scalarLowerBarrier_denominator_pos_of_lt_blowup
    {n c0 t : Real} (hn : 0 < n) (hc0 : 0 < c0)
    (_ht_nonneg : 0 <= t) (ht : t < scalarBlowupTime n c0) :
    0 < 1 - (2 / n) * c0 * t := by
  have ha_pos : 0 < (2 / n) * c0 := mul_pos (div_pos two_pos hn) hc0
  have hmul :
      ((2 / n) * c0) * t <
        ((2 / n) * c0) * scalarBlowupTime n c0 :=
    mul_lt_mul_of_pos_left ht ha_pos
  have hright :
      ((2 / n) * c0) * scalarBlowupTime n c0 = 1 := by
    unfold scalarBlowupTime
    field_simp [ne_of_gt hn, ne_of_gt hc0]
  have hlt : ((2 / n) * c0) * t < 1 := by
    simpa [hright] using hmul
  linarith

theorem scalarLowerBarrier_denominator_pos_on_Icc_of_lt_blowup
    {T n c0 : Real} (hn : 0 < n) (hc0 : 0 < c0)
    (hT : T < scalarBlowupTime n c0) :
    forall t : Real, t ∈ Set.Icc 0 T ->
      0 < 1 - (2 / n) * c0 * t := by
  intro t ht
  exact scalarLowerBarrier_denominator_pos_of_lt_blowup
    (n := n) (c0 := c0) hn hc0 ht.1 (lt_of_le_of_lt ht.2 hT)

theorem exists_lt_scalarLowerBarrier_before_blowup
    {n c0 : Real} (hn : 0 < n) (hc0 : 0 < c0) (B : Real) :
    exists T : Real,
      0 < T ∧ T < scalarBlowupTime n c0 ∧ B < scalarLowerBarrier n c0 T := by
  let C : Real := max B c0 + 1
  have hB_lt_C : B < C := by
    have hB_le : B <= max B c0 := le_max_left B c0
    linarith
  have hc0_lt_C : c0 < C := by
    have hc0_le : c0 <= max B c0 := le_max_right B c0
    linarith
  have hC_pos : 0 < C := lt_trans hc0 hc0_lt_C
  let d : Real := c0 / C
  have hd_pos : 0 < d := div_pos hc0 hC_pos
  have hd_lt_one : d < 1 := (div_lt_one hC_pos).2 hc0_lt_C
  let T : Real := scalarBlowupTime n c0 * (1 - d)
  have hblow_pos : 0 < scalarBlowupTime n c0 :=
    scalarBlowupTime_pos hn hc0
  have hT_pos : 0 < T := by
    exact mul_pos hblow_pos (sub_pos.mpr hd_lt_one)
  have hT_lt : T < scalarBlowupTime n c0 := by
    have hone_sub_lt : 1 - d < 1 := by linarith
    have hmul := mul_lt_mul_of_pos_left hone_sub_lt hblow_pos
    simpa [T] using hmul
  have hden_eq : 1 - (2 / n) * c0 * T = d := by
    unfold T d scalarBlowupTime
    field_simp [ne_of_gt hn, ne_of_gt hc0, ne_of_gt hC_pos]
    ring
  have hbar_eq : scalarLowerBarrier n c0 T = C := by
    unfold scalarLowerBarrier
    rw [hden_eq]
    unfold d
    field_simp [ne_of_gt hc0, ne_of_gt hC_pos]
  exact ⟨T, hT_pos, hT_lt, by simpa [hbar_eq] using hB_lt_C⟩

omit [TopologicalSpace M] [SigmaCompactSpace M] [T2Space M] in
theorem scalar_endpoint_le_blowupTime_of_lower_barrier_bound
    [Nonempty M]
    {scalar : Real -> M -> Real} {n c0 omega : Real}
    (hn : 0 < n) (hc0 : 0 < c0)
    (hlower : ScalarLowerBarrierBoundUpToPole (M := M) scalar n c0 omega)
    (hbounded : ScalarBoundedAboveOnSlab (M := M) scalar
      (scalarBlowupTime n c0)) :
    omega <= scalarBlowupTime n c0 := by
  by_contra hnot
  have hlt_omega : scalarBlowupTime n c0 < omega := lt_of_not_ge hnot
  rcases hbounded with ⟨B, hB⟩
  obtain ⟨T, hT_pos, hT_blow, hbar_gt⟩ :=
    exists_lt_scalarLowerBarrier_before_blowup (n := n) (c0 := c0) hn hc0 B
  let x : M := Classical.choice (inferInstance : Nonempty M)
  have hbar_le_scalar :
      scalarLowerBarrier n c0 T <= scalar T x :=
    hlower T hT_pos (lt_trans hT_blow hlt_omega) hT_blow x
  have hT_mem : T ∈ Set.Icc 0 (scalarBlowupTime n c0) :=
    ⟨le_of_lt hT_pos, le_of_lt hT_blow⟩
  have hscalar_le : scalar T x <= B := hB T hT_mem x
  exact not_lt_of_ge (le_trans hbar_le_scalar hscalar_le) hbar_gt

namespace InitialScalarMinimum

omit [TopologicalSpace M] [SigmaCompactSpace M] [T2Space M] in
theorem pos_of_forall_pos
    {scalar : Real -> M -> Real} {c0 : Real}
    (hmin : InitialScalarMinimum (M := M) scalar c0)
    (hpos : forall x : M, 0 < scalar 0 x) :
    0 < c0 := by
  rcases hmin with ⟨x0, hc0, _hbound⟩
  simpa [hc0] using hpos x0

end InitialScalarMinimum

namespace ScalarBoundedAboveOnSlab

omit [SigmaCompactSpace M] [T2Space M] in
theorem of_continuousOn
    [CompactSpace M]
    {scalar : Real -> M -> Real} {T : Real}
    (hcont : ContinuousOn
      (fun p : Real × M => scalar p.1 p.2)
      (DifferentialGeometry.Integral.Connection.spacetimeSlab (M := M) T)) :
    ScalarBoundedAboveOnSlab (M := M) scalar T := by
  have hcompact : IsCompact (DifferentialGeometry.Integral.Connection.spacetimeSlab (M := M) T) := by
    unfold DifferentialGeometry.Integral.Connection.spacetimeSlab
    exact isCompact_Icc.prod isCompact_univ
  have himage :
      IsCompact
        ((fun p : Real × M => scalar p.1 p.2) ''
          DifferentialGeometry.Integral.Connection.spacetimeSlab (M := M) T) :=
    hcompact.image_of_continuousOn hcont
  rcases himage.bddAbove with ⟨B, hB⟩
  refine ⟨B, ?_⟩
  intro t ht x
  exact hB ⟨(t, x), ⟨ht, trivial⟩, rfl⟩

end ScalarBoundedAboveOnSlab



theorem scalarLowerBarrierBoundUpToPole_of_scalarEvolution_closedOpen
    [I.Boundaryless] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    {omega : Real} (h0ω : 0 < omega)
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (n c0 : Real) (hn : 0 < n) (hc0 : 0 < c0)
    (scalar scalarLap ricciNormSq : Real -> M -> Real)
    (K : Real -> NNReal)
    (hreg : forall T : Real, 0 < T -> T < omega ->
      T < scalarBlowupTime n c0 ->
        ScalarLowerBoundWMPRegularity (I := I) G T n c0 scalar (K T))
    (hevol : ScalarEvolutionEquationOn
      (D := DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen 0 omega h0ω)
      scalar scalarLap ricciNormSq)
    (hlap : forall T : Real, 0 < T -> T < omega ->
      T < scalarBlowupTime n c0 ->
        ScalarLaplacianRealizesHeatOperatorOn (I := I) G T scalar scalarLap)
    (hricci : forall T : Real, 0 < T -> T < omega ->
      T < scalarBlowupTime n c0 ->
        forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
          (1 / n) * (scalar t x) ^ 2 <= ricciNormSq t x)
    (hinit : InitialScalarLowerBound (M := M) scalar c0)
    (hF_lip : forall T : Real, 0 < T -> T < omega ->
      T < scalarBlowupTime n c0 ->
        forall t : Real, t ∈ Set.Icc 0 T ->
          LipschitzOnWith (K T) (fun a : Real => scalarLowerReaction n a t)
            (DifferentialGeometry.Integral.Connection.scalarWMPValueSet (M := M) T scalar
              (scalarLowerBarrier n c0))) :
    ScalarLowerBarrierBoundUpToPole (M := M) scalar n c0 omega := by
  intro T hT_pos hT_omega hT_blow x
  have hden :
      forall t : Real, t ∈ Set.Icc 0 T ->
        0 < 1 - (2 / n) * c0 * t :=
    scalarLowerBarrier_denominator_pos_on_Icc_of_lt_blowup
      (n := n) (c0 := c0) hn hc0 hT_blow
  have hbound :=
    scalar_curvature_lower_bound_of_scalarEvolution_closedOpen
      (I := I) (omega := omega) h0ω G T n c0 hT_pos hT_omega
      (ne_of_gt hn) scalar scalarLap ricciNormSq (K T)
      hden (hreg T hT_pos hT_omega hT_blow) hevol
      (hlap T hT_pos hT_omega hT_blow)
      (hricci T hT_pos hT_omega hT_blow)
      hinit (hF_lip T hT_pos hT_omega hT_blow)
  exact hbound T ⟨le_of_lt hT_pos, le_rfl⟩ x




theorem positive_scalar_finite_time_of_scalarEvolution_closedOpen
    [I.Boundaryless] [CompactSpace M] [Nonempty M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    {omega : Real} (h0ω : 0 < omega)
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (n c0 : Real) (hn : 0 < n)
    (scalar scalarLap ricciNormSq : Real -> M -> Real)
    (K : Real -> NNReal)
    (hinit_min : InitialScalarMinimum (M := M) scalar c0)
    (hinit_pos : forall x : M, 0 < scalar 0 x)
    (hscalar_cont : forall T : Real, 0 <= T -> T < omega ->
      ContinuousOn (fun p : Real × M => scalar p.1 p.2)
        (DifferentialGeometry.Integral.Connection.spacetimeSlab (M := M) T))
    (hreg : forall T : Real, 0 < T -> T < omega ->
      T < scalarBlowupTime n c0 ->
        ScalarLowerBoundWMPRegularity (I := I) G T n c0 scalar (K T))
    (hevol : ScalarEvolutionEquationOn
      (D := DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen 0 omega h0ω)
      scalar scalarLap ricciNormSq)
    (hlap : forall T : Real, 0 < T -> T < omega ->
      T < scalarBlowupTime n c0 ->
        ScalarLaplacianRealizesHeatOperatorOn (I := I) G T scalar scalarLap)
    (hricci : forall T : Real, 0 < T -> T < omega ->
      T < scalarBlowupTime n c0 ->
        forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
          (1 / n) * (scalar t x) ^ 2 <= ricciNormSq t x)
    (hF_lip : forall T : Real, 0 < T -> T < omega ->
      T < scalarBlowupTime n c0 ->
        forall t : Real, t ∈ Set.Icc 0 T ->
          LipschitzOnWith (K T) (fun a : Real => scalarLowerReaction n a t)
            (DifferentialGeometry.Integral.Connection.scalarWMPValueSet (M := M) T scalar
              (scalarLowerBarrier n c0))) :
    omega <= scalarBlowupTime n c0 := by
  have hc0 : 0 < c0 :=
    InitialScalarMinimum.pos_of_forall_pos (M := M) hinit_min hinit_pos
  have hlower :
      ScalarLowerBarrierBoundUpToPole (M := M) scalar n c0 omega :=
    scalarLowerBarrierBoundUpToPole_of_scalarEvolution_closedOpen
      (I := I) h0ω G n c0 hn hc0 scalar scalarLap ricciNormSq K
      hreg hevol hlap hricci
      (InitialScalarMinimum.lowerBound (M := M) hinit_min) hF_lip
  by_contra hnot
  have hlt_omega : scalarBlowupTime n c0 < omega := lt_of_not_ge hnot
  have hblow_pos : 0 < scalarBlowupTime n c0 :=
    scalarBlowupTime_pos hn hc0
  have hbounded :
      ScalarBoundedAboveOnSlab (M := M) scalar (scalarBlowupTime n c0) :=
    ScalarBoundedAboveOnSlab.of_continuousOn (M := M)
      (hscalar_cont (scalarBlowupTime n c0) (le_of_lt hblow_pos) hlt_omega)
  have hle := scalar_endpoint_le_blowupTime_of_lower_barrier_bound
    (M := M) hn hc0 hlower hbounded
  exact hnot hle






theorem finiteTime3D
    [I.Boundaryless] [CompactSpace M] [Nonempty M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    {omega : Real} (h0ω : 0 < omega)
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (c0 : Real)
    (scalar scalarLap ricciNormSq : Real -> M -> Real)
    (K : Real -> NNReal)
    (hinit_min : InitialScalarMinimum (M := M) scalar c0)
    (hinit_pos : forall x : M, 0 < scalar 0 x)
    (hscalar_cont : forall T : Real, 0 <= T -> T < omega ->
      ContinuousOn (fun p : Real × M => scalar p.1 p.2)
        (DifferentialGeometry.Integral.Connection.spacetimeSlab (M := M) T))
    (hreg : forall T : Real, 0 < T -> T < omega ->
      T < scalarBlowupTime 3 c0 ->
        ScalarLowerBoundWMPRegularity (I := I) G T 3 c0 scalar (K T))
    (hevol : ScalarEvolutionEquationOn
      (D := DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen 0 omega h0ω)
      scalar scalarLap ricciNormSq)
    (hlap : forall T : Real, 0 < T -> T < omega ->
      T < scalarBlowupTime 3 c0 ->
        ScalarLaplacianRealizesHeatOperatorOn (I := I) G T scalar scalarLap)
    (hricci : forall T : Real, 0 < T -> T < omega ->
      T < scalarBlowupTime 3 c0 ->
        forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
          (1 / 3 : Real) * (scalar t x) ^ 2 <= ricciNormSq t x)
    (hF_lip : forall T : Real, 0 < T -> T < omega ->
      T < scalarBlowupTime 3 c0 ->
        forall t : Real, t ∈ Set.Icc 0 T ->
          LipschitzOnWith (K T) (fun a : Real => scalarLowerReaction 3 a t)
            (DifferentialGeometry.Integral.Connection.scalarWMPValueSet (M := M) T scalar
              (scalarLowerBarrier 3 c0))) :
    0 < c0 ∧ omega <= 3 / (2 * c0) := by
  have hc0 : 0 < c0 :=
    InitialScalarMinimum.pos_of_forall_pos (M := M) hinit_min hinit_pos
  have hbound :
      omega <= scalarBlowupTime 3 c0 :=
    positive_scalar_finite_time_of_scalarEvolution_closedOpen
      (I := I) h0ω G 3 c0 (by norm_num) scalar scalarLap ricciNormSq K
      hinit_min hinit_pos hscalar_cont hreg hevol hlap hricci hF_lip
  exact ⟨hc0, by simpa [scalarBlowupTime] using hbound⟩

end DifferentialGeometry.PDE.RicciFlow
