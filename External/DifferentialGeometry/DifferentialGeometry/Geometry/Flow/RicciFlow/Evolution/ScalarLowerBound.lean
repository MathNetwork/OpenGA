import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Scalar
import DifferentialGeometry.Geometry.Flow.RicciFlow.MaximumPrinciple.ScalarWeak
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Topology.Order.Compact

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




def scalarLowerBarrier (n c0 : Real) (t : Real) : Real :=
  c0 / (1 - (2 / n) * c0 * t)

@[simp] theorem scalarLowerBarrier_zero (n c0 : Real) :
    scalarLowerBarrier n c0 0 = c0 := by
  simp [scalarLowerBarrier]


def scalarLowerReaction (n : Real) (a _t : Real) : Real :=
  (2 / n) * a ^ 2

theorem scalarLowerReaction_apply (n a t : Real) :
    scalarLowerReaction n a t = (2 / n) * a ^ 2 := by
  rfl


theorem scalarLowerBarrier_hasDerivWithinAt
    (s : Set Real) (n c0 t : Real)
    (hn : n ≠ 0)
    (hden : 1 - (2 / n) * c0 * t ≠ 0) :
    HasDerivWithinAt
      (scalarLowerBarrier n c0)
      (scalarLowerReaction n (scalarLowerBarrier n c0 t) t)
      s t := by
  have hden' : 1 - ((2 / n) * c0) * t ≠ 0 := by
    simpa [mul_assoc] using hden
  have hnum : HasDerivAt (fun _ : Real => c0) 0 t := hasDerivAt_const t c0
  have hlin :
      HasDerivAt (fun y : Real => ((2 / n) * c0) * y) ((2 / n) * c0) t :=
    hasDerivAt_const_mul ((2 / n) * c0)
  have hdenDeriv :
      HasDerivAt
        (fun y : Real => 1 - ((2 / n) * c0) * y)
        (-((2 / n) * c0)) t := by
    simpa using hlin.const_sub 1
  have hquot :
      HasDerivAt
        (fun y : Real => c0 / (1 - ((2 / n) * c0) * y))
        ((0 * (1 - ((2 / n) * c0) * t) -
          c0 * (-((2 / n) * c0))) /
          (1 - ((2 / n) * c0) * t) ^ 2) t :=
    hnum.div hdenDeriv hden'
  have hwithin := hquot.hasDerivWithinAt (s := s)
  convert hwithin using 1
  rw [scalarLowerReaction]
  unfold scalarLowerBarrier
  field_simp [hden, hden', hn]
  ring_nf

theorem scalarLowerBarrier_derivWithin
    {T n c0 t : Real}
    (huniq : UniqueDiffWithinAt Real (Set.Icc 0 T) t)
    (hn : n ≠ 0)
    (hden : 1 - (2 / n) * c0 * t ≠ 0) :
    derivWithin (scalarLowerBarrier n c0) (Set.Icc 0 T) t =
      scalarLowerReaction n (scalarLowerBarrier n c0 t) t :=
  (scalarLowerBarrier_hasDerivWithinAt
      (s := Set.Icc 0 T) n c0 t hn hden).derivWithin huniq

theorem scalarLowerReaction_locallyLipschitz (n t : Real) :
    LocallyLipschitz (fun a : Real => scalarLowerReaction n a t) := by
  have hcd : ContDiff Real 1 (fun a : Real => scalarLowerReaction n a t) := by
    unfold scalarLowerReaction
    fun_prop
  exact hcd.locallyLipschitz



omit [TopologicalSpace M] [SigmaCompactSpace M] [T2Space M] in
theorem exists_scalarLowerReaction_lipschitzOn_valueSet
    (n T : Real) (u : Real -> M -> Real) (c : Real -> Real)
    (hcompact : IsCompact (DifferentialGeometry.Integral.Connection.scalarWMPValueSet (M := M) T u c)) :
    ∃ K : NNReal,
      ∀ t : Real, t ∈ Set.Icc 0 T ->
        LipschitzOnWith K (fun a : Real => scalarLowerReaction n a t)
          (DifferentialGeometry.Integral.Connection.scalarWMPValueSet (M := M) T u c) := by
  have hloc :
      LocallyLipschitzOn (DifferentialGeometry.Integral.Connection.scalarWMPValueSet (M := M) T u c)
        (fun a : Real => scalarLowerReaction n a 0) :=
    (scalarLowerReaction_locallyLipschitz n 0).locallyLipschitzOn
  obtain ⟨K, hK⟩ :=
    LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hcompact hloc
  refine ⟨K, ?_⟩
  intro t _ht
  simpa [scalarLowerReaction] using hK









theorem scalar_curvature_lower_bound_of_parabolic_inequality
    [I.Boundaryless] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (T n c0 : Real) (hT : 0 < T)
    (hn : n ≠ 0)
    (X : Real -> (x : M) -> TangentSpace I x)
    (scalar : Real -> M -> Real) (K : NNReal)
    (hden : ∀ t : Real, t ∈ Set.Icc 0 T ->
      0 < 1 - (2 / n) * c0 * t)
    (hw_cont : ContinuousOn
      (fun p : Real × M =>
        Real.exp (-(K : Real) * p.1) *
          (scalar p.1 p.2 - scalarLowerBarrier n c0 p.1))
      (DifferentialGeometry.Integral.Connection.spacetimeSlab (M := M) T))
    (hw_mdiff : ∀ t : Real, t ∈ Set.Icc 0 T ->
      ∀ x : M, MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M =>
          Real.exp (-(K : Real) * t) *
            (scalar t y - scalarLowerBarrier n c0 t)) x)
    (hw_grad : ∀ t : Real, t ∈ Set.Icc 0 T ->
      ∀ x : M, MDiffAt (T% fun y : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t)
          (fun z : M =>
            Real.exp (-(K : Real) * t) *
              (scalar t z - scalarLowerBarrier n c0 t)) y) x)
    (hscalar_time : ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M,
      DifferentiableWithinAt Real (fun s : Real => scalar s x) (Set.Icc 0 T) t)
    (hscalar_space : ∀ t : Real, t ∈ Set.Icc 0 T ->
      ∀ y : M, MDifferentiableAt I 𝓘(Real, Real) (scalar t) y)
    (hdiff_space : ∀ t : Real, t ∈ Set.Icc 0 T ->
      ∀ y : M, MDifferentiableAt I 𝓘(Real, Real)
        (fun z : M => scalar t z - scalarLowerBarrier n c0 t) y)
    (hdiff_grad : ∀ t : Real, t ∈ Set.Icc 0 T ->
      ∀ x : M, MDiffAt (T% fun y : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t)
          (fun z : M => scalar t z - scalarLowerBarrier n c0 t) y) x)
    (hparabolic : ∀ t : Real, t ∈ Set.Icc 0 T -> 0 < t -> ∀ x : M,
      scalarLowerReaction n (scalar t x) t <=
        DifferentialGeometry.Integral.Connection.parabolicOperatorWithDrift (I := I) G T X scalar t x)
    (hinit : ∀ x : M, c0 <= scalar 0 x)
    (hF_lip : ∀ t : Real, t ∈ Set.Icc 0 T ->
      LipschitzOnWith K (fun a : Real => scalarLowerReaction n a t)
        (DifferentialGeometry.Integral.Connection.scalarWMPValueSet (M := M) T scalar
          (scalarLowerBarrier n c0))) :
    ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M,
      scalarLowerBarrier n c0 t <= scalar t x := by
  refine DifferentialGeometry.Integral.Connection.scalar_wmp_supersolutions_of_lipschitz_on_value_set_of_regular_positive_time
    (I := I) G T (le_of_lt hT) X scalar (scalarLowerBarrier n c0)
    (scalarLowerReaction n) K hw_cont hw_mdiff hw_grad hscalar_time ?_
    hscalar_space hdiff_space hdiff_grad hparabolic ?_ ?_ hF_lip
  · intro t ht
    exact (scalarLowerBarrier_hasDerivWithinAt
      (s := Set.Icc 0 T) n c0 t hn
      (ne_of_gt (hden t ht))).differentiableWithinAt
  · intro t ht
    exact scalarLowerBarrier_derivWithin
      (T := T) (n := n) (c0 := c0) (t := t)
      (uniqueDiffOn_Icc hT t ht) hn (ne_of_gt (hden t ht))
  · intro x
    simpa using hinit x


theorem scalar_curvature_positive_of_lower_barrier
    {n c0 t Rtx : Real}
    (hbound : scalarLowerBarrier n c0 t <= Rtx)
    (hc0 : 0 < c0)
    (hden : 0 < 1 - (2 / n) * c0 * t) :
    0 < Rtx := by
  have hbar : 0 < scalarLowerBarrier n c0 t := by
    exact div_pos hc0 hden
  exact lt_of_lt_of_le hbar hbound




def InitialScalarLowerBound (scalar : Real -> M -> Real) (c0 : Real) : Prop :=
  forall x : M, c0 <= scalar 0 x


def InitialScalarMinimum (scalar : Real -> M -> Real) (c0 : Real) : Prop :=
  exists x0 : M, scalar 0 x0 = c0 /\ InitialScalarLowerBound (M := M) scalar c0

namespace InitialScalarMinimum

omit [TopologicalSpace M] [SigmaCompactSpace M] [T2Space M] in
theorem lowerBound
    {scalar : Real -> M -> Real} {c0 : Real}
    (h : InitialScalarMinimum (M := M) scalar c0) :
    InitialScalarLowerBound (M := M) scalar c0 := by
  rcases h with ⟨_x0, _hc0, hbound⟩
  exact hbound

end InitialScalarMinimum

omit [TopologicalSpace M] [SigmaCompactSpace M] [T2Space M] in
theorem initialScalarMinimum_of_isMinOn
    (scalar : Real -> M -> Real) {c0 : Real} {x0 : M}
    (hc0 : c0 = scalar 0 x0)
    (hmin : IsMinOn (fun x : M => scalar 0 x) Set.univ x0) :
    InitialScalarMinimum (M := M) scalar c0 := by
  refine ⟨x0, hc0.symm, ?_⟩
  intro x
  rw [hc0]
  exact hmin (by simp : x ∈ Set.univ)

omit [SigmaCompactSpace M] [T2Space M] in
theorem exists_initialScalarMinimum_of_continuous
    [CompactSpace M] [Nonempty M]
    (scalar : Real -> M -> Real)
    (hcont : Continuous (fun x : M => scalar 0 x)) :
    exists c0 : Real, InitialScalarMinimum (M := M) scalar c0 := by
  have hcompact : IsCompact (Set.univ : Set M) := isCompact_univ
  have hnonempty : (Set.univ : Set M).Nonempty := Set.univ_nonempty
  obtain ⟨x0, _hx0, hmin⟩ :=
    hcompact.exists_isMinOn hnonempty hcont.continuousOn
  exact ⟨scalar 0 x0,
    initialScalarMinimum_of_isMinOn (M := M) scalar rfl hmin⟩









structure ScalarLowerBoundWMPRegularity
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (T n c0 : Real) (scalar : Real -> M -> Real) (K : NNReal) : Prop where
  weighted_cont : ContinuousOn
    (fun p : Real × M =>
      Real.exp (-(K : Real) * p.1) *
        (scalar p.1 p.2 - scalarLowerBarrier n c0 p.1))
    (DifferentialGeometry.Integral.Connection.spacetimeSlab (M := M) T)
  weighted_mdiff : ∀ t : Real, t ∈ Set.Icc 0 T ->
    ∀ x : M, MDifferentiableAt I 𝓘(Real, Real)
      (fun y : M =>
        Real.exp (-(K : Real) * t) *
          (scalar t y - scalarLowerBarrier n c0 t)) x
  weighted_grad : ∀ t : Real, t ∈ Set.Icc 0 T ->
    ∀ x : M, MDiffAt (T% fun y : M =>
      DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t)
        (fun z : M =>
          Real.exp (-(K : Real) * t) *
            (scalar t z - scalarLowerBarrier n c0 t)) y) x
  scalar_time : ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M,
    DifferentiableWithinAt Real (fun s : Real => scalar s x) (Set.Icc 0 T) t
  scalar_space : ∀ t : Real, t ∈ Set.Icc 0 T ->
    ∀ y : M, MDifferentiableAt I 𝓘(Real, Real) (scalar t) y
  diff_space : ∀ t : Real, t ∈ Set.Icc 0 T ->
    ∀ y : M, MDifferentiableAt I 𝓘(Real, Real)
      (fun z : M => scalar t z - scalarLowerBarrier n c0 t) y
  diff_grad : ∀ t : Real, t ∈ Set.Icc 0 T ->
    ∀ x : M, MDiffAt (T% fun y : M =>
      DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t)
        (fun z : M => scalar t z - scalarLowerBarrier n c0 t) y) x










theorem scalarRegOfSmooth
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSmoothSolutionOn (I := I) (M := M) S)
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (T n c0 : Real) (K : NNReal)
    (hsubset : ∀ t : Real, t ∈ Set.Icc 0 T -> t ∈ D.carrier)
    (hmetric : ∀ t : Real, t ∈ Set.Icc 0 T ->
      G.metric t = S.family.metric t)
    (hden : ∀ t : Real, t ∈ Set.Icc 0 T ->
      1 - (2 / n) * c0 * t ≠ 0) :
    ScalarLowerBoundWMPRegularity (I := I) G T n c0 S.scalar K := by
  classical
  let hreg := hS.scalarRegular
  have hscalar_cont : ContinuousOn
      (fun p : Real × M => S.scalar p.1 p.2)
      (DifferentialGeometry.Integral.Connection.spacetimeSlab (M := M) T) := by
    refine hreg.scalar_continuousOn.mono ?_
    intro p hp
    exact ⟨hsubset p.1 hp.1, trivial⟩
  have hbar_cont : ContinuousOn
      (fun p : Real × M => scalarLowerBarrier n c0 p.1)
      (DifferentialGeometry.Integral.Connection.spacetimeSlab (M := M) T) := by
    have hden_ne : ∀ p : Real × M, p ∈ DifferentialGeometry.Integral.Connection.spacetimeSlab (M := M) T ->
        1 - (2 / n) * c0 * p.1 ≠ 0 := by
      intro p hp
      exact hden p.1 hp.1
    have hden_cont : ContinuousOn
        (fun p : Real × M => 1 - (2 / n) * c0 * p.1)
        (DifferentialGeometry.Integral.Connection.spacetimeSlab (M := M) T) := by
      have hlin : Continuous
          (fun p : Real × M => ((2 / n) * c0) * p.1) :=
        continuous_const.mul continuous_fst
      have hcont : Continuous
          (fun p : Real × M => 1 - ((2 / n) * c0) * p.1) :=
        continuous_const.sub hlin
      simpa [mul_assoc] using hcont.continuousOn
    have hconst : ContinuousOn
        (fun _p : Real × M => c0)
        (DifferentialGeometry.Integral.Connection.spacetimeSlab (M := M) T) := by
      exact continuous_const.continuousOn
    simpa [scalarLowerBarrier] using hconst.div hden_cont hden_ne
  refine
    { weighted_cont := ?_
      weighted_mdiff := ?_
      weighted_grad := ?_
      scalar_time := ?_
      scalar_space := ?_
      diff_space := ?_
      diff_grad := ?_ }
  · have hexp_cont : ContinuousOn
        (fun p : Real × M => Real.exp (-(K : Real) * p.1))
        (DifferentialGeometry.Integral.Connection.spacetimeSlab (M := M) T) := by
      have hlin : Continuous
          (fun p : Real × M => -((K : Real) * p.1)) :=
        (continuous_const.mul continuous_fst).neg
      simpa using (Real.continuous_exp.comp hlin).continuousOn
    exact hexp_cont.mul (hscalar_cont.sub hbar_cont)
  · intro t ht x
    have hdiff :
        MDifferentiableAt I 𝓘(Real, Real)
          (fun y : M => S.scalar t y - scalarLowerBarrier n c0 t) x :=
      (hreg.scalar_space t (hsubset t ht) x).sub mdifferentiableAt_const
    simpa [smul_eq_mul] using
      (hdiff.const_smul (Real.exp (-(K : Real) * t)))
  · intro t ht x
    rw [hmetric t ht]
    exact hreg.scalar_grad_const_mul_sub_const t (hsubset t ht)
      (Real.exp (-(K : Real) * t)) (scalarLowerBarrier n c0 t) x
  · intro t ht x
    exact hreg.scalar_time_within ht hsubset x
  · intro t ht y
    exact hreg.scalar_space t (hsubset t ht) y
  · intro t ht y
    exact (hreg.scalar_space t (hsubset t ht) y).sub mdifferentiableAt_const
  · intro t ht x
    rw [hmetric t ht]
    exact hreg.scalar_grad_sub_const t (hsubset t ht)
      (scalarLowerBarrier n c0 t) x






def ScalarEvolutionAllTimesOn
    (T : Real) (scalar scalarLap ricciNormSq : Real -> M -> Real) : Prop :=
  forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
    HasDerivWithinAt
      (fun s : Real => scalar s x)
      (scalarLap t x + 2 * ricciNormSq t x)
      (Set.Icc 0 T) t







omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem scalar_parabolic_inequality_of_scalarEvolution_allTimes
    [I.Boundaryless]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (T n : Real) (hT : 0 < T)
    (scalar scalarLap ricciNormSq : Real -> M -> Real)
    (hscalar : ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M,
      HasDerivWithinAt
        (fun s : Real => scalar s x)
        (scalarLap t x + 2 * ricciNormSq t x)
        (Set.Icc 0 T) t)
    (hlap : ScalarLaplacianRealizesHeatOperatorOn (I := I) G T scalar scalarLap)
    (hricci : ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M,
      (1 / n) * (scalar t x) ^ 2 <= ricciNormSq t x) :
    ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M,
      scalarLowerReaction n (scalar t x) t <=
        DifferentialGeometry.Integral.Connection.parabolicOperatorWithDrift (I := I) G T
          (fun _t x => (0 : TangentSpace I x)) scalar t x := by
  intro t ht x
  have hderiv :
      derivWithin (fun s : Real => scalar s x) (Set.Icc 0 T) t =
        scalarLap t x + 2 * ricciNormSq t x :=
    (hscalar t ht x).derivWithin (uniqueDiffOn_Icc hT t ht)
  have hparabolic :
      DifferentialGeometry.Integral.Connection.parabolicOperatorWithDrift (I := I) G T
          (fun _t x => (0 : TangentSpace I x)) scalar t x =
        2 * ricciNormSq t x := by
    have hlap_zero :=
      ScalarLaplacianRealizesHeatOperatorOn.zero_drift
        (I := I) (G := G) (T := T) (scalar := scalar)
        (scalarLap := scalarLap) hlap t ht x
    rw [DifferentialGeometry.Integral.Connection.parabolicOperatorWithDrift_eq, hderiv, hlap_zero]
    ring
  have hscale :
      2 * ((1 / n) * (scalar t x) ^ 2) <= 2 * ricciNormSq t x :=
    mul_le_mul_of_nonneg_left (hricci t ht x) (by norm_num)
  calc
    scalarLowerReaction n (scalar t x) t =
        2 * ((1 / n) * (scalar t x) ^ 2) := by
          rw [scalarLowerReaction]
          ring
    _ <= 2 * ricciNormSq t x := hscale
    _ = DifferentialGeometry.Integral.Connection.parabolicOperatorWithDrift (I := I) G T
          (fun _t x => (0 : TangentSpace I x)) scalar t x := hparabolic.symm








omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem scalar_parabolic_inequality_of_scalarEvolution_regularTime
    [I.Boundaryless]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (T n : Real) (hT : 0 < T)
    (scalar scalarLap ricciNormSq : Real -> M -> Real)
    (hslab : Set.Icc 0 T ⊆ D.carrier)
    (hregular : ∀ t : Real, t ∈ Set.Icc 0 T -> 0 < t -> t ∈ D.regular)
    (hscalar : ScalarEvolutionEquationOn (D := D) scalar scalarLap ricciNormSq)
    (hlap : ScalarLaplacianRealizesHeatOperatorOn (I := I) G T scalar scalarLap)
    (hricci : ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M,
      (1 / n) * (scalar t x) ^ 2 <= ricciNormSq t x) :
    ∀ t : Real, t ∈ Set.Icc 0 T -> 0 < t -> ∀ x : M,
      scalarLowerReaction n (scalar t x) t <=
        DifferentialGeometry.Integral.Connection.parabolicOperatorWithDrift (I := I) G T
          (fun _t x => (0 : TangentSpace I x)) scalar t x := by
  intro t ht htpos x
  let τ : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D :=
    ⟨t, hregular t ht htpos⟩
  have hwithin :
      HasDerivWithinAt
        (fun s : Real => scalar s x)
        (scalarLap t x + 2 * ricciNormSq t x)
        (Set.Icc 0 T) t := by
    simpa [τ] using (hscalar τ x).mono hslab
  have hderiv :
      derivWithin (fun s : Real => scalar s x) (Set.Icc 0 T) t =
        scalarLap t x + 2 * ricciNormSq t x :=
    hwithin.derivWithin (uniqueDiffOn_Icc hT t ht)
  have hparabolic :
      DifferentialGeometry.Integral.Connection.parabolicOperatorWithDrift (I := I) G T
          (fun _t x => (0 : TangentSpace I x)) scalar t x =
        2 * ricciNormSq t x := by
    have hlap_zero :=
      ScalarLaplacianRealizesHeatOperatorOn.zero_drift
        (I := I) (G := G) (T := T) (scalar := scalar)
        (scalarLap := scalarLap) hlap t ht x
    rw [DifferentialGeometry.Integral.Connection.parabolicOperatorWithDrift_eq, hderiv, hlap_zero]
    ring
  have hscale :
      2 * ((1 / n) * (scalar t x) ^ 2) <= 2 * ricciNormSq t x :=
    mul_le_mul_of_nonneg_left (hricci t ht x) (by norm_num)
  calc
    scalarLowerReaction n (scalar t x) t =
        2 * ((1 / n) * (scalar t x) ^ 2) := by
          rw [scalarLowerReaction]
          ring
    _ <= 2 * ricciNormSq t x := hscale
    _ = DifferentialGeometry.Integral.Connection.parabolicOperatorWithDrift (I := I) G T
          (fun _t x => (0 : TangentSpace I x)) scalar t x := hparabolic.symm

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem scalar_parabolic_inequality_of_scalarEvolutionAllTimes
    [I.Boundaryless]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (T n : Real) (hT : 0 < T)
    (scalar scalarLap ricciNormSq : Real -> M -> Real)
    (hscalar : ScalarEvolutionAllTimesOn (M := M) T scalar scalarLap ricciNormSq)
    (hlap : ScalarLaplacianRealizesHeatOperatorOn (I := I) G T scalar scalarLap)
    (hricci : ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M,
      (1 / n) * (scalar t x) ^ 2 <= ricciNormSq t x) :
    ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M,
      scalarLowerReaction n (scalar t x) t <=
        DifferentialGeometry.Integral.Connection.parabolicOperatorWithDrift (I := I) G T
          (fun _t x => (0 : TangentSpace I x)) scalar t x :=
  scalar_parabolic_inequality_of_scalarEvolution_allTimes
    (I := I) G T n hT scalar scalarLap ricciNormSq
    hscalar hlap hricci




omit [SigmaCompactSpace M] in
@[deprecated "use a local or intrinsic scalar lower-bound route instead" (since := "2026-05-22")]
theorem scalar_parabolic_inequality_of_scalarEvolutionAllTimes_inFrame
    [I.Boundaryless]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] [Nonempty Idx]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    {u : Set M}
    (S : SolutionOn (I := I) (M := M) D)
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (T n : Real) (hT : 0 < T)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hcover : forall x : M, x ∈ u)
    (hinv : InvMetricLocal (I := I) S gInv frame u)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (hn : n = (Fintype.card Idx : Real))
    (hscalar : ScalarEvolutionAllTimesOn (M := M) T
      (scalarTraceInFrame (I := I) S gInv frame)
      (scalarLaplacianTraceInFrame (M := M) gInv roughLapRic)
      (ricciNormSqInFrame (I := I) S gInv frame))
    (hlap : ScalarLaplacianRealizesHeatOperatorOn (I := I) G T
      (scalarTraceInFrame (I := I) S gInv frame)
      (scalarLaplacianTraceInFrame (M := M) gInv roughLapRic)) :
    ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M,
      scalarLowerReaction n (scalarTraceInFrame (I := I) S gInv frame t x) t <=
        DifferentialGeometry.Integral.Connection.parabolicOperatorWithDrift (I := I) G T
          (fun _t x => (0 : TangentSpace I x))
          (scalarTraceInFrame (I := I) S gInv frame) t x := by
  have hricci :
      ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M,
        (1 / n) * (scalarTraceInFrame (I := I) S gInv frame t x) ^ 2 <=
          ricciNormSqInFrame (I := I) S gInv frame t x := by
    have hcs :=
      RicciTraceNormCauchySchwarzInFrame.of_metric_inverse_frame
        (I := I) S gInv frame hframe hcover hinv n hn
    intro t _ht x
    exact hcs t x
  exact scalar_parabolic_inequality_of_scalarEvolutionAllTimes
    (I := I) G T n hT
    (scalarTraceInFrame (I := I) S gInv frame)
    (scalarLaplacianTraceInFrame (M := M) gInv roughLapRic)
    (ricciNormSqInFrame (I := I) S gInv frame)
    hscalar hlap hricci


theorem scalar_curvature_lower_bound_of_scalarEvolution
    [I.Boundaryless] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (T n c0 : Real) (hT : 0 < T)
    (hn : n ≠ 0)
    (scalar scalarLap ricciNormSq : Real -> M -> Real) (K : NNReal)
    (hslab : Set.Icc 0 T ⊆ D.carrier)
    (hregular : ∀ t : Real, t ∈ Set.Icc 0 T -> 0 < t -> t ∈ D.regular)
    (hden : ∀ t : Real, t ∈ Set.Icc 0 T ->
      0 < 1 - (2 / n) * c0 * t)
    (hw_cont : ContinuousOn
      (fun p : Real × M =>
        Real.exp (-(K : Real) * p.1) *
          (scalar p.1 p.2 - scalarLowerBarrier n c0 p.1))
      (DifferentialGeometry.Integral.Connection.spacetimeSlab (M := M) T))
    (hw_mdiff : ∀ t : Real, t ∈ Set.Icc 0 T ->
      ∀ x : M, MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M =>
          Real.exp (-(K : Real) * t) *
            (scalar t y - scalarLowerBarrier n c0 t)) x)
    (hw_grad : ∀ t : Real, t ∈ Set.Icc 0 T ->
      ∀ x : M, MDiffAt (T% fun y : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t)
          (fun z : M =>
            Real.exp (-(K : Real) * t) *
              (scalar t z - scalarLowerBarrier n c0 t)) y) x)
    (hscalar_time : ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M,
      DifferentiableWithinAt Real (fun s : Real => scalar s x) (Set.Icc 0 T) t)
    (hscalar_space : ∀ t : Real, t ∈ Set.Icc 0 T ->
      ∀ y : M, MDifferentiableAt I 𝓘(Real, Real) (scalar t) y)
    (hdiff_space : ∀ t : Real, t ∈ Set.Icc 0 T ->
      ∀ y : M, MDifferentiableAt I 𝓘(Real, Real)
        (fun z : M => scalar t z - scalarLowerBarrier n c0 t) y)
    (hdiff_grad : ∀ t : Real, t ∈ Set.Icc 0 T ->
      ∀ x : M, MDiffAt (T% fun y : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t)
          (fun z : M => scalar t z - scalarLowerBarrier n c0 t) y) x)
    (hevol : ScalarEvolutionEquationOn (D := D) scalar scalarLap ricciNormSq)
    (hlap : ScalarLaplacianRealizesHeatOperatorOn (I := I) G T scalar scalarLap)
    (hricci : ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M,
      (1 / n) * (scalar t x) ^ 2 <= ricciNormSq t x)
    (hinit : InitialScalarLowerBound (M := M) scalar c0)
    (hF_lip : ∀ t : Real, t ∈ Set.Icc 0 T ->
      LipschitzOnWith K (fun a : Real => scalarLowerReaction n a t)
        (DifferentialGeometry.Integral.Connection.scalarWMPValueSet (M := M) T scalar
          (scalarLowerBarrier n c0))) :
    ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M,
      scalarLowerBarrier n c0 t <= scalar t x := by
  have hparabolic :
      ∀ t : Real, t ∈ Set.Icc 0 T -> 0 < t -> ∀ x : M,
        scalarLowerReaction n (scalar t x) t <=
          DifferentialGeometry.Integral.Connection.parabolicOperatorWithDrift (I := I) G T
            (fun _t x => (0 : TangentSpace I x)) scalar t x :=
    scalar_parabolic_inequality_of_scalarEvolution_regularTime
      (I := I) (D := D) G T n hT scalar scalarLap ricciNormSq
      hslab hregular hevol hlap hricci
  exact scalar_curvature_lower_bound_of_parabolic_inequality
    (I := I) G T n c0 hT hn
    (fun _t x => (0 : TangentSpace I x)) scalar K hden
    hw_cont hw_mdiff hw_grad hscalar_time hscalar_space hdiff_space
    hdiff_grad hparabolic hinit hF_lip


theorem scalar_curvature_lower_bound_of_scalarEvolution_of_regularity
    [I.Boundaryless] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (T n c0 : Real) (hT : 0 < T)
    (hn : n ≠ 0)
    (scalar scalarLap ricciNormSq : Real -> M -> Real) (K : NNReal)
    (hslab : Set.Icc 0 T ⊆ D.carrier)
    (hregular : ∀ t : Real, t ∈ Set.Icc 0 T -> 0 < t -> t ∈ D.regular)
    (hden : ∀ t : Real, t ∈ Set.Icc 0 T ->
      0 < 1 - (2 / n) * c0 * t)
    (hreg : ScalarLowerBoundWMPRegularity (I := I) G T n c0 scalar K)
    (hevol : ScalarEvolutionEquationOn (D := D) scalar scalarLap ricciNormSq)
    (hlap : ScalarLaplacianRealizesHeatOperatorOn (I := I) G T scalar scalarLap)
    (hricci : ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M,
      (1 / n) * (scalar t x) ^ 2 <= ricciNormSq t x)
    (hinit : InitialScalarLowerBound (M := M) scalar c0)
    (hF_lip : ∀ t : Real, t ∈ Set.Icc 0 T ->
      LipschitzOnWith K (fun a : Real => scalarLowerReaction n a t)
        (DifferentialGeometry.Integral.Connection.scalarWMPValueSet (M := M) T scalar
          (scalarLowerBarrier n c0))) :
    ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M,
      scalarLowerBarrier n c0 t <= scalar t x :=
  scalar_curvature_lower_bound_of_scalarEvolution
    (I := I) (D := D) G T n c0 hT hn scalar scalarLap ricciNormSq K
    hslab hregular hden
    hreg.weighted_cont hreg.weighted_mdiff hreg.weighted_grad
    hreg.scalar_time hreg.scalar_space hreg.diff_space hreg.diff_grad
    hevol hlap hricci hinit hF_lip





theorem scalar_curvature_lower_bound_of_scalarEvolution_closedOpen
    [I.Boundaryless] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    {omega : Real} (h0ω : 0 < omega)
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (T n c0 : Real) (hT : 0 < T) (hTω : T < omega)
    (hn : n ≠ 0)
    (scalar scalarLap ricciNormSq : Real -> M -> Real) (K : NNReal)
    (hden : ∀ t : Real, t ∈ Set.Icc 0 T ->
      0 < 1 - (2 / n) * c0 * t)
    (hreg : ScalarLowerBoundWMPRegularity (I := I) G T n c0 scalar K)
    (hevol : ScalarEvolutionEquationOn
      (D := DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen 0 omega h0ω)
      scalar scalarLap ricciNormSq)
    (hlap : ScalarLaplacianRealizesHeatOperatorOn (I := I) G T scalar scalarLap)
    (hricci : ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M,
      (1 / n) * (scalar t x) ^ 2 <= ricciNormSq t x)
    (hinit : InitialScalarLowerBound (M := M) scalar c0)
    (hF_lip : ∀ t : Real, t ∈ Set.Icc 0 T ->
      LipschitzOnWith K (fun a : Real => scalarLowerReaction n a t)
        (DifferentialGeometry.Integral.Connection.scalarWMPValueSet (M := M) T scalar
          (scalarLowerBarrier n c0))) :
    ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M,
      scalarLowerBarrier n c0 t <= scalar t x := by
  have hslab :
      Set.Icc 0 T ⊆
        (DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen 0 omega h0ω).carrier := by
    intro t ht
    change t ∈ Set.Ico 0 omega
    exact ⟨ht.1, lt_of_le_of_lt ht.2 hTω⟩
  have hregular :
      ∀ t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
        t ∈ (DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen 0 omega h0ω).regular := by
    intro t ht htpos
    change t ∈ Set.Ioo 0 omega
    exact ⟨htpos, lt_of_le_of_lt ht.2 hTω⟩
  exact scalar_curvature_lower_bound_of_scalarEvolution_of_regularity
    (I := I) (D := DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen 0 omega h0ω)
    G T n c0 hT hn scalar scalarLap ricciNormSq K
    hslab hregular hden hreg hevol hlap hricci hinit hF_lip



theorem scalar_curvature_lower_bound_of_scalarEvolution_initialMinimum
    [I.Boundaryless] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (T n c0 : Real) (hT : 0 < T)
    (hn : n ≠ 0)
    (scalar scalarLap ricciNormSq : Real -> M -> Real) (K : NNReal)
    (hslab : Set.Icc 0 T ⊆ D.carrier)
    (hregular : ∀ t : Real, t ∈ Set.Icc 0 T -> 0 < t -> t ∈ D.regular)
    (hden : ∀ t : Real, t ∈ Set.Icc 0 T ->
      0 < 1 - (2 / n) * c0 * t)
    (hw_cont : ContinuousOn
      (fun p : Real × M =>
        Real.exp (-(K : Real) * p.1) *
          (scalar p.1 p.2 - scalarLowerBarrier n c0 p.1))
      (DifferentialGeometry.Integral.Connection.spacetimeSlab (M := M) T))
    (hw_mdiff : ∀ t : Real, t ∈ Set.Icc 0 T ->
      ∀ x : M, MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M =>
          Real.exp (-(K : Real) * t) *
            (scalar t y - scalarLowerBarrier n c0 t)) x)
    (hw_grad : ∀ t : Real, t ∈ Set.Icc 0 T ->
      ∀ x : M, MDiffAt (T% fun y : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t)
          (fun z : M =>
            Real.exp (-(K : Real) * t) *
              (scalar t z - scalarLowerBarrier n c0 t)) y) x)
    (hscalar_time : ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M,
      DifferentiableWithinAt Real (fun s : Real => scalar s x) (Set.Icc 0 T) t)
    (hscalar_space : ∀ t : Real, t ∈ Set.Icc 0 T ->
      ∀ y : M, MDifferentiableAt I 𝓘(Real, Real) (scalar t) y)
    (hdiff_space : ∀ t : Real, t ∈ Set.Icc 0 T ->
      ∀ y : M, MDifferentiableAt I 𝓘(Real, Real)
        (fun z : M => scalar t z - scalarLowerBarrier n c0 t) y)
    (hdiff_grad : ∀ t : Real, t ∈ Set.Icc 0 T ->
      ∀ x : M, MDiffAt (T% fun y : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t)
          (fun z : M => scalar t z - scalarLowerBarrier n c0 t) y) x)
    (hevol : ScalarEvolutionEquationOn (D := D) scalar scalarLap ricciNormSq)
    (hlap : ScalarLaplacianRealizesHeatOperatorOn (I := I) G T scalar scalarLap)
    (hricci : ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M,
      (1 / n) * (scalar t x) ^ 2 <= ricciNormSq t x)
    (hinit : InitialScalarMinimum (M := M) scalar c0)
    (hF_lip : ∀ t : Real, t ∈ Set.Icc 0 T ->
      LipschitzOnWith K (fun a : Real => scalarLowerReaction n a t)
        (DifferentialGeometry.Integral.Connection.scalarWMPValueSet (M := M) T scalar
          (scalarLowerBarrier n c0))) :
    ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M,
      scalarLowerBarrier n c0 t <= scalar t x :=
  scalar_curvature_lower_bound_of_scalarEvolution
    (I := I) (D := D) G T n c0 hT hn scalar scalarLap ricciNormSq K
    hslab hregular hden
    hw_cont hw_mdiff hw_grad hscalar_time hscalar_space hdiff_space
    hdiff_grad hevol hlap hricci
    (InitialScalarMinimum.lowerBound (M := M) hinit) hF_lip




@[deprecated "use a local or intrinsic scalar lower-bound route instead" (since := "2026-05-22")]
theorem scalar_curvature_lower_bound_of_scalarEvolution_inFrame
    [I.Boundaryless] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] [Nonempty Idx]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    {u : Set M}
    (S : SolutionOn (I := I) (M := M) D)
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (T n c0 : Real) (hT : 0 < T)
    (hn_ne : n ≠ 0)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hcover : forall x : M, x ∈ u)
    (hinv : InvMetricLocal (I := I) S gInv frame u)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (hn_rank : n = (Fintype.card Idx : Real))
    (K : NNReal)
    (hslab : Set.Icc 0 T ⊆ D.carrier)
    (hregular : ∀ t : Real, t ∈ Set.Icc 0 T -> 0 < t -> t ∈ D.regular)
    (hden : ∀ t : Real, t ∈ Set.Icc 0 T ->
      0 < 1 - (2 / n) * c0 * t)
    (hw_cont : ContinuousOn
      (fun p : Real × M =>
        Real.exp (-(K : Real) * p.1) *
          (scalarTraceInFrame (I := I) S gInv frame p.1 p.2 -
            scalarLowerBarrier n c0 p.1))
      (DifferentialGeometry.Integral.Connection.spacetimeSlab (M := M) T))
    (hw_mdiff : ∀ t : Real, t ∈ Set.Icc 0 T ->
      ∀ x : M, MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M =>
          Real.exp (-(K : Real) * t) *
            (scalarTraceInFrame (I := I) S gInv frame t y -
              scalarLowerBarrier n c0 t)) x)
    (hw_grad : ∀ t : Real, t ∈ Set.Icc 0 T ->
      ∀ x : M, MDiffAt (T% fun y : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t)
          (fun z : M =>
            Real.exp (-(K : Real) * t) *
              (scalarTraceInFrame (I := I) S gInv frame t z -
                scalarLowerBarrier n c0 t)) y) x)
    (hscalar_time : ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M,
      DifferentiableWithinAt Real
        (fun s : Real => scalarTraceInFrame (I := I) S gInv frame s x)
        (Set.Icc 0 T) t)
    (hscalar_space : ∀ t : Real, t ∈ Set.Icc 0 T ->
      ∀ y : M, MDifferentiableAt I 𝓘(Real, Real)
        (scalarTraceInFrame (I := I) S gInv frame t) y)
    (hdiff_space : ∀ t : Real, t ∈ Set.Icc 0 T ->
      ∀ y : M, MDifferentiableAt I 𝓘(Real, Real)
        (fun z : M =>
          scalarTraceInFrame (I := I) S gInv frame t z -
            scalarLowerBarrier n c0 t) y)
    (hdiff_grad : ∀ t : Real, t ∈ Set.Icc 0 T ->
      ∀ x : M, MDiffAt (T% fun y : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t)
          (fun z : M =>
            scalarTraceInFrame (I := I) S gInv frame t z -
              scalarLowerBarrier n c0 t) y) x)
    (hevol : ScalarEvolutionEquationOn (D := D)
      (scalarTraceInFrame (I := I) S gInv frame)
      (scalarLaplacianTraceInFrame (M := M) gInv roughLapRic)
      (ricciNormSqInFrame (I := I) S gInv frame))
    (hlap : ScalarLaplacianRealizesHeatOperatorOn (I := I) G T
      (scalarTraceInFrame (I := I) S gInv frame)
      (scalarLaplacianTraceInFrame (M := M) gInv roughLapRic))
    (hinit : InitialScalarLowerBound (M := M)
      (scalarTraceInFrame (I := I) S gInv frame) c0)
    (hF_lip : ∀ t : Real, t ∈ Set.Icc 0 T ->
      LipschitzOnWith K (fun a : Real => scalarLowerReaction n a t)
        (DifferentialGeometry.Integral.Connection.scalarWMPValueSet (M := M) T
          (scalarTraceInFrame (I := I) S gInv frame)
          (scalarLowerBarrier n c0))) :
    ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M,
      scalarLowerBarrier n c0 t <=
        scalarTraceInFrame (I := I) S gInv frame t x := by
  have hricci :
      ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M,
        (1 / n) * (scalarTraceInFrame (I := I) S gInv frame t x) ^ 2 <=
          ricciNormSqInFrame (I := I) S gInv frame t x := by
    have hcs :=
      RicciTraceNormCauchySchwarzInFrame.of_metric_inverse_frame
        (I := I) S gInv frame hframe hcover hinv n hn_rank
    intro t _ht x
    exact hcs t x
  exact scalar_curvature_lower_bound_of_scalarEvolution
    (I := I) (D := D) G T n c0 hT hn_ne
    (scalarTraceInFrame (I := I) S gInv frame)
    (scalarLaplacianTraceInFrame (M := M) gInv roughLapRic)
    (ricciNormSqInFrame (I := I) S gInv frame) K hslab hregular hden
    hw_cont hw_mdiff hw_grad hscalar_time hscalar_space hdiff_space
    hdiff_grad hevol hlap hricci hinit hF_lip



@[deprecated "use a local or intrinsic scalar lower-bound route instead" (since := "2026-05-22")]
theorem scalar_curvature_lower_bound_of_scalarEvolution_inFrame_closedOpen
    [I.Boundaryless] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] [Nonempty Idx]
    {omega : Real} (h0ω : 0 < omega)
    {u : Set M}
    (S : SolutionOn (I := I) (M := M)
      (DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen 0 omega h0ω))
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (T n c0 : Real) (hT : 0 < T) (hTω : T < omega)
    (hn_ne : n ≠ 0)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hcover : forall x : M, x ∈ u)
    (hinv : InvMetricLocal (I := I) S gInv frame u)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (hn_rank : n = (Fintype.card Idx : Real))
    (K : NNReal)
    (hden : ∀ t : Real, t ∈ Set.Icc 0 T ->
      0 < 1 - (2 / n) * c0 * t)
    (hreg : ScalarLowerBoundWMPRegularity (I := I) G T n c0
      (scalarTraceInFrame (I := I) S gInv frame) K)
    (hevol : ScalarEvolutionEquationOn
      (D := DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen 0 omega h0ω)
      (scalarTraceInFrame (I := I) S gInv frame)
      (scalarLaplacianTraceInFrame (M := M) gInv roughLapRic)
      (ricciNormSqInFrame (I := I) S gInv frame))
    (hlap : ScalarLaplacianRealizesHeatOperatorOn (I := I) G T
      (scalarTraceInFrame (I := I) S gInv frame)
      (scalarLaplacianTraceInFrame (M := M) gInv roughLapRic))
    (hinit : InitialScalarLowerBound (M := M)
      (scalarTraceInFrame (I := I) S gInv frame) c0)
    (hF_lip : ∀ t : Real, t ∈ Set.Icc 0 T ->
      LipschitzOnWith K (fun a : Real => scalarLowerReaction n a t)
        (DifferentialGeometry.Integral.Connection.scalarWMPValueSet (M := M) T
          (scalarTraceInFrame (I := I) S gInv frame)
          (scalarLowerBarrier n c0))) :
    ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M,
      scalarLowerBarrier n c0 t <=
        scalarTraceInFrame (I := I) S gInv frame t x := by
  have hslab :
      Set.Icc 0 T ⊆
        (DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen 0 omega h0ω).carrier := by
    intro t ht
    change t ∈ Set.Ico 0 omega
    exact ⟨ht.1, lt_of_le_of_lt ht.2 hTω⟩
  have hregular :
      ∀ t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
        t ∈ (DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen 0 omega h0ω).regular := by
    intro t ht htpos
    change t ∈ Set.Ioo 0 omega
    exact ⟨htpos, lt_of_le_of_lt ht.2 hTω⟩
  have hricci :
      ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M,
        (1 / n) * (scalarTraceInFrame (I := I) S gInv frame t x) ^ 2 <=
          ricciNormSqInFrame (I := I) S gInv frame t x := by
    have hcs :=
      RicciTraceNormCauchySchwarzInFrame.of_metric_inverse_frame
        (I := I) S gInv frame hframe hcover hinv n hn_rank
    intro t _ht x
    exact hcs t x
  exact scalar_curvature_lower_bound_of_scalarEvolution_of_regularity
    (I := I) (D := DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen 0 omega h0ω)
    G T n c0 hT hn_ne
    (scalarTraceInFrame (I := I) S gInv frame)
    (scalarLaplacianTraceInFrame (M := M) gInv roughLapRic)
    (ricciNormSqInFrame (I := I) S gInv frame) K
    hslab hregular hden hreg hevol hlap hricci hinit hF_lip

end DifferentialGeometry.PDE.RicciFlow
