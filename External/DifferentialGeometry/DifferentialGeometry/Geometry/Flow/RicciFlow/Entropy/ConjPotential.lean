import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.ScalarPotential
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.BochnerL2
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Scalar.Uniform
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Scalar.JointRegularity

set_option autoImplicit false










noncomputable section

open Bundle Filter MeasureTheory Set
open scoped Manifold Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Entropy

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete Real E
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩



noncomputable def conjCoeff
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    C^∞⟮I, M; Real⟯ :=
  ⟨fun x => -metricScalarAt (I := I) (M := M) (S.family.metric t) x,
    (metricScalar_smooth (I := I) (M := M) (S.family.metric t)).neg⟩

omit [NeZero (Module.finrank Real E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] in

omit [SigmaCompactSpace M] in
@[simp] theorem conjCoeff_apply
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (t : Real) (x : M) :
    (conjCoeff (I := I) (M := M) S t : M → Real) x = -S.scalar t x := by
  rfl

omit [NeZero (Module.finrank Real E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] in


theorem conjCoeff_joint
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) :
    ContMDiffOn ((modelWithCornersSelf Real Real).prod I)
      (modelWithCornersSelf Real Real) ∞
      (fun p : Real × M =>
        (conjCoeff (I := I) (M := M) S p.1 : M → Real) p.2)
      (D.regular ×ˢ (Set.univ : Set M)) := by
  simpa only [conjCoeff_apply] using
    (scalar_joint (I := I) S hS).neg



noncomputable def conjCoeffRev
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (T : Real) :
    M × Real → Real := fun p =>
  (conjCoeff (I := I) (M := M) S (T - p.2) : M → Real) p.1

omit [NeZero (Module.finrank Real E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] in


theorem conjCoeff_rev
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : D.RegularTime) :
    ContMDiffOn (I.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real Real) ∞
      (conjCoeffRev (I := I) (M := M) S (T : Real))
      ((Set.univ : Set M) ×ˢ {s : Real | (T : Real) - s ∈ D.regular}) := by
  have hmove :
      ContMDiffOn (I.prod (modelWithCornersSelf Real Real))
        ((modelWithCornersSelf Real Real).prod I) ∞
        (fun p : M × Real => ((T : Real) - p.2, p.1))
        ((Set.univ : Set M) ×ˢ {s : Real | (T : Real) - s ∈ D.regular}) := by
    exact ContMDiffOn.prodMk
      (ContMDiffOn.sub contMDiffOn_const contMDiffOn_snd)
      contMDiffOn_fst
  simpa only [conjCoeffRev] using
    (conjCoeff_joint (I := I) S hS).comp hmove
      (fun p hp => ⟨hp.2, Set.mem_univ p.1⟩)



noncomputable def conjA1
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (T : D.RegularTime) (s : Real) :
    tensorHs (I := I) (M := M) (S.family.metric (T : Real)) 0 0 1 →L[Real]
      tensorHs (I := I) (M := M) (S.family.metric (T : Real)) 0 0 0 :=
  scalarPotH0 (I := I) (M := M) (S.family.metric (T : Real))
    (conjCoeff (I := I) (M := M) S ((T : Real) - s))



omit [BoundarylessManifold I M] in
theorem conjA1_cont
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : D.RegularTime) {A : Set Real}
    (hreg : ∀ s ∈ A, (T : Real) - s ∈ D.regular) :
    ContinuousOn (fun s : Real => conjA1 (I := I) (M := M) S T s) A := by
  letI : SeminormedAddCommGroup
      (tensorHs (I := I) (M := M) (S.family.metric (T : Real)) 0 0 1 →L[Real]
        tensorHs (I := I) (M := M) (S.family.metric (T : Real)) 0 0 0) :=
    ContinuousLinearMap.toSeminormedAddCommGroup
  intro s0 hs0
  let K : D.RegularTime := ⟨(T : Real) - s0, hreg s0 hs0⟩
  have hshift :
      Tendsto (fun s : Real => (T : Real) - s)
        (𝓝 s0) (𝓝 (K : Real)) := by
    dsimp only [K]
    simpa only using
      (tendsto_const_nhds.sub
        (tendsto_id : Tendsto (fun s : Real => s) (𝓝 s0) (𝓝 s0)))
  change Tendsto
    (fun s : Real => conjA1 (I := I) (M := M) S T s)
    (𝓝[A] s0) (𝓝 (conjA1 (I := I) (M := M) S T s0))
  rw [Metric.tendsto_nhds]
  intro eta heta
  have heta2 : 0 < eta / 2 := half_pos heta
  have hcoef0 :
      ∀ᶠ t in 𝓝 (K : Real), ∀ x : M,
        |S.scalar t x - S.scalar (K : Real) x| < eta / 2 :=
    scalar_unif (I := I) S hS K heta2
  have hcoef :
      ∀ᶠ s in 𝓝 s0, ∀ x : M,
        |S.scalar ((T : Real) - s) x -
          S.scalar ((T : Real) - s0) x| < eta / 2 := by
    exact hshift.eventually hcoef0
  filter_upwards [hcoef.filter_mono inf_le_left] with s hs
  rw [dist_eq_norm]
  have hpair := scalarPotH0_pair (I := I) (M := M)
    (S.family.metric (T : Real))
    (conjCoeff (I := I) (M := M) S ((T : Real) - s))
    (conjCoeff (I := I) (M := M) S ((T : Real) - s0)) heta2.le
    (fun x => by
      change |-S.scalar ((T : Real) - s) x -
        -S.scalar ((T : Real) - s0) x| ≤ eta / 2
      rw [neg_sub_neg, abs_sub_comm]
      exact (hs x).le)
  have hop :
      ‖conjA1 (I := I) (M := M) S T s -
          conjA1 (I := I) (M := M) S T s0‖ ≤ eta / 2 := by
    simpa only [conjA1] using hpair
  exact hop.trans_lt (half_lt_self heta)




omit [BoundarylessManifold I M] in
theorem conjA1_short
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : D.RegularTime) :
    ∃ tau : Real, 0 < tau ∧ tau ≤ 1 ∧
      ∃ C1 : NNReal,
        ContinuousOn (fun s : Real => conjA1 (I := I) (M := M) S T s)
          (Set.Icc 0 tau) ∧
        AEStronglyMeasurable
          (fun s : Real => conjA1 (I := I) (M := M) S T s)
          (timeMeasure tau) ∧
        (∀ s ∈ Set.Icc 0 tau,
          ‖conjA1 (I := I) (M := M) S T s‖ ≤ (C1 : Real)) ∧
        ∀ᵐ s ∂timeMeasure tau,
          ‖conjA1 (I := I) (M := M) S T s‖ ≤ (C1 : Real) := by
  letI : SeminormedAddCommGroup
      (tensorHs (I := I) (M := M) (S.family.metric (T : Real)) 0 0 1 →L[Real]
        tensorHs (I := I) (M := M) (S.family.metric (T : Real)) 0 0 0) :=
    ContinuousLinearMap.toSeminormedAddCommGroup
  have hshift :
      Tendsto (fun s : Real => (T : Real) - s)
        (𝓝 0) (𝓝 (T : Real)) := by
    simpa only [sub_zero] using
      (tendsto_const_nhds.sub
        (tendsto_id : Tendsto (fun s : Real => s) (𝓝 0) (𝓝 0)))
  have hreg :
      ∀ᶠ s in 𝓝 (0 : Real), (T : Real) - s ∈ D.regular :=
    hshift.eventually (D.regular_isOpen.mem_nhds T.2)
  have hcoef :
      ∀ᶠ s in 𝓝 (0 : Real), ∀ x : M,
        |S.scalar ((T : Real) - s) x - S.scalar (T : Real) x| < 1 :=
    hshift.eventually (scalar_unif (I := I) S hS T zero_lt_one)
  let U : Set Real := {s |
    (T : Real) - s ∈ D.regular ∧
      ∀ x : M,
        |S.scalar ((T : Real) - s) x - S.scalar (T : Real) x| ≤ 1}
  have hU : U ∈ 𝓝 (0 : Real) := by
    change ∀ᶠ s in 𝓝 (0 : Real),
      (T : Real) - s ∈ D.regular ∧
        ∀ x : M,
          |S.scalar ((T : Real) - s) x - S.scalar (T : Real) x| ≤ 1
    filter_upwards [hreg, hcoef] with s hs hc
    exact ⟨hs, fun x => (hc x).le⟩
  obtain ⟨delta, hdelta, hball⟩ := Metric.mem_nhds_iff.mp hU
  let tau : Real := min 1 (delta / 2)
  have htaupos : 0 < tau := by
    dsimp only [tau]
    exact lt_min zero_lt_one (half_pos hdelta)
  have htauone : tau ≤ 1 := min_le_left _ _
  have htaudelta : tau < delta :=
    (min_le_right (1 : Real) (delta / 2)).trans_lt (half_lt_self hdelta)
  have hIccU : Set.Icc (0 : Real) tau ⊆ U := by
    intro s hs
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hs.1]
    exact hs.2.trans_lt htaudelta
  have hgood (s : Real) (hs : s ∈ Set.Icc (0 : Real) tau) :
      (T : Real) - s ∈ D.regular ∧
        ∀ x : M,
          |S.scalar ((T : Real) - s) x - S.scalar (T : Real) x| ≤ 1 := by
    simpa only [U] using hIccU hs
  have hRcont : Continuous (fun x : M => |S.scalar (T : Real) x|) := by
    have hscalar := metricScalar_smooth (I := I) (M := M)
      (S.family.metric (T : Real))
    simpa only [SolutionOn.scalar, SolutionFamily.scalar, SolutionOn.family]
      using hscalar.continuous.abs
  have hcompact : IsCompact (Set.range (fun x : M => |S.scalar (T : Real) x|)) :=
    isCompact_range hRcont
  obtain ⟨C0, hC0⟩ := hcompact.bddAbove
  have hC0x (x : M) : |S.scalar (T : Real) x| ≤ C0 :=
    hC0 ⟨x, rfl⟩
  let B : Real := max 0 C0 + 1
  have hB0 : 0 ≤ B := by
    dsimp only [B]
    positivity
  let C1 : NNReal := ⟨B, hB0⟩
  have hcoefBound (s : Real) (hs : s ∈ Set.Icc (0 : Real) tau) (x : M) :
      |(conjCoeff (I := I) (M := M) S ((T : Real) - s) : M → Real) x| ≤ B := by
    rw [conjCoeff_apply, abs_neg]
    calc
      |S.scalar ((T : Real) - s) x| =
          |(S.scalar ((T : Real) - s) x - S.scalar (T : Real) x) +
            S.scalar (T : Real) x| := by
        congr 1
        ring
      _ ≤ |S.scalar ((T : Real) - s) x - S.scalar (T : Real) x| +
          |S.scalar (T : Real) x| := abs_add_le _ _
      _ ≤ 1 + C0 := add_le_add ((hgood s hs).2 x) (hC0x x)
      _ = C0 + 1 := add_comm _ _
      _ ≤ max 0 C0 + 1 := add_le_add (le_max_right 0 C0) le_rfl
      _ = B := rfl
  have hcont :
      ContinuousOn (fun s : Real => conjA1 (I := I) (M := M) S T s)
        (Set.Icc 0 tau) :=
    conjA1_cont (I := I) (M := M) S hS T
      (fun s hs => (hgood s hs).1)
  have hmeas :
      AEStronglyMeasurable
        (fun s : Real => conjA1 (I := I) (M := M) S T s)
        (timeMeasure tau) := by
    unfold timeMeasure
    exact hcont.aestronglyMeasurable measurableSet_Icc
  have hboundOn :
      ∀ s ∈ Set.Icc (0 : Real) tau,
        ‖conjA1 (I := I) (M := M) S T s‖ ≤ (C1 : Real) := by
    intro s hs
    rw [conjA1, scalarPotH0_norm]
    exact scalarPotOp_norm (I := I) (M := M)
      (S.family.metric (T : Real))
      (conjCoeff (I := I) (M := M) S ((T : Real) - s)) hB0
      (hcoefBound s hs)
  have hboundAE :
      ∀ᵐ s ∂timeMeasure tau,
        ‖conjA1 (I := I) (M := M) S T s‖ ≤ (C1 : Real) := by
    unfold timeMeasure
    exact (ae_restrict_iff' measurableSet_Icc).2
      (Eventually.of_forall hboundOn)
  exact ⟨tau, htaupos, htauone, C1, hcont, hmeas, hboundOn, hboundAE⟩

omit [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [BoundarylessManifold I M] in


omit [SigmaCompactSpace M] in
theorem conjCoeff_bound
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : D.RegularTime) :
    ∃ tau : Real, 0 < tau ∧ tau ≤ 1 ∧
      ∃ C : Real, 0 ≤ C ∧
        ∀ s ∈ Set.Icc (0 : Real) tau, ∀ x : M,
          |(conjCoeff (I := I) (M := M) S
            ((T : Real) - s) : M → Real) x| ≤ C := by
  have hshift :
      Tendsto (fun s : Real => (T : Real) - s)
        (𝓝 0) (𝓝 (T : Real)) := by
    simpa only [sub_zero] using
      (tendsto_const_nhds.sub
        (tendsto_id : Tendsto (fun s : Real => s) (𝓝 0) (𝓝 0)))
  have hcoef :
      ∀ᶠ s in 𝓝 (0 : Real), ∀ x : M,
        |S.scalar ((T : Real) - s) x - S.scalar (T : Real) x| < 1 :=
    hshift.eventually (scalar_unif (I := I) S hS T zero_lt_one)
  let U : Set Real := {s |
    ∀ x : M,
      |S.scalar ((T : Real) - s) x - S.scalar (T : Real) x| ≤ 1}
  have hU : U ∈ 𝓝 (0 : Real) := by
    change ∀ᶠ s in 𝓝 (0 : Real),
      ∀ x : M,
        |S.scalar ((T : Real) - s) x - S.scalar (T : Real) x| ≤ 1
    filter_upwards [hcoef] with s hs
    exact fun x => (hs x).le
  obtain ⟨delta, hdelta, hball⟩ := Metric.mem_nhds_iff.mp hU
  let tau : Real := min 1 (delta / 2)
  have htau : 0 < tau := by
    dsimp only [tau]
    exact lt_min zero_lt_one (half_pos hdelta)
  have htau_one : tau ≤ 1 := min_le_left _ _
  have htau_delta : tau < delta :=
    (min_le_right (1 : Real) (delta / 2)).trans_lt
      (half_lt_self hdelta)
  have hgood (s : Real) (hs : s ∈ Set.Icc (0 : Real) tau) : s ∈ U := by
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hs.1]
    exact hs.2.trans_lt htau_delta
  have hRcont : Continuous (fun x : M => |S.scalar (T : Real) x|) := by
    have hscalar := metricScalar_smooth (I := I) (M := M)
      (S.family.metric (T : Real))
    simpa only [SolutionOn.scalar, SolutionFamily.scalar, SolutionOn.family]
      using hscalar.continuous.abs
  obtain ⟨C0, hC0⟩ := (isCompact_range hRcont).bddAbove
  have hC0x (x : M) : |S.scalar (T : Real) x| ≤ C0 :=
    hC0 ⟨x, rfl⟩
  let C : Real := max 0 C0 + 1
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  refine ⟨tau, htau, htau_one, C, hC, ?_⟩
  intro s hs x
  rw [conjCoeff_apply, abs_neg]
  calc
    |S.scalar ((T : Real) - s) x| =
        |(S.scalar ((T : Real) - s) x - S.scalar (T : Real) x) +
          S.scalar (T : Real) x| := by
      congr 1
      ring
    _ ≤ |S.scalar ((T : Real) - s) x - S.scalar (T : Real) x| +
        |S.scalar (T : Real) x| := abs_add_le _ _
    _ ≤ 1 + C0 := add_le_add (hgood s hs x) (hC0x x)
    _ = C0 + 1 := add_comm _ _
    _ ≤ max 0 C0 + 1 := add_le_add (le_max_right 0 C0) le_rfl
    _ = C := rfl

end DifferentialGeometry.PDE.RicciFlow.Entropy

end
