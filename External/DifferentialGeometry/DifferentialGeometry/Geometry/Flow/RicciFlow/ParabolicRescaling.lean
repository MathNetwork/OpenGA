import DifferentialGeometry.Geometry.Flow.RicciFlow.Basic
import DifferentialGeometry.Geometry.Connection.LeviCivita.Scaling
import DifferentialGeometry.Geometry.Operator.Scaling
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Scaling

set_option autoImplicit false
set_option linter.style.longLine false








noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M]
variable [SigmaCompactSpace M] [T2Space M]



def paraTime (τ R s : Real) : Real :=
  τ + s / R



def paraBack (τ R t : Real) : Real :=
  R * (t - τ)

@[simp] theorem paraTime_zero (τ R : Real) :
    paraTime τ R 0 = τ := by
  simp [paraTime]

@[simp] theorem paraBack_self (τ R : Real) :
    paraBack τ R τ = 0 := by
  simp [paraBack]

theorem paraTime_back {τ R t : Real} (hR : R ≠ 0) :
    paraTime τ R (paraBack τ R t) = t := by
  unfold paraTime paraBack
  field_simp [hR]
  ring

theorem paraBack_time {τ R s : Real} (hR : R ≠ 0) :
    paraBack τ R (paraTime τ R s) = s := by
  unfold paraTime paraBack
  field_simp [hR]
  ring

private theorem mul_paraTime_eq {τ R s : Real} (hR : R ≠ 0) :
    R * paraTime τ R s = R * τ + s := by
  unfold paraTime
  field_simp [hR]


def paraInterval
    (D : DifferentialGeometry.Integral.Connection.RealTimeInterval) (τ R : Real) (_hR : 0 < R)
    (hτ : τ ∈ D.carrier) : DifferentialGeometry.Integral.Connection.RealTimeInterval where
  carrier := {s : Real | paraTime τ R s ∈ D.carrier}
  regular := {s : Real | paraTime τ R s ∈ D.regular}
  initial := 0
  initial_mem := by
    simpa [paraTime] using hτ
  regular_subset := by
    intro s hs
    exact D.regular_subset hs
  regular_isOpen := by
    have hcont : Continuous (fun r : Real => paraTime τ R r) := by
      unfold paraTime
      fun_prop
    exact hcont.isOpen_preimage _ D.regular_isOpen
  regular_mem_nhds := by
    intro s hs
    have hcont : ContinuousAt (fun r : Real => paraTime τ R r) s := by
      unfold paraTime
      fun_prop
    simpa [Set.preimage] using hcont.preimage_mem_nhds (D.regular_mem_nhds hs)

@[simp] theorem paraInterval_carrier
    (D : DifferentialGeometry.Integral.Connection.RealTimeInterval) (τ R : Real) (hR : 0 < R)
    (hτ : τ ∈ D.carrier) :
    (paraInterval D τ R hR hτ).carrier =
      {s : Real | paraTime τ R s ∈ D.carrier} := by
  rfl

@[simp] theorem paraInterval_regular
    (D : DifferentialGeometry.Integral.Connection.RealTimeInterval) (τ R : Real) (hR : 0 < R)
    (hτ : τ ∈ D.carrier) :
    (paraInterval D τ R hR hτ).regular =
      {s : Real | paraTime τ R s ∈ D.regular} := by
  rfl

theorem paraInterval_closedOpen_carrier
    {T τ R : Real} (hT : 0 < T) (hR : 0 < R)
    (hτ : τ ∈ (DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen 0 T hT).carrier) :
    (paraInterval (DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen 0 T hT)
        τ R hR hτ).carrier =
      Set.Ico (-(R * τ)) (R * (T - τ)) := by
  ext s
  constructor
  · intro hs
    rcases hs with ⟨hlo, hhi⟩
    dsimp [paraTime] at hlo hhi
    have heq : R * paraTime τ R s = R * τ + s :=
      mul_paraTime_eq (τ := τ) (R := R) (s := s) (ne_of_gt hR)
    have hlo' : 0 <= R * paraTime τ R s := by
      exact mul_nonneg (le_of_lt hR) hlo
    have hhi' : R * paraTime τ R s < R * T := by
      exact mul_lt_mul_of_pos_left hhi hR
    constructor <;> nlinarith
  · intro hs
    rcases hs with ⟨hlo, hhi⟩
    have heq : R * paraTime τ R s = R * τ + s :=
      mul_paraTime_eq (τ := τ) (R := R) (s := s) (ne_of_gt hR)
    have hlo' : 0 <= R * paraTime τ R s := by
      rw [heq]
      nlinarith
    have hhi' : R * paraTime τ R s < R * T := by
      rw [heq]
      nlinarith
    constructor
    · have hdiv : 0 <= (R * paraTime τ R s) / R := div_nonneg hlo' (le_of_lt hR)
      rwa [mul_div_cancel_left₀ (paraTime τ R s) (ne_of_gt hR)] at hdiv
    · have hdiv : (R * paraTime τ R s) / R < (R * T) / R :=
        div_lt_div_of_pos_right hhi' hR
      rwa [mul_div_cancel_left₀ (paraTime τ R s) (ne_of_gt hR),
        mul_div_cancel_left₀ T (ne_of_gt hR)] at hdiv

theorem paraInterval_closedOpen_regular
    {T τ R : Real} (hT : 0 < T) (hR : 0 < R)
    (hτ : τ ∈ (DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen 0 T hT).carrier) :
    (paraInterval (DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen 0 T hT)
        τ R hR hτ).regular =
      Set.Ioo (-(R * τ)) (R * (T - τ)) := by
  ext s
  constructor
  · intro hs
    rcases hs with ⟨hlo, hhi⟩
    dsimp [paraTime] at hlo hhi
    have heq : R * paraTime τ R s = R * τ + s :=
      mul_paraTime_eq (τ := τ) (R := R) (s := s) (ne_of_gt hR)
    have hlo' : 0 < R * paraTime τ R s := by
      exact mul_pos hR hlo
    have hhi' : R * paraTime τ R s < R * T := by
      exact mul_lt_mul_of_pos_left hhi hR
    constructor <;> nlinarith
  · intro hs
    rcases hs with ⟨hlo, hhi⟩
    have heq : R * paraTime τ R s = R * τ + s :=
      mul_paraTime_eq (τ := τ) (R := R) (s := s) (ne_of_gt hR)
    have hlo' : 0 < R * paraTime τ R s := by
      rw [heq]
      nlinarith
    have hhi' : R * paraTime τ R s < R * T := by
      rw [heq]
      nlinarith
    constructor
    · have hdiv : 0 < (R * paraTime τ R s) / R := div_pos hlo' hR
      rwa [mul_div_cancel_left₀ (paraTime τ R s) (ne_of_gt hR)] at hdiv
    · have hdiv : (R * paraTime τ R s) / R < (R * T) / R :=
        div_lt_div_of_pos_right hhi' hR
      rwa [mul_div_cancel_left₀ (paraTime τ R s) (ne_of_gt hR),
        mul_div_cancel_left₀ T (ne_of_gt hR)] at hdiv



def paraFamily
    (G : SolutionFamily (I := I) (M := M)) (τ R : Real) (hR : 0 < R) :
    SolutionFamily (I := I) (M := M) where
  metric s := scaleMetric (I := I) R hR (G.metric (paraTime τ R s))


def paraBackFamily
    (G : SolutionFamily (I := I) (M := M)) (τ R : Real) (hR : 0 < R) :
    SolutionFamily (I := I) (M := M) where
  metric t := scaleMetric (I := I) R⁻¹ (inv_pos.mpr hR)
    (G.metric (paraBack τ R t))


def paraSolution
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (τ R : Real) (hR : 0 < R) (hτ : τ ∈ D.carrier) :
    SolutionOn (I := I) (M := M) (paraInterval D τ R hR hτ) where
  base := paraFamily (I := I) S.base τ R hR

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I 1 M] [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem paraSolution_metric
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (τ R : Real) (hR : 0 < R) (hτ : τ ∈ D.carrier) :
    (paraSolution (I := I) S τ R hR hτ).base.metric =
      fun s => scaleMetric (I := I) R hR (S.base.metric (paraTime τ R s)) := by
  rfl

omit [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem paraSolution_connection
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (τ R : Real) (hR : 0 < R) (hτ : τ ∈ D.carrier) :
    (paraSolution (I := I) S τ R hR hτ).base.connection =
      fun s => S.base.connection (paraTime τ R s) := by
  funext s
  simp [paraSolution, paraFamily, SolutionFamily.connection,
    DifferentialGeometry.Integral.Connection.lcConn_scaleMetric]

omit [SigmaCompactSpace M] in
@[simp] theorem paraSolution_ricci
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (τ R : Real) (hR : 0 < R) (hτ : τ ∈ D.carrier) :
    (paraSolution (I := I) S τ R hR hτ).base.ricci =
      fun s => S.base.ricci (paraTime τ R s) := by
  funext s
  simp [paraSolution, paraFamily, SolutionFamily.ricci, metricRicci,
    DifferentialGeometry.Integral.Connection.metricRicci, DifferentialGeometry.Integral.Connection.metricCov, DifferentialGeometry.Integral.Connection.lcConn_scaleMetric]

omit [SigmaCompactSpace M] in
private theorem metricRm04_scaleMetric
    (c : Real) (hc : 0 < c) (g : SmoothRiemannianMetric I M) (x : M) :
    DifferentialGeometry.Integral.Connection.metricRm04 (I := I) (M := M) (scaleMetric (I := I) c hc g) x =
      c • DifferentialGeometry.Integral.Connection.metricRm04 (I := I) (M := M) g x := by
  ext v
  have hv :
      v = DifferentialGeometry.Integral.Connection.vec4 (I := I) (v 0) (v 1) (v 2) (v 3) := by
    funext i
    fin_cases i <;> simp [DifferentialGeometry.Integral.Connection.vec4]
  rw [hv]
  simp [DifferentialGeometry.Integral.Connection.metricRm04, DifferentialGeometry.Integral.Connection.metricCov, scaleMetric_inner,
    DifferentialGeometry.Integral.Connection.lcConn_scaleMetric, smul_eq_mul]

omit [SigmaCompactSpace M] in
@[simp] theorem paraSolution_rm04
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (τ R : Real) (hR : 0 < R) (hτ : τ ∈ D.carrier)
    (s : Real) (x : M) :
    (paraSolution (I := I) S τ R hR hτ).base.rm04 s x =
      R • S.base.rm04 (paraTime τ R s) x := by
  simpa [paraSolution, paraFamily, SolutionFamily.rm04] using
    metricRm04_scaleMetric (I := I) R hR (S.base.metric (paraTime τ R s)) x



omit [SigmaCompactSpace M] in
theorem paraRmNormSq
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (τ R : Real) (hR : 0 < R) (hτ : τ ∈ D.carrier)
    (s : Real) (x : M) :
    Tensor0SBundle.normSq0S (I := I)
        ((paraSolution (I := I) S τ R hR hτ).base.metric s) x 4
        ((paraSolution (I := I) S τ R hR hτ).base.rm04 s x) =
      (R⁻¹) ^ 2 * Tensor0SBundle.normSq0S (I := I)
        (S.base.metric (paraTime τ R s)) x 4
        (S.base.rm04 (paraTime τ R s) x) := by
  rw [paraSolution_rm04, show
    (paraSolution (I := I) S τ R hR hτ).base.metric s =
      scaleMetric (I := I) R hR (S.base.metric (paraTime τ R s)) by rfl,
    Tensor0SBundle.normSq0S_scale, Tensor0SBundle.normSq0S_smul]
  field_simp [ne_of_gt hR]

omit [SigmaCompactSpace M] in
@[simp] private theorem paraNablaRic_eq
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (τ R : Real) (hR : 0 < R) (hτ : τ ∈ D.carrier)
    (s : Real) (x : M) :
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 ((paraSolution (I := I) S τ R hR hτ).family.connection s)
        ((paraSolution (I := I) S τ R hR hτ).ricci s) x =
      totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 (S.family.connection (paraTime τ R s))
        (S.ricci (paraTime τ R s)) x := by
  refine totalNabla0SFun_congr (𝕜 := Real) (E := E) (H := H)
    (I := I) (M := M) 2 ?_ ?_ x
  · have h := congrFun (paraSolution_connection (I := I) S τ R hR hτ) s
    simp [SolutionOn.family] at h ⊢
  · have h := congrFun (paraSolution_ricci (I := I) S τ R hR hτ) s
    simp [SolutionOn.ricci] at h ⊢

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem metricTensorField_scaleMetric
    (c : Real) (hc : 0 < c) (g : SmoothRiemannianMetric I M) (x : M) :
    metricTensorField (I := I) (scaleMetric (I := I) c hc g) x =
      c • metricTensorField (I := I) g x := by
  ext v
  simp [metricTensorField_apply, scaleMetric_inner, smul_eq_mul]

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem metricTracePair0SAt_scaleMetric
    (c : Real) (hc : 0 < c) (g : SmoothRiemannianMetric I M)
    {x : M} (B : Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2 x) :
    DifferentialGeometry.Integral.Connection.metricTracePair0SAt (I := I) (scaleMetric (I := I) c hc g) B =
      c⁻¹ * DifferentialGeometry.Integral.Connection.metricTracePair0SAt (I := I) g B := by
  classical
  let basis : Module.Basis (DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E) Real
      (TangentSpace I x) := DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := I) x
  let gInv : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E ->
      DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E -> Real :=
    fun k l =>
      DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_component (I := I) g x k l
        (extChartAt I x x)
  have hinv : MetricInverseInBasis_gen (I := I) g x basis gInv :=
    DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_metricInverseInBasis_center (I := I) g x
  have hinvScale :
      MetricInverseInBasis_gen (I := I) (scaleMetric (I := I) c hc g) x basis
        (fun i j => c⁻¹ * gInv i j) :=
    metricInvBasis_scale (I := I) c hc g basis gInv hinv
  rw [DifferentialGeometry.Integral.Connection.metricTracePair0SAt_eq_sum_basis (I := I)
      (scaleMetric (I := I) c hc g) basis (fun i j => c⁻¹ * gInv i j) hinvScale,
    DifferentialGeometry.Integral.Connection.metricTracePair0SAt_eq_sum_basis (I := I) g basis gInv hinv]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  ring

omit [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem paraSolution_scalar
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (τ R : Real) (hR : 0 < R) (hτ : τ ∈ D.carrier) :
    (paraSolution (I := I) S τ R hR hτ).scalar =
      fun s x => R⁻¹ * S.scalar (paraTime τ R s) x := by
  funext s x
  simp [SolutionOn.scalar, SolutionFamily.scalar_apply, paraSolution, paraFamily,
    SolutionFamily.ricciAt, metricRicciAt, DifferentialGeometry.Integral.Connection.metricRicciAt,
    DifferentialGeometry.Integral.Connection.metricCov, DifferentialGeometry.Integral.Connection.lcConn_scaleMetric,
    metricTracePair0SAt_scaleMetric]

omit [SigmaCompactSpace M] in
@[simp] theorem paraSolution_ricciNorm
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (τ R : Real) (hR : 0 < R) (hτ : τ ∈ D.carrier) :
    ricciNorm (I := I) (paraSolution (I := I) S τ R hR hτ) =
      fun s x => R⁻¹ * R⁻¹ * ricciNorm (I := I) S (paraTime τ R s) x := by
  funext s x
  have hRic :
      (paraSolution (I := I) S τ R hR hτ).ricci s x =
        S.ricci (paraTime τ R s) x := by
    have h := paraSolution_ricci (I := I) S τ R hR hτ
    change ((paraSolution (I := I) S τ R hR hτ).base.ricci s) x =
      (S.base.ricci (paraTime τ R s)) x
    exact congrArg (fun A => A x) (congrFun h s)
  rw [ricciNorm, hRic]
  simpa [SolutionOn.family, paraSolution, paraFamily, ricciNorm, mul_assoc] using
    (normSq0S_two_scale (I := I) R hR (S.family.metric (paraTime τ R s))
      (x := x) (A := S.ricci (paraTime τ R s) x))

omit [SigmaCompactSpace M] in
private theorem paraRicciNormGrad_eq
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (τ R : Real) (hR : 0 < R) (hτ : τ ∈ D.carrier)
    {s : Real} (hs : s ∈ (paraInterval D τ R hR hτ).carrier) (x : M) :
    DifferentialGeometry.Integral.Connection.gradientFun (I := I)
        ((paraSolution (I := I) S τ R hR hτ).family.metric s)
        (ricciNorm (I := I) (paraSolution (I := I) S τ R hR hτ) s) x =
      (R⁻¹ * R⁻¹ * R⁻¹) •
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (S.family.metric (paraTime τ R s))
          (ricciNorm (I := I) S (paraTime τ R s)) x := by
  have hdiff :
      MDifferentiableAt I 𝓘(Real, Real)
        (ricciNorm (I := I) S (paraTime τ R s)) x :=
    hS.ricciNormSpace (paraTime τ R s) hs x
  calc
    DifferentialGeometry.Integral.Connection.gradientFun (I := I)
        ((paraSolution (I := I) S τ R hR hτ).family.metric s)
        (ricciNorm (I := I) (paraSolution (I := I) S τ R hR hτ) s) x =
        DifferentialGeometry.Integral.Connection.gradientFun (I := I)
          (scaleMetric (I := I) R hR (S.family.metric (paraTime τ R s)))
          ((R⁻¹ * R⁻¹) • ricciNorm (I := I) S (paraTime τ R s)) x := by
          have hfun :
              ricciNorm (I := I) (paraSolution (I := I) S τ R hR hτ) s =
                (R⁻¹ * R⁻¹) • ricciNorm (I := I) S (paraTime τ R s) := by
            funext y
            have h := congrFun
              (congrFun (paraSolution_ricciNorm (I := I) S τ R hR hτ) s) y
            rw [h]
            simp [Pi.smul_apply, smul_eq_mul, mul_assoc]
          rw [hfun]
          simp [SolutionOn.family, paraSolution, paraFamily]
    _ =
        R⁻¹ • DifferentialGeometry.Integral.Connection.gradientFun (I := I) (S.family.metric (paraTime τ R s))
          ((R⁻¹ * R⁻¹) • ricciNorm (I := I) S (paraTime τ R s)) x := by
          rw [DifferentialGeometry.Integral.Connection.gradientFun_scale]
    _ =
        R⁻¹ • ((R⁻¹ * R⁻¹) •
          DifferentialGeometry.Integral.Connection.gradientFun (I := I) (S.family.metric (paraTime τ R s))
            (ricciNorm (I := I) S (paraTime τ R s)) x) := by
          rw [DifferentialGeometry.Integral.Connection.gradientFun_const_smul (I := I)
            (S.family.metric (paraTime τ R s)) (a := R⁻¹ * R⁻¹) hdiff]
    _ =
        (R⁻¹ * R⁻¹ * R⁻¹) •
          DifferentialGeometry.Integral.Connection.gradientFun (I := I) (S.family.metric (paraTime τ R s))
            (ricciNorm (I := I) S (paraTime τ R s)) x := by
          simp [smul_smul, mul_comm]

omit [SigmaCompactSpace M] [T2Space M] in
private theorem lcConnectionSmooth
    (g : SmoothRiemannianMetric I M) :
    CovariantDerivative.ContMDiffCovariantDerivative
      (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g) ∞ := by
  exact
    ⟨DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
      (I := I) g (u := Set.univ) isOpen_univ⟩




omit [SigmaCompactSpace M] in
theorem metricFamilySmooth_para
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (τ R : Real) (hR : 0 < R) (hτ : τ ∈ D.carrier) :
    DifferentialGeometry.Integral.Connection.MetricFamilySmoothOn (I := I) (M := M)
      (paraInterval D τ R hR hτ)
      (paraSolution (I := I) S τ R hR hτ).family := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x X Y
    have hOld := hS.smoothMetric.coeff x X Y
    have haff_global : ContDiff Real ∞ (fun s : Real => paraTime τ R s) := by
      unfold paraTime
      exact contDiff_const.add (contDiff_id.div_const R)
    have hmaps :
        Set.MapsTo (fun s : Real => paraTime τ R s)
          (paraInterval D τ R hR hτ).regular D.regular := by
      intro s hs
      exact hs
    have hcomp :
        ContDiffOn Real ∞
          (fun s : Real => (S.base.metric (paraTime τ R s)).inner x X Y)
          (paraInterval D τ R hR hτ).regular := by
      simpa [Function.comp_def] using
        hOld.comp haff_global.contDiffOn hmaps
    simpa [SolutionOn.family, paraSolution, paraFamily, scaleMetric_inner, smul_eq_mul]
      using ContDiffOn.const_smul R hcomp
  · intro x X Y
    have hOld := hS.smoothMetric.coeff_cont x X Y
    have htime : Continuous (fun s : Real => paraTime τ R s) := by
      unfold paraTime
      exact continuous_const.add (continuous_id.div_const R)
    have hmaps :
        Set.MapsTo (fun s : Real => paraTime τ R s)
          (paraInterval D τ R hR hτ).carrier D.carrier := by
      intro s hs
      exact hs
    have hcomp :
        ContinuousOn
          (fun s : Real => (S.base.metric (paraTime τ R s)).inner x X Y)
          (paraInterval D τ R hR hτ).carrier := by
      simpa [Function.comp_def] using
        hOld.comp htime.continuousOn hmaps
    simpa [SolutionOn.family, paraSolution, paraFamily, scaleMetric_inner, smul_eq_mul]
      using hcomp.const_smul R
  · have hmaps :
        Set.MapsTo (fun s : Real => paraTime τ R s)
          (paraInterval D τ R hR hτ).carrier D.carrier := by
      intro s hs
      exact hs
    have htime : Continuous (fun s : Real => paraTime τ R s) := by
      unfold paraTime
      exact continuous_const.add (continuous_id.div_const R)
    have hcomp :=
      DifferentialGeometry.Integral.Connection.Tensor0SFamilyContinuousOnSet.comp_time (I := I) (M := M)
        hS.smoothMetric.metricTensor_cont htime hmaps
    have hscale :=
      DifferentialGeometry.Integral.Connection.Tensor0SFamilyContinuousOnSet.const_smul (I := I) (M := M)
        R hcomp
    simpa [SolutionOn.family, paraSolution, paraFamily, metricTensorField_scaleMetric]
      using hscale
  · intro Idx _ frame u hframe i j
    have hOld :
        ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
          (fun p : Real × M =>
            (S.family.metric p.1).inner p.2 (frame i p.2) (frame j p.2))
          (D.regular ×ˢ u) :=
      hS.smoothMetric.frameCompSmooth frame hframe i j
    have htime :
        ContMDiff (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
          (fun p : Real × M => paraTime τ R p.1) := by
      unfold paraTime
      exact contMDiff_const.add (contMDiff_fst.div_const R)
    have hmapSmooth :
        ContMDiff (𝓘(Real, Real).prod I) (𝓘(Real, Real).prod I) ∞
          (fun p : Real × M => (paraTime τ R p.1, p.2)) :=
      htime.prodMk contMDiff_snd
    have hmaps :
        Set.MapsTo (fun p : Real × M => (paraTime τ R p.1, p.2))
          ((paraInterval D τ R hR hτ).regular ×ˢ u) (D.regular ×ˢ u) := by
      intro p hp
      exact ⟨hp.1, hp.2⟩
    have hcomp :
        ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
          (fun p : Real × M =>
            (S.base.metric (paraTime τ R p.1)).inner p.2
              (frame i p.2) (frame j p.2))
          ((paraInterval D τ R hR hτ).regular ×ˢ u) := by
      simpa [SolutionOn.family, Function.comp_def] using
        hOld.comp hmapSmooth.contMDiffOn hmaps
    have hscale :
        ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
          (fun p : Real × M =>
            R * (S.base.metric (paraTime τ R p.1)).inner p.2
              (frame i p.2) (frame j p.2))
          ((paraInterval D τ R hR hτ).regular ×ˢ u) :=
      (contMDiffOn_const (c := R)).mul hcomp
    simpa [SolutionOn.family, paraSolution, paraFamily, scaleMetric_inner,
      smul_eq_mul] using hscale


omit [SigmaCompactSpace M] in
theorem connectionFamilySmooth_para
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (_hS : IsSolutionOn (I := I) S)
    (τ R : Real) (hR : 0 < R) (hτ : τ ∈ D.carrier) :
    DifferentialGeometry.Integral.Connection.ConnectionFamilySmoothOn (I := I) (M := M)
      (paraSolution (I := I) S τ R hR hτ).family := by
  intro t
  simpa [SolutionOn.family, paraSolution, paraFamily, SolutionFamily.connection,
    DifferentialGeometry.Integral.Connection.RealizedMetricFamilyOn.connectionAt]
    using lcConnectionSmooth (I := I)
      ((paraSolution (I := I) S τ R hR hτ).base.metric (t : Real))


omit [SigmaCompactSpace M] in
theorem leviCivita_para
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (_hS : IsSolutionOn (I := I) S)
    (τ R : Real) (hR : 0 < R) (hτ : τ ∈ D.carrier) :
    DifferentialGeometry.Integral.Connection.IsLeviCivitaFamilyOn (I := I)
      (paraSolution (I := I) S τ R hR hτ).family := by
  constructor
  · intro t
    exact (paraSolution (I := I) S τ R hR hτ).metricCompatible t
  · intro t
    simpa [SolutionOn.family, paraSolution, paraFamily, SolutionFamily.connection,
      DifferentialGeometry.Integral.Connection.RealizedMetricFamilyOn.connectionAt]
      using DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric_isTorsionFree
        (I := I) ((paraSolution (I := I) S τ R hR hτ).base.metric (t : Real))


omit [SigmaCompactSpace M] in
theorem metricVariation_para
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (τ R : Real) (hR : 0 < R) (hτ : τ ∈ D.carrier) :
    MetricVariationEquationOn (I := I)
      (paraSolution (I := I) S τ R hR hτ) := by
  intro t x X Y
  let tOld : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D :=
    ⟨paraTime τ R (t : Real), t.2⟩
  have hOld := hS.equation tOld x X Y
  have htime :
      HasDerivWithinAt (fun s : Real => paraTime τ R s) R⁻¹
        (paraInterval D τ R hR hτ).carrier (t : Real) := by
    simpa [paraTime, one_div] using
      (((hasDerivWithinAt_id (t : Real)
        (paraInterval D τ R hR hτ).carrier).div_const R).const_add τ)
  have hmaps :
      Set.MapsTo (fun s : Real => paraTime τ R s)
        (paraInterval D τ R hR hτ).carrier D.carrier := by
    intro s hs
    exact hs
  have hcomp := hOld.comp (x := (t : Real)) htime hmaps
  have hscaled := hcomp.const_mul R
  simpa [MetricVariationEquationOn, DifferentialGeometry.Integral.Connection.MetricVariationEquationOn,
    SolutionOn.family, paraSolution, paraFamily, RicciAtFamily.toTensorField,
    SolutionFamily.ricciAt, metricRicciAt, DifferentialGeometry.Integral.Connection.metricRicciAt,
    DifferentialGeometry.Integral.Connection.metricCov, scaleMetric_inner, DifferentialGeometry.Integral.Connection.lcConn_scaleMetric,
    tOld]
    using
      (hscaled.congr_deriv (by
        simp [tOld, SolutionFamily.ricciAt, metricRicciAt, DifferentialGeometry.Integral.Connection.metricRicciAt,
          DifferentialGeometry.Integral.Connection.metricCov]
        field_simp [ne_of_gt hR]))


omit [SigmaCompactSpace M] in
theorem paraSol
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (τ R : Real) (hR : 0 < R) (hτ : τ ∈ D.carrier) :
    IsSolutionOn (I := I) (paraSolution (I := I) S τ R hR hτ) where
  smoothMetric := metricFamilySmooth_para (I := I) S hS τ R hR hτ
  smoothConnection := connectionFamilySmooth_para (I := I) S hS τ R hR hτ
  equation := metricVariation_para (I := I) S hS τ R hR hτ
  scalarCont := by
    have htime : Continuous (fun q : Real × M => paraTime τ R q.1) := by
      unfold paraTime
      exact continuous_const.add (continuous_fst.div_const R)
    have hmap : Continuous (fun q : Real × M => (paraTime τ R q.1, q.2)) :=
      htime.prodMk continuous_snd
    have hmapOn : ContinuousOn (fun q : Real × M => (paraTime τ R q.1, q.2))
        ((paraInterval D τ R hR hτ).carrier ×ˢ (Set.univ : Set M)) :=
      hmap.continuousOn
    have hmaps : Set.MapsTo (fun q : Real × M => (paraTime τ R q.1, q.2))
        ((paraInterval D τ R hR hτ).carrier ×ˢ (Set.univ : Set M))
        (D.carrier ×ˢ (Set.univ : Set M)) := by
      intro q hq
      exact ⟨hq.1, trivial⟩
    have hcomp :
        ContinuousOn
          (fun q : Real × M => S.scalar (paraTime τ R q.1) q.2)
          ((paraInterval D τ R hR hτ).carrier ×ˢ (Set.univ : Set M)) := by
      have h := hS.scalarCont.comp hmapOn hmaps
      simpa [Function.comp_def] using h
    have hscale :
        ContinuousOn
          (fun q : Real × M => R⁻¹ * S.scalar (paraTime τ R q.1) q.2)
          ((paraInterval D τ R hR hτ).carrier ×ˢ (Set.univ : Set M)) :=
      continuousOn_const.mul hcomp
    have hscalar_fun :
        (fun q : Real × M =>
          (paraSolution (I := I) S τ R hR hτ).scalar q.1 q.2) =
            fun q : Real × M => R⁻¹ * S.scalar (paraTime τ R q.1) q.2 := by
      funext q
      rw [paraSolution_scalar (I := I) S τ R hR hτ]
    rw [hscalar_fun]
    exact hscale
  scalarTime := by
    intro K t ht hK x
    let shift : Real -> Real := fun s => paraTime τ R s
    have ht' : shift t ∈ shift '' K := ⟨t, ht, rfl⟩
    have hK' : shift '' K ⊆ D.carrier := by
      intro r hr
      rcases hr with ⟨s, hs, rfl⟩
      exact hK hs
    have hOld := hS.scalarTime (K := shift '' K) (t := shift t) ht' hK' x
    have hshift : DifferentiableWithinAt Real shift K t := by
      simpa [shift, paraTime] using
        ((differentiableWithinAt_id' (𝕜 := Real) (s := K) (x := t)).div_const R).const_add τ
    have hmaps : Set.MapsTo shift K (shift '' K) := by
      intro s hs
      exact ⟨s, hs, rfl⟩
    have hcomp := hOld.comp t hshift hmaps
    have hscaled := hcomp.const_mul R⁻¹
    have hscalar :
        (fun s : Real => (paraSolution (I := I) S τ R hR hτ).scalar s x) =
          fun s : Real => R⁻¹ * S.scalar (paraTime τ R s) x := by
      funext s
      exact congrFun (congrFun (paraSolution_scalar (I := I) S τ R hR hτ) s) x
    rw [hscalar]
    simpa [shift, Function.comp_def] using hscaled
  ricciCont := by
    have hmaps :
        Set.MapsTo (fun s : Real => paraTime τ R s)
          (paraInterval D τ R hR hτ).carrier D.carrier := by
      intro s hs
      exact hs
    have htime : Continuous (fun s : Real => paraTime τ R s) := by
      unfold paraTime
      exact continuous_const.add (continuous_id.div_const R)
    have hcont :=
      DifferentialGeometry.Integral.Connection.Tensor0SFamilyContinuousOnSet.comp_time (I := I) (M := M)
        hS.ricciCont htime hmaps
    simpa [SolutionOn.ricci, paraSolution_ricci (I := I) S τ R hR hτ] using hcont
  rm04Cont := by
    have hmaps :
        Set.MapsTo (fun s : Real => paraTime τ R s)
          (paraInterval D τ R hR hτ).carrier D.carrier := by
      intro s hs
      exact hs
    have htime : Continuous (fun s : Real => paraTime τ R s) := by
      unfold paraTime
      exact continuous_const.add (continuous_id.div_const R)
    have hcomp :=
      DifferentialGeometry.Integral.Connection.Tensor0SFamilyContinuousOnSet.comp_time (I := I) (M := M)
        hS.rm04Cont htime hmaps
    have hscale :=
      DifferentialGeometry.Integral.Connection.Tensor0SFamilyContinuousOnSet.const_smul (I := I) (M := M)
        R hcomp
    simpa [paraSolution_rm04 (I := I) S τ R hR hτ] using hscale
  ricciNormSpace := by
    intro t ht x
    have hOld :
        MDifferentiableAt I 𝓘(Real, Real)
          (ricciNorm (I := I) S (paraTime τ R t)) x :=
      hS.ricciNormSpace (paraTime τ R t) ht x
    have hscaled := hOld.const_smul (R⁻¹ * R⁻¹)
    have hfun :
        ricciNorm (I := I) (paraSolution (I := I) S τ R hR hτ) t =
          (R⁻¹ * R⁻¹) • ricciNorm (I := I) S (paraTime τ R t) := by
      funext y
      have h := congrFun
        (congrFun (paraSolution_ricciNorm (I := I) S τ R hR hτ) t) y
      rw [h]
      simp [Pi.smul_apply, smul_eq_mul, mul_assoc]
    simpa [hfun] using hscaled
  ricciNormGrad := by
    intro t ht x
    have hOld :
        MDiffAt (T% fun y : M =>
          DifferentialGeometry.Integral.Connection.gradientFun (I := I) (S.family.metric (paraTime τ R t))
            (ricciNorm (I := I) S (paraTime τ R t)) y) x :=
      hS.ricciNormGrad (paraTime τ R t) ht x
    have hscaled :
        MDiffAt (T% fun y : M =>
          (R⁻¹ * R⁻¹ * R⁻¹) •
            DifferentialGeometry.Integral.Connection.gradientFun (I := I) (S.family.metric (paraTime τ R t))
              (ricciNorm (I := I) S (paraTime τ R t)) y) x := by
      simpa [Pi.smul_apply] using
        (mdifferentiableAt_const (I := I) (c := R⁻¹ * R⁻¹ * R⁻¹)).smul_section hOld
    have hpt : ∀ y : M,
        DifferentialGeometry.Integral.Connection.gradientFun (I := I)
          ((paraSolution (I := I) S τ R hR hτ).family.metric t)
          (ricciNorm (I := I) (paraSolution (I := I) S τ R hR hτ) t) y =
          (R⁻¹ * R⁻¹ * R⁻¹) •
            DifferentialGeometry.Integral.Connection.gradientFun (I := I) (S.family.metric (paraTime τ R t))
              (ricciNorm (I := I) S (paraTime τ R t)) y := by
      intro y
      exact paraRicciNormGrad_eq (I := I) S hS τ R hR hτ ht y
    have htotal :
        (T% fun y : M =>
          DifferentialGeometry.Integral.Connection.gradientFun (I := I)
            ((paraSolution (I := I) S τ R hR hτ).family.metric t)
            (ricciNorm (I := I) (paraSolution (I := I) S τ R hR hτ) t) y) =
          (T% fun y : M =>
            (R⁻¹ * R⁻¹ * R⁻¹) •
              DifferentialGeometry.Integral.Connection.gradientFun (I := I) (S.family.metric (paraTime τ R t))
                (ricciNorm (I := I) S (paraTime τ R t)) y) := by
      funext y
      change
          TotalSpace.mk' E y
            (DifferentialGeometry.Integral.Connection.gradientFun (I := I)
              ((paraSolution (I := I) S τ R hR hτ).family.metric t)
              (ricciNorm (I := I) (paraSolution (I := I) S τ R hR hτ) t) y) =
            TotalSpace.mk' E y
              ((R⁻¹ * R⁻¹ * R⁻¹) •
                DifferentialGeometry.Integral.Connection.gradientFun (I := I) (S.family.metric (paraTime τ R t))
                  (ricciNorm (I := I) S (paraTime τ R t)) y)
      rw [hpt y]
    rw [htotal]
    exact hscaled

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I 1 M] [SigmaCompactSpace M] [T2Space M] in
theorem paraBack_para_metric
    (G : SolutionFamily (I := I) (M := M))
    (τ R : Real) (hR : 0 < R) (t : Real) :
    ((paraBackFamily (I := I) (paraFamily (I := I) G τ R hR)
      τ R hR).metric t).inner = (G.metric t).inner := by
  funext x
  ext v w
  simp only [paraBackFamily, paraFamily, scaleMetric_inner]
  rw [paraTime_back (τ := τ) (R := R) (t := t) (ne_of_gt hR)]
  rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hR), one_mul]

omit [SigmaCompactSpace M] [T2Space M] in
theorem paraBack_para_connection
    (G : SolutionFamily (I := I) (M := M))
    (τ R : Real) (hR : 0 < R) (t : Real) :
    (paraBackFamily (I := I) (paraFamily (I := I) G τ R hR)
      τ R hR).connection t = G.connection t := by
  simp [paraBackFamily, paraFamily, SolutionFamily.connection,
    DifferentialGeometry.Integral.Connection.lcConn_scaleMetric, paraTime_back (τ := τ) (R := R) (t := t)
      (ne_of_gt hR)]

omit [SigmaCompactSpace M] in
theorem paraBack_para_ricci
    (G : SolutionFamily (I := I) (M := M))
    (τ R : Real) (hR : 0 < R) (t : Real) :
    (paraBackFamily (I := I) (paraFamily (I := I) G τ R hR)
      τ R hR).ricci t = G.ricci t := by
  simp [paraBackFamily, paraFamily, SolutionFamily.ricci, metricRicci,
    DifferentialGeometry.Integral.Connection.metricRicci, DifferentialGeometry.Integral.Connection.metricCov, DifferentialGeometry.Integral.Connection.lcConn_scaleMetric,
    paraTime_back (τ := τ) (R := R) (t := t) (ne_of_gt hR)]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I 1 M] [SigmaCompactSpace M] [T2Space M] in
theorem para_paraBack_metric
    (G : SolutionFamily (I := I) (M := M))
    (τ R : Real) (hR : 0 < R) (s : Real) :
    ((paraFamily (I := I) (paraBackFamily (I := I) G τ R hR)
      τ R hR).metric s).inner = (G.metric s).inner := by
  funext x
  ext v w
  simp only [paraFamily, paraBackFamily, scaleMetric_inner]
  rw [paraBack_time (τ := τ) (R := R) (s := s) (ne_of_gt hR)]
  rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hR), one_mul]

omit [SigmaCompactSpace M] [T2Space M] in
theorem para_paraBack_connection
    (G : SolutionFamily (I := I) (M := M))
    (τ R : Real) (hR : 0 < R) (s : Real) :
    (paraFamily (I := I) (paraBackFamily (I := I) G τ R hR)
      τ R hR).connection s = G.connection s := by
  simp [paraFamily, paraBackFamily, SolutionFamily.connection,
    DifferentialGeometry.Integral.Connection.lcConn_scaleMetric, paraBack_time (τ := τ) (R := R) (s := s)
      (ne_of_gt hR)]

omit [SigmaCompactSpace M] in
theorem para_paraBack_ricci
    (G : SolutionFamily (I := I) (M := M))
    (τ R : Real) (hR : 0 < R) (s : Real) :
    (paraFamily (I := I) (paraBackFamily (I := I) G τ R hR)
      τ R hR).ricci s = G.ricci s := by
  simp [paraFamily, paraBackFamily, SolutionFamily.ricci, metricRicci,
    DifferentialGeometry.Integral.Connection.metricRicci, DifferentialGeometry.Integral.Connection.metricCov, DifferentialGeometry.Integral.Connection.lcConn_scaleMetric,
    paraBack_time (τ := τ) (R := R) (s := s) (ne_of_gt hR)]


def ParaScalarDisplay
    (scalar scalarR : Real -> M -> Real) (τ R : Real) : Prop :=
  forall s x, scalarR s x = R⁻¹ * scalar (paraTime τ R s) x


def ParaTracefreeNormSqDisplay
    (q qR : Real -> M -> Real) (τ R : Real) : Prop :=
  forall s x, qR s x = (R⁻¹) ^ 2 * q (paraTime τ R s) x



omit [TopologicalSpace M] [SigmaCompactSpace M] [T2Space M] in
theorem para_tracefree_ratio_invariant
    {scalar scalarR q qR : Real -> M -> Real}
    {τ R : Real} (hR : 0 < R)
    (hscalar : ParaScalarDisplay (M := M) scalar scalarR τ R)
    (hq : ParaTracefreeNormSqDisplay (M := M) q qR τ R)
    (s : Real) (x : M) :
    qR s x / (scalarR s x) ^ 2 =
      q (paraTime τ R s) x / (scalar (paraTime τ R s) x) ^ 2 := by
  rw [hq s x, hscalar s x]
  field_simp [ne_of_gt hR]

end DifferentialGeometry.PDE.RicciFlow
