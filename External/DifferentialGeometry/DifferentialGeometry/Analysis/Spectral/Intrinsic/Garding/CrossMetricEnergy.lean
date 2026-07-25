import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.ScalarHessBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricLapDiff
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.WindowPreconv
import DifferentialGeometry.Geometry.Operator.HessianTraceRealization










noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Laplacian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete Real E
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [NeZero (Module.finrank Real E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem normSq0S_nonneg
    (g : SmoothRiemannianMetric I M) (x : M) (s : Nat)
    (A : Tensor0SSpace s I x) :
    0 <= normSq0S (I := I) g x s A := by
  classical
  obtain ⟨basis, hON⟩ := exists_gOrthonormalBasis (I := I) g x
  have hinv : MetricInverseInBasis_gen (I := I) g x basis
      (identityInvMetric
        (Idx := Fin (Module.finrank Real (TangentSpace I x)))) := by
    intro i j
    constructor <;> simp [identityInvMetric, diagonalInvMetric, hON]
  rw [normSq0S_identity_eq_sum_sq (I := I) g x s basis hinv A]
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

omit [NeZero (Module.finrank Real E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem normSqRS_nonneg
    (g : SmoothRiemannianMetric I M) (x : M) (r s : Nat)
    (A : TensorRSSpace r s I x) :
    0 <= normSqRS (I := I) (g := g) (x := x) r s A := by
  classical
  obtain ⟨basis, hON⟩ := exists_gOrthonormalBasis (I := I) g x
  have hinv : MetricInverseInBasis_gen (I := I) g x basis
      (identityInvMetric
        (Idx := Fin (Module.finrank Real (TangentSpace I x)))) := by
    intro i j
    constructor <;> simp [identityInvMetric, diagonalInvMetric, hON]
  rw [normSqRS_identity_eq_componentL2SqRS
    (I := I) g x r s basis hinv A]
  unfold componentL2SqRS
  exact Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => sq_nonneg _

private theorem add_sq_le (a b : Real) :
    (a + b) ^ 2 <= 2 * a ^ 2 + 2 * b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
private theorem cross_point_le
    (q k : SmoothRiemannianMetric I M) (Ce R : Real)
    (hEq : DifferentialGeometry.HCGCompactness.MetricUniformEquivalentOn
      (I := I) Set.univ q k Ce)
    (hR0 : 0 <= R) {f : M -> Real}
    (hf : ContMDiff I 𝓘(Real, Real) ∞ f) (x : M)
    (hderiv : DifferentialGeometry.HCGCompactness.metricDerivNorm
      (I := I) 1 q k k x <= R) :
    normSq0S (I := I) k x 2 (leviHessSec (I := I) k f hf x) +
        normSq0S (I := I) k x 1 (duSec (I := I) f hf x) <=
      (2 * Ce ^ 2) *
          normSq0S (I := I) q x 2 (leviHessSec (I := I) q f hf x) +
        (2 * Ce ^ 2 *
            (((3 / 2 : Real) * (Real.sqrt (Ce ^ 3) * R)) ^ 2) + Ce) *
          normSq0S (I := I) q x 1 (duSec (I := I) f hf x) := by
  classical
  let A : Real := (3 / 2 : Real) * (Real.sqrt (Ce ^ 3) * R)
  let Kc : Real := A ^ 2
  let covQ := leviCivitaConnectionOfMetric (I := I) q
  let covK := leviCivitaConnectionOfMetric (I := I) k
  let HessQ := leviHessSec (I := I) q f hf x
  let HessK := leviHessSec (I := I) k f hf x
  let du := duSec (I := I) f hf x
  let Dt := connectionDifferenceTensorAt (I := I) covQ covK x
  let B := connectionDifferenceOutput (I := I)
    (CovariantDerivative.difference covQ covK x) du
  have hEq' :=
    DifferentialGeometry.HCGCompactness.metricUniformEquivalentOn_symm
      (I := I) hEq
  have hCe0 : 0 <= Ce := le_trans zero_le_one hEq.1
  have hA0 : 0 <= A := by
    dsimp only [A]
    exact mul_nonneg (by norm_num)
      (mul_nonneg (Real.sqrt_nonneg _) hR0)
  have hDx :
      Real.sqrt (normSqRS (I := I) (g := q) (x := x) 1 2 Dt) <= A := by
    have hbase :=
      DifferentialGeometry.HCGCompactness.lcDiff_norm_le
        (I := I) (K := Set.univ) k q hEq'
        (x := x) (Set.mem_univ x)
    have hinner :
        Real.sqrt (Ce ^ 3) *
            DifferentialGeometry.HCGCompactness.metricDerivNorm
              (I := I) 1 q k k x <=
          Real.sqrt (Ce ^ 3) * R :=
      mul_le_mul_of_nonneg_left hderiv (Real.sqrt_nonneg _)
    have hmul :=
      mul_le_mul_of_nonneg_left hinner (by norm_num : (0 : Real) <= 3 / 2)
    simpa only [Dt, covQ, covK, A] using hbase.trans hmul
  have hD0 : 0 <= normSqRS (I := I) (g := q) (x := x) 1 2 Dt :=
    normSqRS_nonneg (I := I) q x 1 2 Dt
  have hDsq : normSqRS (I := I) (g := q) (x := x) 1 2 Dt <= Kc := by
    have hsquare := (sq_le_sq₀ (Real.sqrt_nonneg _) hA0).2 hDx
    calc
      normSqRS (I := I) (g := q) (x := x) 1 2 Dt =
          (Real.sqrt (normSqRS (I := I) (g := q) (x := x) 1 2 Dt)) ^ 2 := by
        rw [Real.sq_sqrt hD0]
      _ <= A ^ 2 := hsquare
      _ = Kc := rfl
  have hdu0 : 0 <= normSq0S (I := I) q x 1 du :=
    normSq0S_nonneg (I := I) q x 1 du
  have hB0 : 0 <= normSq0S (I := I) q x 2 B :=
    normSq0S_nonneg (I := I) q x 2 B
  have hout0 :
      Real.sqrt (normSq0S (I := I) q x 2 B) <=
        Real.sqrt (normSqRS (I := I) (g := q) (x := x) 1 2 Dt) *
          Real.sqrt (normSq0S (I := I) q x 1 du) := by
    simpa only [B, Dt, covQ, covK] using
      connOut_norm_le (I := I) q covQ covK du
  have hout :
      normSq0S (I := I) q x 2 B <=
        normSqRS (I := I) (g := q) (x := x) 1 2 Dt *
          normSq0S (I := I) q x 1 du := by
    have hright : 0 <=
        Real.sqrt (normSqRS (I := I) (g := q) (x := x) 1 2 Dt) *
          Real.sqrt (normSq0S (I := I) q x 1 du) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hsquare := (sq_le_sq₀ (Real.sqrt_nonneg _) hright).2 hout0
    calc
      normSq0S (I := I) q x 2 B =
          (Real.sqrt (normSq0S (I := I) q x 2 B)) ^ 2 := by
        rw [Real.sq_sqrt hB0]
      _ <= (Real.sqrt (normSqRS (I := I) (g := q) (x := x) 1 2 Dt) *
          Real.sqrt (normSq0S (I := I) q x 1 du)) ^ 2 := hsquare
      _ = normSqRS (I := I) (g := q) (x := x) 1 2 Dt *
          normSq0S (I := I) q x 1 du := by
        rw [mul_pow, Real.sq_sqrt hD0, Real.sq_sqrt hdu0]
  have hBout : normSq0S (I := I) q x 2 B <=
      Kc * normSq0S (I := I) q x 1 du :=
    hout.trans (mul_le_mul_of_nonneg_right hDsq hdu0)
  have hsub : HessQ - HessK = -B := by
    simpa only [HessQ, HessK, B, covQ, covK, leviHessSec] using
      hess_sub_conn (I := I) covQ covK
        (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
          (I := I) (M := M) q)
        (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
          (I := I) (M := M) k)
        f hf x
  have hHess : HessK = HessQ + B := by
    have hEqAdd := eq_add_of_sub_eq hsub
    rw [hEqAdd]
    abel
  have hHq0 : 0 <= normSq0S (I := I) q x 2 HessQ :=
    normSq0S_nonneg (I := I) q x 2 HessQ
  have hHkq0 : 0 <= normSq0S (I := I) q x 2 HessK :=
    normSq0S_nonneg (I := I) q x 2 HessK
  have htri :
      Real.sqrt (normSq0S (I := I) q x 2 HessK) <=
        Real.sqrt (normSq0S (I := I) q x 2 HessQ) +
          Real.sqrt (normSq0S (I := I) q x 2 B) := by
    rw [hHess]
    exact DifferentialGeometry.HCGCompactness.sqrtNormSq0S_add_le
      (I := I) q x 2 HessQ B
  have htriSq : normSq0S (I := I) q x 2 HessK <=
      2 * normSq0S (I := I) q x 2 HessQ +
        2 * normSq0S (I := I) q x 2 B := by
    have hright : 0 <=
        Real.sqrt (normSq0S (I := I) q x 2 HessQ) +
          Real.sqrt (normSq0S (I := I) q x 2 B) :=
      add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hsquare := (sq_le_sq₀ (Real.sqrt_nonneg _) hright).2 htri
    calc
      normSq0S (I := I) q x 2 HessK =
          (Real.sqrt (normSq0S (I := I) q x 2 HessK)) ^ 2 := by
        rw [Real.sq_sqrt hHkq0]
      _ <= (Real.sqrt (normSq0S (I := I) q x 2 HessQ) +
          Real.sqrt (normSq0S (I := I) q x 2 B)) ^ 2 := hsquare
      _ <= 2 * normSq0S (I := I) q x 2 HessQ +
          2 * normSq0S (I := I) q x 2 B := by
        calc
          _ <= 2 * (Real.sqrt (normSq0S (I := I) q x 2 HessQ)) ^ 2 +
              2 * (Real.sqrt (normSq0S (I := I) q x 2 B)) ^ 2 :=
            add_sq_le _ _
          _ = _ := by rw [Real.sq_sqrt hHq0, Real.sq_sqrt hB0]
  have hcompH := normSq0S_upper_le_of_equiv
    (I := I) q k x 2 hEq.1 (hEq.2 x (Set.mem_univ x)) HessK
  have hHbound : normSq0S (I := I) k x 2 HessK <=
      (2 * Ce ^ 2) * normSq0S (I := I) q x 2 HessQ +
        (2 * Ce ^ 2 * Kc) * normSq0S (I := I) q x 1 du := by
    calc
      normSq0S (I := I) k x 2 HessK <=
          Ce ^ 2 * normSq0S (I := I) q x 2 HessK := hcompH
      _ <= Ce ^ 2 * (2 * normSq0S (I := I) q x 2 HessQ +
          2 * normSq0S (I := I) q x 2 B) :=
        mul_le_mul_of_nonneg_left htriSq (pow_nonneg hCe0 2)
      _ <= Ce ^ 2 * (2 * normSq0S (I := I) q x 2 HessQ +
          2 * (Kc * normSq0S (I := I) q x 1 du)) := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg hCe0 2)
        exact add_le_add le_rfl
          (mul_le_mul_of_nonneg_left hBout (by norm_num))
      _ = (2 * Ce ^ 2) * normSq0S (I := I) q x 2 HessQ +
          (2 * Ce ^ 2 * Kc) * normSq0S (I := I) q x 1 du := by ring
  have hDbound : normSq0S (I := I) k x 1 du <=
      Ce * normSq0S (I := I) q x 1 du := by
    simpa using normSq0S_upper_le_of_equiv
      (I := I) q k x 1 hEq.1 (hEq.2 x (Set.mem_univ x)) du
  have hsum := add_le_add hHbound hDbound
  calc
    normSq0S (I := I) k x 2 (leviHessSec (I := I) k f hf x) +
        normSq0S (I := I) k x 1 (duSec (I := I) f hf x) <=
      ((2 * Ce ^ 2) *
          normSq0S (I := I) q x 2 (leviHessSec (I := I) q f hf x) +
        (2 * Ce ^ 2 * (((3 / 2 : Real) *
          (Real.sqrt (Ce ^ 3) * R)) ^ 2)) *
          normSq0S (I := I) q x 1 (duSec (I := I) f hf x)) +
        Ce * normSq0S (I := I) q x 1 (duSec (I := I) f hf x) := by
      simpa only [HessK, HessQ, du, Kc, A] using hsum
    _ = (2 * Ce ^ 2) *
          normSq0S (I := I) q x 2 (leviHessSec (I := I) q f hf x) +
        (2 * Ce ^ 2 * (((3 / 2 : Real) *
            (Real.sqrt (Ce ^ 3) * R)) ^ 2) + Ce) *
          normSq0S (I := I) q x 1 (duSec (I := I) f hf x) := by ring





theorem cross_energy_le
    (q k : SmoothRiemannianMetric I M) :
    ∃ C : Real, 0 <= C ∧
      ∀ (v : tensorHs (I := I) (M := M) q 0 0 2)
        (hv : (Function.support v.coeff).Finite),
        ∫ x, (normSq0S (I := I) k x 2
              (leviHessSec (I := I) k
                (reprScalar0 (I := I) (M := M) v hv)
                (reprScalar0_smooth (I := I) (M := M) v hv) x) +
            normSq0S (I := I) k x 1
              (duSec (I := I)
                (reprScalar0 (I := I) (M := M) v hv)
                (reprScalar0_smooth (I := I) (M := M) v hv) x))
            ∂(riemannianVolumeMeasure (I := I) (M := M) q) <=
          C * ‖v‖ ^ 2 := by
  classical
  obtain ⟨Ce, hEq⟩ :=
    DifferentialGeometry.HCGCompactness.metricUniformEquivalentOn_of_compact
      (I := I) q k
  have hEq' :=
    DifferentialGeometry.HCGCompactness.metricUniformEquivalentOn_symm
      (I := I) hEq
  obtain ⟨R, hR0, hR⟩ :=
    DifferentialGeometry.HCGCompactness.metricDerivNorm_bddOn
      (I := I) isCompact_univ 1 q k k
  obtain ⟨CH, hCH, hHess⟩ := hessSec_energy_le (I := I) (M := M) q
  let A : Real := (3 / 2 : Real) * (Real.sqrt (Ce ^ 3) * R)
  let Kc : Real := A ^ 2
  let AH : Real := 2 * Ce ^ 2
  let AD : Real := 2 * Ce ^ 2 * Kc + Ce
  let C : Real := AH * CH + AD
  have hCe0 : 0 <= Ce := le_trans zero_le_one hEq.1
  have hKc0 : 0 <= Kc := by
    dsimp only [Kc]
    exact sq_nonneg A
  have hAH0 : 0 <= AH := by
    dsimp only [AH]
    exact mul_nonneg (by norm_num) (sq_nonneg Ce)
  have hAD0 : 0 <= AD := by
    dsimp only [AD]
    exact add_nonneg
      (mul_nonneg (mul_nonneg (by positivity) (sq_nonneg Ce)) hKc0) hCe0
  have hC0 : 0 <= C := by
    dsimp only [C]
    exact add_nonneg (mul_nonneg hAH0 hCH) hAD0
  refine ⟨C, hC0, ?_⟩
  intro v hv
  let f : M -> Real := reprScalar0 (I := I) (M := M) v hv
  let hf : ContMDiff I 𝓘(Real, Real) ∞ f :=
    reprScalar0_smooth (I := I) (M := M) v hv
  let Hk : M -> Real := fun x =>
    normSq0S (I := I) k x 2 (leviHessSec (I := I) k f hf x)
  let Hq : M -> Real := fun x =>
    normSq0S (I := I) q x 2 (leviHessSec (I := I) q f hf x)
  let Dk : M -> Real := fun x =>
    normSq0S (I := I) k x 1 (duSec (I := I) f hf x)
  let Dq : M -> Real := fun x =>
    normSq0S (I := I) q x 1 (duSec (I := I) f hf x)
  let lhs : M -> Real := fun x => Hk x + Dk x
  let rhs : M -> Real := fun x => AH * Hq x + AD * Dq x
  have hpoint : ∀ x : M, lhs x <= rhs x := by
    intro x
    simpa only [lhs, rhs, Hk, Hq, Dk, Dq, AH, AD, Kc, A] using
      cross_point_le (I := I) (M := M) q k Ce R hEq hR0 hf x
        (hR 1 le_rfl x (Set.mem_univ x))
  have hHkEq : Hk = fun x => chartHessFrobeniusSq (I := I) k f x := by
    funext x
    exact hessSec_normSq (I := I) k hf x
  have hHqEq : Hq = fun x => chartHessFrobeniusSq (I := I) q f x := by
    funext x
    exact hessSec_normSq (I := I) q hf x
  have hDkEq : Dk = fun x => normGradSqFun (I := I) k f x := by
    funext x
    simp only [Dk, duSec_apply, normSq0S_eq_inner,
      inner0S_differential1FormFun_pair_eq_grad_inner, normGradSqFun_def]
    rfl
  have hDqEq : Dq = fun x => normGradSqFun (I := I) q f x := by
    funext x
    simp only [Dq, duSec_apply, normSq0S_eq_inner,
      inner0S_differential1FormFun_pair_eq_grad_inner, normGradSqFun_def]
    rfl
  have hHkCont : Continuous Hk := by
    rw [hHkEq]
    exact chartHessFrobeniusSq_continuous (I := I) k hf
  have hHqCont : Continuous Hq := by
    rw [hHqEq]
    exact chartHessFrobeniusSq_continuous (I := I) q hf
  have hDkCont : Continuous Dk := by
    rw [hDkEq]
    exact normGradSqFun_continuous (I := I) k hf
  have hDqCont : Continuous Dq := by
    rw [hDqEq]
    exact normGradSqFun_continuous (I := I) q hf
  have hlhsCont : Continuous lhs := hHkCont.add hDkCont
  have hrhsCont : Continuous rhs :=
    (continuous_const.mul hHqCont).add (continuous_const.mul hDqCont)
  have hlhsInt : Integrable lhs
      (riemannianVolumeMeasure (I := I) (M := M) q) :=
    integrable_of_continuous_compactSpace (I := I) (M := M) q hlhsCont
  have hHqInt : Integrable Hq
      (riemannianVolumeMeasure (I := I) (M := M) q) :=
    integrable_of_continuous_compactSpace (I := I) (M := M) q hHqCont
  have hDqInt : Integrable Dq
      (riemannianVolumeMeasure (I := I) (M := M) q) :=
    integrable_of_continuous_compactSpace (I := I) (M := M) q hDqCont
  have hrhsInt : Integrable rhs
      (riemannianVolumeMeasure (I := I) (M := M) q) :=
    integrable_of_continuous_compactSpace (I := I) (M := M) q hrhsCont
  have hint :
      (∫ x, lhs x ∂(riemannianVolumeMeasure (I := I) (M := M) q)) <=
        ∫ x, rhs x ∂(riemannianVolumeMeasure (I := I) (M := M) q) :=
    integral_mono_ae hlhsInt hrhsInt (Filter.Eventually.of_forall hpoint)
  have hrhsEq :
      (∫ x, rhs x ∂(riemannianVolumeMeasure (I := I) (M := M) q)) =
        AH * (∫ x, Hq x ∂(riemannianVolumeMeasure (I := I) (M := M) q)) +
          AD * (∫ x, Dq x ∂(riemannianVolumeMeasure (I := I) (M := M) q)) := by
    rw [show rhs = fun x => AH * Hq x + AD * Dq x from rfl]
    rw [integral_add (hHqInt.const_mul AH) (hDqInt.const_mul AD),
      integral_const_mul, integral_const_mul]
  have hH :
      (∫ x, Hq x ∂(riemannianVolumeMeasure (I := I) (M := M) q)) <=
        CH * ‖v‖ ^ 2 := by
    simpa only [Hq, f, hf] using hHess v hv
  have hD :
      (∫ x, Dq x ∂(riemannianVolumeMeasure (I := I) (M := M) q)) <=
        ‖v‖ ^ 2 := by
    simpa only [Dq, f, hf] using du_energy_le (I := I) (M := M) q v hv
  calc
    (∫ x, (normSq0S (I := I) k x 2
            (leviHessSec (I := I) k
              (reprScalar0 (I := I) (M := M) v hv)
              (reprScalar0_smooth (I := I) (M := M) v hv) x) +
          normSq0S (I := I) k x 1
            (duSec (I := I)
              (reprScalar0 (I := I) (M := M) v hv)
              (reprScalar0_smooth (I := I) (M := M) v hv) x))
          ∂(riemannianVolumeMeasure (I := I) (M := M) q)) =
        ∫ x, lhs x ∂(riemannianVolumeMeasure (I := I) (M := M) q) := by
      rfl
    _ <= ∫ x, rhs x ∂(riemannianVolumeMeasure (I := I) (M := M) q) := hint
    _ = AH * (∫ x, Hq x ∂(riemannianVolumeMeasure (I := I) (M := M) q)) +
        AD * (∫ x, Dq x ∂(riemannianVolumeMeasure (I := I) (M := M) q)) := hrhsEq
    _ <= AH * (CH * ‖v‖ ^ 2) + AD * ‖v‖ ^ 2 :=
      add_le_add
        (mul_le_mul_of_nonneg_left hH hAH0)
        (mul_le_mul_of_nonneg_left hD hAD0)
    _ = C * ‖v‖ ^ 2 := by
      simp only [C]
      ring

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
