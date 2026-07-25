import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.CrossMetricEnergy
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.MetricLapDiffCore








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
private theorem toRS0_sub {x : M} (A B : Tensor0SSpace 0 I x) :
    Tensor0SSpace.toRS0 (A - B) =
      Tensor0SSpace.toRS0 A - Tensor0SSpace.toRS0 B := by
  apply ContinuousLinearMap.ext
  intro c
  change tensor0SSpace_evalScalar x c • (A - B) =
    tensor0SSpace_evalScalar x c • A - tensor0SSpace_evalScalar x c • B
  exact smul_sub _ _ _

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



theorem lapDiffCore_pair_sq
    (q h k : SmoothRiemannianMetric I M)
    (v : ScalarH2Core (I := I) (M := M) q) :
    ‖lapDiffCore (I := I) (M := M) q h v -
        lapDiffCore (I := I) (M := M) q k v‖ ^ 2 =
      ∫ x, (Δ_g (I := I) h
              (reprScalar0_smooth (I := I) (M := M) v.1 v.2) x -
            Δ_g (I := I) k
              (reprScalar0_smooth (I := I) (M := M) v.1 v.2) x) ^ 2
        ∂(riemannianVolumeMeasure (I := I) (M := M) q) := by
  change ‖SmoothCcTensor.toL2
      (lapDiffSec (I := I) (M := M) q h v) -
        SmoothCcTensor.toL2
          (lapDiffSec (I := I) (M := M) q k v)‖ ^ 2 = _
  rw [← map_sub]
  rw [SmoothCcTensor.norm_toL2, SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun (I := I) (M := M) q 0 0
      (lapDiffSec (I := I) (M := M) q h v -
        lapDiffSec (I := I) (M := M) q k v)]
  unfold tensorL2Inner
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [SmoothCcTensor.toFun_apply, SmoothCcTensor.toSection_sub,
    ContMDiffSection.coe_sub, Pi.sub_apply]
  rw [lapDiffSec_apply (I := I) (M := M) q h v x,
    lapDiffSec_apply (I := I) (M := M) q k v x]
  rw [← toRS0_sub]
  rw [← map_sub]
  rw [inner_toRS0_scalar (I := I) (M := M) q x]
  ring




theorem lapDiff_pair_energy
    (q k : SmoothRiemannianMetric I M) :
    ∃ C : Real, 0 <= C ∧
      ∀ (h : SmoothRiemannianMetric I M)
        (v : tensorHs (I := I) (M := M) q 0 0 2)
        (hv : (Function.support v.coeff).Finite),
        (Module.finrank Real E : Real) *
            HCGCompactness.metricDerivNormSupOn
              (I := I) Set.univ 1 h k k <= (1 / 2 : Real) →
          ∫ x, (Δ_g (I := I) h
                  (reprScalar0_smooth (I := I) (M := M) v hv) x -
                Δ_g (I := I) k
                  (reprScalar0_smooth (I := I) (M := M) v hv) x) ^ 2
              ∂(riemannianVolumeMeasure (I := I) (M := M) q) <=
            C *
              (HCGCompactness.metricDerivNormSupOn
                (I := I) Set.univ 1 h k k) ^ 2 * ‖v‖ ^ 2 := by
  obtain ⟨CX, hCX, hcross⟩ := cross_energy_le (I := I) (M := M) q k
  let n : Real := Module.finrank Real E
  let Kc : Real := 8 * n ^ 2 + 72 * n
  let C : Real := Kc * CX
  have hKc : 0 <= Kc := by
    dsimp only [Kc, n]
    positivity
  refine ⟨C, mul_nonneg hKc hCX, ?_⟩
  intro h v hv hsmall
  let f : M → Real := reprScalar0 (I := I) (M := M) v hv
  let hf : ContMDiff I 𝓘(Real, Real) ∞ f :=
    reprScalar0_smooth (I := I) (M := M) v hv
  let rho : Real :=
    HCGCompactness.metricDerivNormSupOn (I := I) Set.univ 1 h k k
  let A : Real := 8 * n ^ 2 * rho ^ 2
  let B : Real := 72 * n * rho ^ 2
  let P : Real := A + B
  let HessNorm : M → Real := fun x =>
    normSq0S (I := I) k x 2 (leviHessSec (I := I) k f hf x)
  let duNorm : M → Real := fun x =>
    normSq0S (I := I) k x 1 (duSec (I := I) f hf x)
  let lhs : M → Real := fun x =>
    (Δ_g (I := I) h hf x - Δ_g (I := I) k hf x) ^ 2
  let energy : M → Real := fun x => HessNorm x + duNorm x
  have hHessEq : HessNorm = fun x =>
      chartHessFrobeniusSq (I := I) k f x := by
    funext x
    exact hessSec_normSq (I := I) k hf x
  have hduEq : duNorm = fun x => normGradSqFun (I := I) k f x := by
    funext x
    simp only [duNorm, duSec_apply, normSq0S_eq_inner,
      inner0S_differential1FormFun_pair_eq_grad_inner, normGradSqFun_def]
    rfl
  have hHessCont : Continuous HessNorm := by
    rw [hHessEq]
    exact chartHessFrobeniusSq_continuous (I := I) k hf
  have hduCont : Continuous duNorm := by
    rw [hduEq]
    exact normGradSqFun_continuous (I := I) k hf
  have hlhsCont : Continuous lhs := by
    exact (((Δ_g_contMDiff (I := I) h hf).continuous.sub
      (Δ_g_contMDiff (I := I) k hf).continuous).pow 2)
  have henergyCont : Continuous energy := hHessCont.add hduCont
  have hlhsInt : Integrable lhs
      (riemannianVolumeMeasure (I := I) (M := M) q) :=
    integrable_of_continuous_compactSpace (I := I) (M := M) q hlhsCont
  have henergyInt : Integrable energy
      (riemannianVolumeMeasure (I := I) (M := M) q) :=
    integrable_of_continuous_compactSpace (I := I) (M := M) q henergyCont
  have hA0 : 0 <= A := by
    dsimp only [A, n, rho]
    positivity
  have hB0 : 0 <= B := by
    dsimp only [B, n, rho]
    positivity
  have hP0 : 0 <= P := add_nonneg hA0 hB0
  have hpoint : ∀ x : M, lhs x <= P * energy x := by
    intro x
    have hbase := HCGCompactness.lapDiff_sq_le
      (I := I) k h hf x hsmall
    have hH0 : 0 <= HessNorm x := by
      exact normSq0S_nonneg (I := I) k x 2 _
    have hD0 : 0 <= duNorm x := by
      exact normSq0S_nonneg (I := I) k x 1 _
    have hAP : A <= P := by
      dsimp only [P]
      exact le_add_of_nonneg_right hB0
    have hBP : B <= P := by
      dsimp only [P]
      exact le_add_of_nonneg_left hA0
    calc
      lhs x <= A * HessNorm x + B * duNorm x := by
        simpa only [lhs, A, B, n, rho, HessNorm, duNorm, f, hf] using hbase
      _ <= P * HessNorm x + P * duNorm x :=
        add_le_add
          (mul_le_mul_of_nonneg_right hAP hH0)
          (mul_le_mul_of_nonneg_right hBP hD0)
      _ = P * energy x := by
        simp only [energy]
        ring
  have hint :
      (∫ x, lhs x ∂(riemannianVolumeMeasure (I := I) (M := M) q)) <=
        ∫ x, P * energy x
          ∂(riemannianVolumeMeasure (I := I) (M := M) q) :=
    integral_mono_ae hlhsInt (henergyInt.const_mul P)
      (Filter.Eventually.of_forall hpoint)
  have henergy :
      (∫ x, energy x ∂(riemannianVolumeMeasure (I := I) (M := M) q)) <=
        CX * ‖v‖ ^ 2 := by
    simpa only [energy, HessNorm, duNorm, f, hf] using hcross v hv
  calc
    (∫ x, (Δ_g (I := I) h
            (reprScalar0_smooth (I := I) (M := M) v hv) x -
          Δ_g (I := I) k
            (reprScalar0_smooth (I := I) (M := M) v hv) x) ^ 2
        ∂(riemannianVolumeMeasure (I := I) (M := M) q)) =
        ∫ x, lhs x ∂(riemannianVolumeMeasure (I := I) (M := M) q) := by
      rfl
    _ <= ∫ x, P * energy x
        ∂(riemannianVolumeMeasure (I := I) (M := M) q) := hint
    _ = P * (∫ x, energy x
        ∂(riemannianVolumeMeasure (I := I) (M := M) q)) := by
      rw [integral_const_mul]
    _ <= P * (CX * ‖v‖ ^ 2) :=
      mul_le_mul_of_nonneg_left henergy hP0
    _ = C * rho ^ 2 * ‖v‖ ^ 2 := by
      simp only [P, A, B, C, Kc]
      ring
    _ = C *
        (HCGCompactness.metricDerivNormSupOn
          (I := I) Set.univ 1 h k k) ^ 2 * ‖v‖ ^ 2 := by
      rfl



theorem lapDiff_pair_core
    (q k : SmoothRiemannianMetric I M) :
    ∃ C : Real, 0 <= C ∧
      ∀ (h : SmoothRiemannianMetric I M)
        (v : ScalarH2Core (I := I) (M := M) q),
        (Module.finrank Real E : Real) *
            HCGCompactness.metricDerivNormSupOn
              (I := I) Set.univ 1 h k k <= (1 / 2 : Real) →
          ‖lapDiffCore (I := I) (M := M) q h v -
              lapDiffCore (I := I) (M := M) q k v‖ <=
            Real.sqrt C *
              |HCGCompactness.metricDerivNormSupOn
                (I := I) Set.univ 1 h k k| * ‖v‖ := by
  obtain ⟨C, hC, henergy⟩ := lapDiff_pair_energy (I := I) (M := M) q k
  refine ⟨C, hC, ?_⟩
  intro h v hsmall
  let rho : Real :=
    HCGCompactness.metricDerivNormSupOn (I := I) Set.univ 1 h k k
  have hsq :
      ‖lapDiffCore (I := I) (M := M) q h v -
          lapDiffCore (I := I) (M := M) q k v‖ ^ 2 <=
        C * rho ^ 2 * ‖v‖ ^ 2 := by
    rw [lapDiffCore_pair_sq (I := I) (M := M) q h k v]
    simpa only [rho] using henergy h v.1 v.2 hsmall
  have hrhs :
      (Real.sqrt C * |rho| * ‖v‖) ^ 2 =
        C * rho ^ 2 * ‖v‖ ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hC, sq_abs]
  have hrhs0 : 0 <= Real.sqrt C * |rho| * ‖v‖ := by positivity
  rw [← hrhs] at hsq
  nlinarith [norm_nonneg
    (lapDiffCore (I := I) (M := M) q h v -
      lapDiffCore (I := I) (M := M) q k v)]




theorem lapDiff_pair_norm
    (q k : SmoothRiemannianMetric I M) :
    ∃ C : Real, 0 <= C ∧
      ∀ (h : SmoothRiemannianMetric I M),
        (Module.finrank Real E : Real) *
            HCGCompactness.metricDerivNormSupOn
              (I := I) Set.univ 1 h q q <= (1 / 2 : Real) →
        (Module.finrank Real E : Real) *
            HCGCompactness.metricDerivNormSupOn
              (I := I) Set.univ 1 k q q <= (1 / 2 : Real) →
        (Module.finrank Real E : Real) *
            HCGCompactness.metricDerivNormSupOn
              (I := I) Set.univ 1 h k k <= (1 / 2 : Real) →
          ‖lapDiffOp (I := I) (M := M) q h -
              lapDiffOp (I := I) (M := M) q k‖ <=
            Real.sqrt C *
              |HCGCompactness.metricDerivNormSupOn
                (I := I) Set.univ 1 h k k| := by
  obtain ⟨C, hC, hcore⟩ := lapDiff_pair_core (I := I) (M := M) q k
  refine ⟨C, hC, ?_⟩
  intro h hqh hqk hkh
  let rho : Real :=
    HCGCompactness.metricDerivNormSupOn (I := I) Set.univ 1 h k k
  let B : Real := Real.sqrt C * |rho|
  have hB : 0 <= B := by positivity
  have hdense :
      DenseRange (ScalarH2Core (I := I) (M := M) q).subtype :=
    (tensorHsFiniteSupportSubmodule_dense
      (I := I) (M := M) (g := q) (r := 0) (s := 0) (σ := 2)).denseRange_val
  apply (lapDiffOp (I := I) (M := M) q h -
    lapDiffOp (I := I) (M := M) q k).opNorm_le_bound hB
  intro u
  refine hdense.induction_on u ?_ ?_
  · exact isClosed_le
      (lapDiffOp (I := I) (M := M) q h -
        lapDiffOp (I := I) (M := M) q k).continuous.norm
      (continuous_const.mul continuous_norm)
  · intro v
    rw [ContinuousLinearMap.sub_apply]
    simp only [Submodule.coe_subtype]
    rw [lapDiffOp_core (I := I) (M := M) q h v hqh,
      lapDiffOp_core (I := I) (M := M) q k v hqk]
    simpa only [B, rho] using hcore h v hkh

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
