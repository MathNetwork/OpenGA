import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.IntegratedOrder2WeitzenbockCurvature
import DifferentialGeometry.Geometry.Curvature.Order2Defect.GradientSlotLeibniz
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.FiberNormSubadditivity
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.TensorThirdOrderWeitzenbock


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

noncomputable def pointwiseTensorCurv
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    SmoothCcTensor g 0 (s + 1) :=
  rawTensorConnLapSmooth (I := I) g 0 (s + 1) (covGrad (I := I) (M := M) g 0 s S) -
    covGrad (I := I) (M := M) g 0 s (rawTensorConnLapSmooth (I := I) g 0 s S)

theorem pointwiseTensorCurv_commutator_eq
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    rawTensorConnLapSmooth (I := I) g 0 (s + 1) (covGrad (I := I) (M := M) g 0 s S) =
      covGrad (I := I) (M := M) g 0 s (rawTensorConnLapSmooth (I := I) g 0 s S)
        + pointwiseTensorCurv (I := I) (M := M) g s S := by
  set A : SmoothCcTensor g 0 (s + 1) :=
    rawTensorConnLapSmooth (I := I) g 0 (s + 1) (covGrad (I := I) (M := M) g 0 s S) with hA
  set B : SmoothCcTensor g 0 (s + 1) :=
    covGrad (I := I) (M := M) g 0 s (rawTensorConnLapSmooth (I := I) g 0 s S) with hB
  change A = B + (A - B)
  abel

theorem pointwiseTensorCurv_toSection_eq_sub
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) :
    (pointwiseTensorCurv (I := I) (M := M) g s S).toSection x =
      (rawTensorConnLapSmooth (I := I) g 0 (s + 1)
          (covGrad (I := I) (M := M) g 0 s S)).toSection x -
        (covGrad (I := I) (M := M) g 0 s
          (rawTensorConnLapSmooth (I := I) g 0 s S)).toSection x := by
  have hdef : (pointwiseTensorCurv (I := I) (M := M) g s S) =
      rawTensorConnLapSmooth (I := I) g 0 (s + 1) (covGrad (I := I) (M := M) g 0 s S) -
        covGrad (I := I) (M := M) g 0 s (rawTensorConnLapSmooth (I := I) g 0 s S) := rfl
  rw [hdef, SmoothCcTensor.toSection_sub]
  rfl

theorem rawTensorConnLap_gradTensor_toSection_eq_frame_trace_gen
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) :
    (rawTensorConnLapSmooth (I := I) g 0 (s + 1)
        (covGrad (I := I) (M := M) g 0 s S)).toSection x =
      ∑ i : Fin (Module.finrank ℝ E),
        tensorSecondCovDeriv (I := I) g 0 (s + 1)
          (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
          (fun y : M => (covGrad (I := I) (M := M) g 0 s S).toSection y) x := by
  rw [rawTensorConnLapSmooth_toSection_apply]
  exact rawTensorConnLap_eq_frame_trace_secondCovDeriv (I := I) g 0 (s + 1)
    (fun y : M => (covGrad (I := I) (M := M) g 0 s S).toSection y) x

theorem covGrad_rawConnLap_toSection_eq_frame_sum_gen
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) :
    (covGrad (I := I) (M := M) g 0 s
        (rawTensorConnLapSmooth (I := I) g 0 s S)).toSection x =
      ∑ i : Fin (Module.finrank ℝ E),
        covGradBundleEquiv (I := I) (M := M) 0 s x
          ((tensorCov (I := I) g 0 s).toFun
            (fun y : M => tensorSecondCovDeriv (I := I) g 0 s
              (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
              (fun z : M => S.toSection z) y) x) := by
  have hS : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) y (S.toSection y)) :=
    S.toSection.contMDiff
  rw [covGrad_toSection_apply (I := I) (M := M) g 0 s
    (rawTensorConnLapSmooth (I := I) g 0 s S) x]
  rw [show (fun y : M => (rawTensorConnLapSmooth (I := I) g 0 s S).toSection y) =
      (fun y : M => rawTensorConnLap (I := I) g 0 s (fun z : M => S.toSection z) y) from by
    funext y; rw [rawTensorConnLapSmooth_toSection_apply]]
  exact covGradBundleEquiv_covDeriv_rawConnLap_eq_sum (I := I) g 0 s hS x

theorem pointwiseTensorCurv_toSection_eq_frame_sum
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) :
    (pointwiseTensorCurv (I := I) (M := M) g s S).toSection x =
      ∑ i : Fin (Module.finrank ℝ E),
        (tensorSecondCovDeriv (I := I) g 0 (s + 1)
            (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
            (fun y : M => (covGrad (I := I) (M := M) g 0 s S).toSection y) x -
          covGradBundleEquiv (I := I) (M := M) 0 s x
            ((tensorCov (I := I) g 0 s).toFun
              (fun y : M => tensorSecondCovDeriv (I := I) g 0 s
                (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
                (fun z : M => S.toSection z) y) x)) := by
  classical
  rw [pointwiseTensorCurv_toSection_eq_sub (I := I) (M := M) g s S x]
  rw [rawTensorConnLap_gradTensor_toSection_eq_frame_trace_gen (I := I) (M := M) g s S x]
  rw [covGrad_rawConnLap_toSection_eq_frame_sum_gen (I := I) (M := M) g s S x]
  rw [← Finset.sum_sub_distrib]

noncomputable def pointwiseTensorCurvPairing
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) : ℝ :=
  tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) x
    (TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := 0) (s := s + 1) (x := x)
      ((pointwiseTensorCurv (I := I) (M := M) g s S).toSection x))
    (TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := 0) (s := s + 1) (x := x)
      ((covGrad (I := I) (M := M) g 0 s S).toSection x))

lemma pointwiseTensorCurvPairing_eq_toFun
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) :
    pointwiseTensorCurvPairing (I := I) (M := M) g s S x =
      tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) x
        ((pointwiseTensorCurv (I := I) (M := M) g s S).toFun x)
        ((covGrad (I := I) (M := M) g 0 s S).toFun x) := by
  rfl

theorem abs_pointwiseTensorCurvPairing_le
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) :
    |pointwiseTensorCurvPairing (I := I) (M := M) g s S x| ≤
      Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
          ((pointwiseTensorCurv (I := I) (M := M) g s S).toSection x)) *
        Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
          ((covGrad (I := I) (M := M) g 0 s S).toSection x)) := by
  classical
  rw [pointwiseTensorCurvPairing]
  have hcs := abs_tensorInnerPointwise_le_mul (I := I) (M := M) g 0 (s + 1) x
    (TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := 0) (s := s + 1) (x := x)
      ((pointwiseTensorCurv (I := I) (M := M) g s S).toSection x))
    (TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := 0) (s := s + 1) (x := x)
      ((covGrad (I := I) (M := M) g 0 s S).toSection x))
  rw [tensorPointwiseNorm, tensorPointwiseNorm,
    ← riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) x
      ((pointwiseTensorCurv (I := I) (M := M) g s S).toSection x),
    ← riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) x
      ((covGrad (I := I) (M := M) g 0 s S).toSection x)] at hcs
  exact hcs

theorem pointwiseTensorCurv_pairing_bound
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    (K_R K_dR : ℝ)
    (hfibre :
      Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
          ((pointwiseTensorCurv (I := I) (M := M) g s S).toSection x)) ≤
        K_R * Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
            ((covGrad (I := I) (M := M) g 0 s S).toSection x)) +
          K_dR * Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 s x
            (S.toSection x))) :
    |pointwiseTensorCurvPairing (I := I) (M := M) g s S x| ≤
      K_R * riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
          ((covGrad (I := I) (M := M) g 0 s S).toSection x) +
        K_dR * Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x)) *
          Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
            ((covGrad (I := I) (M := M) g 0 s S).toSection x)) := by
  classical
  set sqCurv : ℝ := Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
    ((pointwiseTensorCurv (I := I) (M := M) g s S).toSection x)) with hsqCurv
  set sqGrad : ℝ := Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
    ((covGrad (I := I) (M := M) g 0 s S).toSection x)) with hsqGrad
  set sqS : ℝ := Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x))
    with hsqS
  have hsqGrad_nn : 0 ≤ sqGrad := Real.sqrt_nonneg _
  have hgrad_sq : sqGrad * sqGrad =
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
        ((covGrad (I := I) (M := M) g 0 s S).toSection x) := by
    rw [hsqGrad]
    exact Real.mul_self_sqrt
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + 1) x _)
  have hcs := abs_pointwiseTensorCurvPairing_le (I := I) (M := M) g s S x
  rw [← hsqCurv, ← hsqGrad] at hcs
  calc |pointwiseTensorCurvPairing (I := I) (M := M) g s S x|
      ≤ sqCurv * sqGrad := hcs
    _ ≤ (K_R * sqGrad + K_dR * sqS) * sqGrad :=
        mul_le_mul_of_nonneg_right hfibre hsqGrad_nn
    _ = K_R * (sqGrad * sqGrad) + K_dR * sqS * sqGrad := by ring
    _ = K_R * riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
            ((covGrad (I := I) (M := M) g 0 s S).toSection x) +
          K_dR * sqS * sqGrad := by rw [hgrad_sq]

noncomputable def tensor3rdCurvGenuine
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (W : Π b : M, TangentSpace I b) (T : Π b : M, TensorRSSpace r s I b) (x : M) :
    TensorRSSpace r s I x :=
  ∑ i : Fin (Module.finrank ℝ E),
    (riemannSec (tensorCov (I := I) g r s) (smoothOrthoFrame (I := I) g x i) W
        (covApply (tensorCov (I := I) g r s) (smoothOrthoFrame (I := I) g x i) T) x
      + (tensorCov (I := I) g r s).toFun
          (fun b : M => riemannSec (tensorCov (I := I) g r s)
            (smoothOrthoFrame (I := I) g x i) W T b) x
          (smoothOrthoFrame (I := I) g x i x))

noncomputable def tensor3rdCurvBracket
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (W : Π b : M, TangentSpace I b) (T : Π b : M, TensorRSSpace r s I b) (x : M) :
    TensorRSSpace r s I x :=
  ∑ i : Fin (Module.finrank ℝ E),
    ((tensorCov (I := I) g r s).toFun
        (covApply (tensorCov (I := I) g r s) (smoothOrthoFrame (I := I) g x i) T) x
        (VectorField.mlieBracket I (smoothOrthoFrame (I := I) g x i) W x)
      + (tensorCov (I := I) g r s).toFun
          (covApply (tensorCov (I := I) g r s)
            (VectorField.mlieBracket I (smoothOrthoFrame (I := I) g x i) W) T) x
          (smoothOrthoFrame (I := I) g x i x))

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem Tensor3rdCurv_eq_genuine_add_bracket
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (W : Π b : M, TangentSpace I b) (T : Π b : M, TensorRSSpace r s I b) (x : M) :
    tensorThirdOrderCurvatureDefect (I := I) g r s W T x =
      tensor3rdCurvGenuine (I := I) g r s W T x +
        tensor3rdCurvBracket (I := I) g r s W T x := by
  classical
  rw [Tensor3rdCurv_def, tensor3rdCurvGenuine, tensor3rdCurvBracket,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  abel

omit [CompactSpace M] [I.Boundaryless] in
theorem frame_trace_thirdCovDeriv_defect_eq_genuine_add_bracket
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {W : Π b : M, TangentSpace I b} {T : Π b : M, TensorRSSpace r s I b} {x : M}
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W))
    (hT : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) b (T b))) :
    (∑ i : Fin (Module.finrank ℝ E),
          (tensorCov (I := I) g r s).toFun
            (covApply (tensorCov (I := I) g r s) (smoothOrthoFrame (I := I) g x i)
              (covApply (tensorCov (I := I) g r s) W T)) x
            (smoothOrthoFrame (I := I) g x i x)) -
        (∑ i : Fin (Module.finrank ℝ E),
            (tensorCov (I := I) g r s).toFun
              (covApply (tensorCov (I := I) g r s) (smoothOrthoFrame (I := I) g x i)
                (covApply (tensorCov (I := I) g r s) (smoothOrthoFrame (I := I) g x i) T)) x
              (W x)) =
      tensor3rdCurvGenuine (I := I) g r s W T x +
        tensor3rdCurvBracket (I := I) g r s W T x := by
  rw [frame_trace_thirdCovDeriv_swap (I := I) g r s hW hT,
    Tensor3rdCurv_eq_genuine_add_bracket (I := I) g r s W T x]
  abel

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem riemannianFiberNormSq_tensor3rdCurvGenuine_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (W : Π b : M, TangentSpace I b) (T : Π b : M, TensorRSSpace r s I b) (x : M)
    (cR cdR : ℝ)
    (hR : ∀ i : Fin (Module.finrank ℝ E),
      riemannianFiberNormSq (I := I) (M := M) g r s x
          (riemannSec (tensorCov (I := I) g r s) (smoothOrthoFrame (I := I) g x i) W
            (covApply (tensorCov (I := I) g r s) (smoothOrthoFrame (I := I) g x i) T) x) ≤ cR)
    (hdR : ∀ i : Fin (Module.finrank ℝ E),
      riemannianFiberNormSq (I := I) (M := M) g r s x
          ((tensorCov (I := I) g r s).toFun
            (fun b : M => riemannSec (tensorCov (I := I) g r s)
              (smoothOrthoFrame (I := I) g x i) W T b) x
            (smoothOrthoFrame (I := I) g x i x)) ≤ cdR) :
    riemannianFiberNormSq (I := I) (M := M) g r s x
        (tensor3rdCurvGenuine (I := I) g r s W T x) ≤
      (2 * (Module.finrank ℝ E : ℝ)) * (Module.finrank ℝ E : ℝ) * (cR + cdR) := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn
  set F : Fin n → TensorRSSpace r s I x := fun i =>
    riemannSec (tensorCov (I := I) g r s) (smoothOrthoFrame (I := I) g x i) W
        (covApply (tensorCov (I := I) g r s) (smoothOrthoFrame (I := I) g x i) T) x
      + (tensorCov (I := I) g r s).toFun
          (fun b : M => riemannSec (tensorCov (I := I) g r s)
            (smoothOrthoFrame (I := I) g x i) W T b) x
          (smoothOrthoFrame (I := I) g x i x) with hF
  have hsum : tensor3rdCurvGenuine (I := I) g r s W T x = ∑ i : Fin n, F i := rfl
  rw [hsum]
  have hcard := riemannianFiberNormSq_sum_le_card_mul (I := I) (M := M) g r s x
    (Finset.univ : Finset (Fin n)) F
  rw [Finset.card_univ, Fintype.card_fin] at hcard
  have hper : ∀ i : Fin n,
      riemannianFiberNormSq (I := I) (M := M) g r s x (F i) ≤ 2 * (cR + cdR) := by
    intro i
    have hadd := riemannianFiberNormSq_add_le (I := I) (M := M) g r s x
      (riemannSec (tensorCov (I := I) g r s) (smoothOrthoFrame (I := I) g x i) W
        (covApply (tensorCov (I := I) g r s) (smoothOrthoFrame (I := I) g x i) T) x)
      ((tensorCov (I := I) g r s).toFun
        (fun b : M => riemannSec (tensorCov (I := I) g r s)
          (smoothOrthoFrame (I := I) g x i) W T b) x
        (smoothOrthoFrame (I := I) g x i x))
    have h1 := hR i
    have h2 := hdR i
    calc riemannianFiberNormSq (I := I) (M := M) g r s x (F i)
        ≤ 2 * riemannianFiberNormSq (I := I) (M := M) g r s x
              (riemannSec (tensorCov (I := I) g r s) (smoothOrthoFrame (I := I) g x i) W
                (covApply (tensorCov (I := I) g r s) (smoothOrthoFrame (I := I) g x i) T) x) +
            2 * riemannianFiberNormSq (I := I) (M := M) g r s x
              ((tensorCov (I := I) g r s).toFun
                (fun b : M => riemannSec (tensorCov (I := I) g r s)
                  (smoothOrthoFrame (I := I) g x i) W T b) x
                (smoothOrthoFrame (I := I) g x i x)) := hadd
      _ ≤ 2 * cR + 2 * cdR := by
            have := mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 2)
            have := mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ) ≤ 2)
            linarith
      _ = 2 * (cR + cdR) := by ring
  have hsum_le : ∑ i : Fin n, riemannianFiberNormSq (I := I) (M := M) g r s x (F i) ≤
      (n : ℝ) * (2 * (cR + cdR)) := by
    calc ∑ i : Fin n, riemannianFiberNormSq (I := I) (M := M) g r s x (F i)
        ≤ ∑ _i : Fin n, (2 * (cR + cdR)) := Finset.sum_le_sum (fun i _ => hper i)
      _ = (n : ℝ) * (2 * (cR + cdR)) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  calc riemannianFiberNormSq (I := I) (M := M) g r s x (∑ i : Fin n, F i)
      ≤ (n : ℝ) * ∑ i : Fin n, riemannianFiberNormSq (I := I) (M := M) g r s x (F i) := hcard
    _ ≤ (n : ℝ) * ((n : ℝ) * (2 * (cR + cdR))) :=
        mul_le_mul_of_nonneg_left hsum_le hn_nn
    _ = (2 * (n : ℝ)) * (n : ℝ) * (cR + cdR) := by ring

omit [CompactSpace M] [I.Boundaryless] in
theorem tensor3rdCurv_pure_R_eq_riemannOp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {W : Π b : M, TangentSpace I b} {T : Π b : M, TensorRSSpace r s I b} {x : M}
    (i : Fin (Module.finrank ℝ E))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W))
    (hT : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) b (T b))) :
    riemannSec (tensorCov (I := I) g r s) (smoothOrthoFrame (I := I) g x i) W
        (covApply (tensorCov (I := I) g r s) (smoothOrthoFrame (I := I) g x i) T) x =
      riemannOp (tensorCov (I := I) g r s) x
        (smoothOrthoFrame (I := I) g x i x) (W x)
        (covApply (tensorCov (I := I) g r s) (smoothOrthoFrame (I := I) g x i) T x) := by
  have hB : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (smoothOrthoFrame (I := I) g x i)) :=
    smoothOrthoFrame_smooth (I := I) g x i
  have hZ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) b
        (covApply (tensorCov (I := I) g r s) (smoothOrthoFrame (I := I) g x i) T b)) :=
    covApplyRS_contMDiff (I := I) g r s hT hB
  exact riemannSec_eq_riemannOp_tensorCov (I := I) g r s hB hW hZ

end Connection
end Integral
end DifferentialGeometry

end
