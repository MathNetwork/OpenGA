import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricArmCoeffJetTower
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RecoveryEndomorphismJetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedAppCcLeibniz
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CometricRaiseSlot0CovariantParallelism
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RaisedKoszulParallelRaiseJetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceArmRfnsBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RaisedKoszulCometricRaise
import DifferentialGeometry.Analysis.Sobolev.AntidiagonalTupleProductGrid


noncomputable section

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open TensorRSNabla
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization (metricCauchySchwarzBound ccTensorBilinSymm ccTensorBilinSymm_symm)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

set_option backward.isDefEq.respectTransparency false in
def fullRaisedEndoField (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x) where
  toFun := fun x : M => metricComparisonEndo (I := I) g₀ g₁ x
  contMDiff_toFun := by
    apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
      (F₁ := E) (V₁ := fun z : M => TangentSpace I z)
      (F₂ := E) (V₂ := fun z : M => TangentSpace I z)
      (φ := fun x => metricComparisonEndo (I := I) g₀ g₁ x)
    intro Y
    have hsharpY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b
          (DifferentialGeometry.Integral.DivergenceTheorem.metricSharp
            (I := I) g₁ b (g₀.inner b (Y b)).toLinearMap)) := by
      apply metricSharp_contMDiff_total (I := I) g₁
      intro γ j
      exact metricFlat_chartComponent_contMDiffOn (I := I) g₀ Y γ j
    refine hsharpY.congr (fun x => ?_)
    rw [gInvRaisedEndo_apply, inverseMetricSharpFib_g0FlatCLM_eq_metricSharp]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [SigmaCompactSpace M] in
@[simp] lemma fullRaisedEndoField_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (fullRaisedEndoField (I := I) (M := M) g₀ g₁ x) =
      metricComparisonEndo (I := I) g₀ g₁ x := rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma rfns_neg_fib (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (v : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (-v) =
      riemannianFiberNormSq (I := I) (M := M) g r s x v := by
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (-v),
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x v]
  rw [TensorRSSpace.toModel_neg]
  rw [show (-(TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s)
        (x := x) v)) = ((-1 : ℝ) • TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
        (r := r) (s := s) (x := x) v) from by rw [neg_one_smul]]
  rw [tensorInnerPointwise_smul_left, tensorInnerPointwise_smul_right]
  ring

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma rfns_smul_fib (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) (c : ℝ)
    (v : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (c • v) =
      c ^ 2 * riemannianFiberNormSq (I := I) (M := M) g r s x v := by
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (c • v),
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x v]
  rw [TensorRSSpace.toModel_smul]
  rw [tensorInnerPointwise_smul_left, tensorInnerPointwise_smul_right]
  ring

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma slotExtendFib_comp (g : SmoothRiemannianMetric I M) (p q r : ℕ) (x : M)
    (A : Tensor0SSpace p I x →L[ℝ] Tensor0SSpace q I x)
    (B : Tensor0SSpace r I x →L[ℝ] Tensor0SSpace p I x) :
    (slotExtendPointwise (I := I) (M := M) g p q x A).comp
        (slotExtendPointwise (I := I) (M := M) g r p x B) =
      slotExtendPointwise (I := I) (M := M) g r q x (A.comp B) := by
  apply ContinuousLinearMap.ext
  intro D
  rw [ContinuousLinearMap.comp_apply]
  rw [slotExtendFib_apply, slotExtendFib_apply, slotExtendFib_apply]
  rw [ContinuousLinearEquiv.apply_symm_apply]
  rw [ContinuousLinearMap.comp_assoc]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma slotExtendFib_id_eq (g : SmoothRiemannianMetric I M) (r : ℕ) (x : M) :
    slotExtendPointwise (I := I) (M := M) g r r x (ContinuousLinearMap.id ℝ (Tensor0SSpace r I x)) =
      ContinuousLinearMap.id ℝ (Tensor0SSpace (r + 1) I x) := by
  apply ContinuousLinearMap.ext
  intro D
  rw [slotExtendFib_apply, ContinuousLinearMap.id_comp,
    ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearMap.id_apply]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma appCcLeibnizPsi_diag_eq (g : SmoothRiemannianMetric I M) (b c : ℕ)
    (Φ : SmoothCcTensor g b c) (i : ℕ) :
    appCcLeibnizPsi (I := I) (M := M) g b c Φ i i =
      slotExtendIter (I := I) (M := M) g b c i Φ := by
  induction i with
  | zero => rfl
  | succ i ih =>
      have hss : appCcLeibnizPsi (I := I) (M := M) g b c Φ (i + 1) (i + 1) =
          (if i + 1 < i + 1 then
              covGrad (I := I) (M := M) g (b + (i + 1)) (c + i)
                (appCcLeibnizPsi (I := I) (M := M) g b c Φ i (i + 1))
            else 0) +
            castCcTensorSourceRank g (c + (i + 1)) (by omega : (b + i) + 1 = b + (i + 1))
              (castCcTensorRank g ((b + i) + 1) (by omega : (c + i) + 1 = c + (i + 1))
                (slotExtend (I := I) (M := M) g (b + i) (c + i)
                  (appCcLeibnizPsi (I := I) (M := M) g b c Φ i i))) := rfl
      rw [hss, if_neg (by omega : ¬ i + 1 < i + 1), zero_add]
      rw [show castCcTensorSourceRank g (c + (i + 1)) (by omega : (b + i) + 1 = b + (i + 1))
            (castCcTensorRank g ((b + i) + 1) (by omega : (c + i) + 1 = c + (i + 1))
              (slotExtend (I := I) (M := M) g (b + i) (c + i)
                (appCcLeibnizPsi (I := I) (M := M) g b c Φ i i))) =
          slotExtend (I := I) (M := M) g (b + i) (c + i)
            (appCcLeibnizPsi (I := I) (M := M) g b c Φ i i) from by
        rw [castCcTensorRank, castCcTensorSourceRank]]
      rw [show slotExtendIter (I := I) (M := M) g b c (i + 1) Φ =
            slotExtend (I := I) (M := M) g (b + i) (c + i)
              (slotExtendIter (I := I) (M := M) g b c i Φ) from rfl, ih]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma rfns_iteratedCovGrad_exp_congr (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) (x : M) {e₁ e₂ : ℕ} (h : e₁ = e₂) :
    riemannianFiberNormSq (I := I) (M := M) g r (s + e₁) x
        ((iteratedCovGrad (I := I) g r s e₁ Φ).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g r (s + e₂) x
        ((iteratedCovGrad (I := I) g r s e₂ Φ).toSection x) := by
  subst h; rfl

private lemma rfns_iteratedCovGrad_appCcLeibnizPsi_le
    (g : SmoothRiemannianMetric I M) (b c : ℕ) (Φ : SmoothCcTensor g b c) (x : M) :
    ∀ i k p d : ℕ, k + d = i →
      riemannianFiberNormSq (I := I) (M := M) g (b + k) ((c + i) + p) x
          ((iteratedCovGrad (I := I) g (b + k) (c + i) p
            (appCcLeibnizPsi (I := I) (M := M) g b c Φ i k)).toSection x) ≤
        (4 : ℝ) ^ i * (Module.finrank ℝ E : ℝ) ^ k *
          riemannianFiberNormSq (I := I) (M := M) g b (c + (p + d)) x
            ((iteratedCovGrad (I := I) g b c (p + d) Φ).toSection x) := by
  intro i
  induction i with
  | zero =>
    intro k p d hkd
    obtain rfl : k = 0 := by omega
    obtain rfl : d = 0 := by omega
    have happ : appCcLeibnizPsi (I := I) (M := M) g b c Φ 0 0 = Φ := rfl
    rw [happ]
    simp only [pow_zero, one_mul]
    exact le_of_eq rfl
  | succ i ih =>
    intro k p d hkd
    match k, hkd with
    | 0, hkd =>
      obtain rfl : d = i + 1 := by omega
      have h0 : appCcLeibnizPsi (I := I) (M := M) g b c Φ (i + 1) 0 =
          covGrad (I := I) (M := M) g (b + 0) (c + i)
            (appCcLeibnizPsi (I := I) (M := M) g b c Φ i 0) := rfl
      rw [h0]
      have hcomm : riemannianFiberNormSq (I := I) (M := M) g (b + 0) ((c + (i + 1)) + p) x
            ((iteratedCovGrad (I := I) g (b + 0) (c + (i + 1)) p
              (covGrad (I := I) (M := M) g (b + 0) (c + i)
                (appCcLeibnizPsi (I := I) (M := M) g b c Φ i 0))).toSection x) =
          riemannianFiberNormSq (I := I) (M := M) g (b + 0) ((c + i) + (p + 1)) x
            ((iteratedCovGrad (I := I) g (b + 0) (c + i) (p + 1)
              (appCcLeibnizPsi (I := I) (M := M) g b c Φ i 0)).toSection x) :=
        rfns_iteratedCovGrad_covGrad_comm_rs (I := I) (M := M) g (b + 0) (c + i) p
          (appCcLeibnizPsi (I := I) (M := M) g b c Φ i 0) x
      rw [hcomm]
      have hih := ih 0 (p + 1) i (by omega)
      rw [rfns_iteratedCovGrad_exp_congr (I := I) (M := M) g b c Φ x
        (show (p + 1) + i = p + (i + 1) by omega)] at hih
      refine le_trans hih ?_
      refine mul_le_mul_of_nonneg_right ?_
        (riemannianFiberNormSq_nonneg (I := I) (M := M) g b (c + (p + (i + 1))) x _)
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num) (by omega)) (by positivity)
    | (j + 1), hkd =>
      have hjd : j + d = i := by omega
      have hrec : appCcLeibnizPsi (I := I) (M := M) g b c Φ (i + 1) (j + 1) =
          (if j + 1 < i + 1 then
              covGrad (I := I) (M := M) g (b + (j + 1)) (c + i)
                (appCcLeibnizPsi (I := I) (M := M) g b c Φ i (j + 1))
            else 0) +
            slotExtend (I := I) (M := M) g (b + j) (c + i)
              (appCcLeibnizPsi (I := I) (M := M) g b c Φ i j) := by
        rw [show appCcLeibnizPsi (I := I) (M := M) g b c Φ (i + 1) (j + 1) =
            (if j + 1 < i + 1 then
                covGrad (I := I) (M := M) g (b + (j + 1)) (c + i)
                  (appCcLeibnizPsi (I := I) (M := M) g b c Φ i (j + 1))
              else 0) +
              castCcTensorSourceRank g (c + (i + 1)) (by omega : (b + j) + 1 = b + (j + 1))
                (castCcTensorRank g ((b + j) + 1) (by omega : (c + i) + 1 = c + (i + 1))
                  (slotExtend (I := I) (M := M) g (b + j) (c + i)
                    (appCcLeibnizPsi (I := I) (M := M) g b c Φ i j))) from rfl]
        rw [show castCcTensorSourceRank g (c + (i + 1)) (by omega : (b + j) + 1 = b + (j + 1))
              (castCcTensorRank g ((b + j) + 1) (by omega : (c + i) + 1 = c + (i + 1))
                (slotExtend (I := I) (M := M) g (b + j) (c + i)
                  (appCcLeibnizPsi (I := I) (M := M) g b c Φ i j))) =
            slotExtend (I := I) (M := M) g (b + j) (c + i)
              (appCcLeibnizPsi (I := I) (M := M) g b c Φ i j) from by
          rw [castCcTensorRank, castCcTensorSourceRank]]
      rw [hrec]
      by_cases hji : j < i
      · rw [if_pos (by omega : j + 1 < i + 1)]
        rw [iteratedCovGrad_add]
        rw [show ((iteratedCovGrad (I := I) g (b + (j + 1)) (c + (i + 1)) p
              (covGrad (I := I) (M := M) g (b + (j + 1)) (c + i)
                (appCcLeibnizPsi (I := I) (M := M) g b c Φ i (j + 1))) +
            iteratedCovGrad (I := I) g (b + (j + 1)) (c + (i + 1)) p
              (slotExtend (I := I) (M := M) g (b + j) (c + i)
                (appCcLeibnizPsi (I := I) (M := M) g b c Φ i j))).toSection x) =
            (iteratedCovGrad (I := I) g (b + (j + 1)) (c + (i + 1)) p
              (covGrad (I := I) (M := M) g (b + (j + 1)) (c + i)
                (appCcLeibnizPsi (I := I) (M := M) g b c Φ i (j + 1)))).toSection x +
              (iteratedCovGrad (I := I) g (b + (j + 1)) (c + (i + 1)) p
                (slotExtend (I := I) (M := M) g (b + j) (c + i)
                  (appCcLeibnizPsi (I := I) (M := M) g b c Φ i j))).toSection x from by
          rw [SmoothCcTensor.toSection_add]; rfl]
        refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g (b + (j + 1))
          ((c + (i + 1)) + p) x _ _) ?_
        obtain ⟨e, he⟩ : ∃ e, (j + 1) + e = i := ⟨i - (j + 1), by omega⟩
        have hcommA : riemannianFiberNormSq (I := I) (M := M) g (b + (j + 1)) ((c + (i + 1)) + p) x
              ((iteratedCovGrad (I := I) g (b + (j + 1)) (c + (i + 1)) p
                (covGrad (I := I) (M := M) g (b + (j + 1)) (c + i)
                  (appCcLeibnizPsi (I := I) (M := M) g b c Φ i (j + 1)))).toSection x) =
            riemannianFiberNormSq (I := I) (M := M) g (b + (j + 1)) ((c + i) + (p + 1)) x
              ((iteratedCovGrad (I := I) g (b + (j + 1)) (c + i) (p + 1)
                (appCcLeibnizPsi (I := I) (M := M) g b c Φ i (j + 1))).toSection x) :=
          rfns_iteratedCovGrad_covGrad_comm_rs (I := I) (M := M) g (b + (j + 1)) (c + i) p
            (appCcLeibnizPsi (I := I) (M := M) g b c Φ i (j + 1)) x
        have bA : riemannianFiberNormSq (I := I) (M := M) g (b + (j + 1)) ((c + (i + 1)) + p) x
              ((iteratedCovGrad (I := I) g (b + (j + 1)) (c + (i + 1)) p
                (covGrad (I := I) (M := M) g (b + (j + 1)) (c + i)
                  (appCcLeibnizPsi (I := I) (M := M) g b c Φ i (j + 1)))).toSection x) ≤
            (4 : ℝ) ^ i * (Module.finrank ℝ E : ℝ) ^ (j + 1) *
              riemannianFiberNormSq (I := I) (M := M) g b (c + (p + d)) x
                ((iteratedCovGrad (I := I) g b c (p + d) Φ).toSection x) := by
          rw [hcommA]
          have hihA := ih (j + 1) (p + 1) e he
          rw [rfns_iteratedCovGrad_exp_congr (I := I) (M := M) g b c Φ x
            (show (p + 1) + e = p + d by omega)] at hihA
          exact hihA
        have hsl : riemannianFiberNormSq (I := I) (M := M) g (b + (j + 1)) ((c + (i + 1)) + p) x
              ((iteratedCovGrad (I := I) g (b + (j + 1)) (c + (i + 1)) p
                (slotExtend (I := I) (M := M) g (b + j) (c + i)
                  (appCcLeibnizPsi (I := I) (M := M) g b c Φ i j))).toSection x) ≤
            (Module.finrank ℝ E : ℝ) *
              riemannianFiberNormSq (I := I) (M := M) g (b + j) ((c + i) + p) x
                ((iteratedCovGrad (I := I) g (b + j) (c + i) p
                  (appCcLeibnizPsi (I := I) (M := M) g b c Φ i j)).toSection x) :=
          rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g (b + j) (c + i)
            (appCcLeibnizPsi (I := I) (M := M) g b c Φ i j) p x
        have bB : riemannianFiberNormSq (I := I) (M := M) g (b + (j + 1)) ((c + (i + 1)) + p) x
              ((iteratedCovGrad (I := I) g (b + (j + 1)) (c + (i + 1)) p
                (slotExtend (I := I) (M := M) g (b + j) (c + i)
                  (appCcLeibnizPsi (I := I) (M := M) g b c Φ i j))).toSection x) ≤
            (4 : ℝ) ^ i * (Module.finrank ℝ E : ℝ) ^ (j + 1) *
              riemannianFiberNormSq (I := I) (M := M) g b (c + (p + d)) x
                ((iteratedCovGrad (I := I) g b c (p + d) Φ).toSection x) := by
          refine le_trans hsl ?_
          refine le_trans (mul_le_mul_of_nonneg_left (ih j p d hjd) (by positivity))
            (le_of_eq ?_)
          rw [pow_succ]; ring
        rw [show (4 : ℝ) ^ (i + 1) * (Module.finrank ℝ E : ℝ) ^ (j + 1) *
              riemannianFiberNormSq (I := I) (M := M) g b (c + (p + d)) x
                ((iteratedCovGrad (I := I) g b c (p + d) Φ).toSection x) =
            4 * ((4 : ℝ) ^ i * (Module.finrank ℝ E : ℝ) ^ (j + 1) *
              riemannianFiberNormSq (I := I) (M := M) g b (c + (p + d)) x
                ((iteratedCovGrad (I := I) g b c (p + d) Φ).toSection x)) from by
          rw [pow_succ]; ring]
        linarith [bA, bB]
      · have hji' : ¬ (j + 1 < i + 1) := by omega
        rw [if_neg hji', zero_add]
        have hsl : riemannianFiberNormSq (I := I) (M := M) g (b + (j + 1)) ((c + (i + 1)) + p) x
              ((iteratedCovGrad (I := I) g (b + (j + 1)) (c + (i + 1)) p
                (slotExtend (I := I) (M := M) g (b + j) (c + i)
                  (appCcLeibnizPsi (I := I) (M := M) g b c Φ i j))).toSection x) ≤
            (Module.finrank ℝ E : ℝ) *
              riemannianFiberNormSq (I := I) (M := M) g (b + j) ((c + i) + p) x
                ((iteratedCovGrad (I := I) g (b + j) (c + i) p
                  (appCcLeibnizPsi (I := I) (M := M) g b c Φ i j)).toSection x) :=
          rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g (b + j) (c + i)
            (appCcLeibnizPsi (I := I) (M := M) g b c Φ i j) p x
        refine le_trans hsl ?_
        refine le_trans (mul_le_mul_of_nonneg_left (ih j p d hjd) (by positivity)) ?_
        rw [show (Module.finrank ℝ E : ℝ) *
              ((4 : ℝ) ^ i * (Module.finrank ℝ E : ℝ) ^ j *
                riemannianFiberNormSq (I := I) (M := M) g b (c + (p + d)) x
                  ((iteratedCovGrad (I := I) g b c (p + d) Φ).toSection x)) =
            (4 : ℝ) ^ i * (Module.finrank ℝ E : ℝ) ^ (j + 1) *
              riemannianFiberNormSq (I := I) (M := M) g b (c + (p + d)) x
                ((iteratedCovGrad (I := I) g b c (p + d) Φ).toSection x) from by
          rw [pow_succ]; ring]
        refine mul_le_mul_of_nonneg_right ?_
          (riemannianFiberNormSq_nonneg (I := I) (M := M) g b (c + (p + d)) x _)
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ (by norm_num) (by omega)) (by positivity)

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma iteratedCovGrad_zero_tensor' (g₀ : SmoothRiemannianMetric I M) (r s m : ℕ) :
    iteratedCovGrad (I := I) g₀ r s m (0 : SmoothCcTensor g₀ r s) = 0 := by
  induction m with
  | zero => rw [iteratedCovGrad_zero]
  | succ m ih => rw [iteratedCovGrad_succ, ih, covGrad_zero]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma iteratedCovGrad_eq_zero_of_covGrad_eq_zero' (g₀ : SmoothRiemannianMetric I M)
    (r s : ℕ) (X : SmoothCcTensor g₀ r s)
    (hX : covGrad (I := I) (M := M) g₀ r s X = 0) (m : ℕ) :
    iteratedCovGrad (I := I) g₀ r s (m + 1) X = 0 := by
  induction m with
  | zero => rw [iteratedCovGrad_succ, iteratedCovGrad_zero]; exact hX
  | succ m ih => rw [iteratedCovGrad_succ, ih, covGrad_zero]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma gInvRaisedEndo_self (g₀ : SmoothRiemannianMetric I M) (x : M) :
    metricComparisonEndo (I := I) g₀ g₀ x =
      ContinuousLinearMap.id ℝ (TangentSpace I x) := by
  apply ContinuousLinearMap.ext
  intro v
  rw [gInvRaisedEndo_apply, inverseMetricSharpFib_g0FlatCLM, ContinuousLinearMap.id_apply]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma fullRaisedEndo_comp_recovery (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (metricComparisonEndo (I := I) g₀ g₁ x).comp (metricComparisonEndo (I := I) g₁ g₀ x) =
      ContinuousLinearMap.id ℝ (TangentSpace I x) := by
  apply ContinuousLinearMap.ext
  intro v
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    gInvRaisedEndo_apply, gInvRaisedEndo_apply]
  rw [g0FlatCLM_inverseMetricSharpFib (I := I) g₀ x (g0FlatCLM (I := I) g₁ x v)]
  rw [inverseMetricSharpFib_g0FlatCLM (I := I) g₁ x v]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma recovery_comp_fullRaisedEndo (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (metricComparisonEndo (I := I) g₁ g₀ x).comp (metricComparisonEndo (I := I) g₀ g₁ x) =
      ContinuousLinearMap.id ℝ (TangentSpace I x) := by
  apply ContinuousLinearMap.ext
  intro v
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    gInvRaisedEndo_apply, gInvRaisedEndo_apply]
  rw [g0FlatCLM_inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x v)]
  rw [inverseMetricSharpFib_g0FlatCLM (I := I) g₀ x v]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma slotInsertEndoFib_comp_eq (s : ℕ) (x : M)
    (A B : TangentSpace I x →L[ℝ] TangentSpace I x) :
    ContinuousLinearMap.comp (slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x A)
        (slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x B) =
      slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x (ContinuousLinearMap.comp B A) := by
  have key : ∀ D : Tensor0SSpace (s + 1) I x,
      (ContinuousLinearMap.comp (slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x A)
          (slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x B)) D =
        slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x (ContinuousLinearMap.comp B A) D := by
    intro D
    apply Tensor0SSpace.toModel_injective
    refine ContinuousMultilinearMap.ext (fun m => ?_)
    rw [ContinuousLinearMap.comp_apply, slotInsertEndoFib_apply_eval,
      slotInsertEndoFib_apply_eval, slotInsertEndoFib_apply_eval,
      ContinuousLinearMap.comp_apply, Function.update_self, Function.update_idem]
  exact ContinuousLinearMap.ext key

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma slotInsertEndoFib_id_eq' (s : ℕ) (x : M) :
    slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x
        (ContinuousLinearMap.id ℝ (TangentSpace I x)) =
      ContinuousLinearMap.id ℝ (Tensor0SSpace (s + 1) I x) := by
  apply ContinuousLinearMap.ext
  intro A
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  rw [slotInsertEndoFib_apply_eval, ContinuousLinearMap.id_apply]
  rw [ContinuousLinearMap.id_apply]
  rw [Function.update_eq_self]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma appCcRS_recovery_eq (g₀ g₁ : SmoothRiemannianMetric I M) :
    ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 1
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0 (fullRaisedEndoField (I := I) (M := M) g₁ g₀))
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0 (fullRaisedEndoField (I := I) (M := M) g₀ g₁)) =
      endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
        (fullRaisedEndoField (I := I) (M := M) g₀ g₀) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [appCcRS_toSection]
  simp only [slotInsertEndoCc_toSection, fullRaisedEndoField_apply]
  rw [slotInsertEndoFib_comp_eq, fullRaisedEndo_comp_recovery, gInvRaisedEndo_self]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma endoCovariantDerivative_fullRaised_self_eq_zero (g₀ : SmoothRiemannianMetric I M)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (v : TangentSpace I x) :
    ((endoCovariantDerivative (I := I) (M := M) g₀)
        (fullRaisedEndoField (I := I) (M := M) g₀ g₀) x v) (Y x) = 0 := by
  have hLeib := endoCovariantDerivative_apply (I := I) (M := M) g₀
    (fullRaisedEndoField (I := I) (M := M) g₀ g₀) Y x v
  have hΛapp : (fun y : M => (fullRaisedEndoField (I := I) (M := M) g₀ g₀ y) (Y y)) =
      (fun y : M => Y y) := by
    funext y
    rw [fullRaisedEndoField_apply, gInvRaisedEndo_self, ContinuousLinearMap.id_apply]
  rw [hLeib, hΛapp]
  rw [fullRaisedEndoField_apply, gInvRaisedEndo_self, ContinuousLinearMap.id_apply]
  rw [sub_self]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
private lemma covGrad_slotInsert_self_eq_zero (g₀ : SmoothRiemannianMetric I M) :
    covGrad (I := I) (M := M) g₀ 1 1
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (fullRaisedEndoField (I := I) (M := M) g₀ g₀)) = 0 := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  rw [covGrad_toSection_apply_eval (I := I) (M := M) g₀ 1 1
    (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
      (fullRaisedEndoField (I := I) (M := M) g₀ g₀)) x D m]
  rw [tensorCovDerivAt_slotInsertEndoCc_eq (I := I) (M := M) g₀ 0
    (fullRaisedEndoField (I := I) (M := M) g₀ g₀) x (m 0)]
  rw [show ((endoCovariantDerivative (I := I) (M := M) g₀)
        (fullRaisedEndoField (I := I) (M := M) g₀ g₀) x (m 0)) =
      (0 : TangentSpace I x →L[ℝ] TangentSpace I x) from by
    apply ContinuousLinearMap.ext
    intro w
    rw [ContinuousLinearMap.zero_apply]
    obtain ⟨Y, hY⟩ := ContMDiffSection.exists_eq_at (I := I)
      (F := E) (V := fun y : M => TangentSpace I y) (n := (⊤ : ℕ∞)) x w
    rw [← hY]
    exact endoCovariantDerivative_fullRaised_self_eq_zero (I := I) (M := M) g₀ Y x (m 0)]
  rw [show slotInsertEndoFib (I := I) (M := M) (0 + 1) 0 x
        (0 : TangentSpace I x →L[ℝ] TangentSpace I x) = 0 from by
    rw [show (0 : TangentSpace I x →L[ℝ] TangentSpace I x) =
        (0 : ℝ) • (0 : TangentSpace I x →L[ℝ] TangentSpace I x) from (zero_smul ℝ _).symm,
      slotInsertEndoFib_smul_left, zero_smul]]
  simp [SmoothCcTensor.toSection_zero]

omit [NeZero (Module.finrank ℝ E)] in
private lemma iteratedCovGrad_slotInsert_self_eq_zero (g₀ : SmoothRiemannianMetric I M) (m : ℕ) :
    iteratedCovGrad (I := I) g₀ 1 1 (m + 1)
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (fullRaisedEndoField (I := I) (M := M) g₀ g₀)) = 0 :=
  iteratedCovGrad_eq_zero_of_covGrad_eq_zero' (I := I) (M := M) g₀ 1 1
    (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0 (fullRaisedEndoField (I := I) (M := M) g₀ g₀))
    (covGrad_slotInsert_self_eq_zero (I := I) (M := M) g₀) m

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma slotInsertEndoCc_raisedEndoField_comp_swap_eq_id (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (fullRaisedEndoField (I := I) (M := M) g₀ g₁)).toSection x).comp
      (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (fullRaisedEndoField (I := I) (M := M) g₁ g₀)).toSection x) =
      ContinuousLinearMap.id ℝ (Tensor0SSpace 1 I x) := by
  simp only [slotInsertEndoCc_toSection, fullRaisedEndoField_apply]
  rw [slotInsertEndoFib_comp_eq, recovery_comp_fullRaisedEndo]
  exact slotInsertEndoFib_id_eq' (I := I) (M := M) 0 x

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma slotInsertIter_recovery_comp_eq_id (g₀ g₁ : SmoothRiemannianMetric I M)
    (w : ℕ) (x : M) :
    (show Tensor0SSpace (1 + w) I x →L[ℝ] Tensor0SSpace (1 + w) I x from
        (slotExtendIter (I := I) (M := M) g₀ 1 1 w
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
            (fullRaisedEndoField (I := I) (M := M) g₀ g₁))).toSection x).comp
      (show Tensor0SSpace (1 + w) I x →L[ℝ] Tensor0SSpace (1 + w) I x from
        (slotExtendIter (I := I) (M := M) g₀ 1 1 w
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
            (fullRaisedEndoField (I := I) (M := M) g₁ g₀))).toSection x) =
      ContinuousLinearMap.id ℝ (Tensor0SSpace (1 + w) I x) := by
  induction w with
  | zero =>
      exact slotInsertEndoCc_raisedEndoField_comp_swap_eq_id (I := I) (M := M) g₀ g₁ x
  | succ w ih =>
      rw [show slotExtendIter (I := I) (M := M) g₀ 1 1 (w + 1)
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
              (fullRaisedEndoField (I := I) (M := M) g₀ g₁)) =
          slotExtend (I := I) (M := M) g₀ (1 + w) (1 + w)
            (slotExtendIter (I := I) (M := M) g₀ 1 1 w
              (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
                (fullRaisedEndoField (I := I) (M := M) g₀ g₁))) from rfl]
      rw [show slotExtendIter (I := I) (M := M) g₀ 1 1 (w + 1)
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
              (fullRaisedEndoField (I := I) (M := M) g₁ g₀)) =
          slotExtend (I := I) (M := M) g₀ (1 + w) (1 + w)
            (slotExtendIter (I := I) (M := M) g₀ 1 1 w
              (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
                (fullRaisedEndoField (I := I) (M := M) g₁ g₀))) from rfl]
      rw [slotExtend_toSection, slotExtend_toSection, slotExtendFib_comp, ih]
      exact slotExtendFib_id_eq (I := I) (M := M) g₀ (1 + w) x

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma master_isolation' (g₀ g₁ : SmoothRiemannianMetric I M) (w : ℕ)
    (X : SmoothCcTensor g₀ 1 (1 + w)) :
    ccOperatorFieldComp (I := I) (M := M) g₀ 1 (1 + w) (1 + w)
        (slotExtendIter (I := I) (M := M) g₀ 1 1 w
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
            (fullRaisedEndoField (I := I) (M := M) g₀ g₁)))
        (ccOperatorFieldComp (I := I) (M := M) g₀ 1 (1 + w) (1 + w)
          (slotExtendIter (I := I) (M := M) g₀ 1 1 w
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
              (fullRaisedEndoField (I := I) (M := M) g₁ g₀))) X) = X := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [appCcRS_toSection, appCcRS_toSection]
  rw [← ContinuousLinearMap.comp_assoc]
  rw [slotInsertIter_recovery_comp_eq_id (I := I) (M := M) g₀ g₁ w x]
  rw [ContinuousLinearMap.id_comp]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma slotInsertEndoCc_add (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (A B : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    endoSlotZeroCcTensor (I := I) (M := M) g₀ s (A + B) =
      endoSlotZeroCcTensor (I := I) (M := M) g₀ s A +
        endoSlotZeroCcTensor (I := I) (M := M) g₀ s B := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  rw [show ((endoSlotZeroCcTensor (I := I) (M := M) g₀ s A +
        endoSlotZeroCcTensor (I := I) (M := M) g₀ s B).toSection x) =
      (endoSlotZeroCcTensor (I := I) (M := M) g₀ s A).toSection x +
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ s B).toSection x from by
    rw [SmoothCcTensor.toSection_add]; rfl]
  rw [ContinuousLinearMap.add_apply]
  simp only [slotInsertEndoCc_toSection]
  rw [show ((A + B) x) = A x + B x from by rw [ContMDiffSection.coe_add]; rfl]
  rw [slotInsertEndoFib_add_left, ContinuousLinearMap.add_apply]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma fullRaisedEndoField_recovery_decomp (g₀ g₁ : SmoothRiemannianMetric I M) :
    fullRaisedEndoField (I := I) (M := M) g₁ g₀ =
      gInvDiffRaisedEndoField (I := I) g₁ g₀ +
        fullRaisedEndoField (I := I) (M := M) g₀ g₀ := by
  apply ContMDiffSection.ext
  intro x
  rw [show ((gInvDiffRaisedEndoField (I := I) g₁ g₀ +
        fullRaisedEndoField (I := I) (M := M) g₀ g₀) x) =
      gInvDiffRaisedEndoField (I := I) g₁ g₀ x +
        fullRaisedEndoField (I := I) (M := M) g₀ g₀ x from by
    rw [ContMDiffSection.coe_add]; rfl]
  apply ContinuousLinearMap.ext
  intro v
  rw [fullRaisedEndoField_apply, ContinuousLinearMap.add_apply]
  rw [show (gInvDiffRaisedEndoField (I := I) g₁ g₀ x) = metricComparisonDiffEndo (I := I) g₁ g₀ x from rfl]
  rw [fullRaisedEndoField_apply, gInvRaisedEndo_self, ContinuousLinearMap.id_apply]
  rw [gInvRaisedEndo_eq_diff_add_id]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
set_option backward.isDefEq.respectTransparency false in
private lemma interior_product_toModel_eval (s : ℕ) (x : M) (v : TangentSpace I x)
    (D : Tensor0SSpace (s + 1) I x) (w : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel
        (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) s x v D) w =
      Tensor0SSpace.toModel D (Fin.cons (show E from v) (fun k => (show E from w k))) := by
  have h1 : Tensor0SSpace.toModel
      (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) s x v D) =
      Tensor0SBundle.model_interior_product (𝕜 := ℝ) (E := E) s (show E from v)
        (Tensor0SSpace.toModel D) := rfl
  rw [h1]
  rfl

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
  (smoothCcTensorBilinForm ccTensorModel ccTensorMultilinear ccTensorBilin_apply) in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma unitModel_eq_ccTensorBilin_loc (g₀ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (b : M) (u w : TangentSpace I b) :
    unitModel (I := I) (M := M) g₀ 2 S b ![u, w] = smoothCcTensorBilinForm (I := I) g₀ S b u w := by
  rw [ccTensorBilin_apply (I := I) g₀ S b u w, ccTensorModel]
  rw [show ccTensorMultilinear (I := I) g₀ S b =
      (show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace 2 I b from S.toSection b)
        (unitZeroSec (I := I) (M := M) b) from rfl]
  rw [unitModel]
  refine congrArg _ ?_
  funext k
  fin_cases k <;> rfl

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma cotangentToDual_cometricRaiseSlot0_eq (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (x : M) (om : Tensor0SSpace 1 I x) (w : TangentSpace I x) :
    cotangentToDual (I := I)
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
            (ccTensor02Symm (I := I) (M := M) g₀ T)).toSection x) om) w =
      ccTensorBilinSymm (I := I) g₀ T x (inverseMetricSharpFib (I := I) g₀ x om) w := by
  rw [cotangentToDual_apply]
  rw [cometricRaiseSlot0Field_toSection]
  rw [cometricRaiseSlot0Fib_clm_apply (I := I) g₀ 0 x _ om]
  rw [show (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (0 + 1) x
          (inverseMetricSharpFib (I := I) g₀ x om)
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (0 + 2) I x from
              (ccTensor02Symm (I := I) (M := M) g₀ T).toSection x)
            (unitTensor (I := I) (M := M) x)) (fun _ : Fin 1 => w) : ℝ) =
      Tensor0SSpace.toModel
        (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (0 + 1) x
          (inverseMetricSharpFib (I := I) g₀ x om)
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (0 + 2) I x from
              (ccTensor02Symm (I := I) (M := M) g₀ T).toSection x)
            (unitTensor (I := I) (M := M) x)))
        (fun _ : Fin 1 => w) from rfl]
  rw [interior_product_toModel_eval (I := I) (M := M) (0 + 1) x
    (inverseMetricSharpFib (I := I) g₀ x om)
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (0 + 2) I x from
        (ccTensor02Symm (I := I) (M := M) g₀ T).toSection x)
      (unitTensor (I := I) (M := M) x)) (fun _ : Fin 1 => w)]
  rw [show Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (0 + 2) I x from
            (ccTensor02Symm (I := I) (M := M) g₀ T).toSection x)
          (unitTensor (I := I) (M := M) x))
        (Fin.cons (show E from inverseMetricSharpFib (I := I) g₀ x om)
          (fun _ : Fin 1 => (show E from w))) =
      unitModel (I := I) (M := M) g₀ 2 (ccTensor02Symm (I := I) (M := M) g₀ T) x
        ![inverseMetricSharpFib (I := I) g₀ x om, w] from by
    rw [unitModel]
    congr 1
    funext k
    refine Fin.cases ?_ (fun j => ?_) k
    · simp only [Fin.cons_zero, Matrix.cons_val_zero]
    · simp only [Fin.cons_succ]
      fin_cases j
      rfl]
  rw [unitModel_eq_ccTensorBilin_loc, ccTensorBilin_symmS]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma cotangentToDual_slotInsertEndoFib (x : M)
    (Λ : TangentSpace I x →L[ℝ] TangentSpace I x) (om : Tensor0SSpace 1 I x)
    (w : TangentSpace I x) :
    cotangentToDual (I := I)
        (slotInsertEndoFib (I := I) (M := M) 1 0 x Λ om) w =
      cotangentToDual (I := I) om (Λ w) := by
  rw [cotangentToDual_apply, cotangentToDual_apply]
  rw [show (slotInsertEndoFib (I := I) (M := M) 1 0 x Λ om) (fun _ : Fin 1 => w)
      = Tensor0SSpace.toModel (slotInsertEndoFib (I := I) (M := M) 1 0 x Λ om)
          (fun _ : Fin 1 => (show E from w)) from rfl]
  rw [slotInsertEndoFib_apply_eval]
  rw [show Function.update (fun _ : Fin 1 => (show E from w)) 0
        (Λ ((fun _ : Fin 1 => (show E from w)) 0)) =
      (fun _ : Fin 1 => (show E from Λ w)) from by
    funext k; fin_cases k; simp]
  rfl

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma slotInsertEndoCc_gInvDiffRaised_eq_cometricRaise
    (g₀ g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w) :
    endoSlotZeroCcTensor (I := I) (M := M) g₀ 0 (gInvDiffRaisedEndoField (I := I) g₁ g₀) =
      cometricRaiseSlot0Field (I := I) (M := M) g₀ 0 (ccTensor02Symm (I := I) (M := M) g₀ T) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply tensorRSSpace_ext 1 1 x
  intro om
  apply cotangentToDualLinear_injective (I := I) (x := x)
  apply LinearMap.ext
  intro w
  rw [cotangentToDualLinear_apply, cotangentToDualLinear_apply]
  rw [cotangentToDual_cometricRaiseSlot0_eq (I := I) (M := M) g₀ T x om w]
  simp only [slotInsertEndoCc_toSection]
  rw [show (gInvDiffRaisedEndoField (I := I) g₁ g₀ x) =
      metricComparisonDiffEndo (I := I) g₁ g₀ x from rfl]
  rw [cotangentToDual_slotInsertEndoFib (I := I) (M := M) x
    (metricComparisonDiffEndo (I := I) g₁ g₀ x) om w]
  rw [← cotangentToDualLinear_apply, ← inverseMetricSharpFib_inner]
  rw [g₀.symm x (inverseMetricSharpFib (I := I) g₀ x om)
    (metricComparisonDiffEndo (I := I) g₁ g₀ x w)]
  rw [inner_g1_gInvDiffRaisedEndo (I := I) g₁ g₀ x w
    (inverseMetricSharpFib (I := I) g₀ x om)]
  rw [htie x w (inverseMetricSharpFib (I := I) g₀ x om)]
  rw [add_sub_cancel_left]
  rw [ccTensorBilinSymm_symm (I := I) g₀ T x w (inverseMetricSharpFib (I := I) g₀ x om)]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma slotInsert_recovery_decomp
    (g₀ g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w) :
    endoSlotZeroCcTensor (I := I) (M := M) g₀ 0 (fullRaisedEndoField (I := I) (M := M) g₁ g₀) =
      endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (fullRaisedEndoField (I := I) (M := M) g₀ g₀) +
        cometricRaiseSlot0Field (I := I) (M := M) g₀ 0 (ccTensor02Symm (I := I) (M := M) g₀ T) := by
  rw [fullRaisedEndoField_recovery_decomp (I := I) (M := M) g₀ g₁]
  rw [slotInsertEndoCc_add]
  rw [slotInsertEndoCc_gInvDiffRaised_eq_cometricRaise (I := I) (M := M) g₀ g₁ T htie]
  exact add_comm _ _

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
private lemma rfns_iteratedCovGrad_symmS_le_pointwise
    (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2) (k : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x
        ((iteratedCovGrad (I := I) g₀ 0 2 k (ccTensor02Symm (I := I) (M := M) g₀ T)).toSection x) ≤
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x
        ((iteratedCovGrad (I := I) g₀ 0 2 k T).toSection x) := by
  have hswap_inv : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x
      ((iteratedCovGrad (I := I) g₀ 0 2 k
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x
        ((iteratedCovGrad (I := I) g₀ 0 2 k T).toSection x) :=
    riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) T k x
  set A := iteratedCovGrad (I := I) g₀ 0 2 k T with hA
  set B := iteratedCovGrad (I := I) g₀ 0 2 k
    (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T) with hB
  have hiter : iteratedCovGrad (I := I) g₀ 0 2 k (ccTensor02Symm (I := I) (M := M) g₀ T) =
      (1 / 2 : ℝ) • A + (1 / 2 : ℝ) • B := by
    rw [hA, hB]; exact iteratedCovGrad_symmS_eq (I := I) (M := M) g₀ T k
  have htoSec : ((iteratedCovGrad (I := I) g₀ 0 2 k
        (ccTensor02Symm (I := I) (M := M) g₀ T)).toSection x : TensorRSSpace 0 (2 + k) I x) =
      (1 / 2 : ℝ) • (A.toSection x) + (1 / 2 : ℝ) • (B.toSection x) := by
    rw [hiter]
    rw [show (((1 / 2 : ℝ) • A + (1 / 2 : ℝ) • B).toSection x) =
        ((1 / 2 : ℝ) • A).toSection x + ((1 / 2 : ℝ) • B).toSection x from by
      rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add]; rfl]
    rw [show (((1 / 2 : ℝ) • A).toSection x) = (1 / 2 : ℝ) • (A.toSection x) from by
        rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul]; rfl,
      show (((1 / 2 : ℝ) • B).toSection x) = (1 / 2 : ℝ) • (B.toSection x) from by
        rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul]; rfl]
  rw [htoSec]
  calc riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x
          ((1 / 2 : ℝ) • (A.toSection x) + (1 / 2 : ℝ) • (B.toSection x))
      ≤ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x ((1 / 2 : ℝ) • (A.toSection x)) +
          2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x ((1 / 2 : ℝ) • (B.toSection x)) :=
        riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (2 + k) x _ _
    _ = (1 / 2 : ℝ) * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x (A.toSection x) +
          (1 / 2 : ℝ) * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x (B.toSection x) := by
        rw [rfns_smul_fib, rfns_smul_fib]; ring
    _ = (1 / 2 : ℝ) * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x (A.toSection x) +
          (1 / 2 : ℝ) * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x (A.toSection x) := by
        rw [hswap_inv]
    _ = riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x (A.toSection x) := by ring

omit [NeZero (Module.finrank ℝ E)] in
private lemma rfns_iteratedCovGrad_SI_M_succ_le
    (g₀ g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
    (j : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + (j + 1)) x
        ((iteratedCovGrad (I := I) g₀ 1 1 (j + 1)
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
            (fullRaisedEndoField (I := I) (M := M) g₁ g₀))).toSection x) ≤
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (j + 1)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (j + 1) T).toSection x) := by
  rw [slotInsert_recovery_decomp (I := I) (M := M) g₀ g₁ T htie, iteratedCovGrad_add]
  rw [show ((iteratedCovGrad (I := I) g₀ 1 1 (j + 1)
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (fullRaisedEndoField (I := I) (M := M) g₀ g₀)) +
        iteratedCovGrad (I := I) g₀ 1 1 (j + 1)
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
            (ccTensor02Symm (I := I) (M := M) g₀ T))).toSection x) =
      (iteratedCovGrad (I := I) g₀ 1 1 (j + 1)
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (fullRaisedEndoField (I := I) (M := M) g₀ g₀))).toSection x +
        (iteratedCovGrad (I := I) g₀ 1 1 (j + 1)
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
            (ccTensor02Symm (I := I) (M := M) g₀ T))).toSection x from by
    rw [SmoothCcTensor.toSection_add]; rfl]
  rw [iteratedCovGrad_slotInsert_self_eq_zero (I := I) (M := M) g₀ j]
  rw [show ((0 : SmoothCcTensor g₀ 1 (1 + (j + 1))).toSection x) =
      (0 : TensorRSSpace 1 (1 + (j + 1)) I x) from by rw [SmoothCcTensor.toSection_zero]; rfl]
  rw [zero_add]
  refine le_trans (le_of_eq ?_)
    (rfns_iteratedCovGrad_symmS_le_pointwise (I := I) (M := M) g₀ T (j + 1) x)
  exact riemannianFiberNormSq_iteratedCovGrad_cometricRaiseSlot0Field_eq (E := E) (I := I) (M := M) g₀ 0
    (ccTensor02Symm (I := I) (M := M) g₀ T) (j + 1) x

private lemma rfns_appCcLeibnizPsi_recovery_le
    (g₀ g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
    (m : ℕ) (k : ℕ) (hk : k ≤ m) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ (1 + k) (1 + (m + 1)) x
        ((appCcLeibnizPsi (I := I) (M := M) g₀ 1 1
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
            (fullRaisedEndoField (I := I) (M := M) g₁ g₀)) (m + 1) k).toSection x) ≤
      4 ^ (m + 1) * (Module.finrank ℝ E : ℝ) ^ k *
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + ((m - k) + 1)) x
          ((iteratedCovGrad (I := I) g₀ 0 2 ((m - k) + 1) T).toSection x) := by
  have hkey := rfns_iteratedCovGrad_appCcLeibnizPsi_le (I := I) (M := M) g₀ 1 1
    (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
      (fullRaisedEndoField (I := I) (M := M) g₁ g₀)) x (m + 1) k 0 ((m + 1) - k) (by omega)
  refine le_trans (le_of_eq ?_) (le_trans hkey ?_)
  · rfl
  · refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [rfns_iteratedCovGrad_exp_congr (I := I) (M := M) g₀ 1 1
      (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
        (fullRaisedEndoField (I := I) (M := M) g₁ g₀)) x
      (show 0 + ((m + 1) - k) = (m - k) + 1 by omega)]
    exact rfns_iteratedCovGrad_SI_M_succ_le (I := I) (M := M) g₀ g₁ T htie (m - k) x

private lemma rfns_iteratedCovGrad_SI_F_leibniz_grid_bound
    (g₀ g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
    (m : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + (m + 1)) x
        ((iteratedCovGrad (I := I) g₀ 1 1 (m + 1)
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
            (fullRaisedEndoField (I := I) (M := M) g₀ g₁))).toSection x) ≤
      (Module.finrank ℝ E : ℝ) ^ (m + 1) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + 0) x
          ((iteratedCovGrad (I := I) g₀ 1 1 0
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
              (fullRaisedEndoField (I := I) (M := M) g₀ g₁))).toSection x) *
        ((m + 1 : ℝ) * ∑ k ∈ Finset.range (m + 1),
          (4 ^ (m + 1) * (Module.finrank ℝ E : ℝ) ^ k *
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + ((m - k) + 1)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 ((m - k) + 1) T).toSection x)) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + k) x
              ((iteratedCovGrad (I := I) g₀ 1 1 k
                (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
                  (fullRaisedEndoField (I := I) (M := M) g₀ g₁))).toSection x)) := by
  have hleib := iteratedCovGrad_appCcRS_eq (I := I) (M := M) g₀ 1 1 1
    (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0 (fullRaisedEndoField (I := I) (M := M) g₁ g₀))
    (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0 (fullRaisedEndoField (I := I) (M := M) g₀ g₁)) (m + 1)
  rw [appCcRS_recovery_eq (I := I) (M := M) g₀ g₁,
    iteratedCovGrad_slotInsert_self_eq_zero (I := I) (M := M) g₀ m,
    Finset.sum_range_succ,
    appCcLeibnizPsi_diag_eq (I := I) (M := M) g₀ 1 1
      (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0 (fullRaisedEndoField (I := I) (M := M) g₁ g₀))
      (m + 1)] at hleib
  set sigSum := ∑ k ∈ Finset.range (m + 1), ccOperatorFieldComp (I := I) (M := M) g₀ 1 (1 + k) (1 + (m + 1))
    (appCcLeibnizPsi (I := I) (M := M) g₀ 1 1
      (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0 (fullRaisedEndoField (I := I) (M := M) g₁ g₀))
      (m + 1) k)
    (iteratedCovGrad (I := I) g₀ 1 1 k
      (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0 (fullRaisedEndoField (I := I) (M := M) g₀ g₁)))
    with hsigDef
  have hdiag : ccOperatorFieldComp (I := I) (M := M) g₀ 1 (1 + (m + 1)) (1 + (m + 1))
        (slotExtendIter (I := I) (M := M) g₀ 1 1 (m + 1)
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0 (fullRaisedEndoField (I := I) (M := M) g₁ g₀)))
        (iteratedCovGrad (I := I) g₀ 1 1 (m + 1)
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
            (fullRaisedEndoField (I := I) (M := M) g₀ g₁))) = -sigSum :=
    eq_neg_of_add_eq_zero_right hleib.symm
  have hmi := master_isolation' (I := I) (M := M) g₀ g₁ (m + 1)
    (iteratedCovGrad (I := I) g₀ 1 1 (m + 1)
      (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0 (fullRaisedEndoField (I := I) (M := M) g₀ g₁)))
  rw [hdiag] at hmi
  have hsigToSection : (sigSum.toSection x : TensorRSSpace 1 (1 + (m + 1)) I x) =
      ∑ k ∈ Finset.range (m + 1),
        ((ccOperatorFieldComp (I := I) (M := M) g₀ 1 (1 + k) (1 + (m + 1))
          (appCcLeibnizPsi (I := I) (M := M) g₀ 1 1
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
              (fullRaisedEndoField (I := I) (M := M) g₁ g₀)) (m + 1) k)
          (iteratedCovGrad (I := I) g₀ 1 1 k
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
              (fullRaisedEndoField (I := I) (M := M) g₀ g₁)))).toSection x) := by
    rw [hsigDef, SmoothCcTensor.toSection_sum_apply]
  have hSigmaBound : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + (m + 1)) x
        (sigSum.toSection x) ≤
      (m + 1 : ℝ) * ∑ k ∈ Finset.range (m + 1),
        (4 ^ (m + 1) * (Module.finrank ℝ E : ℝ) ^ k *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + ((m - k) + 1)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 ((m - k) + 1) T).toSection x)) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + k) x
            ((iteratedCovGrad (I := I) g₀ 1 1 k
              (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
                (fullRaisedEndoField (I := I) (M := M) g₀ g₁))).toSection x) := by
    rw [hsigToSection]
    refine le_trans (riemannianFiberNormSq_sum_le_card_mul (I := I) (M := M) g₀ 1 (1 + (m + 1)) x
      (Finset.range (m + 1)) (fun k => (ccOperatorFieldComp (I := I) (M := M) g₀ 1 (1 + k) (1 + (m + 1))
        (appCcLeibnizPsi (I := I) (M := M) g₀ 1 1
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
            (fullRaisedEndoField (I := I) (M := M) g₁ g₀)) (m + 1) k)
        (iteratedCovGrad (I := I) g₀ 1 1 k
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
            (fullRaisedEndoField (I := I) (M := M) g₀ g₁)))).toSection x)) ?_
    rw [Finset.card_range, Nat.cast_add, Nat.cast_one]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Finset.sum_le_sum
    intro k hk
    have hkm : k ≤ m := by rw [Finset.mem_range] at hk; omega
    rw [appCcRS_toSection]
    refine le_trans (riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ 1 (1 + k)
      (1 + (m + 1)) x _ _) ?_
    apply mul_le_mul_of_nonneg_right
      (rfns_appCcLeibnizPsi_recovery_le (I := I) (M := M) g₀ g₁ T htie m k hkm x)
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (1 + k) x _)
  rw [← hmi, appCcRS_toSection]
  refine le_trans (riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ 1 (1 + (m + 1))
    (1 + (m + 1)) x _ _) ?_
  rw [rfns_slotExtendIter_eq (I := I) (M := M) g₀ 1 1 (m + 1)
    (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0 (fullRaisedEndoField (I := I) (M := M) g₀ g₁)) x]
  rw [show ((-sigSum).toSection x : TensorRSSpace 1 (1 + (m + 1)) I x) =
      -(sigSum.toSection x) from by rw [SmoothCcTensor.toSection_neg]; rfl]
  rw [rfns_neg_fib]
  exact mul_le_mul_of_nonneg_left hSigmaBound
    (mul_nonneg (by positivity)
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (1 + 0) x _))

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma coframeS_one_eq_g0FlatCLM' (g₀ : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (K : Fin 1 → Fin n) :
    coframeS (I := I) (M := M) g₀ x 1 e K = g0FlatCLM (I := I) g₀ x (e (K 0)) := by
  apply cotangentToDualLinear_injective (I := I) (x := x)
  apply LinearMap.ext
  intro w
  rw [cotangentToDualLinear_apply, cotangentToDualLinear_apply, cotangentToDual_apply,
    cotangentToDual_apply]
  rw [show coframeS (I := I) (M := M) g₀ x 1 e K (fun _ : Fin 1 => w) =
      ∏ k : Fin 1, g₀.inner x (e (K k)) w from coframeS_apply (I := I) (M := M) g₀ x 1 e K _]
  rw [Fin.prod_univ_one]
  rw [g0FlatCLM_apply, dualToCotangent_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma fiberNormSqComponent_slotInsertFULL
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) {n : ℕ}
    (e : Fin n → TangentSpace I x)
    (K : Fin 1 → Fin n) (J : Fin 1 → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g₀ x 1 1
        ((endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (fullRaisedEndoField (I := I) (M := M) g₀ g₁)).toSection x) n e K J =
      g₀.inner x (e (K 0)) (metricComparisonEndo (I := I) g₀ g₁ x (e (J 0))) := by
  have hcomp : fiberNormSqComponent (I := I) (M := M) g₀ x 1 1
        ((endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (fullRaisedEndoField (I := I) (M := M) g₀ g₁)).toSection x) n e K J =
      Tensor0SSpace.toModel
        ((slotInsertEndoFib (I := I) (M := M) 1 0 x (metricComparisonEndo (I := I) g₀ g₁ x))
          (coframeS (I := I) (M := M) g₀ x 1 e K))
        (fun k => e (J k)) := by
    unfold fiberNormSqComponent coframeS
    rfl
  rw [hcomp, slotInsertEndoFib_apply_eval]
  rw [show (coframeS (I := I) (M := M) g₀ x 1 e K).toModel
        (Function.update (fun k => e (J k)) 0
          (metricComparisonEndo (I := I) g₀ g₁ x ((fun k => e (J k)) 0)))
      = coframeS (I := I) (M := M) g₀ x 1 e K
        (Function.update (fun k => e (J k)) 0
          (metricComparisonEndo (I := I) g₀ g₁ x (e (J 0)))) from rfl]
  rw [coframeS_apply, Fin.prod_univ_one, Function.update_self]

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma rfns_slotInsertFULL_zero_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (_hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1)
    (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (h : ∀ y v w, g₁.inner y v w =
      g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
    {δ : ℝ} (hδ : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
    (hbound : metricCauchySchwarzBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x
        ((endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (fullRaisedEndoField (I := I) (M := M) g₀ g₁)).toSection x) ≤
      ((Module.finrank ℝ E : ℝ)) ^ 2 * (1 / (1 - δ₀)) ^ 2 := by
  classical
  have hceil0 : 0 < 1 - δ₀ := by linarith
  have hcoeff : 0 < 1 - δ := by linarith
  obtain ⟨n, e, bse, hn, hbse, horth, hpars, hrepr_v, hsum⟩ :=
    tangent_orthonormalBasis_witness (I := I) (M := M) g₀ x
  have hnE : n = Module.finrank ℝ E := by rw [hn]; rfl
  have hg₁ : ∀ (b : M) (u₁ u₂ : TangentSpace I b),
      g₁.inner b u₁ u₂ = g₀.inner b u₁ u₂ + ccTensorBilinSymm (I := I) g₀ T b u₁ u₂ :=
    fun b u₁ u₂ => h b u₁ u₂
  rw [riemannianFiberNormSq_eq_sum_componentSq_of_basis (I := I) (M := M) g₀ 1 1 x
    ((endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
      (fullRaisedEndoField (I := I) (M := M) g₀ g₁)).toSection x) e bse hnE hbse horth]
  have hinv_le : 1 / (1 - δ) ≤ 1 / (1 - δ₀) := by
    rw [div_le_div_iff₀ hcoeff hceil0]; linarith
  have hinv₀_nn : 0 ≤ 1 / (1 - δ₀) := by positivity
  have heach : ∀ (K J : Fin 1 → Fin n),
      (fiberNormSqComponent (I := I) (M := M) g₀ x 1 1
        ((endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (fullRaisedEndoField (I := I) (M := M) g₀ g₁)).toSection x) n e K J) ^ 2 ≤
        (1 / (1 - δ₀)) ^ 2 := by
    intro K J
    rw [fiberNormSqComponent_slotInsertFULL (I := I) (M := M) g₀ g₁ x e K J]
    set u : TangentSpace I x := metricComparisonEndo (I := I) g₀ g₁ x (e (J 0)) with hu_def
    have hcs := metric_inner_cauchy_schwarz_sq (I := I) (M := M) g₀ x (e (K 0)) u
    have hKK : g₀.inner x (e (K 0)) (e (K 0)) = 1 := by rw [horth (K 0) (K 0)]; simp
    rw [hKK, one_mul] at hcs
    have hsfib := sqrt_inner_gInvRaisedEndo_le (I := I) g₀ g₁
      (ccTensorBilinSymm (I := I) g₀ T) hg₁ (by linarith : δ < 1) hδ0 hbound x (e (J 0))
    have hJJ : g₀.inner x (e (J 0)) (e (J 0)) = 1 := by rw [horth (J 0) (J 0)]; simp
    rw [hJJ, Real.sqrt_one, mul_one] at hsfib
    rw [← hu_def] at hsfib
    have huu_nn : 0 ≤ g₀.inner x u u := metric_inner_self_nonneg (I := I) (M := M) g₀ x u
    have hsqrt_eq : Real.sqrt (g₀.inner x u u) ^ 2 = g₀.inner x u u :=
      Real.sq_sqrt huu_nn
    have hsqrt_nn : 0 ≤ Real.sqrt (g₀.inner x u u) := Real.sqrt_nonneg _
    have huu_le : g₀.inner x u u ≤ (1 / (1 - δ₀)) ^ 2 := by
      rw [← hsqrt_eq]
      have hsfib' : Real.sqrt (g₀.inner x u u) ≤ 1 / (1 - δ₀) := le_trans hsfib hinv_le
      have := mul_self_le_mul_self hsqrt_nn hsfib'
      nlinarith [this, hsfib', hinv₀_nn]
    calc (g₀.inner x (e (K 0)) u) ^ 2
        ≤ g₀.inner x u u := hcs
      _ ≤ (1 / (1 - δ₀)) ^ 2 := huu_le
  calc ∑ K : Fin 1 → Fin n, ∑ J : Fin 1 → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g₀ x 1 1
          ((endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
            (fullRaisedEndoField (I := I) (M := M) g₀ g₁)).toSection x) n e K J) ^ 2
      ≤ ∑ K : Fin 1 → Fin n, ∑ J : Fin 1 → Fin n, (1 / (1 - δ₀)) ^ 2 :=
        Finset.sum_le_sum (fun K _ => Finset.sum_le_sum (fun J _ => heach K J))
    _ = (Fintype.card (Fin 1 → Fin n) : ℝ) * (Fintype.card (Fin 1 → Fin n) : ℝ) *
        (1 / (1 - δ₀)) ^ 2 := by
        rw [Finset.sum_const, Finset.sum_const]
        simp only [Finset.card_univ, nsmul_eq_mul]
        ring
    _ = ((Module.finrank ℝ E : ℝ)) ^ 2 * (1 / (1 - δ₀)) ^ 2 := by
        simp only [Fintype.card_fun, Fintype.card_fin, pow_one]
        rw [← hnE]
        ring

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma fiberNormSqComponent_slotInsertE
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) {n : ℕ}
    (e : Fin n → TangentSpace I x)
    (K : Fin 1 → Fin n) (J : Fin 1 → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g₀ x 1 1
        ((endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (gInvDiffRaisedEndoField (I := I) g₀ g₁)).toSection x) n e K J =
      g₀.inner x (e (K 0)) (metricComparisonDiffEndo (I := I) g₀ g₁ x (e (J 0))) := by
  have hcomp : fiberNormSqComponent (I := I) (M := M) g₀ x 1 1
        ((endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (gInvDiffRaisedEndoField (I := I) g₀ g₁)).toSection x) n e K J =
      Tensor0SSpace.toModel
        ((slotInsertEndoFib (I := I) (M := M) 1 0 x (metricComparisonDiffEndo (I := I) g₀ g₁ x))
          (coframeS (I := I) (M := M) g₀ x 1 e K))
        (fun k => e (J k)) := by
    unfold fiberNormSqComponent coframeS
    rfl
  rw [hcomp, slotInsertEndoFib_apply_eval]
  rw [show (coframeS (I := I) (M := M) g₀ x 1 e K).toModel
        (Function.update (fun k => e (J k)) 0
          (metricComparisonDiffEndo (I := I) g₀ g₁ x ((fun k => e (J k)) 0)))
      = coframeS (I := I) (M := M) g₀ x 1 e K
        (Function.update (fun k => e (J k)) 0
          (metricComparisonDiffEndo (I := I) g₀ g₁ x (e (J 0)))) from rfl]
  rw [coframeS_apply, Fin.prod_univ_one, Function.update_self]

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma rfns_slotInsertE_zero_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (_hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1)
    (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (h : ∀ y v w, g₁.inner y v w =
      g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
    {δ : ℝ} (hδ : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
    (hbound : metricCauchySchwarzBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x
        ((endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (gInvDiffRaisedEndoField (I := I) g₀ g₁)).toSection x) ≤
      ((Module.finrank ℝ E : ℝ)) ^ 2 * (1 / (1 - δ₀)) ^ 2 := by
  classical
  have hceil0 : 0 < 1 - δ₀ := by linarith
  have hcoeff : 0 < 1 - δ := by linarith
  obtain ⟨n, e, bse, hn, hbse, horth, hpars, hrepr_v, hsum⟩ :=
    tangent_orthonormalBasis_witness (I := I) (M := M) g₀ x
  have hnE : n = Module.finrank ℝ E := by rw [hn]; rfl
  have hg₁ : ∀ (b : M) (u₁ u₂ : TangentSpace I b),
      g₁.inner b u₁ u₂ = g₀.inner b u₁ u₂ + ccTensorBilinSymm (I := I) g₀ T b u₁ u₂ :=
    fun b u₁ u₂ => h b u₁ u₂
  rw [riemannianFiberNormSq_eq_sum_componentSq_of_basis (I := I) (M := M) g₀ 1 1 x
    ((endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
      (gInvDiffRaisedEndoField (I := I) g₀ g₁)).toSection x) e bse hnE hbse horth]
  have hinv₀_nn : 0 ≤ 1 / (1 - δ₀) := by positivity
  have hratio : δ / (1 - δ) ≤ 1 / (1 - δ₀) := by
    rw [div_le_div_iff₀ hcoeff hceil0]
    nlinarith [mul_le_mul_of_nonneg_left hδ hδ0, sq_nonneg (1 - δ)]
  have heach : ∀ (K J : Fin 1 → Fin n),
      (fiberNormSqComponent (I := I) (M := M) g₀ x 1 1
        ((endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (gInvDiffRaisedEndoField (I := I) g₀ g₁)).toSection x) n e K J) ^ 2 ≤
        (1 / (1 - δ₀)) ^ 2 := by
    intro K J
    rw [fiberNormSqComponent_slotInsertE (I := I) (M := M) g₀ g₁ x e K J]
    set u : TangentSpace I x := metricComparisonDiffEndo (I := I) g₀ g₁ x (e (J 0)) with hu_def
    have hcs := metric_inner_cauchy_schwarz_sq (I := I) (M := M) g₀ x (e (K 0)) u
    have hKK : g₀.inner x (e (K 0)) (e (K 0)) = 1 := by rw [horth (K 0) (K 0)]; simp
    rw [hKK, one_mul] at hcs
    have hsfib := sqrt_inner_gInvDiffRaisedEndo_le (I := I) g₀ g₁
      (ccTensorBilinSymm (I := I) g₀ T) hg₁ (by linarith : δ < 1) hδ0 hbound x (e (J 0))
    have hJJ : g₀.inner x (e (J 0)) (e (J 0)) = 1 := by rw [horth (J 0) (J 0)]; simp
    rw [hJJ, Real.sqrt_one, mul_one] at hsfib
    rw [← hu_def] at hsfib
    have huu_nn : 0 ≤ g₀.inner x u u := metric_inner_self_nonneg (I := I) (M := M) g₀ x u
    have hsqrt_eq : Real.sqrt (g₀.inner x u u) ^ 2 = g₀.inner x u u :=
      Real.sq_sqrt huu_nn
    have hsqrt_nn : 0 ≤ Real.sqrt (g₀.inner x u u) := Real.sqrt_nonneg _
    have huu_le : g₀.inner x u u ≤ (1 / (1 - δ₀)) ^ 2 := by
      rw [← hsqrt_eq]
      have hsfib' : Real.sqrt (g₀.inner x u u) ≤ 1 / (1 - δ₀) := le_trans hsfib hratio
      have := mul_self_le_mul_self hsqrt_nn hsfib'
      nlinarith [this, hsfib', hinv₀_nn]
    calc (g₀.inner x (e (K 0)) u) ^ 2
        ≤ g₀.inner x u u := hcs
      _ ≤ (1 / (1 - δ₀)) ^ 2 := huu_le
  calc ∑ K : Fin 1 → Fin n, ∑ J : Fin 1 → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g₀ x 1 1
          ((endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
            (gInvDiffRaisedEndoField (I := I) g₀ g₁)).toSection x) n e K J) ^ 2
      ≤ ∑ K : Fin 1 → Fin n, ∑ J : Fin 1 → Fin n, (1 / (1 - δ₀)) ^ 2 :=
        Finset.sum_le_sum (fun K _ => Finset.sum_le_sum (fun J _ => heach K J))
    _ = (Fintype.card (Fin 1 → Fin n) : ℝ) * (Fintype.card (Fin 1 → Fin n) : ℝ) *
        (1 / (1 - δ₀)) ^ 2 := by
        rw [Finset.sum_const, Finset.sum_const]
        simp only [Finset.card_univ, nsmul_eq_mul]
        ring
    _ = ((Module.finrank ℝ E : ℝ)) ^ 2 * (1 / (1 - δ₀)) ^ 2 := by
        simp only [Fintype.card_fun, Fintype.card_fin, pow_one]
        rw [← hnE]
        ring

private theorem rfns_iteratedCovGrad_slotInsertEndoCc_zero_gInvDiffRaisedEndoField_convolution_recursion
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ (A : ℝ) (B : ℕ → ℝ), 0 ≤ A ∧ (∀ m, 0 ≤ B m) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ y v w, g₁.inner y v w =
          g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (x : M),
        (riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + 0) x
            ((iteratedCovGrad (I := I) g₀ 1 1 0
              (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
                (fullRaisedEndoField (I := I) (M := M) g₀ g₁))).toSection x) ≤ A) ∧
        (∀ m : ℕ,
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + (m + 1)) x
              ((iteratedCovGrad (I := I) g₀ 1 1 (m + 1)
                (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
                  (fullRaisedEndoField (I := I) (M := M) g₀ g₁))).toSection x) ≤
            B m * ∑ k ∈ Finset.range (m + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + ((m - k) + 1)) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 ((m - k) + 1) T).toSection x) *
                riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + k) x
                  ((iteratedCovGrad (I := I) g₀ 1 1 k
                    (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
                      (fullRaisedEndoField (I := I) (M := M) g₀ g₁))).toSection x)) := by
  refine ⟨(Module.finrank ℝ E : ℝ) ^ 2 * (1 / (1 - δ₀)) ^ 2,
    fun m => (Module.finrank ℝ E : ℝ) ^ (m + 1) *
      ((Module.finrank ℝ E : ℝ) ^ 2 * (1 / (1 - δ₀)) ^ 2) *
      ((m : ℝ) + 1) * 4 ^ (m + 1) * (Module.finrank ℝ E : ℝ) ^ m,
    by positivity, fun m => by positivity, ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound x
  have hδ₀0 : 0 ≤ δ₀ := le_trans hδ0 hδ_le
  refine ⟨?_, ?_⟩
  · rw [iteratedCovGrad_zero]
    exact rfns_slotInsertFULL_zero_le (I := I) (M := M) g₀ hδ₀0 hδ₀ g₁ T htie hδ_le hδ0 hbound x
  · intro m
    have hbase : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + 0) x
        ((iteratedCovGrad (I := I) g₀ 1 1 0
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
            (fullRaisedEndoField (I := I) (M := M) g₀ g₁))).toSection x) ≤
        (Module.finrank ℝ E : ℝ) ^ 2 * (1 / (1 - δ₀)) ^ 2 := by
      rw [iteratedCovGrad_zero]
      exact rfns_slotInsertFULL_zero_le (I := I) (M := M) g₀ hδ₀0 hδ₀ g₁ T htie hδ_le hδ0 hbound x
    have hgrid := rfns_iteratedCovGrad_SI_F_leibniz_grid_bound (I := I) (M := M) g₀ g₁ T htie m x
    refine le_trans hgrid ?_
    set SF0 : ℝ := riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + 0) x
      ((iteratedCovGrad (I := I) g₀ 1 1 0
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (fullRaisedEndoField (I := I) (M := M) g₀ g₁))).toSection x) with hSF0
    have hSF0_nn : 0 ≤ SF0 := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (1 + 0) x _
    set S : ℝ := ∑ k ∈ Finset.range (m + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + ((m - k) + 1)) x
          ((iteratedCovGrad (I := I) g₀ 0 2 ((m - k) + 1) T).toSection x) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + k) x
          ((iteratedCovGrad (I := I) g₀ 1 1 k
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
              (fullRaisedEndoField (I := I) (M := M) g₀ g₁))).toSection x) with hSdef
    have hsumbnd : (m + 1 : ℝ) * ∑ k ∈ Finset.range (m + 1),
          (4 ^ (m + 1) * (Module.finrank ℝ E : ℝ) ^ k *
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + ((m - k) + 1)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 ((m - k) + 1) T).toSection x)) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + k) x
              ((iteratedCovGrad (I := I) g₀ 1 1 k
                (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
                  (fullRaisedEndoField (I := I) (M := M) g₀ g₁))).toSection x)
        ≤ ((m : ℝ) + 1) * (4 ^ (m + 1) * (Module.finrank ℝ E : ℝ) ^ m * S) := by
      rw [hSdef]
      have hcast : (m + 1 : ℝ) = (m : ℝ) + 1 := by norm_num
      rw [hcast]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro k hk
      have hkm : k ≤ m := by rw [Finset.mem_range] at hk; omega
      have hTk_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + ((m - k) + 1)) x
          ((iteratedCovGrad (I := I) g₀ 0 2 ((m - k) + 1) T).toSection x) :=
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + ((m - k) + 1)) x _
      have hSFk_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + k) x
          ((iteratedCovGrad (I := I) g₀ 1 1 k
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
              (fullRaisedEndoField (I := I) (M := M) g₀ g₁))).toSection x) :=
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (1 + k) x _
      have hfk : (Module.finrank ℝ E : ℝ) ^ k ≤ (Module.finrank ℝ E : ℝ) ^ m :=
        pow_le_pow_right₀ (by
          have : Module.finrank ℝ E ≠ 0 := NeZero.ne _
          exact_mod_cast Nat.one_le_iff_ne_zero.mpr this) hkm
      calc (4 ^ (m + 1) * (Module.finrank ℝ E : ℝ) ^ k *
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + ((m - k) + 1)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 ((m - k) + 1) T).toSection x)) *
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + k) x
                ((iteratedCovGrad (I := I) g₀ 1 1 k
                  (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
                    (fullRaisedEndoField (I := I) (M := M) g₀ g₁))).toSection x)
          ≤ (4 ^ (m + 1) * (Module.finrank ℝ E : ℝ) ^ m *
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + ((m - k) + 1)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 ((m - k) + 1) T).toSection x)) *
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + k) x
                ((iteratedCovGrad (I := I) g₀ 1 1 k
                  (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
                    (fullRaisedEndoField (I := I) (M := M) g₀ g₁))).toSection x) := by
            apply mul_le_mul_of_nonneg_right _ hSFk_nn
            apply mul_le_mul_of_nonneg_right _ hTk_nn
            exact mul_le_mul_of_nonneg_left hfk (by positivity)
        _ = 4 ^ (m + 1) * (Module.finrank ℝ E : ℝ) ^ m *
              (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + ((m - k) + 1)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 ((m - k) + 1) T).toSection x) *
                riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + k) x
                  ((iteratedCovGrad (I := I) g₀ 1 1 k
                    (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
                      (fullRaisedEndoField (I := I) (M := M) g₀ g₁))).toSection x)) := by
            ring
    have hStep : (Module.finrank ℝ E : ℝ) ^ (m + 1) * SF0 *
          ((m + 1 : ℝ) * ∑ k ∈ Finset.range (m + 1),
            (4 ^ (m + 1) * (Module.finrank ℝ E : ℝ) ^ k *
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + ((m - k) + 1)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 ((m - k) + 1) T).toSection x)) *
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + k) x
                ((iteratedCovGrad (I := I) g₀ 1 1 k
                  (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
                    (fullRaisedEndoField (I := I) (M := M) g₀ g₁))).toSection x))
        ≤ (Module.finrank ℝ E : ℝ) ^ (m + 1) *
            ((Module.finrank ℝ E : ℝ) ^ 2 * (1 / (1 - δ₀)) ^ 2) *
            ((m : ℝ) + 1) * 4 ^ (m + 1) * (Module.finrank ℝ E : ℝ) ^ m * S := by
      have hSnn : 0 ≤ S := by
        rw [hSdef]
        apply Finset.sum_nonneg
        intro k _
        exact mul_nonneg
          (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + ((m - k) + 1)) x _)
          (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (1 + k) x _)
      have h1 : (Module.finrank ℝ E : ℝ) ^ (m + 1) * SF0 *
            ((m + 1 : ℝ) * ∑ k ∈ Finset.range (m + 1),
              (4 ^ (m + 1) * (Module.finrank ℝ E : ℝ) ^ k *
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + ((m - k) + 1)) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 ((m - k) + 1) T).toSection x)) *
                riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + k) x
                  ((iteratedCovGrad (I := I) g₀ 1 1 k
                    (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
                      (fullRaisedEndoField (I := I) (M := M) g₀ g₁))).toSection x))
          ≤ (Module.finrank ℝ E : ℝ) ^ (m + 1) *
              ((Module.finrank ℝ E : ℝ) ^ 2 * (1 / (1 - δ₀)) ^ 2) *
              (((m : ℝ) + 1) * (4 ^ (m + 1) * (Module.finrank ℝ E : ℝ) ^ m * S)) := by
        have hle1 : (Module.finrank ℝ E : ℝ) ^ (m + 1) * SF0 ≤
            (Module.finrank ℝ E : ℝ) ^ (m + 1) *
              ((Module.finrank ℝ E : ℝ) ^ 2 * (1 / (1 - δ₀)) ^ 2) :=
          mul_le_mul_of_nonneg_left (by rw [hSF0] at hbase ⊢; exact hbase) (by positivity)
        refine mul_le_mul hle1 hsumbnd ?_ (by positivity)
        apply mul_nonneg (by positivity)
        apply Finset.sum_nonneg
        intro k _
        refine mul_nonneg (mul_nonneg (by positivity)
          (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + ((m - k) + 1)) x _)) ?_
        exact riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (1 + k) x _
      refine le_trans h1 (le_of_eq ?_)
      ring
    refine le_trans hStep (le_of_eq ?_)
    rw [hSdef]

theorem riemannianFiberNormSq_iteratedCovGrad_slotInsertEndoCc_zero_gInvDiffRaisedEndoField_diagonalProductGrid_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ y v w, g₁.inner y v w =
          g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
            ((iteratedCovGrad (I := I) g₀ 1 1 i
              (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
                (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x) ≤
          C i * ∑ n ∈ Finset.range (i + 1),
            ∑ e ∈ Finset.Nat.antidiagonalTuple n i,
              ∏ m : Fin n,
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T).toSection x) := by
  obtain ⟨A, B, hA, hB, hrec⟩ :=
    rfns_iteratedCovGrad_slotInsertEndoCc_zero_gInvDiffRaisedEndoField_convolution_recursion
      (I := I) (M := M) g₀ hδ₀
  refine ⟨fun i => (DifferentialGeometry.Combinatorics.recGridCS A B i).1 +
      (Module.finrank ℝ E : ℝ) ^ 2 * (1 / (1 - δ₀)) ^ 2,
    fun i => add_nonneg (DifferentialGeometry.Combinatorics.recGridCS_nonneg A B hA hB i).1
      (by positivity), ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound i x
  obtain ⟨hbaseF, hstepF⟩ := hrec g₁ T htie hδ_le hδ0 hbound x
  have hδ₀0 : 0 ≤ δ₀ := le_trans hδ0 hδ_le
  have hD₀nn : 0 ≤ (Module.finrank ℝ E : ℝ) ^ 2 * (1 / (1 - δ₀)) ^ 2 := by positivity
  have hfullgrid := DifferentialGeometry.Combinatorics.antidiagonalTupleGrid_convolution_bound
    (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
      ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x))
    (fun j => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j) x _)
    (fun k => riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + k) x
      ((iteratedCovGrad (I := I) g₀ 1 1 k
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (fullRaisedEndoField (I := I) (M := M) g₀ g₁))).toSection x))
    A hA B hB hbaseF hstepF
  have hfg : fullRaisedEndoField (I := I) (M := M) g₁ g₁ =
      fullRaisedEndoField (I := I) (M := M) g₀ g₀ := by
    apply ContMDiffSection.ext
    intro y
    apply ContinuousLinearMap.ext
    intro v
    rw [fullRaisedEndoField_apply, fullRaisedEndoField_apply, gInvRaisedEndo_self,
      gInvRaisedEndo_self]
  have hid_eq : endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
        (fullRaisedEndoField (I := I) (M := M) g₁ g₁) =
      endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
        (fullRaisedEndoField (I := I) (M := M) g₀ g₀) := by
    rw [hfg]
  have hFULLeq : endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
        (fullRaisedEndoField (I := I) (M := M) g₀ g₁) =
      endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (gInvDiffRaisedEndoField (I := I) g₀ g₁) +
        endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (fullRaisedEndoField (I := I) (M := M) g₁ g₁) := by
    rw [← slotInsertEndoCc_add]
    congr 1
    exact fullRaisedEndoField_recovery_decomp (I := I) (M := M) g₁ g₀
  have hE0 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x
        ((endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (gInvDiffRaisedEndoField (I := I) g₀ g₁)).toSection x) ≤
      (Module.finrank ℝ E : ℝ) ^ 2 * (1 / (1 - δ₀)) ^ 2 :=
    rfns_slotInsertE_zero_le (I := I) (M := M) g₀ hδ₀0 hδ₀ g₁ T
      (fun y v w => htie y v w) hδ_le hδ0 hbound x
  rw [show (∑ n ∈ Finset.range (i + 1),
        ∑ e ∈ Finset.Nat.antidiagonalTuple n i,
          ∏ m : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T).toSection x)) =
      DifferentialGeometry.Combinatorics.antidiagonalTupleGrid
        (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x)) i from rfl]
  rcases i with _ | i'
  · rw [iteratedCovGrad_zero,
      DifferentialGeometry.Combinatorics.antidiagonalTupleGrid_zero, mul_one]
    refine le_trans hE0 ?_
    have hrc : 0 ≤ (DifferentialGeometry.Combinatorics.recGridCS A B 0).1 :=
      (DifferentialGeometry.Combinatorics.recGridCS_nonneg A B hA hB 0).1
    linarith
  · have hzero_id : iteratedCovGrad (I := I) g₀ 1 1 (i' + 1)
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (fullRaisedEndoField (I := I) (M := M) g₁ g₁)) = 0 := by
      rw [hid_eq]
      exact iteratedCovGrad_slotInsert_self_eq_zero (I := I) (M := M) g₀ i'
    have hbridge : iteratedCovGrad (I := I) g₀ 1 1 (i' + 1)
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
            (gInvDiffRaisedEndoField (I := I) g₀ g₁)) =
        iteratedCovGrad (I := I) g₀ 1 1 (i' + 1)
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
            (fullRaisedEndoField (I := I) (M := M) g₀ g₁)) := by
      rw [hFULLeq, iteratedCovGrad_add, hzero_id, add_zero]
    rw [hbridge]
    refine le_trans (hfullgrid (i' + 1)) ?_
    refine mul_le_mul_of_nonneg_right ?_
      (DifferentialGeometry.Combinatorics.antidiagonalTupleGrid_nonneg
        (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x))
        (fun j => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j) x _) (i' + 1))
    linarith

theorem rfns_iteratedCovGrad_slotInsertEndoCc_gInvDiffRaisedEndoField_diagonalProductGrid_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ y v w, g₁.inner y v w =
          g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
                (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x) ≤
          C i * ∑ n ∈ Finset.range (i + 1),
            ∑ e ∈ Finset.Nat.antidiagonalTuple n i,
              ∏ m : Fin n,
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T).toSection x) := by
  obtain ⟨C, hC, hbnd⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_slotInsertEndoCc_zero_gInvDiffRaisedEndoField_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  refine ⟨fun i => (Module.finrank ℝ E : ℝ) * C i,
    fun i => mul_nonneg (Nat.cast_nonneg _) (hC i), ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound i x
  have h2862 := rfns_iteratedCovGrad_slotInsertEndoCc_le_endo (E := E) (I := I) (M := M) g₀ 1
    (gInvDiffRaisedEndoField (I := I) g₀ g₁) i x
  rw [pow_one] at h2862
  refine le_trans h2862 ?_
  have hchild := hbnd g₁ T htie hδ_le hδ0 hbound i x
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left hchild (Nat.cast_nonneg _)

theorem riemannianFiberNormSq_iteratedCovGrad_gInvDiffSlotCoeff_diagonalProductGrid_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ y v w, g₁.inner y v w =
          g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x) ≤
          C i * ∑ n ∈ Finset.range (i + 1),
            ∑ e ∈ Finset.Nat.antidiagonalTuple n i,
              ∏ m : Fin n,
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T).toSection x) := by
  obtain ⟨C, hC, hbnd⟩ :=
    rfns_iteratedCovGrad_slotInsertEndoCc_gInvDiffRaisedEndoField_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  refine ⟨C, hC, fun g₁ T htie δ hδ_le hδ0 hbound i x => ?_⟩
  rw [gInvDiffSlotCoeff_eq_slotInsertEndoCc (E := E) (I := I) g₀ g₁]
  exact hbnd g₁ T htie hδ_le hδ0 hbound i x

end Connection
end Integral
end DifferentialGeometry

end
