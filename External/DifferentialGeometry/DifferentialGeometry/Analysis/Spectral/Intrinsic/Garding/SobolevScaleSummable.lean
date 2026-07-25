import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Defs
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Inclusion
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.TensorConnLapGreenDivergenceIdentityAnySection
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Smooth.EigenvectorSmoothToL2


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

noncomputable def oneMinusConnLapSmooth
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s) :
    SmoothCcTensor g r s :=
  T - rawTensorConnLapSmooth (I := I) g r s T

omit [CompactSpace M] [I.Boundaryless] in
@[simp] lemma oneMinusConnLapSmooth_toSection_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s)
    (x : M) :
    (oneMinusConnLapSmooth (I := I) g r s T).toSection x =
      T.toSection x -
        rawTensorConnLap (I := I) g r s (fun z : M => T.toSection z) x := by
  unfold oneMinusConnLapSmooth
  rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
    rawTensorConnLapSmooth_toSection_apply]

noncomputable def oneMinusConnLapSmoothIter
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ℕ → SmoothCcTensor g r s → SmoothCcTensor g r s
  | 0,     T => T
  | k + 1, T => oneMinusConnLapSmooth (I := I) g r s
                  (oneMinusConnLapSmoothIter g r s k T)

omit [CompactSpace M] [I.Boundaryless] in
@[simp] theorem oneMinusConnLapSmoothIter_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s) :
    oneMinusConnLapSmoothIter (I := I) g r s 0 T = T := rfl

omit [CompactSpace M] [I.Boundaryless] in
@[simp] theorem oneMinusConnLapSmoothIter_succ
    (g : SmoothRiemannianMetric I M) (r s k : ℕ) (T : SmoothCcTensor g r s) :
    oneMinusConnLapSmoothIter (I := I) g r s (k + 1) T =
      oneMinusConnLapSmooth (I := I) g r s
        (oneMinusConnLapSmoothIter (I := I) g r s k T) := rfl

theorem oneMinusConnLapSmooth_toL2_inner_eq_h1
    (g : SmoothRiemannianMetric I M) (T v : SmoothCcTensor g 0 2) :
    ⟪((oneMinusConnLapSmooth (I := I) g 0 2 T : SmoothCcTensor g 0 2) :
          TensorL2 0 2 g),
        (v : TensorL2 0 2 g)⟫_ℝ =
      ⟪smoothToTensorH1Compl (I := I) (M := M) g 0 2 ⟨T⟩,
        smoothToTensorH1Compl (I := I) (M := M) g 0 2 ⟨v⟩⟫_ℝ := by
  have h_rhs :
      ⟪smoothToTensorH1Compl (I := I) (M := M) g 0 2 ⟨T⟩,
          smoothToTensorH1Compl (I := I) (M := M) g 0 2 ⟨v⟩⟫_ℝ =
        ⟪(T : TensorL2 0 2 g), (v : TensorL2 0 2 g)⟫_ℝ +
          ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g 0 2 T v x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    rw [smoothToTensorH1Compl_apply, smoothToTensorH1Compl_apply,
      UniformSpace.Completion.inner_coe, SmoothCcTensorH1.inner_def,
      tensorH1Inner_def]
    rw [show tensorL2Inner (I := I) (M := M) g 0 2
            (⟨T⟩ : SmoothCcTensorH1 g 0 2).toCcTensor.toFun
            (⟨v⟩ : SmoothCcTensorH1 g 0 2).toCcTensor.toFun =
          ⟪(T : TensorL2 0 2 g), (v : TensorL2 0 2 g)⟫_ℝ by
        rw [UniformSpace.Completion.inner_coe]
        exact (SmoothCcTensor.inner_def _ _).symm]
  rw [h_rhs]
  have h_dir :
      ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g 0 2 T v x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        tensorL2Inner (I := I) (M := M) g 0 (2 + 1)
          (covGrad (I := I) (M := M) g 0 2 T).toFun
          (covGrad (I := I) (M := M) g 0 2 v).toFun :=
    (tensorL2Inner_covGrad_eq_integral_tensorCovDerivPointwiseInner
      (I := I) (M := M) g 0 2 T v).symm
  have h_green :
      tensorL2Inner (I := I) (M := M) g 0 (2 + 1)
          (covGrad (I := I) (M := M) g 0 2 T).toFun
          (covGrad (I := I) (M := M) g 0 2 v).toFun =
        - tensorL2Inner (I := I) (M := M) g 0 2
            (rawTensorConnLapSmooth (I := I) g 0 2 T).toFun v.toFun :=
    tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLap_two
      (I := I) (M := M) g T v
  have h_lhs :
      ⟪((oneMinusConnLapSmooth (I := I) g 0 2 T : SmoothCcTensor g 0 2) :
            TensorL2 0 2 g),
          (v : TensorL2 0 2 g)⟫_ℝ =
        tensorL2Inner (I := I) (M := M) g 0 2
            (oneMinusConnLapSmooth (I := I) g 0 2 T).toFun v.toFun := by
    rw [UniformSpace.Completion.inner_coe]
    exact SmoothCcTensor.inner_def _ _
  have h_l2_Tv :
      ⟪(T : TensorL2 0 2 g), (v : TensorL2 0 2 g)⟫_ℝ =
        tensorL2Inner (I := I) (M := M) g 0 2 T.toFun v.toFun := by
    rw [UniformSpace.Completion.inner_coe]
    exact SmoothCcTensor.inner_def _ _
  have h_split :
      tensorL2Inner (I := I) (M := M) g 0 2
          (oneMinusConnLapSmooth (I := I) g 0 2 T).toFun v.toFun =
        tensorL2Inner (I := I) (M := M) g 0 2 T.toFun v.toFun -
          tensorL2Inner (I := I) (M := M) g 0 2
            (rawTensorConnLapSmooth (I := I) g 0 2 T).toFun v.toFun := by
    have h_coe :
        ⟪((oneMinusConnLapSmooth (I := I) g 0 2 T : SmoothCcTensor g 0 2) :
              TensorL2 0 2 g),
            (v : TensorL2 0 2 g)⟫_ℝ =
          ⟪(T : TensorL2 0 2 g), (v : TensorL2 0 2 g)⟫_ℝ -
            ⟪((rawTensorConnLapSmooth (I := I) g 0 2 T : SmoothCcTensor g 0 2) :
                TensorL2 0 2 g),
              (v : TensorL2 0 2 g)⟫_ℝ := by
      rw [show (oneMinusConnLapSmooth (I := I) g 0 2 T : SmoothCcTensor g 0 2) =
            T - rawTensorConnLapSmooth (I := I) g 0 2 T from rfl,
        UniformSpace.Completion.coe_sub, inner_sub_left]
    rw [← h_lhs, h_coe]
    rw [show ⟪(T : TensorL2 0 2 g), (v : TensorL2 0 2 g)⟫_ℝ =
          tensorL2Inner (I := I) (M := M) g 0 2 T.toFun v.toFun by
        rw [UniformSpace.Completion.inner_coe]; exact SmoothCcTensor.inner_def _ _]
    rw [show ⟪((rawTensorConnLapSmooth (I := I) g 0 2 T : SmoothCcTensor g 0 2) :
            TensorL2 0 2 g), (v : TensorL2 0 2 g)⟫_ℝ =
          tensorL2Inner (I := I) (M := M) g 0 2
            (rawTensorConnLapSmooth (I := I) g 0 2 T).toFun v.toFun by
        rw [UniformSpace.Completion.inner_coe]; exact SmoothCcTensor.inner_def _ _]
  rw [h_lhs, h_split, h_l2_Tv, h_dir, h_green]
  ring

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorParseval_l2Coeff_ofCompact_sq
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (u : TensorL2 r s g) :
    ∑' i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s,
        (tensorL2Coeff (I := I) (M := M) h_compact u i) ^ 2 =
      ‖u‖ ^ 2 := by
  rw [tensorParseval_norm_sq (I := I) (M := M) h_compact u]
  refine tsum_congr (fun i => ?_)
  rw [tensorL2Coeff_eq_inner (I := I) (M := M) h_compact u i,
    Real.norm_eq_abs, sq_abs]

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorL2Coeff_ofCompact_summable_sq'
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (u : TensorL2 r s g) :
    Summable (fun i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s =>
      (tensorL2Coeff (I := I) (M := M) h_compact u i) ^ 2) :=
  tensorL2Coeff_summable_sq (I := I) (M := M) h_compact u

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem summable_tensorSobolevWeight_of_even
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (c : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s → ℝ)
    {a : ℝ} {k : ℕ} (hak : a ≤ (2 * k : ℕ))
    (h2k : Summable (fun i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s =>
      tensorSobolevWeight (I := I) (M := M) i (2 * k : ℕ) * (c i) ^ 2)) :
    Summable (fun i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s =>
      tensorSobolevWeight (I := I) (M := M) i a * (c i) ^ 2) := by
  refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) h2k
  · have hw : 0 ≤ tensorSobolevWeight (I := I) (M := M) i a :=
      tensorSobolevWeight_nonneg (I := I) (M := M) i a
    positivity
  · have hmono :
        tensorSobolevWeight (I := I) (M := M) i a ≤
          tensorSobolevWeight (I := I) (M := M) i (2 * k : ℕ) :=
      tensorSobolevWeight_mono (I := I) (M := M) i hak
    exact mul_le_mul_of_nonneg_right hmono (sq_nonneg _)

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
