import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.IteratedCovGradHsJetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Regularity.EigenvectorTensorHsToWtwokTwo









noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E



theorem cc_iter_coeff
    (g : SmoothRiemannianMetric I M) (s n : ℕ)
    (U : SmoothCcTensor g 0 s)
    (i : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
      (I := I) (M := M) g 0 s) :
    tensorL2Coeff (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 s)
        (SmoothCcTensor.toL2
          (oneMinusConnLapSmoothIter (I := I) g 0 s n U)) i =
      (1 + DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
          (I := I) (M := M) i) ^ n *
        tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 s)
          (SmoothCcTensor.toL2 U) i := by
  induction n with
  | zero => simp only [oneMinusConnLapSmoothIter_zero, pow_zero, one_mul]
  | succ n ih =>
      rw [oneMinusConnLapSmoothIter_succ,
        oneMinus_coeff (I := I) (M := M) g s
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 s)
          (oneMinusConnLapSmoothIter (I := I) g 0 s n U) i,
        ih, pow_succ]
      ring

omit [BoundarylessManifold I M] in


theorem cc_l2_pair_tsum
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (A B : SmoothCcTensor g 0 s) :
    tensorL2Inner (I := I) (M := M) g 0 s A.toFun B.toFun =
      ∑' i : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g 0 s,
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 s)
            (SmoothCcTensor.toL2 A) i *
          tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 s)
            (SmoothCcTensor.toL2 B) i := by
  classical
  let hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 s
  let b := tensorResolventHilbertEigenbasisSigma (I := I) (M := M) hc
  have hinner : tensorL2Inner (I := I) (M := M) g 0 s A.toFun B.toFun =
      (⟪SmoothCcTensor.toL2 A, SmoothCcTensor.toL2 B⟫_ℝ : ℝ) := by
    rw [DifferentialGeometry.Integral.L2.SmoothCcTensor.inner_toL2
      (I := I) (M := M) A B]
    exact (SmoothCcTensor.inner_def (I := I) (M := M) A B).symm
  rw [hinner]
  have hparseval := b.tsum_inner_mul_inner
    (SmoothCcTensor.toL2 A) (SmoothCcTensor.toL2 B)
  rw [← hparseval]
  refine tsum_congr (fun i => ?_)
  rw [tensorL2Coeff_eq_inner (I := I) (M := M) hc,
    tensorL2Coeff_eq_inner (I := I) (M := M) hc]
  rw [show (⟪SmoothCcTensor.toL2 A, b i⟫_ℝ : ℝ) =
      ⟪b i, SmoothCcTensor.toL2 A⟫_ℝ from real_inner_comm _ _]



theorem cc_pair_tsum
    (g : SmoothRiemannianMetric I M) (s n : ℕ)
    (U A : SmoothCcTensor g 0 s) :
    ∑' i : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
        (I := I) (M := M) g 0 s,
        tensorSobolevWeight (I := I) (M := M) i (n : ℝ) *
          (tensorL2Coeff (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 s)
              (SmoothCcTensor.toL2 U) i *
            tensorL2Coeff (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 s)
              (SmoothCcTensor.toL2 A) i) =
      tensorL2Inner (I := I) (M := M) g 0 s
        (oneMinusConnLapSmoothIter (I := I) g 0 s n U).toFun A.toFun := by
  classical
  rw [cc_l2_pair_tsum (I := I) (M := M) g s
    (oneMinusConnLapSmoothIter (I := I) g 0 s n U) A]
  refine tsum_congr (fun i => ?_)
  rw [cc_iter_coeff (I := I) (M := M) g s n U i]
  have hweight :
      tensorSobolevWeight (I := I) (M := M) i (n : ℝ) =
        (1 + DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
          (I := I) (M := M) i) ^ n := by
    unfold tensorSobolevWeight
    rw [Real.rpow_natCast]
  rw [hweight]
  ring



theorem finite_repr_norm
    (g : SmoothRiemannianMetric I M) (s m : ℕ)
    (T : tensorHs (I := I) (M := M) g 0 s 0)
    (hT : (Function.support T.coeff).Finite) :
    ‖ccTensorToHs (I := I) (M := M) g s (m : ℝ)
        (tensorHsSmoothRepr (I := I) (M := M) T hT)‖ ^ 2 =
      ∑ i ∈ hT.toFinset,
        tensorSobolevWeight (I := I) (M := M) i (m : ℝ) *
          (T.coeff i) ^ 2 := by
  classical
  let U : SmoothCcTensor g 0 s :=
    tensorHsSmoothRepr (I := I) (M := M) T hT
  have hrepr
      (i : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
        (I := I) (M := M) g 0 s) :
      (ccTensorToHs (I := I) (M := M) g s (m : ℝ) U).coeff i =
        T.coeff i := by
    rw [ccTensorToHs_coeff, SmoothCcTensor.toL2_apply]
    dsimp only [U]
    rw [tensorHsSmoothRepr_toL2 (I := I) (M := M) (le_refl (0 : ℝ)) T hT,
      tensorHsToL2_tensorL2Coeff (I := I) (M := M) (le_refl (0 : ℝ))]
  rw [tensorHs.norm_sq_eq_tsum]
  change
    (∑' i,
      tensorSobolevWeight (I := I) (M := M) i (m : ℝ) *
        ((ccTensorToHs (I := I) (M := M) g s (m : ℝ) U).coeff i) ^ 2) = _
  calc
    _ = ∑' i,
        tensorSobolevWeight (I := I) (M := M) i (m : ℝ) *
          (T.coeff i) ^ 2 := by
      apply tsum_congr
      intro i
      rw [hrepr i]
    _ = _ := by
      rw [tsum_eq_sum (s := hT.toFinset)]
      intro i hi
      have hcoeff : T.coeff i = 0 := by
        by_contra hne
        exact hi (hT.mem_toFinset.mpr (Function.mem_support.mpr hne))
      norm_num [hcoeff]




theorem finite_cc_pair
    (g : SmoothRiemannianMetric I M) (s n : ℕ)
    (T : tensorHs (I := I) (M := M) g 0 s 0)
    (hT : (Function.support T.coeff).Finite)
    (A : SmoothCcTensor g 0 s) :
    ∑ i ∈ hT.toFinset,
        tensorSobolevWeight (I := I) (M := M) i (n : ℝ) *
          (T.coeff i *
            tensorL2Coeff (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 s)
              (SmoothCcTensor.toL2 A) i) =
      tensorL2Inner (I := I) (M := M) g 0 s
        (oneMinusConnLapSmoothIter (I := I) g 0 s n
          (tensorHsSmoothRepr (I := I) (M := M) T hT)).toFun A.toFun := by
  classical
  let hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 s
  have hrepr
      (i : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
        (I := I) (M := M) g 0 s) :
      tensorL2Coeff (I := I) (M := M) hc
          (SmoothCcTensor.toL2
            (tensorHsSmoothRepr (I := I) (M := M) T hT)) i = T.coeff i := by
    rw [SmoothCcTensor.toL2_apply,
      tensorHsSmoothRepr_toL2 (I := I) (M := M) (le_refl (0 : ℝ)) T hT,
      tensorHsToL2_tensorL2Coeff (I := I) (M := M) (le_refl (0 : ℝ))]
  have hzero : ∀ i ∉ hT.toFinset,
      tensorSobolevWeight (I := I) (M := M) i (n : ℝ) *
          (T.coeff i * tensorL2Coeff (I := I) (M := M) hc
            (SmoothCcTensor.toL2 A) i) = 0 := by
    intro i hi
    have hcoeff : T.coeff i = 0 := by
      by_contra hne
      exact hi (hT.mem_toFinset.mpr (Function.mem_support.mpr hne))
    rw [hcoeff, zero_mul, mul_zero]
  calc
    ∑ i ∈ hT.toFinset,
          tensorSobolevWeight (I := I) (M := M) i (n : ℝ) *
            (T.coeff i * tensorL2Coeff (I := I) (M := M) hc
              (SmoothCcTensor.toL2 A) i) =
        ∑' i,
          tensorSobolevWeight (I := I) (M := M) i (n : ℝ) *
            (T.coeff i * tensorL2Coeff (I := I) (M := M) hc
              (SmoothCcTensor.toL2 A) i) :=
      (tsum_eq_sum hzero).symm
    _ = tensorL2Inner (I := I) (M := M) g 0 s
          (oneMinusConnLapSmoothIter (I := I) g 0 s n
            (tensorHsSmoothRepr (I := I) (M := M) T hT)).toFun A.toFun := by
      simpa only [hrepr] using
        (cc_pair_tsum (I := I) (M := M) g s n
          (tensorHsSmoothRepr (I := I) (M := M) T hT) A)

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
