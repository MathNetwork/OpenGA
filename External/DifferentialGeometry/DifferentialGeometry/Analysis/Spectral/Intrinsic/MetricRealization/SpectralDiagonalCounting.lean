import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.SpectralWeylCounting
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Smooth.EigenvectorSmoothToL2
import DifferentialGeometry.Analysis.Integration.Measure.Invariance
























































noncomputable section

set_option linter.style.setOption false
set_option maxHeartbeats 800000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral
namespace MetricRealization

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩
private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E



omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem smoothCcTensor_normSq_eq_integral
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g r s) :
    ‖S‖ ^ 2 =
      ∫ x, tensorInnerPointwise (I := I) (M := M) g r s x (S.toFun x) (S.toFun x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  rw [SmoothCcTensor.norm_def, tensorL2Norm_def,
    Real.sq_sqrt (tensorL2Inner_nonneg (I := I) (M := M) g r s S.toFun)]
  rfl




theorem eigenvectorSmooth_norm_eq_one
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s) :
    ‖eigenvectorSmooth (I := I) (M := M) g r s i‖ = 1 := by
  have h_class : (eigenvectorSmooth (I := I) (M := M) g r s i :
        TensorL2 r s g) =
      tensorResolventEigenbasisVec (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s) i :=
    eigenvectorSmooth_toL2 (I := I) (M := M) g r s i
  have h_one := (tensorResolventEigenbasisVec_orthonormal (I := I) (M := M)
    (g := g) (r := r) (s := s)
    (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)).norm_eq_one i
  have h_coe : ‖(eigenvectorSmooth (I := I) (M := M) g r s i :
        TensorL2 r s g)‖ =
      ‖eigenvectorSmooth (I := I) (M := M) g r s i‖ :=
    UniformSpace.Completion.norm_coe _
  rw [h_class, h_one] at h_coe
  exact h_coe.symm




theorem eigenvectorSmooth_integral_normSq_eq_one
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s) :
    ∫ x, tensorInnerPointwise (I := I) (M := M) g r s x
        ((eigenvectorSmooth (I := I) (M := M) g r s i).toFun x)
        ((eigenvectorSmooth (I := I) (M := M) g r s i).toFun x)
      ∂(riemannianVolumeMeasure (I := I) (M := M) g) = 1 := by
  have h := smoothCcTensor_normSq_eq_integral (I := I) (M := M) g r s
    (eigenvectorSmooth (I := I) (M := M) g r s i)
  rw [eigenvectorSmooth_norm_eq_one (I := I) (M := M) g r s i] at h
  rw [← h]; norm_num





def diagonalKernel (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : Finset (TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s)) (x : M) : ℝ :=
  ∑ i ∈ F,
    tensorInnerPointwise (I := I) (M := M) g r s x
      ((eigenvectorSmooth (I := I) (M := M) g r s i).toFun x)
      ((eigenvectorSmooth (I := I) (M := M) g r s i).toFun x)



private lemma diagonalKernel_summand_integrable
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s) :
    Integrable
      (fun x => tensorInnerPointwise (I := I) (M := M) g r s x
        ((eigenvectorSmooth (I := I) (M := M) g r s i).toFun x)
        ((eigenvectorSmooth (I := I) (M := M) g r s i).toFun x))
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
  (SmoothCcTensor.memL2_toFun (I := I) (M := M)
    (eigenvectorSmooth (I := I) (M := M) g r s i)).integrable_inner_self






theorem finsetCard_eq_integral_diagonalKernel
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : Finset (TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s)) :
    (F.card : ℝ) =
      ∫ x, diagonalKernel (I := I) (M := M) g r s F x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  simp only [diagonalKernel]
  rw [MeasureTheory.integral_finset_sum F
    (fun i _ => diagonalKernel_summand_integrable (I := I) (M := M) g r s i)]
  rw [Finset.sum_congr rfl
    (fun i _ => eigenvectorSmooth_integral_normSq_eq_one (I := I) (M := M) g r s i)]
  simp



private lemma diagonalKernel_integrable
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : Finset (TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s)) :
    Integrable (diagonalKernel (I := I) (M := M) g r s F)
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
  have h : diagonalKernel (I := I) (M := M) g r s F =
      fun x => ∑ i ∈ F,
        tensorInnerPointwise (I := I) (M := M) g r s x
          ((eigenvectorSmooth (I := I) (M := M) g r s i).toFun x)
          ((eigenvectorSmooth (I := I) (M := M) g r s i).toFun x) := rfl
  rw [h]
  exact MeasureTheory.integrable_finset_sum F
    (fun i _ => diagonalKernel_summand_integrable (I := I) (M := M) g r s i)























theorem eigenvalueCountingBound_of_pointwiseDiagonalKernelBound
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (q : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (count : ℝ → Finset (TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s))
    (hmem : ∀ (Λ : ℝ) (i : TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s),
      1 + TensorEigenIdx.lambda (I := I) (M := M) i < Λ → i ∈ count Λ)
    (hkernel : ∀ (Λ : ℝ) (x : M),
      diagonalKernel (I := I) (M := M) g r s (count Λ) x ≤ B * Λ ^ q) :
    EigenvalueCountingBound (I := I) (M := M) g r s := by
  haveI hfin : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  set vol : ℝ :=
    (riemannianVolumeMeasure (I := I) (M := M) g).real Set.univ with hvol_def
  have hvol_nonneg : 0 ≤ vol := by rw [hvol_def]; exact MeasureTheory.measureReal_nonneg
  refine ⟨q, B * vol, mul_nonneg hB hvol_nonneg, count, hmem, ?_⟩
  intro Λ
  rw [finsetCard_eq_integral_diagonalKernel (I := I) (M := M) g r s (count Λ)]
  have h_int_mono :
      ∫ x, diagonalKernel (I := I) (M := M) g r s (count Λ) x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) ≤
        ∫ _x, B * Λ ^ q ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
    MeasureTheory.integral_mono
      (diagonalKernel_integrable (I := I) (M := M) g r s (count Λ))
      (MeasureTheory.integrable_const _)
      (fun x => hkernel Λ x)
  refine le_trans h_int_mono (le_of_eq ?_)
  rw [MeasureTheory.integral_const, smul_eq_mul, ← hvol_def]
  ring

end MetricRealization
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
