import DifferentialGeometry.Analysis.Parabolic.AbstractSemigroup.AbstractSpectralSemigroupContinuity
import DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.Semigroup
import DifferentialGeometry.Analysis.Spectral.Intrinsic.CompactSAResolventIntrinsic

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private noncomputable def intrinsicEigenbasis
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    HilbertBasis (TensorEigenIdx (I := I) (M := M) g r s) ℝ (TensorL2 r s g) :=
  tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
    (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma intrinsic_lambda_nonneg (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      0 ≤ TensorEigenIdx.lambda (I := I) (M := M) i :=
  fun i => tensor_lambda_nonneg (I := I) (M := M) i

noncomputable def tensorHeatSemigroup
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (t : ℝ) :
    TensorL2 r s g →L[ℝ] TensorL2 r s g :=
  abstractSpectralSemigroup (intrinsicEigenbasis (I := I) (M := M) g r s)
    (intrinsic_lambda_nonneg (I := I) (M := M) g r s) t

theorem tensorHeatSemigroup_intrinsic_apply_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    tensorHeatSemigroup (I := I) (M := M) g r s 0 =
      ContinuousLinearMap.id ℝ (TensorL2 r s g) :=
  abstractSpectralSemigroup_apply_zero (intrinsicEigenbasis (I := I) (M := M) g r s)
    (intrinsic_lambda_nonneg (I := I) (M := M) g r s)

theorem tensorHeatSemigroup_intrinsic_apply_add
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {t s' : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s') :
    tensorHeatSemigroup (I := I) (M := M) g r s (t + s') =
      (tensorHeatSemigroup (I := I) (M := M) g r s t).comp
        (tensorHeatSemigroup (I := I) (M := M) g r s s') :=
  abstractSpectralSemigroup_apply_add (intrinsicEigenbasis (I := I) (M := M) g r s)
    (intrinsic_lambda_nonneg (I := I) (M := M) g r s) ht hs

theorem tensorHeatSemigroup_intrinsic_opNorm_le_one
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (t : ℝ) :
    ‖tensorHeatSemigroup (I := I) (M := M) g r s t‖ ≤ 1 :=
  abstractSpectralSemigroup_opNorm_le_one (intrinsicEigenbasis (I := I) (M := M) g r s)
    (intrinsic_lambda_nonneg (I := I) (M := M) g r s) t

theorem tensorHeatSemigroup_intrinsic_continuousOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : TensorL2 r s g) :
    ContinuousOn (fun t : ℝ =>
        tensorHeatSemigroup (I := I) (M := M) g r s t T)
      (Set.Ici (0 : ℝ)) :=
  abstractSpectralSemigroup_continuousOn (intrinsicEigenbasis (I := I) (M := M) g r s)
    (intrinsic_lambda_nonneg (I := I) (M := M) g r s) T

theorem tensorHeatSemigroup_intrinsic_inner_eigenbasis
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {t : ℝ} (ht : 0 ≤ t) (u₀ : TensorL2 r s g)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    ⟪tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s) i,
      tensorHeatSemigroup (I := I) (M := M) g r s t u₀⟫_ℝ =
      Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
        ⟪tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s) i,
          u₀⟫_ℝ := by
  classical
  set b := intrinsicEigenbasis (I := I) (M := M) g r s with hb_def
  change ⟪b i, tensorHeatSemigroup (I := I) (M := M) g r s t u₀⟫_ℝ =
    Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) * ⟪b i, u₀⟫_ℝ
  have h_apply :
      tensorHeatSemigroup (I := I) (M := M) g r s t u₀ =
        ∑' j, heatCoeff (TensorEigenIdx.lambda (I := I) (M := M)) t j •
          ⟪b j, u₀⟫_ℝ • b j := by
    unfold tensorHeatSemigroup
    rw [abstractSpectralSemigroup_apply_of_nonneg b
      (intrinsic_lambda_nonneg (I := I) (M := M) g r s) ht u₀]
  rw [h_apply]
  have h_summable :=
    summable_heatTerm b (intrinsic_lambda_nonneg (I := I) (M := M) g r s) ht u₀
  have h_hsum := h_summable.hasSum
  have h_inner_hsum := h_hsum.mapL (innerSL ℝ (b i))
  have h_orthonormal : Orthonormal ℝ b := b.orthonormal
  have h_inner_eq : ∀ j : TensorEigenIdx (I := I) (M := M) g r s,
      ⟪b i, b j⟫_ℝ = if j = i then (1 : ℝ) else 0 := by
    intro j
    rw [show ⟪b i, b j⟫_ℝ = ⟪b j, b i⟫_ℝ from real_inner_comm _ _]
    exact (orthonormal_iff_ite (𝕜 := ℝ) (v := b)).mp h_orthonormal j i
  have h_summand_eq : ∀ j : TensorEigenIdx (I := I) (M := M) g r s,
      (innerSL ℝ (b i))
          (heatCoeff (TensorEigenIdx.lambda (I := I) (M := M)) t j •
            ⟪b j, u₀⟫_ℝ • b j) =
        if j = i then
          heatCoeff (TensorEigenIdx.lambda (I := I) (M := M)) t j *
            ⟪b j, u₀⟫_ℝ
        else 0 := by
    intro j
    change ⟪b i,
        heatCoeff (TensorEigenIdx.lambda (I := I) (M := M)) t j •
          ⟪b j, u₀⟫_ℝ • b j⟫_ℝ = _
    rw [real_inner_smul_right, real_inner_smul_right, h_inner_eq]
    by_cases hji : j = i
    · subst hji; simp
    · simp [hji]
  have h_inner_hsum' : HasSum (fun j =>
      if j = i then
        heatCoeff (TensorEigenIdx.lambda (I := I) (M := M)) t j *
          ⟪b j, u₀⟫_ℝ
      else 0)
      ((innerSL ℝ (b i))
        (∑' j, heatCoeff (TensorEigenIdx.lambda (I := I) (M := M)) t j •
          ⟪b j, u₀⟫_ℝ • b j)) := by
    convert h_inner_hsum using 1
    funext j
    exact (h_summand_eq j).symm
  have h_tsum_ite :
      ∑' j : TensorEigenIdx (I := I) (M := M) g r s,
        (if j = i then
          heatCoeff (TensorEigenIdx.lambda (I := I) (M := M)) t j *
            ⟪b j, u₀⟫_ℝ
        else 0) =
      heatCoeff (TensorEigenIdx.lambda (I := I) (M := M)) t i *
        ⟪b i, u₀⟫_ℝ := by
    rw [tsum_ite_eq i]
  have h_eq := h_inner_hsum'.tsum_eq
  rw [h_tsum_ite] at h_eq
  have h_inner_val :
      ⟪b i, ∑' j, heatCoeff (TensorEigenIdx.lambda (I := I) (M := M)) t j •
            ⟪b j, u₀⟫_ℝ • b j⟫_ℝ =
        heatCoeff (TensorEigenIdx.lambda (I := I) (M := M)) t i *
          ⟪b i, u₀⟫_ℝ := h_eq.symm
  rw [h_inner_val, heatCoeff_def]

example (g : SmoothRiemannianMetric I M) (r s : ℕ) (t : ℝ) :
    TensorL2 r s g →L[ℝ] TensorL2 r s g :=
  tensorHeatSemigroup (I := I) (M := M) g r s t

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
