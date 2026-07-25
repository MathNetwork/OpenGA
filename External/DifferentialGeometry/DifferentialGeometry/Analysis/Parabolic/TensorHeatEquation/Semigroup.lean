import DifferentialGeometry.Analysis.Spectral.Tensor.Spectrum.EigenBasis
import Mathlib.Analysis.SpecialFunctions.Exp

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorHeatEquation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

abbrev TensorEigenIdx (g : SmoothRiemannianMetric I M) (r s : ℕ) : Type _ :=
  Σ μ : TensorNonzeroResolventEigenvalue (I := I) (M := M) g r s,
    Fin (Module.finrank ℝ
      (tensorResolventEigenspace (I := I) (M := M) g r s μ.val))

noncomputable abbrev TensorEigenIdx.lambda
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (i : TensorEigenIdx (I := I) (M := M) g r s) : ℝ :=
  tensorLaplacianEigenvalueOf i.fst.val

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensor_lambda_nonneg
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    0 ≤ TensorEigenIdx.lambda (I := I) (M := M) i := by
  obtain ⟨u, hu_mem, hu_ne⟩ := i.fst.hasEigenvalue.exists_hasEigenvector
  have hu_in : u ∈ tensorResolventEigenspace
      (I := I) (M := M) g r s i.fst.val := hu_mem
  have h_mem_unit : i.fst.val ∈ Set.Ioc (0 : ℝ) 1 :=
    tensorResolvent_eigenvalue_mem_unit_interval
      (I := I) (M := M) g r s hu_in hu_ne
  exact tensorLaplacianEigenvalueOf_nonneg_of_resolventEigenvalue h_mem_unit

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensor_heat_coeff_mem_unit_interval
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (i : TensorEigenIdx (I := I) (M := M) g r s) {t : ℝ} (ht : 0 ≤ t) :
    0 < Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) ∧
      Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) ≤ 1 := by
  refine ⟨Real.exp_pos _, ?_⟩
  rw [Real.exp_le_one_iff]
  have hlam : 0 ≤ TensorEigenIdx.lambda (I := I) (M := M) i :=
    tensor_lambda_nonneg (I := I) (M := M) i
  nlinarith

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma tensor_heat_coeff_sq_le_one
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (i : TensorEigenIdx (I := I) (M := M) g r s) {t : ℝ} (ht : 0 ≤ t) :
    (Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t)) ^ 2 ≤ 1 := by
  obtain ⟨h_pos, h_le⟩ :=
    tensor_heat_coeff_mem_unit_interval (I := I) (M := M) i ht
  have h_nn : 0 ≤ Real.exp
      (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) := h_pos.le
  nlinarith [sq_nonneg
    (Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) - 1)]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma tensorSummable_basis_coeff_sq
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (T : TensorL2 r s g) :
    Summable (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
      ‖⟪tensorResolventHilbertEigenbasisSigma
            (I := I) (M := M) h_compact i, T⟫_ℝ‖ ^ 2) := by
  set b := tensorResolventHilbertEigenbasisSigma
    (I := I) (M := M) (g := g) (r := r) (s := s) h_compact
  have h_orthonormal : Orthonormal ℝ b := b.orthonormal
  have h_orthFam :
      OrthogonalFamily ℝ
        (fun _ : TensorEigenIdx (I := I) (M := M) g r s => ℝ)
        (fun i => LinearIsometry.toSpanSingleton ℝ
          (TensorL2 r s g) (h_orthonormal.1 i)) :=
    h_orthonormal.orthogonalFamily
  have h_summable_smul : Summable
      (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
        ⟪b i, T⟫_ℝ • b i) := by
    have h_hsum : HasSum (fun i => b.repr T i • b i) T := b.hasSum_repr T
    have h_eq : (fun i => b.repr T i • b i) =
        (fun i => ⟪b i, T⟫_ℝ • b i) := by
      funext i
      rw [b.repr_apply_apply]
    rw [h_eq] at h_hsum
    exact h_hsum.summable
  have h_iff := h_orthFam.summable_iff_norm_sq_summable
    (fun i : TensorEigenIdx (I := I) (M := M) g r s => ⟪b i, T⟫_ℝ)
  have h_map_eq : (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
        LinearIsometry.toSpanSingleton ℝ
          (TensorL2 r s g) (h_orthonormal.1 i) (⟪b i, T⟫_ℝ)) =
      (fun i => ⟪b i, T⟫_ℝ • b i) := by
    funext i
    rw [LinearIsometry.toSpanSingleton_apply]
  rw [h_map_eq] at h_iff
  exact h_iff.mp h_summable_smul

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma tensorParseval_norm_sq
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (T : TensorL2 r s g) :
    ‖T‖ ^ 2 =
      ∑' i : TensorEigenIdx (I := I) (M := M) g r s,
        ‖⟪tensorResolventHilbertEigenbasisSigma
            (I := I) (M := M) h_compact i, T⟫_ℝ‖ ^ 2 := by
  set b := tensorResolventHilbertEigenbasisSigma
    (I := I) (M := M) (g := g) (r := r) (s := s) h_compact
  have h_par := b.tsum_inner_mul_inner T T
  have h_sq : ⟪T, T⟫_ℝ = ‖T‖ ^ 2 := real_inner_self_eq_norm_sq T
  have h_eq : (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
        ⟪T, b i⟫_ℝ * ⟪b i, T⟫_ℝ) =
      (fun i => ‖⟪b i, T⟫_ℝ‖ ^ 2) := by
    funext i
    rw [show ⟪T, b i⟫_ℝ = ⟪b i, T⟫_ℝ from real_inner_comm _ _,
        Real.norm_eq_abs, sq_abs, sq]
  rw [h_eq] at h_par
  linarith [h_par, h_sq]

example (g : SmoothRiemannianMetric I M) (r s : ℕ) : Type _ :=
  TensorEigenIdx (I := I) (M := M) g r s

example {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (i : TensorEigenIdx (I := I) (M := M) g r s) : ℝ :=
  TensorEigenIdx.lambda (I := I) (M := M) i

end TensorHeatEquation
end Parabolic
end Analysis
end DifferentialGeometry

end
