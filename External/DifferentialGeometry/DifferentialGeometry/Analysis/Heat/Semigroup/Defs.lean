import DifferentialGeometry.Analysis.Spectral.Scalar.EigenBasis
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Normed.Group.Tannery

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace HeatEquation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

abbrev EigenIdx (g : SmoothRiemannianMetric I M) :=
  Σ μ : NonzeroResolventEigenvalue (I := I) (M := M) g,
    Fin (Module.finrank ℝ
      (resolventEigenspace (I := I) (M := M) g μ.val))

abbrev EigenIdx.lambda {g : SmoothRiemannianMetric I M}
    (i : EigenIdx (I := I) (M := M) g) : ℝ :=
  laplacianEigenvalueOf i.1.val

omit [NeZero (Module.finrank ℝ E)] in
lemma lambda_nonneg {g : SmoothRiemannianMetric I M}
    (i : EigenIdx (I := I) (M := M) g) :
    0 ≤ EigenIdx.lambda (I := I) (M := M) i :=
  laplacianEigenvalueOf_nonneg (I := I) (M := M) i.1

omit [NeZero (Module.finrank ℝ E)] in
theorem heat_coeff_mem_unit_interval {g : SmoothRiemannianMetric I M}
    (i : EigenIdx (I := I) (M := M) g) {t : ℝ} (ht : 0 ≤ t) :
    0 < Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) ∧
      Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) ≤ 1 := by
  refine ⟨Real.exp_pos _, ?_⟩
  rw [Real.exp_le_one_iff]
  have hlam : 0 ≤ EigenIdx.lambda (I := I) (M := M) i :=
    lambda_nonneg (I := I) (M := M) i
  nlinarith

omit [NeZero (Module.finrank ℝ E)] in
private lemma heat_coeff_sq_le_one {g : SmoothRiemannianMetric I M}
    (i : EigenIdx (I := I) (M := M) g) {t : ℝ} (ht : 0 ≤ t) :
    (Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t)) ^ 2 ≤ 1 := by
  obtain ⟨h_pos, h_le⟩ := heat_coeff_mem_unit_interval (I := I) (M := M) i ht
  have h_nn : 0 ≤ Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) := h_pos.le
  nlinarith [sq_nonneg (Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) - 1)]

lemma summable_basis_coeff_sq
    (g : SmoothRiemannianMetric I M)
    (u : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    Summable (fun i : EigenIdx (I := I) (M := M) g =>
      (⟪resolventHilbertEigenbasisSigma (I := I) (M := M) g i, u⟫_ℝ) ^ 2) := by
  set b := resolventHilbertEigenbasisSigma (I := I) (M := M) g
  have h_orthonormal : Orthonormal ℝ b := b.orthonormal
  have h_orthFam :
      OrthogonalFamily ℝ (fun _ : EigenIdx (I := I) (M := M) g => ℝ)
        (fun i => LinearIsometry.toSpanSingleton ℝ
          (Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
          (h_orthonormal.1 i)) :=
    h_orthonormal.orthogonalFamily
  have h_summable_smul : Summable
      (fun i : EigenIdx (I := I) (M := M) g =>
        ⟪b i, u⟫_ℝ • b i) := by
    have h_hsum : HasSum (fun i => b.repr u i • b i) u := b.hasSum_repr u
    have h_eq : (fun i => b.repr u i • b i) =
        (fun i => ⟪b i, u⟫_ℝ • b i) := by
      funext i
      rw [b.repr_apply_apply]
    rw [h_eq] at h_hsum
    exact h_hsum.summable
  have h_iff := h_orthFam.summable_iff_norm_sq_summable
    (fun i : EigenIdx (I := I) (M := M) g => ⟪b i, u⟫_ℝ)
  have h_map_eq : (fun i : EigenIdx (I := I) (M := M) g =>
        LinearIsometry.toSpanSingleton ℝ
          (Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
          (h_orthonormal.1 i) (⟪b i, u⟫_ℝ)) =
      (fun i => ⟪b i, u⟫_ℝ • b i) := by
    funext i
    rw [LinearIsometry.toSpanSingleton_apply]
  rw [h_map_eq] at h_iff
  have h_sq_eq : (fun i : EigenIdx (I := I) (M := M) g =>
        ‖⟪b i, u⟫_ℝ‖ ^ 2) =
      (fun i => (⟪b i, u⟫_ℝ) ^ 2) := by
    funext i
    rw [Real.norm_eq_abs, sq_abs]
  rw [h_sq_eq] at h_iff
  exact h_iff.mp h_summable_smul

lemma parseval_norm_sq
    (g : SmoothRiemannianMetric I M)
    (u : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    ∑' i : EigenIdx (I := I) (M := M) g,
      (⟪resolventHilbertEigenbasisSigma (I := I) (M := M) g i, u⟫_ℝ) ^ 2 = ‖u‖ ^ 2 := by
  set b := resolventHilbertEigenbasisSigma (I := I) (M := M) g
  have h_par := b.tsum_inner_mul_inner u u
  have h_sq : ⟪u, u⟫_ℝ = ‖u‖ ^ 2 := real_inner_self_eq_norm_sq u
  have h_eq : (fun i : EigenIdx (I := I) (M := M) g =>
        ⟪u, b i⟫_ℝ * ⟪b i, u⟫_ℝ) =
      (fun i => (⟪b i, u⟫_ℝ) ^ 2) := by
    funext i
    rw [show ⟪u, b i⟫_ℝ = ⟪b i, u⟫_ℝ from real_inner_comm _ _, sq]
  rw [h_eq] at h_par
  rw [h_par, h_sq]

lemma summable_heatTerm
    (g : SmoothRiemannianMetric I M) {t : ℝ} (ht : 0 ≤ t)
    (u : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    Summable (fun i : EigenIdx (I := I) (M := M) g =>
      Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) •
        ⟪resolventHilbertEigenbasisSigma (I := I) (M := M) g i, u⟫_ℝ •
        resolventHilbertEigenbasisSigma (I := I) (M := M) g i) := by
  set b := resolventHilbertEigenbasisSigma (I := I) (M := M) g
  have h_orthonormal : Orthonormal ℝ b := b.orthonormal
  have h_orthFam :
      OrthogonalFamily ℝ (fun _ : EigenIdx (I := I) (M := M) g => ℝ)
        (fun i => LinearIsometry.toSpanSingleton ℝ
          (Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
          (h_orthonormal.1 i)) :=
    h_orthonormal.orthogonalFamily
  have h_sq_summable : Summable
      (fun i : EigenIdx (I := I) (M := M) g =>
        (Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) *
          ⟪b i, u⟫_ℝ) ^ 2) := by
    refine Summable.of_nonneg_of_le ?_ ?_ (summable_basis_coeff_sq
      (I := I) (M := M) g u)
    · intro i; positivity
    · intro i
      have h_sq_le : (Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t)) ^ 2 ≤ 1 :=
        heat_coeff_sq_le_one (I := I) (M := M) i ht
      have h_inner_sq_nn : 0 ≤ (⟪b i, u⟫_ℝ) ^ 2 := sq_nonneg _
      calc
        (Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) *
              ⟪b i, u⟫_ℝ) ^ 2
            = (Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t)) ^ 2 *
                (⟪b i, u⟫_ℝ) ^ 2 := by ring
        _ ≤ 1 * (⟪b i, u⟫_ℝ) ^ 2 := by
              apply mul_le_mul_of_nonneg_right h_sq_le h_inner_sq_nn
        _ = (⟪b i, u⟫_ℝ) ^ 2 := one_mul _
  have h_iff := h_orthFam.summable_iff_norm_sq_summable
    (fun i : EigenIdx (I := I) (M := M) g =>
      Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) * ⟪b i, u⟫_ℝ)
  have h_sq_eq : (fun i : EigenIdx (I := I) (M := M) g =>
        ‖Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) *
            ⟪b i, u⟫_ℝ‖ ^ 2) =
      (fun i => (Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) *
          ⟪b i, u⟫_ℝ) ^ 2) := by
    funext i
    rw [Real.norm_eq_abs, sq_abs]
  rw [h_sq_eq] at h_iff
  have h_map_eq : (fun i : EigenIdx (I := I) (M := M) g =>
        LinearIsometry.toSpanSingleton ℝ
          (Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
          (h_orthonormal.1 i)
          (Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) *
            ⟪b i, u⟫_ℝ)) =
      (fun i =>
        Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) •
          ⟪b i, u⟫_ℝ • b i) := by
    funext i
    rw [LinearIsometry.toSpanSingleton_apply]
    rw [mul_smul]
  have h_summable_V : Summable (fun i : EigenIdx (I := I) (M := M) g =>
      LinearIsometry.toSpanSingleton ℝ
        (Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
        (h_orthonormal.1 i)
        (Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) *
          ⟪b i, u⟫_ℝ)) := h_iff.mpr h_sq_summable
  rw [h_map_eq] at h_summable_V
  exact h_summable_V

lemma orthonormal_norm_sq_eq_tsum_sq
    (g : SmoothRiemannianMetric I M)
    (f : EigenIdx (I := I) (M := M) g → ℝ)
    (h_summable : Summable (fun i => (f i) ^ 2)) :
    ‖∑' i : EigenIdx (I := I) (M := M) g, f i •
        resolventHilbertEigenbasisSigma (I := I) (M := M) g i‖ ^ 2 =
      ∑' i, (f i) ^ 2 := by
  set b := resolventHilbertEigenbasisSigma (I := I) (M := M) g
  have h_orthonormal : Orthonormal ℝ b := b.orthonormal
  have h_orthFam :
      OrthogonalFamily ℝ (fun _ : EigenIdx (I := I) (M := M) g => ℝ)
        (fun i => LinearIsometry.toSpanSingleton ℝ
          (Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
          (h_orthonormal.1 i)) :=
    h_orthonormal.orthogonalFamily
  have h_memℓp : Memℓp (fun i : EigenIdx (I := I) (M := M) g => f i) 2 := by
    apply memℓp_gen
    have hpr : (2 : ℝ≥0∞).toReal = 2 := by norm_num
    have h_eq : (fun i : EigenIdx (I := I) (M := M) g =>
          ‖f i‖ ^ (2 : ℝ≥0∞).toReal) =
        (fun i => (f i) ^ 2) := by
      funext i
      rw [hpr, Real.norm_eq_abs, ← sq_abs]
      norm_cast
    rw [h_eq]
    exact h_summable
  set f_lp : lp (fun _ : EigenIdx (I := I) (M := M) g => ℝ) 2 :=
    ⟨fun i => f i, h_memℓp⟩
  have h_iso_norm : ‖h_orthFam.linearIsometry f_lp‖ = ‖f_lp‖ :=
    h_orthFam.linearIsometry.norm_map f_lp
  have h_iso_apply : h_orthFam.linearIsometry f_lp =
      ∑' i : EigenIdx (I := I) (M := M) g, f i • b i := by
    rw [h_orthFam.linearIsometry_apply f_lp]
    apply tsum_congr
    intro i
    rw [LinearIsometry.toSpanSingleton_apply]
  have h_lp_norm_sq : ‖f_lp‖ ^ 2 =
      ∑' i : EigenIdx (I := I) (M := M) g, (f i) ^ 2 := by
    have h_norm_sq := lp.norm_rpow_eq_tsum
      (p := 2) (E := fun _ : EigenIdx (I := I) (M := M) g => ℝ) (by norm_num) f_lp
    have hpr : (2 : ℝ≥0∞).toReal = 2 := by norm_num
    rw [hpr] at h_norm_sq
    have h_lhs : ‖f_lp‖ ^ (2 : ℝ) = ‖f_lp‖ ^ 2 := by norm_cast
    rw [h_lhs] at h_norm_sq
    have h_rhs_eq :
        (∑' i : EigenIdx (I := I) (M := M) g,
          ‖(f_lp : EigenIdx (I := I) (M := M) g → ℝ) i‖ ^ (2 : ℝ)) =
        ∑' i, (f i) ^ 2 := by
      apply tsum_congr
      intro i
      have h_eq_pt : (f_lp : EigenIdx (I := I) (M := M) g → ℝ) i = f i := rfl
      rw [h_eq_pt, Real.norm_eq_abs, ← sq_abs]
      norm_cast
    rw [h_rhs_eq] at h_norm_sq
    exact h_norm_sq
  have h_eq1 : ∑' i : EigenIdx (I := I) (M := M) g, f i • b i =
      h_orthFam.linearIsometry f_lp := h_iso_apply.symm
  rw [h_eq1, h_iso_norm, h_lp_norm_sq]

private lemma norm_sq_heatTerm_sum_le
    (g : SmoothRiemannianMetric I M) {t : ℝ} (ht : 0 ≤ t)
    (u : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    ‖∑' i : EigenIdx (I := I) (M := M) g,
        Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) •
          ⟪resolventHilbertEigenbasisSigma (I := I) (M := M) g i, u⟫_ℝ •
          resolventHilbertEigenbasisSigma (I := I) (M := M) g i‖ ^ 2 ≤
      ‖u‖ ^ 2 := by
  set b := resolventHilbertEigenbasisSigma (I := I) (M := M) g
  have h_summand_eq :
      (fun i : EigenIdx (I := I) (M := M) g =>
        Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) •
          ⟪b i, u⟫_ℝ • b i) =
      (fun i =>
        (Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) *
          ⟪b i, u⟫_ℝ) • b i) := by
    funext i; rw [mul_smul]
  rw [h_summand_eq]
  set f : EigenIdx (I := I) (M := M) g → ℝ := fun i =>
    Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) * ⟪b i, u⟫_ℝ
  have h_f_sq_le : ∀ i, (f i) ^ 2 ≤ (⟪b i, u⟫_ℝ) ^ 2 := by
    intro i
    have h_sq_le : (Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t)) ^ 2 ≤ 1 :=
      heat_coeff_sq_le_one (I := I) (M := M) i ht
    have h_inner_sq_nn : 0 ≤ (⟪b i, u⟫_ℝ) ^ 2 := sq_nonneg _
    change (f i) ^ 2 ≤ (⟪b i, u⟫_ℝ) ^ 2
    calc
      (f i) ^ 2
          = (Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t)) ^ 2 *
              (⟪b i, u⟫_ℝ) ^ 2 := by
                change (Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) *
                  ⟪b i, u⟫_ℝ) ^ 2 = _
                ring
      _ ≤ 1 * (⟪b i, u⟫_ℝ) ^ 2 := by
            apply mul_le_mul_of_nonneg_right h_sq_le h_inner_sq_nn
      _ = (⟪b i, u⟫_ℝ) ^ 2 := one_mul _
  have h_summable_f_sq : Summable (fun i : EigenIdx (I := I) (M := M) g =>
      (f i) ^ 2) := by
    refine Summable.of_nonneg_of_le ?_ ?_ (summable_basis_coeff_sq
      (I := I) (M := M) g u)
    · intro i; positivity
    · exact h_f_sq_le
  have h_norm_sq_eq := orthonormal_norm_sq_eq_tsum_sq (I := I) (M := M) g f h_summable_f_sq
  change ‖∑' i, f i • b i‖ ^ 2 ≤ ‖u‖ ^ 2
  rw [h_norm_sq_eq]
  have h_dom : ∑' i : EigenIdx (I := I) (M := M) g, (f i) ^ 2 ≤
      ∑' i, (⟪b i, u⟫_ℝ) ^ 2 :=
    Summable.tsum_le_tsum h_f_sq_le h_summable_f_sq
      (summable_basis_coeff_sq (I := I) (M := M) g u)
  refine le_trans h_dom ?_
  rw [parseval_norm_sq (I := I) (M := M) g u]

private lemma norm_heatTerm_sum_le
    (g : SmoothRiemannianMetric I M) {t : ℝ} (ht : 0 ≤ t)
    (u : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    ‖∑' i : EigenIdx (I := I) (M := M) g,
        Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) •
          ⟪resolventHilbertEigenbasisSigma (I := I) (M := M) g i, u⟫_ℝ •
          resolventHilbertEigenbasisSigma (I := I) (M := M) g i‖ ≤ ‖u‖ := by
  have h_sq := norm_sq_heatTerm_sum_le (I := I) (M := M) g ht u
  have h_lhs_nn : 0 ≤ ‖∑' i : EigenIdx (I := I) (M := M) g,
      Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) •
        ⟪resolventHilbertEigenbasisSigma (I := I) (M := M) g i, u⟫_ℝ •
        resolventHilbertEigenbasisSigma (I := I) (M := M) g i‖ := norm_nonneg _
  have h_rhs_nn : 0 ≤ ‖u‖ := norm_nonneg _
  exact (abs_le_of_sq_le_sq' h_sq h_rhs_nn).2

private noncomputable def heatSemigroupFun
    (g : SmoothRiemannianMetric I M) (t : ℝ)
    (u : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  ∑' i : EigenIdx (I := I) (M := M) g,
    Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) •
      ⟪resolventHilbertEigenbasisSigma (I := I) (M := M) g i, u⟫_ℝ •
      resolventHilbertEigenbasisSigma (I := I) (M := M) g i

private lemma heatSemigroupFun_add
    (g : SmoothRiemannianMetric I M) {t : ℝ} (ht : 0 ≤ t)
    (u v : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    heatSemigroupFun (I := I) (M := M) g t (u + v) =
      heatSemigroupFun (I := I) (M := M) g t u +
        heatSemigroupFun (I := I) (M := M) g t v := by
  unfold heatSemigroupFun
  set b := resolventHilbertEigenbasisSigma (I := I) (M := M) g
  have h_summand_eq : ∀ i : EigenIdx (I := I) (M := M) g,
      Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) •
        ⟪b i, u + v⟫_ℝ • b i =
      (Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) •
        ⟪b i, u⟫_ℝ • b i) +
      (Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) •
        ⟪b i, v⟫_ℝ • b i) := by
    intro i
    rw [inner_add_right, add_smul, smul_add]
  have h_sum_eq :
      (fun i : EigenIdx (I := I) (M := M) g =>
        Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) •
          ⟪b i, u + v⟫_ℝ • b i) =
      (fun i =>
        (Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) •
          ⟪b i, u⟫_ℝ • b i) +
        (Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) •
          ⟪b i, v⟫_ℝ • b i)) := by
    funext i; exact h_summand_eq i
  rw [h_sum_eq]
  rw [Summable.tsum_add (summable_heatTerm (I := I) (M := M) g ht u)
    (summable_heatTerm (I := I) (M := M) g ht v)]

private lemma heatSemigroupFun_smul
    (g : SmoothRiemannianMetric I M) {t : ℝ} (ht : 0 ≤ t) (c : ℝ)
    (u : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    heatSemigroupFun (I := I) (M := M) g t (c • u) =
      c • heatSemigroupFun (I := I) (M := M) g t u := by
  unfold heatSemigroupFun
  set b := resolventHilbertEigenbasisSigma (I := I) (M := M) g
  have h_summand_eq : ∀ i : EigenIdx (I := I) (M := M) g,
      Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) •
        ⟪b i, c • u⟫_ℝ • b i =
      c • (Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) •
        ⟪b i, u⟫_ℝ • b i) := by
    intro i
    rw [real_inner_smul_right]
    rw [smul_smul, smul_smul, smul_smul]
    congr 1
    ring
  have h_sum_eq :
      (fun i : EigenIdx (I := I) (M := M) g =>
        Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) •
          ⟪b i, c • u⟫_ℝ • b i) =
      (fun i => c • (Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) •
        ⟪b i, u⟫_ℝ • b i)) := by
    funext i; exact h_summand_eq i
  rw [h_sum_eq]
  exact (summable_heatTerm (I := I) (M := M) g ht u).tsum_const_smul c

noncomputable def heatSemigroup
    (g : SmoothRiemannianMetric I M) (t : ℝ) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) →L[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) := by
  by_cases ht : 0 ≤ t
  · refine LinearMap.mkContinuous
      { toFun := heatSemigroupFun (I := I) (M := M) g t
        map_add' := heatSemigroupFun_add (I := I) (M := M) g ht
        map_smul' := fun c u => heatSemigroupFun_smul (I := I) (M := M) g ht c u } 1 ?_
    intro u
    change ‖heatSemigroupFun (I := I) (M := M) g t u‖ ≤ 1 * ‖u‖
    rw [one_mul]
    exact norm_heatTerm_sum_le (I := I) (M := M) g ht u
  · exact 0

theorem heatSemigroup_apply_of_nonneg
    (g : SmoothRiemannianMetric I M) {t : ℝ} (ht : 0 ≤ t)
    (u : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    heatSemigroup (I := I) (M := M) g t u =
      ∑' i : EigenIdx (I := I) (M := M) g,
        Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) •
          ⟪resolventHilbertEigenbasisSigma (I := I) (M := M) g i, u⟫_ℝ •
          resolventHilbertEigenbasisSigma (I := I) (M := M) g i := by
  unfold heatSemigroup
  rw [dif_pos ht]
  rfl

theorem heatSemigroup_of_neg (g : SmoothRiemannianMetric I M) {t : ℝ} (ht : t < 0) :
    heatSemigroup (I := I) (M := M) g t = 0 := by
  unfold heatSemigroup
  rw [dif_neg (not_le.mpr ht)]

theorem heatSemigroup_opNorm_le_one (g : SmoothRiemannianMetric I M)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖heatSemigroup (I := I) (M := M) g t‖ ≤ 1 := by
  unfold heatSemigroup
  rw [dif_pos ht]
  exact LinearMap.mkContinuous_norm_le _ zero_le_one _

theorem heatSemigroup_apply_basis
    (g : SmoothRiemannianMetric I M) {t : ℝ} (ht : 0 ≤ t)
    (i : EigenIdx (I := I) (M := M) g) :
    heatSemigroup (I := I) (M := M) g t
        (resolventEigenbasisSigma (I := I) (M := M) g i) =
      Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) •
        resolventEigenbasisSigma (I := I) (M := M) g i := by
  classical
  set b := resolventHilbertEigenbasisSigma (I := I) (M := M) g
  rw [heatSemigroup_apply_of_nonneg (I := I) (M := M) g ht]
  rw [show resolventEigenbasisSigma (I := I) (M := M) g i = b i from
    (resolventEigenbasisSigma_eq_resolventEigenbasisVec (I := I) (M := M) g i).trans
      (resolventHilbertEigenbasisSigma_apply (I := I) (M := M) g i).symm]
  have h_orthonormal : Orthonormal ℝ b := b.orthonormal
  have h_inner_eq : ∀ j : EigenIdx (I := I) (M := M) g,
      ⟪b j, b i⟫_ℝ = if j = i then 1 else 0 := by
    intro j
    have h := (orthonormal_iff_ite (𝕜 := ℝ) (v := b)).mp h_orthonormal j i
    exact h
  have h_summand_eq : ∀ j : EigenIdx (I := I) (M := M) g,
      Real.exp (-(EigenIdx.lambda (I := I) (M := M) j) * t) •
        ⟪b j, b i⟫_ℝ • b j =
      if j = i then
        Real.exp (-(EigenIdx.lambda (I := I) (M := M) j) * t) • b j
      else 0 := by
    intro j
    rw [h_inner_eq]
    by_cases hji : j = i
    · simp [hji]
    · simp [hji]
  have h_sum_eq :
      (fun j : EigenIdx (I := I) (M := M) g =>
        Real.exp (-(EigenIdx.lambda (I := I) (M := M) j) * t) •
          ⟪b j, b i⟫_ℝ • b j) =
      (fun j =>
        if j = i then
          Real.exp (-(EigenIdx.lambda (I := I) (M := M) j) * t) • b j
        else 0) := by
    funext j; exact h_summand_eq j
  rw [h_sum_eq]
  rw [tsum_ite_eq i]

theorem heatSemigroup_isSelfAdjoint (g : SmoothRiemannianMetric I M)
    {t : ℝ} (ht : 0 ≤ t) :
    IsSelfAdjoint (heatSemigroup (I := I) (M := M) g t) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro u v
  set b := resolventHilbertEigenbasisSigma (I := I) (M := M) g
  change ⟪(heatSemigroup (I := I) (M := M) g t) u, v⟫_ℝ =
      ⟪u, (heatSemigroup (I := I) (M := M) g t) v⟫_ℝ
  rw [heatSemigroup_apply_of_nonneg (I := I) (M := M) g ht u,
      heatSemigroup_apply_of_nonneg (I := I) (M := M) g ht v]
  let φv : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) →L[ℝ] ℝ :=
    (innerSL ℝ).flip v
  let φu : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) →L[ℝ] ℝ :=
    innerSL ℝ u
  have h_lhs : ⟪∑' i : EigenIdx (I := I) (M := M) g,
        Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) •
          ⟪b i, u⟫_ℝ • b i, v⟫_ℝ =
      ∑' i : EigenIdx (I := I) (M := M) g,
        Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) *
          ⟪b i, u⟫_ℝ * ⟪b i, v⟫_ℝ := by
    have h_summable := summable_heatTerm (I := I) (M := M) g ht u
    have h_hsum := h_summable.hasSum
    have h_inner_hsum := h_hsum.mapL φv
    have h_summand_eq : ∀ i : EigenIdx (I := I) (M := M) g,
        φv (Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) •
            ⟪b i, u⟫_ℝ • b i) =
        Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) *
          ⟪b i, u⟫_ℝ * ⟪b i, v⟫_ℝ := by
      intro i
      change ⟪Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) •
          ⟪b i, u⟫_ℝ • b i, v⟫_ℝ = _
      rw [real_inner_smul_left, real_inner_smul_left]
      ring
    have h_inner_hsum' : HasSum (fun i =>
        Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) *
          ⟪b i, u⟫_ℝ * ⟪b i, v⟫_ℝ)
        (φv (∑' i, Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) •
            ⟪b i, u⟫_ℝ • b i)) := by
      convert h_inner_hsum using 1
      funext i; exact (h_summand_eq i).symm
    have h_apply : φv (∑' i : EigenIdx (I := I) (M := M) g,
          Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) •
            ⟪b i, u⟫_ℝ • b i) =
        ⟪∑' i, Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) •
            ⟪b i, u⟫_ℝ • b i, v⟫_ℝ := rfl
    rw [h_apply] at h_inner_hsum'
    exact h_inner_hsum'.tsum_eq.symm
  have h_rhs : ⟪u, ∑' i : EigenIdx (I := I) (M := M) g,
        Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) •
          ⟪b i, v⟫_ℝ • b i⟫_ℝ =
      ∑' i : EigenIdx (I := I) (M := M) g,
        Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) *
          ⟪b i, u⟫_ℝ * ⟪b i, v⟫_ℝ := by
    have h_summable := summable_heatTerm (I := I) (M := M) g ht v
    have h_hsum := h_summable.hasSum
    have h_inner_hsum := h_hsum.mapL φu
    have h_summand_eq : ∀ i : EigenIdx (I := I) (M := M) g,
        φu (Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) •
            ⟪b i, v⟫_ℝ • b i) =
        Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) *
          ⟪b i, u⟫_ℝ * ⟪b i, v⟫_ℝ := by
      intro i
      change ⟪u, Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) •
          ⟪b i, v⟫_ℝ • b i⟫_ℝ = _
      rw [real_inner_smul_right, real_inner_smul_right,
          show ⟪u, b i⟫_ℝ = ⟪b i, u⟫_ℝ from real_inner_comm _ _]
      ring
    have h_inner_hsum' : HasSum (fun i =>
        Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) *
          ⟪b i, u⟫_ℝ * ⟪b i, v⟫_ℝ)
        (φu (∑' i, Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) •
            ⟪b i, v⟫_ℝ • b i)) := by
      convert h_inner_hsum using 1
      funext i; exact (h_summand_eq i).symm
    have h_apply : φu (∑' i : EigenIdx (I := I) (M := M) g,
          Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) •
            ⟪b i, v⟫_ℝ • b i) =
        ⟪u, ∑' i, Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) •
            ⟪b i, v⟫_ℝ • b i⟫_ℝ := rfl
    rw [h_apply] at h_inner_hsum'
    exact h_inner_hsum'.tsum_eq.symm
  rw [h_lhs, h_rhs]

@[simp]
theorem heatSemigroup_zero (g : SmoothRiemannianMetric I M) :
    heatSemigroup (I := I) (M := M) g 0 = ContinuousLinearMap.id ℝ _ := by
  apply ContinuousLinearMap.ext
  intro u
  rw [heatSemigroup_apply_of_nonneg (I := I) (M := M) g (le_refl 0)]
  rw [ContinuousLinearMap.id_apply]
  set b := resolventHilbertEigenbasisSigma (I := I) (M := M) g
  have h_coeff_one : ∀ i : EigenIdx (I := I) (M := M) g,
      Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * 0) = 1 := by
    intro i
    have : -(EigenIdx.lambda (I := I) (M := M) i) * 0 = 0 := by ring
    rw [this, Real.exp_zero]
  have h_summand_eq : (fun i : EigenIdx (I := I) (M := M) g =>
        Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * 0) •
          ⟪b i, u⟫_ℝ • b i) =
      (fun i => ⟪b i, u⟫_ℝ • b i) := by
    funext i; rw [h_coeff_one i, one_smul]
  rw [h_summand_eq]
  have h_hsum : HasSum (fun i => b.repr u i • b i) u := b.hasSum_repr u
  have h_eq : (fun i => b.repr u i • b i) = (fun i => ⟪b i, u⟫_ℝ • b i) := by
    funext i; rw [b.repr_apply_apply]
  rw [h_eq] at h_hsum
  exact h_hsum.tsum_eq

theorem heatSemigroup_add (g : SmoothRiemannianMetric I M)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    heatSemigroup (I := I) (M := M) g (s + t) =
      (heatSemigroup (I := I) (M := M) g s).comp
        (heatSemigroup (I := I) (M := M) g t) := by
  apply ContinuousLinearMap.ext
  intro u
  set b := resolventHilbertEigenbasisSigma (I := I) (M := M) g
  have hst_nn : 0 ≤ s + t := add_nonneg hs ht
  rw [heatSemigroup_apply_of_nonneg (I := I) (M := M) g hst_nn,
      ContinuousLinearMap.comp_apply,
      heatSemigroup_apply_of_nonneg (I := I) (M := M) g ht u]
  have h_summable_t := summable_heatTerm (I := I) (M := M) g ht u
  have h_pull :
      heatSemigroup (I := I) (M := M) g s
          (∑' i : EigenIdx (I := I) (M := M) g,
            Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) •
              ⟪b i, u⟫_ℝ • b i) =
      ∑' i : EigenIdx (I := I) (M := M) g,
        heatSemigroup (I := I) (M := M) g s
          (Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) •
            ⟪b i, u⟫_ℝ • b i) := by
    have h_hsum := h_summable_t.hasSum
    exact (h_hsum.mapL (heatSemigroup (I := I) (M := M) g s)).tsum_eq.symm
  rw [h_pull]
  apply tsum_congr
  intro i
  rw [(heatSemigroup (I := I) (M := M) g s).map_smul,
      (heatSemigroup (I := I) (M := M) g s).map_smul]
  have h_basis_apply :
      heatSemigroup (I := I) (M := M) g s (b i) =
      Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * s) • b i := by
    have hh := heatSemigroup_apply_basis (I := I) (M := M) g hs i
    have h_eq : resolventEigenbasisSigma (I := I) (M := M) g i = b i :=
      (resolventEigenbasisSigma_eq_resolventEigenbasisVec (I := I) (M := M) g i).trans
        (resolventHilbertEigenbasisSigma_apply (I := I) (M := M) g i).symm
    rw [h_eq] at hh
    exact hh
  rw [h_basis_apply]
  have h_exp_add : Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * (s + t)) =
      Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * s) *
      Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) := by
    rw [show -(EigenIdx.lambda (I := I) (M := M) i) * (s + t) =
        -(EigenIdx.lambda (I := I) (M := M) i) * s +
        -(EigenIdx.lambda (I := I) (M := M) i) * t from by ring,
        Real.exp_add]
  rw [show Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * (s + t)) •
      ⟪b i, u⟫_ℝ • b i =
      (Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * (s + t)) *
        ⟪b i, u⟫_ℝ) • b i from by rw [mul_smul]]
  rw [show Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) •
      ⟪b i, u⟫_ℝ •
      Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * s) • b i =
      (Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) *
        (⟪b i, u⟫_ℝ * Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * s))) • b i from by
    rw [mul_smul, mul_smul]]
  congr 1
  rw [h_exp_add]
  ring

theorem heatSemigroup_continuous_at_zero
    (g : SmoothRiemannianMetric I M)
    (u : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    Filter.Tendsto (fun t : ℝ => heatSemigroup (I := I) (M := M) g t u)
        (𝓝[≥] (0 : ℝ)) (𝓝 u) := by
  set b := resolventHilbertEigenbasisSigma (I := I) (M := M) g
  rw [Metric.tendsto_nhds]
  intro ε hε
  have h_summable_sq : Summable (fun i : EigenIdx (I := I) (M := M) g =>
      (⟪b i, u⟫_ℝ) ^ 2) := summable_basis_coeff_sq (I := I) (M := M) g u
  have hε16_pos : (0 : ℝ) < ε ^ 2 / 16 := by positivity
  obtain ⟨T, hT⟩ : ∃ T : Finset (EigenIdx (I := I) (M := M) g),
      ∑' i : { i : EigenIdx (I := I) (M := M) g // i ∉ T },
        (⟪b (i : EigenIdx (I := I) (M := M) g), u⟫_ℝ) ^ 2 < ε ^ 2 / 16 := by
    have h_hsum := h_summable_sq.hasSum
    rw [HasSum, Metric.tendsto_nhds] at h_hsum
    have h_evt := h_hsum (ε ^ 2 / 16) hε16_pos
    obtain ⟨T, hT_T⟩ := h_evt.exists
    refine ⟨T, ?_⟩
    have h_split : ∑' i : EigenIdx (I := I) (M := M) g,
        (⟪b i, u⟫_ℝ) ^ 2 =
        (∑ i ∈ T, (⟪b i, u⟫_ℝ) ^ 2) +
        ∑' i : { i : EigenIdx (I := I) (M := M) g // i ∉ T },
          (⟪b (i : EigenIdx (I := I) (M := M) g), u⟫_ℝ) ^ 2 :=
      (h_summable_sq.sum_add_tsum_subtype_compl T).symm
    rw [dist_eq_norm, h_split] at hT_T
    have h_simp : ∑ i ∈ T, (⟪b i, u⟫_ℝ) ^ 2 -
        ((∑ i ∈ T, (⟪b i, u⟫_ℝ) ^ 2) +
          ∑' i : { i : EigenIdx (I := I) (M := M) g // i ∉ T },
            (⟪b (i : EigenIdx (I := I) (M := M) g), u⟫_ℝ) ^ 2) =
        -(∑' i : { i : EigenIdx (I := I) (M := M) g // i ∉ T },
            (⟪b (i : EigenIdx (I := I) (M := M) g), u⟫_ℝ) ^ 2) := by ring
    rw [h_simp, norm_neg, Real.norm_eq_abs] at hT_T
    have h_tail_nn : 0 ≤ ∑' i : { i : EigenIdx (I := I) (M := M) g // i ∉ T },
        (⟪b (i : EigenIdx (I := I) (M := M) g), u⟫_ℝ) ^ 2 := by
      apply tsum_nonneg
      intro i; exact sq_nonneg _
    rwa [abs_of_nonneg h_tail_nn] at hT_T
  have h_head_tendsto : Tendsto (fun t : ℝ =>
      ∑ i ∈ T, (Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) - 1) ^ 2 *
        (⟪b i, u⟫_ℝ) ^ 2) (𝓝 (0 : ℝ)) (𝓝 0) := by
    have h_each : ∀ i ∈ T, Tendsto (fun t : ℝ =>
        (Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) - 1) ^ 2 *
          (⟪b i, u⟫_ℝ) ^ 2) (𝓝 0) (𝓝 0) := by
      intro i _
      have h_arg : Tendsto (fun t : ℝ =>
          -(EigenIdx.lambda (I := I) (M := M) i) * t) (𝓝 (0 : ℝ)) (𝓝 0) := by
        have h_id : Tendsto (fun t : ℝ => t) (𝓝 (0 : ℝ)) (𝓝 0) := tendsto_id
        have := h_id.const_mul (-(EigenIdx.lambda (I := I) (M := M) i))
        simpa using this
      have h_exp_to_one : Tendsto (fun t : ℝ =>
          Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t)) (𝓝 (0 : ℝ)) (𝓝 1) := by
        have := h_arg.rexp
        simpa [Real.exp_zero] using this
      have h_diff_to_zero : Tendsto (fun t : ℝ =>
          Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) - 1)
          (𝓝 (0 : ℝ)) (𝓝 0) := by
        have := h_exp_to_one.sub_const 1
        simpa using this
      have h_sq_to_zero : Tendsto (fun t : ℝ =>
          (Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) - 1) ^ 2)
          (𝓝 (0 : ℝ)) (𝓝 0) := by
        have := h_diff_to_zero.pow 2
        simpa using this
      have := h_sq_to_zero.mul_const ((⟪b i, u⟫_ℝ) ^ 2)
      simpa using this
    have h_total : Tendsto (fun t : ℝ =>
        ∑ i ∈ T, (Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) - 1) ^ 2 *
          (⟪b i, u⟫_ℝ) ^ 2) (𝓝 0) (𝓝 (∑ i ∈ T, (0 : ℝ))) :=
      tendsto_finset_sum T h_each
    simpa using h_total
  rw [Metric.tendsto_nhds] at h_head_tendsto
  obtain ⟨δ, hδ_pos, hδ⟩ := Metric.eventually_nhds_iff_ball.mp
    (h_head_tendsto (ε ^ 2 / 4) (by positivity))
  rw [Filter.eventually_iff_exists_mem]
  refine ⟨{t : ℝ | 0 ≤ t ∧ t < δ}, ?_, ?_⟩
  · rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
    refine ⟨Set.Iio δ, Iio_mem_nhds hδ_pos, ?_⟩
    intro x hx
    refine ⟨hx.2, ?_⟩
    exact hx.1
  intro t ht_in
  obtain ⟨ht_nn, ht_lt⟩ := ht_in
  rw [dist_eq_norm]
  suffices h_sq : ‖heatSemigroup (I := I) (M := M) g t u - u‖ ^ 2 < ε ^ 2 by
    exact (abs_lt_of_sq_lt_sq' h_sq hε.le).2
  rw [heatSemigroup_apply_of_nonneg (I := I) (M := M) g ht_nn u]
  have h_summable_heat := summable_heatTerm (I := I) (M := M) g ht_nn u
  have h_hsum_heat : HasSum (fun i : EigenIdx (I := I) (M := M) g =>
      Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) •
        ⟪b i, u⟫_ℝ • b i)
      (∑' i, Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) •
        ⟪b i, u⟫_ℝ • b i) := h_summable_heat.hasSum
  have h_hsum_basis : HasSum (fun i : EigenIdx (I := I) (M := M) g =>
      ⟪b i, u⟫_ℝ • b i) u := by
    have h_repr : HasSum (fun i => b.repr u i • b i) u := b.hasSum_repr u
    have h_eq : (fun i => b.repr u i • b i) = (fun i => ⟪b i, u⟫_ℝ • b i) := by
      funext i; rw [b.repr_apply_apply]
    rw [h_eq] at h_repr
    exact h_repr
  have h_hsum_diff : HasSum (fun i : EigenIdx (I := I) (M := M) g =>
      Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) •
        ⟪b i, u⟫_ℝ • b i - ⟪b i, u⟫_ℝ • b i)
      ((∑' i, Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) •
        ⟪b i, u⟫_ℝ • b i) - u) :=
    h_hsum_heat.sub h_hsum_basis
  have h_sum_diff :
      (∑' i : EigenIdx (I := I) (M := M) g,
        Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) •
          ⟪b i, u⟫_ℝ • b i) - u =
      ∑' i : EigenIdx (I := I) (M := M) g,
        (Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) - 1) •
          ⟪b i, u⟫_ℝ • b i := by
    have h_summand_eq : (fun i : EigenIdx (I := I) (M := M) g =>
        Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) •
          ⟪b i, u⟫_ℝ • b i - ⟪b i, u⟫_ℝ • b i) =
        (fun i =>
          (Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) - 1) •
            ⟪b i, u⟫_ℝ • b i) := by
      funext i; rw [sub_smul, one_smul]
    rw [h_summand_eq] at h_hsum_diff
    exact h_hsum_diff.tsum_eq.symm
  rw [h_sum_diff]
  have h_sum_eq :
      (fun i : EigenIdx (I := I) (M := M) g =>
        (Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) - 1) •
          ⟪b i, u⟫_ℝ • b i) =
      (fun i =>
        ((Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) - 1) *
          ⟪b i, u⟫_ℝ) • b i) := by
    funext i; rw [mul_smul]
  rw [h_sum_eq]
  set f : EigenIdx (I := I) (M := M) g → ℝ := fun i =>
    (Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) - 1) * ⟪b i, u⟫_ℝ
  have h_f_sq_le : ∀ i, (f i) ^ 2 ≤ 4 * (⟪b i, u⟫_ℝ) ^ 2 := by
    intro i
    have h_pos : 0 < Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) :=
      Real.exp_pos _
    have h_le : Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have hlam : 0 ≤ EigenIdx.lambda (I := I) (M := M) i :=
        lambda_nonneg (I := I) (M := M) i
      nlinarith
    have h_diff_sq : (Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) - 1) ^ 2 ≤ 4 := by
      nlinarith [h_pos, h_le, sq_nonneg
        (Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) - 1)]
    have h_inner_sq_nn : 0 ≤ (⟪b i, u⟫_ℝ) ^ 2 := sq_nonneg _
    change (f i) ^ 2 ≤ 4 * (⟪b i, u⟫_ℝ) ^ 2
    have h_factor : (f i) ^ 2 =
        (Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) - 1) ^ 2 *
          (⟪b i, u⟫_ℝ) ^ 2 := by
      change ((Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) - 1) *
        ⟪b i, u⟫_ℝ) ^ 2 = _
      ring
    rw [h_factor]
    nlinarith [h_diff_sq, h_inner_sq_nn]
  have h_summable_f_sq : Summable (fun i : EigenIdx (I := I) (M := M) g => (f i) ^ 2) := by
    refine Summable.of_nonneg_of_le ?_ ?_ (h_summable_sq.mul_left 4)
    · intro i; positivity
    · intro i; exact h_f_sq_le i
  have h_norm_sq_eq := orthonormal_norm_sq_eq_tsum_sq (I := I) (M := M) g f h_summable_f_sq
  change ‖∑' i, f i • b i‖ ^ 2 < ε ^ 2
  rw [h_norm_sq_eq]
  have h_split : ∑' i : EigenIdx (I := I) (M := M) g, (f i) ^ 2 =
      (∑ i ∈ T, (f i) ^ 2) +
      ∑' i : { i : EigenIdx (I := I) (M := M) g // i ∉ T },
        (f (i : EigenIdx (I := I) (M := M) g)) ^ 2 :=
    (h_summable_f_sq.sum_add_tsum_subtype_compl T).symm
  rw [h_split]
  have h_head_bound : ∑ i ∈ T, (f i) ^ 2 < ε ^ 2 / 4 := by
    have h_in_ball : t ∈ Metric.ball (0 : ℝ) δ := by
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_nonneg ht_nn]
      exact ht_lt
    have h_dist := hδ t h_in_ball
    rw [dist_zero_right, Real.norm_eq_abs] at h_dist
    have h_head_eq_f : ∀ i,
        (Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) - 1) ^ 2 *
          (⟪b i, u⟫_ℝ) ^ 2 = (f i) ^ 2 := by
      intro i
      change _ = ((Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) - 1) *
        ⟪b i, u⟫_ℝ) ^ 2
      ring
    have h_sum_eq : ∑ i ∈ T, (Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) - 1) ^ 2 *
        (⟪b i, u⟫_ℝ) ^ 2 = ∑ i ∈ T, (f i) ^ 2 := by
      apply Finset.sum_congr rfl
      intros i _; exact h_head_eq_f i
    rw [h_sum_eq] at h_dist
    have h_nn : 0 ≤ ∑ i ∈ T, (f i) ^ 2 := by
      apply Finset.sum_nonneg; intros; exact sq_nonneg _
    rwa [abs_of_nonneg h_nn] at h_dist
  have h_tail_bound : ∑' i : { i : EigenIdx (I := I) (M := M) g // i ∉ T },
      (f (i : EigenIdx (I := I) (M := M) g)) ^ 2 < ε ^ 2 / 4 := by
    have h_tail_le : ∑' i : { i : EigenIdx (I := I) (M := M) g // i ∉ T },
        (f (i : EigenIdx (I := I) (M := M) g)) ^ 2 ≤
        4 * ∑' i : { i : EigenIdx (I := I) (M := M) g // i ∉ T },
          (⟪b (i : EigenIdx (I := I) (M := M) g), u⟫_ℝ) ^ 2 := by
      rw [← tsum_mul_left]
      refine Summable.tsum_le_tsum (fun i => h_f_sq_le i) ?_ ?_
      · exact h_summable_f_sq.subtype _
      · exact (h_summable_sq.subtype _).mul_left 4
    have h_lt : 4 * ∑' i : { i : EigenIdx (I := I) (M := M) g // i ∉ T },
        (⟪b (i : EigenIdx (I := I) (M := M) g), u⟫_ℝ) ^ 2 < 4 * (ε ^ 2 / 16) := by
      apply mul_lt_mul_of_pos_left hT (by norm_num : (0 : ℝ) < 4)
    have h_eq : 4 * (ε ^ 2 / 16) = ε ^ 2 / 4 := by ring
    linarith [h_tail_le, h_lt, h_eq]
  linarith [h_head_bound, h_tail_bound]

end HeatEquation
end Analysis
end DifferentialGeometry

end
