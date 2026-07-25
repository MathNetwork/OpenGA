import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.PreHilbert
import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.Integrability
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Algebra
import DifferentialGeometry.Geometry.Connection.TensorNabla.TensorRSNabla
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Defs
import DifferentialGeometry.Geometry.Connection.LeviCivita.Defs
import DifferentialGeometry.Analysis.Integration.Measure.Properties
import DifferentialGeometry.Geometry.Metric.PointwiseInner.MetricLowering
import DifferentialGeometry.Tensor.Multilinear.BundleSmoothEval
import DifferentialGeometry.Geometry.Metric.TensorInner.TensorRSRiemannian
import DifferentialGeometry.Geometry.Operator.Gradient
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.ContinuousOn


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators Matrix
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Tensor.TensorRSRiemannian
open TensorRSNabla

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

noncomputable def tensorCovDerivAt
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (x : M) (v : E) :
    TensorRSSpace r s I x :=
  tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)
    (fun y : M => S.toSection y) x v

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma tensorCovDerivAt_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (x : M) (v : E) :
    tensorCovDerivAt (I := I) (M := M) g r s S x v =
      tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)
        (fun y : M => S.toSection y) x v := rfl

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma tensorCovDerivAt_add
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S₁ S₂ : SmoothCcTensor g r s) (x : M) (v : E) :
    tensorCovDerivAt (I := I) (M := M) g r s (S₁ + S₂) x v =
      tensorCovDerivAt (I := I) (M := M) g r s S₁ x v +
        tensorCovDerivAt (I := I) (M := M) g r s S₂ x v := by
  unfold tensorCovDerivAt
  have hpt : (fun y : M => (S₁ + S₂).toSection y) =
      (fun y : M => S₁.toSection y) + (fun y : M => S₂.toSection y) := by
    funext y
    rw [SmoothCcTensor.toSection_add]
    rfl
  rw [hpt]
  have hadd := (tensorRSCovariantDerivative I M r s
    (LeviCivita (I := I) g)).isCovariantDerivativeOn.add
    (σ := fun y : M => S₁.toSection y)
    (σ' := fun y : M => S₂.toSection y)
    (S₁.toSection.contMDiff.mdifferentiable (by norm_num)).mdifferentiableAt
    (S₂.toSection.contMDiff.mdifferentiable (by norm_num)).mdifferentiableAt
    (by trivial : x ∈ (Set.univ : Set M))
  have hclm : (tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)).toFun
        (fun y : M => S₁.toSection y + S₂.toSection y) x =
      (tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)).toFun
          (fun y : M => S₁.toSection y) x +
      (tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)).toFun
          (fun y : M => S₂.toSection y) x := hadd
  change (tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)).toFun
      (fun y : M => S₁.toSection y + S₂.toSection y) x v = _
  rw [hclm]
  rfl

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma tensorCovDerivAt_smul
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (c : ℝ) (S : SmoothCcTensor g r s) (x : M) (v : E) :
    tensorCovDerivAt (I := I) (M := M) g r s (c • S) x v =
      c • tensorCovDerivAt (I := I) (M := M) g r s S x v := by
  unfold tensorCovDerivAt
  have hpt : (fun y : M => (c • S).toSection y) =
      (fun _ : M => c) • (fun y : M => S.toSection y) := by
    funext y
    rw [SmoothCcTensor.toSection_smul]
    rfl
  rw [hpt]
  have hf_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M => c) := contMDiff_const
  have hf_mdiff : MDiffAt (fun y : M => c) x :=
    (hf_smooth.mdifferentiable (by norm_num)).mdifferentiableAt
  have hcov_leibniz :=
    (tensorRSCovariantDerivative I M r s
        (LeviCivita (I := I) g)).isCovariantDerivativeOn.leibniz
      (σ := fun y : M => S.toSection y)
      (g := fun _ : M => c)
      (hσ := (S.toSection.contMDiff.mdifferentiable (by norm_num)).mdifferentiableAt)
      (hg := hf_mdiff)
      (hx := (by trivial : x ∈ (Set.univ : Set M)))
  have hext_zero : extDerivFun (I := I) (fun _ : M => c) x = 0 := by
    unfold extDerivFun
    simp [mfderiv_const]
  change (tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)).toFun
      ((fun _ : M => c) • fun y : M => S.toSection y) x v = _
  rw [hcov_leibniz]
  rw [hext_zero]
  simp [ContinuousLinearMap.smul_apply]

noncomputable def tensorCovDerivPointwiseInner
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) (x : M) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
    (gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
      tensorInnerPointwise (I := I) (M := M) g r s x
        (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g r s S x ((chartModelBasis E) i)))
        (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g r s T x ((chartModelBasis E) j)))

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma tensorCovDerivPointwiseInner_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) (x : M) :
    tensorCovDerivPointwiseInner (I := I) (M := M) g r s S T x =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        (gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
          tensorInnerPointwise (I := I) (M := M) g r s x
            (TensorRSSpace.toModel
              (tensorCovDerivAt (I := I) (M := M) g r s S x
                ((chartModelBasis E) i)))
            (TensorRSSpace.toModel
              (tensorCovDerivAt (I := I) (M := M) g r s T x
                ((chartModelBasis E) j))) := rfl

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma tensorCovDerivPointwiseInner_symm
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) (x : M) :
    tensorCovDerivPointwiseInner (I := I) (M := M) g r s S T x =
      tensorCovDerivPointwiseInner (I := I) (M := M) g r s T S x := by
  unfold tensorCovDerivPointwiseInner
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro i _
  refine Finset.sum_congr rfl ?_
  intro j _
  have hG : (gramMatrixAt (I := I) (M := M) g x)⁻¹ j i =
      (gramMatrixAt (I := I) (M := M) g x)⁻¹ i j := by
    have hherm := gramMatrixAt_inv_isHermitian (I := I) (M := M) g x
    have := hherm.apply i j
    simpa [star_trivial] using this
  rw [hG]
  rw [tensorInnerPointwise_symm]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma tensorCovDerivPointwiseInner_add_left
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S₁ S₂ T : SmoothCcTensor g r s) (x : M) :
    tensorCovDerivPointwiseInner (I := I) (M := M) g r s (S₁ + S₂) T x =
      tensorCovDerivPointwiseInner (I := I) (M := M) g r s S₁ T x +
        tensorCovDerivPointwiseInner (I := I) (M := M) g r s S₂ T x := by
  unfold tensorCovDerivPointwiseInner
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro j _
  have hAdd : tensorCovDerivAt (I := I) (M := M) g r s (S₁ + S₂) x
        ((chartModelBasis E) i) =
      tensorCovDerivAt (I := I) (M := M) g r s S₁ x ((chartModelBasis E) i) +
        tensorCovDerivAt (I := I) (M := M) g r s S₂ x ((chartModelBasis E) i) :=
    tensorCovDerivAt_add (I := I) (M := M) g r s S₁ S₂ x ((chartModelBasis E) i)
  rw [hAdd, TensorRSSpace.toModel_add, tensorInnerPointwise_add_left]
  ring

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma tensorCovDerivPointwiseInner_smul_left
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (c : ℝ) (S T : SmoothCcTensor g r s) (x : M) :
    tensorCovDerivPointwiseInner (I := I) (M := M) g r s (c • S) T x =
      c * tensorCovDerivPointwiseInner (I := I) (M := M) g r s S T x := by
  unfold tensorCovDerivPointwiseInner
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j _
  have hSmul : tensorCovDerivAt (I := I) (M := M) g r s (c • S) x
        ((chartModelBasis E) i) =
      c • tensorCovDerivAt (I := I) (M := M) g r s S x ((chartModelBasis E) i) :=
    tensorCovDerivAt_smul (I := I) (M := M) g r s c S x ((chartModelBasis E) i)
  rw [hSmul, TensorRSSpace.toModel_smul, tensorInnerPointwise_smul_left]
  ring

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma tensorCovDerivPointwiseInner_nonneg
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (x : M) :
    0 ≤ tensorCovDerivPointwiseInner (I := I) (M := M) g r s S S x := by
  classical
  set n := Module.finrank ℝ E with hn_def
  set Ginv : Matrix (Fin n) (Fin n) ℝ :=
    (gramMatrixAt (I := I) (M := M) g x)⁻¹ with hGinv
  have hGinv_psd : Ginv.PosSemidef := by
    simpa [hGinv] using gramMatrixAt_inv_posSemidef (I := I) (M := M) g x
  have hGinv_herm : Ginv.IsHermitian := hGinv_psd.isHermitian
  set vfam : Fin n → TensorRSModel r s ℝ E :=
    fun i => TensorRSSpace.toModel
      (tensorCovDerivAt (I := I) (M := M) g r s S x ((chartModelBasis E) i))
    with hvfam_def
  have hspec := hGinv_herm.spectral_theorem
  set U : Matrix (Fin n) (Fin n) ℝ :=
    (hGinv_herm.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) with hU_def
  set μ : Fin n → ℝ := hGinv_herm.eigenvalues with hμ_def
  have hμ_nonneg : ∀ k, 0 ≤ μ k := hGinv_psd.eigenvalues_nonneg
  have hGinv_entry :
      ∀ i j : Fin n,
        Ginv i j = ∑ k : Fin n, μ k * (U i k * U j k) := by
    intro i j
    have hUDstar : Ginv = U * (Matrix.diagonal μ) * star U := by
      have := hspec
      simp only [Unitary.conjStarAlgAut_apply] at this
      have hofReal : (RCLike.ofReal ∘ hGinv_herm.eigenvalues :
          Fin n → ℝ) = hGinv_herm.eigenvalues := by
        funext k
        simp
      rw [hofReal] at this
      exact this
    rw [hUDstar]
    rw [Matrix.mul_apply]
    have hUD_entry : ∀ k : Fin n,
        (U * Matrix.diagonal μ) i k = U i k * μ k := by
      intro k
      rw [Matrix.mul_apply]
      rw [Finset.sum_eq_single k]
      · simp [Matrix.diagonal]
      · intro l _ hl
        simp [Matrix.diagonal, hl]
      · intro hk
        exact absurd (Finset.mem_univ k) hk
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [hUD_entry k]
    have hstar : (star U) k j = U j k := by
      simp [Matrix.star_apply, star_trivial]
    rw [hstar]
    ring
  unfold tensorCovDerivPointwiseInner
  change 0 ≤ ∑ i : Fin n, ∑ j : Fin n,
    Ginv i j * tensorInnerPointwise (I := I) (M := M) g r s x (vfam i) (vfam j)
  have hrewrite :
      ∑ i : Fin n, ∑ j : Fin n,
        Ginv i j *
          tensorInnerPointwise (I := I) (M := M) g r s x (vfam i) (vfam j)
        = ∑ k : Fin n, μ k *
          tensorInnerPointwise (I := I) (M := M) g r s x
            (∑ i : Fin n, U i k • vfam i)
            (∑ j : Fin n, U j k • vfam j) := by
    have hsum_left :
        ∀ (A : Finset (Fin n)) (a : Fin n → ℝ)
          (φ : Fin n → TensorRSModel r s ℝ E)
          (T₀ : TensorRSModel r s ℝ E),
          tensorInnerPointwise (I := I) (M := M) g r s x
              (∑ i ∈ A, a i • φ i) T₀
              =
            ∑ i ∈ A,
              tensorInnerPointwise (I := I) (M := M) g r s x
                (a i • φ i) T₀ := by
      intro A a φ T₀
      classical
      induction A using Finset.induction with
      | empty =>
          simp [tensorInnerPointwise_zero_left]
      | insert i A hi ih =>
          rw [Finset.sum_insert hi]
          rw [tensorInnerPointwise_add_left]
          rw [ih]
          rw [Finset.sum_insert hi]
    have hsum_right :
        ∀ (A : Finset (Fin n))
          (S₀ : TensorRSModel r s ℝ E)
          (a : Fin n → ℝ) (φ : Fin n → TensorRSModel r s ℝ E),
          tensorInnerPointwise (I := I) (M := M) g r s x
              S₀ (∑ j ∈ A, a j • φ j)
              =
            ∑ j ∈ A,
              tensorInnerPointwise (I := I) (M := M) g r s x
                S₀ (a j • φ j) := by
      intro A S₀ a φ
      classical
      induction A using Finset.induction with
      | empty =>
          simp [tensorInnerPointwise_zero_right]
      | insert j A hj ih =>
          rw [Finset.sum_insert hj]
          rw [tensorInnerPointwise_add_right]
          rw [ih]
          rw [Finset.sum_insert hj]
    have hbilin :
        ∀ k : Fin n,
          tensorInnerPointwise (I := I) (M := M) g r s x
              (∑ i : Fin n, U i k • vfam i)
              (∑ j : Fin n, U j k • vfam j)
            = ∑ i : Fin n, ∑ j : Fin n,
              U i k * U j k *
                tensorInnerPointwise (I := I) (M := M) g r s x
                  (vfam i) (vfam j) := by
      intro k
      rw [hsum_left Finset.univ (fun i => U i k) vfam
        (∑ j : Fin n, U j k • vfam j)]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [hsum_right Finset.univ (U i k • vfam i) (fun j => U j k) vfam]
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [tensorInnerPointwise_smul_left, tensorInnerPointwise_smul_right]
      ring
    have hRHS :
        ∑ k : Fin n, μ k *
          tensorInnerPointwise (I := I) (M := M) g r s x
            (∑ i : Fin n, U i k • vfam i)
            (∑ j : Fin n, U j k • vfam j)
          = ∑ k : Fin n, ∑ i : Fin n, ∑ j : Fin n,
              (μ k * (U i k * U j k)) *
                tensorInnerPointwise (I := I) (M := M) g r s x
                  (vfam i) (vfam j) := by
      refine Finset.sum_congr rfl ?_
      intro k _
      rw [hbilin k, Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      ring
    rw [hRHS]
    have hLHS :
        ∑ i : Fin n, ∑ j : Fin n,
          Ginv i j *
            tensorInnerPointwise (I := I) (M := M) g r s x (vfam i) (vfam j)
          = ∑ i : Fin n, ∑ j : Fin n,
              ∑ k : Fin n,
                (μ k * (U i k * U j k)) *
                  tensorInnerPointwise (I := I) (M := M) g r s x
                    (vfam i) (vfam j) := by
      refine Finset.sum_congr rfl ?_
      intro i _
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [hGinv_entry i j, Finset.sum_mul]
    rw [hLHS]
    have h_swap_inner :
        ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
            (μ k * (U i k * U j k)) *
              tensorInnerPointwise (I := I) (M := M) g r s x
                (vfam i) (vfam j)
          = ∑ i : Fin n, ∑ k : Fin n, ∑ j : Fin n,
            (μ k * (U i k * U j k)) *
              tensorInnerPointwise (I := I) (M := M) g r s x
                (vfam i) (vfam j) := by
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [Finset.sum_comm]
    rw [h_swap_inner, Finset.sum_comm]
  rw [hrewrite]
  refine Finset.sum_nonneg ?_
  intro k _
  refine mul_nonneg (hμ_nonneg k) ?_
  exact tensorInnerPointwise_nonneg (I := I) (M := M) g r s x
    (∑ i : Fin n, U i k • vfam i)

noncomputable def tensorH1Inner
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) : ℝ :=
  tensorL2Inner (I := I) (M := M) g r s S.toFun T.toFun +
    ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r s S T x
      ∂(riemannianVolumeMeasure (I := I) (M := M) g)

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma tensorH1Inner_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) :
    tensorH1Inner (I := I) (M := M) g r s S T =
      tensorL2Inner (I := I) (M := M) g r s S.toFun T.toFun +
        ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r s S T x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := rfl

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
