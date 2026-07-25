import DifferentialGeometry.Analysis.Spectral.Tensor.Variational.CovDerivPointwise
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

private lemma trace_invariance_under_change_of_basis
    {n : ℕ} (T : Matrix (Fin n) (Fin n) ℝ) (hT : IsUnit T)
    (G : Matrix (Fin n) (Fin n) ℝ) (hG : IsUnit G)
    (B : Matrix (Fin n) (Fin n) ℝ) :
    let G' := Tᵀ * G * T
    let B' := Tᵀ * B * T
    ∑ i : Fin n, ∑ j : Fin n, G'⁻¹ i j * B' i j =
      ∑ i : Fin n, ∑ j : Fin n, G⁻¹ i j * B i j := by
  classical
  simp only
  have hsum_eq : ∀ M N : Matrix (Fin n) (Fin n) ℝ,
      ∑ i : Fin n, ∑ j : Fin n, M i j * N i j = Matrix.trace (M * Nᵀ) := by
    intro M N
    rw [Matrix.trace]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [Matrix.diag_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl ?_
    intro j _
    simp [Matrix.transpose_apply]
  rw [hsum_eq, hsum_eq]
  set G' : Matrix (Fin n) (Fin n) ℝ := Tᵀ * G * T with hG'_def
  have hG'_inv : G'⁻¹ = T⁻¹ * G⁻¹ * (Tᵀ)⁻¹ := by
    rw [hG'_def]
    have hT_unit : IsUnit T := hT
    have hTT_unit : IsUnit Tᵀ := by
      rw [Matrix.isUnit_iff_isUnit_det] at hT ⊢
      simpa [Matrix.det_transpose] using hT
    have hG_unit : IsUnit G := hG
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, mul_assoc]
  rw [hG'_inv]
  set B' : Matrix (Fin n) (Fin n) ℝ := Tᵀ * B * T with hB'_def
  have hB'_trans : B'ᵀ = Tᵀ * Bᵀ * T := by
    rw [hB'_def, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      mul_assoc]
  rw [hB'_trans]
  have hTT_unit : IsUnit Tᵀ := by
    rw [Matrix.isUnit_iff_isUnit_det] at hT ⊢
    simpa [Matrix.det_transpose] using hT
  have hT_inv_T : (Tᵀ)⁻¹ * Tᵀ = 1 := Matrix.nonsing_inv_mul _
    (by simpa [Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose] using hT)
  have hT_T_inv : T * T⁻¹ = 1 := Matrix.mul_nonsing_inv _
    (by simpa [Matrix.isUnit_iff_isUnit_det] using hT)
  have hcyc :
      T⁻¹ * G⁻¹ * (Tᵀ)⁻¹ * (Tᵀ * Bᵀ * T) =
        T⁻¹ * G⁻¹ * ((Tᵀ)⁻¹ * Tᵀ) * Bᵀ * T := by
    repeat rw [mul_assoc]
  rw [hcyc, hT_inv_T, mul_one]
  have hreassoc : T⁻¹ * G⁻¹ * Bᵀ * T = T⁻¹ * (G⁻¹ * Bᵀ * T) := by
    rw [mul_assoc T⁻¹ G⁻¹ Bᵀ, mul_assoc T⁻¹ (G⁻¹ * Bᵀ) T]
  rw [hreassoc, Matrix.trace_mul_comm T⁻¹ (G⁻¹ * Bᵀ * T)]
  rw [mul_assoc (G⁻¹ * Bᵀ) T T⁻¹, hT_T_inv, mul_one]

noncomputable def chartTensorCovDerivPointwiseInner
    (g : SmoothRiemannianMetric I M) (α : M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) (b : M) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
    (chartGramMatrix (I := I) g α b)⁻¹ i j *
      tensorInnerPointwise (I := I) (M := M) g r s b
        (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g r s S b
            (chartBasisVecFiber (I := I) α i b)))
        (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g r s T b
            (chartBasisVecFiber (I := I) α j b)))

private noncomputable def chartBasisTransitionMatrix (α : M) (b : M) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  Matrix.of fun k i =>
    ((chartModelBasis E).repr (chartBasisVecFiber (I := I) α i b)) k

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma chartBasisVecFiber_eq_sum_chartModelBasis
    (α : M) (b : M) (i : Fin (Module.finrank ℝ E)) :
    chartBasisVecFiber (I := I) α i b =
      ∑ k : Fin (Module.finrank ℝ E),
        chartBasisTransitionMatrix (I := I) α b k i • (chartModelBasis E) k := by
  classical
  unfold chartBasisTransitionMatrix
  simp only [Matrix.of_apply]
  exact (((chartModelBasis E).sum_repr
    (chartBasisVecFiber (I := I) α i b))).symm

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma chartBasisTransitionMatrix_eq_toMatrix
    (α : M) (b : M) :
    chartBasisTransitionMatrix (I := I) α b =
      (chartModelBasis E).toMatrix
        (fun i : Fin (Module.finrank ℝ E) =>
          chartBasisVecFiber (I := I) α i b) := by
  classical
  unfold chartBasisTransitionMatrix
  ext k i
  rw [Module.Basis.toMatrix_apply, Matrix.of_apply]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma chartBasisTransitionMatrix_isUnit
    (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    IsUnit (chartBasisTransitionMatrix (I := I) α b) := by
  classical
  rw [chartBasisTransitionMatrix_eq_toMatrix]
  set chartBasis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E :=
    chartBasisFamily (I := I) α hb with hCB_def
  have hfam_eq : (fun i : Fin (Module.finrank ℝ E) =>
      chartBasisVecFiber (I := I) α i b)
      = (chartBasis : Fin (Module.finrank ℝ E) → E) := by
    funext i
    rw [hCB_def]
    exact (chartBasisFamily_apply (I := I) α hb i).symm
  rw [hfam_eq]
  refine ⟨⟨_, chartBasis.toMatrix (chartModelBasis E), ?_, ?_⟩, rfl⟩
  · exact Module.Basis.toMatrix_mul_toMatrix_flip _ _
  · exact Module.Basis.toMatrix_mul_toMatrix_flip _ _

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma g_inner_bilinear_expand
    (g : SmoothRiemannianMetric I M) (b : M) {n : ℕ}
    (a c : Fin n → ℝ) (u : Fin n → E) :
    g.inner b (∑ k : Fin n, a k • u k) (∑ l : Fin n, c l • u l) =
      ∑ k : Fin n, ∑ l : Fin n,
        a k * c l * g.inner b (u k) (u l) := by
  classical
  have houter : g.inner b (∑ k : Fin n, a k • u k) =
      ∑ k : Fin n, a k • (g.inner b (u k)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [map_smul]
  rw [houter, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro l _
  rw [map_smul, smul_eq_mul]
  ring

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma chartGramMatrix_eq_transition
    (g : SmoothRiemannianMetric I M) (α : M) (b : M) :
    chartGramMatrix (I := I) g α b =
      (chartBasisTransitionMatrix (I := I) α b)ᵀ *
        gramMatrixAt (I := I) (M := M) g b *
        chartBasisTransitionMatrix (I := I) α b := by
  classical
  set n := Module.finrank ℝ E with hn_def
  set T : Matrix (Fin n) (Fin n) ℝ :=
    chartBasisTransitionMatrix (I := I) α b with hT_def
  ext i j
  rw [chartGramMatrix_apply]
  rw [chartBasisVecFiber_eq_sum_chartModelBasis (I := I) α b i,
      chartBasisVecFiber_eq_sum_chartModelBasis (I := I) α b j]
  rw [g_inner_bilinear_expand g b
        (fun k => T k i) (fun l => T l j) (chartModelBasis E)]
  rw [Matrix.mul_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro l _
  rw [Matrix.mul_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [Matrix.transpose_apply, gramMatrixAt_apply]
  ring

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma tensorInnerPointwise_sum_left
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M)
    {ι : Type*} (s' : Finset ι) (A : ι → TensorRSModel r s ℝ E)
    (c : ι → ℝ) (B : TensorRSModel r s ℝ E) :
    tensorInnerPointwise (I := I) (M := M) g r s b (∑ k ∈ s', c k • A k) B =
      ∑ k ∈ s', c k *
        tensorInnerPointwise (I := I) (M := M) g r s b (A k) B := by
  classical
  induction s' using Finset.induction with
  | empty =>
      simp [tensorInnerPointwise_zero_left]
  | insert i₀ s'' hi₀ ih =>
      rw [Finset.sum_insert hi₀, tensorInnerPointwise_add_left,
          tensorInnerPointwise_smul_left, ih, Finset.sum_insert hi₀]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma tensorInnerPointwise_sum_right
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M)
    {ι : Type*} (s' : Finset ι) (A : TensorRSModel r s ℝ E)
    (B : ι → TensorRSModel r s ℝ E) (c : ι → ℝ) :
    tensorInnerPointwise (I := I) (M := M) g r s b A (∑ l ∈ s', c l • B l) =
      ∑ l ∈ s', c l *
        tensorInnerPointwise (I := I) (M := M) g r s b A (B l) := by
  classical
  induction s' using Finset.induction with
  | empty =>
      simp [tensorInnerPointwise_zero_right]
  | insert j₀ s'' hj₀ ih =>
      rw [Finset.sum_insert hj₀, tensorInnerPointwise_add_right,
          tensorInnerPointwise_smul_right, ih, Finset.sum_insert hj₀]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma chartTensorCovDeriv_innerMatrix_eq_transition
    (g : SmoothRiemannianMetric I M) (α : M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) (b : M)
    (i j : Fin (Module.finrank ℝ E)) :
    tensorInnerPointwise (I := I) (M := M) g r s b
        (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g r s S b
            (chartBasisVecFiber (I := I) α i b)))
        (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g r s T b
            (chartBasisVecFiber (I := I) α j b))) =
      ((chartBasisTransitionMatrix (I := I) α b)ᵀ *
          (Matrix.of fun k l : Fin (Module.finrank ℝ E) =>
            tensorInnerPointwise (I := I) (M := M) g r s b
              (TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s S b
                  ((chartModelBasis E) k)))
              (TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s T b
                  ((chartModelBasis E) l)))) *
          chartBasisTransitionMatrix (I := I) α b) i j := by
  classical
  set Tmat : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    chartBasisTransitionMatrix (I := I) α b with hTmat_def
  have hexp_i := chartBasisVecFiber_eq_sum_chartModelBasis (I := I) α b i
  have hexp_j := chartBasisVecFiber_eq_sum_chartModelBasis (I := I) α b j
  have hSi : tensorCovDerivAt (I := I) (M := M) g r s S b
        (chartBasisVecFiber (I := I) α i b) =
      ∑ k : Fin (Module.finrank ℝ E), Tmat k i •
        tensorCovDerivAt (I := I) (M := M) g r s S b ((chartModelBasis E) k) := by
    rw [hexp_i]
    unfold tensorCovDerivAt
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [map_smul]
  have hTj : tensorCovDerivAt (I := I) (M := M) g r s T b
        (chartBasisVecFiber (I := I) α j b) =
      ∑ l : Fin (Module.finrank ℝ E), Tmat l j •
        tensorCovDerivAt (I := I) (M := M) g r s T b ((chartModelBasis E) l) := by
    rw [hexp_j]
    unfold tensorCovDerivAt
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro l _
    rw [map_smul]
  rw [hSi, hTj]
  have htoM_sum : ∀ (s' : Finset (Fin (Module.finrank ℝ E)))
      (f : Fin (Module.finrank ℝ E) → TensorRSSpace r s I b)
      (c : Fin (Module.finrank ℝ E) → ℝ),
      TensorRSSpace.toModel (∑ k ∈ s', c k • f k) =
        ∑ k ∈ s', c k • TensorRSSpace.toModel (f k) := by
    intro s' f c
    classical
    induction s' using Finset.induction with
    | empty => simp [TensorRSSpace.toModel_zero]
    | insert i₀ s'' hi₀ ih =>
        rw [Finset.sum_insert hi₀, TensorRSSpace.toModel_add,
            TensorRSSpace.toModel_smul, ih, Finset.sum_insert hi₀]
  have htoM_left := htoM_sum Finset.univ
    (fun k => tensorCovDerivAt (I := I) (M := M) g r s S b ((chartModelBasis E) k))
    (fun k => Tmat k i)
  have htoM_right := htoM_sum Finset.univ
    (fun l => tensorCovDerivAt (I := I) (M := M) g r s T b ((chartModelBasis E) l))
    (fun l => Tmat l j)
  rw [htoM_left, htoM_right]
  rw [tensorInnerPointwise_sum_left (I := I) (M := M) g r s b Finset.univ]
  conv_lhs =>
    rhs
    ext k
    rw [tensorInnerPointwise_sum_right (I := I) (M := M) g r s b Finset.univ]
    rw [Finset.mul_sum]
  rw [Matrix.mul_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [Matrix.mul_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro l _
  rw [Matrix.transpose_apply, Matrix.of_apply]
  ring

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma chartTensorCovDerivPointwiseInner_eq_tensorCovDerivPointwiseInner
    (g : SmoothRiemannianMetric I M) (α : M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    chartTensorCovDerivPointwiseInner (I := I) (M := M) g α r s S T b =
      tensorCovDerivPointwiseInner (I := I) (M := M) g r s S T b := by
  classical
  set n := Module.finrank ℝ E
  set Tmat : Matrix (Fin n) (Fin n) ℝ :=
    chartBasisTransitionMatrix (I := I) α b with hTmat_def
  set Gmat : Matrix (Fin n) (Fin n) ℝ :=
    gramMatrixAt (I := I) (M := M) g b with hGmat_def
  set Bmat : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.of fun k l : Fin n =>
      tensorInnerPointwise (I := I) (M := M) g r s b
        (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g r s S b ((chartModelBasis E) k)))
        (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g r s T b ((chartModelBasis E) l)))
    with hBmat_def
  unfold chartTensorCovDerivPointwiseInner
  unfold tensorCovDerivPointwiseInner
  have hG_eq : chartGramMatrix (I := I) g α b = Tmatᵀ * Gmat * Tmat :=
    chartGramMatrix_eq_transition (I := I) g α b
  have hLHS_term_eq : ∀ i j : Fin n,
      tensorInnerPointwise (I := I) (M := M) g r s b
          (TensorRSSpace.toModel
            (tensorCovDerivAt (I := I) (M := M) g r s S b
              (chartBasisVecFiber (I := I) α i b)))
          (TensorRSSpace.toModel
            (tensorCovDerivAt (I := I) (M := M) g r s T b
              (chartBasisVecFiber (I := I) α j b))) =
        (Tmatᵀ * Bmat * Tmat) i j := by
    intro i j
    exact chartTensorCovDeriv_innerMatrix_eq_transition (I := I) (M := M) g α r s S T b i j
  have hLHS_rewrite :
      ∑ i : Fin n, ∑ j : Fin n,
          (chartGramMatrix (I := I) g α b)⁻¹ i j *
            tensorInnerPointwise (I := I) (M := M) g r s b
              (TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s S b
                  (chartBasisVecFiber (I := I) α i b)))
              (TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s T b
                  (chartBasisVecFiber (I := I) α j b))) =
        ∑ i : Fin n, ∑ j : Fin n,
          (Tmatᵀ * Gmat * Tmat)⁻¹ i j * (Tmatᵀ * Bmat * Tmat) i j := by
    refine Finset.sum_congr rfl ?_
    intro i _
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [hLHS_term_eq i j, hG_eq]
  rw [hLHS_rewrite]
  have hT_unit : IsUnit Tmat := chartBasisTransitionMatrix_isUnit (I := I) α hb
  have hG_unit : IsUnit Gmat := by
    rw [hGmat_def]
    have hinv_herm := gramMatrixAt_inv_isHermitian (I := I) (M := M) g b
    have hpos := gramMatrixAt_inv_posSemidef (I := I) (M := M) g b
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    have hposdef : (gramMatrixAt (I := I) (M := M) g b).PosDef := by
      refine Matrix.PosDef.of_dotProduct_mulVec_pos
        (gramMatrixAt_isHermitian (I := I) (M := M) g b) ?_
      intro v hv
      let w : E := ∑ i : Fin (Module.finrank ℝ E),
        v i • (chartModelBasis E) i
      have hw_ne : w ≠ 0 := by
        intro h
        have hlin : LinearIndependent ℝ ((chartModelBasis E) : Fin _ → E) :=
          (chartModelBasis E).linearIndependent
        rw [Fintype.linearIndependent_iff] at hlin
        exact hv (funext (hlin v h))
      have hquad : star v ⬝ᵥ (gramMatrixAt (I := I) (M := M) g b) *ᵥ v =
          g.inner b w w := by
        have hexp : g.inner b w w =
            ∑ j : Fin (Module.finrank ℝ E),
              v j * ∑ i : Fin (Module.finrank ℝ E),
                v i * gramMatrixAt (I := I) (M := M) g b i j := by
          change g.inner b (∑ i, v i • (chartModelBasis E) i)
              (∑ j, v j • (chartModelBasis E) j) = _
          rw [map_sum]
          refine Finset.sum_congr rfl ?_
          intro j _
          have hsm1 : (g.inner b (∑ i, v i • (chartModelBasis E) i))
                (v j • (chartModelBasis E) j) =
              v j * (g.inner b (∑ i, v i • (chartModelBasis E) i))
                ((chartModelBasis E) j) := by
            rw [map_smul, smul_eq_mul]
          rw [hsm1]
          congr 1
          rw [map_sum, ContinuousLinearMap.sum_apply]
          refine Finset.sum_congr rfl ?_
          intro i _
          have hsm2 : (g.inner b (v i • (chartModelBasis E) i))
                ((chartModelBasis E) j) =
              v i * (g.inner b ((chartModelBasis E) i)) ((chartModelBasis E) j) := by
            rw [show (g.inner b) (v i • (chartModelBasis E) i) =
                v i • (g.inner b) ((chartModelBasis E) i) from by rw [map_smul]]
            rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
          rw [hsm2, gramMatrixAt_apply]
        rw [hexp]
        change ∑ j : Fin (Module.finrank ℝ E),
            star (v j) * (gramMatrixAt (I := I) (M := M) g b *ᵥ v) j =
          ∑ j : Fin (Module.finrank ℝ E),
            v j * ∑ i : Fin (Module.finrank ℝ E),
              v i * gramMatrixAt (I := I) (M := M) g b i j
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [star_trivial]
        rw [show (gramMatrixAt (I := I) (M := M) g b *ᵥ v) j =
              ∑ i : Fin (Module.finrank ℝ E),
                gramMatrixAt (I := I) (M := M) g b j i * v i from rfl]
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => ?_)
        rw [gramMatrixAt_apply, gramMatrixAt_apply, g.symm]
        ring
      rw [hquad]
      exact g.pos b w hw_ne
    have hdet_pos := hposdef.det_pos
    exact ne_of_gt hdet_pos
  exact trace_invariance_under_change_of_basis Tmat hT_unit Gmat hG_unit Bmat

private noncomputable def frameTransitionMatrix
    (frame : Fin (Module.finrank ℝ E) → E) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  Matrix.of fun k i => ((chartModelBasis E).repr (frame i)) k

omit [NeZero (Module.finrank ℝ E)] in
private lemma frame_eq_sum_chartModelBasis
    (frame : Fin (Module.finrank ℝ E) → E) (i : Fin (Module.finrank ℝ E)) :
    frame i =
      ∑ k : Fin (Module.finrank ℝ E),
        frameTransitionMatrix (E := E) frame k i • (chartModelBasis E) k := by
  classical
  unfold frameTransitionMatrix
  simp only [Matrix.of_apply]
  exact ((chartModelBasis E).sum_repr (frame i)).symm

omit [NeZero (Module.finrank ℝ E)] in
private lemma frameTransitionMatrix_isUnit
    (frame : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E) :
    IsUnit (frameTransitionMatrix (E := E)
      (frame : Fin (Module.finrank ℝ E) → E)) := by
  classical
  have hmat : frameTransitionMatrix (E := E)
      (frame : Fin (Module.finrank ℝ E) → E) =
      (chartModelBasis E).toMatrix (frame : Fin (Module.finrank ℝ E) → E) := by
    unfold frameTransitionMatrix
    ext k i
    rw [Module.Basis.toMatrix_apply, Matrix.of_apply]
  rw [hmat]
  refine ⟨⟨_, frame.toMatrix (chartModelBasis E), ?_, ?_⟩, rfl⟩
  · exact Module.Basis.toMatrix_mul_toMatrix_flip _ _
  · exact Module.Basis.toMatrix_mul_toMatrix_flip _ _

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma frameGram_eq_transition
    (g : SmoothRiemannianMetric I M) (b : M)
    (frame : Fin (Module.finrank ℝ E) → E) :
    (Matrix.of fun i j : Fin (Module.finrank ℝ E) =>
        g.inner b (frame i) (frame j)) =
      (frameTransitionMatrix (E := E) frame)ᵀ *
        gramMatrixAt (I := I) (M := M) g b *
        frameTransitionMatrix (E := E) frame := by
  classical
  ext i j
  rw [Matrix.of_apply]
  rw [frame_eq_sum_chartModelBasis (E := E) frame i,
    frame_eq_sum_chartModelBasis (E := E) frame j]
  rw [g_inner_bilinear_expand g b
        (fun k => frameTransitionMatrix (E := E) frame k i)
        (fun l => frameTransitionMatrix (E := E) frame l j) (chartModelBasis E)]
  rw [Matrix.mul_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro l _
  rw [Matrix.mul_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [Matrix.transpose_apply, gramMatrixAt_apply]
  ring

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma frameInnerMatrix_eq_transition
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) (b : M)
    (frame : Fin (Module.finrank ℝ E) → E)
    (i j : Fin (Module.finrank ℝ E)) :
    tensorInnerPointwise (I := I) (M := M) g r s b
        (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g r s S b (frame i)))
        (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g r s T b (frame j))) =
      ((frameTransitionMatrix (E := E) frame)ᵀ *
          (Matrix.of fun k l : Fin (Module.finrank ℝ E) =>
            tensorInnerPointwise (I := I) (M := M) g r s b
              (TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s S b
                  ((chartModelBasis E) k)))
              (TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s T b
                  ((chartModelBasis E) l)))) *
          frameTransitionMatrix (E := E) frame) i j := by
  classical
  have hSi : tensorCovDerivAt (I := I) (M := M) g r s S b (frame i) =
      ∑ k : Fin (Module.finrank ℝ E),
        frameTransitionMatrix (E := E) frame k i •
        tensorCovDerivAt (I := I) (M := M) g r s S b ((chartModelBasis E) k) := by
    rw [frame_eq_sum_chartModelBasis (E := E) frame i]
    unfold tensorCovDerivAt
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [map_smul]
  have hTj : tensorCovDerivAt (I := I) (M := M) g r s T b (frame j) =
      ∑ l : Fin (Module.finrank ℝ E),
        frameTransitionMatrix (E := E) frame l j •
        tensorCovDerivAt (I := I) (M := M) g r s T b ((chartModelBasis E) l) := by
    rw [frame_eq_sum_chartModelBasis (E := E) frame j]
    unfold tensorCovDerivAt
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro l _
    rw [map_smul]
  rw [hSi, hTj]
  have htoM_sum : ∀ (s' : Finset (Fin (Module.finrank ℝ E)))
      (f : Fin (Module.finrank ℝ E) → TensorRSSpace r s I b)
      (c : Fin (Module.finrank ℝ E) → ℝ),
      TensorRSSpace.toModel (∑ k ∈ s', c k • f k) =
        ∑ k ∈ s', c k • TensorRSSpace.toModel (f k) := by
    intro s' f c
    classical
    induction s' using Finset.induction with
    | empty => simp [TensorRSSpace.toModel_zero]
    | insert i₀ s'' hi₀ ih =>
        rw [Finset.sum_insert hi₀, TensorRSSpace.toModel_add,
            TensorRSSpace.toModel_smul, ih, Finset.sum_insert hi₀]
  rw [htoM_sum Finset.univ
        (fun k => tensorCovDerivAt (I := I) (M := M) g r s S b ((chartModelBasis E) k))
        (fun k => frameTransitionMatrix (E := E) frame k i),
      htoM_sum Finset.univ
        (fun l => tensorCovDerivAt (I := I) (M := M) g r s T b ((chartModelBasis E) l))
        (fun l => frameTransitionMatrix (E := E) frame l j)]
  rw [tensorInnerPointwise_sum_left (I := I) (M := M) g r s b Finset.univ]
  conv_lhs =>
    rhs
    ext k
    rw [tensorInnerPointwise_sum_right (I := I) (M := M) g r s b Finset.univ]
    rw [Finset.mul_sum]
  rw [Matrix.mul_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [Matrix.mul_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro l _
  rw [Matrix.transpose_apply, Matrix.of_apply]
  ring

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma tensorCovDerivPointwiseInner_eq_frameGram_sum
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) (b : M)
    (frame : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E) :
    ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        (Matrix.of fun i' j' : Fin (Module.finrank ℝ E) =>
          g.inner b (frame i') (frame j'))⁻¹ i j *
          tensorInnerPointwise (I := I) (M := M) g r s b
            (TensorRSSpace.toModel
              (tensorCovDerivAt (I := I) (M := M) g r s S b (frame i)))
            (TensorRSSpace.toModel
              (tensorCovDerivAt (I := I) (M := M) g r s T b (frame j))) =
      tensorCovDerivPointwiseInner (I := I) (M := M) g r s S T b := by
  classical
  let Tmat : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    frameTransitionMatrix (E := E) (frame : Fin (Module.finrank ℝ E) → E)
  let Gmat : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    gramMatrixAt (I := I) (M := M) g b
  let Bmat : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    Matrix.of fun k l : Fin (Module.finrank ℝ E) =>
      tensorInnerPointwise (I := I) (M := M) g r s b
        (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g r s S b ((chartModelBasis E) k)))
        (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g r s T b ((chartModelBasis E) l)))
  have hG_eq : (Matrix.of fun i' j' : Fin (Module.finrank ℝ E) =>
      g.inner b (frame i') (frame j')) = Tmatᵀ * Gmat * Tmat :=
    frameGram_eq_transition (I := I) (M := M) g b (frame : Fin (Module.finrank ℝ E) → E)
  have hterm : ∀ i j : Fin (Module.finrank ℝ E),
      (Matrix.of fun i' j' : Fin (Module.finrank ℝ E) =>
            g.inner b (frame i') (frame j'))⁻¹ i j *
          tensorInnerPointwise (I := I) (M := M) g r s b
            (TensorRSSpace.toModel
              (tensorCovDerivAt (I := I) (M := M) g r s S b (frame i)))
            (TensorRSSpace.toModel
              (tensorCovDerivAt (I := I) (M := M) g r s T b (frame j))) =
        (Tmatᵀ * Gmat * Tmat)⁻¹ i j * (Tmatᵀ * Bmat * Tmat) i j := by
    intro i j
    rw [frameInnerMatrix_eq_transition (I := I) (M := M) g r s S T b
      (frame : Fin (Module.finrank ℝ E) → E) i j, hG_eq]
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hterm i j))]
  unfold tensorCovDerivPointwiseInner
  have hT_unit : IsUnit Tmat := frameTransitionMatrix_isUnit (E := E) frame
  have hG_unit : IsUnit Gmat := by
    have hGmat_def : Gmat = gramMatrixAt (I := I) (M := M) g b := rfl
    rw [hGmat_def, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    have hposdef : (gramMatrixAt (I := I) (M := M) g b).PosDef := by
      refine Matrix.PosDef.of_dotProduct_mulVec_pos
        (gramMatrixAt_isHermitian (I := I) (M := M) g b) ?_
      intro v hv
      let w : E := ∑ i : Fin (Module.finrank ℝ E),
        v i • (chartModelBasis E) i
      have hw_ne : w ≠ 0 := by
        intro h
        have hlin : LinearIndependent ℝ ((chartModelBasis E) : Fin _ → E) :=
          (chartModelBasis E).linearIndependent
        rw [Fintype.linearIndependent_iff] at hlin
        exact hv (funext (hlin v h))
      have hquad : star v ⬝ᵥ (gramMatrixAt (I := I) (M := M) g b) *ᵥ v =
          g.inner b w w := by
        have hexp : g.inner b w w =
            ∑ j : Fin (Module.finrank ℝ E),
              v j * ∑ i : Fin (Module.finrank ℝ E),
                v i * gramMatrixAt (I := I) (M := M) g b i j := by
          change g.inner b (∑ i, v i • (chartModelBasis E) i)
              (∑ j, v j • (chartModelBasis E) j) = _
          rw [map_sum]
          refine Finset.sum_congr rfl ?_
          intro j _
          have hsm1 : (g.inner b (∑ i, v i • (chartModelBasis E) i))
                (v j • (chartModelBasis E) j) =
              v j * (g.inner b (∑ i, v i • (chartModelBasis E) i))
                ((chartModelBasis E) j) := by
            rw [map_smul, smul_eq_mul]
          rw [hsm1]
          congr 1
          rw [map_sum, ContinuousLinearMap.sum_apply]
          refine Finset.sum_congr rfl ?_
          intro i _
          have hsm2 : (g.inner b (v i • (chartModelBasis E) i))
                ((chartModelBasis E) j) =
              v i * (g.inner b ((chartModelBasis E) i)) ((chartModelBasis E) j) := by
            rw [show (g.inner b) (v i • (chartModelBasis E) i) =
                v i • (g.inner b) ((chartModelBasis E) i) from by rw [map_smul]]
            rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
          rw [hsm2, gramMatrixAt_apply]
        rw [hexp]
        change ∑ j : Fin (Module.finrank ℝ E),
            star (v j) * (gramMatrixAt (I := I) (M := M) g b *ᵥ v) j =
          ∑ j : Fin (Module.finrank ℝ E),
            v j * ∑ i : Fin (Module.finrank ℝ E),
              v i * gramMatrixAt (I := I) (M := M) g b i j
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [star_trivial]
        rw [show (gramMatrixAt (I := I) (M := M) g b *ᵥ v) j =
              ∑ i : Fin (Module.finrank ℝ E),
                gramMatrixAt (I := I) (M := M) g b j i * v i from rfl]
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => ?_)
        rw [gramMatrixAt_apply, gramMatrixAt_apply, g.symm]
        ring
      rw [hquad]
      exact g.pos b w hw_ne
    exact ne_of_gt hposdef.det_pos
  exact trace_invariance_under_change_of_basis Tmat hT_unit Gmat hG_unit Bmat

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma tensorCovDerivPointwiseInner_eq_orthoFrame_diag_sum
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) (b : M)
    (frame : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (horth : ∀ i j, g.inner b (frame i) (frame j) = if i = j then (1 : ℝ) else 0) :
    tensorCovDerivPointwiseInner (I := I) (M := M) g r s S T b =
      ∑ i : Fin (Module.finrank ℝ E),
        tensorInnerPointwise (I := I) (M := M) g r s b
          (TensorRSSpace.toModel
            (tensorCovDerivAt (I := I) (M := M) g r s S b (frame i)))
          (TensorRSSpace.toModel
            (tensorCovDerivAt (I := I) (M := M) g r s T b (frame i))) := by
  classical
  have hGframe_eq_one :
      (Matrix.of fun i' j' : Fin (Module.finrank ℝ E) =>
        g.inner b (frame i') (frame j')) =
        (1 : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ) := by
    ext i j
    rw [Matrix.of_apply, horth i j, Matrix.one_apply]
  rw [← tensorCovDerivPointwiseInner_eq_frameGram_sum (I := I) (M := M) g r s S T b
    frame]
  rw [hGframe_eq_one, inv_one]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [Finset.sum_eq_single i]
  · rw [Matrix.one_apply_eq, one_mul]
  · intro j _ hji
    rw [Matrix.one_apply_ne (Ne.symm hji), zero_mul]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
