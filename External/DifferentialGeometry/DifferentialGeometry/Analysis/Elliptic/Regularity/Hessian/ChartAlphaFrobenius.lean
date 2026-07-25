import DifferentialGeometry.Analysis.Elliptic.Regularity.Hessian.ChartAlphaMatrix


noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function FiberBundle
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace HessianChartAlphaFrobenius

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPerChartWitness
open DifferentialGeometry.Analysis.Laplacian.HessianLpClass
open DifferentialGeometry.Analysis.Laplacian.HessianPairingChart
open DifferentialGeometry.Analysis.Laplacian.HessianPairingLapDom
open DifferentialGeometry.Analysis.Laplacian.HessianBridge
open DifferentialGeometry.Analysis.Laplacian.HessianTensorChartSmooth
open DifferentialGeometry.Analysis.Laplacian.HessianChartInvariance
open DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaMatrix
open DifferentialGeometry.Analysis.Sobolev.Chart

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private noncomputable def chartAlphaCoBchange
    (α : M) (x : M) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  Matrix.of fun i k =>
    (chartModelBasis E).repr
      ((chartBasisVecFiber (I := I) α i x : TangentSpace I x)) k

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
@[simp] private lemma chartAlphaCoBchange_apply
    (α : M) (x : M) (i k : Fin (Module.finrank ℝ E)) :
    chartAlphaCoBchange (I := I) α x i k =
      (chartModelBasis E).repr
        ((chartBasisVecFiber (I := I) α i x : TangentSpace I x)) k := rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma chartBasisVecFiber_decompose_in_modelBasis
    (α : M) (x : M) (i : Fin (Module.finrank ℝ E)) :
    (chartBasisVecFiber (I := I) α i x : TangentSpace I x) =
      ∑ k : Fin (Module.finrank ℝ E),
        chartAlphaCoBchange (I := I) α x i k •
          ((chartModelBasis E) k : TangentSpace I x) := by
  classical
  have h := (chartModelBasis E).sum_repr
    (chartBasisVecFiber (I := I) α i x : TangentSpace I x)
  exact h.symm

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma clm_bilinear_expand_two_sums
    {x : M} (Hb : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (n : ℕ)
    (c : Fin n → ℝ) (d : Fin n → ℝ)
    (u w : Fin n → TangentSpace I x) :
    Hb (∑ i : Fin n, c i • u i) (∑ j : Fin n, d j • w j) =
      ∑ i : Fin n, ∑ j : Fin n,
        c i * d j * Hb (u i) (w j) := by
  classical
  have h_outer : Hb (∑ i : Fin n, c i • u i) =
      ∑ i : Fin n, c i • Hb (u i) := by
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [Hb.map_smul]
  rw [h_outer]
  rw [ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
  have h_inner : Hb (u i) (∑ j : Fin n, d j • w j) =
      ∑ j : Fin n, d j * Hb (u i) (w j) := by
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [(Hb (u i)).map_smul]
    rw [smul_eq_mul]
  rw [h_inner]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j _
  ring

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma g_inner_bilinear_expand_two_sums
    (g : SmoothRiemannianMetric I M) (x : M)
    (n : ℕ)
    (c : Fin n → ℝ) (d : Fin n → ℝ)
    (u w : Fin n → TangentSpace I x) :
    g.inner x (∑ i : Fin n, c i • u i) (∑ j : Fin n, d j • w j) =
      ∑ i : Fin n, ∑ j : Fin n,
        c i * d j * g.inner x (u i) (w j) :=
  clm_bilinear_expand_two_sums (I := I) (g.inner x) n c d u w

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma chartGramMatrix_alpha_eq_PGPt
    (g : SmoothRiemannianMetric I M) (α : M) (x : M)
    (i j : Fin (Module.finrank ℝ E)) :
    chartGramMatrix (I := I) g α x i j =
      ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        chartAlphaCoBchange (I := I) α x i k *
          chartAlphaCoBchange (I := I) α x j l *
          chartGramMatrix (I := I) g x x k l := by
  classical
  have hi := chartBasisVecFiber_decompose_in_modelBasis (I := I) α x i
  have hj := chartBasisVecFiber_decompose_in_modelBasis (I := I) α x j
  have h_expand :
      g.inner x (chartBasisVecFiber (I := I) α i x)
        (chartBasisVecFiber (I := I) α j x) =
      ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        chartAlphaCoBchange (I := I) α x i k *
          chartAlphaCoBchange (I := I) α x j l *
          g.inner x ((chartModelBasis E) k) ((chartModelBasis E) l) := by
    conv_lhs => rw [hi, hj]
    exact clm_bilinear_expand_two_sums (I := I) (g.inner x) (Module.finrank ℝ E)
      (fun k => chartAlphaCoBchange (I := I) α x i k)
      (fun l => chartAlphaCoBchange (I := I) α x j l)
      (fun k => (chartModelBasis E) k)
      (fun l => (chartModelBasis E) l)
  rw [chartGramMatrix_apply]
  rw [h_expand]
  refine Finset.sum_congr rfl ?_
  intro k _
  refine Finset.sum_congr rfl ?_
  intro l _
  have h_inner : g.inner x ((chartModelBasis E) k : TangentSpace I x)
      ((chartModelBasis E) l : TangentSpace I x) =
      chartGramMatrix (I := I) g x x k l := by
    rw [chartGramMatrix_apply]
    rw [chartBasisVecFiber_self (I := I) x k]
    rw [chartBasisVecFiber_self (I := I) x l]
  rw [h_inner]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma chartGramMatrix_alpha_eq_PGPt_matrix
    (g : SmoothRiemannianMetric I M) (α : M) (x : M) :
    chartGramMatrix (I := I) g α x =
      chartAlphaCoBchange (I := I) α x *
        chartGramMatrix (I := I) g x x *
        (chartAlphaCoBchange (I := I) α x).transpose := by
  classical
  ext i j
  rw [chartGramMatrix_alpha_eq_PGPt (I := I) g α x i j]
  rw [Matrix.mul_apply]
  have h_inner : ∀ k : Fin (Module.finrank ℝ E),
      (chartAlphaCoBchange (I := I) α x *
          chartGramMatrix (I := I) g x x) i k *
        (chartAlphaCoBchange (I := I) α x).transpose k j =
      ∑ l : Fin (Module.finrank ℝ E),
        chartAlphaCoBchange (I := I) α x i l *
          chartGramMatrix (I := I) g x x l k *
          chartAlphaCoBchange (I := I) α x j k := by
    intro k
    rw [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [show (∑ k, (chartAlphaCoBchange (I := I) α x *
            chartGramMatrix (I := I) g x x) i k *
        (chartAlphaCoBchange (I := I) α x).transpose k j) =
      ∑ k, ∑ l,
        chartAlphaCoBchange (I := I) α x i l *
          chartGramMatrix (I := I) g x x l k *
          chartAlphaCoBchange (I := I) α x j k from
    Finset.sum_congr rfl (fun k _ => h_inner k)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro l _
  refine Finset.sum_congr rfl ?_
  intro k _
  ring

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma chartGramMatrix_alpha_isUnit
    (g : SmoothRiemannianMetric I M) (α : M) {x : M}
    (hx : x ∈ (chartAt H α).source) :
    IsUnit (chartGramMatrix (I := I) g α x).det := by
  have hbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact hx
  have hpos := chartGramMatrix_posDef (I := I) g α hbase
  exact isUnit_iff_ne_zero.mpr (ne_of_gt hpos.det_pos)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma chartGramMatrix_x_isUnit
    (g : SmoothRiemannianMetric I M) (x : M) :
    IsUnit (chartGramMatrix (I := I) g x x).det := by
  have hbase : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x
  have hpos := chartGramMatrix_posDef (I := I) g x hbase
  exact isUnit_iff_ne_zero.mpr (ne_of_gt hpos.det_pos)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma chartAlphaCoBchange_isUnit
    (g : SmoothRiemannianMetric I M) (α : M) {x : M}
    (hx : x ∈ (chartAt H α).source) :
    IsUnit (chartAlphaCoBchange (I := I) α x).det := by
  classical
  have h_mat := chartGramMatrix_alpha_eq_PGPt_matrix (I := I) g α x
  have h_det : (chartGramMatrix (I := I) g α x).det =
      (chartAlphaCoBchange (I := I) α x).det *
        (chartGramMatrix (I := I) g x x).det *
        (chartAlphaCoBchange (I := I) α x).transpose.det := by
    rw [h_mat]
    rw [Matrix.det_mul, Matrix.det_mul]
  have h_det' : (chartGramMatrix (I := I) g α x).det =
      (chartAlphaCoBchange (I := I) α x).det^2 *
        (chartGramMatrix (I := I) g x x).det := by
    rw [h_det, Matrix.det_transpose]; ring
  have h_alpha := chartGramMatrix_alpha_isUnit (I := I) g α hx
  have h_x := chartGramMatrix_x_isUnit (I := I) g x
  have h_alpha_ne : (chartGramMatrix (I := I) g α x).det ≠ 0 :=
    h_alpha.ne_zero
  have h_x_ne : (chartGramMatrix (I := I) g x x).det ≠ 0 :=
    h_x.ne_zero
  rw [h_det'] at h_alpha_ne
  have hAne : (chartAlphaCoBchange (I := I) α x).det ≠ 0 := by
    intro hA0
    apply h_alpha_ne
    rw [hA0]
    ring
  exact isUnit_iff_ne_zero.mpr hAne

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma PT_chartInvGram_alpha_P_eq_chartInvGram_x
    (g : SmoothRiemannianMetric I M) (α : M) {x : M}
    (hx : x ∈ (chartAt H α).source) :
    (chartAlphaCoBchange (I := I) α x).transpose *
        chartInvGramMatrix (I := I) g α x *
        chartAlphaCoBchange (I := I) α x =
      chartInvGramMatrix (I := I) g x x := by
  classical
  set P : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    chartAlphaCoBchange (I := I) α x with hP_def
  set Gα : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    chartGramMatrix (I := I) g α x with hGα_def
  set Gx : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    chartGramMatrix (I := I) g x x with hGx_def
  have h_GalphaPGP : Gα = P * Gx * P.transpose :=
    chartGramMatrix_alpha_eq_PGPt_matrix (I := I) g α x
  have h_Galpha_det : IsUnit Gα.det := chartGramMatrix_alpha_isUnit (I := I) g α hx
  have h_Gx_det : IsUnit Gx.det := chartGramMatrix_x_isUnit (I := I) g x
  have h_P_det : IsUnit P.det := chartAlphaCoBchange_isUnit (I := I) g α hx
  have h_PT_det : IsUnit P.transpose.det := by
    rw [Matrix.det_transpose]; exact h_P_det
  have h_Galpha_inv : chartInvGramMatrix (I := I) g α x * Gα = 1 := by
    have hbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
      rw [trivializationAt_baseSet_eq_chartAt_source]
      exact hx
    exact chartInvGramMatrix_mul_chartGramMatrix (I := I) g α hbase
  have h_Gx_inv : chartInvGramMatrix (I := I) g x x * Gx = 1 := by
    have hbase : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
      FiberBundle.mem_baseSet_trivializationAt' x
    exact chartInvGramMatrix_mul_chartGramMatrix (I := I) g x hbase
  have h_target : (P.transpose * chartInvGramMatrix (I := I) g α x * P) * Gx = 1 := by
    have h_PGx_eq : P * Gx = Gα * P.transpose⁻¹ := by
      have h := h_GalphaPGP
      have h_PT_inv_right :
          Gα * P.transpose⁻¹ = P * Gx * P.transpose * P.transpose⁻¹ := by
        rw [h]
      rw [Matrix.mul_assoc] at h_PT_inv_right
      have h_PT_inv : P.transpose * P.transpose⁻¹ = 1 :=
        Matrix.mul_nonsing_inv _ h_PT_det
      rw [h_PT_inv] at h_PT_inv_right
      rw [Matrix.mul_one] at h_PT_inv_right
      exact h_PT_inv_right.symm
    rw [Matrix.mul_assoc P.transpose (chartInvGramMatrix (I := I) g α x) P]
    rw [Matrix.mul_assoc P.transpose (chartInvGramMatrix (I := I) g α x * P) Gx]
    rw [Matrix.mul_assoc (chartInvGramMatrix (I := I) g α x) P Gx]
    rw [h_PGx_eq]
    rw [show chartInvGramMatrix (I := I) g α x * (Gα * P.transpose⁻¹) =
        (chartInvGramMatrix (I := I) g α x * Gα) * P.transpose⁻¹ from
      (Matrix.mul_assoc _ _ _).symm]
    rw [h_Galpha_inv]
    rw [Matrix.one_mul]
    exact Matrix.mul_nonsing_inv P.transpose h_PT_det
  have h_target' : Gx * (P.transpose * chartInvGramMatrix (I := I) g α x * P) = 1 :=
    (mul_eq_one_comm).mp h_target
  have h_inv : (P.transpose * chartInvGramMatrix (I := I) g α x * P) = Gx⁻¹ :=
    (Matrix.inv_eq_right_inv h_target').symm
  rw [h_inv]
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma sum_chartAlphaCoBchange_chartInvGramMatrix_alpha
    (g : SmoothRiemannianMetric I M) (α : M) {x : M}
    (hx : x ∈ (chartAt H α).source) (a c : Fin (Module.finrank ℝ E)) :
    ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        chartAlphaCoBchange (I := I) α x i a *
          chartInvGramMatrix (I := I) g α x i k *
          chartAlphaCoBchange (I := I) α x k c =
      chartInvGramMatrix (I := I) g x x a c := by
  classical
  have h := PT_chartInvGram_alpha_P_eq_chartInvGram_x (I := I) g α hx
  have h_apply : (chartAlphaCoBchange (I := I) α x).transpose *
      chartInvGramMatrix (I := I) g α x *
      chartAlphaCoBchange (I := I) α x =
        chartInvGramMatrix (I := I) g x x := h
  have h_entry : ((chartAlphaCoBchange (I := I) α x).transpose *
      chartInvGramMatrix (I := I) g α x *
      chartAlphaCoBchange (I := I) α x) a c =
        chartInvGramMatrix (I := I) g x x a c := by
    rw [h_apply]
  rw [Matrix.mul_apply] at h_entry
  have h_expand : ∀ k : Fin (Module.finrank ℝ E),
      ((chartAlphaCoBchange (I := I) α x).transpose *
          chartInvGramMatrix (I := I) g α x) a k *
        chartAlphaCoBchange (I := I) α x k c =
      ∑ i : Fin (Module.finrank ℝ E),
        chartAlphaCoBchange (I := I) α x i a *
          chartInvGramMatrix (I := I) g α x i k *
          chartAlphaCoBchange (I := I) α x k c := by
    intro k
    rw [Matrix.mul_apply]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [Matrix.transpose_apply]
  rw [show (∑ k : Fin (Module.finrank ℝ E),
        ((chartAlphaCoBchange (I := I) α x).transpose *
          chartInvGramMatrix (I := I) g α x) a k *
        chartAlphaCoBchange (I := I) α x k c) =
      ∑ k : Fin (Module.finrank ℝ E),
        ∑ i : Fin (Module.finrank ℝ E),
          chartAlphaCoBchange (I := I) α x i a *
            chartInvGramMatrix (I := I) g α x i k *
            chartAlphaCoBchange (I := I) α x k c from
    Finset.sum_congr rfl (fun k _ => h_expand k)] at h_entry
  rw [Finset.sum_comm] at h_entry
  exact h_entry

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma chartHessianTensor_alpha_eq_P_chartHessianTensor_x
    (g : SmoothRiemannianMetric I M) (α : M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) {x : M} (hx : x ∈ (chartAt H α).source)
    (i j : Fin (Module.finrank ℝ E)) :
    chartHessianTensor (I := I) g α f i j x =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        chartAlphaCoBchange (I := I) α x i a *
          chartAlphaCoBchange (I := I) α x j b *
          chartHessianTensor (I := I) g x f a b x := by
  classical
  have hM_alpha : chartAlphaMatrixIdentity (I := I) (M := M) g α f x :=
    chartAlphaMatrixIdentity_holds_chartSource (I := I) g α hf hx
  rw [← hM_alpha i j]
  have hi := chartBasisVecFiber_decompose_in_modelBasis (I := I) α x i
  have hj := chartBasisVecFiber_decompose_in_modelBasis (I := I) α x j
  have hM_x : chartHessianMatrixIdentity (I := I) g f x :=
    chartHessianMatrixIdentity_holds (I := I) g hf x
  have h_expand :
      abstractHessian (I := I) g f x
        (chartBasisVecFiber (I := I) α i x)
        (chartBasisVecFiber (I := I) α j x) =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        chartAlphaCoBchange (I := I) α x i a *
          chartAlphaCoBchange (I := I) α x j b *
          abstractHessian (I := I) g f x
            ((chartModelBasis E) a) ((chartModelBasis E) b) := by
    conv_lhs => rw [hi, hj]
    exact clm_bilinear_expand_two_sums (I := I)
      (abstractHessian (I := I) g f x)
      (Module.finrank ℝ E)
      (fun a => chartAlphaCoBchange (I := I) α x i a)
      (fun b => chartAlphaCoBchange (I := I) α x j b)
      (fun a => (chartModelBasis E) a)
      (fun b => (chartModelBasis E) b)
  rw [h_expand]
  refine Finset.sum_congr rfl ?_
  intro a _
  refine Finset.sum_congr rfl ?_
  intro b _
  rw [hM_x a b]

private lemma nested_sum_perm
    {n : ℕ} (f : Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
        ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n,
          f i j k l a b c d) =
      (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n,
        ∑ i : Fin n, ∑ k : Fin n, ∑ j : Fin n, ∑ l : Fin n,
          f i j k l a b c d) := by
  classical
  rw [show (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
        ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n,
          f i j k l a b c d) =
      ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ a : Fin n, ∑ l : Fin n,
        ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n,
          f i j k l a b c d from by
    refine Finset.sum_congr rfl ?_
    intro i _
    refine Finset.sum_congr rfl ?_
    intro j _
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [Finset.sum_comm]]
  rw [show (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ a : Fin n, ∑ l : Fin n,
        ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n,
          f i j k l a b c d) =
      ∑ i : Fin n, ∑ j : Fin n, ∑ a : Fin n, ∑ k : Fin n, ∑ l : Fin n,
        ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n,
          f i j k l a b c d from by
    refine Finset.sum_congr rfl ?_
    intro i _
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [Finset.sum_comm]]
  rw [show (∑ i : Fin n, ∑ j : Fin n, ∑ a : Fin n, ∑ k : Fin n, ∑ l : Fin n,
        ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n,
          f i j k l a b c d) =
      ∑ i : Fin n, ∑ a : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
        ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n,
          f i j k l a b c d from by
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [Finset.sum_comm]]
  rw [show (∑ i : Fin n, ∑ a : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
        ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n,
          f i j k l a b c d) =
      ∑ a : Fin n, ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
        ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n,
          f i j k l a b c d from by
    rw [Finset.sum_comm]]
  rw [show (∑ a : Fin n, ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
        ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n,
          f i j k l a b c d) =
      ∑ a : Fin n, ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ b : Fin n, ∑ l : Fin n,
        ∑ c : Fin n, ∑ d : Fin n,
          f i j k l a b c d from by
    refine Finset.sum_congr rfl ?_
    intro a _
    refine Finset.sum_congr rfl ?_
    intro i _
    refine Finset.sum_congr rfl ?_
    intro j _
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [Finset.sum_comm]]
  rw [show (∑ a : Fin n, ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ b : Fin n, ∑ l : Fin n,
        ∑ c : Fin n, ∑ d : Fin n,
          f i j k l a b c d) =
      ∑ a : Fin n, ∑ i : Fin n, ∑ j : Fin n, ∑ b : Fin n, ∑ k : Fin n, ∑ l : Fin n,
        ∑ c : Fin n, ∑ d : Fin n,
          f i j k l a b c d from by
    refine Finset.sum_congr rfl ?_
    intro a _
    refine Finset.sum_congr rfl ?_
    intro i _
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [Finset.sum_comm]]
  rw [show (∑ a : Fin n, ∑ i : Fin n, ∑ j : Fin n, ∑ b : Fin n, ∑ k : Fin n, ∑ l : Fin n,
        ∑ c : Fin n, ∑ d : Fin n,
          f i j k l a b c d) =
      ∑ a : Fin n, ∑ i : Fin n, ∑ b : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
        ∑ c : Fin n, ∑ d : Fin n,
          f i j k l a b c d from by
    refine Finset.sum_congr rfl ?_
    intro a _
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [Finset.sum_comm]]
  rw [show (∑ a : Fin n, ∑ i : Fin n, ∑ b : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
        ∑ c : Fin n, ∑ d : Fin n,
          f i j k l a b c d) =
      ∑ a : Fin n, ∑ b : Fin n, ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
        ∑ c : Fin n, ∑ d : Fin n,
          f i j k l a b c d from by
    refine Finset.sum_congr rfl ?_
    intro a _
    rw [Finset.sum_comm]]
  rw [show (∑ a : Fin n, ∑ b : Fin n, ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
        ∑ c : Fin n, ∑ d : Fin n,
          f i j k l a b c d) =
      ∑ a : Fin n, ∑ b : Fin n, ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ c : Fin n,
        ∑ l : Fin n, ∑ d : Fin n,
          f i j k l a b c d from by
    refine Finset.sum_congr rfl ?_
    intro a _
    refine Finset.sum_congr rfl ?_
    intro b _
    refine Finset.sum_congr rfl ?_
    intro i _
    refine Finset.sum_congr rfl ?_
    intro j _
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [Finset.sum_comm]]
  rw [show (∑ a : Fin n, ∑ b : Fin n, ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ c : Fin n,
        ∑ l : Fin n, ∑ d : Fin n,
          f i j k l a b c d) =
      ∑ a : Fin n, ∑ b : Fin n, ∑ i : Fin n, ∑ j : Fin n, ∑ c : Fin n, ∑ k : Fin n,
        ∑ l : Fin n, ∑ d : Fin n,
          f i j k l a b c d from by
    refine Finset.sum_congr rfl ?_
    intro a _
    refine Finset.sum_congr rfl ?_
    intro b _
    refine Finset.sum_congr rfl ?_
    intro i _
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [Finset.sum_comm]]
  rw [show (∑ a : Fin n, ∑ b : Fin n, ∑ i : Fin n, ∑ j : Fin n, ∑ c : Fin n, ∑ k : Fin n,
        ∑ l : Fin n, ∑ d : Fin n,
          f i j k l a b c d) =
      ∑ a : Fin n, ∑ b : Fin n, ∑ i : Fin n, ∑ c : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        ∑ l : Fin n, ∑ d : Fin n,
          f i j k l a b c d from by
    refine Finset.sum_congr rfl ?_
    intro a _
    refine Finset.sum_congr rfl ?_
    intro b _
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [Finset.sum_comm]]
  rw [show (∑ a : Fin n, ∑ b : Fin n, ∑ i : Fin n, ∑ c : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        ∑ l : Fin n, ∑ d : Fin n,
          f i j k l a b c d) =
      ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        ∑ l : Fin n, ∑ d : Fin n,
          f i j k l a b c d from by
    refine Finset.sum_congr rfl ?_
    intro a _
    refine Finset.sum_congr rfl ?_
    intro b _
    rw [Finset.sum_comm]]
  rw [show (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        ∑ l : Fin n, ∑ d : Fin n,
          f i j k l a b c d) =
      ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        ∑ d : Fin n, ∑ l : Fin n,
          f i j k l a b c d from by
    refine Finset.sum_congr rfl ?_
    intro a _
    refine Finset.sum_congr rfl ?_
    intro b _
    refine Finset.sum_congr rfl ?_
    intro c _
    refine Finset.sum_congr rfl ?_
    intro i _
    refine Finset.sum_congr rfl ?_
    intro j _
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [Finset.sum_comm]]
  rw [show (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        ∑ d : Fin n, ∑ l : Fin n,
          f i j k l a b c d) =
      ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ i : Fin n, ∑ j : Fin n, ∑ d : Fin n,
        ∑ k : Fin n, ∑ l : Fin n,
          f i j k l a b c d from by
    refine Finset.sum_congr rfl ?_
    intro a _
    refine Finset.sum_congr rfl ?_
    intro b _
    refine Finset.sum_congr rfl ?_
    intro c _
    refine Finset.sum_congr rfl ?_
    intro i _
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [Finset.sum_comm]]
  rw [show (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ i : Fin n, ∑ j : Fin n, ∑ d : Fin n,
        ∑ k : Fin n, ∑ l : Fin n,
          f i j k l a b c d) =
      ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ i : Fin n, ∑ d : Fin n, ∑ j : Fin n,
        ∑ k : Fin n, ∑ l : Fin n,
          f i j k l a b c d from by
    refine Finset.sum_congr rfl ?_
    intro a _
    refine Finset.sum_congr rfl ?_
    intro b _
    refine Finset.sum_congr rfl ?_
    intro c _
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [Finset.sum_comm]]
  rw [show (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ i : Fin n, ∑ d : Fin n, ∑ j : Fin n,
        ∑ k : Fin n, ∑ l : Fin n,
          f i j k l a b c d) =
      ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n, ∑ i : Fin n, ∑ j : Fin n,
        ∑ k : Fin n, ∑ l : Fin n,
          f i j k l a b c d from by
    refine Finset.sum_congr rfl ?_
    intro a _
    refine Finset.sum_congr rfl ?_
    intro b _
    refine Finset.sum_congr rfl ?_
    intro c _
    rw [Finset.sum_comm]]
  refine Finset.sum_congr rfl ?_
  intro a _
  refine Finset.sum_congr rfl ?_
  intro b _
  refine Finset.sum_congr rfl ?_
  intro c _
  refine Finset.sum_congr rfl ?_
  intro d _
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [Finset.sum_comm]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem chartFrobeniusInvariance_holds
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) {x : M}
    (hx : x ∈ (chartAt H α).source) :
    chartFrobeniusInvariance (I := I) (M := M) g α f x := by
  classical
  set n := Module.finrank ℝ E with hn_def
  set Gα : Fin n → Fin n → ℝ :=
    fun i k => chartInvGramMatrix (I := I) g α x i k with hGα_def
  set Gx : Fin n → Fin n → ℝ :=
    fun a c => chartInvGramMatrix (I := I) g x x a c with hGx_def
  set Hα : Fin n → Fin n → ℝ :=
    fun i j => chartHessianTensor (I := I) g α f i j x with hHα_def
  set Hx : Fin n → Fin n → ℝ :=
    fun a b => chartHessianTensor (I := I) g x f a b x with hHx_def
  set P : Fin n → Fin n → ℝ :=
    fun i a => chartAlphaCoBchange (I := I) α x i a with hP_def
  have h_inverse : ∀ a c : Fin n,
      ∑ i : Fin n, ∑ k : Fin n, P i a * Gα i k * P k c = Gx a c :=
    fun a c => sum_chartAlphaCoBchange_chartInvGramMatrix_alpha (I := I) g α hx a c
  have h_H : ∀ i j : Fin n,
      Hα i j = ∑ a : Fin n, ∑ b : Fin n, P i a * P j b * Hx a b :=
    fun i j => chartHessianTensor_alpha_eq_P_chartHessianTensor_x (I := I) g α hf hx i j
  rw [chartFrobeniusInvariance_def]
  rw [chartHessFrobeniusSqOnChartAlpha_def, chartHessFrobeniusSq_def]
  change (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
            Gα i k * Gα j l * Hα i j * Hα k l) =
         (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n,
            Gx a c * Gx b d * Hx a b * Hx c d)
  have h_LHS_eq : (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
        Gα i k * Gα j l * Hα i j * Hα k l) =
      (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
        ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n,
          (P i a * Gα i k * P k c) * (P j b * Gα j l * P l d) *
            Hx a b * Hx c d) := by
    refine Finset.sum_congr rfl ?_
    intro i _
    refine Finset.sum_congr rfl ?_
    intro j _
    refine Finset.sum_congr rfl ?_
    intro k _
    refine Finset.sum_congr rfl ?_
    intro l _
    rw [h_H i j, h_H k l]
    have h_step1 : Gα i k * Gα j l * (∑ a : Fin n, ∑ b : Fin n, P i a * P j b * Hx a b) *
            (∑ c : Fin n, ∑ d : Fin n, P k c * P l d * Hx c d) =
        ∑ a : Fin n,
          Gα i k * Gα j l * (∑ b : Fin n, P i a * P j b * Hx a b) *
            (∑ c : Fin n, ∑ d : Fin n, P k c * P l d * Hx c d) := by
      conv_lhs =>
        rw [show (Gα i k * Gα j l * (∑ a : Fin n, ∑ b : Fin n, P i a * P j b * Hx a b)) =
              ∑ a : Fin n, Gα i k * Gα j l * (∑ b : Fin n, P i a * P j b * Hx a b) from by
          rw [Finset.mul_sum]]
      rw [Finset.sum_mul]
    rw [h_step1]
    refine Finset.sum_congr rfl ?_
    intro a _
    have h_step2 : Gα i k * Gα j l * (∑ b : Fin n, P i a * P j b * Hx a b) *
            (∑ c : Fin n, ∑ d : Fin n, P k c * P l d * Hx c d) =
        ∑ b : Fin n,
          Gα i k * Gα j l * (P i a * P j b * Hx a b) *
            (∑ c : Fin n, ∑ d : Fin n, P k c * P l d * Hx c d) := by
      conv_lhs =>
        rw [show (Gα i k * Gα j l * (∑ b : Fin n, P i a * P j b * Hx a b)) =
              ∑ b : Fin n, Gα i k * Gα j l * (P i a * P j b * Hx a b) from by
          rw [Finset.mul_sum]]
      rw [Finset.sum_mul]
    rw [h_step2]
    refine Finset.sum_congr rfl ?_
    intro b _
    have h_step3 : Gα i k * Gα j l * (P i a * P j b * Hx a b) *
            (∑ c : Fin n, ∑ d : Fin n, P k c * P l d * Hx c d) =
        ∑ c : Fin n,
          Gα i k * Gα j l * (P i a * P j b * Hx a b) *
            (∑ d : Fin n, P k c * P l d * Hx c d) := by
      rw [Finset.mul_sum]
    rw [h_step3]
    refine Finset.sum_congr rfl ?_
    intro c _
    have h_step4 : Gα i k * Gα j l * (P i a * P j b * Hx a b) *
            (∑ d : Fin n, P k c * P l d * Hx c d) =
        ∑ d : Fin n,
          Gα i k * Gα j l * (P i a * P j b * Hx a b) * (P k c * P l d * Hx c d) := by
      rw [Finset.mul_sum]
    rw [h_step4]
    refine Finset.sum_congr rfl ?_
    intro d _
    ring
  rw [h_LHS_eq]
  rw [nested_sum_perm (fun i j k l a b c d =>
    (P i a * Gα i k * P k c) * (P j b * Gα j l * P l d) * Hx a b * Hx c d)]
  refine Finset.sum_congr rfl ?_
  intro a _
  refine Finset.sum_congr rfl ?_
  intro b _
  refine Finset.sum_congr rfl ?_
  intro c _
  refine Finset.sum_congr rfl ?_
  intro d _
  have h_factor : (∑ i : Fin n, ∑ k : Fin n, ∑ j : Fin n, ∑ l : Fin n,
        (P i a * Gα i k * P k c) * (P j b * Gα j l * P l d) *
          Hx a b * Hx c d) =
      (∑ i : Fin n, ∑ k : Fin n, P i a * Gα i k * P k c) *
        (∑ j : Fin n, ∑ l : Fin n, P j b * Gα j l * P l d) *
        Hx a b * Hx c d := by
    have h1 : (∑ i : Fin n, ∑ k : Fin n, ∑ j : Fin n, ∑ l : Fin n,
          (P i a * Gα i k * P k c) * (P j b * Gα j l * P l d) *
            Hx a b * Hx c d) =
        (∑ i : Fin n, ∑ k : Fin n,
          (P i a * Gα i k * P k c) *
            (∑ j : Fin n, ∑ l : Fin n, P j b * Gα j l * P l d) *
            Hx a b * Hx c d) := by
      refine Finset.sum_congr rfl ?_
      intro i _
      refine Finset.sum_congr rfl ?_
      intro k _
      rw [show (∑ j : Fin n, ∑ l : Fin n,
              (P i a * Gα i k * P k c) * (P j b * Gα j l * P l d) *
                Hx a b * Hx c d) =
            (P i a * Gα i k * P k c) *
              (∑ j : Fin n, ∑ l : Fin n, P j b * Gα j l * P l d) *
              Hx a b * Hx c d from by
        rw [show (P i a * Gα i k * P k c) *
                (∑ j : Fin n, ∑ l : Fin n, P j b * Gα j l * P l d) =
              ∑ j : Fin n, ∑ l : Fin n,
                (P i a * Gα i k * P k c) * (P j b * Gα j l * P l d) from by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro j _
          rw [Finset.mul_sum]]
        rw [show ((∑ j : Fin n, ∑ l : Fin n,
                (P i a * Gα i k * P k c) * (P j b * Gα j l * P l d)) * Hx a b * Hx c d) =
              ∑ j : Fin n, ∑ l : Fin n,
                (P i a * Gα i k * P k c) * (P j b * Gα j l * P l d) * Hx a b * Hx c d from by
          rw [Finset.sum_mul, Finset.sum_mul]
          refine Finset.sum_congr rfl ?_
          intro j _
          rw [Finset.sum_mul, Finset.sum_mul]]]
    rw [h1]
    rw [show (∑ i : Fin n, ∑ k : Fin n,
            (P i a * Gα i k * P k c) *
              (∑ j : Fin n, ∑ l : Fin n, P j b * Gα j l * P l d) *
              Hx a b * Hx c d) =
          (∑ i : Fin n, ∑ k : Fin n, P i a * Gα i k * P k c) *
            (∑ j : Fin n, ∑ l : Fin n, P j b * Gα j l * P l d) *
            Hx a b * Hx c d from by
      rw [show (∑ i : Fin n, ∑ k : Fin n, P i a * Gα i k * P k c) *
              (∑ j : Fin n, ∑ l : Fin n, P j b * Gα j l * P l d) =
            ∑ i : Fin n, ∑ k : Fin n, (P i a * Gα i k * P k c) *
              (∑ j : Fin n, ∑ l : Fin n, P j b * Gα j l * P l d) from by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [Finset.sum_mul]]
      rw [show ((∑ i : Fin n, ∑ k : Fin n, (P i a * Gα i k * P k c) *
                (∑ j : Fin n, ∑ l : Fin n, P j b * Gα j l * P l d)) * Hx a b * Hx c d) =
            ∑ i : Fin n, ∑ k : Fin n, (P i a * Gα i k * P k c) *
              (∑ j : Fin n, ∑ l : Fin n, P j b * Gα j l * P l d) *
              Hx a b * Hx c d from by
        rw [Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [Finset.sum_mul, Finset.sum_mul]]]
  rw [h_factor]
  rw [h_inverse a c, h_inverse b d]

omit [CompactSpace M] in
omit [SigmaCompactSpace M] in
theorem chartFrobeniusSqHSBridge_holds
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) {x : M}
    (hx : x ∈ (chartAt H α).source) :
    chartFrobeniusSqGradVectorBridge (I := I) (M := M) g α f x := by
  classical
  rw [chartFrobeniusSqHSBridge_def]
  have h_inv := chartFrobeniusInvariance_holds (I := I) g α hf hx
  rw [chartFrobeniusInvariance_def] at h_inv
  rw [h_inv]
  exact (frobeniusSq_grad_vector_eq_chartHessFrobeniusSq (I := I) g hf x).symm

omit [CompactSpace M] in
omit [SigmaCompactSpace M] in
theorem smoothTensorPairingChart_eq_hessPairingChart_pullback
    (g : SmoothRiemannianMetric I M) (α : M)
    (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    smoothTensorPairingChart (I := I) (M := M) g α φ v y =
      hessPairingChart (I := I) g φ
        (smoothScalarToContMDiffMap (I := I) (g := g) v)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := by
  classical
  set x_y : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hx_y_def
  have hx_y_chart : x_y ∈ (chartAt H α).source := by
    have hy_target : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target :=
      toEuclidean_symm_mem_target (I := I) hy
    have hx_y_source_ext : x_y ∈ (extChartAt I α).source := by
      rw [hx_y_def]
      exact (extChartAt I α).map_target hy_target
    rwa [extChartAt_source_eq_chartAt_source] at hx_y_source_ext
  have h_HS_add : chartFrobeniusSqGradVectorBridge (I := I) (M := M) g α
      (fun z : M => (φ : M → ℝ) z + v.toFun z) x_y := by
    have hf_add : ContMDiff I 𝓘(ℝ) ∞ (fun z : M => (φ : M → ℝ) z + v.toFun z) :=
      φ.contMDiff.add v.smooth
    exact chartFrobeniusSqHSBridge_holds (I := I) g α hf_add hx_y_chart
  have h_HS_sub : chartFrobeniusSqGradVectorBridge (I := I) (M := M) g α
      (fun z : M => (φ : M → ℝ) z - v.toFun z) x_y := by
    have hf_sub : ContMDiff I 𝓘(ℝ) ∞ (fun z : M => (φ : M → ℝ) z - v.toFun z) :=
      φ.contMDiff.sub v.smooth
    exact chartFrobeniusSqHSBridge_holds (I := I) g α hf_sub hx_y_chart
  have h_swap_aux := chartAlpha_swap_aux_holds (I := I) g α (φ : M → ℝ) v.toFun x_y
  exact smoothTensorPairingChart_eq_hessPairingChart_of_HSBridge
    (I := I) (M := M) g α φ v hy h_HS_add h_HS_sub h_swap_aux

end HessianChartAlphaFrobenius
end Laplacian
end Analysis
end DifferentialGeometry

end
