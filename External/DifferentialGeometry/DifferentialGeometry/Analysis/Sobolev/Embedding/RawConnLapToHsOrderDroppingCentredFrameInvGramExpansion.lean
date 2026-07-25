import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RawConnLapL2SobolevBounds.RawTensorConnLapIterL2WtwokTwoBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartCoordinateExpansion.RawConnLapChartComponentSecondCovDerivFormula
import DifferentialGeometry.Analysis.Elliptic.TensorRegularity.SecondCovDerivExpansion.SecondCovDerivChartProjEuclidGlobal
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartCoordinateExpansion.RawConnLapChartCoordFormulaT0Linear
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartCoordinateExpansion.RawConnLapMinusInvGramPrincipalSmoothCoeff
import DifferentialGeometry.Geometry.Operator.Gradient
import DifferentialGeometry.Analysis.Sobolev.Approximation.SmoothDensity
import DifferentialGeometry.Tensor.Multilinear.HsBoundOp
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.HilbertSpace
import DifferentialGeometry.Analysis.Sobolev.Tensor.PouWeightedHsNorm
import DifferentialGeometry.Analysis.Sobolev.Tensor.PouWeightedHsNormReverseOrderZero
import DifferentialGeometry.Analysis.Integration.L2.Hilbert.DenseSubset
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.TensorSectionL2BoundByComponents
import DifferentialGeometry.Analysis.Sobolev.Manifold.MeasureBridgeUniform
import DifferentialGeometry.Analysis.Spectral.Tensor.NormEstimates.TensorChartComponentSobolevBound
import DifferentialGeometry.Geometry.Connection.ChartFrameNormGlobalSmoothCoordBasisExpansion
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartCoordinateExpansion.CovApplyFrameToCoordExpansion
import DifferentialGeometry.Analysis.Elliptic.TensorRegularity.CovDeriv.ComponentFormula
import DifferentialGeometry.Geometry.Connection.ChartTensorNabla.TensorRS.ChartTensorRSCovariantDerivativeAgreement
import DifferentialGeometry.Tensor.RSTensor.Defs


namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff NNReal ENNReal Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Tensor
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

section RawConnLapOrderDrop

open MeasureTheory
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Sobolev.Tensor
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Tensor
open Tensor0SBundle

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

section CentredFrameCoordExpansion

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem

private noncomputable def centredOrthoFrameCoordMatrix
    (g : SmoothRiemannianMetric I M) (α c : M)
    (i k : Fin (Module.finrank ℝ E)) (b : M) : ℝ := by
  classical
  exact
    if h : b ∈ (trivializationAt E (TangentSpace I) α).baseSet then
      (chartBasisFamily (I := I) α h).repr
        (smoothOrthoFrame (I := I) g c i b) k
    else 0

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma centredOrthoFrameCoordMatrix_of_mem
    (g : SmoothRiemannianMetric I M) (α c : M)
    (i k : Fin (Module.finrank ℝ E)) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    centredOrthoFrameCoordMatrix (I := I) (M := M) g α c i k b =
      (chartBasisFamily (I := I) α hb).repr
        (smoothOrthoFrame (I := I) g c i b) k := by
  classical
  unfold centredOrthoFrameCoordMatrix
  rw [dif_pos hb]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma smoothOrthoFrame_eq_centredCoordMatrix_sum
    (g : SmoothRiemannianMetric I M) (α c : M)
    (i : Fin (Module.finrank ℝ E)) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    smoothOrthoFrame (I := I) g c i b =
      ∑ k : Fin (Module.finrank ℝ E),
        centredOrthoFrameCoordMatrix (I := I) (M := M) g α c i k b •
          chartBasisVecFiber (I := I) α k b := by
  classical
  have hsum := (chartBasisFamily (I := I) α hb).sum_repr
      (smoothOrthoFrame (I := I) g c i b)
  rw [← hsum]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [centredOrthoFrameCoordMatrix_of_mem (I := I) (M := M) g α c i k hb]
  rw [chartBasisFamily_apply (I := I) α hb k]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma centredFrame_gram_expand
    (g : SmoothRiemannianMetric I M) (α c : M)
    {b : M} (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (i j : Fin (Module.finrank ℝ E)) :
    g.inner b (smoothOrthoFrame (I := I) g c i b) (smoothOrthoFrame (I := I) g c j b) =
      ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        centredOrthoFrameCoordMatrix (I := I) (M := M) g α c i k b *
          centredOrthoFrameCoordMatrix (I := I) (M := M) g α c j l b *
            chartGramMatrix (I := I) g α b k l := by
  classical
  rw [smoothOrthoFrame_eq_centredCoordMatrix_sum (I := I) (M := M) g α c i hb]
  rw [smoothOrthoFrame_eq_centredCoordMatrix_sum (I := I) (M := M) g α c j hb]
  set v : Fin (Module.finrank ℝ E) → TangentSpace I b :=
    fun k => chartBasisVecFiber (I := I) α k b with hv_def
  set a : Fin (Module.finrank ℝ E) → ℝ :=
    fun k => centredOrthoFrameCoordMatrix (I := I) (M := M) g α c i k b with ha_def
  set d : Fin (Module.finrank ℝ E) → ℝ :=
    fun l => centredOrthoFrameCoordMatrix (I := I) (M := M) g α c j l b with hd_def
  have hL : g.inner b (∑ k, a k • v k) = ∑ k, a k • g.inner b (v k) := by
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [map_smul]
  rw [hL, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
  have hR : g.inner b (v k) (∑ l, d l • v l) = ∑ l, d l * g.inner b (v k) (v l) := by
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro l _
    rw [map_smul]; rfl
  rw [hR, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro l _
  rw [chartGramMatrix_apply]
  ring

private noncomputable def centredCoordMatrix
    (g : SmoothRiemannianMetric I M) (α c : M) (b : M) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  Matrix.of (fun i k => centredOrthoFrameCoordMatrix (I := I) (M := M) g α c i k b)

omit [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma centredCoordMatrix_orthonormal_form
    (g : SmoothRiemannianMetric I M) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    centredCoordMatrix (I := I) (M := M) g α b b *
        chartGramMatrix (I := I) g α b *
          (centredCoordMatrix (I := I) (M := M) g α b b).transpose =
      (1 : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ) := by
  classical
  ext i j
  have horth : g.inner b (smoothOrthoFrame (I := I) g b i b)
      (smoothOrthoFrame (I := I) g b j b) = if i = j then (1 : ℝ) else 0 :=
    smoothOrthoFrame_orthonormal_center (I := I) g b i j
  have hexp := centredFrame_gram_expand (I := I) (M := M) g α b hb i j
  rw [horth] at hexp
  rw [Matrix.mul_apply]
  have h_inner : ∀ k₀ : Fin (Module.finrank ℝ E),
      (centredCoordMatrix (I := I) (M := M) g α b b *
          chartGramMatrix (I := I) g α b) i k₀ *
        (centredCoordMatrix (I := I) (M := M) g α b b).transpose k₀ j =
      ∑ l₀ : Fin (Module.finrank ℝ E),
        centredCoordMatrix (I := I) (M := M) g α b b i l₀ *
          chartGramMatrix (I := I) g α b l₀ k₀ *
          centredCoordMatrix (I := I) (M := M) g α b b j k₀ := by
    intro k₀
    rw [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [show (∑ k₀, (centredCoordMatrix (I := I) (M := M) g α b b *
            chartGramMatrix (I := I) g α b) i k₀ *
        (centredCoordMatrix (I := I) (M := M) g α b b).transpose k₀ j) =
      ∑ k₀, ∑ l₀,
        centredCoordMatrix (I := I) (M := M) g α b b i l₀ *
          chartGramMatrix (I := I) g α b l₀ k₀ *
          centredCoordMatrix (I := I) (M := M) g α b b j k₀ from
    Finset.sum_congr rfl (fun k₀ _ => h_inner k₀)]
  rw [show (1 : Matrix (Fin (Module.finrank ℝ E))
      (Fin (Module.finrank ℝ E)) ℝ) i j =
      (if i = j then (1 : ℝ) else 0) from by rw [Matrix.one_apply]]
  rw [hexp]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro l₀ _
  refine Finset.sum_congr rfl ?_
  intro k₀ _
  simp only [centredCoordMatrix, Matrix.of_apply]
  ring

omit [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma centredOrthoFrameCoordMatrix_orthonormality
    (g : SmoothRiemannianMetric I M) (α : M) {b : M}
    (hb : b ∈ chartLeviCivitaGoodSet (I := I) α)
    (k l : Fin (Module.finrank ℝ E)) :
    (∑ i : Fin (Module.finrank ℝ E),
        centredOrthoFrameCoordMatrix (I := I) (M := M) g α b i k b *
          centredOrthoFrameCoordMatrix (I := I) (M := M) g α b i l b) =
      chartInvGramMatrix (I := I) g α b k l := by
  classical
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hb
  have hAGA := centredCoordMatrix_orthonormal_form (I := I) (M := M) g α (b := b) hb_base
  set A : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    centredCoordMatrix (I := I) (M := M) g α b b with hA_def
  set G : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    chartGramMatrix (I := I) g α b with hG_def
  have hAGA_right : A * (G * A.transpose) = 1 := by rw [← Matrix.mul_assoc]; exact hAGA
  have hA_left_inv : (G * A.transpose) * A = 1 := mul_eq_one_comm.mp hAGA_right
  rw [Matrix.mul_assoc] at hA_left_inv
  have hAt_eq_Ginv : A.transpose * A = G⁻¹ :=
    (Matrix.inv_eq_right_inv hA_left_inv).symm
  have heval : (A.transpose * A) k l = chartInvGramMatrix (I := I) g α b k l := by
    rw [hAt_eq_Ginv]; rfl
  rw [Matrix.mul_apply] at heval
  rw [show (∑ i, A.transpose k i * A i l) =
      ∑ i, A i k * A i l from
    Finset.sum_congr rfl (fun i _ => by rw [Matrix.transpose_apply])] at heval
  rw [← heval]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [hA_def, centredCoordMatrix, Matrix.of_apply]

private noncomputable def modelBasisProj (k : Fin (Module.finrank ℝ E)) : E →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    (((LinearMap.proj k).comp ((chartModelBasis E).equivFun.toLinearMap)) : E →ₗ[ℝ] ℝ)

omit [NeZero (Module.finrank ℝ E)] in
@[simp] private lemma modelBasisProj_apply (k : Fin (Module.finrank ℝ E)) (v : E) :
    modelBasisProj (E := E) k v = ((chartModelBasis E).repr v) k := by
  classical
  unfold modelBasisProj
  change ((LinearMap.proj k).comp ((chartModelBasis E).equivFun.toLinearMap)) v = _
  rw [LinearMap.comp_apply]
  simp [Module.Basis.equivFun]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma centredOrthoFrameCoordMatrix_eq_clmAt_proj
    (g : SmoothRiemannianMetric I M) (α c : M)
    (i k : Fin (Module.finrank ℝ E)) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    centredOrthoFrameCoordMatrix (I := I) (M := M) g α c i k b =
      modelBasisProj (E := E) k
        ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b
          (smoothOrthoFrame (I := I) g c i b)) := by
  classical
  unfold centredOrthoFrameCoordMatrix
  rw [dif_pos hb]
  unfold chartBasisFamily
  rw [Module.Basis.map_repr]
  simp only [LinearEquiv.trans_apply]
  rw [modelBasisProj_apply]
  congr 2
  have h := Trivialization.coe_continuousLinearEquivAt_eq (R := ℝ)
    (e := trivializationAt E (TangentSpace I) α) (b := b) hb
  exact congrArg (fun (f : TangentSpace I b → E) => f
      (smoothOrthoFrame (I := I) g c i b)) h

omit [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [SigmaCompactSpace M] in
private lemma centredOrthoFrameCoordMatrix_contMDiffOn
    (g : SmoothRiemannianMetric I M) (α c : M)
    (i k : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun b : M => centredOrthoFrameCoordMatrix (I := I) (M := M) g α c i k b)
      (trivializationAt E (TangentSpace I) α).baseSet := by
  classical
  have hB_smooth :
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun b : M => TotalSpace.mk' E (E := TangentSpace I) b
          (smoothOrthoFrame (I := I) g c i b)) :=
    smoothOrthoFrame_smooth (I := I) g c i
  have h_triv :
      ContMDiffOn I 𝓘(ℝ, E) ∞
        (fun b : M => ((trivializationAt E (TangentSpace I) α)
            ⟨b, smoothOrthoFrame (I := I) g c i b⟩).2)
        (trivializationAt E (TangentSpace I) α).baseSet := by
    have hiff := (trivializationAt E (TangentSpace I) α).contMDiffOn_section_baseSet_iff
      (IB := I) (n := ∞)
      (s := fun b : M => smoothOrthoFrame (I := I) g c i b)
    exact hiff.mp hB_smooth.contMDiffOn
  have h_eq_baseSet :
      Set.EqOn (fun b : M => ((trivializationAt E (TangentSpace I) α)
            ⟨b, smoothOrthoFrame (I := I) g c i b⟩).2)
        (fun b : M => (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b
          (smoothOrthoFrame (I := I) g c i b))
        (trivializationAt E (TangentSpace I) α).baseSet := by
    intro b hb
    change ((trivializationAt E (TangentSpace I) α) ⟨b,
        smoothOrthoFrame (I := I) g c i b⟩).2 =
      (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b
        (smoothOrthoFrame (I := I) g c i b)
    have h₁ : ((trivializationAt E (TangentSpace I) α) ⟨b,
        smoothOrthoFrame (I := I) g c i b⟩).2 =
        ((trivializationAt E (TangentSpace I) α).continuousLinearEquivAt ℝ b hb)
          (smoothOrthoFrame (I := I) g c i b) := by
      have hp := Trivialization.apply_eq_prod_continuousLinearEquivAt
        (R := ℝ) (e := trivializationAt E (TangentSpace I) α) (b := b) hb
        (smoothOrthoFrame (I := I) g c i b)
      have hsnd := congrArg Prod.snd hp
      simp only at hsnd
      exact hsnd
    rw [h₁]
    have hclm := Trivialization.coe_continuousLinearEquivAt_eq (R := ℝ)
      (e := trivializationAt E (TangentSpace I) α) (b := b) hb
    exact congrArg (fun (f : TangentSpace I b → E) => f
      (smoothOrthoFrame (I := I) g c i b)) hclm
  have h_triv' :
      ContMDiffOn I 𝓘(ℝ, E) ∞
        (fun b : M => (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b
          (smoothOrthoFrame (I := I) g c i b))
        (trivializationAt E (TangentSpace I) α).baseSet := by
    refine h_triv.congr ?_
    intro y hy
    exact (h_eq_baseSet hy).symm
  have h_clm_smooth : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞
      (modelBasisProj (E := E) k : E → ℝ) :=
    (modelBasisProj (E := E) k).contMDiff
  have h_comp :
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞
        ((modelBasisProj (E := E) k : E → ℝ) ∘
          (fun b : M => (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b
            (smoothOrthoFrame (I := I) g c i b)))
        (trivializationAt E (TangentSpace I) α).baseSet :=
    h_clm_smooth.contMDiffOn.comp (t := Set.univ) h_triv' (Set.subset_preimage_univ)
  refine h_comp.congr ?_
  intro b hb
  exact centredOrthoFrameCoordMatrix_eq_clmAt_proj (I := I) (M := M) g α c i k hb

omit [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [SigmaCompactSpace M] in
private lemma centredOrthoFrameCoordMatrix_mdiffAt
    (g : SmoothRiemannianMetric I M) (α c : M)
    (i k : Fin (Module.finrank ℝ E)) {b : M}
    (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun b : M => centredOrthoFrameCoordMatrix (I := I) (M := M) g α c i k b) b := by
  classical
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hb
  have h_open : IsOpen (trivializationAt E (TangentSpace I) α).baseSet :=
    (trivializationAt E (TangentSpace I) α).open_baseSet
  have h_contMDiffOn :=
    centredOrthoFrameCoordMatrix_contMDiffOn (I := I) (M := M) g α c i k
  have h_contMDiffAt : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun b : M => centredOrthoFrameCoordMatrix (I := I) (M := M) g α c i k b) b :=
    (h_contMDiffOn b hb_base).contMDiffAt (h_open.mem_nhds hb_base)
  exact h_contMDiffAt.mdifferentiableAt (by simp)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma centred_chartBasisVecFiber_mdiffAt
    (α : M) (k : Fin (Module.finrank ℝ E)) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun z : M => TotalSpace.mk' E (E := TangentSpace I) z
        (chartBasisVecFiber (I := I) α k z)) b := by
  classical
  have h_contMDiffOn := chartBasisVec_contMDiffOn (I := I) α k
  have h_open : IsOpen (trivializationAt E (TangentSpace I) α).baseSet :=
    (trivializationAt E (TangentSpace I) α).open_baseSet
  have h_contMDiffAt : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
      (chartBasisVec (I := I) α k) b :=
    (h_contMDiffOn b hb).contMDiffAt (h_open.mem_nhds hb)
  exact h_contMDiffAt.mdifferentiableAt (by simp)

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma centred_covApply_chartBasisVecFiber_T₀_mdiffAt
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : Integral.L2.SmoothCcTensor g r s)
    (k : Fin (Module.finrank ℝ E)) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
      (fun z : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun w : M => TensorRSSpace r s I w) z
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g))
          (fun w : M => chartBasisVecFiber (I := I) α k w)
          (fun w : M => T₀.toSection w) z)) b := by
  classical
  have hcov_RS_smooth :
      CovariantDerivative.ContMDiffCovariantDerivative
        (TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g)) ∞ := inferInstance
  have hT₀_smooth :
      ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
        (fun z : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun w : M => TensorRSSpace r s I w) z (T₀.toSection z)) :=
    T₀.toSection.contMDiff
  have hX_at : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun z : M => TotalSpace.mk' E (E := TangentSpace I) z
        (chartBasisVecFiber (I := I) α k z)) b :=
    centred_chartBasisVecFiber_mdiffAt (I := I) (M := M) α k (b := b) hb
  have hHomSec_on :
      ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] TensorRSModel r s ℝ E)) ∞
        (fun z : M => TotalSpace.mk' (E →L[ℝ] TensorRSModel r s ℝ E)
          (E := fun w : M => TangentSpace I w →L[ℝ] TensorRSSpace r s I w) z
          ((TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g)).toFun (fun w : M => T₀.toSection w) z))
        Set.univ :=
    hcov_RS_smooth.contMDiff.contMDiff hT₀_smooth.contMDiffOn
  have hHomSec_at :
      MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] TensorRSModel r s ℝ E))
        (fun z : M => TotalSpace.mk' (E →L[ℝ] TensorRSModel r s ℝ E)
          (E := fun w : M => TangentSpace I w →L[ℝ] TensorRSSpace r s I w) z
          ((TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g)).toFun (fun w : M => T₀.toSection w) z)) b :=
    ((hHomSec_on.contMDiffAt (Filter.univ_mem))).mdifferentiableAt (by simp)
  exact MDifferentiableAt.clm_bundle_apply (b := id) hHomSec_at hX_at

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma centred_covApply_frameVec_eq_coord_sum
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α c : M)
    (T₀ : Integral.L2.SmoothCcTensor g r s)
    (i : Fin (Module.finrank ℝ E)) {y : M}
    (hy : y ∈ chartLeviCivitaGoodSet (I := I) α) :
    covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
        (LeviCivita (I := I) g))
        (smoothOrthoFrame (I := I) g c i)
        (fun z : M => T₀.toSection z) y =
      ∑ k : Fin (Module.finrank ℝ E),
        centredOrthoFrameCoordMatrix (I := I) (M := M) g α c i k y •
          covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g))
            (fun z : M => chartBasisVecFiber (I := I) α k z)
            (fun z : M => T₀.toSection z) y := by
  classical
  have hy_base : y ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hy
  change (TensorRSNabla.tensorRSCovariantDerivative I M r s
        (LeviCivita (I := I) g)).toFun (fun z : M => T₀.toSection z) y
      (smoothOrthoFrame (I := I) g c i y) =
    ∑ k : Fin (Module.finrank ℝ E),
      centredOrthoFrameCoordMatrix (I := I) (M := M) g α c i k y •
        (TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g)).toFun (fun z : M => T₀.toSection z) y
            (chartBasisVecFiber (I := I) α k y)
  rw [smoothOrthoFrame_eq_centredCoordMatrix_sum (I := I) (M := M) g α c i hy_base]
  set L : TangentSpace I y →L[ℝ] TensorRSSpace r s I y :=
    (TensorRSNabla.tensorRSCovariantDerivative I M r s
        (LeviCivita (I := I) g)).toFun (fun z : M => T₀.toSection z) y
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [L.map_smul]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma centred_finsum_smul_section_mdiffAt
    {ι : Type*} (s_finset : Finset ι)
    (r s : ℕ) (f : ι → M → ℝ)
    (σ : ι → Π z : M, TensorRSSpace r s I z) {b : M}
    (hf : ∀ i ∈ s_finset, MDifferentiableAt I 𝓘(ℝ, ℝ) (f i) b)
    (hσ : ∀ i ∈ s_finset, MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
      (fun z : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun w : M => TensorRSSpace r s I w) z (σ i z)) b) :
    MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
      (fun z : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun w : M => TensorRSSpace r s I w) z
        (∑ i ∈ s_finset, f i z • σ i z)) b := by
  classical
  induction s_finset using Finset.induction_on with
  | empty =>
    have h0 : (fun z : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun w : M => TensorRSSpace r s I w) z
        (∑ i ∈ (∅ : Finset ι), f i z • σ i z)) =
      (fun z : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun w : M => TensorRSSpace r s I w) z (0 : TensorRSSpace r s I z)) := by
      funext z; simp
    rw [h0]
    exact mdifferentiableAt_zeroSection (𝕜 := ℝ)
      (E := fun z : M => TensorRSSpace r s I z) (F := TensorRSModel r s ℝ E)
  | @insert k₀ t hk₀t ih =>
    have hf_k₀ : MDifferentiableAt I 𝓘(ℝ, ℝ) (f k₀) b :=
      hf k₀ (Finset.mem_insert_self k₀ t)
    have hσ_k₀ : MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
        (fun z : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun w : M => TensorRSSpace r s I w) z (σ k₀ z)) b :=
      hσ k₀ (Finset.mem_insert_self k₀ t)
    have hf_rest : ∀ i ∈ t, MDifferentiableAt I 𝓘(ℝ, ℝ) (f i) b := fun i hi =>
      hf i (Finset.mem_insert_of_mem hi)
    have hσ_rest : ∀ i ∈ t, MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
        (fun z : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun w : M => TensorRSSpace r s I w) z (σ i z)) b :=
      fun i hi => hσ i (Finset.mem_insert_of_mem hi)
    have hrest := ih hf_rest hσ_rest
    have hsplit : (fun z : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun w : M => TensorRSSpace r s I w) z
        (∑ i ∈ insert k₀ t, f i z • σ i z)) =
      (fun z : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun w : M => TensorRSSpace r s I w) z
        ((fun w : M => f k₀ w • σ k₀ w) z + (fun w : M => ∑ i ∈ t, f i w • σ i w) z)) := by
      funext z
      congr 1
      rw [Finset.sum_insert hk₀t]
    rw [hsplit]
    have hf_k₀_σ : MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
        (fun z : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun w : M => TensorRSSpace r s I w) z
          ((fun w : M => f k₀ w • σ k₀ w) z)) b := by
      have := MDifferentiableAt.smul_section (𝕜 := ℝ)
        (E := fun z : M => TensorRSSpace r s I z) (F := TensorRSModel r s ℝ E)
        (f := f k₀) (s := σ k₀) (x₀ := b) hf_k₀ hσ_k₀
      exact this
    exact mdifferentiableAt_add_section hf_k₀_σ hrest

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma centred_cov_RS_finsum_smul_section_leibniz_apply
    {ι : Type*} (s_finset : Finset ι)
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (f : ι → M → ℝ) (σ : ι → Π z : M, TensorRSSpace r s I z) {b : M}
    (hf : ∀ i ∈ s_finset, MDifferentiableAt I 𝓘(ℝ, ℝ) (f i) b)
    (hσ : ∀ i ∈ s_finset, MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
      (fun z : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun w : M => TensorRSSpace r s I w) z (σ i z)) b)
    (v : TangentSpace I b) :
    (TensorRSNabla.tensorRSCovariantDerivative I M r s
        (LeviCivita (I := I) g)).toFun
        (fun z : M => ∑ i ∈ s_finset, f i z • σ i z) b v =
      ∑ i ∈ s_finset,
        (f i b • (TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g)).toFun (σ i) b v +
          extDerivFun (f i) b v • σ i b) := by
  classical
  induction s_finset using Finset.induction_on with
  | empty =>
    have h0 : (fun z : M => (∑ i ∈ (∅ : Finset ι), f i z • σ i z :
        TensorRSSpace r s I z)) = (fun _ : M => 0) := by
      funext z; simp
    rw [h0]
    have hZero : (TensorRSNabla.tensorRSCovariantDerivative I M r s
        (LeviCivita (I := I) g)).toFun
        (fun _ : M => (0 : TensorRSSpace r s I _)) b = 0 :=
      (TensorRSNabla.tensorRSCovariantDerivative I M r s
        (LeviCivita (I := I) g)).isCovariantDerivativeOn.zero (hx := Set.mem_univ b)
    rw [hZero]
    simp
  | @insert k t hkt ih =>
    have hf_k : MDifferentiableAt I 𝓘(ℝ, ℝ) (f k) b :=
      hf k (Finset.mem_insert_self k t)
    have hσ_k : MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
        (fun z : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun w : M => TensorRSSpace r s I w) z (σ k z)) b :=
      hσ k (Finset.mem_insert_self k t)
    have hf_rest : ∀ i ∈ t, MDifferentiableAt I 𝓘(ℝ, ℝ) (f i) b := fun i hi =>
      hf i (Finset.mem_insert_of_mem hi)
    have hσ_rest : ∀ i ∈ t, MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
        (fun z : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun w : M => TensorRSSpace r s I w) z (σ i z)) b :=
      fun i hi => hσ i (Finset.mem_insert_of_mem hi)
    have hsum_apply : ∀ z : M, (∑ i ∈ insert k t, f i z • σ i z :
        TensorRSSpace r s I z) =
        f k z • σ k z + ∑ i ∈ t, f i z • σ i z := by
      intro z; rw [Finset.sum_insert hkt]
    have h_fkσk_mdiff : MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
        (fun z : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun w : M => TensorRSSpace r s I w) z (f k z • σ k z)) b :=
      MDifferentiableAt.smul_section (𝕜 := ℝ)
        (E := fun z : M => TensorRSSpace r s I z) (F := TensorRSModel r s ℝ E)
        (f := f k) (s := σ k) (x₀ := b) hf_k hσ_k
    have h_sum_mdiff : MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
        (fun z : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun w : M => TensorRSSpace r s I w) z (∑ i ∈ t, f i z • σ i z)) b :=
      centred_finsum_smul_section_mdiffAt (I := I) (M := M)
        (s_finset := t) r s f σ (b := b) hf_rest hσ_rest
    have hfun_eq :
        (fun z : M => ∑ i ∈ insert k t, f i z • σ i z) =
        ((fun z : M => f k z • σ k z) + (fun z : M => ∑ i ∈ t, f i z • σ i z)) := by
      funext z
      change ∑ i ∈ insert k t, f i z • σ i z =
        (fun z : M => f k z • σ k z) z + (fun z : M => ∑ i ∈ t, f i z • σ i z) z
      rw [hsum_apply z]
    rw [hfun_eq]
    rw [(TensorRSNabla.tensorRSCovariantDerivative I M r s
        (LeviCivita (I := I) g)).isCovariantDerivativeOn.add
      (σ := fun z : M => f k z • σ k z)
      (σ' := fun z : M => ∑ i ∈ t, f i z • σ i z)
      (x := b) h_fkσk_mdiff h_sum_mdiff]
    have h_leib_k := (TensorRSNabla.tensorRSCovariantDerivative I M r s
        (LeviCivita (I := I) g)).isCovariantDerivativeOn.leibniz
      (σ := σ k) (g := f k) (x := b) hσ_k hf_k
    have h_smul_form : (fun z : M => f k z • σ k z) = (f k • σ k :
        Π z : M, TensorRSSpace r s I z) := rfl
    rw [h_smul_form]
    rw [h_leib_k]
    have h_ih := ih hf_rest hσ_rest
    rw [ContinuousLinearMap.add_apply]
    rw [h_ih]
    rw [Finset.sum_insert hkt]
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.smulRight_apply]

omit [CompactSpace M] [I.Boundaryless] in
private lemma centred_cov_RS_covApply_frameVec_eq_coord_expansion
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α c : M)
    (T₀ : Integral.L2.SmoothCcTensor g r s)
    (i : Fin (Module.finrank ℝ E)) {b : M}
    (hb : b ∈ chartLeviCivitaGoodSet (I := I) α)
    (l : Fin (Module.finrank ℝ E)) :
    (TensorRSNabla.tensorRSCovariantDerivative I M r s
        (LeviCivita (I := I) g)).toFun
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g))
          (smoothOrthoFrame (I := I) g c i)
          (fun z : M => T₀.toSection z)) b
        (chartBasisVecFiber (I := I) α l b) =
      (∑ k : Fin (Module.finrank ℝ E),
        centredOrthoFrameCoordMatrix (I := I) (M := M) g α c i k b •
          (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g)).toFun
              (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                (LeviCivita (I := I) g))
                (fun z : M => chartBasisVecFiber (I := I) α k z)
                (fun z : M => T₀.toSection z)) b
              (chartBasisVecFiber (I := I) α l b)) +
      (∑ k : Fin (Module.finrank ℝ E),
        extDerivFun (fun z : M =>
            centredOrthoFrameCoordMatrix (I := I) (M := M) g α c i k z)
            b (chartBasisVecFiber (I := I) α l b) •
          covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g))
            (fun z : M => chartBasisVecFiber (I := I) α k z)
            (fun z : M => T₀.toSection z) b) := by
  classical
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hb
  have hC_mdiff : ∀ k : Fin (Module.finrank ℝ E),
      MDifferentiableAt I 𝓘(ℝ, ℝ)
        (fun z : M => centredOrthoFrameCoordMatrix (I := I) (M := M) g α c i k z) b :=
    fun k => centredOrthoFrameCoordMatrix_mdiffAt (I := I) (M := M) g α c i k (b := b) hb
  have hσ_mdiff : ∀ k : Fin (Module.finrank ℝ E),
      MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
        (fun z : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun w : M => TensorRSSpace r s I w) z
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g))
            (fun w : M => chartBasisVecFiber (I := I) α k w)
            (fun w : M => T₀.toSection w) z)) b := fun k =>
    centred_covApply_chartBasisVecFiber_T₀_mdiffAt
      (I := I) (M := M) g r s α T₀ k (b := b) hb_base
  have hOrig_mdiff : MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
      (fun z : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun w : M => TensorRSSpace r s I w) z
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g))
          (smoothOrthoFrame (I := I) g c i)
          (fun w : M => T₀.toSection w) z)) b := by
    have hcov_RS_smooth :
        CovariantDerivative.ContMDiffCovariantDerivative
          (TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g)) ∞ := inferInstance
    have hT₀_smooth :
        ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
          (fun z : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
            (E := fun w : M => TensorRSSpace r s I w) z (T₀.toSection z)) :=
      T₀.toSection.contMDiff
    have hHomSec_on :
        ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] TensorRSModel r s ℝ E)) ∞
          (fun z : M => TotalSpace.mk' (E →L[ℝ] TensorRSModel r s ℝ E)
            (E := fun w : M => TangentSpace I w →L[ℝ] TensorRSSpace r s I w) z
            ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                (LeviCivita (I := I) g)).toFun (fun w : M => T₀.toSection w) z))
          Set.univ :=
      hcov_RS_smooth.contMDiff.contMDiff hT₀_smooth.contMDiffOn
    have hHomSec_at :
        MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] TensorRSModel r s ℝ E))
          (fun z : M => TotalSpace.mk' (E →L[ℝ] TensorRSModel r s ℝ E)
            (E := fun w : M => TangentSpace I w →L[ℝ] TensorRSSpace r s I w) z
            ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                (LeviCivita (I := I) g)).toFun (fun w : M => T₀.toSection w) z)) b :=
      ((hHomSec_on.contMDiffAt (Filter.univ_mem))).mdifferentiableAt (by simp)
    have hB_at :
        MDifferentiableAt I (I.prod 𝓘(ℝ, E))
          (fun z : M => TotalSpace.mk' E (E := TangentSpace I) z
            (smoothOrthoFrame (I := I) g c i z)) b :=
      ((smoothOrthoFrame_smooth (I := I) g c i).contMDiffAt).mdifferentiableAt (by simp)
    exact MDifferentiableAt.clm_bundle_apply (b := id) hHomSec_at hB_at
  have hSum_mdiff : MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
      (fun z : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun w : M => TensorRSSpace r s I w) z
        (∑ k : Fin (Module.finrank ℝ E),
          centredOrthoFrameCoordMatrix (I := I) (M := M) g α c i k z •
            covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g))
              (fun w : M => chartBasisVecFiber (I := I) α k w)
              (fun w : M => T₀.toSection w) z)) b :=
    centred_finsum_smul_section_mdiffAt (I := I) (M := M)
      (s_finset := Finset.univ) r s
      (fun k => fun z => centredOrthoFrameCoordMatrix (I := I) (M := M) g α c i k z)
      (fun k => fun z =>
        covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g))
          (fun w : M => chartBasisVecFiber (I := I) α k w)
          (fun w : M => T₀.toSection w) z)
      (b := b) (fun k _ => hC_mdiff k) (fun k _ => hσ_mdiff k)
  have hGoodOpen : IsOpen (chartLeviCivitaGoodSet (I := I) α) :=
    chartLeviCivitaGoodSet_isOpen (I := I) α
  have hGood_nhds : chartLeviCivitaGoodSet (I := I) α ∈ 𝓝 b :=
    hGoodOpen.mem_nhds hb
  have hEvent :
      ∀ᶠ z in 𝓝 b,
        covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g))
          (smoothOrthoFrame (I := I) g c i)
          (fun w : M => T₀.toSection w) z =
        (∑ k : Fin (Module.finrank ℝ E),
          centredOrthoFrameCoordMatrix (I := I) (M := M) g α c i k z •
            covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g))
              (fun w : M => chartBasisVecFiber (I := I) α k w)
              (fun w : M => T₀.toSection w) z) := by
    filter_upwards [hGood_nhds] with z hz
    exact centred_covApply_frameVec_eq_coord_sum
      (I := I) (M := M) g r s α c T₀ i (y := z) hz
  set cov_RS := TensorRSNabla.tensorRSCovariantDerivative I M r s
    (LeviCivita (I := I) g) with hcov_RS_def
  have hCovRSReplace :
      cov_RS.toFun
          (fun z : M =>
            covApply cov_RS (smoothOrthoFrame (I := I) g c i)
              (fun w : M => T₀.toSection w) z) b =
      cov_RS.toFun
          (fun z : M => ∑ k : Fin (Module.finrank ℝ E),
            centredOrthoFrameCoordMatrix (I := I) (M := M) g α c i k z •
              covApply cov_RS (fun w : M => chartBasisVecFiber (I := I) α k w)
                (fun w : M => T₀.toSection w) z) b :=
    cov_RS.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      hOrig_mdiff hSum_mdiff (Filter.univ_mem) hEvent
  have hLeibniz := centred_cov_RS_finsum_smul_section_leibniz_apply
    (ι := Fin (Module.finrank ℝ E))
    (s_finset := Finset.univ) (g := g) (r := r) (s := s)
    (f := fun k : Fin (Module.finrank ℝ E) => fun z : M =>
      centredOrthoFrameCoordMatrix (I := I) (M := M) g α c i k z)
    (σ := fun k : Fin (Module.finrank ℝ E) => fun z : M =>
      covApply cov_RS (fun w : M => chartBasisVecFiber (I := I) α k w)
        (fun w : M => T₀.toSection w) z)
    (b := b) (hf := fun k _ => hC_mdiff k) (hσ := fun k _ => hσ_mdiff k)
    (v := chartBasisVecFiber (I := I) α l b)
  change cov_RS.toFun
        (covApply cov_RS (smoothOrthoFrame (I := I) g c i)
          (fun z : M => T₀.toSection z)) b
        (chartBasisVecFiber (I := I) α l b) = _
  have hLHS_replace :
      cov_RS.toFun
          (covApply cov_RS (smoothOrthoFrame (I := I) g c i)
            (fun z : M => T₀.toSection z)) b
          (chartBasisVecFiber (I := I) α l b) =
      cov_RS.toFun
          (fun z : M => ∑ k : Fin (Module.finrank ℝ E),
            centredOrthoFrameCoordMatrix (I := I) (M := M) g α c i k z •
              covApply cov_RS (fun w : M => chartBasisVecFiber (I := I) α k w)
                (fun w : M => T₀.toSection w) z) b
          (chartBasisVecFiber (I := I) α l b) :=
    congrArg (fun (T : TangentSpace I b →L[ℝ] TensorRSSpace r s I b) =>
      T (chartBasisVecFiber (I := I) α l b)) hCovRSReplace
  rw [hLHS_replace]
  rw [hLeibniz]
  rw [Finset.sum_add_distrib]

private noncomputable def chartProjCLM (r s : ℕ) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) (b : M) :
    TensorRSSpace r s I b →L[ℝ] ℝ :=
  (tensorChartComponentProjection (E := E) r s Idx Jdx).comp
    ((trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
@[simp] private lemma chartProjCLM_apply (r s : ℕ) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) (b : M)
    (w : TensorRSSpace r s I b) :
    chartProjCLM (I := I) (M := M) r s α Idx Jdx b w =
      tensorChartComponentProjection (E := E) r s Idx Jdx
        ((trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b w) := rfl

omit [CompactSpace M] [I.Boundaryless] in
private lemma tensorChartComponentRaw_rawConnLap_eq_chartProjCLM
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T₀ : Integral.L2.SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) (b : M) :
    tensorChartComponentRaw (I := I) (M := M) g r s
        (rawTensorConnLapSmooth (I := I) g r s T₀) α Idx Jdx b =
      chartProjCLM (I := I) (M := M) r s α Idx Jdx b
        (rawTensorConnLap (I := I) g r s (fun z : M => T₀.toSection z) b) := by
  unfold tensorChartComponentRaw tensorTrivProj chartProjCLM
  rw [rawTensorConnLapSmooth_toSection_apply (I := I) g r s T₀ b]
  rfl

omit [CompactSpace M] [I.Boundaryless] in
private lemma rawConnLap_chartα_proj_eq_centredFrame_trace_sum
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T₀ : Integral.L2.SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) (b : M) :
    tensorChartComponentRaw (I := I) (M := M) g r s
        (rawTensorConnLapSmooth (I := I) g r s T₀) α Idx Jdx b =
      ∑ i : Fin (Module.finrank ℝ E),
        chartProjCLM (I := I) (M := M) r s α Idx Jdx b
          ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                (LeviCivita (I := I) g)).toFun
              (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                (LeviCivita (I := I) g))
                (smoothOrthoFrame (I := I) g b i)
                (fun z : M => T₀.toSection z)) b
              (smoothOrthoFrame (I := I) g b i b) -
            (TensorRSNabla.tensorRSCovariantDerivative I M r s
                (LeviCivita (I := I) g)).toFun
              (fun z : M => T₀.toSection z) b
              ((LeviCivita (I := I) g).toFun
                (smoothOrthoFrame (I := I) g b i) b
                (smoothOrthoFrame (I := I) g b i b))) := by
  classical
  rw [tensorChartComponentRaw_rawConnLap_eq_chartProjCLM (I := I) (M := M) g r s T₀ α Idx Jdx b]
  rw [← rawTensorConnLap_fixedFrame_smoothOrthoFrame (I := I) g r s
    (fun z : M => T₀.toSection z) b]
  rw [rawTensorConnLap_fixedFrame_def (I := I) g r s
    (smoothOrthoFrame (I := I) g b) (fun z : M => T₀.toSection z) b]
  rw [map_sum]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma chartProjCLM_covApply_chartBasis_eq_euclidPartial_add_lowerOrder
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T₀ : Integral.L2.SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) (m : Fin (Module.finrank ℝ E))
    {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    chartProjCLM (I := I) (M := M) r s α Idx Jdx b
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g))
          (fun z : M => chartBasisVecFiber (I := I) α m z)
          (fun z : M => T₀.toSection z) b) =
      euclidPartial (E := E) m
          (chartPushedRaw I α
            (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx))
          ((toEuclidean (E := E)) ((extChartAt I α) b)) +
        DifferentialGeometry.Analysis.Laplacian.TensorRegularity.covDerivLowerOrderTerm
          (I := I) (M := M) g r s T₀ α m Idx Jdx
          ((toEuclidean (E := E)) ((extChartAt I α) b)) := by
  classical
  have hb_src : b ∈ (chartAt H α).source :=
    chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hb
  have hb_ext : b ∈ (extChartAt I α).source :=
    chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hb
  set y : EuclN := (toEuclidean (E := E)) ((extChartAt I α) b) with hy_def
  have hy_mem : y ∈ chartTargetEuclid (I := I) (M := M) α := by
    rw [hy_def, chartTargetEuclid]
    exact Set.mem_image_of_mem _ ((extChartAt I α).map_source hb_ext)
  have hroundtrip : (extChartAt I α).symm ((toEuclidean (E := E)).symm y) = b := by
    rw [hy_def, (toEuclidean (E := E)).symm_apply_apply, (extChartAt I α).left_inv hb_ext]
  have hAbstract :
      covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g))
          (fun z : M => chartBasisVecFiber (I := I) α m z)
          (fun z : M => T₀.toSection z) b =
        chartTensorRSCovariantDerivative (I := I) r s g α (fun z : M => T₀.toSection z)
          (fun z : M => chartBasisVecFiber (I := I) α m z) b := by
    rw [covApply_apply]
    rw [← tensorCovDerivAt_def (I := I) (M := M) g r s T₀ b
      (chartBasisVecFiber (I := I) α m b)]
    exact tensorCovDerivAt_eq_chartTensorRSCovariantDerivative
      (I := I) (M := M) g r s T₀ α m (b := b) hb
  rw [hAbstract]
  have hComp := DifferentialGeometry.Analysis.Laplacian.TensorRegularity.covDerivComponent_eq_euclidPartial_add_lowerOrder
    (I := I) (M := M) g r s T₀ α m Idx Jdx (y := y) hy_mem
  rw [chartProjCLM_apply]
  rw [hroundtrip] at hComp
  rw [hComp]

end CentredFrameCoordExpansion

section B4Bridge

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem

omit [CompactSpace M] [I.Boundaryless] in
private lemma centredFrame_proj_summand_expand
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T₀ : Integral.L2.SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (i : Fin (Module.finrank ℝ E)) {b : M}
    (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    chartProjCLM (I := I) (M := M) r s α Idx Jdx b
        ((TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g)).toFun
            (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g))
              (smoothOrthoFrame (I := I) g b i)
              (fun z : M => T₀.toSection z)) b
            (smoothOrthoFrame (I := I) g b i b)) =
      (∑ l : Fin (Module.finrank ℝ E),
        ∑ k : Fin (Module.finrank ℝ E),
          centredOrthoFrameCoordMatrix (I := I) (M := M) g α b i l b *
            (centredOrthoFrameCoordMatrix (I := I) (M := M) g α b i k b *
              chartProjCLM (I := I) (M := M) r s α Idx Jdx b
                ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                    (LeviCivita (I := I) g)).toFun
                  (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                    (LeviCivita (I := I) g))
                    (fun z : M => chartBasisVecFiber (I := I) α k z)
                    (fun z : M => T₀.toSection z)) b
                  (chartBasisVecFiber (I := I) α l b)))) +
      (∑ l : Fin (Module.finrank ℝ E),
        ∑ k : Fin (Module.finrank ℝ E),
          centredOrthoFrameCoordMatrix (I := I) (M := M) g α b i l b *
            (extDerivFun (fun z : M =>
                centredOrthoFrameCoordMatrix (I := I) (M := M) g α b i k z)
                b (chartBasisVecFiber (I := I) α l b) *
              chartProjCLM (I := I) (M := M) r s α Idx Jdx b
                (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                  (LeviCivita (I := I) g))
                  (fun z : M => chartBasisVecFiber (I := I) α k z)
                  (fun z : M => T₀.toSection z) b))) := by
  classical
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hb
  set cov_RS := TensorRSNabla.tensorRSCovariantDerivative I M r s
    (LeviCivita (I := I) g) with hcov_RS_def
  set L : TangentSpace I b →L[ℝ] TensorRSSpace r s I b :=
    cov_RS.toFun
        (covApply cov_RS (smoothOrthoFrame (I := I) g b i)
          (fun z : M => T₀.toSection z)) b with hL_def
  have hBb : smoothOrthoFrame (I := I) g b i b =
      ∑ l : Fin (Module.finrank ℝ E),
        centredOrthoFrameCoordMatrix (I := I) (M := M) g α b i l b •
          chartBasisVecFiber (I := I) α l b :=
    smoothOrthoFrame_eq_centredCoordMatrix_sum (I := I) (M := M) g α b i hb_base
  have hLBb : L (smoothOrthoFrame (I := I) g b i b) =
      ∑ l : Fin (Module.finrank ℝ E),
        centredOrthoFrameCoordMatrix (I := I) (M := M) g α b i l b •
          L (chartBasisVecFiber (I := I) α l b) := by
    rw [hBb, map_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [L.map_smul]
  have hL_l : ∀ l : Fin (Module.finrank ℝ E),
      L (chartBasisVecFiber (I := I) α l b) =
        (∑ k : Fin (Module.finrank ℝ E),
          centredOrthoFrameCoordMatrix (I := I) (M := M) g α b i k b •
            cov_RS.toFun
                (covApply cov_RS
                  (fun z : M => chartBasisVecFiber (I := I) α k z)
                  (fun z : M => T₀.toSection z)) b
                (chartBasisVecFiber (I := I) α l b)) +
        (∑ k : Fin (Module.finrank ℝ E),
          extDerivFun (fun z : M =>
              centredOrthoFrameCoordMatrix (I := I) (M := M) g α b i k z)
              b (chartBasisVecFiber (I := I) α l b) •
            covApply cov_RS
              (fun z : M => chartBasisVecFiber (I := I) α k z)
              (fun z : M => T₀.toSection z) b) := by
    intro l
    exact centred_cov_RS_covApply_frameVec_eq_coord_expansion
      (I := I) (M := M) g r s α b T₀ i hb l
  have hProj_arg :
      cov_RS.toFun
          (covApply cov_RS (smoothOrthoFrame (I := I) g b i)
            (fun z : M => T₀.toSection z)) b
          (smoothOrthoFrame (I := I) g b i b) =
        ∑ l : Fin (Module.finrank ℝ E),
          centredOrthoFrameCoordMatrix (I := I) (M := M) g α b i l b •
            ((∑ k : Fin (Module.finrank ℝ E),
                centredOrthoFrameCoordMatrix (I := I) (M := M) g α b i k b •
                  cov_RS.toFun
                      (covApply cov_RS
                        (fun z : M => chartBasisVecFiber (I := I) α k z)
                        (fun z : M => T₀.toSection z)) b
                      (chartBasisVecFiber (I := I) α l b)) +
              (∑ k : Fin (Module.finrank ℝ E),
                extDerivFun (fun z : M =>
                    centredOrthoFrameCoordMatrix (I := I) (M := M) g α b i k z)
                    b (chartBasisVecFiber (I := I) α l b) •
                  covApply cov_RS
                    (fun z : M => chartBasisVecFiber (I := I) α k z)
                    (fun z : M => T₀.toSection z) b)) := by
    rw [show cov_RS.toFun
            (covApply cov_RS (smoothOrthoFrame (I := I) g b i)
              (fun z : M => T₀.toSection z)) b
            (smoothOrthoFrame (I := I) g b i b) =
          L (smoothOrthoFrame (I := I) g b i b) from rfl]
    rw [hLBb]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [hL_l l]
  rw [hProj_arg]
  rw [map_sum]
  have hsummand : ∀ l : Fin (Module.finrank ℝ E),
      chartProjCLM (I := I) (M := M) r s α Idx Jdx b
          (centredOrthoFrameCoordMatrix (I := I) (M := M) g α b i l b •
            ((∑ k : Fin (Module.finrank ℝ E),
                centredOrthoFrameCoordMatrix (I := I) (M := M) g α b i k b •
                  cov_RS.toFun
                      (covApply cov_RS
                        (fun z : M => chartBasisVecFiber (I := I) α k z)
                        (fun z : M => T₀.toSection z)) b
                      (chartBasisVecFiber (I := I) α l b)) +
              (∑ k : Fin (Module.finrank ℝ E),
                extDerivFun (fun z : M =>
                    centredOrthoFrameCoordMatrix (I := I) (M := M) g α b i k z)
                    b (chartBasisVecFiber (I := I) α l b) •
                  covApply cov_RS
                    (fun z : M => chartBasisVecFiber (I := I) α k z)
                    (fun z : M => T₀.toSection z) b))) =
        (∑ k : Fin (Module.finrank ℝ E),
            centredOrthoFrameCoordMatrix (I := I) (M := M) g α b i l b *
              (centredOrthoFrameCoordMatrix (I := I) (M := M) g α b i k b *
                chartProjCLM (I := I) (M := M) r s α Idx Jdx b
                  (cov_RS.toFun
                    (covApply cov_RS
                      (fun z : M => chartBasisVecFiber (I := I) α k z)
                      (fun z : M => T₀.toSection z)) b
                    (chartBasisVecFiber (I := I) α l b)))) +
          (∑ k : Fin (Module.finrank ℝ E),
            centredOrthoFrameCoordMatrix (I := I) (M := M) g α b i l b *
              (extDerivFun (fun z : M =>
                  centredOrthoFrameCoordMatrix (I := I) (M := M) g α b i k z)
                  b (chartBasisVecFiber (I := I) α l b) *
                chartProjCLM (I := I) (M := M) r s α Idx Jdx b
                  (covApply cov_RS
                    (fun z : M => chartBasisVecFiber (I := I) α k z)
                    (fun z : M => T₀.toSection z) b))) := by
    intro l
    rw [map_smul, smul_eq_mul, map_add, mul_add]
    congr 1
    · rw [map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [map_smul, smul_eq_mul]
    · rw [map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [map_smul, smul_eq_mul]
  rw [Finset.sum_congr rfl (fun l _ => hsummand l)]
  rw [Finset.sum_add_distrib]

omit [CompactSpace M] [I.Boundaryless] in
private lemma centredFrame_proj_principal_eq_invGramPrincipalSum
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T₀ : Integral.L2.SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) {b : M}
    (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    (∑ i : Fin (Module.finrank ℝ E),
      ∑ l : Fin (Module.finrank ℝ E),
        ∑ k : Fin (Module.finrank ℝ E),
          centredOrthoFrameCoordMatrix (I := I) (M := M) g α b i l b *
            (centredOrthoFrameCoordMatrix (I := I) (M := M) g α b i k b *
              chartProjCLM (I := I) (M := M) r s α Idx Jdx b
                ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                    (LeviCivita (I := I) g)).toFun
                  (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                    (LeviCivita (I := I) g))
                    (fun z : M => chartBasisVecFiber (I := I) α k z)
                    (fun z : M => T₀.toSection z)) b
                  (chartBasisVecFiber (I := I) α l b)))) =
      chartInvGramPrincipalSum (I := I) (M := M) g r s α T₀ Idx Jdx b := by
  classical
  rw [chartInvGramPrincipalSum]
  set P : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun k l => chartProjCLM (I := I) (M := M) r s α Idx Jdx b
      ((TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g)).toFun
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g))
          (fun z : M => chartBasisVecFiber (I := I) α k z)
          (fun z : M => T₀.toSection z)) b
        (chartBasisVecFiber (I := I) α l b)) with hP_def
  set C : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun i k => centredOrthoFrameCoordMatrix (I := I) (M := M) g α b i k b with hC_def
  have hLHS :
      (∑ i, ∑ l, ∑ k, C i l * (C i k * P k l)) =
        ∑ k, ∑ l, (∑ i, C i k * C i l) * P k l := by
    have h1 : (∑ i, ∑ l, ∑ k, C i l * (C i k * P k l)) =
        ∑ i, ∑ k, ∑ l, C i l * (C i k * P k l) :=
      Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
    rw [h1, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  rw [hLHS]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [show (∑ i, C i k * C i l) = chartInvGramMatrix (I := I) g α b k l from
    centredOrthoFrameCoordMatrix_orthonormality (I := I) (M := M) g α hb k l]
  simp only [hP_def]
  rw [chartProjCLM_apply]

omit [CompactSpace M] in
private lemma rawConnLap_chartα_minus_invGramPrincipalSum_smooth_coeff_form
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ∃ (B_1 : (Fin r → Fin (Module.finrank ℝ E)) →
              (Fin s → Fin (Module.finrank ℝ E)) →
              Fin (Module.finrank ℝ E) → EuclN → ℝ),
    ∃ (B_0 : (Fin r → Fin (Module.finrank ℝ E)) →
              (Fin s → Fin (Module.finrank ℝ E)) → EuclN → ℝ),
      (∀ I' J' m, ContDiffOn ℝ ∞ (B_1 I' J' m) (chartTargetEuclid (I := I) (M := M) α)) ∧
      (∀ I' J', ContDiffOn ℝ ∞ (B_0 I' J') (chartTargetEuclid (I := I) (M := M) α)) ∧
      ∀ (T₀ : Integral.L2.SmoothCcTensor g r s),
        ∀ {b : M}, b ∈ chartLeviCivitaGoodSet (I := I) α →
          tensorChartComponentRaw (I := I) (M := M) g r s
              (rawTensorConnLapSmooth (I := I) g r s T₀) α Idx Jdx b -
            chartInvGramPrincipalSum (I := I) (M := M) g r s α T₀ Idx Jdx b =
            (∑ I' : Fin r → Fin (Module.finrank ℝ E),
              ∑ J' : Fin s → Fin (Module.finrank ℝ E),
              ∑ m,
              B_1 I' J' m ((toEuclidean (E := E)) ((extChartAt I α) b)) *
                euclidPartial (E := E) m
                  (chartPushedRaw I α
                    (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α I' J'))
                  ((toEuclidean (E := E)) ((extChartAt I α) b))) +
            (∑ I' : Fin r → Fin (Module.finrank ℝ E),
              ∑ J' : Fin s → Fin (Module.finrank ℝ E),
              B_0 I' J' ((toEuclidean (E := E)) ((extChartAt I α) b)) *
                chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α I' J')
                  ((toEuclidean (E := E)) ((extChartAt I α) b))) := by
  classical
  obtain ⟨B_1, B_0, hB1cd, hB0cd, hEq⟩ :=
    christoffelTrace_correction_eq_T₀_linear (I := I) (M := M) g r s α Idx Jdx
  refine ⟨B_1, B_0, hB1cd, hB0cd, ?_⟩
  intro T₀ b hb
  rw [rawConnLap_chartα_minus_invGramPrincipalSum_eq_christoffelTrace
    (I := I) (M := M) g r s α T₀ Idx Jdx hb]
  exact hEq T₀ hb

omit [CompactSpace M] in
private lemma rawConnLap_chartα_firstOrder_remainder_smooth_coeff_form
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ∃ (B_1 : (Fin r → Fin (Module.finrank ℝ E)) →
              (Fin s → Fin (Module.finrank ℝ E)) →
              Fin (Module.finrank ℝ E) → EuclN → ℝ),
    ∃ (B_0 : (Fin r → Fin (Module.finrank ℝ E)) →
              (Fin s → Fin (Module.finrank ℝ E)) → EuclN → ℝ),
      (∀ I' J' m, ContDiffOn ℝ ∞ (B_1 I' J' m) (chartTargetEuclid (I := I) (M := M) α)) ∧
      (∀ I' J', ContDiffOn ℝ ∞ (B_0 I' J') (chartTargetEuclid (I := I) (M := M) α)) ∧
      ∀ (T₀ : Integral.L2.SmoothCcTensor g r s),
        ∀ {b : M}, b ∈ chartLeviCivitaGoodSet (I := I) α →
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              ∑ k : Fin (Module.finrank ℝ E),
                centredOrthoFrameCoordMatrix (I := I) (M := M) g α b i l b *
                  (extDerivFun (fun z : M =>
                      centredOrthoFrameCoordMatrix (I := I) (M := M) g α b i k z)
                      b (chartBasisVecFiber (I := I) α l b) *
                    chartProjCLM (I := I) (M := M) r s α Idx Jdx b
                      (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                        (LeviCivita (I := I) g))
                        (fun z : M => chartBasisVecFiber (I := I) α k z)
                        (fun z : M => T₀.toSection z) b))) -
          (∑ i : Fin (Module.finrank ℝ E),
            chartProjCLM (I := I) (M := M) r s α Idx Jdx b
              ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                  (LeviCivita (I := I) g)).toFun
                (fun z : M => T₀.toSection z) b
                ((LeviCivita (I := I) g).toFun
                  (smoothOrthoFrame (I := I) g b i) b
                  (smoothOrthoFrame (I := I) g b i b)))) =
            (∑ I' : Fin r → Fin (Module.finrank ℝ E),
              ∑ J' : Fin s → Fin (Module.finrank ℝ E),
              ∑ m,
              B_1 I' J' m ((toEuclidean (E := E)) ((extChartAt I α) b)) *
                euclidPartial (E := E) m
                  (chartPushedRaw I α
                    (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α I' J'))
                  ((toEuclidean (E := E)) ((extChartAt I α) b))) +
            (∑ I' : Fin r → Fin (Module.finrank ℝ E),
              ∑ J' : Fin s → Fin (Module.finrank ℝ E),
              B_0 I' J' ((toEuclidean (E := E)) ((extChartAt I α) b)) *
                chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α I' J')
                  ((toEuclidean (E := E)) ((extChartAt I α) b))) := by
  classical
  obtain ⟨B_1, B_0, hB1cd, hB0cd, hDiff⟩ :=
    rawConnLap_chartα_minus_invGramPrincipalSum_smooth_coeff_form
      (I := I) (M := M) g r s α Idx Jdx
  refine ⟨B_1, B_0, hB1cd, hB0cd, ?_⟩
  intro T₀ b hb

  have hReduce :
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            centredOrthoFrameCoordMatrix (I := I) (M := M) g α b i l b *
              (extDerivFun (fun z : M =>
                  centredOrthoFrameCoordMatrix (I := I) (M := M) g α b i k z)
                  b (chartBasisVecFiber (I := I) α l b) *
                chartProjCLM (I := I) (M := M) r s α Idx Jdx b
                  (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                    (LeviCivita (I := I) g))
                    (fun z : M => chartBasisVecFiber (I := I) α k z)
                    (fun z : M => T₀.toSection z) b))) -
      (∑ i : Fin (Module.finrank ℝ E),
        chartProjCLM (I := I) (M := M) r s α Idx Jdx b
          ((TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g)).toFun
            (fun z : M => T₀.toSection z) b
            ((LeviCivita (I := I) g).toFun
              (smoothOrthoFrame (I := I) g b i) b
              (smoothOrthoFrame (I := I) g b i b)))) =
      tensorChartComponentRaw (I := I) (M := M) g r s
          (rawTensorConnLapSmooth (I := I) g r s T₀) α Idx Jdx b -
        chartInvGramPrincipalSum (I := I) (M := M) g r s α T₀ Idx Jdx b := by
    have hB2 := rawConnLap_chartα_proj_eq_centredFrame_trace_sum
      (I := I) (M := M) g r s T₀ α Idx Jdx b
    have hsplit_summand : ∀ i : Fin (Module.finrank ℝ E),
        chartProjCLM (I := I) (M := M) r s α Idx Jdx b
            ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                  (LeviCivita (I := I) g)).toFun
                (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                  (LeviCivita (I := I) g))
                  (smoothOrthoFrame (I := I) g b i)
                  (fun z : M => T₀.toSection z)) b
                (smoothOrthoFrame (I := I) g b i b) -
              (TensorRSNabla.tensorRSCovariantDerivative I M r s
                  (LeviCivita (I := I) g)).toFun
                (fun z : M => T₀.toSection z) b
                ((LeviCivita (I := I) g).toFun
                  (smoothOrthoFrame (I := I) g b i) b
                  (smoothOrthoFrame (I := I) g b i b))) =
          ((∑ l : Fin (Module.finrank ℝ E),
              ∑ k : Fin (Module.finrank ℝ E),
                centredOrthoFrameCoordMatrix (I := I) (M := M) g α b i l b *
                  (centredOrthoFrameCoordMatrix (I := I) (M := M) g α b i k b *
                    chartProjCLM (I := I) (M := M) r s α Idx Jdx b
                      ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                          (LeviCivita (I := I) g)).toFun
                        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                          (LeviCivita (I := I) g))
                          (fun z : M => chartBasisVecFiber (I := I) α k z)
                          (fun z : M => T₀.toSection z)) b
                        (chartBasisVecFiber (I := I) α l b)))) +
            (∑ l : Fin (Module.finrank ℝ E),
              ∑ k : Fin (Module.finrank ℝ E),
                centredOrthoFrameCoordMatrix (I := I) (M := M) g α b i l b *
                  (extDerivFun (fun z : M =>
                      centredOrthoFrameCoordMatrix (I := I) (M := M) g α b i k z)
                      b (chartBasisVecFiber (I := I) α l b) *
                    chartProjCLM (I := I) (M := M) r s α Idx Jdx b
                      (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                        (LeviCivita (I := I) g))
                        (fun z : M => chartBasisVecFiber (I := I) α k z)
                        (fun z : M => T₀.toSection z) b)))) -
          chartProjCLM (I := I) (M := M) r s α Idx Jdx b
            ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                (LeviCivita (I := I) g)).toFun
              (fun z : M => T₀.toSection z) b
              ((LeviCivita (I := I) g).toFun
                (smoothOrthoFrame (I := I) g b i) b
                (smoothOrthoFrame (I := I) g b i b))) := by
      intro i
      rw [map_sub]
      rw [centredFrame_proj_summand_expand (I := I) (M := M) g r s T₀ α Idx Jdx i hb]
    rw [hB2, Finset.sum_congr rfl (fun i _ => hsplit_summand i),
      Finset.sum_sub_distrib, Finset.sum_add_distrib,
      centredFrame_proj_principal_eq_invGramPrincipalSum
        (I := I) (M := M) g r s T₀ α Idx Jdx hb]
    ring
  rw [hReduce]
  exact hDiff T₀ hb

omit [CompactSpace M] in
theorem rawTensorConnLap_chartα_proj_eq_invGramPrincipalSum_on_goodSet
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ∃ (B_1 : (Fin r → Fin (Module.finrank ℝ E)) →
              (Fin s → Fin (Module.finrank ℝ E)) →
              Fin (Module.finrank ℝ E) → EuclN → ℝ),
    ∃ (B_0 : (Fin r → Fin (Module.finrank ℝ E)) →
              (Fin s → Fin (Module.finrank ℝ E)) → EuclN → ℝ),
      (∀ I' J' m, ContDiffOn ℝ ∞ (B_1 I' J' m) (chartTargetEuclid (I := I) (M := M) α)) ∧
      (∀ I' J', ContDiffOn ℝ ∞ (B_0 I' J') (chartTargetEuclid (I := I) (M := M) α)) ∧
      ∀ (T₀ : Integral.L2.SmoothCcTensor g r s),
        ∀ {b : M}, b ∈ chartLeviCivitaGoodSet (I := I) α →
          tensorChartComponentRaw (I := I) (M := M) g r s
            (rawTensorConnLapSmooth (I := I) g r s T₀) α Idx Jdx b =
            chartInvGramPrincipalSum (I := I) (M := M) g r s α T₀ Idx Jdx b +
            (∑ I' : Fin r → Fin (Module.finrank ℝ E),
              ∑ J' : Fin s → Fin (Module.finrank ℝ E),
              ∑ m,
              B_1 I' J' m ((toEuclidean (E := E)) ((extChartAt I α) b)) *
                euclidPartial (E := E) m
                  (chartPushedRaw I α
                    (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α I' J'))
                  ((toEuclidean (E := E)) ((extChartAt I α) b))) +
            (∑ I' : Fin r → Fin (Module.finrank ℝ E),
              ∑ J' : Fin s → Fin (Module.finrank ℝ E),
              B_0 I' J' ((toEuclidean (E := E)) ((extChartAt I α) b)) *
                chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α I' J')
                  ((toEuclidean (E := E)) ((extChartAt I α) b))) := by
  classical
  obtain ⟨B_1, B_0, hB1cd, hB0cd, hRem⟩ :=
    rawConnLap_chartα_firstOrder_remainder_smooth_coeff_form
      (I := I) (M := M) g r s α Idx Jdx
  refine ⟨B_1, B_0, hB1cd, hB0cd, ?_⟩
  intro T₀ b hb
  have hB2 := rawConnLap_chartα_proj_eq_centredFrame_trace_sum
    (I := I) (M := M) g r s T₀ α Idx Jdx b
  rw [hB2]
  have hsplit_summand : ∀ i : Fin (Module.finrank ℝ E),
      chartProjCLM (I := I) (M := M) r s α Idx Jdx b
          ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                (LeviCivita (I := I) g)).toFun
              (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                (LeviCivita (I := I) g))
                (smoothOrthoFrame (I := I) g b i)
                (fun z : M => T₀.toSection z)) b
              (smoothOrthoFrame (I := I) g b i b) -
            (TensorRSNabla.tensorRSCovariantDerivative I M r s
                (LeviCivita (I := I) g)).toFun
              (fun z : M => T₀.toSection z) b
              ((LeviCivita (I := I) g).toFun
                (smoothOrthoFrame (I := I) g b i) b
                (smoothOrthoFrame (I := I) g b i b))) =
        ((∑ l : Fin (Module.finrank ℝ E),
            ∑ k : Fin (Module.finrank ℝ E),
              centredOrthoFrameCoordMatrix (I := I) (M := M) g α b i l b *
                (centredOrthoFrameCoordMatrix (I := I) (M := M) g α b i k b *
                  chartProjCLM (I := I) (M := M) r s α Idx Jdx b
                    ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                        (LeviCivita (I := I) g)).toFun
                      (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                        (LeviCivita (I := I) g))
                        (fun z : M => chartBasisVecFiber (I := I) α k z)
                        (fun z : M => T₀.toSection z)) b
                      (chartBasisVecFiber (I := I) α l b)))) +
          (∑ l : Fin (Module.finrank ℝ E),
            ∑ k : Fin (Module.finrank ℝ E),
              centredOrthoFrameCoordMatrix (I := I) (M := M) g α b i l b *
                (extDerivFun (fun z : M =>
                    centredOrthoFrameCoordMatrix (I := I) (M := M) g α b i k z)
                    b (chartBasisVecFiber (I := I) α l b) *
                  chartProjCLM (I := I) (M := M) r s α Idx Jdx b
                    (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                      (LeviCivita (I := I) g))
                      (fun z : M => chartBasisVecFiber (I := I) α k z)
                      (fun z : M => T₀.toSection z) b)))) -
        chartProjCLM (I := I) (M := M) r s α Idx Jdx b
          ((TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g)).toFun
            (fun z : M => T₀.toSection z) b
            ((LeviCivita (I := I) g).toFun
              (smoothOrthoFrame (I := I) g b i) b
              (smoothOrthoFrame (I := I) g b i b))) := by
    intro i
    rw [map_sub]
    rw [centredFrame_proj_summand_expand (I := I) (M := M) g r s T₀ α Idx Jdx i hb]
  rw [Finset.sum_congr rfl (fun i _ => hsplit_summand i)]
  rw [Finset.sum_sub_distrib]
  rw [Finset.sum_add_distrib]
  rw [centredFrame_proj_principal_eq_invGramPrincipalSum
    (I := I) (M := M) g r s T₀ α Idx Jdx hb]
  have hRemEq := hRem T₀ hb
  linarith [hRemEq]

end B4Bridge

end RawConnLapOrderDrop

end DifferentialGeometry.PDE.RicciFlow
