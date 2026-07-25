import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartCoordinateExpansion.ChartFrameNormGlobalSmooth
import DifferentialGeometry.Geometry.Operator.Gradient

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold Set IsManifold ContinuousLinearMap Filter
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Tensor
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

noncomputable def chartFrameNormGlobalSmoothCoordMatrix
    (g : SmoothRiemannianMetric I M) (α : M)
    (i k : Fin (Module.finrank ℝ E)) (b : M) : ℝ := by
  classical
  exact
    if h : b ∈ (trivializationAt E (TangentSpace I) α).baseSet then
      (chartBasisFamily (I := I) α h).repr
        ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b) k
    else 0

omit [I.Boundaryless] in
private lemma chartFrameNormGlobalSmoothCoordMatrix_of_mem
    (g : SmoothRiemannianMetric I M) (α : M)
    (i k : Fin (Module.finrank ℝ E)) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i k b =
      (chartBasisFamily (I := I) α hb).repr
        ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b) k := by
  classical
  unfold chartFrameNormGlobalSmoothCoordMatrix
  rw [dif_pos hb]

omit [I.Boundaryless] in
theorem chartFrameNormGlobalSmooth_eq_coordMatrix_sum
    (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E))
    {b : M}
    (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i :
        Π b : M, TangentSpace I b) b) =
      ∑ k : Fin (Module.finrank ℝ E),
        chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i k b •
          chartBasisVecFiber (I := I) α k b := by
  classical
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hb
  have hsum := (chartBasisFamily (I := I) α hb_base).sum_repr
      ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b)
  have hcoerce : ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i :
        Π b : M, TangentSpace I b) b)
      = (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b := rfl
  rw [hcoerce]
  rw [← hsum]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [chartFrameNormGlobalSmoothCoordMatrix_of_mem (I := I) (M := M) g α i k hb_base]
  rw [chartBasisFamily_apply (I := I) α hb_base k]

section LinearAlgebra

variable (g : SmoothRiemannianMetric I M) (α : M) {b : M}

private noncomputable def coordMatrixOf (i k : Fin (Module.finrank ℝ E)) : ℝ :=
  chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i k b

private noncomputable def coordMatrix :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  Matrix.of (fun i k => coordMatrixOf (I := I) (M := M) g α (b := b) i k)

omit [I.Boundaryless] in
@[simp] private lemma coordMatrix_apply (i k : Fin (Module.finrank ℝ E)) :
    coordMatrix (I := I) (M := M) g α (b := b) i k =
      chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i k b := rfl

omit [I.Boundaryless] in
private lemma chartFrameNormGlobalSmooth_eq_coord_sum_of_mem
    (i : Fin (Module.finrank ℝ E))
    (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b =
      ∑ k : Fin (Module.finrank ℝ E),
        coordMatrix (I := I) (M := M) g α (b := b) i k •
          chartBasisVecFiber (I := I) α k b := by
  classical
  have h :=
    chartFrameNormGlobalSmooth_eq_coordMatrix_sum
      (I := I) (M := M) g α i (b := b) hb
  have hcoerce : ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i :
        Π b : M, TangentSpace I b) b)
      = (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b := rfl
  rw [hcoerce] at h
  rw [h]
  rfl

omit [I.Boundaryless] in
private lemma gram_expand_coordBasis
    (hb : b ∈ chartLeviCivitaGoodSet (I := I) α)
    (i j : Fin (Module.finrank ℝ E)) :
    g.inner b
        ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b)
        ((chartFrameNormGlobalSmooth (I := I) (M := M) g α j).toFun b) =
      ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        coordMatrix (I := I) (M := M) g α (b := b) i k *
          coordMatrix (I := I) (M := M) g α (b := b) j l *
            chartGramMatrix (I := I) g α b k l := by
  classical
  rw [chartFrameNormGlobalSmooth_eq_coord_sum_of_mem (I := I) (M := M) g α i hb]
  rw [chartFrameNormGlobalSmooth_eq_coord_sum_of_mem (I := I) (M := M) g α j hb]
  set v : Fin (Module.finrank ℝ E) → TangentSpace I b :=
    fun k => chartBasisVecFiber (I := I) α k b with hv_def
  set a : Fin (Module.finrank ℝ E) → ℝ :=
    fun k => coordMatrix (I := I) (M := M) g α (b := b) i k with ha_def
  set c : Fin (Module.finrank ℝ E) → ℝ :=
    fun l => coordMatrix (I := I) (M := M) g α (b := b) j l with hc_def
  have hL :
      g.inner b (∑ k, a k • v k) =
        ∑ k, a k • g.inner b (v k) := by
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [map_smul]
  rw [hL]
  rw [ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
  have hR :
      g.inner b (v k) (∑ l, c l • v l) =
        ∑ l, c l * g.inner b (v k) (v l) := by
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro l _
    rw [map_smul]; rfl
  rw [hR, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro l _
  rw [chartGramMatrix_apply]
  ring

omit [I.Boundaryless] in
private lemma orthonormal_matrix_form_at
    (hb_pou : b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x))
    (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    coordMatrix (I := I) (M := M) g α (b := b) *
        chartGramMatrix (I := I) g α b *
          (coordMatrix (I := I) (M := M) g α (b := b)).transpose =
      (1 : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ) := by
  classical
  ext i j
  have hbpouGood :
      b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
            chartLeviCivitaGoodSet (I := I) α := ⟨hb_pou, hb⟩
  have horth :=
    chartFrameNormGlobalSmooth_orthonormal_on_pouTsupportGoodSet
      (I := I) (M := M) g α (b := b) hbpouGood i j
  have hexp := gram_expand_coordBasis (I := I) (M := M) g α (b := b) hb i j
  rw [horth] at hexp
  rw [Matrix.mul_apply]
  have h_inner : ∀ k₀ : Fin (Module.finrank ℝ E),
      (coordMatrix (I := I) (M := M) g α (b := b) *
          chartGramMatrix (I := I) g α b) i k₀ *
        (coordMatrix (I := I) (M := M) g α (b := b)).transpose k₀ j =
      ∑ l₀ : Fin (Module.finrank ℝ E),
        coordMatrix (I := I) (M := M) g α (b := b) i l₀ *
          chartGramMatrix (I := I) g α b l₀ k₀ *
          coordMatrix (I := I) (M := M) g α (b := b) j k₀ := by
    intro k₀
    rw [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [show (∑ k₀, (coordMatrix (I := I) (M := M) g α (b := b) *
            chartGramMatrix (I := I) g α b) i k₀ *
        (coordMatrix (I := I) (M := M) g α (b := b)).transpose k₀ j) =
      ∑ k₀, ∑ l₀,
        coordMatrix (I := I) (M := M) g α (b := b) i l₀ *
          chartGramMatrix (I := I) g α b l₀ k₀ *
          coordMatrix (I := I) (M := M) g α (b := b) j k₀ from
    Finset.sum_congr rfl (fun k₀ _ => h_inner k₀)]
  rw [show (1 : Matrix (Fin (Module.finrank ℝ E))
      (Fin (Module.finrank ℝ E)) ℝ) i j =
      (if i = j then (1 : ℝ) else 0) from by
    rw [Matrix.one_apply]]
  rw [hexp]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro l₀ _
  refine Finset.sum_congr rfl ?_
  intro k₀ _
  ring

omit [I.Boundaryless] in
private lemma orthonormal_matrix_inverse_at
    (hb_pou : b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x))
    (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    (coordMatrix (I := I) (M := M) g α (b := b)).transpose *
        coordMatrix (I := I) (M := M) g α (b := b) =
      chartInvGramMatrix (I := I) g α b := by
  classical
  have hAGA := orthonormal_matrix_form_at (I := I) (M := M) g α
      (b := b) hb_pou hb
  set A : Matrix (Fin (Module.finrank ℝ E))
      (Fin (Module.finrank ℝ E)) ℝ :=
    coordMatrix (I := I) (M := M) g α (b := b)
  set G : Matrix (Fin (Module.finrank ℝ E))
      (Fin (Module.finrank ℝ E)) ℝ := chartGramMatrix (I := I) g α b
  have hAGA_right : A * (G * A.transpose) = 1 := by
    rw [← Matrix.mul_assoc]; exact hAGA
  have hG_At_eq_invA : G * A.transpose = A⁻¹ :=
    (Matrix.inv_eq_right_inv hAGA_right).symm
  have hA_left_inv : (G * A.transpose) * A = 1 :=
    mul_eq_one_comm.mp hAGA_right
  rw [Matrix.mul_assoc] at hA_left_inv
  have hAt_eq_Ginv : A.transpose * A = G⁻¹ :=
    (Matrix.inv_eq_right_inv hA_left_inv).symm
  unfold chartInvGramMatrix
  exact hAt_eq_Ginv

end LinearAlgebra

omit [I.Boundaryless] in
theorem chartFrameNormGlobalSmoothCoordMatrix_orthonormality
    (g : SmoothRiemannianMetric I M) (α : M)
    {b : M}
    (hb_pou : b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x))
    (hb : b ∈ chartLeviCivitaGoodSet (I := I) α)
    (k l : Fin (Module.finrank ℝ E)) :
    (∑ i : Fin (Module.finrank ℝ E),
        chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i k b *
          chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i l b) =
      chartInvGramMatrix (I := I) g α b k l := by
  classical
  have h := orthonormal_matrix_inverse_at (I := I) (M := M) g α
      (b := b) hb_pou hb
  have heval : ((coordMatrix (I := I) (M := M) g α (b := b)).transpose *
      coordMatrix (I := I) (M := M) g α (b := b)) k l =
        chartInvGramMatrix (I := I) g α b k l := by
    rw [h]
  rw [Matrix.mul_apply] at heval
  rw [show (∑ i,
        (coordMatrix (I := I) (M := M) g α (b := b)).transpose k i *
          coordMatrix (I := I) (M := M) g α (b := b) i l) =
      ∑ i,
        coordMatrix (I := I) (M := M) g α (b := b) i k *
          coordMatrix (I := I) (M := M) g α (b := b) i l from by
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [Matrix.transpose_apply]] at heval
  simp only [coordMatrix_apply] at heval
  exact heval

end Connection
end Integral
end DifferentialGeometry
