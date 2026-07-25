import DifferentialGeometry.Geometry.Flow.VectorField
import DifferentialGeometry.Geometry.Connection.ChartFrame.RicciIdentitySmoothFrame
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnDiffPalatini

noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff Matrix

namespace DifferentialGeometry
namespace PDE
namespace DeTurck

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] in
theorem connDiff_cocycle (g₀ g₁ g₂ : SmoothRiemannianMetric I M) (x : M)
    (w v : TangentSpace I x) :
    connDiff (I := I) g₁ g₂ x w v =
      connDiff (I := I) g₁ g₀ x w v + connDiff (I := I) g₀ g₂ x w v := by
  classical
  obtain ⟨σ, hσx⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
    (F := E) (V := (TangentSpace I : M → Type _)) x w
  have hσ : MDiffAt (T% fun y => σ y) x := σ.mdifferentiableAt
  have h12 := connDiff_apply (I := I) g₁ g₂ hσ v
  have h10 := connDiff_apply (I := I) g₁ g₀ hσ v
  have h02 := connDiff_apply (I := I) g₀ g₂ hσ v
  rw [hσx] at h12 h10 h02
  rw [h12, h10, h02]
  abel

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem deTurckVF_sub_eq_connDiff_trace
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    (deTurckVF (I := I) g₁ g_bg :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x -
      (deTurckVF (I := I) g₀ g_bg :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x =
      (∑ j : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g₁ x x j k •
            connDiff (I := I) g₁ g₀ x
              (chartBasisVecFiber (I := I) x j x)
              (chartBasisVecFiber (I := I) x k x)) +
        ∑ j : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
          (chartInvGramMatrix (I := I) g₁ x x j k -
              chartInvGramMatrix (I := I) g₀ x x j k) •
            connDiff (I := I) g₀ g_bg x
              (chartBasisVecFiber (I := I) x j x)
              (chartBasisVecFiber (I := I) x k x) := by
  classical
  rw [deTurckVF_apply_eq (I := I) g₁ g_bg x, deTurckVF_apply_eq (I := I) g₀ g_bg x]
  rw [← Finset.sum_sub_distrib]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← Finset.sum_sub_distrib]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [connDiff_cocycle (I := I) g₀ g₁ g_bg x
      (chartBasisVecFiber (I := I) x j x) (chartBasisVecFiber (I := I) x k x)]
  rw [smul_add]
  rw [sub_smul]
  abel

private def famCoord (x : M) (F : Fin (Module.finrank ℝ E) → TangentSpace I x) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  Matrix.of fun i m =>
    ((chartModelBasis E).repr
      ((trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ x (F i))) m

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in

omit [NeZero (Module.finrank ℝ E)] in
private theorem famCoord_gram_eq_one (g : SmoothRiemannianMetric I M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x).baseSet)
    (hxsrc : x ∈ (extChartAt I x).source)
    (F : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (hF : ∀ i j, g.inner x (F i) (F j) = if i = j then 1 else 0) :
    famCoord (I := I) x F * chartGramMatrix (I := I) g x x *
        (famCoord (I := I) x F)ᵀ = 1 := by
  classical
  ext i j
  rw [Matrix.one_apply]
  have hexp := g_inner_eq_chart_sum (I := I) g x hx hxsrc (F i) (F j)
  rw [hF i j] at hexp
  have hchart : ∀ a b : Fin (Module.finrank ℝ E),
      chartGramOnE (I := I) g x a b (extChartAt I x x) =
        chartGramMatrix (I := I) g x x a b := by
    intro a b; unfold chartGramOnE; rw [(extChartAt I x).left_inv hxsrc]
  rw [Matrix.mul_apply]
  rw [show (∑ a, (famCoord (I := I) x F * chartGramMatrix (I := I) g x x) i a *
        (famCoord (I := I) x F)ᵀ a j) =
      ∑ a, ∑ b, famCoord (I := I) x F i a * famCoord (I := I) x F j b *
        chartGramMatrix (I := I) g x x a b from by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [Matrix.transpose_apply]; ring]
  rw [hexp]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  rw [hchart a b]; rfl

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in

omit [NeZero (Module.finrank ℝ E)] in
private theorem sum_famCoord_eq_chartInvGram (g : SmoothRiemannianMetric I M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x).baseSet)
    (hxsrc : x ∈ (extChartAt I x).source)
    (F : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (hF : ∀ i j, g.inner x (F i) (F j) = if i = j then 1 else 0)
    (m n : Fin (Module.finrank ℝ E)) :
    (∑ i : Fin (Module.finrank ℝ E),
        famCoord (I := I) x F i m * famCoord (I := I) x F i n) =
      chartInvGramMatrix (I := I) g x x m n := by
  classical
  have h1 := famCoord_gram_eq_one (I := I) g hx hxsrc F hF
  have hC : famCoord (I := I) x F * (chartGramMatrix (I := I) g x x *
        (famCoord (I := I) x F)ᵀ) = 1 := by rw [← Matrix.mul_assoc]; exact h1
  have h2 : (chartGramMatrix (I := I) g x x * (famCoord (I := I) x F)ᵀ) *
        famCoord (I := I) x F = 1 := mul_eq_one_comm.mp hC
  rw [Matrix.mul_assoc] at h2
  have hinv : (famCoord (I := I) x F)ᵀ * famCoord (I := I) x F =
      (chartGramMatrix (I := I) g x x)⁻¹ := (Matrix.inv_eq_right_inv h2).symm
  have hmn := congrFun (congrFun hinv m) n
  rw [Matrix.mul_apply] at hmn
  rw [chartInvGramMatrix, ← hmn]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.transpose_apply]

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in

omit [NeZero (Module.finrank ℝ E)] in
private theorem bilin_ortho_family_diag_eq_chartGram_trace
    (g : SmoothRiemannianMetric I M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x).baseSet)
    (hxsrc : x ∈ (extChartAt I x).source)
    (F : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (hF : ∀ i j, g.inner x (F i) (F j) = if i = j then 1 else 0)
    (A : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x) :
    (∑ i : Fin (Module.finrank ℝ E), A (F i) (F i)) =
      ∑ m : Fin (Module.finrank ℝ E), ∑ n : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g x x m n •
          A (chartBasisVecFiber (I := I) x m x) (chartBasisVecFiber (I := I) x n x) := by
  classical
  have hrec : ∀ i, F i =
      ∑ m, famCoord (I := I) x F i m • chartBasisVecFiber (I := I) x m x :=
    fun i => chartBasisVecFiber_recompose (I := I) x hx (F i)
  have hsummand : ∀ i, A (F i) (F i) =
      ∑ m, ∑ n, (famCoord (I := I) x F i m * famCoord (I := I) x F i n) •
        A (chartBasisVecFiber (I := I) x m x) (chartBasisVecFiber (I := I) x n x) := by
    intro i
    conv_lhs => rw [hrec i]
    have hfirst : A (∑ m, famCoord (I := I) x F i m • chartBasisVecFiber (I := I) x m x) =
        ∑ m, famCoord (I := I) x F i m • A (chartBasisVecFiber (I := I) x m x) := by
      rw [map_sum]; refine Finset.sum_congr rfl (fun m _ => ?_); rw [map_smul]
    rw [hfirst, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [ContinuousLinearMap.smul_apply, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [map_smul, smul_smul]
  rw [Finset.sum_congr rfl (fun i _ => hsummand i)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [← Finset.sum_smul]
  rw [sum_famCoord_eq_chartInvGram (I := I) g hx hxsrc F hF m n]

omit [SigmaCompactSpace M] in
theorem deTurckVF_eq_orthoFrame_trace
    (g g_bg : SmoothRiemannianMetric I M) (x : M) :
    (deTurckVF (I := I) g g_bg :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x =
      ∑ i : Fin (Module.finrank ℝ E),
        connDiff (I := I) g g_bg x
          (smoothOrthoFrame (I := I) g x i x)
          (smoothOrthoFrame (I := I) g x i x) := by
  classical
  have hx : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x
  have hxsrc : x ∈ (extChartAt I x).source := mem_extChartAt_source x
  rw [deTurckVF_apply_eq (I := I) g g_bg x]
  rw [bilin_ortho_family_diag_eq_chartGram_trace (I := I) g hx hxsrc
    (fun i => smoothOrthoFrame (I := I) g x i x)
    (fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g x i j)
    (connDiff (I := I) g g_bg x)]

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem connDiff_symm (g g' : SmoothRiemannianMetric I M) (x : M) (w v : TangentSpace I x) :
    connDiff (I := I) g g' x w v = connDiff (I := I) g g' x v w := by
  classical
  obtain ⟨σ, hσx⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
    (F := E) (V := (TangentSpace I : M → Type _)) x w
  obtain ⟨τ, hτx⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
    (F := E) (V := (TangentSpace I : M → Type _)) x v
  have hσ : MDiffAt (T% fun y => σ y) x := σ.mdifferentiableAt
  have hτ : MDiffAt (T% fun y => τ y) x := τ.mdifferentiableAt
  have hστ := connDiff_apply (I := I) g g' (σ := fun y => σ y) hσ (τ x)
  have hτσ := connDiff_apply (I := I) g g' (σ := fun y => τ y) hτ (σ x)
  have htor1 := (CovariantDerivative.torsion_eq_zero_iff (cov := LeviCivita (I := I) g)).mp
    (LeviCivita_torsion_eq_zero (I := I) g) (X := fun y => τ y) (Y := fun y => σ y) hτ hσ
  have htor0 := (CovariantDerivative.torsion_eq_zero_iff (cov := LeviCivita (I := I) g')).mp
    (LeviCivita_torsion_eq_zero (I := I) g') (X := fun y => τ y) (Y := fun y => σ y) hτ hσ
  rw [← hσx, ← hτx, hστ, hτσ]
  have hkey : (LeviCivita (I := I) g).toFun (fun y => σ y) x (τ x)
        - (LeviCivita (I := I) g).toFun (fun y => τ y) x (σ x)
      = (LeviCivita (I := I) g').toFun (fun y => σ y) x (τ x)
        - (LeviCivita (I := I) g').toFun (fun y => τ y) x (σ x) := by
    rw [htor1, htor0]
  have := hkey
  abel_nf
  abel_nf at this
  linear_combination (norm := abel) this

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem connDiff_outerCovDeriv_eq (g g_bg : SmoothRiemannianMetric I M)
    {X Y Z : Π b : M, TangentSpace I b}
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Z)) (x : M) :
    (LeviCivita (I := I) g).toFun
          (diffSec (LeviCivita (I := I) g_bg) (LeviCivita (I := I) g) Y Z) x (X x)
        - connDiff (I := I) g g_bg x (Z x) (covApply (LeviCivita (I := I) g) X Y x)
        - connDiff (I := I) g g_bg x (covApply (LeviCivita (I := I) g) X Z x) (Y x) =
      covDerivConnDiff (I := I) g_bg g X Y Z x
        + (connDiff (I := I) g g_bg x (connDiff (I := I) g g_bg x (Z x) (Y x)) (X x)
            - connDiff (I := I) g g_bg x (Z x) (connDiff (I := I) g g_bg x (Y x) (X x))
            - connDiff (I := I) g g_bg x (connDiff (I := I) g g_bg x (Z x) (X x)) (Y x)) := by
  classical
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  set cov₀ := LeviCivita (I := I) g_bg with hcov₀
  set cov₁ := LeviCivita (I := I) g with hcov₁
  have hAeq : connDiff (I := I) g g_bg =
      CovariantDerivative.difference cov₁ cov₀ := connDiff_eq_difference (I := I) g_bg g
  have hYx : MDiffAt (T% Y) x := (hY x).mdifferentiableAt (by simp)
  have hZx : MDiffAt (T% Z) x := (hZ x).mdifferentiableAt (by simp)
  have hZ1 : ContMDiff I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1) (T% Z) := by simpa using hZ
  have hdiffYZ_at : MDiffAt (T% (diffSec cov₀ cov₁ Y Z)) x :=
    ((diffSec_contMDiff cov₀ cov₁ hY hZ1) x).mdifferentiableAt (by simp)
  rw [covDerivConnDiff_eq (I := I) g_bg g X Y Z x]
  unfold covDerivDiff
  rw [← hcov₀, ← hcov₁]
  have hT1 : cov₁.toFun (diffSec cov₀ cov₁ Y Z) x (X x)
        - cov₀.toFun (diffSec cov₀ cov₁ Y Z) x (X x) =
      connDiff (I := I) g g_bg x (connDiff (I := I) g g_bg x (Z x) (Y x)) (X x) := by
    rw [← diff_eval cov₀ cov₁ hdiffYZ_at (X x), hAeq]
    rfl
  have hcA1 : covApply cov₁ X Y x = covApply cov₀ X Y x + connDiff (I := I) g g_bg x (Y x) (X x) := by
    rw [covApply_cov1_eq cov₀ cov₁ hYx, hAeq]; rfl
  have hcA2 : covApply cov₁ X Z x = covApply cov₀ X Z x + connDiff (I := I) g g_bg x (Z x) (X x) := by
    rw [covApply_cov1_eq cov₀ cov₁ hZx, hAeq]; rfl
  have hT1' : cov₁.toFun (diffSec cov₀ cov₁ Y Z) x (X x) =
      cov₀.toFun (diffSec cov₀ cov₁ Y Z) x (X x)
        + connDiff (I := I) g g_bg x (connDiff (I := I) g g_bg x (Z x) (Y x)) (X x) := by
    rw [← hT1]; abel
  rw [hcA1, hcA2, hT1', ← hAeq, map_add, map_add, ContinuousLinearMap.add_apply]
  abel

end DeTurck
end PDE
end DifferentialGeometry
