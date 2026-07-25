import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.TensorThirdOrderWeitzenbock

noncomputable section

open Bundle Manifold Set FiberBundle NormedSpace Filter
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Integral
namespace Connection

section CovToFunArith

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x : M, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]

lemma cov_toFun_neg (cov : CovariantDerivative I F V)
    {σ : Π b : M, V b} {x : M} (hσ : MDiffAt (T% σ) x) :
    cov.toFun (-σ) x = - cov.toFun σ x := by
  have hneg : MDiffAt (T% (-σ)) x := mdifferentiableAt_neg_section hσ
  have hsum : cov.toFun (σ + (-σ)) x = cov.toFun σ x + cov.toFun (-σ) x :=
    cov.isCovariantDerivativeOnUniv.add hσ hneg
  have hzero : cov.toFun (σ + (-σ)) x = 0 := by
    rw [add_neg_cancel]
    exact cov.isCovariantDerivativeOnUniv.zero (Set.mem_univ x)
  rw [hzero] at hsum
  exact eq_neg_of_add_eq_zero_right hsum.symm

lemma cov_toFun_sub (cov : CovariantDerivative I F V)
    {σ τ : Π b : M, V b} {x : M} (hσ : MDiffAt (T% σ) x) (hτ : MDiffAt (T% τ) x) :
    cov.toFun (σ - τ) x = cov.toFun σ x - cov.toFun τ x := by
  have hneg : MDiffAt (T% (-τ)) x := mdifferentiableAt_neg_section hτ
  have hadd : cov.toFun (σ + (-τ)) x = cov.toFun σ x + cov.toFun (-τ) x :=
    cov.isCovariantDerivativeOnUniv.add hσ hneg
  rw [show σ - τ = σ + (-τ) from by abel, hadd, cov_toFun_neg cov hτ, sub_eq_add_neg]

end CovToFunArith

section SecondBianchi

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

def nablaCurvSec (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X Y Z W : Π b : M, TangentSpace I b) (x : M) : TangentSpace I x :=
  cov.toFun (fun b => riemannSec cov Y Z W b) x (X x)
    - riemannSec cov (covApply cov X Y) Z W x
    - riemannSec cov Y (covApply cov X Z) W x
    - riemannSec cov Y Z (covApply cov X W) x

omit [CompleteSpace E] [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M]
  [BoundarylessManifold I M] in

lemma nablaCurvSec_def (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X Y Z W : Π b : M, TangentSpace I b) (x : M) :
    nablaCurvSec cov X Y Z W x =
      cov.toFun (fun b => riemannSec cov Y Z W b) x (X x)
        - riemannSec cov (covApply cov X Y) Z W x
        - riemannSec cov Y (covApply cov X Z) W x
        - riemannSec cov Y Z (covApply cov X W) x := rfl

omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma covApply_riemannSec_section_distrib
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    {X Y Z W : Π b : M, TangentSpace I b} {x : M}
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Z))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W)) :
    cov.toFun (fun b => riemannSec cov Y Z W b) x (X x) =
      cov.toFun (covApply cov Y (covApply cov Z W)) x (X x)
        - cov.toFun (covApply cov Z (covApply cov Y W)) x (X x)
        - cov.toFun (covApply cov (VectorField.mlieBracket I Y Z) W) x (X x) := by
  classical
  have hsec : (fun b => riemannSec cov Y Z W b) =
      covApply cov Y (covApply cov Z W) - covApply cov Z (covApply cov Y W)
        - covApply cov (VectorField.mlieBracket I Y Z) W := by
    funext b; rw [riemannSec_def]; rfl
  rw [hsec]
  have hbr : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (VectorField.mlieBracket I Y Z)) :=
    mlieBracket_contMDiff (I := I) hY hZ
  have h1 : MDiffAt (T% (covApply cov Y (covApply cov Z W))) x :=
    (covApply_covApply_contMDiff (cov := cov) hY hZ hW x).mdifferentiableAt (by simp)
  have h2 : MDiffAt (T% (covApply cov Z (covApply cov Y W))) x :=
    (covApply_covApply_contMDiff (cov := cov) hZ hY hW x).mdifferentiableAt (by simp)
  have h3 : MDiffAt (T% (covApply cov (VectorField.mlieBracket I Y Z) W)) x :=
    (covApply_contMDiff (cov := cov) hbr hW x).mdifferentiableAt (by simp)
  have h12 : MDiffAt (T% (covApply cov Y (covApply cov Z W)
      - covApply cov Z (covApply cov Y W))) x :=
    (((covApply_covApply_contMDiff (cov := cov) hY hZ hW).sub_section
      (covApply_covApply_contMDiff (cov := cov) hZ hY hW)) x).mdifferentiableAt (by simp)
  rw [cov_toFun_sub cov h12 h3, cov_toFun_sub cov h1 h2]
  simp only [ContinuousLinearMap.sub_apply]

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in

lemma covApply_torsionFree_inner_section_eq_zero
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (htor : cov.torsion = 0)
    {A B W : Π b : M, TangentSpace I b}
    (hA : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% A))
    (hB : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% B)) :
    covApply cov (covApply cov A B) W - covApply cov (covApply cov B A) W
      - covApply cov (VectorField.mlieBracket I A B) W = 0 := by
  classical
  haveI : IsManifold I 2 M := by
    have h_le : (2 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by norm_cast
    exact IsManifold.of_le h_le
  funext b
  simp only [Pi.sub_apply, Pi.zero_apply, covApply_apply]
  have htf : covApply cov A B b - covApply cov B A b = VectorField.mlieBracket I A B b :=
    covApply_sub_eq_mlieBracket (cov := cov) htor
      ((hA b).mdifferentiableAt (by simp)) ((hB b).mdifferentiableAt (by simp))
  rw [show VectorField.mlieBracket I A B b = covApply cov A B b - covApply cov B A b
      from htf.symm, map_sub]
  simp only [covApply_apply]
  abel

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma covApply_outer_torsionFree_collapse
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (htor : cov.torsion = 0)
    {a A B W : Π b : M, TangentSpace I b} {x : M}
    (hA : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% A))
    (hB : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% B))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W)) :
    cov.toFun (covApply cov (covApply cov A B) W) x (a x)
      - cov.toFun (covApply cov (covApply cov B A) W) x (a x)
      - cov.toFun (covApply cov (VectorField.mlieBracket I A B) W) x (a x) = 0 := by
  classical
  have hbr : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (VectorField.mlieBracket I A B)) :=
    mlieBracket_contMDiff (I := I) hA hB
  have hcAB : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (covApply cov A B)) :=
    covApply_contMDiff (cov := cov) hA hB
  have hcBA : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (covApply cov B A)) :=
    covApply_contMDiff (cov := cov) hB hA
  have h1 : MDiffAt (T% (covApply cov (covApply cov A B) W)) x :=
    (covApply_contMDiff (cov := cov) hcAB hW x).mdifferentiableAt (by simp)
  have h2 : MDiffAt (T% (covApply cov (covApply cov B A) W)) x :=
    (covApply_contMDiff (cov := cov) hcBA hW x).mdifferentiableAt (by simp)
  have h12 : MDiffAt (T% (covApply cov (covApply cov A B) W
      - covApply cov (covApply cov B A) W)) x :=
    (((covApply_contMDiff (cov := cov) hcAB hW).sub_section
      (covApply_contMDiff (cov := cov) hcBA hW)) x).mdifferentiableAt (by simp)
  have h3 : MDiffAt (T% (covApply cov (VectorField.mlieBracket I A B) W)) x :=
    (covApply_contMDiff (cov := cov) hbr hW x).mdifferentiableAt (by simp)
  have key : cov.toFun (covApply cov (covApply cov A B) W
      - covApply cov (covApply cov B A) W
      - covApply cov (VectorField.mlieBracket I A B) W) x = 0 := by
    rw [covApply_torsionFree_inner_section_eq_zero cov htor hA hB]
    exact cov.isCovariantDerivativeOnUniv.zero (Set.mem_univ x)
  have hd : cov.toFun (covApply cov (covApply cov A B) W
      - covApply cov (covApply cov B A) W
      - covApply cov (VectorField.mlieBracket I A B) W) x =
      (cov.toFun (covApply cov (covApply cov A B) W) x
        - cov.toFun (covApply cov (covApply cov B A) W) x)
        - cov.toFun (covApply cov (VectorField.mlieBracket I A B) W) x := by
    rw [cov_toFun_sub cov h12 h3, cov_toFun_sub cov h1 h2]
  rw [key] at hd
  have := congrFun (congrArg DFunLike.coe hd.symm) (a x)
  simpa [ContinuousLinearMap.sub_apply] using this

omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma nablaCurvSec_flat
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    {X Y Z W : Π b : M, TangentSpace I b} {x : M}
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Z))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W)) :
    nablaCurvSec cov X Y Z W x =
      cov.toFun (covApply cov Y (covApply cov Z W)) x (X x)
        - cov.toFun (covApply cov Z (covApply cov Y W)) x (X x)
        - cov.toFun (covApply cov (VectorField.mlieBracket I Y Z) W) x (X x)
      - (cov.toFun (covApply cov Z W) x ((covApply cov X Y) x)
          - cov.toFun (covApply cov (covApply cov X Y) W) x (Z x)
          - cov.toFun W x (VectorField.mlieBracket I (covApply cov X Y) Z x))
      - (cov.toFun (covApply cov (covApply cov X Z) W) x (Y x)
          - cov.toFun (covApply cov Y W) x ((covApply cov X Z) x)
          - cov.toFun W x (VectorField.mlieBracket I Y (covApply cov X Z) x))
      - (cov.toFun (covApply cov Z (covApply cov X W)) x (Y x)
          - cov.toFun (covApply cov Y (covApply cov X W)) x (Z x)
          - cov.toFun (covApply cov X W) x (VectorField.mlieBracket I Y Z x)) := by
  rw [nablaCurvSec_def, covApply_riemannSec_section_distrib cov hY hZ hW]
  rw [riemannSec_def (cov := cov) (covApply cov X Y) Z W x,
      riemannSec_def (cov := cov) Y (covApply cov X Z) W x,
      riemannSec_def (cov := cov) Y Z (covApply cov X W) x]

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in

lemma cov_toFun_torsionFree_vector_collapse
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (htor : cov.torsion = 0)
    {A B S : Π b : M, TangentSpace I b} {x : M}
    (hA : MDiffAt (T% A) x) (hB : MDiffAt (T% B) x) :
    cov.toFun S x ((covApply cov A B) x) - cov.toFun S x ((covApply cov B A) x)
      - cov.toFun S x (VectorField.mlieBracket I A B x) = 0 := by
  haveI : IsManifold I 2 M := by
    have h_le : (2 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by norm_cast
    exact IsManifold.of_le h_le
  have htf : covApply cov A B x - covApply cov B A x = VectorField.mlieBracket I A B x :=
    covApply_sub_eq_mlieBracket (cov := cov) htor hA hB
  rw [show VectorField.mlieBracket I A B x = covApply cov A B x - covApply cov B A x
      from htf.symm, map_sub]
  abel

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in

lemma covApply_eq_swap_add_mlieBracket
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (htor : cov.torsion = 0)
    {A B : Π b : M, TangentSpace I b}
    (hA : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% A))
    (hB : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% B)) :
    covApply cov A B = covApply cov B A + VectorField.mlieBracket I A B := by
  haveI : IsManifold I 2 M := by
    have h_le : (2 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by norm_cast
    exact IsManifold.of_le h_le
  funext b
  have htf : covApply cov A B b - covApply cov B A b = VectorField.mlieBracket I A B b :=
    covApply_sub_eq_mlieBracket (cov := cov) htor
      ((hA b).mdifferentiableAt (by simp)) ((hB b).mdifferentiableAt (by simp))
  simp only [Pi.add_apply]
  rw [← htf]; abel

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in

lemma mlieBracket_covApply_pair
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (htor : cov.torsion = 0)
    {A B C : Π b : M, TangentSpace I b} {x : M}
    (hA : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% A))
    (hB : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% B))
    (hcBA : MDiffAt (T% (covApply cov B A)) x)
    (hbrAB : MDiffAt (T% (VectorField.mlieBracket I A B)) x) :
    VectorField.mlieBracket I (covApply cov A B) C x
      + VectorField.mlieBracket I C (covApply cov B A) x =
      VectorField.mlieBracket I (VectorField.mlieBracket I A B) C x := by
  haveI : IsManifold I 2 M := by
    have h_le : (2 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by norm_cast
    exact IsManifold.of_le h_le
  rw [VectorField.mlieBracket_swap_apply (V := C) (W := covApply cov B A)]
  rw [covApply_eq_swap_add_mlieBracket cov htor hA hB]
  rw [VectorField.mlieBracket_add_left hcBA hbrAB]
  abel

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma bianchi_bracket_jacobi_sum_eq_zero
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (htor : cov.torsion = 0)
    {X Y Z : Π b : M, TangentSpace I b} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Z)) :
    VectorField.mlieBracket I (covApply cov X Y) Z x
      + VectorField.mlieBracket I Y (covApply cov X Z) x
      + VectorField.mlieBracket I (covApply cov Y Z) X x
      + VectorField.mlieBracket I Z (covApply cov Y X) x
      + VectorField.mlieBracket I (covApply cov Z X) Y x
      + VectorField.mlieBracket I X (covApply cov Z Y) x = 0 := by
  classical
  haveI : IsManifold I 2 M := by
    have h_le : (2 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by norm_cast
    exact IsManifold.of_le h_le
  haveI : IsManifold I (minSmoothness ℝ 3) M := by
    rw [minSmoothness_of_isRCLikeNormedField]; infer_instance
  have hcYX : MDiffAt (T% (covApply cov Y X)) x :=
    (covApply_contMDiff (cov := cov) hY hX x).mdifferentiableAt (by simp)
  have hcXZ : MDiffAt (T% (covApply cov X Z)) x :=
    (covApply_contMDiff (cov := cov) hX hZ x).mdifferentiableAt (by simp)
  have hcZY : MDiffAt (T% (covApply cov Z Y)) x :=
    (covApply_contMDiff (cov := cov) hZ hY x).mdifferentiableAt (by simp)
  have hbrXY : MDiffAt (T% (VectorField.mlieBracket I X Y)) x :=
    (mlieBracket_contMDiff (I := I) hX hY x).mdifferentiableAt (by simp)
  have hbrZX : MDiffAt (T% (VectorField.mlieBracket I Z X)) x :=
    (mlieBracket_contMDiff (I := I) hZ hX x).mdifferentiableAt (by simp)
  have hbrYZ : MDiffAt (T% (VectorField.mlieBracket I Y Z)) x :=
    (mlieBracket_contMDiff (I := I) hY hZ x).mdifferentiableAt (by simp)
  have p1 := mlieBracket_covApply_pair cov htor (A := X) (B := Y) (C := Z) hX hY hcYX hbrXY
  have p2 := mlieBracket_covApply_pair cov htor (A := Z) (B := X) (C := Y) hZ hX hcXZ hbrZX
  have p3 := mlieBracket_covApply_pair cov htor (A := Y) (B := Z) (C := X) hY hZ hcZY hbrYZ
  have hX2 : ContMDiffAt I (I.prod 𝓘(ℝ, E)) (minSmoothness ℝ 2) (T% X) x := by
    have hle : minSmoothness ℝ 2 ≤ (∞ : WithTop ℕ∞) := by
      rw [minSmoothness_of_isRCLikeNormedField]; norm_cast
    exact (hX x).of_le hle
  have hY2 : ContMDiffAt I (I.prod 𝓘(ℝ, E)) (minSmoothness ℝ 2) (T% Y) x := by
    have hle : minSmoothness ℝ 2 ≤ (∞ : WithTop ℕ∞) := by
      rw [minSmoothness_of_isRCLikeNormedField]; norm_cast
    exact (hY x).of_le hle
  have hZ2 : ContMDiffAt I (I.prod 𝓘(ℝ, E)) (minSmoothness ℝ 2) (T% Z) x := by
    have hle : minSmoothness ℝ 2 ≤ (∞ : WithTop ℕ∞) := by
      rw [minSmoothness_of_isRCLikeNormedField]; norm_cast
    exact (hZ x).of_le hle
  have hJacobi := VectorField.leibniz_identity_mlieBracket_apply (I := I)
    (U := X) (V := Y) (W := Z) (x := x) hX2 hY2 hZ2
  have hJac_cyc :
      VectorField.mlieBracket I (VectorField.mlieBracket I X Y) Z x +
        VectorField.mlieBracket I (VectorField.mlieBracket I Z X) Y x +
        VectorField.mlieBracket I (VectorField.mlieBracket I Y Z) X x = 0 := by
    rw [VectorField.mlieBracket_swap_apply (V := VectorField.mlieBracket I X Y) (W := Z),
        VectorField.mlieBracket_swap_apply (V := VectorField.mlieBracket I Z X) (W := Y),
        VectorField.mlieBracket_swap_apply (V := VectorField.mlieBracket I Y Z) (W := X)]
    have hbr_XZ : VectorField.mlieBracket I X Z = - VectorField.mlieBracket I Z X :=
      VectorField.mlieBracket_swap (V := X) (W := Z)
    have e2 : VectorField.mlieBracket I Y (VectorField.mlieBracket I X Z) x =
        - VectorField.mlieBracket I Y (VectorField.mlieBracket I Z X) x := by
      conv_lhs => rw [hbr_XZ]
      have hsmul : (-VectorField.mlieBracket I Z X)
          = (-1 : ℝ) • VectorField.mlieBracket I Z X := by ext b; simp
      rw [hsmul, VectorField.mlieBracket_const_smul_right (c := (-1 : ℝ)) (V := Y)
        (W := VectorField.mlieBracket I Z X) (x := x) hbrZX]
      simp
    have hab1 : VectorField.mlieBracket I (VectorField.mlieBracket I X Y) Z x =
        - VectorField.mlieBracket I Z (VectorField.mlieBracket I X Y) x :=
      VectorField.mlieBracket_swap_apply (V := VectorField.mlieBracket I X Y) (W := Z)
    rw [hab1, e2] at hJacobi
    linear_combination (norm := abel) -hJacobi
  calc VectorField.mlieBracket I (covApply cov X Y) Z x
      + VectorField.mlieBracket I Y (covApply cov X Z) x
      + VectorField.mlieBracket I (covApply cov Y Z) X x
      + VectorField.mlieBracket I Z (covApply cov Y X) x
      + VectorField.mlieBracket I (covApply cov Z X) Y x
      + VectorField.mlieBracket I X (covApply cov Z Y) x
      = (VectorField.mlieBracket I (covApply cov X Y) Z x
          + VectorField.mlieBracket I Z (covApply cov Y X) x)
        + (VectorField.mlieBracket I (covApply cov Z X) Y x
          + VectorField.mlieBracket I Y (covApply cov X Z) x)
        + (VectorField.mlieBracket I (covApply cov Y Z) X x
          + VectorField.mlieBracket I X (covApply cov Z Y) x) := by abel
    _ = VectorField.mlieBracket I (VectorField.mlieBracket I X Y) Z x
        + VectorField.mlieBracket I (VectorField.mlieBracket I Z X) Y x
        + VectorField.mlieBracket I (VectorField.mlieBracket I Y Z) X x := by
        rw [p1, p2, p3]
    _ = 0 := hJac_cyc

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem second_bianchi_levi_civita
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (htor : cov.torsion = 0)
    {X Y Z W : Π b : M, TangentSpace I b} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Z))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W)) :
    nablaCurvSec cov X Y Z W x + nablaCurvSec cov Y Z X W x
      + nablaCurvSec cov Z X Y W x = 0 := by
  classical
  rw [nablaCurvSec_flat cov hY hZ hW, nablaCurvSec_flat cov hZ hX hW,
      nablaCurvSec_flat cov hX hY hW]

  have g1XYZ := covApply_outer_torsionFree_collapse cov htor (a := X) (A := Y) (B := Z)
    (x := x) hY hZ hW
  have g1YZX := covApply_outer_torsionFree_collapse cov htor (a := Y) (A := Z) (B := X)
    (x := x) hZ hX hW
  have g1ZXY := covApply_outer_torsionFree_collapse cov htor (a := Z) (A := X) (B := Y)
    (x := x) hX hY hW

  have hXat : MDiffAt (T% X) x := (hX x).mdifferentiableAt (by simp)
  have hYat : MDiffAt (T% Y) x := (hY x).mdifferentiableAt (by simp)
  have hZat : MDiffAt (T% Z) x := (hZ x).mdifferentiableAt (by simp)
  have g2XYZ := cov_toFun_torsionFree_vector_collapse cov htor (A := X) (B := Y)
    (S := covApply cov Z W) hXat hYat
  have g2YZX := cov_toFun_torsionFree_vector_collapse cov htor (A := Y) (B := Z)
    (S := covApply cov X W) hYat hZat
  have g2ZXY := cov_toFun_torsionFree_vector_collapse cov htor (A := Z) (B := X)
    (S := covApply cov Y W) hZat hXat

  have g3 := bianchi_bracket_jacobi_sum_eq_zero cov htor (x := x) hX hY hZ
  have g3W : cov.toFun W x (VectorField.mlieBracket I (covApply cov X Y) Z x)
      + cov.toFun W x (VectorField.mlieBracket I Y (covApply cov X Z) x)
      + cov.toFun W x (VectorField.mlieBracket I (covApply cov Y Z) X x)
      + cov.toFun W x (VectorField.mlieBracket I Z (covApply cov Y X) x)
      + cov.toFun W x (VectorField.mlieBracket I (covApply cov Z X) Y x)
      + cov.toFun W x (VectorField.mlieBracket I X (covApply cov Z Y) x) = 0 := by
    rw [← map_add, ← map_add, ← map_add, ← map_add, ← map_add, g3, map_zero]
  linear_combination (norm := abel) g1XYZ + g1YZX + g1ZXY
    - g2XYZ - g2YZX - g2ZXY + g3W

end SecondBianchi

section LeviCivitaSecondBianchi

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem second_bianchi_levi_civita_metric
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {X Y Z W : Π b : M, TangentSpace I b} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Z))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W)) :
    nablaCurvSec (LeviCivita (I := I) g) X Y Z W x
      + nablaCurvSec (LeviCivita (I := I) g) Y Z X W x
      + nablaCurvSec (LeviCivita (I := I) g) Z X Y W x = 0 :=
  second_bianchi_levi_civita (LeviCivita (I := I) g)
    (LeviCivita_torsion_eq_zero (I := I) g) hX hY hZ hW

end LeviCivitaSecondBianchi

end Connection
end Integral
end DifferentialGeometry
