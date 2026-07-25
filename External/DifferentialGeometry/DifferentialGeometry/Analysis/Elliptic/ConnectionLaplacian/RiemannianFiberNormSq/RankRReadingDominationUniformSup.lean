import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.CovGradBundleEquivFiberNormFrameSum
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqRiemannOpHigherRankParseval
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqTensorInnerBridge
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.TensorCurvatureUnitEvalBridge
import DifferentialGeometry.Geometry.Connection.TensorNabla.TensorSlotwiseCurvatureRS


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set FiberBundle NormedSpace Filter CovariantDerivative
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open Tensor0SBundle Tensor0SNabla

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma fiberNormSqComponent_covGradBundleEquivSymm_slice_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (T : TensorRSSpace r (s + 1) I x)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (K : Fin r → Fin n) (J : Fin s → Fin n) (a : Fin n) :
    fiberNormSqComponent (I := I) (M := M) g x r s
        ((covGradBundleEquiv (I := I) (M := M) r s x).symm T (e a)) n e K J =
      fiberNormSqComponent (I := I) (M := M) g x r (s + 1) T n e K (Fin.cons a J) := by
  unfold fiberNormSqComponent
  set ωK : Tensor0SSpace r I x :=
    (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin r) ℝ).compContinuousLinearMap
      (fun k => g.inner x (e (K k))) with hωK
  rw [show (((covGradBundleEquiv (I := I) (M := M) r s x).symm T (e a)) ωK
        (fun k => e (J k)) : ℝ) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
          ((covGradBundleEquiv (I := I) (M := M) r s x).symm T) (e a)) ωK)
        (fun k => e (J k)) from rfl]
  rw [covGradBundleEquiv_symm_apply_eval (I := I) (M := M) r s x T (e a) ωK (fun k => e (J k))]
  congr 1
  exact (Fin.comp_cons e a J).symm

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma riemannianFiberNormSq_eq_sum_fiberNormSqComponent_sq_of_basis
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) (S : TensorRSSpace r s I x)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (bse : Module.Basis (Fin n) ℝ (TangentSpace I x))
    (hn : n = Module.finrank ℝ E) (hbse : ∀ i : Fin n, bse i = e i)
    (horth : ∀ a b : Fin n, g.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0) :
    riemannianFiberNormSq (I := I) (M := M) g r s x S =
      ∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g x r s S n e K J) ^ 2 := by
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x S]
  rw [tensorInnerPointwise_eq_sum_componentS_mul (I := I) (M := M) g r s x e bse hn hbse horth S S]
  refine Finset.sum_congr rfl (fun K _ => Finset.sum_congr rfl (fun J _ => ?_))
  rw [pow_two]

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem riemannianFiberNormSq_covGradBundleEquiv_symm_slice_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (T : TensorRSSpace r (s + 1) I x)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hBorth : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x (B i x) (B j x) = if i = j then (1 : ℝ) else 0)
    (i : Fin (Module.finrank ℝ E)) :
    riemannianFiberNormSq (I := I) (M := M) g r s x
        ((covGradBundleEquiv (I := I) (M := M) r s x).symm T (B i x)) ≤
      riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x T := by
  classical
  set eC : Fin (Module.finrank ℝ E) → TangentSpace I x := fun j => B j x with heC_def
  have horthC : ∀ a b : Fin (Module.finrank ℝ E),
      g.inner x (eC a) (eC b) = if a = b then (1 : ℝ) else 0 := fun a b => hBorth a b
  haveI : Nonempty (Fin (Module.finrank ℝ E)) :=
    ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))⟩⟩

  have he_li : LinearIndependent ℝ eC := by
    rw [linearIndependent_iff']
    intro fs c hsum k hk_mem
    have h_zero : g.inner x (eC k) (∑ j ∈ fs, c j • eC j) = 0 := by rw [hsum]; simp
    rw [map_sum] at h_zero
    have h_pull : ∀ j ∈ fs,
        g.inner x (eC k) (c j • eC j) = c j * (if k = j then (1 : ℝ) else 0) := by
      intro j _
      rw [map_smul, horthC k j, smul_eq_mul]
    rw [Finset.sum_congr rfl h_pull] at h_zero
    rw [Finset.sum_eq_single k (fun j _ hj => by rw [if_neg (Ne.symm hj), mul_zero])
      (fun hk => absurd hk_mem hk)] at h_zero
    rwa [if_pos rfl, mul_one] at h_zero
  have hcard : Fintype.card (Fin (Module.finrank ℝ E)) = Module.finrank ℝ (TangentSpace I x) := by
    rw [Fintype.card_fin]; rfl
  set bse : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
    basisOfLinearIndependentOfCardEqFinrank he_li hcard with hbse_def
  have hbse : ∀ i : Fin (Module.finrank ℝ E), bse i = eC i := fun i => by
    rw [hbse_def, coe_basisOfLinearIndependentOfCardEqFinrank]
  have hnd : Module.finrank ℝ E = Module.finrank ℝ E := rfl
  rw [riemannianFiberNormSq_eq_sum_fiberNormSqComponent_sq_of_basis (I := I) (M := M) g r s x _ eC bse hnd hbse
    horthC]
  rw [riemannianFiberNormSq_eq_sum_fiberNormSqComponent_sq_of_basis (I := I) (M := M) g r (s + 1) x T eC bse hnd
    hbse horthC]
  have hBix : B i x = eC i := rfl
  rw [hBix]

  have hcomp : ∀ K : Fin r → Fin (Module.finrank ℝ E), ∀ J : Fin s → Fin (Module.finrank ℝ E),
      (fiberNormSqComponent (I := I) (M := M) g x r s
          ((covGradBundleEquiv (I := I) (M := M) r s x).symm T (eC i))
          (Module.finrank ℝ E) eC K J) ^ 2 =
        (fiberNormSqComponent (I := I) (M := M) g x r (s + 1) T
          (Module.finrank ℝ E) eC K (Fin.cons i J)) ^ 2 := by
    intro K J
    rw [fiberNormSqComponent_covGradBundleEquivSymm_slice_eq (I := I) (M := M) g r s x T eC K J i]
  rw [Finset.sum_congr rfl (fun K _ => Finset.sum_congr rfl (fun J _ => hcomp K J))]

  refine Finset.sum_le_sum (fun K _ => ?_)
  let consi : (Fin s → Fin (Module.finrank ℝ E)) → (Fin (s + 1) → Fin (Module.finrank ℝ E)) :=
    fun J => Fin.cons i J
  let fJ : (Fin (s + 1) → Fin (Module.finrank ℝ E)) → ℝ :=
    fun J' => (fiberNormSqComponent (I := I) (M := M) g x r (s + 1) T
      (Module.finrank ℝ E) eC K J') ^ 2
  have hinj : Function.Injective consi := Fin.cons_right_injective (α := fun _ => _) i
  have hsumeq : (∑ J : Fin s → Fin (Module.finrank ℝ E),
        (fiberNormSqComponent (I := I) (M := M) g x r (s + 1) T (Module.finrank ℝ E)
          eC K (Fin.cons i J)) ^ 2) =
      ∑ J' ∈ (Finset.univ.image consi), fJ J' :=
    (Finset.sum_image (s := (Finset.univ : Finset (Fin s → Fin (Module.finrank ℝ E))))
      (g := consi) (f := fJ) (fun J1 _ J2 _ hJ => hinj hJ)).symm
  rw [hsumeq]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun J' _ _ => sq_nonneg _)

end Connection
end Integral
end DifferentialGeometry
