import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckMetricArmCoeffField
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceFibreBound
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingReverseHebeyToHs
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingCmOrderDropping
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.PointwiseToL2Packaging
import DifferentialGeometry.Geometry.Connection.TensorNabla.SlotInsertCovariantNaturality
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.SecondBianchi
import DifferentialGeometry.Analysis.Sobolev.GagliardoNirenbergLpFiberNorm
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqNormBridge
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradFibreNormPermutationInvariance
import DifferentialGeometry.Analysis.Sobolev.AntidiagonalTupleProductGrid

noncomputable section

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open TensorRSNabla
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization (metricCauchySchwarzBound ccTensorBilinSymm)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma fiberComponent_slotInsertEndoFib_eq
    (g₀ : SmoothRiemannianMetric I M) (x : M)
    (Λ : TangentSpace I x →L[ℝ] TangentSpace I x)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ i j : Fin n, g₀.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (K J : Fin 2 → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g₀ x 2 2
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) 2 0 x Λ)) n e K J =
      g₀.inner x (Λ (e (J 0))) (e (K 0)) * (if K 1 = J 1 then (1 : ℝ) else 0) := by
  have hcomp : fiberNormSqComponent (I := I) (M := M) g₀ x 2 2
      (show TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) 2 0 x Λ)) n e K J =
      Tensor0SSpace.toModel
        ((slotInsertEndoFib (I := I) (M := M) 2 0 x Λ) (coframeS (I := I) (M := M) g₀ x 2 e K))
        (fun k => e (J k)) := by
    unfold fiberNormSqComponent coframeS; rfl
  rw [hcomp, slotInsertEndoFib_apply_eval]
  rw [show (coframeS (I := I) (M := M) g₀ x 2 e K).toModel
        (Function.update (fun k => e (J k)) 0 (Λ (e (J 0))))
      = coframeS (I := I) (M := M) g₀ x 2 e K
        (Function.update (fun k => e (J k)) 0 (Λ (e (J 0)))) from rfl]
  rw [coframeS_apply, Fin.prod_univ_two, Function.update_self,
    Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0)]
  rw [g₀.symm x (e (K 0)) (Λ (e (J 0))), horth (K 1) (J 1)]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma riemannianFiberNormSq_slotInsertEndoFib_le_card_mul
    (g₀ : SmoothRiemannianMetric I M) (x : M)
    (Λ : TangentSpace I x →L[ℝ] TangentSpace I x) (B : ℝ)
    (hΛ : ∀ a : TangentSpace I x, g₀.inner x a a = 1 → g₀.inner x (Λ a) (Λ a) ≤ B)
    (_hB : 0 ≤ B) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) 2 0 x Λ)) ≤
      ((Module.finrank ℝ E : ℝ)) ^ 2 * B := by
  classical
  obtain ⟨n, e, bse, hn, hbse, horth, hpars, hrepr_v, hsum⟩ :=
    tangent_orthonormalBasis_witness (I := I) (M := M) g₀ x
  have hnE : n = Module.finrank ℝ E := by rw [hn]; rfl
  rw [riemannianFiberNormSq_eq_sum_componentSq_of_basis (I := I) (M := M) g₀ 2 2 x
    (show TensorRSSpace 2 2 I x from
      TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) 2 0 x Λ)) e bse hnE hbse horth]
  have hcompsq : ∀ (K J : Fin 2 → Fin n),
      (fiberNormSqComponent (I := I) (M := M) g₀ x 2 2
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) 2 0 x Λ)) n e K J) ^ 2 =
        (g₀.inner x (e (K 0)) (Λ (e (J 0)))) ^ 2 * (if K 1 = J 1 then (1 : ℝ) else 0) := by
    intro K J
    rw [fiberComponent_slotInsertEndoFib_eq (I := I) g₀ x Λ e horth K J]
    rw [g₀.symm x (Λ (e (J 0))) (e (K 0))]
    by_cases hkj : K 1 = J 1
    · simp only [hkj, if_true, mul_one]
    · simp only [hkj, if_false, mul_zero]; ring
  have hsumeq : (∑ K : Fin 2 → Fin n, ∑ J : Fin 2 → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g₀ x 2 2
          (show TensorRSSpace 2 2 I x from
            TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) 2 0 x Λ)) n e K J) ^ 2) =
      ∑ J : Fin 2 → Fin n, g₀.inner x (Λ (e (J 0))) (Λ (e (J 0))) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun J _ => ?_)
    rw [Finset.sum_congr rfl (fun K _ => hcompsq K J)]
    rw [← (finTwoArrowEquiv (Fin n)).symm.sum_comp
      (fun K : Fin 2 → Fin n => (g₀.inner x (e (K 0)) (Λ (e (J 0)))) ^ 2 *
        (if K 1 = J 1 then (1 : ℝ) else 0))]
    rw [Fintype.sum_prod_type]
    have hKsum : ∀ k0 : Fin n,
        (∑ k1 : Fin n, (g₀.inner x (e (((finTwoArrowEquiv (Fin n)).symm (k0, k1)) 0))
            (Λ (e (J 0)))) ^ 2 *
          (if ((finTwoArrowEquiv (Fin n)).symm (k0, k1)) 1 = J 1 then (1 : ℝ) else 0)) =
        (g₀.inner x (e k0) (Λ (e (J 0)))) ^ 2 := by
      intro k0
      rw [show (∑ k1 : Fin n, (g₀.inner x (e (((finTwoArrowEquiv (Fin n)).symm (k0, k1)) 0))
            (Λ (e (J 0)))) ^ 2 *
          (if ((finTwoArrowEquiv (Fin n)).symm (k0, k1)) 1 = J 1 then (1 : ℝ) else 0)) =
          ∑ k1 : Fin n, (g₀.inner x (e k0) (Λ (e (J 0)))) ^ 2 *
            (if k1 = J 1 then (1 : ℝ) else 0) from by
        refine Finset.sum_congr rfl (fun k1 _ => ?_)
        rfl]
      rw [← Finset.mul_sum, Finset.sum_ite_eq' Finset.univ (J 1) (fun _ => (1 : ℝ))]
      simp
    rw [Finset.sum_congr rfl (fun k0 _ => hKsum k0)]
    exact hpars (Λ (e (J 0)))
  rw [hsumeq]
  have hJbound : ∀ J : Fin 2 → Fin n,
      g₀.inner x (Λ (e (J 0))) (Λ (e (J 0))) ≤ B := by
    intro J
    refine hΛ (e (J 0)) ?_
    rw [horth (J 0) (J 0)]; simp
  calc (∑ J : Fin 2 → Fin n, g₀.inner x (Λ (e (J 0))) (Λ (e (J 0))))
      ≤ ∑ _J : Fin 2 → Fin n, B := Finset.sum_le_sum (fun J _ => hJbound J)
    _ = ((Module.finrank ℝ E : ℝ)) ^ 2 * B := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          Fintype.card_fin, nsmul_eq_mul, ← hnE]
        push_cast; ring

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma fiberComponent_slotInsertEndoFib_eq_general
    (g₀ : SmoothRiemannianMetric I M) (x : M) (s : ℕ) (k : Fin s)
    (Λ : TangentSpace I x →L[ℝ] TangentSpace I x)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ i j : Fin n, g₀.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (K J : Fin s → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g₀ x s s
        (show TensorRSSpace s s I x from
          TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) s k x Λ)) n e K J =
      g₀.inner x (e (K k)) (Λ (e (J k))) *
        ∏ l ∈ Finset.univ.erase k, (if K l = J l then (1 : ℝ) else 0) := by
  have hcomp : fiberNormSqComponent (I := I) (M := M) g₀ x s s
      (show TensorRSSpace s s I x from
        TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) s k x Λ)) n e K J =
      Tensor0SSpace.toModel
        ((slotInsertEndoFib (I := I) (M := M) s k x Λ) (coframeS (I := I) (M := M) g₀ x s e K))
        (fun l => e (J l)) := by
    unfold fiberNormSqComponent coframeS; rfl
  rw [hcomp, slotInsertEndoFib_apply_eval]
  rw [show (coframeS (I := I) (M := M) g₀ x s e K).toModel
        (Function.update (fun l => e (J l)) k (Λ (e (J k))))
      = coframeS (I := I) (M := M) g₀ x s e K
        (Function.update (fun l => e (J l)) k (Λ (e (J k)))) from rfl]
  rw [coframeS_apply]
  rw [← Finset.prod_erase_mul Finset.univ
    (fun l => g₀.inner x (e (K l))
      (Function.update (fun l => e (J l)) k (Λ (e (J k))) l)) (Finset.mem_univ k)]
  rw [Function.update_self]
  rw [g₀.symm x (e (K k)) (Λ (e (J k)))]
  rw [mul_comm]
  congr 1
  refine Finset.prod_congr rfl (fun l hl => ?_)
  have hlk : l ≠ k := Finset.ne_of_mem_erase hl
  rw [Function.update_of_ne hlk, horth (K l) (J l)]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma sum_compSq_slotInsertEndoFib_eq_normSq
    (g₀ : SmoothRiemannianMetric I M) (x : M) (s : ℕ) (k : Fin s)
    (Λ : TangentSpace I x →L[ℝ] TangentSpace I x)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ i j : Fin n, g₀.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (hpars : ∀ v : TangentSpace I x, ∑ i : Fin n, g₀.inner x (e i) v ^ 2 = g₀.inner x v v)
    (J : Fin s → Fin n) :
    (∑ K : Fin s → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g₀ x s s
          (show TensorRSSpace s s I x from
            TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) s k x Λ)) n e K J) ^ 2) =
      g₀.inner x (Λ (e (J k))) (Λ (e (J k))) := by
  classical
  have hcompsq : ∀ K : Fin s → Fin n,
      (fiberNormSqComponent (I := I) (M := M) g₀ x s s
        (show TensorRSSpace s s I x from
          TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) s k x Λ)) n e K J) ^ 2 =
        (g₀.inner x (e (K k)) (Λ (e (J k)))) ^ 2 *
          ∏ l ∈ Finset.univ.erase k, (if K l = J l then (1 : ℝ) else 0) := by
    intro K
    rw [fiberComponent_slotInsertEndoFib_eq_general (I := I) g₀ x s k Λ e horth K J]
    rw [mul_pow]
    congr 1
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl (fun l _ => ?_)
    by_cases hkj : K l = J l
    · simp [hkj]
    · simp [hkj]
  rw [Finset.sum_congr rfl (fun K _ => hcompsq K)]
  set ee := Equiv.funSplitAt k (Fin n) with hee
  rw [← (Equiv.sum_comp ee.symm
    (fun K : Fin s → Fin n => (g₀.inner x (e (K k)) (Λ (e (J k)))) ^ 2 *
      ∏ l ∈ Finset.univ.erase k, (if K l = J l then (1 : ℝ) else 0)))]
  rw [Fintype.sum_prod_type]
  have hkval : ∀ (m : Fin n) (ρ : {i : Fin s // i ≠ k} → Fin n), (ee.symm (m, ρ)) k = m := by
    intro m ρ; rw [hee]; simp [Equiv.funSplitAt, Equiv.piSplitAt]
  have hinner : ∀ m : Fin n,
      (∑ ρ : {i : Fin s // i ≠ k} → Fin n,
        (g₀.inner x (e ((ee.symm (m, ρ)) k)) (Λ (e (J k)))) ^ 2 *
          ∏ l ∈ Finset.univ.erase k,
            (if (ee.symm (m, ρ)) l = J l then (1 : ℝ) else 0)) =
        (g₀.inner x (e m) (Λ (e (J k)))) ^ 2 := by
    intro m
    have hcoe : ∀ (ρ : {i : Fin s // i ≠ k} → Fin n) (l : Fin s) (hl : l ≠ k),
        (ee.symm (m, ρ)) l = ρ ⟨l, hl⟩ := by
      intro ρ l hl
      rw [hee]; simp [Equiv.funSplitAt, Equiv.piSplitAt, hl]
    have hindic : ∀ ρ : {i : Fin s // i ≠ k} → Fin n,
        (∏ l ∈ Finset.univ.erase k,
          (if (ee.symm (m, ρ)) l = J l then (1 : ℝ) else 0)) =
          (if ρ = (fun j : {i : Fin s // i ≠ k} => J j) then (1 : ℝ) else 0) := by
      intro ρ
      by_cases hρ : ρ = (fun j : {i : Fin s // i ≠ k} => J j)
      · rw [if_pos hρ]
        refine Finset.prod_eq_one (fun l hl => ?_)
        have hlk : l ≠ k := Finset.ne_of_mem_erase hl
        rw [hcoe ρ l hlk, hρ, if_pos rfl]
      · rw [if_neg hρ]
        obtain ⟨j, hj⟩ : ∃ j : {i : Fin s // i ≠ k}, ρ j ≠ J j := by
          by_contra hcon
          exact hρ (funext (fun j => not_not.mp (fun h => hcon ⟨j, h⟩)))
        refine Finset.prod_eq_zero (i := (j : Fin s))
          (Finset.mem_erase.mpr ⟨j.2, Finset.mem_univ _⟩) ?_
        rw [hcoe ρ (j : Fin s) j.2, if_neg hj]
    rw [Finset.sum_congr rfl (fun ρ _ => by rw [hkval m ρ, hindic ρ] :
      ∀ ρ ∈ Finset.univ,
        (g₀.inner x (e ((ee.symm (m, ρ)) k)) (Λ (e (J k)))) ^ 2 *
          ∏ l ∈ Finset.univ.erase k,
            (if (ee.symm (m, ρ)) l = J l then (1 : ℝ) else 0) =
        (g₀.inner x (e m) (Λ (e (J k)))) ^ 2 *
          (if ρ = (fun j : {i : Fin s // i ≠ k} => J j) then (1 : ℝ) else 0))]
    rw [← Finset.mul_sum,
      Finset.sum_ite_eq' Finset.univ (fun j : {i : Fin s // i ≠ k} => J j) (fun _ => (1 : ℝ))]
    simp
  rw [Finset.sum_congr rfl (fun m _ => hinner m)]
  exact hpars (Λ (e (J k)))

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma riemannianFiberNormSq_slotInsertEndoFib_le_card_mul_general
    (g₀ : SmoothRiemannianMetric I M) (x : M) (s : ℕ) (k : Fin s)
    (Λ : TangentSpace I x →L[ℝ] TangentSpace I x) (B : ℝ)
    (hΛ : ∀ a : TangentSpace I x, g₀.inner x a a = 1 → g₀.inner x (Λ a) (Λ a) ≤ B)
    (_hB : 0 ≤ B) :
    riemannianFiberNormSq (I := I) (M := M) g₀ s s x
        (show TensorRSSpace s s I x from
          TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) s k x Λ)) ≤
      ((Module.finrank ℝ E : ℝ)) ^ s * B := by
  classical
  obtain ⟨n, e, bse, hn, hbse, horth, hpars, hrepr_v, hsum⟩ :=
    tangent_orthonormalBasis_witness (I := I) (M := M) g₀ x
  have hnE : n = Module.finrank ℝ E := by rw [hn]; rfl
  rw [riemannianFiberNormSq_eq_sum_componentSq_of_basis (I := I) (M := M) g₀ s s x
    (show TensorRSSpace s s I x from
      TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) s k x Λ)) e bse hnE hbse horth]
  rw [Finset.sum_comm]
  have hsumeq : (∑ J : Fin s → Fin n, ∑ K : Fin s → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g₀ x s s
          (show TensorRSSpace s s I x from
            TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) s k x Λ)) n e K J) ^ 2) =
      ∑ J : Fin s → Fin n, g₀.inner x (Λ (e (J k))) (Λ (e (J k))) := by
    refine Finset.sum_congr rfl (fun J _ => ?_)
    exact sum_compSq_slotInsertEndoFib_eq_normSq (I := I) g₀ x s k Λ e horth hpars J
  rw [hsumeq]
  have hJbound : ∀ J : Fin s → Fin n,
      g₀.inner x (Λ (e (J k))) (Λ (e (J k))) ≤ B := by
    intro J
    refine hΛ (e (J k)) ?_
    rw [horth (J k) (J k)]; simp
  calc (∑ J : Fin s → Fin n, g₀.inner x (Λ (e (J k))) (Λ (e (J k))))
      ≤ ∑ _J : Fin s → Fin n, B := Finset.sum_le_sum (fun J _ => hJbound J)
    _ = ((Module.finrank ℝ E : ℝ)) ^ s * B := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          Fintype.card_fin, nsmul_eq_mul, ← hnE]
        push_cast; ring

end Connection
end Integral
end DifferentialGeometry

end
