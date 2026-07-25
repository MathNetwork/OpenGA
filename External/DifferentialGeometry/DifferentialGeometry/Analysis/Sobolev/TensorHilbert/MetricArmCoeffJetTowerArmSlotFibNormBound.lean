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

open TensorMultilinear

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma curry_symm_smul_aux (s : ℕ) (x : M) (c : ℝ)
    (a : TangentSpace I x →L[ℝ] Tensor0SSpace (s+1) I x) :
    (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x).symm (c • a) =
      c • (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x).symm a := by
  apply Tensor0SSpace.toModel_injective (I := I) (M := M)
  ext vv
  rw [show vv = Fin.cons (vv 0) (Matrix.vecTail vv) from (Fin.cons_self_tail vv).symm]
  rw [← tensor0S_curry_apply_eval (T := (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x).symm (c • a))]
  simp only [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearMap.smul_apply,
    Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply]
  rw [← tensor0S_curry_apply_eval (T := (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x).symm a)]
  simp only [ContinuousLinearEquiv.apply_symm_apply]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma curry_symm_add_aux (s : ℕ) (x : M)
    (a b : TangentSpace I x →L[ℝ] Tensor0SSpace (s+1) I x) :
    (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x).symm (a + b) =
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x).symm a +
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x).symm b := by
  apply Tensor0SSpace.toModel_injective (I := I) (M := M)
  ext vv
  rw [show vv = Fin.cons (vv 0) (Matrix.vecTail vv) from (Fin.cons_self_tail vv).symm]
  rw [← tensor0S_curry_apply_eval (T := (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x).symm (a + b))]
  simp only [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearMap.add_apply,
    Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]
  rw [← tensor0S_curry_apply_eval (T := (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x).symm a),
    ← tensor0S_curry_apply_eval (T := (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x).symm b)]
  simp only [ContinuousLinearEquiv.apply_symm_apply]

def bilinearSlotInsertCurriedCLM (s : ℕ) (x : M)
    (Arm : TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x))
    (D : Tensor0SSpace (s + 1) I x) : TangentSpace I x →L[ℝ] Tensor0SSpace (s + 1) I x :=
  haveI : FiniteDimensional ℝ (Tensor0SSpace (s + 1) I x) := inferInstance
  LinearMap.toContinuousLinearMap
    { toFun := fun v0 => slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x (Arm v0) D
      map_add' := fun a b => by
        rw [map_add (Arm), slotInsertEndoFib_add_left (I := I) (M := M) (s+1) 0 x (Arm a) (Arm b),
          ContinuousLinearMap.add_apply]
      map_smul' := fun c a => by
        rw [map_smul (Arm)]
        rw [slotInsertEndoFib_smul_left (I := I) (M := M) (s+1) 0 x c (Arm a)]
        rfl }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma armCurryCLM_apply (s : ℕ) (x : M)
    (Arm : TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x))
    (D : Tensor0SSpace (s + 1) I x) (v0 : TangentSpace I x) :
    bilinearSlotInsertCurriedCLM (I := I) (M := M) s x Arm D v0 =
      slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x (Arm v0) D := rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma armCurryCLM_add (s : ℕ) (x : M)
    (Arm : TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x))
    (D D' : Tensor0SSpace (s + 1) I x) :
    bilinearSlotInsertCurriedCLM (I := I) (M := M) s x Arm (D + D') =
      bilinearSlotInsertCurriedCLM (I := I) (M := M) s x Arm D + bilinearSlotInsertCurriedCLM (I := I) (M := M) s x Arm D' := by
  apply ContinuousLinearMap.ext; intro v0
  simp only [ContinuousLinearMap.add_apply, armCurryCLM_apply, map_add]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma armCurryCLM_smul (s : ℕ) (x : M) (c : ℝ)
    (Arm : TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x))
    (D : Tensor0SSpace (s + 1) I x) :
    bilinearSlotInsertCurriedCLM (I := I) (M := M) s x Arm (c • D) =
      c • bilinearSlotInsertCurriedCLM (I := I) (M := M) s x Arm D := by
  apply ContinuousLinearMap.ext; intro v0
  simp only [ContinuousLinearMap.smul_apply, armCurryCLM_apply, map_smul]

def bilinearSlotInsertCLM (s : ℕ) (x : M)
    (Arm : TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)) :
    Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1 + 1) I x :=
  haveI : FiniteDimensional ℝ (Tensor0SSpace (s + 1) I x) := inferInstance
  LinearMap.toContinuousLinearMap
    { toFun := fun D => (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x).symm
        (bilinearSlotInsertCurriedCLM (I := I) (M := M) s x Arm D)
      map_add' := fun D D' => by
        rw [armCurryCLM_add, curry_symm_add_aux]
      map_smul' := fun c D => by
        rw [armCurryCLM_smul, curry_symm_smul_aux]; rfl }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma armSlotFib_apply (s : ℕ) (x : M)
    (Arm : TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x))
    (D : Tensor0SSpace (s + 1) I x) :
    bilinearSlotInsertCLM (I := I) (M := M) s x Arm D =
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x).symm
        (bilinearSlotInsertCurriedCLM (I := I) (M := M) s x Arm D) := rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma armSlotFib_apply_eval (s : ℕ) (x : M)
    (Arm : TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x))
    (D : Tensor0SSpace (s + 1) I x) (v : Fin (s + 1 + 1) → TangentSpace I x) :
    Tensor0SSpace.toModel (bilinearSlotInsertCLM (I := I) (M := M) s x Arm D) v =
      Tensor0SSpace.toModel
        (slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x (Arm (v 0)) D) (Matrix.vecTail v) := by
  rw [armSlotFib_apply]
  have hkey := tensor0S_curry_apply_eval (I := I) (M := M) (n := s + 1)
    (T := (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x).symm
      (bilinearSlotInsertCurriedCLM (I := I) (M := M) s x Arm D)) (v0 := v 0) (vs := Matrix.vecTail v)
  rw [ContinuousLinearEquiv.apply_symm_apply, armCurryCLM_apply] at hkey
  conv_lhs => rw [show v = Fin.cons (v 0) (Matrix.vecTail v) from (Fin.cons_self_tail v).symm]
  exact hkey.symm

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma fiberComponent_bilinearSlotInsertCLM_eq
    (g₀ : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    (Arm : TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x))
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ i j : Fin n, g₀.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (K : Fin (s + 1) → Fin n) (J : Fin (s + 1 + 1) → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g₀ x (s + 1) (s + 1 + 1)
        (show TensorRSSpace (s + 1) (s + 1 + 1) I x from
          TensorRSSpace.ofCLM (bilinearSlotInsertCLM (I := I) (M := M) s x Arm)) n e K J =
      g₀.inner x (e (K 0)) (Arm (e (J 0)) (e (J (Fin.succ 0)))) *
        ∏ l ∈ Finset.univ.erase (0 : Fin (s + 1)),
          (if K l = J (Fin.succ l) then (1 : ℝ) else 0) := by
  have hcomp : fiberNormSqComponent (I := I) (M := M) g₀ x (s + 1) (s + 1 + 1)
      (show TensorRSSpace (s + 1) (s + 1 + 1) I x from
        TensorRSSpace.ofCLM (bilinearSlotInsertCLM (I := I) (M := M) s x Arm)) n e K J =
      Tensor0SSpace.toModel
        (bilinearSlotInsertCLM (I := I) (M := M) s x Arm (coframeS (I := I) (M := M) g₀ x (s + 1) e K))
        (fun l => e (J l)) := by
    unfold fiberNormSqComponent coframeS; rfl
  rw [hcomp, armSlotFib_apply_eval, slotInsertEndoFib_apply_eval]
  change coframeS (I := I) (M := M) g₀ x (s + 1) e K
        (Function.update (Matrix.vecTail (fun l => e (J l))) 0
          (Arm (e (J 0)) (Matrix.vecTail (fun l => e (J l)) 0))) = _
  rw [coframeS_apply]
  rw [← Finset.prod_erase_mul Finset.univ
    (fun k => g₀.inner x (e (K k))
      (Function.update (Matrix.vecTail (fun l => e (J l))) 0
        (Arm (e (J 0)) (Matrix.vecTail (fun l => e (J l)) 0)) k))
    (Finset.mem_univ (0 : Fin (s + 1)))]
  rw [Function.update_self]
  have hvt0 : Matrix.vecTail (fun l => e (J l)) (0 : Fin (s + 1)) = e (J (Fin.succ 0)) := rfl
  rw [hvt0, mul_comm]
  congr 1
  refine Finset.prod_congr rfl (fun l hl => ?_)
  have hlk : l ≠ (0 : Fin (s + 1)) := Finset.ne_of_mem_erase hl
  rw [Function.update_of_ne hlk]
  change g₀.inner x (e (K l)) (Matrix.vecTail (fun l => e (J l)) l) = _
  rw [show Matrix.vecTail (fun l => e (J l)) l = e (J (Fin.succ l)) from rfl,
    horth (K l) (J (Fin.succ l))]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma sum_compSq_armSlotFib_eq_normSq
    (g₀ : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    (Arm : TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x))
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ i j : Fin n, g₀.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (hpars : ∀ v : TangentSpace I x, ∑ i : Fin n, g₀.inner x (e i) v ^ 2 = g₀.inner x v v)
    (J : Fin (s + 1 + 1) → Fin n) :
    (∑ K : Fin (s + 1) → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g₀ x (s + 1) (s + 1 + 1)
          (show TensorRSSpace (s + 1) (s + 1 + 1) I x from
            TensorRSSpace.ofCLM (bilinearSlotInsertCLM (I := I) (M := M) s x Arm)) n e K J) ^ 2) =
      g₀.inner x (Arm (e (J 0)) (e (J (Fin.succ 0)))) (Arm (e (J 0)) (e (J (Fin.succ 0)))) := by
  classical
  set w : TangentSpace I x := Arm (e (J 0)) (e (J (Fin.succ 0))) with hw_def
  have hcompsq : ∀ K : Fin (s + 1) → Fin n,
      (fiberNormSqComponent (I := I) (M := M) g₀ x (s + 1) (s + 1 + 1)
        (show TensorRSSpace (s + 1) (s + 1 + 1) I x from
          TensorRSSpace.ofCLM (bilinearSlotInsertCLM (I := I) (M := M) s x Arm)) n e K J) ^ 2 =
        (g₀.inner x (e (K 0)) w) ^ 2 *
          ∏ l ∈ Finset.univ.erase (0 : Fin (s + 1)),
            (if K l = J (Fin.succ l) then (1 : ℝ) else 0) := by
    intro K
    rw [fiberComponent_bilinearSlotInsertCLM_eq (I := I) g₀ x s Arm e horth K J, ← hw_def]
    rw [mul_pow]
    congr 1
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl (fun l _ => ?_)
    by_cases hkj : K l = J (Fin.succ l)
    · simp [hkj]
    · simp [hkj]
  rw [Finset.sum_congr rfl (fun K _ => hcompsq K)]
  set ee := Equiv.funSplitAt (0 : Fin (s + 1)) (Fin n) with hee
  rw [← (Equiv.sum_comp ee.symm
    (fun K : Fin (s + 1) → Fin n => (g₀.inner x (e (K 0)) w) ^ 2 *
      ∏ l ∈ Finset.univ.erase (0 : Fin (s + 1)),
        (if K l = J (Fin.succ l) then (1 : ℝ) else 0)))]
  rw [Fintype.sum_prod_type]
  have hkval : ∀ (m : Fin n) (ρ : {i : Fin (s + 1) // i ≠ 0} → Fin n),
      (ee.symm (m, ρ)) 0 = m := by
    intro m ρ; rw [hee]; simp [Equiv.funSplitAt, Equiv.piSplitAt]
  have hinner : ∀ m : Fin n,
      (∑ ρ : {i : Fin (s + 1) // i ≠ 0} → Fin n,
        (g₀.inner x (e ((ee.symm (m, ρ)) 0)) w) ^ 2 *
          ∏ l ∈ Finset.univ.erase (0 : Fin (s + 1)),
            (if (ee.symm (m, ρ)) l = J (Fin.succ l) then (1 : ℝ) else 0)) =
        (g₀.inner x (e m) w) ^ 2 := by
    intro m
    have hcoe : ∀ (ρ : {i : Fin (s + 1) // i ≠ 0} → Fin n) (l : Fin (s + 1)) (hl : l ≠ 0),
        (ee.symm (m, ρ)) l = ρ ⟨l, hl⟩ := by
      intro ρ l hl
      rw [hee]; simp [Equiv.funSplitAt, Equiv.piSplitAt, hl]
    have hindic : ∀ ρ : {i : Fin (s + 1) // i ≠ 0} → Fin n,
        (∏ l ∈ Finset.univ.erase (0 : Fin (s + 1)),
          (if (ee.symm (m, ρ)) l = J (Fin.succ l) then (1 : ℝ) else 0)) =
          (if ρ = (fun j : {i : Fin (s + 1) // i ≠ 0} => J (Fin.succ (j : Fin (s + 1))))
            then (1 : ℝ) else 0) := by
      intro ρ
      by_cases hρ : ρ = (fun j : {i : Fin (s + 1) // i ≠ 0} => J (Fin.succ (j : Fin (s + 1))))
      · rw [if_pos hρ]
        refine Finset.prod_eq_one (fun l hl => ?_)
        have hlk : l ≠ (0 : Fin (s + 1)) := Finset.ne_of_mem_erase hl
        rw [hcoe ρ l hlk, hρ, if_pos rfl]
      · rw [if_neg hρ]
        obtain ⟨j, hj⟩ : ∃ j : {i : Fin (s + 1) // i ≠ 0},
            ρ j ≠ J (Fin.succ (j : Fin (s + 1))) := by
          by_contra hcon
          exact hρ (funext (fun j => not_not.mp (fun h => hcon ⟨j, h⟩)))
        refine Finset.prod_eq_zero (i := (j : Fin (s + 1)))
          (Finset.mem_erase.mpr ⟨j.2, Finset.mem_univ _⟩) ?_
        rw [hcoe ρ (j : Fin (s + 1)) j.2, if_neg hj]
    rw [Finset.sum_congr rfl (fun ρ _ => by rw [hkval m ρ, hindic ρ] :
      ∀ ρ ∈ Finset.univ,
        (g₀.inner x (e ((ee.symm (m, ρ)) 0)) w) ^ 2 *
          ∏ l ∈ Finset.univ.erase (0 : Fin (s + 1)),
            (if (ee.symm (m, ρ)) l = J (Fin.succ l) then (1 : ℝ) else 0) =
        (g₀.inner x (e m) w) ^ 2 *
          (if ρ = (fun j : {i : Fin (s + 1) // i ≠ 0} => J (Fin.succ (j : Fin (s + 1))))
            then (1 : ℝ) else 0))]
    rw [← Finset.mul_sum,
      Finset.sum_ite_eq' Finset.univ
        (fun j : {i : Fin (s + 1) // i ≠ 0} => J (Fin.succ (j : Fin (s + 1)))) (fun _ => (1 : ℝ))]
    simp
  rw [Finset.sum_congr rfl (fun m _ => hinner m)]
  exact hpars w

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem riemannianFiberNormSq_bilinearSlotInsertCLM_le
    (g₀ : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    (Arm : TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)) (B : ℝ)
    (hArm : ∀ a b : TangentSpace I x, g₀.inner x a a = 1 → g₀.inner x b b = 1 →
      g₀.inner x (Arm a b) (Arm a b) ≤ B) :
    riemannianFiberNormSq (I := I) (M := M) g₀ (s + 1) (s + 1 + 1) x
        (show TensorRSSpace (s + 1) (s + 1 + 1) I x from
          TensorRSSpace.ofCLM (bilinearSlotInsertCLM (I := I) (M := M) s x Arm)) ≤
      ((Module.finrank ℝ E : ℝ)) ^ (s + 1 + 1) * B := by
  classical
  obtain ⟨n, e, bse, hn, hbse, horth, hpars, hrepr_v, hsum⟩ :=
    tangent_orthonormalBasis_witness (I := I) (M := M) g₀ x
  have hnE : n = Module.finrank ℝ E := by rw [hn]; rfl
  rw [riemannianFiberNormSq_eq_sum_componentSq_of_basis (I := I) (M := M) g₀ (s + 1) (s + 1 + 1) x
    (show TensorRSSpace (s + 1) (s + 1 + 1) I x from
      TensorRSSpace.ofCLM (bilinearSlotInsertCLM (I := I) (M := M) s x Arm)) e bse hnE hbse horth]
  rw [Finset.sum_comm]
  have hsumeq : (∑ J : Fin (s + 1 + 1) → Fin n, ∑ K : Fin (s + 1) → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g₀ x (s + 1) (s + 1 + 1)
          (show TensorRSSpace (s + 1) (s + 1 + 1) I x from
            TensorRSSpace.ofCLM (bilinearSlotInsertCLM (I := I) (M := M) s x Arm)) n e K J) ^ 2) =
      ∑ J : Fin (s + 1 + 1) → Fin n,
        g₀.inner x (Arm (e (J 0)) (e (J (Fin.succ 0)))) (Arm (e (J 0)) (e (J (Fin.succ 0)))) := by
    refine Finset.sum_congr rfl (fun J _ => ?_)
    exact sum_compSq_armSlotFib_eq_normSq (I := I) g₀ x s Arm e horth hpars J
  rw [hsumeq]
  have hJbound : ∀ J : Fin (s + 1 + 1) → Fin n,
      g₀.inner x (Arm (e (J 0)) (e (J (Fin.succ 0)))) (Arm (e (J 0)) (e (J (Fin.succ 0)))) ≤ B := by
    intro J
    refine hArm (e (J 0)) (e (J (Fin.succ 0))) ?_ ?_
    · rw [horth (J 0) (J 0)]; simp
    · rw [horth (J (Fin.succ 0)) (J (Fin.succ 0))]; simp
  calc (∑ J : Fin (s + 1 + 1) → Fin n,
          g₀.inner x (Arm (e (J 0)) (e (J (Fin.succ 0)))) (Arm (e (J 0)) (e (J (Fin.succ 0)))))
      ≤ ∑ _J : Fin (s + 1 + 1) → Fin n, B := Finset.sum_le_sum (fun J _ => hJbound J)
    _ = ((Module.finrank ℝ E : ℝ)) ^ (s + 1 + 1) * B := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          Fintype.card_fin, nsmul_eq_mul, ← hnE]
        push_cast; ring

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma rfns_armSlotFib_eq_sum_normSq_frame
    (g₀ : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    (Arm : TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x))
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (bse : Module.Basis (Fin n) ℝ (TangentSpace I x))
    (hn : n = Module.finrank ℝ E) (hbse : ∀ i : Fin n, bse i = e i)
    (horth : ∀ i j : Fin n, g₀.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (hpars : ∀ v : TangentSpace I x, ∑ i : Fin n, g₀.inner x (e i) v ^ 2 = g₀.inner x v v) :
    riemannianFiberNormSq (I := I) (M := M) g₀ (s + 1) (s + 1 + 1) x
        (show TensorRSSpace (s + 1) (s + 1 + 1) I x from
          TensorRSSpace.ofCLM (bilinearSlotInsertCLM (I := I) (M := M) s x Arm)) =
      (n : ℝ) ^ s * ∑ p : Fin n × Fin n,
        g₀.inner x (Arm (e p.1) (e p.2)) (Arm (e p.1) (e p.2)) := by
  classical
  rw [riemannianFiberNormSq_eq_sum_componentSq_of_basis (I := I) (M := M) g₀ (s + 1) (s + 1 + 1) x
    (show TensorRSSpace (s + 1) (s + 1 + 1) I x from
      TensorRSSpace.ofCLM (bilinearSlotInsertCLM (I := I) (M := M) s x Arm)) e bse hn hbse horth]
  rw [Finset.sum_comm]
  have hsumeq : (∑ J : Fin (s + 1 + 1) → Fin n, ∑ K : Fin (s + 1) → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g₀ x (s + 1) (s + 1 + 1)
          (show TensorRSSpace (s + 1) (s + 1 + 1) I x from
            TensorRSSpace.ofCLM (bilinearSlotInsertCLM (I := I) (M := M) s x Arm)) n e K J) ^ 2) =
      ∑ J : Fin (s + 1 + 1) → Fin n,
        g₀.inner x (Arm (e (J 0)) (e (J (Fin.succ 0)))) (Arm (e (J 0)) (e (J (Fin.succ 0)))) :=
    Finset.sum_congr rfl (fun J _ => sum_compSq_armSlotFib_eq_normSq (I := I) g₀ x s Arm e horth hpars J)
  rw [hsumeq]
  set F : Fin n → Fin n → ℝ := fun a b => g₀.inner x (Arm (e a) (e b)) (Arm (e a) (e b)) with hF
  have hJF : ∀ J : Fin (s + 1 + 1) → Fin n,
      g₀.inner x (Arm (e (J 0)) (e (J (Fin.succ 0)))) (Arm (e (J 0)) (e (J (Fin.succ 0)))) =
        F (J 0) (J (Fin.succ 0)) := fun J => rfl
  rw [Finset.sum_congr rfl (fun J _ => hJF J)]
  rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (s + 1 + 1) => Fin n))
        (fun pr : Fin n × (Fin (s + 1) → Fin n) => F pr.1 (pr.2 0))
        (fun J : Fin (s + 1 + 1) → Fin n => F (J 0) (J (Fin.succ 0)))
        (fun pr => by
          simp only [Fin.consEquiv_apply]
          rw [Fin.cons_zero, show (Fin.succ 0 : Fin (s + 1 + 1)) = (0 : Fin (s + 1)).succ from rfl,
            Fin.cons_succ])]
  rw [Fintype.sum_prod_type]
  have hinner : ∀ a : Fin n,
      (∑ r : Fin (s + 1) → Fin n, F a (r 0)) = (n : ℝ) ^ s * ∑ b : Fin n, F a b := by
    intro a
    rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (s + 1) => Fin n))
          (fun pr : Fin n × (Fin s → Fin n) => F a pr.1)
          (fun r : Fin (s + 1) → Fin n => F a (r 0))
          (fun pr => by simp [Fin.consEquiv])]
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_congr rfl (fun b _ => by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_pow] :
      ∀ b ∈ Finset.univ, (∑ _t : Fin s → Fin n, F a b) = (n : ℝ) ^ s * F a b)]
    rw [← Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun a _ => hinner a)]
  rw [← Finset.mul_sum]
  congr 1
  rw [Fintype.sum_prod_type]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem riemannianFiberNormSq_armSlotFib_spectator_eq
    (g₀ : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    (Arm : TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)) :
    riemannianFiberNormSq (I := I) (M := M) g₀ (s + 1) (s + 1 + 1) x
        (show TensorRSSpace (s + 1) (s + 1 + 1) I x from
          TensorRSSpace.ofCLM (bilinearSlotInsertCLM (I := I) (M := M) s x Arm)) =
      (Module.finrank ℝ E : ℝ) ^ s *
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + 1) x
          (show TensorRSSpace 1 (1 + 1) I x from
            TensorRSSpace.ofCLM (bilinearSlotInsertCLM (I := I) (M := M) 0 x Arm)) := by
  classical
  obtain ⟨n, e, bse, hn, hbse, horth, hpars, hrepr_v, hsum⟩ :=
    tangent_orthonormalBasis_witness (I := I) (M := M) g₀ x
  have hnE : n = Module.finrank ℝ E := by rw [hn]; rfl
  rw [rfns_armSlotFib_eq_sum_normSq_frame (I := I) g₀ x s Arm e bse hnE hbse horth hpars]
  rw [rfns_armSlotFib_eq_sum_normSq_frame (I := I) g₀ x 0 Arm e bse hnE hbse horth hpars]
  rw [pow_zero, one_mul]
  rw [show ((Module.finrank ℝ E : ℝ)) ^ s = (n : ℝ) ^ s from by rw [hnE]]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem armSlotFib_contMDiff (s : ℕ)
    (Arm : Π x : M, TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x))
    (harm : ∀ (V0 W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯),
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
          (Arm x (V0 x) (W x)))) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel (s + 1) (s + 1 + 1) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel (s + 1) (s + 1 + 1) ℝ E)
        (E := fun z : M => TensorRSSpace (s + 1) (s + 1 + 1) I z) x
        (TensorRSSpace.ofCLM (bilinearSlotInsertCLM (I := I) (M := M) s x (Arm x)))) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SModel (s + 1) ℝ E) (V₁ := fun x : M => Tensor0SSpace (s + 1) I x)
    (F₂ := Tensor0SModel (s + 1 + 1) ℝ E) (V₂ := fun x : M => Tensor0SSpace (s + 1 + 1) I x)
    (φ := fun x : M => (show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1 + 1) I x from
      bilinearSlotInsertCLM (I := I) (M := M) s x (Arm x)))
  intro D
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (s + 1 + 1)
  have hsec : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel (s + 1 + 1) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel (s + 1 + 1) ℝ E)
        (E := fun z : M => Tensor0SSpace (s + 1 + 1) I z) x
        (bilinearSlotInsertCLM (I := I) (M := M) s x (Arm x) (D x))) := by
    refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
      (fun x : M => (bilinearSlotInsertCLM (I := I) (M := M) s x (Arm x) (D x) :
        Bundle.continuousMultilinearMap ℝ (s + 1 + 1) E (TangentSpace I) x))).mpr ?_
    intro σ x₀
    set b := Module.finBasis ℝ E with hb
    set e₁ := trivializationAt E (TangentSpace I : M → Type _) x₀ with he₁def
    have he₁ : x₀ ∈ e₁.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x₀
    have hframe := e₁.isLocalFrameOn_localFrame_baseSet I (⊤ : ℕ∞) b
    obtain ⟨Y, hY⟩ := hframe.exists_contMDiffSection_eqOn_nhd e₁.open_baseSet he₁
    have harmField : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
          (Arm x (Y (σ 0) x) (Y (σ 1) x))) := harm (Y (σ 0)) (Y (σ 1))
    have hscalar : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
        (fun x : M => Tensor0SSpace.toModel (D x)
          (Function.update (fun i : Fin (s + 1) => Y (σ (Fin.succ i)) x) 0
            (Arm x (Y (σ 0) x) (Y (σ 1) x)))) x₀ := by
      refine TensorMultilinear.contMDiffAt_section_apply (n := s + 1) (x₀ := x₀)
        (fun x : M => D x) (D.contMDiff x₀)
        (fun i : Fin (s + 1) => fun x : M =>
          Function.update (fun j : Fin (s + 1) => Y (σ (Fin.succ j)) x) 0
            (Arm x (Y (σ 0) x) (Y (σ 1) x)) i) ?_
      intro i
      by_cases hi : i = 0
      · subst hi
        refine (harmField x₀).congr_of_eventuallyEq (Filter.Eventually.of_forall (fun x => ?_))
        simp only [Function.update_self]
      · refine ((Y (σ (Fin.succ i))).contMDiff x₀).congr_of_eventuallyEq
          (Filter.Eventually.of_forall (fun x => ?_))
        simp only [Function.update_of_ne hi]
    refine hscalar.congr_of_eventuallyEq ?_
    have h_base₁ : ∀ᶠ x in 𝓝 x₀, x ∈ e₁.baseSet := e₁.open_baseSet.mem_nhds he₁
    filter_upwards [h_base₁, hY] with x hx₁ hYx
    rw [continuousMultilinearMap_basis_repr]
    have hframeS : ∀ k : Fin (s + 1 + 1), e₁.symmL ℝ x (b (σ k)) = (Y (σ k)) x := by
      intro k
      rw [hYx (σ k), Trivialization.localFrame_apply_of_mem_baseSet (hx := hx₁)]
      simp [Trivialization.basisAt]
    change Tensor0SSpace.toModel (bilinearSlotInsertCLM (I := I) (M := M) s x (Arm x) (D x))
        (fun j : Fin (s + 1 + 1) => e₁.symmL ℝ x (b (σ j))) = _
    rw [armSlotFib_apply_eval]
    rw [slotInsertEndoFib_apply_eval]
    rw [Tensor0SSpace.toModel]
    have htail0 : Matrix.vecTail (fun j : Fin (s + 1 + 1) => e₁.symmL ℝ x (b (σ j))) 0 =
        (Y (σ 1)) x := by
      change e₁.symmL ℝ x (b (σ (Fin.succ 0))) = _
      rw [hframeS (Fin.succ 0)]; rfl
    have hupd : Function.update (Matrix.vecTail
          (fun j : Fin (s + 1 + 1) => e₁.symmL ℝ x (b (σ j)))) 0
          (Arm x (e₁.symmL ℝ x (b (σ 0)))
            (Matrix.vecTail (fun j : Fin (s + 1 + 1) => e₁.symmL ℝ x (b (σ j))) 0)) =
        Function.update (fun i : Fin (s + 1) => (Y (σ (Fin.succ i))) x) 0
          (Arm x ((Y (σ 0)) x) ((Y (σ 1)) x)) := by
      funext j
      by_cases hj : j = 0
      · subst hj
        simp only [Function.update_self, hframeS 0, htail0]
      · rw [Function.update_of_ne hj, Function.update_of_ne hj]
        change e₁.symmL ℝ x (b (σ (Fin.succ j))) = (Y (σ (Fin.succ j))) x
        rw [hframeS (Fin.succ j)]
    rw [hupd]
  refine hsec.congr ?_
  intro x
  rfl

end Connection
end Integral
end DifferentialGeometry

end
