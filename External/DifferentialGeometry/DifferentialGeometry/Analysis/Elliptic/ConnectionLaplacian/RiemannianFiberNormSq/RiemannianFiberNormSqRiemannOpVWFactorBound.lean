import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.TensorRicciCommutatorRiemannianFiberNormBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqLeChartAlphaSummandSum
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.BigOperators.Ring.Finset


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 1200000

open Bundle Manifold Set FiberBundle NormedSpace Filter CovariantDerivative
open scoped Manifold Topology ContDiff BigOperators RealInnerProductSpace

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Laplacian
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

noncomputable def fiberNormSqComponent
    (g : SmoothRiemannianMetric I M) (b : M) (r s : ℕ)
    (S : TensorRSSpace r s I b)
    (n : ℕ) (e : Fin n → TangentSpace I b)
    (K : Fin r → Fin n) (J : Fin s → Fin n) : ℝ :=
  (S : Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b)
      ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin r) ℝ).compContinuousLinearMap
        (fun k => g.inner b (e (K k))))
      (fun k => e (J k))

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma fiberNormSqSummand_eq_component_sq
    (g : SmoothRiemannianMetric I M) (b : M) (r s : ℕ)
    (S : TensorRSSpace r s I b)
    (n : ℕ) (e : Fin n → TangentSpace I b)
    (K : Fin r → Fin n) (J : Fin s → Fin n) :
    fiberNormSqSummand (I := I) (M := M) g b r s S n e K J =
      fiberNormSqComponent (I := I) (M := M) g b r s S n e K J ^ 2 := rfl

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma fiberNormSqComponent_add
    (g : SmoothRiemannianMetric I M) (b : M) (r s : ℕ)
    (S S' : TensorRSSpace r s I b)
    (n : ℕ) (e : Fin n → TangentSpace I b)
    (K : Fin r → Fin n) (J : Fin s → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g b r s (S + S') n e K J =
      fiberNormSqComponent (I := I) (M := M) g b r s S n e K J +
        fiberNormSqComponent (I := I) (M := M) g b r s S' n e K J := by
  unfold fiberNormSqComponent
  rw [show ((S + S' : TensorRSSpace r s I b) :
        Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b)
        ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin r) ℝ).compContinuousLinearMap
          (fun k => g.inner b (e (K k)))) =
      (S : Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b)
        ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin r) ℝ).compContinuousLinearMap
          (fun k => g.inner b (e (K k)))) +
      (S' : Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b)
        ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin r) ℝ).compContinuousLinearMap
          (fun k => g.inner b (e (K k)))) from rfl]
  rfl

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma fiberNormSqComponent_smul
    (g : SmoothRiemannianMetric I M) (b : M) (r s : ℕ)
    (c : ℝ) (S : TensorRSSpace r s I b)
    (n : ℕ) (e : Fin n → TangentSpace I b)
    (K : Fin r → Fin n) (J : Fin s → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g b r s (c • S) n e K J =
      c * fiberNormSqComponent (I := I) (M := M) g b r s S n e K J := by
  unfold fiberNormSqComponent
  rw [show ((c • S : TensorRSSpace r s I b) :
        Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b)
        ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin r) ℝ).compContinuousLinearMap
          (fun k => g.inner b (e (K k)))) =
      c • (S : Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b)
        ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin r) ℝ).compContinuousLinearMap
          (fun k => g.inner b (e (K k)))) from rfl]
  rfl

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma fiberNormSqComponent_zero
    (g : SmoothRiemannianMetric I M) (b : M) (r s : ℕ)
    (n : ℕ) (e : Fin n → TangentSpace I b)
    (K : Fin r → Fin n) (J : Fin s → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g b r s
      (0 : TensorRSSpace r s I b) n e K J = 0 := rfl

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma fiberNormSqComponent_sum
    {ι : Type*} (g : SmoothRiemannianMetric I M) (b : M) (r s : ℕ)
    (t : Finset ι) (F : ι → TensorRSSpace r s I b)
    (n : ℕ) (e : Fin n → TangentSpace I b)
    (K : Fin r → Fin n) (J : Fin s → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g b r s (∑ i ∈ t, F i) n e K J =
      ∑ i ∈ t, fiberNormSqComponent (I := I) (M := M) g b r s (F i) n e K J := by
  classical
  refine Finset.cons_induction ?_ ?_ t
  · simp [fiberNormSqComponent_zero]
  · intro a s' ha ih
    rw [Finset.sum_cons, Finset.sum_cons, fiberNormSqComponent_add, ih]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma exists_orthonormal_frame_riemannianFiberNormSq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M) :
    ∃ (n : ℕ) (e : Fin n → TangentSpace I b),
      n = Module.finrank ℝ (TangentSpace I b) ∧
      (∀ i j : Fin n, g.inner b (e i) (e j) = if i = j then (1 : ℝ) else 0) ∧
      (∀ v : TangentSpace I b, ∑ i : Fin n, g.inner b (e i) v ^ 2 = g.inner b v v) ∧
      ∀ S : TensorRSSpace r s I b,
        riemannianFiberNormSq (I := I) (M := M) g r s b S =
          ∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
            fiberNormSqSummand (I := I) (M := M) g b r s S n e K J := by
  classical
  let cd : InnerProductSpace.Core ℝ (TangentSpace I b) := g.toRiemannianMetric.toCore b
  have hc : ContinuousAt (fun v : TangentSpace I b => cd.inner v v) 0 :=
    g.toRiemannianMetric.continuousAt b
  have hbnd : Bornology.IsVonNBounded ℝ {v : TangentSpace I b |
      RCLike.re (cd.inner v v) < 1} :=
    g.toRiemannianMetric.isVonNBounded b
  letI nag : NormedAddCommGroup (TangentSpace I b) :=
    cd.toNormedAddCommGroupOfTopology hc hbnd
  letI ips : InnerProductSpace ℝ (TangentSpace I b) :=
    InnerProductSpace.ofCoreOfTopology cd hc hbnd
  set n : ℕ := Module.finrank ℝ (TangentSpace I b) with hn_def
  set e : OrthonormalBasis (Fin n) ℝ (TangentSpace I b) := stdOrthonormalBasis ℝ _ with he_def
  have hinner_eq : ∀ u v : TangentSpace I b, (inner ℝ u v : ℝ) = g.inner b u v :=
    fun u v => rfl
  refine ⟨n, fun i => e i, rfl, ?_, ?_, ?_⟩
  · intro i j
    have horth : Orthonormal ℝ (fun i : Fin n => e i) := e.orthonormal
    have hite := (orthonormal_iff_ite (𝕜 := ℝ) (E := TangentSpace I b)).mp horth i j
    rw [← hinner_eq (e i) (e j)]
    exact hite
  · intro v
    have hpars : ∑ i : Fin n, (inner ℝ (e i) v : ℝ) ^ 2 = ‖v‖ ^ 2 :=
      OrthonormalBasis.sum_sq_inner_right e v
    have hnorm_sq : (‖v‖ : ℝ) ^ 2 = g.inner b v v := by
      have hri : (inner ℝ v v : ℝ) = ‖v‖ ^ 2 := real_inner_self_eq_norm_sq v
      rw [hinner_eq v v] at hri
      exact hri.symm
    calc
      ∑ i : Fin n, g.inner b (e i) v ^ 2
          = ∑ i : Fin n, (inner ℝ (e i) v : ℝ) ^ 2 := by
            refine Finset.sum_congr rfl (fun i _ => ?_); rw [hinner_eq (e i) v]
      _ = ‖v‖ ^ 2 := hpars
      _ = g.inner b v v := hnorm_sq
  · intro S
    rfl

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma tangent_frame_expansion
    (g : SmoothRiemannianMetric I M) (b : M) :
    ∃ (n : ℕ) (e : Fin n → TangentSpace I b),
      n = Module.finrank ℝ (TangentSpace I b) ∧
      (∀ i j : Fin n, g.inner b (e i) (e j) = if i = j then (1 : ℝ) else 0) ∧
      (∀ v : TangentSpace I b, ∑ i : Fin n, g.inner b (e i) v ^ 2 = g.inner b v v) ∧
      (∀ v : TangentSpace I b, v = ∑ i : Fin n, g.inner b (e i) v • e i) ∧
      ∀ S : TensorRSSpace 0 2 I b,
        riemannianFiberNormSq (I := I) (M := M) g 0 2 b S =
          ∑ K : Fin 0 → Fin n, ∑ J : Fin 2 → Fin n,
            fiberNormSqSummand (I := I) (M := M) g b 0 2 S n e K J := by
  classical
  let cd : InnerProductSpace.Core ℝ (TangentSpace I b) := g.toRiemannianMetric.toCore b
  have hc : ContinuousAt (fun v : TangentSpace I b => cd.inner v v) 0 :=
    g.toRiemannianMetric.continuousAt b
  have hbnd : Bornology.IsVonNBounded ℝ {v : TangentSpace I b |
      RCLike.re (cd.inner v v) < 1} :=
    g.toRiemannianMetric.isVonNBounded b
  letI nag : NormedAddCommGroup (TangentSpace I b) :=
    cd.toNormedAddCommGroupOfTopology hc hbnd
  letI ips : InnerProductSpace ℝ (TangentSpace I b) :=
    InnerProductSpace.ofCoreOfTopology cd hc hbnd
  set n : ℕ := Module.finrank ℝ (TangentSpace I b) with hn_def
  set e : OrthonormalBasis (Fin n) ℝ (TangentSpace I b) := stdOrthonormalBasis ℝ _ with he_def
  have hinner_eq : ∀ u v : TangentSpace I b, (inner ℝ u v : ℝ) = g.inner b u v :=
    fun u v => rfl
  refine ⟨n, fun i => e i, rfl, ?_, ?_, ?_, ?_⟩
  · intro i j
    have horth : Orthonormal ℝ (fun i : Fin n => e i) := e.orthonormal
    have hite := (orthonormal_iff_ite (𝕜 := ℝ) (E := TangentSpace I b)).mp horth i j
    rw [← hinner_eq (e i) (e j)]
    exact hite
  · intro v
    have hpars : ∑ i : Fin n, (inner ℝ (e i) v : ℝ) ^ 2 = ‖v‖ ^ 2 :=
      OrthonormalBasis.sum_sq_inner_right e v
    have hnorm_sq : (‖v‖ : ℝ) ^ 2 = g.inner b v v := by
      have hri : (inner ℝ v v : ℝ) = ‖v‖ ^ 2 := real_inner_self_eq_norm_sq v
      rw [hinner_eq v v] at hri
      exact hri.symm
    calc
      ∑ i : Fin n, g.inner b (e i) v ^ 2
          = ∑ i : Fin n, (inner ℝ (e i) v : ℝ) ^ 2 := by
            refine Finset.sum_congr rfl (fun i _ => ?_); rw [hinner_eq (e i) v]
      _ = ‖v‖ ^ 2 := hpars
      _ = g.inner b v v := hnorm_sq
  · intro v
    have hrepr : ∑ i : Fin n, (inner ℝ (e i) v : ℝ) • e i = v :=
      OrthonormalBasis.sum_repr' e v
    have hcongr : (∑ i : Fin n, g.inner b (e i) v • e i) =
        ∑ i : Fin n, (inner ℝ (e i) v : ℝ) • e i := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hinner_eq (e i) v]
    rw [hcongr, hrepr]
  · intro S
    rfl

private lemma clm_apply_smul_sum
    {α : Type*} [AddCommMonoid α] [Module ℝ α] [TopologicalSpace α]
    {β : Type*} [AddCommMonoid β] [Module ℝ β] [TopologicalSpace β]
    {ι : Type*} (R : α →L[ℝ] β) (s : Finset ι) (c : ι → ℝ) (f : ι → α) :
    R (∑ i ∈ s, c i • f i) = ∑ i ∈ s, c i • R (f i) := by
  rw [map_sum]
  exact Finset.sum_congr rfl (fun i _ => map_smul R (c i) (f i))


omit [NeZero (Module.finrank ℝ E)] in
lemma riemannOp_tensorCov_frame_expand
    (g : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (hv_expand : ∀ u : TangentSpace I x, u = ∑ i : Fin n, g.inner x (e i) u • e i)
    (v w : TangentSpace I x) (T : TensorRSSpace 0 2 I x) :
    riemannOp (tensorCov (I := I) g 0 2) x v w T =
      ∑ i : Fin n, ∑ j : Fin n,
        (g.inner x (e i) v * g.inner x (e j) w) •
          riemannOp (tensorCov (I := I) g 0 2) x (e i) (e j) T := by
  classical
  set R := riemannOp (tensorCov (I := I) g 0 2) x with hR_def
  have hv : v = ∑ i : Fin n, g.inner x (e i) v • e i := hv_expand v
  have hw : w = ∑ j : Fin n, g.inner x (e j) w • e j := hv_expand w
  have hRv : R v = ∑ i : Fin n, g.inner x (e i) v • R (e i) := by
    conv_lhs => rw [hv]
    exact clm_apply_smul_sum R Finset.univ (fun i => g.inner x (e i) v) e
  have hRvw : R v w = ∑ i : Fin n, g.inner x (e i) v • R (e i) w := by
    rw [hRv, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [ContinuousLinearMap.smul_apply]
  have hRei_w : ∀ i : Fin n, R (e i) w =
      ∑ j : Fin n, g.inner x (e j) w • R (e i) (e j) := by
    intro i
    conv_lhs => rw [hw]
    exact clm_apply_smul_sum (R (e i)) Finset.univ (fun j => g.inner x (e j) w) e
  have hRvwT : R v w T = ∑ i : Fin n, g.inner x (e i) v • (R (e i) w) T := by
    rw [hRvw, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [ContinuousLinearMap.smul_apply]
  rw [hRvwT]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hRei_w i]
  rw [ContinuousLinearMap.sum_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [ContinuousLinearMap.smul_apply, smul_smul]

omit [NeZero (Module.finrank ℝ E)] in
lemma fiberNormSqSummand_riemannOp_tensorCov_vw_le
    (g : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (hpars : ∀ u : TangentSpace I x, ∑ i : Fin n, g.inner x (e i) u ^ 2 = g.inner x u u)
    (hexpand : ∀ u : TangentSpace I x, u = ∑ i : Fin n, g.inner x (e i) u • e i)
    (v w : TangentSpace I x) (T : TensorRSSpace 0 2 I x)
    (K : Fin 0 → Fin n) (J : Fin 2 → Fin n) :
    fiberNormSqSummand (I := I) (M := M) g x 0 2
        (riemannOp (tensorCov (I := I) g 0 2) x v w T) n e K J ≤
      g.inner x v v * g.inner x w w *
        ∑ i : Fin n, ∑ j : Fin n,
          fiberNormSqSummand (I := I) (M := M) g x 0 2
            (riemannOp (tensorCov (I := I) g 0 2) x (e i) (e j) T) n e K J := by
  classical
  set R := riemannOp (tensorCov (I := I) g 0 2) x with hR_def
  have hexp : R v w T =
      ∑ i : Fin n, ∑ j : Fin n,
        (g.inner x (e i) v * g.inner x (e j) w) • R (e i) (e j) T :=
    riemannOp_tensorCov_frame_expand (I := I) (M := M) g x e hexpand v w T
  set c : Fin n × Fin n → ℝ := fun p => g.inner x (e p.1) v * g.inner x (e p.2) w with hc_def
  set a : Fin n × Fin n → ℝ := fun p =>
    fiberNormSqComponent (I := I) (M := M) g x 0 2 (R (e p.1) (e p.2) T) n e K J with ha_def
  have hcomp_eq :
      fiberNormSqComponent (I := I) (M := M) g x 0 2 (R v w T) n e K J =
        ∑ p : Fin n × Fin n, c p * a p := by
    rw [hexp]
    rw [show (∑ i : Fin n, ∑ j : Fin n,
          (g.inner x (e i) v * g.inner x (e j) w) • R (e i) (e j) T) =
        ∑ p : Fin n × Fin n,
          (g.inner x (e p.1) v * g.inner x (e p.2) w) • R (e p.1) (e p.2) T from
      (Fintype.sum_prod_type'
        (f := fun i j => (g.inner x (e i) v * g.inner x (e j) w) • R (e i) (e j) T)).symm]
    rw [fiberNormSqComponent_sum]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [fiberNormSqComponent_smul]
  rw [fiberNormSqSummand_eq_component_sq, hcomp_eq]
  have hCS : (∑ p : Fin n × Fin n, c p * a p) ^ 2 ≤
      (∑ p : Fin n × Fin n, c p ^ 2) * ∑ p : Fin n × Fin n, a p ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ c a
  refine hCS.trans ?_
  have hcsq : (∑ p : Fin n × Fin n, c p ^ 2) =
      g.inner x v v * g.inner x w w := by
    have hsplit : (∑ p : Fin n × Fin n, c p ^ 2) =
        (∑ i : Fin n, g.inner x (e i) v ^ 2) *
          ∑ j : Fin n, g.inner x (e j) w ^ 2 := by
      rw [Finset.sum_mul_sum]
      rw [Fintype.sum_prod_type (f := fun p : Fin n × Fin n => c p ^ 2)]
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      rw [hc_def]
      ring
    rw [hsplit, hpars v, hpars w]
  have hasq : (∑ p : Fin n × Fin n, a p ^ 2) =
      ∑ i : Fin n, ∑ j : Fin n,
        fiberNormSqSummand (I := I) (M := M) g x 0 2 (R (e i) (e j) T) n e K J := by
    rw [Fintype.sum_prod_type (f := fun p : Fin n × Fin n => a p ^ 2)]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [ha_def, fiberNormSqSummand_eq_component_sq]
  rw [hcsq, hasq]

omit [NeZero (Module.finrank ℝ E)] in
theorem riemannianFiberNormSq_riemannOp_tensorCov_vw_factor_le
    (g : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) (T : TensorRSSpace 0 2 I x) :
    ∃ (n : ℕ) (e : Fin n → TangentSpace I x),
      riemannianFiberNormSq (I := I) (M := M) g 0 2 x
          (riemannOp (tensorCov (I := I) g 0 2) x v w T) ≤
        g.inner x v v * g.inner x w w *
          ∑ i : Fin n, ∑ j : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g 0 2 x
              (riemannOp (tensorCov (I := I) g 0 2) x (e i) (e j) T) := by
  classical
  obtain ⟨n, e, _hn, _horth, hpars, hexpand, hrepr⟩ :=
    tangent_frame_expansion (I := I) (M := M) g x
  refine ⟨n, e, ?_⟩
  set R := riemannOp (tensorCov (I := I) g 0 2) x with hR_def
  set B : ℝ := g.inner x v v * g.inner x w w with hB_def
  have hvv_nonneg : 0 ≤ g.inner x v v := by
    rw [← hpars v]; exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hww_nonneg : 0 ≤ g.inner x w w := by
    rw [← hpars w]; exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hB_nonneg : 0 ≤ B := mul_nonneg hvv_nonneg hww_nonneg
  rw [hrepr (R v w T)]
  have hterm : ∀ K : Fin 0 → Fin n, ∀ J : Fin 2 → Fin n,
      fiberNormSqSummand (I := I) (M := M) g x 0 2 (R v w T) n e K J ≤
        B * ∑ i : Fin n, ∑ j : Fin n,
          fiberNormSqSummand (I := I) (M := M) g x 0 2 (R (e i) (e j) T) n e K J := by
    intro K J
    rw [hB_def]
    exact fiberNormSqSummand_riemannOp_tensorCov_vw_le
      (I := I) (M := M) g x e hpars hexpand v w T K J
  calc
    (∑ K : Fin 0 → Fin n, ∑ J : Fin 2 → Fin n,
        fiberNormSqSummand (I := I) (M := M) g x 0 2 (R v w T) n e K J)
        ≤ ∑ K : Fin 0 → Fin n, ∑ J : Fin 2 → Fin n,
            B * ∑ i : Fin n, ∑ j : Fin n,
              fiberNormSqSummand (I := I) (M := M) g x 0 2 (R (e i) (e j) T) n e K J := by
          refine Finset.sum_le_sum (fun K _ => ?_)
          exact Finset.sum_le_sum (fun J _ => hterm K J)
    _ = B * ∑ K : Fin 0 → Fin n, ∑ J : Fin 2 → Fin n,
            ∑ i : Fin n, ∑ j : Fin n,
              fiberNormSqSummand (I := I) (M := M) g x 0 2 (R (e i) (e j) T) n e K J := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun K _ => ?_)
          rw [Finset.mul_sum]
    _ = B * ∑ i : Fin n, ∑ j : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g 0 2 x (R (e i) (e j) T) := by
          congr 1
          set F : (Fin 0 → Fin n) → (Fin 2 → Fin n) → Fin n → Fin n → ℝ :=
            fun K J i j =>
              fiberNormSqSummand (I := I) (M := M) g x 0 2 (R (e i) (e j) T) n e K J
            with hF_def
          have hrhs : (∑ i : Fin n, ∑ j : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g 0 2 x (R (e i) (e j) T)) =
              ∑ i : Fin n, ∑ j : Fin n, ∑ K : Fin 0 → Fin n, ∑ J : Fin 2 → Fin n,
                F K J i j := by
            refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
            rw [hrepr (R (e i) (e j) T)]
          rw [hrhs]
          have hLHS : (∑ K : Fin 0 → Fin n, ∑ J : Fin 2 → Fin n,
                ∑ i : Fin n, ∑ j : Fin n, F K J i j) =
              ∑ q : (Fin 0 → Fin n) × (Fin 2 → Fin n),
                ∑ p : Fin n × Fin n, F q.1 q.2 p.1 p.2 := by
            have hinner : ∀ K J,
                (∑ i : Fin n, ∑ j : Fin n, F K J i j) =
                  ∑ p : Fin n × Fin n, F K J p.1 p.2 :=
              fun K J => (Fintype.sum_prod_type' (f := fun i j => F K J i j)).symm
            calc
              (∑ K : Fin 0 → Fin n, ∑ J : Fin 2 → Fin n,
                  ∑ i : Fin n, ∑ j : Fin n, F K J i j)
                  = ∑ K : Fin 0 → Fin n, ∑ J : Fin 2 → Fin n,
                      ∑ p : Fin n × Fin n, F K J p.1 p.2 := by
                    refine Finset.sum_congr rfl (fun K _ =>
                      Finset.sum_congr rfl (fun J _ => ?_))
                    rw [hinner K J]
              _ = ∑ q : (Fin 0 → Fin n) × (Fin 2 → Fin n),
                      ∑ p : Fin n × Fin n, F q.1 q.2 p.1 p.2 :=
                    (Fintype.sum_prod_type' (f := fun K J =>
                      ∑ p : Fin n × Fin n, F K J p.1 p.2)).symm
          have hRHS : (∑ i : Fin n, ∑ j : Fin n,
                ∑ K : Fin 0 → Fin n, ∑ J : Fin 2 → Fin n, F K J i j) =
              ∑ p : Fin n × Fin n,
                ∑ q : (Fin 0 → Fin n) × (Fin 2 → Fin n), F q.1 q.2 p.1 p.2 := by
            have hinner : ∀ i j,
                (∑ K : Fin 0 → Fin n, ∑ J : Fin 2 → Fin n, F K J i j) =
                  ∑ q : (Fin 0 → Fin n) × (Fin 2 → Fin n), F q.1 q.2 i j :=
              fun i j => (Fintype.sum_prod_type' (f := fun K J => F K J i j)).symm
            calc
              (∑ i : Fin n, ∑ j : Fin n,
                  ∑ K : Fin 0 → Fin n, ∑ J : Fin 2 → Fin n, F K J i j)
                  = ∑ i : Fin n, ∑ j : Fin n,
                      ∑ q : (Fin 0 → Fin n) × (Fin 2 → Fin n), F q.1 q.2 i j := by
                    refine Finset.sum_congr rfl (fun i _ =>
                      Finset.sum_congr rfl (fun j _ => ?_))
                    rw [hinner i j]
              _ = ∑ p : Fin n × Fin n,
                      ∑ q : (Fin 0 → Fin n) × (Fin 2 → Fin n), F q.1 q.2 p.1 p.2 :=
                    (Fintype.sum_prod_type' (f := fun i j =>
                      ∑ q : (Fin 0 → Fin n) × (Fin 2 → Fin n), F q.1 q.2 i j)).symm
          rw [hLHS, hRHS]
          exact Finset.sum_comm

end Connection
end Integral
end DifferentialGeometry

end
