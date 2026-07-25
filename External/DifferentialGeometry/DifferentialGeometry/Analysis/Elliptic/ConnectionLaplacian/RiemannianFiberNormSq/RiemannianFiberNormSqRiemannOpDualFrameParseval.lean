import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqRiemannOpVWFactorBound
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

noncomputable def tensor00Scalar (x : M) :
    Tensor0SSpace 0 I x →L[ℝ] ℝ :=
  (continuousMultilinearCurryFin0 ℝ E ℝ).toContinuousLinearMap.comp
    (Tensor0SSpace.toModelL (I := I) 0 x)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma tensor00Scalar_apply (x : M) (τ : Tensor0SSpace 0 I x)
    (m : Fin 0 → TangentSpace I x) :
    tensor00Scalar (I := I) (M := M) x τ = τ m := by
  unfold tensor00Scalar
  rw [ContinuousLinearMap.comp_apply]
  have h1 : (Tensor0SSpace.toModelL (I := I) 0 x) τ = Tensor0SSpace.toModel τ := rfl
  rw [h1]
  change (continuousMultilinearCurryFin0 ℝ E ℝ) (Tensor0SSpace.toModel τ) = _
  rw [continuousMultilinearCurryFin0_apply]
  change τ (0 : Fin 0 → TangentSpace I x) = τ m
  congr 1
  exact Subsingleton.elim _ _

noncomputable def coframePair
    (g : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (a b : Fin n) :
    Tensor0SSpace 2 I x :=
  (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 2) ℝ).compContinuousLinearMap
    (fun k : Fin 2 => g.inner x (e ((![a, b] : Fin 2 → Fin n) k)))

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma coframe2_apply
    (g : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (a b : Fin n)
    (u : Fin 2 → TangentSpace I x) :
    coframePair (I := I) (M := M) g x e a b u =
      g.inner x (e a) (u 0) * g.inner x (e b) (u 1) := by
  unfold coframePair
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebra_apply]
  rw [Fin.prod_univ_two]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one]

noncomputable def dualTensorFrame
    (g : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (a b : Fin n) :
    TensorRSSpace 0 2 I x :=
  (tensor00Scalar (I := I) (M := M) x).smulRight
    (coframePair (I := I) (M := M) g x e a b)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma dualTensorFrame_apply
    (g : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (a b : Fin n)
    (τ : Tensor0SSpace 0 I x) :
    (dualTensorFrame (I := I) (M := M) g x e a b :
        Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x) τ =
      tensor00Scalar (I := I) (M := M) x τ • coframePair (I := I) (M := M) g x e a b := by
  unfold dualTensorFrame
  rw [ContinuousLinearMap.smulRight_apply]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma fiberNormSqComponent_dualTensorFrame
    (g : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (a b : Fin n) (K : Fin 0 → Fin n) (J : Fin 2 → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g x 0 2
        (dualTensorFrame (I := I) (M := M) g x e a b) n e K J =
      (if a = J 0 then (1 : ℝ) else 0) * (if b = J 1 then (1 : ℝ) else 0) := by
  classical
  unfold fiberNormSqComponent
  rw [show ((dualTensorFrame (I := I) (M := M) g x e a b :
          Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x)
          ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
            (fun k => g.inner x (e (K k))))) =
        tensor00Scalar (I := I) (M := M) x
            ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
              (fun k => g.inner x (e (K k)))) •
          coframePair (I := I) (M := M) g x e a b from
      dualTensorFrame_apply (I := I) (M := M) g x e a b _]
  have hscalar : tensor00Scalar (I := I) (M := M) x
      ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
        (fun k => g.inner x (e (K k)))) = 1 := by
    rw [tensor00Scalar_apply (I := I) (M := M) x _ (fun k : Fin 0 => k.elim0),
      ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousMultilinearMap.mkPiAlgebra_apply]
    simp
  rw [hscalar, one_smul]
  rw [coframe2_apply (I := I) (M := M) g x e a b (fun k : Fin 2 => e (J k))]
  rw [horth a (J 0), horth b (J 1)]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma tensor02_coframe_expansion
    (g : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (bse : Module.Basis (Fin n) ℝ (TangentSpace I x))
    (hbse : ∀ i : Fin n, bse i = e i)
    (horth : ∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (A : Tensor0SSpace 2 I x) :
    A = ∑ a : Fin n, ∑ b : Fin n,
      (A (fun k : Fin 2 => e ((![a, b] : Fin 2 → Fin n) k))) •
        coframePair (I := I) (M := M) g x e a b := by
  classical
  apply tensor0SSpace_ext (𝕜 := ℝ) 2 x
  intro u
  let Acmm : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => TangentSpace I x) ℝ := A
  let Rcmm : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => TangentSpace I x) ℝ :=
    ∑ a : Fin n, ∑ b : Fin n,
      (A (fun k : Fin 2 => e ((![a, b] : Fin 2 → Fin n) k))) •
        coframePair (I := I) (M := M) g x e a b
  suffices h : Acmm.toMultilinearMap = Rcmm.toMultilinearMap by
    exact congrArg
      (fun (T : MultilinearMap ℝ (fun _ : Fin 2 => TangentSpace I x) ℝ) => T u) h
  refine Module.Basis.ext_multilinear (e := fun _ : Fin 2 => bse) ?_
  intro v
  have hbtuple : (fun i : Fin 2 => bse (v i)) = (fun i : Fin 2 => e (v i)) := by
    funext i; rw [hbse (v i)]
  change Acmm (fun i : Fin 2 => bse (v i)) = Rcmm (fun i : Fin 2 => bse (v i))
  rw [hbtuple]
  have hRHS_eval : Rcmm (fun i : Fin 2 => e (v i)) =
      ∑ a : Fin n, ∑ b : Fin n,
        (A (fun k : Fin 2 => e ((![a, b] : Fin 2 → Fin n) k))) *
          coframePair (I := I) (M := M) g x e a b (fun i : Fin 2 => e (v i)) := by
    change (∑ a : Fin n, ∑ b : Fin n,
          (A (fun k : Fin 2 => e ((![a, b] : Fin 2 → Fin n) k))) •
            coframePair (I := I) (M := M) g x e a b)
        (fun i : Fin 2 => e (v i)) = _
    rw [ContinuousMultilinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [ContinuousMultilinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  change Acmm (fun i : Fin 2 => e (v i)) = _
  rw [hRHS_eval]
  have hcoframe : ∀ a b : Fin n,
      coframePair (I := I) (M := M) g x e a b (fun i : Fin 2 => e (v i)) =
        (if a = v 0 then (1 : ℝ) else 0) * (if b = v 1 then (1 : ℝ) else 0) := by
    intro a b
    rw [coframe2_apply (I := I) (M := M) g x e a b (fun i : Fin 2 => e (v i))]
    rw [horth a (v 0), horth b (v 1)]
  rw [show (∑ a : Fin n, ∑ b : Fin n,
        (A (fun k : Fin 2 => e ((![a, b] : Fin 2 → Fin n) k))) *
          coframePair (I := I) (M := M) g x e a b (fun i : Fin 2 => e (v i))) =
      ∑ a : Fin n, ∑ b : Fin n,
        (A (fun k : Fin 2 => e ((![a, b] : Fin 2 → Fin n) k))) *
          ((if a = v 0 then (1 : ℝ) else 0) * (if b = v 1 then (1 : ℝ) else 0)) from by
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    rw [hcoframe a b]]
  rw [Finset.sum_comm]
  rw [Finset.sum_eq_single (v 1)]
  · rw [Finset.sum_eq_single (v 0)]
    · simp only [if_pos, mul_one]
      congr 1
      funext k
      fin_cases k <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one]
    · intro a _ ha
      rw [if_neg ha, zero_mul, mul_zero]
    · intro h; exact absurd (Finset.mem_univ (v 0)) h
  · intro b _ hb
    refine Finset.sum_eq_zero (fun a _ => ?_)
    rw [if_neg hb, mul_zero, mul_zero]
  · intro h; exact absurd (Finset.mem_univ (v 1)) h

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma tangent_orthonormalBasis_witness
    (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ (n : ℕ) (e : Fin n → TangentSpace I x)
      (bse : Module.Basis (Fin n) ℝ (TangentSpace I x)),
      n = Module.finrank ℝ (TangentSpace I x) ∧
      (∀ i : Fin n, bse i = e i) ∧
      (∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0) ∧
      (∀ v : TangentSpace I x, ∑ i : Fin n, g.inner x (e i) v ^ 2 = g.inner x v v) ∧
      (∀ v : TangentSpace I x, v = ∑ i : Fin n, g.inner x (e i) v • e i) ∧
      ∀ S : TensorRSSpace 0 2 I x,
        riemannianFiberNormSq (I := I) (M := M) g 0 2 x S =
          ∑ K : Fin 0 → Fin n, ∑ J : Fin 2 → Fin n,
            fiberNormSqSummand (I := I) (M := M) g x 0 2 S n e K J := by
  classical
  let cd : InnerProductSpace.Core ℝ (TangentSpace I x) := g.toRiemannianMetric.toCore x
  have hc : ContinuousAt (fun v : TangentSpace I x => cd.inner v v) 0 :=
    g.toRiemannianMetric.continuousAt x
  have hbnd : Bornology.IsVonNBounded ℝ {v : TangentSpace I x |
      RCLike.re (cd.inner v v) < 1} :=
    g.toRiemannianMetric.isVonNBounded x
  letI nag : NormedAddCommGroup (TangentSpace I x) :=
    cd.toNormedAddCommGroupOfTopology hc hbnd
  letI ips : InnerProductSpace ℝ (TangentSpace I x) :=
    InnerProductSpace.ofCoreOfTopology cd hc hbnd
  set n : ℕ := Module.finrank ℝ (TangentSpace I x) with hn_def
  set eob : OrthonormalBasis (Fin n) ℝ (TangentSpace I x) := stdOrthonormalBasis ℝ _
    with heob_def
  have hinner_eq : ∀ u v : TangentSpace I x, (inner ℝ u v : ℝ) = g.inner x u v :=
    fun u v => rfl
  refine ⟨n, fun i => eob i, eob.toBasis, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [OrthonormalBasis.coe_toBasis]
  · intro i j
    have horth : Orthonormal ℝ (fun i : Fin n => eob i) := eob.orthonormal
    have hite := (orthonormal_iff_ite (𝕜 := ℝ) (E := TangentSpace I x)).mp horth i j
    rw [← hinner_eq (eob i) (eob j)]
    exact hite
  · intro v
    have hpars : ∑ i : Fin n, (inner ℝ (eob i) v : ℝ) ^ 2 = ‖v‖ ^ 2 :=
      OrthonormalBasis.sum_sq_inner_right eob v
    have hnorm_sq : (‖v‖ : ℝ) ^ 2 = g.inner x v v := by
      have hri : (inner ℝ v v : ℝ) = ‖v‖ ^ 2 := real_inner_self_eq_norm_sq v
      rw [hinner_eq v v] at hri
      exact hri.symm
    calc
      ∑ i : Fin n, g.inner x (eob i) v ^ 2
          = ∑ i : Fin n, (inner ℝ (eob i) v : ℝ) ^ 2 := by
            refine Finset.sum_congr rfl (fun i _ => ?_); rw [hinner_eq (eob i) v]
      _ = ‖v‖ ^ 2 := hpars
      _ = g.inner x v v := hnorm_sq
  · intro v
    have hrepr : ∑ i : Fin n, (inner ℝ (eob i) v : ℝ) • eob i = v :=
      OrthonormalBasis.sum_repr' eob v
    have hcongr : (∑ i : Fin n, g.inner x (eob i) v • eob i) =
        ∑ i : Fin n, (inner ℝ (eob i) v : ℝ) • eob i := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hinner_eq (eob i) v]
    rw [hcongr, hrepr]
  · intro S
    rfl

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma tensor_dualFrame_expansion
    (g : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (bse : Module.Basis (Fin n) ℝ (TangentSpace I x))
    (hbse : ∀ i : Fin n, bse i = e i)
    (horth : ∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (T : TensorRSSpace 0 2 I x) (K₀ : Fin 0 → Fin n) :
    T = ∑ a : Fin n, ∑ b : Fin n,
      (fiberNormSqComponent (I := I) (M := M) g x 0 2 T n e K₀ (![a, b])) •
        dualTensorFrame (I := I) (M := M) g x e a b := by
  classical
  apply tensorRSSpace_ext (𝕜 := ℝ) 0 2 x
  intro τ
  set c : ℝ := tensor00Scalar (I := I) (M := M) x τ with hc_def
  set ωK : Tensor0SSpace 0 I x :=
    (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
      (fun k => g.inner x (e (K₀ k))) with hωK_def
  have hτ : τ = c • ωK := by
    apply tensor0SSpace_ext (𝕜 := ℝ) 0 x
    intro m
    rw [hc_def, tensor00Scalar_apply (I := I) (M := M) x τ m]
    rw [ContinuousMultilinearMap.smul_apply, smul_eq_mul]
    have hωK1 : ωK m = 1 := by
      rw [hωK_def, ContinuousMultilinearMap.compContinuousLinearMap_apply,
        ContinuousMultilinearMap.mkPiAlgebra_apply]
      simp
    rw [hωK1, mul_one]
  have hLHS : (T : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x) τ =
      c • (T : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x) ωK := by
    rw [hτ, ContinuousLinearMap.map_smul]
  set A : Tensor0SSpace 2 I x :=
    (T : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x) ωK with hA_def
  have hA_expand : A = ∑ a : Fin n, ∑ b : Fin n,
      (A (fun k : Fin 2 => e ((![a, b] : Fin 2 → Fin n) k))) •
        coframePair (I := I) (M := M) g x e a b :=
    tensor02_coframe_expansion (I := I) (M := M) g x e bse hbse horth A
  have hAeval : ∀ a b : Fin n,
      A (fun k : Fin 2 => e ((![a, b] : Fin 2 → Fin n) k)) =
        fiberNormSqComponent (I := I) (M := M) g x 0 2 T n e K₀ (![a, b]) := by
    intro a b
    rw [hA_def]
    rfl
  have hLHS' : (T : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x) τ =
      ∑ a : Fin n, ∑ b : Fin n,
        (fiberNormSqComponent (I := I) (M := M) g x 0 2 T n e K₀ (![a, b])) •
          (c • coframePair (I := I) (M := M) g x e a b) := by
    rw [hLHS, hA_expand, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [hAeval a b, smul_comm]
  have hRHS' : (∑ a : Fin n, ∑ b : Fin n,
        (fiberNormSqComponent (I := I) (M := M) g x 0 2 T n e K₀ (![a, b])) •
          dualTensorFrame (I := I) (M := M) g x e a b :
            Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x) τ =
      ∑ a : Fin n, ∑ b : Fin n,
        (fiberNormSqComponent (I := I) (M := M) g x 0 2 T n e K₀ (![a, b])) •
          (c • coframePair (I := I) (M := M) g x e a b) := by
    rw [ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [ContinuousLinearMap.smul_apply,
      dualTensorFrame_apply (I := I) (M := M) g x e a b τ, ← hc_def]
  rw [hLHS', hRHS']

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma riemannianFiberNormSq_eq_sum_component_sq
    (g : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (hrepr : ∀ S : TensorRSSpace 0 2 I x,
      riemannianFiberNormSq (I := I) (M := M) g 0 2 x S =
        ∑ K : Fin 0 → Fin n, ∑ J : Fin 2 → Fin n,
          fiberNormSqSummand (I := I) (M := M) g x 0 2 S n e K J)
    (T : TensorRSSpace 0 2 I x) (K₀ : Fin 0 → Fin n) :
    riemannianFiberNormSq (I := I) (M := M) g 0 2 x T =
      ∑ a : Fin n, ∑ b : Fin n,
        (fiberNormSqComponent (I := I) (M := M) g x 0 2 T n e K₀ (![a, b])) ^ 2 := by
  classical
  rw [hrepr T]
  rw [Finset.sum_eq_single K₀]
  · rw [show (∑ J : Fin 2 → Fin n,
          fiberNormSqSummand (I := I) (M := M) g x 0 2 T n e K₀ J) =
        ∑ J : Fin 2 → Fin n,
          (fiberNormSqComponent (I := I) (M := M) g x 0 2 T n e K₀ J) ^ 2 from by
      refine Finset.sum_congr rfl (fun J _ => ?_)
      rw [fiberNormSqSummand_eq_component_sq]]
    rw [← Fintype.sum_prod_type'
      (f := fun a b => (fiberNormSqComponent (I := I) (M := M) g x 0 2 T n e K₀ (![a, b])) ^ 2)]
    rw [← Equiv.sum_comp (finTwoArrowEquiv (Fin n)).symm
      (fun J : Fin 2 → Fin n =>
        (fiberNormSqComponent (I := I) (M := M) g x 0 2 T n e K₀ J) ^ 2)]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [finTwoArrowEquiv_symm_apply]
  · intro K _ hK
    exact absurd (Subsingleton.elim K K₀) hK
  · intro h; exact absurd (Finset.mem_univ K₀) h

omit [NeZero (Module.finrank ℝ E)] in
lemma sum_riemannianFiberNormSq_riemannOp_le_Cx
    (g : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (bse : Module.Basis (Fin n) ℝ (TangentSpace I x))
    (hbse : ∀ i : Fin n, bse i = e i)
    (horth : ∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (hrepr : ∀ S : TensorRSSpace 0 2 I x,
      riemannianFiberNormSq (I := I) (M := M) g 0 2 x S =
        ∑ K : Fin 0 → Fin n, ∑ J : Fin 2 → Fin n,
          fiberNormSqSummand (I := I) (M := M) g x 0 2 S n e K J)
    (T : TensorRSSpace 0 2 I x) :
    (∑ i : Fin n, ∑ j : Fin n,
        riemannianFiberNormSq (I := I) (M := M) g 0 2 x
          (riemannOp (tensorCov (I := I) g 0 2) x (e i) (e j) T)) ≤
      (∑ i : Fin n, ∑ j : Fin n, ∑ a : Fin n, ∑ b : Fin n,
          riemannianFiberNormSq (I := I) (M := M) g 0 2 x
            (riemannOp (tensorCov (I := I) g 0 2) x (e i) (e j)
              (dualTensorFrame (I := I) (M := M) g x e a b))) *
        riemannianFiberNormSq (I := I) (M := M) g 0 2 x T := by
  classical
  let K₀ : Fin 0 → Fin n := fun k => k.elim0
  set R := riemannOp (tensorCov (I := I) g 0 2) x with hR_def
  have hParseval := riemannianFiberNormSq_eq_sum_component_sq
    (I := I) (M := M) g x e hrepr T K₀
  have hTexp := tensor_dualFrame_expansion (I := I) (M := M) g x e bse hbse horth T K₀
  set cT : Fin n × Fin n → ℝ :=
    fun p => fiberNormSqComponent (I := I) (M := M) g x 0 2 T n e K₀ (![p.1, p.2]) with hcT
  have hpair : ∀ i j : Fin n,
      riemannianFiberNormSq (I := I) (M := M) g 0 2 x (R (e i) (e j) T) ≤
        (∑ a : Fin n, ∑ b : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g 0 2 x
              (R (e i) (e j) (dualTensorFrame (I := I) (M := M) g x e a b))) *
          riemannianFiberNormSq (I := I) (M := M) g 0 2 x T := by
    intro i j
    have hRT : R (e i) (e j) T =
        ∑ a : Fin n, ∑ b : Fin n,
          cT (a, b) • R (e i) (e j) (dualTensorFrame (I := I) (M := M) g x e a b) := by
      conv_lhs => rw [hTexp]
      rw [map_sum]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [map_sum]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [ContinuousLinearMap.map_smul]
    rw [hRT]
    rw [hrepr (∑ a : Fin n, ∑ b : Fin n,
      cT (a, b) • R (e i) (e j) (dualTensorFrame (I := I) (M := M) g x e a b))]
    have hterm : ∀ (Kx : Fin 0 → Fin n) (Jx : Fin 2 → Fin n),
        fiberNormSqSummand (I := I) (M := M) g x 0 2
            (∑ a : Fin n, ∑ b : Fin n,
              cT (a, b) • R (e i) (e j) (dualTensorFrame (I := I) (M := M) g x e a b))
            n e Kx Jx ≤
          (∑ p : Fin n × Fin n, cT p ^ 2) *
            ∑ p : Fin n × Fin n,
              fiberNormSqSummand (I := I) (M := M) g x 0 2
                (R (e i) (e j) (dualTensorFrame (I := I) (M := M) g x e p.1 p.2)) n e Kx Jx := by
      intro Kx Jx
      rw [fiberNormSqSummand_eq_component_sq]
      have hcomp :
          fiberNormSqComponent (I := I) (M := M) g x 0 2
              (∑ a : Fin n, ∑ b : Fin n,
                cT (a, b) • R (e i) (e j) (dualTensorFrame (I := I) (M := M) g x e a b))
              n e Kx Jx =
            ∑ p : Fin n × Fin n,
              cT p *
                fiberNormSqComponent (I := I) (M := M) g x 0 2
                  (R (e i) (e j) (dualTensorFrame (I := I) (M := M) g x e p.1 p.2)) n e Kx Jx := by
        rw [show (∑ a : Fin n, ∑ b : Fin n,
              cT (a, b) • R (e i) (e j) (dualTensorFrame (I := I) (M := M) g x e a b)) =
            ∑ p : Fin n × Fin n,
              cT p • R (e i) (e j) (dualTensorFrame (I := I) (M := M) g x e p.1 p.2) from
          (Fintype.sum_prod_type'
            (f := fun a b =>
              cT (a, b) • R (e i) (e j)
                (dualTensorFrame (I := I) (M := M) g x e a b))).symm]
        rw [fiberNormSqComponent_sum]
        refine Finset.sum_congr rfl (fun p _ => ?_)
        rw [fiberNormSqComponent_smul]
      rw [hcomp]
      exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ cT
        (fun p => fiberNormSqComponent (I := I) (M := M) g x 0 2
          (R (e i) (e j) (dualTensorFrame (I := I) (M := M) g x e p.1 p.2)) n e Kx Jx)
    calc
      (∑ Kx : Fin 0 → Fin n, ∑ Jx : Fin 2 → Fin n,
          fiberNormSqSummand (I := I) (M := M) g x 0 2
            (∑ a : Fin n, ∑ b : Fin n,
              cT (a, b) • R (e i) (e j) (dualTensorFrame (I := I) (M := M) g x e a b))
            n e Kx Jx)
          ≤ ∑ Kx : Fin 0 → Fin n, ∑ Jx : Fin 2 → Fin n,
              (∑ p : Fin n × Fin n, cT p ^ 2) *
                ∑ p : Fin n × Fin n,
                  fiberNormSqSummand (I := I) (M := M) g x 0 2
                    (R (e i) (e j) (dualTensorFrame (I := I) (M := M) g x e p.1 p.2))
                    n e Kx Jx := by
            refine Finset.sum_le_sum (fun Kx _ => Finset.sum_le_sum (fun Jx _ => hterm Kx Jx))
      _ = (∑ p : Fin n × Fin n, cT p ^ 2) *
            ∑ Kx : Fin 0 → Fin n, ∑ Jx : Fin 2 → Fin n,
              ∑ p : Fin n × Fin n,
                fiberNormSqSummand (I := I) (M := M) g x 0 2
                  (R (e i) (e j) (dualTensorFrame (I := I) (M := M) g x e p.1 p.2))
                  n e Kx Jx := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun Kx _ => ?_)
            rw [Finset.mul_sum]
      _ = (∑ p : Fin n × Fin n, cT p ^ 2) *
            ∑ p : Fin n × Fin n,
              riemannianFiberNormSq (I := I) (M := M) g 0 2 x
                (R (e i) (e j) (dualTensorFrame (I := I) (M := M) g x e p.1 p.2)) := by
            congr 1
            rw [show (∑ p : Fin n × Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g 0 2 x
                    (R (e i) (e j) (dualTensorFrame (I := I) (M := M) g x e p.1 p.2))) =
                ∑ p : Fin n × Fin n, ∑ Kx : Fin 0 → Fin n, ∑ Jx : Fin 2 → Fin n,
                  fiberNormSqSummand (I := I) (M := M) g x 0 2
                    (R (e i) (e j) (dualTensorFrame (I := I) (M := M) g x e p.1 p.2))
                    n e Kx Jx from by
              refine Finset.sum_congr rfl (fun p _ => ?_)
              rw [hrepr (R (e i) (e j) (dualTensorFrame (I := I) (M := M) g x e p.1 p.2))]]
            rw [show (∑ Kx : Fin 0 → Fin n, ∑ Jx : Fin 2 → Fin n, ∑ p : Fin n × Fin n,
                  fiberNormSqSummand (I := I) (M := M) g x 0 2
                    (R (e i) (e j) (dualTensorFrame (I := I) (M := M) g x e p.1 p.2))
                    n e Kx Jx) =
                ∑ Kx : Fin 0 → Fin n, ∑ p : Fin n × Fin n, ∑ Jx : Fin 2 → Fin n,
                  fiberNormSqSummand (I := I) (M := M) g x 0 2
                    (R (e i) (e j) (dualTensorFrame (I := I) (M := M) g x e p.1 p.2))
                    n e Kx Jx from by
              refine Finset.sum_congr rfl (fun Kx _ => ?_)
              rw [Finset.sum_comm]]
            rw [Finset.sum_comm]
      _ ≤ (∑ a : Fin n, ∑ b : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g 0 2 x
                (R (e i) (e j) (dualTensorFrame (I := I) (M := M) g x e a b))) *
            riemannianFiberNormSq (I := I) (M := M) g 0 2 x T := by
            apply le_of_eq
            rw [show (∑ p : Fin n × Fin n, cT p ^ 2) =
                riemannianFiberNormSq (I := I) (M := M) g 0 2 x T from by
              rw [hParseval, ← Fintype.sum_prod_type' (f := fun a b => cT (a, b) ^ 2)]]
            rw [show (∑ p : Fin n × Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g 0 2 x
                    (R (e i) (e j) (dualTensorFrame (I := I) (M := M) g x e p.1 p.2))) =
                ∑ a : Fin n, ∑ b : Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g 0 2 x
                    (R (e i) (e j) (dualTensorFrame (I := I) (M := M) g x e a b)) from
              Fintype.sum_prod_type'
                (f := fun a b =>
                  riemannianFiberNormSq (I := I) (M := M) g 0 2 x
                    (R (e i) (e j) (dualTensorFrame (I := I) (M := M) g x e a b)))]
            ring
  calc
    (∑ i : Fin n, ∑ j : Fin n,
        riemannianFiberNormSq (I := I) (M := M) g 0 2 x (R (e i) (e j) T))
        ≤ ∑ i : Fin n, ∑ j : Fin n,
            (∑ a : Fin n, ∑ b : Fin n,
                riemannianFiberNormSq (I := I) (M := M) g 0 2 x
                  (R (e i) (e j) (dualTensorFrame (I := I) (M := M) g x e a b))) *
              riemannianFiberNormSq (I := I) (M := M) g 0 2 x T := by
          refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hpair i j))
    _ = (∑ i : Fin n, ∑ j : Fin n, ∑ a : Fin n, ∑ b : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g 0 2 x
              (R (e i) (e j) (dualTensorFrame (I := I) (M := M) g x e a b))) *
          riemannianFiberNormSq (I := I) (M := M) g 0 2 x T := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Finset.sum_mul]

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_Cx_riemannianFiberNormSq_riemannOp_tensorCov_le
    (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ Cx : ℝ, 0 ≤ Cx ∧
      ∀ (v w : TangentSpace I x) (T : TensorRSSpace 0 2 I x),
        riemannianFiberNormSq (I := I) (M := M) g 0 2 x
            (riemannOp (tensorCov (I := I) g 0 2) x v w T) ≤
          Cx * g.inner x v v * g.inner x w w *
            riemannianFiberNormSq (I := I) (M := M) g 0 2 x T := by
  classical
  obtain ⟨n, e, bse, _hn, hbse, horth, hpars, hexpand, hrepr⟩ :=
    tangent_orthonormalBasis_witness (I := I) (M := M) g x
  set R := riemannOp (tensorCov (I := I) g 0 2) x with hR_def
  set Cx : ℝ :=
    ∑ i : Fin n, ∑ j : Fin n, ∑ a : Fin n, ∑ b : Fin n,
      riemannianFiberNormSq (I := I) (M := M) g 0 2 x
        (R (e i) (e j) (dualTensorFrame (I := I) (M := M) g x e a b)) with hCx_def
  have hCx_nonneg : 0 ≤ Cx := by
    rw [hCx_def]
    refine Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
      Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => ?_))))
    exact riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 2 x _
  refine ⟨Cx, hCx_nonneg, ?_⟩
  intro v w T
  have hvv_nonneg : 0 ≤ g.inner x v v := by
    rw [← hpars v]; exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hww_nonneg : 0 ≤ g.inner x w w := by
    rw [← hpars w]; exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hvw : riemannianFiberNormSq (I := I) (M := M) g 0 2 x (R v w T) ≤
      g.inner x v v * g.inner x w w *
        ∑ i : Fin n, ∑ j : Fin n,
          riemannianFiberNormSq (I := I) (M := M) g 0 2 x (R (e i) (e j) T) := by
    rw [hrepr (R v w T)]
    have hterm : ∀ K : Fin 0 → Fin n, ∀ J : Fin 2 → Fin n,
        fiberNormSqSummand (I := I) (M := M) g x 0 2 (R v w T) n e K J ≤
          g.inner x v v * g.inner x w w *
            ∑ i : Fin n, ∑ j : Fin n,
              fiberNormSqSummand (I := I) (M := M) g x 0 2 (R (e i) (e j) T) n e K J :=
      fun K J => fiberNormSqSummand_riemannOp_tensorCov_vw_le
        (I := I) (M := M) g x e hpars hexpand v w T K J
    calc
      (∑ K : Fin 0 → Fin n, ∑ J : Fin 2 → Fin n,
          fiberNormSqSummand (I := I) (M := M) g x 0 2 (R v w T) n e K J)
          ≤ ∑ K : Fin 0 → Fin n, ∑ J : Fin 2 → Fin n,
              g.inner x v v * g.inner x w w *
                ∑ i : Fin n, ∑ j : Fin n,
                  fiberNormSqSummand (I := I) (M := M) g x 0 2 (R (e i) (e j) T) n e K J := by
            exact Finset.sum_le_sum (fun K _ => Finset.sum_le_sum (fun J _ => hterm K J))
      _ = g.inner x v v * g.inner x w w *
            ∑ K : Fin 0 → Fin n, ∑ J : Fin 2 → Fin n,
              ∑ i : Fin n, ∑ j : Fin n,
                fiberNormSqSummand (I := I) (M := M) g x 0 2 (R (e i) (e j) T) n e K J := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun K _ => ?_)
            rw [Finset.mul_sum]
      _ = g.inner x v v * g.inner x w w *
            ∑ i : Fin n, ∑ j : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g 0 2 x (R (e i) (e j) T) := by
            congr 1
            rw [show (∑ i : Fin n, ∑ j : Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g 0 2 x (R (e i) (e j) T)) =
                ∑ i : Fin n, ∑ j : Fin n, ∑ K : Fin 0 → Fin n, ∑ J : Fin 2 → Fin n,
                  fiberNormSqSummand (I := I) (M := M) g x 0 2 (R (e i) (e j) T) n e K J from by
              refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
              rw [hrepr (R (e i) (e j) T)]]
            set F : (Fin 0 → Fin n) → (Fin 2 → Fin n) → Fin n → Fin n → ℝ :=
              fun K J i j =>
                fiberNormSqSummand (I := I) (M := M) g x 0 2 (R (e i) (e j) T) n e K J
              with hF_def
            have hLHS : (∑ K : Fin 0 → Fin n, ∑ J : Fin 2 → Fin n,
                  ∑ i : Fin n, ∑ j : Fin n, F K J i j) =
                ∑ q : (Fin 0 → Fin n) × (Fin 2 → Fin n),
                  ∑ p : Fin n × Fin n, F q.1 q.2 p.1 p.2 := by
              calc
                (∑ K : Fin 0 → Fin n, ∑ J : Fin 2 → Fin n,
                    ∑ i : Fin n, ∑ j : Fin n, F K J i j)
                    = ∑ K : Fin 0 → Fin n, ∑ J : Fin 2 → Fin n,
                        ∑ p : Fin n × Fin n, F K J p.1 p.2 := by
                      refine Finset.sum_congr rfl (fun K _ =>
                        Finset.sum_congr rfl (fun J _ => ?_))
                      exact (Fintype.sum_prod_type' (f := fun i j => F K J i j)).symm
                _ = ∑ q : (Fin 0 → Fin n) × (Fin 2 → Fin n),
                        ∑ p : Fin n × Fin n, F q.1 q.2 p.1 p.2 :=
                      (Fintype.sum_prod_type' (f := fun K J =>
                        ∑ p : Fin n × Fin n, F K J p.1 p.2)).symm
            have hRHS : (∑ i : Fin n, ∑ j : Fin n,
                  ∑ K : Fin 0 → Fin n, ∑ J : Fin 2 → Fin n, F K J i j) =
                ∑ p : Fin n × Fin n,
                  ∑ q : (Fin 0 → Fin n) × (Fin 2 → Fin n), F q.1 q.2 p.1 p.2 := by
              calc
                (∑ i : Fin n, ∑ j : Fin n,
                    ∑ K : Fin 0 → Fin n, ∑ J : Fin 2 → Fin n, F K J i j)
                    = ∑ i : Fin n, ∑ j : Fin n,
                        ∑ q : (Fin 0 → Fin n) × (Fin 2 → Fin n), F q.1 q.2 i j := by
                      refine Finset.sum_congr rfl (fun i _ =>
                        Finset.sum_congr rfl (fun j _ => ?_))
                      exact (Fintype.sum_prod_type' (f := fun K J => F K J i j)).symm
                _ = ∑ p : Fin n × Fin n,
                        ∑ q : (Fin 0 → Fin n) × (Fin 2 → Fin n), F q.1 q.2 p.1 p.2 :=
                      (Fintype.sum_prod_type' (f := fun i j =>
                        ∑ q : (Fin 0 → Fin n) × (Fin 2 → Fin n), F q.1 q.2 i j)).symm
            rw [hLHS, hRHS]
            exact Finset.sum_comm
  have hCxT : (∑ i : Fin n, ∑ j : Fin n,
        riemannianFiberNormSq (I := I) (M := M) g 0 2 x (R (e i) (e j) T)) ≤
      Cx * riemannianFiberNormSq (I := I) (M := M) g 0 2 x T := by
    rw [hCx_def]
    exact sum_riemannianFiberNormSq_riemannOp_le_Cx
      (I := I) (M := M) g x e bse hbse horth hrepr T
  calc
    riemannianFiberNormSq (I := I) (M := M) g 0 2 x (R v w T)
        ≤ g.inner x v v * g.inner x w w *
            ∑ i : Fin n, ∑ j : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g 0 2 x (R (e i) (e j) T) := hvw
    _ ≤ g.inner x v v * g.inner x w w *
            (Cx * riemannianFiberNormSq (I := I) (M := M) g 0 2 x T) := by
          refine mul_le_mul_of_nonneg_left hCxT ?_
          exact mul_nonneg hvv_nonneg hww_nonneg
    _ = Cx * g.inner x v v * g.inner x w w *
            riemannianFiberNormSq (I := I) (M := M) g 0 2 x T := by ring

end Connection
end Integral
end DifferentialGeometry

end
