import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqRiemannOpDualFrameParseval


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 1600000

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

noncomputable def coframeS
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    {n : ℕ} (e : Fin n → TangentSpace I x) (J : Fin s → Fin n) :
    Tensor0SSpace s I x :=
  (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin s) ℝ).compContinuousLinearMap
    (fun k : Fin s => g.inner x (e (J k)))

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma coframeS_apply
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    {n : ℕ} (e : Fin n → TangentSpace I x) (J : Fin s → Fin n)
    (u : Fin s → TangentSpace I x) :
    coframeS (I := I) (M := M) g x s e J u =
      ∏ k : Fin s, g.inner x (e (J k)) (u k) := by
  unfold coframeS
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebra_apply]

noncomputable def dualTensorFrameS
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    {n : ℕ} (e : Fin n → TangentSpace I x) (J : Fin s → Fin n) :
    TensorRSSpace 0 s I x :=
  (tensor00Scalar (I := I) (M := M) x).smulRight
    (coframeS (I := I) (M := M) g x s e J)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma dualTensorFrameS_apply
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    {n : ℕ} (e : Fin n → TangentSpace I x) (J : Fin s → Fin n)
    (τ : Tensor0SSpace 0 I x) :
    (dualTensorFrameS (I := I) (M := M) g x s e J :
        Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x) τ =
      tensor00Scalar (I := I) (M := M) x τ • coframeS (I := I) (M := M) g x s e J := by
  unfold dualTensorFrameS
  rw [ContinuousLinearMap.smulRight_apply]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma fiberNormSqComponent_dualTensorFrameS
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (J : Fin s → Fin n) (K : Fin 0 → Fin n) (J' : Fin s → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g x 0 s
        (dualTensorFrameS (I := I) (M := M) g x s e J) n e K J' =
      ∏ k : Fin s, (if J k = J' k then (1 : ℝ) else 0) := by
  classical
  unfold fiberNormSqComponent
  rw [show ((dualTensorFrameS (I := I) (M := M) g x s e J :
          Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x)
          ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
            (fun k => g.inner x (e (K k))))) =
        tensor00Scalar (I := I) (M := M) x
            ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
              (fun k => g.inner x (e (K k)))) •
          coframeS (I := I) (M := M) g x s e J from
      dualTensorFrameS_apply (I := I) (M := M) g x s e J _]
  have hscalar : tensor00Scalar (I := I) (M := M) x
      ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
        (fun k => g.inner x (e (K k)))) = 1 := by
    rw [tensor00Scalar_apply (I := I) (M := M) x _ (fun k : Fin 0 => k.elim0),
      ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousMultilinearMap.mkPiAlgebra_apply]
    simp
  rw [hscalar, one_smul]
  rw [coframeS_apply (I := I) (M := M) g x s e J (fun k : Fin s => e (J' k))]
  refine Finset.prod_congr rfl (fun k _ => ?_)
  rw [horth (J k) (J' k)]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma tensorS_coframe_expansion
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (bse : Module.Basis (Fin n) ℝ (TangentSpace I x))
    (hbse : ∀ i : Fin n, bse i = e i)
    (horth : ∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (A : Tensor0SSpace s I x) :
    A = ∑ J : Fin s → Fin n,
      (A (fun k : Fin s => e (J k))) • coframeS (I := I) (M := M) g x s e J := by
  classical
  apply tensor0SSpace_ext (𝕜 := ℝ) s x
  intro u
  let Acmm : ContinuousMultilinearMap ℝ (fun _ : Fin s => TangentSpace I x) ℝ := A
  let Rcmm : ContinuousMultilinearMap ℝ (fun _ : Fin s => TangentSpace I x) ℝ :=
    ∑ J : Fin s → Fin n,
      (A (fun k : Fin s => e (J k))) • coframeS (I := I) (M := M) g x s e J
  suffices h : Acmm.toMultilinearMap = Rcmm.toMultilinearMap by
    exact congrArg
      (fun (T : MultilinearMap ℝ (fun _ : Fin s => TangentSpace I x) ℝ) => T u) h
  refine Module.Basis.ext_multilinear (e := fun _ : Fin s => bse) ?_
  intro v
  have hbtuple : (fun i : Fin s => bse (v i)) = (fun i : Fin s => e (v i)) := by
    funext i; rw [hbse (v i)]
  change Acmm (fun i : Fin s => bse (v i)) = Rcmm (fun i : Fin s => bse (v i))
  rw [hbtuple]
  have hRHS_eval : Rcmm (fun i : Fin s => e (v i)) =
      ∑ J : Fin s → Fin n,
        (A (fun k : Fin s => e (J k))) *
          coframeS (I := I) (M := M) g x s e J (fun i : Fin s => e (v i)) := by
    change (∑ J : Fin s → Fin n,
          (A (fun k : Fin s => e (J k))) • coframeS (I := I) (M := M) g x s e J)
        (fun i : Fin s => e (v i)) = _
    rw [ContinuousMultilinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun J _ => ?_)
    rw [ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  change Acmm (fun i : Fin s => e (v i)) = _
  rw [hRHS_eval]
  have hcoframe : ∀ J : Fin s → Fin n,
      coframeS (I := I) (M := M) g x s e J (fun i : Fin s => e (v i)) =
        ∏ k : Fin s, (if J k = v k then (1 : ℝ) else 0) := by
    intro J
    rw [coframeS_apply (I := I) (M := M) g x s e J (fun i : Fin s => e (v i))]
    refine Finset.prod_congr rfl (fun k _ => ?_)
    rw [horth (J k) (v k)]
  rw [show (∑ J : Fin s → Fin n,
        (A (fun k : Fin s => e (J k))) *
          coframeS (I := I) (M := M) g x s e J (fun i : Fin s => e (v i))) =
      ∑ J : Fin s → Fin n,
        (A (fun k : Fin s => e (J k))) *
          ∏ k : Fin s, (if J k = v k then (1 : ℝ) else 0) from by
    refine Finset.sum_congr rfl (fun J _ => ?_)
    rw [hcoframe J]]
  rw [Finset.sum_eq_single v]
  · rw [show (∏ k : Fin s, (if v k = v k then (1 : ℝ) else 0)) = 1 from by
      refine Finset.prod_eq_one (fun k _ => ?_); rw [if_pos rfl]]
    rw [mul_one]
  · intro J _ hJ
    have hk : ∃ k : Fin s, J k ≠ v k := by
      by_contra hcon
      refine hJ (funext (fun k => ?_))
      by_contra hkne
      exact hcon ⟨k, hkne⟩
    obtain ⟨k, hkne⟩ := hk
    rw [show (∏ k : Fin s, (if J k = v k then (1 : ℝ) else 0)) = 0 from by
      refine Finset.prod_eq_zero (Finset.mem_univ k) ?_
      rw [if_neg hkne]]
    rw [mul_zero]
  · intro h; exact absurd (Finset.mem_univ v) h

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma tensorS_dualFrame_expansion
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (bse : Module.Basis (Fin n) ℝ (TangentSpace I x))
    (hbse : ∀ i : Fin n, bse i = e i)
    (horth : ∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (T : TensorRSSpace 0 s I x) (K₀ : Fin 0 → Fin n) :
    T = ∑ J : Fin s → Fin n,
      (fiberNormSqComponent (I := I) (M := M) g x 0 s T n e K₀ J) •
        dualTensorFrameS (I := I) (M := M) g x s e J := by
  classical
  apply tensorRSSpace_ext (𝕜 := ℝ) 0 s x
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
  have hLHS : (T : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x) τ =
      c • (T : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x) ωK := by
    rw [hτ, ContinuousLinearMap.map_smul]
  set A : Tensor0SSpace s I x :=
    (T : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x) ωK with hA_def
  have hA_expand : A = ∑ J : Fin s → Fin n,
      (A (fun k : Fin s => e (J k))) • coframeS (I := I) (M := M) g x s e J :=
    tensorS_coframe_expansion (I := I) (M := M) g x s e bse hbse horth A
  have hAeval : ∀ J : Fin s → Fin n,
      A (fun k : Fin s => e (J k)) =
        fiberNormSqComponent (I := I) (M := M) g x 0 s T n e K₀ J := by
    intro J
    rw [hA_def]
    rfl
  have hLHS' : (T : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x) τ =
      ∑ J : Fin s → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g x 0 s T n e K₀ J) •
          (c • coframeS (I := I) (M := M) g x s e J) := by
    rw [hLHS, hA_expand, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun J _ => ?_)
    rw [hAeval J, smul_comm]
  have hRHS' : (∑ J : Fin s → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g x 0 s T n e K₀ J) •
          dualTensorFrameS (I := I) (M := M) g x s e J :
            Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x) τ =
      ∑ J : Fin s → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g x 0 s T n e K₀ J) •
          (c • coframeS (I := I) (M := M) g x s e J) := by
    rw [ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun J _ => ?_)
    rw [ContinuousLinearMap.smul_apply,
      dualTensorFrameS_apply (I := I) (M := M) g x s e J τ, ← hc_def]
  rw [hLHS', hRHS']

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma riemannianFiberNormSq_eq_sum_componentS_sq
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (hrepr : ∀ S : TensorRSSpace 0 s I x,
      riemannianFiberNormSq (I := I) (M := M) g 0 s x S =
        ∑ K : Fin 0 → Fin n, ∑ J : Fin s → Fin n,
          fiberNormSqSummand (I := I) (M := M) g x 0 s S n e K J)
    (T : TensorRSSpace 0 s I x) (K₀ : Fin 0 → Fin n) :
    riemannianFiberNormSq (I := I) (M := M) g 0 s x T =
      ∑ J : Fin s → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g x 0 s T n e K₀ J) ^ 2 := by
  classical
  rw [hrepr T]
  rw [Finset.sum_eq_single K₀]
  · refine Finset.sum_congr rfl (fun J _ => ?_)
    rw [fiberNormSqSummand_eq_component_sq]
  · intro K _ hK
    exact absurd (Subsingleton.elim K K₀) hK
  · intro h; exact absurd (Finset.mem_univ K₀) h

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma tangent_orthonormalBasisS_witness
    (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M) :
    ∃ (n : ℕ) (e : Fin n → TangentSpace I x)
      (bse : Module.Basis (Fin n) ℝ (TangentSpace I x)),
      n = Module.finrank ℝ (TangentSpace I x) ∧
      (∀ i : Fin n, bse i = e i) ∧
      (∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0) ∧
      (∀ v : TangentSpace I x, ∑ i : Fin n, g.inner x (e i) v ^ 2 = g.inner x v v) ∧
      (∀ v : TangentSpace I x, v = ∑ i : Fin n, g.inner x (e i) v • e i) ∧
      ∀ S : TensorRSSpace 0 s I x,
        riemannianFiberNormSq (I := I) (M := M) g 0 s x S =
          ∑ K : Fin 0 → Fin n, ∑ J : Fin s → Fin n,
            fiberNormSqSummand (I := I) (M := M) g x 0 s S n e K J := by
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

omit [NeZero (Module.finrank ℝ E)] in
lemma riemannOp_tensorCovS_frame_expand
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (hv_expand : ∀ u : TangentSpace I x, u = ∑ i : Fin n, g.inner x (e i) u • e i)
    (v w : TangentSpace I x) (T : TensorRSSpace 0 s I x) :
    riemannOp (tensorCov (I := I) g 0 s) x v w T =
      ∑ i : Fin n, ∑ j : Fin n,
        (g.inner x (e i) v * g.inner x (e j) w) •
          riemannOp (tensorCov (I := I) g 0 s) x (e i) (e j) T := by
  classical
  set R := riemannOp (tensorCov (I := I) g 0 s) x with hR_def
  have hv : v = ∑ i : Fin n, g.inner x (e i) v • e i := hv_expand v
  have hw : w = ∑ j : Fin n, g.inner x (e j) w • e j := hv_expand w
  have hRv : R v = ∑ i : Fin n, g.inner x (e i) v • R (e i) := by
    conv_lhs => rw [hv]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_smul]
  have hRvw : R v w = ∑ i : Fin n, g.inner x (e i) v • R (e i) w := by
    rw [hRv, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [ContinuousLinearMap.smul_apply]
  have hRei_w : ∀ i : Fin n, R (e i) w =
      ∑ j : Fin n, g.inner x (e j) w • R (e i) (e j) := by
    intro i
    conv_lhs => rw [hw]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [map_smul]
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
lemma fiberNormSqSummand_riemannOp_tensorCovS_vw_le
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (hpars : ∀ u : TangentSpace I x, ∑ i : Fin n, g.inner x (e i) u ^ 2 = g.inner x u u)
    (hexpand : ∀ u : TangentSpace I x, u = ∑ i : Fin n, g.inner x (e i) u • e i)
    (v w : TangentSpace I x) (T : TensorRSSpace 0 s I x)
    (K : Fin 0 → Fin n) (J : Fin s → Fin n) :
    fiberNormSqSummand (I := I) (M := M) g x 0 s
        (riemannOp (tensorCov (I := I) g 0 s) x v w T) n e K J ≤
      g.inner x v v * g.inner x w w *
        ∑ i : Fin n, ∑ j : Fin n,
          fiberNormSqSummand (I := I) (M := M) g x 0 s
            (riemannOp (tensorCov (I := I) g 0 s) x (e i) (e j) T) n e K J := by
  classical
  set R := riemannOp (tensorCov (I := I) g 0 s) x with hR_def
  have hexp : R v w T =
      ∑ i : Fin n, ∑ j : Fin n,
        (g.inner x (e i) v * g.inner x (e j) w) • R (e i) (e j) T :=
    riemannOp_tensorCovS_frame_expand (I := I) (M := M) g x s e hexpand v w T
  set c : Fin n × Fin n → ℝ := fun p => g.inner x (e p.1) v * g.inner x (e p.2) w with hc_def
  set a : Fin n × Fin n → ℝ := fun p =>
    fiberNormSqComponent (I := I) (M := M) g x 0 s (R (e p.1) (e p.2) T) n e K J with ha_def
  have hcomp_eq :
      fiberNormSqComponent (I := I) (M := M) g x 0 s (R v w T) n e K J =
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
        fiberNormSqSummand (I := I) (M := M) g x 0 s (R (e i) (e j) T) n e K J := by
    rw [Fintype.sum_prod_type (f := fun p : Fin n × Fin n => a p ^ 2)]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [ha_def, fiberNormSqSummand_eq_component_sq]
  rw [hcsq, hasq]

omit [NeZero (Module.finrank ℝ E)] in
lemma sum_riemannianFiberNormSq_riemannOpS_le_Cx
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (bse : Module.Basis (Fin n) ℝ (TangentSpace I x))
    (hbse : ∀ i : Fin n, bse i = e i)
    (horth : ∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (hrepr : ∀ S : TensorRSSpace 0 s I x,
      riemannianFiberNormSq (I := I) (M := M) g 0 s x S =
        ∑ K : Fin 0 → Fin n, ∑ J : Fin s → Fin n,
          fiberNormSqSummand (I := I) (M := M) g x 0 s S n e K J)
    (T : TensorRSSpace 0 s I x) :
    (∑ i : Fin n, ∑ j : Fin n,
        riemannianFiberNormSq (I := I) (M := M) g 0 s x
          (riemannOp (tensorCov (I := I) g 0 s) x (e i) (e j) T)) ≤
      (∑ i : Fin n, ∑ j : Fin n, ∑ J : Fin s → Fin n,
          riemannianFiberNormSq (I := I) (M := M) g 0 s x
            (riemannOp (tensorCov (I := I) g 0 s) x (e i) (e j)
              (dualTensorFrameS (I := I) (M := M) g x s e J))) *
        riemannianFiberNormSq (I := I) (M := M) g 0 s x T := by
  classical
  let K₀ : Fin 0 → Fin n := fun k => k.elim0
  set R := riemannOp (tensorCov (I := I) g 0 s) x with hR_def
  have hParseval := riemannianFiberNormSq_eq_sum_componentS_sq
    (I := I) (M := M) g x s e hrepr T K₀
  have hTexp := tensorS_dualFrame_expansion (I := I) (M := M) g x s e bse hbse horth T K₀
  set cT : (Fin s → Fin n) → ℝ :=
    fun J => fiberNormSqComponent (I := I) (M := M) g x 0 s T n e K₀ J with hcT
  have hpair : ∀ i j : Fin n,
      riemannianFiberNormSq (I := I) (M := M) g 0 s x (R (e i) (e j) T) ≤
        (∑ J : Fin s → Fin n,
            riemannianFiberNormSq (I := I) (M := M) g 0 s x
              (R (e i) (e j) (dualTensorFrameS (I := I) (M := M) g x s e J))) *
          riemannianFiberNormSq (I := I) (M := M) g 0 s x T := by
    intro i j
    have hRT : R (e i) (e j) T =
        ∑ J : Fin s → Fin n,
          cT J • R (e i) (e j) (dualTensorFrameS (I := I) (M := M) g x s e J) := by
      conv_lhs => rw [hTexp]
      rw [map_sum]
      refine Finset.sum_congr rfl (fun J _ => ?_)
      rw [ContinuousLinearMap.map_smul]
    rw [hRT]
    rw [hrepr (∑ J : Fin s → Fin n,
      cT J • R (e i) (e j) (dualTensorFrameS (I := I) (M := M) g x s e J))]
    have hterm : ∀ (Kx : Fin 0 → Fin n) (Jx : Fin s → Fin n),
        fiberNormSqSummand (I := I) (M := M) g x 0 s
            (∑ J : Fin s → Fin n,
              cT J • R (e i) (e j) (dualTensorFrameS (I := I) (M := M) g x s e J))
            n e Kx Jx ≤
          (∑ J : Fin s → Fin n, cT J ^ 2) *
            ∑ J : Fin s → Fin n,
              fiberNormSqSummand (I := I) (M := M) g x 0 s
                (R (e i) (e j) (dualTensorFrameS (I := I) (M := M) g x s e J)) n e Kx Jx := by
      intro Kx Jx
      rw [fiberNormSqSummand_eq_component_sq]
      have hcomp :
          fiberNormSqComponent (I := I) (M := M) g x 0 s
              (∑ J : Fin s → Fin n,
                cT J • R (e i) (e j) (dualTensorFrameS (I := I) (M := M) g x s e J))
              n e Kx Jx =
            ∑ J : Fin s → Fin n,
              cT J *
                fiberNormSqComponent (I := I) (M := M) g x 0 s
                  (R (e i) (e j) (dualTensorFrameS (I := I) (M := M) g x s e J)) n e Kx Jx := by
        rw [fiberNormSqComponent_sum]
        refine Finset.sum_congr rfl (fun J _ => ?_)
        rw [fiberNormSqComponent_smul]
      rw [hcomp]
      exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ cT
        (fun J => fiberNormSqComponent (I := I) (M := M) g x 0 s
          (R (e i) (e j) (dualTensorFrameS (I := I) (M := M) g x s e J)) n e Kx Jx)
    calc
      (∑ Kx : Fin 0 → Fin n, ∑ Jx : Fin s → Fin n,
          fiberNormSqSummand (I := I) (M := M) g x 0 s
            (∑ J : Fin s → Fin n,
              cT J • R (e i) (e j) (dualTensorFrameS (I := I) (M := M) g x s e J))
            n e Kx Jx)
          ≤ ∑ Kx : Fin 0 → Fin n, ∑ Jx : Fin s → Fin n,
              (∑ J : Fin s → Fin n, cT J ^ 2) *
                ∑ J : Fin s → Fin n,
                  fiberNormSqSummand (I := I) (M := M) g x 0 s
                    (R (e i) (e j) (dualTensorFrameS (I := I) (M := M) g x s e J))
                    n e Kx Jx := by
            refine Finset.sum_le_sum (fun Kx _ => Finset.sum_le_sum (fun Jx _ => hterm Kx Jx))
      _ = (∑ J : Fin s → Fin n, cT J ^ 2) *
            ∑ Kx : Fin 0 → Fin n, ∑ Jx : Fin s → Fin n,
              ∑ J : Fin s → Fin n,
                fiberNormSqSummand (I := I) (M := M) g x 0 s
                  (R (e i) (e j) (dualTensorFrameS (I := I) (M := M) g x s e J))
                  n e Kx Jx := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun Kx _ => ?_)
            rw [Finset.mul_sum]
      _ = (∑ J : Fin s → Fin n, cT J ^ 2) *
            ∑ J : Fin s → Fin n,
              riemannianFiberNormSq (I := I) (M := M) g 0 s x
                (R (e i) (e j) (dualTensorFrameS (I := I) (M := M) g x s e J)) := by
            congr 1
            rw [show (∑ J : Fin s → Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g 0 s x
                    (R (e i) (e j) (dualTensorFrameS (I := I) (M := M) g x s e J))) =
                ∑ J : Fin s → Fin n, ∑ Kx : Fin 0 → Fin n, ∑ Jx : Fin s → Fin n,
                  fiberNormSqSummand (I := I) (M := M) g x 0 s
                    (R (e i) (e j) (dualTensorFrameS (I := I) (M := M) g x s e J))
                    n e Kx Jx from by
              refine Finset.sum_congr rfl (fun J _ => ?_)
              rw [hrepr (R (e i) (e j) (dualTensorFrameS (I := I) (M := M) g x s e J))]]
            rw [show (∑ Kx : Fin 0 → Fin n, ∑ Jx : Fin s → Fin n, ∑ J : Fin s → Fin n,
                  fiberNormSqSummand (I := I) (M := M) g x 0 s
                    (R (e i) (e j) (dualTensorFrameS (I := I) (M := M) g x s e J))
                    n e Kx Jx) =
                ∑ Kx : Fin 0 → Fin n, ∑ J : Fin s → Fin n, ∑ Jx : Fin s → Fin n,
                  fiberNormSqSummand (I := I) (M := M) g x 0 s
                    (R (e i) (e j) (dualTensorFrameS (I := I) (M := M) g x s e J))
                    n e Kx Jx from by
              refine Finset.sum_congr rfl (fun Kx _ => ?_)
              rw [Finset.sum_comm]]
            rw [Finset.sum_comm]
      _ ≤ (∑ J : Fin s → Fin n,
              riemannianFiberNormSq (I := I) (M := M) g 0 s x
                (R (e i) (e j) (dualTensorFrameS (I := I) (M := M) g x s e J))) *
            riemannianFiberNormSq (I := I) (M := M) g 0 s x T := by
            apply le_of_eq
            rw [show (∑ J : Fin s → Fin n, cT J ^ 2) =
                riemannianFiberNormSq (I := I) (M := M) g 0 s x T from hParseval.symm]
            ring
  calc
    (∑ i : Fin n, ∑ j : Fin n,
        riemannianFiberNormSq (I := I) (M := M) g 0 s x (R (e i) (e j) T))
        ≤ ∑ i : Fin n, ∑ j : Fin n,
            (∑ J : Fin s → Fin n,
                riemannianFiberNormSq (I := I) (M := M) g 0 s x
                  (R (e i) (e j) (dualTensorFrameS (I := I) (M := M) g x s e J))) *
              riemannianFiberNormSq (I := I) (M := M) g 0 s x T := by
          refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hpair i j))
    _ = (∑ i : Fin n, ∑ j : Fin n, ∑ J : Fin s → Fin n,
            riemannianFiberNormSq (I := I) (M := M) g 0 s x
              (R (e i) (e j) (dualTensorFrameS (I := I) (M := M) g x s e J))) *
          riemannianFiberNormSq (I := I) (M := M) g 0 s x T := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Finset.sum_mul]

noncomputable def tensorEvalAtFrame
    (x : M) (r : ℕ) {n : ℕ} (e : Fin n → TangentSpace I x) (K : Fin r → Fin n) :
    Tensor0SSpace r I x →L[ℝ] ℝ :=
  (LinearMap.toContinuousLinearMap
      ({ toFun := fun f : ContinuousMultilinearMap ℝ (fun _ : Fin r => E) ℝ =>
            f (fun k => e (K k))
         map_add' := fun _ _ => rfl
         map_smul' := fun _ _ => rfl } :
        ContinuousMultilinearMap ℝ (fun _ : Fin r => E) ℝ →ₗ[ℝ] ℝ)).comp
    (Tensor0SSpace.toModelL (I := I) r x)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma tensorEvalAtFrame_apply
    (x : M) (r : ℕ) {n : ℕ} (e : Fin n → TangentSpace I x) (K : Fin r → Fin n)
    (τ : Tensor0SSpace r I x) :
    tensorEvalAtFrame (I := I) (M := M) x r e K τ = τ (fun k => e (K k)) := rfl

noncomputable def dualTensorFrameRS
    (g : SmoothRiemannianMetric I M) (x : M) (r s : ℕ)
    {n : ℕ} (e : Fin n → TangentSpace I x) (K : Fin r → Fin n) (J : Fin s → Fin n) :
    TensorRSSpace r s I x :=
  (tensorEvalAtFrame (I := I) (M := M) x r e K).smulRight
    (coframeS (I := I) (M := M) g x s e J)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma dualTensorFrameRS_apply
    (g : SmoothRiemannianMetric I M) (x : M) (r s : ℕ)
    {n : ℕ} (e : Fin n → TangentSpace I x) (K : Fin r → Fin n) (J : Fin s → Fin n)
    (τ : Tensor0SSpace r I x) :
    (dualTensorFrameRS (I := I) (M := M) g x r s e K J :
        Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x) τ =
      tensorEvalAtFrame (I := I) (M := M) x r e K τ •
        coframeS (I := I) (M := M) g x s e J := by
  unfold dualTensorFrameRS
  rw [ContinuousLinearMap.smulRight_apply]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma fiberNormSqComponent_dualTensorFrameRS
    (g : SmoothRiemannianMetric I M) (x : M) (r s : ℕ)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (K : Fin r → Fin n) (J : Fin s → Fin n)
    (K' : Fin r → Fin n) (J' : Fin s → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g x r s
        (dualTensorFrameRS (I := I) (M := M) g x r s e K J) n e K' J' =
      (∏ k : Fin r, (if K' k = K k then (1 : ℝ) else 0)) *
        ∏ l : Fin s, (if J l = J' l then (1 : ℝ) else 0) := by
  classical
  unfold fiberNormSqComponent
  rw [show ((dualTensorFrameRS (I := I) (M := M) g x r s e K J :
          Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x)
          ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin r) ℝ).compContinuousLinearMap
            (fun k => g.inner x (e (K' k))))) =
        tensorEvalAtFrame (I := I) (M := M) x r e K
            ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin r) ℝ).compContinuousLinearMap
              (fun k => g.inner x (e (K' k)))) •
          coframeS (I := I) (M := M) g x s e J from
      dualTensorFrameRS_apply (I := I) (M := M) g x r s e K J _]
  have hscalar : tensorEvalAtFrame (I := I) (M := M) x r e K
      ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin r) ℝ).compContinuousLinearMap
        (fun k => g.inner x (e (K' k)))) =
      ∏ k : Fin r, (if K' k = K k then (1 : ℝ) else 0) := by
    rw [tensorEvalAtFrame_apply (I := I) (M := M) x r e K,
      ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousMultilinearMap.mkPiAlgebra_apply]
    refine Finset.prod_congr rfl (fun k _ => ?_)
    rw [horth (K' k) (K k)]
  rw [hscalar]
  rw [ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  rw [coframeS_apply (I := I) (M := M) g x s e J (fun l : Fin s => e (J' l))]
  congr 1
  refine Finset.prod_congr rfl (fun l _ => ?_)
  rw [horth (J l) (J' l)]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma tensorRS_dualFrame_expansion
    (g : SmoothRiemannianMetric I M) (x : M) (r s : ℕ)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (bse : Module.Basis (Fin n) ℝ (TangentSpace I x))
    (hbse : ∀ i : Fin n, bse i = e i)
    (horth : ∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (T : TensorRSSpace r s I x) :
    T = ∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
      (fiberNormSqComponent (I := I) (M := M) g x r s T n e K J) •
        dualTensorFrameRS (I := I) (M := M) g x r s e K J := by
  classical
  apply tensorRSSpace_ext (𝕜 := ℝ) r s x
  intro τ
  set Tclm : Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x := T with hTclm
  have hτexp : τ = ∑ K : Fin r → Fin n,
      (τ (fun k : Fin r => e (K k))) • coframeS (I := I) (M := M) g x r e K :=
    tensorS_coframe_expansion (I := I) (M := M) g x r e bse hbse horth τ
  have hLHS : Tclm τ =
      ∑ K : Fin r → Fin n,
        (τ (fun k : Fin r => e (K k))) • Tclm (coframeS (I := I) (M := M) g x r e K) := by
    conv_lhs => rw [hτexp]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun K _ => ?_)
    rw [ContinuousLinearMap.map_smul]
  have hTcoframe : ∀ K : Fin r → Fin n,
      Tclm (coframeS (I := I) (M := M) g x r e K) =
        ∑ J : Fin s → Fin n,
          (fiberNormSqComponent (I := I) (M := M) g x r s T n e K J) •
            coframeS (I := I) (M := M) g x s e J := by
    intro K
    have hAexp := tensorS_coframe_expansion (I := I) (M := M) g x s e bse hbse horth
      (Tclm (coframeS (I := I) (M := M) g x r e K))
    rw [hAexp]
    refine Finset.sum_congr rfl (fun J _ => ?_)
    congr 1
  have hLHS' : Tclm τ =
      ∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
        (τ (fun k : Fin r => e (K k))) •
          ((fiberNormSqComponent (I := I) (M := M) g x r s T n e K J) •
            coframeS (I := I) (M := M) g x s e J) := by
    rw [hLHS]
    refine Finset.sum_congr rfl (fun K _ => ?_)
    rw [hTcoframe K, Finset.smul_sum]
  have hRHS' : (∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g x r s T n e K J) •
          dualTensorFrameRS (I := I) (M := M) g x r s e K J :
            Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x) τ =
      ∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
        (τ (fun k : Fin r => e (K k))) •
          ((fiberNormSqComponent (I := I) (M := M) g x r s T n e K J) •
            coframeS (I := I) (M := M) g x s e J) := by
    rw [ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun K _ => ?_)
    rw [ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun J _ => ?_)
    rw [ContinuousLinearMap.smul_apply,
      dualTensorFrameRS_apply (I := I) (M := M) g x r s e K J τ,
      tensorEvalAtFrame_apply (I := I) (M := M) x r e K, smul_comm]
  change Tclm τ = _
  rw [hLHS', hRHS']

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma riemannianFiberNormSq_eq_sum_componentRS_sq
    (g : SmoothRiemannianMetric I M) (x : M) (r s : ℕ)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (hrepr : ∀ S : TensorRSSpace r s I x,
      riemannianFiberNormSq (I := I) (M := M) g r s x S =
        ∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
          fiberNormSqSummand (I := I) (M := M) g x r s S n e K J)
    (T : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x T =
      ∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g x r s T n e K J) ^ 2 := by
  classical
  rw [hrepr T]
  refine Finset.sum_congr rfl (fun K _ => Finset.sum_congr rfl (fun J _ => ?_))
  rw [fiberNormSqSummand_eq_component_sq]

omit [NeZero (Module.finrank ℝ E)] in
lemma riemannOp_tensorCovRS_frame_expand
    (g : SmoothRiemannianMetric I M) (x : M) (r s : ℕ)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (hv_expand : ∀ u : TangentSpace I x, u = ∑ i : Fin n, g.inner x (e i) u • e i)
    (v w : TangentSpace I x) (T : TensorRSSpace r s I x) :
    riemannOp (tensorCov (I := I) g r s) x v w T =
      ∑ i : Fin n, ∑ j : Fin n,
        (g.inner x (e i) v * g.inner x (e j) w) •
          riemannOp (tensorCov (I := I) g r s) x (e i) (e j) T := by
  classical
  set R := riemannOp (tensorCov (I := I) g r s) x with hR_def
  have hv : v = ∑ i : Fin n, g.inner x (e i) v • e i := hv_expand v
  have hw : w = ∑ j : Fin n, g.inner x (e j) w • e j := hv_expand w
  have hRv : R v = ∑ i : Fin n, g.inner x (e i) v • R (e i) := by
    conv_lhs => rw [hv]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_smul]
  have hRvw : R v w = ∑ i : Fin n, g.inner x (e i) v • R (e i) w := by
    rw [hRv, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [ContinuousLinearMap.smul_apply]
  have hRei_w : ∀ i : Fin n, R (e i) w =
      ∑ j : Fin n, g.inner x (e j) w • R (e i) (e j) := by
    intro i
    conv_lhs => rw [hw]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [map_smul]
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
lemma fiberNormSqSummand_riemannOp_tensorCovRS_vw_le
    (g : SmoothRiemannianMetric I M) (x : M) (r s : ℕ)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (hpars : ∀ u : TangentSpace I x, ∑ i : Fin n, g.inner x (e i) u ^ 2 = g.inner x u u)
    (hexpand : ∀ u : TangentSpace I x, u = ∑ i : Fin n, g.inner x (e i) u • e i)
    (v w : TangentSpace I x) (T : TensorRSSpace r s I x)
    (K : Fin r → Fin n) (J : Fin s → Fin n) :
    fiberNormSqSummand (I := I) (M := M) g x r s
        (riemannOp (tensorCov (I := I) g r s) x v w T) n e K J ≤
      g.inner x v v * g.inner x w w *
        ∑ i : Fin n, ∑ j : Fin n,
          fiberNormSqSummand (I := I) (M := M) g x r s
            (riemannOp (tensorCov (I := I) g r s) x (e i) (e j) T) n e K J := by
  classical
  set R := riemannOp (tensorCov (I := I) g r s) x with hR_def
  have hexp : R v w T =
      ∑ i : Fin n, ∑ j : Fin n,
        (g.inner x (e i) v * g.inner x (e j) w) • R (e i) (e j) T :=
    riemannOp_tensorCovRS_frame_expand (I := I) (M := M) g x r s e hexpand v w T
  set c : Fin n × Fin n → ℝ := fun p => g.inner x (e p.1) v * g.inner x (e p.2) w with hc_def
  set a : Fin n × Fin n → ℝ := fun p =>
    fiberNormSqComponent (I := I) (M := M) g x r s (R (e p.1) (e p.2) T) n e K J with ha_def
  have hcomp_eq :
      fiberNormSqComponent (I := I) (M := M) g x r s (R v w T) n e K J =
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
        fiberNormSqSummand (I := I) (M := M) g x r s (R (e i) (e j) T) n e K J := by
    rw [Fintype.sum_prod_type (f := fun p : Fin n × Fin n => a p ^ 2)]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [ha_def, fiberNormSqSummand_eq_component_sq]
  rw [hcsq, hasq]

omit [NeZero (Module.finrank ℝ E)] in
lemma sum_riemannianFiberNormSq_riemannOpRS_le_Cx
    (g : SmoothRiemannianMetric I M) (x : M) (r s : ℕ)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (bse : Module.Basis (Fin n) ℝ (TangentSpace I x))
    (hbse : ∀ i : Fin n, bse i = e i)
    (horth : ∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (hrepr : ∀ S : TensorRSSpace r s I x,
      riemannianFiberNormSq (I := I) (M := M) g r s x S =
        ∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
          fiberNormSqSummand (I := I) (M := M) g x r s S n e K J)
    (T : TensorRSSpace r s I x) :
    (∑ i : Fin n, ∑ j : Fin n,
        riemannianFiberNormSq (I := I) (M := M) g r s x
          (riemannOp (tensorCov (I := I) g r s) x (e i) (e j) T)) ≤
      (∑ i : Fin n, ∑ j : Fin n, ∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
          riemannianFiberNormSq (I := I) (M := M) g r s x
            (riemannOp (tensorCov (I := I) g r s) x (e i) (e j)
              (dualTensorFrameRS (I := I) (M := M) g x r s e K J))) *
        riemannianFiberNormSq (I := I) (M := M) g r s x T := by
  classical
  set R := riemannOp (tensorCov (I := I) g r s) x with hR_def
  have hParseval := riemannianFiberNormSq_eq_sum_componentRS_sq
    (I := I) (M := M) g x r s e hrepr T
  have hTexp := tensorRS_dualFrame_expansion (I := I) (M := M) g x r s e bse hbse horth T
  set cT : (Fin r → Fin n) × (Fin s → Fin n) → ℝ :=
    fun q => fiberNormSqComponent (I := I) (M := M) g x r s T n e q.1 q.2 with hcT
  have hpair : ∀ i j : Fin n,
      riemannianFiberNormSq (I := I) (M := M) g r s x (R (e i) (e j) T) ≤
        (∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
            riemannianFiberNormSq (I := I) (M := M) g r s x
              (R (e i) (e j) (dualTensorFrameRS (I := I) (M := M) g x r s e K J))) *
          riemannianFiberNormSq (I := I) (M := M) g r s x T := by
    intro i j
    have hRT : R (e i) (e j) T =
        ∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
          cT (K, J) • R (e i) (e j) (dualTensorFrameRS (I := I) (M := M) g x r s e K J) := by
      conv_lhs => rw [hTexp]
      rw [map_sum]
      refine Finset.sum_congr rfl (fun K _ => ?_)
      rw [map_sum]
      refine Finset.sum_congr rfl (fun J _ => ?_)
      rw [ContinuousLinearMap.map_smul]
    rw [hRT]
    rw [hrepr (∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
      cT (K, J) • R (e i) (e j) (dualTensorFrameRS (I := I) (M := M) g x r s e K J))]
    have hterm : ∀ (Kx : Fin r → Fin n) (Jx : Fin s → Fin n),
        fiberNormSqSummand (I := I) (M := M) g x r s
            (∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
              cT (K, J) • R (e i) (e j) (dualTensorFrameRS (I := I) (M := M) g x r s e K J))
            n e Kx Jx ≤
          (∑ q : (Fin r → Fin n) × (Fin s → Fin n), cT q ^ 2) *
            ∑ q : (Fin r → Fin n) × (Fin s → Fin n),
              fiberNormSqSummand (I := I) (M := M) g x r s
                (R (e i) (e j) (dualTensorFrameRS (I := I) (M := M) g x r s e q.1 q.2))
                n e Kx Jx := by
      intro Kx Jx
      rw [fiberNormSqSummand_eq_component_sq]
      have hcomp :
          fiberNormSqComponent (I := I) (M := M) g x r s
              (∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
                cT (K, J) • R (e i) (e j) (dualTensorFrameRS (I := I) (M := M) g x r s e K J))
              n e Kx Jx =
            ∑ q : (Fin r → Fin n) × (Fin s → Fin n),
              cT q *
                fiberNormSqComponent (I := I) (M := M) g x r s
                  (R (e i) (e j) (dualTensorFrameRS (I := I) (M := M) g x r s e q.1 q.2))
                  n e Kx Jx := by
        rw [show (∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
              cT (K, J) • R (e i) (e j) (dualTensorFrameRS (I := I) (M := M) g x r s e K J)) =
            ∑ q : (Fin r → Fin n) × (Fin s → Fin n),
              cT q • R (e i) (e j) (dualTensorFrameRS (I := I) (M := M) g x r s e q.1 q.2) from
          (Fintype.sum_prod_type'
            (f := fun K J =>
              cT (K, J) • R (e i) (e j)
                (dualTensorFrameRS (I := I) (M := M) g x r s e K J))).symm]
        rw [fiberNormSqComponent_sum]
        refine Finset.sum_congr rfl (fun q _ => ?_)
        rw [fiberNormSqComponent_smul]
      rw [hcomp]
      exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ cT
        (fun q => fiberNormSqComponent (I := I) (M := M) g x r s
          (R (e i) (e j) (dualTensorFrameRS (I := I) (M := M) g x r s e q.1 q.2)) n e Kx Jx)
    calc
      (∑ Kx : Fin r → Fin n, ∑ Jx : Fin s → Fin n,
          fiberNormSqSummand (I := I) (M := M) g x r s
            (∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
              cT (K, J) • R (e i) (e j) (dualTensorFrameRS (I := I) (M := M) g x r s e K J))
            n e Kx Jx)
          ≤ ∑ Kx : Fin r → Fin n, ∑ Jx : Fin s → Fin n,
              (∑ q : (Fin r → Fin n) × (Fin s → Fin n), cT q ^ 2) *
                ∑ q : (Fin r → Fin n) × (Fin s → Fin n),
                  fiberNormSqSummand (I := I) (M := M) g x r s
                    (R (e i) (e j) (dualTensorFrameRS (I := I) (M := M) g x r s e q.1 q.2))
                    n e Kx Jx := by
            refine Finset.sum_le_sum (fun Kx _ => Finset.sum_le_sum (fun Jx _ => hterm Kx Jx))
      _ = (∑ q : (Fin r → Fin n) × (Fin s → Fin n), cT q ^ 2) *
            ∑ Kx : Fin r → Fin n, ∑ Jx : Fin s → Fin n,
              ∑ q : (Fin r → Fin n) × (Fin s → Fin n),
                fiberNormSqSummand (I := I) (M := M) g x r s
                  (R (e i) (e j) (dualTensorFrameRS (I := I) (M := M) g x r s e q.1 q.2))
                  n e Kx Jx := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun Kx _ => ?_)
            rw [Finset.mul_sum]
      _ = (∑ q : (Fin r → Fin n) × (Fin s → Fin n), cT q ^ 2) *
            ∑ q : (Fin r → Fin n) × (Fin s → Fin n),
              riemannianFiberNormSq (I := I) (M := M) g r s x
                (R (e i) (e j) (dualTensorFrameRS (I := I) (M := M) g x r s e q.1 q.2)) := by
            congr 1
            rw [show (∑ q : (Fin r → Fin n) × (Fin s → Fin n),
                  riemannianFiberNormSq (I := I) (M := M) g r s x
                    (R (e i) (e j) (dualTensorFrameRS (I := I) (M := M) g x r s e q.1 q.2))) =
                ∑ q : (Fin r → Fin n) × (Fin s → Fin n),
                  ∑ Kx : Fin r → Fin n, ∑ Jx : Fin s → Fin n,
                  fiberNormSqSummand (I := I) (M := M) g x r s
                    (R (e i) (e j) (dualTensorFrameRS (I := I) (M := M) g x r s e q.1 q.2))
                    n e Kx Jx from by
              refine Finset.sum_congr rfl (fun q _ => ?_)
              rw [hrepr (R (e i) (e j) (dualTensorFrameRS (I := I) (M := M) g x r s e q.1 q.2))]]
            rw [show (∑ Kx : Fin r → Fin n, ∑ Jx : Fin s → Fin n,
                  ∑ q : (Fin r → Fin n) × (Fin s → Fin n),
                  fiberNormSqSummand (I := I) (M := M) g x r s
                    (R (e i) (e j) (dualTensorFrameRS (I := I) (M := M) g x r s e q.1 q.2))
                    n e Kx Jx) =
                ∑ Kx : Fin r → Fin n,
                  ∑ q : (Fin r → Fin n) × (Fin s → Fin n), ∑ Jx : Fin s → Fin n,
                  fiberNormSqSummand (I := I) (M := M) g x r s
                    (R (e i) (e j) (dualTensorFrameRS (I := I) (M := M) g x r s e q.1 q.2))
                    n e Kx Jx from by
              refine Finset.sum_congr rfl (fun Kx _ => ?_)
              rw [Finset.sum_comm]]
            rw [Finset.sum_comm]
      _ ≤ (∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
              riemannianFiberNormSq (I := I) (M := M) g r s x
                (R (e i) (e j) (dualTensorFrameRS (I := I) (M := M) g x r s e K J))) *
            riemannianFiberNormSq (I := I) (M := M) g r s x T := by
            apply le_of_eq
            rw [show (∑ q : (Fin r → Fin n) × (Fin s → Fin n), cT q ^ 2) =
                riemannianFiberNormSq (I := I) (M := M) g r s x T from by
              rw [hParseval, ← Fintype.sum_prod_type' (f := fun K J => cT (K, J) ^ 2)]]
            rw [show (∑ q : (Fin r → Fin n) × (Fin s → Fin n),
                  riemannianFiberNormSq (I := I) (M := M) g r s x
                    (R (e i) (e j) (dualTensorFrameRS (I := I) (M := M) g x r s e q.1 q.2))) =
                ∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g r s x
                    (R (e i) (e j) (dualTensorFrameRS (I := I) (M := M) g x r s e K J)) from
              Fintype.sum_prod_type'
                (f := fun K J =>
                  riemannianFiberNormSq (I := I) (M := M) g r s x
                    (R (e i) (e j) (dualTensorFrameRS (I := I) (M := M) g x r s e K J)))]
            ring
  calc
    (∑ i : Fin n, ∑ j : Fin n,
        riemannianFiberNormSq (I := I) (M := M) g r s x (R (e i) (e j) T))
        ≤ ∑ i : Fin n, ∑ j : Fin n,
            (∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
                riemannianFiberNormSq (I := I) (M := M) g r s x
                  (R (e i) (e j) (dualTensorFrameRS (I := I) (M := M) g x r s e K J))) *
              riemannianFiberNormSq (I := I) (M := M) g r s x T := by
          refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hpair i j))
    _ = (∑ i : Fin n, ∑ j : Fin n, ∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
            riemannianFiberNormSq (I := I) (M := M) g r s x
              (R (e i) (e j) (dualTensorFrameRS (I := I) (M := M) g x r s e K J))) *
          riemannianFiberNormSq (I := I) (M := M) g r s x T := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Finset.sum_mul]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma tangent_orthonormalBasisRS_witness
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) :
    ∃ (n : ℕ) (e : Fin n → TangentSpace I x)
      (bse : Module.Basis (Fin n) ℝ (TangentSpace I x)),
      n = Module.finrank ℝ (TangentSpace I x) ∧
      (∀ i : Fin n, bse i = e i) ∧
      (∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0) ∧
      (∀ v : TangentSpace I x, ∑ i : Fin n, g.inner x (e i) v ^ 2 = g.inner x v v) ∧
      (∀ v : TangentSpace I x, v = ∑ i : Fin n, g.inner x (e i) v • e i) ∧
      ∀ S : TensorRSSpace r s I x,
        riemannianFiberNormSq (I := I) (M := M) g r s x S =
          ∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
            fiberNormSqSummand (I := I) (M := M) g x r s S n e K J := by
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

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_Cx_riemannianFiberNormSq_riemannOp_tensorCovS_le_rs
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) :
    ∃ Cx : ℝ, 0 ≤ Cx ∧
      ∀ (v w : TangentSpace I x) (T : TensorRSSpace r s I x),
        riemannianFiberNormSq (I := I) (M := M) g r s x
            (riemannOp (tensorCov (I := I) g r s) x v w T) ≤
          Cx * g.inner x v v * g.inner x w w *
            riemannianFiberNormSq (I := I) (M := M) g r s x T := by
  classical
  obtain ⟨n, e, bse, _hn, hbse, horth, hpars, hexpand, hrepr⟩ :=
    tangent_orthonormalBasisRS_witness (I := I) (M := M) g r s x
  set R := riemannOp (tensorCov (I := I) g r s) x with hR_def
  set Cx : ℝ :=
    ∑ i : Fin n, ∑ j : Fin n, ∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
      riemannianFiberNormSq (I := I) (M := M) g r s x
        (R (e i) (e j) (dualTensorFrameRS (I := I) (M := M) g x r s e K J)) with hCx_def
  have hCx_nonneg : 0 ≤ Cx := by
    rw [hCx_def]
    refine Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
      Finset.sum_nonneg (fun K _ => Finset.sum_nonneg (fun J _ => ?_))))
    exact riemannianFiberNormSq_nonneg (I := I) (M := M) g r s x _
  refine ⟨Cx, hCx_nonneg, ?_⟩
  intro v w T
  have hvv_nonneg : 0 ≤ g.inner x v v := by
    rw [← hpars v]; exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hww_nonneg : 0 ≤ g.inner x w w := by
    rw [← hpars w]; exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hvw : riemannianFiberNormSq (I := I) (M := M) g r s x (R v w T) ≤
      g.inner x v v * g.inner x w w *
        ∑ i : Fin n, ∑ j : Fin n,
          riemannianFiberNormSq (I := I) (M := M) g r s x (R (e i) (e j) T) := by
    rw [hrepr (R v w T)]
    have hterm : ∀ K : Fin r → Fin n, ∀ J : Fin s → Fin n,
        fiberNormSqSummand (I := I) (M := M) g x r s (R v w T) n e K J ≤
          g.inner x v v * g.inner x w w *
            ∑ i : Fin n, ∑ j : Fin n,
              fiberNormSqSummand (I := I) (M := M) g x r s (R (e i) (e j) T) n e K J :=
      fun K J => fiberNormSqSummand_riemannOp_tensorCovRS_vw_le
        (I := I) (M := M) g x r s e hpars hexpand v w T K J
    calc
      (∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
          fiberNormSqSummand (I := I) (M := M) g x r s (R v w T) n e K J)
          ≤ ∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
              g.inner x v v * g.inner x w w *
                ∑ i : Fin n, ∑ j : Fin n,
                  fiberNormSqSummand (I := I) (M := M) g x r s (R (e i) (e j) T) n e K J := by
            exact Finset.sum_le_sum (fun K _ => Finset.sum_le_sum (fun J _ => hterm K J))
      _ = g.inner x v v * g.inner x w w *
            ∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
              ∑ i : Fin n, ∑ j : Fin n,
                fiberNormSqSummand (I := I) (M := M) g x r s (R (e i) (e j) T) n e K J := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun K _ => ?_)
            rw [Finset.mul_sum]
      _ = g.inner x v v * g.inner x w w *
            ∑ i : Fin n, ∑ j : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g r s x (R (e i) (e j) T) := by
            congr 1
            set F : (Fin r → Fin n) → (Fin s → Fin n) → Fin n → Fin n → ℝ :=
              fun K J i j =>
                fiberNormSqSummand (I := I) (M := M) g x r s (R (e i) (e j) T) n e K J
              with hF_def
            have hRHS_eq : (∑ i : Fin n, ∑ j : Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g r s x (R (e i) (e j) T)) =
                ∑ i : Fin n, ∑ j : Fin n, ∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
                  F K J i j := by
              refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
              rw [hF_def]
              exact hrepr (R (e i) (e j) T)
            rw [hRHS_eq]
            have hLHS : (∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
                  ∑ i : Fin n, ∑ j : Fin n, F K J i j) =
                ∑ q : (Fin r → Fin n) × (Fin s → Fin n),
                  ∑ p : Fin n × Fin n, F q.1 q.2 p.1 p.2 := by
              calc
                (∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
                    ∑ i : Fin n, ∑ j : Fin n, F K J i j)
                    = ∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
                        ∑ p : Fin n × Fin n, F K J p.1 p.2 := by
                      refine Finset.sum_congr rfl (fun K _ =>
                        Finset.sum_congr rfl (fun J _ => ?_))
                      exact (Fintype.sum_prod_type' (f := fun i j => F K J i j)).symm
                _ = ∑ q : (Fin r → Fin n) × (Fin s → Fin n),
                        ∑ p : Fin n × Fin n, F q.1 q.2 p.1 p.2 :=
                      (Fintype.sum_prod_type' (f := fun K J =>
                        ∑ p : Fin n × Fin n, F K J p.1 p.2)).symm
            have hRHS : (∑ i : Fin n, ∑ j : Fin n,
                  ∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n, F K J i j) =
                ∑ p : Fin n × Fin n,
                  ∑ q : (Fin r → Fin n) × (Fin s → Fin n), F q.1 q.2 p.1 p.2 := by
              calc
                (∑ i : Fin n, ∑ j : Fin n,
                    ∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n, F K J i j)
                    = ∑ i : Fin n, ∑ j : Fin n,
                        ∑ q : (Fin r → Fin n) × (Fin s → Fin n), F q.1 q.2 i j := by
                      refine Finset.sum_congr rfl (fun i _ =>
                        Finset.sum_congr rfl (fun j _ => ?_))
                      exact (Fintype.sum_prod_type' (f := fun K J => F K J i j)).symm
                _ = ∑ p : Fin n × Fin n,
                        ∑ q : (Fin r → Fin n) × (Fin s → Fin n), F q.1 q.2 p.1 p.2 :=
                      (Fintype.sum_prod_type' (f := fun i j =>
                        ∑ q : (Fin r → Fin n) × (Fin s → Fin n), F q.1 q.2 i j)).symm
            rw [hLHS, hRHS]
            exact Finset.sum_comm
  have hCxT : (∑ i : Fin n, ∑ j : Fin n,
        riemannianFiberNormSq (I := I) (M := M) g r s x (R (e i) (e j) T)) ≤
      Cx * riemannianFiberNormSq (I := I) (M := M) g r s x T := by
    rw [hCx_def]
    exact sum_riemannianFiberNormSq_riemannOpRS_le_Cx
      (I := I) (M := M) g x r s e bse hbse horth hrepr T
  calc
    riemannianFiberNormSq (I := I) (M := M) g r s x (R v w T)
        ≤ g.inner x v v * g.inner x w w *
            ∑ i : Fin n, ∑ j : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g r s x (R (e i) (e j) T) := hvw
    _ ≤ g.inner x v v * g.inner x w w *
            (Cx * riemannianFiberNormSq (I := I) (M := M) g r s x T) := by
          refine mul_le_mul_of_nonneg_left hCxT ?_
          exact mul_nonneg hvv_nonneg hww_nonneg
    _ = Cx * g.inner x v v * g.inner x w w *
            riemannianFiberNormSq (I := I) (M := M) g r s x T := by ring

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_Cx_riemannianFiberNormSq_riemannOp_tensorCovS_le
    (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M) :
    ∃ Cx : ℝ, 0 ≤ Cx ∧
      ∀ (v w : TangentSpace I x) (T : TensorRSSpace 0 s I x),
        riemannianFiberNormSq (I := I) (M := M) g 0 s x
            (riemannOp (tensorCov (I := I) g 0 s) x v w T) ≤
          Cx * g.inner x v v * g.inner x w w *
            riemannianFiberNormSq (I := I) (M := M) g 0 s x T :=
  exists_Cx_riemannianFiberNormSq_riemannOp_tensorCovS_le_rs
    (I := I) (M := M) g 0 s x

omit [NeZero (Module.finrank ℝ E)] in
theorem riemannianFiberNormSq_riemannOp_tensorCovS_vw_factor_le
    (g : SmoothRiemannianMetric I M) (t : ℕ) (x : M)
    (v w : TangentSpace I x) (T : TensorRSSpace 0 t I x) :
    ∃ (n : ℕ) (e : Fin n → TangentSpace I x),
      (∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0) ∧
      (∀ S : TensorRSSpace 0 t I x,
        riemannianFiberNormSq (I := I) (M := M) g 0 t x S =
          ∑ K : Fin 0 → Fin n, ∑ J : Fin t → Fin n,
            fiberNormSqSummand (I := I) (M := M) g x 0 t S n e K J) ∧
      riemannianFiberNormSq (I := I) (M := M) g 0 t x
          (riemannOp (tensorCov (I := I) g 0 t) x v w T) ≤
        g.inner x v v * g.inner x w w *
          ∑ i : Fin n, ∑ j : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g 0 t x
              (riemannOp (tensorCov (I := I) g 0 t) x (e i) (e j) T) := by
  classical
  obtain ⟨n, e, _bse, _hn, _hbse, horth, hpars, hexpand, hrepr⟩ :=
    tangent_orthonormalBasisRS_witness (I := I) (M := M) g 0 t x
  refine ⟨n, e, horth, hrepr, ?_⟩
  set R := riemannOp (tensorCov (I := I) g 0 t) x with hR_def
  rw [hrepr (R v w T)]
  have hterm : ∀ K : Fin 0 → Fin n, ∀ J : Fin t → Fin n,
      fiberNormSqSummand (I := I) (M := M) g x 0 t (R v w T) n e K J ≤
        g.inner x v v * g.inner x w w *
          ∑ i : Fin n, ∑ j : Fin n,
            fiberNormSqSummand (I := I) (M := M) g x 0 t (R (e i) (e j) T) n e K J :=
    fun K J => fiberNormSqSummand_riemannOp_tensorCovRS_vw_le
      (I := I) (M := M) g x 0 t e hpars hexpand v w T K J
  calc
    (∑ K : Fin 0 → Fin n, ∑ J : Fin t → Fin n,
        fiberNormSqSummand (I := I) (M := M) g x 0 t (R v w T) n e K J)
        ≤ ∑ K : Fin 0 → Fin n, ∑ J : Fin t → Fin n,
            g.inner x v v * g.inner x w w *
              ∑ i : Fin n, ∑ j : Fin n,
                fiberNormSqSummand (I := I) (M := M) g x 0 t (R (e i) (e j) T) n e K J := by
          exact Finset.sum_le_sum (fun K _ => Finset.sum_le_sum (fun J _ => hterm K J))
    _ = g.inner x v v * g.inner x w w *
          ∑ K : Fin 0 → Fin n, ∑ J : Fin t → Fin n,
            ∑ i : Fin n, ∑ j : Fin n,
              fiberNormSqSummand (I := I) (M := M) g x 0 t (R (e i) (e j) T) n e K J := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun K _ => ?_)
          rw [Finset.mul_sum]
    _ = g.inner x v v * g.inner x w w *
          ∑ i : Fin n, ∑ j : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g 0 t x (R (e i) (e j) T) := by
          congr 1
          set F : (Fin 0 → Fin n) → (Fin t → Fin n) → Fin n → Fin n → ℝ :=
            fun K J i j =>
              fiberNormSqSummand (I := I) (M := M) g x 0 t (R (e i) (e j) T) n e K J
            with hF_def
          have hRHS_eq : (∑ i : Fin n, ∑ j : Fin n,
                riemannianFiberNormSq (I := I) (M := M) g 0 t x (R (e i) (e j) T)) =
              ∑ i : Fin n, ∑ j : Fin n, ∑ K : Fin 0 → Fin n, ∑ J : Fin t → Fin n,
                F K J i j := by
            refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
            rw [hF_def]
            exact hrepr (R (e i) (e j) T)
          rw [hRHS_eq]
          have hLHS : (∑ K : Fin 0 → Fin n, ∑ J : Fin t → Fin n,
                ∑ i : Fin n, ∑ j : Fin n, F K J i j) =
              ∑ q : (Fin 0 → Fin n) × (Fin t → Fin n),
                ∑ p : Fin n × Fin n, F q.1 q.2 p.1 p.2 := by
            calc
              (∑ K : Fin 0 → Fin n, ∑ J : Fin t → Fin n,
                  ∑ i : Fin n, ∑ j : Fin n, F K J i j)
                  = ∑ K : Fin 0 → Fin n, ∑ J : Fin t → Fin n,
                      ∑ p : Fin n × Fin n, F K J p.1 p.2 := by
                    refine Finset.sum_congr rfl (fun K _ =>
                      Finset.sum_congr rfl (fun J _ => ?_))
                    exact (Fintype.sum_prod_type' (f := fun i j => F K J i j)).symm
              _ = ∑ q : (Fin 0 → Fin n) × (Fin t → Fin n),
                      ∑ p : Fin n × Fin n, F q.1 q.2 p.1 p.2 :=
                    (Fintype.sum_prod_type' (f := fun K J =>
                      ∑ p : Fin n × Fin n, F K J p.1 p.2)).symm
          have hRHS : (∑ i : Fin n, ∑ j : Fin n,
                ∑ K : Fin 0 → Fin n, ∑ J : Fin t → Fin n, F K J i j) =
              ∑ p : Fin n × Fin n,
                ∑ q : (Fin 0 → Fin n) × (Fin t → Fin n), F q.1 q.2 p.1 p.2 := by
            calc
              (∑ i : Fin n, ∑ j : Fin n,
                  ∑ K : Fin 0 → Fin n, ∑ J : Fin t → Fin n, F K J i j)
                  = ∑ i : Fin n, ∑ j : Fin n,
                      ∑ q : (Fin 0 → Fin n) × (Fin t → Fin n), F q.1 q.2 i j := by
                    refine Finset.sum_congr rfl (fun i _ =>
                      Finset.sum_congr rfl (fun j _ => ?_))
                    exact (Fintype.sum_prod_type' (f := fun K J => F K J i j)).symm
              _ = ∑ p : Fin n × Fin n,
                      ∑ q : (Fin 0 → Fin n) × (Fin t → Fin n), F q.1 q.2 p.1 p.2 :=
                    (Fintype.sum_prod_type' (f := fun i j =>
                      ∑ q : (Fin 0 → Fin n) × (Fin t → Fin n), F q.1 q.2 i j)).symm
          rw [hLHS, hRHS]
          exact Finset.sum_comm

end Connection
end Integral
end DifferentialGeometry

end
