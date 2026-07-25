import DifferentialGeometry.Geometry.Connection.ChartTensorNabla.TensorRS.ChartTensorRSCovariantDerivative
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.CovGradParallelNaturality
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameGenuineFieldFiberEnergy
import DifferentialGeometry.Tensor.RSTensor.Coordinates.Field
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Algebra.Order.Chebyshev

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 1600000

open Bundle Manifold Set FiberBundle NormedSpace Filter
open scoped Manifold Topology ContDiff BigOperators RealInnerProductSpace

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M]
  [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in

lemma gFrame_adjoint_parseval_le
    (g : SmoothRiemannianMetric I M) (x : M)
    (W : TangentSpace I x →L[ℝ] TangentSpace I x) (Kw : ℝ) (hKw : 0 ≤ Kw)
    (hW : ∀ u : TangentSpace I x, g.inner x (W u) (W u) ≤ Kw * g.inner x u u)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (hpars : ∀ u : TangentSpace I x, ∑ i : Fin n, g.inner x (e i) u ^ 2 = g.inner x u u)
    (v : TangentSpace I x) :
    ∑ m : Fin n, g.inner x v (W (e m)) ^ 2 ≤ Kw * g.inner x v v := by
  classical
  let cd : InnerProductSpace.Core ℝ (TangentSpace I x) := g.toRiemannianMetric.toCore x
  have hc : ContinuousAt (fun v : TangentSpace I x => cd.inner v v) 0 :=
    g.toRiemannianMetric.continuousAt x
  have hb : Bornology.IsVonNBounded ℝ {v : TangentSpace I x |
      RCLike.re (cd.inner v v) < 1} :=
    g.toRiemannianMetric.isVonNBounded x
  letI nag : NormedAddCommGroup (TangentSpace I x) := cd.toNormedAddCommGroupOfTopology hc hb
  letI ips : InnerProductSpace ℝ (TangentSpace I x) :=
    InnerProductSpace.ofCoreOfTopology cd hc hb
  haveI : CompleteSpace (TangentSpace I x) := FiniteDimensional.complete ℝ _
  have hinner_eq : ∀ u w : TangentSpace I x, (inner ℝ u w : ℝ) = g.inner x u w := fun u w => rfl
  let W' := ContinuousLinearMap.adjoint W
  have hadj : ∀ u w : TangentSpace I x, g.inner x (W' w) u = g.inner x w (W u) := by
    intro u w
    rw [← hinner_eq (W' w) u, ← hinner_eq w (W u)]
    exact ContinuousLinearMap.adjoint_inner_left W u w
  have hsym : ∀ u w, g.inner x u w = g.inner x w u := by
    intro u w; rw [← hinner_eq u w, ← hinner_eq w u]; exact real_inner_comm w u
  have hParv : ∑ m : Fin n, g.inner x (W' v) (e m) ^ 2 = g.inner x (W' v) (W' v) := by
    have hp := hpars (W' v)
    rw [← hp]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [hsym (W' v) (e m)]
  have heq : ∑ m : Fin n, g.inner x v (W (e m)) ^ 2 = g.inner x (W' v) (W' v) := by
    rw [← hParv]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [← hadj (e m) v]
  rw [heq]
  have hnorm : ‖W'‖ = ‖W‖ := by simp [W', LinearIsometryEquiv.norm_map]
  have hWvv : g.inner x (W' v) (W' v) = ‖W' v‖ ^ 2 := by
    rw [← hinner_eq (W' v) (W' v)]; exact real_inner_self_eq_norm_sq (W' v)
  have hvv : g.inner x v v = ‖v‖ ^ 2 := by
    rw [← hinner_eq v v]; exact real_inner_self_eq_norm_sq v
  rw [hWvv, hvv]
  have hle1 : ‖W' v‖ ≤ ‖W'‖ * ‖v‖ := W'.le_opNorm v
  have hsq : ‖W' v‖ ^ 2 ≤ (‖W'‖ * ‖v‖) ^ 2 :=
    sq_le_sq' (by linarith [norm_nonneg (W' v)]) hle1
  have hsqrtKw : ∀ u : TangentSpace I x, ‖W u‖ ≤ Real.sqrt Kw * ‖u‖ := by
    intro u
    have hWu : ‖W u‖ ^ 2 ≤ Kw * ‖u‖ ^ 2 := by
      have := hW u
      rw [← hinner_eq (W u) (W u), ← hinner_eq u u, real_inner_self_eq_norm_sq (W u),
        real_inner_self_eq_norm_sq u] at this
      exact this
    have hbnn : 0 ≤ Real.sqrt Kw * ‖u‖ := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
    have hsqle : ‖W u‖ ^ 2 ≤ (Real.sqrt Kw * ‖u‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hKw]; exact hWu
    have hroot := Real.sqrt_le_sqrt hsqle
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hbnn] at hroot
  have hWnorm_le : ‖W‖ ≤ Real.sqrt Kw :=
    ContinuousLinearMap.opNorm_le_bound W (Real.sqrt_nonneg _) hsqrtKw
  have hWsq_le : ‖W‖ ^ 2 ≤ Kw := by
    calc ‖W‖ ^ 2 ≤ (Real.sqrt Kw) ^ 2 :=
          sq_le_sq' (by linarith [norm_nonneg W, Real.sqrt_nonneg Kw]) hWnorm_le
      _ = Kw := Real.sq_sqrt hKw
  calc ‖W' v‖ ^ 2 ≤ (‖W'‖ * ‖v‖) ^ 2 := hsq
    _ = ‖W‖ ^ 2 * ‖v‖ ^ 2 := by rw [hnorm]; ring
    _ ≤ Kw * ‖v‖ ^ 2 := mul_le_mul_of_nonneg_right hWsq_le (sq_nonneg _)

def embedRS (x : M) (s : ℕ) (A0 : Tensor0SSpace s I x) : TensorRSSpace 0 s I x :=
  ContinuousLinearMap.smulRight (Tensor0SBundle.tensor0SSpace_evalScalar (𝕜 := ℝ) (I := I) x) A0

omit [CompleteSpace E] in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma embedRS_unitZeroSec_apply (x : M) (s : ℕ) (A0 : Tensor0SSpace s I x) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from embedRS (I := I) (M := M) x s A0)
      (unitZeroSec (I := I) (M := M) x) = A0 := by
  rw [embedRS, ContinuousLinearMap.smulRight_apply]
  have he : Tensor0SBundle.tensor0SSpace_evalScalar (𝕜 := ℝ) (I := I) x
      (unitZeroSec (I := I) (M := M) x) = (1 : ℝ) := by
    rw [Tensor0SBundle.tensor0SSpace_evalScalar, ContinuousLinearMap.comp_apply,
      Tensor0SSpace.toModelL_apply, ContinuousMultilinearMap.apply_apply, unitZeroSec_apply,
      Tensor0SSpace.toModel_ofModel, ContinuousMultilinearMap.constOfIsEmpty_apply]
  rw [he, one_smul]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in

omit [FiniteDimensional ℝ E] [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] in
lemma toModel_tensorSlotSubstCLM_apply (s : ℕ) (x : M) (k : Fin s)
    (W : TangentSpace I x →L[ℝ] TangentSpace I x)
    (A0 : Tensor0SSpace s I x) (m : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel
      (tensorSlotSubstCLM (I := I) s x (tangentSlotCLM (I := I) s k W) A0) m =
      Tensor0SSpace.toModel A0 (Function.update m k (W (m k))) := by
  have hupd : (fun i => tangentSlotCLM (I := I) s k W i (m i)) =
      Function.update m k (W (m k)) := by
    funext i
    by_cases h : i = k
    · subst h; rw [tangentSlotCLM_self, Function.update_self]
    · rw [tangentSlotCLM_other (I := I) s k W h, ContinuousLinearMap.id_apply,
        Function.update_of_ne h]
  have happ := tensorSlotSubstCLM_apply (I := I) s x (tangentSlotCLM (I := I) s k W) A0 m
  rw [hupd] at happ
  change (show ContinuousMultilinearMap ℝ (fun _ : Fin s => TangentSpace I x) ℝ from
      tensorSlotSubstCLM (I := I) s x (tangentSlotCLM (I := I) s k W) A0) m = _
  rw [happ]
  rfl

omit [CompleteSpace E] in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma fiberNormSqComponent_embedRS
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ) (A0 : Tensor0SSpace s I x)
    {n : ℕ} (e : Fin n → TangentSpace I x) (K₀ : Fin 0 → Fin n) (J : Fin s → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g x 0 s (embedRS (I := I) (M := M) x s A0) n e K₀ J =
      Tensor0SSpace.toModel A0 (fun k => e (J k)) := by
  rw [fiberNormSqComponent]
  have hscal : ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
        (fun k => g.inner x (e (K₀ k))) : Tensor0SSpace 0 I x) =
      unitZeroSec (I := I) (M := M) x := by
    apply Tensor0SSpace.toModel_injective
    apply ContinuousMultilinearMap.ext
    intro m
    have hL : Tensor0SSpace.toModel
        ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
          (fun k => g.inner x (e (K₀ k))) : Tensor0SSpace 0 I x) m = 1 := by
      change ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
          (fun k => g.inner x (e (K₀ k)))) m = 1
      rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
        ContinuousMultilinearMap.mkPiAlgebra_apply]
      simp
    have hR : Tensor0SSpace.toModel (unitZeroSec (I := I) (M := M) x) m = 1 := by
      rw [unitZeroSec_apply, Tensor0SSpace.toModel_ofModel,
        ContinuousMultilinearMap.constOfIsEmpty_apply]
    rw [hL, hR]
  rw [hscal, embedRS_unitZeroSec_apply]
  rfl

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in

lemma toModel_update_sum_slot (s : ℕ) (x : M) (A0 : Tensor0SSpace s I x) (k : Fin s)
    {n : ℕ} (e : Fin n → TangentSpace I x) (a : Fin n → ℝ) (m : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel A0 (Function.update m k (∑ j, a j • e j)) =
      ∑ j, a j * Tensor0SSpace.toModel A0 (Function.update m k (e j)) := by
  classical
  have h := (Tensor0SSpace.toModel A0).toMultilinearMap.map_update_sum
    (Finset.univ) k (fun j : Fin n => a j • e j) m
  simp only [ContinuousMultilinearMap.coe_coe] at h
  rw [h]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← smul_eq_mul]
  exact (Tensor0SSpace.toModel A0).map_update_smul m k (a j) (e j)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in

private lemma gFrame_gram_sum_sq (g : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (d : Fin n → ℝ)
    (horth : ∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0) :
    g.inner x (∑ j, d j • e j) (∑ l, d l • e l) = ∑ j, d j ^ 2 := by
  classical
  have hbil : g.inner x (∑ j, d j • e j) (∑ l, d l • e l)
      = ∑ j, ∑ l, (d j * d l) * g.inner x (e j) (e l) := by
    rw [show g.inner x (∑ j, d j • e j) = ∑ j, d j • g.inner x (e j) from by
      rw [map_sum]; refine Finset.sum_congr rfl (fun j _ => ?_); rw [map_smul]]
    rw [ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [ContinuousLinearMap.smul_apply, map_sum, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [map_smul, smul_eq_mul]; ring
  rw [hbil]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.sum_eq_single j]
  · rw [horth j j, if_pos rfl, mul_one]; ring
  · intro l _ hl; rw [horth j l, if_neg (fun h => hl h.symm), mul_zero]
  · intro h; exact absurd (Finset.mem_univ j) h

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M]
  [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in

private lemma frame_double_sum_slotSub_le
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    (A0 : Tensor0SSpace s I x) (k : Fin s)
    (W : TangentSpace I x →L[ℝ] TangentSpace I x) (Kw : ℝ) (hKw : 0 ≤ Kw)
    (hW : ∀ u : TangentSpace I x, g.inner x (W u) (W u) ≤ Kw * g.inner x u u)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (hpars : ∀ u : TangentSpace I x, ∑ i : Fin n, g.inner x (e i) u ^ 2 = g.inner x u u)
    (hexpand : ∀ u : TangentSpace I x, u = ∑ i : Fin n, g.inner x (e i) u • e i) :
    ∑ J : Fin s → Fin n,
        (Tensor0SSpace.toModel A0 (Function.update (fun i => e (J i)) k (W (e (J k))))) ^ 2 ≤
      Kw * ∑ J : Fin s → Fin n, (Tensor0SSpace.toModel A0 (fun i => e (J i))) ^ 2 := by
  classical
  set c : (Fin s → Fin n) → ℝ := fun J => Tensor0SSpace.toModel A0 (fun i => e (J i)) with hc
  set vof : (Fin s → Fin n) → TangentSpace I x := fun J =>
    ∑ j : Fin n, c (Function.update J k j) • e j with hvof
  have hA : ∀ J : Fin s → Fin n,
      Tensor0SSpace.toModel A0 (Function.update (fun i => e (J i)) k (W (e (J k)))) =
        g.inner x (vof J) (W (e (J k))) := by
    intro J
    have hWe : W (e (J k)) = ∑ j : Fin n, g.inner x (e j) (W (e (J k))) • e j := hexpand _
    have hstepA : Tensor0SSpace.toModel A0 (Function.update (fun i => e (J i)) k (W (e (J k))))
        = ∑ j : Fin n, g.inner x (e j) (W (e (J k))) * c (Function.update J k j) := by
      conv_lhs => rw [hWe]
      refine (toModel_update_sum_slot (I := I) s x A0 k e
        (fun j => g.inner x (e j) (W (e (J k)))) (fun i => e (J i))).trans ?_
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [hc]
      congr 2
      funext i
      by_cases h : i = k
      · subst h; rw [Function.update_self, Function.update_self]
      · rw [Function.update_of_ne h, Function.update_of_ne h]
    rw [hstepA, hvof]
    rw [show g.inner x (∑ j : Fin n, c (Function.update J k j) • e j) (W (e (J k)))
        = ∑ j : Fin n, c (Function.update J k j) * g.inner x (e j) (W (e (J k))) from by
      rw [show g.inner x (∑ j : Fin n, c (Function.update J k j) • e j)
          = ∑ j : Fin n, c (Function.update J k j) • g.inner x (e j) from by
        rw [map_sum]; refine Finset.sum_congr rfl (fun j _ => ?_); rw [map_smul]]
      rw [ContinuousLinearMap.sum_apply]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [ContinuousLinearMap.smul_apply, smul_eq_mul]]
    refine Finset.sum_congr rfl (fun j _ => ?_); ring
  rw [Finset.sum_congr rfl (fun J _ => by rw [hA J] : ∀ J ∈ Finset.univ,
    (Tensor0SSpace.toModel A0 (Function.update (fun i => e (J i)) k (W (e (J k))))) ^ 2
      = (g.inner x (vof J) (W (e (J k)))) ^ 2)]
  set ee := Equiv.funSplitAt k (Fin n) with hee
  have hreg : ∑ J : Fin s → Fin n, (g.inner x (vof J) (W (e (J k)))) ^ 2 =
      ∑ ρ : {i : Fin s // i ≠ k} → Fin n, ∑ m : Fin n,
        (g.inner x (vof (ee.symm (m, ρ))) (W (e ((ee.symm (m, ρ)) k)))) ^ 2 := by
    rw [← (Equiv.sum_comp ee.symm
      (fun J : Fin s → Fin n => (g.inner x (vof J) (W (e (J k)))) ^ 2))]
    rw [Fintype.sum_prod_type, Finset.sum_comm]
  rw [hreg]
  have hkval : ∀ (m : Fin n) (ρ : {i : Fin s // i ≠ k} → Fin n), (ee.symm (m, ρ)) k = m := by
    intro m ρ; rw [hee]; simp [Equiv.funSplitAt, Equiv.piSplitAt]
  have hupd : ∀ (m : Fin n) (ρ : {i : Fin s // i ≠ k} → Fin n) (j : Fin n),
      Function.update (ee.symm (m, ρ)) k j = ee.symm (j, ρ) := by
    intro m ρ j; rw [hee]; funext i
    by_cases h : i = k
    · subst h; rw [Function.update_self]; simp [Equiv.funSplitAt, Equiv.piSplitAt]
    · rw [Function.update_of_ne h]; simp [Equiv.funSplitAt, Equiv.piSplitAt, h]
  have hvof_eq : ∀ (m : Fin n) (ρ : {i : Fin s // i ≠ k} → Fin n),
      vof (ee.symm (m, ρ)) = ∑ j : Fin n, c (ee.symm (j, ρ)) • e j := by
    intro m ρ; rw [hvof]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hupd m ρ j]
  have hper : ∀ ρ : {i : Fin s // i ≠ k} → Fin n,
      ∑ m : Fin n, (g.inner x (vof (ee.symm (m, ρ))) (W (e ((ee.symm (m, ρ)) k)))) ^ 2 ≤
        Kw * ∑ j : Fin n, c (ee.symm (j, ρ)) ^ 2 := by
    intro ρ
    set vρ := ∑ j : Fin n, c (ee.symm (j, ρ)) • e j with hvρ
    have hrw : ∀ m : Fin n,
        (g.inner x (vof (ee.symm (m, ρ))) (W (e ((ee.symm (m, ρ)) k)))) ^ 2 =
          g.inner x vρ (W (e m)) ^ 2 := by
      intro m; rw [hvof_eq m ρ, hkval m ρ]
    rw [Finset.sum_congr rfl (fun m _ => hrw m)]
    refine le_trans (gFrame_adjoint_parseval_le (I := I) (M := M) g x W Kw hKw hW e hpars vρ) ?_
    rw [gFrame_gram_sum_sq (I := I) (M := M) g x e (fun j => c (ee.symm (j, ρ))) horth]
  refine le_trans (Finset.sum_le_sum (fun ρ _ => hper ρ)) ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ hKw
  rw [← (Equiv.sum_comp ee.symm (fun J : Fin s → Fin n => c J ^ 2))]
  rw [Fintype.sum_prod_type, Finset.sum_comm]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] in

omit [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M] in
private lemma toModel_slotSub_apply (x : M) (s : ℕ)
    (A0 : Tensor0SSpace s I x) (W : TangentSpace I x →L[ℝ] TangentSpace I x)
    {n : ℕ} (e : Fin n → TangentSpace I x) (J : Fin s → Fin n) :
    Tensor0SSpace.toModel
      (- ∑ k : Fin s, tensorSlotSubstCLM (I := I) s x (tangentSlotCLM (I := I) s k W) A0)
      (fun i => e (J i)) =
    - ∑ k : Fin s, Tensor0SSpace.toModel A0 (Function.update (fun i => e (J i)) k (W (e (J k)))) := by
  rw [Tensor0SSpace.toModel_neg]
  rw [show Tensor0SSpace.toModel (∑ k : Fin s, tensorSlotSubstCLM (I := I) s x
        (tangentSlotCLM (I := I) s k W) A0)
      = ∑ k : Fin s, Tensor0SSpace.toModel (tensorSlotSubstCLM (I := I) s x
          (tangentSlotCLM (I := I) s k W) A0) from by
    rw [← Tensor0SSpace.toModelL_apply, map_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Tensor0SSpace.toModelL_apply]]
  rw [ContinuousMultilinearMap.neg_apply, ContinuousMultilinearMap.sum_apply]
  congr 1
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [toModel_tensorSlotSubstCLM_apply]

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem riemannianFiberNormSq_slotSub_le
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ) (A0 : Tensor0SSpace s I x)
    (W : TangentSpace I x →L[ℝ] TangentSpace I x) (Kw : ℝ) (hKw : 0 ≤ Kw)
    (hW : ∀ u : TangentSpace I x, g.inner x (W u) (W u) ≤ Kw * g.inner x u u) :
    riemannianFiberNormSq (I := I) (M := M) g 0 s x
        (embedRS (I := I) (M := M) x s
          (- ∑ k : Fin s, tensorSlotSubstCLM (I := I) s x (tangentSlotCLM (I := I) s k W) A0)) ≤
      (s ^ 2 * Kw) * riemannianFiberNormSq (I := I) (M := M) g 0 s x
        (embedRS (I := I) (M := M) x s A0) := by
  classical
  obtain ⟨n, e, _bse, hn, _hbse, horth, hpars, hexpand, hreprS⟩ :=
    tangent_orthonormalBasisS_witness (I := I) (M := M) g s x
  set K₀ : Fin 0 → Fin n := fun k => k.elim0 with hK₀
  set Q := - ∑ k : Fin s, tensorSlotSubstCLM (I := I) s x (tangentSlotCLM (I := I) s k W) A0 with hQ
  rw [riemannianFiberNormSq_eq_sum_componentS_sq (I := I) (M := M) g x s e hreprS
    (embedRS (I := I) (M := M) x s Q) K₀]
  rw [riemannianFiberNormSq_eq_sum_componentS_sq (I := I) (M := M) g x s e hreprS
    (embedRS (I := I) (M := M) x s A0) K₀]
  have hcompQ : ∀ J : Fin s → Fin n,
      fiberNormSqComponent (I := I) (M := M) g x 0 s (embedRS (I := I) (M := M) x s Q) n e K₀ J =
        - ∑ k : Fin s, Tensor0SSpace.toModel A0
            (Function.update (fun i => e (J i)) k (W (e (J k)))) := by
    intro J
    rw [fiberNormSqComponent_embedRS (I := I) (M := M) g x s Q e K₀ J]
    rw [hQ]
    exact toModel_slotSub_apply (I := I) (M := M) x s A0 W e J
  have hcompA : ∀ J : Fin s → Fin n,
      fiberNormSqComponent (I := I) (M := M) g x 0 s (embedRS (I := I) (M := M) x s A0) n e K₀ J =
        Tensor0SSpace.toModel A0 (fun i => e (J i)) := by
    intro J; rw [fiberNormSqComponent_embedRS (I := I) (M := M) g x s A0 e K₀ J]
  simp_rw [hcompQ, hcompA]
  have hsq : ∀ J : Fin s → Fin n,
      (- ∑ k : Fin s, Tensor0SSpace.toModel A0
          (Function.update (fun i => e (J i)) k (W (e (J k))))) ^ 2
      ≤ (s : ℝ) * ∑ k : Fin s, (Tensor0SSpace.toModel A0
          (Function.update (fun i => e (J i)) k (W (e (J k))))) ^ 2 := by
    intro J
    rw [neg_pow, neg_one_sq, one_mul]
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin s)))
      (f := fun k => Tensor0SSpace.toModel A0 (Function.update (fun i => e (J i)) k (W (e (J k)))))
    simpa using h
  refine le_trans (Finset.sum_le_sum (fun J _ => hsq J)) ?_
  rw [← Finset.mul_sum, Finset.sum_comm]
  have hslot : ∀ k : Fin s,
      ∑ J : Fin s → Fin n,
        (Tensor0SSpace.toModel A0 (Function.update (fun i => e (J i)) k (W (e (J k))))) ^ 2 ≤
      Kw * ∑ J : Fin s → Fin n, (Tensor0SSpace.toModel A0 (fun i => e (J i))) ^ 2 :=
    fun k => frame_double_sum_slotSub_le (I := I) (M := M) g x s A0 k W Kw hKw hW e horth hpars hexpand
  calc (s : ℝ) * ∑ k : Fin s, ∑ J : Fin s → Fin n,
          (Tensor0SSpace.toModel A0 (Function.update (fun i => e (J i)) k (W (e (J k))))) ^ 2
      ≤ (s : ℝ) * ∑ _k : Fin s,
          Kw * ∑ J : Fin s → Fin n, (Tensor0SSpace.toModel A0 (fun i => e (J i))) ^ 2 := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun k _ => hslot k)) (Nat.cast_nonneg _)
    _ = (s ^ 2 * Kw) * ∑ J : Fin s → Fin n, (Tensor0SSpace.toModel A0 (fun i => e (J i))) ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end Connection
end Integral
end DifferentialGeometry
