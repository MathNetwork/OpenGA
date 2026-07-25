import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.BareSlot0CurryParseval
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.Slot0SliceFiberNormDomination
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqTensorInnerBridge
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.TensorLoweringParallel

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open Bundle Manifold Set FiberBundle NormedSpace Filter CovariantDerivative
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma rfns_eq_sum_fiberNormSqSummand_of_orthoFrame
    (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M) (S : TensorRSSpace 0 s I x)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (hn : n = Module.finrank ℝ (TangentSpace I x))
    (horth : ∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0) :
    riemannianFiberNormSq (I := I) (M := M) g 0 s x S =
      ∑ K : Fin 0 → Fin n, ∑ J : Fin s → Fin n,
        fiberNormSqSummand (I := I) (M := M) g x 0 s S n e K J := by
  classical
  subst hn
  haveI : Nonempty (Fin (Module.finrank ℝ (TangentSpace I x))) :=
    ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))⟩⟩
  have he_li : LinearIndependent ℝ e := by
    rw [linearIndependent_iff']
    intro fs c hsum k hk_mem
    have h_zero : g.inner x (e k) (∑ j ∈ fs, c j • e j) = 0 := by rw [hsum]; simp
    rw [map_sum] at h_zero
    have h_pull : ∀ j ∈ fs, g.inner x (e k) (c j • e j) = c j * (if k = j then (1 : ℝ) else 0) := by
      intro j _
      rw [(g.inner x (e k)).map_smul (c j) (e j), smul_eq_mul, horth k j]
    rw [Finset.sum_congr rfl h_pull, Finset.sum_eq_single_of_mem k hk_mem] at h_zero
    · rwa [if_pos rfl, mul_one] at h_zero
    · intro j _ hjk; rw [if_neg (fun h => hjk h.symm), mul_zero]
  have hcard : Fintype.card (Fin (Module.finrank ℝ (TangentSpace I x))) =
      Module.finrank ℝ (TangentSpace I x) := Fintype.card_fin _
  set bse : Module.Basis (Fin (Module.finrank ℝ (TangentSpace I x))) ℝ (TangentSpace I x) :=
    basisOfLinearIndependentOfCardEqFinrank he_li hcard with hbse_def
  have hbse_eq : ∀ i, bse i = e i := by
    intro i; rw [hbse_def]; exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank he_li hcard) i
  have hbse_orth : ∀ i j, g.inner x (bse i) (bse j) = if i = j then (1 : ℝ) else 0 := by
    intro i j; rw [hbse_eq i, hbse_eq j]; exact horth i j

  have hstep : riemannianFiberNormSq (I := I) (M := M) g 0 s x S =
      ∑ ψ : Fin s → Fin (Module.finrank ℝ (TangentSpace I x)),
        Tensor0SSpace.toModel
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from S)
              (unitZeroSec (I := I) (M := M) x))
            (fun k => e (ψ k)) ^ 2 := by
    rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g 0 s x S]
    rw [show tensorInnerPointwise (I := I) (M := M) g 0 s x
          (TensorRSSpace.toModel S) (TensorRSSpace.toModel S) =
        covariantTensorInnerPointwise (I := I) (M := M) (0 + s) g x
          (lowerAllUpperIndices (I := I) (M := M) g 0 s x (TensorRSSpace.toModel S))
          (lowerAllUpperIndices (I := I) (M := M) g 0 s x (TensorRSSpace.toModel S)) from rfl]
    rw [tensorInnerPointwise_0s_eq_diag_sum_orthoFrame (I := I) (M := M) g x (0 + s)
      bse hbse_orth _ _]
    have hkey : ∀ ξ : Fin (0 + s) → Fin (Module.finrank ℝ (TangentSpace I x)),
        lowerAllUpperIndices (I := I) (M := M) g 0 s x
            (TensorRSSpace.toModel S) (fun k => bse (ξ k)) =
          Tensor0SSpace.toModel
              ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from S)
                (unitZeroSec (I := I) (M := M) x))
              (fun j : Fin s => bse (ξ (Fin.natAdd 0 j))) := by
      intro ξ
      rw [lowerAllUpperIndices_apply (I := I) (M := M) g 0 s x (TensorRSSpace.toModel S)
        (fun k => bse (ξ k))]
      rw [toModel_tensorRS_apply (I := I) (M := M) 0 s x S (unitZeroSec (I := I) (M := M) x)]
      rw [unitZeroSec_apply (I := I) (M := M) x, Tensor0SSpace.toModel_ofModel]
      rw [separableFormAt_zero (I := I) (M := M) g x
        (fun i : Fin 0 => (fun k => bse (ξ k)) (Fin.castAdd s i))]
    have hstep2 : ∀ ξ : Fin (0 + s) → Fin (Module.finrank ℝ (TangentSpace I x)),
        lowerAllUpperIndices (I := I) (M := M) g 0 s x
              (TensorRSSpace.toModel S) (fun k => bse (ξ k)) *
            lowerAllUpperIndices (I := I) (M := M) g 0 s x
              (TensorRSSpace.toModel S) (fun k => bse (ξ k)) =
          Tensor0SSpace.toModel
              ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from S)
                (unitZeroSec (I := I) (M := M) x))
              (fun k => e (ξ (Fin.natAdd 0 k))) ^ 2 := by
      intro ξ
      rw [hkey ξ, ← pow_two]
      congr 2
      funext k
      rw [hbse_eq]
    refine Eq.trans (Finset.sum_congr rfl (fun ξ _ => hstep2 ξ)) ?_
    refine Fintype.sum_bijective
      (fun ξ : Fin (0 + s) → Fin (Module.finrank ℝ (TangentSpace I x)) =>
        fun k : Fin s => ξ (Fin.natAdd 0 k))
      ?_ _ _ (fun ξ => rfl)
    refine ⟨fun ξ₁ ξ₂ h => ?_, fun φ => ⟨fun k => φ (Fin.cast (Nat.zero_add s) k), ?_⟩⟩
    · funext k
      have hk : k = Fin.natAdd 0 (Fin.cast (Nat.zero_add s) k) := by ext; simp
      rw [hk]; exact congrFun h (Fin.cast (Nat.zero_add s) k)
    · funext k
      change φ (Fin.cast (Nat.zero_add s) (Fin.natAdd 0 k)) = φ k
      have : Fin.cast (Nat.zero_add s) (Fin.natAdd 0 k) = k := by ext; simp
      rw [this]
  rw [hstep]

  rw [Finset.sum_eq_single (fun k : Fin 0 => k.elim0)]
  · refine Finset.sum_congr rfl (fun J _ => ?_)
    rw [fiberNormSqSummand_eq_component_sq]

    have hweight : ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
        (fun k => g.inner x (e ((fun k : Fin 0 => k.elim0) k))) : Tensor0SSpace 0 I x) =
        unitZeroSec (I := I) (M := M) x := by
      have hcf : ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
          (fun k => g.inner x (e ((fun k : Fin 0 => k.elim0) k))) : Tensor0SSpace 0 I x) =
          coframeS (I := I) (M := M) g x 0 e (fun k : Fin 0 => k.elim0) := rfl
      rw [hcf]
      apply Tensor0SSpace.toModel_injective
      apply ContinuousMultilinearMap.ext
      intro mm
      have hL : Tensor0SSpace.toModel (coframeS (I := I) (M := M) g x 0 e
          (fun k : Fin 0 => k.elim0)) mm = 1 := by
        have h1 : Tensor0SSpace.toModel (coframeS (I := I) (M := M) g x 0 e
            (fun k : Fin 0 => k.elim0)) mm =
            coframeS (I := I) (M := M) g x 0 e (fun k : Fin 0 => k.elim0)
              (fun k : Fin 0 => k.elim0) := by
          apply congrArg; funext k; exact k.elim0
        rw [h1, coframeS_apply (I := I) (M := M) g x 0 e (fun k : Fin 0 => k.elim0)
          (fun k : Fin 0 => k.elim0)]
        simp
      have hR : Tensor0SSpace.toModel (unitZeroSec (I := I) (M := M) x) mm = 1 := by
        rw [unitZeroSec_apply (I := I) (M := M) x, Tensor0SSpace.toModel_ofModel,
          ContinuousMultilinearMap.constOfIsEmpty_apply]
      rw [hL, hR]
    rw [fiberNormSqComponent, hweight]
    rfl
  · intro K _ hK; exact absurd (Subsingleton.elim K (fun k : Fin 0 => k.elim0)) hK
  · intro h; exact absurd (Finset.mem_univ (fun k : Fin 0 => k.elim0)) h

omit [CompactSpace M] [I.Boundaryless] in

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma riemannianFiberNormSq_slot0Curry_covGradBundleEquiv_eq
    (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (Φ : TangentSpace I x →L[ℝ] TensorRSSpace 0 s I x)
    {n : ℕ} (e : Fin n → TangentSpace I x) (K₀ : Fin 0 → Fin n)
    (hreprS : ∀ S : TensorRSSpace 0 s I x,
      riemannianFiberNormSq (I := I) (M := M) g 0 s x S =
        ∑ K : Fin 0 → Fin n, ∑ J : Fin s → Fin n,
          fiberNormSqSummand (I := I) (M := M) g x 0 s S n e K J)
    (a : Fin n) :
    riemannianFiberNormSq (I := I) (M := M) g 0 s x
        (slot0Curry (I := I) (M := M) g x s e K₀
          (covGradBundleEquiv (I := I) (M := M) 0 s x Φ) a) =
      riemannianFiberNormSq (I := I) (M := M) g 0 s x (Φ (e a)) := by
  classical
  rw [riemannianFiberNormSq_eq_sum_componentS_sq (I := I) (M := M) g x s e hreprS _ K₀,
    riemannianFiberNormSq_eq_sum_componentS_sq (I := I) (M := M) g x s e hreprS _ K₀]
  refine Finset.sum_congr rfl (fun J _ => ?_)
  congr 1

  unfold fiberNormSqComponent
  set ωK : Tensor0SSpace 0 I x :=
    (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
      (fun k => g.inner x (e (K₀ k))) with hωK

  have hslot : (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          slot0Curry (I := I) (M := M) g x s e K₀
            (covGradBundleEquiv (I := I) (M := M) 0 s x Φ) a) ωK =
        tensor0S_curry (I := I) (M := M) s x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
            covGradBundleEquiv (I := I) (M := M) 0 s x Φ) ωK) (e a) := by
    rw [slot0Curry_apply (I := I) (M := M) g x s e K₀
      (covGradBundleEquiv (I := I) (M := M) 0 s x Φ) a ωK]
    have hscalar : tensor00Scalar (I := I) (M := M) x ωK = 1 := by
      rw [hωK,
        show ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
            (fun k => g.inner x (e (K₀ k))) : Tensor0SSpace 0 I x) =
          coframeS (I := I) (M := M) g x 0 e K₀ from rfl,
        tensor00Scalar_apply (I := I) (M := M) x _ (fun k : Fin 0 => k.elim0),
        coframeS_apply (I := I) (M := M) g x 0 e K₀]
      simp
    rw [hscalar, one_smul]
  rw [hslot]

  rw [show (tensor0S_curry (I := I) (M := M) s x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          covGradBundleEquiv (I := I) (M := M) 0 s x Φ) ωK) (e a)
        (fun k => e (J k)) : ℝ) =
      Tensor0SSpace.toModel
        (tensor0S_curry (I := I) (M := M) s x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
            covGradBundleEquiv (I := I) (M := M) 0 s x Φ) ωK) (e a))
        (fun k => e (J k)) from rfl]
  rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
    (T := (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
      covGradBundleEquiv (I := I) (M := M) 0 s x Φ) ωK) (v0 := e a) (vs := fun k => e (J k))]

  rw [covGradBundleEquiv_apply_eval (I := I) (M := M) 0 s x Φ ωK
    (Fin.cons (e a) (fun k => e (J k)))]
  rw [Fin.cons_zero]
  congr 1

omit [CompactSpace M] [I.Boundaryless] in

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma riemannianFiberNormSq_covGradBundleEquiv_eq_sum_frame
    (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (Φ : TangentSpace I x →L[ℝ] TensorRSSpace 0 s I x)
    {n : ℕ} (e : Fin n → TangentSpace I x) (K₀ : Fin 0 → Fin n)
    (hreprS : ∀ S : TensorRSSpace 0 s I x,
      riemannianFiberNormSq (I := I) (M := M) g 0 s x S =
        ∑ K : Fin 0 → Fin n, ∑ J : Fin s → Fin n,
          fiberNormSqSummand (I := I) (M := M) g x 0 s S n e K J)
    (hreprSucc : ∀ S : TensorRSSpace 0 (s + 1) I x,
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x S =
        ∑ K : Fin 0 → Fin n, ∑ J : Fin (s + 1) → Fin n,
          fiberNormSqSummand (I := I) (M := M) g x 0 (s + 1) S n e K J) :
    riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
        (covGradBundleEquiv (I := I) (M := M) 0 s x Φ) =
      ∑ a : Fin n, riemannianFiberNormSq (I := I) (M := M) g 0 s x (Φ (e a)) := by
  classical
  rw [riemannianFiberNormSq_succ_eq_sum_slot0Curry_of_frame (I := I) (M := M) g s x e K₀
    hreprS hreprSucc (covGradBundleEquiv (I := I) (M := M) 0 s x Φ)]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  exact riemannianFiberNormSq_slot0Curry_covGradBundleEquiv_eq (I := I) (M := M) g s x Φ e K₀
    hreprS a

omit [CompactSpace M] [I.Boundaryless] in

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma riemannianFiberNormSq_covGradBundleEquiv_le_card_mul
    (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (Φ : TangentSpace I x →L[ℝ] TensorRSSpace 0 s I x) (b : ℝ)
    (hbound : ∀ v : TangentSpace I x, g.inner x v v = 1 →
      riemannianFiberNormSq (I := I) (M := M) g 0 s x (Φ v) ≤ b) :
    riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
        (covGradBundleEquiv (I := I) (M := M) 0 s x Φ) ≤
      (Module.finrank ℝ E : ℝ) * b := by
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
  set e : Fin n → TangentSpace I x := fun i => eob i with he_def
  have hinner_eq : ∀ u v : TangentSpace I x, (inner ℝ u v : ℝ) = g.inner x u v :=
    fun u v => rfl
  have horth : ∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0 := by
    intro i j
    have horthb : Orthonormal ℝ (fun i : Fin n => eob i) := eob.orthonormal
    have hite := (orthonormal_iff_ite (𝕜 := ℝ) (E := TangentSpace I x)).mp horthb i j
    rw [he_def, ← hinner_eq (eob i) (eob j)]
    exact hite
  set K₀ : Fin 0 → Fin n := fun k => k.elim0 with hK₀
  have hreprS : ∀ S : TensorRSSpace 0 s I x,
      riemannianFiberNormSq (I := I) (M := M) g 0 s x S =
        ∑ K : Fin 0 → Fin n, ∑ J : Fin s → Fin n,
          fiberNormSqSummand (I := I) (M := M) g x 0 s S n e K J := by
    intro S; rfl
  have hreprSucc : ∀ S : TensorRSSpace 0 (s + 1) I x,
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x S =
        ∑ K : Fin 0 → Fin n, ∑ J : Fin (s + 1) → Fin n,
          fiberNormSqSummand (I := I) (M := M) g x 0 (s + 1) S n e K J := by
    intro S; rfl
  rw [riemannianFiberNormSq_covGradBundleEquiv_eq_sum_frame (I := I) (M := M) g s x Φ e K₀
    hreprS hreprSucc]

  have hper : ∀ a : Fin n,
      riemannianFiberNormSq (I := I) (M := M) g 0 s x (Φ (e a)) ≤ b := by
    intro a
    refine hbound (e a) ?_
    have := horth a a; rwa [if_pos rfl] at this
  refine le_trans (Finset.sum_le_sum (fun a _ => hper a)) ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hfr : Module.finrank ℝ (TangentSpace I x) = Module.finrank ℝ E := rfl
  rw [hn_def, hfr]

omit [CompactSpace M] [I.Boundaryless] in

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma riemannianFiberNormSq_covGradBundleEquiv_symm_reading_eq_slot0Curry
    (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (T : TensorRSSpace 0 (s + 1) I x)
    {n : ℕ} (e : Fin n → TangentSpace I x) (K₀ : Fin 0 → Fin n)
    (hreprS : ∀ S : TensorRSSpace 0 s I x,
      riemannianFiberNormSq (I := I) (M := M) g 0 s x S =
        ∑ K : Fin 0 → Fin n, ∑ J : Fin s → Fin n,
          fiberNormSqSummand (I := I) (M := M) g x 0 s S n e K J)
    (a : Fin n) :
    riemannianFiberNormSq (I := I) (M := M) g 0 s x
        ((covGradBundleEquiv (I := I) (M := M) 0 s x).symm T (e a)) =
      riemannianFiberNormSq (I := I) (M := M) g 0 s x
        (slot0Curry (I := I) (M := M) g x s e K₀ T a) := by
  classical
  rw [riemannianFiberNormSq_eq_sum_componentS_sq (I := I) (M := M) g x s e hreprS _ K₀,
    riemannianFiberNormSq_eq_sum_componentS_sq (I := I) (M := M) g x s e hreprS _ K₀]
  refine Finset.sum_congr rfl (fun J _ => ?_)
  congr 1
  unfold fiberNormSqComponent
  set ωK : Tensor0SSpace 0 I x :=
    (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
      (fun k => g.inner x (e (K₀ k))) with hωK

  have hslot : (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          slot0Curry (I := I) (M := M) g x s e K₀ T a) ωK =
        tensor0S_curry (I := I) (M := M) s x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from T) ωK) (e a) := by
    rw [slot0Curry_apply (I := I) (M := M) g x s e K₀ T a ωK]
    have hscalar : tensor00Scalar (I := I) (M := M) x ωK = 1 := by
      rw [hωK,
        show ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
            (fun k => g.inner x (e (K₀ k))) : Tensor0SSpace 0 I x) =
          coframeS (I := I) (M := M) g x 0 e K₀ from rfl,
        tensor00Scalar_apply (I := I) (M := M) x _ (fun k : Fin 0 => k.elim0),
        coframeS_apply (I := I) (M := M) g x 0 e K₀]
      simp
    rw [hscalar, one_smul]

  rw [show ((((covGradBundleEquiv (I := I) (M := M) 0 s x).symm T (e a)) ωK)
        (fun k => e (J k)) : ℝ) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          (covGradBundleEquiv (I := I) (M := M) 0 s x).symm T (e a)) ωK)
        (fun k => e (J k)) from rfl]
  rw [covGradBundleEquiv_symm_apply_eval (I := I) (M := M) 0 s x T (e a) ωK (fun k => e (J k))]
  rw [hslot]
  rw [show ((tensor0S_curry (I := I) (M := M) s x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from T) ωK) (e a))
        (fun k => e (J k)) : ℝ) =
      Tensor0SSpace.toModel
        (tensor0S_curry (I := I) (M := M) s x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from T) ωK) (e a))
        (fun k => e (J k)) from rfl]
  rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
    (T := (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from T) ωK)
    (v0 := e a) (vs := fun k => e (J k))]

omit [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma riemannianFiberNormSq_covGradBundleEquiv_symm_reading_le
    (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (T : TensorRSSpace 0 (s + 1) I x)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hBorth : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x (B i x) (B j x) = if i = j then (1 : ℝ) else 0)
    (i : Fin (Module.finrank ℝ E)) :
    riemannianFiberNormSq (I := I) (M := M) g 0 s x
        ((covGradBundleEquiv (I := I) (M := M) 0 s x).symm T (B i x)) ≤
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x T := by
  classical
  set eC : Fin (Module.finrank ℝ E) → TangentSpace I x := fun j => B j x with heC_def
  have hnC : Module.finrank ℝ E = Module.finrank ℝ (TangentSpace I x) := rfl
  have horthC : ∀ a b : Fin (Module.finrank ℝ E),
      g.inner x (eC a) (eC b) = if a = b then (1 : ℝ) else 0 := fun a b => hBorth a b
  set K₀ : Fin 0 → Fin (Module.finrank ℝ E) := fun k => k.elim0 with hK₀

  have hreprS : ∀ S : TensorRSSpace 0 s I x,
      riemannianFiberNormSq (I := I) (M := M) g 0 s x S =
        ∑ K : Fin 0 → Fin (Module.finrank ℝ E), ∑ J : Fin s → Fin (Module.finrank ℝ E),
          fiberNormSqSummand (I := I) (M := M) g x 0 s S (Module.finrank ℝ E) eC K J :=
    fun S => rfns_eq_sum_fiberNormSqSummand_of_orthoFrame (I := I) (M := M) g s x S eC hnC horthC
  have hreprSucc : ∀ S : TensorRSSpace 0 (s + 1) I x,
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x S =
        ∑ K : Fin 0 → Fin (Module.finrank ℝ E), ∑ J : Fin (s + 1) → Fin (Module.finrank ℝ E),
          fiberNormSqSummand (I := I) (M := M) g x 0 (s + 1) S (Module.finrank ℝ E) eC K J :=
    fun S => rfns_eq_sum_fiberNormSqSummand_of_orthoFrame (I := I) (M := M) g (s + 1) x S eC hnC
      horthC
  rw [riemannianFiberNormSq_covGradBundleEquiv_symm_reading_eq_slot0Curry (I := I) (M := M) g s x T
    eC K₀ hreprS i]
  exact riemannianFiberNormSq_slot0Curry_le_of_frame (I := I) (M := M) g s x eC K₀
    hreprS hreprSucc T i

omit [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma riemannianFiberNormSq_succ_eq_sum_bareSlot0Curry_of_orthoFrame
    (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (T : TensorRSSpace 0 (s + 1) I x)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (hn : n = Module.finrank ℝ (TangentSpace I x))
    (horth : ∀ a b : Fin n, g.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0) :
    riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x T =
      ∑ a : Fin n,
        riemannianFiberNormSq (I := I) (M := M) g 0 s x
          (tensor0SToTensorRS (I := I) (M := M) x
            (tensor0S_curry (I := I) (M := M) s x
              ((T : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x)
                (unitZeroSec (I := I) (M := M) x)) (e a))) := by
  classical
  set K₀ : Fin 0 → Fin n := fun k => k.elim0 with hK₀
  have hreprS : ∀ S : TensorRSSpace 0 s I x,
      riemannianFiberNormSq (I := I) (M := M) g 0 s x S =
        ∑ K : Fin 0 → Fin n, ∑ J : Fin s → Fin n,
          fiberNormSqSummand (I := I) (M := M) g x 0 s S n e K J :=
    fun S => rfns_eq_sum_fiberNormSqSummand_of_orthoFrame (I := I) (M := M) g s x S e hn horth
  have hreprSucc : ∀ S : TensorRSSpace 0 (s + 1) I x,
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x S =
        ∑ K : Fin 0 → Fin n, ∑ J : Fin (s + 1) → Fin n,
          fiberNormSqSummand (I := I) (M := M) g x 0 (s + 1) S n e K J :=
    fun S => rfns_eq_sum_fiberNormSqSummand_of_orthoFrame (I := I) (M := M) g (s + 1) x S e hn horth
  rw [riemannianFiberNormSq_succ_eq_sum_slot0Curry_of_frame (I := I) (M := M) g s x e K₀
    hreprS hreprSucc T]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [slot0Curry_eq_tensor0SToTensorRS_curry_unitZeroSec (I := I) (M := M) g x s e K₀ T a]

end Connection
end Integral
end DifferentialGeometry

end
