import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RaisedKoszulCovariantJetTower


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 6400000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization (metricCauchySchwarzBound
    ccTensorBilinSymm smoothCcTensorBilinForm ccTensorBilinSymm_smul ccTensorBilin_apply ccTensorModel
    ccTensorMultilinear)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma interior_product_toModel_eval (s : ℕ) (x : M) (v : TangentSpace I x)
    (D : Tensor0SSpace (s + 1) I x) (w : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel
        (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) s x v D) w =
      Tensor0SSpace.toModel D (Fin.cons (show E from v) (fun k => (show E from w k))) := by
  have h1 : Tensor0SSpace.toModel
      (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) s x v D) =
      Tensor0SBundle.model_interior_product (𝕜 := ℝ) (E := E) s (show E from v)
        (Tensor0SSpace.toModel D) := rfl
  rw [h1]
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma coframeS_one_eq_g0FlatCLM' (g₀ : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (K : Fin 1 → Fin n) :
    coframeS (I := I) (M := M) g₀ x 1 e K = g0FlatCLM (I := I) g₀ x (e (K 0)) := by
  apply cotangentToDualLinear_injective (I := I) (x := x)
  apply LinearMap.ext
  intro w
  rw [cotangentToDualLinear_apply, cotangentToDualLinear_apply, cotangentToDual_apply,
    cotangentToDual_apply]
  rw [show coframeS (I := I) (M := M) g₀ x 1 e K (fun _ : Fin 1 => w) =
      ∏ k : Fin 1, g₀.inner x (e (K k)) w from coframeS_apply (I := I) (M := M) g₀ x 1 e K _]
  rw [Fin.prod_univ_one]
  rw [g0FlatCLM_apply, dualToCotangent_apply]
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma fiberNormSqComponent_zero_toModel
    (g₀ : SmoothRiemannianMetric I M) (s : ℕ) (x : M) (S : SmoothCcTensor g₀ 0 s)
    {n : ℕ} (e : Fin n → TangentSpace I x) (K : Fin 0 → Fin n) (L : Fin s → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g₀ x 0 s (S.toSection x) n e K L =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from S.toSection x)
          (unitTensor (I := I) (M := M) x))
        (fun k => (show E from e (L k))) := by
  rw [show fiberNormSqComponent (I := I) (M := M) g₀ x 0 s (S.toSection x) n e K L =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from S.toSection x)
        (coframeS (I := I) (M := M) g₀ x 0 e K) (fun k => e (L k)) from rfl]
  rw [coframeS_zero_eq_unitZeroSec (I := I) (M := M) g₀ x e K]
  rfl

omit [NeZero (Module.finrank ℝ E)] in
omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma fiberNormSqComponent_cometricRaiseSlot0Field_eq
    (g₀ : SmoothRiemannianMetric I M) (s : ℕ) (x : M) (S : SmoothCcTensor g₀ 0 (s + 2))
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (K : Fin 1 → Fin n) (J : Fin (s + 1) → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g₀ x 1 (s + 1)
        ((cometricRaiseSlot0Field (I := I) (M := M) g₀ s S).toSection x) n e K J =
      fiberNormSqComponent (I := I) (M := M) g₀ x 0 (s + 2)
        (S.toSection x) n e (fun k => k.elim0) (Fin.cons (K 0) J) := by
  classical
  set D : Tensor0SSpace (s + 2) I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 2) I x from S.toSection x)
      (unitTensor (I := I) (M := M) x) with hD
  have hLHS : fiberNormSqComponent (I := I) (M := M) g₀ x 1 (s + 1)
        ((cometricRaiseSlot0Field (I := I) (M := M) g₀ s S).toSection x) n e K J =
      Tensor0SSpace.toModel D
        (Fin.cons (show E from e (K 0)) (fun k => (show E from e (J k)))) := by
    rw [show fiberNormSqComponent (I := I) (M := M) g₀ x 1 (s + 1)
          ((cometricRaiseSlot0Field (I := I) (M := M) g₀ s S).toSection x) n e K J =
        (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
            (cometricRaiseSlot0Field (I := I) (M := M) g₀ s S).toSection x)
          (coframeS (I := I) (M := M) g₀ x 1 e K)
          (fun k => e (J k)) from rfl]
    rw [coframeS_one_eq_g0FlatCLM' (I := I) (M := M) g₀ x e K]
    rw [cometricRaiseSlot0Field_toSection]
    rw [cometricRaiseSlot0Fib_clm_apply (I := I) g₀ s x D (g0FlatCLM (I := I) g₀ x (e (K 0)))]
    rw [inverseMetricSharpFib_g0FlatCLM (I := I) g₀ x (e (K 0))]
    rw [show (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (s + 1) x (e (K 0)) D
            (fun k => e (J k)) : ℝ) =
        Tensor0SSpace.toModel
          (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (s + 1) x (e (K 0)) D)
          (fun k => e (J k)) from rfl]
    rw [interior_product_toModel_eval (I := I) (M := M) (s + 1) x (e (K 0)) D
      (fun k => e (J k))]
  have hRHS : fiberNormSqComponent (I := I) (M := M) g₀ x 0 (s + 2)
        (S.toSection x) n e (fun k => k.elim0) (Fin.cons (K 0) J) =
      Tensor0SSpace.toModel D
        (Fin.cons (show E from e (K 0)) (fun k => (show E from e (J k)))) := by
    rw [fiberNormSqComponent_zero_toModel (I := I) (M := M) g₀ (s + 2) x S e
      (fun k => k.elim0) (Fin.cons (K 0) J)]
    congr 1
    funext k
    refine Fin.cases ?_ (fun j => ?_) k
    · simp only [Fin.cons_zero]
    · simp only [Fin.cons_succ]
  rw [hLHS, hRHS]

omit [NeZero (Module.finrank ℝ E)] in
omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma rfns_cometricRaiseSlot0Field_eq
    (g₀ : SmoothRiemannianMetric I M) (s : ℕ) (x : M) (S : SmoothCcTensor g₀ 0 (s + 2)) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 1 (s + 1) x
        ((cometricRaiseSlot0Field (I := I) (M := M) g₀ s S).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + 2) x (S.toSection x) := by
  classical
  obtain ⟨n, e, bse, hn, hbse, horth, _hpars, _hrepr, _hsum⟩ :=
    tangent_orthonormalBasis_witness (I := I) (M := M) g₀ x
  have hnE : n = Module.finrank ℝ E := by rw [hn]; rfl
  rw [riemannianFiberNormSq_eq_sum_componentSq_of_basis (I := I) (M := M) g₀ 1 (s + 1) x
    ((cometricRaiseSlot0Field (I := I) (M := M) g₀ s S).toSection x) e bse hnE hbse horth]
  rw [riemannianFiberNormSq_eq_sum_componentSq_of_basis (I := I) (M := M) g₀ 0 (s + 2) x
    (S.toSection x) e bse hnE hbse horth]
  rw [show (∑ K : Fin 1 → Fin n, ∑ J : Fin (s + 1) → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g₀ x 1 (s + 1)
          ((cometricRaiseSlot0Field (I := I) (M := M) g₀ s S).toSection x) n e K J) ^ 2) =
      ∑ K : Fin 1 → Fin n, ∑ J : Fin (s + 1) → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g₀ x 0 (s + 2)
          (S.toSection x) n e (fun k => k.elim0) (Fin.cons (K 0) J)) ^ 2 from by
    refine Finset.sum_congr rfl (fun K _ => Finset.sum_congr rfl (fun J _ => ?_))
    rw [fiberNormSqComponent_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ s x S e K J]]
  rw [show (∑ K : Fin 0 → Fin n, ∑ L : Fin (s + 2) → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g₀ x 0 (s + 2) (S.toSection x) n e K L) ^ 2) =
      ∑ L : Fin (s + 2) → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g₀ x 0 (s + 2)
          (S.toSection x) n e (fun k => k.elim0) L) ^ 2 from by
    rw [Finset.sum_eq_single (fun k : Fin 0 => k.elim0)]
    · intro K' _ hK'
      exact absurd (Subsingleton.elim _ _) hK'
    · intro h0
      exact absurd (Finset.mem_univ _) h0]
  rw [Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin n))
      (fun K : Fin 1 → Fin n => ∑ J : Fin (s + 1) → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g₀ x 0 (s + 2)
          (S.toSection x) n e (fun k => k.elim0) (Fin.cons (K 0) J)) ^ 2)
      (fun k0 : Fin n => ∑ J : Fin (s + 1) → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g₀ x 0 (s + 2)
          (S.toSection x) n e (fun k => k.elim0) (Fin.cons k0 J)) ^ 2)
      (fun K => rfl)]
  rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (s + 2) => Fin n))
      (fun pr : Fin n × (Fin (s + 1) → Fin n) =>
        (fiberNormSqComponent (I := I) (M := M) g₀ x 0 (s + 2)
          (S.toSection x) n e (fun k => k.elim0) (Fin.cons pr.1 pr.2)) ^ 2)
      (fun L : Fin (s + 2) → Fin n =>
        (fiberNormSqComponent (I := I) (M := M) g₀ x 0 (s + 2)
          (S.toSection x) n e (fun k => k.elim0) L) ^ 2)
      (fun pr => by simp only [Fin.consEquiv, Equiv.coe_fn_mk])]
  rw [Fintype.sum_prod_type]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem rfns_heq_congr_rk (g₀ : SmoothRiemannianMetric I M) (r : ℕ) {a b : ℕ}
    (h : a = b) {Y : SmoothCcTensor g₀ r a} {Z : SmoothCcTensor g₀ r b} (hYZ : HEq Y Z) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ r a x (Y.toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ r b x (Z.toSection x) := by
  subst h; rw [eq_of_heq hYZ]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem covGrad_heq_congr_rk (g₀ : SmoothRiemannianMetric I M) (r : ℕ) {a b : ℕ}
    (h : a = b) {Y : SmoothCcTensor g₀ r a} {Z : SmoothCcTensor g₀ r b} (hYZ : HEq Y Z) :
    HEq (covGrad (I := I) (M := M) g₀ r a Y) (covGrad (I := I) (M := M) g₀ r b Z) := by
  subst h; rw [eq_of_heq hYZ]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem rfns_castRankCc_rk (g₀ : SmoothRiemannianMetric I M) (r : ℕ) {a b : ℕ}
    (h : a = b) (Y : SmoothCcTensor g₀ r a) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ r b x ((castRankCc g₀ r h Y).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ r a x (Y.toSection x) := by
  subst h; rfl

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem covGrad_castRankCc_eq (g₀ : SmoothRiemannianMetric I M) (r : ℕ) {a b : ℕ}
    (h : a = b) (Y : SmoothCcTensor g₀ r a) :
    covGrad (I := I) (M := M) g₀ r b (castRankCc g₀ r h Y) =
      castRankCc g₀ r (congrArg (· + 1) h) (covGrad (I := I) (M := M) g₀ r a Y) := by
  subst h; rfl

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem domDomCongrSection_refl_rk (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (S : SmoothCcTensor g₀ 0 s) :
    domDomCongrSection (I := I) g₀ (Equiv.refl (Fin s)) S = S := by
  apply smoothCcTensor_ext_of_unitModel
  intro x
  rw [domDomCongrSection_unitModel]
  ext m
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  rfl

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem domDomCongrSection_comp_rk (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (σ τ : Equiv.Perm (Fin s)) (S : SmoothCcTensor g₀ 0 s) :
    domDomCongrSection (I := I) g₀ σ (domDomCongrSection (I := I) g₀ τ S) =
      domDomCongrSection (I := I) g₀ (τ.trans σ) S := by
  apply smoothCcTensor_ext_of_unitModel
  intro x
  rw [domDomCongrSection_unitModel, domDomCongrSection_unitModel, domDomCongrSection_unitModel]
  ext m
  rw [ContinuousMultilinearMap.domDomCongr_apply, ContinuousMultilinearMap.domDomCongr_apply,
    ContinuousMultilinearMap.domDomCongr_apply]
  rfl

omit [NeZero (Module.finrank ℝ E)] in
private theorem covGrad_domDomCongrSection_eq (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (σ : Equiv.Perm (Fin s)) (S : SmoothCcTensor g₀ 0 s) :
    ∃ σ' : Equiv.Perm (Fin (s + 1)),
      covGrad (I := I) (M := M) g₀ 0 s (domDomCongrSection (I := I) g₀ σ S) =
        domDomCongrSection (I := I) g₀ σ' (covGrad (I := I) (M := M) g₀ 0 s S) := by
  obtain ⟨σ', hσ'⟩ :=
    exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀ σ S 1
  refine ⟨σ', ?_⟩
  apply smoothCcTensor_ext_of_unitModel
  intro x
  have h1 := hσ' x
  rw [iteratedCovGrad_succ, iteratedCovGrad_zero, iteratedCovGrad_succ, iteratedCovGrad_zero] at h1
  rw [domDomCongrSection_unitModel]
  exact h1

omit [NeZero (Module.finrank ℝ E)] in
private theorem rfns_domDomCongrSection_eq (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (σ : Equiv.Perm (Fin s)) (S : SmoothCcTensor g₀ 0 s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 s x
        ((domDomCongrSection (I := I) g₀ σ S).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 s x (S.toSection x) := by
  have h := riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀ σ S 0 x
  simpa using h

omit [NeZero (Module.finrank ℝ E)] in
private lemma iteratedCovGrad_cometricRaise_heq (g₀ : SmoothRiemannianMetric I M)
    (s : ℕ) (W : SmoothCcTensor g₀ 0 (s + 2)) (i : ℕ) :
    ∃ σ : Equiv.Perm (Fin ((s + i) + 2)),
      HEq (iteratedCovGrad (I := I) g₀ 1 (s + 1) i
            (cometricRaiseSlot0Field (I := I) (M := M) g₀ s W))
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ (s + i)
          (domDomCongrSection (I := I) g₀ σ
            (castRankCc g₀ 0 (by omega : (s + 2) + i = (s + i) + 2)
              (iteratedCovGrad (I := I) g₀ 0 (s + 2) i W)))) := by
  induction i with
  | zero =>
      refine ⟨Equiv.refl _, ?_⟩
      simp only [iteratedCovGrad_zero]
      rw [domDomCongrSection_refl_rk]
      exact HEq.rfl
  | succ i ih =>
      obtain ⟨σ, hσ⟩ := ih
      obtain ⟨σ', hσ'⟩ := covGrad_domDomCongrSection_eq (I := I) (M := M) g₀ ((s + i) + 2) σ
        (castRankCc g₀ 0 (by omega : (s + 2) + i = (s + i) + 2)
          (iteratedCovGrad (I := I) g₀ 0 (s + 2) i W))
      refine ⟨σ'.trans (Equiv.swap (0 : Fin ((s + i) + 2 + 1)) 1), ?_⟩
      rw [iteratedCovGrad_succ]
      refine HEq.trans (covGrad_heq_congr_rk (I := I) (M := M) g₀ 1
        (by omega : (s + 1) + i = (s + i) + 1) hσ) ?_
      apply heq_of_eq
      rw [covGrad_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ (s + i)]
      rw [hσ']
      rw [covGrad_castRankCc_eq]
      rw [← iteratedCovGrad_succ]
      rw [domDomCongrSection_comp_rk]
      rfl

omit [NeZero (Module.finrank ℝ E)] in
lemma riemannianFiberNormSq_iteratedCovGrad_cometricRaiseSlot0Field_eq
    (g₀ : SmoothRiemannianMetric I M) (s : ℕ) (W : SmoothCcTensor g₀ 0 (s + 2)) (i : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 1 ((s + 1) + i) x
        ((iteratedCovGrad (I := I) g₀ 1 (s + 1) i
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ s W)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((s + 2) + i) x
        ((iteratedCovGrad (I := I) g₀ 0 (s + 2) i W).toSection x) := by
  obtain ⟨σ, hσ⟩ := iteratedCovGrad_cometricRaise_heq (I := I) (M := M) g₀ s W i
  rw [rfns_heq_congr_rk (I := I) (M := M) g₀ 1 (by omega : (s + 1) + i = (s + i) + 1) hσ x]
  rw [rfns_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ (s + i) x]
  rw [rfns_domDomCongrSection_eq]
  rw [rfns_castRankCc_rk]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma ccTensorBilinSymm_zero_apply (g₀ : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2) x v w = 0 := by
  have key := ccTensorBilinSymm_smul (I := I) g₀ (0 : ℝ) (0 : SmoothCcTensor g₀ 0 2) x v w
  rw [zero_smul, zero_mul] at key
  exact key

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] in
private lemma flatArmVec_self_eq_zero (g₀ : SmoothRiemannianMetric I M) (kind : Bool) (x : M)
    (om : Tensor0SSpace 1 I x) (v0 : TangentSpace I x) :
    flatArmVec (I := I) g₀ g₀ kind x om v0 = 0 := by
  have hcd : PDE.DeTurck.connDiff (I := I) g₀ g₀ x = 0 := by
    rw [PDE.DeTurck.connDiff_self]; rfl
  cases kind with
  | true =>
      simp only [flatArmVec, if_true, hcd, ContinuousLinearMap.zero_apply, neg_zero]
  | false =>
      simp only [flatArmVec, if_neg (by decide : ¬ (false = true)), hcd]
      simp

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] in
private lemma flatArmFib_self_eq_zero (g₀ : SmoothRiemannianMetric I M) (kind : Bool) (x : M) :
    flatArmFib (I := I) g₀ g₀ kind x = (0 : TensorRSSpace 1 2 I x) := by
  apply tensorRSSpace_ext 1 2 x
  intro om
  rw [show (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        (0 : TensorRSSpace 1 2 I x)) om = (0 : Tensor0SSpace 2 I x) from rfl]
  rw [flatArmFib_apply]
  apply ContinuousMultilinearMap.ext
  intro YZ
  rw [flatArmPairing_apply, flatArmVec_self_eq_zero, map_zero, ContinuousLinearMap.zero_apply]
  rfl

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma flatArmCc_self_eq_zero (g₀ : SmoothRiemannianMetric I M) (kind : Bool) :
    flatArmCc (I := I) g₀ g₀ kind = 0 := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [flatArmCc_toSection, flatArmFib_self_eq_zero]
  simp

omit [NeZero (Module.finrank ℝ E)] in
private lemma covGrad_sharpFlatEndoCc_self_eq_zero (g₀ : SmoothRiemannianMetric I M) :
    covGrad (I := I) (M := M) g₀ 1 1 (sharpFlatEndoCc (I := I) g₀ g₀) = 0 := by
  rw [covGrad_sharpFlatEndoCc_eq_arms (I := I) g₀ g₀]
  rw [flatArmCc_self_eq_zero, flatArmCc_self_eq_zero, add_zero]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma iteratedCovGrad_zero_tensor (g₀ : SmoothRiemannianMetric I M) (r s m : ℕ) :
    iteratedCovGrad (I := I) g₀ r s m (0 : SmoothCcTensor g₀ r s) = 0 := by
  induction m with
  | zero => rw [iteratedCovGrad_zero]
  | succ m ih => rw [iteratedCovGrad_succ, ih, covGrad_zero]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma unitModel_eq_ccTensorBilin_loc (g₀ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (b : M) (u w : TangentSpace I b) :
    unitModel (I := I) (M := M) g₀ 2 S b ![u, w] = smoothCcTensorBilinForm (I := I) g₀ S b u w := by
  rw [ccTensorBilin_apply (I := I) g₀ S b u w, ccTensorModel]
  rw [show ccTensorMultilinear (I := I) g₀ S b =
      (show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace 2 I b from S.toSection b)
        (unitZeroSec (I := I) (M := M) b) from rfl]
  rw [unitModel]
  refine congrArg _ ?_
  funext k
  fin_cases k <;> rfl

omit [NeZero (Module.finrank ℝ E)] in
omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma omRecoverEndoCc_eq_idEndo_add_raise
    (g₀ g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w) :
    omRecoverEndoCc (I := I) g₀ g₁ =
      sharpFlatEndoCc (I := I) g₀ g₀ +
        cometricRaiseSlot0Field (I := I) (M := M) g₀ 0 (ccTensor02Symm (I := I) (M := M) g₀ T) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply tensorRSSpace_ext 1 1 x
  intro om
  rw [show (sharpFlatEndoCc (I := I) g₀ g₀ +
        cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
          (ccTensor02Symm (I := I) (M := M) g₀ T)).toSection x =
      (sharpFlatEndoCc (I := I) g₀ g₀).toSection x +
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
          (ccTensor02Symm (I := I) (M := M) g₀ T)).toSection x from by
    rw [SmoothCcTensor.toSection_add]; rfl]
  rw [show (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        ((sharpFlatEndoCc (I := I) g₀ g₀).toSection x +
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
            (ccTensor02Symm (I := I) (M := M) g₀ T)).toSection x)) om =
      (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
          (sharpFlatEndoCc (I := I) g₀ g₀).toSection x) om +
        (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
            (ccTensor02Symm (I := I) (M := M) g₀ T)).toSection x) om from rfl]
  have hL : (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (omRecoverEndoCc (I := I) g₀ g₁).toSection x) om =
      g0FlatCLM (I := I) g₁ x (inverseMetricSharpFib (I := I) g₀ x om) := by
    rw [omRecoverEndoCc_toSection]; rfl
  have hS : (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (sharpFlatEndoCc (I := I) g₀ g₀).toSection x) om =
      g0FlatCLM (I := I) g₀ x (inverseMetricSharpFib (I := I) g₀ x om) := by
    rw [sharpFlatEndoCc_toSection]; rfl
  apply cotangentToDualLinear_injective (I := I) (x := x)
  apply LinearMap.ext
  intro w
  rw [cotangentToDualLinear_apply, cotangentToDualLinear_apply]
  rw [show cotangentToDual (I := I)
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
            (sharpFlatEndoCc (I := I) g₀ g₀).toSection x) om +
          (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
            (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
              (ccTensor02Symm (I := I) (M := M) g₀ T)).toSection x) om) w =
      cotangentToDual (I := I)
          ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
            (sharpFlatEndoCc (I := I) g₀ g₀).toSection x) om) w +
        cotangentToDual (I := I)
          ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
            (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
              (ccTensor02Symm (I := I) (M := M) g₀ T)).toSection x) om) w from by
    rw [← cotangentToDualLinear_apply, ← cotangentToDualLinear_apply,
      ← cotangentToDualLinear_apply, map_add, LinearMap.add_apply]]
  rw [hL, cotangentToDual_g0FlatCLM]
  rw [hS, cotangentToDual_g0FlatCLM]
  rw [show cotangentToDual (I := I)
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
            (ccTensor02Symm (I := I) (M := M) g₀ T)).toSection x) om) w =
      ccTensorBilinSymm (I := I) g₀ T x (inverseMetricSharpFib (I := I) g₀ x om) w from by
    rw [cotangentToDual_apply]
    rw [cometricRaiseSlot0Field_toSection]
    rw [cometricRaiseSlot0Fib_clm_apply (I := I) g₀ 0 x _ om]
    rw [show (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (0 + 1) x
            (inverseMetricSharpFib (I := I) g₀ x om)
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (0 + 2) I x from
                (ccTensor02Symm (I := I) (M := M) g₀ T).toSection x)
              (unitTensor (I := I) (M := M) x)) (fun _ : Fin 1 => w) : ℝ) =
        Tensor0SSpace.toModel
          (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (0 + 1) x
            (inverseMetricSharpFib (I := I) g₀ x om)
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (0 + 2) I x from
                (ccTensor02Symm (I := I) (M := M) g₀ T).toSection x)
              (unitTensor (I := I) (M := M) x)))
          (fun _ : Fin 1 => w) from rfl]
    rw [interior_product_toModel_eval (I := I) (M := M) (0 + 1) x
      (inverseMetricSharpFib (I := I) g₀ x om)
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (0 + 2) I x from
          (ccTensor02Symm (I := I) (M := M) g₀ T).toSection x)
        (unitTensor (I := I) (M := M) x)) (fun _ : Fin 1 => w)]
    rw [show Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (0 + 2) I x from
              (ccTensor02Symm (I := I) (M := M) g₀ T).toSection x)
            (unitTensor (I := I) (M := M) x))
          (Fin.cons (show E from inverseMetricSharpFib (I := I) g₀ x om)
            (fun _ : Fin 1 => (show E from w))) =
        unitModel (I := I) (M := M) g₀ 2 (ccTensor02Symm (I := I) (M := M) g₀ T) x
          ![inverseMetricSharpFib (I := I) g₀ x om, w] from by
      rw [unitModel]
      congr 1
      funext k
      refine Fin.cases ?_ (fun j => ?_) k
      · simp only [Fin.cons_zero, Matrix.cons_val_zero]
      · simp only [Fin.cons_succ]
        fin_cases j
        rfl]
    rw [unitModel_eq_ccTensorBilin_loc, ccTensorBilin_symmS]]
  rw [htie]

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma rfns_idEndo_le (g₀ : SmoothRiemannianMetric I M) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x
        ((sharpFlatEndoCc (I := I) g₀ g₀).toSection x) ≤
      (Module.finrank ℝ E : ℝ) ^ 2 := by
  have htie0 : ∀ (y : M) (v w : TangentSpace I y),
      g₀.inner y v w =
        g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2) y v w := by
    intro y v w
    rw [ccTensorBilinSymm_zero_apply, add_zero]
  have hbnd : metricCauchySchwarzBound (I := I) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) 0 := by
    intro y v w
    rw [ccTensorBilinSymm_zero_apply]
    simp
  have hb := riemannianFiberNormSq_sharpFlatEndoCc_le_of_lt_one (I := I) g₀ (δ₀ := 0) (le_refl 0)
    (by norm_num : (0 : ℝ) < 1) g₀ (0 : SmoothCcTensor g₀ 0 2) htie0
    (le_refl (0 : ℝ)) (le_refl 0) hbnd x
  have hsimp : (Module.finrank ℝ E : ℝ) ^ 2 * (1 / (1 - (0 : ℝ))) ^ 2 =
      (Module.finrank ℝ E : ℝ) ^ 2 := by norm_num
  rw [hsimp] at hb
  exact hb

omit [NeZero (Module.finrank ℝ E)] in
theorem riemannianFiberNormSq_iteratedCovGrad_omRecoverEndoCc_le
    (g₀ g₁ : SmoothRiemannianMetric I M) (a : ℕ) (T : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
    {R : ℝ} (_hR : 0 ≤ R) {δ : ℝ} (_hδ0 : 0 ≤ δ) (_hδ1 : δ < 1)
    (hTjet : ∀ j : ℕ, j ≤ a + 1 → ∀ y : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) y
        ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection y) ≤ R ^ 2) :
    ∀ i : ℕ, i ≤ a → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
          ((iteratedCovGrad (I := I) g₀ 1 1 i
            (omRecoverEndoCc (I := I) g₀ g₁)).toSection x) ≤
        2 * (Module.finrank ℝ E : ℝ) ^ 2 + 2 * R ^ 2 := by
  intro i hi x
  have hdecomp := omRecoverEndoCc_eq_idEndo_add_raise (I := I) (M := M) g₀ g₁ T htie
  rw [hdecomp, iteratedCovGrad_add]
  rw [show ((iteratedCovGrad (I := I) g₀ 1 1 i (sharpFlatEndoCc (I := I) g₀ g₀) +
        iteratedCovGrad (I := I) g₀ 1 1 i
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
            (ccTensor02Symm (I := I) (M := M) g₀ T))).toSection x) =
      (iteratedCovGrad (I := I) g₀ 1 1 i (sharpFlatEndoCc (I := I) g₀ g₀)).toSection x +
        (iteratedCovGrad (I := I) g₀ 1 1 i
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
            (ccTensor02Symm (I := I) (M := M) g₀ T))).toSection x from by
    rw [SmoothCcTensor.toSection_add]; rfl]
  refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 1 (1 + i) x _ _) ?_
  have hraise : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
      ((iteratedCovGrad (I := I) g₀ 1 1 i
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
          (ccTensor02Symm (I := I) (M := M) g₀ T))).toSection x) ≤ R ^ 2 := by
    have hiso := riemannianFiberNormSq_iteratedCovGrad_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ 0
      (ccTensor02Symm (I := I) (M := M) g₀ T) i x
    rw [hiso]
    exact rfns_iteratedCovGrad_symmS_le (I := I) (M := M) g₀ a T hTjet i (by omega) x
  have hid : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
      ((iteratedCovGrad (I := I) g₀ 1 1 i (sharpFlatEndoCc (I := I) g₀ g₀)).toSection x) ≤
        (Module.finrank ℝ E : ℝ) ^ 2 := by
    match i, hi with
    | 0, _ =>
        rw [iteratedCovGrad_zero]
        exact rfns_idEndo_le (I := I) (M := M) g₀ x
    | (m + 1), _ =>
        have hzero : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + (m + 1)) x
            ((iteratedCovGrad (I := I) g₀ 1 1 (m + 1)
              (sharpFlatEndoCc (I := I) g₀ g₀)).toSection x) = 0 := by
          rw [← rfns_iteratedCovGrad_covGrad_comm_rs (I := I) (M := M) g₀ 1 1 m
            (sharpFlatEndoCc (I := I) g₀ g₀) x]
          rw [covGrad_sharpFlatEndoCc_self_eq_zero, iteratedCovGrad_zero_tensor]
          rw [show ((0 : SmoothCcTensor g₀ 1 (1 + 1 + m)).toSection x) =
              (0 : TensorRSSpace 1 (1 + 1 + m) I x) from by
            rw [SmoothCcTensor.toSection_zero]; rfl]
          exact riemannianFiberNormSq_zero (I := I) (M := M) g₀ 1 (1 + 1 + m) x
        rw [hzero]
        positivity
  have hidnn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
      ((iteratedCovGrad (I := I) g₀ 1 1 i (sharpFlatEndoCc (I := I) g₀ g₀)).toSection x) :=
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (1 + i) x _
  have hraisenn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
      ((iteratedCovGrad (I := I) g₀ 1 1 i
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
          (ccTensor02Symm (I := I) (M := M) g₀ T))).toSection x) :=
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (1 + i) x _
  linarith [hid, hraise]

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
