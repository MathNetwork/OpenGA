import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceArmRfnsBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RaisedKoszulParallelRaiseJetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CometricRaiseSlot0CovariantParallelism


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 3200000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

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
    ccTensorBilinSymm)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

noncomputable def raisedKoszulJetBase (R δ : ℝ) : ℝ :=
  2 * ((Module.finrank ℝ E : ℝ) + 1) * (1 + R) * (1 / (1 - δ))

noncomputable def raisedKoszulComponentBound (R δ : ℝ) (i : ℕ) : ℝ :=
  raisedKoszulJetBase (E := E) R δ ^ (2 * (i + 1) ^ 2)

noncomputable def raisedKoszulJetBound (R δ : ℝ) (i : ℕ) : ℝ :=
  (Module.finrank ℝ E : ℝ) ^ (3 + i) * raisedKoszulComponentBound (E := E) R δ i

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma raisedKoszulJetBase_nonneg (R δ : ℝ) (hR : 0 ≤ R) (hδ1 : δ < 1) :
    0 ≤ raisedKoszulJetBase (E := E) R δ := by
  have h1 : 0 < 1 - δ := by linarith
  unfold raisedKoszulJetBase
  apply mul_nonneg
  · apply mul_nonneg
    · positivity
    · linarith
  · exact div_nonneg zero_le_one h1.le

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma raisedKoszulComponentBound_nonneg (R δ : ℝ) (hR : 0 ≤ R) (hδ1 : δ < 1) (i : ℕ) :
    0 ≤ raisedKoszulComponentBound (E := E) R δ i := by
  unfold raisedKoszulComponentBound
  exact pow_nonneg (raisedKoszulJetBase_nonneg R δ hR hδ1) _

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma raisedKoszulJetBound_nonneg (R δ : ℝ) (hR : 0 ≤ R) (hδ1 : δ < 1) (i : ℕ) :
    0 ≤ raisedKoszulJetBound (E := E) R δ i := by
  unfold raisedKoszulJetBound
  exact mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
    (raisedKoszulComponentBound_nonneg R δ hR hδ1 i)

omit [FiniteDimensional ℝ E] in
lemma ten_R_sq_le_raisedKoszulComponentBound {R : ℝ} (hR : 0 ≤ R) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (i : ℕ) :
    10 * R ^ 2 ≤ raisedKoszulComponentBound (E := E) R δ i := by
  rw [raisedKoszulComponentBound]
  have hden : (0 : ℝ) < 1 - δ := by linarith
  have hd1 : (1 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by
    have hne : Module.finrank ℝ E ≠ 0 := NeZero.ne _
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne
  have hinv1 : (1 : ℝ) ≤ 1 / (1 - δ) := by
    rw [le_div_iff₀ hden]; linarith
  have hBR : (0 : ℝ) ≤ 1 + R := by linarith
  have hA : (4 : ℝ) ≤ 2 * ((Module.finrank ℝ E : ℝ) + 1) := by linarith
  have hbase_ge : 4 * (1 + R) ≤ raisedKoszulJetBase (E := E) R δ := by
    unfold raisedKoszulJetBase
    calc 4 * (1 + R) = 4 * (1 + R) * 1 := (mul_one _).symm
      _ ≤ 2 * ((Module.finrank ℝ E : ℝ) + 1) * (1 + R) * (1 / (1 - δ)) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hA hBR) hinv1 (by norm_num) (by positivity)
  have h4R0 : (0 : ℝ) ≤ 4 * (1 + R) := by positivity
  have hbase_sq : (4 * (1 + R)) ^ 2 ≤ raisedKoszulJetBase (E := E) R δ ^ 2 := by
    rw [sq, sq]; exact mul_self_le_mul_self h4R0 hbase_ge
  have h10 : 10 * R ^ 2 ≤ (4 * (1 + R)) ^ 2 := by nlinarith [sq_nonneg R, hR]
  have h4Rge1 : (1 : ℝ) ≤ 4 * (1 + R) := by nlinarith [hR]
  have hbase1 : (1 : ℝ) ≤ raisedKoszulJetBase (E := E) R δ := le_trans h4Rge1 hbase_ge
  have hexp : 2 ≤ 2 * (i + 1) ^ 2 := by
    have h1 : 1 ≤ (i + 1) ^ 2 := Nat.one_le_pow 2 (i + 1) (by omega)
    omega
  have hpow : raisedKoszulJetBase (E := E) R δ ^ 2 ≤
      raisedKoszulJetBase (E := E) R δ ^ (2 * (i + 1) ^ 2) :=
    pow_le_pow_right₀ hbase1 hexp
  calc 10 * R ^ 2 ≤ (4 * (1 + R)) ^ 2 := h10
    _ ≤ raisedKoszulJetBase (E := E) R δ ^ 2 := hbase_sq
    _ ≤ raisedKoszulJetBase (E := E) R δ ^ (2 * (i + 1) ^ 2) := hpow

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma rfns_eq_sum_componentSq_of_horth
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) (S : TensorRSSpace r s I x)
    {n : ℕ} (e : Fin n → TangentSpace I x) (hn : n = Module.finrank ℝ E)
    (horth : ∀ a b : Fin n, g₀.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0) :
    riemannianFiberNormSq (I := I) (M := M) g₀ r s x S =
      ∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g₀ x r s S n e K J) ^ 2 := by
  classical
  haveI : Nonempty (Fin n) := by
    rw [hn]
    exact ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))⟩⟩
  have he_li : LinearIndependent ℝ e := by
    rw [linearIndependent_iff']
    intro fs c hsum k hk_mem
    have h_zero : g₀.inner x (e k) (∑ j ∈ fs, c j • e j) = 0 := by rw [hsum]; simp
    rw [map_sum] at h_zero
    have h_pull : ∀ j ∈ fs, g₀.inner x (e k) (c j • e j) =
        c j * (if k = j then (1 : ℝ) else 0) := by
      intro j _
      rw [map_smul, horth k j, smul_eq_mul]
    rw [Finset.sum_congr rfl h_pull] at h_zero
    rw [Finset.sum_eq_single k (fun j _ hj => by rw [if_neg (Ne.symm hj), mul_zero])
      (fun hk => absurd hk_mem hk)] at h_zero
    rwa [if_pos rfl, mul_one] at h_zero
  have hrank : Module.finrank ℝ (TangentSpace I x) = Module.finrank ℝ E := rfl
  have hcard : Fintype.card (Fin n) = Module.finrank ℝ (TangentSpace I x) := by
    rw [Fintype.card_fin, hrank]; exact hn
  set bse := basisOfLinearIndependentOfCardEqFinrank he_li hcard with hbse_def
  have hbse : ∀ i : Fin n, bse i = e i := by
    intro i; rw [hbse_def, coe_basisOfLinearIndependentOfCardEqFinrank]
  exact riemannianFiberNormSq_eq_sum_componentSq_of_basis (I := I) (M := M) g₀ r s x S e bse hn hbse horth

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma fiberNormSqComponent_sq_le_rfns
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) (S : TensorRSSpace r s I x)
    {n : ℕ} (e : Fin n → TangentSpace I x) (hn : n = Module.finrank ℝ E)
    (horth : ∀ a b : Fin n, g₀.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0)
    (K : Fin r → Fin n) (J : Fin s → Fin n) :
    (fiberNormSqComponent (I := I) (M := M) g₀ x r s S n e K J) ^ 2 ≤
      riemannianFiberNormSq (I := I) (M := M) g₀ r s x S := by
  classical
  rw [rfns_eq_sum_componentSq_of_horth (I := I) (M := M) g₀ r s x S e hn horth]
  calc (fiberNormSqComponent (I := I) (M := M) g₀ x r s S n e K J) ^ 2
      ≤ ∑ J' : Fin s → Fin n,
          (fiberNormSqComponent (I := I) (M := M) g₀ x r s S n e K J') ^ 2 :=
        Finset.single_le_sum (fun J' _ => sq_nonneg _) (Finset.mem_univ J)
    _ ≤ ∑ K' : Fin r → Fin n, ∑ J' : Fin s → Fin n,
          (fiberNormSqComponent (I := I) (M := M) g₀ x r s S n e K' J') ^ 2 :=
        Finset.single_le_sum
          (fun K' _ => Finset.sum_nonneg (fun J' _ => sq_nonneg _)) (Finset.mem_univ K)

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

omit [NeZero (Module.finrank ℝ E)] in
lemma raisedKoszul_eq_cometricRaiseSlot0Field_koszulCovecCc
    (g₀ g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w) :
    raisedKoszul (I := I) g₀ g₁ =
      cometricRaiseSlot0Field (I := I) (M := M) g₀ 1 (koszulCovecCc (I := I) g₀ T) := by
  apply Integral.L2.SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [raisedKoszul_toSection, cometricRaiseSlot0Field_toSection]
  apply tensorRSSpace_ext 1 2 x
  intro om
  apply ContinuousMultilinearMap.ext
  intro YZ
  set u : TangentSpace I x := inverseMetricSharpFib (I := I) g₀ x om with hu
  set Δ : TangentSpace I x := PDE.DeTurck.connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1) with hΔ
  set D : Tensor0SSpace 3 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
      (koszulCovecCc (I := I) g₀ T).toSection x) (unitTensor (I := I) (M := M) x) with hDdef
  have hLHS : (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        raisedKoszulFib (I := I) g₀ g₁ x) om YZ =
      g₁.inner x Δ u := by
    rw [raisedKoszulFib_apply, raisedKoszulPairing_apply]
    set P : TangentSpace I x := raisedKoszulVec (I := I) g₀ g₁ x (YZ 0) (YZ 1) with hP
    have hLom : om (fun _ : Fin 1 => P) = g₀.inner x u P := by
      rw [← cotangentToDual_apply (I := I) (x := x) om P]
      rw [show cotangentToDual (I := I) (x := x) om P =
          cotangentToDualLinear (I := I) (x := x) om P from rfl]
      rw [← inverseMetricSharpFib_inner (I := I) g₀ x om P, hu]
    rw [hLom, g₀.symm x u P]
    have hPval : P = inverseMetricSharpFib (I := I) g₀ x (g0FlatCLM (I := I) g₁ x Δ) := by
      rw [hP, raisedKoszulVec_apply, hΔ]
    rw [hPval]
    rw [show g₀.inner x (inverseMetricSharpFib (I := I) g₀ x (g0FlatCLM (I := I) g₁ x Δ)) u =
        cotangentToDualLinear (I := I) (x := x) (g0FlatCLM (I := I) g₁ x Δ) u from
      inverseMetricSharpFib_inner (I := I) g₀ x (g0FlatCLM (I := I) g₁ x Δ) u]
    rw [show cotangentToDualLinear (I := I) (x := x) (g0FlatCLM (I := I) g₁ x Δ) u =
        cotangentToDual (I := I) (x := x) (g0FlatCLM (I := I) g₁ x Δ) u from rfl]
    rw [cotangentToDual_g0FlatCLM (I := I) g₁ x Δ u]
  have hRHS : (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        cometricRaiseSlot0Fib (I := I) g₀ 1 x D) om YZ =
      Tensor0SSpace.toModel D (Fin.cons (show E from u) (fun k => (show E from YZ k))) := by
    rw [cometricRaiseSlot0Fib_clm_apply (I := I) g₀ 1 x D om]
    rw [show (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (1 + 1) x
            (inverseMetricSharpFib (I := I) g₀ x om) D YZ : ℝ) =
        Tensor0SSpace.toModel
          (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (1 + 1) x
            (inverseMetricSharpFib (I := I) g₀ x om) D) YZ from rfl]
    rw [interior_product_toModel_eval (I := I) (M := M) (1 + 1) x
      (inverseMetricSharpFib (I := I) g₀ x om) D YZ, ← hu]
  rw [hLHS, hRHS]
  have hum : unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ T) x =
      Tensor0SSpace.toModel D := rfl
  rw [show Tensor0SSpace.toModel D (Fin.cons (show E from u) (fun k => (show E from YZ k))) =
      unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ T) x ![u, YZ 0, YZ 1] from by
    rw [hum]
    congr 1
    funext k
    fin_cases k <;> rfl]
  rw [koszulCovecCc_unitModel (I := I) g₀ T x (YZ 0) (YZ 1) u]
  rw [connDiffInner_g1_eq_half_covGradSymmS (I := I) g₀ g₁ T htie x (YZ 0) (YZ 1) u]
  rw [symmSCovGrad3]

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
private lemma iteratedCovGrad_cometricRaise_koszul_heq (g₀ : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g₀ 0 3) (i : ℕ) :
    ∃ σ : Equiv.Perm (Fin ((1 + i) + 2)),
      HEq (iteratedCovGrad (I := I) g₀ 1 2 i
            (cometricRaiseSlot0Field (I := I) (M := M) g₀ 1 W))
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ (1 + i)
          (domDomCongrSection (I := I) g₀ σ
            (castRankCc g₀ 0 (by omega : (3 : ℕ) + i = (1 + i) + 2)
              (iteratedCovGrad (I := I) g₀ 0 3 i W)))) := by
  induction i with
  | zero =>
      refine ⟨Equiv.refl _, ?_⟩
      simp only [iteratedCovGrad_zero]
      rw [domDomCongrSection_refl_rk]
      exact HEq.rfl
  | succ i ih =>
      obtain ⟨σ, hσ⟩ := ih
      obtain ⟨σ', hσ'⟩ := covGrad_domDomCongrSection_eq (I := I) (M := M) g₀ ((1 + i) + 2) σ
        (castRankCc g₀ 0 (by omega : (3 : ℕ) + i = (1 + i) + 2) (iteratedCovGrad (I := I) g₀ 0 3 i W))
      refine ⟨σ'.trans (Equiv.swap (0 : Fin ((1 + i) + 2 + 1)) 1), ?_⟩
      rw [iteratedCovGrad_succ]
      refine HEq.trans (covGrad_heq_congr_rk (I := I) (M := M) g₀ 1
        (by omega : 2 + i = (1 + i) + 1) hσ) ?_
      apply heq_of_eq
      rw [covGrad_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ (1 + i)]
      rw [hσ']
      rw [covGrad_castRankCc_eq]
      rw [← iteratedCovGrad_succ]
      rw [domDomCongrSection_comp_rk]
      rfl

omit [NeZero (Module.finrank ℝ E)] in
lemma riemannianFiberNormSq_iteratedCovGrad_cometricRaiseSlot0Field_koszul_eq
    (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2) (i : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 2 i
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
            (koszulCovecCc (I := I) g₀ T))).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
        ((iteratedCovGrad (I := I) g₀ 0 3 i (koszulCovecCc (I := I) g₀ T)).toSection x) := by
  obtain ⟨σ, hσ⟩ :=
    iteratedCovGrad_cometricRaise_koszul_heq (I := I) (M := M) g₀ (koszulCovecCc (I := I) g₀ T) i
  rw [rfns_heq_congr_rk (I := I) (M := M) g₀ 1 (by omega : 2 + i = (1 + i) + 1) hσ x]
  rw [rfns_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ (1 + i) x]
  rw [rfns_domDomCongrSection_eq]
  rw [rfns_castRankCc_rk]

private lemma fiberNormSqComponent_sq_iteratedCovGrad_raisedKoszul_le_koszul_rfns
    (g₀ g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
    (i : ℕ) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (hn : n = Module.finrank ℝ E)
    (horth : ∀ a b : Fin n, g₀.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0)
    (K : Fin 1 → Fin n) (J : Fin (2 + i) → Fin n) :
    (fiberNormSqComponent (I := I) (M := M) g₀ x 1 (2 + i)
        ((iteratedCovGrad (I := I) g₀ 1 2 i (raisedKoszul (I := I) g₀ g₁)).toSection x)
        n e K J) ^ 2 ≤
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
        ((iteratedCovGrad (I := I) g₀ 0 3 i (koszulCovecCc (I := I) g₀ T)).toSection x) := by
  calc (fiberNormSqComponent (I := I) (M := M) g₀ x 1 (2 + i)
          ((iteratedCovGrad (I := I) g₀ 1 2 i (raisedKoszul (I := I) g₀ g₁)).toSection x)
          n e K J) ^ 2
      ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 1 2 i (raisedKoszul (I := I) g₀ g₁)).toSection x) :=
        fiberNormSqComponent_sq_le_rfns (I := I) (M := M) g₀ 1 (2 + i) x _ e hn horth K J
    _ = riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 1 2 i
            (cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
              (koszulCovecCc (I := I) g₀ T))).toSection x) := by
        rw [raisedKoszul_eq_cometricRaiseSlot0Field_koszulCovecCc (I := I) (M := M) g₀ g₁ T htie]
    _ = riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
          ((iteratedCovGrad (I := I) g₀ 0 3 i (koszulCovecCc (I := I) g₀ T)).toSection x) :=
        riemannianFiberNormSq_iteratedCovGrad_cometricRaiseSlot0Field_koszul_eq (I := I) (M := M) g₀ T i x

theorem riemannianFiberNormSq_iteratedCovGrad_raisedKoszul_perComponent_le
    (g₀ g₁ : SmoothRiemannianMetric I M) (a : ℕ) (T : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
    {R : ℝ} (hR : 0 ≤ R) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (_hδ : metricCauchySchwarzBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hTjet : ∀ j : ℕ, j ≤ a + 1 → ∀ y : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) y
        ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection y) ≤ R ^ 2)
    (i : ℕ) (hi : i ≤ a) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (hn : n = Module.finrank ℝ E)
    (horth : ∀ a b : Fin n, g₀.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0)
    (K : Fin 1 → Fin n) (J : Fin (2 + i) → Fin n) :
    (fiberNormSqComponent (I := I) (M := M) g₀ x 1 (2 + i)
        ((iteratedCovGrad (I := I) g₀ 1 2 i (raisedKoszul (I := I) g₀ g₁)).toSection x)
        n e K J) ^ 2 ≤
      raisedKoszulComponentBound (E := E) R δ i := by
  calc (fiberNormSqComponent (I := I) (M := M) g₀ x 1 (2 + i)
          ((iteratedCovGrad (I := I) g₀ 1 2 i (raisedKoszul (I := I) g₀ g₁)).toSection x)
          n e K J) ^ 2
      ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
          ((iteratedCovGrad (I := I) g₀ 0 3 i (koszulCovecCc (I := I) g₀ T)).toSection x) :=
        fiberNormSqComponent_sq_iteratedCovGrad_raisedKoszul_le_koszul_rfns
          (I := I) g₀ g₁ T htie i x e hn horth K J
    _ ≤ 10 * R ^ 2 :=
        rfns_iteratedCovGrad_koszulCovecCc_le (I := I) g₀ a T hTjet i hi x
    _ ≤ raisedKoszulComponentBound (E := E) R δ i :=
        ten_R_sq_le_raisedKoszulComponentBound (E := E) hR hδ0 hδ1 i

theorem riemannianFiberNormSq_iteratedCovGrad_raisedKoszul_le
    (g₀ g₁ : SmoothRiemannianMetric I M) (a : ℕ) (T : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
    {R : ℝ} (hR : 0 ≤ R) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hTjet : ∀ j : ℕ, j ≤ a + 1 → ∀ y : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) y
        ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection y) ≤ R ^ 2) :
    ∀ i : ℕ, i ≤ a → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 1 2 i
            (raisedKoszul (I := I) g₀ g₁)).toSection x) ≤
        raisedKoszulJetBound (E := E) R δ i := by
  intro i hi x
  obtain ⟨n, e, bse, hn, hbse, horth, _hpars, _hrepr, _hsum⟩ :=
    tangent_orthonormalBasis_witness (I := I) (M := M) g₀ x
  have hnE : n = Module.finrank ℝ E := by rw [hn]; rfl
  rw [riemannianFiberNormSq_eq_sum_componentSq_of_basis (I := I) (M := M) g₀ 1 (2 + i) x
    ((iteratedCovGrad (I := I) g₀ 1 2 i (raisedKoszul (I := I) g₀ g₁)).toSection x)
    e bse hnE hbse horth]
  calc ∑ K : Fin 1 → Fin n, ∑ J : Fin (2 + i) → Fin n,
          (fiberNormSqComponent (I := I) (M := M) g₀ x 1 (2 + i)
            ((iteratedCovGrad (I := I) g₀ 1 2 i (raisedKoszul (I := I) g₀ g₁)).toSection x)
            n e K J) ^ 2
      ≤ ∑ K : Fin 1 → Fin n, ∑ J : Fin (2 + i) → Fin n,
          raisedKoszulComponentBound (E := E) R δ i :=
        Finset.sum_le_sum (fun K _ => Finset.sum_le_sum (fun J _ =>
          riemannianFiberNormSq_iteratedCovGrad_raisedKoszul_perComponent_le (I := I) g₀ g₁ a T htie hR hδ0 hδ1 hδ
            hTjet i hi x e hnE horth K J))
    _ = (Fintype.card (Fin 1 → Fin n) : ℝ) * (Fintype.card (Fin (2 + i) → Fin n) : ℝ) *
          raisedKoszulComponentBound (E := E) R δ i := by
        rw [Finset.sum_const, Finset.sum_const]
        simp only [Finset.card_univ, nsmul_eq_mul]
        ring
    _ = raisedKoszulJetBound (E := E) R δ i := by
        rw [raisedKoszulJetBound]
        have hcard : (Fintype.card (Fin 1 → Fin n) : ℝ) *
              (Fintype.card (Fin (2 + i) → Fin n) : ℝ)
            = (Module.finrank ℝ E : ℝ) ^ (3 + i) := by
          simp only [Fintype.card_fun, Fintype.card_fin]
          rw [← hnE]
          push_cast
          rw [← pow_add, show 1 + (2 + i) = 3 + i from by omega]
        rw [hcard]

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
