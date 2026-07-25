import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Defs
import DifferentialGeometry.Analysis.Spectral.Intrinsic.TensorHsInterpolationLimit
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.MercerProjectorTrace


noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorHeatEquation

section

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

def weylSobolevExp : ℕ := 2 * (2 * (Module.finrank ℝ E / 2 + 1))

lemma weylSobolevExp_gt_finrank :
    Module.finrank ℝ E < weylSobolevExp (E := E) := by
  unfold weylSobolevExp; omega

end

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private lemma summable_nat_add_one_rpow_neg (p : ℝ) (hp : 1 < p) :
    Summable (fun k : ℕ => ((k : ℝ) + 1) ^ (-p)) := by
  have hbase : Summable (fun n : ℕ => ((n : ℝ) ^ p)⁻¹) :=
    Real.summable_nat_rpow_inv.mpr hp
  have hshift : Summable (fun k : ℕ => (((k + 1 : ℕ) : ℝ) ^ p)⁻¹) :=
    hbase.comp_injective (add_left_injective 1)
  refine hshift.congr (fun k => ?_)
  rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ (k : ℝ) + 1)]
  push_cast
  ring_nf

private theorem exists_growth_of_counting_bound
    {ι : Type*} (w : ι → ℝ) (hw1 : ∀ i, 1 ≤ w i)
    (hfin : ∀ Λ : ℝ, {i | w i < Λ}.Finite)
    (K p : ℝ) (hK : 0 < K) (hp : 0 < p)
    (hcount : ∀ Λ : ℝ, (Nat.card {i | w i < Λ} : ℝ) ≤ K * Λ ^ p) :
    ∃ (φ : ι → ℕ) (C : ℝ), Function.Injective φ ∧ 0 < C ∧
      ∀ i, C * ((φ i : ℝ) + 1) ^ (1 / p) ≤ w i := by
  classical
  obtain ⟨enc, henc⟩ : ∃ enc : ι → ℕ, Function.Injective enc := by
    have huniv : (Set.univ : Set ι) = ⋃ n : ℕ, {i | w i < (n : ℝ)} := by
      ext i
      simp only [mem_iUnion, mem_setOf_eq, mem_univ, true_iff]
      exact ⟨⌈w i⌉₊ + 1, by push_cast; linarith [Nat.le_ceil (w i)]⟩
    have hcountUniv : (Set.univ : Set ι).Countable := by
      rw [huniv]; exact Set.countable_iUnion (fun n => (hfin (n : ℝ)).countable)
    have : Countable ι := countable_univ_iff.mp hcountUniv
    exact exists_injective_nat ι
  set lex : ι → ι → Prop := fun a b => w a < w b ∨ (w a = w b ∧ enc a < enc b)
    with hlex
  set pred : ι → Set ι := fun i => {j | lex j i} with hpred
  have hpred_sub : ∀ i, pred i ⊆ {j | w j < w i + 1} := by
    intro i j hj
    rcases hj with h | ⟨h, _⟩
    · simp only [mem_setOf_eq]; linarith
    · simp only [mem_setOf_eq]; rw [h]; linarith
  have hpred_fin : ∀ i, (pred i).Finite := fun i =>
    (hfin (w i + 1)).subset (hpred_sub i)
  have hirr : ∀ i, ¬ lex i i := by
    intro i h; rcases h with h | ⟨_, h⟩
    · exact lt_irrefl _ h
    · exact lt_irrefl _ h
  have htrans : ∀ a b c, lex a b → lex b c → lex a c := by
    intro a b c hab hbc
    rcases hab with hab | ⟨hab1, hab2⟩ <;> rcases hbc with hbc | ⟨hbc1, hbc2⟩
    · exact Or.inl (hab.trans hbc)
    · exact Or.inl (by rw [← hbc1]; exact hab)
    · exact Or.inl (by rw [hab1]; exact hbc)
    · exact Or.inr ⟨hab1.trans hbc1, hab2.trans hbc2⟩
  have htot : ∀ a b, a ≠ b → lex a b ∨ lex b a := by
    intro a b hab
    rcases lt_trichotomy (w a) (w b) with h | h | h
    · exact Or.inl (Or.inl h)
    · rcases lt_trichotomy (enc a) (enc b) with he | he | he
      · exact Or.inl (Or.inr ⟨h, he⟩)
      · exact absurd (henc he) hab
      · exact Or.inr (Or.inr ⟨h.symm, he⟩)
    · exact Or.inr (Or.inl h)
  set φ : ι → ℕ := fun i => (pred i).ncard with hφ
  refine ⟨φ, (K * 2 ^ p) ^ (-(1 / p)), ?_, by positivity, ?_⟩
  · intro i j hij
    by_contra hne
    have hsub_of_lex : ∀ a b, lex a b → pred a ⊆ pred b := by
      intro a b hab x hx; exact htrans x a b hx hab
    rcases htot i j hne with h | h
    · have hss : pred i ⊂ pred j := by
        refine ⟨hsub_of_lex i j h, ?_⟩
        intro hcontra
        exact hirr i (hcontra (show i ∈ pred j from h))
      have := Set.ncard_lt_ncard hss (hpred_fin j)
      rw [hφ] at hij; simp only at hij; omega
    · have hss : pred j ⊂ pred i := by
        refine ⟨hsub_of_lex j i h, ?_⟩
        intro hcontra
        exact hirr j (hcontra (show j ∈ pred i from h))
      have := Set.ncard_lt_ncard hss (hpred_fin i)
      rw [hφ] at hij; simp only at hij; omega
  · intro i
    have hi_notmem : i ∉ pred i := hirr i
    have hins_sub : insert i (pred i) ⊆ {j | w j < w i + 1} := by
      intro x hx
      rcases hx with rfl | hx
      · simp only [mem_setOf_eq]; linarith
      · exact hpred_sub i hx
    have hins_card : (insert i (pred i)).ncard = (pred i).ncard + 1 :=
      Set.ncard_insert_of_notMem hi_notmem (hpred_fin i)
    have hcard_le :
        (insert i (pred i)).ncard ≤ ({j | w j < w i + 1} : Set ι).ncard :=
      Set.ncard_le_ncard hins_sub (hfin (w i + 1))
    have hN : (({j | w j < w i + 1} : Set ι).ncard : ℝ) ≤ K * (w i + 1) ^ p := by
      have h := hcount (w i + 1); rwa [Nat.card_coe_set_eq] at h
    have hstep : ((φ i : ℝ) + 1) ≤ K * (w i + 1) ^ p := by
      have hcalc : ((pred i).ncard + 1 : ℝ) ≤ K * (w i + 1) ^ p := by
        calc ((pred i).ncard + 1 : ℝ) = ((insert i (pred i)).ncard : ℝ) := by
              rw [hins_card]; push_cast; ring
          _ ≤ (({j | w j < w i + 1} : Set ι).ncard : ℝ) := by exact_mod_cast hcard_le
          _ ≤ K * (w i + 1) ^ p := hN
      rw [hφ]; simpa using hcalc
    have hwi1 : (1 : ℝ) ≤ w i := hw1 i
    have hwle : w i + 1 ≤ 2 * w i := by linarith
    have hwpos : 0 < w i := by linarith
    have hbase_le : K * (w i + 1) ^ p ≤ K * 2 ^ p * (w i) ^ p := by
      have h2 : (w i + 1) ^ p ≤ (2 * w i) ^ p :=
        Real.rpow_le_rpow (by linarith) hwle hp.le
      have h3 : (2 * w i) ^ p = 2 ^ p * (w i) ^ p :=
        Real.mul_rpow (by norm_num) hwpos.le
      calc K * (w i + 1) ^ p ≤ K * (2 * w i) ^ p :=
            mul_le_mul_of_nonneg_left h2 hK.le
        _ = K * 2 ^ p * (w i) ^ p := by rw [h3]; ring
    have hfinal : ((φ i : ℝ) + 1) ≤ K * 2 ^ p * (w i) ^ p := le_trans hstep hbase_le
    have hKp : 0 < K * 2 ^ p := by positivity
    have hpow : ((φ i : ℝ) + 1) ^ (1 / p) ≤ (K * 2 ^ p * (w i) ^ p) ^ (1 / p) :=
      Real.rpow_le_rpow (by positivity) hfinal (by positivity)
    have hrhs : (K * 2 ^ p * (w i) ^ p) ^ (1 / p) = (K * 2 ^ p) ^ (1 / p) * (w i) := by
      rw [Real.mul_rpow hKp.le (by positivity)]
      congr 1
      rw [← Real.rpow_mul hwpos.le, mul_one_div, div_self (ne_of_gt hp), Real.rpow_one]
    rw [hrhs] at hpow
    have hC : (K * 2 ^ p) ^ (-(1 / p)) * ((K * 2 ^ p) ^ (1 / p) * w i) = w i := by
      rw [← mul_assoc, ← Real.rpow_add hKp]; simp
    calc (K * 2 ^ p) ^ (-(1 / p)) * ((φ i : ℝ) + 1) ^ (1 / p)
        ≤ (K * 2 ^ p) ^ (-(1 / p)) * ((K * 2 ^ p) ^ (1 / p) * w i) :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = w i := hC

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma weylSobolevExp_eq_mercerSobolevExp :
    weylSobolevExp (E := E) = Spectral.Mercer.mercerSobolevExp (E := E) := rfl

theorem eigenProjector_card_le_sobolev (g : SmoothRiemannianMetric I M) :
    ∃ K : ℝ, 0 < K ∧ ∀ Λ : ℝ,
      (Nat.card {i : TensorEigenIdx (I := I) (M := M) g 0 2 |
        1 + TensorEigenIdx.lambda (I := I) (M := M) i < Λ} : ℝ) ≤
        K * (1 + Λ) ^ ((weylSobolevExp (E := E) : ℕ) : ℝ) :=
  Spectral.Mercer.eigenProjector_card_le_mercer (I := I) (M := M) g

theorem tensorEigen_counting_le (g : SmoothRiemannianMetric I M) :
    ∃ K : ℝ, 0 < K ∧ ∀ Λ : ℝ,
      (Nat.card {i : TensorEigenIdx (I := I) (M := M) g 0 2 |
        1 + TensorEigenIdx.lambda (I := I) (M := M) i < Λ} : ℝ) ≤
        K * Λ ^ ((weylSobolevExp (E := E) : ℕ) : ℝ) := by
  obtain ⟨K, hK, hKbound⟩ := eigenProjector_card_le_sobolev (I := I) (M := M) g
  set p : ℝ := ((weylSobolevExp (E := E) : ℕ) : ℝ) with hp_def
  have hp0 : 0 ≤ p := by positivity
  have hpow_nonneg : ∀ Λ : ℝ, 0 ≤ Λ ^ p := by
    intro Λ; rw [hp_def, Real.rpow_natCast, weylSobolevExp, pow_mul]; positivity
  refine ⟨K * 2 ^ p, by positivity, fun Λ => ?_⟩
  by_cases hΛ : 1 < Λ
  · have h1 : (1 + Λ) ^ p ≤ (2 * Λ) ^ p :=
      Real.rpow_le_rpow (by linarith) (by linarith) hp0
    have h2 : (2 * Λ) ^ p = 2 ^ p * Λ ^ p :=
      Real.mul_rpow (by norm_num) (by linarith)
    calc (Nat.card {i : TensorEigenIdx (I := I) (M := M) g 0 2 |
              1 + TensorEigenIdx.lambda (I := I) (M := M) i < Λ} : ℝ)
        ≤ K * (1 + Λ) ^ p := hKbound Λ
      _ ≤ K * (2 * Λ) ^ p := mul_le_mul_of_nonneg_left h1 hK.le
      _ = K * (2 ^ p * Λ ^ p) := by rw [h2]
      _ = K * 2 ^ p * Λ ^ p := by ring
  · have hΛ' : Λ ≤ 1 := not_lt.mp hΛ
    have hempty : {i : TensorEigenIdx (I := I) (M := M) g 0 2 |
        1 + TensorEigenIdx.lambda (I := I) (M := M) i < Λ} = ∅ := by
      ext i
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      have := tensor_lambda_nonneg (I := I) (M := M) i
      linarith
    rw [hempty, Nat.card_coe_set_eq, Set.ncard_empty, Nat.cast_zero]
    have h2p : (0 : ℝ) ≤ (2 : ℝ) ^ p := by positivity
    have := hpow_nonneg Λ
    positivity

theorem tensorEigen_one_add_lambda_growth (g : SmoothRiemannianMetric I M) :
    ∃ (φ : TensorEigenIdx (I := I) (M := M) g 0 2 → ℕ) (C : ℝ),
      Function.Injective φ ∧ 0 < C ∧
        ∀ i : TensorEigenIdx (I := I) (M := M) g 0 2,
          C * ((φ i : ℝ) + 1) ^ (1 / ((weylSobolevExp (E := E) : ℕ) : ℝ)) ≤
            1 + TensorEigenIdx.lambda (I := I) (M := M) i := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  set p : ℝ := ((weylSobolevExp (E := E) : ℕ) : ℝ) with hp_def
  have hp : 0 < p := by
    rw [hp_def]; unfold weylSobolevExp; positivity
  set w : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ :=
    fun i => 1 + TensorEigenIdx.lambda (I := I) (M := M) i with hw_def
  have hw1 : ∀ i, 1 ≤ w i := fun i => by
    rw [hw_def]; have := tensor_lambda_nonneg (I := I) (M := M) i; linarith
  have hfin : ∀ Λ : ℝ, {i | w i < Λ}.Finite := fun Λ =>
    tensorEigenIdx_one_add_lambda_lt_finite (I := I) (M := M) g 0 2 Λ
  obtain ⟨K, hK, hcount⟩ := tensorEigen_counting_le (I := I) (M := M) g
  obtain ⟨φ, C, hφ, hC, hgrow⟩ :=
    exists_growth_of_counting_bound (ι := TensorEigenIdx (I := I) (M := M) g 0 2)
      w hw1 hfin K p hK hp hcount
  refine ⟨φ, C, hφ, hC, fun i => ?_⟩
  have hi := hgrow i
  rw [hw_def] at hi
  exact hi

theorem tensorEigen_summable_negpow (g : SmoothRiemannianMetric I M) (s : ℝ)
    (hs : ((weylSobolevExp (E := E) : ℕ) : ℝ) < s) :
    Summable (fun i : TensorEigenIdx (I := I) (M := M) g 0 2 =>
      tensorSobolevWeight (I := I) (M := M) i (-s)) := by
  set p : ℝ := ((weylSobolevExp (E := E) : ℕ) : ℝ) with hp_def
  have hp : 0 < p := by
    rw [hp_def]; unfold weylSobolevExp; positivity
  obtain ⟨φ, C, hφ, hC, hgrowth⟩ :=
    tensorEigen_one_add_lambda_growth (I := I) (M := M) g
  have hlam : ∀ i : TensorEigenIdx (I := I) (M := M) g 0 2,
      0 ≤ TensorEigenIdx.lambda (I := I) (M := M) i :=
    fun i => tensor_lambda_nonneg (I := I) (M := M) i
  have h1add : ∀ i : TensorEigenIdx (I := I) (M := M) g 0 2,
      (1 : ℝ) ≤ 1 + TensorEigenIdx.lambda (I := I) (M := M) i :=
    fun i => by linarith [hlam i]
  have hbasepos : ∀ i : TensorEigenIdx (I := I) (M := M) g 0 2,
      (0 : ℝ) < C * ((φ i : ℝ) + 1) ^ (1 / p) := fun i => by
    have : (0 : ℝ) < ((φ i : ℝ) + 1) ^ (1 / p) :=
      Real.rpow_pos_of_pos (by positivity) _
    positivity
  set gnat : ℕ → ℝ := fun k => (C * ((k : ℝ) + 1) ^ (1 / p)) ^ (-s) with hgnat
  set f : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ :=
    fun i => (C * ((φ i : ℝ) + 1) ^ (1 / p)) ^ (-s) with hf
  have hfcomp : f = gnat ∘ φ := by
    funext i; simp [hf, hgnat, Function.comp]
  have hgnat_summable : Summable gnat := by
    have hrw : gnat = fun k : ℕ => C ^ (-s) * (((k : ℝ) + 1) ^ (-(s / p))) := by
      funext k
      have hkpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      change (C * ((k : ℝ) + 1) ^ (1 / p)) ^ (-s) = _
      rw [Real.mul_rpow hC.le (Real.rpow_pos_of_pos hkpos _).le,
        ← Real.rpow_mul hkpos.le]
      congr 2
      rw [div_eq_mul_inv]; ring
    rw [hrw]
    apply Summable.mul_left
    have hexp : 1 < s / p := by rw [lt_div_iff₀ hp]; linarith
    exact summable_nat_add_one_rpow_neg (s / p) hexp
  have hfsummable : Summable f := by
    rw [hfcomp]; exact hgnat_summable.comp_injective hφ
  refine Summable.of_nonneg_of_le ?_ ?_ hfsummable
  · intro i
    refine Real.rpow_nonneg (by linarith [h1add i]) _
  · intro i
    change (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (-s) ≤ f i
    rw [hf]
    exact Real.rpow_le_rpow_of_nonpos (hbasepos i) (hgrowth i) (by linarith : (-s) ≤ 0)

end TensorHeatEquation
end Parabolic
end Analysis
end DifferentialGeometry

end
