import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.PouComponentBound.CutoffChartComponentMemWkp
import DifferentialGeometry.Analysis.Sobolev.Euclidean.ChainRule.CompChainRuleK
import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.IteratedSobolevQuant
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Multiplication.MultiplyQuantK


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma tsupport_chartPushedRaw_subset_chartImage
    (α : M) {u : M → ℝ}
    (hu_supp : tsupport u ⊆ (chartAt H α).source) :
    tsupport (chartPushedRaw (I := I) (M := M) α u) ⊆
      (fun x : M => (toEuclidean (E := E)) (extChartAt I α x)) '' (tsupport u) := by
  classical
  have h_image_compact :
      IsCompact ((fun x : M => (toEuclidean (E := E)) (extChartAt I α x)) ''
        (tsupport u)) :=
    chartImage_isCompact_of_compact_in_source (I := I) (M := M) α
      (isClosed_tsupport u).isCompact hu_supp
  refine closure_minimal ?_ h_image_compact.isClosed
  intro y hy
  rw [Function.mem_support] at hy
  by_contra hy_off
  have hy_off' : y ∉ (toEuclidean (E := E)) '' ((extChartAt I α) '' (tsupport u)) := by
    intro hy_in
    apply hy_off
    obtain ⟨z, ⟨x, hx_supp, hxz⟩, hzy⟩ := hy_in
    exact ⟨x, hx_supp, by rw [← hzy, ← hxz]⟩
  by_cases hy_target : y ∈ chartTargetEuclid (I := I) (M := M) α
  · exact hy (chartPushedRaw_eq_zero_off_image_tsupport
      (I := I) (M := M) (u := u) α hy_target hy_off')
  · exact hy (chartPushedRaw_apply_of_notMem (I := I) (M := M) α u hy_target)

private lemma wkpComp_const'_pos
    {d : ℕ} {kmax : ℕ} {Ω Ω' : Set (EuclideanSpace ℝ (Fin d))}
    (Φ : SmoothDiffeoBoundedAtOrder d Ω Ω' kmax) (k : ℕ) (p : ℝ≥0∞) :
    0 < Φ.wkpComp_const' k p := by
  unfold SmoothDiffeoBoundedAtOrder.wkpComp_const'
  have h_card_pos : (0 : ℝ) <
      (Finset.range (k + 1)).sum (fun j => (Fintype.card (Fin j → Fin d) : ℝ)) := by
    have h_zero_in : (0 : ℕ) ∈ Finset.range (k + 1) :=
      Finset.mem_range.mpr (Nat.zero_lt_succ _)
    have h_at_zero : (Fintype.card (Fin 0 → Fin d) : ℝ) = 1 := by
      have h_card : Fintype.card (Fin 0 → Fin d) = 1 := by
        rw [Fintype.card_fun]; simp
      exact_mod_cast h_card
    have h_le := Finset.single_le_sum (s := Finset.range (k + 1))
      (f := fun j => (Fintype.card (Fin j → Fin d) : ℝ))
      (fun j _ => by positivity) h_zero_in
    rw [show ((fun j => (Fintype.card (Fin j → Fin d) : ℝ)) 0 : ℝ) =
        (Fintype.card (Fin 0 → Fin d) : ℝ) from rfl] at h_le
    rw [h_at_zero] at h_le
    linarith
  have h_fact_pos : (0 : ℝ) < (k.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos k
  have h_deriv_pos : (0 : ℝ) < Φ.derivBoundMaxOne ^ k :=
    pow_pos Φ.derivBoundMaxOne_pos k
  have h_jac_pos : 0 < Φ.jacobian_lower_bound := Φ.jacobian_lower_bound_pos
  have h_rpow_pos : (0 : ℝ) < (1 / Φ.jacobian_lower_bound) ^ (1 / p.toReal) :=
    Real.rpow_pos_of_pos (by positivity) _
  have h_k1_pos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.zero_lt_succ k
  positivity

private lemma wkpComp_const'_nonneg
    {d : ℕ} {kmax : ℕ} {Ω Ω' : Set (EuclideanSpace ℝ (Fin d))}
    (Φ : SmoothDiffeoBoundedAtOrder d Ω Ω' kmax) (k : ℕ) (p : ℝ≥0∞) :
    0 ≤ Φ.wkpComp_const' k p :=
  (wkpComp_const'_pos Φ k p).le

private lemma wkpNorm_comp_smoothDiffeoBoundedAtOrder_le
    {d : ℕ} [NeZero d] {kmax : ℕ} (k : ℕ) (hk : k ≤ kmax)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ (⊤ : ℝ≥0∞))
    {Ω Ω' : Set (EuclideanSpace ℝ (Fin d))}
    (hΩ : IsOpen Ω) (hΩ' : IsOpen Ω')
    (Φ : SmoothDiffeoBoundedAtOrder d Ω Ω' kmax)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : MemWkp (d := d) k p u Ω')
    (hu_compactSupport : HasCompactSupport u) (hu_supp : tsupport u ⊆ Ω') :
    iteratedWeakSobolevNorm (d := d) k p (fun x => u (Φ.toFun x)) Ω ≤
      ENNReal.ofReal (Φ.wkpComp_const' k p) * iteratedWeakSobolevNorm (d := d) k p u Ω' := by
  classical
  set K_const : ℝ := Φ.wkpComp_const' k p with hK_def
  have hK_pos : 0 < K_const := wkpComp_const'_pos Φ k p
  have hK_nonneg : 0 ≤ K_const := hK_pos.le
  have h_approx : ∀ n : ℕ, ∃ ψ : EuclideanSpace ℝ (Fin d) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ Ω' ∧
      iteratedWeakSobolevNorm (d := d) k p (fun x => u x - ψ x) Ω' ≤
        ENNReal.ofReal ((1 : ℝ) / (n + 1 : ℝ)) := by
    intro n
    have h_pos : 0 < (1 : ℝ) / (n + 1 : ℝ) := by positivity
    exact MemWkp.exists_smooth_compactSupport_approx
      (d := d) hΩ' k p hp_one hp_top hu hu_compactSupport hu_supp _ h_pos
  let ψ : ℕ → EuclideanSpace ℝ (Fin d) → ℝ := fun n => (h_approx n).choose
  have hψ_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (ψ n) := fun n =>
    (h_approx n).choose_spec.1
  have hψ_cpt : ∀ n, HasCompactSupport (ψ n) := fun n =>
    (h_approx n).choose_spec.2.1
  have hψ_supp : ∀ n, tsupport (ψ n) ⊆ Ω' := fun n =>
    (h_approx n).choose_spec.2.2.1
  have hψ_close : ∀ n,
      iteratedWeakSobolevNorm (d := d) k p (fun x => u x - ψ n x) Ω' ≤
        ENNReal.ofReal ((1 : ℝ) / (n + 1 : ℝ)) := fun n =>
    (h_approx n).choose_spec.2.2.2
  have hψ_mem_target : ∀ n, MemWkp (d := d) k p (ψ n) Ω' := fun n =>
    MemWkp_of_smooth_compactSupport
      (d := d) hΩ' (hψ_smooth n) (hψ_cpt n) (hψ_supp n) hp_one k
  have hψ_comp_mem : ∀ n, MemWkp (d := d) k p (fun x => ψ n (Φ.toFun x)) Ω :=
    fun n =>
      MemWkp.comp_smoothDiffeoBoundedAtOrder (d := d) k hk hp_one hp_top hΩ hΩ'
        Φ (hψ_mem_target n) (hψ_cpt n) (hψ_supp n)
  have h_cauchy : ∀ ε > 0, ∃ N : ℕ, ∀ m n, N ≤ m → N ≤ n →
      iteratedWeakSobolevNorm (d := d) k p
        (fun x => (ψ m (Φ.toFun x)) - (ψ n (Φ.toFun x))) Ω ≤
        ENNReal.ofReal ε := by
    intro ε hε
    have hε_K_pos : 0 < ε / (2 * K_const) := by positivity
    obtain ⟨N0, hN0_real⟩ := exists_nat_gt (1 / (ε / (2 * K_const)) - 1)
    have hN1_pos : (0 : ℝ) < (N0 : ℝ) + 1 := by
      have : 0 < 1 / (ε / (2 * K_const)) := by positivity
      linarith
    have hN0_inv : (1 : ℝ) / (N0 + 1 : ℝ) ≤ ε / (2 * K_const) := by
      rw [div_le_iff₀ hN1_pos]
      have h1 : (1 : ℝ) = (ε / (2 * K_const)) * (1 / (ε / (2 * K_const))) := by
        rw [mul_one_div, div_self hε_K_pos.ne']
      rw [h1]
      apply mul_le_mul_of_nonneg_left _ hε_K_pos.le
      linarith
    refine ⟨N0, ?_⟩
    intro m n hm hn
    let δ : EuclideanSpace ℝ (Fin d) → ℝ := fun x => ψ m x - ψ n x
    have hδ_smooth : ContDiff ℝ (⊤ : ℕ∞) δ := (hψ_smooth m).sub (hψ_smooth n)
    have hδ_cpt : HasCompactSupport δ := (hψ_cpt m).sub (hψ_cpt n)
    have hδ_supp : tsupport δ ⊆ Ω' := by
      have h_supp_sub : Function.support δ ⊆
          Function.support (ψ m) ∪ Function.support (ψ n) := by
        intro x hx
        by_cases hxm : x ∈ Function.support (ψ m)
        · exact Or.inl hxm
        · right
          change ψ n x ≠ 0
          intro hxn
          apply hx
          change ψ m x - ψ n x = 0
          rw [Function.notMem_support.mp hxm, hxn, sub_zero]
      have h_tsupp_sub : tsupport δ ⊆ tsupport (ψ m) ∪ tsupport (ψ n) := by
        unfold tsupport
        refine (closure_mono h_supp_sub).trans ?_
        rw [closure_union]
      exact h_tsupp_sub.trans (Set.union_subset (hψ_supp m) (hψ_supp n))
    have hS1 := Φ.wkpNorm_comp_smooth_le hp_one hp_top hΩ hΩ'
      k hk hδ_smooth hδ_cpt hδ_supp
    have h_δ_alg : δ = (fun x => (u x - ψ n x) - (u x - ψ m x)) := by
      funext x
      change ψ m x - ψ n x = u x - ψ n x - (u x - ψ m x)
      ring
    have h_uψn_mem : MemWkp (d := d) k p (fun x => u x - ψ n x) Ω' :=
      MemWkp.sub (d := d) hp_one hΩ' hu (hψ_mem_target n)
    have h_uψm_mem : MemWkp (d := d) k p (fun x => u x - ψ m x) Ω' :=
      MemWkp.sub (d := d) hp_one hΩ' hu (hψ_mem_target m)
    have h_δ_wkp_le :
        iteratedWeakSobolevNorm (d := d) k p δ Ω' ≤
          iteratedWeakSobolevNorm (d := d) k p (fun x => u x - ψ n x) Ω' +
            iteratedWeakSobolevNorm (d := d) k p (fun x => u x - ψ m x) Ω' := by
      rw [h_δ_alg]
      have hneg : MemWkp (d := d) k p (fun x => -(u x - ψ m x)) Ω' :=
        MemWkp.neg (d := d) hp_one hΩ' h_uψm_mem
      have h_eq :
          (fun x => u x - ψ n x - (u x - ψ m x)) =
            (fun x => (u x - ψ n x) + (-(u x - ψ m x))) := by
        funext x; ring
      rw [h_eq]
      have h_add := wkpNorm_add_le (d := d) hp_one hΩ' h_uψn_mem hneg
      refine h_add.trans ?_
      have h_neg_eq :
          iteratedWeakSobolevNorm (d := d) k p (fun x => -(u x - ψ m x)) Ω' =
            iteratedWeakSobolevNorm (d := d) k p (fun x => u x - ψ m x) Ω' := by
        have h_eq_smul : (fun x => -(u x - ψ m x)) =
            (fun x => (-1 : ℝ) * (u x - ψ m x)) := by funext x; ring
        rw [h_eq_smul, wkpNorm_const_smul (d := d) hp_one hΩ' h_uψm_mem (-1)]
        simp
      rw [h_neg_eq]
    have hψm_close := hψ_close m
    have hψn_close := hψ_close n
    have h_n_le : ENNReal.ofReal ((1 : ℝ) / (n + 1 : ℝ)) ≤
        ENNReal.ofReal ((1 : ℝ) / (N0 + 1 : ℝ)) := by
      refine ENNReal.ofReal_le_ofReal ?_
      apply div_le_div_of_nonneg_left zero_le_one hN1_pos
      have hN0n : (N0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    have h_m_le : ENNReal.ofReal ((1 : ℝ) / (m + 1 : ℝ)) ≤
        ENNReal.ofReal ((1 : ℝ) / (N0 + 1 : ℝ)) := by
      refine ENNReal.ofReal_le_ofReal ?_
      apply div_le_div_of_nonneg_left zero_le_one hN1_pos
      have hN0m : (N0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      linarith
    have h_δ_le_2N0 :
        iteratedWeakSobolevNorm (d := d) k p δ Ω' ≤
          ENNReal.ofReal (2 * ((1 : ℝ) / (N0 + 1 : ℝ))) := by
      refine h_δ_wkp_le.trans ?_
      refine (add_le_add hψn_close hψm_close).trans ?_
      refine (add_le_add h_n_le h_m_le).trans ?_
      have h2 : (2 * ((1 : ℝ) / (N0 + 1 : ℝ))) =
          ((1 : ℝ) / (N0 + 1 : ℝ)) + ((1 : ℝ) / (N0 + 1 : ℝ)) := by ring
      rw [h2]
      have h_pos : 0 ≤ (1 : ℝ) / (N0 + 1 : ℝ) := by positivity
      rw [ENNReal.ofReal_add h_pos h_pos]
    have h_δcomp_eq : (fun x => δ (Φ.toFun x)) =
        (fun x => ψ m (Φ.toFun x) - ψ n (Φ.toFun x)) := by
      funext x; rfl
    rw [h_δcomp_eq] at hS1
    refine hS1.trans ?_
    refine (mul_le_mul_of_nonneg_left h_δ_le_2N0 (zero_le _)).trans ?_
    rw [← ENNReal.ofReal_mul hK_nonneg]
    refine ENNReal.ofReal_le_ofReal ?_
    calc K_const * (2 * ((1 : ℝ) / (N0 + 1 : ℝ)))
        = (2 * K_const) * ((1 : ℝ) / (N0 + 1 : ℝ)) := by ring
      _ ≤ (2 * K_const) * (ε / (2 * K_const)) := by
            apply mul_le_mul_of_nonneg_left hN0_inv
            positivity
      _ = ε := by
            have h_pos : 0 < 2 * K_const := by positivity
            field_simp
  obtain ⟨v, hv_mem, hv_tendsto⟩ :=
    MemWkp.exists_limit_of_wkpNorm_cauchy (d := d) hΩ k p hp_one hp_top
      hψ_comp_mem h_cauchy
  have h_Lp_close : ∀ n,
      eLpNorm (fun x => u (Φ.toFun x) - ψ n (Φ.toFun x)) p
        (volume.restrict Ω) ≤
        ENNReal.ofReal
            ((1 / Φ.jacobian_lower_bound) ^ (1 / p.toReal)) *
          ENNReal.ofReal ((1 : ℝ) / (n + 1 : ℝ)) := by
    intro n
    have h_chg := Φ.eLpNorm_comp_toFun_le_const hp_one hp_top hΩ
      (fun x => u x - ψ n x)
    have h_uψn_mem : MemWkp (d := d) k p (fun x => u x - ψ n x) Ω' :=
      MemWkp.sub (d := d) hp_one hΩ' hu (hψ_mem_target n)
    have h_eLp_le_wkp :
        eLpNorm (fun x => u x - ψ n x) p (volume.restrict Ω') ≤
          iteratedWeakSobolevNorm (d := d) k p (fun x => u x - ψ n x) Ω' := by
      have h_zero_le :
          eLpNorm (fun x => u x - ψ n x) p (volume.restrict Ω') =
            iteratedWeakSobolevNorm (d := d) 0 p (fun x => u x - ψ n x) Ω' := by
        rw [wkpNorm_zero]
      rw [h_zero_le]
      unfold iteratedWeakSobolevNorm
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro j hj
        rw [Finset.mem_range] at hj ⊢; omega
      · intros _ _ _; exact zero_le _
    have h_arg_eq : (fun x => u (Φ.toFun x) - ψ n (Φ.toFun x)) =
        (fun x => (fun y => u y - ψ n y) (Φ.toFun x)) := by funext x; rfl
    rw [h_arg_eq]
    refine h_chg.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (zero_le _)
    exact h_eLp_le_wkp.trans (hψ_close n)
  have h_uΦ_aestrong :
      AEStronglyMeasurable (fun x => u (Φ.toFun x)) (volume.restrict Ω) := by
    have hu_aestrong : AEStronglyMeasurable u (volume.restrict Ω') :=
      hu.memLp.aestronglyMeasurable
    exact hu_aestrong.comp_quasiMeasurePreserving Φ.toFun_quasiMeasurePreserving
  have h_v_eq_uΦ : v =ᵐ[volume.restrict Ω] (fun x => u (Φ.toFun x)) := by
    have h_v_aestrong : AEStronglyMeasurable v (volume.restrict Ω) :=
      hv_mem.memLp.aestronglyMeasurable
    have hp_zero_ne : p ≠ 0 := by
      intro hpz; rw [hpz] at hp_one
      exact absurd hp_one (by norm_num)
    have h_zero :
        eLpNorm (fun x => v x - u (Φ.toFun x)) p (volume.restrict Ω) = 0 := by
      have h_bound : ∀ n,
          eLpNorm (fun x => v x - u (Φ.toFun x)) p (volume.restrict Ω) ≤
            iteratedWeakSobolevNorm (d := d) k p (fun x => v x - ψ n (Φ.toFun x)) Ω +
            ENNReal.ofReal
                ((1 / Φ.jacobian_lower_bound) ^ (1 / p.toReal)) *
              ENNReal.ofReal ((1 : ℝ) / (n + 1 : ℝ)) := by
        intro n
        have h_ψn_comp_aestrong : AEStronglyMeasurable
            (fun x => ψ n (Φ.toFun x)) (volume.restrict Ω) :=
          (hψ_smooth n).continuous.aestronglyMeasurable.comp_quasiMeasurePreserving
            Φ.toFun_quasiMeasurePreserving
        have h_decomp :
            (fun x => v x - u (Φ.toFun x)) = (fun x =>
              (v x - ψ n (Φ.toFun x)) + (ψ n (Φ.toFun x) - u (Φ.toFun x))) := by
          funext x; ring
        rw [h_decomp]
        have h_tri := eLpNorm_add_le (μ := volume.restrict Ω)
          (h_v_aestrong.sub h_ψn_comp_aestrong)
          (h_ψn_comp_aestrong.sub h_uΦ_aestrong) hp_one
        refine h_tri.trans ?_
        have h_first :
            eLpNorm (fun x => v x - ψ n (Φ.toFun x)) p (volume.restrict Ω) ≤
              iteratedWeakSobolevNorm (d := d) k p (fun x => v x - ψ n (Φ.toFun x)) Ω := by
          rw [show eLpNorm (fun x => v x - ψ n (Φ.toFun x)) p (volume.restrict Ω) =
            iteratedWeakSobolevNorm (d := d) 0 p (fun x => v x - ψ n (Φ.toFun x)) Ω from
            (wkpNorm_zero p _ _).symm]
          unfold iteratedWeakSobolevNorm
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
          · intro j hj; rw [Finset.mem_range] at hj ⊢; omega
          · intros _ _ _; exact zero_le _
        have h_second :
            eLpNorm (fun x => ψ n (Φ.toFun x) - u (Φ.toFun x)) p
                (volume.restrict Ω) ≤
              ENNReal.ofReal
                  ((1 / Φ.jacobian_lower_bound) ^ (1 / p.toReal)) *
                ENNReal.ofReal ((1 : ℝ) / (n + 1 : ℝ)) := by
          have h_eq :
              (fun x => ψ n (Φ.toFun x) - u (Φ.toFun x)) =
                (fun x => -(u (Φ.toFun x) - ψ n (Φ.toFun x))) := by
            funext x; ring
          rw [h_eq]
          have h_neg :
              eLpNorm (fun x => -(u (Φ.toFun x) - ψ n (Φ.toFun x))) p
                  (volume.restrict Ω) =
                eLpNorm (fun x => u (Φ.toFun x) - ψ n (Φ.toFun x)) p
                  (volume.restrict Ω) := by
            rw [show (fun x => -(u (Φ.toFun x) - ψ n (Φ.toFun x))) =
                fun x => -1 * (u (Φ.toFun x) - ψ n (Φ.toFun x)) from by
              funext x; ring]
            rw [show (fun x => -1 * (u (Φ.toFun x) - ψ n (Φ.toFun x))) =
                ((-1 : ℝ) • fun x => u (Φ.toFun x) - ψ n (Φ.toFun x)) from by
              funext x; simp [Pi.smul_apply, smul_eq_mul]]
            rw [eLpNorm_const_smul]
            simp
          rw [h_neg]
          exact h_Lp_close n
        exact add_le_add h_first h_second
      apply le_antisymm _ (zero_le _)
      have h_tendsto_first :
          Filter.Tendsto
            (fun n => iteratedWeakSobolevNorm (d := d) k p (fun x => v x - ψ n (Φ.toFun x)) Ω)
            atTop (𝓝 0) := by
        have h_eq : ∀ n, (fun x => v x - ψ n (Φ.toFun x)) =
            (fun x => -(ψ n (Φ.toFun x) - v x)) := by
          intro n; funext x; ring
        have h_norm_eq : ∀ n,
            iteratedWeakSobolevNorm (d := d) k p (fun x => v x - ψ n (Φ.toFun x)) Ω =
              iteratedWeakSobolevNorm (d := d) k p (fun x => ψ n (Φ.toFun x) - v x) Ω := by
          intro n
          rw [h_eq n]
          have hf_mem : MemWkp (d := d) k p
              (fun x => ψ n (Φ.toFun x) - v x) Ω :=
            MemWkp.sub (d := d) hp_one hΩ (hψ_comp_mem n) hv_mem
          rw [show (fun x => -(ψ n (Φ.toFun x) - v x)) =
              (fun x => (-1 : ℝ) * (ψ n (Φ.toFun x) - v x)) from by
            funext x; ring]
          rw [wkpNorm_const_smul (d := d) hp_one hΩ hf_mem (-1)]
          simp
        rw [show (fun n => iteratedWeakSobolevNorm (d := d) k p
              (fun x => v x - ψ n (Φ.toFun x)) Ω) =
            (fun n => iteratedWeakSobolevNorm (d := d) k p
              (fun x => ψ n (Φ.toFun x) - v x) Ω) from funext h_norm_eq]
        exact hv_tendsto
      have h_tendsto_second :
          Filter.Tendsto
            (fun n : ℕ => ENNReal.ofReal
                ((1 / Φ.jacobian_lower_bound) ^ (1 / p.toReal)) *
              ENNReal.ofReal ((1 : ℝ) / (n + 1 : ℝ)))
            atTop (𝓝 0) := by
        have h_inner_tendsto :
            Filter.Tendsto
              (fun n : ℕ => ENNReal.ofReal ((1 : ℝ) / (n + 1 : ℝ)))
              atTop (𝓝 0) := by
          have h_real : Filter.Tendsto
              (fun n : ℕ => (1 : ℝ) / (n + 1 : ℝ)) atTop (𝓝 0) :=
            tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
          have h_ofReal := (ENNReal.continuous_ofReal.tendsto 0).comp h_real
          simpa [ENNReal.ofReal_zero] using h_ofReal
        set C : ℝ≥0∞ := ENNReal.ofReal
            ((1 / Φ.jacobian_lower_bound) ^ (1 / p.toReal)) with hC_def
        have hC_ne_top : C ≠ ⊤ := by rw [hC_def]; exact ENNReal.ofReal_ne_top
        have h_const_mul := ENNReal.Tendsto.const_mul (a := C) (b := 0)
          h_inner_tendsto (Or.inr hC_ne_top)
        simpa using h_const_mul
      have h_tendsto_sum :
          Filter.Tendsto
            (fun n => iteratedWeakSobolevNorm (d := d) k p (fun x => v x - ψ n (Φ.toFun x)) Ω +
              ENNReal.ofReal
                  ((1 / Φ.jacobian_lower_bound) ^ (1 / p.toReal)) *
                ENNReal.ofReal ((1 : ℝ) / (n + 1 : ℝ)))
            atTop (𝓝 0) := by
        have := h_tendsto_first.add h_tendsto_second
        simpa using this
      exact ge_of_tendsto h_tendsto_sum (Filter.Eventually.of_forall h_bound)
    have h_diff_zero : (fun x => v x - u (Φ.toFun x)) =ᵐ[volume.restrict Ω]
        0 := by
      have h_aestrong := h_v_aestrong.sub h_uΦ_aestrong
      exact (eLpNorm_eq_zero_iff h_aestrong hp_zero_ne).mp h_zero
    filter_upwards [h_diff_zero] with x hx
    have : v x - u (Φ.toFun x) = 0 := hx
    linarith
  have h_norm_uΦ_eq_v :
      iteratedWeakSobolevNorm (d := d) k p (fun x => u (Φ.toFun x)) Ω =
        iteratedWeakSobolevNorm (d := d) k p v Ω :=
    (wkpNorm_congr_ae (d := d) hp_one hΩ h_v_eq_uΦ).symm
  rw [h_norm_uΦ_eq_v]
  have h_smooth_bound : ∀ n,
      iteratedWeakSobolevNorm (d := d) k p (fun x => ψ n (Φ.toFun x)) Ω ≤
        ENNReal.ofReal K_const *
          (iteratedWeakSobolevNorm (d := d) k p (fun x => u x - ψ n x) Ω' +
            iteratedWeakSobolevNorm (d := d) k p u Ω') := by
    intro n
    have h_smooth := Φ.wkpNorm_comp_smooth_le hp_one hp_top hΩ hΩ'
      k hk (hψ_smooth n) (hψ_cpt n) (hψ_supp n)
    refine h_smooth.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (zero_le _)
    have hψn_alg : (ψ n) = (fun x => (ψ n x - u x) + u x) := by funext x; ring
    have h_sub_mem : MemWkp (d := d) k p (fun x => ψ n x - u x) Ω' :=
      MemWkp.sub (d := d) hp_one hΩ' (hψ_mem_target n) hu
    have h_uψn_mem : MemWkp (d := d) k p (fun x => u x - ψ n x) Ω' :=
      MemWkp.sub (d := d) hp_one hΩ' hu (hψ_mem_target n)
    have h_tri := wkpNorm_add_le (d := d) hp_one hΩ' h_sub_mem hu
    rw [← hψn_alg] at h_tri
    refine h_tri.trans ?_
    refine add_le_add ?_ (le_refl _)
    have h_neg_eq :
        iteratedWeakSobolevNorm (d := d) k p (fun x => ψ n x - u x) Ω' =
          iteratedWeakSobolevNorm (d := d) k p (fun x => u x - ψ n x) Ω' := by
      have h_eq_smul : (fun x => ψ n x - u x) =
          (fun x => (-1 : ℝ) * (u x - ψ n x)) := by funext x; ring
      rw [h_eq_smul, wkpNorm_const_smul (d := d) hp_one hΩ' h_uψn_mem (-1)]
      simp
    rw [h_neg_eq]
  have h_v_bound : ∀ n,
      iteratedWeakSobolevNorm (d := d) k p v Ω ≤
        iteratedWeakSobolevNorm (d := d) k p (fun x => v x - ψ n (Φ.toFun x)) Ω +
          ENNReal.ofReal K_const *
            (iteratedWeakSobolevNorm (d := d) k p (fun x => u x - ψ n x) Ω' +
              iteratedWeakSobolevNorm (d := d) k p u Ω') := by
    intro n
    have hv_alg : v = (fun x => (v x - ψ n (Φ.toFun x)) + ψ n (Φ.toFun x)) := by
      funext x; ring
    have h_sub_mem : MemWkp (d := d) k p
        (fun x => v x - ψ n (Φ.toFun x)) Ω :=
      MemWkp.sub (d := d) hp_one hΩ hv_mem (hψ_comp_mem n)
    have h_tri := wkpNorm_add_le (d := d) hp_one hΩ h_sub_mem (hψ_comp_mem n)
    rw [← hv_alg] at h_tri
    exact h_tri.trans (add_le_add (le_refl _) (h_smooth_bound n))
  have h_rhs_tendsto :
      Filter.Tendsto
        (fun n => iteratedWeakSobolevNorm (d := d) k p (fun x => v x - ψ n (Φ.toFun x)) Ω +
          ENNReal.ofReal K_const *
            (iteratedWeakSobolevNorm (d := d) k p (fun x => u x - ψ n x) Ω' +
              iteratedWeakSobolevNorm (d := d) k p u Ω'))
        atTop (𝓝 (ENNReal.ofReal K_const * iteratedWeakSobolevNorm (d := d) k p u Ω')) := by
    have h_first_tendsto :
        Filter.Tendsto
          (fun n => iteratedWeakSobolevNorm (d := d) k p (fun x => v x - ψ n (Φ.toFun x)) Ω)
          atTop (𝓝 0) := by
      have h_eq : ∀ n, (fun x => v x - ψ n (Φ.toFun x)) =
          (fun x => -(ψ n (Φ.toFun x) - v x)) := by
        intro n; funext x; ring
      have h_norm_eq : ∀ n,
          iteratedWeakSobolevNorm (d := d) k p (fun x => v x - ψ n (Φ.toFun x)) Ω =
            iteratedWeakSobolevNorm (d := d) k p (fun x => ψ n (Φ.toFun x) - v x) Ω := by
        intro n
        rw [h_eq n]
        have hf_mem : MemWkp (d := d) k p
            (fun x => ψ n (Φ.toFun x) - v x) Ω :=
          MemWkp.sub (d := d) hp_one hΩ (hψ_comp_mem n) hv_mem
        rw [show (fun x => -(ψ n (Φ.toFun x) - v x)) =
            (fun x => (-1 : ℝ) * (ψ n (Φ.toFun x) - v x)) from by
          funext x; ring]
        rw [wkpNorm_const_smul (d := d) hp_one hΩ hf_mem (-1)]
        simp
      rw [show (fun n => iteratedWeakSobolevNorm (d := d) k p
            (fun x => v x - ψ n (Φ.toFun x)) Ω) =
          (fun n => iteratedWeakSobolevNorm (d := d) k p
            (fun x => ψ n (Φ.toFun x) - v x) Ω) from funext h_norm_eq]
      exact hv_tendsto
    have h_inner_tendsto :
        Filter.Tendsto
          (fun n => iteratedWeakSobolevNorm (d := d) k p (fun x => u x - ψ n x) Ω' +
            iteratedWeakSobolevNorm (d := d) k p u Ω')
          atTop (𝓝 (iteratedWeakSobolevNorm (d := d) k p u Ω')) := by
      have h_first :
          Filter.Tendsto
            (fun n => iteratedWeakSobolevNorm (d := d) k p (fun x => u x - ψ n x) Ω')
            atTop (𝓝 0) := by
        have h_close_tendsto :
            Filter.Tendsto
              (fun n : ℕ => ENNReal.ofReal ((1 : ℝ) / (n + 1 : ℝ)))
              atTop (𝓝 0) := by
          have h_real : Filter.Tendsto
              (fun n : ℕ => (1 : ℝ) / (n + 1 : ℝ)) atTop (𝓝 0) :=
            tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
          have h_ofReal := (ENNReal.continuous_ofReal.tendsto 0).comp h_real
          simpa [ENNReal.ofReal_zero] using h_ofReal
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le
          tendsto_const_nhds h_close_tendsto
          (fun n => zero_le _) (fun n => hψ_close n)
      have h_const :
          Filter.Tendsto
            (fun _ : ℕ => iteratedWeakSobolevNorm (d := d) k p u Ω')
            atTop (𝓝 (iteratedWeakSobolevNorm (d := d) k p u Ω')) := tendsto_const_nhds
      have h_add := h_first.add h_const
      simpa using h_add
    have h_const_ne_top : ENNReal.ofReal K_const ≠ ⊤ := ENNReal.ofReal_ne_top
    have h_prod_tendsto :
        Filter.Tendsto
          (fun n => ENNReal.ofReal K_const *
            (iteratedWeakSobolevNorm (d := d) k p (fun x => u x - ψ n x) Ω' +
              iteratedWeakSobolevNorm (d := d) k p u Ω'))
          atTop (𝓝 (ENNReal.ofReal K_const * iteratedWeakSobolevNorm (d := d) k p u Ω')) :=
      ENNReal.Tendsto.const_mul h_inner_tendsto (Or.inr h_const_ne_top)
    have h_sum := h_first_tendsto.add h_prod_tendsto
    simpa using h_sum
  exact ge_of_tendsto h_rhs_tendsto (Filter.Eventually.of_forall h_v_bound)

omit [CompleteSpace E] in
private lemma wkpNorm_chartTransitionTransportCLM_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (β α : M)
    (P₀ Q : TensorCompIdx (E := E) r s) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)),
      MemWkp (d := Module.finrank ℝ E) k 2
        (fun y => (f : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β) →
      MemWkp (d := Module.finrank ℝ E) k 2
        (fun y => ((chartTransitionTransportCLM (I := I) (M := M) g r s β α P₀ Q f :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) α) ∧
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) k 2
        (fun y => ((chartTransitionTransportCLM (I := I) (M := M) g r s β α P₀ Q f :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) α) ≤
      ENNReal.ofReal C *
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) k 2
          (fun y => (f : EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) β) := by
  classical
  set d : ℕ := Module.finrank ℝ E with hd_def
  set cM : M → ℝ := transportCoeffManifold (I := I) (M := M) g r s β α P₀ Q
    with hcM_def
  set cE : EuclN → ℝ := chartPushedRaw (I := I) (M := M) α cM with hcE_def
  set Tα : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hTα_def
  set Tβ : Set EuclN := chartTargetEuclid (I := I) (M := M) β with hTβ_def
  have hTα_open : IsOpen Tα := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hTβ_open : IsOpen Tβ := chartTargetEuclid_isOpen (I := I) (M := M) β
  have hcM_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ cM :=
    contMDiff_transportCoeffManifold (I := I) (M := M) g r s β α P₀ Q
  have hcM_supp_α : tsupport cM ⊆ (chartAt H α).source :=
    tsupport_transportCoeffManifold_subset_sourceα (I := I) (M := M) g r s β α P₀ Q
  have hcM_supp_β : tsupport cM ⊆ (chartAt H β).source :=
    tsupport_transportCoeffManifold_subset_sourceβ (I := I) (M := M) g r s β α P₀ Q
  set Kc : Set M := tsupport cM with hKc_def
  have hKc_compact : IsCompact Kc := (isClosed_tsupport cM).isCompact
  have hKc_in_α : Kc ⊆ (chartAt H α).source := hcM_supp_α
  have hKc_in_β : Kc ⊆ (chartAt H β).source := hcM_supp_β
  have hcE_smooth : ContDiff ℝ ∞ cE :=
    DifferentialGeometry.Analysis.Laplacian.SmoothFChartResidualBilinearBound.chartPushedRaw_contDiff
      (I := I) (M := M) hcM_smooth hcM_supp_α
  have hcE_smooth' : ContDiff ℝ (⊤ : ℕ∞) cE := hcE_smooth
  have hcE_cpt : HasCompactSupport cE :=
    DifferentialGeometry.Analysis.Laplacian.SmoothFChartResidualBilinearBound.chartPushedRaw_smooth_hasCompactSupport_local
      (I := I) (M := M) hcM_supp_α
  obtain ⟨Ccoeff, hCcoeff_nn, hCcoeff_bound⟩ :=
    exists_uniform_iteratedFDeriv_bound_of_smooth_compactSupport
      (d := d) hcE_smooth' hcE_cpt k
  have hcE_tsupp_subset :
      tsupport cE ⊆ (fun x : M => (toEuclidean (E := E)) (extChartAt I α x)) '' Kc :=
    tsupport_chartPushedRaw_subset_chartImage (I := I) (M := M) α hcM_supp_α
  obtain ⟨Ωαβ, Ωβα, hΩαβ_open, hΩβα_open, hΩαβ_subset_target,
    hΩβα_subset_target, _hΩαβ_overlap, _hΩβα_overlap, hKc_image_in_Ωαβ, Φ,
    hΦ_eq, _hΦ_inv_eq⟩ :=
    chartTransition_smoothDiffeoBoundedAtOrder_strict (I := I) (M := M)
      α β hKc_compact hKc_in_α hKc_in_β k
  set KEα : Set EuclN :=
    (fun x : M => (toEuclidean (E := E)) (extChartAt I α x)) '' Kc with hKEα_def
  have hKEα_compact : IsCompact KEα :=
    chartImage_isCompact_of_compact_in_source (I := I) (M := M) α hKc_compact hKc_in_α
  have hKEα_in_Ωαβ : KEα ⊆ Ωαβ := hKc_image_in_Ωαβ
  have hcE_tsupp_Ωαβ : tsupport cE ⊆ Ωαβ := hcE_tsupp_subset.trans hKEα_in_Ωαβ
  set KEβ : Set EuclN := Φ.toFun '' KEα with hKEβ_def
  have hKEβ_compact : IsCompact KEβ :=
    hKEα_compact.image Φ.continuous_toFun
  have hKEβ_in_Ωβα : KEβ ⊆ Ωβα := by
    intro z hz
    obtain ⟨y, hy, hyz⟩ := hz
    have hy_Ωαβ : y ∈ Ωαβ := hKEα_in_Ωαβ hy
    rw [← hyz]
    exact Φ.bijOn.mapsTo hy_Ωαβ
  set Uβ : Set EuclN := Ωβα ∩ Tβ with hUβ_def
  have hUβ_open : IsOpen Uβ := hΩβα_open.inter hTβ_open
  have hKEβ_in_Uβ : KEβ ⊆ Uβ :=
    Set.subset_inter hKEβ_in_Ωβα (hKEβ_in_Ωβα.trans hΩβα_subset_target)
  obtain ⟨δ, χ, _hδ_pos, _hδ_subset, hχ_smooth, hχ_cpt, _hχ_range,
    hχ_one, hχ_supp⟩ :=
    exists_smooth_cutoff_with_neighborhood (d := d) hKEβ_compact hUβ_open hKEβ_in_Uβ
  have hχ_supp_Ωβα : tsupport χ ⊆ Ωβα := fun y hy => (hχ_supp hy).1
  have hχ_supp_Tβ : tsupport χ ⊆ Tβ := fun y hy => (hχ_supp hy).2
  obtain ⟨Cχ, hCχ_nn, hCχ_bound⟩ :=
    exists_uniform_iteratedFDeriv_bound_of_smooth_compactSupport
      (d := d) (hχ_smooth : ContDiff ℝ (⊤ : ℕ∞) χ) hχ_cpt k
  obtain ⟨Kχ, hKχ_pos, hKχ_bound⟩ :=
    wkpNorm_smul_smooth_bounded_le (d := d) k (p := (2 : ℝ≥0∞))
      (by norm_num) (by norm_num)
      hTβ_open (hχ_smooth : ContDiff ℝ (⊤ : ℕ∞) χ) hCχ_nn
      (fun j hj y _ => hCχ_bound y j hj)
  obtain ⟨Kc', hKc'_pos, hKc'_bound⟩ :=
    wkpNorm_smul_smooth_bounded_le (d := d) k (p := (2 : ℝ≥0∞))
      (by norm_num) (by norm_num)
      hΩαβ_open hcE_smooth' hCcoeff_nn
      (fun j hj y _ => hCcoeff_bound y j hj)
  set Kcomp : ℝ := Φ.wkpComp_const' k 2 with hKcomp_def
  have hKcomp_nn : 0 ≤ Kcomp := wkpComp_const'_nonneg Φ k 2
  refine ⟨Kc' * (Kcomp * Kχ), by positivity, ?_⟩
  intro f hf
  set T : EuclN → ℝ := fun y => (f : EuclN → ℝ) y with hT_def
  set v : EuclN → ℝ := fun y => χ y * T y with hv_def
  have hv_supp_χ : tsupport v ⊆ tsupport χ :=
    tsupport_smul_subset_left χ T
  have hv_supp_Ωβα : tsupport v ⊆ Ωβα := hv_supp_χ.trans hχ_supp_Ωβα
  have hv_cpt : HasCompactSupport v := hχ_cpt.mul_right
  have hv_memWkp_Tβ : MemWkp (d := d) k 2 v Tβ :=
    MemWkp.smul_smooth_bounded (d := d) k (by norm_num) hTβ_open
      (hχ_smooth : ContDiff ℝ (⊤ : ℕ∞) χ)
      (fun j hj y _ => hCχ_bound y j hj) hf
  have hv_memWkp_Ωβα : MemWkp (d := d) k 2 v Ωβα :=
    MemWkp.mono_set (d := d) (by norm_num) hTβ_open hΩβα_open
      hΩβα_subset_target hv_memWkp_Tβ
  have hv_comp_memWkp_Ωαβ : MemWkp (d := d) k 2 (fun y => v (Φ.toFun y)) Ωαβ :=
    MemWkp.comp_smoothDiffeoBoundedAtOrder (d := d) k (le_refl k)
      (by norm_num) (by norm_num) hΩαβ_open hΩβα_open Φ
      hv_memWkp_Ωβα hv_cpt hv_supp_Ωβα
  set w : EuclN → ℝ := fun y => cE y * v (Φ.toFun y) with hw_def
  have hw_memWkp_Ωαβ : MemWkp (d := d) k 2 w Ωαβ :=
    MemWkp.smul_smooth_bounded (d := d) k (by norm_num) hΩαβ_open
      hcE_smooth' (fun j hj y _ => hCcoeff_bound y j hj) hv_comp_memWkp_Ωαβ
  have hw_supp_cE : tsupport w ⊆ tsupport cE := by
    refine closure_mono ?_
    intro y hy
    rw [Function.mem_support] at hy
    have hcE_ne : cE y ≠ 0 := by
      intro h0
      apply hy
      simp only [hw_def, h0, zero_mul]
    exact Function.mem_support.mpr hcE_ne
  have hw_supp_Ωαβ : tsupport w ⊆ Ωαβ := hw_supp_cE.trans hcE_tsupp_Ωαβ
  have hw_cpt : HasCompactSupport w :=
    hcE_cpt.of_isClosed_subset (isClosed_tsupport w) hw_supp_cE
  have h_coeFn : (fun y => ((chartTransitionTransportCLM
        (I := I) (M := M) g r s β α P₀ Q f :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      =ᵐ[(volume : Measure EuclN).restrict Tα]
      (fun y => cE y *
        (f : EuclN → ℝ) (chartTransitionEuclid (I := I) (M := M) α β y)) :=
    chartTransitionTransportCLM_coeFn_aeEq
      (I := I) (M := M) g r s β α P₀ Q f
  have h_pointwise : (fun y => cE y *
        (f : EuclN → ℝ) (chartTransitionEuclid (I := I) (M := M) α β y)) = w := by
    funext y
    by_cases hcE_zero : cE y = 0
    · simp only [hw_def, hcE_zero, zero_mul]
    · have hy_tsupp_cE : y ∈ tsupport cE :=
        subset_tsupport cE (Function.mem_support.mpr hcE_zero)
      have hy_KEα : y ∈ KEα := hcE_tsupp_subset hy_tsupp_cE
      have hy_Ωαβ : y ∈ Ωαβ := hKEα_in_Ωαβ hy_KEα
      have hT_eq : chartTransitionEuclid (I := I) (M := M) α β y = Φ.toFun y :=
        (hΦ_eq y hy_Ωαβ).symm
      have hΦy_KEβ : Φ.toFun y ∈ KEβ := ⟨y, hy_KEα, rfl⟩
      have hχ_Φy : χ (Φ.toFun y) = 1 :=
        hχ_one (Φ.toFun y) (Metric.self_subset_cthickening KEβ hΦy_KEβ)
      have hv_Φy : v (Φ.toFun y) =
          (f : EuclN → ℝ) (Φ.toFun y) := by
        simp only [hv_def, hT_def, hχ_Φy, one_mul]
      simp only [hw_def, hT_eq, hv_Φy]
  have h_ae : (fun y => ((chartTransitionTransportCLM
        (I := I) (M := M) g r s β α P₀ Q f :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      =ᵐ[(volume : Measure EuclN).restrict Tα] w := by
    refine h_coeFn.trans ?_
    rw [h_pointwise]
  have hw_memWkp_Tα : MemWkp (d := d) k 2 w Tα :=
    MemWkp.extend_zero (d := d) (by norm_num) (by norm_num)
      hΩαβ_open hTα_open hΩαβ_subset_target hw_memWkp_Ωαβ hw_supp_Ωαβ hw_cpt
  refine ⟨(MemWkp_congr_ae (d := d) (by norm_num) hTα_open h_ae).mpr hw_memWkp_Tα,
    ?_⟩
  rw [wkpNorm_congr_ae (d := d) (by norm_num) hTα_open h_ae]
  have h_w_norm_extend :
      iteratedWeakSobolevNorm (d := d) k 2 w Tα = iteratedWeakSobolevNorm (d := d) k 2 w Ωαβ :=
    wkpNorm_extend_zero (d := d) (by norm_num) (by norm_num)
      hΩαβ_open hTα_open hΩαβ_subset_target hw_memWkp_Ωαβ hw_supp_Ωαβ hw_cpt
  rw [h_w_norm_extend]
  have h_w_le_v_comp :
      iteratedWeakSobolevNorm (d := d) k 2 w Ωαβ ≤
        ENNReal.ofReal Kc' *
          iteratedWeakSobolevNorm (d := d) k 2 (fun y => v (Φ.toFun y)) Ωαβ := by
    have := hKc'_bound (u := fun y => v (Φ.toFun y)) hv_comp_memWkp_Ωαβ
    have h_eq : (fun y => cE y * (fun y => v (Φ.toFun y)) y) = w := by
      funext y; rfl
    rwa [h_eq] at this
  refine h_w_le_v_comp.trans ?_
  have h_v_comp_le :
      iteratedWeakSobolevNorm (d := d) k 2 (fun y => v (Φ.toFun y)) Ωαβ ≤
        ENNReal.ofReal Kcomp * iteratedWeakSobolevNorm (d := d) k 2 v Ωβα :=
    wkpNorm_comp_smoothDiffeoBoundedAtOrder_le (d := d) k (le_refl k)
      (by norm_num) (by norm_num) hΩαβ_open hΩβα_open Φ
      hv_memWkp_Ωβα hv_cpt hv_supp_Ωβα
  have h_v_norm_extend :
      iteratedWeakSobolevNorm (d := d) k 2 v Tβ = iteratedWeakSobolevNorm (d := d) k 2 v Ωβα :=
    wkpNorm_extend_zero (d := d) (by norm_num) (by norm_num)
      hΩβα_open hTβ_open hΩβα_subset_target hv_memWkp_Ωβα hv_supp_Ωβα hv_cpt
  have h_v_le_f :
      iteratedWeakSobolevNorm (d := d) k 2 v Tβ ≤
        ENNReal.ofReal Kχ *
          iteratedWeakSobolevNorm (d := d) k 2 (fun y => (f : EuclN → ℝ) y) Tβ := by
    have := hKχ_bound (u := fun y => (f : EuclN → ℝ) y) hf
    have h_eq : (fun y => χ y * (fun y => (f : EuclN → ℝ) y) y) = v := by
      funext y; rfl
    rwa [h_eq] at this
  calc
    ENNReal.ofReal Kc' *
        iteratedWeakSobolevNorm (d := d) k 2 (fun y => v (Φ.toFun y)) Ωαβ
      ≤ ENNReal.ofReal Kc' *
          (ENNReal.ofReal Kcomp * iteratedWeakSobolevNorm (d := d) k 2 v Ωβα) := by
        exact mul_le_mul_of_nonneg_left h_v_comp_le (zero_le _)
    _ = ENNReal.ofReal Kc' *
          (ENNReal.ofReal Kcomp * iteratedWeakSobolevNorm (d := d) k 2 v Tβ) := by
        rw [h_v_norm_extend]
    _ ≤ ENNReal.ofReal Kc' *
          (ENNReal.ofReal Kcomp *
            (ENNReal.ofReal Kχ *
              iteratedWeakSobolevNorm (d := d) k 2 (fun y => (f : EuclN → ℝ) y) Tβ)) := by
        refine mul_le_mul_of_nonneg_left ?_ (zero_le _)
        exact mul_le_mul_of_nonneg_left h_v_le_f (zero_le _)
    _ = ENNReal.ofReal (Kc' * (Kcomp * Kχ)) *
          iteratedWeakSobolevNorm (d := d) k 2 (fun y => (f : EuclN → ℝ) y) Tβ := by
        rw [ENNReal.ofReal_mul hKc'_pos.le,
          ENNReal.ofReal_mul hKcomp_nn]
        ring

private lemma memWkp_finsetSum
    {d : ℕ} [NeZero d] {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : IsOpen Ω)
    {ι : Type*} (T : Finset ι)
    (F : ι → EuclideanSpace ℝ (Fin d) → ℝ)
    (hF : ∀ i ∈ T, MemWkp (d := d) k p (F i) Ω) :
    MemWkp (d := d) k p (fun y => ∑ i ∈ T, F i y) Ω := by
  classical
  induction T using Finset.induction with
  | empty =>
      simpa using MemWkp_zero_fun (d := d) (k := k) (p := p) hp hΩ
  | insert a s ha ih =>
      have hF_a : MemWkp (d := d) k p (F a) Ω :=
        hF a (Finset.mem_insert_self a s)
      have hF_s : ∀ i ∈ s, MemWkp (d := d) k p (F i) Ω :=
        fun i hi => hF i (Finset.mem_insert_of_mem hi)
      have h_sum_s : MemWkp (d := d) k p (fun y => ∑ i ∈ s, F i y) Ω := ih hF_s
      have h_add : MemWkp (d := d) k p
          (fun y => F a y + ∑ i ∈ s, F i y) Ω :=
        MemWkp.add (d := d) hp hΩ hF_a h_sum_s
      have h_eq : (fun y => ∑ i ∈ insert a s, F i y) =
          fun y => F a y + ∑ i ∈ s, F i y := by
        funext y
        rw [Finset.sum_insert ha]
      rw [h_eq]
      exact h_add

private lemma wkpNorm_double_sum_le
    {d : ℕ} [NeZero d] {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : IsOpen Ω)
    {ι κ : Type*} (S : Finset ι) [Fintype κ]
    (F : ι → κ → EuclideanSpace ℝ (Fin d) → ℝ)
    (hF : ∀ i ∈ S, ∀ j : κ, MemWkp (d := d) k p (F i j) Ω) :
    iteratedWeakSobolevNorm (d := d) k p
        (fun y => ∑ i ∈ S, ∑ j : κ, F i j y) Ω ≤
      ∑ i ∈ S, ∑ j : κ, iteratedWeakSobolevNorm (d := d) k p (F i j) Ω := by
  classical
  have h_inner_mem : ∀ i ∈ S,
      MemWkp (d := d) k p (fun y => ∑ j : κ, F i j y) Ω := by
    intro i hi
    exact memWkp_finsetSum (d := d) hp hΩ (Finset.univ : Finset κ)
      (fun j => F i j) (fun j _ => hF i hi j)
  have h_outer := wkpNorm_sum_le (d := d) hp hΩ S
    (fun i y => ∑ j : κ, F i j y) h_inner_mem
  refine h_outer.trans ?_
  refine Finset.sum_le_sum ?_
  intro i hi
  exact wkpNorm_sum_le (d := d) hp hΩ (Finset.univ : Finset κ)
    (fun j => F i j) (fun j _ => hF i hi j)

omit [CompleteSpace E] in
theorem wkpNorm_tensorL2ChartComponentCutoff_le_of_pou
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (u : TensorL2 r s g) (α : M)
    (P₀ : TensorCompIdx (E := E) r s) (k : ℕ)
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) k 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s u β Q :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    ∃ C : ℝ, 0 ≤ C ∧
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) k 2
          (fun y => ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s u α P₀ :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal C *
          (∑ β ∈ transportChartCenters (I := I) (M := M) α,
            ∑ Q : TensorCompIdx (E := E) r s,
              iteratedWeakSobolevNorm (d := Module.finrank ℝ E) k 2
                (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s u β Q :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
                (chartTargetEuclid (I := I) (M := M) β)) := by
  classical
  set d : ℕ := Module.finrank ℝ E with hd_def
  set Tα : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hTα_def
  have hTα_open : IsOpen Tα := chartTargetEuclid_isOpen (I := I) (M := M) α
  set F : M → TensorCompIdx (E := E) r s → EuclN → ℝ :=
    fun β Q y =>
      ((chartTransitionTransportCLM (I := I) (M := M) g r s β α P₀ Q
          (tensorL2ChartComponent (I := I) (M := M) g r s u β Q) :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hF_def
  have h_per : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      ∃ C : ℝ, 0 ≤ C ∧
        MemWkp (d := d) k 2 (F β Q) Tα ∧
        iteratedWeakSobolevNorm (d := d) k 2 (F β Q) Tα ≤
          ENNReal.ofReal C *
            iteratedWeakSobolevNorm (d := d) k 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s u β Q :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β) := by
    intro β Q
    obtain ⟨C, hC_nn, hC_bound⟩ :=
      wkpNorm_chartTransitionTransportCLM_le (I := I) (M := M) g r s β α P₀ Q k
    obtain ⟨h_mem, h_bound⟩ := hC_bound
      (tensorL2ChartComponent (I := I) (M := M) g r s u β Q) (h_pou β Q)
    exact ⟨C, hC_nn, h_mem, h_bound⟩
  have hF_mem : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := d) k 2 (F β Q) Tα :=
    fun β Q => (h_per β Q).choose_spec.2.1
  set S : Finset M := transportChartCenters (I := I) (M := M) α with hS_def
  set Cfun : M → TensorCompIdx (E := E) r s → ℝ :=
    fun β Q => (h_per β Q).choose with hCfun_def
  have hCfun_nn : ∀ β Q, 0 ≤ Cfun β Q := fun β Q => (h_per β Q).choose_spec.1
  have hCfun_bound : ∀ β Q,
      iteratedWeakSobolevNorm (d := d) k 2 (F β Q) Tα ≤
        ENNReal.ofReal (Cfun β Q) *
          iteratedWeakSobolevNorm (d := d) k 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s u β Q :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β) :=
    fun β Q => (h_per β Q).choose_spec.2.2
  set C : ℝ := 1 + ∑ β ∈ S, ∑ Q : TensorCompIdx (E := E) r s, Cfun β Q
    with hC_def
  have hC_nn : 0 ≤ C := by
    rw [hC_def]
    have h_sum_nn : 0 ≤ ∑ β ∈ S, ∑ Q : TensorCompIdx (E := E) r s, Cfun β Q :=
      Finset.sum_nonneg (fun β _ =>
        Finset.sum_nonneg (fun Q _ => hCfun_nn β Q))
    linarith
  have hCfun_le_C : ∀ β ∈ S, ∀ Q : TensorCompIdx (E := E) r s,
      Cfun β Q ≤ C := by
    intro β hβ Q
    rw [hC_def]
    have h_le_double :
        Cfun β Q ≤ ∑ β' ∈ S, ∑ Q' : TensorCompIdx (E := E) r s, Cfun β' Q' := by
      have h_inner :
          Cfun β Q ≤ ∑ Q' : TensorCompIdx (E := E) r s, Cfun β Q' :=
        Finset.single_le_sum
          (f := fun Q' => Cfun β Q')
          (fun Q' _ => hCfun_nn β Q') (Finset.mem_univ Q)
      have h_outer :
          (∑ Q' : TensorCompIdx (E := E) r s, Cfun β Q') ≤
            ∑ β' ∈ S, ∑ Q' : TensorCompIdx (E := E) r s, Cfun β' Q' :=
        Finset.single_le_sum
          (f := fun β' => ∑ Q' : TensorCompIdx (E := E) r s, Cfun β' Q')
          (fun β' _ => Finset.sum_nonneg (fun Q' _ => hCfun_nn β' Q')) hβ
      exact h_inner.trans h_outer
    linarith
  refine ⟨C, hC_nn, ?_⟩
  have h_decomp : (fun y => ((tensorL2ChartComponentCutoff
        (I := I) (M := M) g r s u α P₀ :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      =ᵐ[(volume : Measure EuclN).restrict Tα]
      (fun y => ∑ β ∈ S, ∑ Q : TensorCompIdx (E := E) r s, F β Q y) :=
    tensorL2ChartComponentCutoff_ae_eq_pou_transport_sum
      (I := I) (M := M) g r s u α P₀
  rw [wkpNorm_congr_ae (d := d) (by norm_num) hTα_open h_decomp]
  have h_double_le :
      iteratedWeakSobolevNorm (d := d) k 2
          (fun y => ∑ β ∈ S, ∑ Q : TensorCompIdx (E := E) r s, F β Q y) Tα ≤
        ∑ β ∈ S, ∑ Q : TensorCompIdx (E := E) r s,
          iteratedWeakSobolevNorm (d := d) k 2 (F β Q) Tα :=
    wkpNorm_double_sum_le (d := d) (by norm_num) hTα_open S F
      (fun β _ Q => hF_mem β Q)
  refine h_double_le.trans ?_
  have h_each_le : ∀ β ∈ S, ∀ Q : TensorCompIdx (E := E) r s,
      iteratedWeakSobolevNorm (d := d) k 2 (F β Q) Tα ≤
        ENNReal.ofReal C *
          iteratedWeakSobolevNorm (d := d) k 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s u β Q :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β) := by
    intro β hβ Q
    refine (hCfun_bound β Q).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (zero_le _)
    exact ENNReal.ofReal_le_ofReal (hCfun_le_C β hβ Q)
  refine (Finset.sum_le_sum (fun β hβ =>
    Finset.sum_le_sum (fun Q _ => h_each_le β hβ Q))).trans ?_
  refine le_of_eq ?_
  have h_inner_factor : ∀ β ∈ S,
      (∑ Q : TensorCompIdx (E := E) r s,
        ENNReal.ofReal C *
          iteratedWeakSobolevNorm (d := d) k 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s u β Q :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β)) =
        ENNReal.ofReal C *
          ∑ Q : TensorCompIdx (E := E) r s,
            iteratedWeakSobolevNorm (d := d) k 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s u β Q :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β) := by
    intro β _
    rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl h_inner_factor, ← Finset.mul_sum]

omit [CompleteSpace E] in
theorem wkpNorm_tensorL2ChartComponentCutoff_le_of_pou_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : TensorL2 r s g,
        (∀ (β : M) (Q : TensorCompIdx (E := E) r s),
          MemWkp (d := Module.finrank ℝ E) k 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s u β Q :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β)) →
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) k 2
            (fun y => ((tensorL2ChartComponentCutoff (I := I) (M := M)
                g r s u α P₀ :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal C *
            (∑ β ∈ transportChartCenters (I := I) (M := M) α,
              ∑ Q : TensorCompIdx (E := E) r s,
                iteratedWeakSobolevNorm (d := Module.finrank ℝ E) k 2
                  (fun y => ((tensorL2ChartComponent (I := I) (M := M)
                      g r s u β Q :
                    Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                    EuclN → ℝ) y)
                  (chartTargetEuclid (I := I) (M := M) β)) := by
  classical
  set d : ℕ := Module.finrank ℝ E with hd_def
  set Tα : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hTα_def
  have hTα_open : IsOpen Tα := chartTargetEuclid_isOpen (I := I) (M := M) α
  set S : Finset M := transportChartCenters (I := I) (M := M) α with hS_def
  set F : TensorL2 r s g → M → TensorCompIdx (E := E) r s → EuclN → ℝ :=
    fun u β Q y =>
      ((chartTransitionTransportCLM (I := I) (M := M) g r s β α P₀ Q
          (tensorL2ChartComponent (I := I) (M := M) g r s u β Q) :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hF_def
  set Cfun : M → TensorCompIdx (E := E) r s → ℝ :=
    fun β Q =>
      (wkpNorm_chartTransitionTransportCLM_le (I := I) (M := M)
        g r s β α P₀ Q k).choose
    with hCfun_def
  have hCfun_spec : ∀ β Q,
      0 ≤ Cfun β Q ∧
        ∀ f : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β),
          MemWkp (d := d) k 2 (fun y => (f : EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β) →
          MemWkp (d := d) k 2
              (fun y => ((chartTransitionTransportCLM (I := I) (M := M)
                  g r s β α P₀ Q f :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
              Tα ∧
            iteratedWeakSobolevNorm (d := d) k 2
                (fun y => ((chartTransitionTransportCLM (I := I) (M := M)
                    g r s β α P₀ Q f :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
                Tα ≤
              ENNReal.ofReal (Cfun β Q) *
                iteratedWeakSobolevNorm (d := d) k 2 (fun y => (f : EuclN → ℝ) y)
                  (chartTargetEuclid (I := I) (M := M) β) := fun β Q =>
    (wkpNorm_chartTransitionTransportCLM_le (I := I) (M := M)
      g r s β α P₀ Q k).choose_spec
  have hCfun_nn : ∀ β Q, 0 ≤ Cfun β Q := fun β Q => (hCfun_spec β Q).1
  set C : ℝ := 1 + ∑ β ∈ S, ∑ Q : TensorCompIdx (E := E) r s, Cfun β Q
    with hC_def
  have hC_nn : 0 ≤ C := by
    rw [hC_def]
    have h_sum_nn : 0 ≤ ∑ β ∈ S, ∑ Q : TensorCompIdx (E := E) r s, Cfun β Q :=
      Finset.sum_nonneg (fun β _ =>
        Finset.sum_nonneg (fun Q _ => hCfun_nn β Q))
    linarith
  have hCfun_le_C : ∀ β ∈ S, ∀ Q : TensorCompIdx (E := E) r s, Cfun β Q ≤ C := by
    intro β hβ Q
    rw [hC_def]
    have h_inner : Cfun β Q ≤ ∑ Q' : TensorCompIdx (E := E) r s, Cfun β Q' :=
      Finset.single_le_sum (f := fun Q' => Cfun β Q')
        (fun Q' _ => hCfun_nn β Q') (Finset.mem_univ Q)
    have h_outer :
        (∑ Q' : TensorCompIdx (E := E) r s, Cfun β Q') ≤
          ∑ β' ∈ S, ∑ Q' : TensorCompIdx (E := E) r s, Cfun β' Q' :=
      Finset.single_le_sum
        (f := fun β' => ∑ Q' : TensorCompIdx (E := E) r s, Cfun β' Q')
        (fun β' _ => Finset.sum_nonneg (fun Q' _ => hCfun_nn β' Q')) hβ
    linarith [h_inner.trans h_outer]
  refine ⟨C, hC_nn, fun u h_pou => ?_⟩
  have hF_spec : ∀ β Q,
      MemWkp (d := d) k 2 (F u β Q) Tα ∧
        iteratedWeakSobolevNorm (d := d) k 2 (F u β Q) Tα ≤
          ENNReal.ofReal (Cfun β Q) *
            iteratedWeakSobolevNorm (d := d) k 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M)
                  g r s u β Q :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β) := fun β Q =>
    (hCfun_spec β Q).2 (tensorL2ChartComponent (I := I) (M := M) g r s u β Q)
      (h_pou β Q)
  have hF_mem : ∀ β Q, MemWkp (d := d) k 2 (F u β Q) Tα :=
    fun β Q => (hF_spec β Q).1
  have h_decomp : (fun y => ((tensorL2ChartComponentCutoff
        (I := I) (M := M) g r s u α P₀ :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      =ᵐ[(volume : Measure EuclN).restrict Tα]
      (fun y => ∑ β ∈ S, ∑ Q : TensorCompIdx (E := E) r s, F u β Q y) :=
    tensorL2ChartComponentCutoff_ae_eq_pou_transport_sum
      (I := I) (M := M) g r s u α P₀
  rw [wkpNorm_congr_ae (d := d) (by norm_num) hTα_open h_decomp]
  have h_double_le :
      iteratedWeakSobolevNorm (d := d) k 2
          (fun y => ∑ β ∈ S, ∑ Q : TensorCompIdx (E := E) r s, F u β Q y) Tα ≤
        ∑ β ∈ S, ∑ Q : TensorCompIdx (E := E) r s,
          iteratedWeakSobolevNorm (d := d) k 2 (F u β Q) Tα :=
    wkpNorm_double_sum_le (d := d) (by norm_num) hTα_open S (F u)
      (fun β _ Q => hF_mem β Q)
  refine h_double_le.trans ?_
  have h_each_le : ∀ β ∈ S, ∀ Q : TensorCompIdx (E := E) r s,
      iteratedWeakSobolevNorm (d := d) k 2 (F u β Q) Tα ≤
        ENNReal.ofReal C *
          iteratedWeakSobolevNorm (d := d) k 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s u β Q :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β) := by
    intro β hβ Q
    refine (hF_spec β Q).2.trans ?_
    exact mul_le_mul_of_nonneg_right
      (ENNReal.ofReal_le_ofReal (hCfun_le_C β hβ Q)) (zero_le _)
  refine (Finset.sum_le_sum (fun β hβ =>
    Finset.sum_le_sum (fun Q _ => h_each_le β hβ Q))).trans ?_
  refine le_of_eq ?_
  have h_inner_factor : ∀ β ∈ S,
      (∑ Q : TensorCompIdx (E := E) r s,
        ENNReal.ofReal C *
          iteratedWeakSobolevNorm (d := d) k 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s u β Q :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β)) =
        ENNReal.ofReal C *
          ∑ Q : TensorCompIdx (E := E) r s,
            iteratedWeakSobolevNorm (d := d) k 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s u β Q :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β) := by
    intro β _
    rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl h_inner_factor, ← Finset.mul_sum]

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
