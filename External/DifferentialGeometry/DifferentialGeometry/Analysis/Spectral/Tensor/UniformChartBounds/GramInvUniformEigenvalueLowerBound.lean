import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.InnerBounds.InnerLowerBound
import DifferentialGeometry.Analysis.Spectral.Tensor.NormEstimates.NormComparison
import DifferentialGeometry.Geometry.Connection.ChartBridge.MetricInverse
import DifferentialGeometry.Geometry.Metric.PointwiseInner.DualMetric
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Comparison
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order.Compact

































noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Set IsManifold ContinuousLinearMap Metric Function
open scoped Manifold Topology Bundle ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.DivergenceTheorem
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] in


private lemma sphere_isCompact :
    IsCompact {ξ : Fin (Module.finrank ℝ E) → ℝ |
      ∑ i : Fin (Module.finrank ℝ E), ξ i ^ 2 = 1} := by
  have hcont : Continuous
      (fun ξ : Fin (Module.finrank ℝ E) → ℝ =>
        ∑ i : Fin (Module.finrank ℝ E), ξ i ^ 2) :=
    continuous_finset_sum _ (fun i _ => (continuous_apply i).pow 2)
  have hclosed : IsClosed {ξ : Fin (Module.finrank ℝ E) → ℝ |
      ∑ i : Fin (Module.finrank ℝ E), ξ i ^ 2 = 1} :=
    isClosed_eq hcont continuous_const
  have hbdd : Bornology.IsBounded {ξ : Fin (Module.finrank ℝ E) → ℝ |
      ∑ i : Fin (Module.finrank ℝ E), ξ i ^ 2 = 1} := by
    refine (Metric.isBounded_iff_subset_closedBall (0 : _)).mpr ⟨1, ?_⟩
    intro ξ hξ
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr ?_
    intro i
    have hle : ξ i ^ 2 ≤ ∑ j : Fin (Module.finrank ℝ E), ξ j ^ 2 := by
      refine Finset.single_le_sum (s := Finset.univ)
        (f := fun j : Fin (Module.finrank ℝ E) => ξ j ^ 2) ?_ (Finset.mem_univ i)
      intro j _
      exact sq_nonneg _
    rw [hξ] at hle
    have habs : |ξ i| ≤ 1 := by
      have h_abs_sq : |ξ i| ^ 2 ≤ 1 := by rw [sq_abs]; exact hle
      nlinarith [abs_nonneg (ξ i), sq_nonneg (|ξ i| - 1)]
    exact habs
  exact (isCompact_iff_isClosed_bounded.mpr ⟨hclosed, hbdd⟩)














theorem exists_chartInvGramMatrix_quadForm_lower_bound_on_compact
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    {Kα : Set M} (hKα_compact : IsCompact Kα)
    (hKα_sub_baseSet :
      Kα ⊆ (trivializationAt E (TangentSpace I) α).baseSet) :
    ∃ c : ℝ, 0 < c ∧
      ∀ b : M, b ∈ Kα →
        ∀ ξ : Fin (Module.finrank ℝ E) → ℝ,
          c * (∑ i : Fin (Module.finrank ℝ E), ξ i ^ 2) ≤
            ∑ i : Fin (Module.finrank ℝ E),
              ∑ j : Fin (Module.finrank ℝ E),
                chartInvGramMatrix (I := I) g α b i j * ξ i * ξ j := by
  classical
  set Q : M × (Fin (Module.finrank ℝ E) → ℝ) → ℝ := fun p =>
    ∑ i : Fin (Module.finrank ℝ E),
      ∑ j : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g α p.1 i j * p.2 i * p.2 j
    with hQ_def
  have hQ_pos_baseSet : ∀ b ∈ (trivializationAt E (TangentSpace I) α).baseSet,
      ∀ ξ : Fin (Module.finrank ℝ E) → ℝ, ξ ≠ 0 →
        0 < ∑ i : Fin (Module.finrank ℝ E),
              ∑ j : Fin (Module.finrank ℝ E),
                chartInvGramMatrix (I := I) g α b i j * ξ i * ξ j := by
    intro b hb ξ hξ
    have hG_pd : (chartGramMatrix (I := I) g α b).PosDef :=
      chartGramMatrix_posDef (I := I) g α hb
    have hGinv_pd : (chartInvGramMatrix (I := I) g α b).PosDef := by
      unfold chartInvGramMatrix
      exact hG_pd.inv
    have hdot_pos :
        0 < star ξ ⬝ᵥ chartInvGramMatrix (I := I) g α b *ᵥ ξ :=
      hGinv_pd.dotProduct_mulVec_pos hξ
    have hexp :
        star ξ ⬝ᵥ chartInvGramMatrix (I := I) g α b *ᵥ ξ =
          ∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              chartInvGramMatrix (I := I) g α b i j * ξ i * ξ j := by
      simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      ring
    rw [← hexp]; exact hdot_pos
  have hQ_cont : ContinuousOn Q
      ((trivializationAt E (TangentSpace I) α).baseSet ×ˢ
        (Set.univ : Set (Fin (Module.finrank ℝ E) → ℝ))) := by
    refine continuousOn_finset_sum _ (fun i _ => ?_)
    refine continuousOn_finset_sum _ (fun j _ => ?_)
    refine ContinuousOn.mul ?_ ?_
    · refine ContinuousOn.mul ?_ ?_
      · have hentry := (chartInvGramMatrix_entry_contMDiffOn
          (I := I) g α i j).continuousOn
        exact hentry.comp continuous_fst.continuousOn (fun p hp => hp.1)
      · exact ((continuous_apply i).comp continuous_snd).continuousOn
    · exact ((continuous_apply j).comp continuous_snd).continuousOn
  set Sph : Set (Fin (Module.finrank ℝ E) → ℝ) :=
    {ξ | ∑ i : Fin (Module.finrank ℝ E), ξ i ^ 2 = 1} with hSph_def
  have hSph_compact : IsCompact Sph := sphere_isCompact (E := E)
  set K : Set (M × (Fin (Module.finrank ℝ E) → ℝ)) := Kα ×ˢ Sph with hK_def
  have hK_compact : IsCompact K := hKα_compact.prod hSph_compact
  have hK_sub_baseSet :
      K ⊆ (trivializationAt E (TangentSpace I) α).baseSet ×ˢ Set.univ := by
    intro p hp
    exact ⟨hKα_sub_baseSet hp.1, mem_univ _⟩
  have hQ_cont_K : ContinuousOn Q K := hQ_cont.mono hK_sub_baseSet
  have hSph_ne_zero : ∀ ξ ∈ Sph, ξ ≠ 0 := by
    intro ξ hξ hξ0
    have : (1 : ℝ) = 0 := by
      rw [← hξ, hξ0]; simp
    exact one_ne_zero this
  by_cases hK_ne : K.Nonempty
  · obtain ⟨p₀, hp₀_mem, hp₀_min⟩ :=
      hK_compact.exists_isMinOn hK_ne hQ_cont_K
    have hp₀_M : p₀.1 ∈ Kα := hp₀_mem.1
    have hp₀_S : p₀.2 ∈ Sph := hp₀_mem.2
    have hp₀_ξne : p₀.2 ≠ 0 := hSph_ne_zero p₀.2 hp₀_S
    have hp₀_base : p₀.1 ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
      hKα_sub_baseSet hp₀_M
    have hp₀_pos : 0 < Q p₀ :=
      hQ_pos_baseSet p₀.1 hp₀_base p₀.2 hp₀_ξne
    refine ⟨Q p₀, hp₀_pos, ?_⟩
    intro b hb ξ
    by_cases hξ_eq : (∑ i : Fin (Module.finrank ℝ E), ξ i ^ 2) = 0
    · have hξzero : ∀ i, ξ i = 0 := by
        intro i
        have hle : ξ i ^ 2 ≤ ∑ j : Fin (Module.finrank ℝ E), ξ j ^ 2 := by
          refine Finset.single_le_sum (s := Finset.univ)
            (f := fun j : Fin (Module.finrank ℝ E) => ξ j ^ 2) ?_ (Finset.mem_univ i)
          intro j _; exact sq_nonneg _
        rw [hξ_eq] at hle
        have hsqz : ξ i ^ 2 = 0 := le_antisymm hle (sq_nonneg _)
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsqz
      have hQzero :
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              chartInvGramMatrix (I := I) g α b i j * ξ i * ξ j) = 0 := by
        refine Finset.sum_eq_zero (fun i _ => ?_)
        refine Finset.sum_eq_zero (fun j _ => ?_)
        rw [hξzero i, mul_zero, zero_mul]
      rw [hξ_eq, mul_zero, hQzero]
    · have hξ_pos : 0 < ∑ i : Fin (Module.finrank ℝ E), ξ i ^ 2 :=
        lt_of_le_of_ne (Finset.sum_nonneg (fun i _ => sq_nonneg _))
          (Ne.symm hξ_eq)
      set r : ℝ := Real.sqrt (∑ i : Fin (Module.finrank ℝ E), ξ i ^ 2)
        with hr_def
      have hr_pos : 0 < r := Real.sqrt_pos.mpr hξ_pos
      have hr_ne : r ≠ 0 := ne_of_gt hr_pos
      have hr_sq : r ^ 2 = ∑ i, ξ i ^ 2 := by
        rw [hr_def, sq]; rw [Real.mul_self_sqrt (le_of_lt hξ_pos)]
      set η : Fin (Module.finrank ℝ E) → ℝ := fun i => ξ i / r with hη_def
      have hη_sph : η ∈ Sph := by
        rw [hSph_def]
        change ∑ i : Fin (Module.finrank ℝ E), η i ^ 2 = 1
        have : ∑ i : Fin (Module.finrank ℝ E), η i ^ 2 =
            (∑ i, ξ i ^ 2) / r ^ 2 := by
          rw [Finset.sum_div]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [hη_def, div_pow]
        rw [this, hr_sq]
        exact div_self (ne_of_gt hξ_pos)
      have hbη_mem : (b, η) ∈ K := ⟨hb, hη_sph⟩
      have hmin_le_bη : Q p₀ ≤ Q (b, η) := hp₀_min hbη_mem
      have hQscale :
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              chartInvGramMatrix (I := I) g α b i j * ξ i * ξ j) =
            r ^ 2 *
              (∑ i : Fin (Module.finrank ℝ E),
                ∑ j : Fin (Module.finrank ℝ E),
                  chartInvGramMatrix (I := I) g α b i j * η i * η j) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [hη_def]
        change chartInvGramMatrix (I := I) g α b i j * ξ i * ξ j =
          r ^ 2 * (chartInvGramMatrix (I := I) g α b i j * (ξ i / r) * (ξ j / r))
        field_simp
      rw [hQscale]
      have hQη : Q (b, η) =
          ∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              chartInvGramMatrix (I := I) g α b i j * η i * η j := rfl
      rw [← hQη]
      rw [← hr_sq, mul_comm]
      exact mul_le_mul_of_nonneg_left hmin_le_bη (sq_nonneg r)
  · refine ⟨1, one_pos, ?_⟩
    intro b hb ξ
    by_cases hKα_ne : Kα.Nonempty
    · by_cases hn : Nonempty (Fin (Module.finrank ℝ E))
      · haveI : Nonempty (Fin (Module.finrank ℝ E)) := hn
        set i₀ : Fin (Module.finrank ℝ E) := Classical.arbitrary _
        set e₀ : Fin (Module.finrank ℝ E) → ℝ :=
          (Pi.single i₀ (1 : ℝ) : Fin (Module.finrank ℝ E) → ℝ) with he₀_def
        have h0 : e₀ ∈ Sph := by
          rw [hSph_def]
          change ∑ i : Fin (Module.finrank ℝ E), (e₀ i) ^ 2 = 1
          rw [Finset.sum_eq_single i₀]
          · simp [he₀_def]
          · intro i _ hi
            rw [he₀_def, Pi.single_apply, if_neg hi]; ring
          · intro h
            exact absurd (Finset.mem_univ _) h
        obtain ⟨b₀, hb₀⟩ := hKα_ne
        exact absurd ⟨(b₀, e₀), ⟨hb₀, h0⟩⟩ hK_ne
      · have hempty : ¬ Nonempty (Fin (Module.finrank ℝ E)) := hn
        have hsum_empty : ∀ f : Fin (Module.finrank ℝ E) → ℝ,
            ∑ i : Fin (Module.finrank ℝ E), f i = 0 := by
          intro f
          apply Finset.sum_eq_zero
          intro i _
          exact absurd ⟨i⟩ hempty
        rw [hsum_empty]
        rw [mul_zero]
        exact le_of_eq (hsum_empty _).symm
    · exact absurd ⟨b, hb⟩ hKα_ne



theorem chartInvGram_quad_ub
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    {Kα : Set M} (hKα_compact : IsCompact Kα)
    (hKα_sub_baseSet :
      Kα ⊆ (trivializationAt E (TangentSpace I) α).baseSet) :
    ∃ C : ℝ, 0 < C ∧
      ∀ b : M, b ∈ Kα →
        ∀ ξ : Fin (Module.finrank ℝ E) → ℝ,
          (∑ i : Fin (Module.finrank ℝ E),
              ∑ j : Fin (Module.finrank ℝ E),
                chartInvGramMatrix (I := I) g α b i j * ξ i * ξ j) ≤
            C * (∑ i : Fin (Module.finrank ℝ E), ξ i ^ 2) := by
  classical
  set Q : M × (Fin (Module.finrank ℝ E) → ℝ) → ℝ := fun p =>
    ∑ i : Fin (Module.finrank ℝ E),
      ∑ j : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g α p.1 i j * p.2 i * p.2 j
    with hQ_def
  have hQ_cont : ContinuousOn Q
      ((trivializationAt E (TangentSpace I) α).baseSet ×ˢ
        (Set.univ : Set (Fin (Module.finrank ℝ E) → ℝ))) := by
    refine continuousOn_finset_sum _ (fun i _ => ?_)
    refine continuousOn_finset_sum _ (fun j _ => ?_)
    refine ContinuousOn.mul ?_ ?_
    · refine ContinuousOn.mul ?_ ?_
      · have hentry := (chartInvGramMatrix_entry_contMDiffOn
          (I := I) g α i j).continuousOn
        exact hentry.comp continuous_fst.continuousOn (fun p hp => hp.1)
      · exact ((continuous_apply i).comp continuous_snd).continuousOn
    · exact ((continuous_apply j).comp continuous_snd).continuousOn
  set Sph : Set (Fin (Module.finrank ℝ E) → ℝ) :=
    {ξ | ∑ i : Fin (Module.finrank ℝ E), ξ i ^ 2 = 1} with hSph_def
  have hSph_compact : IsCompact Sph := sphere_isCompact (E := E)
  set K : Set (M × (Fin (Module.finrank ℝ E) → ℝ)) := Kα ×ˢ Sph with hK_def
  have hK_compact : IsCompact K := hKα_compact.prod hSph_compact
  have hK_sub_baseSet :
      K ⊆ (trivializationAt E (TangentSpace I) α).baseSet ×ˢ Set.univ := by
    intro p hp
    exact ⟨hKα_sub_baseSet hp.1, mem_univ _⟩
  have hQ_cont_K : ContinuousOn Q K := hQ_cont.mono hK_sub_baseSet
  obtain ⟨B, hB⟩ := hK_compact.bddAbove_image hQ_cont_K
  refine ⟨max 1 B, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro b hb ξ
  by_cases hξ_eq : (∑ i : Fin (Module.finrank ℝ E), ξ i ^ 2) = 0
  · have hξzero : ∀ i, ξ i = 0 := by
      intro i
      have hle : ξ i ^ 2 ≤ ∑ j : Fin (Module.finrank ℝ E), ξ j ^ 2 := by
        refine Finset.single_le_sum (s := Finset.univ)
          (f := fun j : Fin (Module.finrank ℝ E) => ξ j ^ 2) ?_ (Finset.mem_univ i)
        intro j _
        exact sq_nonneg _
      rw [hξ_eq] at hle
      have hsqz : ξ i ^ 2 = 0 := le_antisymm hle (sq_nonneg _)
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsqz
    have hQzero :
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g α b i j * ξ i * ξ j) = 0 := by
      refine Finset.sum_eq_zero (fun i _ => ?_)
      refine Finset.sum_eq_zero (fun j _ => ?_)
      rw [hξzero i, mul_zero, zero_mul]
    rw [hQzero, hξ_eq, mul_zero]
  · have hξ_pos : 0 < ∑ i : Fin (Module.finrank ℝ E), ξ i ^ 2 :=
      lt_of_le_of_ne (Finset.sum_nonneg (fun i _ => sq_nonneg _))
        (Ne.symm hξ_eq)
    set r : ℝ := Real.sqrt (∑ i : Fin (Module.finrank ℝ E), ξ i ^ 2)
      with hr_def
    have hr_pos : 0 < r := Real.sqrt_pos.mpr hξ_pos
    have hr_sq : r ^ 2 = ∑ i, ξ i ^ 2 := by
      rw [hr_def, sq]
      rw [Real.mul_self_sqrt (le_of_lt hξ_pos)]
    set η : Fin (Module.finrank ℝ E) → ℝ := fun i => ξ i / r with hη_def
    have hη_sph : η ∈ Sph := by
      rw [hSph_def]
      change ∑ i : Fin (Module.finrank ℝ E), η i ^ 2 = 1
      have hsum : ∑ i : Fin (Module.finrank ℝ E), η i ^ 2 =
          (∑ i, ξ i ^ 2) / r ^ 2 := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [hη_def, div_pow]
      rw [hsum, hr_sq]
      exact div_self (ne_of_gt hξ_pos)
    have hbη_mem : (b, η) ∈ K := ⟨hb, hη_sph⟩
    have hQ_le : Q (b, η) ≤ max 1 B :=
      (hB ⟨(b, η), hbη_mem, rfl⟩).trans (le_max_right _ _)
    have hQscale :
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g α b i j * ξ i * ξ j) =
          r ^ 2 *
            (∑ i : Fin (Module.finrank ℝ E),
              ∑ j : Fin (Module.finrank ℝ E),
                chartInvGramMatrix (I := I) g α b i j * η i * η j) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [hη_def]
      change chartInvGramMatrix (I := I) g α b i j * ξ i * ξ j =
        r ^ 2 * (chartInvGramMatrix (I := I) g α b i j * (ξ i / r) * (ξ j / r))
      field_simp
    rw [hQscale]
    have hQη : Q (b, η) =
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g α b i j * η i * η j := rfl
    rw [← hQη]
    calc
      r ^ 2 * Q (b, η) ≤ r ^ 2 * max 1 B :=
        mul_le_mul_of_nonneg_left hQ_le (sq_nonneg r)
      _ = max 1 B * (∑ i : Fin (Module.finrank ℝ E), ξ i ^ 2) := by
        rw [← hr_sq]
        ring



theorem chartInvGram_quad_le
    (g h : SmoothRiemannianMetric I M) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (C : ℝ) (hC : 1 ≤ C)
    (hequiv : ∀ v : TangentSpace I b,
      C⁻¹ * g.inner b v v ≤ h.inner b v v ∧
        h.inner b v v ≤ C * g.inner b v v)
    (ξ : Fin (Module.finrank ℝ E) → ℝ) :
    (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) h α b i j * ξ i * ξ j) ≤
      C * (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g α b i j * ξ i * ξ j) := by
  classical
  let basis := chartBasisFamily (I := I) α hb
  let ξDual : Module.Dual ℝ (TangentSpace I b) :=
    ∑ i : Fin (Module.finrank ℝ E), ξ i • basis.coord i
  let A : Tensor0SSpace 1 I b := dualToCotangent_gen (I := I) ξDual
  have hA (i : Fin (Module.finrank ℝ E)) :
      cotangentToDual_gen (I := I) A (basis i) = ξ i := by
    simp only [A, cotangentToDual_dualToCotangent_gen, ξDual,
      LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [hji]
    · simp
  have hinv (g' : SmoothRiemannianMetric I M) :
      MetricInverseInBasis (I := I) g' b basis
        (fun i j => chartInvGramMatrix (I := I) g' α b i j) := by
    have hgram : ∀ i j : Fin (Module.finrank ℝ E),
        g'.inner b (basis i) (basis j) = chartGramMatrix (I := I) g' α b i j := by
      intro i j
      simp [basis, chartBasisFamily_apply, chartGramMatrix_apply]
    intro i j
    constructor
    · simp only [hgram]
      rw [← Matrix.mul_apply,
        chartInvGramMatrix_mul_chartGramMatrix (I := I) g' α hb,
        Matrix.one_apply]
    · simp only [hgram]
      rw [← Matrix.mul_apply,
        chartGramMatrix_mul_chartInvGramMatrix (I := I) g' α hb,
        Matrix.one_apply]
  have hcoord (g' : SmoothRiemannianMetric I M) :
      normSq0S (I := I) g' b 1 A =
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g' α b i j * ξ i * ξ j := by
    rw [Tensor0SBundle.normSq0S_eq_coord (I := I) g' b 1 basis
      (fun i j => chartInvGramMatrix (I := I) g' α b i j)
      (hinv g') A,
      Tensor0SBundle.coordInner0S_one_eq]
    simp only [hA]
  calc
    (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) h α b i j * ξ i * ξ j) =
        normSq0S (I := I) h b 1 A := (hcoord h).symm
    _ ≤ C ^ 1 * normSq0S (I := I) g b 1 A :=
      Tensor0SBundle.normSq0S_upper_le_of_equiv
        (I := I) g h b 1 hC hequiv A
    _ = C * (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g α b i j * ξ i * ξ j) := by
      rw [hcoord]
      simp

theorem chartInvGram_ent_le
    (g : SmoothRiemannianMetric I M) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    {C : ℝ}
    (hquad : ∀ ξ : Fin (Module.finrank ℝ E) → ℝ,
      (∑ p : Fin (Module.finrank ℝ E),
          ∑ q : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g α b p q * ξ p * ξ q) ≤
        C * (∑ p : Fin (Module.finrank ℝ E), ξ p ^ 2))
    (i j : Fin (Module.finrank ℝ E)) :
    |chartInvGramMatrix (I := I) g α b i j| ≤ C := by
  classical
  have hpos : (chartInvGramMatrix (I := I) g α b).PosSemidef := by
    unfold chartInvGramMatrix
    exact (chartGramMatrix_posDef (I := I) g α hb).inv.posSemidef
  have hdiag_nonneg (k : Fin (Module.finrank ℝ E)) :
      0 ≤ chartInvGramMatrix (I := I) g α b k k := hpos.diag_nonneg
  have hdiag_le (k : Fin (Module.finrank ℝ E)) :
      chartInvGramMatrix (I := I) g α b k k ≤ C := by
    simpa [Pi.single_apply] using hquad (Pi.single k (1 : ℝ))
  by_cases hij : i = j
  · subst j
    rw [abs_of_nonneg (hdiag_nonneg i)]
    exact hdiag_le i
  have hsymm : chartInvGramMatrix (I := I) g α b j i =
      chartInvGramMatrix (I := I) g α b i j := by
    simpa using hpos.isHermitian.apply i j
  let ei : Fin (Module.finrank ℝ E) → ℝ := Pi.single i (1 : ℝ)
  let ej : Fin (Module.finrank ℝ E) → ℝ := Pi.single j (1 : ℝ)
  have hei_sq : ∑ p : Fin (Module.finrank ℝ E), ei p ^ 2 = 1 := by
    simp [ei, Pi.single_apply]
  have hej_sq : ∑ p : Fin (Module.finrank ℝ E), ej p ^ 2 = 1 := by
    simp [ej, Pi.single_apply]
  have hcross : ∑ p : Fin (Module.finrank ℝ E), ei p * ej p = 0 := by
    rw [Finset.sum_eq_single i]
    · simp [ei, ej, hij]
    · intro p _ hpi
      simp [ei, hpi]
    · simp
  have hcross_two : ∑ p : Fin (Module.finrank ℝ E), 2 * ei p * ej p = 0 := by
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum, hcross, mul_zero]
  have hplus_norm : ∑ p : Fin (Module.finrank ℝ E), (ei p + ej p) ^ 2 = 2 := by
    simp_rw [add_sq]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hei_sq, hej_sq]
    rw [hcross_two]
    ring
  have hminus_norm : ∑ p : Fin (Module.finrank ℝ E), (ei p - ej p) ^ 2 = 2 := by
    simp_rw [sub_sq]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hei_sq, hej_sq]
    rw [hcross_two]
    ring
  have hplus_eval :
      (∑ p : Fin (Module.finrank ℝ E),
        ∑ q : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g α b p q * (ei p + ej p) * (ei q + ej q)) =
        chartInvGramMatrix (I := I) g α b i i +
          chartInvGramMatrix (I := I) g α b i j +
          chartInvGramMatrix (I := I) g α b j i +
          chartInvGramMatrix (I := I) g α b j j := by
    simp only [mul_add, add_mul, Finset.sum_add_distrib]
    simp [ei, ej, Pi.single_apply]
    ring
  have hminus_eval :
      (∑ p : Fin (Module.finrank ℝ E),
        ∑ q : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g α b p q * (ei p - ej p) * (ei q - ej q)) =
        chartInvGramMatrix (I := I) g α b i i -
          chartInvGramMatrix (I := I) g α b i j -
          chartInvGramMatrix (I := I) g α b j i +
          chartInvGramMatrix (I := I) g α b j j := by
    simp only [mul_sub, sub_mul, Finset.sum_sub_distrib]
    simp [ei, ej, Pi.single_apply]
    ring
  by_cases hentry : 0 ≤ chartInvGramMatrix (I := I) g α b i j
  · have hplus := hquad (ei + ej)
    change (∑ p : Fin (Module.finrank ℝ E),
        ∑ q : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g α b p q * (ei p + ej p) * (ei q + ej q)) ≤
      C * ∑ p : Fin (Module.finrank ℝ E), (ei p + ej p) ^ 2 at hplus
    rw [hplus_eval, hplus_norm, hsymm] at hplus
    rw [abs_of_nonneg hentry]
    nlinarith [hdiag_nonneg i, hdiag_nonneg j]
  · have hminus := hquad (ei - ej)
    change (∑ p : Fin (Module.finrank ℝ E),
        ∑ q : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g α b p q * (ei p - ej p) * (ei q - ej q)) ≤
      C * ∑ p : Fin (Module.finrank ℝ E), (ei p - ej p) ^ 2 at hminus
    rw [hminus_eval, hminus_norm, hsymm] at hminus
    rw [abs_of_neg (lt_of_not_ge hentry)]
    nlinarith [hdiag_nonneg i, hdiag_nonneg j]



theorem chartInvGram_unif_ub
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]
    {ι : Type*} (gBase : SmoothRiemannianMetric I M)
    (gSeq : ι → SmoothRiemannianMetric I M) (α : M)
    {Kα : Set M} (hKα_compact : IsCompact Kα)
    (hKα_sub_baseSet :
      Kα ⊆ (trivializationAt E (TangentSpace I) α).baseSet)
    (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hequiv : ∀ k : ι, ∀ b ∈ Kα, ∀ v : TangentSpace I b,
      Λ⁻¹ * gBase.inner b v v ≤ (gSeq k).inner b v v ∧
        (gSeq k).inner b v v ≤ Λ * gBase.inner b v v) :
    ∃ C : ℝ, 0 < C ∧
      ∀ k : ι, ∀ b ∈ Kα,
        ∀ ξ : Fin (Module.finrank ℝ E) → ℝ,
          (∑ i : Fin (Module.finrank ℝ E),
              ∑ j : Fin (Module.finrank ℝ E),
                chartInvGramMatrix (I := I) (gSeq k) α b i j * ξ i * ξ j) ≤
            C * (∑ i : Fin (Module.finrank ℝ E), ξ i ^ 2) := by
  obtain ⟨CBase, hCBase, hbase⟩ :=
    chartInvGram_quad_ub (I := I) (M := M) gBase α
      hKα_compact hKα_sub_baseSet
  have hΛpos : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
  refine ⟨Λ * CBase, mul_pos hΛpos hCBase, ?_⟩
  intro k b hb ξ
  calc
    (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) (gSeq k) α b i j * ξ i * ξ j) ≤
        Λ * (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) gBase α b i j * ξ i * ξ j) :=
      chartInvGram_quad_le (I := I) gBase (gSeq k) α
        (hKα_sub_baseSet hb) Λ hΛ (hequiv k b hb) ξ
    _ ≤ Λ * (CBase * (∑ i : Fin (Module.finrank ℝ E), ξ i ^ 2)) :=
      mul_le_mul_of_nonneg_left (hbase b hb ξ) hΛpos.le
    _ = (Λ * CBase) * (∑ i : Fin (Module.finrank ℝ E), ξ i ^ 2) := by ring



theorem chartInvGram_unif_lb
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]
    {ι : Type*} (gBase : SmoothRiemannianMetric I M)
    (gSeq : ι → SmoothRiemannianMetric I M) (α : M)
    {Kα : Set M} (hKα_compact : IsCompact Kα)
    (hKα_sub_baseSet :
      Kα ⊆ (trivializationAt E (TangentSpace I) α).baseSet)
    (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hequiv : ∀ k : ι, ∀ b ∈ Kα, ∀ v : TangentSpace I b,
      Λ⁻¹ * gBase.inner b v v ≤ (gSeq k).inner b v v ∧
        (gSeq k).inner b v v ≤ Λ * gBase.inner b v v) :
    ∃ c : ℝ, 0 < c ∧
      ∀ k : ι, ∀ b ∈ Kα,
        ∀ ξ : Fin (Module.finrank ℝ E) → ℝ,
          c * (∑ i : Fin (Module.finrank ℝ E), ξ i ^ 2) ≤
            ∑ i : Fin (Module.finrank ℝ E),
              ∑ j : Fin (Module.finrank ℝ E),
                chartInvGramMatrix (I := I) (gSeq k) α b i j * ξ i * ξ j := by
  classical
  obtain ⟨cBase, hcBase, hbase⟩ :=
    exists_chartInvGramMatrix_quadForm_lower_bound_on_compact
      (I := I) (M := M) gBase α hKα_compact hKα_sub_baseSet
  have hΛpos : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
  refine ⟨cBase / Λ, div_pos hcBase hΛpos, ?_⟩
  intro k b hb ξ
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    hKα_sub_baseSet hb
  let basis := chartBasisFamily (I := I) α hb_base
  let ξDual : Module.Dual ℝ (TangentSpace I b) :=
    ∑ i : Fin (Module.finrank ℝ E), ξ i • basis.coord i
  let A : Tensor0SSpace 1 I b := dualToCotangent_gen (I := I) ξDual
  have hA (i : Fin (Module.finrank ℝ E)) :
      cotangentToDual_gen (I := I) A (basis i) = ξ i := by
    simp only [A, cotangentToDual_dualToCotangent_gen, ξDual,
      LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [hji]
    · simp
  have hinv (g : SmoothRiemannianMetric I M) :
      MetricInverseInBasis (I := I) g b basis
        (fun i j => chartInvGramMatrix (I := I) g α b i j) := by
    have hgram : ∀ i j : Fin (Module.finrank ℝ E),
        g.inner b (basis i) (basis j) = chartGramMatrix (I := I) g α b i j := by
      intro i j
      simp [basis, chartBasisFamily_apply, chartGramMatrix_apply]
    intro i j
    constructor
    · simp only [hgram]
      rw [← Matrix.mul_apply,
        chartInvGramMatrix_mul_chartGramMatrix (I := I) g α hb_base,
        Matrix.one_apply]
    · simp only [hgram]
      rw [← Matrix.mul_apply,
        chartGramMatrix_mul_chartInvGramMatrix (I := I) g α hb_base,
        Matrix.one_apply]
  have hbase_coord :
      normSq0S (I := I) gBase b 1 A =
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) gBase α b i j * ξ i * ξ j := by
    rw [Tensor0SBundle.normSq0S_eq_coord (I := I) gBase b 1 basis
      (fun i j => chartInvGramMatrix (I := I) gBase α b i j)
      (hinv gBase) A,
      Tensor0SBundle.coordInner0S_one_eq]
    simp only [hA]
  have hseq_coord :
      normSq0S (I := I) (gSeq k) b 1 A =
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) (gSeq k) α b i j * ξ i * ξ j := by
    rw [Tensor0SBundle.normSq0S_eq_coord (I := I) (gSeq k) b 1 basis
      (fun i j => chartInvGramMatrix (I := I) (gSeq k) α b i j)
      (hinv (gSeq k)) A,
      Tensor0SBundle.coordInner0S_one_eq]
    simp only [hA]
  have hnorm :
      Λ⁻¹ * normSq0S (I := I) gBase b 1 A ≤
        normSq0S (I := I) (gSeq k) b 1 A := by
    simpa using Tensor0SBundle.normSq0S_lower_le_of_equiv
      (I := I) gBase (gSeq k) b 1 hΛ (hequiv k b hb) A
  have hΛinv_nonneg : 0 ≤ Λ⁻¹ := inv_nonneg.mpr hΛpos.le
  calc
    cBase / Λ * (∑ i : Fin (Module.finrank ℝ E), ξ i ^ 2) =
        Λ⁻¹ * (cBase * ∑ i : Fin (Module.finrank ℝ E), ξ i ^ 2) := by
          rw [div_eq_mul_inv]
          ring
    _ ≤ Λ⁻¹ * normSq0S (I := I) gBase b 1 A :=
      mul_le_mul_of_nonneg_left
        (hbase b hb ξ |>.trans_eq hbase_coord.symm) hΛinv_nonneg
    _ ≤ normSq0S (I := I) (gSeq k) b 1 A := hnorm
    _ = _ := hseq_coord



theorem chartInvGram_pou_lb
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]
    {ι : Type*} (gBase : SmoothRiemannianMetric I M)
    (gSeq : ι → SmoothRiemannianMetric I M)
    (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hequiv : ∀ k : ι, ∀ b : M, ∀ v : TangentSpace I b,
      Λ⁻¹ * gBase.inner b v v ≤ (gSeq k).inner b v v ∧
        (gSeq k).inner b v v ≤ Λ * gBase.inner b v v) :
    ∃ c : ℝ, 0 < c ∧
      ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        ∀ k : ι, ∀ b ∈ tsupport
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
          ∀ ξ : Fin (Module.finrank ℝ E) → ℝ,
            c * (∑ i : Fin (Module.finrank ℝ E), ξ i ^ 2) ≤
              ∑ i : Fin (Module.finrank ℝ E),
                ∑ j : Fin (Module.finrank ℝ E),
                  chartInvGramMatrix (I := I) (gSeq k) α b i j * ξ i * ξ j := by
  classical
  have hper : ∀ α : M, ∃ c : ℝ, 0 < c ∧
      ∀ k : ι, ∀ b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ ξ : Fin (Module.finrank ℝ E) → ℝ,
          c * (∑ i : Fin (Module.finrank ℝ E), ξ i ^ 2) ≤
            ∑ i : Fin (Module.finrank ℝ E),
              ∑ j : Fin (Module.finrank ℝ E),
                chartInvGramMatrix (I := I) (gSeq k) α b i j * ξ i * ξ j := by
    intro α
    exact chartInvGram_unif_lb (I := I) (M := M) gBase gSeq α
      (pouTsupport_isCompact (I := I) (M := M) α)
      (pouTsupport_subset_baseSet (I := I) (M := M) α) Λ hΛ
      (fun k b _hb v => hequiv k b v)
  choose cα hcα hbound using hper
  by_cases hM : Nonempty M
  · letI : Nonempty M := hM
    let b₀ : M := Classical.arbitrary M
    obtain ⟨α₀, hα₀_pos⟩ :
        ∃ α : M, 0 < (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) b₀ :=
      (chartAtlasPOU I M).exists_pos_of_mem (Set.mem_univ b₀)
    have hα₀_mem : α₀ ∈ chartAtlasPOU_finset (I := I) (M := M) := by
      rw [chartAtlasPOU_finset_mem]
      exact ⟨b₀, ne_of_gt hα₀_pos⟩
    have hS_ne : (chartAtlasPOU_finset (I := I) (M := M)).Nonempty :=
      ⟨α₀, hα₀_mem⟩
    let c : ℝ :=
      (chartAtlasPOU_finset (I := I) (M := M)).image cα |>.min' (by
        rw [Finset.image_nonempty]
        exact hS_ne)
    have hc_pos : 0 < c := by
      have hc_mem : c ∈ (chartAtlasPOU_finset (I := I) (M := M)).image cα :=
        Finset.min'_mem _ _
      obtain ⟨α, _hα, hαc⟩ := Finset.mem_image.mp hc_mem
      rw [← hαc]
      exact hcα α
    have hc_le : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M), c ≤ cα α := by
      intro α hα
      apply Finset.min'_le
      exact Finset.mem_image.mpr ⟨α, hα, rfl⟩
    refine ⟨c, hc_pos, ?_⟩
    intro α hα k b hb ξ
    calc
      c * (∑ i : Fin (Module.finrank ℝ E), ξ i ^ 2) ≤
          cα α * (∑ i : Fin (Module.finrank ℝ E), ξ i ^ 2) :=
        mul_le_mul_of_nonneg_right (hc_le α hα)
          (Finset.sum_nonneg fun i _ => sq_nonneg (ξ i))
      _ ≤ _ := hbound α k b hb ξ
  · refine ⟨1, one_pos, ?_⟩
    intro α _hα
    exact (hM ⟨α⟩).elim



theorem chartInvGram_pou_ub
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]
    {ι : Type*} (gBase : SmoothRiemannianMetric I M)
    (gSeq : ι → SmoothRiemannianMetric I M)
    (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hequiv : ∀ k : ι, ∀ b : M, ∀ v : TangentSpace I b,
      Λ⁻¹ * gBase.inner b v v ≤ (gSeq k).inner b v v ∧
        (gSeq k).inner b v v ≤ Λ * gBase.inner b v v) :
    ∃ C : ℝ, 0 < C ∧
      ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        ∀ k : ι, ∀ b ∈ tsupport
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
          ∀ ξ : Fin (Module.finrank ℝ E) → ℝ,
            (∑ i : Fin (Module.finrank ℝ E),
                ∑ j : Fin (Module.finrank ℝ E),
                  chartInvGramMatrix (I := I) (gSeq k) α b i j * ξ i * ξ j) ≤
              C * (∑ i : Fin (Module.finrank ℝ E), ξ i ^ 2) := by
  classical
  have hper : ∀ α : M, ∃ C : ℝ, 0 < C ∧
      ∀ k : ι, ∀ b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ ξ : Fin (Module.finrank ℝ E) → ℝ,
          (∑ i : Fin (Module.finrank ℝ E),
              ∑ j : Fin (Module.finrank ℝ E),
                chartInvGramMatrix (I := I) (gSeq k) α b i j * ξ i * ξ j) ≤
            C * (∑ i : Fin (Module.finrank ℝ E), ξ i ^ 2) := by
    intro α
    exact chartInvGram_unif_ub (I := I) (M := M) gBase gSeq α
      (pouTsupport_isCompact (I := I) (M := M) α)
      (pouTsupport_subset_baseSet (I := I) (M := M) α) Λ hΛ
      (fun k b _hb v => hequiv k b v)
  choose Cα hCα hbound using hper
  let C : ℝ := 1 + ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M), Cα α
  have hsum_nonneg : 0 ≤ ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M), Cα α :=
    Finset.sum_nonneg fun α _ => (hCα α).le
  have hC_pos : 0 < C := by
    dsimp [C]
    linarith
  refine ⟨C, hC_pos, ?_⟩
  intro α hα k b hb ξ
  have hCα_le : Cα α ≤ C := by
    have hsingle : Cα α ≤
        ∑ β ∈ chartAtlasPOU_finset (I := I) (M := M), Cα β :=
      Finset.single_le_sum (fun β _ => (hCα β).le) hα
    dsimp [C]
    linarith
  exact (hbound α k b hb ξ).trans
    (mul_le_mul_of_nonneg_right hCα_le
      (Finset.sum_nonneg fun i _ => sq_nonneg (ξ i)))



theorem chartInvGram_pou_bnd
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]
    {ι : Type*} (gBase : SmoothRiemannianMetric I M)
    (gSeq : ι → SmoothRiemannianMetric I M)
    (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hequiv : ∀ k : ι, ∀ b : M, ∀ v : TangentSpace I b,
      Λ⁻¹ * gBase.inner b v v ≤ (gSeq k).inner b v v ∧
        (gSeq k).inner b v v ≤ Λ * gBase.inner b v v) :
    ∃ C : ℝ, 0 < C ∧
      ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        ∀ k : ι, ∀ b ∈ tsupport
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
          ∀ i j : Fin (Module.finrank ℝ E),
            |chartInvGramMatrix (I := I) (gSeq k) α b i j| ≤ C := by
  obtain ⟨C, hC, hupper⟩ :=
    chartInvGram_pou_ub (I := I) (M := M) gBase gSeq Λ hΛ hequiv
  refine ⟨C, hC, ?_⟩
  intro α hα k b hb i j
  exact chartInvGram_ent_le (I := I) (gSeq k) α
    (pouTsupport_subset_baseSet (I := I) (M := M) α hb)
    (hupper α hα k b hb) i j



theorem chartInvGram_pou_eqv
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]
    {ι : Type*} (gBase : SmoothRiemannianMetric I M)
    (gSeq : ι → SmoothRiemannianMetric I M)
    (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hequiv : ∀ k : ι, ∀ b : M, ∀ v : TangentSpace I b,
      Λ⁻¹ * gBase.inner b v v ≤ (gSeq k).inner b v v ∧
        (gSeq k).inner b v v ≤ Λ * gBase.inner b v v) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        ∀ k : ι, ∀ b ∈ tsupport
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
          ∀ ξ : Fin (Module.finrank ℝ E) → ℝ,
            c * (∑ i : Fin (Module.finrank ℝ E), ξ i ^ 2) ≤
                ∑ i : Fin (Module.finrank ℝ E),
                  ∑ j : Fin (Module.finrank ℝ E),
                    chartInvGramMatrix (I := I) (gSeq k) α b i j * ξ i * ξ j ∧
              (∑ i : Fin (Module.finrank ℝ E),
                  ∑ j : Fin (Module.finrank ℝ E),
                    chartInvGramMatrix (I := I) (gSeq k) α b i j * ξ i * ξ j) ≤
                C * (∑ i : Fin (Module.finrank ℝ E), ξ i ^ 2) := by
  obtain ⟨c, hc, hlower⟩ :=
    chartInvGram_pou_lb (I := I) (M := M) gBase gSeq Λ hΛ hequiv
  obtain ⟨C, hC, hupper⟩ :=
    chartInvGram_pou_ub (I := I) (M := M) gBase gSeq Λ hΛ hequiv
  refine ⟨c, C, hc, hC, ?_⟩
  intro α hα k b hb ξ
  exact ⟨hlower α hα k b hb ξ, hupper α hα k b hb ξ⟩














theorem exists_chartInvGramMatrix_quadForm_lower_bound_on_pouTsupport
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M) :
    ∃ c : ℝ, 0 < c ∧
      ∀ b : M, b ∈ tsupport
          ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) : M → ℝ) →
        ∀ ξ : Fin (Module.finrank ℝ E) → ℝ,
          c * (∑ i : Fin (Module.finrank ℝ E), ξ i ^ 2) ≤
            ∑ i : Fin (Module.finrank ℝ E),
              ∑ j : Fin (Module.finrank ℝ E),
                chartInvGramMatrix (I := I) g α b i j * ξ i * ξ j :=
  exists_chartInvGramMatrix_quadForm_lower_bound_on_compact
    (I := I) (M := M) g α
    (pouTsupport_isCompact (I := I) (M := M) α)
    (pouTsupport_subset_baseSet (I := I) (M := M) α)

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
