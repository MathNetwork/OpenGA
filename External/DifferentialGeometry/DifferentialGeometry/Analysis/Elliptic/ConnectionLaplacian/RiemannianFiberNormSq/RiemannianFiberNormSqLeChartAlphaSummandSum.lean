import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.Defs
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.FiberNormSqSummandChartAlphaBound
import DifferentialGeometry.Analysis.Spectral.Tensor.UniformChartBounds.GramInvUniformEigenvalueLowerBound


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold Set Filter Tensor0SBundle Metric
open scoped Manifold Topology ContDiff ENNReal BigOperators Matrix

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma sphere_isCompact_forward :
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

omit [NeZero (Module.finrank ℝ E)] in
private lemma exists_chartGramMatrix_quadForm_lower_bound_on_compact
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
                chartGramMatrix (I := I) g α b i j * ξ i * ξ j := by
  classical
  set Q : M × (Fin (Module.finrank ℝ E) → ℝ) → ℝ := fun p =>
    ∑ i : Fin (Module.finrank ℝ E),
      ∑ j : Fin (Module.finrank ℝ E),
        chartGramMatrix (I := I) g α p.1 i j * p.2 i * p.2 j
    with hQ_def
  have hQ_pos_baseSet : ∀ b ∈ (trivializationAt E (TangentSpace I) α).baseSet,
      ∀ ξ : Fin (Module.finrank ℝ E) → ℝ, ξ ≠ 0 →
        0 < ∑ i : Fin (Module.finrank ℝ E),
              ∑ j : Fin (Module.finrank ℝ E),
                chartGramMatrix (I := I) g α b i j * ξ i * ξ j := by
    intro b hb ξ hξ
    have hG_pd : (chartGramMatrix (I := I) g α b).PosDef :=
      chartGramMatrix_posDef (I := I) g α hb
    have hdot_pos :
        0 < star ξ ⬝ᵥ chartGramMatrix (I := I) g α b *ᵥ ξ :=
      hG_pd.dotProduct_mulVec_pos hξ
    have hexp :
        star ξ ⬝ᵥ chartGramMatrix (I := I) g α b *ᵥ ξ =
          ∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              chartGramMatrix (I := I) g α b i j * ξ i * ξ j := by
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
      · have hentry := (chartGramMatrix_entry_contMDiffOn
          (I := I) g α i j).continuousOn
        exact hentry.comp continuous_fst.continuousOn (fun p hp => hp.1)
      · exact ((continuous_apply i).comp continuous_snd).continuousOn
    · exact ((continuous_apply j).comp continuous_snd).continuousOn
  set Sph : Set (Fin (Module.finrank ℝ E) → ℝ) :=
    {ξ | ∑ i : Fin (Module.finrank ℝ E), ξ i ^ 2 = 1} with hSph_def
  have hSph_compact : IsCompact Sph := sphere_isCompact_forward (E := E)
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
              chartGramMatrix (I := I) g α b i j * ξ i * ξ j) = 0 := by
        refine Finset.sum_eq_zero (fun i _ => ?_)
        refine Finset.sum_eq_zero (fun j _ => ?_)
        rw [hξzero i, mul_zero, zero_mul]
      rw [hξ_eq, mul_zero, hQzero]
    · have hξ_pos : 0 < ∑ i : Fin (Module.finrank ℝ E), ξ i ^ 2 :=
        lt_of_le_of_ne (Finset.sum_nonneg (fun i _ => sq_nonneg _))
          (Ne.symm hξ_eq)
      set rr : ℝ := Real.sqrt (∑ i : Fin (Module.finrank ℝ E), ξ i ^ 2)
        with hrr_def
      have hrr_pos : 0 < rr := Real.sqrt_pos.mpr hξ_pos
      have hrr_ne : rr ≠ 0 := ne_of_gt hrr_pos
      have hrr_sq : rr ^ 2 = ∑ i, ξ i ^ 2 := by
        rw [hrr_def, sq]; rw [Real.mul_self_sqrt (le_of_lt hξ_pos)]
      set η : Fin (Module.finrank ℝ E) → ℝ := fun i => ξ i / rr with hη_def
      have hη_sph : η ∈ Sph := by
        rw [hSph_def]
        change ∑ i : Fin (Module.finrank ℝ E), η i ^ 2 = 1
        have : ∑ i : Fin (Module.finrank ℝ E), η i ^ 2 =
            (∑ i, ξ i ^ 2) / rr ^ 2 := by
          rw [Finset.sum_div]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [hη_def, div_pow]
        rw [this, hrr_sq]
        exact div_self (ne_of_gt hξ_pos)
      have hbη_mem : (b, η) ∈ K := ⟨hb, hη_sph⟩
      have hmin_le_bη : Q p₀ ≤ Q (b, η) := hp₀_min hbη_mem
      have hQscale :
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              chartGramMatrix (I := I) g α b i j * ξ i * ξ j) =
            rr ^ 2 *
              (∑ i : Fin (Module.finrank ℝ E),
                ∑ j : Fin (Module.finrank ℝ E),
                  chartGramMatrix (I := I) g α b i j * η i * η j) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [hη_def]
        change chartGramMatrix (I := I) g α b i j * ξ i * ξ j =
          rr ^ 2 * (chartGramMatrix (I := I) g α b i j * (ξ i / rr) * (ξ j / rr))
        field_simp
      rw [hQscale]
      have hQη : Q (b, η) =
          ∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              chartGramMatrix (I := I) g α b i j * η i * η j := rfl
      rw [← hQη]
      rw [← hrr_sq, mul_comm]
      exact mul_le_mul_of_nonneg_left hmin_le_bη (sq_nonneg rr)
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

omit [NeZero (Module.finrank ℝ E)] in
private lemma exists_chartGramMatrix_quadForm_lower_bound_on_pouTsupport
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M) :
    ∃ c : ℝ, 0 < c ∧
      ∀ b : M, b ∈ tsupport
          (fun x : M =>
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ∀ ξ : Fin (Module.finrank ℝ E) → ℝ,
          c * (∑ i : Fin (Module.finrank ℝ E), ξ i ^ 2) ≤
            ∑ i : Fin (Module.finrank ℝ E),
              ∑ j : Fin (Module.finrank ℝ E),
                chartGramMatrix (I := I) g α b i j * ξ i * ξ j :=
  exists_chartGramMatrix_quadForm_lower_bound_on_compact
    (I := I) (M := M) g α
    (pouTsupport_isCompact (I := I) (M := M) α)
    (pouTsupport_subset_baseSet (I := I) (M := M) α)

omit [NeZero (Module.finrank ℝ E)] in
private lemma riemannianFiberNormSq_eq_sum_witness_orthonormal
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M)
    (T : TensorRSSpace r s I b) :
    ∃ (n : ℕ) (e : Fin n → TangentSpace I b),
      n = Module.finrank ℝ (TangentSpace I b) ∧
      (∀ i j : Fin n, g.inner b (e i) (e j) =
        if i = j then (1 : ℝ) else 0) ∧
      riemannianFiberNormSq (I := I) (M := M) g r s b T =
        ∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
          fiberNormSqSummand (I := I) (M := M) g b r s T n e K J := by
  classical
  let cd : InnerProductSpace.Core ℝ (TangentSpace I b) := g.toRiemannianMetric.toCore b
  have hc : ContinuousAt (fun v : TangentSpace I b => cd.inner v v) 0 :=
    g.toRiemannianMetric.continuousAt b
  have hb : Bornology.IsVonNBounded ℝ {v : TangentSpace I b |
      RCLike.re (cd.inner v v) < 1} :=
    g.toRiemannianMetric.isVonNBounded b
  letI nag : NormedAddCommGroup (TangentSpace I b) :=
    cd.toNormedAddCommGroupOfTopology hc hb
  letI ips : InnerProductSpace ℝ (TangentSpace I b) :=
    InnerProductSpace.ofCoreOfTopology cd hc hb
  let n : ℕ := Module.finrank ℝ (TangentSpace I b)
  let e : OrthonormalBasis (Fin n) ℝ (TangentSpace I b) := stdOrthonormalBasis ℝ _
  refine ⟨n, fun i => e i, rfl, ?_, ?_⟩
  · intro i j
    have horth : Orthonormal ℝ (fun i : Fin n => e i) := e.orthonormal
    have hite :=
      (orthonormal_iff_ite (𝕜 := ℝ) (E := TangentSpace I b)).mp horth i j
    have h_inner_eq : (inner ℝ (e i) (e j) : ℝ) = g.inner b (e i) (e j) := by
      change cd.inner (e i) (e j) = g.inner b (e i) (e j)
      rfl
    rw [← h_inner_eq]
    exact hite
  · rfl

omit [NeZero (Module.finrank ℝ E)] in
private lemma sum_sq_repr_le_inv_c
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    {c : ℝ} (hc_pos : 0 < c)
    (hG_lower :
      ∀ b : M, b ∈ tsupport
          (fun x : M =>
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ∀ ξ : Fin (Module.finrank ℝ E) → ℝ,
          c * (∑ i : Fin (Module.finrank ℝ E), ξ i ^ 2) ≤
            ∑ i : Fin (Module.finrank ℝ E),
              ∑ j : Fin (Module.finrank ℝ E),
                chartGramMatrix (I := I) g α b i j * ξ i * ξ j)
    {b : M}
    (hb : b ∈ tsupport
        (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x))
    (A : Fin (Module.finrank ℝ E) → ℝ)
    (hA_one :
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          chartGramMatrix (I := I) g α b i j * A i * A j = 1) :
    (∑ i : Fin (Module.finrank ℝ E), A i ^ 2) ≤ 1 / c := by
  have hlower := hG_lower b hb A
  rw [hA_one] at hlower
  have h_div : c * (∑ i : Fin (Module.finrank ℝ E), A i ^ 2) / c ≤ 1 / c :=
    div_le_div_of_nonneg_right hlower (le_of_lt hc_pos) |>.trans_eq rfl
  have h_simpl :
      c * (∑ i : Fin (Module.finrank ℝ E), A i ^ 2) / c =
        ∑ i : Fin (Module.finrank ℝ E), A i ^ 2 := by
    field_simp
  rw [h_simpl] at h_div
  exact h_div

omit [NeZero (Module.finrank ℝ E)] in
private lemma mkPiAlgebra_inner_eK_expand_repr
    (g : SmoothRiemannianMetric I M) (α : M) {b : M}
    (_hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (r : ℕ) {n : ℕ}
    (e : Fin n → TangentSpace I b)
    (K : Fin r → Fin n)
    (A : Fin n → Fin (Module.finrank ℝ E) → ℝ)
    (hA :
      ∀ i : Fin n,
        e i = ∑ j : Fin (Module.finrank ℝ E),
          A i j • chartBasisVecFiber (I := I) α j b) :
    ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin r) ℝ).compContinuousLinearMap
        (fun k : Fin r => g.inner b (e (K k)))) =
      ∑ I' : Fin r → Fin (Module.finrank ℝ E),
        (∏ k : Fin r, A (K k) (I' k)) •
          ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin r) ℝ).compContinuousLinearMap
            (fun k : Fin r =>
              g.inner b (chartBasisVecFiber (I := I) α (I' k) b))) := by
  classical
  refine ContinuousMultilinearMap.ext (fun v => ?_)
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebra_apply]
  have h_each : ∀ k : Fin r,
      g.inner b (e (K k)) (v k) =
        ∑ j : Fin (Module.finrank ℝ E),
          A (K k) j *
            g.inner b (chartBasisVecFiber (I := I) α j b) (v k) := by
    intro k
    rw [hA (K k)]
    rw [map_sum, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  trans (∏ k : Fin r,
        ∑ j : Fin (Module.finrank ℝ E),
          A (K k) j *
            g.inner b (chartBasisVecFiber (I := I) α j b) (v k))
  · exact Finset.prod_congr rfl (fun k _ => h_each k)
  rw [Finset.prod_univ_sum]
  rw [Fintype.piFinset_univ]
  refine Eq.trans ?_ (ContinuousMultilinearMap.sum_apply _ v).symm
  refine Finset.sum_congr rfl ?_
  intro I' _
  change ∏ k, A (K k) (I' k) *
      g.inner b (chartBasisVecFiber (I := I) α (I' k) b) (v k) =
    (∏ k : Fin r, A (K k) (I' k)) •
      (((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin r) ℝ).compContinuousLinearMap
        (fun k : Fin r =>
          g.inner b (chartBasisVecFiber (I := I) α (I' k) b))) v)
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebra_apply, smul_eq_mul]
  rw [← Finset.prod_mul_distrib]

omit [NeZero (Module.finrank ℝ E)] in
private lemma tensor0S_apply_eJ_expand_repr
    {b : M}
    (s : ℕ) {n : ℕ}
    (e : Fin n → TangentSpace I b)
    (α : M)
    (A : Fin n → Fin (Module.finrank ℝ E) → ℝ)
    (hA :
      ∀ i : Fin n,
        e i = ∑ j : Fin (Module.finrank ℝ E),
          A i j • chartBasisVecFiber (I := I) α j b)
    (X : ContinuousMultilinearMap ℝ (fun _ : Fin s => TangentSpace I b) ℝ)
    (J : Fin s → Fin n) :
    X (fun k : Fin s => e (J k)) =
      ∑ J' : Fin s → Fin (Module.finrank ℝ E),
        (∏ l : Fin s, A (J l) (J' l)) *
          X (fun k : Fin s => chartBasisVecFiber (I := I) α (J' k) b) := by
  classical
  have h_eq_fn :
      (fun k : Fin s => e (J k)) =
        fun k : Fin s =>
          ∑ j : Fin (Module.finrank ℝ E),
            A (J k) j • chartBasisVecFiber (I := I) α j b := by
    funext k; exact hA (J k)
  rw [h_eq_fn]
  rw [ContinuousMultilinearMap.map_sum_finset]
  refine Finset.sum_congr rfl ?_
  intro J' _
  rw [ContinuousMultilinearMap.map_smul_univ]
  rw [smul_eq_mul]

omit [NeZero (Module.finrank ℝ E)] in
private lemma fiberNormSqSummand_at_eg_le_chartAlpha_sum
    (g : SmoothRiemannianMetric I M) (r s : ℕ) {b : M}
    (α : M)
    (hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (T : TensorRSSpace r s I b)
    {n : ℕ} (e : Fin n → TangentSpace I b)
    (A : Fin n → Fin (Module.finrank ℝ E) → ℝ)
    (hA :
      ∀ i : Fin n,
        e i = ∑ j : Fin (Module.finrank ℝ E),
          A i j • chartBasisVecFiber (I := I) α j b)
    (K : Fin r → Fin n) (J : Fin s → Fin n) :
    fiberNormSqSummand (I := I) (M := M) g b r s T n e K J ≤
      (∏ k : Fin r,
        ∑ l : Fin (Module.finrank ℝ E), A (K k) l ^ 2) *
      ((∏ l : Fin s,
        ∑ m : Fin (Module.finrank ℝ E), A (J l) m ^ 2) *
        ∑ I' : Fin r → Fin (Module.finrank ℝ E),
          ∑ J' : Fin s → Fin (Module.finrank ℝ E),
            fiberNormSqSummand (I := I) (M := M) g b r s T
              (Module.finrank ℝ E)
              (fun i : Fin (Module.finrank ℝ E) =>
                chartBasisVecFiber (I := I) α i b) I' J') := by
  classical
  have h_cov_expand :=
    mkPiAlgebra_inner_eK_expand_repr (I := I) (M := M) g α hb_base r e K A hA
  have h_T_apply :
      (T : Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b)
        ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin r) ℝ).compContinuousLinearMap
          (fun k : Fin r => g.inner b (e (K k)))) =
        ∑ I' : Fin r → Fin (Module.finrank ℝ E),
          (∏ k : Fin r, A (K k) (I' k)) •
            (T : Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b)
              ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin r) ℝ).compContinuousLinearMap
                (fun k : Fin r =>
                  g.inner b (chartBasisVecFiber (I := I) α (I' k) b))) := by
    rw [h_cov_expand, map_sum]
    refine Finset.sum_congr rfl ?_
    intro I' _
    rw [map_smul]
  set XKJ : ℝ :=
    (((T : Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b)
        ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin r) ℝ).compContinuousLinearMap
          (fun k : Fin r => g.inner b (e (K k))))) :
        ContinuousMultilinearMap ℝ (fun _ : Fin s => TangentSpace I b) ℝ)
      (fun k : Fin s => e (J k)) with hXKJ_def
  have h_XKJ_eq :
      XKJ =
        ∑ I' : Fin r → Fin (Module.finrank ℝ E),
          ∑ J' : Fin s → Fin (Module.finrank ℝ E),
            (∏ k : Fin r, A (K k) (I' k)) *
              ((∏ l : Fin s, A (J l) (J' l)) *
                (((T : Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b)
                    ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin r) ℝ).compContinuousLinearMap
                      (fun k : Fin r =>
                        g.inner b (chartBasisVecFiber (I := I) α (I' k) b)))) :
                    ContinuousMultilinearMap ℝ (fun _ : Fin s => TangentSpace I b) ℝ)
                  (fun k : Fin s => chartBasisVecFiber (I := I) α (J' k) b)) := by
    rw [hXKJ_def, h_T_apply]
    rw [ContinuousMultilinearMap.sum_apply]
    refine Finset.sum_congr rfl ?_
    intro I' _
    rw [ContinuousMultilinearMap.smul_apply, smul_eq_mul]
    rw [tensor0S_apply_eJ_expand_repr (I := I) (M := M) (s := s) e α A hA _ J]
    rw [Finset.mul_sum]
  set Yfn : (Fin r → Fin (Module.finrank ℝ E)) × (Fin s → Fin (Module.finrank ℝ E)) → ℝ :=
    fun p =>
      (((T : Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b)
        ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin r) ℝ).compContinuousLinearMap
          (fun k : Fin r =>
            g.inner b (chartBasisVecFiber (I := I) α (p.1 k) b)))) :
          ContinuousMultilinearMap ℝ (fun _ : Fin s => TangentSpace I b) ℝ)
        (fun k : Fin s => chartBasisVecFiber (I := I) α (p.2 k) b)
    with hYfn_def
  set αfn : (Fin r → Fin (Module.finrank ℝ E)) × (Fin s → Fin (Module.finrank ℝ E)) → ℝ :=
    fun p =>
      (∏ k : Fin r, A (K k) (p.1 k)) * (∏ l : Fin s, A (J l) (p.2 l))
    with hαfn_def
  have h_XKJ_as_sum :
      XKJ =
        ∑ p : (Fin r → Fin (Module.finrank ℝ E)) × (Fin s → Fin (Module.finrank ℝ E)),
          αfn p * Yfn p := by
    rw [h_XKJ_eq]
    rw [show (Finset.univ : Finset ((Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)))) =
          (Finset.univ : Finset (Fin r → Fin (Module.finrank ℝ E))) ×ˢ
          (Finset.univ : Finset (Fin s → Fin (Module.finrank ℝ E))) from
        (Finset.univ_product_univ).symm]
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl ?_
    intro I' _
    refine Finset.sum_congr rfl ?_
    intro J' _
    change (∏ k : Fin r, A (K k) (I' k)) *
        ((∏ l : Fin s, A (J l) (J' l)) * Yfn (I', J')) =
      αfn (I', J') * Yfn (I', J')
    rw [hαfn_def]
    ring
  have h_CS :
      XKJ ^ 2 ≤
        (∑ p : (Fin r → Fin (Module.finrank ℝ E)) × (Fin s → Fin (Module.finrank ℝ E)),
          αfn p ^ 2) *
        (∑ p : (Fin r → Fin (Module.finrank ℝ E)) × (Fin s → Fin (Module.finrank ℝ E)),
          Yfn p ^ 2) := by
    rw [h_XKJ_as_sum]
    exact Finset.sum_mul_sq_le_sq_mul_sq (R := ℝ) _ αfn Yfn
  have h_α_sq_split :
      (∑ p : (Fin r → Fin (Module.finrank ℝ E)) × (Fin s → Fin (Module.finrank ℝ E)),
        αfn p ^ 2) =
        (∑ I' : Fin r → Fin (Module.finrank ℝ E),
          (∏ k : Fin r, A (K k) (I' k)) ^ 2) *
        (∑ J' : Fin s → Fin (Module.finrank ℝ E),
          (∏ l : Fin s, A (J l) (J' l)) ^ 2) := by
    have h_expand :
        (∑ p : (Fin r → Fin (Module.finrank ℝ E)) × (Fin s → Fin (Module.finrank ℝ E)),
          αfn p ^ 2) =
          ∑ I' : Fin r → Fin (Module.finrank ℝ E),
            ∑ J' : Fin s → Fin (Module.finrank ℝ E),
              ((∏ k : Fin r, A (K k) (I' k)) ^ 2) *
              ((∏ l : Fin s, A (J l) (J' l)) ^ 2) := by
      rw [show (Finset.univ : Finset ((Fin r → Fin (Module.finrank ℝ E)) ×
              (Fin s → Fin (Module.finrank ℝ E)))) =
            (Finset.univ : Finset (Fin r → Fin (Module.finrank ℝ E))) ×ˢ
            (Finset.univ : Finset (Fin s → Fin (Module.finrank ℝ E))) from
          (Finset.univ_product_univ).symm]
      rw [Finset.sum_product]
      refine Finset.sum_congr rfl ?_
      intro I' _
      refine Finset.sum_congr rfl ?_
      intro J' _
      rw [hαfn_def, mul_pow]
    rw [h_expand]
    rw [Finset.sum_mul_sum]
  have h_prod_sum_K :
      ∑ I' : Fin r → Fin (Module.finrank ℝ E),
        (∏ k : Fin r, A (K k) (I' k)) ^ 2 =
      ∏ k : Fin r, ∑ l : Fin (Module.finrank ℝ E), A (K k) l ^ 2 := by
    have h_each : ∀ I' : Fin r → Fin (Module.finrank ℝ E),
        (∏ k : Fin r, A (K k) (I' k)) ^ 2 =
          ∏ k : Fin r, (A (K k) (I' k)) ^ 2 := by
      intro I'
      rw [← Finset.prod_pow]
    have h_sum_prod :
        ∑ I' : Fin r → Fin (Module.finrank ℝ E),
          ∏ k : Fin r, (A (K k) (I' k)) ^ 2 =
        ∏ k : Fin r, ∑ l : Fin (Module.finrank ℝ E), A (K k) l ^ 2 := by
      rw [show ∏ k : Fin r, ∑ l : Fin (Module.finrank ℝ E), A (K k) l ^ 2 =
          ∑ I' ∈ Fintype.piFinset (fun _ : Fin r =>
              (Finset.univ : Finset (Fin (Module.finrank ℝ E)))),
            ∏ k : Fin r, (A (K k) (I' k)) ^ 2 from
        Finset.prod_univ_sum _ _]
      rw [Fintype.piFinset_univ]
    calc ∑ I' : Fin r → Fin (Module.finrank ℝ E),
            (∏ k : Fin r, A (K k) (I' k)) ^ 2
        = ∑ I' : Fin r → Fin (Module.finrank ℝ E),
            ∏ k : Fin r, (A (K k) (I' k)) ^ 2 :=
          Finset.sum_congr rfl (fun I' _ => h_each I')
      _ = ∏ k : Fin r, ∑ l : Fin (Module.finrank ℝ E), A (K k) l ^ 2 := h_sum_prod
  have h_prod_sum_J :
      ∑ J' : Fin s → Fin (Module.finrank ℝ E),
        (∏ l : Fin s, A (J l) (J' l)) ^ 2 =
      ∏ l : Fin s, ∑ m : Fin (Module.finrank ℝ E), A (J l) m ^ 2 := by
    have h_each : ∀ J' : Fin s → Fin (Module.finrank ℝ E),
        (∏ l : Fin s, A (J l) (J' l)) ^ 2 =
          ∏ l : Fin s, (A (J l) (J' l)) ^ 2 := by
      intro J'
      rw [← Finset.prod_pow]
    have h_sum_prod :
        ∑ J' : Fin s → Fin (Module.finrank ℝ E),
          ∏ l : Fin s, (A (J l) (J' l)) ^ 2 =
        ∏ l : Fin s, ∑ m : Fin (Module.finrank ℝ E), A (J l) m ^ 2 := by
      rw [show ∏ l : Fin s, ∑ m : Fin (Module.finrank ℝ E), A (J l) m ^ 2 =
          ∑ J' ∈ Fintype.piFinset (fun _ : Fin s =>
              (Finset.univ : Finset (Fin (Module.finrank ℝ E)))),
            ∏ l : Fin s, (A (J l) (J' l)) ^ 2 from
        Finset.prod_univ_sum _ _]
      rw [Fintype.piFinset_univ]
    calc ∑ J' : Fin s → Fin (Module.finrank ℝ E),
            (∏ l : Fin s, A (J l) (J' l)) ^ 2
        = ∑ J' : Fin s → Fin (Module.finrank ℝ E),
            ∏ l : Fin s, (A (J l) (J' l)) ^ 2 :=
          Finset.sum_congr rfl (fun J' _ => h_each J')
      _ = ∏ l : Fin s, ∑ m : Fin (Module.finrank ℝ E), A (J l) m ^ 2 := h_sum_prod
  rw [h_prod_sum_K, h_prod_sum_J] at h_α_sq_split
  rw [h_α_sq_split] at h_CS
  have h_Y_sum_split :
      (∑ p : (Fin r → Fin (Module.finrank ℝ E)) × (Fin s → Fin (Module.finrank ℝ E)),
        Yfn p ^ 2) =
        ∑ I' : Fin r → Fin (Module.finrank ℝ E),
          ∑ J' : Fin s → Fin (Module.finrank ℝ E),
            Yfn (I', J') ^ 2 := by
    rw [← Finset.univ_product_univ]
    rw [Finset.sum_product]
  rw [h_Y_sum_split] at h_CS
  have h_Y_eq_summand :
      ∀ I' : Fin r → Fin (Module.finrank ℝ E),
        ∀ J' : Fin s → Fin (Module.finrank ℝ E),
          Yfn (I', J') ^ 2 =
            fiberNormSqSummand (I := I) (M := M) g b r s T
              (Module.finrank ℝ E)
              (fun i : Fin (Module.finrank ℝ E) =>
                chartBasisVecFiber (I := I) α i b) I' J' := by
    intro I' J'
    rw [hYfn_def]
    rfl
  have h_Y_double_eq :
      (∑ I' : Fin r → Fin (Module.finrank ℝ E),
        ∑ J' : Fin s → Fin (Module.finrank ℝ E), Yfn (I', J') ^ 2) =
        ∑ I' : Fin r → Fin (Module.finrank ℝ E),
          ∑ J' : Fin s → Fin (Module.finrank ℝ E),
            fiberNormSqSummand (I := I) (M := M) g b r s T
              (Module.finrank ℝ E)
              (fun i : Fin (Module.finrank ℝ E) =>
                chartBasisVecFiber (I := I) α i b) I' J' := by
    refine Finset.sum_congr rfl (fun I' _ => ?_)
    refine Finset.sum_congr rfl (fun J' _ => ?_)
    exact h_Y_eq_summand I' J'
  rw [h_Y_double_eq] at h_CS
  have h_target_eq :
      fiberNormSqSummand (I := I) (M := M) g b r s T n e K J = XKJ ^ 2 := by
    unfold fiberNormSqSummand
    rfl
  rw [h_target_eq]
  have hgoal_eq :
      (∏ k : Fin r, ∑ l : Fin (Module.finrank ℝ E), A (K k) l ^ 2) *
        ((∏ l : Fin s, ∑ m : Fin (Module.finrank ℝ E), A (J l) m ^ 2) *
          ∑ I' : Fin r → Fin (Module.finrank ℝ E),
            ∑ J' : Fin s → Fin (Module.finrank ℝ E),
              fiberNormSqSummand (I := I) (M := M) g b r s T
                (Module.finrank ℝ E)
                (fun i : Fin (Module.finrank ℝ E) =>
                  chartBasisVecFiber (I := I) α i b) I' J') =
        (∏ k : Fin r, ∑ l : Fin (Module.finrank ℝ E), A (K k) l ^ 2) *
          (∏ l : Fin s, ∑ m : Fin (Module.finrank ℝ E), A (J l) m ^ 2) *
          ∑ I' : Fin r → Fin (Module.finrank ℝ E),
            ∑ J' : Fin s → Fin (Module.finrank ℝ E),
              fiberNormSqSummand (I := I) (M := M) g b r s T
                (Module.finrank ℝ E)
                (fun i : Fin (Module.finrank ℝ E) =>
                  chartBasisVecFiber (I := I) α i b) I' J' := by ring
  rw [hgoal_eq]
  exact h_CS

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] in
private lemma finrank_tangentSpace_eq (b : M) :
    Module.finrank ℝ (TangentSpace I b) = Module.finrank ℝ E := rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem riemannianFiberNormSq_le_chartAlpha_summand_sum_on_pouTsupport
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g r s),
        ∀ {b : M},
          b ∈ tsupport (fun x : M =>
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
          riemannianFiberNormSq (I := I) (M := M) g r s b (S.toSection b) ≤
            C *
              (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
                ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
                  fiberNormSqSummand (I := I) (M := M) g b r s (S.toSection b)
                    (Module.finrank ℝ E)
                    (fun i : Fin (Module.finrank ℝ E) =>
                      chartBasisVecFiber (I := I) α i b)
                    Idx Jdx) := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn_def
  obtain ⟨c, hc_pos, hG_lower⟩ :=
    exists_chartGramMatrix_quadForm_lower_bound_on_pouTsupport (I := I) (M := M) g α
  set C : ℝ := (n : ℝ) ^ r * (n : ℝ) ^ s * ((1 : ℝ) / c) ^ (r + s) with hC_def
  have hcinv_nn : 0 ≤ (1 : ℝ) / c := by
    refine div_nonneg ?_ (le_of_lt hc_pos)
    exact zero_le_one
  have hcinv_pow_nn : 0 ≤ ((1 : ℝ) / c) ^ (r + s) := pow_nonneg hcinv_nn _
  have hn_pow_r_nn : 0 ≤ (n : ℝ) ^ r := pow_nonneg (Nat.cast_nonneg n) r
  have hn_pow_s_nn : 0 ≤ (n : ℝ) ^ s := pow_nonneg (Nat.cast_nonneg n) s
  have hC_nonneg : 0 ≤ C := by
    rw [hC_def]
    exact mul_nonneg (mul_nonneg hn_pow_r_nn hn_pow_s_nn) hcinv_pow_nn
  refine ⟨C, hC_nonneg, ?_⟩
  intro S b hb
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    have hsub :
        tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ⊆
        (trivializationAt E (TangentSpace I) α).baseSet :=
      pouTsupport_subset_baseSet (I := I) (M := M) α
    exact hsub hb
  obtain ⟨n', e, hn', he_orth, h_eq⟩ :=
    riemannianFiberNormSq_eq_sum_witness_orthonormal (I := I) (M := M)
      g r s b (S.toSection b)
  subst hn'
  set Bfam := chartBasisFamily (I := I) α hb_base with hBfam_def
  set A : Fin (Module.finrank ℝ (TangentSpace I b)) → Fin (Module.finrank ℝ E) → ℝ :=
    fun i j => Bfam.repr (e i) j with hA_def
  have hA_expand :
      ∀ i : Fin (Module.finrank ℝ (TangentSpace I b)),
        e i = ∑ j : Fin (Module.finrank ℝ E),
          A i j • chartBasisVecFiber (I := I) α j b := by
    intro i
    have h := Bfam.sum_repr (e i)
    have hBfam_apply : ∀ j : Fin (Module.finrank ℝ E),
        Bfam j = chartBasisVecFiber (I := I) α j b := by
      intro j
      rw [hBfam_def]
      exact chartBasisFamily_apply (I := I) α hb_base j
    rw [← h]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hA_def, hBfam_apply j]
  have hA_sumsq_le : ∀ i : Fin (Module.finrank ℝ (TangentSpace I b)),
      (∑ j : Fin (Module.finrank ℝ E), A i j ^ 2) ≤ 1 / c := by
    intro i
    have h_one : g.inner b (e i) (e i) = 1 := by
      have := he_orth i i
      rw [if_pos rfl] at this
      exact this
    have h_expand_inner :
        g.inner b (e i) (e i) =
          ∑ j : Fin (Module.finrank ℝ E),
            ∑ k : Fin (Module.finrank ℝ E),
              chartGramMatrix (I := I) g α b j k * A i j * A i k := by
      have h_ei : e i = ∑ j : Fin (Module.finrank ℝ E),
          A i j • chartBasisVecFiber (I := I) α j b := hA_expand i
      rw [h_ei]
      have hdotmul := chartGramMatrix_dotProduct_mulVec (I := I) g α b (A i)
      rw [← hdotmul]
      simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      ring
    have hA_one :
        ∑ j : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            chartGramMatrix (I := I) g α b j k * A i j * A i k = 1 := by
      rw [← h_expand_inner]; exact h_one
    exact sum_sq_repr_le_inv_c (I := I) (M := M) g α hc_pos hG_lower hb (A i) hA_one
  rw [h_eq]
  have h_inner_sum_nn :
      0 ≤ ∑ I' : Fin r → Fin (Module.finrank ℝ E),
        ∑ J' : Fin s → Fin (Module.finrank ℝ E),
          fiberNormSqSummand (I := I) (M := M) g b r s (S.toSection b)
            (Module.finrank ℝ E)
            (fun i : Fin (Module.finrank ℝ E) =>
              chartBasisVecFiber (I := I) α i b) I' J' := by
    refine Finset.sum_nonneg ?_
    intro I' _
    refine Finset.sum_nonneg ?_
    intro J' _
    exact fiberNormSqSummand_nonneg (I := I) (M := M) g b r s _ _ _ I' J'
  set RHSinner : ℝ :=
    ∑ I' : Fin r → Fin (Module.finrank ℝ E),
      ∑ J' : Fin s → Fin (Module.finrank ℝ E),
        fiberNormSqSummand (I := I) (M := M) g b r s (S.toSection b)
          (Module.finrank ℝ E)
          (fun i : Fin (Module.finrank ℝ E) =>
            chartBasisVecFiber (I := I) α i b) I' J'
    with hRHSinner_def
  have h_per_KJ :
      ∀ K : Fin r → Fin (Module.finrank ℝ (TangentSpace I b)),
        ∀ J : Fin s → Fin (Module.finrank ℝ (TangentSpace I b)),
          fiberNormSqSummand (I := I) (M := M) g b r s (S.toSection b)
              (Module.finrank ℝ (TangentSpace I b)) e K J ≤
            ((1 : ℝ) / c) ^ r * ((1 : ℝ) / c) ^ s * RHSinner := by
    intro K J
    have h_per :=
      fiberNormSqSummand_at_eg_le_chartAlpha_sum (I := I) (M := M)
        g r s α hb_base (S.toSection b) e A hA_expand K J
    have h_prod_K_le :
        (∏ k : Fin r,
          ∑ l : Fin (Module.finrank ℝ E), A (K k) l ^ 2) ≤ ((1 : ℝ) / c) ^ r := by
      have h_nn_k : ∀ k : Fin r, 0 ≤ ∑ l : Fin (Module.finrank ℝ E), A (K k) l ^ 2 := by
        intro k
        exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      have h_per_k : ∀ k : Fin r,
          (∑ l : Fin (Module.finrank ℝ E), A (K k) l ^ 2) ≤ 1 / c :=
        fun k => hA_sumsq_le (K k)
      have h_prod_le :
          ∏ k : Fin r, ∑ l : Fin (Module.finrank ℝ E), A (K k) l ^ 2 ≤
            ∏ _k : Fin r, ((1 : ℝ) / c) :=
        Finset.prod_le_prod (fun k _ => h_nn_k k) (fun k _ => h_per_k k)
      have h_const_prod : (∏ _k : Fin r, ((1 : ℝ) / c)) = ((1 : ℝ) / c) ^ r := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [h_const_prod] at h_prod_le
      exact h_prod_le
    have h_prod_J_le :
        (∏ l : Fin s,
          ∑ m : Fin (Module.finrank ℝ E), A (J l) m ^ 2) ≤ ((1 : ℝ) / c) ^ s := by
      have h_nn_l : ∀ l : Fin s, 0 ≤ ∑ m : Fin (Module.finrank ℝ E), A (J l) m ^ 2 := by
        intro l
        exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      have h_per_l : ∀ l : Fin s,
          (∑ m : Fin (Module.finrank ℝ E), A (J l) m ^ 2) ≤ 1 / c :=
        fun l => hA_sumsq_le (J l)
      have h_prod_le :
          ∏ l : Fin s, ∑ m : Fin (Module.finrank ℝ E), A (J l) m ^ 2 ≤
            ∏ _l : Fin s, ((1 : ℝ) / c) :=
        Finset.prod_le_prod (fun l _ => h_nn_l l) (fun l _ => h_per_l l)
      have h_const_prod : (∏ _l : Fin s, ((1 : ℝ) / c)) = ((1 : ℝ) / c) ^ s := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [h_const_prod] at h_prod_le
      exact h_prod_le
    have h_prod_J_sum_nn :
        0 ≤ (∏ l : Fin s,
          ∑ m : Fin (Module.finrank ℝ E), A (J l) m ^ 2) * RHSinner := by
      refine mul_nonneg ?_ h_inner_sum_nn
      exact Finset.prod_nonneg (fun l _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    have hb1 :
        (∏ k : Fin r,
          ∑ l : Fin (Module.finrank ℝ E), A (K k) l ^ 2) *
        ((∏ l : Fin s,
          ∑ m : Fin (Module.finrank ℝ E), A (J l) m ^ 2) * RHSinner) ≤
          ((1 : ℝ) / c) ^ r *
          ((∏ l : Fin s,
            ∑ m : Fin (Module.finrank ℝ E), A (J l) m ^ 2) * RHSinner) :=
      mul_le_mul_of_nonneg_right h_prod_K_le h_prod_J_sum_nn
    have hcinv_pow_r_nn : 0 ≤ ((1 : ℝ) / c) ^ r := pow_nonneg hcinv_nn r
    have hb2 :
        ((1 : ℝ) / c) ^ r *
          ((∏ l : Fin s,
            ∑ m : Fin (Module.finrank ℝ E), A (J l) m ^ 2) * RHSinner) ≤
          ((1 : ℝ) / c) ^ r * (((1 : ℝ) / c) ^ s * RHSinner) := by
      refine mul_le_mul_of_nonneg_left ?_ hcinv_pow_r_nn
      exact mul_le_mul_of_nonneg_right h_prod_J_le h_inner_sum_nn
    have h_combined :
        fiberNormSqSummand (I := I) (M := M) g b r s (S.toSection b)
            (Module.finrank ℝ (TangentSpace I b)) e K J ≤
          ((1 : ℝ) / c) ^ r * (((1 : ℝ) / c) ^ s * RHSinner) :=
      (h_per.trans hb1).trans hb2
    have h_alg :
        ((1 : ℝ) / c) ^ r * (((1 : ℝ) / c) ^ s * RHSinner) =
          ((1 : ℝ) / c) ^ r * ((1 : ℝ) / c) ^ s * RHSinner := by ring
    rw [h_alg] at h_combined
    exact h_combined
  have h_sum_le :
      (∑ K : Fin r → Fin (Module.finrank ℝ (TangentSpace I b)),
          ∑ J : Fin s → Fin (Module.finrank ℝ (TangentSpace I b)),
            fiberNormSqSummand (I := I) (M := M) g b r s (S.toSection b)
              (Module.finrank ℝ (TangentSpace I b)) e K J) ≤
        ∑ K : Fin r → Fin (Module.finrank ℝ (TangentSpace I b)),
          ∑ _J : Fin s → Fin (Module.finrank ℝ (TangentSpace I b)),
            ((1 : ℝ) / c) ^ r * ((1 : ℝ) / c) ^ s * RHSinner := by
    refine Finset.sum_le_sum (fun K _ => ?_)
    refine Finset.sum_le_sum (fun J _ => ?_)
    exact h_per_KJ K J
  refine h_sum_le.trans ?_
  set nt : ℕ := Module.finrank ℝ (TangentSpace I b) with hnt_def
  have hnt_eq_n : nt = n := by
    rw [hnt_def, hn_def]
    rfl
  have h_card_K : (Finset.univ : Finset (Fin r → Fin nt)).card = nt ^ r := by
    rw [Finset.card_univ]
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  have h_card_J : (Finset.univ : Finset (Fin s → Fin nt)).card = nt ^ s := by
    rw [Finset.card_univ]
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  have h_inner_const :
      ∀ _K : Fin r → Fin nt,
        (∑ _J : Fin s → Fin nt,
          ((1 : ℝ) / c) ^ r * ((1 : ℝ) / c) ^ s * RHSinner) =
        ((nt ^ s : ℕ) : ℝ) * (((1 : ℝ) / c) ^ r * ((1 : ℝ) / c) ^ s * RHSinner) := by
    intro _K
    rw [Finset.sum_const, h_card_J]
    rw [nsmul_eq_mul]
  have h_outer_const :
      (∑ _K : Fin r → Fin nt,
        ((nt ^ s : ℕ) : ℝ) * (((1 : ℝ) / c) ^ r * ((1 : ℝ) / c) ^ s * RHSinner)) =
      ((nt ^ r : ℕ) : ℝ) *
        (((nt ^ s : ℕ) : ℝ) * (((1 : ℝ) / c) ^ r * ((1 : ℝ) / c) ^ s * RHSinner)) := by
    rw [Finset.sum_const, h_card_K]
    rw [nsmul_eq_mul]
  have h_rhs_compute :
      (∑ _K : Fin r → Fin nt,
        ∑ _J : Fin s → Fin nt,
          ((1 : ℝ) / c) ^ r * ((1 : ℝ) / c) ^ s * RHSinner) =
      ((nt ^ r : ℕ) : ℝ) *
        (((nt ^ s : ℕ) : ℝ) * (((1 : ℝ) / c) ^ r * ((1 : ℝ) / c) ^ s * RHSinner)) := by
    have h_inner_eq :
        (∑ _K : Fin r → Fin nt,
          ∑ _J : Fin s → Fin nt,
            ((1 : ℝ) / c) ^ r * ((1 : ℝ) / c) ^ s * RHSinner) =
        ∑ _K : Fin r → Fin nt,
          ((nt ^ s : ℕ) : ℝ) * (((1 : ℝ) / c) ^ r * ((1 : ℝ) / c) ^ s * RHSinner) :=
      Finset.sum_congr rfl (fun K _ => h_inner_const K)
    rw [h_inner_eq, h_outer_const]
  rw [hnt_eq_n] at h_rhs_compute
  have h_final_alg :
      ((n ^ r : ℕ) : ℝ) *
        (((n ^ s : ℕ) : ℝ) *
          (((1 : ℝ) / c) ^ r * ((1 : ℝ) / c) ^ s * RHSinner)) =
        C * RHSinner := by
    rw [hC_def]
    push_cast
    have hpow_split : ((1 : ℝ) / c) ^ (r + s) = ((1 : ℝ) / c) ^ r * ((1 : ℝ) / c) ^ s :=
      pow_add _ _ _
    rw [hpow_split]
    ring
  exact le_of_eq (h_rhs_compute.trans h_final_alg)

end Connection
end Integral
end DifferentialGeometry

end
