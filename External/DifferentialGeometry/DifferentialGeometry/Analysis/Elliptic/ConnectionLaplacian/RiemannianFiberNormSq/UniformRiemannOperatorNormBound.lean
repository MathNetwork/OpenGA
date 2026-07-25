import DifferentialGeometry.Geometry.Connection.ChartBridge.RiemannBasisIdentityOffCentre
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartFiberTrivialisationOpNorm.ChartRiemannDataUniformBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.ChartGramMatrixQuadFormUpperBound
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.ChartGeometry.GoodSetMeasure
import DifferentialGeometry.Analysis.Integration.Measure.Rellich
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Topology.Order.Compact


noncomputable section

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]


omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma metric_inner_self_nonneg
    (g : SmoothRiemannianMetric I M) (x : M) (v : TangentSpace I x) :
    0 ≤ g.inner x v v := by
  rcases eq_or_ne v 0 with hv0 | hv0
  · rw [hv0]; simp
  · exact (g.pos x v hv0).le


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] in
private lemma pouTsupport_subset_goodSet (α : M) :
    tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ⊆
      chartLeviCivitaGoodSet (I := I) α := by
  intro b hb
  have heq : chartLeviCivitaGoodSet (I := I) α = (chartAt H α).source := by
    rw [DifferentialGeometry.Integral.Connection.chartLeviCivitaGoodSet_eq_extChartAt_source
          (I := I) α]
    exact extChartAt_source_eq_chartAt_source (I := I) α
  rw [heq]
  exact chartAtlasPOU_isSubordinate I M α hb

omit [BoundarylessManifold I M] in
theorem exists_chartGramMatrix_quadForm_lower_bound_on_pouTsupport
    (g : SmoothRiemannianMetric I M) (α : M) :
    ∃ c : ℝ, 0 < c ∧
      ∀ b ∈ tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x),
        ∀ ξ : Fin (Module.finrank ℝ E) → ℝ,
          c * (∑ i : Fin (Module.finrank ℝ E), ξ i ^ 2) ≤
            ∑ i : Fin (Module.finrank ℝ E),
              ∑ j : Fin (Module.finrank ℝ E),
                chartGramMatrix (I := I) g α b i j * ξ i * ξ j := by
  classical
  set Kα : Set M := tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) with hKα_def
  have hKα_compact : IsCompact Kα :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.pouTsupport_isCompact (I := I) (M := M) α
  have hKα_sub_baseSet : Kα ⊆ (trivializationAt E (TangentSpace I) α).baseSet := by
    intro b hb
    exact chartLeviCivitaGoodSet_mem_baseSet (I := I) (pouTsupport_subset_goodSet (I := I) α hb)
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
  have hSph_compact : IsCompact Sph := by
    have hcont : Continuous
        (fun ξ : Fin (Module.finrank ℝ E) → ℝ =>
          ∑ i : Fin (Module.finrank ℝ E), ξ i ^ 2) :=
      continuous_finset_sum _ (fun i _ => (continuous_apply i).pow 2)
    have hclosed : IsClosed Sph := isClosed_eq hcont continuous_const
    have hbdd : Bornology.IsBounded Sph := by
      refine (Metric.isBounded_iff_subset_closedBall (0 : _)).mpr ⟨1, ?_⟩
      intro ξ hξ
      rw [Metric.mem_closedBall, dist_zero_right]
      refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr ?_
      intro i
      have hle : ξ i ^ 2 ≤ ∑ j : Fin (Module.finrank ℝ E), ξ j ^ 2 := by
        refine Finset.single_le_sum (s := Finset.univ)
          (f := fun j : Fin (Module.finrank ℝ E) => ξ j ^ 2) (fun j _ => sq_nonneg _)
          (Finset.mem_univ i)
      rw [show ∑ j : Fin (Module.finrank ℝ E), ξ j ^ 2 = 1 from hξ] at hle
      have habs : |ξ i| ≤ 1 := by
        have h_abs_sq : |ξ i| ^ 2 ≤ 1 := by rw [sq_abs]; exact hle
        nlinarith [abs_nonneg (ξ i), h_abs_sq]
      exact (Real.norm_eq_abs _).symm ▸ habs
    exact Metric.isCompact_of_isClosed_isBounded hclosed hbdd
  set Kprod : Set (M × (Fin (Module.finrank ℝ E) → ℝ)) := Kα ×ˢ Sph with hKprod_def
  have hKprod_compact : IsCompact Kprod := hKα_compact.prod hSph_compact
  have hKprod_sub_baseSet :
      Kprod ⊆ (trivializationAt E (TangentSpace I) α).baseSet ×ˢ Set.univ :=
    fun p hp => ⟨hKα_sub_baseSet hp.1, mem_univ _⟩
  have hQ_cont_K : ContinuousOn Q Kprod := hQ_cont.mono hKprod_sub_baseSet
  have hSph_ne_zero : ∀ ξ ∈ Sph, ξ ≠ 0 := by
    intro ξ hξ hξ0
    have : (1 : ℝ) = 0 := by
      rw [show (1 : ℝ) = ∑ i : Fin (Module.finrank ℝ E), ξ i ^ 2 from hξ.symm, hξ0]; simp
    exact one_ne_zero this
  by_cases hK_ne : Kprod.Nonempty
  · obtain ⟨p₀, hp₀_mem, hp₀_min⟩ :=
      hKprod_compact.exists_isMinOn hK_ne hQ_cont_K
    have hp₀_base : p₀.1 ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
      hKα_sub_baseSet hp₀_mem.1
    have hp₀_pos : 0 < Q p₀ :=
      hQ_pos_baseSet p₀.1 hp₀_base p₀.2 (hSph_ne_zero p₀.2 hp₀_mem.2)
    refine ⟨Q p₀, hp₀_pos, ?_⟩
    intro b hb ξ
    by_cases hξ_eq : (∑ i : Fin (Module.finrank ℝ E), ξ i ^ 2) = 0
    · have hξzero : ∀ i, ξ i = 0 := by
        intro i
        have hle : ξ i ^ 2 ≤ ∑ j : Fin (Module.finrank ℝ E), ξ j ^ 2 :=
          Finset.single_le_sum (s := Finset.univ)
            (f := fun j : Fin (Module.finrank ℝ E) => ξ j ^ 2)
            (fun j _ => sq_nonneg _) (Finset.mem_univ i)
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
        lt_of_le_of_ne (Finset.sum_nonneg (fun i _ => sq_nonneg _)) (Ne.symm hξ_eq)
      set rr : ℝ := Real.sqrt (∑ i : Fin (Module.finrank ℝ E), ξ i ^ 2) with hrr_def
      have hrr_pos : 0 < rr := Real.sqrt_pos.mpr hξ_pos
      have hrr_sq : rr ^ 2 = ∑ i, ξ i ^ 2 := by
        rw [hrr_def, sq, Real.mul_self_sqrt (le_of_lt hξ_pos)]
      set η : Fin (Module.finrank ℝ E) → ℝ := fun i => ξ i / rr with hη_def
      have hη_sph : η ∈ Sph := by
        rw [hSph_def]
        change ∑ i : Fin (Module.finrank ℝ E), η i ^ 2 = 1
        have hcalc : ∑ i : Fin (Module.finrank ℝ E), η i ^ 2 =
            (∑ i, ξ i ^ 2) / rr ^ 2 := by
          rw [Finset.sum_div]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [hη_def, div_pow]
        rw [hcalc, hrr_sq, div_self (ne_of_gt hξ_pos)]
      have hηmem : (b, η) ∈ Kprod := ⟨hb, hη_sph⟩
      have hmin : Q p₀ ≤ Q (b, η) := hp₀_min hηmem
      have hQη_eq : Q (b, η) =
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              chartGramMatrix (I := I) g α b i j * ξ i * ξ j) / rr ^ 2 := by
        change (∑ i : Fin (Module.finrank ℝ E),
              ∑ j : Fin (Module.finrank ℝ E),
                chartGramMatrix (I := I) g α b i j * η i * η j) =
            (∑ i : Fin (Module.finrank ℝ E),
              ∑ j : Fin (Module.finrank ℝ E),
                chartGramMatrix (I := I) g α b i j * ξ i * ξ j) / rr ^ 2
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [hη_def]
        field_simp
      rw [hQη_eq] at hmin
      have hrrsq_pos : 0 < rr ^ 2 := by rw [hrr_sq]; exact hξ_pos
      have hmul : Q p₀ * rr ^ 2 ≤
          ∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              chartGramMatrix (I := I) g α b i j * ξ i * ξ j :=
        (le_div_iff₀ hrrsq_pos).mp hmin
      have hgoal_eq : Q p₀ * (∑ i : Fin (Module.finrank ℝ E), ξ i ^ 2)
          = Q p₀ * rr ^ 2 := by rw [hrr_sq]
      rw [hgoal_eq]
      exact hmul
  · refine ⟨1, one_pos, ?_⟩
    intro b hb
    have hSph_ne : Sph.Nonempty := by
      refine ⟨fun i => if i = ⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩ then 1 else 0, ?_⟩
      change ∑ i : Fin (Module.finrank ℝ E),
          (if i = ⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩ then (1 : ℝ) else 0) ^ 2 = 1
      rw [Finset.sum_eq_single ⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩]
      · simp
      · intro j _ hj; rw [if_neg hj]; ring
      · intro hj; exact absurd (Finset.mem_univ _) hj
    obtain ⟨ξ₀, hξ₀⟩ := hSph_ne
    exact absurd ⟨(b, ξ₀), hb, hξ₀⟩ hK_ne


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma gInner_self_eq_chartGram_quadForm
    (g : SmoothRiemannianMetric I M) (α : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet) (v : TangentSpace I x) :
    g.inner x v v =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          chartGramMatrix (I := I) g α x i j *
            (chartBasisFamily (I := I) α hx).repr v i *
            (chartBasisFamily (I := I) α hx).repr v j := by
  classical
  set c : Fin (Module.finrank ℝ E) → ℝ :=
    fun i => (chartBasisFamily (I := I) α hx).repr v i with hc_def
  have hv : v = ∑ i, c i • chartBasisVecFiber (I := I) α i x := by
    have h := (chartBasisFamily (I := I) α hx).sum_repr v
    rw [← h]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hc_def, chartBasisFamily_apply (I := I) α hx i]
  have hdot := chartGramMatrix_dotProduct_mulVec (I := I) g α x c
  have hgi : g.inner x (∑ i, c i • chartBasisVecFiber (I := I) α i x)
        (∑ j, c j • chartBasisVecFiber (I := I) α j x)
      = ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            chartGramMatrix (I := I) g α x i j * c i * c j := by
    rw [← hdot]
    simp only [dotProduct, Matrix.mulVec, chartGramMatrix_apply, Pi.star_apply, star_trivial]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  calc g.inner x v v
      = g.inner x (∑ i, c i • chartBasisVecFiber (I := I) α i x)
          (∑ j, c j • chartBasisVecFiber (I := I) α j x) := by rw [← hv]
    _ = _ := hgi


omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma riemannOp_LeviCivita_chartAlpha_frame_expand
    (g : SmoothRiemannianMetric I M) (α : M) {x : M}
    (hx_base : x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (hx_good : x ∈ chartLeviCivitaGoodSet (I := I) α)
    (v w u : TangentSpace I x) :
    riemannOp (cov := LeviCivita (I := I) g) x v w u =
      ∑ l : Fin (Module.finrank ℝ E),
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            ∑ k : Fin (Module.finrank ℝ E),
              (chartBasisFamily (I := I) α hx_base).repr u i *
                (chartBasisFamily (I := I) α hx_base).repr v j *
                (chartBasisFamily (I := I) α hx_base).repr w k *
                chartRiemannTensor (I := I) g α i j k l (extChartAt I α x)) •
          chartBasisVecFiber (I := I) α l x := by
  classical
  set eα : Fin (Module.finrank ℝ E) → TangentSpace I x :=
    fun i => chartBasisVecFiber (I := I) α i x with heα_def
  set a : Fin (Module.finrank ℝ E) → ℝ :=
    fun j => (chartBasisFamily (I := I) α hx_base).repr v j with ha_def
  set b : Fin (Module.finrank ℝ E) → ℝ :=
    fun k => (chartBasisFamily (I := I) α hx_base).repr w k with hb_def
  set c : Fin (Module.finrank ℝ E) → ℝ :=
    fun i => (chartBasisFamily (I := I) α hx_base).repr u i with hc_def
  have hv : v = ∑ j, a j • eα j := by
    have h := (chartBasisFamily (I := I) α hx_base).sum_repr v
    rw [← h]; refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [ha_def, heα_def, chartBasisFamily_apply (I := I) α hx_base j]
  have hw : w = ∑ k, b k • eα k := by
    have h := (chartBasisFamily (I := I) α hx_base).sum_repr w
    rw [← h]; refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hb_def, heα_def, chartBasisFamily_apply (I := I) α hx_base k]
  have hu : u = ∑ i, c i • eα i := by
    have h := (chartBasisFamily (I := I) α hx_base).sum_repr u
    rw [← h]; refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hc_def, heα_def, chartBasisFamily_apply (I := I) α hx_base i]
  have hbasis : ∀ i j k : Fin (Module.finrank ℝ E),
      riemannOp (cov := LeviCivita (I := I) g) x (eα j) (eα k) (eα i) =
        ∑ l : Fin (Module.finrank ℝ E),
          chartRiemannTensor (I := I) g α i j k l (extChartAt I α x) • eα l := by
    intro i j k
    have hgood : x ∈ chartLeviCivitaGoodSet (I := I) α := hx_good
    exact riemannOp_chartBasisVec_alpha_eq (I := I) g α i j k hgood

  have htri : riemannOp (cov := LeviCivita (I := I) g) x v w u =
      ∑ i, ∑ k, ∑ j, (c i * (b k * a j)) •
        riemannOp (cov := LeviCivita (I := I) g) x (eα j) (eα k) (eα i) := by
    conv_lhs => rw [hv, hw, hu]
    simp only [map_sum, map_smul, ContinuousLinearMap.coe_sum', Finset.sum_apply,
      ContinuousLinearMap.smul_apply, Finset.smul_sum, smul_smul]
  rw [htri]

  have hexpand : (∑ i, ∑ k, ∑ j, (c i * (b k * a j)) •
        riemannOp (cov := LeviCivita (I := I) g) x (eα j) (eα k) (eα i)) =
      ∑ i, ∑ k, ∑ j, ∑ l,
        (c i * a j * b k *
          chartRiemannTensor (I := I) g α i j k l (extChartAt I α x)) • eα l := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun k _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hbasis i j k, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [smul_smul]
    congr 1
    ring
  rw [hexpand]

  set t : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → TangentSpace I x :=
    fun i j k l => (c i * a j * b k *
      chartRiemannTensor (I := I) g α i j k l (extChartAt I α x)) • eα l with ht_def
  change (∑ i, ∑ k, ∑ j, ∑ l, t i j k l) =
      ∑ l, (∑ i, ∑ j, ∑ k, (c i * a j * b k *
        chartRiemannTensor (I := I) g α i j k l (extChartAt I α x))) • eα l
  have hRHS_distr : (∑ l, (∑ i, ∑ j, ∑ k, (c i * a j * b k *
          chartRiemannTensor (I := I) g α i j k l (extChartAt I α x))) • eα l) =
      ∑ l, ∑ i, ∑ j, ∑ k, t i j k l := by
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.sum_smul]
  rw [hRHS_distr]

  rw [show (∑ i, ∑ k, ∑ j, ∑ l, t i j k l) = ∑ i, ∑ k, ∑ l, ∑ j, t i j k l from by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.sum_comm]]

  rw [show (∑ i, ∑ k, ∑ l, ∑ j, t i j k l) = ∑ i, ∑ l, ∑ k, ∑ j, t i j k l from by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_comm]]

  rw [Finset.sum_comm]

  refine Finset.sum_congr rfl (fun l _ => ?_)
  refine Finset.sum_congr rfl (fun i _ => ?_)

  rw [Finset.sum_comm]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma riemannOp_normSq_le_chartConstants
    (g : SmoothRiemannianMetric I M) (α : M) {x : M}
    (hx_base : x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (hx_good : x ∈ chartLeviCivitaGoodSet (I := I) α)
    {CR CG cg : ℝ} (hCR : 0 ≤ CR) (hCG : 0 ≤ CG) (hcg : 0 < cg)
    (hCRbound : ∀ i j k l : Fin (Module.finrank ℝ E),
      |chartRiemannTensor (I := I) g α i j k l (extChartAt I α x)| ≤ CR)
    (hCGbound : ∀ ξ : Fin (Module.finrank ℝ E) → ℝ,
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          chartGramMatrix (I := I) g α x i j * ξ i * ξ j ≤
        CG * ∑ i : Fin (Module.finrank ℝ E), ξ i ^ 2)
    (hcgbound : ∀ ξ : Fin (Module.finrank ℝ E) → ℝ,
      cg * (∑ i : Fin (Module.finrank ℝ E), ξ i ^ 2) ≤
        ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          chartGramMatrix (I := I) g α x i j * ξ i * ξ j)
    (v w u : TangentSpace I x) :
    g.inner x (riemannOp (cov := LeviCivita (I := I) g) x v w u)
        (riemannOp (cov := LeviCivita (I := I) g) x v w u) ≤
      CG * CR ^ 2 * (Module.finrank ℝ E : ℝ) ^ 4 * cg⁻¹ ^ 3 *
        g.inner x v v * g.inner x w w * g.inner x u u := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn_def
  set a : Fin n → ℝ := fun j => (chartBasisFamily (I := I) α hx_base).repr v j with ha_def
  set b : Fin n → ℝ := fun k => (chartBasisFamily (I := I) α hx_base).repr w k with hb_def
  set c : Fin n → ℝ := fun i => (chartBasisFamily (I := I) α hx_base).repr u i with hc_def
  set R : Fin n → Fin n → Fin n → Fin n → ℝ :=
    fun i j k l => chartRiemannTensor (I := I) g α i j k l (extChartAt I α x) with hR_def
  set coeff : Fin n → ℝ := fun l => ∑ i, ∑ j, ∑ k, c i * a j * b k * R i j k l with hcoeff_def

  have hRvwu : riemannOp (cov := LeviCivita (I := I) g) x v w u =
      ∑ l, coeff l • chartBasisVecFiber (I := I) α l x := by
    rw [riemannOp_LeviCivita_chartAlpha_frame_expand (I := I) g α hx_base hx_good v w u]

  have hgnorm_eq : g.inner x (riemannOp (cov := LeviCivita (I := I) g) x v w u)
        (riemannOp (cov := LeviCivita (I := I) g) x v w u) =
      ∑ l, ∑ l', chartGramMatrix (I := I) g α x l l' * coeff l * coeff l' := by
    rw [hRvwu]
    have hdot := chartGramMatrix_dotProduct_mulVec (I := I) g α x coeff
    rw [← hdot]
    simp only [dotProduct, Matrix.mulVec, chartGramMatrix_apply, Pi.star_apply, star_trivial]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l' _ => ?_)
    ring
  have hgnorm_le_CGcoeff : g.inner x (riemannOp (cov := LeviCivita (I := I) g) x v w u)
        (riemannOp (cov := LeviCivita (I := I) g) x v w u) ≤
      CG * ∑ l, coeff l ^ 2 := by
    rw [hgnorm_eq]; exact hCGbound coeff

  set Sa : ℝ := ∑ j, |a j| with hSa_def
  set Sb : ℝ := ∑ k, |b k| with hSb_def
  set Sc : ℝ := ∑ i, |c i| with hSc_def
  have hSa_nonneg : 0 ≤ Sa := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hSb_nonneg : 0 ≤ Sb := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hSc_nonneg : 0 ≤ Sc := Finset.sum_nonneg (fun _ _ => abs_nonneg _)

  have hk_collapse : ∀ i j : Fin n,
      (∑ k, |c i| * |a j| * |b k|) = |c i| * |a j| * Sb := by
    intro i j
    rw [hSb_def, Finset.mul_sum]
  have hj_collapse : ∀ i : Fin n,
      (∑ j, |c i| * |a j| * Sb) = |c i| * Sa * Sb := by
    intro i
    rw [hSa_def]
    rw [show |c i| * (∑ j, |a j|) * Sb = (∑ j, |a j|) * (|c i| * Sb) from by ring,
      Finset.sum_mul]
    refine Finset.sum_congr rfl (fun j _ => ?_); ring
  have hprod_factor : (∑ i, ∑ j, ∑ k, |c i| * |a j| * |b k|) = Sc * (Sa * Sb) := by
    have hstep : (∑ i, ∑ j, ∑ k, |c i| * |a j| * |b k|) =
        ∑ i, |c i| * Sa * Sb := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [show (∑ j, ∑ k, |c i| * |a j| * |b k|) = ∑ j, |c i| * |a j| * Sb from
        Finset.sum_congr rfl (fun j _ => hk_collapse i j)]
      exact hj_collapse i
    rw [hstep, hSc_def]
    rw [show (∑ i, |c i| * Sa * Sb) = (∑ i, |c i|) * (Sa * Sb) from by
      rw [Finset.sum_mul]; refine Finset.sum_congr rfl (fun i _ => ?_); ring]
  have hcoeff_abs : ∀ l, |coeff l| ≤ CR * (Sc * Sa * Sb) := by
    intro l
    rw [hcoeff_def]
    have hstep : |∑ i, ∑ j, ∑ k, c i * a j * b k * R i j k l| ≤
        ∑ i, ∑ j, ∑ k, |c i| * |a j| * |b k| * CR := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun i _ => ?_))
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun j _ => ?_))
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun k _ => ?_))
      rw [abs_mul, abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left (hCRbound i j k l) (by positivity)
    refine le_trans hstep ?_
    have heq : (∑ i, ∑ j, ∑ k, |c i| * |a j| * |b k| * CR) =
        (∑ i, ∑ j, ∑ k, |c i| * |a j| * |b k|) * CR := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Finset.sum_mul]
    rw [heq, hprod_factor]
    exact le_of_eq (by ring)

  have hcoeff_sq : ∀ l, coeff l ^ 2 ≤ CR ^ 2 * (Sc * Sa * Sb) ^ 2 := by
    intro l
    have h1 : |coeff l| ≤ CR * (Sc * Sa * Sb) := hcoeff_abs l
    have h2 : 0 ≤ CR * (Sc * Sa * Sb) :=
      mul_nonneg hCR (by positivity)
    calc coeff l ^ 2 = |coeff l| ^ 2 := (sq_abs _).symm
      _ ≤ (CR * (Sc * Sa * Sb)) ^ 2 := by
          exact pow_le_pow_left₀ (abs_nonneg _) h1 2
      _ = CR ^ 2 * (Sc * Sa * Sb) ^ 2 := by ring
  have hsum_coeff_sq : ∑ l, coeff l ^ 2 ≤
      (n : ℝ) * (CR ^ 2 * (Sc * Sa * Sb) ^ 2) := by
    calc ∑ l, coeff l ^ 2 ≤ ∑ _l : Fin n, CR ^ 2 * (Sc * Sa * Sb) ^ 2 :=
          Finset.sum_le_sum (fun l _ => hcoeff_sq l)
      _ = (n : ℝ) * (CR ^ 2 * (Sc * Sa * Sb) ^ 2) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

  have hSa_sq : Sa ^ 2 ≤ (n : ℝ) * ∑ j, a j ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n)))
      (f := fun j => |a j|)
    rw [Finset.card_univ, Fintype.card_fin] at h
    have heq : ∑ j, |a j| ^ 2 = ∑ j, a j ^ 2 :=
      Finset.sum_congr rfl (fun j _ => sq_abs _)
    rw [heq] at h
    exact h
  have hSb_sq : Sb ^ 2 ≤ (n : ℝ) * ∑ k, b k ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n)))
      (f := fun k => |b k|)
    rw [Finset.card_univ, Fintype.card_fin] at h
    have heq : ∑ k, |b k| ^ 2 = ∑ k, b k ^ 2 :=
      Finset.sum_congr rfl (fun k _ => sq_abs _)
    rw [heq] at h
    exact h
  have hSc_sq : Sc ^ 2 ≤ (n : ℝ) * ∑ i, c i ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n)))
      (f := fun i => |c i|)
    rw [Finset.card_univ, Fintype.card_fin] at h
    have heq : ∑ i, |c i| ^ 2 = ∑ i, c i ^ 2 :=
      Finset.sum_congr rfl (fun i _ => sq_abs _)
    rw [heq] at h
    exact h

  have hgvv_eq : g.inner x v v =
      ∑ i, ∑ j, chartGramMatrix (I := I) g α x i j * a i * a j := by
    rw [gInner_self_eq_chartGram_quadForm (I := I) g α hx_base v]
  have hgww_eq : g.inner x w w =
      ∑ i, ∑ j, chartGramMatrix (I := I) g α x i j * b i * b j := by
    rw [gInner_self_eq_chartGram_quadForm (I := I) g α hx_base w]
  have hguu_eq : g.inner x u u =
      ∑ i, ∑ j, chartGramMatrix (I := I) g α x i j * c i * c j := by
    rw [gInner_self_eq_chartGram_quadForm (I := I) g α hx_base u]
  have hQa_le : ∑ j, a j ^ 2 ≤ cg⁻¹ * g.inner x v v := by
    have hlow : cg * (∑ j, a j ^ 2) ≤ g.inner x v v := by rw [hgvv_eq]; exact hcgbound a
    rw [inv_mul_eq_div, le_div_iff₀' hcg]; exact hlow
  have hQb_le : ∑ k, b k ^ 2 ≤ cg⁻¹ * g.inner x w w := by
    have hlow : cg * (∑ k, b k ^ 2) ≤ g.inner x w w := by rw [hgww_eq]; exact hcgbound b
    rw [inv_mul_eq_div, le_div_iff₀' hcg]; exact hlow
  have hQc_le : ∑ i, c i ^ 2 ≤ cg⁻¹ * g.inner x u u := by
    have hlow : cg * (∑ i, c i ^ 2) ≤ g.inner x u u := by rw [hguu_eq]; exact hcgbound c
    rw [inv_mul_eq_div, le_div_iff₀' hcg]; exact hlow
  have hgvv_nonneg : 0 ≤ g.inner x v v := metric_inner_self_nonneg (I := I) g x v
  have hgww_nonneg : 0 ≤ g.inner x w w := metric_inner_self_nonneg (I := I) g x w
  have hguu_nonneg : 0 ≤ g.inner x u u := metric_inner_self_nonneg (I := I) g x u
  have hQa_nonneg : 0 ≤ ∑ j, a j ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hQb_nonneg : 0 ≤ ∑ k, b k ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hQc_nonneg : 0 ≤ ∑ i, c i ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

  have hCG_nonneg : 0 ≤ CG := hCG

  have hScab_sq : (Sc * Sa * Sb) ^ 2 ≤
      (n : ℝ) ^ 3 * ((∑ i, c i ^ 2) * (∑ j, a j ^ 2) * (∑ k, b k ^ 2)) := by
    have hexp : (Sc * Sa * Sb) ^ 2 = Sc ^ 2 * Sa ^ 2 * Sb ^ 2 := by ring
    rw [hexp]
    have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hScsq_nn : (0 : ℝ) ≤ Sc ^ 2 := sq_nonneg _
    have hSasq_nn : (0 : ℝ) ≤ Sa ^ 2 := sq_nonneg _
    have hnQc_nn : (0 : ℝ) ≤ (n : ℝ) * ∑ i, c i ^ 2 := by positivity
    have hnQa_nn : (0 : ℝ) ≤ (n : ℝ) * ∑ j, a j ^ 2 := by positivity
    calc Sc ^ 2 * Sa ^ 2 * Sb ^ 2
        ≤ ((n : ℝ) * ∑ i, c i ^ 2) * ((n : ℝ) * ∑ j, a j ^ 2) *
            ((n : ℝ) * ∑ k, b k ^ 2) :=
          mul_le_mul (mul_le_mul hSc_sq hSa_sq hSasq_nn hnQc_nn) hSb_sq (sq_nonneg _)
            (mul_nonneg hnQc_nn hnQa_nn)
      _ = (n : ℝ) ^ 3 * ((∑ i, c i ^ 2) * (∑ j, a j ^ 2) * (∑ k, b k ^ 2)) := by ring
  have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hcg_inv_nonneg : (0 : ℝ) ≤ cg⁻¹ := le_of_lt (inv_pos.mpr hcg)
  have hCR2_nonneg : (0 : ℝ) ≤ CR ^ 2 := sq_nonneg _

  have hsum_coeff_sq' : ∑ l, coeff l ^ 2 ≤
      CR ^ 2 * (n : ℝ) ^ 4 * ((∑ i, c i ^ 2) * (∑ j, a j ^ 2) * (∑ k, b k ^ 2)) := by
    calc ∑ l, coeff l ^ 2 ≤ (n : ℝ) * (CR ^ 2 * (Sc * Sa * Sb) ^ 2) := hsum_coeff_sq
      _ ≤ (n : ℝ) * (CR ^ 2 *
            ((n : ℝ) ^ 3 * ((∑ i, c i ^ 2) * (∑ j, a j ^ 2) * (∑ k, b k ^ 2)))) := by
          gcongr
      _ = CR ^ 2 * (n : ℝ) ^ 4 *
            ((∑ i, c i ^ 2) * (∑ j, a j ^ 2) * (∑ k, b k ^ 2)) := by ring

  have hQprod_le : (∑ i, c i ^ 2) * (∑ j, a j ^ 2) * (∑ k, b k ^ 2) ≤
      cg⁻¹ ^ 3 * (g.inner x u u * g.inner x v v * g.inner x w w) := by
    calc (∑ i, c i ^ 2) * (∑ j, a j ^ 2) * (∑ k, b k ^ 2)
        ≤ (cg⁻¹ * g.inner x u u) * (cg⁻¹ * g.inner x v v) * (cg⁻¹ * g.inner x w w) := by
          gcongr
      _ = cg⁻¹ ^ 3 * (g.inner x u u * g.inner x v v * g.inner x w w) := by ring

  calc g.inner x (riemannOp (cov := LeviCivita (I := I) g) x v w u)
        (riemannOp (cov := LeviCivita (I := I) g) x v w u)
      ≤ CG * ∑ l, coeff l ^ 2 := hgnorm_le_CGcoeff
    _ ≤ CG * (CR ^ 2 * (n : ℝ) ^ 4 *
          ((∑ i, c i ^ 2) * (∑ j, a j ^ 2) * (∑ k, b k ^ 2))) := by
        gcongr
    _ ≤ CG * (CR ^ 2 * (n : ℝ) ^ 4 *
          (cg⁻¹ ^ 3 * (g.inner x u u * g.inner x v v * g.inner x w w))) := by
        gcongr
    _ = CG * CR ^ 2 * (n : ℝ) ^ 4 * cg⁻¹ ^ 3 *
          g.inner x v v * g.inner x w w * g.inner x u u := by ring

theorem exists_uniform_riemannOp_LeviCivita_gNorm_bound
    (g : SmoothRiemannianMetric I M) :
    ∃ Kbase : ℝ, 0 ≤ Kbase ∧
      ∀ (x : M) (v w u : TangentSpace I x),
        g.inner x (riemannOp (cov := LeviCivita (I := I) g) x v w u)
            (riemannOp (cov := LeviCivita (I := I) g) x v w u) ≤
          Kbase * g.inner x v v * g.inner x w w * g.inner x u u := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn_def

  have hCR_ex : ∀ α : M, ∃ C : ℝ, 0 ≤ C ∧
      ∀ b ∈ tsupport (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x),
        ∀ i j k l : Fin n,
          |chartRiemannTensor (I := I) g α i j k l (extChartAt I α b)| ≤ C := by
    intro α
    obtain ⟨C, hC0, hCbound⟩ :=
      exists_chartRiemannData_uniform_bound_pouTsupport (I := I) g α
    refine ⟨C, hC0, fun b hb i j k l => ?_⟩
    exact hCbound ⟨hb, pouTsupport_subset_goodSet (I := I) α hb⟩ i j k l
  have hCG_ex : ∀ α : M, ∃ C : ℝ, 0 ≤ C ∧
      ∀ b ∈ tsupport (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x),
        ∀ ξ : Fin n → ℝ,
          ∑ i, ∑ j, chartGramMatrix (I := I) g α b i j * ξ i * ξ j ≤ C * ∑ i, ξ i ^ 2 := by
    intro α
    obtain ⟨C, hC0, hCbound⟩ :=
      exists_chartGramMatrix_quadForm_upper_bound_on_pouTsupport (I := I) g α
    refine ⟨C, hC0, fun b hb ξ => ?_⟩
    have h := hCbound hb ξ
    refine le_trans (le_of_eq ?_) h
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [chartGramMatrix_apply]

  choose CR hCR0 hCRbound using hCR_ex
  choose CG hCG0 hCGbound using hCG_ex
  choose cg hcg0 hcgbound using fun α =>
    exists_chartGramMatrix_quadForm_lower_bound_on_pouTsupport (I := I) g α
  set Kα : M → ℝ := fun α =>
    CG α * CR α ^ 2 * (n : ℝ) ^ 4 * (cg α)⁻¹ ^ 3 with hKα_def
  have hKα_nonneg : ∀ α, 0 ≤ Kα α := by
    intro α
    rw [hKα_def]
    have hcgα : 0 < cg α := hcg0 α
    have hinv : 0 ≤ (cg α)⁻¹ ^ 3 := by positivity
    have hCRα : 0 ≤ CR α := hCR0 α
    have hCGα : 0 ≤ CG α := hCG0 α
    positivity
  refine ⟨∑ α ∈ chartAtlasPOU_finset (I := I) (M := M), Kα α, ?_, ?_⟩
  · exact Finset.sum_nonneg (fun α _ => hKα_nonneg α)
  intro x v w u

  have hsum := DifferentialGeometry.Analysis.Sobolev.Chart.chartAtlasPOU_finset_sum_eq_one
    (I := I) (M := M) x
  have hex_pos : ∃ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ((chartAtlasPOU I M) α) x ≠ 0 := by
    by_contra hno
    have hno' : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        ((chartAtlasPOU I M) α) x = 0 := by
      intro α hα
      by_contra hne
      exact hno ⟨α, hα, hne⟩
    have hzero : ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        ((chartAtlasPOU I M) α) x = 0 :=
      Finset.sum_eq_zero (fun α hα => hno' α hα)
    rw [hzero] at hsum
    exact one_ne_zero hsum.symm
  obtain ⟨α, hα_mem, hα_pos⟩ := hex_pos
  have hx_tsupport : x ∈ tsupport
      (fun y : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) y) := by
    apply subset_tsupport
    exact hα_pos
  have hx_good : x ∈ chartLeviCivitaGoodSet (I := I) α :=
    pouTsupport_subset_goodSet (I := I) α hx_tsupport
  have hx_base : x ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hx_good

  have hpt := riemannOp_normSq_le_chartConstants (I := I) g α hx_base hx_good
    (CR := CR α) (CG := CG α) (cg := cg α) (hCR0 α) (hCG0 α) (hcg0 α)
    (fun i j k l => hCRbound α x hx_tsupport i j k l)
    (fun ξ => hCGbound α x hx_tsupport ξ)
    (fun ξ => hcgbound α x hx_tsupport ξ) v w u

  have hKα_le : Kα α ≤ ∑ β ∈ chartAtlasPOU_finset (I := I) (M := M), Kα β :=
    Finset.single_le_sum (fun β _ => hKα_nonneg β) hα_mem
  have hgvv_nonneg : 0 ≤ g.inner x v v := metric_inner_self_nonneg (I := I) g x v
  have hgww_nonneg : 0 ≤ g.inner x w w := metric_inner_self_nonneg (I := I) g x w
  have hguu_nonneg : 0 ≤ g.inner x u u := metric_inner_self_nonneg (I := I) g x u
  calc g.inner x (riemannOp (cov := LeviCivita (I := I) g) x v w u)
        (riemannOp (cov := LeviCivita (I := I) g) x v w u)
      ≤ Kα α * g.inner x v v * g.inner x w w * g.inner x u u := by
        rw [hKα_def]; exact hpt
    _ ≤ (∑ β ∈ chartAtlasPOU_finset (I := I) (M := M), Kα β) *
          g.inner x v v * g.inner x w w * g.inner x u u := by
        gcongr

end Connection
end Integral
end DifferentialGeometry

end
