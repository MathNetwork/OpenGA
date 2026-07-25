import DifferentialGeometry.Geometry.Comparison.HopfRinowProper
import DifferentialGeometry.Geometry.Comparison.RiemannianDistContinuity
import DifferentialGeometry.Geometry.Comparison.Variation.FirstVariation
import DifferentialGeometry.Geometry.Operator.Operators
import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.UnitInterval

set_option autoImplicit false









noncomputable section

open Set Function Filter Bundle Manifold
open scoped Topology Manifold ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace CenterOfMass

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable {ι : Type*} [Fintype ι]




def StrictMidConvexOn {X : Type*} (join : X -> X -> Real -> X)
    (S : Set X) (φ : X -> Real) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, a ≠ b ->
    join a b (1 / 2 : Real) ∈ S ∧
      φ (join a b (1 / 2 : Real)) < max (φ a) (φ b)



def StrictMidJensenOn {X : Type*} (join : X -> X -> Real -> X)
    (S : Set X) (φ : X -> Real) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, a ≠ b ->
    join a b (1 / 2 : Real) ∈ S ∧
      φ (join a b (1 / 2 : Real)) < (φ a + φ b) / 2



theorem jensen_of_strict {X : Type*} {join : X -> X -> Real -> X}
    {S : Set X} {φ : X -> Real}
    (hmid : ∀ a ∈ S, ∀ b ∈ S, a ≠ b -> join a b (1 / 2 : Real) ∈ S)
    (hzero : ∀ a ∈ S, ∀ b ∈ S, join a b 0 = a)
    (hone : ∀ a ∈ S, ∀ b ∈ S, join a b 1 = b)
    (hstrict : ∀ a ∈ S, ∀ b ∈ S, a ≠ b ->
      StrictConvexOn Real unitInterval (fun t : Real => φ (join a b t))) :
    StrictMidJensenOn join S φ := by
  intro a ha b hb hne
  refine ⟨hmid a ha b hb hne, ?_⟩
  have hlt :=
    (hstrict a ha b hb hne).2 unitInterval.zero_mem unitInterval.one_mem
      (by norm_num : (0 : Real) ≠ 1)
      (by norm_num : (0 : Real) < 1 / 2)
      (by norm_num : (0 : Real) < 1 / 2)
      (by norm_num : (1 / 2 : Real) + 1 / 2 = 1)
  have hlt_mid :
      φ (join a b (1 / 2 : Real)) <
        (1 / 2 : Real) * φ (join a b 0) +
          (1 / 2 : Real) * φ (join a b 1) := by
    simpa using hlt
  rw [hzero a ha b hb, hone a ha b hb] at hlt_mid
  linarith


theorem min_unique_of_mid {X : Type*} {join : X -> X -> Real -> X}
    {S : Set X} {φ : X -> Real} (hstrict : StrictMidConvexOn join S φ)
    {x y : X} (hxS : x ∈ S) (hyS : y ∈ S)
    (hxmin : ∀ z ∈ S, φ x ≤ φ z) (hymin : ∀ z ∈ S, φ y ≤ φ z) :
    x = y := by
  by_contra hxy
  obtain ⟨hmS, hm_lt⟩ := hstrict x hxS y hyS hxy
  have hxy_le : φ x ≤ φ y := hxmin y hyS
  have hyx_le : φ y ≤ φ x := hymin x hxS
  have hφeq : φ x = φ y := le_antisymm hxy_le hyx_le
  rw [hφeq, max_self] at hm_lt
  have hy_le_m := hymin (join x y (1 / 2 : Real)) hmS
  linarith

section Metric

variable {X : Type*} [MetricSpace X]


def halfSqDist (pt : X) (q : X) : Real :=
  (1 / 2 : Real) * dist q pt ^ 2


def metricEnergy (μ : ι -> Real) (pts : ι -> X) (q : X) : Real :=
  (1 / 2 : Real) * ∑ i : ι, μ i * dist q (pts i) ^ 2


theorem metricEnergy_half (μ : ι -> Real) (pts : ι -> X) (q : X) :
    metricEnergy μ pts q = ∑ i : ι, μ i * halfSqDist (pts i) q := by
  simp [metricEnergy, halfSqDist, Finset.mul_sum, mul_assoc, mul_comm]

set_option maxHeartbeats 800000 in











theorem metricEnergy_argmin_stable {P : Type*} [TopologicalSpace P] [FirstCountableTopology P]
    {K : Set X} (hK : IsCompact K)
    (μ : P -> ι -> Real) (pts : P -> ι -> X) (c : P -> X) (p₀ : P)
    (hμ : Continuous μ) (hpts : Continuous pts)
    (hc_min : ∀ a : P, ∀ y : X,
      metricEnergy (μ a) (pts a) (c a) ≤ metricEnergy (μ a) (pts a) y)
    (hc_mem : ∀ a : P, c a ∈ K)
    (huniq : ∀ y : X,
      (∀ z : X, metricEnergy (μ p₀) (pts p₀) y ≤ metricEnergy (μ p₀) (pts p₀) z) → y = c p₀) :
    Filter.Tendsto c (nhds p₀) (nhds (c p₀)) := by
  classical
  have Econt : Continuous (fun aq : P × X => metricEnergy (μ aq.1) (pts aq.1) aq.2) := by
    unfold metricEnergy
    refine continuous_const.mul (continuous_finset_sum _ (fun i _ => ?_))
    refine ((continuous_apply i).comp (hμ.comp continuous_fst)).mul ?_
    exact (Continuous.dist continuous_snd
      ((continuous_apply i).comp (hpts.comp continuous_fst))).pow 2
  rw [tendsto_iff_seq_tendsto]
  intro seq hseq
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨cstar, hcstar_mem, φ, hφ_mono, hφ_tend⟩ :=
    hK.tendsto_subseq (x := fun n => c (seq (ns n))) (fun n => hc_mem (seq (ns n)))
  have hp_tend : Filter.Tendsto (fun n => seq (ns (φ n))) Filter.atTop (nhds p₀) :=
    hseq.comp (hns.comp hφ_mono.tendsto_atTop)
  have hcstar_min : ∀ y : X,
      metricEnergy (μ p₀) (pts p₀) cstar ≤ metricEnergy (μ p₀) (pts p₀) y := by
    intro y
    have hLHS : Filter.Tendsto
        (fun n => metricEnergy (μ (seq (ns (φ n)))) (pts (seq (ns (φ n))))
          (c (seq (ns (φ n))))) Filter.atTop
        (nhds (metricEnergy (μ p₀) (pts p₀) cstar)) :=
      (Econt.tendsto (p₀, cstar)).comp (hp_tend.prodMk_nhds hφ_tend)
    have hRHS : Filter.Tendsto
        (fun n => metricEnergy (μ (seq (ns (φ n)))) (pts (seq (ns (φ n)))) y) Filter.atTop
        (nhds (metricEnergy (μ p₀) (pts p₀) y)) :=
      ((Econt.comp (continuous_id.prodMk continuous_const)).tendsto p₀).comp hp_tend
    exact le_of_tendsto_of_tendsto hLHS hRHS
      (Filter.Eventually.of_forall (fun n => hc_min (seq (ns (φ n))) y))
  refine ⟨φ, ?_⟩
  rw [huniq cstar hcstar_min] at hφ_tend
  exact hφ_tend



theorem metricEnergy_strict (μ : ι -> Real) (pts : ι -> X)
    {join : X -> X -> Real -> X} {S : Set X}
    (hμ_nonneg : ∀ i : ι, 0 ≤ μ i) (hμ_pos : ∃ i : ι, 0 < μ i)
    (hjensen : ∀ i : ι, StrictMidJensenOn join S (halfSqDist (pts i))) :
    StrictMidConvexOn join S (metricEnergy μ pts) := by
  classical
  intro a ha b hb hne
  rcases hμ_pos with ⟨i₀, hμi₀⟩
  set m : X := join a b (1 / 2 : Real)
  have hmS : m ∈ S := (hjensen i₀ a ha b hb hne).1
  refine ⟨hmS, ?_⟩
  have hle : ∀ i ∈ (Finset.univ : Finset ι),
      μ i * halfSqDist (pts i) m ≤
        μ i * ((halfSqDist (pts i) a + halfSqDist (pts i) b) / 2) := by
    intro i _
    exact mul_le_mul_of_nonneg_left (hjensen i a ha b hb hne).2.le (hμ_nonneg i)
  have hlt : ∃ i ∈ (Finset.univ : Finset ι),
      μ i * halfSqDist (pts i) m <
        μ i * ((halfSqDist (pts i) a + halfSqDist (pts i) b) / 2) := by
    refine ⟨i₀, Finset.mem_univ i₀, ?_⟩
    exact mul_lt_mul_of_pos_left (hjensen i₀ a ha b hb hne).2 hμi₀
  have hsum :
      (∑ i : ι, μ i * halfSqDist (pts i) m) <
        ∑ i : ι, μ i * ((halfSqDist (pts i) a + halfSqDist (pts i) b) / 2) :=
    Finset.sum_lt_sum hle hlt
  have hsum_eq :
      (∑ i : ι, μ i * ((halfSqDist (pts i) a + halfSqDist (pts i) b) / 2)) =
        ((∑ i : ι, μ i * halfSqDist (pts i) a) +
          ∑ i : ι, μ i * halfSqDist (pts i) b) / 2 := by
    calc
      (∑ i : ι, μ i * ((halfSqDist (pts i) a + halfSqDist (pts i) b) / 2))
          = ∑ i : ι,
              (μ i * halfSqDist (pts i) a + μ i * halfSqDist (pts i) b) / 2 := by
            apply Finset.sum_congr rfl
            intro i _
            ring
      _ = (∑ i : ι,
              (μ i * halfSqDist (pts i) a + μ i * halfSqDist (pts i) b)) / 2 := by
            rw [Finset.sum_div]
      _ = ((∑ i : ι, μ i * halfSqDist (pts i) a) +
            ∑ i : ι, μ i * halfSqDist (pts i) b) / 2 := by
            rw [Finset.sum_add_distrib]
  have hmid :
      metricEnergy μ pts m < (metricEnergy μ pts a + metricEnergy μ pts b) / 2 := by
    rw [hsum_eq] at hsum
    simpa [metricEnergy_half] using hsum
  have havg_le :
      (metricEnergy μ pts a + metricEnergy μ pts b) / 2 ≤
        max (metricEnergy μ pts a) (metricEnergy μ pts b) := by
    have ha_le : metricEnergy μ pts a ≤
        max (metricEnergy μ pts a) (metricEnergy μ pts b) := le_max_left _ _
    have hb_le : metricEnergy μ pts b ≤
        max (metricEnergy μ pts a) (metricEnergy μ pts b) := le_max_right _ _
    linarith
  exact lt_of_lt_of_le hmid havg_le



theorem metricEnergy_lt_far (μ : ι -> Real) (pts : ι -> X) {p q : X} {r : Real}
    (hr : 0 < r) (hpts : ∀ i : ι, dist p (pts i) < r)
    (hq : 2 * r ≤ dist p q) (hμ_nonneg : ∀ i : ι, 0 ≤ μ i)
    (hμ_pos : ∃ i : ι, 0 < μ i) :
    metricEnergy μ pts p < metricEnergy μ pts q := by
  classical
  have hsquares_le : ∀ i : ι, μ i * dist p (pts i) ^ 2 ≤
      μ i * dist q (pts i) ^ 2 := by
    intro i
    have htri : dist p q ≤ dist p (pts i) + dist (pts i) q :=
      dist_triangle p (pts i) q
    have hqdist : r < dist q (pts i) := by
      rw [dist_comm q (pts i)]
      linarith [hpts i, hq, htri]
    have hp_sq : dist p (pts i) ^ 2 < r ^ 2 :=
      (sq_lt_sq₀ dist_nonneg hr.le).mpr (hpts i)
    have hq_sq : r ^ 2 < dist q (pts i) ^ 2 :=
      (sq_lt_sq₀ hr.le dist_nonneg).mpr hqdist
    exact mul_le_mul_of_nonneg_left (le_trans hp_sq.le hq_sq.le) (hμ_nonneg i)
  have hsquares_lt : ∃ i ∈ (Finset.univ : Finset ι), μ i * dist p (pts i) ^ 2 <
      μ i * dist q (pts i) ^ 2 := by
    rcases hμ_pos with ⟨i, hμi⟩
    have htri : dist p q ≤ dist p (pts i) + dist (pts i) q :=
      dist_triangle p (pts i) q
    have hqdist : r < dist q (pts i) := by
      rw [dist_comm q (pts i)]
      linarith [hpts i, hq, htri]
    have hp_sq : dist p (pts i) ^ 2 < r ^ 2 :=
      (sq_lt_sq₀ dist_nonneg hr.le).mpr (hpts i)
    have hq_sq : r ^ 2 < dist q (pts i) ^ 2 :=
      (sq_lt_sq₀ hr.le dist_nonneg).mpr hqdist
    refine ⟨i, Finset.mem_univ i, ?_⟩
    exact mul_lt_mul_of_pos_left (lt_trans hp_sq hq_sq) hμi
  have hsum : (∑ i : ι, μ i * dist p (pts i) ^ 2) <
      ∑ i : ι, μ i * dist q (pts i) ^ 2 :=
    Finset.sum_lt_sum (fun i _ => hsquares_le i) hsquares_lt
  exact mul_lt_mul_of_pos_left hsum (by norm_num : (0 : Real) < 1 / 2)



theorem metricEnergy_min_dist_le (μ : ι -> Real) (pts : ι -> X) {q qstar : X}
    {ε : Real} (hε : 0 ≤ ε) (hpts : ∀ i : ι, dist qstar (pts i) ≤ ε)
    (hμ_nonneg : ∀ i : ι, 0 ≤ μ i) (hμ_pos : ∃ i : ι, 0 < μ i)
    (hmin : ∀ y : X, metricEnergy μ pts q ≤ metricEnergy μ pts y) :
    dist q qstar ≤ 2 * ε := by
  classical
  set S : Real := ∑ i : ι, μ i
  have hS_def : S = ∑ i : ι, μ i := rfl
  have hS_pos : 0 < S := by
    rcases hμ_pos with ⟨i₀, hi₀⟩
    exact Finset.sum_pos' (fun i _ => hμ_nonneg i)
      ⟨i₀, Finset.mem_univ i₀, hi₀⟩
  have hupper_sum :
      (∑ i : ι, μ i * dist qstar (pts i) ^ 2) ≤ ∑ i : ι, μ i * ε ^ 2 := by
    refine Finset.sum_le_sum ?_
    intro i _
    have hsq : dist qstar (pts i) ^ 2 ≤ ε ^ 2 :=
      (sq_le_sq₀ dist_nonneg hε).mpr (hpts i)
    exact mul_le_mul_of_nonneg_left hsq (hμ_nonneg i)
  have henergy_upper : metricEnergy μ pts qstar ≤ (1 / 2 : Real) * S * ε ^ 2 := by
    calc
      metricEnergy μ pts qstar =
          (1 / 2 : Real) * ∑ i : ι, μ i * dist qstar (pts i) ^ 2 := rfl
      _ ≤ (1 / 2 : Real) * (∑ i : ι, μ i * ε ^ 2) :=
          mul_le_mul_of_nonneg_left hupper_sum (by norm_num : (0 : Real) ≤ 1 / 2)
      _ = (1 / 2 : Real) * S * ε ^ 2 := by
          rw [← Finset.sum_mul, ← hS_def]
          ring
  by_cases hcase : ε ≤ dist q qstar
  · have hdelta_nonneg : 0 ≤ dist q qstar - ε := sub_nonneg.mpr hcase
    have hdist_lower : ∀ i : ι, dist q qstar - ε ≤ dist q (pts i) := by
      intro i
      have htri : dist q qstar ≤ dist q (pts i) + dist (pts i) qstar :=
        dist_triangle q (pts i) qstar
      have hptsi : dist (pts i) qstar ≤ ε := by
        simpa [dist_comm] using hpts i
      linarith
    have hlower_sum :
        ∑ i : ι, μ i * (dist q qstar - ε) ^ 2 ≤
          ∑ i : ι, μ i * dist q (pts i) ^ 2 := by
      refine Finset.sum_le_sum ?_
      intro i _
      have hsq : (dist q qstar - ε) ^ 2 ≤ dist q (pts i) ^ 2 :=
        (sq_le_sq₀ hdelta_nonneg dist_nonneg).mpr (hdist_lower i)
      exact mul_le_mul_of_nonneg_left hsq (hμ_nonneg i)
    have henergy_lower :
        (1 / 2 : Real) * S * (dist q qstar - ε) ^ 2 ≤ metricEnergy μ pts q := by
      calc
        (1 / 2 : Real) * S * (dist q qstar - ε) ^ 2 =
            (1 / 2 : Real) * (∑ i : ι, μ i * (dist q qstar - ε) ^ 2) := by
              rw [← Finset.sum_mul, ← hS_def]
              ring
        _ ≤ (1 / 2 : Real) * (∑ i : ι, μ i * dist q (pts i) ^ 2) :=
            mul_le_mul_of_nonneg_left hlower_sum
              (by norm_num : (0 : Real) ≤ 1 / 2)
        _ = metricEnergy μ pts q := rfl
    have hcoef_pos : 0 < (1 / 2 : Real) * S :=
      mul_pos (by norm_num : (0 : Real) < 1 / 2) hS_pos
    have hsquares : (dist q qstar - ε) ^ 2 ≤ ε ^ 2 := by
      have hcombined :
          (1 / 2 : Real) * S * (dist q qstar - ε) ^ 2 ≤
            (1 / 2 : Real) * S * ε ^ 2 :=
        le_trans henergy_lower (le_trans (hmin qstar) henergy_upper)
      have hcombined' :
          ((1 / 2 : Real) * S) * (dist q qstar - ε) ^ 2 ≤
            ((1 / 2 : Real) * S) * ε ^ 2 := by
        simpa [mul_assoc] using hcombined
      exact le_of_mul_le_mul_left hcombined' hcoef_pos
    have hdelta_le : dist q qstar - ε ≤ ε :=
      (sq_le_sq₀ hdelta_nonneg hε).mp hsquares
    linarith
  · have hd_le : dist q qstar ≤ ε := le_of_not_ge hcase
    linarith

end Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M] [ConnectedSpace M]




def centerEnergy (g : SmoothRiemannianMetric I M) (μ : ι -> Real) (pts : ι -> M)
    (q : M) : Real :=
  letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  (1 / 2 : Real) * ∑ i : ι, μ i * (riemannianEDist I q (pts i)).toReal ^ 2


omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M] [ConnectedSpace M] in
theorem centerEnergy_congr (g : SmoothRiemannianMetric I M) (μ : ι → Real)
    {pts pts' : ι → M} (hpts : ∀ i, μ i ≠ 0 → pts i = pts' i) (q : M) :
    centerEnergy (I := I) g μ pts q = centerEnergy (I := I) g μ pts' q := by
  classical
  simp only [centerEnergy]
  congr 1
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases hi : μ i = 0
  · simp only [hi, zero_mul]
  · rw [hpts i hi]


omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
theorem centerEnergy_cont (g : SmoothRiemannianMetric I M)
    (μ : ι -> Real) (pts : ι -> M) :
    Continuous (centerEnergy (I := I) g μ pts) := by
  classical
  letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  have hdist : ∀ i : ι, Continuous fun q : M =>
      (riemannianEDist I q (pts i)).toReal := by
    intro i
    have hfinite :
        {q : M | riemannianEDist I (pts i) q ≠ (⊤ : ℝ≥0∞)} = Set.univ := by
      ext q
      simp [Exponential.riemannianEDist_ne_top (I := I) (pts i) q]
    have hbaseOn := continuousOn_riemannianEDist_toReal_on_finite g (pts i)
    have hbase : Continuous fun q : M => (riemannianEDist I (pts i) q).toReal := by
      rw [hfinite] at hbaseOn
      exact continuousOn_univ.mp hbaseOn
    simpa [riemannianEDist_comm] using hbase
  have hsum : Continuous fun q : M =>
      ∑ i : ι, μ i * (riemannianEDist I q (pts i)).toReal ^ 2 :=
    continuous_finset_sum _ fun i _ => continuous_const.mul ((hdist i).pow 2)
  simpa [centerEnergy] using continuous_const.mul hsum


omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
theorem exists_minOn_compact (g : SmoothRiemannianMetric I M)
    (μ : ι -> Real) (pts : ι -> M) {K : Set M}
    (hK : IsCompact K) (hne : K.Nonempty) :
    ∃ q ∈ K, ∀ y ∈ K,
      centerEnergy (I := I) g μ pts q ≤ centerEnergy (I := I) g μ pts y := by
  exact hK.exists_isMinOn hne (centerEnergy_cont (I := I) g μ pts).continuousOn



theorem exists_minOn_ball [T3Space M] (g : SmoothRiemannianMetric I M)
    (hcomplete :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
      CompleteSpace M)
    (hEnorm :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      ∀ x : M, ∀ v : TangentSpace I x,
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (μ : ι -> Real) (pts : ι -> M) (p : M) {R : Real} (hR : 0 ≤ R) :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    ∃ q ∈ Metric.closedBall p R, ∀ y ∈ Metric.closedBall p R,
      centerEnergy (I := I) g μ pts q ≤ centerEnergy (I := I) g μ pts y := by
  classical
  letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  haveI : ProperSpace M :=
    HopfRinow.properSpace_riemMetric (I := I) (M := M) hcomplete g hEnorm
  exact exists_minOn_compact (I := I) g μ pts (isCompact_closedBall p R)
    ⟨p, by simpa [Metric.mem_closedBall] using hR⟩



omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
theorem centerEnergy_eq_dist [T3Space M] (g : SmoothRiemannianMetric I M)
    (μ : ι -> Real) (pts : ι -> M) (q : M) :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    centerEnergy (I := I) g μ pts q =
      metricEnergy μ pts q := by
  classical
  letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  simp [centerEnergy, metricEnergy, HopfRinow.riemMetric_dist_eq (I := I) (M := M)]



omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
theorem centerEnergy_min_dist_le [T3Space M] (g : SmoothRiemannianMetric I M)
    (μ : ι -> Real) (pts : ι -> M) {q qstar : M} {ε : Real} :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    0 ≤ ε ->
      (∀ i : ι, dist qstar (pts i) ≤ ε) ->
      (∀ i : ι, 0 ≤ μ i) ->
      (∃ i : ι, 0 < μ i) ->
      (∀ y : M, centerEnergy (I := I) g μ pts q ≤ centerEnergy (I := I) g μ pts y) ->
      dist q qstar ≤ 2 * ε := by
  classical
  letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  intro hε hpts hμ_nonneg hμ_pos hmin
  refine metricEnergy_min_dist_le μ pts hε hpts hμ_nonneg hμ_pos ?_
  intro y
  have h := hmin y
  rw [centerEnergy_eq_dist (I := I) g μ pts q,
    centerEnergy_eq_dist (I := I) g μ pts y] at h
  exact h



omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
theorem grad_centerEnergy [T3Space M] (g : SmoothRiemannianMetric I M)
    {κ : Type} [Fintype κ] :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    ∀ (μ : κ -> Real) (pts : κ -> M) (x : M),
      (∀ i : κ, MDifferentiableAt I 𝓘(Real, Real) (halfSqDist (pts i)) x) ->
      gradientFun (I := I) g (centerEnergy (I := I) g μ pts) x =
        ∑ i : κ, μ i • gradientFun (I := I) g (halfSqDist (pts i)) x := by
  classical
  letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  intro μ pts x hdiff
  have hfun :
      centerEnergy (I := I) g μ pts =
        (∑ i : κ, μ i • halfSqDist (pts i)) := by
    funext q
    rw [centerEnergy_eq_dist (I := I) (ι := κ) g μ pts q,
      metricEnergy_half (ι := κ)]
    simp [Pi.smul_apply, smul_eq_mul]
  rw [hfun]
  simpa using
    gradientFun_sum_smul (I := I) g (Finset.univ : Finset κ) μ
      (f := fun i : κ => halfSqDist (pts i)) (x := x)
      (by intro i _; exact hdiff i)



omit [NeZero (Module.finrank ℝ E)] [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
theorem sum_grad_eq_zero [T3Space M] (g : SmoothRiemannianMetric I M)
    {κ : Type} [Fintype κ] :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    ∀ (μ : κ -> Real) (pts : κ -> M) (q : M),
      (∀ y : M, centerEnergy (I := I) g μ pts q ≤
        centerEnergy (I := I) g μ pts y) ->
      MDifferentiableAt I 𝓘(Real, Real) (centerEnergy (I := I) g μ pts) q ->
      (∀ i : κ, MDifferentiableAt I 𝓘(Real, Real) (halfSqDist (pts i)) q) ->
      ∑ i : κ, μ i • gradientFun (I := I) g (halfSqDist (pts i)) q = 0 := by
  classical
  letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  intro μ pts q hmin hdiffEnergy hdiffSummands
  have hlocal : IsLocalMin (centerEnergy (I := I) g μ pts) q := by
    unfold IsLocalMin IsMinFilter
    exact Filter.Eventually.of_forall hmin
  have hgrad0 :
      gradientFun (I := I) g (centerEnergy (I := I) g μ pts) q = 0 :=
    gradientFun_eq_zero_of_isLocalMin (I := I) g hlocal hdiffEnergy
  have hsum :=
    grad_centerEnergy (I := I) g μ pts q hdiffSummands
  rwa [hsum] at hgrad0






omit [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M] in
theorem sum_expInv_eq_zero [T3Space M] (g : SmoothRiemannianMetric I M)
    {κ : Type} [Fintype κ] :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    ∀ (μ : κ -> Real) (pts : κ -> M) (q : M),
      (∀ y : M, centerEnergy (I := I) g μ pts q ≤
        centerEnergy (I := I) g μ pts y) ->
      MDifferentiableAt I 𝓘(Real, Real) (centerEnergy (I := I) g μ pts) q ->
      (∀ i : κ, MDifferentiableAt I 𝓘(Real, Real) (halfSqDist (pts i)) q) ->
      (∀ i : κ,
        gradientFun (I := I) g (halfSqDist (pts i)) q =
          - (show TangentSpace I q from NormalCoordinates.normalChartAt (I := I) g q (pts i))) ->
      ∑ i : κ, μ i •
        (show TangentSpace I q from NormalCoordinates.normalChartAt (I := I) g q (pts i)) = 0 := by
  classical
  letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  intro μ pts q hmin hdiffEnergy hdiffSummands hgrad
  have hsum :=
    sum_grad_eq_zero (I := I) g μ pts q hmin hdiffEnergy hdiffSummands
  have hneg :
      ∑ i : κ, μ i •
        (-(show TangentSpace I q from NormalCoordinates.normalChartAt (I := I) g q (pts i))) =
          0 := by
    calc
      ∑ i : κ, μ i •
          (-(show TangentSpace I q from NormalCoordinates.normalChartAt (I := I) g q (pts i))) =
          ∑ i : κ, μ i • gradientFun (I := I) g (halfSqDist (pts i)) q := by
            apply Finset.sum_congr rfl
            intro i _
            rw [hgrad i]
      _ = 0 := hsum
  have hsum_neg :
      - (∑ i : κ, μ i •
        (show TangentSpace I q from NormalCoordinates.normalChartAt (I := I) g q (pts i))) =
          0 := by
    simpa [Finset.sum_neg_distrib, smul_neg] using hneg
  exact neg_eq_zero.mp hsum_neg





omit [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M] [ConnectedSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem halfSqDist_deriv_of_lengthVariation [MetricSpace M]
    (g : SmoothRiemannianMetric I M) (pt : M) (beta gamma : Real -> M)
    (f : Real -> Real -> M) (L : Real)
    (hf : DifferentialGeometry.Geometry.Riemannian.Variation.IsSmoothVariation
      (I := I) f)
    (hL : 0 < L)
    (hgamma : DifferentialGeometry.Geometry.Riemannian.Geodesic.IsGeodesicOn
      (I := I) g gamma (Set.Icc 0 L))
    (hfc : ∀ t : Real, f 0 t = gamma t)
    (hinit : ∀ s : Real, f s 0 = beta s)
    (hfixL : ∀ s : Real, f s L = pt) (hgammaL : gamma L = pt)
    (hUnit : ∀ t ∈ Set.Icc (0 : Real) L,
      g.inner (gamma t)
          (mfderiv (𝓘(Real, Real)) I gamma t (1 : Real))
          (mfderiv (𝓘(Real, Real)) I gamma t (1 : Real)) = 1)
    (hdist : (fun s : Real => dist (f s 0) pt) =ᶠ[nhds (0 : Real)]
        (fun s : Real =>
          DifferentialGeometry.Geometry.Riemannian.Variation.arcLength
            (I := I) g (fun t : Real => f s t) 0 L))
    (hdist0 : dist (f 0 0) pt = L) :
    HasDerivAt (fun s : Real => halfSqDist pt (beta s))
      (L * (- g.inner (gamma 0)
          (mfderiv (𝓘(Real, Real)) I (fun u : Real => f u 0) 0 (1 : Real))
          (mfderiv (𝓘(Real, Real)) I gamma 0 (1 : Real)))) 0 := by
  have hfixL' : ∀ s : Real, f s L = gamma L := by
    intro s
    exact (hfixL s).trans hgammaL.symm
  have hdist' : (fun s : Real => dist (f s 0) (gamma L)) =ᶠ[nhds (0 : Real)]
      (fun s : Real =>
        DifferentialGeometry.Geometry.Riemannian.Variation.arcLength
          (I := I) g (fun t : Real => f s t) 0 L) := by
    filter_upwards [hdist] with s hs
    simpa [hgammaL] using hs
  have hdist0' : dist (f 0 0) (gamma L) = L := by
    simpa [hgammaL] using hdist0
  have h :=
    DifferentialGeometry.Geometry.Riemannian.Variation.halfSq_deriv_length
      (I := I) g gamma f L hf hL hgamma hfc hfixL' hUnit hdist' hdist0'
  simpa [halfSqDist, hinit, hgammaL] using h




omit [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M] in
theorem grad_halfSqDist_of_flat [T3Space M] (g : SmoothRiemannianMetric I M)
    (pt q : M) :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    ((mfderiv I 𝓘(Real, Real) (halfSqDist pt) q).toLinearMap =
        metricFlatEquiv (I := I) g q
          (-(show TangentSpace I q from NormalCoordinates.normalChartAt (I := I) g q pt))) ->
    gradientFun (I := I) g (halfSqDist pt) q =
      - (show TangentSpace I q from NormalCoordinates.normalChartAt (I := I) g q pt) := by
  classical
  letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  intro hflat
  exact gradientFun_eq_of_flat (I := I) g hflat



omit [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M] in
theorem sum_expInv_of_flat [T3Space M] (g : SmoothRiemannianMetric I M)
    {κ : Type} [Fintype κ] :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    ∀ (μ : κ -> Real) (pts : κ -> M) (q : M),
      (∀ y : M, centerEnergy (I := I) g μ pts q ≤
        centerEnergy (I := I) g μ pts y) ->
      MDifferentiableAt I 𝓘(Real, Real) (centerEnergy (I := I) g μ pts) q ->
      (∀ i : κ, MDifferentiableAt I 𝓘(Real, Real) (halfSqDist (pts i)) q) ->
      (∀ i : κ,
        (mfderiv I 𝓘(Real, Real) (halfSqDist (pts i)) q).toLinearMap =
          metricFlatEquiv (I := I) g q
            (-(show TangentSpace I q from NormalCoordinates.normalChartAt (I := I) g q (pts i)))) ->
      ∑ i : κ, μ i •
        (show TangentSpace I q from NormalCoordinates.normalChartAt (I := I) g q (pts i)) = 0 := by
  classical
  letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  intro μ pts q hmin hdiffEnergy hdiffSummands hflat
  exact sum_expInv_eq_zero (I := I) g μ pts q hmin hdiffEnergy hdiffSummands
    (fun i => grad_halfSqDist_of_flat (I := I) g (pts i) q (hflat i))




omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
theorem centerEnergy_strict [T3Space M] (g : SmoothRiemannianMetric I M)
    (μ : ι -> Real) (pts : ι -> M) :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    ∀ {join : M -> M -> Real -> M} {S : Set M},
      (∀ i : ι, 0 ≤ μ i) -> (∃ i : ι, 0 < μ i) ->
      (∀ i : ι, StrictMidJensenOn join S (halfSqDist (pts i))) ->
      StrictMidConvexOn join S (centerEnergy (I := I) g μ pts) := by
  classical
  letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  intro join S hμ_nonneg hμ_pos hjensen
  have hmetric := metricEnergy_strict μ pts hμ_nonneg hμ_pos hjensen
  intro a ha b hb hne
  obtain ⟨hmS, hm_lt⟩ := hmetric a ha b hb hne
  refine ⟨hmS, ?_⟩
  simpa [centerEnergy_eq_dist (I := I) g μ pts (join a b (1 / 2 : Real)),
    centerEnergy_eq_dist (I := I) g μ pts a,
    centerEnergy_eq_dist (I := I) g μ pts b] using hm_lt




omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
theorem centerEnergy_lt_far [T3Space M] (g : SmoothRiemannianMetric I M)
    (μ : ι -> Real) (pts : ι -> M) :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    ∀ {p q : M} {r : Real}, 0 < r -> (∀ i : ι, dist p (pts i) < r) ->
      2 * r ≤ dist p q -> (∀ i : ι, 0 ≤ μ i) -> (∃ i : ι, 0 < μ i) ->
      centerEnergy (I := I) g μ pts p < centerEnergy (I := I) g μ pts q := by
  classical
  letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  intro p q r hr hpts hq hμ_nonneg hμ_pos
  rw [centerEnergy_eq_dist (I := I) g μ pts p,
    centerEnergy_eq_dist (I := I) g μ pts q]
  exact metricEnergy_lt_far μ pts hr hpts hq hμ_nonneg hμ_pos




theorem exists_global_min [T3Space M] (g : SmoothRiemannianMetric I M)
    (hcomplete :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
      CompleteSpace M)
    (hEnorm :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      ∀ x : M, ∀ v : TangentSpace I x,
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (μ : ι -> Real) (pts : ι -> M) :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    ∀ {p : M} {r : Real}, 0 < r -> (∀ i : ι, dist p (pts i) < r) ->
      (∀ i : ι, 0 ≤ μ i) -> (∃ i : ι, 0 < μ i) ->
      ∃ q ∈ Metric.closedBall p (2 * r), ∀ y : M,
        centerEnergy (I := I) g μ pts q ≤ centerEnergy (I := I) g μ pts y := by
  classical
  letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  intro p r hr hpts hμ_nonneg hμ_pos
  obtain ⟨q, hqball, hqmin⟩ :=
    exists_minOn_ball (I := I) g hcomplete hEnorm μ pts p (R := 2 * r) (by linarith)
  refine ⟨q, hqball, fun y => ?_⟩
  by_cases hy : y ∈ Metric.closedBall p (2 * r)
  · exact hqmin y hy
  · have hyfar : 2 * r ≤ dist p y := by
      rw [Metric.mem_closedBall, not_le] at hy
      exact (le_of_lt (by rwa [dist_comm] at hy))
    have hpball : p ∈ Metric.closedBall p (2 * r) := by
      rw [Metric.mem_closedBall]
      simpa [dist_self] using (by linarith : (0 : Real) ≤ 2 * r)
    have hq_le_p := hqmin p hpball
    have hp_lt_y :=
      centerEnergy_lt_far (I := I) g μ pts hr hpts hyfar hμ_nonneg hμ_pos
    exact le_trans hq_le_p hp_lt_y.le



theorem exists_global_min_dist_le [T3Space M] (g : SmoothRiemannianMetric I M)
    (hcomplete :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
      CompleteSpace M)
    (hEnorm :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      ∀ x : M, ∀ v : TangentSpace I x,
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (μ : ι -> Real) (pts : ι -> M) :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    ∀ {p qstar : M} {r ε : Real}, 0 < r -> (∀ i : ι, dist p (pts i) < r) ->
      0 ≤ ε -> (∀ i : ι, dist qstar (pts i) ≤ ε) ->
      (∀ i : ι, 0 ≤ μ i) -> (∃ i : ι, 0 < μ i) ->
      ∃ q ∈ Metric.closedBall p (2 * r),
        (∀ y : M, centerEnergy (I := I) g μ pts q ≤ centerEnergy (I := I) g μ pts y) ∧
          dist q qstar ≤ 2 * ε := by
  classical
  letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  intro p qstar r ε hr hpts hε hnear hμ_nonneg hμ_pos
  obtain ⟨q, hqball, hqmin⟩ :=
    exists_global_min (I := I) g hcomplete hEnorm μ pts hr hpts hμ_nonneg hμ_pos
  refine ⟨q, hqball, hqmin, ?_⟩
  exact centerEnergy_min_dist_le (I := I) g μ pts hε hnear hμ_nonneg hμ_pos hqmin




theorem exists_unique_min [T3Space M] (g : SmoothRiemannianMetric I M)
    (hcomplete :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
      CompleteSpace M)
    (hEnorm :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      ∀ x : M, ∀ v : TangentSpace I x,
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (μ : ι -> Real) (pts : ι -> M) :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    ∀ (join : M -> M -> Real -> M) {p : M} {r : Real}, 0 < r ->
      (∀ i : ι, dist p (pts i) < r) -> (∀ i : ι, 0 ≤ μ i) ->
      (∃ i : ι, 0 < μ i) ->
      StrictMidConvexOn join (Metric.closedBall p (2 * r))
        (centerEnergy (I := I) g μ pts) ->
      ∃ q ∈ Metric.closedBall p (2 * r),
        (∀ y : M, centerEnergy (I := I) g μ pts q ≤
          centerEnergy (I := I) g μ pts y) ∧
        ∀ y : M,
          (∀ z : M, centerEnergy (I := I) g μ pts y ≤
            centerEnergy (I := I) g μ pts z) -> y = q := by
  classical
  letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  intro join p r hr hpts hμ_nonneg hμ_pos hstrict
  obtain ⟨q, hqball, hqmin⟩ :=
    exists_global_min (I := I) g hcomplete hEnorm μ pts hr hpts hμ_nonneg hμ_pos
  refine ⟨q, hqball, hqmin, fun y hymin => ?_⟩
  have hyball : y ∈ Metric.closedBall p (2 * r) := by
    by_contra hy
    have hyfar : 2 * r ≤ dist p y := by
      rw [Metric.mem_closedBall, not_le] at hy
      exact le_of_lt (by rwa [dist_comm] at hy)
    have hp_lt_y :=
      centerEnergy_lt_far (I := I) g μ pts hr hpts hyfar hμ_nonneg hμ_pos
    have hy_le_p := hymin p
    linarith
  exact min_unique_of_mid hstrict hyball hqball
    (fun z _ => hymin z) (fun z _ => hqmin z)


theorem exists_unique_min_dist_le [T3Space M] (g : SmoothRiemannianMetric I M)
    (hcomplete :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
      CompleteSpace M)
    (hEnorm :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      ∀ x : M, ∀ v : TangentSpace I x,
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (μ : ι -> Real) (pts : ι -> M) :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    ∀ (join : M -> M -> Real -> M) {p qstar : M} {r ε : Real}, 0 < r ->
      (∀ i : ι, dist p (pts i) < r) -> 0 ≤ ε ->
      (∀ i : ι, dist qstar (pts i) ≤ ε) -> (∀ i : ι, 0 ≤ μ i) ->
      (∃ i : ι, 0 < μ i) ->
      StrictMidConvexOn join (Metric.closedBall p (2 * r))
        (centerEnergy (I := I) g μ pts) ->
      ∃ q ∈ Metric.closedBall p (2 * r),
        (∀ y : M, centerEnergy (I := I) g μ pts q ≤
          centerEnergy (I := I) g μ pts y) ∧
        dist q qstar ≤ 2 * ε ∧
        ∀ y : M,
          (∀ z : M, centerEnergy (I := I) g μ pts y ≤
            centerEnergy (I := I) g μ pts z) -> y = q := by
  classical
  letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  intro join p qstar r ε hr hpts hε hnear hμ_nonneg hμ_pos hstrict
  obtain ⟨q, hqball, hqmin, huniq⟩ :=
    exists_unique_min (I := I) g hcomplete hEnorm μ pts join hr hpts
      hμ_nonneg hμ_pos hstrict
  refine ⟨q, hqball, hqmin, ?_, huniq⟩
  exact centerEnergy_min_dist_le (I := I) g μ pts hε hnear hμ_nonneg hμ_pos hqmin





theorem exists_unique_jensen [T3Space M] (g : SmoothRiemannianMetric I M)
    (hcomplete :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
      CompleteSpace M)
    (hEnorm :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      ∀ x : M, ∀ v : TangentSpace I x,
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (μ : ι -> Real) (pts : ι -> M) :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    ∀ (join : M -> M -> Real -> M) {p : M} {r : Real}, 0 < r ->
      (∀ i : ι, dist p (pts i) < r) -> (∀ i : ι, 0 ≤ μ i) ->
      (∃ i : ι, 0 < μ i) ->
      (∀ i : ι, StrictMidJensenOn join (Metric.closedBall p (2 * r))
        (halfSqDist (pts i))) ->
      ∃ q ∈ Metric.closedBall p (2 * r),
        (∀ y : M, centerEnergy (I := I) g μ pts q ≤
          centerEnergy (I := I) g μ pts y) ∧
        ∀ y : M,
          (∀ z : M, centerEnergy (I := I) g μ pts y ≤
            centerEnergy (I := I) g μ pts z) -> y = q := by
  classical
  letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  intro join p r hr hpts hμ_nonneg hμ_pos hjensen
  exact exists_unique_min (I := I) g hcomplete hEnorm μ pts join hr hpts
    hμ_nonneg hμ_pos
    (centerEnergy_strict (I := I) g μ pts hμ_nonneg hμ_pos hjensen)



theorem exists_unique_jensen_dist_le [T3Space M] (g : SmoothRiemannianMetric I M)
    (hcomplete :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
      CompleteSpace M)
    (hEnorm :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      ∀ x : M, ∀ v : TangentSpace I x,
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (μ : ι -> Real) (pts : ι -> M) :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    ∀ (join : M -> M -> Real -> M) {p qstar : M} {r ε : Real}, 0 < r ->
      (∀ i : ι, dist p (pts i) < r) -> 0 ≤ ε ->
      (∀ i : ι, dist qstar (pts i) ≤ ε) -> (∀ i : ι, 0 ≤ μ i) ->
      (∃ i : ι, 0 < μ i) ->
      (∀ i : ι, StrictMidJensenOn join (Metric.closedBall p (2 * r))
        (halfSqDist (pts i))) ->
      ∃ q ∈ Metric.closedBall p (2 * r),
        (∀ y : M, centerEnergy (I := I) g μ pts q ≤
          centerEnergy (I := I) g μ pts y) ∧
        dist q qstar ≤ 2 * ε ∧
        ∀ y : M,
          (∀ z : M, centerEnergy (I := I) g μ pts y ≤
            centerEnergy (I := I) g μ pts z) -> y = q := by
  classical
  letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  intro join p qstar r ε hr hpts hε hnear hμ_nonneg hμ_pos hjensen
  exact exists_unique_min_dist_le (I := I) g hcomplete hEnorm μ pts join hr hpts
    hε hnear hμ_nonneg hμ_pos
    (centerEnergy_strict (I := I) g μ pts hμ_nonneg hμ_pos hjensen)




theorem exists_unique_curve [T3Space M] (g : SmoothRiemannianMetric I M)
    (hcomplete :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
      CompleteSpace M)
    (hEnorm :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      ∀ x : M, ∀ v : TangentSpace I x,
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (μ : ι -> Real) (pts : ι -> M) :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    ∀ (join : M -> M -> Real -> M) {p : M} {r : Real}, 0 < r ->
      (∀ i : ι, dist p (pts i) < r) -> (∀ i : ι, 0 ≤ μ i) ->
      (∃ i : ι, 0 < μ i) ->
      (∀ a ∈ Metric.closedBall p (2 * r), ∀ b ∈ Metric.closedBall p (2 * r),
        a ≠ b -> join a b (1 / 2 : Real) ∈ Metric.closedBall p (2 * r)) ->
      (∀ a ∈ Metric.closedBall p (2 * r), ∀ b ∈ Metric.closedBall p (2 * r),
        join a b 0 = a) ->
      (∀ a ∈ Metric.closedBall p (2 * r), ∀ b ∈ Metric.closedBall p (2 * r),
        join a b 1 = b) ->
      (∀ i : ι, ∀ a ∈ Metric.closedBall p (2 * r),
        ∀ b ∈ Metric.closedBall p (2 * r), a ≠ b ->
          StrictConvexOn Real unitInterval
            (fun t : Real => halfSqDist (pts i) (join a b t))) ->
      ∃ q ∈ Metric.closedBall p (2 * r),
        (∀ y : M, centerEnergy (I := I) g μ pts q ≤
          centerEnergy (I := I) g μ pts y) ∧
        ∀ y : M,
          (∀ z : M, centerEnergy (I := I) g μ pts y ≤
            centerEnergy (I := I) g μ pts z) -> y = q := by
  classical
  letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  intro join p r hr hpts hμ_nonneg hμ_pos hmid hzero hone hstrict
  refine exists_unique_jensen (I := I) g hcomplete hEnorm μ pts join hr hpts
    hμ_nonneg hμ_pos ?_
  intro i
  exact jensen_of_strict hmid hzero hone (fun a ha b hb hne =>
    hstrict i a ha b hb hne)



theorem exists_unique_curve_dist_le [T3Space M] (g : SmoothRiemannianMetric I M)
    (hcomplete :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
      CompleteSpace M)
    (hEnorm :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      ∀ x : M, ∀ v : TangentSpace I x,
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (μ : ι -> Real) (pts : ι -> M) :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    ∀ (join : M -> M -> Real -> M) {p qstar : M} {r ε : Real}, 0 < r ->
      (∀ i : ι, dist p (pts i) < r) -> 0 ≤ ε ->
      (∀ i : ι, dist qstar (pts i) ≤ ε) -> (∀ i : ι, 0 ≤ μ i) ->
      (∃ i : ι, 0 < μ i) ->
      (∀ a ∈ Metric.closedBall p (2 * r), ∀ b ∈ Metric.closedBall p (2 * r),
        a ≠ b -> join a b (1 / 2 : Real) ∈ Metric.closedBall p (2 * r)) ->
      (∀ a ∈ Metric.closedBall p (2 * r), ∀ b ∈ Metric.closedBall p (2 * r),
        join a b 0 = a) ->
      (∀ a ∈ Metric.closedBall p (2 * r), ∀ b ∈ Metric.closedBall p (2 * r),
        join a b 1 = b) ->
      (∀ i : ι, ∀ a ∈ Metric.closedBall p (2 * r),
        ∀ b ∈ Metric.closedBall p (2 * r), a ≠ b ->
          StrictConvexOn Real unitInterval
            (fun t : Real => halfSqDist (pts i) (join a b t))) ->
      ∃ q ∈ Metric.closedBall p (2 * r),
        (∀ y : M, centerEnergy (I := I) g μ pts q ≤
          centerEnergy (I := I) g μ pts y) ∧
        dist q qstar ≤ 2 * ε ∧
        ∀ y : M,
          (∀ z : M, centerEnergy (I := I) g μ pts y ≤
            centerEnergy (I := I) g μ pts z) -> y = q := by
  classical
  letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  intro join p qstar r ε hr hpts hε hnear hμ_nonneg hμ_pos hmid hzero hone hstrict
  refine exists_unique_jensen_dist_le (I := I) g hcomplete hEnorm μ pts join hr hpts
    hε hnear hμ_nonneg hμ_pos ?_
  intro i
  exact jensen_of_strict hmid hzero hone (fun a ha b hb hne =>
    hstrict i a ha b hb hne)

end CenterOfMass
end Riemannian
end Geometry
end DifferentialGeometry

end
