import DifferentialGeometry.Geometry.Exponential.GaussLemma
import DifferentialGeometry.Geometry.Geodesic.Equation
import DifferentialGeometry.Geometry.Geodesic.Existence
import DifferentialGeometry.Geometry.Geodesic.MaximalInterval
import DifferentialGeometry.Geometry.Geodesic.Uniqueness
import DifferentialGeometry.Geometry.Geodesic.Homogeneity
import DifferentialGeometry.Geometry.Geodesic.CrossVFReduction
import DifferentialGeometry.Geometry.Geodesic.ProjDerivative
import DifferentialGeometry.Geometry.Exponential.Defs
import DifferentialGeometry.Geometry.Exponential.Smoothness.ZeroSectionConstancy
import DifferentialGeometry.Geometry.Connection.ParallelTransport.AlongCurve
import DifferentialGeometry.Geometry.Connection.ParallelTransport.MFDerivAlongCurve
import DifferentialGeometry.Analysis.Integration.Measure.ChartDensity
import DifferentialGeometry.Geometry.Connection.LeviCivita.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.EMetricSpace.Lipschitz
import DifferentialGeometry.Geometry.Comparison.GeodesicSpeedBound



noncomputable section

open Set Function Filter Bundle Manifold
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace HopfRinow

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.MFDerivAlongCurve
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]

omit [NeZero (Module.finrank ℝ E)] in
theorem velocity_converges_of_bounded_accel
    {P P' : ℝ → E} {b C : ℝ}
    (hderiv : ∀ s : ℝ, s < b → HasDerivAt P (P' s) s)
    (hbound : ∀ s : ℝ, s < b → ‖P' s‖ ≤ C) :
    ∃ w : E, Tendsto P (𝓝[<] b) (𝓝 w) := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  haveI hNB : (𝓝[<] b).NeBot := nhdsLT_neBot b
  suffices hcauchy : Cauchy (Filter.map P (𝓝[<] b)) by
    exact cauchy_map_iff_exists_tendsto.mp hcauchy
  refine Metric.cauchy_iff.mpr ⟨Filter.map_neBot, ?_⟩
  have hC_nn : 0 ≤ C := by
    obtain ⟨s, hs⟩ := exists_lt b
    exact le_trans (norm_nonneg _) (hbound s hs)
  intro ε hε
  have hCC_pos : 0 < C + 1 := by linarith
  set η : ℝ := ε / (C + 1) with hη_def
  have hη_pos : 0 < η := div_pos hε hCC_pos
  have hIoo_mem : P '' Set.Ioo (b - η) b ∈ Filter.map P (𝓝[<] b) :=
    Filter.image_mem_map (Ioo_mem_nhdsLT (by linarith : b - η < b))
  refine ⟨P '' Set.Ioo (b - η) b, hIoo_mem, ?_⟩
  rintro x ⟨sx, hsx, rfl⟩ y ⟨sy, hsy, rfl⟩
  set s : ℝ := min sx sy with hs_def
  set t : ℝ := max sx sy with ht_def
  have hst : s ≤ t := min_le_max
  have ht_hi : t < b := max_lt hsx.2 hsy.2
  have hs_lo : b - η < s := lt_min hsx.1 hsy.1
  have ht_sub_s_lt : t - s < η := by
    rcases le_total sx sy with h | h
    · rw [hs_def, ht_def, min_eq_left h, max_eq_right h]; linarith [hsy.2, hsx.1]
    · rw [hs_def, ht_def, min_eq_right h, max_eq_left h]; linarith [hsx.2, hsy.1]
  have hmvt : ‖P t - P s‖ ≤ C * (t - s) := by
    have hIcc_sub : Set.Icc s t ⊆ Set.Iio b := fun τ hτ => lt_of_le_of_lt hτ.2 ht_hi
    have hderivW : ∀ x ∈ Set.Icc s t, HasDerivWithinAt P (P' x) (Set.Icc s t) x :=
      fun x hx => (hderiv x (hIcc_sub hx)).hasDerivWithinAt
    have hboundW : ∀ x ∈ Set.Ico s t, ‖P' x‖ ≤ C :=
      fun x hx => hbound x (lt_of_lt_of_le hx.2 ht_hi.le)
    exact norm_image_sub_le_of_norm_deriv_le_segment' hderivW hboundW t
      (right_mem_Icc.mpr hst)
  have h_dist_eq : dist (P sx) (P sy) = ‖P t - P s‖ := by
    rcases le_total sx sy with h | h
    · rw [hs_def, ht_def, min_eq_left h, max_eq_right h, dist_eq_norm, norm_sub_rev]
    · rw [hs_def, ht_def, min_eq_right h, max_eq_left h, dist_eq_norm]
  rw [h_dist_eq]
  calc ‖P t - P s‖ ≤ C * (t - s) := hmvt
    _ ≤ C * η := mul_le_mul_of_nonneg_left ht_sub_s_lt.le hC_nn
    _ < ε := by
        rw [hη_def]
        have hrw : C * (ε / (C + 1)) = ε * (C / (C + 1)) := by ring
        rw [hrw]
        have hfrac : C / (C + 1) < 1 := by rw [div_lt_one hCC_pos]; linarith
        have := mul_lt_mul_of_pos_left hfrac hε
        rwa [mul_one] at this

omit [NeZero (Module.finrank ℝ E)] in
theorem velocity_converges_of_bounded_accel_Ioo
    {P P' : ℝ → E} {a b C : ℝ} (hab : a < b)
    (hderiv : ∀ s : ℝ, s ∈ Set.Ioo a b → HasDerivAt P (P' s) s)
    (hbound : ∀ s : ℝ, s ∈ Set.Ioo a b → ‖P' s‖ ≤ C) :
    ∃ w : E, Tendsto P (𝓝[<] b) (𝓝 w) := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  haveI hNB : (𝓝[<] b).NeBot := nhdsLT_neBot b
  suffices hcauchy : Cauchy (Filter.map P (𝓝[<] b)) by
    exact cauchy_map_iff_exists_tendsto.mp hcauchy
  refine Metric.cauchy_iff.mpr ⟨Filter.map_neBot, ?_⟩
  have hC_nn : 0 ≤ C := by
    have hmid : (a + b) / 2 ∈ Set.Ioo a b := by
      constructor <;> [linarith; linarith]
    exact le_trans (norm_nonneg _) (hbound _ hmid)
  intro ε hε
  have hCC_pos : 0 < C + 1 := by linarith
  set η : ℝ := ε / (C + 1) with hη_def
  have hη_pos : 0 < η := div_pos hε hCC_pos
  set lo : ℝ := max a (b - η) with hlo_def
  have hlo_lt_b : lo < b := max_lt hab (by linarith)
  have ha_le_lo : a ≤ lo := le_max_left _ _
  have hsub : Set.Ioo lo b ⊆ Set.Ioo a b :=
    fun τ hτ => ⟨lt_of_le_of_lt ha_le_lo hτ.1, hτ.2⟩
  have hIoo_mem : P '' Set.Ioo lo b ∈ Filter.map P (𝓝[<] b) :=
    Filter.image_mem_map (Ioo_mem_nhdsLT hlo_lt_b)
  refine ⟨P '' Set.Ioo lo b, hIoo_mem, ?_⟩
  rintro x ⟨sx, hsx, rfl⟩ y ⟨sy, hsy, rfl⟩
  set s : ℝ := min sx sy with hs_def
  set t : ℝ := max sx sy with ht_def
  have hst : s ≤ t := min_le_max
  have ht_hi : t < b := max_lt hsx.2 hsy.2
  have hs_lo : lo < s := lt_min hsx.1 hsy.1
  have ht_sub_s_lt : t - s < η := by
    have hlo_ge : b - η ≤ lo := le_max_right _ _
    rcases le_total sx sy with h | h
    · rw [hs_def, ht_def, min_eq_left h, max_eq_right h]; linarith [hsy.2, hsx.1]
    · rw [hs_def, ht_def, min_eq_right h, max_eq_left h]; linarith [hsx.2, hsy.1]
  have hmvt : ‖P t - P s‖ ≤ C * (t - s) := by
    have hIcc_sub : Set.Icc s t ⊆ Set.Ioo a b := by
      intro τ hτ
      exact hsub ⟨lt_of_lt_of_le hs_lo hτ.1, lt_of_le_of_lt hτ.2 ht_hi⟩
    have hderivW : ∀ x ∈ Set.Icc s t, HasDerivWithinAt P (P' x) (Set.Icc s t) x :=
      fun x hx => (hderiv x (hIcc_sub hx)).hasDerivWithinAt
    have hboundW : ∀ x ∈ Set.Ico s t, ‖P' x‖ ≤ C :=
      fun x hx => hbound x (hIcc_sub (Set.Ico_subset_Icc_self hx))
    exact norm_image_sub_le_of_norm_deriv_le_segment' hderivW hboundW t
      (right_mem_Icc.mpr hst)
  have h_dist_eq : dist (P sx) (P sy) = ‖P t - P s‖ := by
    rcases le_total sx sy with h | h
    · rw [hs_def, ht_def, min_eq_left h, max_eq_right h, dist_eq_norm, norm_sub_rev]
    · rw [hs_def, ht_def, min_eq_right h, max_eq_left h, dist_eq_norm]
  rw [h_dist_eq]
  calc ‖P t - P s‖ ≤ C * (t - s) := hmvt
    _ ≤ C * η := mul_le_mul_of_nonneg_left ht_sub_s_lt.le hC_nn
    _ < ε := by
        rw [hη_def]
        have hrw : C * (ε / (C + 1)) = ε * (C / (C + 1)) := by ring
        rw [hrw]
        have hfrac : C / (C + 1) < 1 := by rw [div_lt_one hCC_pos]; linarith
        have := mul_lt_mul_of_pos_left hfrac hε
        rwa [mul_one] at this

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M] in
theorem chartChristoffelContraction_continuousOn_prod
    (g : SmoothRiemannianMetric I M) (α : M) :
    ContinuousOn
      (fun p : E × E => chartChristoffelContraction (I := I) g α p.1 p.1 p.2)
      (Set.univ ×ˢ interior (extChartAt I α).target) := by
  classical
  unfold chartChristoffelContraction
  refine continuousOn_finset_sum _ (fun k _ => ?_)
  refine ContinuousOn.smul ?_ continuousOn_const
  refine continuousOn_finset_sum _ (fun i _ => ?_)
  refine continuousOn_finset_sum _ (fun j _ => ?_)
  have hΓ : ContinuousOn (fun y : E => chartChristoffel (I := I) g α i j k y)
      (interior (extChartAt I α).target) :=
    (chartChristoffel_contDiffOn_interior (I := I) g α i j k).continuousOn
  have hΓp : ContinuousOn
      (fun p : E × E => chartChristoffel (I := I) g α i j k p.2)
      (Set.univ ×ˢ interior (extChartAt I α).target) :=
    hΓ.comp continuousOn_snd (fun p hp => hp.2)
  have hci : Continuous (fun p : E × E => chartCoord (E := E) i p.1) := by
    have : Continuous (fun v : E => chartCoord (E := E) i v) :=
      (((chartModelBasis E).coord i).toContinuousLinearMap).continuous
    exact this.comp continuous_fst
  have hcj : Continuous (fun p : E × E => chartCoord (E := E) j p.1) := by
    have : Continuous (fun v : E => chartCoord (E := E) j v) :=
      (((chartModelBasis E).coord j).toContinuousLinearMap).continuous
    exact this.comp continuous_fst
  exact (hΓp.mul hci.continuousOn).mul hcj.continuousOn

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M] in
theorem chartVelocity_converges_at_finite_endpoint
    (g : SmoothRiemannianMetric I M) (α : M)
    {u u' : ℝ → E} {b K₁ : ℝ} {S : Set E}
    (hS_compact : IsCompact S)
    (hS_sub : S ⊆ interior (extChartAt I α).target)
    (_hu_deriv : ∀ s : ℝ, s < b → HasDerivAt u (u' s) s)
    (hu'_deriv : ∀ s : ℝ, s < b →
      HasDerivAt u'
        (- chartChristoffelContraction (I := I) g α (u' s) (u' s) (u s)) s)
    (hu'_bound : ∀ s : ℝ, s < b → ‖u' s‖ ≤ K₁)
    (hu_mem : ∀ s : ℝ, s < b → u s ∈ S) :
    ∃ w : E, Tendsto u' (𝓝[<] b) (𝓝 w) := by
  classical
  set K : Set (E × E) := Metric.closedBall (0 : E) K₁ ×ˢ S with hK_def
  have hK_compact : IsCompact K :=
    (isCompact_closedBall (0 : E) K₁).prod hS_compact
  have hΓcont := chartChristoffelContraction_continuousOn_prod (I := I) g α
  have hΓcont_K : ContinuousOn
      (fun p : E × E => chartChristoffelContraction (I := I) g α p.1 p.1 p.2) K := by
    refine hΓcont.mono ?_
    intro p hp
    exact ⟨Set.mem_univ _, hS_sub hp.2⟩
  obtain ⟨C, hC⟩ := hK_compact.exists_bound_of_continuousOn hΓcont_K
  set P' : ℝ → E :=
    fun s => - chartChristoffelContraction (I := I) g α (u' s) (u' s) (u s) with hP'_def
  have hderiv_pf : ∀ s : ℝ, s < b → HasDerivAt u' (P' s) s := fun s hs => hu'_deriv s hs
  have hbound_pf : ∀ s : ℝ, s < b → ‖P' s‖ ≤ C := by
    intro s hs
    have hmem : ((u' s, u s) : E × E) ∈ K := by
      refine ⟨?_, hu_mem s hs⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hu'_bound s hs
    have hCs :
        ‖chartChristoffelContraction (I := I) g α (u' s) (u' s) (u s)‖ ≤ C :=
      hC ((u' s, u s) : E × E) hmem
    rw [hP'_def, norm_neg]
    exact hCs
  exact velocity_converges_of_bounded_accel (P := u') (P' := P') (b := b) (C := C)
    hderiv_pf hbound_pf

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M] in
theorem chartVelocity_converges_at_finite_endpoint_Ioo
    (g : SmoothRiemannianMetric I M) (α : M)
    {u u' : ℝ → E} {a b K₁ : ℝ} {S : Set E} (hab : a < b)
    (hS_compact : IsCompact S)
    (hS_sub : S ⊆ interior (extChartAt I α).target)
    (_hu_deriv : ∀ s : ℝ, s ∈ Set.Ioo a b → HasDerivAt u (u' s) s)
    (hu'_deriv : ∀ s : ℝ, s ∈ Set.Ioo a b →
      HasDerivAt u'
        (- chartChristoffelContraction (I := I) g α (u' s) (u' s) (u s)) s)
    (hu'_bound : ∀ s : ℝ, s ∈ Set.Ioo a b → ‖u' s‖ ≤ K₁)
    (hu_mem : ∀ s : ℝ, s ∈ Set.Ioo a b → u s ∈ S) :
    ∃ w : E, Tendsto u' (𝓝[<] b) (𝓝 w) := by
  classical
  set K : Set (E × E) := Metric.closedBall (0 : E) K₁ ×ˢ S with hK_def
  have hK_compact : IsCompact K :=
    (isCompact_closedBall (0 : E) K₁).prod hS_compact
  have hΓcont := chartChristoffelContraction_continuousOn_prod (I := I) g α
  have hΓcont_K : ContinuousOn
      (fun p : E × E => chartChristoffelContraction (I := I) g α p.1 p.1 p.2) K := by
    refine hΓcont.mono ?_
    intro p hp
    exact ⟨Set.mem_univ _, hS_sub hp.2⟩
  obtain ⟨C, hC⟩ := hK_compact.exists_bound_of_continuousOn hΓcont_K
  set P' : ℝ → E :=
    fun s => - chartChristoffelContraction (I := I) g α (u' s) (u' s) (u s) with hP'_def
  have hderiv_pf : ∀ s : ℝ, s ∈ Set.Ioo a b → HasDerivAt u' (P' s) s :=
    fun s hs => hu'_deriv s hs
  have hbound_pf : ∀ s : ℝ, s ∈ Set.Ioo a b → ‖P' s‖ ≤ C := by
    intro s hs
    have hmem : ((u' s, u s) : E × E) ∈ K := by
      refine ⟨?_, hu_mem s hs⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hu'_bound s hs
    have hCs :
        ‖chartChristoffelContraction (I := I) g α (u' s) (u' s) (u s)‖ ≤ C :=
      hC ((u' s, u s) : E × E) hmem
    rw [hP'_def, norm_neg]
    exact hCs
  exact velocity_converges_of_bounded_accel_Ioo (P := u') (P' := P') (a := a)
    (b := b) (C := C) hab hderiv_pf hbound_pf

private def chartGramQuad (g : SmoothRiemannianMetric I M) (y : M)
    (z : E) (V : E) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
    chartGramOnE (I := I) g y i j z *
      chartCoord (E := E) i V * chartCoord (E := E) j V

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M] in
private lemma chartGramQuad_eq_inner
    (g : SmoothRiemannianMetric I M) (y : M) {z : E}
    (_hz : z ∈ (extChartAt I y).target) (V : E) :
    chartGramQuad (I := I) g y z V =
      g.inner ((extChartAt I y).symm z)
        ((trivializationAt E (TangentSpace I) y).symmL ℝ ((extChartAt I y).symm z) V)
        ((trivializationAt E (TangentSpace I) y).symmL ℝ ((extChartAt I y).symm z) V) := by
  classical
  set x : M := (extChartAt I y).symm z with hx_def
  rw [chartGramQuad,
    inner_eq_chartGramOnE_bilinear_on_baseSet (I := I) g y (x := x) V V]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [chartGramOnE_def, hx_def]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M] in
private lemma chartGramQuad_pos
    (g : SmoothRiemannianMetric I M) (y : M) {z : E}
    (hz : z ∈ (extChartAt I y).target) {V : E} (hV : V ≠ 0) :
    0 < chartGramQuad (I := I) g y z V := by
  classical
  rw [chartGramQuad_eq_inner (I := I) g y hz V]
  set x : M := (extChartAt I y).symm z with hx_def
  have hx_src : x ∈ (chartAt H y).source := by
    rw [hx_def, ← extChartAt_source_eq_chartAt_source (I := I)]
    exact (extChartAt I y).map_target hz
  have hbase : x ∈ (trivializationAt E (TangentSpace I) y).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact hx_src
  have hsymm_ne : (trivializationAt E (TangentSpace I) y).symmL ℝ x V ≠ 0 := by
    intro hzero
    apply hV
    have hround :
        ((trivializationAt E (TangentSpace I) y).continuousLinearMapAt ℝ x)
            ((trivializationAt E (TangentSpace I) y).symmL ℝ x V) = V :=
      (trivializationAt E (TangentSpace I) y).continuousLinearMapAt_symmL
        (R := ℝ) hbase V
    rw [hzero, map_zero] at hround
    exact hround.symm
  exact g.pos x _ hsymm_ne

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M] in
private lemma chartGramQuad_smul
    (g : SmoothRiemannianMetric I M) (y : M) (z : E) (a : ℝ) (V : E) :
    chartGramQuad (I := I) g y z (a • V) = a ^ 2 * chartGramQuad (I := I) g y z V := by
  classical
  unfold chartGramQuad
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [chartCoord_smul, chartCoord_smul]
  ring

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M] in
private lemma chartGramQuad_continuousOn
    (g : SmoothRiemannianMetric I M) (y : M) :
    ContinuousOn (fun p : E × E => chartGramQuad (I := I) g y p.1 p.2)
      ((extChartAt I y).target ×ˢ (Set.univ : Set E)) := by
  classical
  unfold chartGramQuad
  refine continuousOn_finset_sum _ (fun i _ => continuousOn_finset_sum _ (fun j _ => ?_))
  have hG : ContinuousOn (fun p : E × E => chartGramOnE (I := I) g y i j p.1)
      ((extChartAt I y).target ×ˢ (Set.univ : Set E)) :=
    ((chartGramOnE_contDiffOn (I := I) g y i j).continuousOn).comp continuousOn_fst
      (fun p hp => hp.1)
  have hci : Continuous (fun p : E × E => chartCoord (E := E) i p.2) :=
    (((chartModelBasis E).coord i).toContinuousLinearMap).continuous.comp continuous_snd
  have hcj : Continuous (fun p : E × E => chartCoord (E := E) j p.2) :=
    (((chartModelBasis E).coord j).toContinuousLinearMap).continuous.comp continuous_snd
  exact (hG.mul hci.continuousOn).mul hcj.continuousOn

omit [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M] in
private lemma exists_chartGramQuad_lower_bound
    (g : SmoothRiemannianMetric I M) (y : M) {S : Set E}
    (hS_compact : IsCompact S) (hS_sub : S ⊆ (extChartAt I y).target)
    (hS_ne : S.Nonempty) :
    ∃ m : ℝ, 0 < m ∧ ∀ z ∈ S, ∀ V : E, m * ‖V‖ ^ 2 ≤ chartGramQuad (I := I) g y z V := by
  classical
  have hfin_pos : 0 < Module.finrank ℝ E := Nat.pos_of_ne_zero (NeZero.ne _)
  haveI : Nontrivial E := Module.nontrivial_of_finrank_pos hfin_pos
  set T : Set (E × E) := S ×ˢ Metric.sphere (0 : E) 1 with hT_def
  have hsphere_compact : IsCompact (Metric.sphere (0 : E) 1) :=
    isCompact_sphere (0 : E) 1
  have hT_compact : IsCompact T := hS_compact.prod hsphere_compact
  have hsphere_ne : (Metric.sphere (0 : E) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  have hT_ne : T.Nonempty := hS_ne.prod hsphere_ne
  have hQcont : ContinuousOn (fun p : E × E => chartGramQuad (I := I) g y p.1 p.2) T := by
    refine (chartGramQuad_continuousOn (I := I) g y).mono ?_
    intro p hp
    exact ⟨hS_sub hp.1, Set.mem_univ _⟩
  obtain ⟨p₀, hp₀_mem, hp₀_min⟩ :=
    hT_compact.exists_isMinOn hT_ne hQcont
  set m : ℝ := chartGramQuad (I := I) g y p₀.1 p₀.2 with hm_def
  have hp₀1_mem : p₀.1 ∈ S := hp₀_mem.1
  have hp₀2_sphere : p₀.2 ∈ Metric.sphere (0 : E) 1 := hp₀_mem.2
  have hp₀2_ne : p₀.2 ≠ 0 := by
    intro hz
    rw [Metric.mem_sphere, hz, dist_self] at hp₀2_sphere
    exact one_ne_zero hp₀2_sphere.symm
  have hm_pos : 0 < m :=
    chartGramQuad_pos (I := I) g y (hS_sub hp₀1_mem) hp₀2_ne
  refine ⟨m, hm_pos, ?_⟩
  intro z hz V
  rcases eq_or_ne V 0 with hV | hV
  · subst hV; simp [chartGramQuad]
  · set r : ℝ := ‖V‖ with hr_def
    have hr_pos : 0 < r := by rw [hr_def]; exact norm_pos_iff.mpr hV
    set Vhat : E := r⁻¹ • V with hVhat_def
    have hVhat_unit : Vhat ∈ Metric.sphere (0 : E) 1 := by
      rw [Metric.mem_sphere, dist_zero_right, hVhat_def, norm_smul, norm_inv,
        Real.norm_eq_abs, abs_of_pos hr_pos, hr_def]
      field_simp
    have hmem_T : ((z, Vhat) : E × E) ∈ T := ⟨hz, hVhat_unit⟩
    have hmin : m ≤ chartGramQuad (I := I) g y z Vhat :=
      isMinOn_iff.mp hp₀_min ((z, Vhat) : E × E) hmem_T
    have hV_eq : V = r • Vhat := by
      rw [hVhat_def, smul_smul, mul_inv_cancel₀ (ne_of_gt hr_pos), one_smul]
    have hscale : chartGramQuad (I := I) g y z V = r ^ 2 * chartGramQuad (I := I) g y z Vhat := by
      conv_lhs => rw [hV_eq]
      rw [chartGramQuad_smul]
    rw [hscale, hr_def]
    have hr2_nn : (0 : ℝ) ≤ ‖V‖ ^ 2 := sq_nonneg _
    calc m * ‖V‖ ^ 2 = ‖V‖ ^ 2 * m := by ring
      _ ≤ ‖V‖ ^ 2 * chartGramQuad (I := I) g y z Vhat :=
          mul_le_mul_of_nonneg_left hmin hr2_nn

omit
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M] in
theorem chartVelocity_bound_near_limit
    (g : SmoothRiemannianMetric I M) (y : M) {γ : ℝ → M} {a b c : ℝ}
    (hab : a < b) (hc_nonneg : 0 ≤ c)
    (hγ_mdiff : MDifferentiableOn 𝓘(ℝ, ℝ) I γ (Set.Ioo a b))
    (hy_lim : Tendsto γ (𝓝[<] b) (𝓝 y))
    (hSpeedSq : ∀ s ∈ Set.Ioo a b,
      (g.inner (γ s)) (mfderiv 𝓘(ℝ, ℝ) I γ s 1) (mfderiv 𝓘(ℝ, ℝ) I γ s 1) ≤ c ^ 2) :
    ∃ (ε K : ℝ) (S : Set E), 0 < ε ∧ IsCompact S ∧
      S ⊆ interior (extChartAt I y).target ∧
      (∀ s ∈ Set.Ioo (b - ε) b,
        ‖deriv (chartCurve (I := I) y γ) s‖ ≤ K ∧
          chartCurve (I := I) y γ s ∈ S) := by
  classical
  have hy_src : y ∈ (chartAt H y).source := mem_chart_source H y
  have hy_ext_src : y ∈ (extChartAt I y).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hy_src
  have hy_target : extChartAt I y y ∈ (extChartAt I y).target :=
    (extChartAt I y).map_source hy_ext_src
  have hy_interior : extChartAt I y y ∈ interior (extChartAt I y).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) y hy_target
  obtain ⟨ρ, hρ_pos, hρ_sub⟩ :=
    Metric.isOpen_iff.mp isOpen_interior _ hy_interior
  set S : Set E := Metric.closedBall (extChartAt I y y) (ρ / 2) with hS_def
  have hS_compact : IsCompact S := isCompact_closedBall _ _
  have hS_sub : S ⊆ interior (extChartAt I y).target := by
    intro z hz
    refine hρ_sub ?_
    rw [Metric.mem_ball]
    rw [hS_def, Metric.mem_closedBall] at hz
    linarith [hz]
  have hS_ne : S.Nonempty := ⟨extChartAt I y y, by
    rw [hS_def, Metric.mem_closedBall, dist_self]; linarith⟩
  obtain ⟨m, hm_pos, hm_bound⟩ :=
    exists_chartGramQuad_lower_bound (I := I) g y hS_compact
      (hS_sub.trans interior_subset) hS_ne
  set K : ℝ := c / Real.sqrt m with hK_def
  have hu_lim : Tendsto (chartCurve (I := I) y γ) (𝓝[<] b) (𝓝 (extChartAt I y y)) := by
    have hcont_at : ContinuousAt (extChartAt I y) y :=
      (continuousAt_extChartAt (I := I) y)
    have : Tendsto (fun s => extChartAt I y (γ s)) (𝓝[<] b) (𝓝 (extChartAt I y y)) :=
      hcont_at.tendsto.comp hy_lim
    simpa [chartCurve] using this
  have hu_mem_ev : ∀ᶠ s in 𝓝[<] b, chartCurve (I := I) y γ s ∈ S := by
    have hball_nhds : Metric.closedBall (extChartAt I y y) (ρ / 2) ∈
        𝓝 (extChartAt I y y) :=
      Metric.closedBall_mem_nhds _ (by linarith)
    exact hu_lim hball_nhds
  have hsrc_ev : ∀ᶠ s in 𝓝[<] b, γ s ∈ (chartAt H y).source := by
    have hsrc_nhds : (chartAt H y).source ∈ 𝓝 y :=
      (chartAt H y).open_source.mem_nhds hy_src
    exact hy_lim hsrc_nhds
  obtain ⟨U, hU_nhds, hU_sub⟩ :=
    mem_nhdsWithin_iff_exists_mem_nhds_inter.mp
      (Filter.inter_mem hu_mem_ev hsrc_ev)
  obtain ⟨δ₀, hδ₀_pos, hδ₀_sub⟩ := Metric.mem_nhds_iff.mp hU_nhds
  set δ : ℝ := min δ₀ ((b - a) / 2) with hδ_def
  have hδ_pos : 0 < δ := lt_min hδ₀_pos (by linarith)
  have hδ_le : δ ≤ δ₀ := min_le_left _ _
  have hδ_le2 : δ ≤ (b - a) / 2 := min_le_right _ _
  have hba_gt : a < b - δ := by linarith
  refine ⟨δ, K, S, hδ_pos, hS_compact, hS_sub, ?_⟩
  intro s hs
  have hs_ball : s ∈ Metric.ball b δ₀ := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    refine ⟨by linarith [hs.1, hδ_le], by linarith [hs.2]⟩
  have hs_Ioo : s ∈ Set.Ioo a b := ⟨lt_trans hba_gt hs.1, hs.2⟩
  have hs_Iio : s ∈ Set.Iio b := hs.2
  have hs_both : chartCurve (I := I) y γ s ∈ S ∧ γ s ∈ (chartAt H y).source :=
    hU_sub ⟨hδ₀_sub hs_ball, hs_Iio⟩
  obtain ⟨hu_memS, hγ_src⟩ := hs_both
  refine ⟨?_, hu_memS⟩
  set V : E := deriv (chartCurve (I := I) y γ) s with hV_def
  have hVeq : (fderiv ℝ ((extChartAt I y) ∘ γ) s : ℝ →L[ℝ] E) (1 : ℝ) = V := by
    rw [hV_def, deriv]; rfl
  have hγ_s : MDifferentiableAt 𝓘(ℝ, ℝ) I γ s :=
    (hγ_mdiff s hs_Ioo).mdifferentiableAt (isOpen_Ioo.mem_nhds hs_Ioo)
  have hraw := raw_mfderiv_eq_symmL_fderiv_at (I := I) (γ := γ) (α := y)
    (s := s) hγ_s hγ_src
  rw [hVeq] at hraw
  have hu_target : chartCurve (I := I) y γ s ∈ (extChartAt I y).target :=
    interior_subset (hS_sub hu_memS)
  have hinv : (extChartAt I y).symm (chartCurve (I := I) y γ s) = γ s := by
    rw [chartCurve_def]
    exact (extChartAt I y).left_inv (by
      rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hγ_src)
  have hspeed_eq :
      chartGramQuad (I := I) g y (chartCurve (I := I) y γ s) V =
        (g.inner (γ s)) (mfderiv 𝓘(ℝ, ℝ) I γ s 1) (mfderiv 𝓘(ℝ, ℝ) I γ s 1) := by
    rw [chartGramQuad_eq_inner (I := I) g y hu_target V, hinv]
    rw [← hraw]
    rfl
  have hQ_le : chartGramQuad (I := I) g y (chartCurve (I := I) y γ s) V ≤ c ^ 2 := by
    rw [hspeed_eq]; exact hSpeedSq s hs_Ioo
  have hlow : m * ‖V‖ ^ 2 ≤ c ^ 2 :=
    le_trans (hm_bound (chartCurve (I := I) y γ s) hu_memS V) hQ_le
  have hVsq_le : ‖V‖ ^ 2 ≤ c ^ 2 / m := by
    rw [le_div_iff₀ hm_pos]; linarith [hlow]
  have hsqrt_m_pos : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm_pos
  rw [hK_def]
  rw [le_div_iff₀ hsqrt_m_pos]
  have hlhs_nn : 0 ≤ ‖V‖ * Real.sqrt m := mul_nonneg (norm_nonneg _) hsqrt_m_pos.le
  have hsq : (‖V‖ * Real.sqrt m) ^ 2 ≤ c ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hm_pos.le]
    calc ‖V‖ ^ 2 * m ≤ (c ^ 2 / m) * m :=
          mul_le_mul_of_nonneg_right hVsq_le hm_pos.le
      _ = c ^ 2 := by field_simp
  have := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq hlhs_nn, Real.sqrt_sq hc_nonneg] at this

end HopfRinow
end Riemannian
end Geometry
end DifferentialGeometry
