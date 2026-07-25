import DifferentialGeometry.Geometry.Exponential.Smoothness.AtZero
import DifferentialGeometry.Analysis.ODE.Flow.C1Regularity.FrechetDerivative



noncomputable section

open Set Function Filter Metric Bundle Manifold Real
open scoped Topology NNReal Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Analysis.ODE
open DifferentialGeometry.Analysis.ODE.Flow
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

section ChartPhaseVFLinearization

variable [I.Boundaryless]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma chartChristoffel_scalarSummand_hasFDerivAt_zero
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j k : Fin (Module.finrank ℝ E)) {x : E}
    (hx : x ∈ interior (extChartAt I α).target) :
    HasFDerivAt
      (fun z : E × E =>
        chartChristoffel (I := I) g α i j k z.1 *
          chartCoord (E := E) i z.2 *
          chartCoord (E := E) j z.2)
      (0 : E × E →L[ℝ] ℝ) (x, (0 : E)) := by
  classical
  have hbase : ContDiffOn ℝ ∞ (chartChristoffel (I := I) g α i j k)
      (interior (extChartAt I α).target) :=
    chartChristoffel_contDiffOn_interior (I := I) g α i j k
  have hbaseAt : ContDiffAt ℝ ∞ (chartChristoffel (I := I) g α i j k) x :=
    hbase.contDiffAt (isOpen_interior.mem_nhds hx)
  have hΓ_diffAt : DifferentiableAt ℝ
      (fun z : E × E => chartChristoffel (I := I) g α i j k z.1) (x, (0 : E)) := by
    have hcomp : ContDiffAt ℝ ∞
        ((chartChristoffel (I := I) g α i j k) ∘ (Prod.fst : E × E → E))
        ((x, (0 : E)) : E × E) := by
      have hfstAt : ContDiffAt ℝ ∞ (Prod.fst : E × E → E) ((x, (0 : E)) : E × E) :=
        contDiff_fst.contDiffAt
      exact hbaseAt.comp _ hfstAt
    have hcomp' : ContDiffAt ℝ ∞
        (fun z : E × E => chartChristoffel (I := I) g α i j k z.1)
        ((x, (0 : E)) : E × E) := hcomp
    have h0 : (∞ : WithTop ℕ∞) ≠ 0 := by decide
    exact hcomp'.differentiableAt h0
  let Li : E →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap ((chartModelBasis E).coord i)
  let Lj : E →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap ((chartModelBasis E).coord j)
  have hci_z : HasFDerivAt (fun z : E × E => chartCoord (E := E) i z.2)
      (Li.comp (ContinuousLinearMap.snd ℝ E E)) ((x, (0 : E)) : E × E) :=
    (Li.hasFDerivAt).comp ((x, (0 : E)) : E × E)
      ((ContinuousLinearMap.snd ℝ E E).hasFDerivAt)
  have hcj_z : HasFDerivAt (fun z : E × E => chartCoord (E := E) j z.2)
      (Lj.comp (ContinuousLinearMap.snd ℝ E E)) ((x, (0 : E)) : E × E) :=
    (Lj.hasFDerivAt).comp ((x, (0 : E)) : E × E)
      ((ContinuousLinearMap.snd ℝ E E).hasFDerivAt)
  set fA := fun z : E × E => chartChristoffel (I := I) g α i j k z.1
  set fB := fun z : E × E => chartCoord (E := E) i z.2
  set fC := fun z : E × E => chartCoord (E := E) j z.2
  have hA_hfd : HasFDerivAt fA (fderiv ℝ fA (x, (0 : E))) (x, (0 : E)) :=
    hΓ_diffAt.hasFDerivAt
  have hB0 : fB (x, (0 : E)) = 0 := by
    change chartCoord (E := E) i (0 : E) = 0
    exact chartCoord_zero (E := E) i
  have hC0 : fC (x, (0 : E)) = 0 := by
    change chartCoord (E := E) j (0 : E) = 0
    exact chartCoord_zero (E := E) j
  have hAB := hA_hfd.mul hci_z
  have hABC := hAB.mul hcj_z
  have hAB0 : (fA * fB) (x, (0 : E)) = 0 := by
    change fA (x, (0 : E)) * fB (x, (0 : E)) = 0
    rw [hB0]; ring
  have hfn_eq :
      (fun z : E × E => chartChristoffel (I := I) g α i j k z.1 *
          chartCoord (E := E) i z.2 * chartCoord (E := E) j z.2) =
        (fun z : E × E => (fA * fB) z * fC z) := by
    funext z; change fA z * fB z * fC z = (fA z * fB z) * fC z; ring
  rw [hfn_eq]
  have := hABC
  rw [hAB0, hC0, zero_smul, zero_smul, zero_add] at this
  exact this

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma chartChristoffelContraction_hasFDerivAt_zero
    (g : SmoothRiemannianMetric I M) (α : M) {x : E}
    (hx : x ∈ interior (extChartAt I α).target) :
    HasFDerivAt
      (fun z : E × E => chartChristoffelContraction (I := I) g α z.2 z.2 z.1)
      (0 : E × E →L[ℝ] E) (x, (0 : E)) := by
  classical
  have hsum : HasFDerivAt
      (fun z : E × E =>
        ∑ k : Fin (Module.finrank ℝ E),
          (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
              chartChristoffel (I := I) g α i j k z.1 *
                chartCoord (E := E) i z.2 *
                chartCoord (E := E) j z.2) •
            chartModelBasis E k)
      (∑ _k : Fin (Module.finrank ℝ E), (0 : E × E →L[ℝ] E)) (x, (0 : E)) := by
    refine HasFDerivAt.fun_sum (fun k _ => ?_)
    have hscalar : HasFDerivAt
        (fun z : E × E => ∑ i : Fin (Module.finrank ℝ E),
              ∑ j : Fin (Module.finrank ℝ E),
                chartChristoffel (I := I) g α i j k z.1 *
                  chartCoord (E := E) i z.2 *
                  chartCoord (E := E) j z.2)
        (∑ _i : Fin (Module.finrank ℝ E), ∑ _j : Fin (Module.finrank ℝ E),
          (0 : E × E →L[ℝ] ℝ)) (x, (0 : E)) := by
      refine HasFDerivAt.fun_sum (fun i _ => ?_)
      refine HasFDerivAt.fun_sum (fun j _ => ?_)
      exact chartChristoffel_scalarSummand_hasFDerivAt_zero
        (I := I) (g := g) (α := α) i j k hx
    have hscalar_zero :
        (∑ _i : Fin (Module.finrank ℝ E), ∑ _j : Fin (Module.finrank ℝ E),
          (0 : E × E →L[ℝ] ℝ)) = 0 := by simp
    rw [hscalar_zero] at hscalar
    set scalar : E × E → ℝ := fun z =>
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g α i j k z.1 *
            chartCoord (E := E) i z.2 *
            chartCoord (E := E) j z.2
    have hscalar_x0 : scalar (x, (0 : E)) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro i _
      refine Finset.sum_eq_zero ?_
      intro j _
      have h2 : chartCoord (E := E) j (x, (0 : E)).2 = 0 := by
        change chartCoord (E := E) j (0 : E) = 0
        exact chartCoord_zero (E := E) j
      rw [h2]; ring
    let Lk : ℝ →L[ℝ] E :=
      (ContinuousLinearMap.id ℝ ℝ).smulRight (chartModelBasis E k)
    have hLk : HasFDerivAt (fun s : ℝ => s • (chartModelBasis E k))
        Lk (scalar (x, (0 : E))) := by
      have h1 : HasFDerivAt (Lk : ℝ → E) Lk (scalar (x, (0 : E))) := Lk.hasFDerivAt
      exact h1
    have hcomp := hLk.comp ((x, (0 : E)) : E × E) hscalar
    have hcomp_eq :
        Lk.comp (0 : E × E →L[ℝ] ℝ) = (0 : E × E →L[ℝ] E) :=
      ContinuousLinearMap.comp_zero _
    have hfn_eq2 :
        (fun s : ℝ => s • (chartModelBasis E k)) ∘ scalar =
          (fun z : E × E => scalar z • (chartModelBasis E k)) := by
      funext z; rfl
    rw [hfn_eq2] at hcomp
    rw [hcomp_eq] at hcomp
    convert hcomp using 1
  have hsum0 : (∑ _k : Fin (Module.finrank ℝ E), (0 : E × E →L[ℝ] E)) = 0 := by simp
  rw [hsum0] at hsum
  have hfn_eq : (fun z : E × E => chartChristoffelContraction (I := I) g α z.2 z.2 z.1) =
      (fun z : E × E =>
        ∑ k : Fin (Module.finrank ℝ E),
          (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
              chartChristoffel (I := I) g α i j k z.1 *
                chartCoord (E := E) i z.2 *
                chartCoord (E := E) j z.2) •
            chartModelBasis E k) := by
    funext z
    rfl
  rw [hfn_eq]
  exact hsum

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma chartPhaseVF_hasFDerivAt_zero_section
    (g : SmoothRiemannianMetric I M) (α : M) {x : E}
    (hx : x ∈ interior (extChartAt I α).target) :
    HasFDerivAt (chartPhaseVF (I := I) g α)
      ((ContinuousLinearMap.snd ℝ E E).prod (0 : E × E →L[ℝ] E))
      ((x, (0 : E)) : E × E) := by
  classical
  have hfst : HasFDerivAt (fun z : E × E => z.2)
      (ContinuousLinearMap.snd ℝ E E) ((x, (0 : E)) : E × E) :=
    (ContinuousLinearMap.snd ℝ E E).hasFDerivAt
  have hΓ := chartChristoffelContraction_hasFDerivAt_zero (I := I) g (α := α) hx
  have hsnd : HasFDerivAt
      (fun z : E × E => -chartChristoffelContraction (I := I) g α z.2 z.2 z.1)
      (-0 : E × E →L[ℝ] E) ((x, (0 : E)) : E × E) := hΓ.neg
  have h0_eq : (-0 : E × E →L[ℝ] E) = (0 : E × E →L[ℝ] E) := by simp
  rw [h0_eq] at hsnd
  have hcombined := hfst.prodMk hsnd
  exact hcombined

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma chartPhaseVFCutoff_eventuallyEq_chartPhaseVF
    (g : SmoothRiemannianMetric I M) (α : M)
    {z₀ : E × E} (b : ContDiffBump z₀)
    {z : E × E} (hz : z ∈ Metric.ball z₀ b.rIn) :
    chartPhaseVFCutoff (I := I) g α z₀ b =ᶠ[𝓝 z] chartPhaseVF (I := I) g α := by
  have hpos : 0 < b.rIn - dist z z₀ := by
    have := Metric.mem_ball.mp hz; linarith
  refine Filter.eventuallyEq_of_mem
    (s := Metric.ball z (b.rIn - dist z z₀))
    (Metric.ball_mem_nhds z hpos) ?_
  intro w hw
  have hw_dist : dist w z < b.rIn - dist z z₀ := Metric.mem_ball.mp hw
  have hw_z₀ : dist w z₀ ≤ b.rIn := by
    have := dist_triangle w z z₀; linarith
  exact chartPhaseVFCutoff_eq_of_mem_closedBall (I := I) g α z₀ b
    (Metric.mem_closedBall.mpr hw_z₀)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma chartPhaseVFCutoff_hasFDerivAt_zero_section
    (g : SmoothRiemannianMetric I M) (α : M) {x : E}
    (hx : x ∈ interior (extChartAt I α).target)
    {z₀ : E × E} (b : ContDiffBump z₀)
    (hz_in : ((x, (0 : E)) : E × E) ∈ Metric.ball z₀ b.rIn) :
    HasFDerivAt (chartPhaseVFCutoff (I := I) g α z₀ b)
      ((ContinuousLinearMap.snd ℝ E E).prod (0 : E × E →L[ℝ] E))
      ((x, (0 : E)) : E × E) := by
  have heq := chartPhaseVFCutoff_eventuallyEq_chartPhaseVF
    (I := I) g α (z₀ := z₀) b (z := ((x, (0 : E)) : E × E)) hz_in
  have hVF := chartPhaseVF_hasFDerivAt_zero_section (I := I) g (α := α) hx
  exact hVF.congr_of_eventuallyEq heq

end ChartPhaseVFLinearization

section CombinedData

variable [I.Boundaryless] [CompleteSpace E]

omit [NeZero (Module.finrank ℝ E)] in
private theorem exists_combined_chartFlow_data
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ (Φ : (E × E) × ℝ → E × E)
      (b : ContDiffBump ((extChartAt I p p, (0 : E)) : E × E))
      (r : ℝ≥0) (ε ρ T T_match t' Mb : ℝ),
      0 < r ∧ 0 < ε ∧ 0 < ρ ∧ 0 < T ∧ 0 < T_match ∧ T_match < T ∧ T_match ≤ ε ∧
      0 < t' ∧ t' < T_match ∧ 0 ≤ Mb ∧ Mb * t' < 1 ∧
      Metric.closedBall ((extChartAt I p p, (0 : E)) : E × E) b.rOut ⊆
        (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E) ∧
      IsLocalFlow (chartPhaseVFTime (I := I) g p
          ((extChartAt I p p, (0 : E)) : E × E) b)
        (0 : ℝ) ((extChartAt I p p, (0 : E)) : E × E) r (-ε) ε Φ ∧
      ContDiffOn ℝ 1 Φ
        ((Metric.ball ((extChartAt I p p, (0 : E)) : E × E) ρ) ×ˢ Set.Ioo (-T) T) ∧
      (∀ s ∈ Set.Ioo (-T_match) T_match,
        Φ (((extChartAt I p p, (0 : E)) : E × E), s) =
          ((extChartAt I p p, (0 : E)) : E × E)) ∧
      (∀ τ : ℝ, ∀ z : E × E,
        ‖fderiv ℝ (chartPhaseVFTime (I := I) g p
          ((extChartAt I p p, (0 : E)) : E × E) b τ) z‖ ≤ Mb) ∧
      (∀ v ∈ Metric.ball (0 : E) ρ,
        Φ (((extChartAt I p p, v) : E × E), 0) = ((extChartAt I p p, v) : E × E)) ∧
      (∀ v ∈ Metric.ball (0 : E) ρ, ∀ s ∈ Set.Icc (-T_match) T_match,
        Φ (((extChartAt I p p, v) : E × E), s) ∈
          (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E)) ∧
      (∀ v ∈ Metric.ball (0 : E) ρ, ∀ s ∈ Set.Ioo (-T_match) T_match,
        HasDerivAt (fun s' : ℝ => Φ (((extChartAt I p p, v) : E × E), s'))
          (chartPhaseVF (I := I) g p
            (Φ (((extChartAt I p p, v) : E × E), s))) s) := by
  classical
  set x₀ : E := extChartAt I p p with hx₀_def
  have hx₀_src : p ∈ (extChartAt I p).source := mem_extChartAt_source (I := I) p
  have hx₀_target : x₀ ∈ (extChartAt I p).target :=
    (extChartAt I p).map_source hx₀_src
  have hx₀_interior : x₀ ∈ interior (extChartAt I p).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) p hx₀_target
  obtain ⟨b, rN, εN, ρ_V4, T_V4, Φ, hr, hε, hρ_V4_pos, hT_V4_pos, hb_sub, hΦ_ILF,
    hΦ_cd_V4, hΦ_init0⟩ :=
    Geodesic.exists_chartPhase_contDiffOn_isLocalFlow_combined
      (I := I) (g := g) (α := p) (x₀ := x₀) (v₀ := (0 : E)) hx₀_interior
  obtain ⟨ρ₁, T₁, hρ₁_pos, hT₁_pos, hρ₁_le_ρ_V4, hT₁_lt_T_V4, h_orbit_in⟩ :=
    exists_uniform_orbit_in_inner_ball (I := I) (p := p)
      (x₀ := x₀) hx₀_def
      (b := b) (ρ_V4 := ρ_V4) (T_V4 := T_V4) hρ_V4_pos hT_V4_pos
      (Φ := Φ) hΦ_cd_V4 hΦ_init0
  obtain ⟨Mglob, hMglob_nn, hMglob_bd⟩ :=
    Geodesic.exists_bound_fderiv_chartPhaseVFCutoff (I := I) g p
      ((x₀, (0 : E)) : E × E) b hb_sub
  have hM_bd : ∀ τ : ℝ, ∀ z : E × E,
      ‖fderiv ℝ (chartPhaseVFTime (I := I) g p ((x₀, (0 : E)) : E × E) b τ) z‖ ≤ Mglob :=
    fun _ z => hMglob_bd z
  have hconst_ev : ∀ᶠ s in 𝓝 (0 : ℝ),
      Φ (((x₀, (0 : E)) : E × E), s) = ((x₀, (0 : E)) : E × E) :=
    chartFlow_zero_section_eventually_const (I := I) (g := g) (p := p)
      (Φ := Φ) (b := b) (r := rN) (ε := εN) hΦ_ILF hb_sub hr hε
  rcases Filter.eventually_iff_exists_mem.mp hconst_ev with ⟨U, hU_nhds, hU⟩
  rcases _root_.mem_nhds_iff.mp hU_nhds with ⟨V, hVU, hV_open, hV_mem_zero⟩
  rcases (Metric.isOpen_iff.mp hV_open) (0 : ℝ) hV_mem_zero with
    ⟨δ_match, hδ_match_pos, hδ_sub⟩
  set ρ : ℝ := min ρ₁ ((rN : ℝ) / 2) with hρ_def
  have hρ_pos : 0 < ρ := by
    apply lt_min hρ₁_pos
    have : (0 : ℝ) < (rN : ℝ) := hr
    linarith
  have hρ_le_ρ₁ : ρ ≤ ρ₁ := min_le_left _ _
  have hρ_le_ρ_V4 : ρ ≤ ρ_V4 := le_trans hρ_le_ρ₁ hρ₁_le_ρ_V4
  have hρ_le_rN : ρ ≤ (rN : ℝ) := by
    have h1 : min ρ₁ ((rN : ℝ) / 2) ≤ (rN : ℝ) / 2 := min_le_right _ _
    have h2 : ((rN : ℝ) / 2) ≤ (rN : ℝ) := by
      have : (0 : ℝ) ≤ (rN : ℝ) := rN.coe_nonneg; linarith
    rw [hρ_def]; linarith
  set T_match : ℝ := min (min δ_match T₁) (εN / 2) with hT_match_def
  have hT_match_pos : 0 < T_match :=
    lt_min (lt_min hδ_match_pos hT₁_pos) (by linarith)
  have hT_match_le_δ : T_match ≤ δ_match := by
    have h1 : T_match ≤ min δ_match T₁ := min_le_left _ _
    have h2 : min δ_match T₁ ≤ δ_match := min_le_left _ _
    linarith
  have hT_match_le_T₁ : T_match ≤ T₁ := by
    have h1 : T_match ≤ min δ_match T₁ := min_le_left _ _
    have h2 : min δ_match T₁ ≤ T₁ := min_le_right _ _
    linarith
  have hT_match_le_ε_half : T_match ≤ εN / 2 := min_le_right _ _
  have hT_match_le_ε : T_match ≤ εN := by linarith
  have hT_match_lt_ε : T_match < εN := by linarith
  set T : ℝ := T_V4 with hT_def
  have hT_pos : 0 < T := hT_V4_pos
  have hT_match_lt_T : T_match < T := by
    have h1 : T_match ≤ T₁ := hT_match_le_T₁
    have h2 : T₁ < T_V4 := hT₁_lt_T_V4
    linarith
  set t' : ℝ := (min T_match (1 / (2 * (Mglob + 1)))) / 2 with ht'_def
  have hinner_pos : 0 < min T_match (1 / (2 * (Mglob + 1))) := by
    apply lt_min hT_match_pos
    apply div_pos one_pos
    positivity
  have ht'_pos : 0 < t' := by rw [ht'_def]; linarith
  have ht'_lt_T_match : t' < T_match := by
    have h1 : min T_match (1 / (2 * (Mglob + 1))) ≤ T_match := min_le_left _ _
    have h2 : (0 : ℝ) < min T_match (1 / (2 * (Mglob + 1))) := hinner_pos
    rw [ht'_def]; linarith
  have ht'_lt_inv : t' < 1 / (2 * (Mglob + 1)) := by
    have h1 : min T_match (1 / (2 * (Mglob + 1))) ≤ 1 / (2 * (Mglob + 1)) := min_le_right _ _
    have h2 : (0 : ℝ) < min T_match (1 / (2 * (Mglob + 1))) := hinner_pos
    rw [ht'_def]; linarith
  have hMt'_lt : Mglob * t' < 1 := by
    rcases eq_or_lt_of_le hMglob_nn with heq | hlt
    · rw [← heq, zero_mul]; norm_num
    · have h1 : Mglob * t' < Mglob * (1 / (2 * (Mglob + 1))) :=
        mul_lt_mul_of_pos_left ht'_lt_inv hlt
      have h2 : Mglob * (1 / (2 * (Mglob + 1))) = Mglob / (2 * (Mglob + 1)) := by
        field_simp
      have hbd : Mglob / (2 * (Mglob + 1)) < 1 := by
        rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * (Mglob + 1))]
        linarith
      linarith
  have hΦ_const_zero : ∀ s ∈ Set.Ioo (-T_match) T_match,
      Φ (((x₀, (0 : E)) : E × E), s) = ((x₀, (0 : E)) : E × E) := by
    intro s hs
    have hs_in_V : s ∈ V := by
      apply hδ_sub
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
      refine ⟨?_, ?_⟩
      · linarith [hs.1]
      · linarith [hs.2]
    exact hU _ (hVU hs_in_V)
  have hΦ_init_v : ∀ v ∈ Metric.ball (0 : E) ρ,
      Φ (((x₀, v) : E × E), 0) = ((x₀, v) : E × E) := by
    intro v hv
    have hv_in_cb : ((x₀, v) : E × E) ∈
        Metric.closedBall ((x₀, (0 : E)) : E × E) (rN : ℝ) := by
      rw [Metric.mem_closedBall, Prod.dist_eq]
      simp only [dist_self, dist_zero_right]
      rw [Metric.mem_ball, dist_zero_right] at hv
      have : ‖v‖ ≤ (rN : ℝ) := le_of_lt (lt_of_lt_of_le hv hρ_le_rN)
      exact max_le rN.coe_nonneg this
    exact hΦ_ILF.apply_initial ((x₀, v) : E × E) hv_in_cb
  have h_inner_v : ∀ v ∈ Metric.ball (0 : E) ρ, ∀ s ∈ Set.Icc (-T_match) T_match,
      Φ (((x₀, v) : E × E), s) ∈ Metric.ball ((x₀, (0 : E)) : E × E) b.rIn := by
    intro v hv s hs
    have hv_ρ₁ : v ∈ Metric.ball (0 : E) ρ₁ := by
      rw [Metric.mem_ball, dist_zero_right] at hv ⊢
      exact lt_of_lt_of_le hv hρ_le_ρ₁
    have hs_T₁ : s ∈ Set.Icc (-T₁) T₁ := by
      refine ⟨?_, ?_⟩
      · linarith [hs.1]
      · linarith [hs.2]
    exact h_orbit_in v hv_ρ₁ s hs_T₁
  have hΦ_target_v : ∀ v ∈ Metric.ball (0 : E) ρ, ∀ s ∈ Set.Icc (-T_match) T_match,
      Φ (((x₀, v) : E × E), s) ∈
        (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E) := by
    intro v hv s hs
    have h_inball := h_inner_v v hv s hs
    have h_inclosed : Φ (((x₀, v) : E × E), s) ∈
        Metric.closedBall ((x₀, (0 : E)) : E × E) b.rIn :=
      Metric.ball_subset_closedBall h_inball
    have h_inOuter : Φ (((x₀, v) : E × E), s) ∈
        Metric.closedBall ((x₀, (0 : E)) : E × E) b.rOut :=
      Metric.closedBall_subset_closedBall (le_of_lt b.rIn_lt_rOut) h_inclosed
    exact hb_sub h_inOuter
  have hT_match_lt_εN : T_match < εN := hT_match_lt_ε
  have hΦ_phase_v : ∀ v ∈ Metric.ball (0 : E) ρ, ∀ s ∈ Set.Ioo (-T_match) T_match,
      HasDerivAt (fun s' : ℝ => Φ (((x₀, v) : E × E), s'))
        (chartPhaseVF (I := I) g p (Φ (((x₀, v) : E × E), s))) s :=
    orbit_hasDerivAt_chartPhaseVF_uniform
      (I := I) (g := g) (p := p) (x₀ := x₀) hx₀_def
      (b := b) (r := rN) (ε := εN) hr hε
      (Φ := Φ) hΦ_ILF hb_sub
      (ρ := ρ) (T := T_match) hρ_pos hT_match_pos hT_match_lt_εN hρ_le_rN
      (fun v hv s hs => h_inner_v v hv s hs)
  refine ⟨Φ, b, rN, εN, ρ, T, T_match, t', Mglob, hr, hε, hρ_pos, hT_pos, hT_match_pos,
    hT_match_lt_T, hT_match_le_ε, ht'_pos, ht'_lt_T_match, hMglob_nn, hMt'_lt,
    hb_sub, hΦ_ILF, ?_, hΦ_const_zero, hM_bd, hΦ_init_v, hΦ_target_v, hΦ_phase_v⟩
  · apply hΦ_cd_V4.mono
    intro w hw
    refine ⟨?_, ?_⟩
    · exact (Metric.ball_subset_ball hρ_le_ρ_V4) hw.1
    · exact hw.2

end CombinedData

section Headline

variable [I.Boundaryless] [CompleteSpace E]
  [T2Space (TangentBundle I M)]

omit [NeZero (Module.finrank ℝ E)] in
theorem mfderiv_expMap_at_zero
    (g : SmoothRiemannianMetric I M) (p : M) :
    mfderiv 𝓘(ℝ, E) I
      (fun v : E => (expMap (I := I) g p (show TangentSpace I p from v) : M))
      (0 : E) =
      ContinuousLinearMap.id ℝ E := by
  classical
  obtain ⟨Φ, b, r, ε, ρ, T, T_match, t', Mb, hr, hε, hρ_pos, hT_pos, hT_match_pos,
    hT_match_lt_T, hT_match_le_ε, ht'_pos, ht'_lt_T_match, hMb_nn, hMt'_lt,
    hb_sub, hΦ_ILF, _hΦ_cd, hΦ_const_zero, hM_bd, hΦ_init_v, hΦ_target_v,
    hΦ_phase_v⟩ :=
    exists_combined_chartFlow_data (I := I) g p
  let x₀ : E := extChartAt I p p
  have hx₀_def : x₀ = extChartAt I p p := rfl
  have hx₀_src : p ∈ (extChartAt I p).source := mem_extChartAt_source (I := I) p
  have hx₀_target : x₀ ∈ (extChartAt I p).target :=
    (extChartAt I p).map_source hx₀_src
  have hx₀_interior : x₀ ∈ interior (extChartAt I p).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) p hx₀_target
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have ht'_lt_ε : t' < ε := lt_of_lt_of_le ht'_lt_T_match hT_match_le_ε
  have ht'_in_Icc_t' : t' ∈ Set.Icc (0 - t') (0 + t') := by
    refine ⟨?_, ?_⟩ <;> linarith
  have hsub_Icc : Set.Icc (0 - t') (0 + t') ⊆ Set.Icc (-ε) ε := by
    intro s hs
    refine ⟨?_, ?_⟩ <;> [linarith [hs.1]; linarith [hs.2]]
  have hf_C1 : ContDiffOn ℝ 1 (uncurry (chartPhaseVFTime (I := I) g p
      ((extChartAt I p p, (0 : E)) : E × E) b)) (Set.univ : Set (ℝ × (E × E))) :=
    Geodesic.chartPhaseVFTime_uncurry_contDiffOn_univ_one (I := I) g p
      ((extChartAt I p p, (0 : E)) : E × E) b hb_sub
  have hA_bd : ∀ τ ∈ Set.Icc (0 - t') (0 + t'),
      ‖fderiv ℝ (chartPhaseVFTime (I := I) g p ((x₀, (0 : E)) : E × E) b τ)
        (Φ ⟨((x₀, (0 : E)) : E × E), τ⟩)‖ ≤ Mb :=
    fun τ _ => hM_bd τ _
  have hΦ_fderiv := hasFDerivAt_flow_at_initial_of_isLocalFlow
    (f := chartPhaseVFTime (I := I) g p ((x₀, (0 : E)) : E × E) b)
    (t₀ := 0) (x₀ := ((x₀, (0 : E)) : E × E)) (r := r) (tmin := -ε) (tmax := ε)
    (Φ := Φ) hΦ_ILF hf_C1 ht'_pos hMb_nn hMt'_lt hsub_Icc hA_bd hr (t := t')
    ht'_in_Icc_t'
  set hA_cont :=
    (hΦ_ILF.continuousOn_fderiv_along_orbit hf_C1 ((x₀, (0 : E)) : E × E)
      (Metric.mem_closedBall_self (le_of_lt hr'))).mono hsub_Icc with hA_cont_def
  set Lmap : E × E →L[ℝ] E × E :=
    variationalLinearMapAt
      (f := chartPhaseVFTime (I := I) g p ((x₀, (0 : E)) : E × E) b)
      (α := fun s => Φ ⟨((x₀, (0 : E)) : E × E), s⟩) (t₀ := 0)
      ht'_pos hMb_nn hMt'_lt hA_cont hA_bd ht'_in_Icc_t'
    with hLmap_def
  have hLmap_apply : ∀ δx δw : E,
      Lmap ((δx, δw) : E × E) = ((δx + t' • δw, δw) : E × E) := by
    intro δx δw
    have hΦ_orbit_const_t' : ∀ s ∈ Set.Icc (0 - t') (0 + t'),
        Φ (((x₀, (0 : E)) : E × E), s) = ((x₀, (0 : E)) : E × E) := by
      intro s hs
      have hs_in_match : s ∈ Set.Ioo (-T_match) T_match := by
        refine ⟨?_, ?_⟩
        · linarith [hs.1]
        · linarith [hs.2]
      exact hΦ_const_zero s hs_in_match
    have hz0_in : ((x₀, (0 : E)) : E × E) ∈
        Metric.ball ((x₀, (0 : E)) : E × E) b.rIn :=
      Metric.mem_ball_self b.rIn_pos
    have hy_isVarSol : IsVariationalSolutionOn
        (chartPhaseVFTime (I := I) g p ((x₀, (0 : E)) : E × E) b)
        (fun s => Φ ⟨((x₀, (0 : E)) : E × E), s⟩) ((δx, δw) : E × E) 0
        (fun s : ℝ => ((δx + s • δw, δw) : E × E))
        (Set.Icc (0 - t') (0 + t')) := by
      refine ⟨?_, ?_⟩
      · change ((δx + (0 : ℝ) • δw, δw) : E × E) = ((δx, δw) : E × E)
        simp
      · intro t ht
        have hα_t : Φ ⟨((x₀, (0 : E)) : E × E), t⟩ = ((x₀, (0 : E)) : E × E) :=
          hΦ_orbit_const_t' t ht
        have hfderiv_eq :
            fderiv ℝ (chartPhaseVFTime (I := I) g p ((x₀, (0 : E)) : E × E) b t)
              (Φ ⟨((x₀, (0 : E)) : E × E), t⟩) =
            (ContinuousLinearMap.snd ℝ E E).prod (0 : E × E →L[ℝ] E) := by
          rw [hα_t]
          have hfd : HasFDerivAt
              (chartPhaseVFCutoff (I := I) g p ((x₀, (0 : E)) : E × E) b)
              ((ContinuousLinearMap.snd ℝ E E).prod (0 : E × E →L[ℝ] E))
              ((x₀, (0 : E)) : E × E) :=
            chartPhaseVFCutoff_hasFDerivAt_zero_section (I := I) g
              (α := p) hx₀_interior (z₀ := ((x₀, (0 : E)) : E × E)) b hz0_in
          exact hfd.fderiv
        have hy_deriv : HasDerivAt (fun s : ℝ => ((δx + s • δw, δw) : E × E))
            ((δw, (0 : E)) : E × E) t := by
          have hx_part : HasDerivAt (fun s : ℝ => δx + s • δw) δw t := by
            have h1 : HasDerivAt (fun s : ℝ => s • δw) δw t := by
              have := (hasDerivAt_id (𝕜 := ℝ) t).smul_const δw
              simpa using this
            have h2 : HasDerivAt (fun s : ℝ => δx + s • δw) (0 + δw) t :=
              (hasDerivAt_const t δx).add h1
            simpa using h2
          have hw_part : HasDerivAt (fun _ : ℝ => δw) (0 : E) t :=
            hasDerivAt_const t δw
          exact hx_part.prodMk hw_part
        have happly : (ContinuousLinearMap.snd ℝ E E).prod (0 : E × E →L[ℝ] E)
            (((δx + t • δw, δw) : E × E)) = ((δw, (0 : E)) : E × E) := by
          ext
          · rfl
          · rfl
        rw [hfderiv_eq, happly]
        exact hy_deriv.hasDerivWithinAt
    have hvSol_isSol := variationalSolutionFun_isSolution
      ht'_pos hMb_nn hMt'_lt hA_cont hA_bd ((δx, δw) : E × E)
    have huniq := IsVariationalSolutionOn.unique_Icc ht'_pos hA_cont
      hvSol_isSol hy_isVarSol
    have hvSol_at_t' := huniq ht'_in_Icc_t'
    have hLmap_eq :
        Lmap ((δx, δw) : E × E) =
          variationalSolutionFun
            (f := chartPhaseVFTime (I := I) g p ((x₀, (0 : E)) : E × E) b)
            (α := fun s => Φ ⟨((x₀, (0 : E)) : E × E), s⟩) (t₀ := 0)
            ht'_pos hMb_nn hMt'_lt hA_cont hA_bd
            ((δx, δw) : E × E) t' := rfl
    rw [hLmap_eq, hvSol_at_t']
  set Linl : E →L[ℝ] E × E := ContinuousLinearMap.inr ℝ E E with hLinl_def
  have hLinl_apply : ∀ w : E, Linl w = ((0 : E), w) := fun _ => rfl
  have hincl : HasFDerivAt (fun v : E => ((x₀, v) : E × E)) Linl (0 : E) := by
    have h1 : HasFDerivAt (fun _ : E => x₀) (0 : E →L[ℝ] E) (0 : E) :=
      hasFDerivAt_const _ _
    have h2 : HasFDerivAt (fun v : E => v) (ContinuousLinearMap.id ℝ E) (0 : E) :=
      hasFDerivAt_id _
    exact h1.prodMk h2
  have hΦv : HasFDerivAt (fun v : E => Φ (((x₀, v) : E × E), t'))
      (Lmap.comp Linl) (0 : E) := by
    have := hΦ_fderiv.comp (0 : E) hincl
    simpa using this
  have hΦv_fst : HasFDerivAt (fun v : E => (Φ (((x₀, v) : E × E), t')).1)
      ((ContinuousLinearMap.fst ℝ E E).comp (Lmap.comp Linl)) (0 : E) := by
    have hfst_clm : HasFDerivAt (Prod.fst : E × E → E)
        (ContinuousLinearMap.fst ℝ E E) (Φ (((x₀, (0 : E)) : E × E), t')) :=
      (ContinuousLinearMap.fst ℝ E E).hasFDerivAt
    have := hfst_clm.comp (0 : E) hΦv
    simpa using this
  have hcomp_eq :
      (ContinuousLinearMap.fst ℝ E E).comp (Lmap.comp Linl) =
        t' • ContinuousLinearMap.id ℝ E := by
    ext δ
    change (Lmap (((0 : E), δ) : E × E)).1 = t' • δ
    have hL_apply := hLmap_apply (0 : E) δ
    rw [hL_apply]
    change ((0 : E) + t' • δ : E) = t' • δ
    rw [zero_add]
  rw [hcomp_eq] at hΦv_fst
  have hΦv_fst_mfd : HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, E)
      (fun v : E => (Φ (((x₀, v) : E × E), t')).1)
      (0 : E) (t' • ContinuousLinearMap.id ℝ E) :=
    hΦv_fst.hasMFDerivAt
  have hMrange : (Set.range I) = (Set.univ : Set E) :=
    ModelWithCorners.Boundaryless.range_eq_univ
  have hmf_symm_within : mfderivWithin 𝓘(ℝ, E) I (extChartAt I p).symm (Set.range I)
      ((extChartAt I p) p) = ContinuousLinearMap.id ℝ E :=
    mfderivWithin_range_extChartAt_symm
  have hsymm_mdiffWithin : MDifferentiableWithinAt 𝓘(ℝ, E) I (extChartAt I p).symm
      (Set.range I) ((extChartAt I p) p) :=
    mdifferentiableWithinAt_extChartAt_symm hx₀_target
  have hsymm_mdiffAt : MDifferentiableAt 𝓘(ℝ, E) I (extChartAt I p).symm
      ((extChartAt I p) p) := by
    have hnhds : (Set.range I) ∈ 𝓝 ((extChartAt I p) p) := by
      rw [hMrange]; exact Filter.univ_mem
    exact hsymm_mdiffWithin.mdifferentiableAt hnhds
  have hmf_symm : mfderiv 𝓘(ℝ, E) I (extChartAt I p).symm x₀ =
      ContinuousLinearMap.id ℝ E := by
    have heq : mfderiv 𝓘(ℝ, E) I (extChartAt I p).symm ((extChartAt I p) p) =
        ContinuousLinearMap.id ℝ E := by
      rw [← mfderivWithin_univ, ← hMrange]
      exact hmf_symm_within
    exact heq
  have hsymm_hasMFD :
      HasMFDerivAt 𝓘(ℝ, E) I (extChartAt I p).symm ((extChartAt I p) p)
        (ContinuousLinearMap.id ℝ E) := by
    have h1 := hsymm_mdiffAt.hasMFDerivAt
    rw [show ((extChartAt I p) p) = x₀ from rfl, hmf_symm] at h1
    exact h1
  have hΦv_fst_at_zero : (fun v : E => (Φ (((x₀, v) : E × E), t')).1) 0 = x₀ := by
    have h_t'_match : t' ∈ Set.Ioo (-T_match) T_match := ⟨by linarith, ht'_lt_T_match⟩
    have hΦ_zero : Φ (((x₀, (0 : E)) : E × E), t') = ((x₀, (0 : E)) : E × E) :=
      hΦ_const_zero t' h_t'_match
    change (Φ (((x₀, (0 : E)) : E × E), t')).1 = x₀
    rw [hΦ_zero]
  have hsymm_at_fnv0 : HasMFDerivAt 𝓘(ℝ, E) I (extChartAt I p).symm
      ((fun v : E => (Φ (((x₀, v) : E × E), t')).1) 0)
      (ContinuousLinearMap.id ℝ E) := by
    rw [hΦv_fst_at_zero]
    exact hsymm_hasMFD
  have hcomp_mfd : HasMFDerivAt 𝓘(ℝ, E) I
      ((extChartAt I p).symm ∘ fun v : E => (Φ (((x₀, v) : E × E), t')).1)
      (0 : E)
      ((ContinuousLinearMap.id ℝ E).comp (t' • ContinuousLinearMap.id ℝ E)) :=
    hsymm_at_fnv0.comp (0 : E) hΦv_fst_mfd
  have hLcomp_eq : (ContinuousLinearMap.id ℝ E).comp (t' • ContinuousLinearMap.id ℝ E) =
      t' • ContinuousLinearMap.id ℝ E := by
    ext δ; simp
  have hcomp_mfd2 : HasMFDerivAt 𝓘(ℝ, E) I
      ((extChartAt I p).symm ∘ fun v : E => (Φ (((x₀, v) : E × E), t')).1)
      (0 : E) (t' • ContinuousLinearMap.id ℝ E) :=
    hLcomp_eq ▸ hcomp_mfd
  have hcand_eq :
      ((extChartAt I p).symm ∘ fun v : E => (Φ (((x₀, v) : E × E), t')).1) =
        chartFlowCandidate (I := I) Φ p t' := by
    funext v; rfl
  rw [hcand_eq] at hcomp_mfd2
  have hT_match_lt_T : T_match < T := hT_match_lt_T
  have hΦ_target_v_T_match : ∀ v ∈ Metric.ball (0 : E) ρ, ∀ s ∈ Set.Icc (-T_match) T_match,
      Φ (((x₀, v) : E × E), s) ∈
        (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E) := hΦ_target_v
  have hΦ_phase_v_T_match : ∀ v ∈ Metric.ball (0 : E) ρ, ∀ s ∈ Set.Ioo (-T_match) T_match,
      HasDerivAt (fun s' : ℝ => Φ (((x₀, v) : E × E), s'))
        (chartPhaseVF (I := I) g p (Φ (((x₀, v) : E × E), s))) s := hΦ_phase_v
  have hexp_eq : ∀ v ∈ Metric.ball (0 : E) ρ,
      expMap (I := I) g p (show TangentSpace I p from t' • v) =
        chartFlowCandidate (I := I) Φ p t' v := by
    intro v hv
    have hΦ_init_v_at : Φ (((x₀, v) : E × E), 0) = ((x₀, v) : E × E) := hΦ_init_v v hv
    have hΦ_target_for_v : ∀ s ∈ Set.Icc (-T_match) T_match,
        Φ (((x₀, v) : E × E), s) ∈
          (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E) :=
      hΦ_target_v_T_match v hv
    have hΦ_phase_for_v : ∀ s ∈ Set.Ioo (-T_match) T_match,
        HasDerivAt (fun s' : ℝ => Φ (((x₀, v) : E × E), s'))
          (chartPhaseVF (I := I) g p (Φ (((x₀, v) : E × E), s))) s :=
      hΦ_phase_v_T_match v hv
    have hproj := chartFlowOrbitLiftRescaled_proj_at_one
      (I := I) (g := g) (p := p) (v := v)
      (T := T_match) (t' := t') ht'_pos ht'_lt_T_match
      (Φ := Φ) hΦ_init_v_at hΦ_target_for_v hΦ_phase_for_v
    have hΦ_target_t'1 : Φ (((x₀, v) : E × E), t' * 1) ∈
        (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E) := by
      have hmul_one : t' * 1 = t' := mul_one t'
      rw [hmul_one]
      exact hΦ_target_for_v t' (Set.Ioo_subset_Icc_self
        ⟨by linarith, ht'_lt_T_match⟩)
    have hproj_def :=
      chartFlowOrbitLiftRescaled_proj (I := I) (p := p) (v := v) (t' := t')
        (Φ := Φ) (s := 1) hΦ_target_t'1
    have hproj_def' :
        (chartFlowOrbitLiftRescaled (I := I) Φ p t' v 1).proj =
          (extChartAt I p).symm (Φ (((x₀, v) : E × E), t')).1 := by
      rw [hproj_def, mul_one]
    rw [← hproj, hproj_def']
    rfl
  have hev_eq : (fun v : E => expMap (I := I) g p (show TangentSpace I p from t' • v)) =ᶠ[𝓝 (0 : E)]
      chartFlowCandidate (I := I) Φ p t' := by
    refine Filter.eventuallyEq_of_mem (Metric.ball_mem_nhds (0 : E) hρ_pos) ?_
    intro v hv
    exact hexp_eq v hv
  have hexp_scaled_mfd : HasMFDerivAt 𝓘(ℝ, E) I
      (fun v : E => expMap (I := I) g p (show TangentSpace I p from t' • v))
      (0 : E) (t' • ContinuousLinearMap.id ℝ E) :=
    hcomp_mfd2.congr_of_eventuallyEq hev_eq
  have hexpMap_contMDiffAt :=
    expMap_contMDiffAt_zero (I := I) g p
  have hexpMap_mdiffAt : MDifferentiableAt 𝓘(ℝ, E) I
      (fun v : E => (expMap (I := I) g p (show TangentSpace I p from v) : M))
      (0 : E) :=
    hexpMap_contMDiffAt.mdifferentiableAt one_ne_zero
  set Lexp : E →L[ℝ] E :=
    mfderiv 𝓘(ℝ, E) I
      (fun v : E => (expMap (I := I) g p (show TangentSpace I p from v) : M)) (0 : E)
    with hLexp_def
  have hsmul_hfd : HasFDerivAt (fun v : E => t' • v) (t' • ContinuousLinearMap.id ℝ E)
      (0 : E) := by
    have hid : HasFDerivAt (fun v : E => v) (ContinuousLinearMap.id ℝ E) (0 : E) :=
      hasFDerivAt_id _
    have := hid.const_smul t'
    exact this
  have hsmul_mfd : HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, E) (fun v : E => t' • v) (0 : E)
      (t' • ContinuousLinearMap.id ℝ E) := hsmul_hfd.hasMFDerivAt
  have hexp_mfd_zero : HasMFDerivAt 𝓘(ℝ, E) I
      (fun v : E => (expMap (I := I) g p (show TangentSpace I p from v) : M))
      ((fun v : E => t' • v) 0) Lexp := by
    have hpoint : (fun v : E => t' • v) 0 = (0 : E) := by simp
    rw [hpoint]
    exact hexpMap_mdiffAt.hasMFDerivAt
  have hcomp_chain : HasMFDerivAt 𝓘(ℝ, E) I
      ((fun v : E => (expMap (I := I) g p (show TangentSpace I p from v) : M)) ∘
        (fun v : E => t' • v))
      (0 : E) (Lexp.comp (t' • ContinuousLinearMap.id ℝ E)) :=
    hexp_mfd_zero.comp (0 : E) hsmul_mfd
  have hcomp_eq2 :
      ((fun v : E => (expMap (I := I) g p (show TangentSpace I p from v) : M)) ∘
        (fun v : E => t' • v)) =
      (fun v : E => expMap (I := I) g p (show TangentSpace I p from t' • v)) := by
    funext v; rfl
  rw [hcomp_eq2] at hcomp_chain
  have hLexp_eq : Lexp.comp (t' • ContinuousLinearMap.id ℝ E) =
      t' • ContinuousLinearMap.id ℝ E := by
    have h1 : mfderiv 𝓘(ℝ, E) I
        (fun v : E => expMap (I := I) g p (show TangentSpace I p from t' • v))
        (0 : E) = Lexp.comp (t' • ContinuousLinearMap.id ℝ E) :=
      hcomp_chain.mfderiv
    have h2 : mfderiv 𝓘(ℝ, E) I
        (fun v : E => expMap (I := I) g p (show TangentSpace I p from t' • v))
        (0 : E) = t' • ContinuousLinearMap.id ℝ E :=
      hexp_scaled_mfd.mfderiv
    rw [← h1, h2]
  have ht'_ne : (t' : ℝ) ≠ 0 := ne_of_gt ht'_pos
  have hsmul_factor : Lexp.comp (t' • ContinuousLinearMap.id ℝ E) =
      t' • Lexp := by
    ext δ
    change Lexp ((t' • ContinuousLinearMap.id ℝ E) δ) = (t' • Lexp) δ
    change Lexp (t' • δ) = t' • Lexp δ
    rw [Lexp.map_smul]
  rw [hsmul_factor] at hLexp_eq
  have hLexp_id : Lexp = ContinuousLinearMap.id ℝ E :=
    (smul_right_injective (E →L[ℝ] E) ht'_ne) hLexp_eq
  rw [hLexp_def] at hLexp_id
  exact hLexp_id

end Headline

end Exponential
end Riemannian
end Geometry
end DifferentialGeometry

end
