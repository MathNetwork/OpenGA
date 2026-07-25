import DifferentialGeometry.Geometry.Geodesic.Equation
import DifferentialGeometry.Geometry.Geodesic.Existence
import DifferentialGeometry.Geometry.Geodesic.MaximalInterval
import DifferentialGeometry.Geometry.Geodesic.Smoothness
import DifferentialGeometry.Geometry.Geodesic.Uniqueness
import DifferentialGeometry.Analysis.ODE.Flow.C1Regularity.ContDiffOnOne
import DifferentialGeometry.Analysis.ODE.Flow.HigherRegularity.VariationalMapContDiffOnK
import DifferentialGeometry.Analysis.ODE.Flow.HigherRegularity.ContDiffOnTop
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension



noncomputable section

open Set Function Filter Metric Asymptotics Real Bundle Manifold
open scoped Topology NNReal Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

def chartPhaseVF (g : SmoothRiemannianMetric I M) (α : M) : E × E → E × E :=
  fun z => (z.2, - chartChristoffelContraction (I := I) g α z.2 z.2 z.1)

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma chartPhaseVF_apply (g : SmoothRiemannianMetric I M) (α : M)
    (z : E × E) :
    chartPhaseVF (I := I) g α z =
      (z.2, - chartChristoffelContraction (I := I) g α z.2 z.2 z.1) := rfl

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma chartPhaseVF_mk (g : SmoothRiemannianMetric I M) (α : M)
    (x v : E) :
    chartPhaseVF (I := I) g α (x, v) =
      (v, - chartChristoffelContraction (I := I) g α v v x) := rfl

variable [I.Boundaryless]

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
lemma chartChristoffelContraction_scalarCoeff_contDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (k : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun z : E × E =>
        ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g α i j k z.1 *
            chartCoord (E := E) i z.2 *
            chartCoord (E := E) j z.2)
      ((interior (extChartAt I α).target) ×ˢ (Set.univ : Set E)) := by
  classical
  refine ContDiffOn.sum (fun i _ => ?_)
  refine ContDiffOn.sum (fun j _ => ?_)
  have hΓ : ContDiffOn ℝ ∞
      (fun z : E × E => chartChristoffel (I := I) g α i j k z.1)
      ((interior (extChartAt I α).target) ×ˢ (Set.univ : Set E)) := by
    have hbase : ContDiffOn ℝ ∞ (chartChristoffel (I := I) g α i j k)
        (interior (extChartAt I α).target) :=
      chartChristoffel_contDiffOn_interior (I := I) g α i j k
    have hfst : ContDiff ℝ ∞ (Prod.fst : E × E → E) := contDiff_fst
    have hmapsto : MapsTo (Prod.fst : E × E → E)
        ((interior (extChartAt I α).target) ×ˢ (Set.univ : Set E))
        (interior (extChartAt I α).target) :=
      fun _ hp => hp.1
    exact hbase.comp hfst.contDiffOn hmapsto
  have hCLM_i : ContDiff ℝ ∞ (((chartModelBasis E).coord i).toContinuousLinearMap) :=
    ((chartModelBasis E).coord i).toContinuousLinearMap.contDiff
  have hCLM_j : ContDiff ℝ ∞ (((chartModelBasis E).coord j).toContinuousLinearMap) :=
    ((chartModelBasis E).coord j).toContinuousLinearMap.contDiff
  have hsnd : ContDiff ℝ ∞ (Prod.snd : E × E → E) := contDiff_snd
  have hci : ContDiffOn ℝ ∞
      (fun z : E × E => chartCoord (E := E) i z.2)
      ((interior (extChartAt I α).target) ×ˢ (Set.univ : Set E)) :=
    (hCLM_i.comp hsnd).contDiffOn
  have hcj : ContDiffOn ℝ ∞
      (fun z : E × E => chartCoord (E := E) j z.2)
      ((interior (extChartAt I α).target) ×ˢ (Set.univ : Set E)) :=
    (hCLM_j.comp hsnd).contDiffOn
  exact (hΓ.mul hci).mul hcj

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
lemma chartChristoffelContraction_contDiffOn
    (g : SmoothRiemannianMetric I M) (α : M) :
    ContDiffOn ℝ ∞
      (fun z : E × E => chartChristoffelContraction (I := I) g α z.2 z.2 z.1)
      ((interior (extChartAt I α).target) ×ˢ (Set.univ : Set E)) := by
  classical
  unfold chartChristoffelContraction
  refine ContDiffOn.sum (fun k _ => ?_)
  have hscalar :=
    chartChristoffelContraction_scalarCoeff_contDiffOn (I := I) g α k
  have hconst : ContDiffOn ℝ ∞
      (fun _ : E × E => (chartModelBasis E) k)
      ((interior (extChartAt I α).target) ×ˢ (Set.univ : Set E)) :=
    contDiffOn_const
  exact hscalar.smul hconst

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartPhaseVF_contDiffOn
    (g : SmoothRiemannianMetric I M) (α : M) :
    ContDiffOn ℝ ∞ (chartPhaseVF (I := I) g α)
      ((interior (extChartAt I α).target) ×ˢ (Set.univ : Set E)) := by
  have hfst : ContDiffOn ℝ ∞ (fun z : E × E => z.2)
      ((interior (extChartAt I α).target) ×ˢ (Set.univ : Set E)) :=
    contDiff_snd.contDiffOn
  have hΓ : ContDiffOn ℝ ∞
      (fun z : E × E => chartChristoffelContraction (I := I) g α z.2 z.2 z.1)
      ((interior (extChartAt I α).target) ×ˢ (Set.univ : Set E)) :=
    chartChristoffelContraction_contDiffOn (I := I) g α
  exact hfst.prodMk hΓ.neg

def chartPhaseVFCutoff (g : SmoothRiemannianMetric I M) (α : M)
    (z₀ : E × E) (b : ContDiffBump z₀) : E × E → E × E :=
  fun z => b z • chartPhaseVF (I := I) g α z

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
@[simp] lemma chartPhaseVFCutoff_apply
    (g : SmoothRiemannianMetric I M) (α : M)
    (z₀ : E × E) (b : ContDiffBump z₀) (z : E × E) :
    chartPhaseVFCutoff (I := I) g α z₀ b z =
      b z • chartPhaseVF (I := I) g α z := rfl

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma chartPhaseVFCutoff_eq_of_mem_closedBall
    (g : SmoothRiemannianMetric I M) (α : M)
    (z₀ : E × E) (b : ContDiffBump z₀) {z : E × E}
    (hz : z ∈ Metric.closedBall z₀ b.rIn) :
    chartPhaseVFCutoff (I := I) g α z₀ b z = chartPhaseVF (I := I) g α z := by
  have hb1 : b z = 1 := b.one_of_mem_closedBall hz
  simp [chartPhaseVFCutoff_apply, hb1]

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartPhaseVFCutoff_contDiff
    (g : SmoothRiemannianMetric I M) (α : M)
    (z₀ : E × E) (b : ContDiffBump z₀)
    (hb_sub : Metric.closedBall z₀ b.rOut ⊆
      (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E)) :
    ContDiff ℝ ∞ (chartPhaseVFCutoff (I := I) g α z₀ b) := by
  classical
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ Metric.closedBall z₀ b.rOut
  · have hz_open : z ∈ (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E) :=
      hb_sub hz
    have hopen : IsOpen ((interior (extChartAt I α).target) ×ˢ
        (Set.univ : Set E)) :=
      isOpen_interior.prod isOpen_univ
    have hVF_at : ContDiffAt ℝ ∞ (chartPhaseVF (I := I) g α) z :=
      (chartPhaseVF_contDiffOn (I := I) g α).contDiffAt
        (hopen.mem_nhds hz_open)
    have hb_at : ContDiffAt ℝ ∞ (fun z => (b : E × E → ℝ) z) z :=
      b.contDiff.contDiffAt
    exact hb_at.smul hVF_at
  · rw [Metric.mem_closedBall] at hz
    have hdist : b.rOut < dist z z₀ := not_le.mp hz
    have hopen : IsOpen {w : E × E | b.rOut < dist w z₀} := by
      have hcont : Continuous (fun w : E × E => dist w z₀) :=
        continuous_id.dist continuous_const
      exact hcont.isOpen_preimage _ isOpen_Ioi
    have hmem : z ∈ {w : E × E | b.rOut < dist w z₀} := hdist
    refine ContDiffAt.congr_of_eventuallyEq (f := fun _ : E × E => (0 : E × E))
      contDiffAt_const ?_
    refine Filter.eventuallyEq_of_mem (hopen.mem_nhds hmem) ?_
    intro w hw
    have hw' : b.rOut < dist w z₀ := hw
    have hb0 : (b : E × E → ℝ) w = 0 :=
      b.zero_of_le_dist (le_of_lt hw')
    simp [chartPhaseVFCutoff_apply, hb0]

def chartPhaseVFTime (g : SmoothRiemannianMetric I M) (α : M)
    (z₀ : E × E) (b : ContDiffBump z₀) : ℝ → (E × E) → E × E :=
  fun _ z => chartPhaseVFCutoff (I := I) g α z₀ b z

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
@[simp] lemma chartPhaseVFTime_apply
    (g : SmoothRiemannianMetric I M) (α : M)
    (z₀ : E × E) (b : ContDiffBump z₀) (t : ℝ) (z : E × E) :
    chartPhaseVFTime (I := I) g α z₀ b t z =
      chartPhaseVFCutoff (I := I) g α z₀ b z := rfl

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma uncurry_chartPhaseVFTime_eq
    (g : SmoothRiemannianMetric I M) (α : M)
    (z₀ : E × E) (b : ContDiffBump z₀) :
    Function.uncurry (chartPhaseVFTime (I := I) g α z₀ b) =
      fun p : ℝ × (E × E) => chartPhaseVFCutoff (I := I) g α z₀ b p.2 := by
  funext p; rfl

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
lemma chartPhaseVFTime_uncurry_contDiff
    (g : SmoothRiemannianMetric I M) (α : M)
    (z₀ : E × E) (b : ContDiffBump z₀)
    (hb_sub : Metric.closedBall z₀ b.rOut ⊆
      (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E)) :
    ContDiff ℝ ∞ (Function.uncurry (chartPhaseVFTime (I := I) g α z₀ b)) := by
  rw [uncurry_chartPhaseVFTime_eq]
  have hVF : ContDiff ℝ ∞ (chartPhaseVFCutoff (I := I) g α z₀ b) :=
    chartPhaseVFCutoff_contDiff (I := I) g α z₀ b hb_sub
  exact hVF.comp contDiff_snd

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
lemma chartPhaseVFTime_uncurry_contDiffOn_univ_one
    (g : SmoothRiemannianMetric I M) (α : M)
    (z₀ : E × E) (b : ContDiffBump z₀)
    (hb_sub : Metric.closedBall z₀ b.rOut ⊆
      (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E)) :
    ContDiffOn ℝ 1 (Function.uncurry (chartPhaseVFTime (I := I) g α z₀ b))
      (Set.univ : Set (ℝ × (E × E))) := by
  have h := chartPhaseVFTime_uncurry_contDiff (I := I) g α z₀ b hb_sub
  have h1 : ContDiff ℝ 1 (Function.uncurry (chartPhaseVFTime (I := I) g α z₀ b)) :=
    h.of_le (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))
  exact h1.contDiffOn

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
lemma chartPhaseVFTime_uncurry_contDiffOn_univ_two
    (g : SmoothRiemannianMetric I M) (α : M)
    (z₀ : E × E) (b : ContDiffBump z₀)
    (hb_sub : Metric.closedBall z₀ b.rOut ⊆
      (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E)) :
    ContDiffOn ℝ 2 (Function.uncurry (chartPhaseVFTime (I := I) g α z₀ b))
      (Set.univ : Set (ℝ × (E × E))) := by
  have h := chartPhaseVFTime_uncurry_contDiff (I := I) g α z₀ b hb_sub
  have hle : (2 : WithTop ℕ∞) ≤ ∞ := by
    have h2le : ((2 : ℕ∞) : WithTop ℕ∞) ≤ ∞ :=
      by exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤)
    simpa using h2le
  have h2 : ContDiff ℝ 2 (Function.uncurry (chartPhaseVFTime (I := I) g α z₀ b)) :=
    h.of_le hle
  exact h2.contDiffOn

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
lemma chartPhaseVFTime_uncurry_contDiffOn_univ_nat
    (g : SmoothRiemannianMetric I M) (α : M)
    (z₀ : E × E) (b : ContDiffBump z₀) (n : ℕ)
    (hb_sub : Metric.closedBall z₀ b.rOut ⊆
      (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E)) :
    ContDiffOn ℝ (n : ℕ∞) (Function.uncurry (chartPhaseVFTime (I := I) g α z₀ b))
      (Set.univ : Set (ℝ × (E × E))) := by
  have h := chartPhaseVFTime_uncurry_contDiff (I := I) g α z₀ b hb_sub
  have hle : ((n : ℕ∞) : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by
    have hnle : (n : ℕ∞) ≤ (⊤ : ℕ∞) := le_top
    exact_mod_cast hnle
  have hn : ContDiff ℝ ((n : ℕ∞) : WithTop ℕ∞)
      (Function.uncurry (chartPhaseVFTime (I := I) g α z₀ b)) :=
    h.of_le hle
  exact hn.contDiffOn

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [I.Boundaryless] in
lemma exists_contDiffBump_subset_chart_interior
    (α : M) {x₀ v₀ : E}
    (hx₀ : x₀ ∈ interior (extChartAt I α).target) :
    ∃ b : ContDiffBump ((x₀, v₀) : E × E),
      Metric.closedBall ((x₀, v₀) : E × E) b.rOut ⊆
        (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E) := by
  obtain ⟨ε, hε, hε_sub⟩ := Metric.mem_nhds_iff.mp
    (isOpen_interior.mem_nhds hx₀)
  refine ⟨{ rIn := ε / 4, rOut := ε / 2,
            rIn_pos := by positivity,
            rIn_lt_rOut := by linarith }, ?_⟩
  intro p hp
  refine ⟨?_, Set.mem_univ _⟩
  rw [Metric.mem_closedBall, Prod.dist_eq] at hp
  have hfst : dist p.1 x₀ ≤ ε / 2 := le_trans (le_max_left _ _) hp
  have hfst_lt : dist p.1 x₀ < ε := lt_of_le_of_lt hfst (by linarith)
  exact hε_sub (Metric.mem_ball.mpr hfst_lt)

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem exists_chartPhase_isLocalFlow
    [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (α : M) {x₀ v₀ : E}
    (hx₀ : x₀ ∈ interior (extChartAt I α).target) :
    ∃ (b : ContDiffBump ((x₀, v₀) : E × E))
      (r : ℝ≥0) (ε : ℝ) (Φ : (E × E) × ℝ → E × E),
      0 < r ∧ 0 < ε ∧
      Metric.closedBall ((x₀, v₀) : E × E) b.rOut ⊆
        (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E) ∧
      DifferentialGeometry.Analysis.ODE.Flow.IsLocalFlow
        (chartPhaseVFTime (I := I) g α (x₀, v₀) b)
        (0 : ℝ) (x₀, v₀) r (-ε) ε Φ := by
  obtain ⟨b, hb_sub⟩ :=
    exists_contDiffBump_subset_chart_interior (I := I) (α := α)
      (x₀ := x₀) (v₀ := v₀) hx₀
  have hC1 :
      ContDiffOn ℝ 1
        (Function.uncurry (chartPhaseVFTime (I := I) g α (x₀, v₀) b))
        (Set.univ : Set (ℝ × (E × E))) :=
    chartPhaseVFTime_uncurry_contDiffOn_univ_one (I := I) g α (x₀, v₀) b hb_sub
  obtain ⟨r, ε, hr, hε, Φ, hΦ⟩ :=
    DifferentialGeometry.Analysis.ODE.Flow.exists_isLocalFlow_of_contDiffOn_univ
      (E := E × E) (chartPhaseVFTime (I := I) g α (x₀, v₀) b) hC1 0 (x₀, v₀)
  refine ⟨b, r, ε, Φ, hr, hε, hb_sub, ?_⟩
  have heq1 : (0 : ℝ) - ε = -ε := by ring
  have heq2 : (0 : ℝ) + ε = ε := by ring
  rw [heq1, heq2] at hΦ
  exact hΦ

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
lemma exists_bound_fderiv_chartPhaseVFCutoff
    (g : SmoothRiemannianMetric I M) (α : M)
    (z₀ : E × E) (b : ContDiffBump z₀)
    (hb_sub : Metric.closedBall z₀ b.rOut ⊆
      (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z : E × E,
      ‖fderiv ℝ (chartPhaseVFCutoff (I := I) g α z₀ b) z‖ ≤ M := by
  classical
  have hVF_cd : ContDiff ℝ ∞ (chartPhaseVFCutoff (I := I) g α z₀ b) :=
    chartPhaseVFCutoff_contDiff (I := I) g α z₀ b hb_sub
  have hfderiv_cont : Continuous
      (fun z => fderiv ℝ (chartPhaseVFCutoff (I := I) g α z₀ b) z) := by
    exact hVF_cd.continuous_fderiv (by
      intro h
      exact absurd h (by decide))
  set R : ℝ := b.rOut + 1 with hR_def
  have hR_pos : 0 < R := by have := b.rOut_pos; linarith
  have hcompact : IsCompact (Metric.closedBall z₀ R) := isCompact_closedBall _ _
  have hnonempty : (Metric.closedBall z₀ R).Nonempty := ⟨z₀, Metric.mem_closedBall_self hR_pos.le⟩
  have hfd_cont_on : ContinuousOn
      (fun z => ‖fderiv ℝ (chartPhaseVFCutoff (I := I) g α z₀ b) z‖)
      (Metric.closedBall z₀ R) :=
    (continuous_norm.comp hfderiv_cont).continuousOn
  rcases hcompact.exists_isMaxOn hnonempty hfd_cont_on with ⟨zmax, _, hzmax_max⟩
  set Mglob : ℝ := ‖fderiv ℝ (chartPhaseVFCutoff (I := I) g α z₀ b) zmax‖ with hMglob_def
  have hMglob_nn : 0 ≤ Mglob := norm_nonneg _
  refine ⟨Mglob, hMglob_nn, ?_⟩
  intro z
  by_cases hz_in : z ∈ Metric.closedBall z₀ R
  · exact hzmax_max hz_in
  · rw [Metric.mem_closedBall] at hz_in
    have hR_lt : R < dist z z₀ := not_le.mp hz_in
    have hdist_gt : b.rOut < dist z z₀ := by linarith
    have hopen : IsOpen {w : E × E | b.rOut < dist w z₀} := by
      have hcont : Continuous (fun w : E × E => dist w z₀) :=
        continuous_id.dist continuous_const
      exact hcont.isOpen_preimage _ isOpen_Ioi
    have hmem : z ∈ {w : E × E | b.rOut < dist w z₀} := hdist_gt
    have hev : chartPhaseVFCutoff (I := I) g α z₀ b =ᶠ[𝓝 z] (fun _ => (0 : E × E)) := by
      refine Filter.eventuallyEq_of_mem (hopen.mem_nhds hmem) ?_
      intro w hw
      have hw' : b.rOut < dist w z₀ := hw
      have hb0 : (b : E × E → ℝ) w = 0 := b.zero_of_le_dist (le_of_lt hw')
      simp [chartPhaseVFCutoff_apply, hb0]
    have hfd_eq : fderiv ℝ (chartPhaseVFCutoff (I := I) g α z₀ b) z =
        fderiv ℝ (fun _ : E × E => (0 : E × E)) z :=
      Filter.EventuallyEq.fderiv_eq hev
    have hfd_zero : fderiv ℝ (fun _ : E × E => (0 : E × E)) z = 0 := by
      change fderiv ℝ (0 : E × E → E × E) z = 0
      rw [fderiv_zero]; rfl
    rw [hfd_eq, hfd_zero]
    rw [norm_zero]
    exact hMglob_nn

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem exists_chartPhase_contDiffOn_isLocalFlow
    [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (α : M) {x₀ v₀ : E}
    (hx₀ : x₀ ∈ interior (extChartAt I α).target) :
    ∃ (b : ContDiffBump ((x₀, v₀) : E × E))
      (ρ T : ℝ)
      (Φ : (E × E) × ℝ → E × E),
      0 < ρ ∧ 0 < T ∧
      Metric.closedBall ((x₀, v₀) : E × E) b.rOut ⊆
        (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E) ∧
      ContDiffOn ℝ 1 Φ
        ((Metric.ball ((x₀, v₀) : E × E) ρ) ×ˢ Set.Ioo (-T) T) ∧
      Φ (((x₀, v₀) : E × E), 0) = (x₀, v₀) := by
  classical
  obtain ⟨b, hb_sub⟩ :=
    exists_contDiffBump_subset_chart_interior (I := I) (α := α)
      (x₀ := x₀) (v₀ := v₀) hx₀
  have hC1 :
      ContDiffOn ℝ 1
        (Function.uncurry (chartPhaseVFTime (I := I) g α (x₀, v₀) b))
        (Set.univ : Set (ℝ × (E × E))) :=
    chartPhaseVFTime_uncurry_contDiffOn_univ_one (I := I) g α (x₀, v₀) b hb_sub
  obtain ⟨rN, εN, hrN, hεN, Φ, hΦ⟩ :=
    DifferentialGeometry.Analysis.ODE.Flow.exists_isLocalFlow_of_contDiffOn_univ
      (E := E × E) (chartPhaseVFTime (I := I) g α (x₀, v₀) b) hC1 0 (x₀, v₀)
  obtain ⟨Mglob, hMglob_nn, hMglob_bound⟩ :=
    exists_bound_fderiv_chartPhaseVFCutoff (I := I) g α (x₀, v₀) b hb_sub
  have hfderiv_eq : ∀ (τ : ℝ) (z : E × E),
      fderiv ℝ (chartPhaseVFTime (I := I) g α (x₀, v₀) b τ) z =
        fderiv ℝ (chartPhaseVFCutoff (I := I) g α (x₀, v₀) b) z := by
    intro τ z
    rfl
  set Tcap : ℝ := min εN (1 / (2 * (Mglob + 1))) with hTcap_def
  have hTcap_pos : 0 < Tcap := by
    apply lt_min hεN
    apply div_pos one_pos
    positivity
  set T_out : ℝ := Tcap / 2 with hT_out_def
  set T_mid : ℝ := Tcap / 4 with hT_mid_def
  set T : ℝ := Tcap / 8 with hT_def
  have hT_pos : 0 < T := by positivity
  have hT_lt_mid : T < T_mid := by
    have : (0 : ℝ) < Tcap := hTcap_pos
    change Tcap / 8 < Tcap / 4; linarith
  have hT_mid_lt_out : T_mid < T_out := by
    have : (0 : ℝ) < Tcap := hTcap_pos
    change Tcap / 4 < Tcap / 2; linarith
  have hT_out_le_eps : T_out ≤ εN := by
    have hpos : 0 < εN := hεN
    have hcap_le : Tcap ≤ εN := min_le_left _ _
    change Tcap / 2 ≤ εN; linarith
  have hMT_mid_lt_one : Mglob * T_mid < 1 := by
    have h_cap_le : Tcap ≤ 1 / (2 * (Mglob + 1)) := min_le_right _ _
    have hT_mid_le : T_mid ≤ 1 / (8 * (Mglob + 1)) := by
      change Tcap / 4 ≤ 1 / (8 * (Mglob + 1))
      have hpos_den : (0 : ℝ) < 2 * (Mglob + 1) := by positivity
      have hstep : Tcap / 4 ≤ (1 / (2 * (Mglob + 1))) / 4 := by linarith
      have heq : (1 / (2 * (Mglob + 1))) / 4 = 1 / (8 * (Mglob + 1)) := by
        field_simp; ring
      linarith [heq ▸ hstep]
    have hMplus_pos : (0 : ℝ) < Mglob + 1 := by linarith
    have hMplus8_pos : (0 : ℝ) < 8 * (Mglob + 1) := by positivity
    have hbound_aux : Mglob / (8 * (Mglob + 1)) ≤ 1 / 8 := by
      have hnum : Mglob * 8 ≤ 1 * (8 * (Mglob + 1)) := by nlinarith [hMglob_nn]
      have := (div_le_div_iff_of_pos_left (a := (1 : ℝ)) (by norm_num)
        hMplus8_pos (by norm_num : (0 : ℝ) < 8))
      rw [div_le_iff₀ hMplus8_pos, div_mul_eq_mul_div, le_div_iff₀ (by norm_num : (0 : ℝ) < 8)]
      nlinarith [hMglob_nn]
    calc Mglob * T_mid ≤ Mglob * (1 / (8 * (Mglob + 1))) := by
            apply mul_le_mul_of_nonneg_left hT_mid_le hMglob_nn
      _ = Mglob / (8 * (Mglob + 1)) := by ring
      _ ≤ 1 / 8 := hbound_aux
      _ < 1 := by norm_num
  have hsub_T_out : Set.Icc ((0 : ℝ) - T_out) (0 + T_out) ⊆
      Set.Icc ((0 : ℝ) - εN) (0 + εN) := by
    intro t ht
    refine ⟨?_, ?_⟩
    · linarith [ht.1, hT_out_le_eps]
    · linarith [ht.2, hT_out_le_eps]
  set ρ_out : ℝ≥0 := ⟨(rN : ℝ) / 2, by positivity⟩ with hρ_out_def
  set ρ_mid : ℝ≥0 := ⟨(rN : ℝ) / 4, by positivity⟩ with hρ_mid_def
  set ρ : ℝ≥0 := ⟨(rN : ℝ) / 8, by positivity⟩ with hρ_def
  set r' : ℝ≥0 := ⟨(rN : ℝ) / 8, by positivity⟩ with hr'_def
  have hr'_pos : 0 < r' := by
    change (0 : ℝ) < (rN : ℝ) / 8
    have : (0 : ℝ) < rN := hrN
    linarith
  have hρ_pos : (0 : ℝ) < (ρ : ℝ) := by
    change (0 : ℝ) < (rN : ℝ) / 8
    have : (0 : ℝ) < rN := hrN
    linarith
  have hρ_lt_mid : (ρ : ℝ) < (ρ_mid : ℝ) := by
    change (rN : ℝ) / 8 < (rN : ℝ) / 4
    have : (0 : ℝ) < rN := hrN
    linarith
  have hρ_mid_lt_out : (ρ_mid : ℝ) < (ρ_out : ℝ) := by
    change (rN : ℝ) / 4 < (rN : ℝ) / 2
    have : (0 : ℝ) < rN := hrN
    linarith
  have hρρ' : (ρ_mid : ℝ) + (r' : ℝ) ≤ (rN : ℝ) := by
    change (rN : ℝ) / 4 + (rN : ℝ) / 8 ≤ (rN : ℝ)
    have : (0 : ℝ) ≤ rN := le_of_lt hrN
    linarith
  have hρ_out_le_r : (ρ_out : ℝ) ≤ (rN : ℝ) := by
    change (rN : ℝ) / 2 ≤ (rN : ℝ)
    have : (0 : ℝ) ≤ rN := le_of_lt hrN
    linarith
  have hA_bd : ∀ x ∈ Metric.closedBall ((x₀, v₀) : E × E) (ρ_out : ℝ),
      ∀ τ ∈ Set.Icc (0 - T_out) (0 + T_out),
      ‖fderiv ℝ (chartPhaseVFTime (I := I) g α (x₀, v₀) b τ) (Φ ⟨x, τ⟩)‖
        ≤ Mglob := by
    intro x _ τ _
    rw [hfderiv_eq]
    exact hMglob_bound _
  have hCDOn :=
    DifferentialGeometry.Analysis.ODE.Flow.contDiffOn_flow_of_isLocalFlow
      hΦ hC1 hT_pos hT_lt_mid hT_mid_lt_out hMglob_nn hMT_mid_lt_one hsub_T_out
      hr'_pos hρ_lt_mid hρ_mid_lt_out hρρ' hρ_out_le_r hA_bd
  have hball_eq : (Metric.ball ((x₀, v₀) : E × E) ((ρ : ℝ))) ×ˢ
      Set.Ioo (0 - T) (0 + T) =
      (Metric.ball ((x₀, v₀) : E × E) ((ρ : ℝ))) ×ˢ
      Set.Ioo (-T) T := by
    congr 1
    ext t
    simp only [Set.mem_Ioo, zero_sub, zero_add]
  rw [hball_eq] at hCDOn
  have hinitial : Φ (((x₀, v₀) : E × E), 0) = (x₀, v₀) :=
    hΦ.apply_initial (x₀, v₀) (Metric.mem_closedBall_self (by
      exact_mod_cast (le_of_lt hrN)))
  refine ⟨b, (ρ : ℝ), T, Φ, hρ_pos, hT_pos, hb_sub, hCDOn, hinitial⟩

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem exists_chartPhase_contDiffOn_isLocalFlow_combined
    [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (α : M) {x₀ v₀ : E}
    (hx₀ : x₀ ∈ interior (extChartAt I α).target) :
    ∃ (b : ContDiffBump ((x₀, v₀) : E × E))
      (r : ℝ≥0) (ε : ℝ) (ρ T : ℝ)
      (Φ : (E × E) × ℝ → E × E),
      0 < r ∧ 0 < ε ∧ 0 < ρ ∧ 0 < T ∧
      Metric.closedBall ((x₀, v₀) : E × E) b.rOut ⊆
        (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E) ∧
      DifferentialGeometry.Analysis.ODE.Flow.IsLocalFlow
        (chartPhaseVFTime (I := I) g α (x₀, v₀) b)
        (0 : ℝ) (x₀, v₀) r (-ε) ε Φ ∧
      ContDiffOn ℝ 1 Φ
        ((Metric.ball ((x₀, v₀) : E × E) ρ) ×ˢ Set.Ioo (-T) T) ∧
      Φ (((x₀, v₀) : E × E), 0) = (x₀, v₀) := by
  classical
  obtain ⟨b, hb_sub⟩ :=
    exists_contDiffBump_subset_chart_interior (I := I) (α := α)
      (x₀ := x₀) (v₀ := v₀) hx₀
  have hC1 :
      ContDiffOn ℝ 1
        (Function.uncurry (chartPhaseVFTime (I := I) g α (x₀, v₀) b))
        (Set.univ : Set (ℝ × (E × E))) :=
    chartPhaseVFTime_uncurry_contDiffOn_univ_one (I := I) g α (x₀, v₀) b hb_sub
  obtain ⟨rN, εN, hrN, hεN, Φ, hΦ⟩ :=
    DifferentialGeometry.Analysis.ODE.Flow.exists_isLocalFlow_of_contDiffOn_univ
      (E := E × E) (chartPhaseVFTime (I := I) g α (x₀, v₀) b) hC1 0 (x₀, v₀)
  obtain ⟨Mglob, hMglob_nn, hMglob_bound⟩ :=
    exists_bound_fderiv_chartPhaseVFCutoff (I := I) g α (x₀, v₀) b hb_sub
  have hfderiv_eq : ∀ (τ : ℝ) (z : E × E),
      fderiv ℝ (chartPhaseVFTime (I := I) g α (x₀, v₀) b τ) z =
        fderiv ℝ (chartPhaseVFCutoff (I := I) g α (x₀, v₀) b) z := by
    intro τ z; rfl
  set Tcap : ℝ := min εN (1 / (2 * (Mglob + 1))) with hTcap_def
  have hTcap_pos : 0 < Tcap := by
    apply lt_min hεN
    apply div_pos one_pos
    positivity
  set T_out : ℝ := Tcap / 2 with hT_out_def
  set T_mid : ℝ := Tcap / 4 with hT_mid_def
  set T : ℝ := Tcap / 8 with hT_def
  have hT_pos : 0 < T := by positivity
  have hT_lt_mid : T < T_mid := by
    have : (0 : ℝ) < Tcap := hTcap_pos
    change Tcap / 8 < Tcap / 4; linarith
  have hT_mid_lt_out : T_mid < T_out := by
    have : (0 : ℝ) < Tcap := hTcap_pos
    change Tcap / 4 < Tcap / 2; linarith
  have hT_out_le_eps : T_out ≤ εN := by
    have hpos : 0 < εN := hεN
    have hcap_le : Tcap ≤ εN := min_le_left _ _
    change Tcap / 2 ≤ εN; linarith
  have hMT_mid_lt_one : Mglob * T_mid < 1 := by
    have h_cap_le : Tcap ≤ 1 / (2 * (Mglob + 1)) := min_le_right _ _
    have hT_mid_le : T_mid ≤ 1 / (8 * (Mglob + 1)) := by
      change Tcap / 4 ≤ 1 / (8 * (Mglob + 1))
      have hpos_den : (0 : ℝ) < 2 * (Mglob + 1) := by positivity
      have hstep : Tcap / 4 ≤ (1 / (2 * (Mglob + 1))) / 4 := by linarith
      have heq : (1 / (2 * (Mglob + 1))) / 4 = 1 / (8 * (Mglob + 1)) := by
        field_simp; ring
      linarith [heq ▸ hstep]
    have hMplus_pos : (0 : ℝ) < Mglob + 1 := by linarith
    have hMplus8_pos : (0 : ℝ) < 8 * (Mglob + 1) := by positivity
    have hbound_aux : Mglob / (8 * (Mglob + 1)) ≤ 1 / 8 := by
      rw [div_le_iff₀ hMplus8_pos, div_mul_eq_mul_div,
          le_div_iff₀ (by norm_num : (0 : ℝ) < 8)]
      nlinarith [hMglob_nn]
    calc Mglob * T_mid ≤ Mglob * (1 / (8 * (Mglob + 1))) := by
            apply mul_le_mul_of_nonneg_left hT_mid_le hMglob_nn
      _ = Mglob / (8 * (Mglob + 1)) := by ring
      _ ≤ 1 / 8 := hbound_aux
      _ < 1 := by norm_num
  have hsub_T_out : Set.Icc ((0 : ℝ) - T_out) (0 + T_out) ⊆
      Set.Icc ((0 : ℝ) - εN) (0 + εN) := by
    intro t ht
    refine ⟨?_, ?_⟩
    · linarith [ht.1, hT_out_le_eps]
    · linarith [ht.2, hT_out_le_eps]
  set ρ_out : ℝ≥0 := ⟨(rN : ℝ) / 2, by positivity⟩ with hρ_out_def
  set ρ_mid : ℝ≥0 := ⟨(rN : ℝ) / 4, by positivity⟩ with hρ_mid_def
  set ρ : ℝ≥0 := ⟨(rN : ℝ) / 8, by positivity⟩ with hρ_def
  set r' : ℝ≥0 := ⟨(rN : ℝ) / 8, by positivity⟩ with hr'_def
  have hr'_pos : 0 < r' := by
    change (0 : ℝ) < (rN : ℝ) / 8
    have : (0 : ℝ) < rN := hrN
    linarith
  have hρ_pos : (0 : ℝ) < (ρ : ℝ) := by
    change (0 : ℝ) < (rN : ℝ) / 8
    have : (0 : ℝ) < rN := hrN
    linarith
  have hρ_lt_mid : (ρ : ℝ) < (ρ_mid : ℝ) := by
    change (rN : ℝ) / 8 < (rN : ℝ) / 4
    have : (0 : ℝ) < rN := hrN
    linarith
  have hρ_mid_lt_out : (ρ_mid : ℝ) < (ρ_out : ℝ) := by
    change (rN : ℝ) / 4 < (rN : ℝ) / 2
    have : (0 : ℝ) < rN := hrN
    linarith
  have hρρ' : (ρ_mid : ℝ) + (r' : ℝ) ≤ (rN : ℝ) := by
    change (rN : ℝ) / 4 + (rN : ℝ) / 8 ≤ (rN : ℝ)
    have : (0 : ℝ) ≤ rN := le_of_lt hrN
    linarith
  have hρ_out_le_r : (ρ_out : ℝ) ≤ (rN : ℝ) := by
    change (rN : ℝ) / 2 ≤ (rN : ℝ)
    have : (0 : ℝ) ≤ rN := le_of_lt hrN
    linarith
  have hA_bd : ∀ x ∈ Metric.closedBall ((x₀, v₀) : E × E) (ρ_out : ℝ),
      ∀ τ ∈ Set.Icc (0 - T_out) (0 + T_out),
      ‖fderiv ℝ (chartPhaseVFTime (I := I) g α (x₀, v₀) b τ) (Φ ⟨x, τ⟩)‖
        ≤ Mglob := by
    intro x _ τ _
    rw [hfderiv_eq]
    exact hMglob_bound _
  have hCDOn :=
    DifferentialGeometry.Analysis.ODE.Flow.contDiffOn_flow_of_isLocalFlow
      hΦ hC1 hT_pos hT_lt_mid hT_mid_lt_out hMglob_nn hMT_mid_lt_one hsub_T_out
      hr'_pos hρ_lt_mid hρ_mid_lt_out hρρ' hρ_out_le_r hA_bd
  have hball_eq : (Metric.ball ((x₀, v₀) : E × E) ((ρ : ℝ))) ×ˢ
      Set.Ioo (0 - T) (0 + T) =
      (Metric.ball ((x₀, v₀) : E × E) ((ρ : ℝ))) ×ˢ
      Set.Ioo (-T) T := by
    congr 1
    ext t
    simp only [Set.mem_Ioo, zero_sub, zero_add]
  rw [hball_eq] at hCDOn
  have heq1 : (0 : ℝ) - εN = -εN := by ring
  have heq2 : (0 : ℝ) + εN = εN := by ring
  have hΦ' : DifferentialGeometry.Analysis.ODE.Flow.IsLocalFlow
        (chartPhaseVFTime (I := I) g α (x₀, v₀) b)
        (0 : ℝ) (x₀, v₀) rN (-εN) εN Φ := by
    have := hΦ
    rw [heq1, heq2] at this
    exact this
  have hinitial : Φ (((x₀, v₀) : E × E), 0) = (x₀, v₀) :=
    hΦ'.apply_initial (x₀, v₀) (Metric.mem_closedBall_self (by
      exact_mod_cast (le_of_lt hrN)))
  exact ⟨b, rN, εN, (ρ : ℝ), T, Φ, hrN, hεN, hρ_pos, hT_pos, hb_sub, hΦ', hCDOn, hinitial⟩

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem exists_chartPhase_contDiffOn_isLocalFlow_combined_two
    [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (α : M) {x₀ v₀ : E}
    (hx₀ : x₀ ∈ interior (extChartAt I α).target) :
    ∃ (b : ContDiffBump ((x₀, v₀) : E × E))
      (r : ℝ≥0) (ε : ℝ) (ρ T : ℝ)
      (Φ : (E × E) × ℝ → E × E),
      0 < r ∧ 0 < ε ∧ 0 < ρ ∧ 0 < T ∧
      Metric.closedBall ((x₀, v₀) : E × E) b.rOut ⊆
        (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E) ∧
      DifferentialGeometry.Analysis.ODE.Flow.IsLocalFlow
        (chartPhaseVFTime (I := I) g α (x₀, v₀) b)
        (0 : ℝ) (x₀, v₀) r (-ε) ε Φ ∧
      ContDiffOn ℝ 2 Φ
        ((Metric.ball ((x₀, v₀) : E × E) ρ) ×ˢ Set.Ioo (-T) T) ∧
      Φ (((x₀, v₀) : E × E), 0) = (x₀, v₀) := by
  classical
  obtain ⟨b, hb_sub⟩ :=
    exists_contDiffBump_subset_chart_interior (I := I) (α := α)
      (x₀ := x₀) (v₀ := v₀) hx₀
  have hC1 :
      ContDiffOn ℝ 1
        (Function.uncurry (chartPhaseVFTime (I := I) g α (x₀, v₀) b))
        (Set.univ : Set (ℝ × (E × E))) :=
    chartPhaseVFTime_uncurry_contDiffOn_univ_one (I := I) g α (x₀, v₀) b hb_sub
  have hC2 :
      ContDiffOn ℝ 2
        (Function.uncurry (chartPhaseVFTime (I := I) g α (x₀, v₀) b))
        (Set.univ : Set (ℝ × (E × E))) :=
    chartPhaseVFTime_uncurry_contDiffOn_univ_two (I := I) g α (x₀, v₀) b hb_sub
  obtain ⟨rN, εN, hrN, hεN, Φ, hΦ⟩ :=
    DifferentialGeometry.Analysis.ODE.Flow.exists_isLocalFlow_of_contDiffOn_univ
      (E := E × E) (chartPhaseVFTime (I := I) g α (x₀, v₀) b) hC1 0 (x₀, v₀)
  have ht₀_mem : (0 : ℝ) ∈ Set.Ioo ((0 : ℝ) - εN) ((0 : ℝ) + εN) :=
    ⟨by linarith, by linarith⟩
  have hrN_pos : 0 < (rN : ℝ) := hrN
  obtain ⟨U, hU_open, hU_mem, hU_C2⟩ :=
    DifferentialGeometry.Analysis.ODE.Flow.exists_contDiffOn_flow_C2
      (E := E × E) hΦ hC2 ht₀_mem hrN_pos
  have hU_nhds : U ∈ 𝓝 (((x₀, v₀) : E × E), (0 : ℝ)) :=
    hU_open.mem_nhds hU_mem
  obtain ⟨Uspace, Utime, hUspace_open, hUspace_mem, hUtime_open, hUtime_mem,
      hU_prod_sub⟩ := mem_nhds_prod_iff'.mp hU_nhds
  obtain ⟨ρ, hρ_pos, hρ_sub⟩ :=
    Metric.isOpen_iff.mp hUspace_open ((x₀, v₀) : E × E) hUspace_mem
  obtain ⟨δ, hδ_pos, hδ_sub⟩ :=
    Metric.isOpen_iff.mp hUtime_open (0 : ℝ) hUtime_mem
  set T : ℝ := δ with hT_def
  have hT_pos : 0 < T := hδ_pos
  have hIoo_sub : Set.Ioo (-T) T ⊆ Utime := by
    intro t ht
    apply hδ_sub
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
    exact ⟨ht.1, ht.2⟩
  have hprod_sub : (Metric.ball ((x₀, v₀) : E × E) ρ) ×ˢ Set.Ioo (-T) T ⊆ U := by
    intro w hw
    refine hU_prod_sub ⟨hρ_sub hw.1, hIoo_sub hw.2⟩
  have hCDOn : ContDiffOn ℝ 2 Φ
      ((Metric.ball ((x₀, v₀) : E × E) ρ) ×ˢ Set.Ioo (-T) T) :=
    hU_C2.mono hprod_sub
  have heq1 : (0 : ℝ) - εN = -εN := by ring
  have heq2 : (0 : ℝ) + εN = εN := by ring
  have hΦ' : DifferentialGeometry.Analysis.ODE.Flow.IsLocalFlow
        (chartPhaseVFTime (I := I) g α (x₀, v₀) b)
        (0 : ℝ) (x₀, v₀) rN (-εN) εN Φ := by
    have := hΦ
    rw [heq1, heq2] at this
    exact this
  have hinitial : Φ (((x₀, v₀) : E × E), 0) = (x₀, v₀) :=
    hΦ'.apply_initial (x₀, v₀) (Metric.mem_closedBall_self (by
      exact_mod_cast (le_of_lt hrN)))
  exact ⟨b, rN, εN, ρ, T, Φ, hrN, hεN, hρ_pos, hT_pos, hb_sub, hΦ', hCDOn, hinitial⟩

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem exists_chartPhase_contDiffOn_isLocalFlow_combined_nat
    [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (α : M) {x₀ v₀ : E} (n : ℕ) (hn : 1 ≤ n)
    (hx₀ : x₀ ∈ interior (extChartAt I α).target) :
    ∃ (b : ContDiffBump ((x₀, v₀) : E × E))
      (r : ℝ≥0) (ε : ℝ) (ρ T : ℝ)
      (Φ : (E × E) × ℝ → E × E),
      0 < r ∧ 0 < ε ∧ 0 < ρ ∧ 0 < T ∧
      Metric.closedBall ((x₀, v₀) : E × E) b.rOut ⊆
        (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E) ∧
      DifferentialGeometry.Analysis.ODE.Flow.IsLocalFlow
        (chartPhaseVFTime (I := I) g α (x₀, v₀) b)
        (0 : ℝ) (x₀, v₀) r (-ε) ε Φ ∧
      ContDiffOn ℝ (n : ℕ∞) Φ
        ((Metric.ball ((x₀, v₀) : E × E) ρ) ×ˢ Set.Ioo (-T) T) ∧
      Φ (((x₀, v₀) : E × E), 0) = (x₀, v₀) := by
  classical
  obtain ⟨b, hb_sub⟩ :=
    exists_contDiffBump_subset_chart_interior (I := I) (α := α)
      (x₀ := x₀) (v₀ := v₀) hx₀
  have hC1 :
      ContDiffOn ℝ 1
        (Function.uncurry (chartPhaseVFTime (I := I) g α (x₀, v₀) b))
        (Set.univ : Set (ℝ × (E × E))) :=
    chartPhaseVFTime_uncurry_contDiffOn_univ_one (I := I) g α (x₀, v₀) b hb_sub
  have hCn :
      ContDiffOn ℝ (n : ℕ∞)
        (Function.uncurry (chartPhaseVFTime (I := I) g α (x₀, v₀) b))
        (Set.univ : Set (ℝ × (E × E))) :=
    chartPhaseVFTime_uncurry_contDiffOn_univ_nat (I := I) g α (x₀, v₀) b n hb_sub
  obtain ⟨rN, εN, hrN, hεN, Φ, hΦ⟩ :=
    DifferentialGeometry.Analysis.ODE.Flow.exists_isLocalFlow_of_contDiffOn_univ
      (E := E × E) (chartPhaseVFTime (I := I) g α (x₀, v₀) b) hC1 0 (x₀, v₀)
  have ht₀_mem : (0 : ℝ) ∈ Set.Ioo ((0 : ℝ) - εN) ((0 : ℝ) + εN) :=
    ⟨by linarith, by linarith⟩
  have hrN_pos : 0 < (rN : ℝ) := hrN
  obtain ⟨U, hU_open, hU_mem, hU_Cn⟩ :=
    DifferentialGeometry.Analysis.ODE.Flow.exists_contDiffOn_flow_Cnat
      (E := E × E) hΦ hn hCn ht₀_mem hrN_pos
  have hU_nhds : U ∈ 𝓝 (((x₀, v₀) : E × E), (0 : ℝ)) :=
    hU_open.mem_nhds hU_mem
  obtain ⟨Uspace, Utime, hUspace_open, hUspace_mem, hUtime_open, hUtime_mem,
      hU_prod_sub⟩ := mem_nhds_prod_iff'.mp hU_nhds
  obtain ⟨ρ, hρ_pos, hρ_sub⟩ :=
    Metric.isOpen_iff.mp hUspace_open ((x₀, v₀) : E × E) hUspace_mem
  obtain ⟨δ, hδ_pos, hδ_sub⟩ :=
    Metric.isOpen_iff.mp hUtime_open (0 : ℝ) hUtime_mem
  set T : ℝ := δ with hT_def
  have hT_pos : 0 < T := hδ_pos
  have hIoo_sub : Set.Ioo (-T) T ⊆ Utime := by
    intro t ht
    apply hδ_sub
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
    exact ⟨ht.1, ht.2⟩
  have hprod_sub : (Metric.ball ((x₀, v₀) : E × E) ρ) ×ˢ Set.Ioo (-T) T ⊆ U := by
    intro w hw
    refine hU_prod_sub ⟨hρ_sub hw.1, hIoo_sub hw.2⟩
  have hCDOn : ContDiffOn ℝ (n : ℕ∞) Φ
      ((Metric.ball ((x₀, v₀) : E × E) ρ) ×ˢ Set.Ioo (-T) T) :=
    hU_Cn.mono hprod_sub
  have heq1 : (0 : ℝ) - εN = -εN := by ring
  have heq2 : (0 : ℝ) + εN = εN := by ring
  have hΦ' : DifferentialGeometry.Analysis.ODE.Flow.IsLocalFlow
        (chartPhaseVFTime (I := I) g α (x₀, v₀) b)
        (0 : ℝ) (x₀, v₀) rN (-εN) εN Φ := by
    have := hΦ
    rw [heq1, heq2] at this
    exact this
  have hinitial : Φ (((x₀, v₀) : E × E), 0) = (x₀, v₀) :=
    hΦ'.apply_initial (x₀, v₀) (Metric.mem_closedBall_self (by
      exact_mod_cast (le_of_lt hrN)))
  exact ⟨b, rN, εN, ρ, T, Φ, hrN, hεN, hρ_pos, hT_pos, hb_sub, hΦ', hCDOn, hinitial⟩










omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem exists_chartPhase_contDiffOn_isLocalFlow_combined_inf
    [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (α : M) {x₀ v₀ : E}
    (hx₀ : x₀ ∈ interior (extChartAt I α).target) :
    ∃ (b : ContDiffBump ((x₀, v₀) : E × E))
      (r : ℝ≥0) (ε : ℝ) (ρ T : ℝ)
      (Φ : (E × E) × ℝ → E × E),
      0 < r ∧ 0 < ε ∧ 0 < ρ ∧ 0 < T ∧
      Metric.closedBall ((x₀, v₀) : E × E) b.rOut ⊆
        (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E) ∧
      DifferentialGeometry.Analysis.ODE.Flow.IsLocalFlow
        (chartPhaseVFTime (I := I) g α (x₀, v₀) b)
        (0 : ℝ) (x₀, v₀) r (-ε) ε Φ ∧
      ContDiffOn ℝ ∞ Φ
        ((Metric.ball ((x₀, v₀) : E × E) ρ) ×ˢ Set.Ioo (-T) T) ∧
      Φ (((x₀, v₀) : E × E), 0) = (x₀, v₀) := by
  classical
  obtain ⟨b, hb_sub⟩ :=
    exists_contDiffBump_subset_chart_interior (I := I) (α := α)
      (x₀ := x₀) (v₀ := v₀) hx₀
  have hf_inf : ContDiff ℝ ∞
      (Function.uncurry (chartPhaseVFTime (I := I) g α (x₀, v₀) b)) :=
    chartPhaseVFTime_uncurry_contDiff (I := I) g α (x₀, v₀) b hb_sub
  have hC1 : ContDiffOn ℝ 1
      (Function.uncurry (chartPhaseVFTime (I := I) g α (x₀, v₀) b))
      (Set.univ : Set (ℝ × (E × E))) :=
    chartPhaseVFTime_uncurry_contDiffOn_univ_one (I := I) g α (x₀, v₀) b hb_sub
  obtain ⟨rN, εN, hrN, hεN, Φ, hΦ⟩ :=
    DifferentialGeometry.Analysis.ODE.Flow.exists_isLocalFlow_of_contDiffOn_univ
      (E := E × E) (chartPhaseVFTime (I := I) g α (x₀, v₀) b) hC1 0 (x₀, v₀)
  have heq1 : (0 : ℝ) - εN = -εN := by ring
  have heq2 : (0 : ℝ) + εN = εN := by ring
  have hΦ' : DifferentialGeometry.Analysis.ODE.Flow.IsLocalFlow
        (chartPhaseVFTime (I := I) g α (x₀, v₀) b)
        (0 : ℝ) (x₀, v₀) rN (-εN) εN Φ := by
    have := hΦ
    rw [heq1, heq2] at this
    exact this
  have ht₀_mem : (0 : ℝ) ∈ Set.Ioo (-εN) εN := ⟨by linarith, hεN⟩
  have hrN_pos : 0 < (rN : ℝ) := hrN
  obtain ⟨T_out, T_mid, T, M, ρ_out, ρ_mid, ρ, r',
    hT, hT_lt_mid, hT_mid_lt_out, hM, hMT_mid, hr', hρ_pos, hρ_lt_mid, hρ_mid_lt_out,
    hρρ', hρ_out_le_r, hsub, hA_bd⟩ :=
    DifferentialGeometry.Analysis.ODE.Flow.exists_flow_nesting_data hΦ' hC1 ht₀_mem hrN_pos
  have hCDOn0 : ContDiffOn ℝ ∞ Φ
      ((Metric.ball ((x₀, v₀) : E × E) ρ) ×ˢ Set.Ioo ((0 : ℝ) - T) ((0 : ℝ) + T)) :=
    hΦ'.contDiffOn_top hf_inf hT hT_lt_mid hT_mid_lt_out hM hMT_mid hsub hr'
      hρ_lt_mid hρ_mid_lt_out hρρ' hρ_out_le_r hA_bd
  have hCDOn : ContDiffOn ℝ ∞ Φ
      ((Metric.ball ((x₀, v₀) : E × E) ρ) ×ˢ Set.Ioo (-T) T) := by
    simpa only [zero_sub, zero_add] using hCDOn0
  have hinitial : Φ (((x₀, v₀) : E × E), 0) = (x₀, v₀) :=
    hΦ'.apply_initial (x₀, v₀) (Metric.mem_closedBall_self (by exact_mod_cast (le_of_lt hrN)))
  exact ⟨b, rN, εN, ρ, T, Φ, hrN, hεN, hρ_pos, hT, hb_sub, hΦ', hCDOn, hinitial⟩

end Geodesic
end Riemannian
end Geometry
end DifferentialGeometry

end
