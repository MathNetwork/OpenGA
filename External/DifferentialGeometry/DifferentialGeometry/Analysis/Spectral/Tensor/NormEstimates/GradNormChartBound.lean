import DifferentialGeometry.Geometry.Operator.Gradient
import DifferentialGeometry.Analysis.Integration.Measure.RiemannianMeasure
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChartComponent.ComponentSobolevBound
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChartComponent.ComponentSobolevPointwise
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.ChartGeometry.GoodSetMeasure


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

section CompactBound

variable [CompactSpace M]

private lemma tsupport_chartAtlasPOU_isCompact (α : M) :
    IsCompact (tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) :=
  isClosed_tsupport _ |>.isCompact

omit [CompactSpace M] in
private lemma tsupport_chartAtlasPOU_subset_chartSource (α : M) :
    tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ⊆
      (chartAt H α).source := by
  intro x hx
  exact (chartAtlasPOU_isSubordinate I M) α hx

theorem exists_chartInvGramMatrix_l1Sum_sup_on_pouTsupport
    (g : SmoothRiemannianMetric I M) (α : M) :
    ∃ M_Ginv : ℝ, 0 ≤ M_Ginv ∧
      ∀ b : M, b ∈ tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        chartInvGramMatrix_l1Sum (I := I) (M := M) g α b ≤ M_Ginv := by
  classical
  set K : Set M := tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) with hK
  have hK_compact : IsCompact K :=
    tsupport_chartAtlasPOU_isCompact (I := I) (M := M) α
  have hK_subset : K ⊆ (chartAt H α).source :=
    tsupport_chartAtlasPOU_subset_chartSource (I := I) (M := M) α
  have h_cont : ContinuousOn
      (chartInvGramMatrix_l1Sum (I := I) (M := M) g α) K :=
    (chartInvGramMatrix_l1Sum_continuousOn (I := I) (M := M) g α).mono hK_subset
  by_cases hK_ne : K.Nonempty
  · obtain ⟨b_max, _hb_max_mem, hb_max_isMax⟩ :=
      hK_compact.exists_isMaxOn hK_ne h_cont
    refine ⟨max (chartInvGramMatrix_l1Sum (I := I) (M := M) g α b_max) 0,
            le_max_right _ _, ?_⟩
    intro b hb
    have h_le_max : chartInvGramMatrix_l1Sum (I := I) (M := M) g α b ≤
        chartInvGramMatrix_l1Sum (I := I) (M := M) g α b_max := hb_max_isMax hb
    exact h_le_max.trans (le_max_left _ _)
  · refine ⟨0, le_refl 0, ?_⟩
    intro b hb
    exact (hK_ne ⟨b, hb⟩).elim

end CompactBound

section VanishOutsidePou

variable [CompactSpace M] [I.Boundaryless] [NeZero (Module.finrank ℝ E)]

omit [CompactSpace M] [I.Boundaryless] [NeZero (Module.finrank ℝ E)] in
private lemma tensorChartComponentScalar_eventuallyEq_zero_of_notMem_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {b : M} (hb : b ∉ tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) :
    tensorChartComponentScalar (I := I) (M := M) g r s S α Idx Jdx =ᶠ[𝓝 b]
      (fun _ : M => (0 : ℝ)) := by
  classical
  set K : Set M := tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) with hK_def
  have hK_closed : IsClosed K := isClosed_tsupport _
  have h_open_compl : IsOpen Kᶜ := hK_closed.isOpen_compl
  have hb_compl : b ∈ Kᶜ := hb
  have h_mem : Kᶜ ∈ 𝓝 b := h_open_compl.mem_nhds hb_compl
  refine Filter.eventually_of_mem h_mem ?_
  intro y hy
  have hy_notin : y ∉ K := hy
  have hy_notin_supp : y ∉ Function.support
      (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) := by
    intro h_in
    exact hy_notin (subset_tsupport _ h_in)
  have h_rho_zero : ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) y = 0 := by
    by_contra h_ne
    exact hy_notin_supp h_ne
  change tensorChartComponentScalar (I := I) (M := M) g r s S α Idx Jdx y = 0
  unfold tensorChartComponentScalar tensorChartComponentPou
  rw [h_rho_zero, zero_mul]

omit [CompactSpace M] [I.Boundaryless] [NeZero (Module.finrank ℝ E)] in
private lemma gradFun_tensorChartComponentScalar_eq_zero_of_notMem_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {b : M} (hb : b ∉ tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) :
    gradFun (I := I) g
        (tensorChartComponentScalar (I := I) (M := M)
          g r s S α Idx Jdx) b = (0 : TangentSpace I b) :=
  gradFun_eq_zero_of_eventuallyEq_zero (I := I) g
    (tensorChartComponentScalar_eventuallyEq_zero_of_notMem_pouTsupport
      (I := I) (M := M) g r s S α Idx Jdx hb)

omit [CompactSpace M] [I.Boundaryless] [NeZero (Module.finrank ℝ E)] in
theorem sqrt_g_inner_gradFun_tensorChartComponentScalar_eq_zero_outside_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {b : M} (hb : b ∉ tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) :
    Real.sqrt
        (g.inner b
          (gradFun (I := I) g
            (tensorChartComponentScalar (I := I) (M := M)
              g r s S α Idx Jdx) b)
          (gradFun (I := I) g
            (tensorChartComponentScalar (I := I) (M := M)
              g r s S α Idx Jdx) b)) = 0 := by
  have h_grad_zero :
      gradFun (I := I) g
          (tensorChartComponentScalar (I := I) (M := M)
            g r s S α Idx Jdx) b = (0 : TangentSpace I b) :=
    gradFun_tensorChartComponentScalar_eq_zero_of_notMem_pouTsupport
      (I := I) (M := M) g r s S α Idx Jdx hb
  rw [h_grad_zero]
  have h_inner_zero : g.inner b
      (0 : TangentSpace I b) (0 : TangentSpace I b) = 0 := by
    rw [map_zero]
  rw [h_inner_zero, Real.sqrt_zero]

end VanishOutsidePou

section LeibnizChartPartial

variable [CompactSpace M] [I.Boundaryless] [NeZero (Module.finrank ℝ E)]

open DifferentialGeometry.Integral.DivergenceTheorem

omit [Module.Finite ℝ E] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless] [NeZero (Module.finrank ℝ E)] in
private lemma scalarOnE_mul_pointwise (α : M) (f g : M → ℝ) :
    scalarOnE (I := I) α (fun x : M => f x * g x) =
      (fun y : E => scalarOnE (I := I) α f y * scalarOnE (I := I) α g y) := by
  funext y
  unfold scalarOnE
  rfl

omit [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless] [NeZero (Module.finrank ℝ E)] in
private lemma scalarOnE_tensorChartComponentRaw_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (scalarOnE (I := I) α
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx))
      (extChartAt I α).target := by
  classical
  have hraw_on :
      ContMDiffOn I (𝓘(ℝ, ℝ)) ∞
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)
        ((chartAt H α).source) :=
    tensorChartComponentRaw_contMDiffOn_chart_source
      (I := I) (M := M) g r s S α Idx Jdx
  have hsrc_eq : (chartAt H α).source = (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]
  have hraw_on' :
      ContMDiffOn I (𝓘(ℝ, ℝ)) ∞
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)
        ((extChartAt I α).source) := by
    rw [← hsrc_eq]; exact hraw_on
  have hsymm :
      ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I α).symm
        (extChartAt I α).target := contMDiffOn_extChartAt_symm (I := I) α
  have hsymm_maps :
      Set.MapsTo (extChartAt I α).symm
        (extChartAt I α).target (extChartAt I α).source := fun _ hy =>
    (extChartAt I α).map_target hy
  have hcomp :
      ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, ℝ)) ∞
        ((tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx) ∘
          (extChartAt I α).symm)
        (extChartAt I α).target :=
    hraw_on'.comp hsymm hsymm_maps
  exact hcomp.contDiffOn

omit [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [NeZero (Module.finrank ℝ E)] in
private lemma differentiableAt_scalarOnE_tensorChartComponentRaw
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {z : E} (hz : z ∈ (extChartAt I α).target) :
    DifferentiableAt ℝ
      (scalarOnE (I := I) α
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)) z := by
  classical
  have h_smooth :=
    scalarOnE_tensorChartComponentRaw_contDiffOn
      (I := I) (M := M) g r s S α Idx Jdx
  have h_open : IsOpen ((extChartAt I α).target) :=
    isOpen_extChartAt_target (I := I) α
  have h_within :
      ContDiffWithinAt ℝ ∞
        (scalarOnE (I := I) α
          (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx))
        (extChartAt I α).target z := h_smooth z hz
  have h_at :
      ContDiffAt ℝ ∞
        (scalarOnE (I := I) α
          (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)) z :=
    h_within.contDiffAt (h_open.mem_nhds hz)
  exact h_at.differentiableAt (by simp)

omit [CompactSpace M] [NeZero (Module.finrank ℝ E)] in
private lemma differentiableAt_scalarOnE_chartAtlasPOU
    (α : M) {z : E} (hz : z ∈ (extChartAt I α).target) :
    DifferentiableAt ℝ
      (scalarOnE (I := I) α
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) z := by
  classical
  have hPOU_smooth : ContMDiff I (𝓘(ℝ, ℝ)) ∞
      (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) :=
    (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff
  have h_smooth :
      ContDiffOn ℝ ∞
        (scalarOnE (I := I) α
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ))
        (extChartAt I α).target :=
    scalarOnE_contDiffOn (I := I) α hPOU_smooth
  have h_open : IsOpen ((extChartAt I α).target) :=
    isOpen_extChartAt_target (I := I) α
  have h_within :
      ContDiffWithinAt ℝ ∞
        (scalarOnE (I := I) α
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ))
        (extChartAt I α).target z := h_smooth z hz
  have h_at :
      ContDiffAt ℝ ∞
        (scalarOnE (I := I) α
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) z :=
    h_within.contDiffAt (h_open.mem_nhds hz)
  exact h_at.differentiableAt (by simp)

omit [CompactSpace M] [NeZero (Module.finrank ℝ E)] in
theorem partialDeriv_scalarOnE_tensorChartComponentScalar_leibniz
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {b : M} (hb : b ∈ (chartAt H α).source)
    (k : Fin (Module.finrank ℝ E)) :
    partialDeriv (E := E) k
      (scalarOnE (I := I) α
        (tensorChartComponentScalar (I := I) (M := M) g r s S α Idx Jdx))
      (extChartAt I α b) =
    partialDeriv (E := E) k
        (scalarOnE (I := I) α
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ))
        (extChartAt I α b) *
      scalarOnE (I := I) α
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)
        (extChartAt I α b) +
    scalarOnE (I := I) α
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
        (extChartAt I α b) *
      partialDeriv (E := E) k
        (scalarOnE (I := I) α
          (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx))
        (extChartAt I α b) := by
  classical
  set ρ : M → ℝ :=
    fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x with hρ_def
  set raw : M → ℝ :=
    tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx with hraw_def
  set z : E := extChartAt I α b with hz_def
  have hb_src : b ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hb
  have hz_target : z ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source hb_src
  have h_scalar_eq :
      tensorChartComponentScalar (I := I) (M := M) g r s S α Idx Jdx =
        (fun x : M => ρ x * raw x) := by
    funext x
    show tensorChartComponentScalar (I := I) (M := M) g r s S α Idx Jdx x =
        ρ x * raw x
    unfold tensorChartComponentScalar tensorChartComponentPou
    rfl
  have h_scalarOnE_prod :
      scalarOnE (I := I) α
          (tensorChartComponentScalar (I := I) (M := M) g r s S α Idx Jdx) =
        (fun y : E => scalarOnE (I := I) α ρ y * scalarOnE (I := I) α raw y) := by
    rw [h_scalar_eq]
    exact scalarOnE_mul_pointwise (I := I) α ρ raw
  have hρ_diff : DifferentiableAt ℝ (scalarOnE (I := I) α ρ) z :=
    differentiableAt_scalarOnE_chartAtlasPOU (I := I) (M := M) α hz_target
  have hraw_diff : DifferentiableAt ℝ (scalarOnE (I := I) α raw) z :=
    differentiableAt_scalarOnE_tensorChartComponentRaw
      (I := I) (M := M) g r s S α Idx Jdx hz_target
  unfold partialDeriv
  rw [h_scalarOnE_prod]
  have h_fderiv_mul :
      fderiv ℝ
          (fun y : E => scalarOnE (I := I) α ρ y * scalarOnE (I := I) α raw y) z =
        scalarOnE (I := I) α ρ z • fderiv ℝ (scalarOnE (I := I) α raw) z +
          scalarOnE (I := I) α raw z • fderiv ℝ (scalarOnE (I := I) α ρ) z :=
    fderiv_fun_mul hρ_diff hraw_diff
  rw [h_fderiv_mul]
  rw [ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply]
  simp only [smul_eq_mul]
  ring

end LeibnizChartPartial

section PointwiseGradientBound

variable [CompactSpace M] [I.Boundaryless] [NeZero (Module.finrank ℝ E)]

open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Connection
open Tensor0SBundle

omit [CompactSpace M] [I.Boundaryless] [NeZero (Module.finrank ℝ E)] in
private lemma scalarOnE_chartAtlasPOU_abs_le_one (α : M) (y : E) :
    |scalarOnE (I := I) α
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) y| ≤ 1 := by
  classical
  set x : M := (extChartAt I α).symm y
  have h_nn : 0 ≤ ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x :=
    (chartAtlasPOU I M).nonneg α x
  have h_le : ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x ≤ 1 :=
    (chartAtlasPOU I M).le_one α x
  have h_val :
      scalarOnE (I := I) α
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) y =
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x := rfl
  rw [h_val, abs_of_nonneg h_nn]
  exact h_le

omit [CompactSpace M] [NeZero (Module.finrank ℝ E)] in
private lemma sum_sq_partialDeriv_scalarOnE_chartAtlasPOU_continuousOn
    (α : M) :
    ContinuousOn (fun y : E =>
        ∑ k : Fin (Module.finrank ℝ E),
          (partialDeriv (E := E) k
            (scalarOnE (I := I) α
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) y) ^ 2)
      (extChartAt I α).target := by
  classical
  have h_smooth :
      ContDiffOn ℝ ∞
        (scalarOnE (I := I) α
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ))
        (extChartAt I α).target :=
    scalarOnE_contDiffOn (I := I) α
      (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff
  have h_fderiv_cont : ContinuousOn
      (fun y : E => fderiv ℝ (scalarOnE (I := I) α
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) y)
      (extChartAt I α).target :=
    h_smooth.continuousOn_fderiv_of_isOpen (isOpen_extChartAt_target (I := I) α)
      (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))
  refine continuousOn_finset_sum _ ?_
  intro k _
  unfold partialDeriv
  have h_eval_cont :
      Continuous (fun L : E →L[ℝ] ℝ => L ((chartModelBasis E) k)) :=
    continuous_id.clm_apply continuous_const
  exact (h_eval_cont.comp_continuousOn h_fderiv_cont).pow 2

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_sum_sq_partialDeriv_scalarOnE_chartAtlasPOU_sup
    (α : M) :
    ∃ M_dρ : ℝ, 0 ≤ M_dρ ∧
      ∀ b : M, b ∈ tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ∑ k : Fin (Module.finrank ℝ E),
          (partialDeriv (E := E) k
            (scalarOnE (I := I) α
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ))
            (extChartAt I α b)) ^ 2 ≤ M_dρ := by
  classical
  set K : Set M := tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) with hK_def
  have hK_compact : IsCompact K :=
    tsupport_chartAtlasPOU_isCompact (I := I) (M := M) α
  have hK_subset_chartSrc : K ⊆ (chartAt H α).source :=
    tsupport_chartAtlasPOU_subset_chartSource (I := I) (M := M) α
  have hK_subset_extSrc : K ⊆ (extChartAt I α).source := by
    intro x hx
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    exact hK_subset_chartSrc hx
  have h_ext_cont_on_K : ContinuousOn (extChartAt I α) K :=
    (continuousOn_extChartAt (I := I) α).mono hK_subset_extSrc
  set K' : Set E := (extChartAt I α) '' K with hK'_def
  have hK'_compact : IsCompact K' :=
    hK_compact.image_of_continuousOn h_ext_cont_on_K
  have hK'_subset_target : K' ⊆ (extChartAt I α).target := by
    rintro y ⟨x, hx_in_K, hx_eq⟩
    rw [← hx_eq]
    exact (extChartAt I α).map_source (hK_subset_extSrc hx_in_K)
  have h_cont_on_K' : ContinuousOn (fun y : E =>
        ∑ k : Fin (Module.finrank ℝ E),
          (partialDeriv (E := E) k
            (scalarOnE (I := I) α
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) y) ^ 2) K' :=
    (sum_sq_partialDeriv_scalarOnE_chartAtlasPOU_continuousOn
      (I := I) (M := M) α).mono hK'_subset_target
  by_cases hK'_ne : K'.Nonempty
  · obtain ⟨y_max, _hy_max_mem, hy_max_isMax⟩ :=
      hK'_compact.exists_isMaxOn hK'_ne h_cont_on_K'
    refine ⟨max (∑ k : Fin (Module.finrank ℝ E),
              (partialDeriv (E := E) k
                (scalarOnE (I := I) α
                  ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) y_max) ^ 2)
            0, le_max_right _ _, ?_⟩
    intro b hb
    have hb_in_K' : extChartAt I α b ∈ K' := ⟨b, hb, rfl⟩
    have h_le_max := hy_max_isMax hb_in_K'
    exact h_le_max.trans (le_max_left _ _)
  · refine ⟨0, le_refl 0, ?_⟩
    intro b hb
    have hb_in_K' : extChartAt I α b ∈ K' := ⟨b, hb, rfl⟩
    exact (hK'_ne ⟨_, hb_in_K'⟩).elim

omit [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless] [NeZero (Module.finrank ℝ E)] in
private lemma chartBasisVecFiber_eq_trivFromE_chartModelBasis
    (α : M) (k : Fin (Module.finrank ℝ E)) (b : M) :
    chartBasisVecFiber (I := I) α k b =
      trivFromE (I := I) α b ((chartModelBasis E) k) := rfl

private lemma sq_add_le_two_mul_sq_add_sq_local (a b : ℝ) :
    (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  have h : (a + b) ^ 2 + (a - b) ^ 2 = 2 * a ^ 2 + 2 * b ^ 2 := by ring
  have hsq : 0 ≤ (a - b) ^ 2 := sq_nonneg _
  linarith

omit [NeZero (Module.finrank ℝ E)] in
private theorem g_inner_gradFun_tensorChartComponentScalar_le_const_on_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g r s)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)) (b : M),
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        g.inner b
          (gradFun (I := I) g
            (tensorChartComponentScalar (I := I) (M := M)
              g r s S α Idx Jdx) b)
          (gradFun (I := I) g
            (tensorChartComponentScalar (I := I) (M := M)
              g r s S α Idx Jdx) b) ≤
          C * ((∑ k : Fin (Module.finrank ℝ E),
                ‖(trivializationAt (TensorRSModel r s ℝ E)
                    (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt
                      ℝ b
                  (chartTensorRSCovariantDerivative (I := I) r s g α
                    (fun b' => S.toSection b')
                    (chartBasisVecFiber (I := I) α k) b)‖ ^ 2)
              + (∑ k : Fin (Module.finrank ℝ E),
                ‖(trivializationAt (TensorRSModel r s ℝ E)
                    (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt
                      ℝ b
                  (- (∑ i : Fin r,
                      chartTensorRSInputSlotCorrection (I := I) r s g α
                        (fun b' => S.toSection b')
                        (chartBasisVecFiber (I := I) α k) b i)
                    + (∑ l : Fin s,
                        chartTensorRSOutputSlotCorrection (I := I) r s g α
                          (fun b' => S.toSection b')
                          (chartBasisVecFiber (I := I) α k) b l))‖ ^ 2)
              + (scalarOnE (I := I) α
                  (tensorChartComponentRaw (I := I) (M := M)
                    g r s S α Idx Jdx) (extChartAt I α b)) ^ 2) := by
  classical
  obtain ⟨M_Ginv, hM_Ginv_nn, hM_Ginv_le⟩ :=
    exists_chartInvGramMatrix_l1Sum_sup_on_pouTsupport (I := I) (M := M) g α
  obtain ⟨M_dρ, hM_dρ_nn, hM_dρ_le⟩ :=
    exists_sum_sq_partialDeriv_scalarOnE_chartAtlasPOU_sup (I := I) (M := M) α
  set C_proj : ℝ := chartComponentProjectionUniformBound (E := E) r s
    with hC_proj_def
  have hC_proj_nn : 0 ≤ C_proj :=
    chartComponentProjectionUniformBound_nonneg (E := E) r s
  set C : ℝ := max (max (2 * M_Ginv * M_dρ) (4 * M_Ginv * C_proj ^ 2)) 0
    with hC_def
  have hC_nn : 0 ≤ C := le_max_right _ _
  have h_coef1_le_C : 2 * M_Ginv * M_dρ ≤ C := by
    rw [hC_def]; exact le_max_of_le_left (le_max_left _ _)
  have h_coef2_le_C : 4 * M_Ginv * C_proj ^ 2 ≤ C := by
    rw [hC_def]; exact le_max_of_le_left (le_max_right _ _)
  refine ⟨C, hC_nn, ?_⟩
  intro S Idx Jdx b hb
  set z : E := extChartAt I α b with hz_def
  have hb_chart_src : b ∈ (chartAt H α).source :=
    tsupport_chartAtlasPOU_subset_chartSource (I := I) (M := M) α hb
  have hb_goodSet : b ∈ chartLeviCivitaGoodSet (I := I) α := by
    rw [chartLeviCivitaGoodSet_eq_extChartAt_source (I := I) α,
        extChartAt_source_eq_chartAt_source (I := I)]
    exact hb_chart_src
  have hu_mdiff_at : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (tensorChartComponentScalar (I := I) (M := M) g r s S α Idx Jdx) b :=
    ((tensorChartComponentScalar_contMDiff (I := I) (M := M)
        g r s S α Idx Jdx).contMDiffAt).mdifferentiableAt (by simp)
  set Tcov : Fin (Module.finrank ℝ E) → ℝ := fun k =>
    ‖(trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
      (chartTensorRSCovariantDerivative (I := I) r s g α
        (fun b' => S.toSection b')
        (chartBasisVecFiber (I := I) α k) b)‖ ^ 2
    with hTcov_def
  set Tchr : Fin (Module.finrank ℝ E) → ℝ := fun k =>
    ‖(trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
      (- (∑ i : Fin r,
          chartTensorRSInputSlotCorrection (I := I) r s g α
            (fun b' => S.toSection b')
            (chartBasisVecFiber (I := I) α k) b i)
        + (∑ l : Fin s,
            chartTensorRSOutputSlotCorrection (I := I) r s g α
              (fun b' => S.toSection b')
              (chartBasisVecFiber (I := I) α k) b l))‖ ^ 2
    with hTchr_def
  set Tcov_sum : ℝ := ∑ k : Fin (Module.finrank ℝ E), Tcov k with hTcov_sum_def
  set Tchr_sum : ℝ := ∑ k : Fin (Module.finrank ℝ E), Tchr k with hTchr_sum_def
  have hTcov_nn : ∀ k, 0 ≤ Tcov k := fun k => by rw [hTcov_def]; exact sq_nonneg _
  have hTchr_nn : ∀ k, 0 ≤ Tchr k := fun k => by rw [hTchr_def]; exact sq_nonneg _
  have hTcov_sum_nn : 0 ≤ Tcov_sum :=
    Finset.sum_nonneg (fun k _ => hTcov_nn k)
  have hTchr_sum_nn : 0 ≤ Tchr_sum :=
    Finset.sum_nonneg (fun k _ => hTchr_nn k)
  set raw_z : ℝ := scalarOnE (I := I) α
      (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx) z
    with hraw_z_def
  have hraw_sq_nn : 0 ≤ raw_z ^ 2 := sq_nonneg _
  set ρ_z : ℝ := scalarOnE (I := I) α
      (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) z
    with hρ_z_def
  have hρ_z_abs_le_one : |ρ_z| ≤ 1 := by
    rw [hρ_z_def]
    exact scalarOnE_chartAtlasPOU_abs_le_one (I := I) (M := M) α z
  have hρ_z_sq_le_one : ρ_z ^ 2 ≤ 1 := by
    rw [show ρ_z ^ 2 = |ρ_z| ^ 2 from by rw [sq_abs]]
    have h1 : |ρ_z| * |ρ_z| ≤ 1 * 1 :=
      mul_le_mul hρ_z_abs_le_one hρ_z_abs_le_one (abs_nonneg _) zero_le_one
    nlinarith [h1]
  have h_step_grad3 :
      g.inner b
        (gradFun (I := I) g
          (tensorChartComponentScalar (I := I) (M := M) g r s S α Idx Jdx) b)
        (gradFun (I := I) g
          (tensorChartComponentScalar (I := I) (M := M) g r s S α Idx Jdx) b) ≤
      chartInvGramMatrix_l1Sum (I := I) (M := M) g α b *
        ∑ k : Fin (Module.finrank ℝ E),
          (partialDeriv (E := E) k (scalarOnE (I := I) α
            (tensorChartComponentScalar (I := I) (M := M)
              g r s S α Idx Jdx)) z) ^ 2 := by
    have := g_inner_gradFun_le_chartInvGramMatrix_l1Sum_mul_sum_sq_partials
      (I := I) (M := M) g α
      (f := tensorChartComponentScalar (I := I) (M := M) g r s S α Idx Jdx)
      (x := b) hu_mdiff_at hb_chart_src
    rw [hz_def]
    exact this
  have h_l1Sum_le : chartInvGramMatrix_l1Sum (I := I) (M := M) g α b ≤ M_Ginv :=
    hM_Ginv_le b hb
  have h_leibniz : ∀ k : Fin (Module.finrank ℝ E),
      partialDeriv (E := E) k (scalarOnE (I := I) α
          (tensorChartComponentScalar (I := I) (M := M) g r s S α Idx Jdx)) z =
        partialDeriv (E := E) k (scalarOnE (I := I) α
            (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) z *
          raw_z +
        ρ_z *
          partialDeriv (E := E) k (scalarOnE (I := I) α
            (tensorChartComponentRaw (I := I) (M := M)
              g r s S α Idx Jdx)) z := by
    intro k
    have h := partialDeriv_scalarOnE_tensorChartComponentScalar_leibniz
      (I := I) (M := M) g r s S α Idx Jdx hb_chart_src k
    rw [hraw_z_def, hρ_z_def, hz_def]
    exact h
  have h_sq_le : ∀ k : Fin (Module.finrank ℝ E),
      (partialDeriv (E := E) k (scalarOnE (I := I) α
          (tensorChartComponentScalar (I := I) (M := M)
            g r s S α Idx Jdx)) z) ^ 2 ≤
        2 * ((partialDeriv (E := E) k (scalarOnE (I := I) α
              (fun x : M =>
                ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) z) ^ 2 *
            raw_z ^ 2) +
        2 * (ρ_z ^ 2 *
            (partialDeriv (E := E) k (scalarOnE (I := I) α
              (tensorChartComponentRaw (I := I) (M := M)
                g r s S α Idx Jdx)) z) ^ 2) := by
    intro k
    rw [h_leibniz k]
    have h_tri := sq_add_le_two_mul_sq_add_sq_local
      (partialDeriv (E := E) k (scalarOnE (I := I) α
        (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) z *
          raw_z)
      (ρ_z *
        partialDeriv (E := E) k (scalarOnE (I := I) α
          (tensorChartComponentRaw (I := I) (M := M)
            g r s S α Idx Jdx)) z)
    have h_eq1 : (partialDeriv (E := E) k (scalarOnE (I := I) α
        (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) z *
          raw_z) ^ 2 =
        (partialDeriv (E := E) k (scalarOnE (I := I) α
          (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) z) ^ 2
        * raw_z ^ 2 := by ring
    have h_eq2 : (ρ_z *
        partialDeriv (E := E) k (scalarOnE (I := I) α
          (tensorChartComponentRaw (I := I) (M := M)
            g r s S α Idx Jdx)) z) ^ 2 =
        ρ_z ^ 2 *
        (partialDeriv (E := E) k (scalarOnE (I := I) α
          (tensorChartComponentRaw (I := I) (M := M)
            g r s S α Idx Jdx)) z) ^ 2 := by ring
    linarith [h_tri, h_eq1.le, h_eq1.symm.le, h_eq2.le, h_eq2.symm.le]
  set Sρ : ℝ := ∑ k : Fin (Module.finrank ℝ E),
    (partialDeriv (E := E) k (scalarOnE (I := I) α
      (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) z) ^ 2
    with hSρ_def
  set Sraw : ℝ := ∑ k : Fin (Module.finrank ℝ E),
    (partialDeriv (E := E) k (scalarOnE (I := I) α
      (tensorChartComponentRaw (I := I) (M := M)
        g r s S α Idx Jdx)) z) ^ 2
    with hSraw_def
  have hSρ_nn : 0 ≤ Sρ := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hSraw_nn : 0 ≤ Sraw := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hSρ_le_M_dρ : Sρ ≤ M_dρ := by
    rw [hSρ_def, hz_def]
    exact hM_dρ_le b hb
  have h_sum_sq_le :
      ∑ k : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) k (scalarOnE (I := I) α
          (tensorChartComponentScalar (I := I) (M := M)
            g r s S α Idx Jdx)) z) ^ 2 ≤
      2 * raw_z ^ 2 * Sρ + 2 * ρ_z ^ 2 * Sraw := by
    have hRHS_eq :
        2 * raw_z ^ 2 * Sρ + 2 * ρ_z ^ 2 * Sraw =
        ∑ k : Fin (Module.finrank ℝ E),
          (2 * ((partialDeriv (E := E) k (scalarOnE (I := I) α
                (fun x : M =>
                  ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) z) ^ 2 *
              raw_z ^ 2) +
          2 * (ρ_z ^ 2 *
              (partialDeriv (E := E) k (scalarOnE (I := I) α
                (tensorChartComponentRaw (I := I) (M := M)
                  g r s S α Idx Jdx)) z) ^ 2)) := by
      rw [hSρ_def, hSraw_def]
      rw [Finset.mul_sum, Finset.mul_sum]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro k _
      ring
    rw [hRHS_eq]
    exact Finset.sum_le_sum (fun k _ => h_sq_le k)
  have h_sum_sq_le' :
      ∑ k : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) k (scalarOnE (I := I) α
          (tensorChartComponentScalar (I := I) (M := M)
            g r s S α Idx Jdx)) z) ^ 2 ≤
      2 * raw_z ^ 2 * M_dρ + 2 * Sraw := by
    have h1 : 2 * raw_z ^ 2 * Sρ ≤ 2 * raw_z ^ 2 * M_dρ := by
      have hcoef_nn : 0 ≤ 2 * raw_z ^ 2 := by positivity
      exact mul_le_mul_of_nonneg_left hSρ_le_M_dρ hcoef_nn
    have h2 : 2 * ρ_z ^ 2 * Sraw ≤ 2 * Sraw := by
      have h_2ρ_le : 2 * ρ_z ^ 2 ≤ 2 * 1 :=
        mul_le_mul_of_nonneg_left hρ_z_sq_le_one (by norm_num)
      have h_arith : 2 * 1 * Sraw = 2 * Sraw := by ring
      have h_step : 2 * ρ_z ^ 2 * Sraw ≤ 2 * 1 * Sraw :=
        mul_le_mul_of_nonneg_right h_2ρ_le hSraw_nn
      linarith [h_step, h_arith.le, h_arith.symm.le]
    linarith
  have h_twoTerm_per_k : ∀ k : Fin (Module.finrank ℝ E),
      (partialDeriv (E := E) k (scalarOnE (I := I) α
          (tensorChartComponentRaw (I := I) (M := M)
            g r s S α Idx Jdx)) z) ^ 2 ≤
        2 * ‖tensorChartComponentProjection (E := E) r s Idx Jdx‖ ^ 2 *
          Tcov k +
        2 * ‖tensorChartComponentProjection (E := E) r s Idx Jdx‖ ^ 2 *
          Tchr k := by
    intro k
    have h_lhs_eq :
        partialDeriv (E := E) k (scalarOnE (I := I) α
          (tensorChartComponentRaw (I := I) (M := M)
            g r s S α Idx Jdx)) z =
        fderiv ℝ
          (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx ∘
            (extChartAt I α).symm) z
          ((chartModelBasis E) k) := rfl
    rw [h_lhs_eq]
    have hXb : chartBasisVecFiber (I := I) α k b =
        trivFromE (I := I) α b ((chartModelBasis E) k) := rfl
    have h_split :=
      fderiv_tensorChartComponentRaw_pullback_norm_sq_two_term_split
        (I := I) (M := M) g r s α S Idx Jdx
        (chartBasisVecFiber (I := I) α k) hb_goodSet
        ((chartModelBasis E) k) hXb
    rw [hz_def]
    rw [hTcov_def, hTchr_def]
    exact h_split
  set Pnorm_sq : ℝ := ‖tensorChartComponentProjection (E := E) r s Idx Jdx‖ ^ 2
    with hPnorm_sq_def
  have hPnorm_sq_nn : 0 ≤ Pnorm_sq := sq_nonneg _
  have h_Sraw_le :
      Sraw ≤ 2 * Pnorm_sq * Tcov_sum + 2 * Pnorm_sq * Tchr_sum := by
    rw [hSraw_def, hTcov_sum_def, hTchr_sum_def]
    rw [Finset.mul_sum, Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun k _ => ?_)
    rw [hPnorm_sq_def]
    exact h_twoTerm_per_k k
  have h_Pnorm_le_C_proj : Pnorm_sq ≤ C_proj ^ 2 := by
    rw [hPnorm_sq_def, hC_proj_def]
    have hP_nn : 0 ≤ ‖tensorChartComponentProjection (E := E) r s Idx Jdx‖ :=
      norm_nonneg _
    have hP_le : ‖tensorChartComponentProjection (E := E) r s Idx Jdx‖ ≤
        chartComponentProjectionUniformBound (E := E) r s :=
      tensorChartComponentProjection_norm_le_uniform (E := E) r s Idx Jdx
    have h := mul_self_le_mul_self hP_nn hP_le
    have h_lhs : ‖tensorChartComponentProjection (E := E) r s Idx Jdx‖ *
        ‖tensorChartComponentProjection (E := E) r s Idx Jdx‖ =
        ‖tensorChartComponentProjection (E := E) r s Idx Jdx‖ ^ 2 := by rw [sq]
    have h_rhs : chartComponentProjectionUniformBound (E := E) r s *
        chartComponentProjectionUniformBound (E := E) r s =
        chartComponentProjectionUniformBound (E := E) r s ^ 2 := by rw [sq]
    linarith
  have h_Sraw_le' :
      Sraw ≤ 2 * C_proj ^ 2 * Tcov_sum + 2 * C_proj ^ 2 * Tchr_sum := by
    refine h_Sraw_le.trans ?_
    have h_2P_le : 2 * Pnorm_sq ≤ 2 * C_proj ^ 2 :=
      mul_le_mul_of_nonneg_left h_Pnorm_le_C_proj (by norm_num)
    have h1 : 2 * Pnorm_sq * Tcov_sum ≤ 2 * C_proj ^ 2 * Tcov_sum :=
      mul_le_mul_of_nonneg_right h_2P_le hTcov_sum_nn
    have h2 : 2 * Pnorm_sq * Tchr_sum ≤ 2 * C_proj ^ 2 * Tchr_sum :=
      mul_le_mul_of_nonneg_right h_2P_le hTchr_sum_nn
    linarith
  have h_sum_sq_final :
      ∑ k : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) k (scalarOnE (I := I) α
          (tensorChartComponentScalar (I := I) (M := M)
            g r s S α Idx Jdx)) z) ^ 2 ≤
      2 * raw_z ^ 2 * M_dρ +
        (4 * C_proj ^ 2 * Tcov_sum + 4 * C_proj ^ 2 * Tchr_sum) := by
    refine h_sum_sq_le'.trans ?_
    have h_2Sraw_le : 2 * Sraw ≤
        4 * C_proj ^ 2 * Tcov_sum + 4 * C_proj ^ 2 * Tchr_sum := by
      have := mul_le_mul_of_nonneg_left h_Sraw_le' (by norm_num : (0 : ℝ) ≤ 2)
      linarith
    linarith
  have h_l1Sum_nn : 0 ≤ chartInvGramMatrix_l1Sum (I := I) (M := M) g α b := by
    unfold chartInvGramMatrix_l1Sum
    exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have h_sum_sq_nn : 0 ≤ ∑ k : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) k (scalarOnE (I := I) α
          (tensorChartComponentScalar (I := I) (M := M)
            g r s S α Idx Jdx)) z) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have h_step_combined :
      g.inner b
        (gradFun (I := I) g
          (tensorChartComponentScalar (I := I) (M := M) g r s S α Idx Jdx) b)
        (gradFun (I := I) g
          (tensorChartComponentScalar (I := I) (M := M) g r s S α Idx Jdx) b) ≤
      M_Ginv * (2 * raw_z ^ 2 * M_dρ +
        (4 * C_proj ^ 2 * Tcov_sum + 4 * C_proj ^ 2 * Tchr_sum)) := by
    refine h_step_grad3.trans ?_
    have h1 : chartInvGramMatrix_l1Sum (I := I) (M := M) g α b *
        ∑ k : Fin (Module.finrank ℝ E),
          (partialDeriv (E := E) k (scalarOnE (I := I) α
            (tensorChartComponentScalar (I := I) (M := M)
              g r s S α Idx Jdx)) z) ^ 2 ≤
        M_Ginv *
        ∑ k : Fin (Module.finrank ℝ E),
          (partialDeriv (E := E) k (scalarOnE (I := I) α
            (tensorChartComponentScalar (I := I) (M := M)
              g r s S α Idx Jdx)) z) ^ 2 :=
      mul_le_mul_of_nonneg_right h_l1Sum_le h_sum_sq_nn
    have h2 : M_Ginv *
        ∑ k : Fin (Module.finrank ℝ E),
          (partialDeriv (E := E) k (scalarOnE (I := I) α
            (tensorChartComponentScalar (I := I) (M := M)
              g r s S α Idx Jdx)) z) ^ 2 ≤
        M_Ginv * (2 * raw_z ^ 2 * M_dρ +
          (4 * C_proj ^ 2 * Tcov_sum + 4 * C_proj ^ 2 * Tchr_sum)) :=
      mul_le_mul_of_nonneg_left h_sum_sq_final hM_Ginv_nn
    linarith
  have h_rhs_arith : M_Ginv * (2 * raw_z ^ 2 * M_dρ +
        (4 * C_proj ^ 2 * Tcov_sum + 4 * C_proj ^ 2 * Tchr_sum)) =
      (2 * M_Ginv * M_dρ) * raw_z ^ 2 +
        (4 * M_Ginv * C_proj ^ 2) * Tcov_sum +
        (4 * M_Ginv * C_proj ^ 2) * Tchr_sum := by ring
  have h_step_rearranged :
      g.inner b
        (gradFun (I := I) g
          (tensorChartComponentScalar (I := I) (M := M) g r s S α Idx Jdx) b)
        (gradFun (I := I) g
          (tensorChartComponentScalar (I := I) (M := M) g r s S α Idx Jdx) b) ≤
      (2 * M_Ginv * M_dρ) * raw_z ^ 2 +
        (4 * M_Ginv * C_proj ^ 2) * Tcov_sum +
        (4 * M_Ginv * C_proj ^ 2) * Tchr_sum := by
    rw [← h_rhs_arith]; exact h_step_combined
  have h_coef1_term : (2 * M_Ginv * M_dρ) * raw_z ^ 2 ≤ C * raw_z ^ 2 :=
    mul_le_mul_of_nonneg_right h_coef1_le_C hraw_sq_nn
  have h_coef2_term : (4 * M_Ginv * C_proj ^ 2) * Tcov_sum ≤ C * Tcov_sum :=
    mul_le_mul_of_nonneg_right h_coef2_le_C hTcov_sum_nn
  have h_coef3_term : (4 * M_Ginv * C_proj ^ 2) * Tchr_sum ≤ C * Tchr_sum :=
    mul_le_mul_of_nonneg_right h_coef2_le_C hTchr_sum_nn
  have h_target_arith :
      C * (Tcov_sum + Tchr_sum + raw_z ^ 2) =
        C * Tcov_sum + C * Tchr_sum + C * raw_z ^ 2 := by ring
  calc g.inner b
        (gradFun (I := I) g
          (tensorChartComponentScalar (I := I) (M := M) g r s S α Idx Jdx) b)
        (gradFun (I := I) g
          (tensorChartComponentScalar (I := I) (M := M) g r s S α Idx Jdx) b)
      ≤ (2 * M_Ginv * M_dρ) * raw_z ^ 2 +
          (4 * M_Ginv * C_proj ^ 2) * Tcov_sum +
          (4 * M_Ginv * C_proj ^ 2) * Tchr_sum := h_step_rearranged
    _ ≤ C * raw_z ^ 2 + C * Tcov_sum + C * Tchr_sum := by
        linarith [h_coef1_term, h_coef2_term, h_coef3_term]
    _ = C * (Tcov_sum + Tchr_sum + raw_z ^ 2) := by rw [h_target_arith]; ring

end PointwiseGradientBound

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
