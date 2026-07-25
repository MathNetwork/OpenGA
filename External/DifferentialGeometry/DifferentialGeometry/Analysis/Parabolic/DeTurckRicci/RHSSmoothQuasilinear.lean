import DifferentialGeometry.Geometry.Flow.RicciFlow.DeTurckRHS
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.QuasilinearMetricShortTimeExistence
import DifferentialGeometry.Analysis.Parabolic.DeTurckRicci.RHSStrictParabolic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.Cartan.Formula
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnection
import DifferentialGeometry.Geometry.Connection.LeviCivita.Defs
import DifferentialGeometry.Geometry.Connection.TensorNabla.CotangentExtension
import DifferentialGeometry.Geometry.Flow.VectorFieldSmooth
import DifferentialGeometry.Geometry.Flow.LieDerivativeMetric
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.LocalFormula
import DifferentialGeometry.Geometry.Curvature.Riemann.Ricci
import DifferentialGeometry.Geometry.Curvature.Riemann.Defs
import Mathlib.Geometry.Manifold.ContMDiff.Basic

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry
open DifferentialGeometry.PDE
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

noncomputable def chartFrameVec (α : M) (i : Fin (Module.finrank ℝ E))
    (x : M) : TangentSpace I x :=
  (trivializationAt E (TangentSpace I) α).symmL ℝ x (chartModelBasis E i)

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem deturckvf_chart_smooth_in_g_jet
    (g g_bg : SmoothRiemannianMetric I M) (α : M)
    (k : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun x : M =>
        chartCoeff (I := I) α
          (deTurckVF (I := I) g g_bg
            : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) k x)
      (chartAt H α).source := by
  have h := chartCoeff_contMDiffOn (I := I) α
    (deTurckVF (I := I) g g_bg
      : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) k
  exact h

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem deturckvf_chart_component_smooth_in_g_input
    (g g_bg : SmoothRiemannianMetric I M) (α : M)
    (k : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun x : M =>
        chartCoeff (I := I) α
          (deTurckVF (I := I) g g_bg
            : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) k x)
      (chartAt H α).source :=
  chartCoeff_contMDiffOn (I := I) α
    (deTurckVF (I := I) g g_bg
      : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) k

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem liederivmetric_chart_smooth_in_g_w_jet [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    (W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (α : M) (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun x : M => chartLieDerivMetricMatrix (I := I) g W α i j x)
      (chartAt H α).source :=
  chartLieDerivMetricMatrix_contMDiffOn (I := I) g W α i j

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem liederivmetric_chart_component_smooth_in_g_w_input
    (g : SmoothRiemannianMetric I M)
    (W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (α : M) (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun x : M =>
        lieDerivMetric (I := I) g W x
          (chartFrameVec (I := I) α i x) (chartFrameVec (I := I) α j x))
      (chartAt H α).source := by
  classical
  intro x₀ hx₀
  have h_frame_on : ∀ k : Fin (Module.finrank ℝ E),
      ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
        (fun b : M => TotalSpace.mk' E b (chartFrameVec (I := I) α k b))
        (chartAt H α).source := fun k => by
    have h := chartAlphaFrame_section_contMDiffOn (I := I) α k
    exact h
  obtain ⟨S, hS_eq⟩ :=
    exists_contMDiffSection_eqOn_nhd
      (s := fun k : Fin (Module.finrank ℝ E) => fun b : M => chartFrameVec (I := I) α k b)
      (u := (chartAt H α).source) (p := x₀)
      h_frame_on ((chartAt H α).open_source) hx₀
  have hSk_smooth : ∀ k : Fin (Module.finrank ℝ E),
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun b : M => TotalSpace.mk' E b ((S k) b : TangentSpace I b)) :=
    fun k => (S k).contMDiff
  have hW_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E b (W b : TangentSpace I b)) := W.contMDiff
  have hW_smooth' : ContMDiffOn I (I.prod 𝓘(ℝ, E))
      ((∞ : WithTop ℕ∞) + 1)
      (fun b : M => TotalSpace.mk' E b (W b : TangentSpace I b)) Set.univ := by
    have : ContMDiff I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1)
        (fun b : M => TotalSpace.mk' E b (W b : TangentSpace I b)) := by simpa using hW_smooth
    exact this.contMDiffOn
  have h_LCWop : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
        b ((LeviCivita (I := I) g).toFun (fun b : M => W b) b)) Set.univ :=
    LeviCivita_section_contMDiffOn_univ (I := I) g hW_smooth'
  have h_LCWS : ∀ k : Fin (Module.finrank ℝ E),
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun b : M => TotalSpace.mk' E
          (E := fun x : M => TangentSpace I x) b
          ((LeviCivita (I := I) g).toFun (fun b : M => W b) b (S k b))) := by
    intro k b
    have hop_at : ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
        (fun b : M => TotalSpace.mk' (E →L[ℝ] E)
          (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
          b ((LeviCivita (I := I) g).toFun (fun b : M => W b) b)) b :=
      h_LCWop.contMDiffAt (Filter.univ_mem)
    have hSk_at : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
        (fun b : M => TotalSpace.mk' E b ((S k) b : TangentSpace I b)) b := hSk_smooth k b
    exact ContMDiffAt.clm_bundle_apply
      (E₁ := fun x : M => TangentSpace I x)
      (E₂ := fun x : M => TangentSpace I x)
      (b := fun b : M => b)
      (ϕ := fun b => (LeviCivita (I := I) g).toFun (fun b : M => W b) b)
      (v := fun b => S k b)
      hop_at hSk_at
  have h_inner :
      ∀ {X Y : Π b : M, TangentSpace I b},
        ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
          (fun b : M => TotalSpace.mk' E b (X b : TangentSpace I b)) →
        ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
          (fun b : M => TotalSpace.mk' E b (Y b : TangentSpace I b)) →
        ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun b : M => g.inner b (X b) (Y b)) := by
    intro X Y hX hY
    have hg : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
        (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
          b (g.inner b)) := g.contMDiff
    have hgX : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
        (fun b : M => TotalSpace.mk' (E →L[ℝ] ℝ)
          (E := fun x : M => TangentSpace I x →L[ℝ] ℝ) b (g.inner b (X b))) :=
      ContMDiff.clm_bundle_apply
        (E₁ := fun x : M => TangentSpace I x)
        (E₂ := fun x : M => TangentSpace I x →L[ℝ] ℝ)
        (b := fun b : M => b)
        (ϕ := fun b => g.inner b) (v := fun b => X b) hg hX
    exact cotangentCov_pairing_contMDiff hgX hY
  have h_summand1 : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun b : M => g.inner b
        ((LeviCivita (I := I) g).toFun (fun b : M => W b) b (S i b)) (S j b)) :=
    h_inner (h_LCWS i) (hSk_smooth j)
  have h_summand2 : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun b : M => g.inner b (S i b)
        ((LeviCivita (I := I) g).toFun (fun b : M => W b) b (S j b))) :=
    h_inner (hSk_smooth i) (h_LCWS j)
  have h_sum_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun b : M =>
        g.inner b ((LeviCivita (I := I) g).toFun (fun b : M => W b) b (S i b)) (S j b)
        + g.inner b (S i b)
            ((LeviCivita (I := I) g).toFun (fun b : M => W b) b (S j b))) :=
    h_summand1.add h_summand2
  have h_cartan_pair : ∀ b : M,
      lieDerivMetric (I := I) g W b (S i b) (S j b) =
        g.inner b ((LeviCivita (I := I) g).toFun (fun b : M => W b) b (S i b)) (S j b)
        + g.inner b (S i b)
            ((LeviCivita (I := I) g).toFun (fun b : M => W b) b (S j b)) := by
    intro b
    exact DifferentialGeometry.PDE.RicciFlow.Pullback.cartan_formula_for_lie_deriv_metric
      (I := I) g W b (S i b) (S j b)
  have h_pair_S_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun b : M => lieDerivMetric (I := I) g W b (S i b) (S j b)) := by
    have h_congr : (fun b : M => lieDerivMetric (I := I) g W b (S i b) (S j b)) =
        (fun b : M =>
          g.inner b ((LeviCivita (I := I) g).toFun (fun b : M => W b) b (S i b)) (S j b)
          + g.inner b (S i b)
              ((LeviCivita (I := I) g).toFun (fun b : M => W b) b (S j b))) :=
      funext h_cartan_pair
    rw [h_congr]; exact h_sum_smooth
  have h_pair_S_at : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun b : M => lieDerivMetric (I := I) g W b (S i b) (S j b)) x₀ := h_pair_S_smooth x₀
  have h_chart_at : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun x : M => lieDerivMetric (I := I) g W x
        (chartFrameVec (I := I) α i x) (chartFrameVec (I := I) α j x)) x₀ := by
    refine h_pair_S_at.congr_of_eventuallyEq ?_
    filter_upwards [hS_eq] with b hb
    rw [hb i, hb j]
  exact h_chart_at.contMDiffWithinAt

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem ricciTensor_chartFrameComponent_contMDiffOn
    (g : SmoothRiemannianMetric I M)
    (α : M) (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun x : M =>
        ricciTensor (I := I) g x
          (chartFrameVec (I := I) α i x) (chartFrameVec (I := I) α j x))
      (chartAt H α).source := by
  classical
  intro x₀ hx₀
  have h_frame_on : ∀ k : Fin (Module.finrank ℝ E),
      ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
        (fun b : M => TotalSpace.mk' E b (chartFrameVec (I := I) α k b))
        (chartAt H α).source := fun k => by
    have h := chartAlphaFrame_section_contMDiffOn (I := I) α k
    exact h
  obtain ⟨S, hS_eq⟩ :=
    exists_contMDiffSection_eqOn_nhd
      (s := fun k : Fin (Module.finrank ℝ E) => fun b : M => chartFrameVec (I := I) α k b)
      (u := (chartAt H α).source) (p := x₀)
      h_frame_on ((chartAt H α).open_source) hx₀
  have hSk_smooth : ∀ k : Fin (Module.finrank ℝ E),
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (fun b : M => TotalSpace.mk' E b ((S k) b : TangentSpace I b))
        := fun k => (S k).contMDiff
  have h_scalar :
      ContMDiff I 𝓘(ℝ, ℝ) ∞
        (fun b : M => ricciTensor (I := I) g b ((S i) b) ((S j) b)) :=
    ricciTensor_pairing_contMDiff (I := I) g (hSk_smooth i) (hSk_smooth j)
  have h_scalar_at : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun b : M => ricciTensor (I := I) g b ((S i) b) ((S j) b)) x₀ := h_scalar x₀
  have h_chart_at : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun x : M => ricciTensor (I := I) g x
        (chartFrameVec (I := I) α i x) (chartFrameVec (I := I) α j x)) x₀ := by
    refine h_scalar_at.congr_of_eventuallyEq ?_
    filter_upwards [hS_eq] with b hb
    rw [hb i, hb j]
  exact h_chart_at.contMDiffWithinAt

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem combine_smoothness_of_summands
    (g_bg g : SmoothRiemannianMetric I M)
    (α : M) (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun x : M =>
        deTurckRicciRHS (I := I) g_bg g x
          (chartFrameVec (I := I) α i x) (chartFrameVec (I := I) α j x))
      (chartAt H α).source := by
  set W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    DifferentialGeometry.PDE.DeTurck.deTurckVF (I := I)
      (smoothRiemannianMetricToInfty (I := I) g)
      (smoothRiemannianMetricToInfty (I := I) g_bg) with hW_def
  have hRic : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun x : M => ricciTensor (I := I) g x
        (chartFrameVec (I := I) α i x) (chartFrameVec (I := I) α j x))
      (chartAt H α).source :=
    ricciTensor_chartFrameComponent_contMDiffOn (I := I) g α i j
  have hLie : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun x : M => lieDerivMetric (I := I) g W x
        (chartFrameVec (I := I) α i x) (chartFrameVec (I := I) α j x))
      (chartAt H α).source :=
    liederivmetric_chart_component_smooth_in_g_w_input (I := I) g W α i j
  have h_unfold : ∀ x : M,
      deTurckRicciRHS (I := I) g_bg g x
          (chartFrameVec (I := I) α i x) (chartFrameVec (I := I) α j x) =
        (-2 : ℝ) * (ricciTensor (I := I) g x
          (chartFrameVec (I := I) α i x) (chartFrameVec (I := I) α j x))
          + lieDerivMetric (I := I) g W x
              (chartFrameVec (I := I) α i x) (chartFrameVec (I := I) α j x) := by
    intro x
    change ((-2 : ℝ) • ricciTensor (I := I)
            (smoothRiemannianMetricToInfty (I := I) g) x +
          lieDerivMetricClm (I := I) g W x)
        (chartFrameVec (I := I) α i x) (chartFrameVec (I := I) α j x) =
      (-2 : ℝ) * (ricciTensor (I := I) g x
          (chartFrameVec (I := I) α i x) (chartFrameVec (I := I) α j x))
        + lieDerivMetric (I := I) g W x
            (chartFrameVec (I := I) α i x) (chartFrameVec (I := I) α j x)
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul]
    rfl
  refine ContMDiffOn.congr ?_ (fun x _ => (h_unfold x).symm)
  exact ((contMDiffOn_const (c := (-2 : ℝ))).mul hRic).add hLie

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem linearity_in_second_derivatives
    (g_bg g : SmoothRiemannianMetric I M)
    (α : M) (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun x : M =>
        deTurckRicciRHS (I := I) g_bg g x
          (chartFrameVec (I := I) α i x) (chartFrameVec (I := I) α j x))
      (chartAt H α).source :=
  combine_smoothness_of_summands (I := I) g_bg g α i j

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem deTurckRicciRHS_isSmoothQuasilinear [I.Boundaryless]
    (g_bg : SmoothRiemannianMetric I M) :
    IsSmoothQuasilinearMetricRHS (I := I)
      (deTurckRicciRHS (I := I) g_bg) := by
  refine ⟨?_, ?_⟩
  · intro g α i j
    exact combine_smoothness_of_summands (I := I) g_bg g α i j
  · intro g
    exact deTurckRicciRHS_isStrictlyParabolic_at_self g g_bg

end DifferentialGeometry.PDE.RicciFlow
