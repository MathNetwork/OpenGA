import DifferentialGeometry.Geometry.Connection.ParallelTransport.ParallelTransport
import DifferentialGeometry.Geometry.Connection.ParallelTransport.AlongCurve
import DifferentialGeometry.Geometry.Curvature.Riemann.Defs
import DifferentialGeometry.Geometry.Connection.LeviCivita.Defs
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Defs
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciIdentity
import DifferentialGeometry.Geometry.Connection.ChartBridge.Riemann
import DifferentialGeometry.Geometry.Connection.ChartBridge.Ricci
import DifferentialGeometry.Geometry.Connection.ChartBridge.RiemannBasisBracket
import DifferentialGeometry.Analysis.Integration.Measure.ChartDensity
import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Symmetric


noncomputable section

open Set Function Filter Manifold Bundle
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Variation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.Geodesic

def IsSmoothVariation
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (f : ℝ → ℝ → M) : Prop :=
  ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I (8 : ℕ) (fun p : ℝ × ℝ => f p.1 p.2)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma partial_snd_apply_one (G : ℝ × ℝ → E) (u t : ℝ)
    (h : DifferentiableAt ℝ G (u, t)) :
    fderiv ℝ (fun v : ℝ => G (u, v)) t (1 : ℝ) = fderiv ℝ G (u, t) (0, 1) := by
  have hcomp : (fun v : ℝ => G (u, v)) = G ∘ (fun v : ℝ => (u, v)) := rfl
  have hincl : HasFDerivAt (fun v : ℝ => (u, v)) (ContinuousLinearMap.inr ℝ ℝ ℝ) t :=
    hasFDerivAt_prodMk_right u t
  have hG : HasFDerivAt G (fderiv ℝ G (u, t)) (u, t) := h.hasFDerivAt
  have hch := hG.comp t hincl
  rw [hcomp, hch.fderiv]
  simp [ContinuousLinearMap.inr]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma partial_fst_apply_one (G : ℝ × ℝ → E) (s v : ℝ)
    (h : DifferentiableAt ℝ G (s, v)) :
    fderiv ℝ (fun u : ℝ => G (u, v)) s (1 : ℝ) = fderiv ℝ G (s, v) (1, 0) := by
  have hcomp : (fun u : ℝ => G (u, v)) = G ∘ (fun u : ℝ => (u, v)) := rfl
  have hincl : HasFDerivAt (fun u : ℝ => (u, v)) (ContinuousLinearMap.inl ℝ ℝ ℝ) s :=
    hasFDerivAt_prodMk_left s v
  have hG : HasFDerivAt G (fderiv ℝ G (s, v)) (s, v) := h.hasFDerivAt
  have hch := hG.comp s hincl
  rw [hcomp, hch.fderiv]
  simp [ContinuousLinearMap.inl]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma deriv_jointFderiv_snd (G : ℝ × ℝ → E) (s t : ℝ)
    (hG : ContDiffAt ℝ 2 G (s, t)) :
    deriv (fun u : ℝ => fderiv ℝ G (u, t) (0, 1)) s
      = fderiv ℝ (fderiv ℝ G) (s, t) (1, 0) (0, 1) := by
  have hg : ContDiffAt ℝ 1 (fderiv ℝ G) (s, t) := hG.fderiv_right (le_refl _)
  have hgdiff : DifferentiableAt ℝ (fderiv ℝ G) (s, t) := hg.differentiableAt one_ne_zero
  have hincl : HasFDerivAt (fun u : ℝ => (u, t)) (ContinuousLinearMap.inl ℝ ℝ ℝ) s :=
    hasFDerivAt_prodMk_left s t
  have hcomp : HasFDerivAt (fun u : ℝ => fderiv ℝ G (u, t))
      ((fderiv ℝ (fderiv ℝ G) (s, t)).comp (ContinuousLinearMap.inl ℝ ℝ ℝ)) s :=
    hgdiff.hasFDerivAt.comp s hincl
  set L : (ℝ × ℝ →L[ℝ] E) →L[ℝ] E := ContinuousLinearMap.apply ℝ E ((0, 1) : ℝ × ℝ) with hL
  have hcomp2 : HasFDerivAt (fun u : ℝ => L (fderiv ℝ G (u, t)))
      (L.comp ((fderiv ℝ (fderiv ℝ G) (s, t)).comp (ContinuousLinearMap.inl ℝ ℝ ℝ))) s :=
    L.hasFDerivAt.comp s hcomp
  have hderiv : HasDerivAt (fun u : ℝ => L (fderiv ℝ G (u, t)))
      ((L.comp ((fderiv ℝ (fderiv ℝ G) (s, t)).comp (ContinuousLinearMap.inl ℝ ℝ ℝ))) 1) s :=
    hcomp2.hasDerivAt
  have heq : (fun u : ℝ => L (fderiv ℝ G (u, t))) =
      (fun u : ℝ => fderiv ℝ G (u, t) (0, 1)) := rfl
  rw [heq] at hderiv
  rw [hderiv.deriv]
  simp [hL, ContinuousLinearMap.inl]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma deriv_jointFderiv_fst (G : ℝ × ℝ → E) (s t : ℝ)
    (hG : ContDiffAt ℝ 2 G (s, t)) :
    deriv (fun v : ℝ => fderiv ℝ G (s, v) (1, 0)) t
      = fderiv ℝ (fderiv ℝ G) (s, t) (0, 1) (1, 0) := by
  have hg : ContDiffAt ℝ 1 (fderiv ℝ G) (s, t) := hG.fderiv_right (le_refl _)
  have hgdiff : DifferentiableAt ℝ (fderiv ℝ G) (s, t) := hg.differentiableAt one_ne_zero
  have hincl : HasFDerivAt (fun v : ℝ => (s, v)) (ContinuousLinearMap.inr ℝ ℝ ℝ) t :=
    hasFDerivAt_prodMk_right s t
  have hcomp : HasFDerivAt (fun v : ℝ => fderiv ℝ G (s, v))
      ((fderiv ℝ (fderiv ℝ G) (s, t)).comp (ContinuousLinearMap.inr ℝ ℝ ℝ)) t :=
    hgdiff.hasFDerivAt.comp t hincl
  set L : (ℝ × ℝ →L[ℝ] E) →L[ℝ] E := ContinuousLinearMap.apply ℝ E ((1, 0) : ℝ × ℝ) with hL
  have hcomp2 : HasFDerivAt (fun v : ℝ => L (fderiv ℝ G (s, v)))
      (L.comp ((fderiv ℝ (fderiv ℝ G) (s, t)).comp (ContinuousLinearMap.inr ℝ ℝ ℝ))) t :=
    L.hasFDerivAt.comp t hcomp
  have hderiv : HasDerivAt (fun v : ℝ => L (fderiv ℝ G (s, v)))
      ((L.comp ((fderiv ℝ (fderiv ℝ G) (s, t)).comp (ContinuousLinearMap.inr ℝ ℝ ℝ))) 1) t :=
    hcomp2.hasDerivAt
  have heq : (fun v : ℝ => L (fderiv ℝ G (s, v))) =
      (fun v : ℝ => fderiv ℝ G (s, v) (1, 0)) := rfl
  rw [heq] at hderiv
  rw [hderiv.deriv]
  simp [hL, ContinuousLinearMap.inr]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma eventually_diff_along_fst (G : ℝ × ℝ → E) (s t : ℝ)
    (hG : ContDiffAt ℝ 2 G (s, t)) :
    ∀ᶠ u in nhds s, DifferentiableAt ℝ G (u, t) := by
  have hC1 : ContDiffAt ℝ 1 G (s, t) := hG.of_le one_le_two
  have hdiffG : ∀ᶠ p in nhds (s, t), DifferentiableAt ℝ G p :=
    (hC1.eventually (by norm_num)).mono (fun p hp => hp.differentiableAt one_ne_zero)
  have hcont : Continuous (fun u : ℝ => (u, t)) := by continuity
  have h2 : Filter.Tendsto (fun u : ℝ => (u, t)) (nhds s) (nhds (s, t)) := by
    simpa using hcont.continuousAt (x := s)
  exact h2.eventually hdiffG

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma eventually_diff_along_snd (G : ℝ × ℝ → E) (s t : ℝ)
    (hG : ContDiffAt ℝ 2 G (s, t)) :
    ∀ᶠ v in nhds t, DifferentiableAt ℝ G (s, v) := by
  have hC1 : ContDiffAt ℝ 1 G (s, t) := hG.of_le one_le_two
  have hdiffG : ∀ᶠ p in nhds (s, t), DifferentiableAt ℝ G p :=
    (hC1.eventually (by norm_num)).mono (fun p hp => hp.differentiableAt one_ne_zero)
  have hcont : Continuous (fun v : ℝ => (s, v)) := by continuity
  have h2 : Filter.Tendsto (fun v : ℝ => (s, v)) (nhds t) (nhds (s, t)) := by
    simpa using hcont.continuousAt (x := t)
  exact h2.eventually hdiffG

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma deriv_partialFderiv_snd (F : ℝ → ℝ → E) (s t : ℝ)
    (hF : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => F p.1 p.2) (s, t)) :
    deriv (fun u : ℝ => fderiv ℝ (fun v : ℝ => F u v) t (1 : ℝ)) s
      = fderiv ℝ (fderiv ℝ (fun p : ℝ × ℝ => F p.1 p.2)) (s, t) (1, 0) (0, 1) := by
  set G : ℝ × ℝ → E := fun p : ℝ × ℝ => F p.1 p.2 with hG_def
  have hev : (fun u : ℝ => fderiv ℝ (fun v : ℝ => F u v) t (1 : ℝ))
      =ᶠ[nhds s] (fun u : ℝ => fderiv ℝ G (u, t) (0, 1)) := by
    filter_upwards [eventually_diff_along_fst G s t hF] with u hu
    have hFv : (fun v : ℝ => F u v) = (fun v : ℝ => G (u, v)) := rfl
    rw [hFv]; exact partial_snd_apply_one G u t hu
  rw [hev.deriv_eq]
  exact deriv_jointFderiv_snd G s t hF

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma deriv_partialFderiv_fst (F : ℝ → ℝ → E) (s t : ℝ)
    (hF : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => F p.1 p.2) (s, t)) :
    deriv (fun v : ℝ => fderiv ℝ (fun u : ℝ => F u v) s (1 : ℝ)) t
      = fderiv ℝ (fderiv ℝ (fun p : ℝ × ℝ => F p.1 p.2)) (s, t) (0, 1) (1, 0) := by
  set G : ℝ × ℝ → E := fun p : ℝ × ℝ => F p.1 p.2 with hG_def
  have hev : (fun v : ℝ => fderiv ℝ (fun u : ℝ => F u v) s (1 : ℝ))
      =ᶠ[nhds t] (fun v : ℝ => fderiv ℝ G (s, v) (1, 0)) := by
    filter_upwards [eventually_diff_along_snd G s t hF] with v hv
    have hFu : (fun u : ℝ => F u v) = (fun u : ℝ => G (u, v)) := rfl
    rw [hFu]; exact partial_fst_apply_one G s v hv
  rw [hev.deriv_eq]
  exact deriv_jointFderiv_fst G s t hF

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma mixed_partialFderiv_comm (F : ℝ → ℝ → E) (s t : ℝ)
    (hF : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => F p.1 p.2) (s, t)) :
    deriv (fun u : ℝ => fderiv ℝ (fun v : ℝ => F u v) t (1 : ℝ)) s
      = deriv (fun v : ℝ => fderiv ℝ (fun u : ℝ => F u v) s (1 : ℝ)) t := by
  rw [deriv_partialFderiv_snd F s t hF, deriv_partialFderiv_fst F s t hF]
  have hsymm : IsSymmSndFDerivAt ℝ (fun p : ℝ × ℝ => F p.1 p.2) (s, t) := by
    refine ContDiffAt.isSymmSndFDerivAt hF ?_
    rw [minSmoothness_of_isRCLikeNormedField]
  exact hsymm (1, 0) (0, 1)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma chartPulled_contDiffAt
    (f : ℝ → ℝ → M) (hf : IsSmoothVariation (I := I) f) (s t : ℝ) :
    ContDiffAt ℝ 2
      (fun p : ℝ × ℝ => extChartAt I (f s t) (f p.1 p.2)) (s, t) := by
  have hext : ContMDiffAt I 𝓘(ℝ, E) (8 : ℕ) (extChartAt I (f s t)) (f s t) :=
    (contMDiffAt_extChartAt (I := I) (x := f s t)).of_le (by exact_mod_cast le_top)
  have hcomp : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) (8 : ℕ)
      (fun p : ℝ × ℝ => extChartAt I (f s t) (f p.1 p.2)) (s, t) :=
    hext.comp (s, t) hf.contMDiffAt
  have key : ContDiffAt ℝ (8 : ℕ)
      (fun p : ℝ × ℝ => extChartAt I (f s t) (f p.1 p.2)) (s, t) := by
    rw [← contMDiffAt_iff_contDiffAt, modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact hcomp
  exact key.of_le (by exact_mod_cast (by norm_num : (2 : ℕ) ≤ 8))

omit [InnerProductSpace ℝ E] [T2Space M] [SigmaCompactSpace M] in

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem commute_ds_dt_fixed_chart_C2
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M)
    (s t : ℝ)
    (hF2 : ContDiffAt ℝ 2
      (fun p : ℝ × ℝ => extChartAt I (f s t) (f p.1 p.2)) (s, t)) :
    chartCovDerivAlong (I := I) g (f s t) (fun u : ℝ => f u t)
      (fun u : ℝ => fderiv ℝ (fun v : ℝ => extChartAt I (f s t) (f u v)) t (1 : ℝ)) s
    = chartCovDerivAlong (I := I) g (f s t) (fun v : ℝ => f s v)
      (fun v : ℝ => fderiv ℝ (fun u : ℝ => extChartAt I (f s t) (f u v)) s (1 : ℝ)) t := by
  classical
  set α : M := f s t with hα
  set F : ℝ → ℝ → E := fun u v => extChartAt I α (f u v) with hF_def
  rw [chartCovDerivAlong_def, chartCovDerivAlong_def]
  have hsec :
      deriv (fun u : ℝ => fderiv ℝ (fun v : ℝ => F u v) t (1 : ℝ)) s
        = deriv (fun v : ℝ => fderiv ℝ (fun u : ℝ => F u v) s (1 : ℝ)) t :=
    mixed_partialFderiv_comm F s t hF2
  have hcurveL : chartCurve (I := I) α (fun u : ℝ => f u t) s = F s t := rfl
  have hcurveR : chartCurve (I := I) α (fun v : ℝ => f s v) t = F s t := rfl
  have hXL : (fun u : ℝ => fderiv ℝ (fun v : ℝ => F u v) t (1 : ℝ)) s
      = fderiv ℝ (fun v : ℝ => F s v) t (1 : ℝ) := rfl
  have hXR : (fun v : ℝ => fderiv ℝ (fun u : ℝ => F u v) s (1 : ℝ)) t
      = fderiv ℝ (fun u : ℝ => F u t) s (1 : ℝ) := rfl
  have hvelL : deriv (chartCurve (I := I) α (fun u : ℝ => f u t)) s
      = fderiv ℝ (fun u : ℝ => F u t) s (1 : ℝ) := by
    rw [← fderiv_apply_one_eq_deriv]; rfl
  have hvelR : deriv (chartCurve (I := I) α (fun v : ℝ => f s v)) t
      = fderiv ℝ (fun v : ℝ => F s v) t (1 : ℝ) := by
    rw [← fderiv_apply_one_eq_deriv]; rfl
  have hChristoffel :
      chartChristoffelContraction (I := I) g α
          (deriv (chartCurve (I := I) α (fun u : ℝ => f u t)) s)
          ((fun u : ℝ => fderiv ℝ (fun v : ℝ => F u v) t (1 : ℝ)) s)
          (chartCurve (I := I) α (fun u : ℝ => f u t) s)
        = chartChristoffelContraction (I := I) g α
          (deriv (chartCurve (I := I) α (fun v : ℝ => f s v)) t)
          ((fun v : ℝ => fderiv ℝ (fun u : ℝ => F u v) s (1 : ℝ)) t)
          (chartCurve (I := I) α (fun v : ℝ => f s v) t) := by
    rw [hvelL, hcurveL, hXL, hvelR, hcurveR, hXR]
    exact chartChristoffelContraction_symm (I := I) g α
      (fderiv ℝ (fun u : ℝ => F u t) s (1 : ℝ))
      (fderiv ℝ (fun v : ℝ => F s v) t (1 : ℝ)) (F s t)
  rw [hsec, hChristoffel]

omit [InnerProductSpace ℝ E] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem commute_ds_dt_fixed_chart
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M)
    (hf : IsSmoothVariation (I := I) f)
    (s t : ℝ) :
    chartCovDerivAlong (I := I) g (f s t) (fun u : ℝ => f u t)
      (fun u : ℝ => fderiv ℝ (fun v : ℝ => extChartAt I (f s t) (f u v)) t (1 : ℝ)) s
    = chartCovDerivAlong (I := I) g (f s t) (fun v : ℝ => f s v)
      (fun v : ℝ => fderiv ℝ (fun u : ℝ => extChartAt I (f s t) (f u v)) s (1 : ℝ)) t :=
  commute_ds_dt_fixed_chart_C2 (I := I) g f s t
    (chartPulled_contDiffAt (I := I) f hf s t)

section FixedChartCurvatureHelpers
open DifferentialGeometry.Integral.DivergenceTheorem

def chartCoordCLM (i : Fin (Module.finrank ℝ E)) : E →L[ℝ] ℝ :=
  (chartModelBasis E).coord i |>.toContinuousLinearMap

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
@[simp] lemma chartCoordCLM_apply (i : Fin (Module.finrank ℝ E)) (v : E) :
    chartCoordCLM (E := E) i v = chartCoord (E := E) i v := rfl

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma hasDerivAt_chartCoord {P : ℝ → E} {P' : E} {s : ℝ} (hP : HasDerivAt P P' s)
    (i : Fin (Module.finrank ℝ E)) :
    HasDerivAt (fun u => chartCoord (E := E) i (P u)) (chartCoord (E := E) i P') s := by
  have := (chartCoordCLM (E := E) i).hasFDerivAt.comp_hasDerivAt s hP
  simpa using this

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma hasDerivAt_chartChristoffelContraction
    (g : SmoothRiemannianMetric I M) (α : M)
    {P Q R : ℝ → E} {P' Q' R' : E} {s : ℝ}
    (hP : HasDerivAt P P' s) (hQ : HasDerivAt Q Q' s) (hR : HasDerivAt R R' s)
    (hΓ : ∀ i j k : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ (chartChristoffel (I := I) g α i j k) (R s)) :
    HasDerivAt (fun u => chartChristoffelContraction (I := I) g α (P u) (Q u) (R u))
      (∑ k : Fin (Module.finrank ℝ E),
        (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          ((fderiv ℝ (chartChristoffel (I := I) g α i j k) (R s) R') *
              chartCoord (E := E) i (P s) * chartCoord (E := E) j (Q s)
            + chartChristoffel (I := I) g α i j k (R s) *
              chartCoord (E := E) i P' * chartCoord (E := E) j (Q s)
            + chartChristoffel (I := I) g α i j k (R s) *
              chartCoord (E := E) i (P s) * chartCoord (E := E) j Q')) •
          chartModelBasis E k) s := by
  classical
  have hfun : (fun u => chartChristoffelContraction (I := I) g α (P u) (Q u) (R u))
      = fun u => ∑ k : Fin (Module.finrank ℝ E),
          (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g α i j k (R u) *
              chartCoord (E := E) i (P u) * chartCoord (E := E) j (Q u)) •
            chartModelBasis E k := by
    funext u; rw [chartChristoffelContraction_def]
  rw [hfun]
  apply HasDerivAt.fun_sum
  intro k _
  apply HasDerivAt.smul_const
  apply HasDerivAt.fun_sum
  intro i _
  apply HasDerivAt.fun_sum
  intro j _
  have hΓc : HasDerivAt (fun u => chartChristoffel (I := I) g α i j k (R u))
      (fderiv ℝ (chartChristoffel (I := I) g α i j k) (R s) R') s := by
    have h := (hΓ i j k).hasFDerivAt.comp_hasDerivAt s hR
    exact h
  have hPi : HasDerivAt (fun u => chartCoord (E := E) i (P u)) (chartCoord (E := E) i P') s :=
    hasDerivAt_chartCoord hP i
  have hQj : HasDerivAt (fun u => chartCoord (E := E) j (Q u)) (chartCoord (E := E) j Q') s :=
    hasDerivAt_chartCoord hQ j
  have h12 := hΓc.mul hPi
  have h123 := h12.mul hQj
  have hval :
      (fderiv ℝ (chartChristoffel (I := I) g α i j k) (R s) R') *
            chartCoord (E := E) i (P s) * chartCoord (E := E) j (Q s)
          + chartChristoffel (I := I) g α i j k (R s) *
            chartCoord (E := E) i P' * chartCoord (E := E) j (Q s)
          + chartChristoffel (I := I) g α i j k (R s) *
            chartCoord (E := E) i (P s) * chartCoord (E := E) j Q'
        = ((fderiv ℝ (chartChristoffel (I := I) g α i j k) (R s) R') *
              chartCoord (E := E) i (P s)
            + chartChristoffel (I := I) g α i j k (R s) * chartCoord (E := E) i P') *
            chartCoord (E := E) j (Q s)
          + chartChristoffel (I := I) g α i j k (R s) * chartCoord (E := E) i (P s) *
            chartCoord (E := E) j Q' := by ring
  rw [hval]
  exact h123

end FixedChartCurvatureHelpers

namespace Aux2
open DifferentialGeometry.Geometry.Riemannian.Variation
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma partial_snd_apply_one (G : ℝ × ℝ → E) (u t : ℝ)
    (h : DifferentiableAt ℝ G (u, t)) :
    fderiv ℝ (fun v : ℝ => G (u, v)) t (1 : ℝ) = fderiv ℝ G (u, t) (0, 1) := by
  have hcomp : (fun v : ℝ => G (u, v)) = G ∘ (fun v : ℝ => (u, v)) := rfl
  have hincl : HasFDerivAt (fun v : ℝ => (u, v)) (ContinuousLinearMap.inr ℝ ℝ ℝ) t :=
    hasFDerivAt_prodMk_right u t
  have hG : HasFDerivAt G (fderiv ℝ G (u, t)) (u, t) := h.hasFDerivAt
  have hch := hG.comp t hincl
  rw [hcomp, hch.fderiv]; simp [ContinuousLinearMap.inr]

lemma partial_fst_apply_one (G : ℝ × ℝ → E) (s v : ℝ)
    (h : DifferentiableAt ℝ G (s, v)) :
    fderiv ℝ (fun u : ℝ => G (u, v)) s (1 : ℝ) = fderiv ℝ G (s, v) (1, 0) := by
  have hcomp : (fun u : ℝ => G (u, v)) = G ∘ (fun u : ℝ => (u, v)) := rfl
  have hincl : HasFDerivAt (fun u : ℝ => (u, v)) (ContinuousLinearMap.inl ℝ ℝ ℝ) s :=
    hasFDerivAt_prodMk_left s v
  have hG : HasFDerivAt G (fderiv ℝ G (s, v)) (s, v) := h.hasFDerivAt
  have hch := hG.comp s hincl
  rw [hcomp, hch.fderiv]; simp [ContinuousLinearMap.inl]

lemma hasDerivAt_partial_snd (F : ℝ → ℝ → E) (s t : ℝ)
    (hF : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => F p.1 p.2) (s, t)) :
    HasDerivAt (fun u : ℝ => fderiv ℝ (fun v : ℝ => F u v) t (1 : ℝ))
      (fderiv ℝ (fderiv ℝ (fun p : ℝ × ℝ => F p.1 p.2)) (s, t) (1, 0) (0, 1)) s := by
  set G : ℝ × ℝ → E := fun p : ℝ × ℝ => F p.1 p.2 with hG_def
  have hg : ContDiffAt ℝ 1 (fderiv ℝ G) (s, t) := hF.fderiv_right (le_refl _)
  have hgdiff : DifferentiableAt ℝ (fderiv ℝ G) (s, t) := hg.differentiableAt one_ne_zero
  have hincl : HasFDerivAt (fun u : ℝ => (u, t)) (ContinuousLinearMap.inl ℝ ℝ ℝ) s :=
    hasFDerivAt_prodMk_left s t
  have hcomp : HasFDerivAt (fun u : ℝ => fderiv ℝ G (u, t))
      ((fderiv ℝ (fderiv ℝ G) (s, t)).comp (ContinuousLinearMap.inl ℝ ℝ ℝ)) s :=
    hgdiff.hasFDerivAt.comp s hincl
  set L : (ℝ × ℝ →L[ℝ] E) →L[ℝ] E := ContinuousLinearMap.apply ℝ E ((0, 1) : ℝ × ℝ) with hL
  have hcomp2 : HasFDerivAt (fun u : ℝ => L (fderiv ℝ G (u, t)))
      (L.comp ((fderiv ℝ (fderiv ℝ G) (s, t)).comp (ContinuousLinearMap.inl ℝ ℝ ℝ))) s :=
    L.hasFDerivAt.comp s hcomp
  have hbase : HasDerivAt (fun u : ℝ => fderiv ℝ G (u, t) (0, 1))
      (fderiv ℝ (fderiv ℝ G) (s, t) (1, 0) (0, 1)) s := by
    have := hcomp2.hasDerivAt
    simpa [hL, ContinuousLinearMap.inl] using this
  have hC1 : ContDiffAt ℝ 1 G (s, t) := hF.of_le one_le_two
  have hdiffG : ∀ᶠ p in nhds (s, t), DifferentiableAt ℝ G p :=
    (hC1.eventually (by norm_num)).mono (fun p hp => hp.differentiableAt one_ne_zero)
  have hcont : Continuous (fun u : ℝ => (u, t)) := by continuity
  have htend : Filter.Tendsto (fun u : ℝ => (u, t)) (nhds s) (nhds (s, t)) := by
    simpa using hcont.continuousAt (x := s)
  have hev : (fun u : ℝ => fderiv ℝ (fun v : ℝ => F u v) t (1 : ℝ))
      =ᶠ[nhds s] (fun u : ℝ => fderiv ℝ G (u, t) (0, 1)) := by
    filter_upwards [htend.eventually hdiffG] with u hu
    have hFv : (fun v : ℝ => F u v) = (fun v : ℝ => G (u, v)) := rfl
    rw [hFv]; exact partial_snd_apply_one G u t hu
  exact hbase.congr_of_eventuallyEq hev

lemma hasDerivAt_slice_fst (F : ℝ → ℝ → E) (s t : ℝ)
    (hF : DifferentiableAt ℝ (fun p : ℝ × ℝ => F p.1 p.2) (s, t)) :
    HasDerivAt (fun u : ℝ => F u t)
      (fderiv ℝ (fun p : ℝ × ℝ => F p.1 p.2) (s, t) (1, 0)) s := by
  set G : ℝ × ℝ → E := fun p : ℝ × ℝ => F p.1 p.2 with hG_def
  have hincl : HasFDerivAt (fun u : ℝ => (u, t)) (ContinuousLinearMap.inl ℝ ℝ ℝ) s :=
    hasFDerivAt_prodMk_left s t
  have hGd : HasFDerivAt G (fderiv ℝ G (s, t)) (s, t) := hF.hasFDerivAt
  have hcomp : HasFDerivAt (G ∘ fun u : ℝ => (u, t))
      ((fderiv ℝ G (s, t)).comp (ContinuousLinearMap.inl ℝ ℝ ℝ)) s :=
    hGd.comp s hincl
  have := hcomp.hasDerivAt
  have hFeq : (fun u : ℝ => F u t) = (fun u : ℝ => G (u, t)) := rfl
  rw [hFeq]
  simpa [ContinuousLinearMap.inl] using this

lemma hasDerivAt_slice_snd (F : ℝ → ℝ → E) (s t : ℝ)
    (hF : DifferentiableAt ℝ (fun p : ℝ × ℝ => F p.1 p.2) (s, t)) :
    HasDerivAt (fun v : ℝ => F s v)
      (fderiv ℝ (fun p : ℝ × ℝ => F p.1 p.2) (s, t) (0, 1)) t := by
  set G : ℝ × ℝ → E := fun p : ℝ × ℝ => F p.1 p.2 with hG_def
  have hincl : HasFDerivAt (fun v : ℝ => (s, v)) (ContinuousLinearMap.inr ℝ ℝ ℝ) t :=
    hasFDerivAt_prodMk_right s t
  have hGd : HasFDerivAt G (fderiv ℝ G (s, t)) (s, t) := hF.hasFDerivAt
  have hcomp : HasFDerivAt (G ∘ fun v : ℝ => (s, v))
      ((fderiv ℝ G (s, t)).comp (ContinuousLinearMap.inr ℝ ℝ ℝ)) t :=
    hGd.comp t hincl
  have := hcomp.hasDerivAt
  have hFeq : (fun v : ℝ => F s v) = (fun v : ℝ => G (s, v)) := rfl
  rw [hFeq]
  simpa [ContinuousLinearMap.inr] using this

lemma hasDerivAt_partial_fst (F : ℝ → ℝ → E) (s t : ℝ)
    (hF : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => F p.1 p.2) (s, t)) :
    HasDerivAt (fun v : ℝ => fderiv ℝ (fun u : ℝ => F u v) s (1 : ℝ))
      (fderiv ℝ (fderiv ℝ (fun p : ℝ × ℝ => F p.1 p.2)) (s, t) (0, 1) (1, 0)) t := by
  set G : ℝ × ℝ → E := fun p : ℝ × ℝ => F p.1 p.2 with hG_def
  have hg : ContDiffAt ℝ 1 (fderiv ℝ G) (s, t) := hF.fderiv_right (le_refl _)
  have hgdiff : DifferentiableAt ℝ (fderiv ℝ G) (s, t) := hg.differentiableAt one_ne_zero
  have hincl : HasFDerivAt (fun v : ℝ => (s, v)) (ContinuousLinearMap.inr ℝ ℝ ℝ) t :=
    hasFDerivAt_prodMk_right s t
  have hcomp : HasFDerivAt (fun v : ℝ => fderiv ℝ G (s, v))
      ((fderiv ℝ (fderiv ℝ G) (s, t)).comp (ContinuousLinearMap.inr ℝ ℝ ℝ)) t :=
    hgdiff.hasFDerivAt.comp t hincl
  set L : (ℝ × ℝ →L[ℝ] E) →L[ℝ] E := ContinuousLinearMap.apply ℝ E ((1, 0) : ℝ × ℝ) with hL
  have hcomp2 : HasFDerivAt (fun v : ℝ => L (fderiv ℝ G (s, v)))
      (L.comp ((fderiv ℝ (fderiv ℝ G) (s, t)).comp (ContinuousLinearMap.inr ℝ ℝ ℝ))) t :=
    L.hasFDerivAt.comp t hcomp
  have hbase : HasDerivAt (fun v : ℝ => fderiv ℝ G (s, v) (1, 0))
      (fderiv ℝ (fderiv ℝ G) (s, t) (0, 1) (1, 0)) t := by
    have := hcomp2.hasDerivAt
    simpa [hL, ContinuousLinearMap.inr] using this
  have hC1 : ContDiffAt ℝ 1 G (s, t) := hF.of_le one_le_two
  have hdiffG : ∀ᶠ p in nhds (s, t), DifferentiableAt ℝ G p :=
    (hC1.eventually (by norm_num)).mono (fun p hp => hp.differentiableAt one_ne_zero)
  have hcont : Continuous (fun v : ℝ => (s, v)) := by continuity
  have htend : Filter.Tendsto (fun v : ℝ => (s, v)) (nhds t) (nhds (s, t)) := by
    simpa using hcont.continuousAt (x := t)
  have hev : (fun v : ℝ => fderiv ℝ (fun u : ℝ => F u v) s (1 : ℝ))
      =ᶠ[nhds t] (fun v : ℝ => fderiv ℝ G (s, v) (1, 0)) := by
    filter_upwards [htend.eventually hdiffG] with v hv
    have hFu : (fun u : ℝ => F u v) = (fun u : ℝ => G (u, v)) := rfl
    rw [hFu]
    have hcomp' : (fun u : ℝ => G (u, v)) = G ∘ (fun u : ℝ => (u, v)) := rfl
    have hincl' : HasFDerivAt (fun u : ℝ => (u, v)) (ContinuousLinearMap.inl ℝ ℝ ℝ) s :=
      hasFDerivAt_prodMk_left s v
    have hGd : HasFDerivAt G (fderiv ℝ G (s, v)) (s, v) := hv.hasFDerivAt
    have hch := hGd.comp s hincl'
    rw [hcomp', hch.fderiv]; simp [ContinuousLinearMap.inl]
  exact hbase.congr_of_eventuallyEq hev

end Aux2

namespace Aux3
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M] in
lemma chartChristoffel_differentiableAt_self
    (g : SmoothRiemannianMetric I M) (α : M) (i j k : Fin (Module.finrank ℝ E)) :
    DifferentiableAt ℝ (chartChristoffel (I := I) g α i j k) (extChartAt I α α) := by
  have hx_target : extChartAt I α α ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source (mem_extChartAt_source (I := I) α)
  have hx_int : extChartAt I α α ∈ interior (extChartAt I α).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α hx_target
  have hcd : ContDiffOn ℝ ∞ (chartChristoffel (I := I) g α i j k)
      (interior (extChartAt I α).target) :=
    chartChristoffel_contDiffOn_interior (I := I) g α i j k
  have hat : ContDiffAt ℝ ∞ (chartChristoffel (I := I) g α i j k) (extChartAt I α α) :=
    hcd.contDiffAt (isOpen_interior.mem_nhds hx_int)
  exact hat.differentiableAt (by decide)

end Aux3

namespace Aux4
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure
open Aux2
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma innerW_eq (g : SmoothRiemannianMetric I M) (α : M) (f : ℝ → ℝ → M) (Y : ℝ → ℝ → E) (t : ℝ) :
    (fun u => chartCovDerivAlong (I := I) g α (fun v : ℝ => f u v) (fun v : ℝ => Y u v) t)
      = fun u => fderiv ℝ (fun v : ℝ => Y u v) t (1 : ℝ)
          + chartChristoffelContraction (I := I) g α
              (fderiv ℝ (fun v : ℝ => extChartAt I α (f u v)) t (1 : ℝ))
              (Y u t)
              (extChartAt I α (f u t)) := by
  funext u
  rw [chartCovDerivAlong_def]
  rfl

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma hasDerivAt_innerW
    (g : SmoothRiemannianMetric I M) (α : M) (f : ℝ → ℝ → M) (Y : ℝ → ℝ → E) (s t : ℝ)
    (hF : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => extChartAt I α (f p.1 p.2)) (s, t))
    (hY : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Y p.1 p.2) (s, t))
    (hΓ : ∀ i j k : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ (chartChristoffel (I := I) g α i j k) (extChartAt I α (f s t))) :
    HasDerivAt
      (fun u => chartCovDerivAlong (I := I) g α (fun v : ℝ => f u v) (fun v : ℝ => Y u v) t)
      (fderiv ℝ (fderiv ℝ (fun p : ℝ × ℝ => Y p.1 p.2)) (s, t) (1, 0) (0, 1)
        + (∑ k : Fin (Module.finrank ℝ E),
            (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
              ((fderiv ℝ (chartChristoffel (I := I) g α i j k) (extChartAt I α (f s t))
                    (fderiv ℝ (fun p : ℝ × ℝ => extChartAt I α (f p.1 p.2)) (s, t) (1, 0))) *
                  chartCoord (E := E) i (fderiv ℝ (fun v : ℝ => extChartAt I α (f s v)) t (1 : ℝ))
                  * chartCoord (E := E) j (Y s t)
                + chartChristoffel (I := I) g α i j k (extChartAt I α (f s t)) *
                  chartCoord (E := E) i
                    (fderiv ℝ (fderiv ℝ (fun p : ℝ × ℝ => extChartAt I α (f p.1 p.2))) (s, t) (1, 0) (0, 1))
                  * chartCoord (E := E) j (Y s t)
                + chartChristoffel (I := I) g α i j k (extChartAt I α (f s t)) *
                  chartCoord (E := E) i (fderiv ℝ (fun v : ℝ => extChartAt I α (f s v)) t (1 : ℝ))
                  * chartCoord (E := E) j (fderiv ℝ (fun p : ℝ × ℝ => Y p.1 p.2) (s, t) (1, 0)))) •
              chartModelBasis E k)) s := by
  rw [innerW_eq]
  have hterm1 : HasDerivAt (fun u => fderiv ℝ (fun v : ℝ => Y u v) t (1 : ℝ))
      (fderiv ℝ (fderiv ℝ (fun p : ℝ × ℝ => Y p.1 p.2)) (s, t) (1, 0) (0, 1)) s :=
    hasDerivAt_partial_snd Y s t hY
  have hP : HasDerivAt (fun u => fderiv ℝ (fun v : ℝ => extChartAt I α (f u v)) t (1 : ℝ))
      (fderiv ℝ (fderiv ℝ (fun p : ℝ × ℝ => extChartAt I α (f p.1 p.2))) (s, t) (1, 0) (0, 1)) s :=
    hasDerivAt_partial_snd (fun u v => extChartAt I α (f u v)) s t hF
  have hQ : HasDerivAt (fun u => Y u t)
      (fderiv ℝ (fun p : ℝ × ℝ => Y p.1 p.2) (s, t) (1, 0)) s :=
    hasDerivAt_slice_fst Y s t (hY.differentiableAt two_ne_zero)
  have hR : HasDerivAt (fun u => extChartAt I α (f u t))
      (fderiv ℝ (fun p : ℝ × ℝ => extChartAt I α (f p.1 p.2)) (s, t) (1, 0)) s :=
    hasDerivAt_slice_fst (fun u v => extChartAt I α (f u v)) s t (hF.differentiableAt two_ne_zero)
  have hRs : (fun u => extChartAt I α (f u t)) s = extChartAt I α (f s t) := rfl
  have hΓ' : ∀ i j k : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ (chartChristoffel (I := I) g α i j k) ((fun u => extChartAt I α (f u t)) s) := hΓ
  have hterm2 := hasDerivAt_chartChristoffelContraction (I := I) g α hP hQ hR hΓ'
  exact hterm1.add hterm2

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma nabla_s_nabla_t_eq
    (g : SmoothRiemannianMetric I M) (α : M) (f : ℝ → ℝ → M) (Y : ℝ → ℝ → E) (s t : ℝ) :
    chartCovDerivAlong (I := I) g α (fun u : ℝ => f u t)
        (fun u => chartCovDerivAlong (I := I) g α (fun v : ℝ => f u v) (fun v : ℝ => Y u v) t) s
      = deriv (fun u => chartCovDerivAlong (I := I) g α (fun v : ℝ => f u v)
              (fun v : ℝ => Y u v) t) s
        + chartChristoffelContraction (I := I) g α
            (fderiv ℝ (fun u : ℝ => extChartAt I α (f u t)) s (1 : ℝ))
            (chartCovDerivAlong (I := I) g α (fun v : ℝ => f s v) (fun v : ℝ => Y s v) t)
            (extChartAt I α (f s t)) := by
  rw [chartCovDerivAlong_def]
  rfl

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma hasDerivAt_innerW_snd
    (g : SmoothRiemannianMetric I M) (α : M) (f : ℝ → ℝ → M) (Y : ℝ → ℝ → E) (s t : ℝ)
    (hF : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => extChartAt I α (f p.1 p.2)) (s, t))
    (hY : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Y p.1 p.2) (s, t))
    (hΓ : ∀ i j k : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ (chartChristoffel (I := I) g α i j k) (extChartAt I α (f s t))) :
    HasDerivAt
      (fun v => chartCovDerivAlong (I := I) g α (fun u : ℝ => f u v) (fun u : ℝ => Y u v) s)
      (fderiv ℝ (fderiv ℝ (fun p : ℝ × ℝ => Y p.1 p.2)) (s, t) (0, 1) (1, 0)
        + (∑ k : Fin (Module.finrank ℝ E),
            (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
              ((fderiv ℝ (chartChristoffel (I := I) g α i j k) (extChartAt I α (f s t))
                    (fderiv ℝ (fun p : ℝ × ℝ => extChartAt I α (f p.1 p.2)) (s, t) (0, 1))) *
                  chartCoord (E := E) i (fderiv ℝ (fun u : ℝ => extChartAt I α (f u t)) s (1 : ℝ))
                  * chartCoord (E := E) j (Y s t)
                + chartChristoffel (I := I) g α i j k (extChartAt I α (f s t)) *
                  chartCoord (E := E) i
                    (fderiv ℝ (fderiv ℝ (fun p : ℝ × ℝ => extChartAt I α (f p.1 p.2))) (s, t) (0, 1) (1, 0))
                  * chartCoord (E := E) j (Y s t)
                + chartChristoffel (I := I) g α i j k (extChartAt I α (f s t)) *
                  chartCoord (E := E) i (fderiv ℝ (fun u : ℝ => extChartAt I α (f u t)) s (1 : ℝ))
                  * chartCoord (E := E) j (fderiv ℝ (fun p : ℝ × ℝ => Y p.1 p.2) (s, t) (0, 1)))) •
              chartModelBasis E k)) t := by
  have hinnerW_eq : (fun v => chartCovDerivAlong (I := I) g α (fun u : ℝ => f u v)
        (fun u : ℝ => Y u v) s)
      = fun v => fderiv ℝ (fun u : ℝ => Y u v) s (1 : ℝ)
          + chartChristoffelContraction (I := I) g α
              (fderiv ℝ (fun u : ℝ => extChartAt I α (f u v)) s (1 : ℝ))
              (Y s v)
              (extChartAt I α (f s v)) := by
    funext v; rw [chartCovDerivAlong_def]; rfl
  rw [hinnerW_eq]
  have hterm1 : HasDerivAt (fun v => fderiv ℝ (fun u : ℝ => Y u v) s (1 : ℝ))
      (fderiv ℝ (fderiv ℝ (fun p : ℝ × ℝ => Y p.1 p.2)) (s, t) (0, 1) (1, 0)) t :=
    Aux2.hasDerivAt_partial_fst Y s t hY
  have hP : HasDerivAt (fun v => fderiv ℝ (fun u : ℝ => extChartAt I α (f u v)) s (1 : ℝ))
      (fderiv ℝ (fderiv ℝ (fun p : ℝ × ℝ => extChartAt I α (f p.1 p.2))) (s, t) (0, 1) (1, 0)) t :=
    Aux2.hasDerivAt_partial_fst (fun u v => extChartAt I α (f u v)) s t hF
  have hQ : HasDerivAt (fun v => Y s v)
      (fderiv ℝ (fun p : ℝ × ℝ => Y p.1 p.2) (s, t) (0, 1)) t :=
    Aux2.hasDerivAt_slice_snd Y s t (hY.differentiableAt two_ne_zero)
  have hR : HasDerivAt (fun v => extChartAt I α (f s v))
      (fderiv ℝ (fun p : ℝ × ℝ => extChartAt I α (f p.1 p.2)) (s, t) (0, 1)) t :=
    Aux2.hasDerivAt_slice_snd (fun u v => extChartAt I α (f u v)) s t (hF.differentiableAt two_ne_zero)
  have hΓ' : ∀ i j k : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ (chartChristoffel (I := I) g α i j k) ((fun v => extChartAt I α (f s v)) t) := hΓ
  have hterm2 := hasDerivAt_chartChristoffelContraction (I := I) g α hP hQ hR hΓ'
  exact hterm1.add hterm2

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma nabla_t_nabla_s_eq
    (g : SmoothRiemannianMetric I M) (α : M) (f : ℝ → ℝ → M) (Y : ℝ → ℝ → E) (s t : ℝ) :
    chartCovDerivAlong (I := I) g α (fun v : ℝ => f s v)
        (fun v => chartCovDerivAlong (I := I) g α (fun u : ℝ => f u v) (fun u : ℝ => Y u v) s) t
      = deriv (fun v => chartCovDerivAlong (I := I) g α (fun u : ℝ => f u v)
              (fun u : ℝ => Y u v) s) t
        + chartChristoffelContraction (I := I) g α
            (fderiv ℝ (fun v : ℝ => extChartAt I α (f s v)) t (1 : ℝ))
            (chartCovDerivAlong (I := I) g α (fun u : ℝ => f u t) (fun u : ℝ => Y u t) s)
            (extChartAt I α (f s t)) := by
  rw [chartCovDerivAlong_def]; rfl

end Aux4

namespace Aux5
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma fderiv_eq_sum_partialDeriv (u : E → ℝ) (y v : E) :
    fderiv ℝ u y v =
      ∑ k : Fin (Module.finrank ℝ E),
        chartCoord (E := E) k v * partialDeriv (E := E) k u y := by
  classical
  have hv : v = ∑ k : Fin (Module.finrank ℝ E),
      chartCoord (E := E) k v • (chartModelBasis E) k := by
    conv_lhs => rw [← (chartModelBasis E).sum_repr v]
    rfl
  conv_lhs => rw [hv]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [map_smul, smul_eq_mul]
  rfl

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma chartCoord_basis (b s : Fin (Module.finrank ℝ E)) :
    chartCoord (E := E) s (chartModelBasis E b) = if b = s then 1 else 0 := by
  rw [chartCoord]; exact (chartModelBasis E).repr_self_apply b s

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma chartCoord_sum_smul_basis (c : Fin (Module.finrank ℝ E) → ℝ)
    (s : Fin (Module.finrank ℝ E)) :
    chartCoord (E := E) s (∑ m, c m • chartModelBasis E m) = c s := by
  classical
  rw [← chartCoordCLM_apply, map_sum]
  rw [Finset.sum_eq_single s]
  · rw [map_smul, chartCoordCLM_apply, chartCoord_basis, if_pos rfl, smul_eq_mul, mul_one]
  · intro b _ hb
    rw [map_smul, chartCoordCLM_apply, chartCoord_basis, if_neg hb, smul_eq_mul, mul_zero]
  · intro h; exact absurd (Finset.mem_univ s) h

end Aux5

namespace Aux6
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open Aux5
open scoped Manifold ContDiff Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M]

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M] in
lemma chartCoord_chartChristoffelContraction
    (g : SmoothRiemannianMetric I M) (x : M) (v w y : E) (l : Fin (Module.finrank ℝ E)) :
    chartCoord (E := E) l (chartChristoffelContraction (I := I) g x v w y)
      = ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g x i j l y *
            chartCoord (E := E) i v * chartCoord (E := E) j w := by
  classical
  rw [chartChristoffelContraction_def]
  rw [Aux5.chartCoord_sum_smul_basis (E := E)
      (fun l => ∑ i, ∑ j, chartChristoffel (I := I) g x i j l y *
        chartCoord (E := E) i v * chartCoord (E := E) j w) l]

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M] in
lemma partialDeriv_chartChristoffel_symm
    (g : SmoothRiemannianMetric I M) (x : M) (i j l d : Fin (Module.finrank ℝ E)) (y : E) :
    partialDeriv (E := E) d (chartChristoffel (I := I) g x i j l) y
      = partialDeriv (E := E) d (chartChristoffel (I := I) g x j i l) y := by
  have hfun : chartChristoffel (I := I) g x i j l = chartChristoffel (I := I) g x j i l := by
    funext y'; exact chartChristoffel_symm (I := I) g x i j l y'
  rw [hfun]

omit [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M] in
omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma curvPart_eq_chartRiemannCLM
    (g : SmoothRiemannianMetric I M) (x : M) (D₁ D₂ Yv : E) :
    (∑ k : Fin (Module.finrank ℝ E),
        (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          ((fderiv ℝ (chartChristoffel (I := I) g x i j k) (extChartAt I x x) D₁) *
              chartCoord (E := E) i D₂ * chartCoord (E := E) j Yv
            - (fderiv ℝ (chartChristoffel (I := I) g x i j k) (extChartAt I x x) D₂) *
              chartCoord (E := E) i D₁ * chartCoord (E := E) j Yv)) •
          chartModelBasis E k)
      + (chartChristoffelContraction (I := I) g x D₁
            (chartChristoffelContraction (I := I) g x D₂ Yv (extChartAt I x x))
            (extChartAt I x x)
          - chartChristoffelContraction (I := I) g x D₂
            (chartChristoffelContraction (I := I) g x D₁ Yv (extChartAt I x x))
            (extChartAt I x x))
      = chartRiemannCLM (I := I) g x D₁ D₂ Yv := by
  classical
  set y₀ : E := extChartAt I x x with hy₀
  set d₁ : Fin (Module.finrank ℝ E) → ℝ := fun i => chartCoord (E := E) i D₁ with hd₁
  set d₂ : Fin (Module.finrank ℝ E) → ℝ := fun i => chartCoord (E := E) i D₂ with hd₂
  set yc : Fin (Module.finrank ℝ E) → ℝ := fun i => chartCoord (E := E) i Yv with hyc
  have hfd₁ : ∀ i j k, fderiv ℝ (chartChristoffel (I := I) g x i j k) y₀ D₁
      = ∑ d, d₁ d * partialDeriv (E := E) d (chartChristoffel (I := I) g x i j k) y₀ :=
    fun i j k => Aux5.fderiv_eq_sum_partialDeriv _ y₀ D₁
  have hfd₂ : ∀ i j k, fderiv ℝ (chartChristoffel (I := I) g x i j k) y₀ D₂
      = ∑ d, d₂ d * partialDeriv (E := E) d (chartChristoffel (I := I) g x i j k) y₀ :=
    fun i j k => Aux5.fderiv_eq_sum_partialDeriv _ y₀ D₂
  have hAA₁ : chartChristoffelContraction (I := I) g x D₁
        (chartChristoffelContraction (I := I) g x D₂ Yv y₀) y₀
      = ∑ l, (∑ i, ∑ j, chartChristoffel (I := I) g x i j l y₀ * d₁ i *
          (∑ p, ∑ q, chartChristoffel (I := I) g x p q j y₀ * d₂ p * yc q)) •
          chartModelBasis E l := by
    rw [chartChristoffelContraction_def]
    refine Finset.sum_congr rfl fun l _ => ?_
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show chartCoord (E := E) j
          (chartChristoffelContraction (I := I) g x D₂ Yv y₀)
        = ∑ p, ∑ q, chartChristoffel (I := I) g x p q j y₀ * d₂ p * yc q from
      chartCoord_chartChristoffelContraction (I := I) g x D₂ Yv y₀ j]
  have hAA₂ : chartChristoffelContraction (I := I) g x D₂
        (chartChristoffelContraction (I := I) g x D₁ Yv y₀) y₀
      = ∑ l, (∑ i, ∑ j, chartChristoffel (I := I) g x i j l y₀ * d₂ i *
          (∑ p, ∑ q, chartChristoffel (I := I) g x p q j y₀ * d₁ p * yc q)) •
          chartModelBasis E l := by
    rw [chartChristoffelContraction_def]
    refine Finset.sum_congr rfl fun l _ => ?_
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show chartCoord (E := E) j
          (chartChristoffelContraction (I := I) g x D₁ Yv y₀)
        = ∑ p, ∑ q, chartChristoffel (I := I) g x p q j y₀ * d₁ p * yc q from
      chartCoord_chartChristoffelContraction (I := I) g x D₁ Yv y₀ j]
  have hRHS : chartRiemannCLM (I := I) g x D₁ D₂ Yv
      = ∑ l, (∑ i, ∑ j, ∑ k, yc i * d₁ j * d₂ k *
          chartRiemannTensor (I := I) g x i j k l y₀) • chartModelBasis E l := by
    rw [chartRiemannCLM_apply]
    rw [show (∑ i, ∑ j, ∑ k, ∑ l,
            ((chartModelBasis E).repr Yv i * (chartModelBasis E).repr D₁ j *
                (chartModelBasis E).repr D₂ k *
                chartRiemannTensor (I := I) g x i j k l y₀) • ((chartModelBasis E) l : E))
          = ∑ i, ∑ j, ∑ l, ∑ k,
            ((chartModelBasis E).repr Yv i * (chartModelBasis E).repr D₁ j *
                (chartModelBasis E).repr D₂ k *
                chartRiemannTensor (I := I) g x i j k l y₀) • ((chartModelBasis E) l : E) from by
      refine Finset.sum_congr rfl fun i _ => ?_
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_comm]]
    rw [show (∑ i, ∑ j, ∑ l, ∑ k,
            ((chartModelBasis E).repr Yv i * (chartModelBasis E).repr D₁ j *
                (chartModelBasis E).repr D₂ k *
                chartRiemannTensor (I := I) g x i j k l y₀) • ((chartModelBasis E) l : E))
          = ∑ i, ∑ l, ∑ j, ∑ k,
            ((chartModelBasis E).repr Yv i * (chartModelBasis E).repr D₁ j *
                (chartModelBasis E).repr D₂ k *
                chartRiemannTensor (I := I) g x i j k l y₀) • ((chartModelBasis E) l : E) from by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rfl
  rw [hAA₁, hAA₂, hRHS]
  rw [← Finset.sum_sub_distrib]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← sub_smul, ← add_smul]
  congr 1
  have hR_split : (∑ i, ∑ j, ∑ k, yc i * d₁ j * d₂ k *
        chartRiemannTensor (I := I) g x i j k l y₀)
      = (∑ i, ∑ j, ∑ k, yc i * d₁ j * d₂ k *
            (partialDeriv (E := E) j (chartChristoffel (I := I) g x i k l) y₀
              - partialDeriv (E := E) k (chartChristoffel (I := I) g x i j l) y₀))
        + (∑ i, ∑ j, ∑ k, yc i * d₁ j * d₂ k *
            (∑ m, (chartChristoffel (I := I) g x j m l y₀ *
                  chartChristoffel (I := I) g x i k m y₀
                - chartChristoffel (I := I) g x k m l y₀ *
                  chartChristoffel (I := I) g x i j m y₀))) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [chartRiemannTensor_def]; ring
  rw [hR_split]
  congr 1
  · have hLHS : (∑ i, ∑ j,
          ((fderiv ℝ (chartChristoffel (I := I) g x i j l) y₀ D₁) * d₂ i * yc j
            - (fderiv ℝ (chartChristoffel (I := I) g x i j l) y₀ D₂) * d₁ i * yc j))
        = (∑ i, ∑ j, ∑ d,
            d₁ d * partialDeriv (E := E) d (chartChristoffel (I := I) g x i j l) y₀ * d₂ i * yc j)
          - (∑ i, ∑ j, ∑ d,
            d₂ d * partialDeriv (E := E) d (chartChristoffel (I := I) g x i j l) y₀ * d₁ i * yc j) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hfd₁ i j l, hfd₂ i j l, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul,
        Finset.sum_mul, ← Finset.sum_sub_distrib]
    rw [hLHS]
    have hRHS' : (∑ i, ∑ j, ∑ k, yc i * d₁ j * d₂ k *
          (partialDeriv (E := E) j (chartChristoffel (I := I) g x i k l) y₀
            - partialDeriv (E := E) k (chartChristoffel (I := I) g x i j l) y₀))
        = (∑ i, ∑ j, ∑ k, yc i * d₁ j * d₂ k *
              partialDeriv (E := E) j (chartChristoffel (I := I) g x i k l) y₀)
          - (∑ i, ∑ j, ∑ k, yc i * d₁ j * d₂ k *
              partialDeriv (E := E) k (chartChristoffel (I := I) g x i j l) y₀) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [hRHS']
    congr 1
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun d _ => ?_
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [partialDeriv_chartChristoffel_symm (I := I) g x i j l d]
      ring
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      refine Finset.sum_congr rfl fun i _ => ?_
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [partialDeriv_chartChristoffel_symm (I := I) g x i j l d]
      ring
  · have hAA1c : (∑ i, ∑ j, chartChristoffel (I := I) g x i j l y₀ * d₁ i *
            (∑ p, ∑ q, chartChristoffel (I := I) g x p q j y₀ * d₂ p * yc q))
        = ∑ i, ∑ j, ∑ p, ∑ q,
            chartChristoffel (I := I) g x i j l y₀ * d₁ i *
              chartChristoffel (I := I) g x p q j y₀ * d₂ p * yc q := by
      refine Finset.sum_congr rfl fun i _ => ?_
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      ring
    have hAA2c : (∑ i, ∑ j, chartChristoffel (I := I) g x i j l y₀ * d₂ i *
            (∑ p, ∑ q, chartChristoffel (I := I) g x p q j y₀ * d₁ p * yc q))
        = ∑ i, ∑ j, ∑ p, ∑ q,
            chartChristoffel (I := I) g x i j l y₀ * d₂ i *
              chartChristoffel (I := I) g x p q j y₀ * d₁ p * yc q := by
      refine Finset.sum_congr rfl fun i _ => ?_
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      ring
    rw [hAA1c, hAA2c]
    have hBsplit : (∑ i, ∑ j, ∑ k, yc i * d₁ j * d₂ k *
          (∑ m, (chartChristoffel (I := I) g x j m l y₀ *
                chartChristoffel (I := I) g x i k m y₀
              - chartChristoffel (I := I) g x k m l y₀ *
                chartChristoffel (I := I) g x i j m y₀)))
        = (∑ i, ∑ j, ∑ k, ∑ m, yc i * d₁ j * d₂ k *
              (chartChristoffel (I := I) g x j m l y₀ *
                chartChristoffel (I := I) g x i k m y₀))
          - (∑ i, ∑ j, ∑ k, ∑ m, yc i * d₁ j * d₂ k *
              (chartChristoffel (I := I) g x k m l y₀ *
                chartChristoffel (I := I) g x i j m y₀)) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun m _ => ?_
      ring
    rw [hBsplit]
    have hcollapse : ∀ F : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
          Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ,
        (∑ a, ∑ b, ∑ c, ∑ d, F a b c d)
          = ∑ w : (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) ×
              (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)),
            F w.1.1 w.1.2 w.2.1 w.2.2 := by
      intro F
      simp only [Fintype.sum_prod_type]
    congr 1
    · rw [hcollapse (fun i j p q => chartChristoffel (I := I) g x i j l y₀ * d₁ i *
          chartChristoffel (I := I) g x p q j y₀ * d₂ p * yc q)]
      rw [hcollapse (fun i j k m => yc i * d₁ j * d₂ k *
          (chartChristoffel (I := I) g x j m l y₀ * chartChristoffel (I := I) g x i k m y₀))]
      refine Finset.sum_nbij'
        (i := fun w => ((w.2.2, w.1.1), (w.2.1, w.1.2)))
        (j := fun w => ((w.1.2, w.2.2), (w.2.1, w.1.1))) ?_ ?_ ?_ ?_ ?_
      · intro w _; exact Finset.mem_univ _
      · intro w _; exact Finset.mem_univ _
      · intro w _; rfl
      · intro w _; rfl
      · intro w _
        dsimp only
        rw [chartChristoffel_symm (I := I) g x w.2.1 w.2.2 w.1.2 y₀]
        ring
    · rw [hcollapse (fun i j p q => chartChristoffel (I := I) g x i j l y₀ * d₂ i *
          chartChristoffel (I := I) g x p q j y₀ * d₁ p * yc q)]
      rw [hcollapse (fun i j k m => yc i * d₁ j * d₂ k *
          (chartChristoffel (I := I) g x k m l y₀ * chartChristoffel (I := I) g x i j m y₀))]
      refine Finset.sum_nbij'
        (i := fun w => ((w.2.2, w.2.1), (w.1.1, w.1.2)))
        (j := fun w => ((w.2.1, w.2.2), (w.1.2, w.1.1))) ?_ ?_ ?_ ?_ ?_
      · intro w _; exact Finset.mem_univ _
      · intro w _; exact Finset.mem_univ _
      · intro w _; rfl
      · intro w _; rfl
      · intro w _
        dsimp only
        rw [chartChristoffel_symm (I := I) g x w.2.1 w.2.2 w.1.2 y₀]
        ring

end Aux6

namespace Aux7
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open Aux4 Aux6
open scoped Manifold ContDiff Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

omit [T2Space M] [SigmaCompactSpace M] in
omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma commutator_eq_chartRiemannCLM
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M) (Y : ℝ → ℝ → E) (s t : ℝ)
    (hF : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => extChartAt I (f s t) (f p.1 p.2)) (s, t))
    (hY : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Y p.1 p.2) (s, t)) :
    chartCovDerivAlong (I := I) g (f s t) (fun u : ℝ => f u t) (fun u : ℝ =>
        chartCovDerivAlong (I := I) g (f s t) (fun v : ℝ => f u v)
          (fun v : ℝ => Y u v) t) s
      - chartCovDerivAlong (I := I) g (f s t) (fun v : ℝ => f s v) (fun v : ℝ =>
        chartCovDerivAlong (I := I) g (f s t) (fun u : ℝ => f u v)
          (fun u : ℝ => Y u v) s) t
      = chartRiemannCLM (I := I) g (f s t)
          (fderiv ℝ (fun u : ℝ => extChartAt I (f s t) (f u t)) s (1 : ℝ))
          (fderiv ℝ (fun v : ℝ => extChartAt I (f s t) (f s v)) t (1 : ℝ))
          (Y s t) := by
  classical
  set α : M := f s t with hα
  set y₀ : E := extChartAt I α (f s t) with hy₀
  have hΓ : ∀ i j k : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ (chartChristoffel (I := I) g α i j k) y₀ := by
    intro i j k
    have := Aux3.chartChristoffel_differentiableAt_self (I := I) g α i j k
    rwa [show extChartAt I α α = y₀ from by rw [hy₀, hα]] at this
  rw [nabla_s_nabla_t_eq (I := I) g α f Y s t,
      nabla_t_nabla_s_eq (I := I) g α f Y s t]
  rw [(hasDerivAt_innerW (I := I) g α f Y s t hF hY hΓ).deriv,
      (hasDerivAt_innerW_snd (I := I) g α f Y s t hF hY hΓ).deriv]
  have hWs : chartCovDerivAlong (I := I) g α (fun v : ℝ => f s v) (fun v : ℝ => Y s v) t
      = fderiv ℝ (fun v : ℝ => Y s v) t (1 : ℝ)
        + chartChristoffelContraction (I := I) g α
            (fderiv ℝ (fun v : ℝ => extChartAt I α (f s v)) t (1 : ℝ)) (Y s t) y₀ := by
    rw [chartCovDerivAlong_def]; rfl
  have hWt : chartCovDerivAlong (I := I) g α (fun u : ℝ => f u t) (fun u : ℝ => Y u t) s
      = fderiv ℝ (fun u : ℝ => Y u t) s (1 : ℝ)
        + chartChristoffelContraction (I := I) g α
            (fderiv ℝ (fun u : ℝ => extChartAt I α (f u t)) s (1 : ℝ)) (Y s t) y₀ := by
    rw [chartCovDerivAlong_def]; rfl
  rw [hWs, hWt]
  set G : ℝ × ℝ → E := fun p : ℝ × ℝ => extChartAt I α (f p.1 p.2) with hG
  set D₁ : E := fderiv ℝ G (s, t) (1, 0) with hD₁
  set D₂ : E := fderiv ℝ G (s, t) (0, 1) with hD₂
  set Yv : E := Y s t with hYv
  have hGdiff : DifferentiableAt ℝ G (s, t) := hF.differentiableAt two_ne_zero
  have hpf₁ : fderiv ℝ (fun u : ℝ => extChartAt I α (f u t)) s (1 : ℝ) = D₁ :=
    Aux2.partial_fst_apply_one (fun p : ℝ × ℝ => extChartAt I α (f p.1 p.2)) s t hGdiff
  have hpf₂ : fderiv ℝ (fun v : ℝ => extChartAt I α (f s v)) t (1 : ℝ) = D₂ :=
    Aux2.partial_snd_apply_one (fun p : ℝ × ℝ => extChartAt I α (f p.1 p.2)) s t hGdiff
  have hSchwarzF : fderiv ℝ (fderiv ℝ G) (s, t) (1, 0) (0, 1)
      = fderiv ℝ (fderiv ℝ G) (s, t) (0, 1) (1, 0) := by
    have hsymm : IsSymmSndFDerivAt ℝ G (s, t) := by
      refine ContDiffAt.isSymmSndFDerivAt hF ?_
      rw [minSmoothness_of_isRCLikeNormedField]
    exact hsymm (1, 0) (0, 1)
  have hSchwarzY : fderiv ℝ (fderiv ℝ (fun p : ℝ × ℝ => Y p.1 p.2)) (s, t) (1, 0) (0, 1)
      = fderiv ℝ (fderiv ℝ (fun p : ℝ × ℝ => Y p.1 p.2)) (s, t) (0, 1) (1, 0) := by
    have hsymm : IsSymmSndFDerivAt ℝ (fun p : ℝ × ℝ => Y p.1 p.2) (s, t) := by
      refine ContDiffAt.isSymmSndFDerivAt hY ?_
      rw [minSmoothness_of_isRCLikeNormedField]
    exact hsymm (1, 0) (0, 1)
  simp only [hpf₁, hpf₂]
  rw [← curvPart_eq_chartRiemannCLM (I := I) g α D₁ D₂ Yv]
  simp only [hSchwarzF]
  rw [← hy₀]
  rw [ChartChristoffel.contraction_add_right (g := g) (α := α) (y := y₀) D₁
        (fderiv ℝ (fun v : ℝ => Y s v) t (1 : ℝ))
        (chartChristoffelContraction (I := I) g α D₂ Yv y₀),
      ChartChristoffel.contraction_add_right (g := g) (α := α) (y := y₀) D₂
        (fderiv ℝ (fun u : ℝ => Y u t) s (1 : ℝ))
        (chartChristoffelContraction (I := I) g α D₁ Yv y₀)]
  have hYpf₁ : fderiv ℝ (fun u : ℝ => Y u t) s (1 : ℝ)
      = fderiv ℝ (fun p : ℝ × ℝ => Y p.1 p.2) (s, t) (1, 0) :=
    Aux2.partial_fst_apply_one (fun p : ℝ × ℝ => Y p.1 p.2) s t (hY.differentiableAt two_ne_zero)
  have hYpf₂ : fderiv ℝ (fun v : ℝ => Y s v) t (1 : ℝ)
      = fderiv ℝ (fun p : ℝ × ℝ => Y p.1 p.2) (s, t) (0, 1) :=
    Aux2.partial_snd_apply_one (fun p : ℝ × ℝ => Y p.1 p.2) s t (hY.differentiableAt two_ne_zero)
  rw [hYpf₁, hYpf₂, hSchwarzY]
  set mY : E := fderiv ℝ (fderiv ℝ (fun p : ℝ × ℝ => Y p.1 p.2)) (s, t) (0, 1) (1, 0) with hmY
  set mF : E := fderiv ℝ (fderiv ℝ G) (s, t) (0, 1) (1, 0) with hmF
  set DY₁ : E := fderiv ℝ (fun p : ℝ × ℝ => Y p.1 p.2) (s, t) (1, 0) with hDY₁
  set DY₂ : E := fderiv ℝ (fun p : ℝ × ℝ => Y p.1 p.2) (s, t) (0, 1) with hDY₂
  have hsplit_st : (∑ k : Fin (Module.finrank ℝ E),
        (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          ((fderiv ℝ (chartChristoffel (I := I) g α i j k) y₀ D₁) *
              chartCoord (E := E) i D₂ * chartCoord (E := E) j Yv
            + chartChristoffel (I := I) g α i j k y₀ *
              chartCoord (E := E) i mF * chartCoord (E := E) j Yv
            + chartChristoffel (I := I) g α i j k y₀ *
              chartCoord (E := E) i D₂ * chartCoord (E := E) j DY₁)) •
          chartModelBasis E k)
      = (∑ k, (∑ i, ∑ j,
            (fderiv ℝ (chartChristoffel (I := I) g α i j k) y₀ D₁) *
              chartCoord (E := E) i D₂ * chartCoord (E := E) j Yv) • chartModelBasis E k)
        + chartChristoffelContraction (I := I) g α mF Yv y₀
        + chartChristoffelContraction (I := I) g α D₂ DY₁ y₀ := by
    rw [chartChristoffelContraction_def (v := mF), chartChristoffelContraction_def (v := D₂) (w := DY₁)]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← add_smul, ← add_smul]
    congr 1
    simp only [Finset.sum_add_distrib]
  have hsplit_ts : (∑ k : Fin (Module.finrank ℝ E),
        (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          ((fderiv ℝ (chartChristoffel (I := I) g α i j k) y₀ D₂) *
              chartCoord (E := E) i D₁ * chartCoord (E := E) j Yv
            + chartChristoffel (I := I) g α i j k y₀ *
              chartCoord (E := E) i mF * chartCoord (E := E) j Yv
            + chartChristoffel (I := I) g α i j k y₀ *
              chartCoord (E := E) i D₁ * chartCoord (E := E) j DY₂)) •
          chartModelBasis E k)
      = (∑ k, (∑ i, ∑ j,
            (fderiv ℝ (chartChristoffel (I := I) g α i j k) y₀ D₂) *
              chartCoord (E := E) i D₁ * chartCoord (E := E) j Yv) • chartModelBasis E k)
        + chartChristoffelContraction (I := I) g α mF Yv y₀
        + chartChristoffelContraction (I := I) g α D₁ DY₂ y₀ := by
    rw [chartChristoffelContraction_def (v := mF), chartChristoffelContraction_def (v := D₁) (w := DY₂)]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← add_smul, ← add_smul]
    congr 1
    simp only [Finset.sum_add_distrib]
  have hdGcomb : (∑ k, (∑ i, ∑ j,
          (fderiv ℝ (chartChristoffel (I := I) g α i j k) y₀ D₁) *
            chartCoord (E := E) i D₂ * chartCoord (E := E) j Yv) • chartModelBasis E k)
        - (∑ k, (∑ i, ∑ j,
          (fderiv ℝ (chartChristoffel (I := I) g α i j k) y₀ D₂) *
            chartCoord (E := E) i D₁ * chartCoord (E := E) j Yv) • chartModelBasis E k)
      = ∑ k, (∑ i, ∑ j,
          ((fderiv ℝ (chartChristoffel (I := I) g α i j k) y₀ D₁) *
              chartCoord (E := E) i D₂ * chartCoord (E := E) j Yv
            - (fderiv ℝ (chartChristoffel (I := I) g α i j k) y₀ D₂) *
              chartCoord (E := E) i D₁ * chartCoord (E := E) j Yv)) • chartModelBasis E k := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← sub_smul]
    congr 1
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
  rw [hsplit_st, hsplit_ts]
  rw [← hdGcomb]
  abel_nf

end Aux7

omit [InnerProductSpace ℝ E] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem chartCovDerivAlong_commutator_eq_riemannOp_on_variation
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M)
    (hf : IsSmoothVariation (I := I) f)
    (Y : ℝ → ℝ → E) (s t : ℝ)
    (hY : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Y p.1 p.2) (s, t)) :
    chartCovDerivAlong (I := I) g (f s t) (fun u : ℝ => f u t) (fun u : ℝ =>
        chartCovDerivAlong (I := I) g (f s t) (fun v : ℝ => f u v)
          (fun v : ℝ => Y u v) t) s
      - chartCovDerivAlong (I := I) g (f s t) (fun v : ℝ => f s v) (fun v : ℝ =>
        chartCovDerivAlong (I := I) g (f s t) (fun u : ℝ => f u v)
          (fun u : ℝ => Y u v) s) t
    = (DifferentialGeometry.Integral.Connection.riemannOp
        (DifferentialGeometry.Integral.Connection.LeviCivita
          (I := I) g) (f s t))
        (fderiv ℝ (fun u : ℝ => extChartAt I (f s t) (f u t)) s (1 : ℝ))
        (fderiv ℝ (fun v : ℝ => extChartAt I (f s t) (f s v)) t (1 : ℝ))
        (Y s t) := by
  have hF : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => extChartAt I (f s t) (f p.1 p.2)) (s, t) :=
    chartPulled_contDiffAt (I := I) f hf s t
  rw [Aux7.commutator_eq_chartRiemannCLM (I := I) g f Y s t hF hY,
    ← DifferentialGeometry.Integral.Connection.riemannOp_eq_chartRiemannCLM_apply_of_basis_identity
      (I := I) g (f s t)
      (DifferentialGeometry.Integral.Connection.chartRiemannBasisIdentity_LeviCivita
        (I := I) g (f s t))]

end Variation
end Riemannian
end Geometry
end DifferentialGeometry

end
