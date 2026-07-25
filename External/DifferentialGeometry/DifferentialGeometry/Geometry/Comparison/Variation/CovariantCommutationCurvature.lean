import DifferentialGeometry.Geometry.Connection.ParallelTransport.ParallelTransport
import DifferentialGeometry.Geometry.Comparison.Variation.FixedChartIdentities
import DifferentialGeometry.Geometry.Connection.ParallelTransport.AlongCurve
import DifferentialGeometry.Geometry.Connection.ParallelTransport.CovariantDerivativeAlong
import DifferentialGeometry.Geometry.Connection.ParallelTransport.MFDerivAlongCurve
import DifferentialGeometry.Geometry.Geodesic.Equation
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Defs
import DifferentialGeometry.Geometry.Connection.LeviCivita.Defs
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciIdentity
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnection
import DifferentialGeometry.Geometry.Metric.TensorInner.TangentRiemannian
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Topology.VectorBundle.Riemannian
import Mathlib.Topology.Compactness.Compact
import DifferentialGeometry.Geometry.Comparison.Variation.ArcLength
import DifferentialGeometry.Geometry.Comparison.Variation.SpeedDerivative
import DifferentialGeometry.Geometry.Comparison.Variation.FirstVariation



noncomputable section

open Set Function Filter Manifold Bundle MeasureTheory intervalIntegral
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Variation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.Geodesic

open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong in

omit [T2Space M] [SigmaCompactSpace M] in
private lemma chartCoord_covDerivAlong_eq_chartCovDerivAlong_chartRepAtBase
    {n : WithTop ℕ∞} [ENat.LEInfty n] (hn : n ≠ 0)
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (V : ∀ t, TangentSpace I (γ t))
    (t : ℝ) (β : M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I n γ) (hβ : γ t ∈ (chartAt H β).source)
    (hV : DifferentiableAt ℝ (chartRepAt (I := I) γ V t) t) :
    (trivializationAt E (TangentSpace I) β).continuousLinearMapAt ℝ (γ t)
        (covDerivAlong (I := I) g γ V t)
      = chartCovDerivAlong (I := I) g β γ (chartRepAtBase (I := I) β γ V) t := by
  have hinv := covDerivAlong_chart_foot_invariance (I := I) hn g γ V t β hγ hβ hV
  rw [← hinv]
  have hmem : γ t ∈ (trivializationAt E (TangentSpace I) β).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact hβ
  exact (trivializationAt E (TangentSpace I) β).continuousLinearMapAt_symmL (R := ℝ) hmem _

open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong in

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma slice_velocityField_chartRep_differentiableAt
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M)
    (hf : IsSmoothVariation (I := I) f) (u t₀ : ℝ) :
    DifferentiableAt ℝ
      (chartRepAt (I := I) (fun v : ℝ => f u v)
        (fun v : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f u w) v (1 : ℝ)) t₀) t₀ := by
  have hf' : IsSmoothVariation (I := I) (fun a b : ℝ => f (u + a) b) := by
    have hcomp : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (8 : ℕ)
        (fun p : ℝ × ℝ => (u + p.1, p.2)) :=
      (contMDiff_const.add contMDiff_fst).prodMk contMDiff_snd
    exact (hf : ContMDiff _ _ _ _).comp hcomp
  have h := velocityField_chartRep_differentiableAt (I := I) g (fun a b : ℝ => f (u + a) b) hf' t₀
  have hrw : (fun a b : ℝ => f (u + a) b) = (fun a b : ℝ => f (u + a) b) := rfl
  have hval : (u + 0 : ℝ) = u := add_zero u
  rw [hval] at h
  exact h

open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong in

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma slice_longitudinalField_transverse_chartRep_differentiableAt
    (_g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M)
    (hf : IsSmoothVariation (I := I) f) (v : ℝ) :
    DifferentiableAt ℝ
      (chartRepAt (I := I) (fun u : ℝ => f u v)
        (fun u : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f u w) v (1 : ℝ)) 0) 0 := by
  classical
  set α : M := f 0 v with hα
  have hslice_u : ∀ s : ℝ, ContMDiff (𝓘(ℝ, ℝ)) I (8 : ℕ) (fun w : ℝ => f s w) := by
    intro s
    have hincl : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (8 : ℕ) (fun w : ℝ => (s, w)) :=
      contMDiff_const.prodMk contMDiff_id
    exact (hf : ContMDiff _ _ _ _).comp hincl
  have htransverse : ContMDiff (𝓘(ℝ, ℝ)) I (8 : ℕ) (fun u : ℝ => f u v) := by
    have hincl : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (8 : ℕ) (fun u : ℝ => (u, v)) :=
      contMDiff_id.prodMk contMDiff_const
    exact (hf : ContMDiff _ _ _ _).comp hincl
  set sec : ℝ → E := fun u : ℝ => fderiv ℝ (fun w : ℝ => extChartAt I α (f u w)) v (1 : ℝ)
    with hsec
  have hsec_cdiff : ContDiffAt ℝ (7 : ℕ) sec 0 := by
    have hsrc0 : f 0 v ∈ (chartAt H α).source := by rw [hα]; exact mem_chart_source H (f 0 v)
    have hjoint : ContDiffAt ℝ (8 : ℕ)
        (Function.uncurry (fun u w : ℝ => extChartAt I α (f u w))) (0, v) := by
      have h := chartPulled_contDiffAt_infty (I := I) f hf α 0 v hsrc0
      exact h
    have hgv : ContDiffAt ℝ (7 : ℕ) (fun _ : ℝ => v) 0 := contDiffAt_const
    have hpartial : ContDiffAt ℝ (7 : ℕ)
        (fun u : ℝ => fderiv ℝ (fun w : ℝ => extChartAt I α (f u w)) ((fun _ : ℝ => v) u)) 0 :=
      ContDiffAt.fderiv (𝕜 := ℝ)
        (f := fun u w : ℝ => extChartAt I α (f u w)) (g := fun _ : ℝ => v)
        hjoint hgv (by exact_mod_cast (by norm_num : (7 : ℕ) + 1 ≤ 8))
    exact (ContinuousLinearMap.apply ℝ E (1 : ℝ)).contDiff.contDiffAt.comp 0 hpartial
  have hopen : IsOpen {u : ℝ | f u v ∈ (chartAt H α).source} :=
    htransverse.continuous.isOpen_preimage _ (chartAt H α).open_source
  have h0 : (0 : ℝ) ∈ {u : ℝ | f u v ∈ (chartAt H α).source} := by
    change f 0 v ∈ (chartAt H α).source; rw [hα]; exact mem_chart_source H (f 0 v)
  have heq : (chartRepAt (I := I) (fun u : ℝ => f u v)
      (fun u : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f u w) v (1 : ℝ)) 0)
        =ᶠ[𝓝 (0 : ℝ)] sec := by
    filter_upwards [hopen.mem_nhds h0] with u hu
    have hsrc : (fun w : ℝ => f u w) v ∈ (chartAt H α).source := hu
    have hbridge := MFDerivAlongCurve.chartCoord_mfderiv_along_curve_eq_fderiv_of_mdifferentiableAt
      (I := I) (M := M) (γ := fun w : ℝ => f u w) ((hslice_u u).mdifferentiableAt (by norm_num)) α hsrc
    change (trivializationAt E (TangentSpace I) ((fun u : ℝ => f u v) 0)).continuousLinearMapAt ℝ
        ((fun u : ℝ => f u v) u) (mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f u w) v (1 : ℝ)) = sec u
    rw [hsec, show (fun u : ℝ => f u v) 0 = α from hα.symm]
    have hcompfun : ((extChartAt I α) ∘ (fun w : ℝ => f u w))
        = (fun w : ℝ => extChartAt I α (f u w)) := rfl
    rw [hcompfun] at hbridge
    exact hbridge
  exact (heq.differentiableAt_iff).mpr (hsec_cdiff.differentiableAt (by simp))

open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong in

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma chartCoord_longitudinalVelocity_contDiffAt
    (f : ℝ → ℝ → M) (hf : IsSmoothVariation (I := I) f) (t : ℝ) :
    ContDiffAt ℝ 2 (fun p : ℝ × ℝ =>
        (trivializationAt E (TangentSpace I) (f 0 t)).continuousLinearMapAt ℝ (f p.1 p.2)
          (mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f p.1 w) p.2 (1 : ℝ))) (0, t) := by
  classical
  set β : M := f 0 t with hβ
  have hsrc0 : f 0 t ∈ (chartAt H β).source := by rw [hβ]; exact mem_chart_source H (f 0 t)
  have hF : ContDiffAt ℝ (8 : ℕ) (fun p : ℝ × ℝ => extChartAt I β (f p.1 p.2)) (0, t) :=
    chartPulled_contDiffAt_infty (I := I) f hf β 0 t hsrc0
  have hfd : ContDiffAt ℝ (7 : ℕ) (fderiv ℝ (fun q : ℝ × ℝ => extChartAt I β (f q.1 q.2))) (0, t) :=
    hF.fderiv_right (m := (7 : ℕ)) (by exact_mod_cast (by norm_num : (7 : ℕ) + 1 ≤ 8))
  have hYmodel : ContDiffAt ℝ 2 (fun p : ℝ × ℝ =>
      fderiv ℝ (fun q : ℝ × ℝ => extChartAt I β (f q.1 q.2)) p (0, 1)) (0, t) :=
    ((ContinuousLinearMap.apply ℝ E ((0, 1) : ℝ × ℝ)).contDiff.contDiffAt.comp (0, t)
      hfd).of_le (by norm_cast)
  have hslice_u : ∀ s : ℝ, ContMDiff (𝓘(ℝ, ℝ)) I (8 : ℕ) (fun w : ℝ => f s w) := by
    intro s
    have hincl : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (8 : ℕ) (fun w : ℝ => (s, w)) :=
      contMDiff_const.prodMk contMDiff_id
    exact (hf : ContMDiff _ _ _ _).comp hincl
  have hf_cont : Continuous (fun p : ℝ × ℝ => f p.1 p.2) := hf.continuous
  have hopen : IsOpen {p : ℝ × ℝ | f p.1 p.2 ∈ (chartAt H β).source} :=
    hf_cont.isOpen_preimage _ (chartAt H β).open_source
  have hmem0 : (0, t) ∈ {p : ℝ × ℝ | f p.1 p.2 ∈ (chartAt H β).source} := by
    change f 0 t ∈ (chartAt H β).source; exact hsrc0
  have heq : (fun p : ℝ × ℝ =>
      (trivializationAt E (TangentSpace I) β).continuousLinearMapAt ℝ (f p.1 p.2)
        (mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f p.1 w) p.2 (1 : ℝ)))
        =ᶠ[𝓝 (0, t)]
      (fun p : ℝ × ℝ => fderiv ℝ (fun q : ℝ × ℝ => extChartAt I β (f q.1 q.2)) p (0, 1)) := by
    filter_upwards [hopen.mem_nhds hmem0] with p hp
    have hsrc : (fun w : ℝ => f p.1 w) p.2 ∈ (chartAt H β).source := hp
    have hbridge := MFDerivAlongCurve.chartCoord_mfderiv_along_curve_eq_fderiv_of_mdifferentiableAt
      (I := I) (M := M) (γ := fun w : ℝ => f p.1 w) ((hslice_u p.1).mdifferentiableAt (by norm_num)) β hsrc
    have hcompfun : ((extChartAt I β) ∘ (fun w : ℝ => f p.1 w))
        = (fun w : ℝ => extChartAt I β (f p.1 w)) := rfl
    rw [hcompfun] at hbridge
    rw [hbridge]
    have hdiffJoint : DifferentiableAt ℝ (fun q : ℝ × ℝ => extChartAt I β (f q.1 q.2)) p := by
      have hC1 : ContDiffAt ℝ 1 (fun q : ℝ × ℝ => extChartAt I β (f q.1 q.2)) p :=
        (chartPulled_contDiffAt_infty (I := I) f hf β p.1 p.2 hsrc).of_le (by norm_cast)
      exact hC1.differentiableAt (by simp)
    have hincl : HasFDerivAt (fun w : ℝ => (p.1, w)) (ContinuousLinearMap.inr ℝ ℝ ℝ) p.2 :=
      hasFDerivAt_prodMk_right p.1 p.2
    have hG : HasFDerivAt (fun q : ℝ × ℝ => extChartAt I β (f q.1 q.2))
        (fderiv ℝ (fun q : ℝ × ℝ => extChartAt I β (f q.1 q.2)) p) p :=
      hdiffJoint.hasFDerivAt
    have hch := hG.comp p.2 hincl
    have hcompfun2 : (fun w : ℝ => extChartAt I β (f p.1 w))
        = (fun q : ℝ × ℝ => extChartAt I β (f q.1 q.2)) ∘ (fun w : ℝ => (p.1, w)) := rfl
    rw [hcompfun2, hch.fderiv]
    simp [ContinuousLinearMap.inr]
  exact hYmodel.congr_of_eventuallyEq heq

open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
  DifferentialGeometry.Integral.DivergenceTheorem in

omit [T2Space M] [SigmaCompactSpace M] in
lemma slice_secondCovDeriv_chartRep_differentiableAt
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M)
    (hf : IsSmoothVariation (I := I) f) (t : ℝ) :
    DifferentiableAt ℝ
      (chartRepAt (I := I) (fun s : ℝ => f s t)
        (fun s : ℝ => covDerivAlong (I := I) g (fun s' : ℝ => f s' t)
          (fun s' : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f s' w) t (1 : ℝ)) s) 0) 0 := by
  classical
  set β : M := f 0 t with hβ
  have hslice_u : ∀ s : ℝ, ContMDiff (𝓘(ℝ, ℝ)) I (8 : ℕ) (fun w : ℝ => f s w) := by
    intro s
    have hincl : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (8 : ℕ) (fun w : ℝ => (s, w)) :=
      contMDiff_const.prodMk contMDiff_id
    exact (hf : ContMDiff _ _ _ _).comp hincl
  have htransverse : ContMDiff (𝓘(ℝ, ℝ)) I (8 : ℕ) (fun s : ℝ => f s t) := by
    have hincl : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (8 : ℕ) (fun s : ℝ => (s, t)) :=
      contMDiff_id.prodMk contMDiff_const
    exact (hf : ContMDiff _ _ _ _).comp hincl
  set velT : ℝ → ℝ → E :=
    fun s v => mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f s w) v (1 : ℝ) with hvelT
  set Y : ℝ → E := fun s : ℝ =>
    (trivializationAt E (TangentSpace I) β).continuousLinearMapAt ℝ (f s t) (velT s t) with hY
  have hY_C2 : ContDiffAt ℝ 2 Y 0 := by
    have hjoint : ContDiffAt ℝ 2 (fun p : ℝ × ℝ =>
        (trivializationAt E (TangentSpace I) (f 0 t)).continuousLinearMapAt ℝ (f p.1 p.2)
          (mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f p.1 w) p.2 (1 : ℝ))) (0, t) :=
      chartCoord_longitudinalVelocity_contDiffAt (I := I) f hf t
    have hincl : ContDiffAt ℝ 2 (fun s : ℝ => (s, t)) 0 :=
      (contDiff_id.prodMk contDiff_const).contDiffAt
    have := hjoint.comp 0 hincl
    exact this
  have hY_C1 : ContDiffAt ℝ 1 Y 0 := hY_C2.of_le one_le_two
  have hY_diff : DifferentiableAt ℝ Y 0 := hY_C1.differentiableAt (by norm_cast)
  have hderivY_diff : DifferentiableAt ℝ (deriv Y) 0 :=
    (hY_C2.derivWithin (m := 1) (by norm_cast)).differentiableAt (by norm_cast)
  set uC : ℝ → E := chartCurve (I := I) β (fun s : ℝ => f s t) with huC
  have huC_cdiff : ContDiffAt ℝ (8 : ℕ) uC 0 := contDiffAt_chartCurve (I := I) htransverse 0
  have huC_diff : DifferentiableAt ℝ uC 0 := huC_cdiff.differentiableAt (by norm_num)
  have hderivuC_diff : DifferentiableAt ℝ (deriv uC) 0 :=
    (huC_cdiff.derivWithin (m := (1 : ℕ)) (by exact_mod_cast (by norm_num : (1 : ℕ) + 1 ≤ 8))).differentiableAt
      (by norm_num)
  have huC0 : uC 0 = extChartAt I β β := by rw [huC, chartCurve_def, hβ]
  have hΓ_diff : ∀ i j k : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ (chartChristoffel (I := I) g β i j k) (uC 0) := by
    intro i j k
    rw [huC0]
    exact Aux3.chartChristoffel_differentiableAt_self (I := I) g β i j k
  have hsrcβ : f 0 t ∈ (chartAt H β).source := by rw [hβ]; exact mem_chart_source H (f 0 t)
  have hopenL : IsOpen {s : ℝ | f s t ∈ (chartAt H β).source} :=
    htransverse.continuous.isOpen_preimage _ (chartAt H β).open_source
  have h0L : (0 : ℝ) ∈ {s : ℝ | f s t ∈ (chartAt H β).source} := hsrcβ
  have hVTdiff : ∀ s : ℝ, DifferentiableAt ℝ
      (chartRepAt (I := I) (fun s' : ℝ => f s' t) (fun s' : ℝ => velT s' t) s) s := by
    intro s
    have hf' : IsSmoothVariation (I := I) (fun a b : ℝ => f (s + a) b) := by
      have hcomp : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (8 : ℕ)
          (fun p : ℝ × ℝ => (s + p.1, p.2)) :=
        (contMDiff_const.add contMDiff_fst).prodMk contMDiff_snd
      exact (hf : ContMDiff _ _ _ _).comp hcomp
    have hd := slice_longitudinalField_transverse_chartRep_differentiableAt
      (I := I) g (fun a b : ℝ => f (s + a) b) hf' t
    set RF : ℝ → E := chartRepAt (I := I)
        (fun a' : ℝ => f (s + a') t)
        (fun a' : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f (s + a') w) t (1 : ℝ)) 0 with hRF
    have hrep : chartRepAt (I := I) (fun s' : ℝ => f s' t) (fun s' : ℝ => velT s' t) s
        = (fun a : ℝ => RF (a - s)) := by
      funext a
      have hcancel : s + (a - s) = a := by ring
      rw [hRF, chartRepAt_apply, chartRepAt_apply, hcancel]
      simp only [add_zero, hvelT]
    rw [hrep]
    have hRFdiff : DifferentiableAt ℝ RF 0 := hd
    have hsub_diff : DifferentiableAt ℝ (fun a : ℝ => a - s) s :=
      differentiableAt_id.sub_const s
    have hcomp : DifferentiableAt ℝ (fun a : ℝ => RF (a - s)) s := by
      have hrw : (fun a : ℝ => RF (a - s)) = RF ∘ (fun a : ℝ => a - s) := rfl
      rw [hrw]
      refine DifferentiableAt.comp s ?_ hsub_diff
      simpa using hRFdiff
    exact hcomp
  have hbridge : (chartRepAt (I := I) (fun s : ℝ => f s t)
        (fun s : ℝ => covDerivAlong (I := I) g (fun s' : ℝ => f s' t)
          (fun s' : ℝ => velT s' t) s) 0)
      =ᶠ[nhds (0 : ℝ)]
        (fun s : ℝ => chartCovDerivAlong (I := I) g β (fun s : ℝ => f s t) Y s) := by
    filter_upwards [hopenL.mem_nhds h0L] with s hs
    rw [chartRepAt_apply]
    change (trivializationAt E (TangentSpace I) β).continuousLinearMapAt ℝ (f s t)
        (covDerivAlong (I := I) g (fun s' : ℝ => f s' t) (fun s' : ℝ => velT s' t) s)
      = chartCovDerivAlong (I := I) g β (fun s : ℝ => f s t) Y s
    have hfwd := chartCoord_covDerivAlong_eq_chartCovDerivAlong_chartRepAtBase (I := I) (by norm_num) g
      (fun s' : ℝ => f s' t) (fun s' : ℝ => velT s' t) s β htransverse hs (hVTdiff s)
    rw [hfwd]
    have hYeq : chartRepAtBase (I := I) β (fun s' : ℝ => f s' t) (fun s' : ℝ => velT s' t) = Y := by
      funext s'; rw [chartRepAtBase_apply, hY]
    rw [hYeq]
  have hccd_diff : DifferentiableAt ℝ
      (fun s : ℝ => chartCovDerivAlong (I := I) g β (fun s : ℝ => f s t) Y s) 0 := by
    have hfun : (fun s : ℝ => chartCovDerivAlong (I := I) g β (fun s : ℝ => f s t) Y s)
        = (fun s : ℝ => deriv Y s
            + chartChristoffelContraction (I := I) g β (deriv uC s) (Y s) (uC s)) := by
      funext s; rw [chartCovDerivAlong_def]
    rw [hfun]
    refine DifferentiableAt.add hderivY_diff ?_
    have hΓhd := hasDerivAt_chartChristoffelContraction (I := I) g β
      (P := deriv uC) (Q := Y) (R := uC)
      (P' := deriv (deriv uC) 0) (Q' := deriv Y 0) (R' := deriv uC 0)
      hderivuC_diff.hasDerivAt hY_diff.hasDerivAt huC_diff.hasDerivAt hΓ_diff
    exact hΓhd.differentiableAt
  exact (hbridge.differentiableAt_iff).mpr hccd_diff

open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong in

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma chartCoord_transverseVelocity_contDiffAt
    (f : ℝ → ℝ → M) (hf : IsSmoothVariation (I := I) f) (t : ℝ) :
    ContDiffAt ℝ 2 (fun p : ℝ × ℝ =>
        (trivializationAt E (TangentSpace I) (f 0 t)).continuousLinearMapAt ℝ (f p.1 p.2)
          (mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f w p.2) p.1 (1 : ℝ))) (0, t) := by
  classical
  set β : M := f 0 t with hβ
  have hsrc0 : f 0 t ∈ (chartAt H β).source := by rw [hβ]; exact mem_chart_source H (f 0 t)
  have hF : ContDiffAt ℝ (8 : ℕ) (fun p : ℝ × ℝ => extChartAt I β (f p.1 p.2)) (0, t) :=
    chartPulled_contDiffAt_infty (I := I) f hf β 0 t hsrc0
  have hfd : ContDiffAt ℝ (7 : ℕ) (fderiv ℝ (fun q : ℝ × ℝ => extChartAt I β (f q.1 q.2))) (0, t) :=
    hF.fderiv_right (m := (7 : ℕ)) (by exact_mod_cast (by norm_num : (7 : ℕ) + 1 ≤ 8))
  have hYmodel : ContDiffAt ℝ 2 (fun p : ℝ × ℝ =>
      fderiv ℝ (fun q : ℝ × ℝ => extChartAt I β (f q.1 q.2)) p (1, 0)) (0, t) :=
    ((ContinuousLinearMap.apply ℝ E ((1, 0) : ℝ × ℝ)).contDiff.contDiffAt.comp (0, t)
      hfd).of_le (by norm_cast)
  have hslice_v : ∀ v : ℝ, ContMDiff (𝓘(ℝ, ℝ)) I (8 : ℕ) (fun w : ℝ => f w v) := by
    intro v
    have hincl : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (8 : ℕ) (fun w : ℝ => (w, v)) :=
      contMDiff_id.prodMk contMDiff_const
    exact (hf : ContMDiff _ _ _ _).comp hincl
  have hf_cont : Continuous (fun p : ℝ × ℝ => f p.1 p.2) := hf.continuous
  have hopen : IsOpen {p : ℝ × ℝ | f p.1 p.2 ∈ (chartAt H β).source} :=
    hf_cont.isOpen_preimage _ (chartAt H β).open_source
  have hmem0 : (0, t) ∈ {p : ℝ × ℝ | f p.1 p.2 ∈ (chartAt H β).source} := by
    change f 0 t ∈ (chartAt H β).source; exact hsrc0
  have heq : (fun p : ℝ × ℝ =>
      (trivializationAt E (TangentSpace I) β).continuousLinearMapAt ℝ (f p.1 p.2)
        (mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f w p.2) p.1 (1 : ℝ)))
        =ᶠ[𝓝 (0, t)]
      (fun p : ℝ × ℝ => fderiv ℝ (fun q : ℝ × ℝ => extChartAt I β (f q.1 q.2)) p (1, 0)) := by
    filter_upwards [hopen.mem_nhds hmem0] with p hp
    have hsrc : (fun w : ℝ => f w p.2) p.1 ∈ (chartAt H β).source := hp
    have hbridge := MFDerivAlongCurve.chartCoord_mfderiv_along_curve_eq_fderiv_of_mdifferentiableAt
      (I := I) (M := M) (γ := fun w : ℝ => f w p.2) ((hslice_v p.2).mdifferentiableAt (by norm_num)) β hsrc
    have hcompfun : ((extChartAt I β) ∘ (fun w : ℝ => f w p.2))
        = (fun w : ℝ => extChartAt I β (f w p.2)) := rfl
    rw [hcompfun] at hbridge
    rw [hbridge]
    have hdiffJoint : DifferentiableAt ℝ (fun q : ℝ × ℝ => extChartAt I β (f q.1 q.2)) p := by
      have hC1 : ContDiffAt ℝ 1 (fun q : ℝ × ℝ => extChartAt I β (f q.1 q.2)) p :=
        (chartPulled_contDiffAt_infty (I := I) f hf β p.1 p.2 hsrc).of_le (by norm_cast)
      exact hC1.differentiableAt (by simp)
    have hincl : HasFDerivAt (fun w : ℝ => (w, p.2)) (ContinuousLinearMap.inl ℝ ℝ ℝ) p.1 :=
      hasFDerivAt_prodMk_left p.1 p.2
    have hG : HasFDerivAt (fun q : ℝ × ℝ => extChartAt I β (f q.1 q.2))
        (fderiv ℝ (fun q : ℝ × ℝ => extChartAt I β (f q.1 q.2)) p) p :=
      hdiffJoint.hasFDerivAt
    have hch := hG.comp p.1 hincl
    have hcompfun2 : (fun w : ℝ => extChartAt I β (f w p.2))
        = (fun q : ℝ × ℝ => extChartAt I β (f q.1 q.2)) ∘ (fun w : ℝ => (w, p.2)) := rfl
    rw [hcompfun2, hch.fderiv]
    simp [ContinuousLinearMap.inl]
  exact hYmodel.congr_of_eventuallyEq heq

open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong in

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma slice_transverseField_longitudinal_chartRep_differentiableAt
    (_g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M)
    (hf : IsSmoothVariation (I := I) f) (s t₀ : ℝ) :
    DifferentiableAt ℝ
      (chartRepAt (I := I) (fun v : ℝ => f s v)
        (fun v : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f w v) s (1 : ℝ)) t₀) t₀ := by
  classical
  set α : M := f s t₀ with hα
  have hslice_v : ∀ v : ℝ, ContMDiff (𝓘(ℝ, ℝ)) I (8 : ℕ) (fun w : ℝ => f w v) := by
    intro v
    have hincl : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (8 : ℕ) (fun w : ℝ => (w, v)) :=
      contMDiff_id.prodMk contMDiff_const
    exact (hf : ContMDiff _ _ _ _).comp hincl
  have hslice_s : ContMDiff (𝓘(ℝ, ℝ)) I (8 : ℕ) (fun v : ℝ => f s v) := by
    have hincl : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (8 : ℕ) (fun v : ℝ => (s, v)) :=
      contMDiff_const.prodMk contMDiff_id
    exact (hf : ContMDiff _ _ _ _).comp hincl
  set sec : ℝ → E := fun v : ℝ => fderiv ℝ (fun w : ℝ => extChartAt I α (f w v)) s (1 : ℝ)
    with hsec
  have hsec_cdiff : ContDiffAt ℝ (7 : ℕ) sec t₀ := by
    have hsrc0 : f s t₀ ∈ (chartAt H α).source := by rw [hα]; exact mem_chart_source H (f s t₀)
    have hjoint : ContDiffAt ℝ (8 : ℕ)
        (Function.uncurry (fun v w : ℝ => extChartAt I α (f w v))) (t₀, s) := by
      have h := chartPulled_contDiffAt_infty (I := I) f hf α s t₀ hsrc0
      have hswap : ContDiffAt ℝ (8 : ℕ)
          ((fun p : ℝ × ℝ => extChartAt I α (f p.1 p.2)) ∘ (fun q : ℝ × ℝ => (q.2, q.1)))
          (t₀, s) :=
        h.comp (t₀, s) ((contDiffAt_snd).prodMk (contDiffAt_fst))
      exact hswap
    have hgs : ContDiffAt ℝ (7 : ℕ) (fun _ : ℝ => s) t₀ := contDiffAt_const
    have hpartial : ContDiffAt ℝ (7 : ℕ)
        (fun v : ℝ => fderiv ℝ (fun w : ℝ => extChartAt I α (f w v)) ((fun _ : ℝ => s) v)) t₀ :=
      ContDiffAt.fderiv (𝕜 := ℝ)
        (f := fun v w : ℝ => extChartAt I α (f w v)) (g := fun _ : ℝ => s)
        hjoint hgs (by exact_mod_cast (by norm_num : (7 : ℕ) + 1 ≤ 8))
    exact (ContinuousLinearMap.apply ℝ E (1 : ℝ)).contDiff.contDiffAt.comp t₀ hpartial
  have hopen : IsOpen {v : ℝ | f s v ∈ (chartAt H α).source} :=
    hslice_s.continuous.isOpen_preimage _ (chartAt H α).open_source
  have h0 : t₀ ∈ {v : ℝ | f s v ∈ (chartAt H α).source} := by
    change f s t₀ ∈ (chartAt H α).source; rw [hα]; exact mem_chart_source H (f s t₀)
  have heq : (chartRepAt (I := I) (fun v : ℝ => f s v)
      (fun v : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f w v) s (1 : ℝ)) t₀)
        =ᶠ[𝓝 t₀] sec := by
    filter_upwards [hopen.mem_nhds h0] with v hv
    have hsrc : (fun w : ℝ => f w v) s ∈ (chartAt H α).source := hv
    have hbridge := MFDerivAlongCurve.chartCoord_mfderiv_along_curve_eq_fderiv_of_mdifferentiableAt
      (I := I) (M := M) (γ := fun w : ℝ => f w v) ((hslice_v v).mdifferentiableAt (by norm_num)) α hsrc
    change (trivializationAt E (TangentSpace I) ((fun v : ℝ => f s v) t₀)).continuousLinearMapAt ℝ
        ((fun v : ℝ => f s v) v) (mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f w v) s (1 : ℝ)) = sec v
    rw [hsec, show (fun v : ℝ => f s v) t₀ = α from hα.symm]
    have hcompfun : ((extChartAt I α) ∘ (fun w : ℝ => f w v))
        = (fun w : ℝ => extChartAt I α (f w v)) := rfl
    rw [hcompfun] at hbridge
    exact hbridge
  exact (heq.differentiableAt_iff).mpr (hsec_cdiff.differentiableAt (by simp))

open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong in

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma slice_transverseVelocity_chartRep_differentiableAt
    (_g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M)
    (hf : IsSmoothVariation (I := I) f) (v : ℝ) :
    DifferentiableAt ℝ
      (chartRepAt (I := I) (fun u : ℝ => f u v)
        (fun u : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f w v) u (1 : ℝ)) 0) 0 := by
  classical
  set α : M := f 0 v with hα
  have htransverse : ContMDiff (𝓘(ℝ, ℝ)) I (8 : ℕ) (fun u : ℝ => f u v) := by
    have hincl : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (8 : ℕ) (fun u : ℝ => (u, v)) :=
      contMDiff_id.prodMk contMDiff_const
    exact (hf : ContMDiff _ _ _ _).comp hincl
  set sec : ℝ → E := fun u : ℝ => fderiv ℝ (fun w : ℝ => extChartAt I α (f w v)) u (1 : ℝ)
    with hsec
  have hchartcurve_cdiff : ContDiffAt ℝ (8 : ℕ) (fun w : ℝ => extChartAt I α (f w v)) 0 := by
    have hext : ContMDiffAt I 𝓘(ℝ, E) (8 : ℕ) (extChartAt I α) (f 0 v) :=
      contMDiffAt_extChartAt (I := I) (x := α)
    have hcomp : ContMDiffAt (𝓘(ℝ, ℝ)) 𝓘(ℝ, E) (8 : ℕ) (fun w : ℝ => extChartAt I α (f w v)) 0 :=
      hext.comp 0 htransverse.contMDiffAt
    exact contMDiffAt_iff_contDiffAt.mp hcomp
  have hsec_cdiff : ContDiffAt ℝ (7 : ℕ) sec 0 := by
    have hfd : ContDiffAt ℝ (7 : ℕ) (fderiv ℝ (fun w : ℝ => extChartAt I α (f w v))) 0 :=
      hchartcurve_cdiff.fderiv_right (by exact_mod_cast (by norm_num : (7 : ℕ) + 1 ≤ 8))
    have heval : ContDiffAt ℝ (7 : ℕ)
        (fun u : ℝ => (ContinuousLinearMap.apply ℝ E (1 : ℝ))
          (fderiv ℝ (fun w : ℝ => extChartAt I α (f w v)) u)) 0 :=
      (ContinuousLinearMap.apply ℝ E (1 : ℝ)).contDiff.contDiffAt.comp 0 hfd
    exact heval
  have hopen : IsOpen {u : ℝ | f u v ∈ (chartAt H α).source} :=
    htransverse.continuous.isOpen_preimage _ (chartAt H α).open_source
  have h0 : (0 : ℝ) ∈ {u : ℝ | f u v ∈ (chartAt H α).source} := by
    change f 0 v ∈ (chartAt H α).source; rw [hα]; exact mem_chart_source H (f 0 v)
  have heq : (chartRepAt (I := I) (fun u : ℝ => f u v)
      (fun u : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f w v) u (1 : ℝ)) 0)
        =ᶠ[𝓝 (0 : ℝ)] sec := by
    filter_upwards [hopen.mem_nhds h0] with u hu
    have hsrc : (fun w : ℝ => f w v) u ∈ (chartAt H α).source := hu
    have hbridge := MFDerivAlongCurve.chartCoord_mfderiv_along_curve_eq_fderiv_of_mdifferentiableAt
      (I := I) (M := M) (γ := fun w : ℝ => f w v) (htransverse.mdifferentiableAt (by norm_num)) α hsrc
    change (trivializationAt E (TangentSpace I) ((fun u : ℝ => f u v) 0)).continuousLinearMapAt ℝ
        ((fun u : ℝ => f u v) u) (mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f w v) u (1 : ℝ)) = sec u
    rw [hsec, show (fun u : ℝ => f u v) 0 = α from hα.symm]
    have hcompfun : ((extChartAt I α) ∘ (fun w : ℝ => f w v))
        = (fun w : ℝ => extChartAt I α (f w v)) := rfl
    rw [hcompfun] at hbridge
    exact hbridge
  exact (heq.differentiableAt_iff).mpr (hsec_cdiff.differentiableAt (by simp))

open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong in

omit [SigmaCompactSpace M] in
theorem commute_ds_dt_curvature_innerS
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M)
    (hf : IsSmoothVariation (I := I) f) (t : ℝ)
    (houterL : DifferentiableAt ℝ (chartRepAt (I := I) (fun s : ℝ => f s t)
        (fun s : ℝ => covDerivAlong (I := I) g (fun v : ℝ => f s v)
          (fun v : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f w v) s (1 : ℝ)) t) 0) 0)
    (houterR : DifferentiableAt ℝ (chartRepAt (I := I) (fun v : ℝ => f 0 v)
        (fun v : ℝ => covDerivAlong (I := I) g (fun u : ℝ => f u v)
          (fun u : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f w v) u (1 : ℝ)) 0) t) t) :
    covDerivAlong (I := I) g (fun s : ℝ => f s t)
        (fun s : ℝ => covDerivAlong (I := I) g (fun v : ℝ => f s v)
          (fun v : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f w v) s (1 : ℝ)) t) 0
      - covDerivAlong (I := I) g (fun v : ℝ => f 0 v)
        (fun v : ℝ => covDerivAlong (I := I) g (fun u : ℝ => f u v)
          (fun u : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f w v) u (1 : ℝ)) 0) t
      = (DifferentialGeometry.Integral.Connection.riemannOp
          (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g) (f 0 t))
          (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u t) 0 (1 : ℝ))
          (mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f 0 w) t (1 : ℝ))
          (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u t) 0 (1 : ℝ)) := by
  classical
  set β : M := f 0 t with hβ
  have hslice_u : ∀ s : ℝ, ContMDiff (𝓘(ℝ, ℝ)) I (8 : ℕ) (fun w : ℝ => f s w) := by
    intro s
    have hincl : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (8 : ℕ) (fun w : ℝ => (s, w)) :=
      contMDiff_const.prodMk contMDiff_id
    exact (hf : ContMDiff _ _ _ _).comp hincl
  have hslice_v : ∀ v : ℝ, ContMDiff (𝓘(ℝ, ℝ)) I (8 : ℕ) (fun w : ℝ => f w v) := by
    intro v
    have hincl : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (8 : ℕ) (fun w : ℝ => (w, v)) :=
      contMDiff_id.prodMk contMDiff_const
    exact (hf : ContMDiff _ _ _ _).comp hincl
  have htransverse : ContMDiff (𝓘(ℝ, ℝ)) I (8 : ℕ) (fun s : ℝ => f s t) := hslice_v t
  have hcentral : ContMDiff (𝓘(ℝ, ℝ)) I (8 : ℕ) (fun v : ℝ => f 0 v) := hslice_u 0
  set velS : ℝ → ℝ → E :=
    fun s v => mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f w v) s (1 : ℝ) with hvelS
  set Y : ℝ → ℝ → E := fun u v =>
    (trivializationAt E (TangentSpace I) β).continuousLinearMapAt ℝ (f u v) (velS u v) with hY
  have hY_chartRepAtBase_u : ∀ u : ℝ,
      (fun v : ℝ => Y u v)
        = chartRepAtBase (I := I) β (fun w : ℝ => f u w) (fun w : ℝ => velS u w) := by
    intro u; funext v; rw [hY, chartRepAtBase_apply]
  have hY_chartRepAtBase_v : ∀ v : ℝ,
      (fun u : ℝ => Y u v)
        = chartRepAtBase (I := I) β (fun w : ℝ => f w v) (fun w : ℝ => velS w v) := by
    intro v; funext u; rw [hY, chartRepAtBase_apply]
  have hY_C2 : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Y p.1 p.2) (0, t) :=
    chartCoord_transverseVelocity_contDiffAt (I := I) f hf t
  have hfixed := chartCovDerivAlong_commutator_eq_riemannOp_on_variation (I := I) g f hf Y 0 t hY_C2
  have hsrcβ : f 0 t ∈ (chartAt H β).source := by rw [hβ]; exact mem_chart_source H (f 0 t)
  have hopenL : IsOpen {s : ℝ | f s t ∈ (chartAt H β).source} :=
    htransverse.continuous.isOpen_preimage _ (chartAt H β).open_source
  have h0L : (0 : ℝ) ∈ {s : ℝ | f s t ∈ (chartAt H β).source} := hsrcβ
  have hopenR : IsOpen {v : ℝ | f 0 v ∈ (chartAt H β).source} :=
    hcentral.continuous.isOpen_preimage _ (chartAt H β).open_source
  have h0R : t ∈ {v : ℝ | f 0 v ∈ (chartAt H β).source} := hsrcβ
  have hinnerL_diff : ∀ s : ℝ, DifferentiableAt ℝ
      (chartRepAt (I := I) (fun v : ℝ => f s v) (fun v : ℝ => velS s v) t) t := fun s =>
    slice_transverseField_longitudinal_chartRep_differentiableAt (I := I) g f hf s t
  have hinnerL : ∀ s : ℝ, f s t ∈ (chartAt H β).source →
      chartCovDerivAlong (I := I) g β (fun v : ℝ => f s v) (fun v : ℝ => Y s v) t
        = (trivializationAt E (TangentSpace I) β).continuousLinearMapAt ℝ (f s t)
            (covDerivAlong (I := I) g (fun v : ℝ => f s v) (fun v : ℝ => velS s v) t) := by
    intro s hs
    rw [hY_chartRepAtBase_u s]
    exact (chartCoord_covDerivAlong_eq_chartCovDerivAlong_chartRepAtBase (I := I) (by norm_num) g
      (fun w : ℝ => f s w) (fun w : ℝ => velS s w) t β (hslice_u s) hs
      (hinnerL_diff s)).symm
  have hinnerR_diff : ∀ v : ℝ, DifferentiableAt ℝ
      (chartRepAt (I := I) (fun u : ℝ => f u v) (fun u : ℝ => velS u v) 0) 0 := fun v =>
    slice_transverseVelocity_chartRep_differentiableAt (I := I) g f hf v
  have hinnerR : ∀ v : ℝ, f 0 v ∈ (chartAt H β).source →
      chartCovDerivAlong (I := I) g β (fun u : ℝ => f u v) (fun u : ℝ => Y u v) 0
        = (trivializationAt E (TangentSpace I) β).continuousLinearMapAt ℝ (f 0 v)
            (covDerivAlong (I := I) g (fun u : ℝ => f u v) (fun u : ℝ => velS u v) 0) := by
    intro v hv
    rw [hY_chartRepAtBase_v v]
    exact (chartCoord_covDerivAlong_eq_chartCovDerivAlong_chartRepAtBase (I := I) (by norm_num) g
      (fun w : ℝ => f w v) (fun w : ℝ => velS w v) 0 β (hslice_v v) hv (hinnerR_diff v)).symm
  set innerL : ∀ s : ℝ, TangentSpace I ((fun s : ℝ => f s t) s) :=
    fun s => covDerivAlong (I := I) g (fun v : ℝ => f s v) (fun v : ℝ => velS s v) t with hinnerL_def
  set innerR : ∀ v : ℝ, TangentSpace I ((fun v : ℝ => f 0 v) v) :=
    fun v => covDerivAlong (I := I) g (fun u : ℝ => f u v) (fun u : ℝ => velS u v) 0 with hinnerR_def
  have hrepL_eq : chartRepAt (I := I) (fun s : ℝ => f s t) innerL 0
      =ᶠ[𝓝 (0 : ℝ)]
        (fun s : ℝ => chartCovDerivAlong (I := I) g β (fun v : ℝ => f s v) (fun v : ℝ => Y s v) t) := by
    filter_upwards [hopenL.mem_nhds h0L] with s hs
    rw [chartRepAt_apply]
    change (trivializationAt E (TangentSpace I) β).continuousLinearMapAt ℝ (f s t) (innerL s) = _
    rw [hinnerL_def, ← hinnerL s hs]
  have hrepR_eq : chartRepAt (I := I) (fun v : ℝ => f 0 v) innerR t
      =ᶠ[𝓝 t]
        (fun v : ℝ => chartCovDerivAlong (I := I) g β (fun u : ℝ => f u v) (fun u : ℝ => Y u v) 0) := by
    filter_upwards [hopenR.mem_nhds h0R] with v hv
    rw [chartRepAt_apply]
    change (trivializationAt E (TangentSpace I) β).continuousLinearMapAt ℝ (f 0 v) (innerR v) = _
    rw [hinnerR_def, ← hinnerR v hv]
  have houterL_bridge :
      (trivializationAt E (TangentSpace I) β).continuousLinearMapAt ℝ ((fun s : ℝ => f s t) 0)
          (covDerivAlong (I := I) g (fun s : ℝ => f s t) innerL 0)
        = chartCovDerivAlong (I := I) g β (fun s : ℝ => f s t)
            (fun s : ℝ => chartCovDerivAlong (I := I) g β (fun v : ℝ => f s v)
              (fun v : ℝ => Y s v) t) 0 := by
    rw [chartCoord_covDerivAlong_eq_chartCovDerivAlong_chartRepAtBase (I := I) (by norm_num) g
      (fun s : ℝ => f s t) innerL 0 β htransverse (by rw [hβ] at hsrcβ ⊢; exact hsrcβ) houterL]
    rw [show chartRepAtBase (I := I) β (fun s : ℝ => f s t) innerL
        = chartRepAt (I := I) (fun s : ℝ => f s t) innerL 0 from
      chartRepAtBase_foot (I := I) (fun s : ℝ => f s t) innerL 0]
    rw [chartCovDerivAlong_def, chartCovDerivAlong_def, hrepL_eq.deriv_eq, hrepL_eq.eq_of_nhds]
  have houterR_bridge :
      (trivializationAt E (TangentSpace I) β).continuousLinearMapAt ℝ ((fun v : ℝ => f 0 v) t)
          (covDerivAlong (I := I) g (fun v : ℝ => f 0 v) innerR t)
        = chartCovDerivAlong (I := I) g β (fun v : ℝ => f 0 v)
            (fun v : ℝ => chartCovDerivAlong (I := I) g β (fun u : ℝ => f u v)
              (fun u : ℝ => Y u v) 0) t := by
    rw [chartCoord_covDerivAlong_eq_chartCovDerivAlong_chartRepAtBase (I := I) (by norm_num) g
      (fun v : ℝ => f 0 v) innerR t β hcentral (by rw [hβ] at hsrcβ ⊢; exact hsrcβ) houterR]
    rw [show chartRepAtBase (I := I) β (fun v : ℝ => f 0 v) innerR
        = chartRepAt (I := I) (fun v : ℝ => f 0 v) innerR t from
      chartRepAtBase_foot (I := I) (fun v : ℝ => f 0 v) innerR t]
    rw [chartCovDerivAlong_def, chartCovDerivAlong_def, hrepR_eq.deriv_eq, hrepR_eq.eq_of_nhds]
  have hfootOuterL : (fun s : ℝ => f s t) 0 = β := by rw [hβ]
  have hfootOuterR : (fun v : ℝ => f 0 v) t = β := by rw [hβ]
  have hmemβ : β ∈ (trivializationAt E (TangentSpace I) β).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) β
  have hLeft : covDerivAlong (I := I) g (fun s : ℝ => f s t) innerL 0
      = (trivializationAt E (TangentSpace I) β).symmL ℝ β
          (chartCovDerivAlong (I := I) g β (fun s : ℝ => f s t)
            (fun s : ℝ => chartCovDerivAlong (I := I) g β (fun v : ℝ => f s v)
              (fun v : ℝ => Y s v) t) 0) := by
    rw [← houterL_bridge, hfootOuterL]
    exact ((trivializationAt E (TangentSpace I) β).symmL_continuousLinearMapAt
      (R := ℝ) hmemβ _).symm
  have hRight : covDerivAlong (I := I) g (fun v : ℝ => f 0 v) innerR t
      = (trivializationAt E (TangentSpace I) β).symmL ℝ β
          (chartCovDerivAlong (I := I) g β (fun v : ℝ => f 0 v)
            (fun v : ℝ => chartCovDerivAlong (I := I) g β (fun u : ℝ => f u v)
              (fun u : ℝ => Y u v) 0) t) := by
    rw [← houterR_bridge, hfootOuterR]
    exact ((trivializationAt E (TangentSpace I) β).symmL_continuousLinearMapAt
      (R := ℝ) hmemβ _).symm
  change covDerivAlong (I := I) g (fun s : ℝ => f s t) innerL 0
      - covDerivAlong (I := I) g (fun v : ℝ => f 0 v) innerR t = _
  rw [hLeft, hRight, ← map_sub]
  rw [hfixed]
  have hfoot_src : f 0 t ∈ (chartAt H (f 0 t)).source := mem_chart_source H (f 0 t)
  have hfoot_clm : ∀ x : TangentSpace I (f 0 t),
      (trivializationAt E (TangentSpace I) (f 0 t)).continuousLinearMapAt ℝ (f 0 t) x = x := by
    intro x
    rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core (I := I) hfoot_src]
    exact (tangentBundleCore I M).coordChange_self (achart H (f 0 t)) (f 0 t)
      (mem_achart_source H (f 0 t)) x
  have hfoot_symmL : ∀ x : TangentSpace I (f 0 t),
      (trivializationAt E (TangentSpace I) (f 0 t)).symmL ℝ (f 0 t) x = x := by
    intro x
    rw [TangentBundle.symmL_trivializationAt_eq_core (I := I) hfoot_src]
    exact (tangentBundleCore I M).coordChange_self (achart H (f 0 t)) (f 0 t)
      (mem_achart_source H (f 0 t)) x
  have hslotS : (fderiv ℝ (fun u : ℝ => extChartAt I (f 0 t) (f u t)) 0 (1 : ℝ))
      = (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u t) 0 (1 : ℝ) : E) := by
    have hbridge := MFDerivAlongCurve.chartCoord_mfderiv_along_curve_eq_fderiv_of_mdifferentiableAt
      (I := I) (M := M) (γ := fun u : ℝ => f u t) ((hslice_v t).mdifferentiableAt (by norm_num)) (f 0 t)
      (by change f 0 t ∈ (chartAt H (f 0 t)).source; exact hfoot_src)
    have hcompfun : ((extChartAt I (f 0 t)) ∘ (fun u : ℝ => f u t))
        = (fun u : ℝ => extChartAt I (f 0 t) (f u t)) := rfl
    rw [hcompfun, hfoot_clm] at hbridge
    exact hbridge.symm
  have hslotT : (fderiv ℝ (fun v : ℝ => extChartAt I (f 0 t) (f 0 v)) t (1 : ℝ))
      = (mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f 0 w) t (1 : ℝ) : E) := by
    have hbridge := MFDerivAlongCurve.chartCoord_mfderiv_along_curve_eq_fderiv_of_mdifferentiableAt
      (I := I) (M := M) (γ := fun w : ℝ => f 0 w) ((hslice_u 0).mdifferentiableAt (by norm_num)) (f 0 t)
      (by change f 0 t ∈ (chartAt H (f 0 t)).source; exact hfoot_src)
    have hcompfun : ((extChartAt I (f 0 t)) ∘ (fun w : ℝ => f 0 w))
        = (fun w : ℝ => extChartAt I (f 0 t) (f 0 w)) := rfl
    rw [hcompfun, hfoot_clm] at hbridge
    exact hbridge.symm
  have hYft : Y 0 t = (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u t) 0 (1 : ℝ) : E) := by
    rw [hY]
    change (trivializationAt E (TangentSpace I) β).continuousLinearMapAt ℝ (f 0 t) (velS 0 t)
      = mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u t) 0 (1 : ℝ)
    rw [hβ, hfoot_clm]
  rw [hslotS, hslotT, hYft]
  rw [show (trivializationAt E (TangentSpace I) β).symmL ℝ β
        = (trivializationAt E (TangentSpace I) (f 0 t)).symmL ℝ (f 0 t) from by rw [hβ]]
  rw [hfoot_symmL]

open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong in

omit [SigmaCompactSpace M] in
theorem commute_ds_dt_curvature
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M)
    (hf : IsSmoothVariation (I := I) f) (t : ℝ)
    (houterL : DifferentiableAt ℝ (chartRepAt (I := I) (fun s : ℝ => f s t)
        (fun s : ℝ => covDerivAlong (I := I) g (fun v : ℝ => f s v)
          (fun v : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f s w) v (1 : ℝ)) t) 0) 0)
    (houterR : DifferentiableAt ℝ (chartRepAt (I := I) (fun v : ℝ => f 0 v)
        (fun v : ℝ => covDerivAlong (I := I) g (fun u : ℝ => f u v)
          (fun u : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f u w) v (1 : ℝ)) 0) t) t) :
    covDerivAlong (I := I) g (fun s : ℝ => f s t)
        (fun s : ℝ => covDerivAlong (I := I) g (fun v : ℝ => f s v)
          (fun v : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f s w) v (1 : ℝ)) t) 0
      - covDerivAlong (I := I) g (fun v : ℝ => f 0 v)
        (fun v : ℝ => covDerivAlong (I := I) g (fun u : ℝ => f u v)
          (fun u : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f u w) v (1 : ℝ)) 0) t
      = (DifferentialGeometry.Integral.Connection.riemannOp
          (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g) (f 0 t))
          (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u t) 0 (1 : ℝ))
          (mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f 0 w) t (1 : ℝ))
          (mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f 0 w) t (1 : ℝ)) := by
  classical
  set β : M := f 0 t with hβ
  have hslice_u : ∀ s : ℝ, ContMDiff (𝓘(ℝ, ℝ)) I (8 : ℕ) (fun w : ℝ => f s w) := by
    intro s
    have hincl : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (8 : ℕ) (fun w : ℝ => (s, w)) :=
      contMDiff_const.prodMk contMDiff_id
    exact (hf : ContMDiff _ _ _ _).comp hincl
  have hslice_v : ∀ v : ℝ, ContMDiff (𝓘(ℝ, ℝ)) I (8 : ℕ) (fun w : ℝ => f w v) := by
    intro v
    have hincl : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (8 : ℕ) (fun w : ℝ => (w, v)) :=
      contMDiff_id.prodMk contMDiff_const
    exact (hf : ContMDiff _ _ _ _).comp hincl
  have htransverse : ContMDiff (𝓘(ℝ, ℝ)) I (8 : ℕ) (fun s : ℝ => f s t) := hslice_v t
  have hcentral : ContMDiff (𝓘(ℝ, ℝ)) I (8 : ℕ) (fun v : ℝ => f 0 v) := hslice_u 0
  set velT : ℝ → ℝ → E :=
    fun s v => mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f s w) v (1 : ℝ) with hvelT
  set Y : ℝ → ℝ → E := fun u v =>
    (trivializationAt E (TangentSpace I) β).continuousLinearMapAt ℝ (f u v) (velT u v) with hY
  have hY_chartRepAtBase_u : ∀ u : ℝ,
      (fun v : ℝ => Y u v)
        = chartRepAtBase (I := I) β (fun w : ℝ => f u w) (fun w : ℝ => velT u w) := by
    intro u; funext v; rw [hY, chartRepAtBase_apply]
  have hY_chartRepAtBase_v : ∀ v : ℝ,
      (fun u : ℝ => Y u v)
        = chartRepAtBase (I := I) β (fun w : ℝ => f w v) (fun w : ℝ => velT w v) := by
    intro v; funext u; rw [hY, chartRepAtBase_apply]
  have hY_C2 : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Y p.1 p.2) (0, t) :=
    chartCoord_longitudinalVelocity_contDiffAt (I := I) f hf t
  have hfixed := chartCovDerivAlong_commutator_eq_riemannOp_on_variation (I := I) g f hf Y 0 t hY_C2
  have hsrcβ : f 0 t ∈ (chartAt H β).source := by rw [hβ]; exact mem_chart_source H (f 0 t)
  have hopenL : IsOpen {s : ℝ | f s t ∈ (chartAt H β).source} :=
    htransverse.continuous.isOpen_preimage _ (chartAt H β).open_source
  have h0L : (0 : ℝ) ∈ {s : ℝ | f s t ∈ (chartAt H β).source} := hsrcβ
  have hopenR : IsOpen {v : ℝ | f 0 v ∈ (chartAt H β).source} :=
    hcentral.continuous.isOpen_preimage _ (chartAt H β).open_source
  have h0R : t ∈ {v : ℝ | f 0 v ∈ (chartAt H β).source} := hsrcβ
  have hinnerL : ∀ s : ℝ, f s t ∈ (chartAt H β).source →
      chartCovDerivAlong (I := I) g β (fun v : ℝ => f s v) (fun v : ℝ => Y s v) t
        = (trivializationAt E (TangentSpace I) β).continuousLinearMapAt ℝ (f s t)
            (covDerivAlong (I := I) g (fun v : ℝ => f s v) (fun v : ℝ => velT s v) t) := by
    intro s hs
    rw [hY_chartRepAtBase_u s]
    exact (chartCoord_covDerivAlong_eq_chartCovDerivAlong_chartRepAtBase (I := I) (by norm_num) g
      (fun w : ℝ => f s w) (fun w : ℝ => velT s w) t β (hslice_u s) hs
      (slice_velocityField_chartRep_differentiableAt (I := I) g f hf s t)).symm
  have hinnerR_diff : ∀ v : ℝ, DifferentiableAt ℝ
      (chartRepAt (I := I) (fun u : ℝ => f u v) (fun u : ℝ => velT u v) 0) 0 := fun v =>
    slice_longitudinalField_transverse_chartRep_differentiableAt (I := I) g f hf v
  have hinnerR : ∀ v : ℝ, f 0 v ∈ (chartAt H β).source →
      chartCovDerivAlong (I := I) g β (fun u : ℝ => f u v) (fun u : ℝ => Y u v) 0
        = (trivializationAt E (TangentSpace I) β).continuousLinearMapAt ℝ (f 0 v)
            (covDerivAlong (I := I) g (fun u : ℝ => f u v) (fun u : ℝ => velT u v) 0) := by
    intro v hv
    rw [hY_chartRepAtBase_v v]
    exact (chartCoord_covDerivAlong_eq_chartCovDerivAlong_chartRepAtBase (I := I) (by norm_num) g
      (fun w : ℝ => f w v) (fun w : ℝ => velT w v) 0 β (hslice_v v) hv (hinnerR_diff v)).symm
  set innerL : ∀ s : ℝ, TangentSpace I ((fun s : ℝ => f s t) s) :=
    fun s => covDerivAlong (I := I) g (fun v : ℝ => f s v) (fun v : ℝ => velT s v) t with hinnerL_def
  set innerR : ∀ v : ℝ, TangentSpace I ((fun v : ℝ => f 0 v) v) :=
    fun v => covDerivAlong (I := I) g (fun u : ℝ => f u v) (fun u : ℝ => velT u v) 0 with hinnerR_def
  have hrepL_eq : chartRepAt (I := I) (fun s : ℝ => f s t) innerL 0
      =ᶠ[𝓝 (0 : ℝ)]
        (fun s : ℝ => chartCovDerivAlong (I := I) g β (fun v : ℝ => f s v) (fun v : ℝ => Y s v) t) := by
    filter_upwards [hopenL.mem_nhds h0L] with s hs
    rw [chartRepAt_apply]
    change (trivializationAt E (TangentSpace I) β).continuousLinearMapAt ℝ (f s t) (innerL s) = _
    rw [hinnerL_def, ← hinnerL s hs]
  have hrepR_eq : chartRepAt (I := I) (fun v : ℝ => f 0 v) innerR t
      =ᶠ[𝓝 t]
        (fun v : ℝ => chartCovDerivAlong (I := I) g β (fun u : ℝ => f u v) (fun u : ℝ => Y u v) 0) := by
    filter_upwards [hopenR.mem_nhds h0R] with v hv
    rw [chartRepAt_apply]
    change (trivializationAt E (TangentSpace I) β).continuousLinearMapAt ℝ (f 0 v) (innerR v) = _
    rw [hinnerR_def, ← hinnerR v hv]
  have houterL_bridge :
      (trivializationAt E (TangentSpace I) β).continuousLinearMapAt ℝ ((fun s : ℝ => f s t) 0)
          (covDerivAlong (I := I) g (fun s : ℝ => f s t) innerL 0)
        = chartCovDerivAlong (I := I) g β (fun s : ℝ => f s t)
            (fun s : ℝ => chartCovDerivAlong (I := I) g β (fun v : ℝ => f s v)
              (fun v : ℝ => Y s v) t) 0 := by
    rw [chartCoord_covDerivAlong_eq_chartCovDerivAlong_chartRepAtBase (I := I) (by norm_num) g
      (fun s : ℝ => f s t) innerL 0 β htransverse (by rw [hβ] at hsrcβ ⊢; exact hsrcβ) houterL]
    rw [show chartRepAtBase (I := I) β (fun s : ℝ => f s t) innerL
        = chartRepAt (I := I) (fun s : ℝ => f s t) innerL 0 from
      chartRepAtBase_foot (I := I) (fun s : ℝ => f s t) innerL 0]
    rw [chartCovDerivAlong_def, chartCovDerivAlong_def, hrepL_eq.deriv_eq, hrepL_eq.eq_of_nhds]
  have houterR_bridge :
      (trivializationAt E (TangentSpace I) β).continuousLinearMapAt ℝ ((fun v : ℝ => f 0 v) t)
          (covDerivAlong (I := I) g (fun v : ℝ => f 0 v) innerR t)
        = chartCovDerivAlong (I := I) g β (fun v : ℝ => f 0 v)
            (fun v : ℝ => chartCovDerivAlong (I := I) g β (fun u : ℝ => f u v)
              (fun u : ℝ => Y u v) 0) t := by
    rw [chartCoord_covDerivAlong_eq_chartCovDerivAlong_chartRepAtBase (I := I) (by norm_num) g
      (fun v : ℝ => f 0 v) innerR t β hcentral (by rw [hβ] at hsrcβ ⊢; exact hsrcβ) houterR]
    rw [show chartRepAtBase (I := I) β (fun v : ℝ => f 0 v) innerR
        = chartRepAt (I := I) (fun v : ℝ => f 0 v) innerR t from
      chartRepAtBase_foot (I := I) (fun v : ℝ => f 0 v) innerR t]
    rw [chartCovDerivAlong_def, chartCovDerivAlong_def, hrepR_eq.deriv_eq, hrepR_eq.eq_of_nhds]
  have hfootOuterL : (fun s : ℝ => f s t) 0 = β := by rw [hβ]
  have hfootOuterR : (fun v : ℝ => f 0 v) t = β := by rw [hβ]
  have hmemβ : β ∈ (trivializationAt E (TangentSpace I) β).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) β
  have hLeft : covDerivAlong (I := I) g (fun s : ℝ => f s t) innerL 0
      = (trivializationAt E (TangentSpace I) β).symmL ℝ β
          (chartCovDerivAlong (I := I) g β (fun s : ℝ => f s t)
            (fun s : ℝ => chartCovDerivAlong (I := I) g β (fun v : ℝ => f s v)
              (fun v : ℝ => Y s v) t) 0) := by
    rw [← houterL_bridge, hfootOuterL]
    exact ((trivializationAt E (TangentSpace I) β).symmL_continuousLinearMapAt
      (R := ℝ) hmemβ _).symm
  have hRight : covDerivAlong (I := I) g (fun v : ℝ => f 0 v) innerR t
      = (trivializationAt E (TangentSpace I) β).symmL ℝ β
          (chartCovDerivAlong (I := I) g β (fun v : ℝ => f 0 v)
            (fun v : ℝ => chartCovDerivAlong (I := I) g β (fun u : ℝ => f u v)
              (fun u : ℝ => Y u v) 0) t) := by
    rw [← houterR_bridge, hfootOuterR]
    exact ((trivializationAt E (TangentSpace I) β).symmL_continuousLinearMapAt
      (R := ℝ) hmemβ _).symm
  change covDerivAlong (I := I) g (fun s : ℝ => f s t) innerL 0
      - covDerivAlong (I := I) g (fun v : ℝ => f 0 v) innerR t = _
  rw [hLeft, hRight, ← map_sub]
  rw [hfixed]
  have hfoot_src : f 0 t ∈ (chartAt H (f 0 t)).source := mem_chart_source H (f 0 t)
  have hfoot_clm : ∀ x : TangentSpace I (f 0 t),
      (trivializationAt E (TangentSpace I) (f 0 t)).continuousLinearMapAt ℝ (f 0 t) x = x := by
    intro x
    rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core (I := I) hfoot_src]
    exact (tangentBundleCore I M).coordChange_self (achart H (f 0 t)) (f 0 t)
      (mem_achart_source H (f 0 t)) x
  have hfoot_symmL : ∀ x : TangentSpace I (f 0 t),
      (trivializationAt E (TangentSpace I) (f 0 t)).symmL ℝ (f 0 t) x = x := by
    intro x
    rw [TangentBundle.symmL_trivializationAt_eq_core (I := I) hfoot_src]
    exact (tangentBundleCore I M).coordChange_self (achart H (f 0 t)) (f 0 t)
      (mem_achart_source H (f 0 t)) x
  have hslotS : (fderiv ℝ (fun u : ℝ => extChartAt I (f 0 t) (f u t)) 0 (1 : ℝ))
      = (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u t) 0 (1 : ℝ) : E) := by
    have hbridge := MFDerivAlongCurve.chartCoord_mfderiv_along_curve_eq_fderiv_of_mdifferentiableAt
      (I := I) (M := M) (γ := fun u : ℝ => f u t) ((hslice_v t).mdifferentiableAt (by norm_num)) (f 0 t)
      (by change f 0 t ∈ (chartAt H (f 0 t)).source; exact hfoot_src)
    have hcompfun : ((extChartAt I (f 0 t)) ∘ (fun u : ℝ => f u t))
        = (fun u : ℝ => extChartAt I (f 0 t) (f u t)) := rfl
    rw [hcompfun, hfoot_clm] at hbridge
    exact hbridge.symm
  have hslotT : (fderiv ℝ (fun v : ℝ => extChartAt I (f 0 t) (f 0 v)) t (1 : ℝ))
      = (mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f 0 w) t (1 : ℝ) : E) := by
    have hbridge := MFDerivAlongCurve.chartCoord_mfderiv_along_curve_eq_fderiv_of_mdifferentiableAt
      (I := I) (M := M) (γ := fun w : ℝ => f 0 w) ((hslice_u 0).mdifferentiableAt (by norm_num)) (f 0 t)
      (by change f 0 t ∈ (chartAt H (f 0 t)).source; exact hfoot_src)
    have hcompfun : ((extChartAt I (f 0 t)) ∘ (fun w : ℝ => f 0 w))
        = (fun w : ℝ => extChartAt I (f 0 t) (f 0 w)) := rfl
    rw [hcompfun, hfoot_clm] at hbridge
    exact hbridge.symm
  have hYft : Y 0 t = (mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f 0 w) t (1 : ℝ) : E) := by
    rw [hY]
    change (trivializationAt E (TangentSpace I) β).continuousLinearMapAt ℝ (f 0 t) (velT 0 t)
      = mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f 0 w) t (1 : ℝ)
    rw [hβ, hfoot_clm]
  rw [hslotS, hslotT, hYft]
  rw [show (trivializationAt E (TangentSpace I) β).symmL ℝ β
        = (trivializationAt E (TangentSpace I) (f 0 t)).symmL ℝ (f 0 t) from by rw [hβ]]
  rw [hfoot_symmL]

open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong in

omit [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma covDerivAlong_const_add_shift
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V : ∀ s : ℝ, TangentSpace I (γ s)) (c : ℝ) :
    covDerivAlong (I := I) g (fun a : ℝ => γ (c + a))
        (fun a : ℝ => V (c + a)) 0
      = covDerivAlong (I := I) g γ V c := by
  classical
  have hfoot : γ (c + 0) = γ c := by rw [add_zero]
  have hrep : chartRepAt (I := I) (fun a : ℝ => γ (c + a)) (fun a : ℝ => V (c + a)) 0
      = (fun a : ℝ => chartRepAt (I := I) γ V c (c + a)) := by
    funext a
    rw [chartRepAt_apply, chartRepAt_apply]
    simp only [add_zero]
  have hcurve : chartCurve (I := I) (γ c) (fun a : ℝ => γ (c + a))
      = (fun a : ℝ => chartCurve (I := I) (γ c) γ (c + a)) := by
    funext a; rw [chartCurve_def, chartCurve_def]
  have hchart : chartCovDerivAlong (I := I) g (γ c) (fun a : ℝ => γ (c + a))
        (chartRepAt (I := I) (fun a : ℝ => γ (c + a)) (fun a : ℝ => V (c + a)) 0) 0
      = chartCovDerivAlong (I := I) g (γ c) γ (chartRepAt (I := I) γ V c) c := by
    rw [chartCovDerivAlong_def, chartCovDerivAlong_def, hrep, hcurve]
    rw [deriv_comp_const_add (chartRepAt (I := I) γ V c) c 0,
        deriv_comp_const_add (chartCurve (I := I) (γ c) γ) c 0]
    simp only [add_zero]
  rw [covDerivAlong_def, covDerivAlong_def]
  rw [hfoot]
  rw [hchart]

open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong in

omit [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma commute_ds_dt_intrinsic_shifted
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M)
    (hf : IsSmoothVariation (I := I) f) (t : ℝ) :
    (fun s : ℝ => covDerivAlong (I := I) g (fun s' : ℝ => f s' t)
        (fun s' : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f s' w) t (1 : ℝ)) s)
      = (fun s : ℝ => covDerivAlong (I := I) g (fun v : ℝ => f s v)
        (fun v : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f w v) s (1 : ℝ)) t) := by
  classical
  funext s
  set fsh : ℝ → ℝ → M := fun a b : ℝ => f (s + a) b with hfsh
  have hfsh_smooth : IsSmoothVariation (I := I) fsh := by
    have hshift : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (8 : ℕ)
        (fun q : ℝ × ℝ => (s + q.1, q.2)) :=
      (contMDiff_const.add contMDiff_fst).prodMk contMDiff_snd
    exact (hf : ContMDiff _ _ _ _).comp hshift
  have hcomm := commute_ds_dt_intrinsic (I := I) g fsh hfsh_smooth t
  have hLHS : covDerivAlong (I := I) g (fun a : ℝ => fsh a t)
        (fun a : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => fsh a u) t (1 : ℝ)) 0
      = covDerivAlong (I := I) g (fun s' : ℝ => f s' t)
        (fun s' : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f s' w) t (1 : ℝ)) s := by
    have hshift := covDerivAlong_const_add_shift (I := I) g (fun s' : ℝ => f s' t)
      (fun s' : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f s' w) t (1 : ℝ)) s
    exact hshift
  have hbaseR : (fun v : ℝ => fsh 0 v) = (fun v : ℝ => f s v) := by funext v; rw [hfsh]; simp
  have hsecR : ∀ v : ℝ, mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => fsh u v) 0 (1 : ℝ)
      = mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f w v) s (1 : ℝ) := by
    intro v
    have hslice_v : ContMDiff (𝓘(ℝ, ℝ)) I (8 : ℕ) (fun w : ℝ => f w v) := by
      have hincl : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (8 : ℕ) (fun w : ℝ => (w, v)) :=
        contMDiff_id.prodMk contMDiff_const
      exact (hf : ContMDiff _ _ _ _).comp hincl
    have hcomp_eq : (fun u : ℝ => fsh u v)
        = (fun w : ℝ => f w v) ∘ (fun u : ℝ => s + u) := by funext u; simp only [hfsh, Function.comp]
    have hψ_mdiff : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) (fun u : ℝ => s + u) 0 := by
      have hcd : ContMDiffAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) ∞ (fun u : ℝ => s + u) 0 := by
        rw [contMDiffAt_iff_contDiffAt]
        exact (contDiffAt_const.add contDiffAt_id)
      exact hcd.mdifferentiableAt (by simp)
    have hφ_mdiff : MDifferentiableAt (𝓘(ℝ, ℝ)) I (fun w : ℝ => f w v) ((fun u : ℝ => s + u) 0) := by
      have hpt : ((fun u : ℝ => s + u) 0) = s := by simp
      rw [hpt]; exact (hslice_v.contMDiffAt).mdifferentiableAt (by simp)
    rw [hcomp_eq, mfderiv_comp 0 hφ_mdiff hψ_mdiff]
    have hderiv : HasDerivAt (fun u : ℝ => s + u) (1 : ℝ) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_add s
    have hψfd : mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) (fun u : ℝ => s + u) 0 (1 : ℝ) = (1 : ℝ) := by
      have heq : mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) (fun u : ℝ => s + u) 0
          = fderiv ℝ (fun u : ℝ => s + u) 0 :=
        mfderiv_eq_fderiv (𝕜 := ℝ) (f := fun u : ℝ => s + u) (x := 0)
      rw [heq]
      change deriv (fun u : ℝ => s + u) 0 = (1 : ℝ)
      exact hderiv.deriv
    rw [ContinuousLinearMap.comp_apply]
    rw [show (mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) (fun u : ℝ => s + u) 0) (1 : ℝ) = (1 : ℝ) from hψfd]
    change mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f w v) (s + 0) (1 : ℝ)
      = mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f w v) s (1 : ℝ)
    rw [add_zero]
  have hRHS : covDerivAlong (I := I) g (fun v : ℝ => fsh 0 v)
        (fun v : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => fsh u v) 0 (1 : ℝ)) t
      = covDerivAlong (I := I) g (fun v : ℝ => f s v)
        (fun v : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f w v) s (1 : ℝ)) t := by
    rw [hbaseR]
    congr 1
    funext v; exact hsecR v
  rw [← hLHS, ← hRHS]
  exact hcomm

open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
  DifferentialGeometry.Integral.DivergenceTheorem in

omit [T2Space M] [SigmaCompactSpace M] in
lemma slice_secondCovDeriv_central_chartRep_differentiableAt
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M)
    (hf : IsSmoothVariation (I := I) f) (t : ℝ) :
    DifferentiableAt ℝ
      (chartRepAt (I := I) (fun v : ℝ => f 0 v)
        (fun v : ℝ => covDerivAlong (I := I) g (fun u : ℝ => f u v)
          (fun u : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f w v) u (1 : ℝ)) 0) t) t := by
  classical
  set β : M := f 0 t with hβ
  have hslice_v : ∀ v : ℝ, ContMDiff (𝓘(ℝ, ℝ)) I (8 : ℕ) (fun w : ℝ => f w v) := by
    intro v
    have hincl : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (8 : ℕ) (fun w : ℝ => (w, v)) :=
      contMDiff_id.prodMk contMDiff_const
    exact (hf : ContMDiff _ _ _ _).comp hincl
  have hcentral : ContMDiff (𝓘(ℝ, ℝ)) I (8 : ℕ) (fun v : ℝ => f 0 v) := by
    have hincl : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (8 : ℕ) (fun v : ℝ => ((0 : ℝ), v)) :=
      contMDiff_const.prodMk contMDiff_id
    exact (hf : ContMDiff _ _ _ _).comp hincl
  set velS : ℝ → ℝ → E :=
    fun u v => mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f w v) u (1 : ℝ) with hvelS
  set Y : ℝ → ℝ → E := fun u v =>
    (trivializationAt E (TangentSpace I) β).continuousLinearMapAt ℝ (f u v) (velS u v) with hY
  have hY_C2 : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Y p.1 p.2) (0, t) :=
    chartCoord_transverseVelocity_contDiffAt (I := I) f hf t
  have hY0_C2 : ContDiffAt ℝ 2 (fun v : ℝ => Y 0 v) t := by
    have hincl : ContDiffAt ℝ 2 (fun v : ℝ => ((0 : ℝ), v)) t :=
      (contDiff_const.prodMk contDiff_id).contDiffAt
    exact hY_C2.comp t hincl
  have hY0_diff : DifferentiableAt ℝ (fun v : ℝ => Y 0 v) t :=
    hY0_C2.differentiableAt (by norm_cast)
  have hsrc0 : f 0 t ∈ (chartAt H β).source := by rw [hβ]; exact mem_chart_source H (f 0 t)
  set uC : ℝ → ℝ → E := fun u v => extChartAt I β (f u v) with huC
  have huC_joint : ContDiffAt ℝ (8 : ℕ) (fun p : ℝ × ℝ => uC p.1 p.2) (0, t) :=
    chartPulled_contDiffAt_infty (I := I) f hf β 0 t hsrc0
  have huC0_diff : DifferentiableAt ℝ (fun v : ℝ => uC 0 v) t := by
    have hincl : ContDiffAt ℝ (8 : ℕ) (fun v : ℝ => ((0 : ℝ), v)) t :=
      (contDiff_const.prodMk contDiff_id).contDiffAt
    exact ((huC_joint.comp t hincl).differentiableAt (by norm_num))
  have hpartialY : HasDerivAt
      (fun v : ℝ => fderiv ℝ (fun u : ℝ => Y u v) 0 (1 : ℝ))
      (fderiv ℝ (fderiv ℝ (fun p : ℝ × ℝ => Y p.1 p.2)) (0, t) (0, 1) (1, 0)) t :=
    Aux2.hasDerivAt_partial_fst Y 0 t hY_C2
  have huC_joint_C2 : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => uC p.1 p.2) (0, t) :=
    huC_joint.of_le (by norm_cast)
  have hpartialU : HasDerivAt
      (fun v : ℝ => fderiv ℝ (fun u : ℝ => uC u v) 0 (1 : ℝ))
      (fderiv ℝ (fderiv ℝ (fun p : ℝ × ℝ => uC p.1 p.2)) (0, t) (0, 1) (1, 0)) t :=
    Aux2.hasDerivAt_partial_fst uC 0 t huC_joint_C2
  have huC0t : uC 0 t = extChartAt I β β := by rw [huC, hβ]
  have hΓ_diff : ∀ i j k : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ (chartChristoffel (I := I) g β i j k) (uC 0 t) := by
    intro i j k
    rw [huC0t]
    exact Aux3.chartChristoffel_differentiableAt_self (I := I) g β i j k
  set Z : ℝ → E := fun v : ℝ =>
    chartCovDerivAlong (I := I) g β (fun u : ℝ => f u v) (fun u : ℝ => Y u v) 0 with hZdef
  have hZ_diff : DifferentiableAt ℝ Z t := by
    have hZeq : Z = (fun v : ℝ => fderiv ℝ (fun u : ℝ => Y u v) 0 (1 : ℝ)
        + chartChristoffelContraction (I := I) g β
            (fderiv ℝ (fun u : ℝ => uC u v) 0 (1 : ℝ)) (Y 0 v) (uC 0 v)) := by
      funext v
      change chartCovDerivAlong (I := I) g β (fun u : ℝ => f u v) (fun u : ℝ => Y u v) 0
        = fderiv ℝ (fun u : ℝ => Y u v) 0 (1 : ℝ)
          + chartChristoffelContraction (I := I) g β
              (fderiv ℝ (fun u : ℝ => uC u v) 0 (1 : ℝ)) (Y 0 v) (uC 0 v)
      rw [chartCovDerivAlong_def, fderiv_apply_one_eq_deriv, fderiv_apply_one_eq_deriv]
      rfl
    rw [hZeq]
    refine DifferentiableAt.add hpartialY.differentiableAt ?_
    have hΓhd := hasDerivAt_chartChristoffelContraction (I := I) g β
      (P := fun v : ℝ => fderiv ℝ (fun u : ℝ => uC u v) 0 (1 : ℝ))
      (Q := fun v : ℝ => Y 0 v) (R := fun v : ℝ => uC 0 v)
      (P' := _) (Q' := _) (R' := _)
      hpartialU hY0_diff.hasDerivAt huC0_diff.hasDerivAt hΓ_diff
    exact hΓhd.differentiableAt
  have hopen : IsOpen {v : ℝ | f 0 v ∈ (chartAt H β).source} :=
    hcentral.continuous.isOpen_preimage _ (chartAt H β).open_source
  have h0R : t ∈ {v : ℝ | f 0 v ∈ (chartAt H β).source} := by
    change f 0 t ∈ (chartAt H β).source; exact hsrc0
  have hinnerR_diff : ∀ v : ℝ, DifferentiableAt ℝ
      (chartRepAt (I := I) (fun u : ℝ => f u v) (fun u : ℝ => velS u v) 0) 0 := fun v =>
    slice_transverseVelocity_chartRep_differentiableAt (I := I) g f hf v
  have hbridge : (chartRepAt (I := I) (fun v : ℝ => f 0 v)
        (fun v : ℝ => covDerivAlong (I := I) g (fun u : ℝ => f u v)
          (fun u : ℝ => velS u v) 0) t)
      =ᶠ[nhds t] Z := by
    filter_upwards [hopen.mem_nhds h0R] with v hv
    rw [chartRepAt_apply]
    change (trivializationAt E (TangentSpace I) β).continuousLinearMapAt ℝ (f 0 v)
        (covDerivAlong (I := I) g (fun u : ℝ => f u v) (fun u : ℝ => velS u v) 0)
      = Z v
    have hfwd := chartCoord_covDerivAlong_eq_chartCovDerivAlong_chartRepAtBase (I := I) (by norm_num) g
      (fun u : ℝ => f u v) (fun u : ℝ => velS u v) 0 β (hslice_v v) hv (hinnerR_diff v)
    rw [hfwd]
    have hYeq : chartRepAtBase (I := I) β (fun u : ℝ => f u v) (fun u : ℝ => velS u v)
        = (fun u : ℝ => Y u v) := by
      funext u; rw [chartRepAtBase_apply, hY]
    rw [hYeq, hZdef]
  exact (hbridge.differentiableAt_iff).mpr hZ_diff

open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
  DifferentialGeometry.Integral.DivergenceTheorem in

omit [T2Space M] [SigmaCompactSpace M] in
lemma variationField_covDeriv_chartRep_differentiableAt
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M)
    (hf : IsSmoothVariation (I := I) f) (t : ℝ) :
    DifferentiableAt ℝ
      (chartRepAt (I := I) (fun v : ℝ => f 0 v)
        (fun v : ℝ => covDerivAlong (I := I) g (fun w : ℝ => f 0 w)
          (fun w : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u w) 0 (1 : ℝ)) v) t) t := by
  classical
  set β : M := f 0 t with hβ
  have hcentral : ContMDiff (𝓘(ℝ, ℝ)) I (8 : ℕ) (fun v : ℝ => f 0 v) := by
    have hincl : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (8 : ℕ) (fun v : ℝ => ((0 : ℝ), v)) :=
      contMDiff_const.prodMk contMDiff_id
    exact (hf : ContMDiff _ _ _ _).comp hincl
  set Vsec : ℝ → E := fun v : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u v) 0 (1 : ℝ)
    with hVsecdef
  set Y0 : ℝ → E := fun v : ℝ =>
    (trivializationAt E (TangentSpace I) β).continuousLinearMapAt ℝ (f 0 v) (Vsec v) with hY0
  have hY0_C2 : ContDiffAt ℝ 2 Y0 t := by
    have hjoint : ContDiffAt ℝ 2 (fun p : ℝ × ℝ =>
        (trivializationAt E (TangentSpace I) (f 0 t)).continuousLinearMapAt ℝ (f p.1 p.2)
          (mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f w p.2) p.1 (1 : ℝ))) (0, t) :=
      chartCoord_transverseVelocity_contDiffAt (I := I) f hf t
    have hincl : ContDiffAt ℝ 2 (fun v : ℝ => ((0 : ℝ), v)) t :=
      (contDiff_const.prodMk contDiff_id).contDiffAt
    have hcomp := hjoint.comp t hincl
    exact hcomp
  have hY0_C1 : ContDiffAt ℝ 1 Y0 t := hY0_C2.of_le one_le_two
  have hY0_diff : DifferentiableAt ℝ Y0 t := hY0_C1.differentiableAt (by norm_cast)
  have hderivY0_diff : DifferentiableAt ℝ (deriv Y0) t :=
    (hY0_C2.derivWithin (m := 1) (by norm_cast)).differentiableAt (by norm_cast)
  set uC : ℝ → E := chartCurve (I := I) β (fun v : ℝ => f 0 v) with huC
  have huC_cdiff : ContDiffAt ℝ (8 : ℕ) uC t := contDiffAt_chartCurve (I := I) hcentral t
  have huC_diff : DifferentiableAt ℝ uC t := huC_cdiff.differentiableAt (by norm_num)
  have hderivuC_diff : DifferentiableAt ℝ (deriv uC) t :=
    (huC_cdiff.derivWithin (m := (1 : ℕ)) (by exact_mod_cast (by norm_num : (1 : ℕ) + 1 ≤ 8))).differentiableAt
      (by norm_num)
  have huC0 : uC t = extChartAt I β β := by rw [huC, chartCurve_def, hβ]
  have hΓ_diff : ∀ i j k : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ (chartChristoffel (I := I) g β i j k) (uC t) := by
    intro i j k
    rw [huC0]
    exact Aux3.chartChristoffel_differentiableAt_self (I := I) g β i j k
  have hsrcβ : f 0 t ∈ (chartAt H β).source := by rw [hβ]; exact mem_chart_source H (f 0 t)
  have hopen : IsOpen {v : ℝ | f 0 v ∈ (chartAt H β).source} :=
    hcentral.continuous.isOpen_preimage _ (chartAt H β).open_source
  have h0R : t ∈ {v : ℝ | f 0 v ∈ (chartAt H β).source} := hsrcβ
  have hVdiff : ∀ v : ℝ, DifferentiableAt ℝ (chartRepAt (I := I) (fun w : ℝ => f 0 w) Vsec v) v := by
    intro v
    have h := variationField_chartRep_differentiableAt (I := I) g f hf v
    exact h
  have hbridge : (chartRepAt (I := I) (fun v : ℝ => f 0 v)
        (fun v : ℝ => covDerivAlong (I := I) g (fun w : ℝ => f 0 w) Vsec v) t)
      =ᶠ[nhds t]
        (fun v : ℝ => chartCovDerivAlong (I := I) g β (fun w : ℝ => f 0 w) Y0 v) := by
    filter_upwards [hopen.mem_nhds h0R] with v hv
    rw [chartRepAt_apply]
    change (trivializationAt E (TangentSpace I) β).continuousLinearMapAt ℝ (f 0 v)
        (covDerivAlong (I := I) g (fun w : ℝ => f 0 w) Vsec v)
      = chartCovDerivAlong (I := I) g β (fun w : ℝ => f 0 w) Y0 v
    have hfwd := chartCoord_covDerivAlong_eq_chartCovDerivAlong_chartRepAtBase (I := I) (by norm_num) g
      (fun w : ℝ => f 0 w) Vsec v β hcentral hv (hVdiff v)
    rw [hfwd]
    have hYeq : chartRepAtBase (I := I) β (fun w : ℝ => f 0 w) Vsec = Y0 := by
      funext w; rw [chartRepAtBase_apply, hY0]
    rw [hYeq]
  have hccd_diff : DifferentiableAt ℝ
      (fun v : ℝ => chartCovDerivAlong (I := I) g β (fun w : ℝ => f 0 w) Y0 v) t := by
    have hfun : (fun v : ℝ => chartCovDerivAlong (I := I) g β (fun w : ℝ => f 0 w) Y0 v)
        = (fun v : ℝ => deriv Y0 v
            + chartChristoffelContraction (I := I) g β (deriv uC v) (Y0 v) (uC v)) := by
      funext v; rw [chartCovDerivAlong_def]
    rw [hfun]
    refine DifferentiableAt.add hderivY0_diff ?_
    have hΓhd := hasDerivAt_chartChristoffelContraction (I := I) g β
      (P := deriv uC) (Q := Y0) (R := uC)
      (P' := deriv (deriv uC) t) (Q' := deriv Y0 t) (R' := deriv uC t)
      hderivuC_diff.hasDerivAt hY0_diff.hasDerivAt huC_diff.hasDerivAt hΓ_diff
    exact hΓhd.differentiableAt
  refine (hbridge.differentiableAt_iff).mpr hccd_diff

end Variation
end Riemannian
end Geometry
end DifferentialGeometry

end
