import DifferentialGeometry.Analysis.Elliptic.Regularity.GradInner.Laplacian.SmoothViaDensity
import DifferentialGeometry.Analysis.Elliptic.Regularity.GradInner.Laplacian.DensityExtension


noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace GradInnerVariationalIntegralForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Laplacian.GradInnerLpIdentity
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianCandidate
open DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational
open DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaChristoffelDischarge
open DifferentialGeometry.Analysis.Laplacian.HessianBridgeSmoothLp
open DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianFinal
open DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianSmoothFull
open DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianSmoothCanonical
open DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDensityExtension

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] in
theorem lpInner_H1ComplToLp_oneSubLap_eq_lpInner_smooth_preimage
    (g : SmoothRiemannianMetric I M)
    {w_lift : H1Compl (I := I) (M := M) g}
    (hw_lift : w_lift ∈ laplacianDomain (I := I) (M := M) g)
    (w : SmoothScalar g) :
    ⟪H1ComplToLp (I := I) (M := M) g w_lift,
        smoothToLp (I := I) (M := M) g w.oneSubLapClassical⟫_ℝ =
      ⟪smoothToLp (I := I) (M := M) g w,
        laplacianDomain.preimage (I := I) (M := M) g ⟨w_lift, hw_lift⟩⟫_ℝ := by
  classical
  have h_LHS : ⟪H1ComplToLp (I := I) (M := M) g w_lift,
        smoothToLp (I := I) (M := M) g w.oneSubLapClassical⟫_ℝ =
      ⟪w_lift, smoothToH1Compl (I := I) (M := M) g w⟫_ℝ := by
    rw [show ⟪w_lift, smoothToH1Compl (I := I) (M := M) g w⟫_ℝ =
        ⟪smoothToH1Compl (I := I) (M := M) g w, w_lift⟫_ℝ from
      real_inner_comm _ _]
    rw [show smoothToH1Compl (I := I) (M := M) g w =
        resolvent (I := I) (M := M) g
          (smoothToLp (I := I) (M := M) g w.oneSubLapClassical) from
      smoothToH1Compl_eq_resolvent_oneSubLap (I := I) (M := M) w]
    exact (resolvent_inner_eq_lpFunctional (I := I) (M := M) g
      (smoothToLp (I := I) (M := M) g w.oneSubLapClassical) w_lift).symm
  have h_RHS : ⟪smoothToLp (I := I) (M := M) g w,
        laplacianDomain.preimage (I := I) (M := M) g ⟨w_lift, hw_lift⟩⟫_ℝ =
      ⟪w_lift, smoothToH1Compl (I := I) (M := M) g w⟫_ℝ := by
    rw [show smoothToLp (I := I) (M := M) g w =
        H1ComplToLp (I := I) (M := M) g
          (smoothToH1Compl (I := I) (M := M) g w) from
      (H1ComplToLp_smoothToH1Compl (I := I) (M := M) g w).symm]
    have h_var := (resolvent_inner_eq_lpFunctional (I := I) (M := M) g
      (laplacianDomain.preimage (I := I) (M := M) g ⟨w_lift, hw_lift⟩)
      (smoothToH1Compl (I := I) (M := M) g w)).symm
    rw [h_var]
    congr 1
    exact resolvent_laplacianDomain_preimage_eq (I := I) (M := M) g ⟨w_lift, hw_lift⟩
  rw [h_LHS, h_RHS]

omit [NeZero (Module.finrank ℝ E)] in
theorem lpInner_gradInner_smooth_oneSubLap_eq_lpInner_smooth_preimage
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    {w_lift : H1Compl (I := I) (M := M) g}
    (hw_lift : w_lift ∈ laplacianDomain (I := I) (M := M) g)
    (h_witness : H1ComplToLp (I := I) (M := M) g w_lift =
      gradInnerCLM (I := I) (M := M) g φ u_h)
    (w : SmoothScalar g) :
    ⟪gradInnerCLM (I := I) (M := M) g φ u_h,
        smoothToLp (I := I) (M := M) g w.oneSubLapClassical⟫_ℝ =
      ⟪smoothToLp (I := I) (M := M) g w,
        laplacianDomain.preimage (I := I) (M := M) g ⟨w_lift, hw_lift⟩⟫_ℝ := by
  rw [← h_witness]
  exact lpInner_H1ComplToLp_oneSubLap_eq_lpInner_smooth_preimage
    (I := I) (M := M) g hw_lift w

omit [NeZero (Module.finrank ℝ E)] in
theorem integral_H1ComplToLp_oneSubLap_eq_integral_preimage_smooth
    (g : SmoothRiemannianMetric I M)
    {w_lift : H1Compl (I := I) (M := M) g}
    (hw_lift : w_lift ∈ laplacianDomain (I := I) (M := M) g)
    (w : SmoothScalar g) :
    ∫ x, ((H1ComplToLp (I := I) (M := M) g w_lift :
              Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x *
            (w.toFun x - Δ_g (I := I) g w.smooth x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, w.toFun x *
            ((laplacianDomain.preimage (I := I) (M := M) g
                ⟨w_lift, hw_lift⟩ :
                Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  have h_abs := lpInner_H1ComplToLp_oneSubLap_eq_lpInner_smooth_preimage
    (I := I) (M := M) g hw_lift w
  rw [L2.inner_def, L2.inner_def] at h_abs
  have h_LHS_coe :
      ((smoothToLp (I := I) (M := M) g w.oneSubLapClassical :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =ᵐ[
          riemannianVolumeMeasure (I := I) (M := M) g]
        (fun x : M => w.toFun x - Δ_g (I := I) g w.smooth x) := by
    have h := MemLp.coeFn_toLp w.oneSubLapClassical.memLp_two
    filter_upwards [h] with x hx
    change ((w.oneSubLapClassical.memLp_two.toLp _ :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x = _
    rw [hx]
    rfl
  have h_RHS_coe :
      ((smoothToLp (I := I) (M := M) g w :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =ᵐ[
          riemannianVolumeMeasure (I := I) (M := M) g]
        (fun x : M => w.toFun x) := MemLp.coeFn_toLp w.memLp_two
  have h_LHS_integral :
      ∫ a, @inner ℝ ℝ _
            (((H1ComplToLp (I := I) (M := M) g w_lift :
                Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
                M → ℝ) a)
            (((smoothToLp (I := I) (M := M) g w.oneSubLapClassical :
                Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
                M → ℝ) a)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        ∫ x, ((H1ComplToLp (I := I) (M := M) g w_lift :
              Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x *
              (w.toFun x - Δ_g (I := I) g w.smooth x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    refine integral_congr_ae ?_
    filter_upwards [h_LHS_coe] with x hx
    have h_inner_apply :
        @inner ℝ ℝ _
            (((H1ComplToLp (I := I) (M := M) g w_lift :
                Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
                M → ℝ) x)
            (((smoothToLp (I := I) (M := M) g w.oneSubLapClassical :
                Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
                M → ℝ) x) =
          ((smoothToLp (I := I) (M := M) g w.oneSubLapClassical :
                Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x *
            ((H1ComplToLp (I := I) (M := M) g w_lift :
                Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x := rfl
    rw [h_inner_apply]
    change _ * _ = _ * _
    rw [hx]
    ring
  have h_RHS_integral :
      ∫ a, @inner ℝ ℝ _
            (((smoothToLp (I := I) (M := M) g w :
                Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
                M → ℝ) a)
            (((laplacianDomain.preimage (I := I) (M := M) g
                ⟨w_lift, hw_lift⟩ :
                Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
                M → ℝ) a)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        ∫ x, w.toFun x *
              ((laplacianDomain.preimage (I := I) (M := M) g
                  ⟨w_lift, hw_lift⟩ :
                  Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    refine integral_congr_ae ?_
    filter_upwards [h_RHS_coe] with x hx
    have h_inner_apply :
        @inner ℝ ℝ _
            (((smoothToLp (I := I) (M := M) g w :
                Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
                M → ℝ) x)
            (((laplacianDomain.preimage (I := I) (M := M) g
                ⟨w_lift, hw_lift⟩ :
                Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
                M → ℝ) x) =
          ((laplacianDomain.preimage (I := I) (M := M) g
                ⟨w_lift, hw_lift⟩ :
                Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x *
            ((smoothToLp (I := I) (M := M) g w :
                Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x := rfl
    rw [h_inner_apply]
    change _ * _ = _ * _
    rw [hx]
    ring
  rw [← h_LHS_integral, ← h_RHS_integral]
  exact h_abs

omit [NeZero (Module.finrank ℝ E)] in
theorem integral_gradInner_oneSubLap_smooth_eq_integral_preimage_smooth
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    {w_lift : H1Compl (I := I) (M := M) g}
    (hw_lift : w_lift ∈ laplacianDomain (I := I) (M := M) g)
    (h_witness : H1ComplToLp (I := I) (M := M) g w_lift =
      gradInnerCLM (I := I) (M := M) g φ u_h)
    (w : SmoothScalar g) :
    ∫ x, ((gradInnerCLM (I := I) (M := M) g φ u_h :
              Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x *
            (w.toFun x - Δ_g (I := I) g w.smooth x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, w.toFun x *
            ((laplacianDomain.preimage (I := I) (M := M) g
                ⟨w_lift, hw_lift⟩ :
                Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  rw [← h_witness]
  exact integral_H1ComplToLp_oneSubLap_eq_integral_preimage_smooth
    (I := I) (M := M) g hw_lift w

omit [NeZero (Module.finrank ℝ E)] in
theorem integral_gradInner_oneSubLap_smooth_eq_integral_smoothCase
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (w : SmoothScalar g) :
    ∫ x, ((gradInnerCLM (I := I) (M := M) g φ
              (smoothToH1Compl (I := I) (M := M) g v) :
              Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x *
            (w.toFun x - Δ_g (I := I) g w.smooth x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, w.toFun x *
            ((smoothToLp (I := I) (M := M) g
                (gradInnerSmoothBundle (I := I) (M := M) g φ v).oneSubLapClassical :
                Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  set w_lift : H1Compl (I := I) (M := M) g :=
    smoothGradInnerWitness (I := I) (M := M) g φ v with hw_lift_def
  have hw_lift_mem : w_lift ∈ laplacianDomain (I := I) (M := M) g := by
    rw [hw_lift_def]
    exact smoothGradInnerWitness_mem_laplacianDomain (I := I) (M := M) g φ v
  have hw_lift_eq : H1ComplToLp (I := I) (M := M) g w_lift =
      gradInnerCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) := by
    rw [hw_lift_def]
    exact H1ComplToLp_smoothGradInnerWitness (I := I) (M := M) g φ v
  have h_main :=
    integral_gradInner_oneSubLap_smooth_eq_integral_preimage_smooth
      (I := I) (M := M) g φ hw_lift_mem hw_lift_eq w
  have h_preimage_eq :
      laplacianDomain.preimage (I := I) (M := M) g ⟨w_lift, hw_lift_mem⟩ =
        smoothToLp (I := I) (M := M) g
          (gradInnerSmoothBundle (I := I) (M := M) g φ v).oneSubLapClassical := by
    apply resolvent_injective (I := I) (M := M) g
    have h_lhs := resolvent_laplacianDomain_preimage_eq (I := I) (M := M) g
      ⟨w_lift, hw_lift_mem⟩
    rw [h_lhs]
    change w_lift = _
    rw [hw_lift_def]
    unfold smoothGradInnerWitness
    exact smoothToH1Compl_eq_resolvent_oneSubLap (I := I) (M := M)
      (gradInnerSmoothBundle (I := I) (M := M) g φ v)
  rw [h_preimage_eq] at h_main
  exact h_main

theorem integral_gradInner_oneSubLap_smooth_eq_integral_candidate_of_variational
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (hvar_id :
      gradInnerCLM (I := I) (M := M) g φ u_h =
        H1ComplToLp (I := I) (M := M) g
          (resolvent (I := I) (M := M) g
            (gradInnerLaplacianCandidateUnconditional
              (I := I) (M := M) g φ hu_h)))
    (w : SmoothScalar g) :
    ∫ x, ((gradInnerCLM (I := I) (M := M) g φ u_h :
              Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x *
            (w.toFun x - Δ_g (I := I) g w.smooth x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, w.toFun x *
            ((gradInnerLaplacianCandidateUnconditional
                (I := I) (M := M) g φ hu_h :
                Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  set F : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
    gradInnerLaplacianCandidateUnconditional (I := I) (M := M) g φ hu_h with hF_def
  set w_lift : H1Compl (I := I) (M := M) g :=
    resolvent (I := I) (M := M) g F with hw_lift_def
  have hw_lift_mem : w_lift ∈ laplacianDomain (I := I) (M := M) g := by
    rw [hw_lift_def]
    exact (laplacianDomain_mem_iff (I := I) (M := M) g).mpr ⟨F, rfl⟩
  have h_preimage_eq :
      laplacianDomain.preimage (I := I) (M := M) g ⟨w_lift, hw_lift_mem⟩ = F := by
    apply resolvent_injective (I := I) (M := M) g
    rw [resolvent_laplacianDomain_preimage_eq]
  have hw_lift_eq : H1ComplToLp (I := I) (M := M) g w_lift =
      gradInnerCLM (I := I) (M := M) g φ u_h := by
    rw [hw_lift_def]
    exact hvar_id.symm
  have h_main :=
    integral_gradInner_oneSubLap_smooth_eq_integral_preimage_smooth
      (I := I) (M := M) g φ hw_lift_mem hw_lift_eq w
  rw [h_preimage_eq] at h_main
  exact h_main

theorem integral_gradInner_oneSubLap_smooth_eq_integral_candidate_smoothCase_of_discharge
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_discharge : christoffelDischargeSmoothCase (I := I) (M := M) g φ v)
    (w : SmoothScalar g) :
    ∫ x, ((gradInnerCLM (I := I) (M := M) g φ
              (smoothToH1Compl (I := I) (M := M) g v) :
              Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x *
            (w.toFun x - Δ_g (I := I) g w.smooth x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, w.toFun x *
            ((gradInnerLaplacianCandidateUnconditional (I := I) (M := M) g φ
                (smoothToH1Compl_mem_laplacianDomainPow_two
                  (I := I) (M := M) g v) :
                Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  have hvar_id :=
    gradInnerCLM_eq_H1ComplToLp_resolvent_smoothCase_of_discharge
      (I := I) (M := M) g φ v h_discharge
  exact integral_gradInner_oneSubLap_smooth_eq_integral_candidate_of_variational
    (I := I) (M := M) g φ
    (smoothToH1Compl_mem_laplacianDomainPow_two (I := I) (M := M) g v)
    hvar_id w

theorem integral_gradInner_oneSubLap_smooth_eq_integral_candidate_density
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_smooth_seq : ℕ → SmoothScalar g)
    (h_conv_H1Compl : Tendsto
      (fun n => smoothToH1Compl (I := I) (M := M) g (h_smooth_seq n))
      atTop (𝓝 u_h))
    (h_conv_candidate : Tendsto
      (fun n => gradInnerLaplacianCandidateUnconditional (I := I) (M := M) g φ
        (smoothToH1Compl_mem_laplacianDomainPow_two
          (I := I) (M := M) g (h_smooth_seq n)))
      atTop (𝓝 (gradInnerLaplacianCandidateUnconditional
        (I := I) (M := M) g φ hu_h)))
    (h_smooth_identity : ∀ n,
      smoothCandidate_identification_target (I := I) (M := M) g φ
        (h_smooth_seq n))
    (w : SmoothScalar g) :
    ∫ x, ((gradInnerCLM (I := I) (M := M) g φ u_h :
              Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x *
            (w.toFun x - Δ_g (I := I) g w.smooth x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, w.toFun x *
            ((gradInnerLaplacianCandidateUnconditional
                (I := I) (M := M) g φ hu_h :
                Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  have hvar_id :=
    gradInnerCLM_eq_H1ComplToLp_resolvent_unconditional_via_density
      (I := I) (M := M) g φ hu_h h_smooth_seq h_conv_H1Compl
      h_conv_candidate h_smooth_identity
  exact integral_gradInner_oneSubLap_smooth_eq_integral_candidate_of_variational
    (I := I) (M := M) g φ hu_h hvar_id w

omit [NeZero (Module.finrank ℝ E)] in
theorem integral_gradInner_oneSubLap_contMDiff_eq_integral_preimage
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    {w_lift : H1Compl (I := I) (M := M) g}
    (hw_lift : w_lift ∈ laplacianDomain (I := I) (M := M) g)
    (h_witness : H1ComplToLp (I := I) (M := M) g w_lift =
      gradInnerCLM (I := I) (M := M) g φ u_h)
    {w : M → ℝ} (hw : ContMDiff I 𝓘(ℝ, ℝ) ∞ w) :
    ∫ x, ((gradInnerCLM (I := I) (M := M) g φ u_h :
              Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x *
            (w x - Δ_g (I := I) g hw x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, w x *
            ((laplacianDomain.preimage (I := I) (M := M) g
                ⟨w_lift, hw_lift⟩ :
                Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  exact integral_gradInner_oneSubLap_smooth_eq_integral_preimage_smooth
    (I := I) (M := M) g φ hw_lift h_witness ⟨w, hw⟩

omit [NeZero (Module.finrank ℝ E)] in
theorem integral_grad_inner_oneSubLap_smooth_pointwise
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (w : SmoothScalar g) :
    ∫ x, g.inner x (gradFun (I := I) g (φ : M → ℝ) x)
            (gradFun (I := I) g v.toFun x) *
            (w.toFun x - Δ_g (I := I) g w.smooth x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, w.toFun x *
            ((gradInnerSmoothBundle (I := I) (M := M) g φ v).toFun x -
              Δ_g (I := I) g
                (gradInnerSmoothBundle (I := I) (M := M) g φ v).smooth x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  have h_main :=
    integral_gradInner_oneSubLap_smooth_eq_integral_smoothCase
      (I := I) (M := M) g φ v w
  have h_LHS_coeFn :
      ((gradInnerCLM (I := I) (M := M) g φ
          (smoothToH1Compl (I := I) (M := M) g v) :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      (fun x : M => g.inner x (gradFun (I := I) g (φ : M → ℝ) x)
        (gradFun (I := I) g v.toFun x)) := by
    rw [gradInnerCLM_smoothToH1Compl (I := I) (M := M) g φ v]
    exact gradInnerSmooth_coeFn (I := I) (M := M) g φ v
  have h_RHS_coeFn :
      ((smoothToLp (I := I) (M := M) g
          (gradInnerSmoothBundle (I := I) (M := M) g φ v).oneSubLapClassical :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      (fun x : M => (gradInnerSmoothBundle (I := I) (M := M) g φ v).toFun x -
            Δ_g (I := I) g
              (gradInnerSmoothBundle (I := I) (M := M) g φ v).smooth x) := by
    have h := MemLp.coeFn_toLp
      (gradInnerSmoothBundle (I := I) (M := M) g φ v).oneSubLapClassical.memLp_two
    filter_upwards [h] with x hx
    change ((((gradInnerSmoothBundle (I := I) (M := M) g φ v).oneSubLapClassical.memLp_two.toLp
        _ :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x) = _
    rw [hx]
    rfl
  have h_LHS_int_ae :
      (fun x : M =>
          ((gradInnerCLM (I := I) (M := M) g φ
              (smoothToH1Compl (I := I) (M := M) g v) :
              Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x *
            (w.toFun x - Δ_g (I := I) g w.smooth x)) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      (fun x : M => g.inner x (gradFun (I := I) g (φ : M → ℝ) x)
            (gradFun (I := I) g v.toFun x) *
          (w.toFun x - Δ_g (I := I) g w.smooth x)) := by
    filter_upwards [h_LHS_coeFn] with x hx
    rw [hx]
  have h_RHS_int_ae :
      (fun x : M =>
          w.toFun x *
          ((smoothToLp (I := I) (M := M) g
              (gradInnerSmoothBundle (I := I) (M := M) g φ v).oneSubLapClassical :
              Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      (fun x : M => w.toFun x *
          ((gradInnerSmoothBundle (I := I) (M := M) g φ v).toFun x -
            Δ_g (I := I) g
              (gradInnerSmoothBundle (I := I) (M := M) g φ v).smooth x)) := by
    filter_upwards [h_RHS_coeFn] with x hx
    rw [hx]
  have h_LHS_eq :=
    integral_congr_ae h_LHS_int_ae
  have h_RHS_eq :=
    integral_congr_ae h_RHS_int_ae
  rw [← h_LHS_eq, ← h_RHS_eq]
  exact h_main

omit [NeZero (Module.finrank ℝ E)] in
theorem integral_gradInner_oneSubLap_contMDiffMap_eq_integral_preimage
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    {w_lift : H1Compl (I := I) (M := M) g}
    (hw_lift : w_lift ∈ laplacianDomain (I := I) (M := M) g)
    (h_witness : H1ComplToLp (I := I) (M := M) g w_lift =
      gradInnerCLM (I := I) (M := M) g φ u_h)
    (w : C^∞⟮I, M; ℝ⟯) :
    ∫ x, ((gradInnerCLM (I := I) (M := M) g φ u_h :
              Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x *
            ((w : M → ℝ) x - Δ_g (I := I) g w.contMDiff x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, (w : M → ℝ) x *
            ((laplacianDomain.preimage (I := I) (M := M) g
                ⟨w_lift, hw_lift⟩ :
                Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  exact integral_gradInner_oneSubLap_smooth_eq_integral_preimage_smooth
    (I := I) (M := M) g φ hw_lift h_witness ⟨(w : M → ℝ), w.contMDiff⟩

omit [NeZero (Module.finrank ℝ E)] in
theorem weak_oneSubLap_holds_of_image_in_laplacianDomain
    (g : SmoothRiemannianMetric I M)
    {A : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    {w_lift : H1Compl (I := I) (M := M) g}
    (hw_lift : w_lift ∈ laplacianDomain (I := I) (M := M) g)
    (h_A_eq : H1ComplToLp (I := I) (M := M) g w_lift = A) :
    ∀ w : SmoothScalar g,
      ∫ x, (A : M → ℝ) x * (w.toFun x - Δ_g (I := I) g w.smooth x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, w.toFun x *
            ((laplacianDomain.preimage (I := I) (M := M) g
                ⟨w_lift, hw_lift⟩ :
                Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  intro w
  rw [← h_A_eq]
  exact integral_H1ComplToLp_oneSubLap_eq_integral_preimage_smooth
    (I := I) (M := M) g hw_lift w

section SanityTests

example (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_discharge : christoffelDischargeSmoothCase (I := I) (M := M) g φ v)
    (w : SmoothScalar g) :
    ∫ x, ((gradInnerCLM (I := I) (M := M) g φ
              (smoothToH1Compl (I := I) (M := M) g v) :
              Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x *
            (w.toFun x - Δ_g (I := I) g w.smooth x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, w.toFun x *
            ((gradInnerLaplacianCandidateUnconditional (I := I) (M := M) g φ
                (smoothToH1Compl_mem_laplacianDomainPow_two
                  (I := I) (M := M) g v) :
                Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
  integral_gradInner_oneSubLap_smooth_eq_integral_candidate_smoothCase_of_discharge
    (I := I) (M := M) g φ v h_discharge w

example (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v w : SmoothScalar g) :
    ∫ x, ((gradInnerCLM (I := I) (M := M) g φ
              (smoothToH1Compl (I := I) (M := M) g v) :
              Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x *
            (w.toFun x - Δ_g (I := I) g w.smooth x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, w.toFun x *
            ((smoothToLp (I := I) (M := M) g
                (gradInnerSmoothBundle (I := I) (M := M) g φ v).oneSubLapClassical :
                Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
  integral_gradInner_oneSubLap_smooth_eq_integral_smoothCase
    (I := I) (M := M) g φ v w

end SanityTests

end GradInnerVariationalIntegralForm
end Laplacian
end Analysis
end DifferentialGeometry

end
