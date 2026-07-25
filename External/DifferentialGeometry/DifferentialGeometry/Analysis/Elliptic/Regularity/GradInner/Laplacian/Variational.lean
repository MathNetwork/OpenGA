import DifferentialGeometry.Analysis.Elliptic.Regularity.GradInner.Laplacian.Candidate
import DifferentialGeometry.Analysis.Elliptic.Regularity.Hessian.PairingLapDom
import DifferentialGeometry.Analysis.Elliptic.Regularity.Hessian.PairingChart
import DifferentialGeometry.Analysis.Elliptic.Regularity.Ricci.PairingCLM


noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace GradInnerLaplacianVariational

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Laplacian.GradInnerLpIdentity
open DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianCandidate
open DifferentialGeometry.Analysis.Laplacian.HessianPairingLapDom
open DifferentialGeometry.Analysis.Laplacian.HessianPairingChart
open DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

noncomputable def gradInnerLapU
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  gradInnerCLM (I := I) (M := M) g φ
    (u_h - preimageLift (I := I) (M := M) g hu_h)

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma gradInnerLapU_def
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    gradInnerLapU (I := I) (M := M) g φ hu_h =
      gradInnerCLM (I := I) (M := M) g φ
        (u_h - preimageLift (I := I) (M := M) g hu_h) := rfl

omit [NeZero (Module.finrank ℝ E)] in
lemma gradInnerLapU_eq_sub
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    gradInnerLapU (I := I) (M := M) g φ hu_h =
      gradInnerCLM (I := I) (M := M) g φ u_h -
        gradInnerCLM (I := I) (M := M) g φ
          (preimageLift (I := I) (M := M) g hu_h) := by
  unfold gradInnerLapU
  rw [map_sub]

noncomputable def gradInnerLaplacianCandidateUnconditional
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  gradInnerCLM (I := I) (M := M) g φ u_h
    - gradInnerCLM (I := I) (M := M) g
        (smoothLaplacianBundle (I := I) (M := M) g φ) u_h
    - gradInnerLapU (I := I) (M := M) g φ hu_h
    - (2 : ℝ) • ricciPairingCLM (I := I) (M := M) g φ u_h
    - (2 : ℝ) • hessPairingLpOnLapDom (I := I) (M := M) g φ
        (laplacianDomainPow_succ_subset_laplacianDomain
          (I := I) (M := M) g 1 hu_h)

@[simp] theorem gradInnerLaplacianCandidateUnconditional_def
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    gradInnerLaplacianCandidateUnconditional (I := I) (M := M) g φ hu_h =
      gradInnerCLM (I := I) (M := M) g φ u_h
        - gradInnerCLM (I := I) (M := M) g
            (smoothLaplacianBundle (I := I) (M := M) g φ) u_h
        - gradInnerLapU (I := I) (M := M) g φ hu_h
        - (2 : ℝ) • ricciPairingCLM (I := I) (M := M) g φ u_h
        - (2 : ℝ) • hessPairingLpOnLapDom (I := I) (M := M) g φ
            (laplacianDomainPow_succ_subset_laplacianDomain
              (I := I) (M := M) g 1 hu_h) := rfl

theorem gradInnerLaplacianCandidateUnconditional_explicit
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    gradInnerLaplacianCandidateUnconditional (I := I) (M := M) g φ hu_h =
      - gradInnerCLM (I := I) (M := M) g
            (smoothLaplacianBundle (I := I) (M := M) g φ) u_h
        + gradInnerCLM (I := I) (M := M) g φ
            (preimageLift (I := I) (M := M) g hu_h)
        - (2 : ℝ) • ricciPairingCLM (I := I) (M := M) g φ u_h
        - (2 : ℝ) • hessPairingLpOnLapDom (I := I) (M := M) g φ
            (laplacianDomainPow_succ_subset_laplacianDomain
              (I := I) (M := M) g 1 hu_h) := by
  unfold gradInnerLaplacianCandidateUnconditional
  rw [gradInnerLapU_eq_sub]
  abel

omit [NeZero (Module.finrank ℝ E)] in
theorem gradInnerCLM_mem_image_laplacianDomain_smooth
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    gradInnerCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) ∈
      Set.image (H1ComplToLp (I := I) (M := M) g)
        (laplacianDomain (I := I) (M := M) g : Set (H1Compl g)) :=
  gradInnerCLM_smoothToH1Compl_mem_image_laplacianDomain
    (I := I) (M := M) g φ v

omit [NeZero (Module.finrank ℝ E)] in
theorem gradInnerCLM_mem_image_laplacianDomain_from_witness
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    {w_lift : H1Compl (I := I) (M := M) g}
    (hw_lift_dom : w_lift ∈ laplacianDomain (I := I) (M := M) g)
    (hw_lift_eq : H1ComplToLp (I := I) (M := M) g w_lift =
      gradInnerCLM (I := I) (M := M) g φ u_h) :
    gradInnerCLM (I := I) (M := M) g φ u_h ∈
      Set.image (H1ComplToLp (I := I) (M := M) g)
        (laplacianDomain (I := I) (M := M) g : Set (H1Compl g)) :=
  ⟨w_lift, hw_lift_dom, hw_lift_eq⟩

theorem gradInnerLaplacianCandidateUnconditional_norm_le
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    ‖gradInnerLaplacianCandidateUnconditional (I := I) (M := M) g φ hu_h‖ ≤
      ‖gradInnerCLM (I := I) (M := M) g φ u_h‖ +
      ‖gradInnerCLM (I := I) (M := M) g
        (smoothLaplacianBundle (I := I) (M := M) g φ) u_h‖ +
      ‖gradInnerLapU (I := I) (M := M) g φ hu_h‖ +
      2 * ‖ricciPairingCLM (I := I) (M := M) g φ u_h‖ +
      2 * ‖hessPairingLpOnLapDom (I := I) (M := M) g φ
        (laplacianDomainPow_succ_subset_laplacianDomain
          (I := I) (M := M) g 1 hu_h)‖ := by
  unfold gradInnerLaplacianCandidateUnconditional
  have hstep1 := norm_sub_le
    (gradInnerCLM (I := I) (M := M) g φ u_h
      - gradInnerCLM (I := I) (M := M) g
          (smoothLaplacianBundle (I := I) (M := M) g φ) u_h
      - gradInnerLapU (I := I) (M := M) g φ hu_h
      - (2 : ℝ) • ricciPairingCLM (I := I) (M := M) g φ u_h)
    ((2 : ℝ) • hessPairingLpOnLapDom (I := I) (M := M) g φ
      (laplacianDomainPow_succ_subset_laplacianDomain (I := I) (M := M) g 1 hu_h))
  have hstep2 := norm_sub_le
    (gradInnerCLM (I := I) (M := M) g φ u_h
      - gradInnerCLM (I := I) (M := M) g
          (smoothLaplacianBundle (I := I) (M := M) g φ) u_h
      - gradInnerLapU (I := I) (M := M) g φ hu_h)
    ((2 : ℝ) • ricciPairingCLM (I := I) (M := M) g φ u_h)
  have hstep3 := norm_sub_le
    (gradInnerCLM (I := I) (M := M) g φ u_h
      - gradInnerCLM (I := I) (M := M) g
          (smoothLaplacianBundle (I := I) (M := M) g φ) u_h)
    (gradInnerLapU (I := I) (M := M) g φ hu_h)
  have hstep4 := norm_sub_le (gradInnerCLM (I := I) (M := M) g φ u_h)
    (gradInnerCLM (I := I) (M := M) g
      (smoothLaplacianBundle (I := I) (M := M) g φ) u_h)
  have h_smul_ricci :
      ‖(2 : ℝ) • ricciPairingCLM (I := I) (M := M) g φ u_h‖ =
      2 * ‖ricciPairingCLM (I := I) (M := M) g φ u_h‖ := by
    rw [norm_smul]; simp
  have h_smul_hess :
      ‖(2 : ℝ) • hessPairingLpOnLapDom (I := I) (M := M) g φ
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)‖ =
      2 * ‖hessPairingLpOnLapDom (I := I) (M := M) g φ
        (laplacianDomainPow_succ_subset_laplacianDomain
          (I := I) (M := M) g 1 hu_h)‖ := by
    rw [norm_smul]; simp
  linarith [hstep1, hstep2, hstep3, hstep4, h_smul_ricci, h_smul_hess]

omit [NeZero (Module.finrank ℝ E)] in
lemma gradInnerCLM_smoothToH1Compl_eq_smoothToLp
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    gradInnerCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) =
      smoothToLp (I := I) (M := M) g
        (gradInnerSmoothBundle (I := I) (M := M) g φ v) := by
  rw [gradInnerCLM_smoothToH1Compl]
  exact gradInnerSmooth_eq_smoothToLp_bundle (I := I) (M := M) g φ v

omit [NeZero (Module.finrank ℝ E)] in
lemma ricciPairingCLM_smoothToH1Compl_eq_smoothToLp
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    ricciPairingCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) =
      smoothToLp (I := I) (M := M) g
        (smoothRicciPairingBundle (I := I) (M := M) g φ v) := by
  rw [ricciPairingCLM_smoothToH1Compl]
  rfl

noncomputable def smoothGradInnerWitness
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    H1Compl (I := I) (M := M) g :=
  smoothToH1Compl (I := I) (M := M) g
    (gradInnerSmoothBundle (I := I) (M := M) g φ v)

omit [NeZero (Module.finrank ℝ E)] in
theorem smoothGradInnerWitness_mem_laplacianDomain
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    smoothGradInnerWitness (I := I) (M := M) g φ v ∈
      laplacianDomain (I := I) (M := M) g := by
  unfold smoothGradInnerWitness
  exact smoothToH1Compl_mem_laplacianDomain
    (I := I) (M := M)
    (gradInnerSmoothBundle (I := I) (M := M) g φ v)

omit [NeZero (Module.finrank ℝ E)] in
theorem H1ComplToLp_smoothGradInnerWitness
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    H1ComplToLp (I := I) (M := M) g
        (smoothGradInnerWitness (I := I) (M := M) g φ v) =
      gradInnerCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) := by
  unfold smoothGradInnerWitness
  rw [H1ComplToLp_smoothToH1Compl]
  rw [gradInnerCLM_smoothToH1Compl_eq_smoothToLp]

omit [NeZero (Module.finrank ℝ E)] in
theorem gradInnerCLM_eq_H1ComplToLp_smoothWitness
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    gradInnerCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) =
      H1ComplToLp (I := I) (M := M) g
        (smoothGradInnerWitness (I := I) (M := M) g φ v) := by
  rw [H1ComplToLp_smoothGradInnerWitness]

omit [NeZero (Module.finrank ℝ E)] in
theorem smoothMulH1Compl_smoothToH1Compl_mem_laplacianDomainPow_two_via
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    smoothMulH1Compl (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) ∈
      laplacianDomainPow (I := I) (M := M) g 2 := by
  rw [smoothMulH1Compl_mem_pow_two_iff_gradInnerCLM_mem_image
    (I := I) (M := M) g φ
    (smoothToH1Compl_mem_laplacianDomainPow_two (I := I) (M := M) g v)]
  exact gradInnerCLM_mem_image_laplacianDomain_smooth
    (I := I) (M := M) g φ v

omit [NeZero (Module.finrank ℝ E)] in
theorem gradInnerCLM_mem_image_laplacianDomain_of_witness
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (mkWitness :
      ∃ w_lift : H1Compl (I := I) (M := M) g,
        w_lift ∈ laplacianDomain (I := I) (M := M) g ∧
        H1ComplToLp (I := I) (M := M) g w_lift =
          gradInnerCLM (I := I) (M := M) g φ u_h) :
    gradInnerCLM (I := I) (M := M) g φ u_h ∈
      Set.image (H1ComplToLp (I := I) (M := M) g)
        (laplacianDomain (I := I) (M := M) g : Set (H1Compl g)) := by
  obtain ⟨w_lift, hw_lift_dom, hw_lift_eq⟩ := mkWitness
  exact ⟨w_lift, hw_lift_dom, hw_lift_eq⟩

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_witness_smoothToH1Compl
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    ∃ w_lift : H1Compl (I := I) (M := M) g,
      w_lift ∈ laplacianDomain (I := I) (M := M) g ∧
      H1ComplToLp (I := I) (M := M) g w_lift =
        gradInnerCLM (I := I) (M := M) g φ
          (smoothToH1Compl (I := I) (M := M) g v) := by
  refine ⟨smoothGradInnerWitness (I := I) (M := M) g φ v, ?_, ?_⟩
  · exact smoothGradInnerWitness_mem_laplacianDomain (I := I) (M := M) g φ v
  · exact H1ComplToLp_smoothGradInnerWitness (I := I) (M := M) g φ v

theorem gradInnerCLM_eq_H1ComplToLp_resolvent_of_variational
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (hvar_id :
      gradInnerCLM (I := I) (M := M) g φ u_h =
        H1ComplToLp (I := I) (M := M) g
          (resolvent (I := I) (M := M) g
            (gradInnerLaplacianCandidateUnconditional
              (I := I) (M := M) g φ hu_h))) :
    gradInnerCLM (I := I) (M := M) g φ u_h ∈
      Set.image (H1ComplToLp (I := I) (M := M) g)
        (laplacianDomain (I := I) (M := M) g : Set (H1Compl g)) := by
  classical
  refine ⟨resolvent (I := I) (M := M) g
    (gradInnerLaplacianCandidateUnconditional (I := I) (M := M) g φ hu_h),
    ?_, hvar_id.symm⟩
  exact (laplacianDomain_mem_iff (I := I) (M := M) g).mpr
    ⟨gradInnerLaplacianCandidateUnconditional (I := I) (M := M) g φ hu_h, rfl⟩

omit [NeZero (Module.finrank ℝ E)] in
theorem smoothGradInnerWitness_eq_resolvent
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    smoothGradInnerWitness (I := I) (M := M) g φ v =
      resolvent (I := I) (M := M) g
        (smoothToLp (I := I) (M := M) g
          (gradInnerSmoothBundle (I := I) (M := M) g φ v).oneSubLapClassical) := by
  unfold smoothGradInnerWitness
  exact smoothToH1Compl_eq_resolvent_oneSubLap (I := I) (M := M)
    (gradInnerSmoothBundle (I := I) (M := M) g φ v)

omit [NeZero (Module.finrank ℝ E)] in
theorem gradInnerCLM_smoothToH1Compl_eq_H1ComplToLp_resolvent_smoothCandidate
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    gradInnerCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) =
      H1ComplToLp (I := I) (M := M) g
        (resolvent (I := I) (M := M) g
          (smoothToLp (I := I) (M := M) g
            (gradInnerSmoothBundle (I := I) (M := M) g φ v).oneSubLapClassical)) := by
  rw [gradInnerCLM_eq_H1ComplToLp_smoothWitness]
  rw [smoothGradInnerWitness_eq_resolvent]

omit [NeZero (Module.finrank ℝ E)] in
theorem gradInnerCLM_smoothToH1Compl_eq_resolventL2_smoothCandidate
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    gradInnerCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) =
      resolventL2 (I := I) (M := M) g
        (smoothToLp (I := I) (M := M) g
          (gradInnerSmoothBundle (I := I) (M := M) g φ v).oneSubLapClassical) := by
  rw [gradInnerCLM_smoothToH1Compl_eq_H1ComplToLp_resolvent_smoothCandidate]
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem hessPairingChart_polar
    (g : SmoothRiemannianMetric I M) (φ v : C^∞⟮I, M; ℝ⟯) (b : M) :
    4 * hessPairingChart (I := I) g φ v b =
      chartHessFrobeniusSq (I := I) g (fun x : M => φ x + v x) b -
        chartHessFrobeniusSq (I := I) g (fun x : M => φ x - v x) b := by
  rw [hessPairingChart_def]
  ring

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem chartHessFrobeniusSq_polar_eq_hessPairing
    (g : SmoothRiemannianMetric I M) (φ v : C^∞⟮I, M; ℝ⟯) (b : M) :
    chartHessFrobeniusSq (I := I) g (fun x : M => φ x + v x) b -
        chartHessFrobeniusSq (I := I) g (fun x : M => φ x - v x) b =
      4 * hessPairingChart (I := I) g φ v b :=
  (hessPairingChart_polar (I := I) (M := M) g φ v b).symm

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem g_inner_polar
    (g : SmoothRiemannianMetric I M) (b : M) (u w : TangentSpace I b) :
    g.inner b (u + w) (u + w) - g.inner b (u - w) (u - w) =
      4 * g.inner b u w := by
  classical
  have h_inner_sym : g.inner b w u = g.inner b u w := g.symm b _ _
  have hp1 : g.inner b (u + w) (u + w) =
      g.inner b u u + g.inner b u w + g.inner b w u + g.inner b w w := by
    rw [ContinuousLinearMap.map_add (g.inner b) u w]
    rw [ContinuousLinearMap.add_apply]
    rw [(g.inner b u).map_add, (g.inner b w).map_add]
    ring
  have hp2 : g.inner b (u - w) (u - w) =
      g.inner b u u - g.inner b u w - g.inner b w u + g.inner b w w := by
    rw [ContinuousLinearMap.map_sub (g.inner b) u w]
    rw [ContinuousLinearMap.sub_apply]
    rw [(g.inner b u).map_sub, (g.inner b w).map_sub]
    ring
  rw [hp1, hp2, h_inner_sym]
  ring

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem ricciTensor_polar
    (g : SmoothRiemannianMetric I M) (b : M) (u w : TangentSpace I b) :
    ricciTensor (I := I) g b (u + w) (u + w) -
        ricciTensor (I := I) g b (u - w) (u - w) =
      4 * ricciTensor (I := I) g b u w := by
  classical
  have h_sym : ricciTensor (I := I) g b w u =
      ricciTensor (I := I) g b u w :=
    ricciTensor_symm (I := I) g b w u
  have hp1 : ricciTensor (I := I) g b (u + w) (u + w) =
      ricciTensor (I := I) g b u u + ricciTensor (I := I) g b u w +
        ricciTensor (I := I) g b w u + ricciTensor (I := I) g b w w := by
    rw [ContinuousLinearMap.map_add (ricciTensor (I := I) g b) u w]
    rw [ContinuousLinearMap.add_apply]
    rw [(ricciTensor (I := I) g b u).map_add,
      (ricciTensor (I := I) g b w).map_add]
    ring
  have hp2 : ricciTensor (I := I) g b (u - w) (u - w) =
      ricciTensor (I := I) g b u u - ricciTensor (I := I) g b u w -
        ricciTensor (I := I) g b w u + ricciTensor (I := I) g b w w := by
    rw [ContinuousLinearMap.map_sub (ricciTensor (I := I) g b) u w]
    rw [ContinuousLinearMap.sub_apply]
    rw [(ricciTensor (I := I) g b u).map_sub,
      (ricciTensor (I := I) g b w).map_sub]
    ring
  rw [hp1, hp2, h_sym]
  ring

def smoothCandidate_identification_target
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    Prop :=
  gradInnerLaplacianCandidateUnconditional (I := I) (M := M) g φ
      (smoothToH1Compl_mem_laplacianDomainPow_two (I := I) (M := M) g v) =
    smoothToLp (I := I) (M := M) g
      (gradInnerSmoothBundle (I := I) (M := M) g φ v).oneSubLapClassical

theorem smoothCase_via_candidate_identification
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_identify : smoothCandidate_identification_target
      (I := I) (M := M) g φ v) :
    gradInnerCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) =
      H1ComplToLp (I := I) (M := M) g
        (resolvent (I := I) (M := M) g
          (gradInnerLaplacianCandidateUnconditional (I := I) (M := M) g φ
            (smoothToH1Compl_mem_laplacianDomainPow_two
              (I := I) (M := M) g v))) := by
  rw [gradInnerCLM_smoothToH1Compl_eq_H1ComplToLp_resolvent_smoothCandidate]
  unfold smoothCandidate_identification_target at h_identify
  rw [h_identify]

end GradInnerLaplacianVariational
end Laplacian
end Analysis
end DifferentialGeometry

end
