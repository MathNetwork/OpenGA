import DifferentialGeometry.Analysis.Elliptic.Regularity.GradInner.Laplacian.Variational

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace GradInnerLaplacianFinal

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
open DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

noncomputable def gradInnerCLM_imageLap_witness
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    H1Compl (I := I) (M := M) g :=
  resolvent (I := I) (M := M) g
    (gradInnerLaplacianCandidateUnconditional (I := I) (M := M) g φ hu_h)

theorem gradInnerCLM_imageLap_witness_mem_laplacianDomain
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    gradInnerCLM_imageLap_witness (I := I) (M := M) g φ hu_h ∈
      laplacianDomain (I := I) (M := M) g := by
  unfold gradInnerCLM_imageLap_witness
  exact (laplacianDomain_mem_iff (I := I) (M := M) g).mpr
    ⟨gradInnerLaplacianCandidateUnconditional (I := I) (M := M) g φ hu_h, rfl⟩

theorem gradInnerCLM_mem_image_laplacianDomain_of_variational
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (hvar_id :
      gradInnerCLM (I := I) (M := M) g φ u_h =
        H1ComplToLp (I := I) (M := M) g
          (gradInnerCLM_imageLap_witness (I := I) (M := M) g φ hu_h)) :
    gradInnerCLM (I := I) (M := M) g φ u_h ∈
      Set.image (H1ComplToLp (I := I) (M := M) g)
        (laplacianDomain (I := I) (M := M) g : Set (H1Compl g)) :=
  ⟨gradInnerCLM_imageLap_witness (I := I) (M := M) g φ hu_h,
    gradInnerCLM_imageLap_witness_mem_laplacianDomain
      (I := I) (M := M) g φ hu_h, hvar_id.symm⟩

theorem gradInnerCLM_imageLap_witness_eq_resolvent_candidate
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    gradInnerCLM_imageLap_witness (I := I) (M := M) g φ hu_h =
      resolvent (I := I) (M := M) g
        (gradInnerLaplacianCandidateUnconditional
          (I := I) (M := M) g φ hu_h) := rfl

theorem variational_identity_implies_mem_image
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
        (laplacianDomain (I := I) (M := M) g : Set (H1Compl g)) :=
  gradInnerCLM_eq_H1ComplToLp_resolvent_of_variational
    (I := I) (M := M) g φ hu_h hvar_id

theorem gradInnerCLM_smoothCase_eq_resolventL2_candidate
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_identify : smoothCandidate_identification_target
      (I := I) (M := M) g φ v) :
    gradInnerCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) =
      H1ComplToLp (I := I) (M := M) g
        (resolvent (I := I) (M := M) g
          (gradInnerLaplacianCandidateUnconditional (I := I) (M := M) g φ
            (smoothToH1Compl_mem_laplacianDomainPow_two
              (I := I) (M := M) g v))) :=
  smoothCase_via_candidate_identification
    (I := I) (M := M) g φ v h_identify

theorem gradInnerCLM_smoothCase_mem_image_laplacianDomain_via_candidate
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_identify : smoothCandidate_identification_target
      (I := I) (M := M) g φ v) :
    gradInnerCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) ∈
      Set.image (H1ComplToLp (I := I) (M := M) g)
        (laplacianDomain (I := I) (M := M) g : Set (H1Compl g)) :=
  variational_identity_implies_mem_image (I := I) (M := M) g φ
    (smoothToH1Compl_mem_laplacianDomainPow_two (I := I) (M := M) g v)
    (gradInnerCLM_smoothCase_eq_resolventL2_candidate
      (I := I) (M := M) g φ v h_identify)

omit [NeZero (Module.finrank ℝ E)] in
theorem gradInnerCLM_smoothCase_mem_image_laplacianDomain
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    gradInnerCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) ∈
      Set.image (H1ComplToLp (I := I) (M := M) g)
        (laplacianDomain (I := I) (M := M) g : Set (H1Compl g)) :=
  gradInnerCLM_mem_image_laplacianDomain_smooth (I := I) (M := M) g φ v

omit [NeZero (Module.finrank ℝ E)] in
theorem smoothMulH1Compl_smoothToH1Compl_mem_laplacianDomainPow_two_unconditional
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    smoothMulH1Compl (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) ∈
      laplacianDomainPow (I := I) (M := M) g 2 :=
  smoothMulH1Compl_smoothToH1Compl_mem_laplacianDomainPow_two
    (I := I) (M := M) g φ v

omit [NeZero (Module.finrank ℝ E)] in
theorem mem_image_laplacianDomain_iff_smoothMulH1Compl_mem_pow_two
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    gradInnerCLM (I := I) (M := M) g φ u_h ∈
      Set.image (H1ComplToLp (I := I) (M := M) g)
        (laplacianDomain (I := I) (M := M) g : Set (H1Compl g)) ↔
      smoothMulH1Compl (I := I) (M := M) g φ u_h ∈
        laplacianDomainPow (I := I) (M := M) g 2 := by
  rw [← smoothMulH1Compl_mem_pow_two_iff_gradInnerCLM_mem_image
    (I := I) (M := M) g φ hu_h]

omit [NeZero (Module.finrank ℝ E)] in
theorem gradInnerCLM_mem_image_laplacianDomain_of_iteratedClosure
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_sM : smoothMulH1Compl (I := I) (M := M) g φ u_h ∈
      laplacianDomainPow (I := I) (M := M) g 2) :
    gradInnerCLM (I := I) (M := M) g φ u_h ∈
      Set.image (H1ComplToLp (I := I) (M := M) g)
        (laplacianDomain (I := I) (M := M) g : Set (H1Compl g)) :=
  gradInnerCLM_mem_image_of_smoothMulH1Compl_mem_pow_two
    (I := I) (M := M) g φ hu_h h_sM

omit [NeZero (Module.finrank ℝ E)] in
theorem smoothMulH1Compl_mem_pow_two_iff_via_candidate_resolvent
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    smoothMulH1Compl (I := I) (M := M) g φ u_h ∈
      laplacianDomainPow (I := I) (M := M) g 2 ↔
    gradInnerCLM (I := I) (M := M) g φ u_h ∈
      Set.image (H1ComplToLp (I := I) (M := M) g)
        (laplacianDomain (I := I) (M := M) g : Set (H1Compl g)) :=
  smoothMulH1Compl_mem_pow_two_iff_gradInnerCLM_mem_image
    (I := I) (M := M) g φ hu_h

theorem smoothMulH1Compl_mem_pow_two_of_variational_identity
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (hvar_id :
      gradInnerCLM (I := I) (M := M) g φ u_h =
        H1ComplToLp (I := I) (M := M) g
          (resolvent (I := I) (M := M) g
            (gradInnerLaplacianCandidateUnconditional
              (I := I) (M := M) g φ hu_h))) :
    smoothMulH1Compl (I := I) (M := M) g φ u_h ∈
      laplacianDomainPow (I := I) (M := M) g 2 := by
  have h_image := variational_identity_implies_mem_image
    (I := I) (M := M) g φ hu_h hvar_id
  exact (smoothMulH1Compl_mem_pow_two_iff_via_candidate_resolvent
    (I := I) (M := M) g φ hu_h).mpr h_image

end GradInnerLaplacianFinal
end Laplacian
end Analysis
end DifferentialGeometry

end
