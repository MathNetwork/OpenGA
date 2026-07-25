import DifferentialGeometry.Analysis.Elliptic.Regularity.GradInner.Laplacian.LpIdentity
import DifferentialGeometry.Analysis.Elliptic.Regularity.Hessian.LpClass
import DifferentialGeometry.Geometry.Curvature.Bochner.BochnerConcrete


noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace GradInnerLaplacianCandidate

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

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma smoothRicciPairing_contMDiff
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun b : M =>
      ricciTensor (I := I) g b
        (gradFun (I := I) g φ b) (gradFun (I := I) g v.toFun b)) := by
  classical
  have hRic :=
    ricciTensor_contMDiff (I := I) g
  have hGradφ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => gradFun (I := I) g φ b)) :=
    gradFun_contMDiff_total_section (I := I) g φ.contMDiff
  have hGradv : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => gradFun (I := I) g v.toFun b)) :=
    gradFun_contMDiff_total_section (I := I) g v.smooth
  have happ :
      ContMDiff I (I.prod 𝓘(ℝ, ℝ)) ∞
        (fun m : M => (⟨m,
            ricciTensor (I := I) g m
              (gradFun (I := I) g φ m)
              (gradFun (I := I) g v.toFun m)⟩ :
              TotalSpace ℝ (Bundle.Trivial M ℝ))) :=
    ContMDiff.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ)
      (b := id) hRic hGradφ hGradv
  intro m
  have hpm := happ m
  rw [Bundle.contMDiffAt_totalSpace] at hpm
  exact hpm.2

noncomputable def smoothRicciPairingBundle
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    SmoothScalar g where
  toFun := fun b => ricciTensor
    (I := I) g b
    (gradFun (I := I) g φ b) (gradFun (I := I) g v.toFun b)
  smooth := smoothRicciPairing_contMDiff (I := I) (M := M) g φ v

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma smoothRicciPairingBundle_apply
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    (v : SmoothScalar g) (b : M) :
    (smoothRicciPairingBundle (I := I) (M := M) g φ v).toFun b =
      ricciTensor (I := I) g b
        (gradFun (I := I) g φ b) (gradFun (I := I) g v.toFun b) := rfl

noncomputable def smoothRicciPairingLp
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  smoothToLp (I := I) (M := M) g (smoothRicciPairingBundle g φ v)

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma smoothRicciPairingLp_def
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    smoothRicciPairingLp (I := I) (M := M) g φ v =
      smoothToLp (I := I) (M := M) g
        (smoothRicciPairingBundle g φ v) := rfl

noncomputable def gradInnerLaplacianCandidate
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_ricci_part h_hess_part :
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  gradInnerCLM (I := I) (M := M) g φ u_h
    - gradInnerCLM (I := I) (M := M) g
        (smoothLaplacianBundle (I := I) (M := M) g φ) u_h
    - gradInnerCLM (I := I) (M := M) g φ
        (preimageLift (I := I) (M := M) g hu_h)
    - (2 : ℝ) • h_ricci_part
    - (2 : ℝ) • h_hess_part

omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem gradInnerLaplacianCandidate_def
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_ricci_part h_hess_part :
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    gradInnerLaplacianCandidate (I := I) (M := M) g φ hu_h
        h_ricci_part h_hess_part =
      gradInnerCLM (I := I) (M := M) g φ u_h
        - gradInnerCLM (I := I) (M := M) g
            (smoothLaplacianBundle (I := I) (M := M) g φ) u_h
        - gradInnerCLM (I := I) (M := M) g φ
            (preimageLift (I := I) (M := M) g hu_h)
        - (2 : ℝ) • h_ricci_part
        - (2 : ℝ) • h_hess_part := rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem gradInnerLaplacianCandidate_ricci_add
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_ricci_part1 h_ricci_part2 h_hess_part :
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    gradInnerLaplacianCandidate (I := I) (M := M) g φ hu_h
        (h_ricci_part1 + h_ricci_part2) h_hess_part =
      gradInnerLaplacianCandidate (I := I) (M := M) g φ hu_h
          h_ricci_part1 h_hess_part -
        (2 : ℝ) • h_ricci_part2 := by
  unfold gradInnerLaplacianCandidate
  rw [smul_add]
  abel

omit [NeZero (Module.finrank ℝ E)] in
theorem gradInnerLaplacianCandidate_hess_add
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_ricci_part h_hess_part1 h_hess_part2 :
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    gradInnerLaplacianCandidate (I := I) (M := M) g φ hu_h
        h_ricci_part (h_hess_part1 + h_hess_part2) =
      gradInnerLaplacianCandidate (I := I) (M := M) g φ hu_h
          h_ricci_part h_hess_part1 -
        (2 : ℝ) • h_hess_part2 := by
  unfold gradInnerLaplacianCandidate
  rw [smul_add]
  abel

omit [NeZero (Module.finrank ℝ E)] in
theorem gradInnerLaplacianCandidate_norm_lt_top
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_ricci_part h_hess_part :
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    eLpNorm
        ((gradInnerLaplacianCandidate (I := I) (M := M) g φ hu_h
            h_ricci_part h_hess_part : Lp ℝ 2 _) : M → ℝ) 2
        (riemannianVolumeMeasure (I := I) (M := M) g) < ⊤ :=
  (Lp.memLp _).2

omit [NeZero (Module.finrank ℝ E)] in
theorem gradInnerLaplacianCandidate_norm_le
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_ricci_part h_hess_part :
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    ‖gradInnerLaplacianCandidate (I := I) (M := M) g φ hu_h
        h_ricci_part h_hess_part‖ ≤
      ‖gradInnerCLM (I := I) (M := M) g φ u_h‖ +
      ‖gradInnerCLM (I := I) (M := M) g
        (smoothLaplacianBundle (I := I) (M := M) g φ) u_h‖ +
      ‖gradInnerCLM (I := I) (M := M) g φ
        (preimageLift (I := I) (M := M) g hu_h)‖ +
      2 * ‖h_ricci_part‖ +
      2 * ‖h_hess_part‖ := by
  unfold gradInnerLaplacianCandidate
  have hstep1 : ‖gradInnerCLM (I := I) (M := M) g φ u_h
        - gradInnerCLM (I := I) (M := M) g
            (smoothLaplacianBundle (I := I) (M := M) g φ) u_h
        - gradInnerCLM (I := I) (M := M) g φ
            (preimageLift (I := I) (M := M) g hu_h)
        - (2 : ℝ) • h_ricci_part
        - (2 : ℝ) • h_hess_part‖ ≤
      ‖gradInnerCLM (I := I) (M := M) g φ u_h
        - gradInnerCLM (I := I) (M := M) g
            (smoothLaplacianBundle (I := I) (M := M) g φ) u_h
        - gradInnerCLM (I := I) (M := M) g φ
            (preimageLift (I := I) (M := M) g hu_h)
        - (2 : ℝ) • h_ricci_part‖ +
      ‖(2 : ℝ) • h_hess_part‖ := by
    exact norm_sub_le _ _
  have hstep2 : ‖gradInnerCLM (I := I) (M := M) g φ u_h
        - gradInnerCLM (I := I) (M := M) g
            (smoothLaplacianBundle (I := I) (M := M) g φ) u_h
        - gradInnerCLM (I := I) (M := M) g φ
            (preimageLift (I := I) (M := M) g hu_h)
        - (2 : ℝ) • h_ricci_part‖ ≤
      ‖gradInnerCLM (I := I) (M := M) g φ u_h
        - gradInnerCLM (I := I) (M := M) g
            (smoothLaplacianBundle (I := I) (M := M) g φ) u_h
        - gradInnerCLM (I := I) (M := M) g φ
            (preimageLift (I := I) (M := M) g hu_h)‖ +
      ‖(2 : ℝ) • h_ricci_part‖ := by
    exact norm_sub_le _ _
  have hstep3 : ‖gradInnerCLM (I := I) (M := M) g φ u_h
        - gradInnerCLM (I := I) (M := M) g
            (smoothLaplacianBundle (I := I) (M := M) g φ) u_h
        - gradInnerCLM (I := I) (M := M) g φ
            (preimageLift (I := I) (M := M) g hu_h)‖ ≤
      ‖gradInnerCLM (I := I) (M := M) g φ u_h
        - gradInnerCLM (I := I) (M := M) g
            (smoothLaplacianBundle (I := I) (M := M) g φ) u_h‖ +
      ‖gradInnerCLM (I := I) (M := M) g φ
        (preimageLift (I := I) (M := M) g hu_h)‖ := by
    exact norm_sub_le _ _
  have hstep4 : ‖gradInnerCLM (I := I) (M := M) g φ u_h
        - gradInnerCLM (I := I) (M := M) g
            (smoothLaplacianBundle (I := I) (M := M) g φ) u_h‖ ≤
      ‖gradInnerCLM (I := I) (M := M) g φ u_h‖ +
      ‖gradInnerCLM (I := I) (M := M) g
        (smoothLaplacianBundle (I := I) (M := M) g φ) u_h‖ := by
    exact norm_sub_le _ _
  have h_smul_ricci : ‖(2 : ℝ) • h_ricci_part‖ = 2 * ‖h_ricci_part‖ := by
    rw [norm_smul]
    simp
  have h_smul_hess : ‖(2 : ℝ) • h_hess_part‖ = 2 * ‖h_hess_part‖ := by
    rw [norm_smul]
    simp
  linarith [hstep1, hstep2, hstep3, hstep4, h_smul_ricci, h_smul_hess,
    norm_nonneg (gradInnerCLM (I := I) (M := M) g φ u_h),
    norm_nonneg (gradInnerCLM (I := I) (M := M) g
      (smoothLaplacianBundle (I := I) (M := M) g φ) u_h),
    norm_nonneg (gradInnerCLM (I := I) (M := M) g φ
      (preimageLift (I := I) (M := M) g hu_h)),
    norm_nonneg ((2 : ℝ) • h_ricci_part),
    norm_nonneg ((2 : ℝ) • h_hess_part)]

omit [NeZero (Module.finrank ℝ E)] in
lemma smoothRicciPairingLp_coeFn
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    (smoothRicciPairingLp (I := I) (M := M) g φ v :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      (fun b : M =>
        ricciTensor (I := I) g b
          (gradFun (I := I) g φ b) (gradFun (I := I) g v.toFun b)) := by
  unfold smoothRicciPairingLp
  exact MemLp.coeFn_toLp
    (smoothRicciPairingBundle (I := I) (M := M) g φ v).memLp_two

end GradInnerLaplacianCandidate
end Laplacian
end Analysis
end DifferentialGeometry

end
