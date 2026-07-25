import DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.ResidualRegularity.BilinearH1ComplFromDomainPow
import DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.ResidualRegularity.BilinearH1ComplFromDomainPow2
import DifferentialGeometry.Analysis.Elliptic.Regularity.FChartResidual.LpDecomposition
import DifferentialGeometry.Analysis.Elliptic.Regularity.GradInner.Laplacian.LpIdentity
import DifferentialGeometry.Analysis.Elliptic.Regularity.GradInner.Laplacian.DensityExtension
import DifferentialGeometry.Analysis.Elliptic.Regularity.GradInner.Laplacian.IntegralForm
import DifferentialGeometry.Analysis.Sobolev.Chart.SmoothDensity.SmoothMul

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace DiffChartBilinearH1ComplFinal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainChartData
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul
open DifferentialGeometry.Analysis.Laplacian.GradInnerLpIdentity
open DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational
open DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianDensityExtension
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl
open DifferentialGeometry.Analysis.Sobolev.Chart

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] in
theorem gradInnerCLM_mem_image_smooth
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    gradInnerCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) ∈
      Set.image (H1ComplToLp (I := I) (M := M) g)
        (laplacianDomain (I := I) (M := M) g : Set (H1Compl g)) :=
  gradInnerCLM_smoothToH1Compl_mem_image_laplacianDomain
    (I := I) (M := M) g φ v

theorem gradInnerCLM_mem_image_density
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
        (h_smooth_seq n)) :
    gradInnerCLM (I := I) (M := M) g φ u_h ∈
      Set.image (H1ComplToLp (I := I) (M := M) g)
        (laplacianDomain (I := I) (M := M) g : Set (H1Compl g)) :=
  gradInnerCLM_mem_image_laplacianDomain_via_density
    (I := I) (M := M) g φ hu_h h_smooth_seq h_conv_H1Compl
    h_conv_candidate h_smooth_identity

omit [NeZero (Module.finrank ℝ E)] in
theorem smoothMulH1Compl_mem_pow_two_smooth
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    smoothMulH1Compl (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) ∈
      laplacianDomainPow (I := I) (M := M) g 2 :=
  smoothMulH1Compl_smoothToH1Compl_mem_laplacianDomainPow_two
    (I := I) (M := M) g φ v

theorem smoothMulH1Compl_mem_pow_two_density
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
        (h_smooth_seq n)) :
    smoothMulH1Compl (I := I) (M := M) g φ u_h ∈
      laplacianDomainPow (I := I) (M := M) g 2 :=
  smoothMulH1Compl_mem_pow_two_via_density
    (I := I) (M := M) g φ hu_h h_smooth_seq h_conv_H1Compl
    h_conv_candidate h_smooth_identity

private lemma rhoAlpha_mul_preimage_coeFn_memWkpChart_two_two
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g 2 2
      (fun x : M => (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x *
        ((laplacianDomain.preimage (I := I) (M := M) g
            ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
              (I := I) (M := M) g 1 hu_h⟩ :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x) := by
  classical
  have h_preimage_h2 := (laplacianDomainPow_two_h2_plus_rhs_h2
    (I := I) (M := M) g hu_h).2.1
  exact DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart_smooth_mul
    (I := I) (M := M) g (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) h_preimage_h2

theorem fHLeibnizResidualLp_coeFn_memWkpChart_two_two_of_mem
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_mem : smoothMulH1Compl (I := I) (M := M) g
        (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) u_h ∈
      laplacianDomainPow (I := I) (M := M) g 2) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g 2 2
      (fun x : M =>
        ((laplacianDomain.preimage (I := I) (M := M) g
            ⟨smoothMulH1Compl (I := I) (M := M) g
                (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) u_h,
              smoothMulH1Compl_mem_laplacianDomain (I := I) (M := M) g
                (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
                (laplacianDomainPow_succ_subset_laplacianDomain
                  (I := I) (M := M) g 1 hu_h)⟩ :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x -
        (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x *
          ((laplacianDomain.preimage (I := I) (M := M) g
              ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
                (I := I) (M := M) g 1 hu_h⟩ :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x) := by
  classical
  have h_smHC_h2 := (laplacianDomainPow_two_h2_plus_rhs_h2
    (I := I) (M := M) g h_mem).2.1
  have h_smoothMul_h2 := rhoAlpha_mul_preimage_coeFn_memWkpChart_two_two
    (I := I) (M := M) g α hu_h
  have h_preimage_eq :
      laplacianDomain.preimage (I := I) (M := M) g
          ⟨smoothMulH1Compl (I := I) (M := M) g
              (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) u_h,
            smoothMulH1Compl_mem_laplacianDomain (I := I) (M := M) g
              (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
              (laplacianDomainPow_succ_subset_laplacianDomain
                (I := I) (M := M) g 1 hu_h)⟩ =
      laplacianDomain.preimage (I := I) (M := M) g
        ⟨smoothMulH1Compl (I := I) (M := M) g
            (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) u_h,
          laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 h_mem⟩ := rfl
  rw [h_preimage_eq]
  exact DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart_sub
    (I := I) (M := M) g (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    h_smHC_h2 h_smoothMul_h2

theorem fHLeibnizResidualLp_coeFn_memWkpChart_two_two_density
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_smooth_seq : ℕ → SmoothScalar g)
    (h_conv_H1Compl : Tendsto
      (fun n => smoothToH1Compl (I := I) (M := M) g (h_smooth_seq n))
      atTop (𝓝 u_h))
    (h_conv_candidate : Tendsto
      (fun n => gradInnerLaplacianCandidateUnconditional (I := I) (M := M) g
        (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
        (smoothToH1Compl_mem_laplacianDomainPow_two
          (I := I) (M := M) g (h_smooth_seq n)))
      atTop (𝓝 (gradInnerLaplacianCandidateUnconditional
        (I := I) (M := M) g
        (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) hu_h)))
    (h_smooth_identity : ∀ n,
      smoothCandidate_identification_target (I := I) (M := M) g
        (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) (h_smooth_seq n)) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g 2 2
      (fun x : M =>
        ((laplacianDomain.preimage (I := I) (M := M) g
            ⟨smoothMulH1Compl (I := I) (M := M) g
                (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) u_h,
              smoothMulH1Compl_mem_laplacianDomain (I := I) (M := M) g
                (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
                (laplacianDomainPow_succ_subset_laplacianDomain
                  (I := I) (M := M) g 1 hu_h)⟩ :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x -
        (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x *
          ((laplacianDomain.preimage (I := I) (M := M) g
              ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
                (I := I) (M := M) g 1 hu_h⟩ :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x) := by
  classical
  have h_mem := smoothMulH1Compl_mem_pow_two_density
    (I := I) (M := M) g (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) hu_h
    h_smooth_seq h_conv_H1Compl h_conv_candidate h_smooth_identity
  exact fHLeibnizResidualLp_coeFn_memWkpChart_two_two_of_mem
    (I := I) (M := M) g α hu_h h_mem

noncomputable def diffChartBilinearH1ComplData_of_laplacianDomainPow_two_density
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (_h_smooth_seq : ℕ → SmoothScalar g)
    (_h_conv_H1Compl : Tendsto
      (fun n => smoothToH1Compl (I := I) (M := M) g (_h_smooth_seq n))
      atTop (𝓝 u_h))
    (_h_conv_candidate : Tendsto
      (fun n => gradInnerLaplacianCandidateUnconditional (I := I) (M := M) g
        (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
        (smoothToH1Compl_mem_laplacianDomainPow_two
          (I := I) (M := M) g (_h_smooth_seq n)))
      atTop (𝓝 (gradInnerLaplacianCandidateUnconditional
        (I := I) (M := M) g
        (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) hu_h)))
    (_h_smooth_identity : ∀ n,
      smoothCandidate_identification_target (I := I) (M := M) g
        (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) (_h_smooth_seq n))
    (direction : Fin (Module.finrank ℝ E))
    (h_residual_memW1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (fChartResidual (I := I) (M := M) g α u_h)
      (chartTargetEuclid (I := I) (M := M) α))
    (h_identity :
      ∀ ψ : EuclN → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α →
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                (chosenSecondPartialChartPushedU
                  (I := I) (M := M) g α u_h i direction) y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN)) +
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
              (laplacianDomainPow_succ_subset_laplacianDomain
                (I := I) (M := M) g 1 hu_h)).weak_partial direction y * ψ y
          ∂(volume : Measure EuclN)) =
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            chosenFChartDeriv (I := I) (M := M) g α hu_h direction y * ψ y
          ∂(volume : Measure EuclN)) -
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramDerivOnEuclid (I := I) g α i j direction y *
                (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
                  (laplacianDomainPow_succ_subset_laplacianDomain
                    (I := I) (M := M) g 1 hu_h)).weak_partial i y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN)) -
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityDerivOnEuclid (I := I) g α direction y *
            (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
              (laplacianDomainPow_succ_subset_laplacianDomain
                (I := I) (M := M) g 1 hu_h)).u_chart y * ψ y
          ∂(volume : Measure EuclN)) +
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityDerivOnEuclid (I := I) g α direction y *
            (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
              (laplacianDomainPow_succ_subset_laplacianDomain
                (I := I) (M := M) g 1 hu_h)).f_chart y * ψ y
          ∂(volume : Measure EuclN))) :
    DiffChartBilinearH1ComplData (I := I) (M := M) g α :=
  diffChartBilinearH1ComplData_of_laplacianDomainPow_two_via_residual
    (I := I) (M := M) g α hu_h direction h_residual_memW1p h_identity

end DiffChartBilinearH1ComplFinal
end Laplacian
end Analysis
end DifferentialGeometry

end
