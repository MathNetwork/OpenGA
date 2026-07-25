import DifferentialGeometry.Analysis.Elliptic.Regularity.Hessian.SmoothCaseLpClass
import DifferentialGeometry.Analysis.Elliptic.Regularity.GradInner.Laplacian.Smooth

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace GradInnerLaplacianSmoothCanonical

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
open DifferentialGeometry.Analysis.Laplacian.HessianPairingChart
open DifferentialGeometry.Analysis.Laplacian.HessianPairingLapDom
open DifferentialGeometry.Analysis.Laplacian.HessianBridgeSmoothLp
open DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaChristoffelDischarge
open DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianCandidate
open DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational
open DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM
open DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianFinal
open DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLpFull
open DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianSmoothFull

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

theorem gradInnerCLM_eq_H1ComplToLp_resolvent_unconditional_smooth_of_christoffel_discharge
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_transfer : perChartAeTransferableSmoothCase (I := I) (M := M) g φ v)
    (h_discharge : christoffelDischargeSmoothCase (I := I) (M := M) g φ v) :
    gradInnerCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) =
      H1ComplToLp (I := I) (M := M) g
        (resolvent (I := I) (M := M) g
          (gradInnerLaplacianCandidateUnconditional (I := I) (M := M) g φ
            (smoothToH1Compl_mem_laplacianDomainPow_two
              (I := I) (M := M) g v))) :=
  gradInnerCLM_eq_H1ComplToLp_resolvent_unconditional_smooth_of_hessHypothesis
    (I := I) (M := M) g φ v
    (hessPairingLpOnLapDom_eq_hessPairingSmoothLp_smoothCase_connector
      (I := I) (M := M) g φ v h_transfer h_discharge)

theorem smoothCase_full_unconditional_of_christoffel_discharge
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_transfer : perChartAeTransferableSmoothCase (I := I) (M := M) g φ v)
    (h_discharge : christoffelDischargeSmoothCase (I := I) (M := M) g φ v) :
    gradInnerCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) ∈
      Set.image (H1ComplToLp (I := I) (M := M) g)
        (laplacianDomain (I := I) (M := M) g : Set (H1Compl g)) :=
  smoothCase_full_unconditional_of_hessHypothesis
    (I := I) (M := M) g φ v
    (hessPairingLpOnLapDom_eq_hessPairingSmoothLp_smoothCase_connector
      (I := I) (M := M) g φ v h_transfer h_discharge)

theorem smoothMulH1Compl_smoothToH1Compl_mem_laplacianDomainPow_two_unconditional_of_christoffel_discharge
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_transfer : perChartAeTransferableSmoothCase (I := I) (M := M) g φ v)
    (h_discharge : christoffelDischargeSmoothCase (I := I) (M := M) g φ v) :
    smoothMulH1Compl (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) ∈
      laplacianDomainPow (I := I) (M := M) g 2 :=
  smoothMulH1Compl_smoothToH1Compl_mem_laplacianDomainPow_two_via_candidate
    (I := I) (M := M) g φ v
    (hessPairingLpOnLapDom_eq_hessPairingSmoothLp_smoothCase_connector
      (I := I) (M := M) g φ v h_transfer h_discharge)

theorem smoothCase_variational_identity_unconditional_of_christoffel_discharge
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_transfer : perChartAeTransferableSmoothCase (I := I) (M := M) g φ v)
    (h_discharge : christoffelDischargeSmoothCase (I := I) (M := M) g φ v) :
    gradInnerCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) =
      H1ComplToLp (I := I) (M := M) g
        (resolvent (I := I) (M := M) g
          (gradInnerLaplacianCandidateUnconditional (I := I) (M := M) g φ
            (smoothToH1Compl_mem_laplacianDomainPow_two
              (I := I) (M := M) g v))) :=
  gradInnerCLM_eq_H1ComplToLp_resolvent_unconditional_smooth_of_christoffel_discharge
    (I := I) (M := M) g φ v h_transfer h_discharge

theorem gradInnerCLM_eq_H1ComplToLp_resolvent_smoothCase_of_discharge
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_discharge : christoffelDischargeSmoothCase (I := I) (M := M) g φ v) :
    gradInnerCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) =
      H1ComplToLp (I := I) (M := M) g
        (resolvent (I := I) (M := M) g
          (gradInnerLaplacianCandidateUnconditional (I := I) (M := M) g φ
            (smoothToH1Compl_mem_laplacianDomainPow_two
              (I := I) (M := M) g v))) :=
  gradInnerCLM_eq_H1ComplToLp_resolvent_unconditional_smooth_of_christoffel_discharge
    (I := I) (M := M) g φ v
    (perChartAeTransferableSmoothCase_holds (I := I) (M := M) g φ v) h_discharge

theorem smoothCase_full_of_discharge
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_discharge : christoffelDischargeSmoothCase (I := I) (M := M) g φ v) :
    gradInnerCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) ∈
      Set.image (H1ComplToLp (I := I) (M := M) g)
        (laplacianDomain (I := I) (M := M) g : Set (H1Compl g)) :=
  smoothCase_full_unconditional_of_christoffel_discharge
    (I := I) (M := M) g φ v
    (perChartAeTransferableSmoothCase_holds (I := I) (M := M) g φ v) h_discharge

theorem smoothMulH1Compl_smoothToH1Compl_mem_laplacianDomainPow_two_of_discharge
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_discharge : christoffelDischargeSmoothCase (I := I) (M := M) g φ v) :
    smoothMulH1Compl (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) ∈
      laplacianDomainPow (I := I) (M := M) g 2 :=
  smoothMulH1Compl_smoothToH1Compl_mem_laplacianDomainPow_two_unconditional_of_christoffel_discharge
    (I := I) (M := M) g φ v
    (perChartAeTransferableSmoothCase_holds (I := I) (M := M) g φ v) h_discharge

theorem smoothCase_variational_identity_of_discharge
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_discharge : christoffelDischargeSmoothCase (I := I) (M := M) g φ v) :
    gradInnerCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) =
      H1ComplToLp (I := I) (M := M) g
        (resolvent (I := I) (M := M) g
          (gradInnerLaplacianCandidateUnconditional (I := I) (M := M) g φ
            (smoothToH1Compl_mem_laplacianDomainPow_two
              (I := I) (M := M) g v))) :=
  gradInnerCLM_eq_H1ComplToLp_resolvent_smoothCase_of_discharge
    (I := I) (M := M) g φ v h_discharge

end GradInnerLaplacianSmoothCanonical
end Laplacian
end Analysis
end DifferentialGeometry

end
