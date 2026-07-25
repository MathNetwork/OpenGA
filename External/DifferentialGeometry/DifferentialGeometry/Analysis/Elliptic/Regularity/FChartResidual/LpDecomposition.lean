import DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.ResidualRegularity.BilinearH1ComplFromDomainPow
import DifferentialGeometry.Analysis.Elliptic.Regularity.LaplacianDomain.SmoothMulH1Compl
import DifferentialGeometry.Analysis.Elliptic.Regularity.LaplacianDomain.PerChart

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace ResidualLpDecomposition

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] in
lemma fHLeibnizGeneralResidualCLM_eq_fHLeibnizResidualLp
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) :
    leibnizCompensatedSourceResidualCLMOfSmoothFactor (I := I) (M := M) g
        (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) u_h =
      -((2 : ℝ) • gradInnerCLM (I := I) (M := M) g
          (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) u_h) -
        smoothMulLp (I := I) (M := M) g
          (laplacianOfChartPOU (I := I) (M := M) g α)
          (H1ComplToLp (I := I) (M := M) g u_h) := by
  classical
  rw [fHLeibnizGeneralResidualCLM_apply]
  rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem preimage_smoothMulH1Compl_eq_smoothMulLp_preimage_add_residual
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_dom : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    laplacianDomain.preimage (I := I) (M := M) g
        ⟨smoothMulH1Compl (I := I) (M := M) g
            (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) u_h,
          smoothMulH1Compl_mem_laplacianDomain (I := I) (M := M) g
            (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) hu_dom⟩ =
      smoothMulLp (I := I) (M := M) g
          (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
          (laplacianDomain.preimage (I := I) (M := M) g ⟨u_h, hu_dom⟩) +
        leibnizCompensatedSourceResidualCLMOfSmoothFactor (I := I) (M := M) g
          (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) u_h := by
  classical
  have h_preimage_smoothMulH1Compl :=
    laplacianDomain_preimage_smoothMulH1Compl (I := I) (M := M) g
      (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) hu_dom
  unfold leibnizCompensatedSourceOfSmoothFactor at h_preimage_smoothMulH1Compl
  have h_diff_eq :
      H1ComplToLp (I := I) (M := M) g u_h -
        laplacianOp (I := I) (M := M) g ⟨u_h, hu_dom⟩ =
      laplacianDomain.preimage (I := I) (M := M) g ⟨u_h, hu_dom⟩ := by
    rw [laplacianOp_apply]
    abel
  rw [h_diff_eq] at h_preimage_smoothMulH1Compl
  exact h_preimage_smoothMulH1Compl

omit [NeZero (Module.finrank ℝ E)] in
theorem fHLeibnizGeneralResidualCLM_eq_preimageDiff
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_dom : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    leibnizCompensatedSourceResidualCLMOfSmoothFactor (I := I) (M := M) g
        (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) u_h =
      laplacianDomain.preimage (I := I) (M := M) g
          ⟨smoothMulH1Compl (I := I) (M := M) g
              (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) u_h,
            smoothMulH1Compl_mem_laplacianDomain (I := I) (M := M) g
              (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) hu_dom⟩ -
        smoothMulLp (I := I) (M := M) g
          (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
          (laplacianDomain.preimage (I := I) (M := M) g ⟨u_h, hu_dom⟩) := by
  classical
  have h := preimage_smoothMulH1Compl_eq_smoothMulLp_preimage_add_residual
    (I := I) (M := M) g α hu_dom
  rw [h]
  abel

end ResidualLpDecomposition
end Laplacian
end Analysis
end DifferentialGeometry

end
