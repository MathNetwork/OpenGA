import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChartComponent.ComponentSobolevBound
import DifferentialGeometry.Analysis.Sobolev.Tensor.PouWeightedHsNorm
import DifferentialGeometry.Analysis.Sobolev.Chart.SmoothDensity.SmoothMulQuant
import DifferentialGeometry.Analysis.Sobolev.Chart.CrossChartBounds.CrossChartBoundStrictMemWkpHigherOrder
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Density
import DifferentialGeometry.Analysis.Integration.Measure.Family
import DifferentialGeometry.Analysis.Elliptic.Regularity.SmoothFChartResidual.BilinearBound

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace HebeyBlock

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Tensor
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [NeZero (Module.finrank ℝ E)] in
private lemma chartPushed_pou_mul_smooth_compactSupport
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (β : M) :
    ∃ v : EuclN → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) v ∧ HasCompactSupport v ∧
      tsupport v ⊆ chartTargetEuclid (I := I) (M := M) β ∧
      (chartPushed (I := I) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) β f)
        =ᵐ[(volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) β)] v := by
  classical
  set g_M : M → ℝ := fun x =>
    ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M β
      : C^∞⟮I, M; ℝ⟯) : M → ℝ) x * f x with hg_M_def
  have hPOU_smooth :
      ContMDiff I 𝓘(ℝ, ℝ) ∞
        (((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M β
          : C^∞⟮I, M; ℝ⟯) : M → ℝ)) :=
    (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M β
      : C^∞⟮I, M; ℝ⟯).contMDiff
  have hg_M_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ g_M := hPOU_smooth.mul hf
  have hg_M_supp : tsupport g_M ⊆ (chartAt H β).source := by
    have h_subset_pou_supp :
        tsupport g_M ⊆
          tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M β
            : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
      have h_eq : g_M = fun x =>
          ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M β
            : C^∞⟮I, M; ℝ⟯) : M → ℝ) x • f x := by
        funext x; rfl
      rw [h_eq]
      exact tsupport_smul_subset_left
        (f := fun x : M => ((DifferentialGeometry.Integral.Measure.chartAtlasPOU
          I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) (g := f)
    exact h_subset_pou_supp.trans
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M β)
  set v : EuclN → ℝ := chartPushedRaw I β g_M with hv_def
  refine ⟨v, ?_, ?_, ?_, ?_⟩
  · rw [hv_def]
    exact DifferentialGeometry.Analysis.Laplacian.SmoothFChartResidualBilinearBound.chartPushedRaw_contDiff
      (I := I) (M := M) (α := β) (u := g_M) hg_M_smooth hg_M_supp
  · rw [hv_def]
    exact DifferentialGeometry.Analysis.Laplacian.SmoothFChartResidualBilinearBound.chartPushedRaw_smooth_hasCompactSupport_local
      (I := I) (M := M) (α := β) (u := g_M) hg_M_supp
  · rw [hv_def]
    exact DifferentialGeometry.Analysis.Laplacian.SmoothFChartResidualBilinearBound.tsupport_chartPushedRaw_subset_chartTargetEuclid
      (I := I) (M := M) (α := β) (u := g_M) hg_M_supp
  · refine (ae_restrict_iff'
      (chartTargetEuclid_measurableSet (I := I) (M := M) β)).mpr ?_
    refine Filter.Eventually.of_forall ?_
    intro y hy
    rw [hv_def]
    exact chartPushed_eq_chartPushedRaw_pou_mul_on_target
      (I := I) (M := M)
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) β f hy

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorChartComponentScalar_memWkpChart
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    MemWkpChart (I := I) (M := M) g k 2
      (tensorChartComponentScalar (I := I) (M := M) g r s T α Idx Jdx) := by
  classical
  intro β
  have hf_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (tensorChartComponentScalar (I := I) (M := M) g r s T α Idx Jdx) :=
    tensorChartComponentScalar_contMDiff
      (I := I) (M := M) g r s T α Idx Jdx
  obtain ⟨v, hv_smooth, hv_cpt, hv_supp, hv_ae⟩ :=
    chartPushed_pou_mul_smooth_compactSupport
      (f := tensorChartComponentScalar (I := I) (M := M) g r s T α Idx Jdx)
      hf_smooth β
  have hp : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have hv_mem :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) k 2 v
        (chartTargetEuclid (I := I) (M := M) β) :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_of_smooth_compactSupport
      (d := Module.finrank ℝ E)
      (chartTargetEuclid_isOpen (I := I) (M := M) β) hv_smooth hv_cpt hv_supp hp k
  exact (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_congr_ae
    (d := Module.finrank ℝ E) hp
    (chartTargetEuclid_isOpen (I := I) (M := M) β) hv_ae.symm).mp hv_mem

end HebeyBlock
end RicciFlow
end PDE
end DifferentialGeometry
