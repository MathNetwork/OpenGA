import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.RHS.DifferentiatedRHS.EigenvectorDifferentiatedRHS
import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.IteratedSobolevQuant

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Tensor.TensorRSRiemannian
open TensorRSNabla
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl
open DifferentialGeometry.Analysis.Sobolev.Chart
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

def diffNumeratorAggregate
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (fChartEffPrev : EuclN → ℝ) : ℝ≥0∞ :=
  (∑ a : Fin (Module.finrank ℝ E),
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) 2 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
        (chartTargetEuclid (I := I) (M := M) α))
    + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) 2 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ m (Fin.init l))
        (chartTargetEuclid (I := I) (M := M) α)
    + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) 1 2 fChartEffPrev
        (chartTargetEuclid (I := I) (M := M) α)
    + eLpNorm fChartEffPrev 2
        ((volume : Measure EuclN).restrict
          (chartPouKernel (I := I) (M := M) α))

section AtomBoundsUnconditional

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (i : TensorEigenIdx (I := I) (M := M) g r s)
  (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
  (l : Fin (m + 1) → Fin (Module.finrank ℝ E))

omit [CompleteSpace E] in
lemma eLpNorm_iteratedPartial_succ_le
    (a : Fin (Module.finrank ℝ E)) :
    eLpNorm (eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l))) 2
      ((volume : Measure EuclN).restrict
        (chartPouKernel (I := I) (M := M) α))
      ≤ iteratedWeakSobolevNorm (d := Module.finrank ℝ E) 2 2
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
          (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have hK_meas : MeasurableSet (chartPouKernel (I := I) (M := M) α) :=
    chartPouKernel_measurableSet (I := I) (M := M) α
  have hK_in : chartPouKernel (I := I) (M := M) α ⊆
      chartTargetEuclid (I := I) (M := M) α :=
    chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
  have h_eq : (volume : Measure EuclN).restrict
        (chartPouKernel (I := I) (M := M) α) =
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)).restrict
        (chartPouKernel (I := I) (M := M) α) := by
    rw [Measure.restrict_restrict hK_meas,
      Set.inter_eq_self_of_subset_left hK_in]
  rw [h_eq]
  refine le_trans (eLpNorm_mono_measure _
    (Measure.restrict_le_self)) ?_
  exact eLpNorm_le_wkpNorm (d := Module.finrank ℝ E) 2 2
    (chartTargetEuclid (I := I) (M := M) α) _

omit [CompleteSpace E] in
lemma eLpNorm_iteratedPartial_le :
    eLpNorm (eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s i α P₀ m (Fin.init l)) 2
      ((volume : Measure EuclN).restrict
        (chartPouKernel (I := I) (M := M) α))
      ≤ iteratedWeakSobolevNorm (d := Module.finrank ℝ E) 2 2
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ m (Fin.init l))
          (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have hK_meas : MeasurableSet (chartPouKernel (I := I) (M := M) α) :=
    chartPouKernel_measurableSet (I := I) (M := M) α
  have hK_in : chartPouKernel (I := I) (M := M) α ⊆
      chartTargetEuclid (I := I) (M := M) α :=
    chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
  have h_eq : (volume : Measure EuclN).restrict
        (chartPouKernel (I := I) (M := M) α) =
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)).restrict
        (chartPouKernel (I := I) (M := M) α) := by
    rw [Measure.restrict_restrict hK_meas,
      Set.inter_eq_self_of_subset_left hK_in]
  rw [h_eq]
  refine le_trans (eLpNorm_mono_measure _
    (Measure.restrict_le_self)) ?_
  exact eLpNorm_le_wkpNorm (d := Module.finrank ℝ E) 2 2
    (chartTargetEuclid (I := I) (M := M) α) _

omit [CompleteSpace E] in
lemma eLpNorm_chosenWeakPartial_iteratedPartial_succ_le
    (a b : Fin (Module.finrank ℝ E)) :
    eLpNorm (chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
        (chartTargetEuclid (I := I) (M := M) α)) 2
      ((volume : Measure EuclN).restrict
        (chartPouKernel (I := I) (M := M) α))
      ≤ iteratedWeakSobolevNorm (d := Module.finrank ℝ E) 2 2
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
          (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hK_meas : MeasurableSet (chartPouKernel (I := I) (M := M) α) :=
    chartPouKernel_measurableSet (I := I) (M := M) α
  have hK_in : chartPouKernel (I := I) (M := M) α ⊆ Ω :=
    chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
  have h_eq : (volume : Measure EuclN).restrict
        (chartPouKernel (I := I) (M := M) α) =
      ((volume : Measure EuclN).restrict Ω).restrict
        (chartPouKernel (I := I) (M := M) α) := by
    rw [Measure.restrict_restrict hK_meas,
      Set.inter_eq_self_of_subset_left hK_in]
  rw [h_eq]
  refine le_trans (eLpNorm_mono_measure _ (Measure.restrict_le_self)) ?_
  refine le_trans (eLpNorm_le_wkpNorm (d := Module.finrank ℝ E) 1 2 Ω _) ?_
  exact wkpNorm_chosenWeakPartial_le (d := Module.finrank ℝ E) 1 hΩ_open _ b

end AtomBoundsUnconditional

omit [CompleteSpace E] in
lemma iter_memLp_volume_restrict
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (m : ℕ) (l : Fin m → Fin (Module.finrank ℝ E))
    {K : Set EuclN} (hK_meas : MeasurableSet K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    MemLp (eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s i α P₀ m l) 2
      ((volume : Measure EuclN).restrict K) := by
  have h_global := eigenvectorChartIteratedPartial_memLp_volume
    (I := I) (M := M) g r s i α P₀ m l
  have h_eq : ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)).restrict K =
      (volume : Measure EuclN).restrict K := by
    rw [Measure.restrict_restrict hK_meas]
    exact congrArg _ (Set.inter_eq_self_of_subset_left hK_in)
  exact h_eq ▸ h_global.restrict K

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
