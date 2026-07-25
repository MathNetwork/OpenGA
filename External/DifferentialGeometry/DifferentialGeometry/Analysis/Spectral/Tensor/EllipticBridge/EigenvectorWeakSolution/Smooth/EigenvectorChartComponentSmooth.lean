import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Regularity.EigenvectorArbitraryKRegularity
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Iterated.EigenvectorIteratedData
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Embedding.IteratedSobolevEmbedding

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.Chart hiding chartTargetEuclid
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Sobolev.EuclideanIteratedEmbedding

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

omit [CompleteSpace E] in
theorem eigenvectorChartComponent_exists_smooth_representative
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    ∃ u_smooth : EuclN → ℝ,
      ContDiffOn ℝ (∞ : WithTop ℕ∞) u_smooth
        (chartTargetEuclid (I := I) (M := M) α) ∧
      HasCompactSupport u_smooth ∧
      tsupport u_smooth ⊆ chartTargetEuclid (I := I) (M := M) α ∧
      u_smooth =ᵐ[(volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
        eigenvectorChartComponentFun (I := I) (M := M)
          g r s i α P₀ := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  set u : EuclN → ℝ :=
    eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀
    with hu_def
  set K : Set EuclN := chartPouKernel (I := I) (M := M) α with hK_def
  have hΩ_open : IsOpen Ω :=
    DifferentialGeometry.Analysis.Laplacian.MetricExtension.chartTargetEuclid_isOpen
      (I := I) (M := M) α
  have hK_compact : IsCompact K := chartPouKernel_isCompact (I := I) (M := M) α
  have hK_subset_Ω : K ⊆ Ω :=
    chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
  have hu_memWkp : ∀ k : ℕ,
      MemWkp (d := Module.finrank ℝ E) k 2 u Ω := fun k =>
    eigenvector_chartComponent_memWkp_arbitrary g r s i k α P₀
  obtain ⟨u₀, hu₀_cdiff, hu_ae_u₀⟩ :=
    contDiffOn_of_forall_memWkp_two (d := Module.finrank ℝ E) hΩ_open hu_memWkp
  obtain ⟨δ, η, hδ_pos, _hδ_subset, hη_cdiff, hη_cpt, _hη_range,
      hη_one_cthick, hη_tsupp⟩ :=
    exists_smooth_cutoff_with_neighborhood (d := Module.finrank ℝ E)
      hK_compact hΩ_open hK_subset_Ω
  have hη_one_K : ∀ y ∈ K, η y = 1 := fun y hy =>
    hη_one_cthick y (Metric.self_subset_cthickening _ hy)
  set u_smooth : EuclN → ℝ := fun y => η y * u₀ y with hu_smooth_def
  have hu_smooth_cdiff : ContDiffOn ℝ (∞ : WithTop ℕ∞) u_smooth Ω :=
    (hη_cdiff.contDiffOn).mul hu₀_cdiff
  have hu_smooth_cpt : HasCompactSupport u_smooth :=
    HasCompactSupport.mul_right hη_cpt
  have hu_smooth_tsupp : tsupport u_smooth ⊆ Ω :=
    (tsupport_mul_subset_left).trans hη_tsupp
  refine ⟨u_smooth, hu_smooth_cdiff, hu_smooth_cpt, hu_smooth_tsupp, ?_⟩
  have hu_ae_zero :
      u =ᵐ[(volume : Measure EuclN).restrict (Ω \ K)]
        (fun _ : EuclN => (0 : ℝ)) :=
    eigenvectorChartComponentFun_ae_zero_off_chartPouKernel
      g r s i α P₀
  have hK_closed : IsClosed K := hK_compact.isClosed
  have hΩK_open : IsOpen (Ω \ K) := hΩ_open.sdiff hK_closed
  have hΩK_subset : Ω \ K ⊆ Ω := Set.diff_subset
  have hu₀_ae_u_ΩK : u₀ =ᵐ[(volume : Measure EuclN).restrict (Ω \ K)] u :=
    Filter.EventuallyEq.symm
      (ae_restrict_of_ae_restrict_of_subset hΩK_subset hu_ae_u₀)
  have hu_smooth_ae_zero_ΩK :
      u_smooth =ᵐ[(volume : Measure EuclN).restrict (Ω \ K)]
        (fun _ : EuclN => (0 : ℝ)) := by
    have hu₀_ae_zero_ΩK :
        u₀ =ᵐ[(volume : Measure EuclN).restrict (Ω \ K)]
          (fun _ : EuclN => (0 : ℝ)) := hu₀_ae_u_ΩK.trans hu_ae_zero
    filter_upwards [hu₀_ae_zero_ΩK] with y hy
    simp [hu_smooth_def, hy]
  have hu_ae_u_smooth_ΩK :
      u =ᵐ[(volume : Measure EuclN).restrict (Ω \ K)] u_smooth :=
    hu_ae_zero.trans hu_smooth_ae_zero_ΩK.symm
  have hK_meas : MeasurableSet K := hK_closed.measurableSet
  have hu₀_ae_u_K : u₀ =ᵐ[(volume : Measure EuclN).restrict K] u :=
    Filter.EventuallyEq.symm
      (ae_restrict_of_ae_restrict_of_subset hK_subset_Ω hu_ae_u₀)
  have hu_smooth_ae_u₀_K :
      u_smooth =ᵐ[(volume : Measure EuclN).restrict K] u₀ := by
    refine (ae_restrict_iff' hK_meas).mpr ?_
    exact Filter.Eventually.of_forall fun y hy => by
      simp [hu_smooth_def, hη_one_K y hy]
  have hu_ae_u_smooth_K :
      u =ᵐ[(volume : Measure EuclN).restrict K] u_smooth :=
    (hu₀_ae_u_K.symm).trans hu_smooth_ae_u₀_K.symm
  have hΩ_eq : Ω = K ∪ (Ω \ K) := by
    rw [Set.union_diff_cancel hK_subset_Ω]
  have hu_ae_u_smooth :
      u =ᵐ[(volume : Measure EuclN).restrict Ω] u_smooth := by
    rw [hΩ_eq]
    exact (MeasureTheory.ae_restrict_union_iff K (Ω \ K)
      (fun x => u x = u_smooth x)).mpr ⟨hu_ae_u_smooth_K, hu_ae_u_smooth_ΩK⟩
  exact hu_ae_u_smooth.symm

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry
