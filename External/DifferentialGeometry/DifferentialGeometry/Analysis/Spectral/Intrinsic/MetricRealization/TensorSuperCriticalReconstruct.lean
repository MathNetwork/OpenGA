import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.SpectralSmoothRepresentative
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.PouComponentBound.CutoffChartComponentMemWkp
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.EnergyBound.EigenvectorChartWeightedMemLp
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.LowerOrder.EigenvectorChartLowerOrderLimits
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Smooth.EigenvectorSmooth
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.Representation.TensorChartFrameSection
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.Representation.TensorL2ChartComponentExt
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.PouComponentBound.PouCutoffComponentBridge
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.ChartTransition.TensorChartTransition
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.ChartTransition.TensorChartTransitionTransport
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.ChartTransition.ChartTransitionTransportCLM
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.CovGrad.EigenvectorCovGradLeibniz
import DifferentialGeometry.Analysis.Sobolev.Chart.ChartTransition.QuasiMeasurePreserving
import DifferentialGeometry.Analysis.Sobolev.Chart.ChartTransition.ChartPullbackSmooth
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Embedding.IteratedSobolevEmbedding
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Density














































noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators Matrix
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral
namespace MetricRealization

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Sobolev.EuclideanIteratedEmbedding
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Analysis.Laplacian.MetricExtension hiding chartTargetEuclid

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E



omit [NeZero (Module.finrank ℝ E)] in
private lemma chartTargetEuclid_sdiff_chartPouKernel_isOpen' (α : M) :
    IsOpen (chartTargetEuclid (I := I) (M := M) α \
      chartPouKernel (I := I) (M := M) α) :=
  (DifferentialGeometry.Analysis.Laplacian.MetricExtension.chartTargetEuclid_isOpen
    (I := I) (M := M) α).sdiff
    (chartPouKernel_isCompact (I := I) (M := M) α).isClosed



omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma chartTargetEuclid_sdiff_chartPouKernel_subset' (α : M) :
    chartTargetEuclid (I := I) (M := M) α \
        chartPouKernel (I := I) (M := M) α ⊆
      chartTargetEuclid (I := I) (M := M) α :=
  Set.diff_subset




omit [NeZero (Module.finrank ℝ E)] in
private lemma superCriticalChartComponent_ae_zero_off_kernel
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (w : TensorL2 r s g) (α : M)
    (P₀ : DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorCompIdx
      (E := E) r s) :
    (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s w α P₀ :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α)] (fun _ : EuclN => (0 : ℝ)) := by
  classical
  have h_ae :
      ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
        y ∉ chartPouKernel (I := I) (M := M) α →
          ((tensorL2ChartComponent (I := I) (M := M) g r s w α P₀ :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y = 0 :=
    tensorL2ChartComponent_ae_zero_off_chartPouKernel
      (I := I) (M := M) g r s w α P₀
  have hV_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α \
      chartPouKernel (I := I) (M := M) α) :=
    (chartTargetEuclid_sdiff_chartPouKernel_isOpen' (I := I) (M := M) α).measurableSet
  have h_ae_V :
      ∀ᵐ y ∂((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α)),
        y ∉ chartPouKernel (I := I) (M := M) α →
          ((tensorL2ChartComponent (I := I) (M := M) g r s w α P₀ :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y = 0 := by
    refine ae_mono ?_ h_ae
    show (volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α) ≤
      chartL2Measure (I := I) (M := M) α
    rw [show chartL2Measure (I := I) (M := M) α =
        (volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α) from rfl]
    exact Measure.restrict_mono_set _
      (chartTargetEuclid_sdiff_chartPouKernel_subset' (I := I) (M := M) α)
  rw [Filter.EventuallyEq, ae_restrict_iff' hV_meas]
  filter_upwards [(ae_restrict_iff' hV_meas).mp h_ae_V] with y hy
  intro hy_V
  exact hy hy_V hy_V.2









theorem superCriticalChartComponent_exists_smooth_representative
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (w : TensorL2 r s g) (α : M)
    (P₀ : DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorCompIdx
      (E := E) r s)
    (h_all : ∀ k : ℕ,
      MemWkp (d := Module.finrank ℝ E) (2 * k) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s w α P₀ :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) α)) :
    ∃ u_smooth : EuclN → ℝ,
      ContDiffOn ℝ (∞ : WithTop ℕ∞) u_smooth
        (chartTargetEuclid (I := I) (M := M) α) ∧
      HasCompactSupport u_smooth ∧
      tsupport u_smooth ⊆ chartTargetEuclid (I := I) (M := M) α ∧
      u_smooth =ᵐ[(volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s w α P₀ :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  set u : EuclN → ℝ :=
    (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s w α P₀ :
      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) with hu_def
  set K : Set EuclN := chartPouKernel (I := I) (M := M) α with hK_def
  have hΩ_open : IsOpen Ω :=
    DifferentialGeometry.Analysis.Laplacian.MetricExtension.chartTargetEuclid_isOpen
      (I := I) (M := M) α
  have hK_compact : IsCompact K := chartPouKernel_isCompact (I := I) (M := M) α
  have hK_subset_Ω : K ⊆ Ω :=
    chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
  have hu_memWkp : ∀ k : ℕ,
      MemWkp (d := Module.finrank ℝ E) k 2 u Ω := by
    intro k
    exact MemWkp.le_of_le (d := Module.finrank ℝ E)
      (by omega : k ≤ 2 * k) (h_all k)
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
    superCriticalChartComponent_ae_zero_off_kernel
      (I := I) (M := M) g r s w α P₀
  have hK_closed : IsClosed K := hK_compact.isClosed
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

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)



private def wChartComp (w : TensorL2 r s g) (α : M)
    (P : TensorCompIdx (E := E) r s) : EuclN → ℝ :=
  fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s w α P :
    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y



private def chosenComp_w (w : TensorL2 r s g)
    (h_all : ∀ k : ℕ, ∀ (α : M) (P₀ : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (2 * k) 2
        (wChartComp (I := I) (M := M) g r s w α P₀)
        (chartTargetEuclid (I := I) (M := M) α))
    (α : M) (P : TensorCompIdx (E := E) r s) : EuclN → ℝ :=
  Classical.choose
    (superCriticalChartComponent_exists_smooth_representative
      (I := I) (M := M) g r s w α P (fun k => h_all k α P))



private lemma chosenComp_w_contDiffOn (w : TensorL2 r s g)
    (h_all : ∀ k : ℕ, ∀ (α : M) (P₀ : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (2 * k) 2
        (wChartComp (I := I) (M := M) g r s w α P₀)
        (chartTargetEuclid (I := I) (M := M) α))
    (α : M) (P : TensorCompIdx (E := E) r s) :
    ContDiffOn ℝ ∞ (chosenComp_w (I := I) (M := M) g r s w h_all α P)
      (chartTargetEuclid (I := I) (M := M) α) :=
  (Classical.choose_spec
    (superCriticalChartComponent_exists_smooth_representative
      (I := I) (M := M) g r s w α P (fun k => h_all k α P))).1


private lemma chosenComp_w_hasCompactSupport (w : TensorL2 r s g)
    (h_all : ∀ k : ℕ, ∀ (α : M) (P₀ : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (2 * k) 2
        (wChartComp (I := I) (M := M) g r s w α P₀)
        (chartTargetEuclid (I := I) (M := M) α))
    (α : M) (P : TensorCompIdx (E := E) r s) :
    HasCompactSupport (chosenComp_w (I := I) (M := M) g r s w h_all α P) :=
  (Classical.choose_spec
    (superCriticalChartComponent_exists_smooth_representative
      (I := I) (M := M) g r s w α P (fun k => h_all k α P))).2.1



private lemma chosenComp_w_tsupport (w : TensorL2 r s g)
    (h_all : ∀ k : ℕ, ∀ (α : M) (P₀ : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (2 * k) 2
        (wChartComp (I := I) (M := M) g r s w α P₀)
        (chartTargetEuclid (I := I) (M := M) α))
    (α : M) (P : TensorCompIdx (E := E) r s) :
    tsupport (chosenComp_w (I := I) (M := M) g r s w h_all α P) ⊆
      chartTargetEuclid (I := I) (M := M) α :=
  (Classical.choose_spec
    (superCriticalChartComponent_exists_smooth_representative
      (I := I) (M := M) g r s w α P (fun k => h_all k α P))).2.2.1




private lemma chosenComp_w_ae_eq (w : TensorL2 r s g)
    (h_all : ∀ k : ℕ, ∀ (α : M) (P₀ : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (2 * k) 2
        (wChartComp (I := I) (M := M) g r s w α P₀)
        (chartTargetEuclid (I := I) (M := M) α))
    (α : M) (P : TensorCompIdx (E := E) r s) :
    chosenComp_w (I := I) (M := M) g r s w h_all α P
      =ᵐ[(volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      wChartComp (I := I) (M := M) g r s w α P :=
  (Classical.choose_spec
    (superCriticalChartComponent_exists_smooth_representative
      (I := I) (M := M) g r s w α P (fun k => h_all k α P))).2.2.2



private lemma chosenComp_w_hu (w : TensorL2 r s g)
    (h_all : ∀ k : ℕ, ∀ (α : M) (P₀ : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (2 * k) 2
        (wChartComp (I := I) (M := M) g r s w α P₀)
        (chartTargetEuclid (I := I) (M := M) α))
    (α : M) :
    ∀ P : TensorCompIdx (E := E) r s,
      ContDiffOn ℝ ∞ (chosenComp_w (I := I) (M := M) g r s w h_all α P)
        (chartTargetEuclid (I := I) (M := M) α) :=
  fun P => chosenComp_w_contDiffOn (I := I) (M := M) g r s w h_all α P



private lemma chosenComp_w_hsupp (w : TensorL2 r s g)
    (h_all : ∀ k : ℕ, ∀ (α : M) (P₀ : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (2 * k) 2
        (wChartComp (I := I) (M := M) g r s w α P₀)
        (chartTargetEuclid (I := I) (M := M) α))
    (α : M) :
    ∀ P : TensorCompIdx (E := E) r s,
      HasCompactSupport (chosenComp_w (I := I) (M := M) g r s w h_all α P) ∧
        tsupport (chosenComp_w (I := I) (M := M) g r s w h_all α P) ⊆
          chartTargetEuclid (I := I) (M := M) α :=
  fun P => ⟨chosenComp_w_hasCompactSupport (I := I) (M := M) g r s w h_all α P,
    chosenComp_w_tsupport (I := I) (M := M) g r s w h_all α P⟩



private def wSmoothChart (w : TensorL2 r s g)
    (h_all : ∀ k : ℕ, ∀ (α : M) (P₀ : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (2 * k) 2
        (wChartComp (I := I) (M := M) g r s w α P₀)
        (chartTargetEuclid (I := I) (M := M) α))
    (α : M) : SmoothCcTensor g r s :=
  tensorBundleSectionOfChartComponents (I := I) (M := M) g r s α
    (chosenComp_w (I := I) (M := M) g r s w h_all α)
    (chosenComp_w_hu (I := I) (M := M) g r s w h_all α)
    (chosenComp_w_hsupp (I := I) (M := M) g r s w h_all α)




private lemma tensorChartComponentRaw_wSmoothChart_self (w : TensorL2 r s g)
    (h_all : ∀ k : ℕ, ∀ (α : M) (P₀ : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (2 * k) 2
        (wChartComp (I := I) (M := M) g r s w α P₀)
        (chartTargetEuclid (I := I) (M := M) α))
    (α : M) (P : TensorCompIdx (E := E) r s)
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    tensorChartComponentRaw (I := I) (M := M) g r s
        (wSmoothChart (I := I) (M := M) g r s w h_all α)
        α P.1 P.2 ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) =
      chosenComp_w (I := I) (M := M) g r s w h_all α P y :=
  tensorChartComponentRaw_tensorBundleSectionOfChartComponents
    (I := I) (M := M) g r s α
    (chosenComp_w (I := I) (M := M) g r s w h_all α)
    (chosenComp_w_hu (I := I) (M := M) g r s w h_all α)
    (chosenComp_w_hsupp (I := I) (M := M) g r s w h_all α) P hy



private lemma wSmoothChart_toSection_eq_zero_off_source (w : TensorL2 r s g)
    (h_all : ∀ k : ℕ, ∀ (α : M) (P₀ : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (2 * k) 2
        (wChartComp (I := I) (M := M) g r s w α P₀)
        (chartTargetEuclid (I := I) (M := M) α))
    (α : M) {x : M} (hx : x ∉ (chartAt H α).source) :
    (wSmoothChart (I := I) (M := M) g r s w h_all α).toSection x = 0 :=
  tensorBundleSectionOfChartComponents_toSection_eq_zero_off_source
    (I := I) (M := M) g r s α
    (chosenComp_w (I := I) (M := M) g r s w h_all α)
    (chosenComp_w_hu (I := I) (M := M) g r s w h_all α)
    (chosenComp_w_hsupp (I := I) (M := M) g r s w h_all α) hx



private lemma tensorChartComponentRaw_wSmoothChart_eq_zero_off_source
    (w : TensorL2 r s g)
    (h_all : ∀ k : ℕ, ∀ (α : M) (P₀ : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (2 * k) 2
        (wChartComp (I := I) (M := M) g r s w α P₀)
        (chartTargetEuclid (I := I) (M := M) α))
    (α β : M) (P : TensorCompIdx (E := E) r s) {x : M}
    (hx : x ∉ (chartAt H α).source) :
    tensorChartComponentRaw (I := I) (M := M) g r s
        (wSmoothChart (I := I) (M := M) g r s w h_all α)
        β P.1 P.2 x = 0 := by
  rw [tensorChartComponentRaw_def]
  have hsec : (wSmoothChart (I := I) (M := M) g r s w h_all α).toSection x = 0 :=
    wSmoothChart_toSection_eq_zero_off_source (I := I) (M := M) g r s w h_all α hx
  rw [show tensorTrivProj (I := I) (M := M) g r s
        (wSmoothChart (I := I) (M := M) g r s w h_all α) β x =
      (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) β).continuousLinearMapAt ℝ x
        ((wSmoothChart (I := I) (M := M) g r s w h_all α).toSection x)
      from rfl, hsec, map_zero, map_zero]




private def wSmooth (w : TensorL2 r s g)
    (h_all : ∀ k : ℕ, ∀ (α : M) (P₀ : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (2 * k) 2
        (wChartComp (I := I) (M := M) g r s w α P₀)
        (chartTargetEuclid (I := I) (M := M) α)) : SmoothCcTensor g r s :=
  ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
    wSmoothChart (I := I) (M := M) g r s w h_all α

private lemma wSmooth_eq (w : TensorL2 r s g)
    (h_all : ∀ k : ℕ, ∀ (α : M) (P₀ : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (2 * k) 2
        (wChartComp (I := I) (M := M) g r s w α P₀)
        (chartTargetEuclid (I := I) (M := M) α)) :
    wSmooth (I := I) (M := M) g r s w h_all =
      ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        wSmoothChart (I := I) (M := M) g r s w h_all α := rfl



omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma transportChartCenters_subset_chartAtlasPOU_finset' (β : M) :
    transportChartCenters (I := I) (M := M) β ⊆
      chartAtlasPOU_finset (I := I) (M := M) := by
  intro γ hγ
  rw [mem_transportChartCenters] at hγ
  rw [chartAtlasPOU_finset_mem]
  exact hγ.mono (Set.inter_subset_left)




private lemma ae_eq_of_ae_eq_restrict_of_eqOn_compl'
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f h : X → ℝ} {t : Set X} (ht : MeasurableSet t)
    (h_restrict : f =ᵐ[μ.restrict t] h)
    (h_compl : ∀ x, x ∉ t → f x = h x) :
    f =ᵐ[μ] h := by
  rw [Filter.EventuallyEq, MeasureTheory.ae_iff]
  have h_diff_subset : {x | ¬ f x = h x} ⊆ t := by
    intro x hx
    by_contra hxt
    exact hx (h_compl x hxt)
  have h_inter : {x | ¬ f x = h x} = {x | ¬ f x = h x} ∩ t :=
    (Set.inter_eq_left.mpr h_diff_subset).symm
  rw [Filter.EventuallyEq, MeasureTheory.ae_iff] at h_restrict
  rw [MeasureTheory.Measure.restrict_apply₀'] at h_restrict
  · rwa [h_inter]
  · exact ht.nullMeasurableSet


private lemma ite_finsetSum_eq_finsetSum_ite'
    {ι : Type*} (t : Finset ι) (p : Prop) [Decidable p] (f : ι → ℝ) :
    (if p then ∑ a ∈ t, f a else 0) = ∑ a ∈ t, (if p then f a else 0) := by
  by_cases hp : p
  · simp only [if_pos hp]
  · simp only [if_neg hp, Finset.sum_const_zero]

open Classical in



private lemma chartPushedRaw_ite_transitionSum_eq_finsetSum_w (w : TensorL2 r s g)
    (h_all : ∀ k : ℕ, ∀ (α : M) (P₀ : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (2 * k) 2
        (wChartComp (I := I) (M := M) g r s w α P₀)
        (chartTargetEuclid (I := I) (M := M) α))
    (α β : M) (P₀ : TensorCompIdx (E := E) r s) (y : EuclN) :
    chartPushedRaw I β
        (fun x => if x ∈ (chartAt H α).source then
          ∑ Q : TensorCompIdx (E := E) r s,
            transitionCoeff (E := E) (I := I) (M := M) r s α β P₀ Q x *
              tensorChartComponentRaw (I := I) (M := M) g r s
                (wSmoothChart (I := I) (M := M) g r s w h_all α)
                α Q.1 Q.2 x
          else 0) y =
      ∑ Q : TensorCompIdx (E := E) r s,
        chartPushedRaw I β
          (fun x => if x ∈ (chartAt H α).source then
            transitionCoeff (E := E) (I := I) (M := M) r s α β P₀ Q x *
              tensorChartComponentRaw (I := I) (M := M) g r s
                (wSmoothChart (I := I) (M := M) g r s w h_all α)
                α Q.1 Q.2 x
          else 0) y := by
  classical
  have h_ite :
      (fun x => if x ∈ (chartAt H α).source then
          ∑ Q : TensorCompIdx (E := E) r s,
            transitionCoeff (E := E) (I := I) (M := M) r s α β P₀ Q x *
              tensorChartComponentRaw (I := I) (M := M) g r s
                (wSmoothChart (I := I) (M := M) g r s w h_all α)
                α Q.1 Q.2 x
          else 0) =
        fun x => ∑ Q : TensorCompIdx (E := E) r s,
          (if x ∈ (chartAt H α).source then
            transitionCoeff (E := E) (I := I) (M := M) r s α β P₀ Q x *
              tensorChartComponentRaw (I := I) (M := M) g r s
                (wSmoothChart (I := I) (M := M) g r s w h_all α)
                α Q.1 Q.2 x
          else 0) := by
    funext x
    exact ite_finsetSum_eq_finsetSum_ite' (Finset.univ) _ _
  rw [h_ite]
  exact chartPushedRaw_finsetSum (I := I) (M := M) β
    (Finset.univ : Finset (TensorCompIdx (E := E) r s))
    (fun Q x => if x ∈ (chartAt H α).source then
      transitionCoeff (E := E) (I := I) (M := M) r s α β P₀ Q x *
        tensorChartComponentRaw (I := I) (M := M) g r s
          (wSmoothChart (I := I) (M := M) g r s w h_all α)
          α Q.1 Q.2 x
    else 0) y

open Classical in



private lemma raw_wSmoothChart_eq_ite (w : TensorL2 r s g)
    (h_all : ∀ k : ℕ, ∀ (α : M) (P₀ : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (2 * k) 2
        (wChartComp (I := I) (M := M) g r s w α P₀)
        (chartTargetEuclid (I := I) (M := M) α))
    (α β : M) (P₀ : TensorCompIdx (E := E) r s)
    {x : M} (hxβ : x ∈ (chartAt H β).source) :
    tensorChartComponentRaw (I := I) (M := M) g r s
        (wSmoothChart (I := I) (M := M) g r s w h_all α)
        β P₀.1 P₀.2 x =
      (if x ∈ (chartAt H α).source then
        ∑ Q : TensorCompIdx (E := E) r s,
          transitionCoeff (E := E) (I := I) (M := M) r s α β P₀ Q x *
            tensorChartComponentRaw (I := I) (M := M) g r s
              (wSmoothChart (I := I) (M := M) g r s w h_all α)
              α Q.1 Q.2 x
        else 0) := by
  classical
  by_cases hxα : x ∈ (chartAt H α).source
  · rw [if_pos hxα]
    exact tensorChartComponentRaw_eq_transitionCoeff_sum
      (E := E) (I := I) (M := M) g r s
      (wSmoothChart (I := I) (M := M) g r s w h_all α)
      α β P₀ ⟨hxα, hxβ⟩
  · rw [if_neg hxα]
    exact tensorChartComponentRaw_wSmoothChart_eq_zero_off_source
      (I := I) (M := M) g r s w h_all α β P₀ hxα

open Classical in



private lemma wSmoothChart_tensorL2ChartComponent_coeFn_aeEq (w : TensorL2 r s g)
    (h_all : ∀ k : ℕ, ∀ (α : M) (P₀ : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (2 * k) 2
        (wChartComp (I := I) (M := M) g r s w α P₀)
        (chartTargetEuclid (I := I) (M := M) α))
    (α β : M) (P₀ : TensorCompIdx (E := E) r s) :
    ((tensorL2ChartComponent (I := I) (M := M) g r s
        (wSmoothChart (I := I) (M := M) g r s w h_all α : TensorL2 r s g) β P₀ :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ)
      =ᵐ[chartL2Measure (I := I) (M := M) β]
      (fun y => chartPushedRaw I β
          (fun x => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) y *
        chartPushedRaw I β
          (fun x => if x ∈ (chartAt H α).source then
            ∑ Q : TensorCompIdx (E := E) r s,
              transitionCoeff (E := E) (I := I) (M := M) r s α β P₀ Q x *
                tensorChartComponentRaw (I := I) (M := M) g r s
                  (wSmoothChart (I := I) (M := M) g r s w h_all α)
                  α Q.1 Q.2 x
            else 0) y) := by
  classical
  have h_coeFn :=
    tensorL2ChartComponent_smoothToTensorL2_coeFn (I := I) (M := M) g r s
      (wSmoothChart (I := I) (M := M) g r s w h_all α) β P₀
  have h_mem : ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) β),
      y ∈ chartTargetEuclid (I := I) (M := M) β := by
    rw [chartL2Measure]
    exact ae_restrict_mem
      (DifferentialGeometry.Analysis.Laplacian.MetricExtension.chartTargetEuclid_isOpen
        (I := I) (M := M) β).measurableSet
  filter_upwards [h_coeFn, h_mem] with y hy_coe hy
  rw [hy_coe]
  rw [tensorChartComponent_eq_chartPushedRaw_pou_mul_chartPushedRaw_raw_on_target
    (I := I) (M := M) g r s
    (wSmoothChart (I := I) (M := M) g r s w h_all α)
    β P₀.1 P₀.2 hy]
  congr 1
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) β
      (tensorChartComponentRaw (I := I) (M := M) g r s
        (wSmoothChart (I := I) (M := M) g r s w h_all α)
        β P₀.1 P₀.2) hy,
    chartPushedRaw_apply_of_mem (I := I) (M := M) β
      (fun x => if x ∈ (chartAt H α).source then
        ∑ Q : TensorCompIdx (E := E) r s,
          transitionCoeff (E := E) (I := I) (M := M) r s α β P₀ Q x *
            tensorChartComponentRaw (I := I) (M := M) g r s
              (wSmoothChart (I := I) (M := M) g r s w h_all α)
              α Q.1 Q.2 x
        else 0) hy]
  exact raw_wSmoothChart_eq_ite (I := I) (M := M) g r s w h_all α β
    P₀ (symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) β hy)



private def chartKernelCutoffPushed (γ : M) : EuclN → ℝ :=
  chartPushedRaw (I := I) (M := M) γ
    (fun x => ((chartKernelCutoff (I := I) (M := M) γ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)



omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma chartKernelCutoffPushed_eq_one_on_chartPouKernel
    (γ : M) {y : EuclN}
    (hy : y ∈ chartPouKernel (I := I) (M := M) γ) :
    chartKernelCutoffPushed (I := I) (M := M) γ y = 1 := by
  classical
  rw [chartPouKernel] at hy
  obtain ⟨v, ⟨ww, hw_supp, hwv⟩, hvy⟩ := hy
  have hw_srcγ : ww ∈ (chartAt H γ).source :=
    (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M) γ hw_supp
  have hw_extsrc : ww ∈ (extChartAt I γ).source := by
    rw [extChartAt_source (I := I)]; exact hw_srcγ
  have hy_target : y ∈ chartTargetEuclid (I := I) (M := M) γ :=
    chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) γ
      ⟨v, ⟨ww, hw_supp, hwv⟩, hvy⟩
  have hsymm : (extChartAt I γ).symm ((toEuclidean (E := E)).symm y) = ww := by
    rw [← hvy, ← hwv, (toEuclidean (E := E)).symm_apply_apply,
      (extChartAt I γ).left_inv hw_extsrc]
  unfold chartKernelCutoffPushed
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) γ _ hy_target, hsymm]
  exact chartKernelCutoff_eqOn_one (I := I) (M := M) γ hw_supp



omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma chartKernelCutoffPushed_toEuclidean_extChartAt
    (γ : M) {z : M} (hz : z ∈ (chartAt H γ).source) :
    chartKernelCutoffPushed (I := I) (M := M) γ
        ((toEuclidean (E := E)) (extChartAt I γ z)) =
      ((chartKernelCutoff (I := I) (M := M) γ : C^∞⟮I, M; ℝ⟯) : M → ℝ) z := by
  unfold chartKernelCutoffPushed
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) γ _
      (toEuclidean_extChartAt_mem_chartTargetEuclid (I := I) (M := M) γ hz),
    symm_toEuclidean_symm_toEuclidean_extChartAt (I := I) (M := M) γ hz]




omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma chartPushedPouWeight_toEuclidean_extChartAt'
    (α : M) {z : M} (hz : z ∈ (chartAt H α).source) :
    chartPushedPouWeight (I := I) (M := M) α
        ((toEuclidean (E := E)) (extChartAt I α z)) =
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) z := by
  unfold chartPushedPouWeight
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _
      (toEuclidean_extChartAt_mem_chartTargetEuclid (I := I) (M := M) α hz),
    symm_toEuclidean_symm_toEuclidean_extChartAt (I := I) (M := M) α hz]




omit [NeZero (Module.finrank ℝ E)] in
private lemma wChartComp_ae_eq_chartKernelCutoffPushed_mul (w : TensorL2 r s g)
    (γ : M) (Q : TensorCompIdx (E := E) r s) :
    wChartComp (I := I) (M := M) g r s w γ Q
      =ᵐ[(volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) γ)]
      (fun y => chartKernelCutoffPushed (I := I) (M := M) γ y *
        wChartComp (I := I) (M := M) g r s w γ Q y) := by
  classical
  have hK_meas : MeasurableSet (chartPouKernel (I := I) (M := M) γ) :=
    chartPouKernel_measurableSet (I := I) (M := M) γ
  have h_on_K : ∀ᵐ y ∂((volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) γ)),
      y ∈ chartPouKernel (I := I) (M := M) γ →
        wChartComp (I := I) (M := M) g r s w γ Q y =
          chartKernelCutoffPushed (I := I) (M := M) γ y *
            wChartComp (I := I) (M := M) g r s w γ Q y := by
    refine Filter.Eventually.of_forall (fun y hy => ?_)
    rw [chartKernelCutoffPushed_eq_one_on_chartPouKernel (I := I) (M := M) γ hy,
      one_mul]
  have h_off_raw :
      wChartComp (I := I) (M := M) g r s w γ Q
        =ᵐ[(volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) γ \
              chartPouKernel (I := I) (M := M) γ)]
        (fun _ : EuclN => (0 : ℝ)) :=
    superCriticalChartComponent_ae_zero_off_kernel (I := I) (M := M) g r s w γ Q
  have h_off_restrict :
      wChartComp (I := I) (M := M) g r s w γ Q
        =ᵐ[((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) γ)).restrict
            (chartPouKernel (I := I) (M := M) γ)ᶜ]
        (fun _ : EuclN => (0 : ℝ)) := by
    have h_restrict_eq :
        ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) γ)).restrict
          (chartPouKernel (I := I) (M := M) γ)ᶜ =
        (volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) γ \
            chartPouKernel (I := I) (M := M) γ) := by
      rw [Measure.restrict_restrict hK_meas.compl, Set.inter_comm,
        ← Set.diff_eq]
    rw [h_restrict_eq]
    exact h_off_raw
  have h_off_K : ∀ᵐ y ∂((volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) γ)),
      y ∉ chartPouKernel (I := I) (M := M) γ →
        wChartComp (I := I) (M := M) g r s w γ Q y =
          chartKernelCutoffPushed (I := I) (M := M) γ y *
            wChartComp (I := I) (M := M) g r s w γ Q y := by
    have h_imp := (ae_restrict_iff' hK_meas.compl).mp h_off_restrict
    filter_upwards [h_imp] with y hy hy_off
    have hy_zero : wChartComp (I := I) (M := M) g r s w γ Q y = 0 := hy hy_off
    rw [hy_zero, mul_zero]
  filter_upwards [h_on_K, h_off_K] with y hy_on hy_off
  by_cases hy_mem : y ∈ chartPouKernel (I := I) (M := M) γ
  · exact hy_on hy_mem
  · exact hy_off hy_mem




private lemma chosenComp_w_comp_chartTransition_ae_eq (w : TensorL2 r s g)
    (h_all : ∀ k : ℕ, ∀ (α : M) (P₀ : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (2 * k) 2
        (wChartComp (I := I) (M := M) g r s w α P₀)
        (chartTargetEuclid (I := I) (M := M) α))
    (β γ : M) (Q : TensorCompIdx (E := E) r s) :
    (fun y => chosenComp_w (I := I) (M := M) g r s w h_all γ Q
        (chartTransitionEuclid (I := I) (M := M) β γ y))
      =ᵐ[(volume : Measure EuclN).restrict
          (chartOverlapEuclid (I := I) (M := M) β γ)]
      (fun y => wChartComp (I := I) (M := M) g r s w γ Q
        (chartTransitionEuclid (I := I) (M := M) β γ y)) := by
  have h_target := chosenComp_w_ae_eq (I := I) (M := M) g r s w h_all γ Q
  have h_overlap :
      chosenComp_w (I := I) (M := M) g r s w h_all γ Q
        =ᵐ[(volume : Measure EuclN).restrict
            (chartOverlapEuclid (I := I) (M := M) γ β)]
        wChartComp (I := I) (M := M) g r s w γ Q :=
    ae_mono (Measure.restrict_mono_set _
      (chartOverlapEuclid_subset_chartTarget (I := I) (M := M) γ β)) h_target
  exact chartTransitionEuclid_comp_ae_eq_restrict (I := I) (M := M) β γ h_overlap




omit [NeZero (Module.finrank ℝ E)] in
private lemma wChartComp_comp_chartTransition_ae_eq_cutoff_mul (w : TensorL2 r s g)
    (β γ : M) (Q : TensorCompIdx (E := E) r s) :
    (fun y => wChartComp (I := I) (M := M) g r s w γ Q
        (chartTransitionEuclid (I := I) (M := M) β γ y))
      =ᵐ[(volume : Measure EuclN).restrict
          (chartOverlapEuclid (I := I) (M := M) β γ)]
      (fun y => chartKernelCutoffPushed (I := I) (M := M) γ
          (chartTransitionEuclid (I := I) (M := M) β γ y) *
        wChartComp (I := I) (M := M) g r s w γ Q
          (chartTransitionEuclid (I := I) (M := M) β γ y)) := by
  have h_target :=
    wChartComp_ae_eq_chartKernelCutoffPushed_mul (I := I) (M := M) g r s w γ Q
  have h_overlap :
      wChartComp (I := I) (M := M) g r s w γ Q
        =ᵐ[(volume : Measure EuclN).restrict
            (chartOverlapEuclid (I := I) (M := M) γ β)]
        (fun y => chartKernelCutoffPushed (I := I) (M := M) γ y *
          wChartComp (I := I) (M := M) g r s w γ Q y) :=
    ae_mono (Measure.restrict_mono_set _
      (chartOverlapEuclid_subset_chartTarget (I := I) (M := M) γ β)) h_target
  exact chartTransitionEuclid_comp_ae_eq_restrict (I := I) (M := M) β γ h_overlap

open Classical in





private lemma wSmoothChart_transport_term_aeEq (w : TensorL2 r s g)
    (h_all : ∀ k : ℕ, ∀ (α : M) (P₀ : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (2 * k) 2
        (wChartComp (I := I) (M := M) g r s w α P₀)
        (chartTargetEuclid (I := I) (M := M) α))
    (β γ : M) (P₀ Q : TensorCompIdx (E := E) r s) :
    (fun y => chartPushedRaw I β
        (fun x => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) y *
      chartPushedRaw I β
        (fun x => if x ∈ (chartAt H γ).source then
          transitionCoeff (E := E) (I := I) (M := M) r s γ β P₀ Q x *
            tensorChartComponentRaw (I := I) (M := M) g r s
              (wSmoothChart (I := I) (M := M) g r s w h_all γ)
              γ Q.1 Q.2 x
          else 0) y)
      =ᵐ[chartL2Measure (I := I) (M := M) β]
    (fun y => chartPushedRaw I β
        (fun x => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) y *
      ((chartTransitionTransportCLM (I := I) (M := M) g r s γ β P₀ Q
          (tensorL2ChartComponent (I := I) (M := M) g r s w γ Q) :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) := by
  classical
  set W : EuclN → ℝ := fun y => chartPushedRaw I β
    (fun x => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) y with hW_def
  set A : EuclN → ℝ := fun y => chartPushedRaw I β
    (fun x => if x ∈ (chartAt H γ).source then
      transitionCoeff (E := E) (I := I) (M := M) r s γ β P₀ Q x *
        tensorChartComponentRaw (I := I) (M := M) g r s
          (wSmoothChart (I := I) (M := M) g r s w h_all γ)
          γ Q.1 Q.2 x
      else 0) y with hA_def
  set B : EuclN → ℝ := fun y =>
    ((chartTransitionTransportCLM (I := I) (M := M) g r s γ β P₀ Q
        (tensorL2ChartComponent (I := I) (M := M) g r s w γ Q) :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y with hB_def
  set RHS : EuclN → ℝ := fun y =>
    chartPushedRaw (I := I) (M := M) β
        (transportCoeffManifold (I := I) (M := M) g r s γ β P₀ Q) y *
      wChartComp (I := I) (M := M) g r s w γ Q
        (chartTransitionEuclid (I := I) (M := M) β γ y) with hRHS_def
  have hB_eq : B =ᵐ[chartL2Measure (I := I) (M := M) β] RHS := by
    have h := chartTransitionTransportCLM_coeFn_aeEq (I := I) (M := M) g r s γ β
      P₀ Q (tensorL2ChartComponent (I := I) (M := M) g r s w γ Q)
    exact h.trans (Filter.EventuallyEq.of_eq rfl)
  have h_goal : (fun y => W y * A y)
      =ᵐ[chartL2Measure (I := I) (M := M) β] (fun y => W y * RHS y) := by
    have hΩ_open : IsOpen (chartOverlapEuclid (I := I) (M := M) β γ) :=
      chartOverlapEuclid_isOpen (I := I) (M := M) β γ
    have hΩ_meas : MeasurableSet (chartOverlapEuclid (I := I) (M := M) β γ) :=
      hΩ_open.measurableSet
    have h_restrict_eq :
        (chartL2Measure (I := I) (M := M) β).restrict
          (chartOverlapEuclid (I := I) (M := M) β γ) =
        (volume : Measure EuclN).restrict
          (chartOverlapEuclid (I := I) (M := M) β γ) := by
      rw [chartL2Measure, Measure.restrict_restrict hΩ_meas,
        Set.inter_eq_left.mpr
          (chartOverlapEuclid_subset_chartTarget (I := I) (M := M) β γ)]
    have h_on_overlap : (fun y => W y * A y)
        =ᵐ[(chartL2Measure (I := I) (M := M) β).restrict
            (chartOverlapEuclid (I := I) (M := M) β γ)]
        (fun y => W y * RHS y) := by
      rw [h_restrict_eq]
      have h_mem : ∀ᵐ y ∂((volume : Measure EuclN).restrict
          (chartOverlapEuclid (I := I) (M := M) β γ)),
          y ∈ chartOverlapEuclid (I := I) (M := M) β γ :=
        ae_restrict_mem hΩ_meas
      have h_cc := chosenComp_w_comp_chartTransition_ae_eq
        (I := I) (M := M) g r s w h_all β γ Q
      have h_kc :=
        wChartComp_comp_chartTransition_ae_eq_cutoff_mul
          (I := I) (M := M) g r s w β γ Q
      filter_upwards [h_mem, h_cc, h_kc] with y hy_mem hy_cc hy_kc
      have hy_target : y ∈ chartTargetEuclid (I := I) (M := M) β :=
        chartOverlapEuclid_subset_chartTarget (I := I) (M := M) β γ hy_mem
      set z : M := (extChartAt I β).symm ((toEuclidean (E := E)).symm y)
        with hz_def
      have hz_srcβ : z ∈ (chartAt H β).source :=
        symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) β hy_target
      have hz_srcγ : z ∈ (chartAt H γ).source :=
        (mem_chartOverlapEuclid_iff_of_mem_chartTargetEuclid
          (I := I) (M := M) β γ hy_target).mp hy_mem
      set zγ : EuclN := (toEuclidean (E := E)) (extChartAt I γ z) with hzγ_def
      have hsymm_target : (toEuclidean (E := E)).symm y ∈
          (extChartAt I β).target := by
        rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy_target
        exact hy_target
      have hy_eq : (toEuclidean (E := E)) (extChartAt I β z) = y := by
        rw [hz_def, (extChartAt I β).right_inv hsymm_target]
        exact (toEuclidean (E := E)).apply_symm_apply y
      have hT_eq : chartTransitionEuclid (I := I) (M := M) β γ y = zγ := by
        rw [← hy_eq, hzγ_def]
        exact chartTransitionEuclid_eq_chartα_image (I := I) (M := M) β γ hz_srcβ
      have hA_y : A y =
          transitionCoeff (E := E) (I := I) (M := M) r s γ β P₀ Q z *
            chosenComp_w (I := I) (M := M) g r s w h_all γ Q zγ := by
        rw [hA_def]
        simp only
        rw [chartPushedRaw_apply_of_mem (I := I) (M := M) β _ hy_target,
          ← hz_def, if_pos hz_srcγ]
        congr 1
        have h_raw := tensorChartComponentRaw_wSmoothChart_self
          (I := I) (M := M) g r s w h_all γ Q
          (toEuclidean_extChartAt_mem_chartTargetEuclid (I := I) (M := M) γ
            hz_srcγ)
        rw [symm_toEuclidean_symm_toEuclidean_extChartAt
          (I := I) (M := M) γ hz_srcγ] at h_raw
        rw [h_raw, hzγ_def]
      have hRHS_y : RHS y =
          (((chartKernelCutoff (I := I) (M := M) β :
                C^∞⟮I, M; ℝ⟯) : M → ℝ) z *
            ((chartKernelCutoff (I := I) (M := M) γ :
                C^∞⟮I, M; ℝ⟯) : M → ℝ) z *
            transitionCoeff (E := E) (I := I) (M := M) r s γ β P₀ Q z) *
          wChartComp (I := I) (M := M) g r s w γ Q zγ := by
        rw [hRHS_def]
        simp only
        rw [chartPushedRaw_apply_of_mem (I := I) (M := M) β _ hy_target,
          ← hz_def, transportCoeffManifold_apply, hT_eq]
      have h_cutγ : chartKernelCutoffPushed (I := I) (M := M) γ zγ =
          ((chartKernelCutoff (I := I) (M := M) γ : C^∞⟮I, M; ℝ⟯) : M → ℝ) z := by
        rw [hzγ_def]
        exact chartKernelCutoffPushed_toEuclidean_extChartAt
          (I := I) (M := M) γ hz_srcγ
      rw [hT_eq] at hy_cc hy_kc
      rw [h_cutγ] at hy_kc
      set Eγ : ℝ := wChartComp (I := I) (M := M) g r s w γ Q zγ with hEγ_def
      rw [hA_y, hy_cc, hRHS_y]
      by_cases hWy : W y = 0
      · rw [hWy, zero_mul, zero_mul]
      · have hWy_val : W y =
            ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) z := by
          rw [hW_def]
          simp only
          rw [chartPushedRaw_apply_of_mem (I := I) (M := M) β _ hy_target,
            ← hz_def]
        have hz_pou : z ∈ tsupport
            (fun x : M => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) := by
          refine subset_tsupport _ ?_
          rw [Function.mem_support]
          rw [hWy_val] at hWy
          exact hWy
        have h_cutβ : ((chartKernelCutoff (I := I) (M := M) β :
            C^∞⟮I, M; ℝ⟯) : M → ℝ) z = 1 :=
          chartKernelCutoff_eqOn_one (I := I) (M := M) β hz_pou
        rw [h_cutβ, one_mul]
        rw [show transitionCoeff (E := E) (I := I) (M := M) r s γ β P₀ Q z * Eγ =
            transitionCoeff (E := E) (I := I) (M := M) r s γ β P₀ Q z *
              (((chartKernelCutoff (I := I) (M := M) γ :
                  C^∞⟮I, M; ℝ⟯) : M → ℝ) z * Eγ) from by rw [← hy_kc]]
        ring
    have h_off_overlap : ∀ y, y ∉ chartOverlapEuclid (I := I) (M := M) β γ →
        W y * A y = W y * RHS y := by
      intro y hy_notin
      by_cases hy_target : y ∈ chartTargetEuclid (I := I) (M := M) β
      · set z : M := (extChartAt I β).symm ((toEuclidean (E := E)).symm y)
          with hz_def
        have hz_notin_srcγ : z ∉ (chartAt H γ).source := by
          intro hz_srcγ
          exact hy_notin
            ((mem_chartOverlapEuclid_iff_of_mem_chartTargetEuclid
              (I := I) (M := M) β γ hy_target).mpr hz_srcγ)
        have hA_y : A y = 0 := by
          rw [hA_def]
          simp only
          rw [chartPushedRaw_apply_of_mem (I := I) (M := M) β _ hy_target,
            ← hz_def, if_neg hz_notin_srcγ]
        have hRHS_y : RHS y = 0 := by
          rw [hRHS_def]
          simp only
          have h_cutγ_zero : ((chartKernelCutoff (I := I) (M := M) γ :
              C^∞⟮I, M; ℝ⟯) : M → ℝ) z = 0 :=
            image_eq_zero_of_notMem_tsupport (fun h =>
              hz_notin_srcγ
                (chartKernelCutoff_tsupport_subset_source (I := I) (M := M) γ h))
          have h_coeff_zero : chartPushedRaw (I := I) (M := M) β
              (transportCoeffManifold (I := I) (M := M) g r s γ β P₀ Q) y = 0 := by
            rw [chartPushedRaw_apply_of_mem (I := I) (M := M) β _ hy_target,
              ← hz_def, transportCoeffManifold_apply, h_cutγ_zero]
            ring
          rw [h_coeff_zero, zero_mul]
        rw [hA_y, hRHS_y]
      · have hWy : W y = 0 := by
          rw [hW_def]
          simp only
          exact chartPushedRaw_apply_of_notMem (I := I) (M := M) β _ hy_target
        rw [hWy, zero_mul, zero_mul]
    exact ae_eq_of_ae_eq_restrict_of_eqOn_compl' hΩ_meas h_on_overlap
      h_off_overlap
  refine h_goal.trans ?_
  exact (Filter.EventuallyEq.refl _ W).mul hB_eq.symm

open Classical in




private lemma wSmoothChart_tensorL2ChartComponent_eq_transport_sum
    (w : TensorL2 r s g)
    (h_all : ∀ k : ℕ, ∀ (α : M) (P₀ : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (2 * k) 2
        (wChartComp (I := I) (M := M) g r s w α P₀)
        (chartTargetEuclid (I := I) (M := M) α))
    (α β : M) (P₀ : TensorCompIdx (E := E) r s) :
    ((tensorL2ChartComponent (I := I) (M := M) g r s
        (wSmoothChart (I := I) (M := M) g r s w h_all α : TensorL2 r s g) β P₀ :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ)
      =ᵐ[chartL2Measure (I := I) (M := M) β]
      (fun y => chartPushedRaw I β
          (fun x => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) y *
        ∑ Q : TensorCompIdx (E := E) r s,
          ((chartTransitionTransportCLM (I := I) (M := M) g r s α β P₀ Q
              (tensorL2ChartComponent (I := I) (M := M) g r s w α Q) :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
            EuclN → ℝ) y) := by
  classical
  refine (wSmoothChart_tensorL2ChartComponent_coeFn_aeEq
    (I := I) (M := M) g r s w h_all α β P₀).trans ?_
  have h_push : ∀ y : EuclN,
      chartPushedRaw I β
          (fun x => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) y *
        chartPushedRaw I β
          (fun x => if x ∈ (chartAt H α).source then
            ∑ Q : TensorCompIdx (E := E) r s,
              transitionCoeff (E := E) (I := I) (M := M) r s α β P₀ Q x *
                tensorChartComponentRaw (I := I) (M := M) g r s
                  (wSmoothChart (I := I) (M := M) g r s w h_all α)
                  α Q.1 Q.2 x
            else 0) y =
        ∑ Q : TensorCompIdx (E := E) r s,
          (chartPushedRaw I β
              (fun x => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) y *
            chartPushedRaw I β
              (fun x => if x ∈ (chartAt H α).source then
                transitionCoeff (E := E) (I := I) (M := M) r s α β P₀ Q x *
                  tensorChartComponentRaw (I := I) (M := M) g r s
                    (wSmoothChart (I := I) (M := M) g r s w h_all α)
                    α Q.1 Q.2 x
              else 0) y) := by
    intro y
    rw [chartPushedRaw_ite_transitionSum_eq_finsetSum_w
      (I := I) (M := M) g r s w h_all α β P₀ y, Finset.mul_sum]
  have h_terms : ∀ Q : TensorCompIdx (E := E) r s,
      (fun y => chartPushedRaw I β
          (fun x => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) y *
        chartPushedRaw I β
          (fun x => if x ∈ (chartAt H α).source then
            transitionCoeff (E := E) (I := I) (M := M) r s α β P₀ Q x *
              tensorChartComponentRaw (I := I) (M := M) g r s
                (wSmoothChart (I := I) (M := M) g r s w h_all α)
                α Q.1 Q.2 x
          else 0) y)
        =ᵐ[chartL2Measure (I := I) (M := M) β]
      (fun y => chartPushedRaw I β
          (fun x => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) y *
        ((chartTransitionTransportCLM (I := I) (M := M) g r s α β P₀ Q
            (tensorL2ChartComponent (I := I) (M := M) g r s w α Q) :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) :=
    fun Q => wSmoothChart_transport_term_aeEq
      (I := I) (M := M) g r s w h_all β α P₀ Q
  have h_sum := finsetSum_ae_eq (I := I) (M := M) β
    (Finset.univ : Finset (TensorCompIdx (E := E) r s))
    (fun Q _ => h_terms Q)
  refine Filter.EventuallyEq.trans (Filter.EventuallyEq.of_eq (funext h_push)) ?_
  refine h_sum.trans (Filter.EventuallyEq.of_eq ?_)
  funext y
  rw [Finset.mul_sum]




omit [NeZero (Module.finrank ℝ E)] in
private lemma wChartComp_ite_chartPushedPouWeight_zero_ae_zero (w : TensorL2 r s g)
    (α : M) (Q : TensorCompIdx (E := E) r s) :
    (fun y => if chartPushedPouWeight (I := I) (M := M) α y = 0 then
        wChartComp (I := I) (M := M) g r s w α Q y
      else 0)
      =ᵐ[chartL2Measure (I := I) (M := M) α]
      (fun _ : EuclN => (0 : ℝ)) := by
  classical
  have h_gate : ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
      chartPushedPouWeight (I := I) (M := M) α y = 0 →
        wChartComp (I := I) (M := M) g r s w α Q y = 0 := by
    filter_upwards [tensorL2ChartComponent_eq_chartPushedPou_mul_cutoff
      (I := I) (M := M) g r s w α Q] with y hy hy_zero
    rw [show wChartComp (I := I) (M := M) g r s w α Q y =
        ((tensorL2ChartComponent (I := I) (M := M) g r s w α Q :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y from rfl,
      hy]
    rw [show chartPushedRaw I α
          (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) y =
        chartPushedPouWeight (I := I) (M := M) α y from rfl, hy_zero, zero_mul]
  filter_upwards [h_gate] with y hy
  by_cases hw : chartPushedPouWeight (I := I) (M := M) α y = 0
  · rw [if_pos hw]; exact hy hw
  · rw [if_neg hw]




private lemma chartTransitionTransportCLM_w_ae_zero_of_notMem (w : TensorL2 r s g)
    (α β : M) (P₀ Q : TensorCompIdx (E := E) r s)
    (hα : α ∉ transportChartCenters (I := I) (M := M) β) :
    ((chartTransitionTransportCLM (I := I) (M := M) g r s α β P₀ Q
        (tensorL2ChartComponent (I := I) (M := M) g r s w α Q) :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ)
      =ᵐ[chartL2Measure (I := I) (M := M) β]
      (fun _ : EuclN => (0 : ℝ)) := by
  classical
  have h_coeFn := chartTransitionTransportCLM_coeFn_aeEq (I := I) (M := M)
    g r s α β P₀ Q (tensorL2ChartComponent (I := I) (M := M) g r s w α Q)
  refine h_coeFn.trans ?_
  have hΩ_open : IsOpen (chartOverlapEuclid (I := I) (M := M) β α) :=
    chartOverlapEuclid_isOpen (I := I) (M := M) β α
  have hΩ_meas : MeasurableSet (chartOverlapEuclid (I := I) (M := M) β α) :=
    hΩ_open.measurableSet
  have h_restrict_eq :
      (chartL2Measure (I := I) (M := M) β).restrict
        (chartOverlapEuclid (I := I) (M := M) β α) =
      (volume : Measure EuclN).restrict
        (chartOverlapEuclid (I := I) (M := M) β α) := by
    rw [chartL2Measure, Measure.restrict_restrict hΩ_meas,
      Set.inter_eq_left.mpr
        (chartOverlapEuclid_subset_chartTarget (I := I) (M := M) β α)]
  have h_on_overlap :
      (fun y => chartPushedRaw (I := I) (M := M) β
          (transportCoeffManifold (I := I) (M := M) g r s α β P₀ Q) y *
        (wChartComp (I := I) (M := M) g r s w α Q)
          (chartTransitionEuclid (I := I) (M := M) β α y))
        =ᵐ[(chartL2Measure (I := I) (M := M) β).restrict
            (chartOverlapEuclid (I := I) (M := M) β α)]
      (fun _ : EuclN => (0 : ℝ)) := by
    rw [h_restrict_eq]
    have h_gate_target :=
      wChartComp_ite_chartPushedPouWeight_zero_ae_zero
        (I := I) (M := M) g r s w α Q
    have h_gate_overlap :
        (fun y => if chartPushedPouWeight (I := I) (M := M) α y = 0 then
            wChartComp (I := I) (M := M) g r s w α Q y
          else 0)
          =ᵐ[(volume : Measure EuclN).restrict
              (chartOverlapEuclid (I := I) (M := M) α β)]
        (fun _ : EuclN => (0 : ℝ)) := by
      rw [chartL2Measure] at h_gate_target
      exact ae_mono (Measure.restrict_mono_set _
        (chartOverlapEuclid_subset_chartTarget (I := I) (M := M) α β))
        h_gate_target
    have h_gate_transport := chartTransitionEuclid_comp_ae_eq_restrict
      (I := I) (M := M) β α h_gate_overlap
    have h_mem : ∀ᵐ y ∂((volume : Measure EuclN).restrict
        (chartOverlapEuclid (I := I) (M := M) β α)),
        y ∈ chartOverlapEuclid (I := I) (M := M) β α :=
      ae_restrict_mem hΩ_meas
    filter_upwards [h_mem, h_gate_transport] with y hy_mem hy_gate
    have hy_target : y ∈ chartTargetEuclid (I := I) (M := M) β :=
      chartOverlapEuclid_subset_chartTarget (I := I) (M := M) β α hy_mem
    set z : M := (extChartAt I β).symm ((toEuclidean (E := E)).symm y)
      with hz_def
    have hz_srcβ : z ∈ (chartAt H β).source :=
      symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) β hy_target
    have hz_srcα : z ∈ (chartAt H α).source :=
      (mem_chartOverlapEuclid_iff_of_mem_chartTargetEuclid
        (I := I) (M := M) β α hy_target).mp hy_mem
    have hsymm_target : (toEuclidean (E := E)).symm y ∈
        (extChartAt I β).target := by
      rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy_target
      exact hy_target
    have hy_eq : (toEuclidean (E := E)) (extChartAt I β z) = y := by
      rw [hz_def, (extChartAt I β).right_inv hsymm_target]
      exact (toEuclidean (E := E)).apply_symm_apply y
    have hT_eq : chartTransitionEuclid (I := I) (M := M) β α y =
        (toEuclidean (E := E)) (extChartAt I α z) := by
      rw [← hy_eq]
      exact chartTransitionEuclid_eq_chartα_image (I := I) (M := M) β α hz_srcβ
    have h_coeff : chartPushedRaw (I := I) (M := M) β
        (transportCoeffManifold (I := I) (M := M) g r s α β P₀ Q) y =
        transportCoeffManifold (I := I) (M := M) g r s α β P₀ Q z := by
      rw [chartPushedRaw_apply_of_mem (I := I) (M := M) β _ hy_target, ← hz_def]
    by_cases hχβ : ((chartKernelCutoff (I := I) (M := M) β :
        C^∞⟮I, M; ℝ⟯) : M → ℝ) z = 0
    · rw [h_coeff, transportCoeffManifold_apply, hχβ]
      ring
    · have hχβ_supp : z ∈ tsupport
          ((chartKernelCutoff (I := I) (M := M) β : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
        subset_tsupport _ hχβ
      have hρα : ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) z = 0 := by
        by_contra hρα_ne
        exact hα (mem_transportChartCenters_of_pou_cutoff_ne
          (I := I) (M := M) β α hρα_ne hχβ)
      have hw_zero : chartPushedPouWeight (I := I) (M := M) α
          (chartTransitionEuclid (I := I) (M := M) β α y) = 0 := by
        rw [hT_eq, chartPushedPouWeight_toEuclidean_extChartAt'
          (I := I) (M := M) α hz_srcα, hρα]
      have hy_gate' : (if chartPushedPouWeight (I := I) (M := M) α
            (chartTransitionEuclid (I := I) (M := M) β α y) = 0 then
          wChartComp (I := I) (M := M) g r s w α Q
            (chartTransitionEuclid (I := I) (M := M) β α y)
        else 0) = 0 := hy_gate
      rw [if_pos hw_zero] at hy_gate'
      rw [hy_gate', mul_zero]
  have h_off_overlap : ∀ y, y ∉ chartOverlapEuclid (I := I) (M := M) β α →
      chartPushedRaw (I := I) (M := M) β
          (transportCoeffManifold (I := I) (M := M) g r s α β P₀ Q) y *
        (wChartComp (I := I) (M := M) g r s w α Q)
          (chartTransitionEuclid (I := I) (M := M) β α y) = 0 := by
    intro y hy_notin
    by_cases hy_target : y ∈ chartTargetEuclid (I := I) (M := M) β
    · set z : M := (extChartAt I β).symm ((toEuclidean (E := E)).symm y)
        with hz_def
      have hz_notin_srcα : z ∉ (chartAt H α).source := by
        intro hz_srcα
        exact hy_notin
          ((mem_chartOverlapEuclid_iff_of_mem_chartTargetEuclid
            (I := I) (M := M) β α hy_target).mpr hz_srcα)
      have hχα_zero : ((chartKernelCutoff (I := I) (M := M) α :
          C^∞⟮I, M; ℝ⟯) : M → ℝ) z = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h =>
          hz_notin_srcα
            (chartKernelCutoff_tsupport_subset_source (I := I) (M := M) α h))
      have h_coeff_zero : chartPushedRaw (I := I) (M := M) β
          (transportCoeffManifold (I := I) (M := M) g r s α β P₀ Q) y = 0 := by
        rw [chartPushedRaw_apply_of_mem (I := I) (M := M) β _ hy_target,
          ← hz_def, transportCoeffManifold_apply, hχα_zero]
        ring
      rw [h_coeff_zero, zero_mul]
    · rw [chartPushedRaw_apply_of_notMem (I := I) (M := M) β _ hy_target,
        zero_mul]
  exact ae_eq_of_ae_eq_restrict_of_eqOn_compl' hΩ_meas h_on_overlap h_off_overlap




private lemma transportSum_w_ae_zero_of_notMem (w : TensorL2 r s g)
    (α β : M) (P₀ : TensorCompIdx (E := E) r s)
    (hα : α ∉ transportChartCenters (I := I) (M := M) β) :
    (fun y => ∑ Q : TensorCompIdx (E := E) r s,
        ((chartTransitionTransportCLM (I := I) (M := M) g r s α β P₀ Q
            (tensorL2ChartComponent (I := I) (M := M) g r s w α Q) :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
      =ᵐ[chartL2Measure (I := I) (M := M) β]
      (fun _ : EuclN => (0 : ℝ)) := by
  classical
  have h_each : ∀ Q : TensorCompIdx (E := E) r s,
      ((chartTransitionTransportCLM (I := I) (M := M) g r s α β P₀ Q
          (tensorL2ChartComponent (I := I) (M := M) g r s w α Q) :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ)
        =ᵐ[chartL2Measure (I := I) (M := M) β] (fun _ : EuclN => (0 : ℝ)) :=
    fun Q => chartTransitionTransportCLM_w_ae_zero_of_notMem
      (I := I) (M := M) g r s w α β P₀ Q hα
  have h_sum := finsetSum_ae_eq (I := I) (M := M) β
    (Finset.univ : Finset (TensorCompIdx (E := E) r s))
    (fun Q _ => h_each Q)
  refine h_sum.trans (Filter.EventuallyEq.of_eq ?_)
  funext y
  rw [Finset.sum_const_zero]

open Classical in




private lemma wSmooth_tensorL2ChartComponent_eq (w : TensorL2 r s g)
    (h_all : ∀ k : ℕ, ∀ (α : M) (P₀ : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (2 * k) 2
        (wChartComp (I := I) (M := M) g r s w α P₀)
        (chartTargetEuclid (I := I) (M := M) α))
    (β : M) (P₀ : TensorCompIdx (E := E) r s) :
    tensorL2ChartComponent g r s
        (wSmooth (I := I) (M := M) g r s w h_all : TensorL2 r s g) β P₀ =
      tensorL2ChartComponent g r s w β P₀ := by
  classical
  apply Lp.ext
  have h_coe_sum :
      (wSmooth (I := I) (M := M) g r s w h_all : TensorL2 r s g) =
        ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
          (wSmoothChart (I := I) (M := M) g r s w h_all α : TensorL2 r s g) := by
    rw [← smoothToTensorL2_apply (I := I) (M := M) g r s,
      wSmooth_eq (I := I) (M := M) g r s w h_all, map_sum]
    refine Finset.sum_congr rfl (fun α _ => ?_)
    rw [smoothToTensorL2_apply]
  have h_lhs_sum :
      tensorL2ChartComponent (I := I) (M := M) g r s
          (wSmooth (I := I) (M := M) g r s w h_all : TensorL2 r s g) β P₀ =
        ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
          tensorL2ChartComponent (I := I) (M := M) g r s
            (wSmoothChart (I := I) (M := M) g r s w h_all α : TensorL2 r s g)
            β P₀ := by
    rw [← tensorL2ChartComponentCLM_apply (I := I) (M := M) g r s β P₀,
      h_coe_sum, map_sum]
    refine Finset.sum_congr rfl (fun α _ => ?_)
    rw [tensorL2ChartComponentCLM_apply]
  rw [h_lhs_sum]
  refine (coeFn_finsetSum_chartL2 (I := I) (M := M) β
    (chartAtlasPOU_finset (I := I) (M := M))
    (fun α => tensorL2ChartComponent (I := I) (M := M) g r s
      (wSmoothChart (I := I) (M := M) g r s w h_all α : TensorL2 r s g)
      β P₀)).trans ?_
  have h_lhs_terms :
      (fun y => ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        ((tensorL2ChartComponent (I := I) (M := M) g r s
            (wSmoothChart (I := I) (M := M) g r s w h_all α : TensorL2 r s g)
            β P₀ :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        =ᵐ[chartL2Measure (I := I) (M := M) β]
      (fun y => ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        (chartPushedRaw I β
            (fun x => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) y *
          ∑ Q : TensorCompIdx (E := E) r s,
            ((chartTransitionTransportCLM (I := I) (M := M) g r s α β P₀ Q
                (tensorL2ChartComponent (I := I) (M := M) g r s w α Q) :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
              EuclN → ℝ) y)) :=
    finsetSum_ae_eq (I := I) (M := M) β
      (chartAtlasPOU_finset (I := I) (M := M))
      (fun α _ => wSmoothChart_tensorL2ChartComponent_eq_transport_sum
        (I := I) (M := M) g r s w h_all α β P₀)
  refine h_lhs_terms.trans ?_
  refine Filter.EventuallyEq.symm
    ((tensorL2ChartComponent_ae_eq_pou_transport_sum (I := I) (M := M)
      g r s w β P₀).trans ?_)
  have h_subset : transportChartCenters (I := I) (M := M) β ⊆
      chartAtlasPOU_finset (I := I) (M := M) :=
    transportChartCenters_subset_chartAtlasPOU_finset' (I := I) (M := M) β
  set F : M → EuclN → ℝ := fun α y =>
    chartPushedRaw I β
        (fun x => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) y *
      ∑ Q : TensorCompIdx (E := E) r s,
        ((chartTransitionTransportCLM (I := I) (M := M) g r s α β P₀ Q
            (tensorL2ChartComponent (I := I) (M := M) g r s w α Q) :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y
    with hF_def
  have h_rhs_eq :
      (fun y => chartPushedRaw I β
          (fun x => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) y *
        ∑ γ ∈ transportChartCenters (I := I) (M := M) β,
          ∑ Q : TensorCompIdx (E := E) r s,
            ((chartTransitionTransportCLM (I := I) (M := M) g r s γ β P₀ Q
                (tensorL2ChartComponent (I := I) (M := M) g r s w γ Q) :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
              EuclN → ℝ) y) =
        fun y => ∑ γ ∈ transportChartCenters (I := I) (M := M) β, F γ y := by
    funext y
    rw [Finset.mul_sum]
  rw [h_rhs_eq]
  have h_union : chartAtlasPOU_finset (I := I) (M := M) =
      transportChartCenters (I := I) (M := M) β ∪
        (chartAtlasPOU_finset (I := I) (M := M) \
          transportChartCenters (I := I) (M := M) β) :=
    (Finset.union_sdiff_of_subset h_subset).symm
  have h_disjoint : Disjoint (transportChartCenters (I := I) (M := M) β)
      (chartAtlasPOU_finset (I := I) (M := M) \
        transportChartCenters (I := I) (M := M) β) :=
    Finset.disjoint_sdiff
  have h_split : (fun y => ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        F α y) =
      fun y => (∑ γ ∈ transportChartCenters (I := I) (M := M) β, F γ y) +
        ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M) \
            transportChartCenters (I := I) (M := M) β, F α y := by
    funext y
    conv_lhs => rw [h_union]
    rw [Finset.sum_union h_disjoint]
  rw [h_split]
  have h_extra : (fun y => ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M) \
          transportChartCenters (I := I) (M := M) β, F α y)
        =ᵐ[chartL2Measure (I := I) (M := M) β] (fun _ : EuclN => (0 : ℝ)) := by
    have h_each : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M) \
        transportChartCenters (I := I) (M := M) β,
        F α =ᵐ[chartL2Measure (I := I) (M := M) β] (fun _ : EuclN => (0 : ℝ)) := by
      intro α hα
      have hα_notin : α ∉ transportChartCenters (I := I) (M := M) β :=
        (Finset.mem_sdiff.mp hα).2
      have h_zero := transportSum_w_ae_zero_of_notMem
        (I := I) (M := M) g r s w α β P₀ hα_notin
      filter_upwards [h_zero] with y hy
      rw [hF_def]
      change chartPushedRaw I β
          (fun x => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) y *
        ∑ Q : TensorCompIdx (E := E) r s,
          ((chartTransitionTransportCLM (I := I) (M := M) g r s α β P₀ Q
              (tensorL2ChartComponent (I := I) (M := M) g r s w α Q) :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y =
        (0 : ℝ)
      rw [hy, mul_zero]
    have h_sum := finsetSum_ae_eq (I := I) (M := M) β
      (chartAtlasPOU_finset (I := I) (M := M) \
        transportChartCenters (I := I) (M := M) β)
      (fun α hα => h_each α hα)
    refine h_sum.trans (Filter.EventuallyEq.of_eq ?_)
    funext y
    rw [Finset.sum_const_zero]
  filter_upwards [h_extra] with y hy
  rw [show (∑ α ∈ chartAtlasPOU_finset (I := I) (M := M) \
        transportChartCenters (I := I) (M := M) β, F α y) = 0 from hy,
    add_zero]















theorem tensorSuperCriticalReconstruct
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    TensorSuperCriticalReconstruct (I := I) (M := M) g r s := by
  intro w h_all
  have h_all' : ∀ k : ℕ, ∀ (α : M) (P₀ : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (2 * k) 2
        (wChartComp (I := I) (M := M) g r s w α P₀)
        (chartTargetEuclid (I := I) (M := M) α) :=
    fun k α P₀ => h_all k α P₀
  refine ⟨wSmooth (I := I) (M := M) g r s w h_all', ?_⟩
  exact tensorL2_eq_of_chartComponent_eq (I := I) (M := M) g r s
    (wSmooth (I := I) (M := M) g r s w h_all' : TensorL2 r s g) w
    (fun β P₀ => wSmooth_tensorL2ChartComponent_eq
      (I := I) (M := M) g r s w h_all' β P₀)

end MetricRealization
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
