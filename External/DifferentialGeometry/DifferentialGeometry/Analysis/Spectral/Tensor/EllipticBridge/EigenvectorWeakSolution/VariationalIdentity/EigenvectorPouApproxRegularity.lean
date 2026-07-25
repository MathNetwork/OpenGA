import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.RHS.ChartRHSBounds.EigenvectorChartRHS
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Cross.EigenvectorChartCrossLimits
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Cross.EigenvectorChartCrossRightLimit
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Cross.EigenvectorChartCrossRightDiv
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.LowerOrder.EigenvectorChartLowerOrderLimits
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.VariationalIdentity.EigenvectorChartTestDecoupling
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Component.EigenvectorChartComponentL2
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.ChartPartial.EigenvectorChartPartialL2
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.EnergyBound.EigenvectorChartWeightedMemLp
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.ChartPartial.EigenvectorWeakPartials
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.VariationalIdentity.TensorChartBilinearData
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.AbstractChartPull
import DifferentialGeometry.Analysis.Elliptic.TensorRegularity.WeakSolution.WeakSolutionDirichlet
import DifferentialGeometry.Analysis.Elliptic.TensorRegularity.Bootstrap.BootstrapSource
import DifferentialGeometry.Analysis.Elliptic.TensorRegularity.DirichletForm.RotatedTestSection
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovariantLeibniz


noncomputable section

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators
  RealInnerProductSpace InnerProductSpace Matrix

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
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Analysis.Laplacian.MetricExtension hiding chartTargetEuclid
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
open DifferentialGeometry.Analysis.Laplacian.ChartLocalLaplacian

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

lemma tendsto_lp_inner_integral
    {β : Type*} [MeasurableSpace β] {μ : Measure β}
    (m : Lp ℝ 2 μ) {g : ℕ → Lp ℝ 2 μ} {g_lim : Lp ℝ 2 μ}
    (h_tendsto : Filter.Tendsto g atTop (𝓝 g_lim)) :
    Filter.Tendsto (fun n => ∫ a, (m : β → ℝ) a * (g n : β → ℝ) a ∂μ)
      atTop (𝓝 (∫ a, (m : β → ℝ) a * (g_lim : β → ℝ) a ∂μ)) := by
  classical
  have h_inner_eq : ∀ (f : Lp ℝ 2 μ),
      ∫ a, (m : β → ℝ) a * (f : β → ℝ) a ∂μ = ⟪m, f⟫_ℝ := by
    intro f
    rw [L2.inner_def (𝕜 := ℝ) m f]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun a => ?_))
    change (m : β → ℝ) a * (f : β → ℝ) a =
      @inner ℝ _ _ ((m : β → ℝ) a) ((f : β → ℝ) a)
    rw [show @inner ℝ _ _ ((m : β → ℝ) a) ((f : β → ℝ) a) =
        (f : β → ℝ) a * (m : β → ℝ) a from RCLike.inner_apply _ _]
    ring
  rw [h_inner_eq g_lim,
    show (fun n => ∫ a, (m : β → ℝ) a * (g n : β → ℝ) a ∂μ) =
      (fun n => ⟪m, g n⟫_ℝ) from funext (fun n => h_inner_eq (g n))]
  exact (continuous_inner.tendsto (m, g_lim)).comp
    (Filter.Tendsto.prodMk_nhds tendsto_const_nhds h_tendsto)

def eigenvectorPouApprox
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (n : ℕ) : SmoothCcTensor g r s :=
  pouSmul (I := I) (M := M) g r s α
    (eigenvectorSmoothApprox (I := I) (M := M)
      g r s i n).toCcTensor

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
lemma euclidPartial_zero_off_tsupport
    {u : EuclN → ℝ} (l : Fin (Module.finrank ℝ E))
    {y : EuclN} (hy : y ∉ tsupport u) :
    euclidPartial (E := E) l u y = 0 := by
  classical
  have hopen_c : IsOpen (tsupport u)ᶜ := (isClosed_tsupport u).isOpen_compl
  have hu_evt : u =ᶠ[𝓝 y] (fun _ => (0 : ℝ)) :=
    Filter.eventually_of_mem (hopen_c.mem_nhds hy)
      (fun z hz => image_eq_zero_of_notMem_tsupport hz)
  rw [euclidPartial_def, Filter.EventuallyEq.fderiv_eq hu_evt,
    fderiv_const_apply, ContinuousLinearMap.zero_apply]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
lemma densityOnEuclid_mul_test_memLp
    (g : SmoothRiemannianMetric I M) (α : M)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    MemLp (fun y => densityOnEuclid (I := I) g α y * ψ y) 2
      (chartL2Measure (I := I) (M := M) α) := by
  classical
  have h_cd : ContDiff ℝ ∞ (fun y => densityOnEuclid (I := I) g α y * ψ y) :=
    contDiff_mul_chartTest (I := I) (M := M) α
      (densityOnEuclid_contDiffOn (I := I) g α) hψ hψ_supp
  have h_cs : HasCompactSupport (fun y => densityOnEuclid (I := I) g α y * ψ y) :=
    hasCompactSupport_mul_chartTest (E := E) hψ_cs
  rw [chartL2Measure]
  exact (h_cd.continuous.memLp_of_hasCompactSupport h_cs).restrict _

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma test_memLp
    (α : M) {ψ : EuclN → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψ_cs : HasCompactSupport ψ) :
    MemLp ψ 2 (chartL2Measure (I := I) (M := M) α) := by
  rw [chartL2Measure]
  exact (hψ.continuous.memLp_of_hasCompactSupport hψ_cs).restrict _

private def principalSymbolTest
    (g : SmoothRiemannianMetric I M) (α : M)
    (ψ : EuclN → ℝ) (i' : Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  fun y => ∑ j : Fin (Module.finrank ℝ E),
    weightedInvGramOnEuclid (I := I) g α i' j y *
      (fderiv ℝ ψ y) (EuclideanSpace.single j 1)

omit [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma principalSymbolTest_memLp
    (g : SmoothRiemannianMetric I M) (α : M)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α)
    (i' : Fin (Module.finrank ℝ E)) :
    MemLp (principalSymbolTest (I := I) (M := M) g α ψ i') 2
      (chartL2Measure (I := I) (M := M) α) := by
  classical
  have hdψ_cd : ∀ j : Fin (Module.finrank ℝ E),
      ContDiff ℝ ∞ (euclidPartial (E := E) j ψ) :=
    fun j => euclidPartial_contDiff (E := E) hψ j
  have hdψ_cs : ∀ j : Fin (Module.finrank ℝ E),
      HasCompactSupport (euclidPartial (E := E) j ψ) := by
    intro j
    refine HasCompactSupport.of_support_subset_isCompact
      (K := tsupport ψ) hψ_cs ?_
    intro y hy
    rw [Function.mem_support] at hy
    by_contra hyψ
    exact hy (euclidPartial_zero_off_tsupport j hyψ)
  have hdψ_supp : ∀ j : Fin (Module.finrank ℝ E),
      tsupport (euclidPartial (E := E) j ψ) ⊆
        chartTargetEuclid (I := I) (M := M) α := by
    intro j
    refine (closure_minimal ?_ (isClosed_tsupport _)).trans hψ_supp
    intro z hz
    rw [Function.mem_support] at hz
    by_contra hz'
    exact hz (euclidPartial_zero_off_tsupport j hz')
  have hgram : ∀ j : Fin (Module.finrank ℝ E), ContDiffOn ℝ ∞
      (fun y => weightedInvGramOnEuclid (I := I) g α i' j y)
      (chartTargetEuclid (I := I) (M := M) α) := by
    intro j
    refine (weightedInvGramEuclid_contDiffOn (I := I) (M := M) g α i' j).congr ?_
    intro y _
    rw [weightedInvGramEuclid_eq_weightedInvGramOnEuclid (I := I) (M := M)
      g α i' j]
  have hpst_eq : principalSymbolTest (I := I) (M := M) g α ψ i' =
      fun y => ∑ j : Fin (Module.finrank ℝ E),
        weightedInvGramOnEuclid (I := I) g α i' j y *
          euclidPartial (E := E) j ψ y := by
    funext y
    simp only [principalSymbolTest]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [euclidPartial_def]
  rw [hpst_eq, chartL2Measure]
  have hsum_memLp : MemLp (fun y => ∑ j : Fin (Module.finrank ℝ E),
        weightedInvGramOnEuclid (I := I) g α i' j y *
          euclidPartial (E := E) j ψ y) 2 (volume : Measure EuclN) := by
    refine memLp_finset_sum (μ := (volume : Measure EuclN))
      (Finset.univ : Finset (Fin (Module.finrank ℝ E))) (fun j _ => ?_)
    have hcd : ContDiff ℝ ∞ (fun y => weightedInvGramOnEuclid (I := I) g α i' j y *
        euclidPartial (E := E) j ψ y) :=
      contDiff_mul_chartTest (I := I) (M := M) α (hgram j) (hdψ_cd j) (hdψ_supp j)
    have hcs : HasCompactSupport (fun y => weightedInvGramOnEuclid (I := I) g α i' j y *
        euclidPartial (E := E) j ψ y) :=
      hasCompactSupport_mul_chartTest (E := E) (hdψ_cs j)
    exact hcd.continuous.memLp_of_hasCompactSupport hcs
  exact hsum_memLp.restrict _

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
lemma density_coeff_test_memLp
    (g : SmoothRiemannianMetric I M) (α : M)
    {c : EuclN → ℝ}
    (hc : ContDiffOn ℝ ∞ c (chartTargetEuclid (I := I) (M := M) α))
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    MemLp (fun y => densityOnEuclid (I := I) g α y * c y * ψ y) 2
      (chartL2Measure (I := I) (M := M) α) := by
  classical
  have hcd : ContDiff ℝ ∞ (fun y => densityOnEuclid (I := I) g α y * c y * ψ y) :=
    contDiff_mul_chartTest (I := I) (M := M) α
      ((densityOnEuclid_contDiffOn (I := I) g α).mul hc) hψ hψ_supp
  have hcs : HasCompactSupport
      (fun y => densityOnEuclid (I := I) g α y * c y * ψ y) := by
    refine HasCompactSupport.of_support_subset_isCompact
      (K := tsupport ψ) hψ_cs ?_
    intro y hy
    rw [Function.mem_support] at hy
    by_contra hyψ
    exact hy (by rw [image_eq_zero_of_notMem_tsupport hyψ, mul_zero])
  rw [chartL2Measure]
  exact (hcd.continuous.memLp_of_hasCompactSupport hcs).restrict _

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma pouSmul_eq_scalarSmul
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) :
    pouSmul (I := I) (M := M) g r s α S =
      scalarSmul (I := I) (M := M) g r s (chartAtlasPOU I M α) S := rfl

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
lemma density_memLp2_test_integrable
    (g : SmoothRiemannianMetric I M) (α : M) {w : EuclN → ℝ}
    (hw : MemLp w 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)))
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    Integrable (fun y => densityOnEuclid (I := I) g α y * w y * ψ y)
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  have hm_memLp : MemLp (fun y => densityOnEuclid (I := I) g α y * ψ y) 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
    have h := densityOnEuclid_mul_test_memLp (I := I) (M := M) g α hψ hψ_cs hψ_supp
    rw [chartL2Measure] at h
    exact h
  have hprod : MemLp (fun y => w y *
      (fun y => densityOnEuclid (I := I) g α y * ψ y) y) 1
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
    hm_memLp.mul' hw
  refine (memLp_one_iff_integrable.mp hprod).congr ?_
  refine Filter.Eventually.of_forall (fun y => ?_)
  simp only []
  ring

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
lemma density_coeff_memLp2_test_integrable
    (g : SmoothRiemannianMetric I M) (α : M)
    {c : EuclN → ℝ}
    (hc : ContDiffOn ℝ ∞ c (chartTargetEuclid (I := I) (M := M) α))
    {w : EuclN → ℝ}
    (hw : MemLp w 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)))
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    Integrable (fun y => densityOnEuclid (I := I) g α y * (c y * w y) * ψ y)
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  have hm_memLp : MemLp (fun y => densityOnEuclid (I := I) g α y * c y * ψ y) 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
    have h := density_coeff_test_memLp (I := I) (M := M) g α hc hψ hψ_cs hψ_supp
    rw [chartL2Measure] at h
    exact h
  have hprod : MemLp (fun y => w y *
      (fun y => densityOnEuclid (I := I) g α y * c y * ψ y) y) 1
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
    hm_memLp.mul' hw
  refine (memLp_one_iff_integrable.mp hprod).congr ?_
  refine Filter.Eventually.of_forall (fun y => ?_)
  simp only []
  ring

omit [CompleteSpace E] in
lemma eigenvectorPouApprox_component_tsupport_subset
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (n : ℕ) :
    tsupport (tensorComponentEuclid (I := I) (M := M) g r s
        (eigenvectorPouApprox (I := I) (M := M) g r s i α n) α P₀) ⊆
      chartPouKernel (I := I) (M := M) α := by
  rw [eigenvectorPouApprox,
    ← tensorChartComponent_eq_tensorComponentEuclid_pouSmul]
  exact tensorChartComponent_tsupport_subset_chartPouKernel (I := I) (M := M)
    g r s _ α P₀.1 P₀.2

omit [CompleteSpace E] in
lemma eigenvectorPouApprox_tsupport_subset_source
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (n : ℕ) :
    tsupport (eigenvectorPouApprox (I := I) (M := M)
        g r s i α n).toFun ⊆ (chartAt H α).source :=
  pouSmul_tsupport_subset_chartSource (I := I) (M := M) g r s α _

omit [CompleteSpace E] in
private lemma eigenvectorPouApprox_component_contDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (n : ℕ) :
    ContDiff ℝ ∞ (tensorComponentEuclid (I := I) (M := M) g r s
      (eigenvectorPouApprox (I := I) (M := M) g r s i α n) α P₀) :=
  tensorComponentEuclid_contDiff (I := I) (M := M) g r s
    (eigenvectorPouApprox (I := I) (M := M) g r s i α n) α P₀
    (eigenvectorPouApprox_tsupport_subset_source (I := I) (M := M)
      g r s i α n)

omit [CompleteSpace E] in
private lemma euclidPartial_eigenvectorPouApprox_component_contDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) (n : ℕ) :
    ContDiff ℝ ∞ (euclidPartial (E := E) k
      (tensorComponentEuclid (I := I) (M := M) g r s
        (eigenvectorPouApprox (I := I) (M := M) g r s i α n) α P₀)) :=
  euclidPartial_contDiff (E := E)
    (eigenvectorPouApprox_component_contDiff (I := I) (M := M)
      g r s i α P₀ n) k

omit [CompleteSpace E] in
private lemma euclidPartial_eigenvectorPouApprox_component_hasCompactSupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) (n : ℕ) :
    HasCompactSupport (euclidPartial (E := E) k
      (tensorComponentEuclid (I := I) (M := M) g r s
        (eigenvectorPouApprox (I := I) (M := M)
          g r s i α n) α P₀)) := by
  classical
  refine HasCompactSupport.of_support_subset_isCompact
    (K := chartPouKernel (I := I) (M := M) α)
    (chartPouKernel_isCompact (I := I) (M := M) α) ?_
  intro y hy
  rw [Function.mem_support] at hy
  by_contra hyK
  refine hy ?_
  have hopen_c : IsOpen (chartPouKernel (I := I) (M := M) α)ᶜ :=
    (chartPouKernel_isCompact (I := I) (M := M) α).isClosed.isOpen_compl
  have hu_evt : (tensorComponentEuclid (I := I) (M := M) g r s
      (eigenvectorPouApprox (I := I) (M := M) g r s i α n) α P₀)
      =ᶠ[𝓝 y] (fun _ => (0 : ℝ)) :=
    Filter.eventually_of_mem (hopen_c.mem_nhds hyK)
      (fun z hz => image_eq_zero_of_notMem_tsupport
        (fun h => hz (eigenvectorPouApprox_component_tsupport_subset
          (I := I) (M := M) g r s i α P₀ n h)))
  rw [euclidPartial_def, Filter.EventuallyEq.fderiv_eq hu_evt,
    fderiv_const_apply, ContinuousLinearMap.zero_apply]

omit [CompleteSpace E] in
private lemma euclidPartial_eigenvectorPouApprox_component_memLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) (n : ℕ) :
    MemLp (euclidPartial (E := E) k
        (tensorComponentEuclid (I := I) (M := M) g r s
          (eigenvectorPouApprox (I := I) (M := M)
            g r s i α n) α P₀)) 2
      (chartL2Measure (I := I) (M := M) α) := by
  rw [chartL2Measure]
  exact ((euclidPartial_eigenvectorPouApprox_component_contDiff
    (I := I) (M := M) g r s i α P₀ k n).continuous.memLp_of_hasCompactSupport
    (euclidPartial_eigenvectorPouApprox_component_hasCompactSupport
      (I := I) (M := M) g r s i α P₀ k n)).restrict _

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in

omit [CompleteSpace E] in
private lemma eigenvectorChartPartialCLM_smoothApprox_coeFn_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) (n : ℕ) :
    ((eigenvectorChartPartialCLM (I := I) (M := M) g r s α P₀ k
        (smoothToTensorH1Compl (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n)) :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) =ᵐ[
        chartL2Measure (I := I) (M := M) α]
      euclidPartial (E := E) k
        (tensorComponentEuclid (I := I) (M := M) g r s
          (eigenvectorPouApprox (I := I) (M := M)
            g r s i α n) α P₀) := by
  classical
  have hμ : i.fst.val ≠ 0 := i.fst.val_ne_zero
  have h1 := eigenvectorChartPartialLp_approx_coeFn (I := I) (M := M)
    g r s i α P₀ k n
  have h2 := chosenWeakPartial'_tensorChartComponent_ae_eq (I := I) (M := M)
    g r s (eigenvectorSmoothApprox (I := I) (M := M)
      g r s i n).toCcTensor
    α P₀.1 P₀.2 k
  have h3 : tensorChartComponent (I := I) (M := M) g r s
        (eigenvectorSmoothApprox (I := I) (M := M)
          g r s i n).toCcTensor
        α P₀.1 P₀.2 =
      tensorComponentEuclid (I := I) (M := M) g r s
        (eigenvectorPouApprox (I := I) (M := M)
          g r s i α n) α P₀ := by
    rw [eigenvectorPouApprox]
    exact tensorChartComponent_eq_tensorComponentEuclid_pouSmul (I := I) (M := M)
      g r s α _ P₀
  have hsmul := Lp.coeFn_smul (i.fst.val)⁻¹
    (eigenvectorChartPartialCLM (I := I) (M := M) g r s α P₀ k
      (smoothToTensorH1Compl (I := I) (M := M) g r s
        (eigenvectorSmoothApprox (I := I) (M := M) g r s i n)))
  have h4 : ((eigenvectorChartPartialCLM (I := I) (M := M) g r s α P₀ k
        (smoothToTensorH1Compl (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n)) :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) =ᵐ[
        chartL2Measure (I := I) (M := M) α]
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
        (tensorChartComponent (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor
          α P₀.1 P₀.2)
        (chartTargetEuclid (I := I) (M := M) α) := by
    have hcomb := hsmul.symm.trans h1
    filter_upwards [hcomb] with y hy
    have hyeq : (i.fst.val)⁻¹ • ((eigenvectorChartPartialCLM (I := I) (M := M)
        g r s α P₀ k
        (smoothToTensorH1Compl (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n)) :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y =
      (i.fst.val)⁻¹ • chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
        (tensorChartComponent (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor
          α P₀.1 P₀.2)
        (chartTargetEuclid (I := I) (M := M) α) y := hy
    exact smul_right_injective ℝ (inv_ne_zero hμ) hyeq
  refine (h4.trans h2).trans ?_
  rw [h3]

omit [CompleteSpace E] in
private lemma euclidPartial_eigenvectorPouApprox_toLp_eq_clm
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) (n : ℕ) :
    (euclidPartial_eigenvectorPouApprox_component_memLp (I := I) (M := M)
        g r s i α P₀ k n).toLp _ =
      eigenvectorChartPartialCLM (I := I) (M := M) g r s α P₀ k
        (smoothToTensorH1Compl (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n)) := by
  refine Lp.ext ?_
  refine (MemLp.coeFn_toLp _).trans ?_
  exact (eigenvectorChartPartialCLM_smoothApprox_coeFn_eq (I := I) (M := M)
    g r s i α P₀ k n).symm

omit [CompleteSpace E] in
private lemma euclidPartial_eigenvectorPouApprox_toLp_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    Filter.Tendsto
      (fun n => (euclidPartial_eigenvectorPouApprox_component_memLp
        (I := I) (M := M) g r s i α P₀ k n).toLp _)
      atTop
      (𝓝 (i.fst.val •
        eigenvectorChartPartialLp (I := I) (M := M)
          g r s i α P₀ k)) := by
  classical
  have hμ : i.fst.val ≠ 0 := i.fst.val_ne_zero
  have h_base := eigenvectorChartPartialLp_tendsto (I := I) (M := M)
    g r s i α P₀ k
  have h_scaled := h_base.const_smul i.fst.val
  have h_eq : ∀ n : ℕ, i.fst.val • ((i.fst.val)⁻¹ •
        eigenvectorChartPartialCLM (I := I) (M := M) g r s α P₀ k
          (smoothToTensorH1Compl (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M)
              g r s i n))) =
      (euclidPartial_eigenvectorPouApprox_component_memLp
        (I := I) (M := M) g r s i α P₀ k n).toLp _ := by
    intro n
    rw [smul_smul, mul_inv_cancel₀ hμ, one_smul,
      euclidPartial_eigenvectorPouApprox_toLp_eq_clm (I := I) (M := M)
        g r s i α P₀ k n]
  exact h_scaled.congr h_eq

omit [CompleteSpace E] in
private lemma principalIntegrand_eigenvectorPouApprox_eqOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    {ψ : EuclN → ℝ} (n : ℕ) :
    Set.EqOn
      ((tensorPrincipalForm (I := I) (M := M) g α
          (chartPouKernel_isCompact (I := I) (M := M) α)
          (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)).principalIntegrand
        (tensorComponentEuclid (I := I) (M := M) g r s
          (eigenvectorPouApprox (I := I) (M := M)
            g r s i α n) α P₀) ψ)
      (fun y => ∑ k : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          weightedInvGramOnEuclid (I := I) g α k l y *
            euclidPartial (E := E) k
              (tensorComponentEuclid (I := I) (M := M) g r s
                (eigenvectorPouApprox (I := I) (M := M)
                  g r s i α n) α P₀)
              y *
            euclidPartial (E := E) l ψ y)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  intro y hy
  by_cases hyK : y ∈ chartPouKernel (I := I) (M := M) α
  · have hPI := weightedInvGram_principalIntegrand_eq (I := I) (M := M) g α
      (chartPouKernel_isCompact (I := I) (M := M) α)
      (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
      (tensorComponentEuclid (I := I) (M := M) g r s
        (eigenvectorPouApprox (I := I) (M := M)
          g r s i α n) α P₀) ψ hyK
    rw [← hPI, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [show weightedInvGramOnEuclid (I := I) g α k l y =
        densityOnEuclid (I := I) g α y *
          chartInvGramEuclid (I := I) g α k l y from by
      rw [← weightedInvGramEuclid_eq_weightedInvGramOnEuclid (I := I) (M := M)
        g α k l]; rfl]
    ring
  · have hu_partial_zero : ∀ k : Fin (Module.finrank ℝ E),
        euclidPartial (E := E) k
          (tensorComponentEuclid (I := I) (M := M) g r s
            (eigenvectorPouApprox (I := I) (M := M)
              g r s i α n) α P₀)
          y = 0 := by
      intro k
      have hopen_c : IsOpen (chartPouKernel (I := I) (M := M) α)ᶜ :=
        (chartPouKernel_isCompact (I := I) (M := M) α).isClosed.isOpen_compl
      have hu_evt : (tensorComponentEuclid (I := I) (M := M) g r s
          (eigenvectorPouApprox (I := I) (M := M)
            g r s i α n) α P₀)
          =ᶠ[𝓝 y] (fun _ => (0 : ℝ)) :=
        Filter.eventually_of_mem (hopen_c.mem_nhds hyK)
          (fun z hz => image_eq_zero_of_notMem_tsupport
            (fun h => hz (eigenvectorPouApprox_component_tsupport_subset
              (I := I) (M := M) g r s i α P₀ n h)))
      rw [euclidPartial_def, Filter.EventuallyEq.fderiv_eq hu_evt,
        fderiv_const_apply, ContinuousLinearMap.zero_apply]
    have hLHS_zero :
        (tensorPrincipalForm (I := I) (M := M) g α
            (chartPouKernel_isCompact (I := I) (M := M) α)
            (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)).principalIntegrand
          (tensorComponentEuclid (I := I) (M := M) g r s
            (eigenvectorPouApprox (I := I) (M := M)
              g r s i α n) α P₀)
          ψ y = 0 := by
      rw [SmoothEllipticBilinearForm.principalIntegrand]
      refine Finset.sum_eq_zero (fun k _ => Finset.sum_eq_zero (fun l _ => ?_))
      have hk := hu_partial_zero k
      rw [euclidPartial_def] at hk
      rw [hk]; ring
    have hRHS_zero :
        (fun y => ∑ k : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            weightedInvGramOnEuclid (I := I) g α k l y *
              euclidPartial (E := E) k
                (tensorComponentEuclid (I := I) (M := M) g r s
                  (eigenvectorPouApprox (I := I) (M := M)
                    g r s i α n) α P₀)
                y *
              euclidPartial (E := E) l ψ y) y = 0 := by
      refine Finset.sum_eq_zero (fun k _ => Finset.sum_eq_zero (fun l _ => ?_))
      rw [hu_partial_zero k]; ring
    rw [hLHS_zero, hRHS_zero]


omit [CompleteSpace E] in
private lemma bilin_eigenvectorPouApprox_eq_sum
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ ∞ ψ) (_hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) (n : ℕ) :
    (tensorPrincipalForm (I := I) (M := M) g α
        (chartPouKernel_isCompact (I := I) (M := M) α)
        (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)).bilin
      (tensorComponentEuclid (I := I) (M := M) g r s
        (eigenvectorPouApprox (I := I) (M := M)
          g r s i α n) α P₀) ψ =
      ∑ i' : Fin (Module.finrank ℝ E),
        ∫ y, (principalSymbolTest (I := I) (M := M) g α ψ i' y) *
          euclidPartial (E := E) i'
            (tensorComponentEuclid (I := I) (M := M) g r s
              (eigenvectorPouApprox (I := I) (M := M)
                g r s i α n) α P₀)
            y ∂(chartL2Measure (I := I) (M := M) α) := by
  classical
  set uₙ : EuclN → ℝ := tensorComponentEuclid (I := I) (M := M) g r s
    (eigenvectorPouApprox (I := I) (M := M) g r s i α n) α P₀
    with huₙ_def
  set Bform := tensorPrincipalForm (I := I) (M := M) g α
    (chartPouKernel_isCompact (I := I) (M := M) α)
    (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α) with hBform_def
  have hcTE_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α
  have hcTE_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    hcTE_open.measurableSet
  have huₙ_cd : ContDiff ℝ ∞ uₙ :=
    eigenvectorPouApprox_component_contDiff (I := I) (M := M)
      g r s i α P₀ n
  have hP_principal : ContDiff ℝ ∞ (Bform.principalIntegrand uₙ ψ) := by
    have huₙ_dpartial : ∀ a : Fin (Module.finrank ℝ E),
        ContDiff ℝ ∞ (fun x => (fderiv ℝ uₙ x) (EuclideanSpace.single a 1)) :=
      fun a => euclidPartial_contDiff (E := E) huₙ_cd a
    have hψ_dpartial : ∀ b : Fin (Module.finrank ℝ E),
        ContDiff ℝ ∞ (fun x => (fderiv ℝ ψ x) (EuclideanSpace.single b 1)) :=
      fun b => euclidPartial_contDiff (E := E) hψ b
    have hbody : ContDiff ℝ ∞
        (fun x => ∑ a : Fin (Module.finrank ℝ E),
          ∑ b : Fin (Module.finrank ℝ E),
            Bform.a x a b *
              ((fderiv ℝ uₙ x) (EuclideanSpace.single a 1)) *
              ((fderiv ℝ ψ x) (EuclideanSpace.single b 1))) :=
      ContDiff.sum (fun a _ => ContDiff.sum (fun b _ =>
        ((Bform.smooth_a a b).mul (huₙ_dpartial a)).mul (hψ_dpartial b)))
    exact hbody
  have huₙ_partial_zero : ∀ k : Fin (Module.finrank ℝ E), ∀ y,
      y ∉ tsupport uₙ → euclidPartial (E := E) k uₙ y = 0 :=
    fun k y hy => euclidPartial_zero_off_tsupport (E := E) k hy
  have huₙ_tsupport_compact : IsCompact (tsupport uₙ) :=
    IsCompact.of_isClosed_subset (chartPouKernel_isCompact (I := I) (M := M) α)
      (isClosed_tsupport _)
      (eigenvectorPouApprox_component_tsupport_subset (I := I) (M := M)
        g r s i α P₀ n)
  have hcs_principal : HasCompactSupport (Bform.principalIntegrand uₙ ψ) := by
    refine HasCompactSupport.of_support_subset_isCompact
      huₙ_tsupport_compact ?_
    intro y hy
    rw [Function.mem_support] at hy
    by_contra hyu
    refine hy ?_
    rw [SmoothEllipticBilinearForm.principalIntegrand]
    refine Finset.sum_eq_zero (fun a _ => Finset.sum_eq_zero (fun b _ => ?_))
    have hk := huₙ_partial_zero a y hyu
    rw [euclidPartial_def] at hk
    rw [hk]; ring
  have hbilin_eq : Bform.bilin uₙ ψ =
      ∫ y, Bform.principalIntegrand uₙ ψ y ∂(volume : Measure EuclN) := by
    rw [SmoothEllipticBilinearForm.bilin, MeasureTheory.setIntegral_univ]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro y
    change Bform.principalIntegrand uₙ ψ y + Bform.c y * uₙ y * ψ y =
      Bform.principalIntegrand uₙ ψ y
    rw [hBform_def, tensorPrincipalForm_c_apply (I := I) (M := M) g α
      (chartPouKernel_isCompact (I := I) (M := M) α)
      (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α) y]
    ring
  have hPI_zero : ∀ y, y ∉ chartTargetEuclid (I := I) (M := M) α →
      Bform.principalIntegrand uₙ ψ y = 0 := by
    intro y hy
    have hyψ : y ∉ tsupport ψ := fun h => hy (hψ_supp h)
    rw [SmoothEllipticBilinearForm.principalIntegrand]
    refine Finset.sum_eq_zero (fun a _ => Finset.sum_eq_zero (fun b _ => ?_))
    rw [show (fderiv ℝ ψ y) (EuclideanSpace.single b 1) =
        euclidPartial (E := E) b ψ y from (euclidPartial_def _ _ _).symm,
      euclidPartial_zero_off_tsupport (E := E) b hyψ]
    ring
  have hPI_volume_to_target :
      ∫ y, Bform.principalIntegrand uₙ ψ y ∂(volume : Measure EuclN) =
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          Bform.principalIntegrand uₙ ψ y ∂(volume : Measure EuclN) :=
    (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hPI_zero).symm
  have hPI_target_eq :
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
          Bform.principalIntegrand uₙ ψ y ∂(volume : Measure EuclN) =
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α k l y *
                euclidPartial (E := E) k uₙ y *
                euclidPartial (E := E) l ψ y) ∂(volume : Measure EuclN) := by
    refine MeasureTheory.setIntegral_congr_fun hcTE_meas ?_
    have := principalIntegrand_eigenvectorPouApprox_eqOn (I := I) (M := M)
      g r s i α P₀ (ψ := ψ) n
    rw [hBform_def, huₙ_def]
    exact this
  have hreorg :
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α k l y *
                euclidPartial (E := E) k uₙ y *
                euclidPartial (E := E) l ψ y) ∂(volume : Measure EuclN) =
        ∑ i' : Fin (Module.finrank ℝ E),
          ∫ y, (principalSymbolTest (I := I) (M := M) g α ψ i' y) *
            euclidPartial (E := E) i' uₙ y
            ∂(chartL2Measure (I := I) (M := M) α) := by
    have hcoeff : ∀ i' : Fin (Module.finrank ℝ E),
        ∫ y, (principalSymbolTest (I := I) (M := M) g α ψ i' y) *
            euclidPartial (E := E) i' uₙ y
            ∂(chartL2Measure (I := I) (M := M) α) =
          ∫ y in chartTargetEuclid (I := I) (M := M) α,
            (∑ l : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i' l y *
                euclidPartial (E := E) i' uₙ y *
                euclidPartial (E := E) l ψ y) ∂(volume : Measure EuclN) := by
      intro i'
      rw [chartL2Measure]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
      intro y
      simp only [principalSymbolTest]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [show (fderiv ℝ ψ y) (EuclideanSpace.single l 1) =
          euclidPartial (E := E) l ψ y from (euclidPartial_def _ _ _).symm]
      ring
    rw [show (fun i' : Fin (Module.finrank ℝ E) =>
          ∫ y, (principalSymbolTest (I := I) (M := M) g α ψ i' y) *
            euclidPartial (E := E) i' uₙ y
            ∂(chartL2Measure (I := I) (M := M) α)) =
        (fun i' : Fin (Module.finrank ℝ E) =>
          ∫ y in chartTargetEuclid (I := I) (M := M) α,
            (∑ l : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i' l y *
                euclidPartial (E := E) i' uₙ y *
                euclidPartial (E := E) l ψ y) ∂(volume : Measure EuclN))
        from funext hcoeff]
    have huₙ_partial_cd : ∀ k : Fin (Module.finrank ℝ E),
        ContDiff ℝ ∞ (euclidPartial (E := E) k uₙ) :=
      fun k => euclidPartial_eigenvectorPouApprox_component_contDiff
        (I := I) (M := M) g r s i α P₀ k n
    have huₙ_partial_cs : ∀ k : Fin (Module.finrank ℝ E),
        HasCompactSupport (euclidPartial (E := E) k uₙ) :=
      fun k => euclidPartial_eigenvectorPouApprox_component_hasCompactSupport
        (I := I) (M := M) g r s i α P₀ k n
    have huₙ_partial_supp : ∀ k : Fin (Module.finrank ℝ E),
        tsupport (euclidPartial (E := E) k uₙ) ⊆
          chartTargetEuclid (I := I) (M := M) α := by
      intro k
      refine (closure_minimal ?_
        (chartPouKernel_isCompact (I := I) (M := M) α).isClosed).trans
        (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
      intro y hy
      rw [Function.mem_support] at hy
      by_contra hyK
      refine hy ?_
      have hopen_c : IsOpen (chartPouKernel (I := I) (M := M) α)ᶜ :=
        (chartPouKernel_isCompact (I := I) (M := M) α).isClosed.isOpen_compl
      have hu_evt : uₙ =ᶠ[𝓝 y] (fun _ => (0 : ℝ)) :=
        Filter.eventually_of_mem (hopen_c.mem_nhds hyK)
          (fun z hz => image_eq_zero_of_notMem_tsupport
            (fun h => hz ((eigenvectorPouApprox_component_tsupport_subset
              (I := I) (M := M) g r s i α P₀ n) h)))
      rw [euclidPartial_def, Filter.EventuallyEq.fderiv_eq hu_evt,
        fderiv_const_apply, ContinuousLinearMap.zero_apply]
    have hgram_cd : ∀ k l : Fin (Module.finrank ℝ E),
        ContDiffOn ℝ ∞ (fun y => weightedInvGramOnEuclid (I := I) g α k l y)
          (chartTargetEuclid (I := I) (M := M) α) := by
      intro k l
      refine (weightedInvGramEuclid_contDiffOn (I := I) (M := M) g α k l).congr ?_
      intro y _
      rw [weightedInvGramEuclid_eq_weightedInvGramOnEuclid (I := I) (M := M) g α k l]
    have hdψ_cd : ∀ l : Fin (Module.finrank ℝ E),
        ContDiff ℝ ∞ (euclidPartial (E := E) l ψ) :=
      fun l => euclidPartial_contDiff (E := E) hψ l
    have hsummand_cd : ∀ k l : Fin (Module.finrank ℝ E),
        ContDiff ℝ ∞ (fun y => weightedInvGramOnEuclid (I := I) g α k l y *
          euclidPartial (E := E) k uₙ y *
          euclidPartial (E := E) l ψ y) := by
      intro k l
      have h1 : ContDiff ℝ ∞ (fun y =>
          weightedInvGramOnEuclid (I := I) g α k l y *
            euclidPartial (E := E) k uₙ y) :=
        contDiff_mul_chartTest (I := I) (M := M) α (hgram_cd k l)
          (huₙ_partial_cd k) (huₙ_partial_supp k)
      exact h1.mul (hdψ_cd l)
    have hsummand_cs : ∀ k l : Fin (Module.finrank ℝ E),
        HasCompactSupport (fun y => weightedInvGramOnEuclid (I := I) g α k l y *
          euclidPartial (E := E) k uₙ y *
          euclidPartial (E := E) l ψ y) := by
      intro k l
      refine HasCompactSupport.of_support_subset_isCompact
        (huₙ_partial_cs k) ?_
      intro y hy
      rw [Function.mem_support] at hy
      by_contra hyu
      refine hy ?_
      rw [show euclidPartial (E := E) k uₙ y = 0 from
        image_eq_zero_of_notMem_tsupport hyu]
      ring
    have hsummand_int : ∀ k l : Fin (Module.finrank ℝ E),
        Integrable (fun y => weightedInvGramOnEuclid (I := I) g α k l y *
          euclidPartial (E := E) k uₙ y *
          euclidPartial (E := E) l ψ y) (volume : Measure EuclN) :=
      fun k l => (hsummand_cd k l).continuous.integrable_of_hasCompactSupport
        (hsummand_cs k l)
    have hsplit : ∀ i' : Fin (Module.finrank ℝ E),
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
            (∑ l : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i' l y *
                euclidPartial (E := E) i' uₙ y *
                euclidPartial (E := E) l ψ y) ∂(volume : Measure EuclN) =
          ∫ y, (∑ l : Fin (Module.finrank ℝ E),
            weightedInvGramOnEuclid (I := I) g α i' l y *
              euclidPartial (E := E) i' uₙ y *
              euclidPartial (E := E) l ψ y) ∂(volume : Measure EuclN) := by
      intro i'
      refine MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero ?_
      intro y hy
      refine Finset.sum_eq_zero (fun l _ => ?_)
      rw [show euclidPartial (E := E) i' uₙ y = 0 from
        image_eq_zero_of_notMem_tsupport
          (fun h => hy (huₙ_partial_supp i' h))]
      ring
    rw [show (fun i' : Fin (Module.finrank ℝ E) =>
          ∫ y in chartTargetEuclid (I := I) (M := M) α,
            (∑ l : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i' l y *
                euclidPartial (E := E) i' uₙ y *
                euclidPartial (E := E) l ψ y) ∂(volume : Measure EuclN)) =
        (fun i' : Fin (Module.finrank ℝ E) =>
          ∫ y, (∑ l : Fin (Module.finrank ℝ E),
            weightedInvGramOnEuclid (I := I) g α i' l y *
              euclidPartial (E := E) i' uₙ y *
              euclidPartial (E := E) l ψ y) ∂(volume : Measure EuclN))
        from funext hsplit]
    rw [← MeasureTheory.integral_finset_sum _
      (fun i' _ => MeasureTheory.integrable_finset_sum _
        (fun l _ => hsummand_int i' l))]
    have hdouble_split :
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
            (∑ k : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                weightedInvGramOnEuclid (I := I) g α k l y *
                  euclidPartial (E := E) k uₙ y *
                  euclidPartial (E := E) l ψ y) ∂(volume : Measure EuclN) =
          ∫ y, (∑ i' : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i' l y *
                euclidPartial (E := E) i' uₙ y *
                euclidPartial (E := E) l ψ y) ∂(volume : Measure EuclN) := by
      refine MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero ?_
      intro y hy
      refine Finset.sum_eq_zero (fun k _ => Finset.sum_eq_zero (fun l _ => ?_))
      rw [show euclidPartial (E := E) k uₙ y = 0 from
        image_eq_zero_of_notMem_tsupport
          (fun h => hy (huₙ_partial_supp k h))]
      ring
    rw [hdouble_split]
  rw [hbilin_eq, hPI_volume_to_target, hPI_target_eq, hreorg]


omit [CompleteSpace E] in
lemma bilin_eigenvectorPouApprox_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    Filter.Tendsto
      (fun n => (tensorPrincipalForm (I := I) (M := M) g α
          (chartPouKernel_isCompact (I := I) (M := M) α)
          (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)).bilin
        (tensorComponentEuclid (I := I) (M := M) g r s
          (eigenvectorPouApprox (I := I) (M := M)
            g r s i α n) α P₀) ψ)
      atTop
      (𝓝 (i.fst.val *
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i' : Fin (Module.finrank ℝ E),
            ∑ j' : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i' j' y *
                eigenvectorChartWeakPartial (I := I) (M := M)
                  g r s i α P₀ i' y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j' 1))
          ∂(volume : Measure EuclN))) := by
  classical
  set mtest : Fin (Module.finrank ℝ E) → Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) :=
    fun i' => (principalSymbolTest_memLp (I := I) (M := M) g α hψ hψ_cs hψ_supp i').toLp _
    with hmtest_def
  have h_dir : ∀ i' : Fin (Module.finrank ℝ E),
      Filter.Tendsto
        (fun n => ∫ y, (mtest i' : EuclN → ℝ) y *
          ((euclidPartial_eigenvectorPouApprox_component_memLp
            (I := I) (M := M) g r s i α P₀ i' n).toLp _ : EuclN → ℝ) y
          ∂(chartL2Measure (I := I) (M := M) α))
        atTop
        (𝓝 (∫ y, (mtest i' : EuclN → ℝ) y *
          ((i.fst.val •
            eigenvectorChartPartialLp (I := I) (M := M)
              g r s i α P₀ i' :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
          ∂(chartL2Measure (I := I) (M := M) α))) := by
    intro i'
    exact tendsto_lp_inner_integral (μ := chartL2Measure (I := I) (M := M) α)
      (mtest i')
      (euclidPartial_eigenvectorPouApprox_toLp_tendsto (I := I) (M := M)
        g r s i α P₀ i')
  have h_int_n : ∀ (i' : Fin (Module.finrank ℝ E)) (n : ℕ),
      ∫ y, (mtest i' : EuclN → ℝ) y *
        ((euclidPartial_eigenvectorPouApprox_component_memLp
          (I := I) (M := M) g r s i α P₀ i' n).toLp _ : EuclN → ℝ) y
        ∂(chartL2Measure (I := I) (M := M) α) =
      ∫ y, (principalSymbolTest (I := I) (M := M) g α ψ i' y) *
        euclidPartial (E := E) i'
          (tensorComponentEuclid (I := I) (M := M) g r s
            (eigenvectorPouApprox (I := I) (M := M)
              g r s i α n) α P₀)
          y ∂(chartL2Measure (I := I) (M := M) α) := by
    intro i' n
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [(by rw [hmtest_def]; exact MemLp.coeFn_toLp _ :
        (mtest i' : EuclN → ℝ) =ᵐ[chartL2Measure (I := I) (M := M) α]
          principalSymbolTest (I := I) (M := M) g α ψ i'),
      MemLp.coeFn_toLp (euclidPartial_eigenvectorPouApprox_component_memLp
        (I := I) (M := M) g r s i α P₀ i' n)] with y hy_m hy_g
    rw [hy_m, hy_g]
  have h_bilin_n : ∀ n : ℕ,
      (tensorPrincipalForm (I := I) (M := M) g α
          (chartPouKernel_isCompact (I := I) (M := M) α)
          (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)).bilin
        (tensorComponentEuclid (I := I) (M := M) g r s
          (eigenvectorPouApprox (I := I) (M := M)
            g r s i α n) α P₀) ψ =
      ∑ i' : Fin (Module.finrank ℝ E),
        ∫ y, (mtest i' : EuclN → ℝ) y *
          ((euclidPartial_eigenvectorPouApprox_component_memLp
            (I := I) (M := M) g r s i α P₀ i' n).toLp _ : EuclN → ℝ) y
          ∂(chartL2Measure (I := I) (M := M) α) := by
    intro n
    rw [bilin_eigenvectorPouApprox_eq_sum (I := I) (M := M)
      g r s i α P₀ hψ hψ_cs hψ_supp n]
    exact Finset.sum_congr rfl (fun i' _ => (h_int_n i' n).symm)
  have h_sum_tendsto :
      Filter.Tendsto
        (fun n => ∑ i' : Fin (Module.finrank ℝ E),
          ∫ y, (mtest i' : EuclN → ℝ) y *
            ((euclidPartial_eigenvectorPouApprox_component_memLp
              (I := I) (M := M) g r s i α P₀ i' n).toLp _ : EuclN → ℝ) y
            ∂(chartL2Measure (I := I) (M := M) α))
        atTop
        (𝓝 (∑ i' : Fin (Module.finrank ℝ E),
          ∫ y, (mtest i' : EuclN → ℝ) y *
            ((i.fst.val •
              eigenvectorChartPartialLp (I := I) (M := M)
                g r s i α P₀ i' :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
            ∂(chartL2Measure (I := I) (M := M) α))) :=
    tendsto_finset_sum (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
      (fun i' _ => h_dir i')
  have h_limit_eq :
      ∑ i' : Fin (Module.finrank ℝ E),
        ∫ y, (mtest i' : EuclN → ℝ) y *
          ((i.fst.val •
            eigenvectorChartPartialLp (I := I) (M := M)
              g r s i α P₀ i' :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
          ∂(chartL2Measure (I := I) (M := M) α) =
      i.fst.val *
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i' : Fin (Module.finrank ℝ E),
            ∑ j' : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i' j' y *
                eigenvectorChartWeakPartial (I := I) (M := M)
                  g r s i α P₀ i' y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j' 1))
          ∂(volume : Measure EuclN) := by
    have h_summand : ∀ i' : Fin (Module.finrank ℝ E),
        ∫ y, (mtest i' : EuclN → ℝ) y *
          ((i.fst.val •
            eigenvectorChartPartialLp (I := I) (M := M)
              g r s i α P₀ i' :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
          ∂(chartL2Measure (I := I) (M := M) α) =
        i.fst.val *
          ∫ y in chartTargetEuclid (I := I) (M := M) α,
            (∑ j' : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i' j' y *
                eigenvectorChartWeakPartial (I := I) (M := M)
                  g r s i α P₀ i' y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j' 1))
            ∂(volume : Measure EuclN) := by
      intro i'
      have h_m_ae : (mtest i' : EuclN → ℝ)
          =ᵐ[chartL2Measure (I := I) (M := M) α]
          principalSymbolTest (I := I) (M := M) g α ψ i' := by
        rw [hmtest_def]; exact MemLp.coeFn_toLp _
      have h_g_ae : ((i.fst.val •
            eigenvectorChartPartialLp (I := I) (M := M)
              g r s i α P₀ i' :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ)
          =ᵐ[chartL2Measure (I := I) (M := M) α]
          fun y => i.fst.val •
            eigenvectorChartWeakPartial (I := I) (M := M)
              g r s i α P₀ i' y :=
        Lp.coeFn_smul i.fst.val
          (eigenvectorChartPartialLp (I := I) (M := M)
            g r s i α P₀ i')
      have h_ae_prod :
          (fun y => (mtest i' : EuclN → ℝ) y *
            ((i.fst.val •
              eigenvectorChartPartialLp (I := I) (M := M)
                g r s i α P₀ i' :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
          =ᵐ[chartL2Measure (I := I) (M := M) α]
          fun y => i.fst.val *
            (principalSymbolTest (I := I) (M := M) g α ψ i' y *
              eigenvectorChartWeakPartial (I := I) (M := M)
                g r s i α P₀ i' y) := by
        filter_upwards [h_m_ae, h_g_ae] with y hy_m hy_g
        rw [hy_m, hy_g, smul_eq_mul]; ring
      rw [integral_congr_ae h_ae_prod, MeasureTheory.integral_const_mul]
      congr 1
      change ∫ y, (principalSymbolTest (I := I) (M := M) g α ψ i' y *
          eigenvectorChartWeakPartial (I := I) (M := M)
            g r s i α P₀ i' y)
          ∂((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)) = _
      refine MeasureTheory.setIntegral_congr_fun
        (chartTargetEuclid_measurableSet (I := I) (M := M) α) (fun y _ => ?_)
      simp only [principalSymbolTest]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun j' _ => ?_)
      ring
    rw [Finset.sum_congr rfl (fun i' _ => h_summand i'), ← Finset.mul_sum]
    congr 1
    have h_inner_integrable : ∀ i' : Fin (Module.finrank ℝ E),
        Integrable (fun y => ∑ j' : Fin (Module.finrank ℝ E),
          weightedInvGramOnEuclid (I := I) g α i' j' y *
            eigenvectorChartWeakPartial (I := I) (M := M)
              g r s i α P₀ i' y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j' 1))
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)) := by
      intro i'
      have hwp_memLp : MemLp (eigenvectorChartWeakPartial (I := I) (M := M)
          g r s i α P₀ i') 2
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)) := by
        have h : MemLp (fun y => ((eigenvectorChartPartialLp
            (I := I) (M := M) g r s i α P₀ i' :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) 2
            (chartL2Measure (I := I) (M := M) α) :=
          Lp.memLp _
        exact h
      have hpst_memLp : MemLp (principalSymbolTest (I := I) (M := M) g α ψ i') 2
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)) := by
        exact principalSymbolTest_memLp (I := I) (M := M) g α hψ hψ_cs
          hψ_supp i'
      have hprod : MemLp (fun y => principalSymbolTest (I := I) (M := M) g α ψ i' y *
          eigenvectorChartWeakPartial (I := I) (M := M)
            g r s i α P₀ i' y) 1
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)) :=
        hwp_memLp.mul hpst_memLp
      have hprod_int : Integrable (fun y =>
          principalSymbolTest (I := I) (M := M) g α ψ i' y *
            eigenvectorChartWeakPartial (I := I) (M := M)
              g r s i α P₀ i' y)
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)) :=
        (memLp_one_iff_integrable).mp hprod
      refine hprod_int.congr ?_
      refine Filter.Eventually.of_forall (fun y => ?_)
      simp only [principalSymbolTest]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun j' _ => ?_)
      ring
    rw [← MeasureTheory.integral_finset_sum _
      (fun i' _ => h_inner_integrable i')]
  rw [show (fun n => (tensorPrincipalForm (I := I) (M := M) g α
        (chartPouKernel_isCompact (I := I) (M := M) α)
        (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)).bilin
      (tensorComponentEuclid (I := I) (M := M) g r s
        (eigenvectorPouApprox (I := I) (M := M)
          g r s i α n) α P₀) ψ) =
      (fun n => ∑ i' : Fin (Module.finrank ℝ E),
        ∫ y, (mtest i' : EuclN → ℝ) y *
          ((euclidPartial_eigenvectorPouApprox_component_memLp
            (I := I) (M := M) g r s i α P₀ i' n).toLp _ : EuclN → ℝ) y
          ∂(chartL2Measure (I := I) (M := M) α))
      from funext h_bilin_n]
  rw [← h_limit_eq]
  exact h_sum_tendsto

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
