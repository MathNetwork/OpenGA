import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.LowerOrder.LowerOrderCoeffFactors


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold Set Filter MeasureTheory
open scoped Manifold Topology ContDiff BigOperators Matrix ENNReal NNReal
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Analysis.Laplacian.MetricExtension hiding chartTargetEuclid

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

def approxComponentLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s) (n : ℕ) :
    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) :=
  (tensorChartComponent_memLp (I := I) (M := M) g r s
    (eigenvectorSmoothApprox (I := I) (M := M) g r s i n).toCcTensor
    α P.1 P.2).toLp
    (tensorChartComponent (I := I) (M := M) g r s
      (eigenvectorSmoothApprox (I := I) (M := M)
        g r s i n).toCcTensor α P.1 P.2)

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in

def componentLpLimit
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s) :
    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) :=
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  i.fst.val •
    tensorL2ChartComponent (I := I) (M := M) g r s
      (tensorResolventEigenbasisVec (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s) i)
      α P

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in

omit [CompleteSpace E] in
lemma approxComponentLp_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s) :
    Filter.Tendsto
      (fun n => approxComponentLp (I := I) (M := M) g r s i α P n)
      atTop
      (𝓝 (componentLpLimit (I := I) (M := M) g r s i α P)) := by
  classical
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  have h_tendsto :=
    (eigenvectorChartComponentL2_tendsto (I := I) (M := M)
      g r s i α P).const_smul i.fst.val
  have h_term : ∀ n : ℕ,
      i.fst.val •
        tensorL2ChartComponent (I := I) (M := M) g r s
          ((i.fst.val)⁻¹ •
            (((eigenvectorSmoothApprox (I := I) (M := M)
                g r s i n).toCcTensor) : TensorL2 r s g)) α P =
        approxComponentLp (I := I) (M := M) g r s i α P n := by
    intro n
    rw [eigenvectorChartComponentL2_approx_eq (I := I) (M := M)
      g r s i α P n, smul_smul, mul_inv_cancel₀ i.fst.val_ne_zero,
      one_smul]
    rfl
  rw [show (fun n => i.fst.val •
        tensorL2ChartComponent (I := I) (M := M) g r s
          ((i.fst.val)⁻¹ •
            (((eigenvectorSmoothApprox (I := I) (M := M)
                g r s i n).toCcTensor) : TensorL2 r s g)) α P) =
      (fun n => approxComponentLp (I := I) (M := M)
        g r s i α P n) from funext h_term] at h_tendsto
  exact h_tendsto

def approxPartialLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) (n : ℕ) :
    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) :=
  (chosenWeakPartial'_tensorChartComponent_memLp (I := I) (M := M) g r s
    (eigenvectorSmoothApprox (I := I) (M := M) g r s i n)
    α P.1 P.2 k).toLp
    (chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
      (tensorChartComponent (I := I) (M := M) g r s
        (eigenvectorSmoothApprox (I := I) (M := M)
          g r s i n).toCcTensor α P.1 P.2)
      (chartTargetEuclid (I := I) (M := M) α))

def partialLpLimit
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) :=
  i.fst.val •
    eigenvectorChartPartialLp (I := I) (M := M) g r s i α P k

omit [CompleteSpace E] in
lemma approxPartialLp_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    Filter.Tendsto
      (fun n => approxPartialLp (I := I) (M := M) g r s i α P k n)
      atTop
      (𝓝 (partialLpLimit (I := I) (M := M) g r s i α P k)) := by
  classical
  have h_tendsto :=
    (eigenvectorChartPartialLp_tendsto (I := I) (M := M)
      g r s i α P k).const_smul i.fst.val
  have h_term : ∀ n : ℕ,
      i.fst.val •
        ((i.fst.val)⁻¹ •
          eigenvectorChartPartialCLM (I := I) (M := M) g r s α P k
            (smoothToTensorH1Compl (I := I) (M := M) g r s
              (eigenvectorSmoothApprox (I := I) (M := M)
                g r s i n))) =
        approxPartialLp (I := I) (M := M) g r s i α P k n := by
    intro n
    rw [eigenvectorChartPartialLp_approx_eq (I := I) (M := M)
      g r s i α P k n, smul_smul, mul_inv_cancel₀ i.fst.val_ne_zero,
      one_smul]
    rfl
  rw [show (fun n => i.fst.val •
        ((i.fst.val)⁻¹ •
          eigenvectorChartPartialCLM (I := I) (M := M) g r s α P k
            (smoothToTensorH1Compl (I := I) (M := M) g r s
              (eigenvectorSmoothApprox (I := I) (M := M)
                g r s i n)))) =
      (fun n => approxPartialLp (I := I) (M := M)
        g r s i α P k n) from funext h_term] at h_tendsto
  exact h_tendsto

omit [CompleteSpace E] in
lemma tendsto_componentSummand
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s)
    {c : EuclN → ℝ}
    (hc : ContDiffOn ℝ ∞ c (chartTargetEuclid (I := I) (M := M) α))
    (hP_memLp : ∀ n : ℕ,
      MemLp (fun y => c y *
        tensorChartComponent (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor α P.1 P.2 y) 2
        (chartL2Measure (I := I) (M := M) α))
    (hlim_memLp : MemLp
      (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α) c y *
        (componentLpLimit (I := I) (M := M) g r s i α P :
          EuclN → ℝ) y) 2 (chartL2Measure (I := I) (M := M) α)) :
    Filter.Tendsto
      (fun n => (hP_memLp n).toLp _)
      atTop
      (𝓝 (hlim_memLp.toLp _)) := by
  classical
  obtain ⟨C, hC_nn, hC⟩ :=
    exists_bound_on_chartPouKernel (I := I) (M := M) α hc
  set ci : EuclN → ℝ := Set.indicator (chartPouKernel (I := I) (M := M) α) c
    with hci_def
  have hci_bd : ∀ y : EuclN, ‖ci y‖ ≤ C := by
    intro y
    by_cases hy : y ∈ chartPouKernel (I := I) (M := M) α
    · rw [hci_def, Set.indicator_of_mem hy]; exact hC y hy
    · rw [hci_def, Set.indicator_of_notMem hy, norm_zero]; exact hC_nn
  have hci_meas : AEStronglyMeasurable ci
      (chartL2Measure (I := I) (M := M) α) :=
    aestronglyMeasurable_indicator_mul (I := I) (M := M) α hc
  have h_engine := tendsto_bdd_mul (I := I) (M := M) α hC_nn hci_bd hci_meas
    (approxComponentLp_tendsto (I := I) (M := M) g r s i α P)
  have h_term : ∀ n : ℕ,
      (memLp_bdd_mul (I := I) (M := M) α hC_nn hci_bd hci_meas
        (Lp.memLp (approxComponentLp (I := I) (M := M)
          g r s i α P n))).toLp _ =
        (hP_memLp n).toLp _ := by
    intro n
    apply Lp.ext
    refine (MemLp.coeFn_toLp _).trans (Filter.EventuallyEq.trans ?_
      (MemLp.coeFn_toLp _).symm)
    have hcomp : (approxComponentLp (I := I) (M := M)
        g r s i α P n : EuclN → ℝ) =ᵐ[
        chartL2Measure (I := I) (M := M) α]
        tensorChartComponent (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor α P.1 P.2 := by
      rw [approxComponentLp]; exact MemLp.coeFn_toLp _
    filter_upwards [hcomp] with y hy
    rw [hy]
    by_cases hker : y ∈ chartPouKernel (I := I) (M := M) α
    · rw [hci_def, Set.indicator_of_mem hker]
    · rw [hci_def, Set.indicator_of_notMem hker, zero_mul,
        tensorChartComponent_eq_zero_off_chartPouKernel
          (I := I) (M := M) g r s _ α P.1 P.2 hker, mul_zero]
  have h_lim :
      (memLp_bdd_mul (I := I) (M := M) α hC_nn hci_bd hci_meas
        (Lp.memLp (componentLpLimit (I := I) (M := M)
          g r s i α P))).toLp _ = hlim_memLp.toLp _ := by
    apply Lp.ext
    exact (MemLp.coeFn_toLp _).trans (MemLp.coeFn_toLp _).symm
  rw [show (fun n => (memLp_bdd_mul (I := I) (M := M) α hC_nn hci_bd hci_meas
        (Lp.memLp (approxComponentLp (I := I) (M := M)
          g r s i α P n))).toLp _) =
      (fun n => (hP_memLp n).toLp _) from funext h_term, h_lim] at h_engine
  exact h_engine

omit [CompleteSpace E] in
lemma tendsto_partialSummand
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E))
    {c : EuclN → ℝ}
    (hc : ContDiffOn ℝ ∞ c (chartTargetEuclid (I := I) (M := M) α))
    (hP_memLp : ∀ n : ℕ,
      MemLp (fun y => c y *
        euclidPartial (E := E) k
          (tensorChartComponent (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M)
              g r s i n).toCcTensor α P.1 P.2) y) 2
        (chartL2Measure (I := I) (M := M) α))
    (hlim_memLp : MemLp
      (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α) c y *
        (partialLpLimit (I := I) (M := M) g r s i α P k :
          EuclN → ℝ) y) 2 (chartL2Measure (I := I) (M := M) α)) :
    Filter.Tendsto
      (fun n => (hP_memLp n).toLp _)
      atTop
      (𝓝 (hlim_memLp.toLp _)) := by
  classical
  obtain ⟨C, hC_nn, hC⟩ :=
    exists_bound_on_chartPouKernel (I := I) (M := M) α hc
  set ci : EuclN → ℝ := Set.indicator (chartPouKernel (I := I) (M := M) α) c
    with hci_def
  have hci_bd : ∀ y : EuclN, ‖ci y‖ ≤ C := by
    intro y
    by_cases hy : y ∈ chartPouKernel (I := I) (M := M) α
    · rw [hci_def, Set.indicator_of_mem hy]; exact hC y hy
    · rw [hci_def, Set.indicator_of_notMem hy, norm_zero]; exact hC_nn
  have hci_meas : AEStronglyMeasurable ci
      (chartL2Measure (I := I) (M := M) α) :=
    aestronglyMeasurable_indicator_mul (I := I) (M := M) α hc
  have h_engine := tendsto_bdd_mul (I := I) (M := M) α hC_nn hci_bd hci_meas
    (approxPartialLp_tendsto (I := I) (M := M) g r s i α P k)
  have h_term : ∀ n : ℕ,
      (memLp_bdd_mul (I := I) (M := M) α hC_nn hci_bd hci_meas
        (Lp.memLp (approxPartialLp (I := I) (M := M)
          g r s i α P k n))).toLp _ =
        (hP_memLp n).toLp _ := by
    intro n
    apply Lp.ext
    refine (MemLp.coeFn_toLp _).trans (Filter.EventuallyEq.trans ?_
      (MemLp.coeFn_toLp _).symm)
    have hpart : (approxPartialLp (I := I) (M := M)
        g r s i α P k n : EuclN → ℝ) =ᵐ[
        chartL2Measure (I := I) (M := M) α]
        euclidPartial (E := E) k
          (tensorChartComponent (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M)
              g r s i n).toCcTensor α P.1 P.2) := by
      refine (MemLp.coeFn_toLp _).trans ?_
      exact chosenWeakPartial'_tensorChartComponent_ae_eq (I := I) (M := M)
        g r s (eigenvectorSmoothApprox (I := I) (M := M)
          g r s i n).toCcTensor α P.1 P.2 k
    filter_upwards [hpart] with y hy
    rw [hy]
    by_cases hker : y ∈ chartPouKernel (I := I) (M := M) α
    · rw [hci_def, Set.indicator_of_mem hker]
    · rw [hci_def, Set.indicator_of_notMem hker, zero_mul,
        euclidPartial_tensorChartComponent_eq_zero_off_chartPouKernel
          (I := I) (M := M) g r s _ α P.1 P.2 k hker, mul_zero]
  have h_lim :
      (memLp_bdd_mul (I := I) (M := M) α hC_nn hci_bd hci_meas
        (Lp.memLp (partialLpLimit (I := I) (M := M)
          g r s i α P k))).toLp _ = hlim_memLp.toLp _ := by
    apply Lp.ext
    exact (MemLp.coeFn_toLp _).trans (MemLp.coeFn_toLp _).symm
  rw [show (fun n => (memLp_bdd_mul (I := I) (M := M) α hC_nn hci_bd hci_meas
        (Lp.memLp (approxPartialLp (I := I) (M := M)
          g r s i α P k n))).toLp _) =
      (fun n => (hP_memLp n).toLp _) from funext h_term, h_lim] at h_engine
  exact h_engine

omit [CompleteSpace E] in
lemma euclidPartial_tensorChartComponent_approx_memLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) (n : ℕ) :
    MemLp
      (euclidPartial (E := E) k
        (tensorChartComponent (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor α P.1 P.2)) 2
      (chartL2Measure (I := I) (M := M) α) :=
  MemLp.ae_eq
    (chosenWeakPartial'_tensorChartComponent_ae_eq (I := I) (M := M) g r s
      (eigenvectorSmoothApprox (I := I) (M := M)
        g r s i n).toCcTensor α P.1 P.2 k)
    (chosenWeakPartial'_tensorChartComponent_memLp (I := I) (M := M) g r s
      (eigenvectorSmoothApprox (I := I) (M := M) g r s i n)
      α P.1 P.2 k)

omit [CompleteSpace E] in
lemma memLp_factor_mul_componentAtom
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s) (n : ℕ)
    {c : EuclN → ℝ}
    (hc : ContDiffOn ℝ ∞ c (chartTargetEuclid (I := I) (M := M) α)) :
    MemLp
      (fun y => c y *
        tensorChartComponent (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor α P.1 P.2 y) 2
      (chartL2Measure (I := I) (M := M) α) := by
  classical
  obtain ⟨C, hC_nn, hC⟩ := exists_bound_on_chartPouKernel (I := I) (M := M) α hc
  have hci_bd : ∀ y : EuclN,
      ‖Set.indicator (chartPouKernel (I := I) (M := M) α) c y‖ ≤ C := by
    intro y
    by_cases hy : y ∈ chartPouKernel (I := I) (M := M) α
    · rw [Set.indicator_of_mem hy]; exact hC y hy
    · rw [Set.indicator_of_notMem hy, norm_zero]; exact hC_nn
  have h_eq :
      (fun y => c y *
        tensorChartComponent (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor α P.1 P.2 y) =
        (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α) c y *
          tensorChartComponent (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M)
              g r s i n).toCcTensor α P.1 P.2 y) := by
    funext y
    by_cases hker : y ∈ chartPouKernel (I := I) (M := M) α
    · rw [Set.indicator_of_mem hker]
    · rw [Set.indicator_of_notMem hker, zero_mul,
        tensorChartComponent_eq_zero_off_chartPouKernel
          (I := I) (M := M) g r s _ α P.1 P.2 hker, mul_zero]
  rw [h_eq]
  exact memLp_bdd_mul (I := I) (M := M) α hC_nn hci_bd
    (aestronglyMeasurable_indicator_mul (I := I) (M := M) α hc)
    (tensorChartComponent_memLp (I := I) (M := M) g r s
      (eigenvectorSmoothApprox (I := I) (M := M)
        g r s i n).toCcTensor α P.1 P.2)

omit [CompleteSpace E] in
lemma memLp_factor_mul_partialAtom
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) (n : ℕ)
    {c : EuclN → ℝ}
    (hc : ContDiffOn ℝ ∞ c (chartTargetEuclid (I := I) (M := M) α)) :
    MemLp
      (fun y => c y *
        euclidPartial (E := E) k
          (tensorChartComponent (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M)
              g r s i n).toCcTensor α P.1 P.2) y) 2
      (chartL2Measure (I := I) (M := M) α) := by
  classical
  obtain ⟨C, hC_nn, hC⟩ := exists_bound_on_chartPouKernel (I := I) (M := M) α hc
  have hci_bd : ∀ y : EuclN,
      ‖Set.indicator (chartPouKernel (I := I) (M := M) α) c y‖ ≤ C := by
    intro y
    by_cases hy : y ∈ chartPouKernel (I := I) (M := M) α
    · rw [Set.indicator_of_mem hy]; exact hC y hy
    · rw [Set.indicator_of_notMem hy, norm_zero]; exact hC_nn
  have h_eq :
      (fun y => c y *
        euclidPartial (E := E) k
          (tensorChartComponent (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M)
              g r s i n).toCcTensor α P.1 P.2) y) =
        (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α) c y *
          euclidPartial (E := E) k
            (tensorChartComponent (I := I) (M := M) g r s
              (eigenvectorSmoothApprox (I := I) (M := M)
                g r s i n).toCcTensor α P.1 P.2) y) := by
    funext y
    by_cases hker : y ∈ chartPouKernel (I := I) (M := M) α
    · rw [Set.indicator_of_mem hker]
    · rw [Set.indicator_of_notMem hker, zero_mul,
        euclidPartial_tensorChartComponent_eq_zero_off_chartPouKernel
          (I := I) (M := M) g r s _ α P.1 P.2 k hker, mul_zero]
  rw [h_eq]
  exact memLp_bdd_mul (I := I) (M := M) α hC_nn hci_bd
    (aestronglyMeasurable_indicator_mul (I := I) (M := M) α hc)
    (euclidPartial_tensorChartComponent_approx_memLp (I := I) (M := M)
      g r s i α P k n)

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
