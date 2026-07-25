import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Component.PouComponentBridge
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Completion


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators Matrix
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Analysis.Laplacian.MetricExtension hiding chartTargetEuclid
open DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv

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

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma wrappedComponentProj_section_eq_tensorChartComponentRaw
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M) (b : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    wrappedComponentProj (I := I) (M := M) r s α b Idx Jdx (S.toSection b) =
      tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx b := by
  rw [wrappedComponentProj_apply, tensorChartComponentRaw_def]
  rfl

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma tensorInnerPointwise_chart_eq_component_sum
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Sg T : SmoothCcTensor g r s) (α : M)
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    tensorInnerPointwise (I := I) (M := M) g r s
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
        (Sg.toFun ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
        (T.toFun ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) =
      ∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
        covChartMetricGram (I := I) (M := M) g r s α P Q y *
          tensorComponentEuclid (I := I) (M := M) g r s Sg α P y *
          tensorComponentEuclid (I := I) (M := M) g r s T α Q y := by
  classical
  set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb_def
  have hb_chart : b ∈ (chartAt H α).source :=
    symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) α hy
  rw [show Sg.toFun b = TensorRSSpace.toModel (Sg.toSection b) from rfl]
  rw [show T.toFun b = TensorRSSpace.toModel (T.toSection b) from rfl]
  rw [tensorInnerPointwise_toModel_eq_component_sum (I := I) (M := M)
    g r s α hb_chart (Sg.toSection b) (T.toSection b)]
  refine Finset.sum_congr rfl (fun P _ => Finset.sum_congr rfl (fun Q _ => ?_))
  rw [show chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α b
        (tensorChartBasisElement (E := E) r s P.1 P.2)
        (tensorChartBasisElement (E := E) r s Q.1 Q.2) =
      covChartMetricGram (I := I) (M := M) g r s α P Q y from by
    rw [covChartMetricGram_def, ← hb_def]]
  rw [wrappedComponentProj_section_eq_tensorChartComponentRaw
    (I := I) (M := M) g r s Sg α b P.1 P.2,
    wrappedComponentProj_section_eq_tensorChartComponentRaw
      (I := I) (M := M) g r s T α b Q.1 Q.2]
  rw [show tensorChartComponentRaw (I := I) (M := M) g r s Sg α P.1 P.2 b =
      tensorComponentEuclid (I := I) (M := M) g r s Sg α P y from by
    rw [tensorComponentEuclid_apply_of_mem (I := I) (M := M) g r s Sg α P hy,
      hb_def]]
  rw [show tensorChartComponentRaw (I := I) (M := M) g r s T α Q.1 Q.2 b =
      tensorComponentEuclid (I := I) (M := M) g r s T α Q y from by
    rw [tensorComponentEuclid_apply_of_mem (I := I) (M := M) g r s T α Q hy,
      hb_def]]
  ring

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma pairingIntegrand_continuous
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Sg T : SmoothCcTensor g r s) :
    Continuous
      (fun x : M => tensorInnerPointwise (I := I) (M := M) g r s x
        (Sg.toFun x) (T.toFun x)) :=
  DifferentialGeometry.Integral.L2.SmoothCcTensor.continuous_inner_cross
    (I := I) (M := M) Sg T

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma pairingIntegrand_tsupport_subset
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Sg T : SmoothCcTensor g r s) (α : M)
    (hSg : tsupport Sg.toFun ⊆ (chartAt H α).source) :
    tsupport
        (fun x : M => tensorInnerPointwise (I := I) (M := M) g r s x
          (Sg.toFun x) (T.toFun x)) ⊆
      (chartAt H α).source := by
  refine (closure_minimal ?_ (isClosed_tsupport Sg.toFun)).trans hSg
  intro x hx
  rw [Function.mem_support] at hx
  by_contra hx_notsupp
  exact hx (by
    rw [image_eq_zero_of_notMem_tsupport hx_notsupp]
    exact tensorInnerPointwise_zero_left (I := I) (M := M) g r s x (T.toFun x))

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorL2Inner_chartSupported_chart_pull
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Sg T : SmoothCcTensor g r s) (α : M)
    (hSg : tsupport Sg.toFun ⊆ (chartAt H α).source) :
    tensorL2Inner (I := I) (M := M) g r s Sg.toFun T.toFun =
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          (∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
            covChartMetricGram (I := I) (M := M) g r s α P Q y *
              tensorComponentEuclid (I := I) (M := M) g r s Sg α P y *
              tensorComponentEuclid (I := I) (M := M) g r s T α Q y)
        ∂(volume : Measure EuclN) := by
  classical
  rw [show tensorL2Inner (I := I) (M := M) g r s Sg.toFun T.toFun =
      ∫ x, tensorInnerPointwise (I := I) (M := M) g r s x (Sg.toFun x) (T.toFun x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) from rfl]
  have hcont : Continuous
      (fun x : M => tensorInnerPointwise (I := I) (M := M) g r s x
        (Sg.toFun x) (T.toFun x)) :=
    pairingIntegrand_continuous (I := I) (M := M) g r s Sg T
  have hsupp : tsupport
      (fun x : M => tensorInnerPointwise (I := I) (M := M) g r s x
        (Sg.toFun x) (T.toFun x)) ⊆
      (chartAt H α).source :=
    pairingIntegrand_tsupport_subset (I := I) (M := M) g r s Sg T α hSg
  rw [integral_riemannianVolumeMeasure_eq_euclidean_chartTarget
    (I := I) (M := M) g α hcont hsupp]
  rw [map_toEuclidean_modelHaar_eq_volume (E := E)]
  have hctE_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α).measurableSet
  refine setIntegral_congr_fun hctE_meas (fun y hy => ?_)
  rw [tensorInnerPointwise_chart_eq_component_sum (I := I) (M := M)
    g r s Sg T α hy]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma tensorComponentEuclid_pouSmul_eq_tensorChartComponent
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Sg : SmoothCcTensor g r s) (P : CompIdx E r s) :
    tensorComponentEuclid (I := I) (M := M) g r s
        (pouSmul (I := I) (M := M) g r s α Sg) α P =
      tensorChartComponent (I := I) (M := M) g r s Sg α P.1 P.2 :=
  (tensorChartComponent_eq_tensorComponentEuclid_pouSmul
    (I := I) (M := M) g r s α Sg P).symm

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma componentSum_pouSmul_reassoc
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Sg T : SmoothCcTensor g r s)
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    (∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
        covChartMetricGram (I := I) (M := M) g r s α P Q y *
          tensorComponentEuclid (I := I) (M := M) g r s
            (pouSmul (I := I) (M := M) g r s α Sg) α P y *
          tensorComponentEuclid (I := I) (M := M) g r s T α Q y) =
      ∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
        covChartMetricGram (I := I) (M := M) g r s α P Q y *
          tensorComponentEuclid (I := I) (M := M) g r s Sg α P y *
          tensorChartComponent (I := I) (M := M) g r s T α Q.1 Q.2 y := by
  classical
  refine Finset.sum_congr rfl (fun P _ => Finset.sum_congr rfl (fun Q _ => ?_))
  rw [tensorComponentEuclid_pouSmul_eq_tensorChartComponent
    (I := I) (M := M) g r s α Sg P]
  set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb_def
  have hSg_eq : tensorChartComponent (I := I) (M := M) g r s Sg α P.1 P.2 y =
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
        tensorComponentEuclid (I := I) (M := M) g r s Sg α P y := by
    rw [tensorChartComponent_def]
    rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy]
    rw [tensorComponentEuclid_apply_of_mem (I := I) (M := M) g r s Sg α P hy]
    rfl
  have hT_eq : tensorChartComponent (I := I) (M := M) g r s T α Q.1 Q.2 y =
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
        tensorComponentEuclid (I := I) (M := M) g r s T α Q y := by
    rw [tensorChartComponent_def]
    rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy]
    rw [tensorComponentEuclid_apply_of_mem (I := I) (M := M) g r s T α Q hy]
    rfl
  rw [hSg_eq, hT_eq]
  ring

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma tensorChartComponent_aeEq_tensorL2ChartComponent
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M) (Q : CompIdx E r s) :
    tensorChartComponent (I := I) (M := M) g r s T α Q.1 Q.2 =ᵐ[
        (volume : Measure EuclN).restrict (chartTargetEuclid (I := I) (M := M) α)]
      ((tensorL2ChartComponent (I := I) (M := M) g r s
          (T : TensorL2 r s g) α Q :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) :=
  (tensorL2ChartComponent_smoothToTensorL2_coeFn
    (I := I) (M := M) g r s T α Q).symm

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma chartL2Measure_eq_volume_restrict (α : M) :
    chartL2Measure (I := I) (M := M) α =
      (volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α) := rfl

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma chartPull_integrand_aeEq_abstract
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Sg T : SmoothCcTensor g r s) :
    (fun y : EuclN => densityOnEuclid (I := I) g α y *
        (∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
          covChartMetricGram (I := I) (M := M) g r s α P Q y *
            tensorComponentEuclid (I := I) (M := M) g r s Sg α P y *
            tensorChartComponent (I := I) (M := M) g r s T α Q.1 Q.2 y)) =ᵐ[
        (volume : Measure EuclN).restrict (chartTargetEuclid (I := I) (M := M) α)]
      (fun y : EuclN => densityOnEuclid (I := I) g α y *
        (∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
          covChartMetricGram (I := I) (M := M) g r s α P Q y *
            tensorComponentEuclid (I := I) (M := M) g r s Sg α P y *
            ((tensorL2ChartComponent (I := I) (M := M) g r s
                (T : TensorL2 r s g) α Q :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ)
              y)) := by
  classical
  have hae : ∀ Q : CompIdx E r s,
      tensorChartComponent (I := I) (M := M) g r s T α Q.1 Q.2 =ᵐ[
          (volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)]
        ((tensorL2ChartComponent (I := I) (M := M) g r s
            (T : TensorL2 r s g) α Q :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) :=
    fun Q => tensorChartComponent_aeEq_tensorL2ChartComponent
      (I := I) (M := M) g r s T α Q
  have hall : ∀ᵐ y ∂((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)),
      ∀ Q : CompIdx E r s,
        tensorChartComponent (I := I) (M := M) g r s T α Q.1 Q.2 y =
          ((tensorL2ChartComponent (I := I) (M := M) g r s
              (T : TensorL2 r s g) α Q :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y := by
    rw [MeasureTheory.ae_all_iff]
    exact hae
  filter_upwards [hall] with y hy
  refine congrArg (densityOnEuclid (I := I) g α y * ·) ?_
  refine Finset.sum_congr rfl (fun P _ => Finset.sum_congr rfl (fun Q _ => ?_))
  rw [hy Q]

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma tensorL2Inner_pouSmul_smooth_chart_pull
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Sg T : SmoothCcTensor g r s) :
    tensorL2Inner (I := I) (M := M) g r s
        (pouSmul (I := I) (M := M) g r s α Sg).toFun T.toFun =
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          (∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
            covChartMetricGram (I := I) (M := M) g r s α P Q y *
              tensorComponentEuclid (I := I) (M := M) g r s Sg α P y *
              ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (T : TensorL2 r s g) α Q :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ)
                y)
        ∂(volume : Measure EuclN) := by
  classical
  have hpou_supp : tsupport (pouSmul (I := I) (M := M) g r s α Sg).toFun ⊆
      (chartAt H α).source :=
    pouSmul_tsupport_subset_chartSource (I := I) (M := M) g r s α Sg
  rw [tensorL2Inner_chartSupported_chart_pull (I := I) (M := M) g r s
    (pouSmul (I := I) (M := M) g r s α Sg) T α hpou_supp]
  have hctE_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α).measurableSet
  rw [setIntegral_congr_fun hctE_meas (fun y hy => by
    rw [componentSum_pouSmul_reassoc (I := I) (M := M) g r s α Sg T hy])]
  exact MeasureTheory.integral_congr_ae
    (chartPull_integrand_aeEq_abstract (I := I) (M := M) g r s α Sg T)

private noncomputable def chartPullCoeff
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Sg : SmoothCcTensor g r s) (Q : CompIdx E r s) : EuclN → ℝ :=
  fun y => ∑ P : CompIdx E r s,
    densityOnEuclid (I := I) g α y *
      covChartMetricGram (I := I) (M := M) g r s α P Q y *
      tensorComponentEuclid (I := I) (M := M) g r s Sg α P y

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M] in
private lemma chartPullCoeff_summand_continuous
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Sg : SmoothCcTensor g r s) (P Q : CompIdx E r s)
    (hSg : tsupport Sg.toFun ⊆ (chartAt H α).source) :
    Continuous (fun y : EuclN =>
      densityOnEuclid (I := I) g α y *
        covChartMetricGram (I := I) (M := M) g r s α P Q y *
        tensorComponentEuclid (I := I) (M := M) g r s Sg α P y) := by
  classical
  have hopen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α
  have hdensity : ContinuousOn (densityOnEuclid (I := I) g α)
      (chartTargetEuclid (I := I) (M := M) α) :=
    (densityOnEuclid_contDiffOn (I := I) g α).continuousOn
  have hgram : ContinuousOn (covChartMetricGram (I := I) (M := M) g r s α P Q)
      (chartTargetEuclid (I := I) (M := M) α) :=
    (covChartMetricGram_contDiffOn (I := I) (M := M) g r s α P Q).continuousOn
  have hcomp : ContinuousOn (tensorComponentEuclid (I := I) (M := M) g r s Sg α P)
      (chartTargetEuclid (I := I) (M := M) α) :=
    (tensorComponentEuclid_contDiffOn (I := I) (M := M) g r s Sg α P).continuousOn
  have hcontOn : ContinuousOn (fun y : EuclN =>
      densityOnEuclid (I := I) g α y *
        covChartMetricGram (I := I) (M := M) g r s α P Q y *
        tensorComponentEuclid (I := I) (M := M) g r s Sg α P y)
      (chartTargetEuclid (I := I) (M := M) α) :=
    (hdensity.mul hgram).mul hcomp
  have hsupp_subset : tsupport (fun y : EuclN =>
      densityOnEuclid (I := I) g α y *
        covChartMetricGram (I := I) (M := M) g r s α P Q y *
        tensorComponentEuclid (I := I) (M := M) g r s Sg α P y) ⊆
      chartTargetEuclid (I := I) (M := M) α := by
    refine Subset.trans ?_
      (tensorComponentEuclid_tsupport_subset (I := I) (M := M) g r s Sg α P hSg)
    refine closure_minimal ?_ (isClosed_tsupport _)
    intro y hy
    rw [Function.mem_support] at hy
    refine subset_tsupport _ ?_
    rw [Function.mem_support]
    intro hzero
    exact hy (by rw [hzero, mul_zero])
  exact hcontOn.continuous_of_tsupport_subset hopen hsupp_subset

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma chartPullCoeff_summand_hasCompactSupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Sg : SmoothCcTensor g r s) (P Q : CompIdx E r s)
    (hSg : tsupport Sg.toFun ⊆ (chartAt H α).source) :
    HasCompactSupport (fun y : EuclN =>
      densityOnEuclid (I := I) g α y *
        covChartMetricGram (I := I) (M := M) g r s α P Q y *
        tensorComponentEuclid (I := I) (M := M) g r s Sg α P y) := by
  classical
  refine HasCompactSupport.of_support_subset_isCompact
    (tensorComponentEuclid_hasCompactSupport (I := I) (M := M) g r s Sg α P hSg) ?_
  intro y hy
  rw [Function.mem_support] at hy
  refine subset_tsupport _ ?_
  rw [Function.mem_support]
  intro hzero
  exact hy (by rw [hzero, mul_zero])

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M] in
private lemma chartPullCoeff_continuous
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Sg : SmoothCcTensor g r s) (Q : CompIdx E r s)
    (hSg : tsupport Sg.toFun ⊆ (chartAt H α).source) :
    Continuous (chartPullCoeff (I := I) (M := M) g r s α Sg Q) := by
  classical
  unfold chartPullCoeff
  exact continuous_finset_sum _ (fun P _ =>
    chartPullCoeff_summand_continuous (I := I) (M := M) g r s α Sg P Q hSg)

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma chartPullCoeff_hasCompactSupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Sg : SmoothCcTensor g r s) (Q : CompIdx E r s)
    (hSg : tsupport Sg.toFun ⊆ (chartAt H α).source) :
    HasCompactSupport (chartPullCoeff (I := I) (M := M) g r s α Sg Q) := by
  classical
  set K : Set EuclN :=
    ⋃ P : CompIdx E r s, tsupport (fun y : EuclN =>
      densityOnEuclid (I := I) g α y *
        covChartMetricGram (I := I) (M := M) g r s α P Q y *
        tensorComponentEuclid (I := I) (M := M) g r s Sg α P y) with hK_def
  have hK_compact : IsCompact K := by
    rw [hK_def]
    refine isCompact_iUnion (fun P => ?_)
    exact chartPullCoeff_summand_hasCompactSupport
      (I := I) (M := M) g r s α Sg P Q hSg
  refine HasCompactSupport.of_support_subset_isCompact hK_compact ?_
  intro y hy
  rw [Function.mem_support] at hy
  rw [hK_def, Set.mem_iUnion]
  by_contra hy_notin
  simp only [not_exists] at hy_notin
  refine hy ?_
  unfold chartPullCoeff
  refine Finset.sum_eq_zero (fun P _ => ?_)
  exact image_eq_zero_of_notMem_tsupport (f := fun y : EuclN =>
    densityOnEuclid (I := I) g α y *
      covChartMetricGram (I := I) (M := M) g r s α P Q y *
      tensorComponentEuclid (I := I) (M := M) g r s Sg α P y) (hy_notin P)

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M] in
private lemma chartPullCoeff_memLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Sg : SmoothCcTensor g r s) (Q : CompIdx E r s)
    (hSg : tsupport Sg.toFun ⊆ (chartAt H α).source) :
    MemLp (chartPullCoeff (I := I) (M := M) g r s α Sg Q) 2
      (chartL2Measure (I := I) (M := M) α) := by
  haveI : IsFiniteMeasureOnCompacts (chartL2Measure (I := I) (M := M) α) := by
    rw [chartL2Measure_eq_volume_restrict (I := I) (M := M) α]
    infer_instance
  exact (chartPullCoeff_continuous (I := I) (M := M) g r s α Sg Q
      hSg).memLp_of_hasCompactSupport
    (chartPullCoeff_hasCompactSupport (I := I) (M := M) g r s α Sg Q hSg)

private noncomputable def chartPullCoeffLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Sg : SmoothCcTensor g r s) (Q : CompIdx E r s)
    (hSg : tsupport Sg.toFun ⊆ (chartAt H α).source) :
    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) :=
  (chartPullCoeff_memLp (I := I) (M := M) g r s α Sg Q hSg).toLp _

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M] in
private lemma inner_chartPullCoeffLp_eq_integral
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Sg : SmoothCcTensor g r s) (Q : CompIdx E r s)
    (hSg : tsupport Sg.toFun ⊆ (chartAt H α).source)
    (w : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
    (⟪chartPullCoeffLp (I := I) (M := M) g r s α Sg Q hSg, w⟫_ℝ : ℝ) =
      ∫ y, chartPullCoeff (I := I) (M := M) g r s α Sg Q y * (w : EuclN → ℝ) y
        ∂(chartL2Measure (I := I) (M := M) α) := by
  classical
  rw [MeasureTheory.L2.inner_def]
  refine MeasureTheory.integral_congr_ae ?_
  have hcoe : ((chartPullCoeffLp (I := I) (M := M) g r s α Sg Q hSg :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) =ᵐ[
        chartL2Measure (I := I) (M := M) α]
      chartPullCoeff (I := I) (M := M) g r s α Sg Q := by
    unfold chartPullCoeffLp
    exact MemLp.coeFn_toLp _
  filter_upwards [hcoe] with y hy
  rw [RCLike.inner_apply, conj_trivial, hy, mul_comm]

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma continuous_chartPullCoeff_pairing
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Sg : SmoothCcTensor g r s) (Q : CompIdx E r s)
    (hSg : tsupport Sg.toFun ⊆ (chartAt H α).source) :
    Continuous (fun u : TensorL2 r s g =>
      (⟪chartPullCoeffLp (I := I) (M := M) g r s α Sg Q hSg,
          tensorL2ChartComponent (I := I) (M := M) g r s u α Q⟫_ℝ : ℝ)) := by
  classical
  have hfun : (fun u : TensorL2 r s g =>
      (⟪chartPullCoeffLp (I := I) (M := M) g r s α Sg Q hSg,
          tensorL2ChartComponent (I := I) (M := M) g r s u α Q⟫_ℝ : ℝ)) =
      (fun w : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) =>
        (⟪chartPullCoeffLp (I := I) (M := M) g r s α Sg Q hSg, w⟫_ℝ : ℝ)) ∘
        (fun u : TensorL2 r s g =>
          tensorL2ChartComponentCLM (I := I) (M := M) g r s α Q u) := by
    funext u
    rw [Function.comp_apply, tensorL2ChartComponentCLM_apply]
  rw [hfun]
  refine Continuous.comp ?_
    (tensorL2ChartComponentCLM (I := I) (M := M) g r s α Q).continuous
  exact (innerSL ℝ
    (chartPullCoeffLp (I := I) (M := M) g r s α Sg Q hSg)).continuous

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma chartPull_integrand_eq_coeff_mul
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Sg : SmoothCcTensor g r s) (u : TensorL2 r s g) (y : EuclN) :
    densityOnEuclid (I := I) g α y *
        (∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
          covChartMetricGram (I := I) (M := M) g r s α P Q y *
            tensorComponentEuclid (I := I) (M := M) g r s Sg α P y *
            ((tensorL2ChartComponent (I := I) (M := M) g r s u α Q :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) =
      ∑ Q : CompIdx E r s,
        chartPullCoeff (I := I) (M := M) g r s α Sg Q y *
          ((tensorL2ChartComponent (I := I) (M := M) g r s u α Q :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y := by
  classical
  have hlhs : densityOnEuclid (I := I) g α y *
        (∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
          covChartMetricGram (I := I) (M := M) g r s α P Q y *
            tensorComponentEuclid (I := I) (M := M) g r s Sg α P y *
            ((tensorL2ChartComponent (I := I) (M := M) g r s u α Q :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) =
      ∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
        (densityOnEuclid (I := I) g α y *
            covChartMetricGram (I := I) (M := M) g r s α P Q y *
            tensorComponentEuclid (I := I) (M := M) g r s Sg α P y) *
          ((tensorL2ChartComponent (I := I) (M := M) g r s u α Q :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun P _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun Q _ => ?_)
    ring
  have hrhs : (∑ Q : CompIdx E r s,
        chartPullCoeff (I := I) (M := M) g r s α Sg Q y *
          ((tensorL2ChartComponent (I := I) (M := M) g r s u α Q :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) =
      ∑ Q : CompIdx E r s, ∑ P : CompIdx E r s,
        (densityOnEuclid (I := I) g α y *
            covChartMetricGram (I := I) (M := M) g r s α P Q y *
            tensorComponentEuclid (I := I) (M := M) g r s Sg α P y) *
          ((tensorL2ChartComponent (I := I) (M := M) g r s u α Q :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y := by
    refine Finset.sum_congr rfl (fun Q _ => ?_)
    unfold chartPullCoeff
    rw [Finset.sum_mul]
  rw [hlhs, hrhs, Finset.sum_comm]

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma chartPull_summand_integrable
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Sg : SmoothCcTensor g r s) (u : TensorL2 r s g) (Q : CompIdx E r s)
    (hSg : tsupport Sg.toFun ⊆ (chartAt H α).source) :
    Integrable (fun y : EuclN =>
        chartPullCoeff (I := I) (M := M) g r s α Sg Q y *
          ((tensorL2ChartComponent (I := I) (M := M) g r s u α Q :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      (chartL2Measure (I := I) (M := M) α) := by
  classical
  have hcoeff : MemLp (chartPullCoeff (I := I) (M := M) g r s α Sg Q) 2
      (chartL2Measure (I := I) (M := M) α) :=
    chartPullCoeff_memLp (I := I) (M := M) g r s α Sg Q hSg
  have hcomp : MemLp
      (((tensorL2ChartComponent (I := I) (M := M) g r s u α Q :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ)) 2
      (chartL2Measure (I := I) (M := M) α) :=
    Lp.memLp _
  have hint := MemLp.integrable_mul hcoeff hcomp
  exact hint

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma chartPull_integral_eq_sum_inner
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Sg : SmoothCcTensor g r s) (u : TensorL2 r s g)
    (hSg : tsupport Sg.toFun ⊆ (chartAt H α).source) :
    ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          (∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
            covChartMetricGram (I := I) (M := M) g r s α P Q y *
              tensorComponentEuclid (I := I) (M := M) g r s Sg α P y *
              ((tensorL2ChartComponent (I := I) (M := M) g r s u α Q :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
        ∂(volume : Measure EuclN) =
      ∑ Q : CompIdx E r s,
        (⟪chartPullCoeffLp (I := I) (M := M) g r s α Sg Q hSg,
            tensorL2ChartComponent (I := I) (M := M) g r s u α Q⟫_ℝ : ℝ) := by
  classical
  rw [show (∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          (∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
            covChartMetricGram (I := I) (M := M) g r s α P Q y *
              tensorComponentEuclid (I := I) (M := M) g r s Sg α P y *
              ((tensorL2ChartComponent (I := I) (M := M) g r s u α Q :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
        ∂(volume : Measure EuclN)) =
      ∫ y,
        densityOnEuclid (I := I) g α y *
          (∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
            covChartMetricGram (I := I) (M := M) g r s α P Q y *
              tensorComponentEuclid (I := I) (M := M) g r s Sg α P y *
              ((tensorL2ChartComponent (I := I) (M := M) g r s u α Q :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
        ∂(chartL2Measure (I := I) (M := M) α) from rfl]
  rw [show (fun y : EuclN =>
        densityOnEuclid (I := I) g α y *
          (∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
            covChartMetricGram (I := I) (M := M) g r s α P Q y *
              tensorComponentEuclid (I := I) (M := M) g r s Sg α P y *
              ((tensorL2ChartComponent (I := I) (M := M) g r s u α Q :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)) =
      (fun y : EuclN =>
        ∑ Q : CompIdx E r s,
          chartPullCoeff (I := I) (M := M) g r s α Sg Q y *
            ((tensorL2ChartComponent (I := I) (M := M) g r s u α Q :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) from by
    funext y
    exact chartPull_integrand_eq_coeff_mul (I := I) (M := M) g r s α Sg u y]
  rw [MeasureTheory.integral_finset_sum (Finset.univ : Finset (CompIdx E r s))
    (fun Q _ => chartPull_summand_integrable
      (I := I) (M := M) g r s α Sg u Q hSg)]
  refine Finset.sum_congr rfl (fun Q _ => ?_)
  rw [inner_chartPullCoeffLp_eq_integral (I := I) (M := M) g r s α Sg Q hSg]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma continuous_lhs
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Sg : SmoothCcTensor g r s) :
    Continuous (fun u : TensorL2 r s g =>
      (⟪(pouSmul (I := I) (M := M) g r s α Sg : TensorL2 r s g), u⟫_ℝ : ℝ)) :=
  (innerSL ℝ (pouSmul (I := I) (M := M) g r s α Sg :
    TensorL2 r s g)).continuous

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma continuous_rhs
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Sg : SmoothCcTensor g r s)
    (hSg : tsupport Sg.toFun ⊆ (chartAt H α).source) :
    Continuous (fun u : TensorL2 r s g =>
      ∑ Q : CompIdx E r s,
        (⟪chartPullCoeffLp (I := I) (M := M) g r s α Sg Q hSg,
            tensorL2ChartComponent (I := I) (M := M) g r s u α Q⟫_ℝ : ℝ)) :=
  continuous_finset_sum _ (fun Q _ =>
    continuous_chartPullCoeff_pairing (I := I) (M := M) g r s α Sg Q hSg)

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma headline_on_smooth
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Sg : SmoothCcTensor g r s)
    (hSg : tsupport Sg.toFun ⊆ (chartAt H α).source)
    (T : SmoothCcTensor g r s) :
    (⟪(pouSmul (I := I) (M := M) g r s α Sg : TensorL2 r s g),
        (T : TensorL2 r s g)⟫_ℝ : ℝ) =
      ∑ Q : CompIdx E r s,
        (⟪chartPullCoeffLp (I := I) (M := M) g r s α Sg Q hSg,
            tensorL2ChartComponent (I := I) (M := M) g r s
              (T : TensorL2 r s g) α Q⟫_ℝ : ℝ) := by
  classical
  rw [show (⟪(pouSmul (I := I) (M := M) g r s α Sg : TensorL2 r s g),
        (T : TensorL2 r s g)⟫_ℝ : ℝ) =
      (⟪pouSmul (I := I) (M := M) g r s α Sg, T⟫_ℝ : ℝ) from
    UniformSpace.Completion.inner_coe _ _]
  rw [SmoothCcTensor.inner_def]
  rw [tensorL2Inner_pouSmul_smooth_chart_pull (I := I) (M := M) g r s α Sg T]
  exact chartPull_integral_eq_sum_inner (I := I) (M := M) g r s α Sg
    (T : TensorL2 r s g) hSg

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma headline_fun_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Sg : SmoothCcTensor g r s)
    (hSg : tsupport Sg.toFun ⊆ (chartAt H α).source) :
    (fun u : TensorL2 r s g =>
        (⟪(pouSmul (I := I) (M := M) g r s α Sg : TensorL2 r s g), u⟫_ℝ : ℝ)) =
      (fun u : TensorL2 r s g =>
        ∑ Q : CompIdx E r s,
          (⟪chartPullCoeffLp (I := I) (M := M) g r s α Sg Q hSg,
              tensorL2ChartComponent (I := I) (M := M) g r s u α Q⟫_ℝ : ℝ)) := by
  classical
  have hdense : DenseRange
      ((↑) : SmoothCcTensor g r s → UniformSpace.Completion (SmoothCcTensor g r s)) :=
    UniformSpace.Completion.denseRange_coe
  refine hdense.equalizer
    (continuous_lhs (I := I) (M := M) g r s α Sg)
    (continuous_rhs (I := I) (M := M) g r s α Sg hSg) ?_
  funext T
  exact headline_on_smooth (I := I) (M := M) g r s α Sg hSg T

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorL2Inner_pouSmul_tensorL2ChartComponent_pull
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (u : TensorL2 r s g) (Sg : SmoothCcTensor g r s)
    (hSg : tsupport Sg.toFun ⊆ (chartAt H α).source) :
    (⟪(pouSmul (I := I) (M := M) g r s α Sg : TensorL2 r s g), u⟫_ℝ : ℝ) =
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          (∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
            covChartMetricGram (I := I) (M := M) g r s α P Q y *
              tensorComponentEuclid (I := I) (M := M) g r s Sg α P y *
              ((tensorL2ChartComponent (I := I) (M := M) g r s u α Q :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
        ∂(volume : Measure EuclN) := by
  classical
  have hfun := headline_fun_eq (I := I) (M := M) g r s α Sg hSg
  have hu := congrFun hfun u
  rw [hu]
  exact (chartPull_integral_eq_sum_inner (I := I) (M := M) g r s α Sg u hSg).symm

section ElaborationTests

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)

example (Sg T : SmoothCcTensor g r s) (α : M)
    (hSg : tsupport Sg.toFun ⊆ (chartAt H α).source) :
    tensorL2Inner (I := I) (M := M) g r s Sg.toFun T.toFun =
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          (∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
            covChartMetricGram (I := I) (M := M) g r s α P Q y *
              tensorComponentEuclid (I := I) (M := M) g r s Sg α P y *
              tensorComponentEuclid (I := I) (M := M) g r s T α Q y)
        ∂(volume : Measure EuclN) :=
  tensorL2Inner_chartSupported_chart_pull (I := I) (M := M) g r s Sg T α hSg

example (u : TensorL2 r s g) (Sg : SmoothCcTensor g r s) (α : M)
    (hSg : tsupport Sg.toFun ⊆ (chartAt H α).source) :
    (⟪(pouSmul (I := I) (M := M) g r s α Sg : TensorL2 r s g), u⟫_ℝ : ℝ) =
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          (∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
            covChartMetricGram (I := I) (M := M) g r s α P Q y *
              tensorComponentEuclid (I := I) (M := M) g r s Sg α P y *
              ((tensorL2ChartComponent (I := I) (M := M) g r s u α Q :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
        ∂(volume : Measure EuclN) :=
  tensorL2Inner_pouSmul_tensorL2ChartComponent_pull
    (I := I) (M := M) g r s α u Sg hSg

end ElaborationTests

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
