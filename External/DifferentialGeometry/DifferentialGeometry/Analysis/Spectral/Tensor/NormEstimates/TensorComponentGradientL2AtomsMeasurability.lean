import DifferentialGeometry.Analysis.Sobolev.Tensor.ChartComponents
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.ChartGeometry.GoodSetMeasure
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChristoffelCorrection.ChristoffelL2BoundFromH1
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChartComponent.ComponentL2BoundUniform
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChristoffelCorrection.CovL2BoundFromH1
import DifferentialGeometry.Analysis.Spectral.Tensor.Variational.H1Compl
import DifferentialGeometry.Analysis.Spectral.Tensor.Variational.PreHilbert
import DifferentialGeometry.Analysis.Spectral.Tensor.UniformChartBounds.SlotChartSourceContMDiff
import DifferentialGeometry.Analysis.Spectral.Tensor.UniformChartBounds.SlotUniformBound
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChristoffelCorrection.ChristoffelBound
import DifferentialGeometry.Analysis.Spectral.Tensor.TrivProj.ChartTwistIdentity
import DifferentialGeometry.Geometry.Connection.ChartTensorNabla.TensorRS.ChartTensorRSCovariantDerivativeAgreement
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.CovApplyAndSlotCorrectionBounds.SlotCorrectionChartKernel
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartFiberTrivialisationOpNorm.TensorRSChartFiberFromModelOpNorm
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartFiberTrivialisationOpNorm.TensorRSChartFiberToModelOpNorm
import DifferentialGeometry.Analysis.Integration.Measure.ChartDensity
import Mathlib.MeasureTheory.Integral.IntegrableOn


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Connection

section AtomMeasurability

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma pouTsupport_measurableSet_meas (α : M) :
    MeasurableSet (tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) :=
  (isClosed_tsupport _).measurableSet

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [CompactSpace M] in
private lemma scalarOnE_raw_eq_raw_on_pouTsupport_meas
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {b : M} (hb : b ∈ tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) :
    scalarOnE (I := I) α
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)
        (extChartAt I α b) =
      tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx b := by
  classical
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    pouTsupport_subset_baseSet (I := I) (M := M) α hb
  have hb_chart : b ∈ (chartAt H α).source := hb_base
  have hb_ext : b ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    exact hb_chart
  exact scalarOnE_extChartAt (I := I) α
    (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx) hb_ext

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [CompactSpace M] in
private lemma tensorChartComponentRaw_continuousOn_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)
      (tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) := by
  classical
  have h_on : ContinuousOn
      (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)
      ((chartAt H α).source) :=
    (tensorChartComponentRaw_contMDiffOn_chart_source
      (I := I) (M := M) g r s S α Idx Jdx).continuousOn
  refine h_on.mono ?_
  intro b hb
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    pouTsupport_subset_baseSet (I := I) (M := M) α hb
  exact hb_base

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [CompactSpace M] in
private lemma scalarOnE_raw_continuousOn_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (fun b : M => scalarOnE (I := I) α
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)
        (extChartAt I α b))
      (tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) := by
  classical
  have h_raw_on :=
    tensorChartComponentRaw_continuousOn_pouTsupport
      (I := I) (M := M) g r s α S Idx Jdx
  refine h_raw_on.congr ?_
  intro b hb
  exact scalarOnE_raw_eq_raw_on_pouTsupport_meas
    (I := I) (M := M) g r s α S Idx Jdx hb

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [CompactSpace M] in
private lemma abs_scalarOnE_raw_continuousOn_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (fun b : M => |scalarOnE (I := I) α
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)
        (extChartAt I α b)|)
      (tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) := by
  classical
  have h_inner := scalarOnE_raw_continuousOn_pouTsupport
    (I := I) (M := M) g r s α S Idx Jdx
  exact _root_.continuous_abs.comp_continuousOn h_inner

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma abs_scalarOnE_raw_aestronglyMeasurable_restrict_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    AEStronglyMeasurable
      (fun b : M => |scalarOnE (I := I) α
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)
        (extChartAt I α b)|)
      ((riemannianVolumeMeasure (I := I) (M := M) g).restrict
        (tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x))) := by
  classical
  exact ContinuousOn.aestronglyMeasurable_of_isCompact
    (abs_scalarOnE_raw_continuousOn_pouTsupport
      (I := I) (M := M) g r s α S Idx Jdx)
    (pouTsupport_isCompact (I := I) (M := M) α)
    (pouTsupport_measurableSet_meas (I := I) (M := M) α)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem aestronglyMeasurable_indicator_tsupp_abs_raw
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensorH1 g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    AEStronglyMeasurable
      (fun b : M =>
        (tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)).indicator
          (fun b' : M => |scalarOnE (I := I) α
            (tensorChartComponentRaw (I := I) (M := M)
              g r s S.toCcTensor α Idx Jdx)
            (extChartAt I α b')|) b)
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  set ρSet : Set M := tsupport (fun x : M =>
    ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) with hρSet_def
  have hρSet_meas : MeasurableSet ρSet :=
    pouTsupport_measurableSet_meas (I := I) (M := M) α
  rw [aestronglyMeasurable_indicator_iff hρSet_meas]
  exact abs_scalarOnE_raw_aestronglyMeasurable_restrict_pouTsupport
    (I := I) (M := M) g r s α S.toCcTensor Idx Jdx

section ChristoffelAtomMeasurability

variable (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
  (j : Fin (Module.finrank ℝ E))

private def trivInput
    (T : Π b' : M, TensorRSSpace r s I b') (b : M) (k : Fin r) :
    TensorRSModel r s ℝ E :=
  (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
    (chartTensorRSInputSlotCorrection (I := I) r s g α
      (fun b' => T b') (chartBasisVecFiber (I := I) α j) b k)

private def trivOutput
    (T : Π b' : M, TensorRSSpace r s I b') (b : M) (l : Fin s) :
    TensorRSModel r s ℝ E :=
  (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
    (chartTensorRSOutputSlotCorrection (I := I) r s g α
      (fun b' => T b') (chartBasisVecFiber (I := I) α j) b l)

private def christoffelAtomIntegrand
    (T : Π b' : M, TensorRSSpace r s I b') (b : M) : ℝ :=
  ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
    Real.sqrt
      ((∑ k : Fin r, ‖trivInput (I := I) g r s α j T b k‖ ^ 2) +
       (∑ l : Fin s, ‖trivOutput (I := I) g r s α j T b l‖ ^ 2))

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma triv_continuousLinearMapAt_eq_triv_snd
    {b : M} (hb : b ∈ (chartAt H α).source) (v : TensorRSSpace r s I b) :
    (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b v =
      (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α ⟨b, v⟩).2 := by
  classical
  have hbaseRS : b ∈ (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).baseSet := by
    change b ∈ (trivializationAt (Tensor0SModel r ℝ E)
        (fun y : M => Tensor0SSpace r I y) α).baseSet ∩
      (trivializationAt (Tensor0SModel s ℝ E)
        (fun y : M => Tensor0SSpace s I y) α).baseSet
    refine ⟨?_, ?_⟩
    all_goals
      change b ∈ (trivializationAt E (TangentSpace I) α).baseSet
      exact hb
  have hcoe := (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).coe_linearMapAt_of_mem
    (R := ℝ) hbaseRS
  change ((trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).linearMapAt ℝ b) v = _
  exact congrFun hcoe _

variable {g r s α j} in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma trivInput_continuousOn_chartSource (S : SmoothCcTensor g r s)
    (k : Fin r) :
    ContinuousOn (fun b : M => trivInput (I := I) g r s α j S.toSection b k)
      ((chartAt H α).source) := by
  classical
  have h_trivImage :=
    (chartTensorRSInputSlotCorrection_chartBasisVec_trivImage_contMDiffOn_chartSource
      (I := I) (M := M) g r s α
      (fun b' : M => S.toSection b') S.toSection.contMDiff j k).continuousOn
  refine h_trivImage.congr ?_
  intro b hb
  exact triv_continuousLinearMapAt_eq_triv_snd (I := I) (r := r) (s := s)
    (α := α) (b := b) hb
    (chartTensorRSInputSlotCorrection (I := I) r s g α
      (fun b' => S.toSection b') (chartBasisVecFiber (I := I) α j) b k)

variable {g r s α j} in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma trivOutput_continuousOn_chartSource (S : SmoothCcTensor g r s)
    (l : Fin s) :
    ContinuousOn (fun b : M => trivOutput (I := I) g r s α j S.toSection b l)
      ((chartAt H α).source) := by
  classical
  have h_trivImage :=
    (chartTensorRSOutputSlotCorrection_chartBasisVec_trivImage_contMDiffOn_chartSource
      (I := I) (M := M) g r s α
      (fun b' : M => S.toSection b') S.toSection.contMDiff j l).continuousOn
  refine h_trivImage.congr ?_
  intro b hb
  exact triv_continuousLinearMapAt_eq_triv_snd (I := I) (r := r) (s := s)
    (α := α) (b := b) hb
    (chartTensorRSOutputSlotCorrection (I := I) r s g α
      (fun b' => S.toSection b') (chartBasisVecFiber (I := I) α j) b l)

variable {g r s α j} in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
private lemma christoffelAtomIntegrand_continuousOn_chartSource
    (S : SmoothCcTensor g r s) :
    ContinuousOn (christoffelAtomIntegrand (I := I) g r s α j S.toSection)
      ((chartAt H α).source) := by
  classical
  have h_pou : ContinuousOn
      (fun b : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b)
      ((chartAt H α).source) :=
    ((chartAtlasPOU I M α).contMDiff.continuous).continuousOn
  have h_input : ContinuousOn
      (fun b : M => ∑ k : Fin r, ‖trivInput (I := I) g r s α j S.toSection b k‖ ^ 2)
      ((chartAt H α).source) :=
    continuousOn_finset_sum _ (fun k _ =>
      (trivInput_continuousOn_chartSource (I := I) S k).norm.pow 2)
  have h_output : ContinuousOn
      (fun b : M => ∑ l : Fin s, ‖trivOutput (I := I) g r s α j S.toSection b l‖ ^ 2)
      ((chartAt H α).source) :=
    continuousOn_finset_sum _ (fun l _ =>
      (trivOutput_continuousOn_chartSource (I := I) S l).norm.pow 2)
  have h_sumsq := h_input.add h_output
  have h_sqrt := Real.continuous_sqrt.comp_continuousOn h_sumsq
  exact h_pou.mul h_sqrt

variable {g r s α j} in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
private lemma christoffelAtomIntegrand_continuousOn_pouTsupport
    (S : SmoothCcTensor g r s) :
    ContinuousOn (christoffelAtomIntegrand (I := I) g r s α j S.toSection)
      (tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) := by
  classical
  refine (christoffelAtomIntegrand_continuousOn_chartSource (I := I) S).mono ?_
  intro b hb
  exact pouTsupport_subset_baseSet (I := I) (M := M) α hb

variable {g r s α j} in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma christoffelAtomIntegrand_zero_outside_pouTsupport
    (T : Π b' : M, TensorRSSpace r s I b') {b : M}
    (hb : b ∉ tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) :
    christoffelAtomIntegrand (I := I) g r s α j T b = 0 := by
  classical
  have hρ_zero : ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b = 0 := by
    by_contra hne
    exact hb (subset_tsupport _ hne)
  simp [christoffelAtomIntegrand, hρ_zero]

variable {g r s α j} in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma christoffelAtomIntegrand_eq_indicator
    (T : Π b' : M, TensorRSSpace r s I b') :
    christoffelAtomIntegrand (I := I) g r s α j T =
      (tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)).indicator
        (christoffelAtomIntegrand (I := I) g r s α j T) := by
  classical
  funext b
  by_cases hb : b ∈ tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)
  · rw [Set.indicator_of_mem hb]
  · rw [Set.indicator_of_notMem hb]
    exact christoffelAtomIntegrand_zero_outside_pouTsupport (I := I) T hb

variable {g r s α j} in
omit [NeZero (Module.finrank ℝ E)] in
private lemma christoffelAtomIntegrand_aestronglyMeasurable_restrict_pouTsupport
    (S : SmoothCcTensor g r s) :
    AEStronglyMeasurable
      (christoffelAtomIntegrand (I := I) g r s α j S.toSection)
      ((riemannianVolumeMeasure (I := I) (M := M) g).restrict
        (tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x))) := by
  classical
  exact ContinuousOn.aestronglyMeasurable_of_isCompact
    (christoffelAtomIntegrand_continuousOn_pouTsupport (I := I) S)
    (pouTsupport_isCompact (I := I) (M := M) α)
    (pouTsupport_measurableSet_meas (I := I) (M := M) α)

end ChristoffelAtomMeasurability

omit [NeZero (Module.finrank ℝ E)] in
theorem aestronglyMeasurable_pou_mul_sqrt_sum_christoffel_correction
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (j : Fin (Module.finrank ℝ E))
    (S : SmoothCcTensorH1 g r s) :
    AEStronglyMeasurable
      (fun b : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
          Real.sqrt
            ((∑ k : Fin r,
                ‖(trivializationAt (TensorRSModel r s ℝ E)
                    (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt
                      ℝ b
                  (chartTensorRSInputSlotCorrection (I := I) r s g α
                    (fun b' => S.toCcTensor.toSection b')
                    (chartBasisVecFiber (I := I) α j) b k)‖ ^ 2) +
              (∑ l : Fin s,
                ‖(trivializationAt (TensorRSModel r s ℝ E)
                    (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt
                      ℝ b
                  (chartTensorRSOutputSlotCorrection (I := I) r s g α
                    (fun b' => S.toCcTensor.toSection b')
                    (chartBasisVecFiber (I := I) α j) b l)‖ ^ 2)))
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  change AEStronglyMeasurable
    (christoffelAtomIntegrand (I := I) g r s α j S.toCcTensor.toSection)
    (riemannianVolumeMeasure (I := I) (M := M) g)
  rw [christoffelAtomIntegrand_eq_indicator (I := I)
    (T := fun b' : M => S.toCcTensor.toSection b')]
  rw [aestronglyMeasurable_indicator_iff
    (pouTsupport_measurableSet_meas (I := I) (M := M) α)]
  exact christoffelAtomIntegrand_aestronglyMeasurable_restrict_pouTsupport
    (I := I) S.toCcTensor

end AtomMeasurability

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
