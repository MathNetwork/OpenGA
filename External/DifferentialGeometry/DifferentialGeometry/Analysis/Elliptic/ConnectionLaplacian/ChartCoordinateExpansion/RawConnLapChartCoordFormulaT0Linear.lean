import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartCoordinateExpansion.ChartFrameTraceΓCorrectionT0Linear
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartCoordinateExpansion.LeibnizRemainderFirstDerivExpansion
import DifferentialGeometry.Analysis.Elliptic.TensorRegularity.SecondCovDerivExpansion.SecondCovDerivChartProjEuclidGlobal
import DifferentialGeometry.Analysis.Elliptic.TensorRegularity.ChartPullbackSmoothness.ChartInvGramMatrixPullback
import DifferentialGeometry.Analysis.Elliptic.TensorRegularity.ChartPullbackSmoothness.ChartFrameCoordMatrixPullback
import DifferentialGeometry.Analysis.Elliptic.TensorRegularity.DirichletForm.FinsetSumSwap


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold Set IsManifold ContinuousLinearMap Filter
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Tensor
open Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Sobolev.Chart hiding chartTargetEuclid

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private noncomputable def secondCovDeriv_GlobalCorr
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (k l : Fin (Module.finrank ℝ E))
    (I' : Fin r → Fin (Module.finrank ℝ E))
    (J' : Fin s → Fin (Module.finrank ℝ E))
    (m : Fin (Module.finrank ℝ E)) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
  Classical.choose
    (secondCovDeriv_chartα_proj_eq_iteratedFDeriv_T₀_eqOn
      (I := I) (M := M) g r s α Idx Jdx k l) I' J' m

private noncomputable def secondCovDeriv_GlobalCorr0
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (k l : Fin (Module.finrank ℝ E))
    (I' : Fin r → Fin (Module.finrank ℝ E))
    (J' : Fin s → Fin (Module.finrank ℝ E)) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
  Classical.choose
    (Classical.choose_spec
      (secondCovDeriv_chartα_proj_eq_iteratedFDeriv_T₀_eqOn
        (I := I) (M := M) g r s α Idx Jdx k l)) I' J'

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma secondCovDeriv_GlobalCorr_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (k l : Fin (Module.finrank ℝ E))
    (I' : Fin r → Fin (Module.finrank ℝ E))
    (J' : Fin s → Fin (Module.finrank ℝ E))
    (m : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (secondCovDeriv_GlobalCorr (I := I) (M := M) g r s α Idx Jdx k l I' J' m)
      (chartTargetEuclid (I := I) (M := M) α) :=
  (Classical.choose_spec
      (Classical.choose_spec
        (secondCovDeriv_chartα_proj_eq_iteratedFDeriv_T₀_eqOn
          (I := I) (M := M) g r s α Idx Jdx k l))).1 I' J' m

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma secondCovDeriv_GlobalCorr0_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (k l : Fin (Module.finrank ℝ E))
    (I' : Fin r → Fin (Module.finrank ℝ E))
    (J' : Fin s → Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (secondCovDeriv_GlobalCorr0 (I := I) (M := M) g r s α Idx Jdx k l I' J')
      (chartTargetEuclid (I := I) (M := M) α) :=
  (Classical.choose_spec
      (Classical.choose_spec
        (secondCovDeriv_chartα_proj_eq_iteratedFDeriv_T₀_eqOn
          (I := I) (M := M) g r s α Idx Jdx k l))).2.1 I' J'

omit [NeZero (Module.finrank ℝ E)] in
private lemma secondCovDeriv_GlobalCorr_pointwise
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (k l : Fin (Module.finrank ℝ E))
    (T₀ : SmoothCcTensor g r s)
    {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    tensorChartComponentProjection (E := E) r s Idx Jdx
        ((trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          ((TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g)).toFun
            (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g))
              (chartBasisVecFiber (I := I) α k) T₀.toSection) b
            (chartBasisVecFiber (I := I) α l b))) =
      euclidPartial (E := E) l
        (euclidPartial (E := E) k
          (chartPushedRaw I α
            (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)))
        ((toEuclidean (E := E)) ((extChartAt I α) b)) +
      (∑ I' : Fin r → Fin (Module.finrank ℝ E),
        ∑ J' : Fin s → Fin (Module.finrank ℝ E),
        ∑ m : Fin (Module.finrank ℝ E),
        secondCovDeriv_GlobalCorr (I := I) (M := M) g r s α Idx Jdx k l I' J' m
            ((toEuclidean (E := E)) ((extChartAt I α) b)) *
          euclidPartial (E := E) m
            (chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α I' J'))
            ((toEuclidean (E := E)) ((extChartAt I α) b))) +
      (∑ I' : Fin r → Fin (Module.finrank ℝ E),
        ∑ J' : Fin s → Fin (Module.finrank ℝ E),
        secondCovDeriv_GlobalCorr0 (I := I) (M := M) g r s α Idx Jdx k l I' J'
            ((toEuclidean (E := E)) ((extChartAt I α) b)) *
          chartPushedRaw I α
            (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α I' J')
            ((toEuclidean (E := E)) ((extChartAt I α) b))) :=
  (Classical.choose_spec
      (Classical.choose_spec
        (secondCovDeriv_chartα_proj_eq_iteratedFDeriv_T₀_eqOn
          (I := I) (M := M) g r s α Idx Jdx k l))).2.2 T₀ hb

private noncomputable def chartFrameTraceΓ_Coeff_1
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (I' : Fin r → Fin (Module.finrank ℝ E))
    (J' : Fin s → Fin (Module.finrank ℝ E))
    (m : Fin (Module.finrank ℝ E)) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
  Classical.choose
    (chartFrameTraceΓCorrection_eq_T₀_linear
      (I := I) (M := M) g r s α Idx Jdx) I' J' m

private noncomputable def chartFrameTraceΓ_Coeff_0
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (I' : Fin r → Fin (Module.finrank ℝ E))
    (J' : Fin s → Fin (Module.finrank ℝ E)) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
  Classical.choose
    (Classical.choose_spec
      (chartFrameTraceΓCorrection_eq_T₀_linear
        (I := I) (M := M) g r s α Idx Jdx)) I' J'

private lemma chartFrameTraceΓ_Coeff_1_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (I' : Fin r → Fin (Module.finrank ℝ E))
    (J' : Fin s → Fin (Module.finrank ℝ E))
    (m : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (chartFrameTraceΓ_Coeff_1 (I := I) (M := M) g r s α Idx Jdx I' J' m)
      (chartTargetEuclid (I := I) (M := M) α) :=
  (Classical.choose_spec
      (Classical.choose_spec
        (chartFrameTraceΓCorrection_eq_T₀_linear
          (I := I) (M := M) g r s α Idx Jdx))).1 I' J' m

private lemma chartFrameTraceΓ_Coeff_0_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (I' : Fin r → Fin (Module.finrank ℝ E))
    (J' : Fin s → Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (chartFrameTraceΓ_Coeff_0 (I := I) (M := M) g r s α Idx Jdx I' J')
      (chartTargetEuclid (I := I) (M := M) α) :=
  (Classical.choose_spec
      (Classical.choose_spec
        (chartFrameTraceΓCorrection_eq_T₀_linear
          (I := I) (M := M) g r s α Idx Jdx))).2.1 I' J'

private lemma chartFrameTraceΓCorrection_pointwise
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (T₀ : SmoothCcTensor g r s)
    {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    chartFrameTraceΓCorrection (I := I) (M := M) g r s α T₀ Idx Jdx b =
      (∑ I' : Fin r → Fin (Module.finrank ℝ E),
        ∑ J' : Fin s → Fin (Module.finrank ℝ E),
        ∑ m : Fin (Module.finrank ℝ E),
        chartFrameTraceΓ_Coeff_1 (I := I) (M := M) g r s α Idx Jdx I' J' m
            ((toEuclidean (E := E)) ((extChartAt I α) b)) *
          euclidPartial (E := E) m
            (chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α I' J'))
            ((toEuclidean (E := E)) ((extChartAt I α) b))) +
      (∑ I' : Fin r → Fin (Module.finrank ℝ E),
        ∑ J' : Fin s → Fin (Module.finrank ℝ E),
        chartFrameTraceΓ_Coeff_0 (I := I) (M := M) g r s α Idx Jdx I' J'
            ((toEuclidean (E := E)) ((extChartAt I α) b)) *
          chartPushedRaw I α
            (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α I' J')
            ((toEuclidean (E := E)) ((extChartAt I α) b))) :=
  (Classical.choose_spec
      (Classical.choose_spec
        (chartFrameTraceΓCorrection_eq_T₀_linear
          (I := I) (M := M) g r s α Idx Jdx))).2.2 T₀ hb

private noncomputable def invGramPull
    (g : SmoothRiemannianMetric I M) (α : M)
    (k l : Fin (Module.finrank ℝ E)) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
  fun y => chartInvGramMatrix (I := I) g α
    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) k l

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private lemma invGramPull_contDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (k l : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (invGramPull (I := I) (M := M) g α k l)
      (chartTargetEuclid (I := I) (M := M) α) :=
  chartInvGramMatrix_pullback_contDiffOn_chartTarget
    (I := I) (M := M) g α k l

private noncomputable def chartFrameCoordPull
    (g : SmoothRiemannianMetric I M) (α : M)
    (i k : Fin (Module.finrank ℝ E)) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
  fun y => chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i k
    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))

omit [BoundarylessManifold I M] in
private lemma chartFrameCoordPull_contDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (i k : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (chartFrameCoordPull (I := I) (M := M) g α i k)
      (chartTargetEuclid (I := I) (M := M) α) :=
  chartFrameNormGlobalSmoothCoordMatrix_pullback_contDiffOn_chartTarget
    (I := I) (M := M) g α i k

private noncomputable def chartFrameCoordDirDerivPull
    (g : SmoothRiemannianMetric I M) (α : M)
    (i k l : Fin (Module.finrank ℝ E)) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
  fun y => extDerivFun (I := I)
    (chartFrameNormGlobalSmoothCoordMatrix (I := I) g α i k)
    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
    (chartBasisVecFiber (I := I) α l
      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))

omit [BoundarylessManifold I M] in
private lemma chartFrameCoordDirDerivPull_contDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (i k l : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (chartFrameCoordDirDerivPull (I := I) (M := M) g α i k l)
      (chartTargetEuclid (I := I) (M := M) α) :=
  chartFrameNormGlobalSmoothCoordMatrix_dirDeriv_pullback_contDiffOn_chartTarget
    (I := I) (M := M) g α i k l

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma invGramPull_at_b_eq
    (g : SmoothRiemannianMetric I M) (α : M)
    (k l : Fin (Module.finrank ℝ E))
    {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    invGramPull (I := I) (M := M) g α k l
        ((toEuclidean (E := E)) ((extChartAt I α) b)) =
      chartInvGramMatrix (I := I) g α b k l := by
  have hb_src : b ∈ (extChartAt I α).source :=
    chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hb
  have hsymm : (toEuclidean (E := E)).symm
      ((toEuclidean (E := E)) ((extChartAt I α) b)) =
      (extChartAt I α) b :=
    (toEuclidean (E := E)).symm_apply_apply _
  have hleft_inv : (extChartAt I α).symm ((extChartAt I α) b) = b :=
    (extChartAt I α).left_inv hb_src
  unfold invGramPull
  rw [hsymm, hleft_inv]

omit [I.Boundaryless] [BoundarylessManifold I M] in
private lemma chartFrameCoordPull_at_b_eq
    (g : SmoothRiemannianMetric I M) (α : M)
    (i k : Fin (Module.finrank ℝ E))
    {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    chartFrameCoordPull (I := I) (M := M) g α i k
        ((toEuclidean (E := E)) ((extChartAt I α) b)) =
      chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i k b := by
  have hb_src : b ∈ (extChartAt I α).source :=
    chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hb
  have hsymm : (toEuclidean (E := E)).symm
      ((toEuclidean (E := E)) ((extChartAt I α) b)) =
      (extChartAt I α) b :=
    (toEuclidean (E := E)).symm_apply_apply _
  have hleft_inv : (extChartAt I α).symm ((extChartAt I α) b) = b :=
    (extChartAt I α).left_inv hb_src
  unfold chartFrameCoordPull
  rw [hsymm, hleft_inv]

omit [I.Boundaryless] [BoundarylessManifold I M] in
private lemma chartFrameCoordDirDerivPull_at_b_eq
    (g : SmoothRiemannianMetric I M) (α : M)
    (i k l : Fin (Module.finrank ℝ E))
    {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    chartFrameCoordDirDerivPull (I := I) (M := M) g α i k l
        ((toEuclidean (E := E)) ((extChartAt I α) b)) =
      extDerivFun (I := I)
        (chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i k) b
        (chartBasisVecFiber (I := I) α l b) := by
  have hb_src : b ∈ (extChartAt I α).source :=
    chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hb
  have hsymm : (toEuclidean (E := E)).symm
      ((toEuclidean (E := E)) ((extChartAt I α) b)) =
      (extChartAt I α) b :=
    (toEuclidean (E := E)).symm_apply_apply _
  have hleft_inv : (extChartAt I α).symm ((extChartAt I α) b) = b :=
    (extChartAt I α).left_inv hb_src
  unfold chartFrameCoordDirDerivPull
  rw [hsymm, hleft_inv]

private noncomputable def C_2_principal
    (g : SmoothRiemannianMetric I M) (α : M)
    (k l : Fin (Module.finrank ℝ E)) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
  invGramPull (I := I) (M := M) g α k l

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma C_2_principal_contDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (k l : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (C_2_principal (I := I) (M := M) g α k l)
      (chartTargetEuclid (I := I) (M := M) α) :=
  invGramPull_contDiffOn (I := I) (M := M) g α k l

private noncomputable def C_1_firstDeriv
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (I' : Fin r → Fin (Module.finrank ℝ E))
    (J' : Fin s → Fin (Module.finrank ℝ E))
    (m : Fin (Module.finrank ℝ E)) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
  fun y =>
    (∑ k : Fin (Module.finrank ℝ E),
      ∑ l : Fin (Module.finrank ℝ E),
        invGramPull (I := I) (M := M) g α k l y *
          secondCovDeriv_GlobalCorr (I := I) (M := M) g r s α Idx Jdx k l I' J' m y) +
    (if I' = Idx ∧ J' = Jdx then
       ∑ i : Fin (Module.finrank ℝ E),
         ∑ l : Fin (Module.finrank ℝ E),
           chartFrameCoordPull (I := I) (M := M) g α i l y *
             chartFrameCoordDirDerivPull (I := I) (M := M) g α i m l y
     else 0) -
    chartFrameTraceΓ_Coeff_1 (I := I) (M := M) g r s α Idx Jdx I' J' m y

private lemma C_1_firstDeriv_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (I' : Fin r → Fin (Module.finrank ℝ E))
    (J' : Fin s → Fin (Module.finrank ℝ E))
    (m : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (C_1_firstDeriv (I := I) (M := M) g r s α Idx Jdx I' J' m)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  unfold C_1_firstDeriv
  refine ContDiffOn.sub ?_ ?_
  · refine ContDiffOn.add ?_ ?_
    · refine ContDiffOn.sum (fun k _ => ?_)
      refine ContDiffOn.sum (fun l _ => ?_)
      exact (invGramPull_contDiffOn (I := I) (M := M) g α k l).mul
        (secondCovDeriv_GlobalCorr_contDiffOn
          (I := I) (M := M) g r s α Idx Jdx k l I' J' m)
    · by_cases h : I' = Idx ∧ J' = Jdx
      · simp only [h]
        refine ContDiffOn.sum (fun i _ => ?_)
        refine ContDiffOn.sum (fun l _ => ?_)
        exact (chartFrameCoordPull_contDiffOn (I := I) (M := M) g α i l).mul
          (chartFrameCoordDirDerivPull_contDiffOn (I := I) (M := M) g α i m l)
      · simp only [h, if_false]
        exact contDiffOn_const
  · exact chartFrameTraceΓ_Coeff_1_contDiffOn
      (I := I) (M := M) g r s α Idx Jdx I' J' m

private noncomputable def C_0_zeroth
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (I' : Fin r → Fin (Module.finrank ℝ E))
    (J' : Fin s → Fin (Module.finrank ℝ E)) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
  fun y =>
    (∑ k : Fin (Module.finrank ℝ E),
      ∑ l : Fin (Module.finrank ℝ E),
        invGramPull (I := I) (M := M) g α k l y *
          secondCovDeriv_GlobalCorr0 (I := I) (M := M) g r s α Idx Jdx k l I' J' y) +
    (∑ i : Fin (Module.finrank ℝ E),
      ∑ l : Fin (Module.finrank ℝ E),
        ∑ k : Fin (Module.finrank ℝ E),
          chartFrameCoordPull (I := I) (M := M) g α i l y *
            chartFrameCoordDirDerivPull (I := I) (M := M) g α i k l y *
            covDerivLowerOrderCoeff (I := I) (M := M) g r s α k Idx I' Jdx J' y) -
    chartFrameTraceΓ_Coeff_0 (I := I) (M := M) g r s α Idx Jdx I' J' y

private lemma C_0_zeroth_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (I' : Fin r → Fin (Module.finrank ℝ E))
    (J' : Fin s → Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (C_0_zeroth (I := I) (M := M) g r s α Idx Jdx I' J')
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  unfold C_0_zeroth
  refine ContDiffOn.sub ?_ ?_
  · refine ContDiffOn.add ?_ ?_
    · refine ContDiffOn.sum (fun k _ => ?_)
      refine ContDiffOn.sum (fun l _ => ?_)
      exact (invGramPull_contDiffOn (I := I) (M := M) g α k l).mul
        (secondCovDeriv_GlobalCorr0_contDiffOn
          (I := I) (M := M) g r s α Idx Jdx k l I' J')
    · refine ContDiffOn.sum (fun i _ => ?_)
      refine ContDiffOn.sum (fun l _ => ?_)
      refine ContDiffOn.sum (fun k _ => ?_)
      refine ((chartFrameCoordPull_contDiffOn (I := I) (M := M) g α i l).mul
        (chartFrameCoordDirDerivPull_contDiffOn
          (I := I) (M := M) g α i k l)).mul ?_
      exact covDerivLowerOrderCoeff_contDiffOn
        (I := I) (M := M) g r s α k Idx I' Jdx J'
  · exact chartFrameTraceΓ_Coeff_0_contDiffOn
      (I := I) (M := M) g r s α Idx Jdx I' J'

private noncomputable def rawTensorConnLapLinearFormulaRHS
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (T₀ : SmoothCcTensor g r s) (b : M) : ℝ :=
  (∑ k, ∑ l,
    C_2_principal (I := I) (M := M) g α k l
        ((toEuclidean (E := E)) ((extChartAt I α) b)) *
      euclidPartial (E := E) l
        (euclidPartial (E := E) k
          (chartPushedRaw I α
            (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)))
        ((toEuclidean (E := E)) ((extChartAt I α) b))) +
  (∑ I' : Fin r → Fin (Module.finrank ℝ E),
    ∑ J' : Fin s → Fin (Module.finrank ℝ E),
    ∑ m,
    C_1_firstDeriv (I := I) (M := M) g r s α Idx Jdx I' J' m
        ((toEuclidean (E := E)) ((extChartAt I α) b)) *
      euclidPartial (E := E) m
        (chartPushedRaw I α
          (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α I' J'))
        ((toEuclidean (E := E)) ((extChartAt I α) b))) +
  (∑ I' : Fin r → Fin (Module.finrank ℝ E),
    ∑ J' : Fin s → Fin (Module.finrank ℝ E),
    C_0_zeroth (I := I) (M := M) g r s α Idx Jdx I' J'
        ((toEuclidean (E := E)) ((extChartAt I α) b)) *
      chartPushedRaw I α
        (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α I' J')
        ((toEuclidean (E := E)) ((extChartAt I α) b)))

private theorem rawTensorConnLap_chartα_raw_eq_T₀_linear_formula_pointwise
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (T₀ : SmoothCcTensor g r s) {b : M}
    (hb : b ∈ tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
      chartLeviCivitaGoodSet (I := I) α) :
    tensorChartComponentRaw (I := I) (M := M) g r s
        (rawTensorConnLapSmooth (I := I) g r s T₀) α Idx Jdx b =
      rawTensorConnLapLinearFormulaRHS (I := I) (M := M) g r s α Idx Jdx T₀ b := by
  classical
  unfold rawTensorConnLapLinearFormulaRHS
  set y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    (toEuclidean (E := E)) ((extChartAt I α) b) with hy_def
  have hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α := hb.2
  set P : (Fin r → Fin (Module.finrank ℝ E)) →
          (Fin s → Fin (Module.finrank ℝ E)) →
          Fin (Module.finrank ℝ E) → ℝ :=
    fun I' J' m =>
      euclidPartial (E := E) m
        (chartPushedRaw I α
          (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α I' J')) y
    with hP_def
  set R : (Fin r → Fin (Module.finrank ℝ E)) →
          (Fin s → Fin (Module.finrank ℝ E)) → ℝ :=
    fun I' J' =>
      chartPushedRaw I α
        (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α I' J') y
    with hR_def
  set PP : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun k l =>
      euclidPartial (E := E) l
        (euclidPartial (E := E) k
          (chartPushedRaw I α
            (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx))) y
    with hPP_def
  set IG : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun k l => invGramPull (I := I) (M := M) g α k l y
    with hIG_def
  set GC : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
           (Fin r → Fin (Module.finrank ℝ E)) →
           (Fin s → Fin (Module.finrank ℝ E)) →
           Fin (Module.finrank ℝ E) → ℝ :=
    fun k l I' J' m =>
      secondCovDeriv_GlobalCorr (I := I) (M := M) g r s α Idx Jdx k l I' J' m y
    with hGC_def
  set GC0 : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
            (Fin r → Fin (Module.finrank ℝ E)) →
            (Fin s → Fin (Module.finrank ℝ E)) → ℝ :=
    fun k l I' J' =>
      secondCovDeriv_GlobalCorr0 (I := I) (M := M) g r s α Idx Jdx k l I' J' y
    with hGC0_def
  set CF : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun i l => chartFrameCoordPull (I := I) (M := M) g α i l y
    with hCF_def
  set DCF : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
            Fin (Module.finrank ℝ E) → ℝ :=
    fun i k l => chartFrameCoordDirDerivPull (I := I) (M := M) g α i k l y
    with hDCF_def
  set LC : Fin (Module.finrank ℝ E) →
           (Fin r → Fin (Module.finrank ℝ E)) →
           (Fin s → Fin (Module.finrank ℝ E)) → ℝ :=
    fun k I' J' =>
      covDerivLowerOrderCoeff (I := I) (M := M) g r s α k Idx I' Jdx J' y
    with hLC_def
  set Γ1 : (Fin r → Fin (Module.finrank ℝ E)) →
           (Fin s → Fin (Module.finrank ℝ E)) →
           Fin (Module.finrank ℝ E) → ℝ :=
    fun I' J' m =>
      chartFrameTraceΓ_Coeff_1 (I := I) (M := M) g r s α Idx Jdx I' J' m y
    with hΓ1_def
  set Γ0 : (Fin r → Fin (Module.finrank ℝ E)) →
           (Fin s → Fin (Module.finrank ℝ E)) → ℝ :=
    fun I' J' =>
      chartFrameTraceΓ_Coeff_0 (I := I) (M := M) g r s α Idx Jdx I' J' y
    with hΓ0_def
  rw [chartPushed_rawConnLap_chart_α_proj_eq_chartInvGram_secondCovDeriv_plus_corrections
    (I := I) (M := M) g r s α T₀ Idx Jdx (b := b) hb]
  rw [chartFrameTraceΓCorrection_pointwise
    (I := I) (M := M) g r s α Idx Jdx T₀ hb_good]
  have hPrincipal_unfold :
      chartInvGramPrincipalSum (I := I) (M := M) g r s α T₀ Idx Jdx b =
        ∑ k, ∑ l,
          IG k l * (PP k l + (∑ I', ∑ J', ∑ m, GC k l I' J' m * P I' J' m)
                          + (∑ I', ∑ J', GC0 k l I' J' * R I' J')) := by
    unfold chartInvGramPrincipalSum
    refine Finset.sum_congr rfl (fun k _ => ?_)
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [secondCovDeriv_GlobalCorr_pointwise
      (I := I) (M := M) g r s α Idx Jdx k l T₀ hb_good]
    rw [← invGramPull_at_b_eq (I := I) (M := M) g α k l hb_good]
  rw [hPrincipal_unfold]
  rw [chartLeibnizRemainder_eq_T₀_linear
    (I := I) (M := M) g r s α T₀ Idx Jdx hb]
  have hLeibnizUnfold :
      (∑ i, ∑ l, ∑ k,
          chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i l b *
            extDerivFun (I := I)
                (fun z : M =>
                  chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i k z) b
                (chartBasisVecFiber (I := I) α l b) *
            (euclidPartial (E := E) k
                (chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)) y +
              ∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
                      (Fin s → Fin (Module.finrank ℝ E)),
                covDerivLowerOrderCoeff (I := I) (M := M) g r s α k Idx p.1 Jdx p.2 y *
                  chartPushedRaw I α
                    (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α p.1 p.2) y)) =
      ∑ i, ∑ l, ∑ k,
        CF i l * DCF i k l *
          (euclidPartial (E := E) k
              (chartPushedRaw I α
                (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)) y +
            ∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
                    (Fin s → Fin (Module.finrank ℝ E)),
              covDerivLowerOrderCoeff (I := I) (M := M) g r s α k Idx p.1 Jdx p.2 y *
                chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α p.1 p.2) y) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun l _ => ?_)
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [show chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i l b =
        CF i l from
      (chartFrameCoordPull_at_b_eq (I := I) (M := M) g α i l hb_good).symm]
    rw [show extDerivFun (I := I)
          (fun z : M =>
            chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i k z) b
          (chartBasisVecFiber (I := I) α l b) =
        DCF i k l from
      (chartFrameCoordDirDerivPull_at_b_eq (I := I) (M := M) g α i k l hb_good).symm]
  rw [hLeibnizUnfold]
  have hPair : ∀ (k : Fin (Module.finrank ℝ E)),
      (∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
              (Fin s → Fin (Module.finrank ℝ E)),
        covDerivLowerOrderCoeff (I := I) (M := M) g r s α k Idx p.1 Jdx p.2 y *
          chartPushedRaw I α
            (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α p.1 p.2) y) =
      ∑ I' : Fin r → Fin (Module.finrank ℝ E),
        ∑ J' : Fin s → Fin (Module.finrank ℝ E),
          LC k I' J' * R I' J' := by
    intro k
    rw [← Finset.sum_product']
    rfl
  have hLeibniz_pair' :
      (∑ i, ∑ l, ∑ k,
          CF i l * DCF i k l *
            (euclidPartial (E := E) k
                (chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)) y +
              ∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
                      (Fin s → Fin (Module.finrank ℝ E)),
                covDerivLowerOrderCoeff (I := I) (M := M) g r s α k Idx p.1 Jdx p.2 y *
                  chartPushedRaw I α
                    (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α p.1 p.2) y)) =
      ∑ i, ∑ l, ∑ k,
        CF i l * DCF i k l *
          (P Idx Jdx k +
            ∑ I' : Fin r → Fin (Module.finrank ℝ E),
              ∑ J' : Fin s → Fin (Module.finrank ℝ E),
                LC k I' J' * R I' J') := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun l _ => ?_)
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hPair k]
  rw [hLeibniz_pair']
  have hC2_RHS :
      (∑ k, ∑ l,
          C_2_principal (I := I) (M := M) g α k l y * PP k l) =
        ∑ k, ∑ l, IG k l * PP k l := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rfl
  have hC1_RHS :
      (∑ I' : Fin r → Fin (Module.finrank ℝ E),
        ∑ J' : Fin s → Fin (Module.finrank ℝ E),
        ∑ m,
          C_1_firstDeriv (I := I) (M := M) g r s α Idx Jdx I' J' m y *
            P I' J' m) =
      (∑ I' : Fin r → Fin (Module.finrank ℝ E),
        ∑ J' : Fin s → Fin (Module.finrank ℝ E),
        ∑ m,
          (∑ k, ∑ l, IG k l * GC k l I' J' m) * P I' J' m) +
      (∑ I' : Fin r → Fin (Module.finrank ℝ E),
        ∑ J' : Fin s → Fin (Module.finrank ℝ E),
        ∑ m,
          (if I' = Idx ∧ J' = Jdx then
            ∑ i, ∑ l, CF i l * DCF i m l
           else 0) * P I' J' m) -
      (∑ I' : Fin r → Fin (Module.finrank ℝ E),
        ∑ J' : Fin s → Fin (Module.finrank ℝ E),
        ∑ m, Γ1 I' J' m * P I' J' m) := by
    have hStep1 :
        (∑ I' : Fin r → Fin (Module.finrank ℝ E),
          ∑ J' : Fin s → Fin (Module.finrank ℝ E),
          ∑ m,
            C_1_firstDeriv (I := I) (M := M) g r s α Idx Jdx I' J' m y *
              P I' J' m) =
        ∑ I' : Fin r → Fin (Module.finrank ℝ E),
          ∑ J' : Fin s → Fin (Module.finrank ℝ E),
          ∑ m,
            ((∑ k, ∑ l, IG k l * GC k l I' J' m) * P I' J' m +
            (if I' = Idx ∧ J' = Jdx then
              ∑ i, ∑ l, CF i l * DCF i m l
             else 0) * P I' J' m -
            Γ1 I' J' m * P I' J' m) := by
      refine Finset.sum_congr rfl (fun I' _ => ?_)
      refine Finset.sum_congr rfl (fun J' _ => ?_)
      refine Finset.sum_congr rfl (fun m _ => ?_)
      unfold C_1_firstDeriv
      ring
    rw [hStep1]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hC0_RHS :
      (∑ I' : Fin r → Fin (Module.finrank ℝ E),
        ∑ J' : Fin s → Fin (Module.finrank ℝ E),
          C_0_zeroth (I := I) (M := M) g r s α Idx Jdx I' J' y * R I' J') =
      (∑ I' : Fin r → Fin (Module.finrank ℝ E),
        ∑ J' : Fin s → Fin (Module.finrank ℝ E),
          (∑ k, ∑ l, IG k l * GC0 k l I' J') * R I' J') +
      (∑ I' : Fin r → Fin (Module.finrank ℝ E),
        ∑ J' : Fin s → Fin (Module.finrank ℝ E),
          (∑ i, ∑ l, ∑ k, CF i l * DCF i k l * LC k I' J') * R I' J') -
      (∑ I' : Fin r → Fin (Module.finrank ℝ E),
        ∑ J' : Fin s → Fin (Module.finrank ℝ E), Γ0 I' J' * R I' J') := by
    have hStep1 :
        (∑ I' : Fin r → Fin (Module.finrank ℝ E),
          ∑ J' : Fin s → Fin (Module.finrank ℝ E),
            C_0_zeroth (I := I) (M := M) g r s α Idx Jdx I' J' y * R I' J') =
        ∑ I' : Fin r → Fin (Module.finrank ℝ E),
          ∑ J' : Fin s → Fin (Module.finrank ℝ E),
            ((∑ k, ∑ l, IG k l * GC0 k l I' J') * R I' J' +
            (∑ i, ∑ l, ∑ k, CF i l * DCF i k l * LC k I' J') * R I' J' -
            Γ0 I' J' * R I' J') := by
      refine Finset.sum_congr rfl (fun I' _ => ?_)
      refine Finset.sum_congr rfl (fun J' _ => ?_)
      unfold C_0_zeroth
      ring
    rw [hStep1]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hC2_RHS, hC1_RHS, hC0_RHS]
  have hSwap_GC :
      (∑ k, ∑ l,
          IG k l *
            ∑ I' : Fin r → Fin (Module.finrank ℝ E),
              ∑ J' : Fin s → Fin (Module.finrank ℝ E),
              ∑ m, GC k l I' J' m * P I' J' m) =
        ∑ I' : Fin r → Fin (Module.finrank ℝ E),
          ∑ J' : Fin s → Fin (Module.finrank ℝ E),
          ∑ m, (∑ k, ∑ l, IG k l * GC k l I' J' m) * P I' J' m := by
    have hDist :
        (∑ k, ∑ l,
            IG k l *
              ∑ I' : Fin r → Fin (Module.finrank ℝ E),
                ∑ J' : Fin s → Fin (Module.finrank ℝ E),
                ∑ m, GC k l I' J' m * P I' J' m) =
        ∑ k, ∑ l, ∑ I' : Fin r → Fin (Module.finrank ℝ E),
          ∑ J' : Fin s → Fin (Module.finrank ℝ E), ∑ m,
            IG k l * (GC k l I' J' m * P I' J' m) := by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun I' _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun J' _ => ?_)
      rw [Finset.mul_sum]
    rw [hDist]
    rw [show
        (∑ k, ∑ l, ∑ I' : Fin r → Fin (Module.finrank ℝ E),
          ∑ J' : Fin s → Fin (Module.finrank ℝ E), ∑ m,
            IG k l * (GC k l I' J' m * P I' J' m)) =
        ∑ k, ∑ l, IG k l *
          ∑ I' : Fin r → Fin (Module.finrank ℝ E),
            ∑ J' : Fin s → Fin (Module.finrank ℝ E),
              ∑ m, GC k l I' J' m * P I' J' m from by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun I' _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun J' _ => ?_)
      rw [Finset.mul_sum]]
    have h1 :
        (∑ k, ∑ l, IG k l *
            ∑ I' : Fin r → Fin (Module.finrank ℝ E),
              ∑ J' : Fin s → Fin (Module.finrank ℝ E),
                ∑ m, GC k l I' J' m * P I' J' m) =
        ∑ k, ∑ l, ∑ I' : Fin r → Fin (Module.finrank ℝ E),
          ∑ J' : Fin s → Fin (Module.finrank ℝ E),
            ∑ m, IG k l * (GC k l I' J' m * P I' J' m) := by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun I' _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun J' _ => ?_)
      rw [Finset.mul_sum]
    rw [h1]
    rw [show
        (∑ k, ∑ l, ∑ I' : Fin r → Fin (Module.finrank ℝ E),
          ∑ J' : Fin s → Fin (Module.finrank ℝ E),
            ∑ m, IG k l * (GC k l I' J' m * P I' J' m)) =
        ∑ k, ∑ I' : Fin r → Fin (Module.finrank ℝ E),
          ∑ l, ∑ J' : Fin s → Fin (Module.finrank ℝ E),
            ∑ m, IG k l * (GC k l I' J' m * P I' J' m) from by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [Finset.sum_comm]]
    rw [Finset.sum_comm]
    rw [show
        (∑ I' : Fin r → Fin (Module.finrank ℝ E),
          ∑ k, ∑ l, ∑ J' : Fin s → Fin (Module.finrank ℝ E),
            ∑ m, IG k l * (GC k l I' J' m * P I' J' m)) =
        ∑ I' : Fin r → Fin (Module.finrank ℝ E),
          ∑ k, ∑ J' : Fin s → Fin (Module.finrank ℝ E),
            ∑ l, ∑ m, IG k l * (GC k l I' J' m * P I' J' m) from by
      refine Finset.sum_congr rfl (fun I' _ => ?_)
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [Finset.sum_comm]]
    rw [show
        (∑ I' : Fin r → Fin (Module.finrank ℝ E),
          ∑ k, ∑ J' : Fin s → Fin (Module.finrank ℝ E),
            ∑ l, ∑ m, IG k l * (GC k l I' J' m * P I' J' m)) =
        ∑ I' : Fin r → Fin (Module.finrank ℝ E),
          ∑ J' : Fin s → Fin (Module.finrank ℝ E),
            ∑ k, ∑ l, ∑ m, IG k l * (GC k l I' J' m * P I' J' m) from by
      refine Finset.sum_congr rfl (fun I' _ => ?_)
      rw [Finset.sum_comm]]
    refine Finset.sum_congr rfl (fun I' _ => ?_)
    refine Finset.sum_congr rfl (fun J' _ => ?_)
    have ha :
        (∑ k, ∑ l, ∑ m, IG k l * (GC k l I' J' m * P I' J' m)) =
        ∑ k, ∑ m, ∑ l, IG k l * (GC k l I' J' m * P I' J' m) := by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [Finset.sum_comm]
    rw [ha]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    ring
  have hSwap_GC0 :
      (∑ k, ∑ l,
          IG k l *
            ∑ I' : Fin r → Fin (Module.finrank ℝ E),
              ∑ J' : Fin s → Fin (Module.finrank ℝ E),
                GC0 k l I' J' * R I' J') =
        ∑ I' : Fin r → Fin (Module.finrank ℝ E),
          ∑ J' : Fin s → Fin (Module.finrank ℝ E),
            (∑ k, ∑ l, IG k l * GC0 k l I' J') * R I' J' := by
    have hDist :
        (∑ k, ∑ l,
            IG k l *
              ∑ I' : Fin r → Fin (Module.finrank ℝ E),
                ∑ J' : Fin s → Fin (Module.finrank ℝ E),
                  GC0 k l I' J' * R I' J') =
        ∑ k, ∑ l, ∑ I' : Fin r → Fin (Module.finrank ℝ E),
          ∑ J' : Fin s → Fin (Module.finrank ℝ E),
            IG k l * (GC0 k l I' J' * R I' J') := by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun I' _ => ?_)
      rw [Finset.mul_sum]
    rw [hDist]
    rw [show
        (∑ k, ∑ l, ∑ I' : Fin r → Fin (Module.finrank ℝ E),
          ∑ J' : Fin s → Fin (Module.finrank ℝ E),
            IG k l * (GC0 k l I' J' * R I' J')) =
        ∑ k, ∑ I' : Fin r → Fin (Module.finrank ℝ E),
          ∑ l, ∑ J' : Fin s → Fin (Module.finrank ℝ E),
            IG k l * (GC0 k l I' J' * R I' J') from by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [Finset.sum_comm]]
    rw [Finset.sum_comm]
    rw [show
        (∑ I' : Fin r → Fin (Module.finrank ℝ E),
          ∑ k, ∑ l, ∑ J' : Fin s → Fin (Module.finrank ℝ E),
            IG k l * (GC0 k l I' J' * R I' J')) =
        ∑ I' : Fin r → Fin (Module.finrank ℝ E),
          ∑ k, ∑ J' : Fin s → Fin (Module.finrank ℝ E),
            ∑ l, IG k l * (GC0 k l I' J' * R I' J') from by
      refine Finset.sum_congr rfl (fun I' _ => ?_)
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [Finset.sum_comm]]
    rw [show
        (∑ I' : Fin r → Fin (Module.finrank ℝ E),
          ∑ k, ∑ J' : Fin s → Fin (Module.finrank ℝ E),
            ∑ l, IG k l * (GC0 k l I' J' * R I' J')) =
        ∑ I' : Fin r → Fin (Module.finrank ℝ E),
          ∑ J' : Fin s → Fin (Module.finrank ℝ E),
            ∑ k, ∑ l, IG k l * (GC0 k l I' J' * R I' J') from by
      refine Finset.sum_congr rfl (fun I' _ => ?_)
      rw [Finset.sum_comm]]
    refine Finset.sum_congr rfl (fun I' _ => ?_)
    refine Finset.sum_congr rfl (fun J' _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    ring
  have hLeib_split :
      (∑ i, ∑ l, ∑ k,
          CF i l * DCF i k l *
            (P Idx Jdx k +
              ∑ I' : Fin r → Fin (Module.finrank ℝ E),
                ∑ J' : Fin s → Fin (Module.finrank ℝ E),
                  LC k I' J' * R I' J')) =
      (∑ i, ∑ l, ∑ k, CF i l * DCF i k l * P Idx Jdx k) +
      (∑ i, ∑ l, ∑ k, CF i l * DCF i k l *
          ∑ I' : Fin r → Fin (Module.finrank ℝ E),
            ∑ J' : Fin s → Fin (Module.finrank ℝ E),
              LC k I' J' * R I' J') := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  rw [hLeib_split]
  have hLeib_partial_collapse :
      (∑ I' : Fin r → Fin (Module.finrank ℝ E),
        ∑ J' : Fin s → Fin (Module.finrank ℝ E),
        ∑ m,
          (if I' = Idx ∧ J' = Jdx then
            ∑ i, ∑ l, CF i l * DCF i m l
           else 0) * P I' J' m) =
        ∑ m, (∑ i, ∑ l, CF i l * DCF i m l) * P Idx Jdx m := by
    rw [Finset.sum_eq_single Idx]
    · rw [Finset.sum_eq_single Jdx]
      · refine Finset.sum_congr rfl (fun m _ => ?_)
        simp [and_self]
      · intro J' _ hJne
        refine Finset.sum_eq_zero (fun m _ => ?_)
        simp [hJne]
      · intro hJ; exact absurd (Finset.mem_univ _) hJ
    · intro I' _ hIne
      refine Finset.sum_eq_zero (fun J' _ => ?_)
      refine Finset.sum_eq_zero (fun m _ => ?_)
      simp [hIne]
    · intro hI; exact absurd (Finset.mem_univ _) hI
  have hLeib_partial_factor :
      (∑ i, ∑ l, ∑ k, CF i l * DCF i k l * P Idx Jdx k) =
      ∑ k, (∑ i, ∑ l, CF i l * DCF i k l) * P Idx Jdx k := by
    have hcomm1 :
        (∑ i, ∑ l, ∑ k, CF i l * DCF i k l * P Idx Jdx k) =
        ∑ i, ∑ k, ∑ l, CF i l * DCF i k l * P Idx Jdx k := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.sum_comm]
    rw [hcomm1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_mul]
  have hLeib_zeroth_match :
      (∑ i, ∑ l, ∑ k, CF i l * DCF i k l *
          ∑ I' : Fin r → Fin (Module.finrank ℝ E),
            ∑ J' : Fin s → Fin (Module.finrank ℝ E),
              LC k I' J' * R I' J') =
      ∑ I' : Fin r → Fin (Module.finrank ℝ E),
        ∑ J' : Fin s → Fin (Module.finrank ℝ E),
          (∑ i, ∑ l, ∑ k, CF i l * DCF i k l * LC k I' J') * R I' J' := by
    have hL :
        (∑ i, ∑ l, ∑ k, CF i l * DCF i k l *
            ∑ I' : Fin r → Fin (Module.finrank ℝ E),
              ∑ J' : Fin s → Fin (Module.finrank ℝ E),
                LC k I' J' * R I' J') =
        ∑ i, ∑ l, ∑ k, ∑ I' : Fin r → Fin (Module.finrank ℝ E),
          ∑ J' : Fin s → Fin (Module.finrank ℝ E),
            CF i l * DCF i k l * LC k I' J' * R I' J' := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      refine Finset.sum_congr rfl (fun l _ => ?_)
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun I' _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun J' _ => ?_)
      ring
    rw [hL]
    have hR :
        (∑ I' : Fin r → Fin (Module.finrank ℝ E),
          ∑ J' : Fin s → Fin (Module.finrank ℝ E),
            (∑ i, ∑ l, ∑ k, CF i l * DCF i k l * LC k I' J') * R I' J') =
        ∑ I' : Fin r → Fin (Module.finrank ℝ E),
          ∑ J' : Fin s → Fin (Module.finrank ℝ E),
            ∑ i, ∑ l, ∑ k, CF i l * DCF i k l * LC k I' J' * R I' J' := by
      refine Finset.sum_congr rfl (fun I' _ => ?_)
      refine Finset.sum_congr rfl (fun J' _ => ?_)
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [Finset.sum_mul]
    rw [hR]
    have hS1 :
        (∑ i, ∑ l, ∑ k, ∑ I' : Fin r → Fin (Module.finrank ℝ E),
          ∑ J' : Fin s → Fin (Module.finrank ℝ E),
            CF i l * DCF i k l * LC k I' J' * R I' J') =
        ∑ i, ∑ l, ∑ I' : Fin r → Fin (Module.finrank ℝ E),
          ∑ k, ∑ J' : Fin s → Fin (Module.finrank ℝ E),
            CF i l * DCF i k l * LC k I' J' * R I' J' := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [Finset.sum_comm]
    rw [hS1]
    have hS2 :
        (∑ i, ∑ l, ∑ I' : Fin r → Fin (Module.finrank ℝ E),
          ∑ k, ∑ J' : Fin s → Fin (Module.finrank ℝ E),
            CF i l * DCF i k l * LC k I' J' * R I' J') =
        ∑ i, ∑ I' : Fin r → Fin (Module.finrank ℝ E),
          ∑ l, ∑ k, ∑ J' : Fin s → Fin (Module.finrank ℝ E),
            CF i l * DCF i k l * LC k I' J' * R I' J' := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.sum_comm]
    rw [hS2]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun I' _ => ?_)
    have hT1 :
        (∑ i, ∑ l, ∑ k, ∑ J' : Fin s → Fin (Module.finrank ℝ E),
          CF i l * DCF i k l * LC k I' J' * R I' J') =
        ∑ i, ∑ l, ∑ J' : Fin s → Fin (Module.finrank ℝ E),
          ∑ k, CF i l * DCF i k l * LC k I' J' * R I' J' := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [Finset.sum_comm]
    rw [hT1]
    have hT2 :
        (∑ i, ∑ l, ∑ J' : Fin s → Fin (Module.finrank ℝ E),
          ∑ k, CF i l * DCF i k l * LC k I' J' * R I' J') =
        ∑ i, ∑ J' : Fin s → Fin (Module.finrank ℝ E),
          ∑ l, ∑ k, CF i l * DCF i k l * LC k I' J' * R I' J' := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.sum_comm]
    rw [hT2]
    rw [Finset.sum_comm]
  have hPrincipal_distrib :
      (∑ k, ∑ l,
          IG k l * (PP k l + (∑ I', ∑ J', ∑ m, GC k l I' J' m * P I' J' m)
                          + (∑ I', ∑ J', GC0 k l I' J' * R I' J'))) =
      (∑ k, ∑ l, IG k l * PP k l) +
      (∑ k, ∑ l, IG k l *
          (∑ I' : Fin r → Fin (Module.finrank ℝ E),
            ∑ J' : Fin s → Fin (Module.finrank ℝ E), ∑ m,
              GC k l I' J' m * P I' J' m)) +
      (∑ k, ∑ l, IG k l *
          (∑ I' : Fin r → Fin (Module.finrank ℝ E),
            ∑ J' : Fin s → Fin (Module.finrank ℝ E), GC0 k l I' J' * R I' J')) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    ring
  rw [hPrincipal_distrib]
  rw [hSwap_GC, hSwap_GC0]
  rw [hLeib_partial_collapse, hLeib_partial_factor.symm, hLeib_zeroth_match]
  ring

theorem rawTensorConnLap_chartα_raw_eq_T₀_linear_formula
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ∃ (C_2 : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
              EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ),
    ∃ (C_1 : (Fin r → Fin (Module.finrank ℝ E)) →
              (Fin s → Fin (Module.finrank ℝ E)) →
              Fin (Module.finrank ℝ E) →
              EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ),
    ∃ (C_0 : (Fin r → Fin (Module.finrank ℝ E)) →
              (Fin s → Fin (Module.finrank ℝ E)) →
              EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ),
      (∀ k l, ContDiffOn ℝ ∞ (C_2 k l) (chartTargetEuclid (I := I) (M := M) α)) ∧
      (∀ I' J' m, ContDiffOn ℝ ∞ (C_1 I' J' m) (chartTargetEuclid (I := I) (M := M) α)) ∧
      (∀ I' J', ContDiffOn ℝ ∞ (C_0 I' J') (chartTargetEuclid (I := I) (M := M) α)) ∧
      ∀ (T₀ : SmoothCcTensor g r s),
        ∀ {b : M},
          b ∈ tsupport (fun x : M =>
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
            chartLeviCivitaGoodSet (I := I) α →
          tensorChartComponentRaw (I := I) (M := M) g r s
            (rawTensorConnLapSmooth (I := I) g r s T₀) α Idx Jdx b =
            (∑ k, ∑ l,
              C_2 k l ((toEuclidean (E := E)) ((extChartAt I α) b)) *
                euclidPartial (E := E) l
                  (euclidPartial (E := E) k
                    (chartPushedRaw I α (tensorChartComponentRaw g r s T₀ α Idx Jdx)))
                  ((toEuclidean (E := E)) ((extChartAt I α) b))) +
            (∑ I' : Fin r → Fin (Module.finrank ℝ E),
              ∑ J' : Fin s → Fin (Module.finrank ℝ E),
              ∑ m,
              C_1 I' J' m ((toEuclidean (E := E)) ((extChartAt I α) b)) *
                euclidPartial (E := E) m
                  (chartPushedRaw I α (tensorChartComponentRaw g r s T₀ α I' J'))
                  ((toEuclidean (E := E)) ((extChartAt I α) b))) +
            (∑ I' : Fin r → Fin (Module.finrank ℝ E),
              ∑ J' : Fin s → Fin (Module.finrank ℝ E),
              C_0 I' J' ((toEuclidean (E := E)) ((extChartAt I α) b)) *
                chartPushedRaw I α (tensorChartComponentRaw g r s T₀ α I' J')
                  ((toEuclidean (E := E)) ((extChartAt I α) b))) := by
  refine ⟨C_2_principal (I := I) (M := M) g α,
    C_1_firstDeriv (I := I) (M := M) g r s α Idx Jdx,
    C_0_zeroth (I := I) (M := M) g r s α Idx Jdx,
    fun k l => C_2_principal_contDiffOn (I := I) (M := M) g α k l,
    fun I' J' m => C_1_firstDeriv_contDiffOn
      (I := I) (M := M) g r s α Idx Jdx I' J' m,
    fun I' J' => C_0_zeroth_contDiffOn (I := I) (M := M) g r s α Idx Jdx I' J', ?_⟩
  intro T₀ b hb
  exact rawTensorConnLap_chartα_raw_eq_T₀_linear_formula_pointwise
    (I := I) (M := M) g r s α Idx Jdx T₀ hb

end Connection
end Integral
end DifferentialGeometry

end
