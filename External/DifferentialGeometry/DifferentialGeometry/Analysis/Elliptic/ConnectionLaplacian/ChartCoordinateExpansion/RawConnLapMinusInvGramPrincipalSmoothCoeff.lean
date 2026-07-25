import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartCoordinateExpansion.RawConnLapChartProjFullExpansionViaChartInvGram
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartCoordinateExpansion.ChartFrameTraceΓCorrectionT0Linear
import DifferentialGeometry.Analysis.Elliptic.TensorRegularity.CovDeriv.SlotCorrectionComponent
import DifferentialGeometry.Analysis.Elliptic.TensorRegularity.ChartPullbackSmoothness.ChartInvGramMatrixPullback
import DifferentialGeometry.Geometry.Curvature.Order2Defect.MetricTraceFrame
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.TensorRicciCommutator


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [CompactSpace M] [I.Boundaryless] in
theorem rawConnLap_chartα_minus_invGramPrincipalSum_eq_christoffelTrace
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    tensorChartComponentRaw (I := I) (M := M) g r s
        (rawTensorConnLapSmooth (I := I) g r s T₀) α Idx Jdx b -
      chartInvGramPrincipalSum (I := I) (M := M) g r s α T₀ Idx Jdx b =
      - ∑ k : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g α b k l *
              tensorChartComponentProjection (E := E) r s Idx Jdx
                ((trivializationAt (TensorRSModel r s ℝ E)
                    (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
                  ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                      (LeviCivita (I := I) g)).toFun
                    (fun z : M => T₀.toSection z) b
                    ((LeviCivita (I := I) g).toFun
                      (fun z : M => chartBasisVecFiber (I := I) α k z) b
                      (chartBasisVecFiber (I := I) α l b)))) := by
  classical
  have hT_total : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y
        ((fun z : M => T₀.toSection z) y)) := T₀.toSection.contMDiff
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hb

  set proj : TensorRSSpace r s I b →L[ℝ] ℝ :=
    (tensorChartComponentProjection (E := E) r s Idx Jdx).comp
      ((trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b)
    with hproj_def
  have hproj_apply : ∀ D : TensorRSSpace r s I b,
      proj D =
        tensorChartComponentProjection (E := E) r s Idx Jdx
          ((trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b D) := by
    intro D; rw [hproj_def, ContinuousLinearMap.comp_apply]

  set Ψ : TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] TensorRSSpace r s I b :=
    tensorHessianBilinAt (I := I) g r s (fun z : M => T₀.toSection z) hT_total b
    with hΨ_def
  set B : Fin (Module.finrank ℝ E) → TangentSpace I b :=
    fun i => smoothOrthoFrame (I := I) g b i b with hB_def
  have hB_orthonormal : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner b (B i) (B j) = if i = j then (1 : ℝ) else 0 :=
    fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g b i j

  have hChartBasis_mdiff : ∀ k : Fin (Module.finrank ℝ E),
      MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (fun z : M => TotalSpace.mk' E (E := fun w : M => TangentSpace I w) z
          (chartBasisVecFiber (I := I) α k z)) b :=
    fun k => ((chartBasisVec_contMDiffOn (I := I) α k).contMDiffAt
      ((trivializationAt E (TangentSpace I) α).open_baseSet.mem_nhds
        hb_base)).mdifferentiableAt (by simp)

  have hLHS_trace :
      tensorChartComponentRaw (I := I) (M := M) g r s
          (rawTensorConnLapSmooth (I := I) g r s T₀) α Idx Jdx b =
        proj (∑ i : Fin (Module.finrank ℝ E), Ψ (B i) (B i)) := by
    rw [tensorChartComponentRaw_def, tensorTrivProj, rawTensorConnLapSmooth_toSection_apply]
    rw [rawTensorConnLap_eq_frame_trace (I := I) g r s
      (fun z : M => T₀.toSection z) hT_total b B hB_orthonormal]
    rw [← hΨ_def, hproj_apply]

  have hTrace_fibre :
      (∑ i : Fin (Module.finrank ℝ E), Ψ (B i) (B i)) =
        ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g α b k l •
            Ψ (chartBasisVecFiber (I := I) α k b)
              (chartBasisVecFiber (I := I) α l b) :=
    orthonormal_basis_bilin_trace_chartα (I := I) (A := TensorRSSpace r s I b)
      g α hb_base Ψ B hB_orthonormal
  have hTrace_chartα :
      proj (∑ i : Fin (Module.finrank ℝ E), Ψ (B i) (B i)) =
        ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g α b k l *
            proj (Ψ (chartBasisVecFiber (I := I) α k b)
              (chartBasisVecFiber (I := I) α l b)) := by
    rw [hTrace_fibre, map_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [map_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [map_smul, smul_eq_mul]

  have hProjΨ_chartBasis : ∀ k l : Fin (Module.finrank ℝ E),
      proj (Ψ (chartBasisVecFiber (I := I) α k b) (chartBasisVecFiber (I := I) α l b)) =
          tensorChartComponentProjection (E := E) r s Idx Jdx
            ((trivializationAt (TensorRSModel r s ℝ E)
                (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
              ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                  (LeviCivita (I := I) g)).toFun
                (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                  (LeviCivita (I := I) g)) (chartBasisVecFiber (I := I) α k)
                  (fun z : M => T₀.toSection z)) b
                (chartBasisVecFiber (I := I) α l b))) -
        tensorChartComponentProjection (E := E) r s Idx Jdx
          ((trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
            ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                (LeviCivita (I := I) g)).toFun
              (fun z : M => T₀.toSection z) b
              ((LeviCivita (I := I) g).toFun
                (fun z : M => chartBasisVecFiber (I := I) α k z) b
                (chartBasisVecFiber (I := I) α l b)))) := by
    intro k l
    rw [hΨ_def, tensorHessianBilinAt_apply (I := I) g r s
      (fun z : M => T₀.toSection z) hT_total (hChartBasis_mdiff k) (hChartBasis_mdiff l)]
    rw [hproj_apply, map_sub, map_sub]

  set A : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun k l =>
      chartInvGramMatrix (I := I) g α b k l *
        tensorChartComponentProjection (E := E) r s Idx Jdx
          ((trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
            ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                (LeviCivita (I := I) g)).toFun
              (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                (LeviCivita (I := I) g)) (chartBasisVecFiber (I := I) α k)
                (fun z : M => T₀.toSection z)) b
              (chartBasisVecFiber (I := I) α l b)))
    with hA_def
  set C : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun k l =>
      chartInvGramMatrix (I := I) g α b k l *
        tensorChartComponentProjection (E := E) r s Idx Jdx
          ((trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
            ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                (LeviCivita (I := I) g)).toFun
              (fun z : M => T₀.toSection z) b
              ((LeviCivita (I := I) g).toFun
                (fun z : M => chartBasisVecFiber (I := I) α k z) b
                (chartBasisVecFiber (I := I) α l b))))
    with hC_def

  have hProjΨ_split : ∀ k l : Fin (Module.finrank ℝ E),
      chartInvGramMatrix (I := I) g α b k l *
          proj (Ψ (chartBasisVecFiber (I := I) α k b)
            (chartBasisVecFiber (I := I) α l b)) =
        A k l - C k l := by
    intro k l
    rw [hProjΨ_chartBasis k l, hA_def, hC_def, mul_sub]
  rw [hLHS_trace, hTrace_chartα]
  rw [Finset.sum_congr rfl (fun k (_ : k ∈ Finset.univ) =>
    Finset.sum_congr rfl (fun l (_ : l ∈ Finset.univ) => hProjΨ_split k l))]
  have hPrincipal :
      (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E), A k l) =
        chartInvGramPrincipalSum (I := I) (M := M) g r s α T₀ Idx Jdx b := by
    rw [chartInvGramPrincipalSum, hA_def]
  have hSplit :
      (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E), (A k l - C k l)) =
        (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E), A k l) -
          ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E), C k l := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.sum_sub_distrib]
  rw [hSplit, hPrincipal]
  ring

private noncomputable def wTraceCoordPullback
    (g : SmoothRiemannianMetric I M) (α : M) (m : Fin (Module.finrank ℝ E)) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
  fun y =>
    ∑ k : Fin (Module.finrank ℝ E),
      ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramEuclid (I := I) g α k l y *
          chartChristoffelEuclid (I := I) g α l k m y

omit [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma wTraceCoordPullback_contDiffOn
    (g : SmoothRiemannianMetric I M) (α : M) (m : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (wTraceCoordPullback (I := I) (M := M) g α m)
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α) := by
  classical
  refine ContDiffOn.sum (fun k _ => ?_)
  refine ContDiffOn.sum (fun l _ => ?_)
  exact (chartInvGramEuclid_contDiffOn (I := I) g α k l).mul
    (chartChristoffelEuclid_contDiffOn (I := I) g α l k m)

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma christoffelTrace_proj_eq_wCoord_sum
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    (∑ k : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g α b k l *
            tensorChartComponentProjection (E := E) r s Idx Jdx
              ((trivializationAt (TensorRSModel r s ℝ E)
                  (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
                ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                    (LeviCivita (I := I) g)).toFun
                  (fun z : M => T₀.toSection z) b
                  ((LeviCivita (I := I) g).toFun
                    (fun z : M => chartBasisVecFiber (I := I) α k z) b
                    (chartBasisVecFiber (I := I) α l b))))) =
      ∑ m : Fin (Module.finrank ℝ E),
        wTraceCoordPullback (I := I) (M := M) g α m
            ((toEuclidean (E := E)) ((extChartAt I α) b)) *
          tensorChartComponentProjection (E := E) r s Idx Jdx
            ((trivializationAt (TensorRSModel r s ℝ E)
                (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
              ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                  (LeviCivita (I := I) g)).toFun
                (fun z : M => T₀.toSection z) b
                (chartBasisVecFiber (I := I) α m b))) := by
  classical
  set y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    (toEuclidean (E := E)) ((extChartAt I α) b) with hy_def
  have hb_src : b ∈ (extChartAt I α).source :=
    chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hb
  have hsymm_te : (toEuclidean (E := E)).symm y = (extChartAt I α) b := by
    rw [hy_def]; exact (toEuclidean (E := E)).symm_apply_apply _
  have hleft_inv : (extChartAt I α).symm ((extChartAt I α) b) = b :=
    (extChartAt I α).left_inv hb_src
  have hb_eq : (extChartAt I α).symm ((toEuclidean (E := E)).symm y) = b := by
    rw [hsymm_te, hleft_inv]
  set L : TensorRSSpace r s I b →L[ℝ] ℝ :=
    (tensorChartComponentProjection (E := E) r s Idx Jdx).comp
      ((trivializationAt (TensorRSModel r s ℝ E)
          (fun z : M => TensorRSSpace r s I z) α).continuousLinearMapAt ℝ b)
    with hL_def
  set Lcov : TangentSpace I b →L[ℝ] TensorRSSpace r s I b :=
    (TensorRSNabla.tensorRSCovariantDerivative I M r s
        (LeviCivita (I := I) g)).toFun
      (fun z : M => T₀.toSection z) b
    with hLcov_def

  have hChristEval : ∀ k l m : Fin (Module.finrank ℝ E),
      chartChristoffelEuclid (I := I) g α l k m y =
        chartChristoffel (I := I) g α l k m ((extChartAt I α) b) := by
    intro k l m
    rw [chartChristoffelEuclid_def, hsymm_te]

  have hInvGramEval : ∀ k l : Fin (Module.finrank ℝ E),
      chartInvGramEuclid (I := I) g α k l y = chartInvGramMatrix (I := I) g α b k l := by
    intro k l
    rw [chartInvGramEuclid_def, chartInvGramOnE_def, hsymm_te, hleft_inv]

  have hSummandLHS : ∀ k l : Fin (Module.finrank ℝ E),
      L (Lcov ((LeviCivita (I := I) g).toFun
            (fun z : M => chartBasisVecFiber (I := I) α k z) b
            (chartBasisVecFiber (I := I) α l b))) =
        ∑ m : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g α l k m ((extChartAt I α) b) *
            L (Lcov (chartBasisVecFiber (I := I) α m b)) := by
    intro k l
    rw [LeviCivita_chartBasisVec_alpha_basis_apply (I := I) (M := M) g α l k hb]
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [Lcov.map_smul, L.map_smul, smul_eq_mul]

  have hExpand : (∑ k : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g α b k l *
            L (Lcov ((LeviCivita (I := I) g).toFun
                (fun z : M => chartBasisVecFiber (I := I) α k z) b
                (chartBasisVecFiber (I := I) α l b)))) =
      ∑ k : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          ∑ m : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g α b k l *
              chartChristoffel (I := I) g α l k m ((extChartAt I α) b) *
              L (Lcov (chartBasisVecFiber (I := I) α m b)) := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [hSummandLHS k l, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    ring
  have hReorder : (∑ k : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          ∑ m : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g α b k l *
              chartChristoffel (I := I) g α l k m ((extChartAt I α) b) *
              L (Lcov (chartBasisVecFiber (I := I) α m b))) =
      ∑ m : Fin (Module.finrank ℝ E),
        (∑ k : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g α b k l *
              chartChristoffel (I := I) g α l k m ((extChartAt I α) b)) *
          L (Lcov (chartBasisVecFiber (I := I) α m b)) := by
    rw [Finset.sum_congr rfl (fun k (_ : k ∈ Finset.univ) => Finset.sum_comm
      (f := fun (l : Fin (Module.finrank ℝ E)) (m : Fin (Module.finrank ℝ E)) =>
        chartInvGramMatrix (I := I) g α b k l *
          chartChristoffel (I := I) g α l k m ((extChartAt I α) b) *
          L (Lcov (chartBasisVecFiber (I := I) α m b))))]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.sum_mul]
  have hStep := hExpand.trans hReorder
  rw [hL_def, hLcov_def] at hStep
  simp only [ContinuousLinearMap.comp_apply] at hStep
  rw [hStep]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  congr 1
  rw [wTraceCoordPullback]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [hInvGramEval k l, hChristEval k l m]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma chartα_proj_covRS_chartBasis_eq_euclidPartial_plus_lower
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s)
    (m : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    tensorChartComponentProjection (E := E) r s Idx Jdx
        ((trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          ((TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g)).toFun
            (fun z : M => T₀.toSection z) b
            (chartBasisVecFiber (I := I) α m b))) =
      euclidPartial (E := E) m
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α
            (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx))
          ((toEuclidean (E := E)) ((extChartAt I α) b)) +
        covDerivLowerOrderTerm (I := I) (M := M) g r s T₀ α m Idx Jdx
          ((toEuclidean (E := E)) ((extChartAt I α) b)) := by
  classical
  set y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    (toEuclidean (E := E)) ((extChartAt I α) b) with hy_def
  have hb_src : b ∈ (extChartAt I α).source :=
    chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hb
  have hb_tgt : (extChartAt I α) b ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source hb_src
  have hy_mem : y ∈ DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α :=
    ⟨(extChartAt I α) b, hb_tgt, rfl⟩
  have hsymm_te : (toEuclidean (E := E)).symm y = (extChartAt I α) b := by
    rw [hy_def]; exact (toEuclidean (E := E)).symm_apply_apply _
  have hleft_inv : (extChartAt I α).symm ((extChartAt I α) b) = b :=
    (extChartAt I α).left_inv hb_src
  have hb_eq : (extChartAt I α).symm ((toEuclidean (E := E)).symm y) = b := by
    rw [hsymm_te, hleft_inv]
  have hLHS_eq :
      (TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g)).toFun
        (fun z : M => T₀.toSection z) b
        (chartBasisVecFiber (I := I) α m b) =
      chartTensorRSCovariantDerivative (I := I) r s g α T₀.toSection
        (chartBasisVecFiber (I := I) α m) b := by
    have htdef := tensorCovDerivAt_def (I := I) (M := M) g r s T₀ b
      (chartBasisVecFiber (I := I) α m b)
    have hagree := tensorCovDerivAt_eq_chartTensorRSCovariantDerivative
      (I := I) (M := M) g r s T₀ α m hb
    exact htdef.symm.trans hagree
  rw [hLHS_eq]
  have hB1 := covDerivComponent_eq_euclidPartial_add_lowerOrder
    (I := I) (M := M) g r s T₀ α m Idx Jdx hy_mem
  rw [hb_eq] at hB1
  rw [hB1]

private noncomputable def christoffelTracePrincipalCoeff
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (I' : Fin r → Fin (Module.finrank ℝ E))
    (J' : Fin s → Fin (Module.finrank ℝ E))
    (m : Fin (Module.finrank ℝ E)) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
  fun y =>
    (if I' = Idx ∧ J' = Jdx then (1 : ℝ) else 0) *
      (- wTraceCoordPullback (I := I) (M := M) g α m y)

omit [BoundarylessManifold I M] in
omit [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma christoffelTracePrincipalCoeff_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (I' : Fin r → Fin (Module.finrank ℝ E))
    (J' : Fin s → Fin (Module.finrank ℝ E))
    (m : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (christoffelTracePrincipalCoeff (I := I) (M := M) g r s α Idx Jdx I' J' m)
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α) := by
  classical
  unfold christoffelTracePrincipalCoeff
  exact contDiffOn_const.mul (wTraceCoordPullback_contDiffOn (I := I) (M := M) g α m).neg

private noncomputable def christoffelTraceZerothCoeff
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (I' : Fin r → Fin (Module.finrank ℝ E))
    (J' : Fin s → Fin (Module.finrank ℝ E)) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
  fun y =>
    ∑ m : Fin (Module.finrank ℝ E),
      (- wTraceCoordPullback (I := I) (M := M) g α m y) *
        covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx I' Jdx J' y

omit [BoundarylessManifold I M] in
omit [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma christoffelTraceZerothCoeff_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (I' : Fin r → Fin (Module.finrank ℝ E))
    (J' : Fin s → Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (christoffelTraceZerothCoeff (I := I) (M := M) g r s α Idx Jdx I' J')
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α) := by
  classical
  unfold christoffelTraceZerothCoeff
  refine ContDiffOn.sum (fun m _ => ?_)
  exact (wTraceCoordPullback_contDiffOn (I := I) (M := M) g α m).neg.mul
    (covDerivLowerOrderCoeff_contDiffOn (I := I) (M := M) g r s α m Idx I' Jdx J')

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem christoffelTrace_correction_eq_T₀_linear
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ∃ (B_1 : (Fin r → Fin (Module.finrank ℝ E)) →
              (Fin s → Fin (Module.finrank ℝ E)) →
              Fin (Module.finrank ℝ E) →
              EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ),
    ∃ (B_0 : (Fin r → Fin (Module.finrank ℝ E)) →
              (Fin s → Fin (Module.finrank ℝ E)) →
              EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ),
      (∀ I' J' m, ContDiffOn ℝ ∞ (B_1 I' J' m)
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α)) ∧
      (∀ I' J', ContDiffOn ℝ ∞ (B_0 I' J')
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α)) ∧
      ∀ (T₀ : SmoothCcTensor g r s),
        ∀ {b : M}, b ∈ chartLeviCivitaGoodSet (I := I) α →
          (- ∑ k : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                chartInvGramMatrix (I := I) g α b k l *
                  tensorChartComponentProjection (E := E) r s Idx Jdx
                    ((trivializationAt (TensorRSModel r s ℝ E)
                        (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
                      ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                          (LeviCivita (I := I) g)).toFun
                        (fun z : M => T₀.toSection z) b
                        ((LeviCivita (I := I) g).toFun
                          (fun z : M => chartBasisVecFiber (I := I) α k z) b
                          (chartBasisVecFiber (I := I) α l b))))) =
            (∑ I' : Fin r → Fin (Module.finrank ℝ E),
              ∑ J' : Fin s → Fin (Module.finrank ℝ E),
              ∑ m,
              B_1 I' J' m ((toEuclidean (E := E)) ((extChartAt I α) b)) *
                euclidPartial (E := E) m
                  (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α
                    (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α I' J'))
                  ((toEuclidean (E := E)) ((extChartAt I α) b))) +
            (∑ I' : Fin r → Fin (Module.finrank ℝ E),
              ∑ J' : Fin s → Fin (Module.finrank ℝ E),
              B_0 I' J' ((toEuclidean (E := E)) ((extChartAt I α) b)) *
                DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α I' J')
                  ((toEuclidean (E := E)) ((extChartAt I α) b))) := by
  classical
  refine ⟨christoffelTracePrincipalCoeff (I := I) (M := M) g r s α Idx Jdx,
          christoffelTraceZerothCoeff (I := I) (M := M) g r s α Idx Jdx,
          ?_, ?_, ?_⟩
  · intro I' J' m
    exact christoffelTracePrincipalCoeff_contDiffOn (I := I) (M := M) g r s α Idx Jdx I' J' m
  · intro I' J'
    exact christoffelTraceZerothCoeff_contDiffOn (I := I) (M := M) g r s α Idx Jdx I' J'
  · intro T₀ b hb
    set y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
      (toEuclidean (E := E)) ((extChartAt I α) b) with hy_def
    have hb_src : b ∈ (extChartAt I α).source :=
      chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hb
    have hb_tgt : (extChartAt I α) b ∈ (extChartAt I α).target :=
      (extChartAt I α).map_source hb_src
    have hy_mem : y ∈ DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α := ⟨(extChartAt I α) b, hb_tgt, rfl⟩

    rw [christoffelTrace_proj_eq_wCoord_sum (I := I) (M := M) g r s α T₀ Idx Jdx hb]

    have hStep2 :
        (∑ m : Fin (Module.finrank ℝ E),
          wTraceCoordPullback (I := I) (M := M) g α m y *
            tensorChartComponentProjection (E := E) r s Idx Jdx
              ((trivializationAt (TensorRSModel r s ℝ E)
                  (fun z : M => TensorRSSpace r s I z) α).continuousLinearMapAt ℝ b
                ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                    (LeviCivita (I := I) g)).toFun
                  (fun z : M => T₀.toSection z) b
                  (chartBasisVecFiber (I := I) α m b)))) =
        ∑ m : Fin (Module.finrank ℝ E),
          wTraceCoordPullback (I := I) (M := M) g α m y *
            (euclidPartial (E := E) m
                (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)) y +
              covDerivLowerOrderTerm (I := I) (M := M) g r s T₀ α m Idx Jdx y) := by
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [chartα_proj_covRS_chartBasis_eq_euclidPartial_plus_lower
        (I := I) (M := M) g r s α T₀ m Idx Jdx hb]
    rw [hStep2]

    have hStep3 :
        (- ∑ m : Fin (Module.finrank ℝ E),
            wTraceCoordPullback (I := I) (M := M) g α m y *
              (euclidPartial (E := E) m
                  (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α
                    (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)) y +
                covDerivLowerOrderTerm (I := I) (M := M) g r s T₀ α m Idx Jdx y)) =
        (∑ m : Fin (Module.finrank ℝ E),
          (- wTraceCoordPullback (I := I) (M := M) g α m y) *
            euclidPartial (E := E) m
              (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α
                (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)) y) +
        (∑ m : Fin (Module.finrank ℝ E),
          (- wTraceCoordPullback (I := I) (M := M) g α m y) *
            covDerivLowerOrderTerm (I := I) (M := M) g r s T₀ α m Idx Jdx y) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      ring
    rw [hStep3]

    have hPrincipal_block_eq :
        (∑ m : Fin (Module.finrank ℝ E),
          (- wTraceCoordPullback (I := I) (M := M) g α m y) *
            euclidPartial (E := E) m
              (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α
                (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)) y) =
        ∑ I' : Fin r → Fin (Module.finrank ℝ E),
          ∑ J' : Fin s → Fin (Module.finrank ℝ E),
            ∑ m : Fin (Module.finrank ℝ E),
              christoffelTracePrincipalCoeff (I := I) (M := M) g r s α Idx Jdx I' J' m y *
                euclidPartial (E := E) m
                  (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α
                    (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α I' J')) y := by
      rw [Finset.sum_eq_single Idx]
      · rw [Finset.sum_eq_single Jdx]
        · refine Finset.sum_congr rfl (fun m _ => ?_)
          unfold christoffelTracePrincipalCoeff
          simp [and_self]
        · intro J' _ hJne
          refine Finset.sum_eq_zero (fun m _ => ?_)
          unfold christoffelTracePrincipalCoeff
          simp [hJne]
        · intro hJ; exact absurd (Finset.mem_univ _) hJ
      · intro I' _ hIne
        refine Finset.sum_eq_zero (fun J' _ => ?_)
        refine Finset.sum_eq_zero (fun m _ => ?_)
        unfold christoffelTracePrincipalCoeff
        simp [hIne]
      · intro hI; exact absurd (Finset.mem_univ _) hI

    have hZeroth_block_eq :
        (∑ m : Fin (Module.finrank ℝ E),
          (- wTraceCoordPullback (I := I) (M := M) g α m y) *
            covDerivLowerOrderTerm (I := I) (M := M) g r s T₀ α m Idx Jdx y) =
        ∑ I' : Fin r → Fin (Module.finrank ℝ E),
          ∑ J' : Fin s → Fin (Module.finrank ℝ E),
            christoffelTraceZerothCoeff (I := I) (M := M) g r s α Idx Jdx I' J' y *
              DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α
                (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α I' J') y := by
      have hLowerEq : ∀ m,
          covDerivLowerOrderTerm (I := I) (M := M) g r s T₀ α m Idx Jdx y =
          ∑ I' : Fin r → Fin (Module.finrank ℝ E),
            ∑ J' : Fin s → Fin (Module.finrank ℝ E),
              covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx I' Jdx J' y *
                DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α I' J') y := by
        intro m
        rw [covDerivComponent_lowerOrder_eq_linearCombination
          (I := I) (M := M) g r s T₀ α m Idx Jdx y]
        rw [← Finset.sum_product']
        refine Finset.sum_congr rfl (fun p _ => ?_)
        rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_mem
          (I := I) (M := M) α
          (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α p.1 p.2) hy_mem]
      have hSubst :
          (∑ m : Fin (Module.finrank ℝ E),
            (- wTraceCoordPullback (I := I) (M := M) g α m y) *
              covDerivLowerOrderTerm (I := I) (M := M) g r s T₀ α m Idx Jdx y) =
          ∑ m : Fin (Module.finrank ℝ E),
            ∑ I' : Fin r → Fin (Module.finrank ℝ E),
              ∑ J' : Fin s → Fin (Module.finrank ℝ E),
                (- wTraceCoordPullback (I := I) (M := M) g α m y) *
                  (covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx I' Jdx J' y *
                    DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α
                      (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α I' J') y) := by
        refine Finset.sum_congr rfl (fun m _ => ?_)
        rw [hLowerEq m, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun I' _ => ?_)
        rw [Finset.mul_sum]
      rw [hSubst]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun I' _ => ?_)
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun J' _ => ?_)
      unfold christoffelTraceZerothCoeff
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      ring
    rw [hPrincipal_block_eq, hZeroth_block_eq]

end Connection
end Integral
end DifferentialGeometry

end
