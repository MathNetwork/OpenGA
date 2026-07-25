import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartCoordinateExpansion.LeibnizRemainderSecondDerivCancellation
import DifferentialGeometry.Analysis.Elliptic.TensorRegularity.SecondCovDerivExpansion.SkExtChartComponentEqCovDerivEuclid
import DifferentialGeometry.Analysis.Elliptic.TensorRegularity.CovDeriv.ComponentFormula

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold Set IsManifold ContinuousLinearMap Filter NormedSpace
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
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma tensorChartComponentProjection_covApply_eq_covDerivComponentEuclid
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s) (k : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {b : M} (hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    tensorChartComponentProjection (E := E) r s Idx Jdx
        ((trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g))
            (fun z : M => chartBasisVecFiber (I := I) α k z)
            (fun z : M => T₀.toSection z) b)) =
      covDerivComponentEuclid (I := I) (M := M) g r s α T₀ k Idx Jdx
        ((toEuclidean (E := E)) ((extChartAt I α) b)) := by
  classical
  have hb_src : b ∈ (extChartAt I α).source :=
    chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hb_good
  have hb_inv : (extChartAt I α).symm ((extChartAt I α) b) = b :=
    (extChartAt I α).left_inv hb_src
  have hsymm_te : (toEuclidean (E := E)).symm
      ((toEuclidean (E := E)) ((extChartAt I α) b)) =
      (extChartAt I α) b :=
    (toEuclidean (E := E)).symm_apply_apply _
  have hpullback :
      (extChartAt I α).symm
          ((toEuclidean (E := E)).symm
              ((toEuclidean (E := E)) ((extChartAt I α) b))) = b := by
    rw [hsymm_te]; exact hb_inv
  rw [covDerivComponentEuclid_def]
  rw [hpullback]
  congr 1
  congr 1
  rw [covApply_apply]
  have hCovDerivAt : (TensorRSNabla.tensorRSCovariantDerivative I M r s
        (LeviCivita (I := I) g)).toFun (fun z : M => T₀.toSection z) b
        (chartBasisVecFiber (I := I) α k b) =
      tensorCovDerivAt (I := I) (M := M) g r s T₀ b
        (chartBasisVecFiber (I := I) α k b) := by
    rw [tensorCovDerivAt_def]
  rw [hCovDerivAt]
  exact tensorCovDerivAt_eq_chartTensorRSCovariantDerivative
    (I := I) (M := M) g r s T₀ α k (b := b) hb_good

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma tensorChartComponentProjection_covApply_eq_T₀_expansion
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s) (k : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {b : M} (hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    tensorChartComponentProjection (E := E) r s Idx Jdx
        ((trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g))
            (fun z : M => chartBasisVecFiber (I := I) α k z)
            (fun z : M => T₀.toSection z) b)) =
      euclidPartial (E := E) k
          (chartPushedRaw I α
            (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx))
          ((toEuclidean (E := E)) ((extChartAt I α) b)) +
        ∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
                (Fin s → Fin (Module.finrank ℝ E)),
          covDerivLowerOrderCoeff (I := I) (M := M) g r s α k Idx p.1 Jdx p.2
              ((toEuclidean (E := E)) ((extChartAt I α) b)) *
            chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α p.1 p.2)
              ((toEuclidean (E := E)) ((extChartAt I α) b)) := by
  classical
  rw [tensorChartComponentProjection_covApply_eq_covDerivComponentEuclid
    (I := I) (M := M) g r s α T₀ k Idx Jdx hb_good]
  have hb_src : b ∈ (extChartAt I α).source :=
    chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hb_good
  have hb_tgt : (extChartAt I α) b ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source hb_src
  have hy_target :
      (toEuclidean (E := E)) ((extChartAt I α) b) ∈
        chartTargetEuclid (I := I) (M := M) α :=
    ⟨(extChartAt I α) b, hb_tgt, rfl⟩
  have hEqOn := covDerivComponentEuclid_eqOn (I := I) (M := M) g r s α T₀ k Idx
    Jdx hy_target
  simp only at hEqOn
  rw [hEqOn]
  rw [covDerivLowerOrderTerm_def]
  congr 1
  refine Finset.sum_congr rfl (fun p _ => ?_)
  congr 1
  exact (chartPushedRaw_apply_of_mem (I := I) (M := M) α
    (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α p.1 p.2)
    hy_target).symm

theorem chartLeibnizRemainder_eq_T₀_linear
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {b : M}
    (hb : b ∈ tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
      chartLeviCivitaGoodSet (I := I) α) :
    chartLeibnizRemainder (I := I) (M := M) g r s α T₀ Idx Jdx b =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i l b *
              (extDerivFun (I := I) (fun z : M =>
                  chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M)
                    g α i k z) b
                  (chartBasisVecFiber (I := I) α l b)) *
              (euclidPartial (E := E) k
                  (chartPushedRaw I α
                    (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx
                      Jdx))
                  ((toEuclidean (E := E)) ((extChartAt I α) b)) +
                ∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
                        (Fin s → Fin (Module.finrank ℝ E)),
                  covDerivLowerOrderCoeff (I := I) (M := M) g r s α k Idx p.1
                      Jdx p.2
                      ((toEuclidean (E := E)) ((extChartAt I α) b)) *
                    chartPushedRaw I α
                      (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α
                        p.1 p.2)
                      ((toEuclidean (E := E)) ((extChartAt I α) b))) := by
  classical
  have hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α := hb.2
  rw [chartLeibnizRemainder_eq_firstDerivOnly
    (I := I) (M := M) g r s α T₀ Idx Jdx hb]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun l _ => ?_)
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [tensorChartComponentProjection_covApply_eq_T₀_expansion
    (I := I) (M := M) g r s α T₀ k Idx Jdx hb_good]

end Connection
end Integral
end DifferentialGeometry

end
