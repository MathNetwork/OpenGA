import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartCoordinateExpansion.RawConnLapChartProjAsWeightedSecondCovDerivMinusΓTrace

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 400000

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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

noncomputable def chartInvGramPrincipalSum
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (b : M) : ℝ :=
  ∑ k : Fin (Module.finrank ℝ E),
    ∑ l : Fin (Module.finrank ℝ E),
      chartInvGramMatrix (I := I) g α b k l *
        tensorChartComponentProjection (E := E) r s Idx Jdx
          ((trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
            ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                (LeviCivita (I := I) g)).toFun
              (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                (LeviCivita (I := I) g))
                (chartBasisVecFiber (I := I) α k)
                (fun z : M => T₀.toSection z)) b
              (chartBasisVecFiber (I := I) α l b)))

noncomputable def chartFrameCoordMatrixWeightedDoubleSum
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (b : M) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E),
    ∑ l : Fin (Module.finrank ℝ E),
      chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i l b *
        tensorChartComponentProjection (E := E) r s Idx Jdx
          ((trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
            ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                (LeviCivita (I := I) g)).toFun
              (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                (LeviCivita (I := I) g))
                (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun
                (fun z : M => T₀.toSection z)) b
              (chartBasisVecFiber (I := I) α l b)))

noncomputable def chartLeibnizRemainder
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (b : M) : ℝ :=
  chartFrameCoordMatrixWeightedDoubleSum (I := I) (M := M) g r s α T₀ Idx Jdx b -
    chartInvGramPrincipalSum (I := I) (M := M) g r s α T₀ Idx Jdx b

noncomputable def chartFrameTraceΓCorrection
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (b : M) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E),
    tensorChartComponentProjection (E := E) r s Idx Jdx
      ((trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
        ((TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g)).toFun
          (fun z : M => T₀.toSection z) b
          ((LeviCivita (I := I) g).toFun
            (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b
            ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b))))

omit [I.Boundaryless] in
lemma chartInvGramPrincipal_plus_LeibnizRemainder_eq_frameWeighted
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (b : M) :
    chartInvGramPrincipalSum (I := I) (M := M) g r s α T₀ Idx Jdx b +
        chartLeibnizRemainder (I := I) (M := M) g r s α T₀ Idx Jdx b =
      chartFrameCoordMatrixWeightedDoubleSum (I := I) (M := M)
        g r s α T₀ Idx Jdx b := by
  classical
  unfold chartLeibnizRemainder
  ring

omit [I.Boundaryless] in
theorem chartPushed_rawConnLap_chart_α_proj_eq_chartInvGram_secondCovDeriv_plus_corrections
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {b : M}
    (hb : b ∈ tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
      chartLeviCivitaGoodSet (I := I) α) :
    tensorChartComponentRaw (I := I) (M := M) g r s
        (rawTensorConnLapSmooth (I := I) g r s T₀) α Idx Jdx b =
      (chartInvGramPrincipalSum (I := I) (M := M) g r s α T₀ Idx Jdx b +
        chartLeibnizRemainder (I := I) (M := M) g r s α T₀ Idx Jdx b) -
      chartFrameTraceΓCorrection (I := I) (M := M) g r s α T₀ Idx Jdx b := by
  classical
  have hPred :=
    chartPushed_rawConnLap_chart_α_proj_eq_weighted_secondCovDeriv_minus_frameTraceΓ
      (I := I) (M := M) g r s α T₀ Idx Jdx (b := b) hb
  rw [hPred]
  have hFrameWeighted_eq :
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i l b *
            tensorChartComponentProjection (E := E) r s Idx Jdx
              ((trivializationAt (TensorRSModel r s ℝ E)
                  (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
                ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                    (LeviCivita (I := I) g)).toFun
                  (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                    (LeviCivita (I := I) g))
                    (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun
                    (fun z : M => T₀.toSection z)) b
                  (chartBasisVecFiber (I := I) α l b)))) =
        chartFrameCoordMatrixWeightedDoubleSum (I := I) (M := M)
          g r s α T₀ Idx Jdx b := rfl
  rw [hFrameWeighted_eq]
  have hΓ_eq :
      (∑ i : Fin (Module.finrank ℝ E),
        tensorChartComponentProjection (E := E) r s Idx Jdx
          ((trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
            ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                (LeviCivita (I := I) g)).toFun
              (fun z : M => T₀.toSection z) b
              ((LeviCivita (I := I) g).toFun
                (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b
                ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b))))) =
        chartFrameTraceΓCorrection (I := I) (M := M) g r s α T₀ Idx Jdx b := rfl
  rw [hΓ_eq]
  have hSplit :=
    chartInvGramPrincipal_plus_LeibnizRemainder_eq_frameWeighted
      (I := I) (M := M) g r s α T₀ Idx Jdx b
  linarith

end Connection
end Integral
end DifferentialGeometry

end
