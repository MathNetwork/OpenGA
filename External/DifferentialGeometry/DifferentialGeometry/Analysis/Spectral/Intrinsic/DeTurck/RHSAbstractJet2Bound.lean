import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.RHSPointwiseLipschitz
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.LieMatrixChartBridge
import DifferentialGeometry.Geometry.Flow.RicciFlow.LieDerivativePairing
import DifferentialGeometry.Geometry.Connection.ChartBridge.Ricci
import DifferentialGeometry.Geometry.Connection.ChartBridge.RiemannBasisIdentity
import DifferentialGeometry.Geometry.Connection.ChartBridge.RiemannBasisIdentityOffCentre





















































































noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Set IsManifold ContinuousLinearMap Filter
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients
open DifferentialGeometry.PDE.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]












omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem abstractRHSFrameComponent_eq_ricci_add_lie
    (g_bg g : SmoothRiemannianMetric I M) (α x : M)
    (i j : Fin (Module.finrank ℝ E)) :
    deTurckRicciRHS (I := I) g_bg g x
        (chartFrameVec (I := I) α i x) (chartFrameVec (I := I) α j x) =
      (-2 : ℝ) * ricciTensor (I := I)
          (smoothRiemannianMetricToInfty (I := I) g) x
          (chartFrameVec (I := I) α i x) (chartFrameVec (I := I) α j x)
        + lieDerivMetric (I := I) (smoothRiemannianMetricToInfty (I := I) g)
            (deTurckVF (I := I) (smoothRiemannianMetricToInfty (I := I) g)
              (smoothRiemannianMetricToInfty (I := I) g_bg)) x
            (chartFrameVec (I := I) α i x) (chartFrameVec (I := I) α j x) := by
  change ((-2 : ℝ) • ricciTensor (I := I)
          (smoothRiemannianMetricToInfty (I := I) g) x +
        lieDerivMetricClm (I := I) g
          (deTurckVF (I := I) (smoothRiemannianMetricToInfty (I := I) g)
            (smoothRiemannianMetricToInfty (I := I) g_bg)) x)
      (chartFrameVec (I := I) α i x) (chartFrameVec (I := I) α j x) = _
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rfl










omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem abstractRHSFrameComponent_diff_eq
    (g_bg g₁ g₂ : SmoothRiemannianMetric I M) (α x : M)
    (i j : Fin (Module.finrank ℝ E)) :
    (deTurckRicciRHS (I := I) g_bg g₁ x - deTurckRicciRHS (I := I) g_bg g₂ x)
        (chartFrameVec (I := I) α i x) (chartFrameVec (I := I) α j x) =
      (-2 : ℝ) * (ricciTensor (I := I)
            (smoothRiemannianMetricToInfty (I := I) g₁) x
            (chartFrameVec (I := I) α i x) (chartFrameVec (I := I) α j x)
          - ricciTensor (I := I)
            (smoothRiemannianMetricToInfty (I := I) g₂) x
            (chartFrameVec (I := I) α i x) (chartFrameVec (I := I) α j x))
        + (lieDerivMetric (I := I) (smoothRiemannianMetricToInfty (I := I) g₁)
              (deTurckVF (I := I) (smoothRiemannianMetricToInfty (I := I) g₁)
                (smoothRiemannianMetricToInfty (I := I) g_bg)) x
              (chartFrameVec (I := I) α i x) (chartFrameVec (I := I) α j x)
            - lieDerivMetric (I := I) (smoothRiemannianMetricToInfty (I := I) g₂)
              (deTurckVF (I := I) (smoothRiemannianMetricToInfty (I := I) g₂)
                (smoothRiemannianMetricToInfty (I := I) g_bg)) x
              (chartFrameVec (I := I) α i x) (chartFrameVec (I := I) α j x)) := by
  rw [deTurckRHS_diff_frame_component_apply (I := I) g_bg g₁ g₂ α x i j,
    abstractRHSFrameComponent_eq_ricci_add_lie (I := I) g_bg g₁ α x i j,
    abstractRHSFrameComponent_eq_ricci_add_lie (I := I) g_bg g₂ α x i j]
  ring






omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem abstractLieFrameComponent_eq_chartMatrix
    (g_bg g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ∀ x ∈ chartLeviCivitaGoodSet (I := I) α,
      lieDerivMetric (I := I) (smoothRiemannianMetricToInfty (I := I) g)
          (deTurckVF (I := I) (smoothRiemannianMetricToInfty (I := I) g)
            (smoothRiemannianMetricToInfty (I := I) g_bg)) x
          (chartFrameVec (I := I) α i x) (chartFrameVec (I := I) α j x) =
        chartLieDerivMetricMatrix (I := I)
          (smoothRiemannianMetricToInfty (I := I) g)
          (deTurckVF (I := I) (smoothRiemannianMetricToInfty (I := I) g)
            (smoothRiemannianMetricToInfty (I := I) g_bg)) α i j x := by
  intro x hx
  exact (chartLieDerivMetricMatrix_eq_lieDerivMetric_chartFrame (I := I)
    (smoothRiemannianMetricToInfty (I := I) g)
    (deTurckVF (I := I) (smoothRiemannianMetricToInfty (I := I) g)
      (smoothRiemannianMetricToInfty (I := I) g_bg)) α i j x hx).symm












omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem abstractRicciFrameComponent_eq_chartRicciSwap_of_basisIdentity
    (g : SmoothRiemannianMetric I M) (α x : M)
    (i j : Fin (Module.finrank ℝ E))
    (h : chartRiemannBasisIdentity (I := I) (smoothRiemannianMetricToInfty (I := I) g) x) :
    ricciTensor (I := I) (smoothRiemannianMetricToInfty (I := I) g) x
        (chartFrameVec (I := I) α i x) (chartFrameVec (I := I) α j x) =
      ∑ p : Fin (Module.finrank ℝ E), ∑ q : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr (chartFrameVec (I := I) α i x)) q *
          ((chartModelBasis E).repr (chartFrameVec (I := I) α j x)) p *
          chartRicciTensor (I := I) (smoothRiemannianMetricToInfty (I := I) g) x p q
            (extChartAt I x x) :=
  ricciTensor_eq_chartRicciSwap_of_basis_identity (I := I)
    (smoothRiemannianMetricToInfty (I := I) g) x h
    (chartFrameVec (I := I) α i x) (chartFrameVec (I := I) α j x)






omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem riemannOp_eq_chartRiemannCLM_apply'
    (g : SmoothRiemannianMetric I M) (x : M) (v w u : TangentSpace I x) :
    riemannOp (cov := LeviCivita (I := I) (smoothRiemannianMetricToInfty (I := I) g)) x v w u =
      chartRiemannCLM (I := I) (smoothRiemannianMetricToInfty (I := I) g) x v w u :=
  riemannOp_eq_chartRiemannCLM_apply (I := I)
    (smoothRiemannianMetricToInfty (I := I) g) x v w u





omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem ricciTensor_eq_chartRicciSwap
    (g : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    ricciTensor (I := I) (smoothRiemannianMetricToInfty (I := I) g) x v w =
      ∑ p : Fin (Module.finrank ℝ E),
        ∑ q : Fin (Module.finrank ℝ E),
          ((chartModelBasis E).repr v) q *
            ((chartModelBasis E).repr w) p *
            chartRicciTensor (I := I) (smoothRiemannianMetricToInfty (I := I) g) x p q
              (extChartAt I x x) :=
  ricciTensor_eq_chartRicciSwap_of_basis_identity (I := I)
    (smoothRiemannianMetricToInfty (I := I) g) x
    (chartRiemannBasisIdentity_holds (I := I)
      (smoothRiemannianMetricToInfty (I := I) g) x) v w



omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem ricciFun_eq_ricciTensor_swap
    (g : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    ricciFun (I := I) (smoothRiemannianMetricToInfty (I := I) g) x v w =
      ricciTensor (I := I) (smoothRiemannianMetricToInfty (I := I) g) x w v :=
  ricciFun_eq_ricciTensor_swap_of_basis_identity (I := I)
    (smoothRiemannianMetricToInfty (I := I) g) x
    (chartRiemannBasisIdentity_holds (I := I)
      (smoothRiemannianMetricToInfty (I := I) g) x) v w






omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem ricciFun_eq_ricciTensor
    (g : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    ricciFun (I := I) (smoothRiemannianMetricToInfty (I := I) g) x v w =
      ricciTensor (I := I) (smoothRiemannianMetricToInfty (I := I) g) x v w :=
  ricciFun_eq_ricciTensor_of_basis_identity (I := I)
    (smoothRiemannianMetricToInfty (I := I) g) x
    (chartRiemannBasisIdentity_holds (I := I)
      (smoothRiemannianMetricToInfty (I := I) g) x) v w






omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem abstractRicciFrameComponent_eq_chartRicciSwap
    (g : SmoothRiemannianMetric I M) (α x : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ricciTensor (I := I) (smoothRiemannianMetricToInfty (I := I) g) x
        (chartFrameVec (I := I) α i x) (chartFrameVec (I := I) α j x) =
      ∑ p : Fin (Module.finrank ℝ E), ∑ q : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr (chartFrameVec (I := I) α i x)) q *
          ((chartModelBasis E).repr (chartFrameVec (I := I) α j x)) p *
          chartRicciTensor (I := I) (smoothRiemannianMetricToInfty (I := I) g) x p q
            (extChartAt I x x) :=
  abstractRicciFrameComponent_eq_chartRicciSwap_of_basisIdentity (I := I) g α x i j
    (chartRiemannBasisIdentity_holds (I := I)
      (smoothRiemannianMetricToInfty (I := I) g) x)









omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem abstractRicciFrameComponent_eq_chartRicciAlpha
    (g : SmoothRiemannianMetric I M) (α : M)
    (p q : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    ricciTensor (I := I) (smoothRiemannianMetricToInfty (I := I) g) x
        (chartFrameVec (I := I) α p x) (chartFrameVec (I := I) α q x) =
      chartRicciTensor (I := I) (smoothRiemannianMetricToInfty (I := I) g) α p q
        (extChartAt I α x) := by
  rw [chartFrameVec_eq_chartBasisVecFiber, chartFrameVec_eq_chartBasisVecFiber]
  exact ricciTensor_chartBasisVec_alpha_eq (I := I)
    (smoothRiemannianMetricToInfty (I := I) g) α p q hx







omit [CompactSpace M] in
omit [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem chartCarrierRHSComp_diff_abs_le_jet2
    (g_bg g₁ g₂ : SmoothRiemannianMetric I M) (α : M)
    {K : Set E} (hK : IsCompact K)
    (hKsub : K ⊆ interior (extChartAt I α).target) :
    ∃ C : ℝ, 0 < C ∧ ∀ y ∈ K, ∀ i j : Fin (Module.finrank ℝ E),
      |chartDeTurckRHSComp (I := I) g_bg g₁ α i j y -
          chartDeTurckRHSComp (I := I) g_bg g₂ α i j y| ≤
        C * chartMetricJet2DiffSup (I := I) (M := M) g₁ g₂ α y :=
  exists_chartDeTurckRHSComp_lipschitz_on_compact (I := I) g_bg g₁ g₂ α hK hKsub










omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem abstractRHSFrameComponent_eq_chartCarrier
    (g_bg g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    deTurckRicciRHS (I := I) g_bg g x
        (chartFrameVec (I := I) α i x) (chartFrameVec (I := I) α j x) =
      chartDeTurckRHSComp (I := I) g_bg g α i j (extChartAt I α x) := by
  rw [abstractRHSFrameComponent_eq_ricci_add_lie (I := I) g_bg g α x i j]
  rw [abstractRicciFrameComponent_eq_chartRicciAlpha (I := I) g α i j hx]
  rw [abstractLieFrameComponent_eq_chartMatrix (I := I) g_bg g α i j x hx]
  rw [DeTurckCoefficients.chartLieDerivMetricMatrix_deTurckVF_eq_chartLieDeTurckComp
    (I := I) (smoothRiemannianMetricToInfty (I := I) g)
    (smoothRiemannianMetricToInfty (I := I) g_bg) α i j hx]
  rw [chartDeTurckRHSComp_def]
  rfl




omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem abstractRHSFrameComponent_diff_eq_chartCarrier_diff
    (g_bg g₁ g₂ : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    (deTurckRicciRHS (I := I) g_bg g₁ x - deTurckRicciRHS (I := I) g_bg g₂ x)
        (chartFrameVec (I := I) α i x) (chartFrameVec (I := I) α j x) =
      chartDeTurckRHSComp (I := I) g_bg g₁ α i j (extChartAt I α x) -
        chartDeTurckRHSComp (I := I) g_bg g₂ α i j (extChartAt I α x) := by
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply,
    abstractRHSFrameComponent_eq_chartCarrier (I := I) g_bg g₁ α i j hx,
    abstractRHSFrameComponent_eq_chartCarrier (I := I) g_bg g₂ α i j hx]



omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma symm_mem_chartLeviCivitaGoodSet_of_interior
    (α : M) {y : E} (hy : y ∈ interior ((extChartAt I α).target : Set E)) :
    (extChartAt I α).symm y ∈ chartLeviCivitaGoodSet (I := I) α ∧
      extChartAt I α ((extChartAt I α).symm y) = y := by
  have hy_target : y ∈ (extChartAt I α).target := interior_subset hy
  have hsrc : (extChartAt I α).symm y ∈ (extChartAt I α).source :=
    (extChartAt I α).map_target hy_target
  have hround : extChartAt I α ((extChartAt I α).symm y) = y :=
    (extChartAt I α).right_inv hy_target
  refine ⟨mem_chartLeviCivitaGoodSet_iff.mpr ⟨hsrc, ?_, ?_⟩, hround⟩
  · rw [TangentBundle.trivializationAt_baseSet]
    rw [extChartAt_source] at hsrc; exact hsrc
  · rw [hround]; exact hy


















omit [CompactSpace M] in
omit [SigmaCompactSpace M] in
theorem abstractRHSFrameComponent_diff_abs_le_jet2
    (g_bg g₁ g₂ : SmoothRiemannianMetric I M) (α : M)
    {K : Set E} (hK : IsCompact K)
    (hKsub : K ⊆ interior (extChartAt I α).target) :
    ∃ C : ℝ, 0 < C ∧ ∀ y ∈ K, ∀ i j : Fin (Module.finrank ℝ E),
      |(deTurckRicciRHS (I := I) g_bg g₁ ((extChartAt I α).symm y) -
            deTurckRicciRHS (I := I) g_bg g₂ ((extChartAt I α).symm y))
          (chartFrameVec (I := I) α i ((extChartAt I α).symm y))
          (chartFrameVec (I := I) α j ((extChartAt I α).symm y))| ≤
        C * chartMetricJet2DiffSup (I := I) (M := M) g₁ g₂ α y := by
  obtain ⟨C, hC_pos, hC⟩ :=
    chartCarrierRHSComp_diff_abs_le_jet2 (I := I) g_bg g₁ g₂ α hK hKsub
  refine ⟨C, hC_pos, ?_⟩
  intro y hy i j
  obtain ⟨hx_good, hround⟩ :=
    symm_mem_chartLeviCivitaGoodSet_of_interior (I := I) α (hKsub hy)
  rw [abstractRHSFrameComponent_diff_eq_chartCarrier_diff (I := I) g_bg g₁ g₂ α i j hx_good,
    hround]
  exact hC y hy i j

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
