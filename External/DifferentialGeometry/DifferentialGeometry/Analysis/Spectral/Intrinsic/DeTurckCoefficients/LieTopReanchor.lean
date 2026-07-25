import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartCoordinateExpansion.RealizedGramDerivChartEvaluation
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.DeTurckLieCoeffAppCcValue
import DifferentialGeometry.Analysis.Parabolic.DeTurckLinearization.LieDeTurckRemainderOrderSplit










noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Tensor0SBundle ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.PDE.DeTurck.DeTurckLinearization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]
  [SigmaCompactSpace M]

set_option linter.style.setOption false
set_option backward.isDefEq.respectTransparency false

omit [NeZero (Module.finrank ℝ E)] in
omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma lieArm2_appCc_value_invGram
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (D : SmoothCcTensor g₀ 0 4)
    (x : M) (i j : Fin (Module.finrank ℝ E)) :
    unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 4 2
          (deTurckLieArm2PrincipalCoeff (I := I) g₀ g₁ g_bg) D) x
        ![(chartModelBasis E) i, (chartModelBasis E) j] =
      ∑ k₁ : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix g₁ x x k₁ l *
          (unitModel (I := I) (M := M) g₀ 4 D x
              ![(chartModelBasis E) i, (chartModelBasis E) l,
                (chartModelBasis E) j, (chartModelBasis E) k₁]
            + unitModel (I := I) (M := M) g₀ 4 D x
              ![(chartModelBasis E) j, (chartModelBasis E) l,
                (chartModelBasis E) i, (chartModelBasis E) k₁]
            - unitModel (I := I) (M := M) g₀ 4 D x
              ![(chartModelBasis E) i, (chartModelBasis E) j,
                (chartModelBasis E) l, (chartModelBasis E) k₁]) := by
  classical
  refine (deTurckLieArm2PrincipalCoeff_apply_eq (I := I) g₀ g₁ g_bg D x
    ![(chartModelBasis E) i, (chartModelBasis E) j]).trans ?_
  have hv0 : (![(chartModelBasis E) i, (chartModelBasis E) j] :
      Fin 2 → TangentSpace I x) 0 = (chartModelBasis E) i := rfl
  have hv1 : (![(chartModelBasis E) i, (chartModelBasis E) j] :
      Fin 2 → TangentSpace I x) 1 = (chartModelBasis E) j := rfl
  simp only [hv0, hv1]
  have hpack13 : ∀ (u w : TangentSpace I x) (c v : E),
      quadrilinearMapSlotBilinearAt (E := E) (unitModel (I := I) (M := M) g₀ 4 D x)
        1 3 (by decide) ![(show E from u), 0, (show E from w), 0] c v =
      unitModel (I := I) (M := M) g₀ 4 D x ![u, c, w, v] := by
    intro u w c v
    rw [unitModel4SlotBilin_apply]
    refine congrArg (fun t : Fin 4 → E => unitModel (I := I) (M := M) g₀ 4 D x t) ?_
    funext m
    fin_cases m <;> simp [Function.update]
  have hpack23 : ∀ (u w : TangentSpace I x) (c v : E),
      quadrilinearMapSlotBilinearAt (E := E) (unitModel (I := I) (M := M) g₀ 4 D x)
        2 3 (by decide) ![(show E from u), (show E from w), 0, 0] c v =
      unitModel (I := I) (M := M) g₀ 4 D x ![u, w, c, v] := by
    intro u w c v
    rw [unitModel4SlotBilin_apply]
    refine congrArg (fun t : Fin 4 → E => unitModel (I := I) (M := M) g₀ 4 D x t) ?_
    funext m
    fin_cases m <;> simp [Function.update]
  have hpat : ∀ (u w : TangentSpace I x),
      (∑ k : Fin (Module.finrank ℝ E),
        unitModel (I := I) (M := M) g₀ 4 D x
          ![u, cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)),
            w, (Module.finBasis ℝ E) k]) =
      ∑ k₁ : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix g₁ x x k₁ l *
          unitModel (I := I) (M := M) g₀ 4 D x
            ![u, (chartModelBasis E) l, w, (chartModelBasis E) k₁] := by
    intro u w
    rw [show (∑ k : Fin (Module.finrank ℝ E),
        unitModel (I := I) (M := M) g₀ 4 D x
          ![u, cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)),
            w, (Module.finBasis ℝ E) k]) =
      ∑ k : Fin (Module.finrank ℝ E),
        quadrilinearMapSlotBilinearAt (E := E) (unitModel (I := I) (M := M) g₀ 4 D x)
          1 3 (by decide) ![(show E from u), 0, (show E from w), 0]
          (cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)))
          ((Module.finBasis ℝ E) k) from
      Finset.sum_congr rfl (fun k _ => (hpack13 u w _ _).symm)]
    rw [cometricFinBasisTrace_eq_chartInvGram_bilin (I := I) g₁ x _]
    refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun l _ => ?_))
    rw [smul_eq_mul, hpack13 u w]
  have hpatH : (∑ k : Fin (Module.finrank ℝ E),
      unitModel (I := I) (M := M) g₀ 4 D x
        ![(chartModelBasis E) i, (chartModelBasis E) j,
          cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)),
          (Module.finBasis ℝ E) k]) =
      ∑ k₁ : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix g₁ x x k₁ l *
          unitModel (I := I) (M := M) g₀ 4 D x
            ![(chartModelBasis E) i, (chartModelBasis E) j,
              (chartModelBasis E) l, (chartModelBasis E) k₁] := by
    rw [show (∑ k : Fin (Module.finrank ℝ E),
        unitModel (I := I) (M := M) g₀ 4 D x
          ![(chartModelBasis E) i, (chartModelBasis E) j,
            cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)),
            (Module.finBasis ℝ E) k]) =
      ∑ k : Fin (Module.finrank ℝ E),
        quadrilinearMapSlotBilinearAt (E := E) (unitModel (I := I) (M := M) g₀ 4 D x)
          2 3 (by decide)
          ![(chartModelBasis E) i, (chartModelBasis E) j, 0, 0]
          (cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)))
          ((Module.finBasis ℝ E) k) from
      Finset.sum_congr rfl (fun k _ =>
        (hpack23 ((chartModelBasis E) i) ((chartModelBasis E) j) _ _).symm)]
    rw [cometricFinBasisTrace_eq_chartInvGram_bilin (I := I) g₁ x _]
    refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun l _ => ?_))
    rw [smul_eq_mul, hpack23 ((chartModelBasis E) i) ((chartModelBasis E) j)]
  rw [hpat ((chartModelBasis E) i) ((chartModelBasis E) j),
    hpat ((chartModelBasis E) j) ((chartModelBasis E) i), hpatH]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun k₁ _ => ?_)
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  ring

open DifferentialGeometry.PDE.DeTurck.RicciLinearization (realizedGramDeriv)
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (domDomCongrSection_unitModel unitModel_basisChart_eq_tensorChartComponentRaw tensorChartComponentRaw tensorChartComponentRaw_add tensorChartComponentRaw_smul arm2ReadoutCovDerivPair arm1ReadoutCovDeriv iteratedCovGrad2_chartComponent_readout iteratedCovGrad1_chartComponent_readout partialDeriv2_realizedGramDeriv_eq_half_sum_euclidPartial2 partialDeriv_realizedGramDeriv_eq_half_sum_euclidPartial realizedGramDeriv_eventuallyEq_symm_scalarOnE_raw euclidPartial_swap_chartPushedRaw_tensorChartComponentRaw covDerivLowerOrderTerm02_center_eq covDerivLowerOrderTerm03_center_eq euclidPartial2_chartPushedRaw_eq_partialDeriv2_scalarOnE partialDeriv_scalarOnE_eq_euclidPartial_local toEuclidean_extChartAt_mem_chartTargetEuclid symm_toEuclidean_symm_toEuclidean_extChartAt)
open DifferentialGeometry.Analysis.Sobolev.Chart (chartPushedRaw chartPushedRaw_apply_of_mem chartTargetEuclid chartTargetEuclid_isOpen)
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity (tensorChartComponentRaw_eq_chartFrame chartFrameBasisModel covDerivLowerOrderTerm euclidPartial euclidPartial_def covDerivComponent_lowerOrder_contDiffOn euclidPartial_chartPushedRaw_contDiffOn chartPushedRaw_tensorChartComponentRaw_contDiffOn)
open DifferentialGeometry.PDE.DeTurck.DeTurckLinearization (chartDeTurckCorrPrincipalSymbolExprRaw chartDeTurckCorrHessBlockRaw)
open DifferentialGeometry.Integral.DivergenceTheorem (partialDeriv chartGramOnE chartInvGramOnE)
open DifferentialGeometry.Integral.Measure (chartGramMatrix)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma lieArm_frame0_eq_unitTensor (x b : M) :
    chartFrameBasisModel (I := I) (M := M) x b 0 ![] = unitTensor (I := I) (M := M) b := by
  apply ContinuousMultilinearMap.ext
  intro v
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma lieArm_rawComponent_eq_unitModel_frame
    (g : SmoothRiemannianMetric I M) (s : ℕ) (W : SmoothCcTensor g 0 s) (x : M)
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) {b : M}
    (hb : b ∈ (chartAt H x).source) :
    tensorChartComponentRaw (I := I) (M := M) g 0 s W x ![] Jdx b =
      unitModel (I := I) (M := M) g s W b
        (fun j => (show E from chartBasisVecFiber (I := I) x (Jdx j) b)) := by
  rw [tensorChartComponentRaw_eq_chartFrame (I := I) (M := M) g 0 s W x hb ![] Jdx]
  rw [lieArm_frame0_eq_unitTensor (I := I) (M := M) x b]
  rfl

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma lieArm_euclidPartial_add_local
    (l : Fin (Module.finrank ℝ E))
    {f h : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ}
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hf : DifferentiableAt ℝ f y) (hh : DifferentiableAt ℝ h y) :
    euclidPartial (E := E) l (fun z => f z + h z) y =
      euclidPartial (E := E) l f y + euclidPartial (E := E) l h y := by
  rw [euclidPartial_def, euclidPartial_def, euclidPartial_def, fderiv_fun_add hf hh,
    ContinuousLinearMap.add_apply]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma lieArm_covDerivLowerOrderTerm_differentiableAt_center
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g₀ r s) (x : M)
    (m : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    DifferentiableAt ℝ
      (covDerivLowerOrderTerm (I := I) (M := M) g₀ r s S x m Idx Jdx)
      (toEuclidean (E := E) (extChartAt I x x)) := by
  have hmem : (toEuclidean (E := E)) (extChartAt I x x) ∈
      chartTargetEuclid (I := I) (M := M) x :=
    toEuclidean_extChartAt_mem_chartTargetEuclid (I := I) (M := M) x (mem_chart_source H x)
  have hcd : ContDiffOn ℝ ∞
      (covDerivLowerOrderTerm (I := I) (M := M) g₀ r s S x m Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) x) :=
    covDerivComponent_lowerOrder_contDiffOn (I := I) (M := M) g₀ r s S x m Idx Jdx
      (fun Idx' Jdx' => chartPushedRaw_tensorChartComponentRaw_contDiffOn
        (I := I) (M := M) g₀ r s S x Idx' Jdx')
  exact (hcd.contDiffAt
    ((DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) x).mem_nhds hmem)).differentiableAt (by simp)

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma lieArm_euclidPartial_chartPushedRaw_differentiableAt_center
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g₀ r s) (x : M)
    (k : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    DifferentiableAt ℝ
      (euclidPartial (E := E) k
        (chartPushedRaw I x
          (tensorChartComponentRaw (I := I) (M := M) g₀ r s S x Idx Jdx)))
      (toEuclidean (E := E) (extChartAt I x x)) := by
  have hmem : (toEuclidean (E := E)) (extChartAt I x x) ∈
      chartTargetEuclid (I := I) (M := M) x :=
    toEuclidean_extChartAt_mem_chartTargetEuclid (I := I) (M := M) x (mem_chart_source H x)
  have hcd : ContDiffOn ℝ ∞
      (euclidPartial (E := E) k
        (chartPushedRaw I x
          (tensorChartComponentRaw (I := I) (M := M) g₀ r s S x Idx Jdx)))
      (chartTargetEuclid (I := I) (M := M) x) :=
    euclidPartial_chartPushedRaw_contDiffOn (I := I) (M := M) g₀ r s S x k Idx Jdx
  exact (hcd.contDiffAt
    ((DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) x).mem_nhds hmem)).differentiableAt (by simp)

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma lieArm_unitModel4_basisChart_readout_split
    (g₀ : SmoothRiemannianMetric I M) (h : SmoothCcTensor g₀ 0 2) (x : M)
    (a b c d : Fin (Module.finrank ℝ E)) :
    unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 h) x
        ![chartModelBasis E a, chartModelBasis E b, chartModelBasis E c, chartModelBasis E d] =
      euclidPartial (E := E) a
          (fun y' => euclidPartial (E := E) b
            (chartPushedRaw I x (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2
              h x ![] ![c, d])) y')
          (toEuclidean (E := E) (extChartAt I x x))
        + arm2ReadoutCovDerivPair (I := I) (M := M) g₀ h x ![a, b, c, d] := by
  classical
  have hmemsrc : x ∈ (chartAt H x).source := mem_chart_source H x
  have hroundtrip : (extChartAt I x).symm
      ((toEuclidean (E := E)).symm ((toEuclidean (E := E)) (extChartAt I x x))) = x :=
    symm_toEuclidean_symm_toEuclidean_extChartAt (I := I) (M := M) x hmemsrc
  rw [show (![chartModelBasis E a, chartModelBasis E b, chartModelBasis E c,
        chartModelBasis E d] : Fin 4 → TangentSpace I x) =
      (fun j => chartModelBasis E ((![a, b, c, d] : Fin 4 → Fin (Module.finrank ℝ E)) j)) from by
    funext j; fin_cases j <;> rfl]
  rw [unitModel_basisChart_eq_tensorChartComponentRaw (I := I) (M := M) g₀ (2 + 2)
    (iteratedCovGrad (I := I) g₀ 0 2 2 h) x (![a, b, c, d])]
  rw [show tensorChartComponentRaw (I := I) (M := M) g₀ 0 (2 + 2)
        (iteratedCovGrad (I := I) g₀ 0 2 2 h) x ![] (![a, b, c, d]) x =
      tensorChartComponentRaw (I := I) (M := M) g₀ 0 (2 + 2)
        (iteratedCovGrad (I := I) g₀ 0 2 2 h) x ![] (![a, b, c, d])
        ((extChartAt I x).symm
          ((toEuclidean (E := E)).symm ((toEuclidean (E := E)) (extChartAt I x x)))) from by
    rw [hroundtrip] ]
  rw [iteratedCovGrad2_chartComponent_readout (I := I) g₀ h x (![a, b, c, d])]
  have hJ0 : (![a, b, c, d] : Fin (2 + 2) → Fin (Module.finrank ℝ E)) 0 = a := rfl
  have hJ1 : (Matrix.vecTail (![a, b, c, d] : Fin (2 + 2) → Fin (Module.finrank ℝ E))) 0 = b := rfl
  have hJtail2 : Matrix.vecTail (Matrix.vecTail
      (![a, b, c, d] : Fin (2 + 2) → Fin (Module.finrank ℝ E))) = ![c, d] := by
    funext j; fin_cases j <;> rfl
  simp only [arm2ReadoutCovDerivPair, hJ0, hJ1, hJtail2]
  have hPdiff : DifferentiableAt ℝ
      (euclidPartial (E := E) b
        (chartPushedRaw I x (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![c, d])))
      (toEuclidean (E := E) (extChartAt I x x)) :=
    lieArm_euclidPartial_chartPushedRaw_differentiableAt_center (I := I) (M := M) g₀ 0 2 h x b ![] ![c, d]
  have hQdiff : DifferentiableAt ℝ
      (covDerivLowerOrderTerm (I := I) (M := M) g₀ 0 2 h x b ![] ![c, d])
      (toEuclidean (E := E) (extChartAt I x x)) :=
    lieArm_covDerivLowerOrderTerm_differentiableAt_center (I := I) (M := M) g₀ 0 2 h x b ![] ![c, d]
  rw [lieArm_euclidPartial_add_local a hPdiff hQdiff]
  ring

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma lieArm_unitModel3_basisChart_readout_split
    (g₀ : SmoothRiemannianMetric I M) (h : SmoothCcTensor g₀ 0 2) (x : M)
    (a b c : Fin (Module.finrank ℝ E)) :
    unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 h) x
        ![chartModelBasis E a, chartModelBasis E b, chartModelBasis E c] =
      euclidPartial (E := E) a
          (chartPushedRaw I x (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2
            h x ![] ![b, c]))
          (toEuclidean (E := E) (extChartAt I x x))
        + arm1ReadoutCovDeriv (I := I) (M := M) g₀ h x ![a, b, c] := by
  classical
  have hmemsrc : x ∈ (chartAt H x).source := mem_chart_source H x
  have hroundtrip : (extChartAt I x).symm
      ((toEuclidean (E := E)).symm ((toEuclidean (E := E)) (extChartAt I x x))) = x :=
    symm_toEuclidean_symm_toEuclidean_extChartAt (I := I) (M := M) x hmemsrc
  rw [show (![chartModelBasis E a, chartModelBasis E b, chartModelBasis E c] :
        Fin 3 → TangentSpace I x) =
      (fun j => chartModelBasis E ((![a, b, c] : Fin 3 → Fin (Module.finrank ℝ E)) j)) from by
    funext j; fin_cases j <;> rfl]
  rw [unitModel_basisChart_eq_tensorChartComponentRaw (I := I) (M := M) g₀ (2 + 1)
    (iteratedCovGrad (I := I) g₀ 0 2 1 h) x (![a, b, c])]
  rw [show tensorChartComponentRaw (I := I) (M := M) g₀ 0 (2 + 1)
        (iteratedCovGrad (I := I) g₀ 0 2 1 h) x ![] (![a, b, c]) x =
      tensorChartComponentRaw (I := I) (M := M) g₀ 0 (2 + 1)
        (iteratedCovGrad (I := I) g₀ 0 2 1 h) x ![] (![a, b, c])
        ((extChartAt I x).symm
          ((toEuclidean (E := E)).symm ((toEuclidean (E := E)) (extChartAt I x x)))) from by
    rw [hroundtrip] ]
  rw [iteratedCovGrad1_chartComponent_readout (I := I) g₀ h x (![a, b, c])]
  have hJ0 : (![a, b, c] : Fin (2 + 1) → Fin (Module.finrank ℝ E)) 0 = a := rfl
  have hJtail : Matrix.vecTail (![a, b, c] : Fin (2 + 1) → Fin (Module.finrank ℝ E)) = ![b, c] := by
    funext j; fin_cases j <;> rfl
  simp only [arm1ReadoutCovDeriv, hJ0, hJtail]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma lieArm_symmS_rawComponent
    (g : SmoothRiemannianMetric I M) (S : SmoothCcTensor g 0 2) (x : M)
    (c d : Fin (Module.finrank ℝ E)) {b : M}
    (hb : b ∈ (chartAt H x).source) :
    tensorChartComponentRaw (I := I) (M := M) g 0 2
        (ccTensor02Symm (I := I) (M := M) g S) x ![] ![c, d] b =
      (1 / 2 : ℝ) *
        (tensorChartComponentRaw (I := I) (M := M) g 0 2 S x ![] ![c, d] b +
          tensorChartComponentRaw (I := I) (M := M) g 0 2 S x ![] ![d, c] b) := by
  classical
  have hswap : tensorChartComponentRaw (I := I) (M := M) g 0 2
      (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) S) x ![] ![c, d] b =
      tensorChartComponentRaw (I := I) (M := M) g 0 2 S x ![] ![d, c] b := by
    rw [lieArm_rawComponent_eq_unitModel_frame (I := I) (M := M) g 2 _ x ![c, d] hb,
      lieArm_rawComponent_eq_unitModel_frame (I := I) (M := M) g 2 S x ![d, c] hb]
    rw [domDomCongrSection_unitModel (I := I) (M := M) g (Equiv.swap (0 : Fin 2) 1) S b]
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    refine congrArg (fun t : Fin 2 → E => unitModel (I := I) (M := M) g 2 S b t) ?_
    funext j
    fin_cases j <;> rfl
  rw [show ccTensor02Symm (I := I) (M := M) g S =
      (1 / 2 : ℝ) • (S + domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) S) from rfl]
  rw [tensorChartComponentRaw_smul, tensorChartComponentRaw_add, hswap]
  rw [smul_eq_mul]

omit [BoundarylessManifold I M] in
private lemma lieArm_scalarOnE_symmS_eventuallyEq_realizedGramDeriv
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (c d : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE (I := I) x
        (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2
          (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![] ![c, d]) =ᶠ[𝓝 (extChartAt I x x)]
      realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x c d := by
  classical
  have hev := realizedGramDeriv_eventuallyEq_symm_scalarOnE_raw (I := I) g₀ T T'
    hδ_lt hδ hδ'_lt hδ' x c d
  have hx_src : x ∈ (extChartAt I x).source := by
    rw [extChartAt_source (I := I)]; exact mem_chart_source H x
  have htarget : extChartAt I x x ∈ (extChartAt I x).target :=
    (extChartAt I x).map_source hx_src
  have htarget_open : IsOpen ((extChartAt I x).target : Set E) :=
    isOpen_extChartAt_target (I := I) x
  filter_upwards [htarget_open.mem_nhds htarget, hev] with y hy_tgt hev_y
  rw [hev_y]
  have hb : (extChartAt I x).symm y ∈ (chartAt H x).source := by
    rw [← extChartAt_source (I := I)]
    exact (extChartAt I x).map_target hy_tgt
  rw [DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE_def]
  rw [lieArm_symmS_rawComponent (I := I) (M := M) g₀ (T - T') x c d hb]
  rw [DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE_def,
    DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE_def]

omit [BoundarylessManifold I M] in
private lemma lieArm_partialDeriv_symmS_scalar_eventuallyEq
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (m c d : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) m
        (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE (I := I) x
          (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2
            (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![] ![c, d])) =ᶠ[𝓝 (extChartAt I x x)]
      DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) m
        (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x c d) := by
  have hev := (lieArm_scalarOnE_symmS_eventuallyEq_realizedGramDeriv (I := I) g₀ T T'
    hδ_lt hδ hδ'_lt hδ' x c d).eventuallyEq_nhds
  filter_upwards [hev] with y hy
  unfold DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv
  rw [hy.fderiv_eq]

omit [BoundarylessManifold I M] in
private lemma lieArm_U4_readout
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (a b c d : Fin (Module.finrank ℝ E)) :
    unitModel (I := I) (M := M) g₀ 4
        (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x
        ![chartModelBasis E a, chartModelBasis E b, chartModelBasis E c, chartModelBasis E d] =
      DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) a
          (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) b
            (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x c d))
          (extChartAt I x x)
        + arm2ReadoutCovDerivPair (I := I) (M := M) g₀
            (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![a, b, c, d] := by
  classical
  rw [lieArm_unitModel4_basisChart_readout_split (I := I) (M := M) g₀
    (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x a b c d]
  refine congrArg (fun t : ℝ =>
    t + arm2ReadoutCovDerivPair (I := I) (M := M) g₀
      (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![a, b, c, d]) ?_
  rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.euclidPartial2_chartPushedRaw_eq_partialDeriv2_scalarOnE (I := I) (M := M) g₀
    (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x b a c d]
  have hev1 := lieArm_partialDeriv_symmS_scalar_eventuallyEq (I := I) g₀ T T'
    hδ_lt hδ hδ'_lt hδ' x b c d
  change fderiv ℝ
      (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) b
        (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE (I := I) x
          (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2
            (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![] ![c, d])))
      (extChartAt I x x) ((chartModelBasis E) a) = fderiv ℝ
      (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) b
        (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x c d))
      (extChartAt I x x) ((chartModelBasis E) a)
  rw [hev1.fderiv_eq]

omit [BoundarylessManifold I M] in
private lemma lieArm_U3_readout
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (a b c : Fin (Module.finrank ℝ E)) :
    unitModel (I := I) (M := M) g₀ 3
        (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x
        ![chartModelBasis E a, chartModelBasis E b, chartModelBasis E c] =
      DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) a
          (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x b c)
          (extChartAt I x x)
        + arm1ReadoutCovDeriv (I := I) (M := M) g₀
            (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![a, b, c] := by
  classical
  rw [lieArm_unitModel3_basisChart_readout_split (I := I) (M := M) g₀
    (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x a b c]
  refine congrArg (fun t : ℝ =>
    t + arm1ReadoutCovDeriv (I := I) (M := M) g₀
      (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![a, b, c]) ?_
  have hYmem : (toEuclidean (E := E)) (extChartAt I x x) ∈
      chartTargetEuclid (I := I) (M := M) x :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.toEuclidean_extChartAt_mem_chartTargetEuclid
      (I := I) (M := M) x (mem_chart_source H x)
  have hround : extChartAt I x ((extChartAt I x).symm
      ((toEuclidean (E := E)).symm ((toEuclidean (E := E)) (extChartAt I x x)))) =
      extChartAt I x x := by
    rw [(toEuclidean (E := E)).symm_apply_apply]
    have htarget : extChartAt I x x ∈ (extChartAt I x).target :=
      (extChartAt I x).map_source
        (by rw [extChartAt_source (I := I)]; exact mem_chart_source H x)
    rw [(extChartAt I x).right_inv htarget]
  have h := DifferentialGeometry.Analysis.Parabolic.TensorSpectral.partialDeriv_scalarOnE_eq_euclidPartial_local (I := I) (M := M)
    (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2
      (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![] ![b, c]) x a hYmem
  rw [hround] at h
  rw [← h]
  have hev1 := lieArm_scalarOnE_symmS_eventuallyEq_realizedGramDeriv (I := I) g₀ T T'
    hδ_lt hδ hδ'_lt hδ' x b c
  unfold DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv
  rw [hev1.fderiv_eq]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma lieArm_chartInvGramOnE_center (g : SmoothRiemannianMetric I M) (x : M)
    (a b : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Integral.DivergenceTheorem.chartInvGramOnE (I := I) g x a b
        (extChartAt I x x) =
      chartInvGramMatrix (I := I) g x x a b := by
  rw [DifferentialGeometry.Integral.DivergenceTheorem.chartInvGramOnE_def]
  have hx_src : x ∈ (extChartAt I x).source := by
    rw [extChartAt_source (I := I)]; exact mem_chart_source H x
  rw [(extChartAt I x).left_inv hx_src]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma lieArm_chartGramOnE_center (g : SmoothRiemannianMetric I M) (x : M)
    (a b : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE (I := I) g x a b
        (extChartAt I x x) =
      DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) g x x a b := by
  rw [DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE_def]
  have hx_src : x ∈ (extChartAt I x).source := by
    rw [extChartAt_source (I := I)]; exact mem_chart_source H x
  rw [(extChartAt I x).left_inv hx_src]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma lieArm_chartInvGramMatrix_symm (g : SmoothRiemannianMetric I M) (x : M)
    (a b : Fin (Module.finrank ℝ E)) :
    chartInvGramMatrix (I := I) g x x a b = chartInvGramMatrix (I := I) g x x b a := by
  have hherm : (DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) g x x)⁻¹.IsHermitian :=
    (DifferentialGeometry.Integral.Measure.chartGramMatrix_isHermitian (I := I) g x x).inv
  have h := congrFun (congrFun hherm a) b
  rw [Matrix.conjTranspose_apply, star_trivial] at h
  exact h.symm

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma lieArm_gram_invGram_collapse (g : SmoothRiemannianMetric I M) (x : M)
    (l j : Fin (Module.finrank ℝ E)) :
    (∑ k : Fin (Module.finrank ℝ E),
        DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) g x x k j *
          chartInvGramMatrix (I := I) g x x k l) =
      if l = j then (1 : ℝ) else 0 := by
  classical
  have hx_base : x ∈ (trivializationAt E (TangentSpace I) x).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact mem_chart_source H x
  have hmul := DifferentialGeometry.Integral.DivergenceTheorem.chartInvGramMatrix_mul_chartGramMatrix (I := I) g x hx_base
  have h := congrFun (congrFun hmul l) j
  rw [Matrix.mul_apply, Matrix.one_apply] at h
  rw [show (∑ k : Fin (Module.finrank ℝ E),
      DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) g x x k j *
        chartInvGramMatrix (I := I) g x x k l) =
    ∑ k : Fin (Module.finrank ℝ E),
      chartInvGramMatrix (I := I) g x x l k *
        DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) g x x k j from
    Finset.sum_congr rfl (fun k _ => by
      rw [lieArm_chartInvGramMatrix_symm (I := I) g x k l]; ring)]
  rw [h]

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
private lemma lieArm_partialDeriv2_realizedGramDeriv_swap
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (m₁ m₂ a b : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) m₂
        (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) m₁
          (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x a b))
        (extChartAt I x x) =
      DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) m₁
        (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) m₂
          (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x a b))
        (extChartAt I x x) := by
  rw [partialDeriv2_realizedGramDeriv_eq_half_sum_euclidPartial2 (I := I) g₀ T T'
      hδ_lt hδ hδ'_lt hδ' x m₁ m₂ a b,
    partialDeriv2_realizedGramDeriv_eq_half_sum_euclidPartial2 (I := I) g₀ T T'
      hδ_lt hδ hδ'_lt hδ' x m₂ m₁ a b]
  rw [euclidPartial_swap_chartPushedRaw_tensorChartComponentRaw (I := I) g₀ (T - T') x m₂ m₁ a b, euclidPartial_swap_chartPushedRaw_tensorChartComponentRaw (I := I) g₀ (T - T') x m₂ m₁ b a]

open DifferentialGeometry.PDE.DeTurck.DeTurckLinearization (chartDeTurckCorrPrincipalSymbolExprRaw chartDeTurckCorrHessBlockRaw)
open DifferentialGeometry.Integral.DivergenceTheorem (partialDeriv chartGramOnE chartInvGramOnE)
open DifferentialGeometry.Integral.Measure (chartGramMatrix)

omit [CompactSpace M] [BoundarylessManifold I M] in
private lemma lieArm_P2_halfCollapse
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g₁ g_bg : SmoothRiemannianMetric I M) (x : M) (d e : Fin (Module.finrank ℝ E)) :
    (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g₁ x k e (extChartAt I x x) *
          ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g₁ x a b (extChartAt I x x) *
              chartDeTurckCorrHessBlockRaw (I := I) g₁ g_bg x
                (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x) d a b k
                (extChartAt I x x)) =
      ∑ k₁ : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k₁ l *
          (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) d
              (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) l
                (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x e k₁))
              (extChartAt I x x)
            - (1 / 2 : ℝ) *
              DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) d
                (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) e
                  (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l k₁))
                (extChartAt I x x)) := by
  classical
  set pd2 : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ := fun d' a' l' b' =>
    DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) d'
      (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) a'
        (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l' b'))
      (extChartAt I x x) with hpd2
  set CIM : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ := fun a b =>
    chartInvGramMatrix (I := I) g₁ x x a b with hCIM
  set CGM : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ := fun a b =>
    DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) g₁ x x a b with hCGM
  have hHB : ∀ k a b : Fin (Module.finrank ℝ E),
      chartDeTurckCorrHessBlockRaw (I := I) g₁ g_bg x
          (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x) d a b k
          (extChartAt I x x) =
        (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
          CIM k l * (pd2 d a l b + pd2 d b l a - pd2 d l a b) := by
    intro k a b
    rw [chartDeTurckCorrHessBlockRaw]
    refine congrArg (fun t : ℝ => (1 / 2 : ℝ) * t) ?_
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [lieArm_chartInvGramOnE_center (I := I) g₁ x k l]
  have hstep1 : (∑ k : Fin (Module.finrank ℝ E),
      chartGramOnE (I := I) g₁ x k e (extChartAt I x x) *
        ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g₁ x a b (extChartAt I x x) *
            chartDeTurckCorrHessBlockRaw (I := I) g₁ g_bg x
              (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x) d a b k
              (extChartAt I x x)) =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        CIM a b * ((1 / 2 : ℝ) *
          ((∑ k : Fin (Module.finrank ℝ E), CGM k e * CIM k l) *
            (pd2 d a l b + pd2 d b l a - pd2 d l a b))) := by
    rw [show (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g₁ x k e (extChartAt I x x) *
          ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g₁ x a b (extChartAt I x x) *
              chartDeTurckCorrHessBlockRaw (I := I) g₁ g_bg x
                (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x) d a b k
                (extChartAt I x x)) =
      ∑ k : Fin (Module.finrank ℝ E),
        CGM k e * ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          CIM a b * ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
            CIM k l * (pd2 d a l b + pd2 d b l a - pd2 d l a b)) from by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [lieArm_chartGramOnE_center (I := I) g₁ x k e]
      refine congrArg (fun t : ℝ => CGM k e * t) ?_
      refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
      rw [lieArm_chartInvGramOnE_center (I := I) g₁ x a b, hHB k a b]]
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun k _ => ?_))
    ring
  rw [hstep1]
  have hstep2 : ∀ a b : Fin (Module.finrank ℝ E),
      (∑ l : Fin (Module.finrank ℝ E),
        CIM a b * ((1 / 2 : ℝ) *
          ((∑ k : Fin (Module.finrank ℝ E), CGM k e * CIM k l) *
            (pd2 d a l b + pd2 d b l a - pd2 d l a b)))) =
      CIM a b * ((1 / 2 : ℝ) * (pd2 d a e b + pd2 d b e a - pd2 d e a b)) := by
    intro a b
    rw [Finset.sum_congr rfl (fun l _ => by
        rw [lieArm_gram_invGram_collapse (I := I) g₁ x l e] :
      ∀ l ∈ Finset.univ,
        CIM a b * ((1 / 2 : ℝ) *
          ((∑ k : Fin (Module.finrank ℝ E), CGM k e * CIM k l) *
            (pd2 d a l b + pd2 d b l a - pd2 d l a b))) =
        CIM a b * ((1 / 2 : ℝ) *
          ((if l = e then (1 : ℝ) else 0) *
            (pd2 d a l b + pd2 d b l a - pd2 d l a b))))]
    rw [Finset.sum_eq_single e]
    · rw [if_pos rfl, one_mul]
    · intro l _ hl
      rw [if_neg hl, zero_mul, mul_zero, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ e) h
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => hstep2 a b))]
  have hterm1 : (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
      CIM a b * ((1 / 2 : ℝ) * pd2 d a e b)) =
      ∑ k₁ : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        CIM k₁ l * ((1 / 2 : ℝ) * pd2 d l e k₁) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun l _ => ?_))
    rw [show CIM l k₁ = CIM k₁ l from lieArm_chartInvGramMatrix_symm (I := I) g₁ x l k₁]
  have hterm3 : (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
      CIM a b * ((1 / 2 : ℝ) * pd2 d e a b)) =
      ∑ k₁ : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        CIM k₁ l * ((1 / 2 : ℝ) * pd2 d e l k₁) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun l _ => ?_))
    rw [show CIM l k₁ = CIM k₁ l from lieArm_chartInvGramMatrix_symm (I := I) g₁ x l k₁]
  have hsplit : (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
      CIM a b * ((1 / 2 : ℝ) * (pd2 d a e b + pd2 d b e a - pd2 d e a b))) =
      (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        CIM a b * ((1 / 2 : ℝ) * pd2 d a e b))
      + (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        CIM a b * ((1 / 2 : ℝ) * pd2 d b e a))
      - (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        CIM a b * ((1 / 2 : ℝ) * pd2 d e a b)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    ring
  rw [hsplit, hterm1, hterm3]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun k₁ _ => ?_)
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  ring
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (deTurckLieArm2PrincipalCoeff deTurckLieArm2PrincipalCoeff_apply_eq cometricFinBasisTrace_eq_chartInvGram_bilin quadrilinearMapSlotBilinearAt unitModel4SlotBilin_apply)



def lieTopTail
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    (g₁ : SmoothRiemannianMetric I M) (x : M)
    (i j : Fin (Module.finrank ℝ E)) : ℝ :=
  ∑ k₁ : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
    chartInvGramMatrix (I := I) g₁ x x k₁ l *
      (arm2ReadoutCovDerivPair (I := I) (M := M) g₀
          (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![i, l, j, k₁]
        + arm2ReadoutCovDerivPair (I := I) (M := M) g₀
          (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![j, l, i, k₁]
        - arm2ReadoutCovDerivPair (I := I) (M := M) g₀
          (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![i, j, l, k₁])



omit [BoundarylessManifold I M] in
theorem lieTop_cov_eq_raw
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g₁ g_bg : SmoothRiemannianMetric I M) (x : M) (i j : Fin (Module.finrank ℝ E)) :
    unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 4 2
          (deTurckLieArm2PrincipalCoeff (I := I) g₀ g₁ g_bg)
          (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ (T - T')))) x
        ![(chartModelBasis E) i, (chartModelBasis E) j] =
      chartDeTurckCorrPrincipalSymbolExprRaw (I := I) g₁ g_bg x
          (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x) i j (extChartAt I x x)
        + lieTopTail (I := I) g₀ T T' g₁ x i j := by
  classical
  rw [lieTopTail]
  set pd2 : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ := fun d' a' l' b' =>
    DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) d'
      (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) a'
        (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l' b'))
      (extChartAt I x x) with hpd2
  set R4 : (Fin 4 → Fin (Module.finrank ℝ E)) → ℝ := fun Jdx =>
    arm2ReadoutCovDerivPair (I := I) (M := M) g₀
      (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x Jdx with hR4
  set CIM : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ := fun a b =>
    chartInvGramMatrix (I := I) g₁ x x a b with hCIM
  rw [lieArm2_appCc_value_invGram (I := I) g₀ g₁ g_bg
    (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x i j]
  have hU4 : ∀ a b c d : Fin (Module.finrank ℝ E),
      unitModel (I := I) (M := M) g₀ 4
          (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x
          ![chartModelBasis E a, chartModelBasis E b, chartModelBasis E c, chartModelBasis E d] =
        pd2 a b c d + R4 ![a, b, c, d] := fun a b c d =>
    lieArm_U4_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x a b c d
  rw [Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun l _ => by
      rw [hU4 i l j k₁, hU4 j l i k₁, hU4 i j l k₁] :
    ∀ l ∈ Finset.univ,
      chartInvGramMatrix (I := I) g₁ x x k₁ l *
        (unitModel (I := I) (M := M) g₀ 4
            (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x
            ![chartModelBasis E i, chartModelBasis E l, chartModelBasis E j, chartModelBasis E k₁]
          + unitModel (I := I) (M := M) g₀ 4
            (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x
            ![chartModelBasis E j, chartModelBasis E l, chartModelBasis E i, chartModelBasis E k₁]
          - unitModel (I := I) (M := M) g₀ 4
            (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x
            ![chartModelBasis E i, chartModelBasis E j, chartModelBasis E l, chartModelBasis E k₁]) =
      CIM k₁ l *
        ((pd2 i l j k₁ + R4 ![i, l, j, k₁])
          + (pd2 j l i k₁ + R4 ![j, l, i, k₁])
          - (pd2 i j l k₁ + R4 ![i, j, l, k₁]))))]
  have hsplit : (∑ k₁ : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
      CIM k₁ l *
        ((pd2 i l j k₁ + R4 ![i, l, j, k₁])
          + (pd2 j l i k₁ + R4 ![j, l, i, k₁])
          - (pd2 i j l k₁ + R4 ![i, j, l, k₁]))) =
      (∑ k₁ : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        CIM k₁ l * (pd2 i l j k₁ + pd2 j l i k₁ - pd2 i j l k₁))
      + (∑ k₁ : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        CIM k₁ l * (R4 ![i, l, j, k₁] + R4 ![j, l, i, k₁] - R4 ![i, j, l, k₁])) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k₁ _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    ring
  rw [hsplit]
  refine congrArg (fun t : ℝ => t + _) ?_
  rw [show chartDeTurckCorrPrincipalSymbolExprRaw (I := I) g₁ g_bg x
      (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x) i j (extChartAt I x x) =
    (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g₁ x k j (extChartAt I x x) *
          ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g₁ x a b (extChartAt I x x) *
              chartDeTurckCorrHessBlockRaw (I := I) g₁ g_bg x
                (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x) i a b k
                (extChartAt I x x)) +
    (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g₁ x i k (extChartAt I x x) *
          ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g₁ x a b (extChartAt I x x) *
              chartDeTurckCorrHessBlockRaw (I := I) g₁ g_bg x
                (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x) j a b k
                (extChartAt I x x)) from rfl]
  rw [Finset.sum_congr rfl (fun k _ => by
      rw [DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE_symm (I := I) g₁ x i k
        (extChartAt I x x)] :
    ∀ k ∈ Finset.univ,
      chartGramOnE (I := I) g₁ x i k (extChartAt I x x) *
          ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g₁ x a b (extChartAt I x x) *
              chartDeTurckCorrHessBlockRaw (I := I) g₁ g_bg x
                (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x) j a b k
                (extChartAt I x x) =
      chartGramOnE (I := I) g₁ x k i (extChartAt I x x) *
          ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g₁ x a b (extChartAt I x x) *
              chartDeTurckCorrHessBlockRaw (I := I) g₁ g_bg x
                (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x) j a b k
                (extChartAt I x x))]
  rw [lieArm_P2_halfCollapse (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' g₁ g_bg x i j,
    lieArm_P2_halfCollapse (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' g₁ g_bg x j i]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k₁ _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  simp only [hpd2]
  rw [lieArm_partialDeriv2_realizedGramDeriv_swap (I := I) g₀ T T'
    hδ_lt hδ hδ'_lt hδ' x i j l k₁]
  ring

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients
