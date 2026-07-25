import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartCoordinateExpansion.RealizedGramDerivChartEvaluation
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.DeTurckLieCoeffAppCcValue
import DifferentialGeometry.Analysis.Parabolic.DeTurckLinearization.LieDeTurckRemainderOrderSplit









noncomputable section

set_option linter.style.setOption false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000

open MeasureTheory Set Filter Topology Bundle Manifold Tensor0SBundle ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff Matrix

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]
  [SigmaCompactSpace M]
variable (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
variable {δ δ' : ℝ}

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
    rw [hroundtrip]]
  rw [iteratedCovGrad1_chartComponent_readout (I := I) g₀ h x (![a, b, c])]
  have hJ0 : (![a, b, c] : Fin (2 + 1) → Fin (Module.finrank ℝ E)) 0 = a := rfl
  have hJtail : Matrix.vecTail (![a, b, c] : Fin (2 + 1) → Fin (Module.finrank ℝ E)) =
      ![b, c] := by
    funext j; fin_cases j <;> rfl
  simp only [arm1ReadoutCovDeriv, hJ0, hJtail]



omit [BoundarylessManifold I M] in
theorem lieU3_readout (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (a b c : Fin (Module.finrank ℝ E)) :
    unitModel (I := I) (M := M) g₀ 3
        (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x
        ![chartModelBasis E a, chartModelBasis E b, chartModelBasis E c] =
      partialDeriv (E := E) a
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
    toEuclidean_extChartAt_mem_chartTargetEuclid
      (I := I) (M := M) x (mem_chart_source H x)
  have hround : extChartAt I x ((extChartAt I x).symm
      ((toEuclidean (E := E)).symm ((toEuclidean (E := E)) (extChartAt I x x)))) =
      extChartAt I x x := by
    rw [(toEuclidean (E := E)).symm_apply_apply]
    have htarget : extChartAt I x x ∈ (extChartAt I x).target :=
      (extChartAt I x).map_source
        (by rw [extChartAt_source (I := I)]; exact mem_chart_source H x)
    rw [(extChartAt I x).right_inv htarget]
  have h := partialDeriv_scalarOnE_eq_euclidPartial_local (I := I) (M := M)
    (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2
      (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![] ![b, c]) x a hYmem
  rw [hround] at h
  rw [← h]
  have hev1 := lieArm_scalarOnE_symmS_eventuallyEq_realizedGramDeriv (I := I) g₀ T T'
    hδ_lt hδ hδ'_lt hδ' x b c
  unfold partialDeriv
  rw [hev1.fderiv_eq]
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (arm2ReadoutCovDerivPair arm1ReadoutCovDeriv arm1ReadoutCovDeriv_center_eq arm2ReadoutCovDerivPair_center_eq partialDeriv_realizedGramDeriv_eq_half_sum_euclidPartial)
open DifferentialGeometry.Analysis.Sobolev.Chart (chartPushedRaw chartPushedRaw_apply_of_mem chartTargetEuclid chartTargetEuclid_isOpen)
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity (euclidPartial euclidPartial_def chartChristoffelEuclid chartChristoffelEuclid_def chartPushedRaw_tensorChartComponentRaw_contDiffOn)

omit [BoundarylessManifold I M] in
private lemma lieCorr0_raw_readout (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (c d : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw
        (I := I) (M := M) g₀ 0 2 (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![] ![c, d] x =
      realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x c d (extChartAt I x x) := by
  have hev := lieArm_scalarOnE_symmS_eventuallyEq_realizedGramDeriv (I := I) g₀ T T'
    hδ_lt hδ hδ'_lt hδ' x c d
  have hpt := hev.self_of_nhds
  rw [DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE_def] at hpt
  have hx_src : x ∈ (extChartAt I x).source := by
    rw [extChartAt_source (I := I)]; exact mem_chart_source H x
  rw [(extChartAt I x).left_inv hx_src] at hpt
  exact hpt


omit [BoundarylessManifold I M] in
theorem lieArm1_center (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (a b c : Fin (Module.finrank ℝ E)) :
    arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x
        ![a, b, c] =
      (- ∑ r : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g₀ x a b r (extChartAt I x x) *
            realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x r c (extChartAt I x x))
      + (- ∑ r : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g₀ x a c r (extChartAt I x x) *
            realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x b r
              (extChartAt I x x)) := by
  rw [arm1ReadoutCovDeriv_center_eq (I := I) (M := M) g₀
    (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x a b c]
  refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ + t₂) ?_ ?_
  · refine congrArg Neg.neg (Finset.sum_congr rfl (fun r _ => ?_))
    rw [lieCorr0_raw_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x r c]
  · refine congrArg Neg.neg (Finset.sum_congr rfl (fun r _ => ?_))
    rw [lieCorr0_raw_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x b r]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma lieCorr0_euclid_christoffel_bridge (g : SmoothRiemannianMetric I M) (x : M)
    (m a b r : Fin (Module.finrank ℝ E)) :
    euclidPartial (E := E) m
        (chartChristoffelEuclid (I := I) g x a b r)
        (toEuclidean (E := E) (extChartAt I x x)) =
      partialDeriv (E := E) m (chartChristoffel (I := I) g x a b r) (extChartAt I x x) := by
  classical
  have hy_int : extChartAt I x x ∈ interior ((extChartAt I x).target : Set E) :=
    DifferentialGeometry.Integral.DivergenceTheorem.extChartAt_target_subset_interior_of_boundaryless
      (I := I) x (mem_extChartAt_target x)
  have hdiff : DifferentiableAt ℝ (chartChristoffel (I := I) g x a b r) (extChartAt I x x) :=
    ((DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel_contDiffOn_interior
      (I := I) g x a b r).contDiffAt
      (isOpen_interior.mem_nhds hy_int)).differentiableAt (by simp)
  rw [euclidPartial_def, DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv]
  have hcomp : (chartChristoffelEuclid (I := I) g x a b r) =
      (chartChristoffel (I := I) g x a b r) ∘ (toEuclidean (E := E)).symm := rfl
  rw [hcomp]
  rw [fderiv_comp (toEuclidean (E := E) (extChartAt I x x))
    (by
      rw [(toEuclidean (E := E)).symm_apply_apply]
      exact hdiff)
    (toEuclidean (E := E)).symm.differentiableAt]
  rw [(toEuclidean (E := E)).symm.fderiv]
  rw [ContinuousLinearMap.comp_apply]
  rw [(toEuclidean (E := E)).symm_apply_apply]
  refine congrArg (fun t => fderiv ℝ (chartChristoffel (I := I) g x a b r)
    (extChartAt I x x) t) ?_
  rw [ContinuousLinearEquiv.coe_coe]
  rw [chartModelBasis_apply]

omit [BoundarylessManifold I M] in
private lemma lieCorr0_euclid_f_bridge (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (m r d : Fin (Module.finrank ℝ E)) :
    euclidPartial (E := E) m
        (chartPushedRaw I x
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw
            (I := I) (M := M) g₀ 0 2 (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![] ![r, d]))
        (toEuclidean (E := E) (extChartAt I x x)) =
      partialDeriv (E := E) m
        (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x r d)
        (extChartAt I x x) := by
  classical
  have hcenter : (toEuclidean (E := E)) (extChartAt I x x) ∈
      chartTargetEuclid (I := I) (M := M) x :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.toEuclidean_extChartAt_mem_chartTargetEuclid
      (I := I) (M := M) x (mem_chart_source H x)
  have hopen : IsOpen (chartTargetEuclid (I := I) (M := M) x) :=
    chartTargetEuclid_isOpen (I := I) (M := M) x
  have hev : (chartPushedRaw I x
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw
        (I := I) (M := M) g₀ 0 2 (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![] ![r, d]))
      =ᶠ[𝓝 ((toEuclidean (E := E)) (extChartAt I x x))]
      (fun y => (1 / 2 : ℝ) * chartPushedRaw I x
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw
            (I := I) (M := M) g₀ 0 2 (T - T') x ![] ![r, d]) y +
        (1 / 2 : ℝ) * chartPushedRaw I x
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw
            (I := I) (M := M) g₀ 0 2 (T - T') x ![] ![d, r]) y) := by
    filter_upwards [hopen.mem_nhds hcenter] with y hy
    rw [chartPushedRaw_apply_of_mem (I := I) (M := M) x _ hy,
      chartPushedRaw_apply_of_mem (I := I) (M := M) x _ hy,
      chartPushedRaw_apply_of_mem (I := I) (M := M) x _ hy]
    have hb : (extChartAt I x).symm ((toEuclidean (E := E)).symm y) ∈
        (chartAt H x).source := by
      obtain ⟨z, hz, rfl⟩ := hy
      rw [(toEuclidean (E := E)).symm_apply_apply, ← extChartAt_source (I := I)]
      exact (extChartAt I x).map_target hz
    rw [lieArm_symmS_rawComponent (I := I) (M := M) g₀ (T - T') x r d hb]
    ring
  rw [show euclidPartial (E := E) m
      (chartPushedRaw I x
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw
          (I := I) (M := M) g₀ 0 2 (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![] ![r, d]))
      (toEuclidean (E := E) (extChartAt I x x)) =
    euclidPartial (E := E) m
      (fun y => (1 / 2 : ℝ) * chartPushedRaw I x
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw
            (I := I) (M := M) g₀ 0 2 (T - T') x ![] ![r, d]) y +
        (1 / 2 : ℝ) * chartPushedRaw I x
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw
            (I := I) (M := M) g₀ 0 2 (T - T') x ![] ![d, r]) y)
      (toEuclidean (E := E) (extChartAt I x x)) from by
    rw [euclidPartial_def, euclidPartial_def, hev.fderiv_eq]]
  have hd1 : DifferentiableAt ℝ (chartPushedRaw I x
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw
        (I := I) (M := M) g₀ 0 2 (T - T') x ![] ![r, d]))
      (toEuclidean (E := E) (extChartAt I x x)) :=
    ((chartPushedRaw_tensorChartComponentRaw_contDiffOn (I := I) (M := M) g₀ 0 2
      (T - T') x ![] ![r, d]).contDiffAt (hopen.mem_nhds hcenter)).differentiableAt (by simp)
  have hd2 : DifferentiableAt ℝ (chartPushedRaw I x
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw
        (I := I) (M := M) g₀ 0 2 (T - T') x ![] ![d, r]))
      (toEuclidean (E := E) (extChartAt I x x)) :=
    ((chartPushedRaw_tensorChartComponentRaw_contDiffOn (I := I) (M := M) g₀ 0 2
      (T - T') x ![] ![d, r]).contDiffAt (hopen.mem_nhds hcenter)).differentiableAt (by simp)
  rw [euclidPartial_def]
  rw [fderiv_fun_add (hd1.const_mul (1 / 2 : ℝ)) (hd2.const_mul (1 / 2 : ℝ))]
  rw [ContinuousLinearMap.add_apply]
  rw [fderiv_const_mul hd1 (1 / 2 : ℝ), fderiv_const_mul hd2 (1 / 2 : ℝ)]
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply]
  rw [partialDeriv_realizedGramDeriv_eq_half_sum_euclidPartial (I := I) g₀ T T'
    hδ_lt hδ hδ'_lt hδ' x m r d]
  rw [euclidPartial_def, euclidPartial_def]
  simp only [smul_eq_mul]


omit [BoundarylessManifold I M] in
theorem lieR4_center (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (a b c d : Fin (Module.finrank ℝ E)) :
    arm2ReadoutCovDerivPair (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x
        ![a, b, c, d] =
      (((- ∑ r : Fin (Module.finrank ℝ E),
              partialDeriv (E := E) a (chartChristoffel (I := I) g₀ x c b r)
                  (extChartAt I x x) *
                realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x r d
                  (extChartAt I x x))
          + (- ∑ r : Fin (Module.finrank ℝ E),
              partialDeriv (E := E) a (chartChristoffel (I := I) g₀ x d b r)
                  (extChartAt I x x) *
                realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x c r
                  (extChartAt I x x)))
        + ((- ∑ r : Fin (Module.finrank ℝ E),
              chartChristoffel (I := I) g₀ x c b r (extChartAt I x x) *
                partialDeriv (E := E) a
                  (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x r d)
                  (extChartAt I x x))
          + (- ∑ r : Fin (Module.finrank ℝ E),
              chartChristoffel (I := I) g₀ x d b r (extChartAt I x x) *
                partialDeriv (E := E) a
                  (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x c r)
                  (extChartAt I x x))))
      + ((- ∑ r : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g₀ x a b r (extChartAt I x x) *
              (partialDeriv (E := E) r
                  (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x c d)
                  (extChartAt I x x)
                + ((- ∑ t : Fin (Module.finrank ℝ E),
                      chartChristoffel (I := I) g₀ x r c t (extChartAt I x x) *
                        realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x t d
                          (extChartAt I x x))
                  + (- ∑ t : Fin (Module.finrank ℝ E),
                      chartChristoffel (I := I) g₀ x r d t (extChartAt I x x) *
                        realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x c t
                          (extChartAt I x x)))))
        + ((- ∑ r : Fin (Module.finrank ℝ E),
              chartChristoffel (I := I) g₀ x a c r (extChartAt I x x) *
                (partialDeriv (E := E) b
                    (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x r d)
                    (extChartAt I x x)
                  + ((- ∑ t : Fin (Module.finrank ℝ E),
                        chartChristoffel (I := I) g₀ x b r t (extChartAt I x x) *
                          realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x t d
                            (extChartAt I x x))
                    + (- ∑ t : Fin (Module.finrank ℝ E),
                        chartChristoffel (I := I) g₀ x b d t (extChartAt I x x) *
                          realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x r t
                            (extChartAt I x x)))))
          + (- ∑ r : Fin (Module.finrank ℝ E),
              chartChristoffel (I := I) g₀ x a d r (extChartAt I x x) *
                (partialDeriv (E := E) b
                    (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x c r)
                    (extChartAt I x x)
                  + ((- ∑ t : Fin (Module.finrank ℝ E),
                        chartChristoffel (I := I) g₀ x b c t (extChartAt I x x) *
                          realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x t r
                            (extChartAt I x x))
                    + (- ∑ t : Fin (Module.finrank ℝ E),
                        chartChristoffel (I := I) g₀ x b r t (extChartAt I x x) *
                          realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x c t
                            (extChartAt I x x))))))) := by
  classical
  rw [arm2ReadoutCovDerivPair_center_eq (I := I) (M := M) g₀
    (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x a b c d]
  refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ + t₂) (congrArg₂ (fun t₁ t₂ : ℝ => t₁ + t₂) ?_ ?_)
    (congrArg₂ (fun t₁ t₂ : ℝ => t₁ + t₂) ?_ (congrArg₂ (fun t₁ t₂ : ℝ => t₁ + t₂) ?_ ?_))
  · refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ + t₂) ?_ ?_
    · refine congrArg Neg.neg (Finset.sum_congr rfl (fun r _ => ?_))
      rw [lieCorr0_euclid_christoffel_bridge (I := I) g₀ x a c b r,
        lieCorr0_raw_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x r d]
    · refine congrArg Neg.neg (Finset.sum_congr rfl (fun r _ => ?_))
      rw [lieCorr0_euclid_christoffel_bridge (I := I) g₀ x a d b r,
        lieCorr0_raw_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x c r]
  · refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ + t₂) ?_ ?_
    · refine congrArg Neg.neg (Finset.sum_congr rfl (fun r _ => ?_))
      rw [lieCorr0_euclid_f_bridge (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x a r d]
    · refine congrArg Neg.neg (Finset.sum_congr rfl (fun r _ => ?_))
      rw [lieCorr0_euclid_f_bridge (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x a c r]
  · refine congrArg Neg.neg (Finset.sum_congr rfl (fun r _ => ?_))
    refine congrArg (fun t : ℝ =>
      chartChristoffel (I := I) g₀ x a b r (extChartAt I x x) * t) ?_
    refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ + t₂) ?_ ?_
    · rw [lieCorr0_euclid_f_bridge (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x r c d]
    · refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ + t₂) ?_ ?_
      · refine congrArg Neg.neg (Finset.sum_congr rfl (fun t _ => ?_))
        rw [lieCorr0_raw_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x t d]
      · refine congrArg Neg.neg (Finset.sum_congr rfl (fun t _ => ?_))
        rw [lieCorr0_raw_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x c t]
  · refine congrArg Neg.neg (Finset.sum_congr rfl (fun r _ => ?_))
    refine congrArg (fun t : ℝ =>
      chartChristoffel (I := I) g₀ x a c r (extChartAt I x x) * t) ?_
    refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ + t₂) ?_ ?_
    · rw [lieCorr0_euclid_f_bridge (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x b r d]
    · refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ + t₂) ?_ ?_
      · refine congrArg Neg.neg (Finset.sum_congr rfl (fun t _ => ?_))
        rw [lieCorr0_raw_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x t d]
      · refine congrArg Neg.neg (Finset.sum_congr rfl (fun t _ => ?_))
        rw [lieCorr0_raw_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x r t]
  · refine congrArg Neg.neg (Finset.sum_congr rfl (fun r _ => ?_))
    refine congrArg (fun t : ℝ =>
      chartChristoffel (I := I) g₀ x a d r (extChartAt I x x) * t) ?_
    refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ + t₂) ?_ ?_
    · rw [lieCorr0_euclid_f_bridge (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x b c r]
    · refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ + t₂) ?_ ?_
      · refine congrArg Neg.neg (Finset.sum_congr rfl (fun t _ => ?_))
        rw [lieCorr0_raw_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x t r]
      · refine congrArg Neg.neg (Finset.sum_congr rfl (fun t _ => ?_))
        rw [lieCorr0_raw_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x c t]

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
