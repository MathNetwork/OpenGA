import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.RealizedJet2CovGradBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartFiberTrivialisationOpNorm.TensorRSChartFiberToModelOpNorm
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChartComponent.ComponentL2BoundUniform
import DifferentialGeometry.Analysis.Elliptic.TensorRegularity.CovDeriv.ComponentSecondFormula































noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral
namespace MetricRealization

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace
  Bundle.continuousMultilinearMap.mixed_instNormedAddCommGroup
  Bundle.continuousMultilinearMap.mixed_instNormedSpace in










omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
theorem tensorChartComponentRaw_abs_le_riemannianFibreNorm
    (g_bg : SmoothRiemannianMetric I M) (s : ℕ) (α : M)
    {K : Set M} (hK : IsCompact K) (hKsub : K ⊆ (chartAt H α).source) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 s I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g_bg 0 s
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : SmoothCcTensor g_bg 0 s) (b : M), b ∈ K →
      ∀ (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        |tensorChartComponentRaw (I := I) (M := M) g_bg 0 s T α
            (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) Jdx b| ≤
          C * ‖T.toSection b‖ := by
  classical
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g_bg 0 s
  obtain ⟨Cop, hCop_pos, hCop_bound⟩ :=
    tensorRSChartFiberToModel_opNorm_isBounded_on_compact_unconditional
      (I := I) (M := M) g_bg 0 s α hK hKsub
  set Cproj : ℝ := chartComponentProjectionUniformBound (E := E) 0 s with hCproj_def
  have hCproj_nn : 0 ≤ Cproj := chartComponentProjectionUniformBound_nonneg (E := E) 0 s
  refine ⟨Cproj * Cop, mul_nonneg hCproj_nn (le_of_lt hCop_pos), ?_⟩
  intro T b hb Jdx
  set v : TensorRSModel 0 s ℝ E :=
    tensorTrivProj (I := I) (M := M) g_bg 0 s T α b with hv_def
  rw [tensorChartComponentRaw_def]
  have h_proj_le :
      |tensorChartComponentProjection (E := E) 0 s
          (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) Jdx v| ≤
        ‖tensorChartComponentProjection (E := E) 0 s
            (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) Jdx‖ * ‖v‖ := by
    have h := (tensorChartComponentProjection (E := E) 0 s
        (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) Jdx).le_opNorm v
    simpa [Real.norm_eq_abs] using h
  have h_proj_norm_le :
      ‖tensorChartComponentProjection (E := E) 0 s
          (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) Jdx‖ ≤ Cproj :=
    tensorChartComponentProjection_norm_le_uniform (E := E) 0 s _ Jdx
  have h_v_le : ‖v‖ ≤ Cop * ‖T.toSection b‖ := by
    rw [hv_def]
    exact hCop_bound b hb (T.toSection b)
  calc |tensorChartComponentProjection (E := E) 0 s
            (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) Jdx v|
      ≤ ‖tensorChartComponentProjection (E := E) 0 s
            (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) Jdx‖ * ‖v‖ := h_proj_le
    _ ≤ Cproj * ‖v‖ :=
        mul_le_mul_of_nonneg_right h_proj_norm_le (norm_nonneg _)
    _ ≤ Cproj * (Cop * ‖T.toSection b‖) :=
        mul_le_mul_of_nonneg_left h_v_le hCproj_nn
    _ = Cproj * Cop * ‖T.toSection b‖ := by ring





omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma chartFrameBasisModel_zero_eq_constOfIsEmpty (α x : M) :
    chartFrameBasisModel (I := I) (M := M) α x 0
        (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) =
      ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ) := by
  refine ContinuousMultilinearMap.ext ?_
  intro v
  rw [chartFrameBasisModel_apply]
  simp






omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem ccTensorBilin_chartBasisVecFiber_eq_tensorChartComponentRaw
    (g_bg : SmoothRiemannianMetric I M) (S : SmoothCcTensor g_bg 0 2) (α : M) {x : M}
    (hx : x ∈ (chartAt H α).source) (l b : Fin (Module.finrank ℝ E)) :
    smoothCcTensorBilinForm (I := I) g_bg S x
        (chartBasisVecFiber (I := I) α l x) (chartBasisVecFiber (I := I) α b x) =
      tensorChartComponentRaw (I := I) (M := M) g_bg 0 2 S α
        (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E)))
        ![l, b] x := by
  classical
  rw [tensorChartComponentRaw_eq_chartFrame (I := I) (M := M) g_bg 0 2 S α hx
    (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) ![l, b]]
  rw [chartFrameBasisModel_zero_eq_constOfIsEmpty (I := I) (M := M) α x]
  rw [ccTensorBilin_apply, ccTensorModel, ccTensorMultilinear_apply]
  change (Tensor0SBundle.Tensor0SSpace.toModel
      (S.toSection x (ContinuousMultilinearMap.constOfIsEmpty ℝ
        (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))))
      ![chartBasisVecFiber (I := I) α l x, chartBasisVecFiber (I := I) α b x] =
    (S.toSection x (ContinuousMultilinearMap.constOfIsEmpty ℝ
        (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)))
      (fun j : Fin 2 => chartBasisVecFiber (I := I) α (![l, b] j) x)
  rw [Tensor0SBundle.Tensor0SSpace.toModel,
    Tensor0SBundle.tensor0SSpace_continuousLinearEquiv_apply]
  congr 1
  funext j
  fin_cases j <;> rfl






omit [BoundarylessManifold I M] in
theorem reprDiffChartCompOnE_eq_symm_tensorChartComponentRaw
    (g_bg : SmoothRiemannianMetric I M) {σ : ℝ}
    {u₁ u₂ : tensorHs (I := I) (M := M) g_bg 0 2 σ}
    (hu₁ : isRealizableMetricPerturbationAt (I := I) g_bg u₁) (hu₂ : isRealizableMetricPerturbationAt (I := I) g_bg u₂)
    (α : M) (l b : Fin (Module.finrank ℝ E)) {y : E}
    (hy : (extChartAt I α).symm y ∈ (chartAt H α).source) :
    reprDiffChartCompOnE (I := I) g_bg hu₁ hu₂ α l b y =
      (1 / 2 : ℝ) *
        (tensorChartComponentRaw (I := I) (M := M) g_bg 0 2
            (realizableRepr (I := I) g_bg hu₁ - realizableRepr (I := I) g_bg hu₂) α
            (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) ![l, b]
            ((extChartAt I α).symm y) +
          tensorChartComponentRaw (I := I) (M := M) g_bg 0 2
            (realizableRepr (I := I) g_bg hu₁ - realizableRepr (I := I) g_bg hu₂) α
            (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) ![b, l]
            ((extChartAt I α).symm y)) := by
  classical
  set S : SmoothCcTensor g_bg 0 2 :=
    realizableRepr (I := I) g_bg hu₁ - realizableRepr (I := I) g_bg hu₂ with hS_def
  rw [reprDiffChartCompOnE, ccTensorBilinSymm_apply]
  rw [ccTensorBilin_chartBasisVecFiber_eq_tensorChartComponentRaw (I := I) g_bg S α hy l b,
    ccTensorBilin_chartBasisVecFiber_eq_tensorChartComponentRaw (I := I) g_bg S α hy b l]




omit [NeZero (Module.finrank ℝ E)] in
theorem partialDeriv_eq_euclidPartial_comp_toEuclidean
    (a : Fin (Module.finrank ℝ E)) (f : E → ℝ) (y : E) :
    partialDeriv (E := E) a f y =
      euclidPartial (E := E) a (f ∘ (toEuclidean (E := E)).symm) (toEuclidean (E := E) y) := by
  rw [euclidPartial_def, partialDeriv]
  rw [(toEuclidean (E := E)).symm.comp_right_fderiv
    (f := f) (x := toEuclidean (E := E) y)]
  rw [ContinuousLinearMap.comp_apply]
  rw [show (toEuclidean (E := E)).symm.toContinuousLinearMap
      (EuclideanSpace.single a (1 : ℝ)) = (chartModelBasis E) a from by
    rw [chartModelBasis_apply]; rfl]
  rw [show (toEuclidean (E := E)).symm (toEuclidean (E := E) y) = y from by simp]




omit [NeZero (Module.finrank ℝ E)] in
theorem partialDeriv_comp_toEuclidean_symm_eq_euclidPartial
    (a : Fin (Module.finrank ℝ E)) (f : E → ℝ) :
    (partialDeriv (E := E) a f) ∘ (toEuclidean (E := E)).symm =
      euclidPartial (E := E) a (f ∘ (toEuclidean (E := E)).symm) := by
  funext z
  rw [Function.comp_apply,
    partialDeriv_eq_euclidPartial_comp_toEuclidean (E := E) a f
      ((toEuclidean (E := E)).symm z)]
  rw [show toEuclidean (E := E) ((toEuclidean (E := E)).symm z) = z from by simp]





omit [NeZero (Module.finrank ℝ E)] in
theorem partialDeriv2_eq_euclidPartial2_comp_toEuclidean
    (c a : Fin (Module.finrank ℝ E)) (f : E → ℝ) (y : E) :
    partialDeriv (E := E) c (partialDeriv (E := E) a f) y =
      euclidPartial (E := E) c
        (euclidPartial (E := E) a (f ∘ (toEuclidean (E := E)).symm))
        (toEuclidean (E := E) y) := by
  rw [partialDeriv_eq_euclidPartial_comp_toEuclidean (E := E) c (partialDeriv (E := E) a f) y]
  rw [partialDeriv_comp_toEuclidean_symm_eq_euclidPartial (E := E) a f]





omit [BoundarylessManifold I M] in
theorem reprDiffChartCompOnE_comp_toEuclidean_symm_eqOn
    (g_bg : SmoothRiemannianMetric I M) {σ : ℝ}
    {u₁ u₂ : tensorHs (I := I) (M := M) g_bg 0 2 σ}
    (hu₁ : isRealizableMetricPerturbationAt (I := I) g_bg u₁) (hu₂ : isRealizableMetricPerturbationAt (I := I) g_bg u₂)
    (α : M) (l b : Fin (Module.finrank ℝ E)) :
    Set.EqOn
      (reprDiffChartCompOnE (I := I) g_bg hu₁ hu₂ α l b ∘ (toEuclidean (E := E)).symm)
      (fun y' => (1 / 2 : ℝ) *
        (chartPushedRaw I α
            (tensorChartComponentRaw (I := I) (M := M) g_bg 0 2
              (realizableRepr (I := I) g_bg hu₁ - realizableRepr (I := I) g_bg hu₂) α
              (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) ![l, b]) y'
          + chartPushedRaw I α
            (tensorChartComponentRaw (I := I) (M := M) g_bg 0 2
              (realizableRepr (I := I) g_bg hu₁ - realizableRepr (I := I) g_bg hu₂) α
              (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) ![b, l]) y'))
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  intro y' hy'
  set S : SmoothCcTensor g_bg 0 2 :=
    realizableRepr (I := I) g_bg hu₁ - realizableRepr (I := I) g_bg hu₂ with hS_def
  have hb_src : (extChartAt I α).symm ((toEuclidean (E := E)).symm y') ∈ (chartAt H α).source :=
    symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) α hy'
  simp only []
  rw [Function.comp_apply,
    reprDiffChartCompOnE_eq_symm_tensorChartComponentRaw (I := I) g_bg hu₁ hu₂ α l b
      (y := (toEuclidean (E := E)).symm y') hb_src]
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy',
    chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy']






omit [BoundarylessManifold I M] in
theorem euclidPartial_chartPushedRaw_eq_covGrad_sub_lowerOrder
    (g_bg : SmoothRiemannianMetric I M) (S : SmoothCcTensor g_bg 0 2) (α : M)
    (a l b : Fin (Module.finrank ℝ E)) {y' : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy' : y' ∈ chartTargetEuclid (I := I) (M := M) α) :
    euclidPartial (E := E) a
        (chartPushedRaw I α
          (tensorChartComponentRaw (I := I) (M := M) g_bg 0 2 S α
            (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) ![l, b])) y' =
      tensorChartComponentRaw (I := I) (M := M) g_bg 0 (2 + 1)
          (covGrad (I := I) (M := M) g_bg 0 2 S) α
          (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) ![a, l, b]
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y'))
        - covDerivLowerOrderTerm (I := I) (M := M) g_bg 0 2 S α a
            (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) ![l, b] y' := by
  classical
  have hJ0 : (![a, l, b] : Fin 3 → Fin (Module.finrank ℝ E)) 0 = a := rfl
  have hJtail : Matrix.vecTail (![a, l, b] : Fin 3 → Fin (Module.finrank ℝ E)) = ![l, b] := by
    funext j; fin_cases j <;> rfl
  have hform := tensorChartComponentRaw_covGrad (I := I) (M := M) g_bg 0 2 S α
    (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) ![a, l, b] hy'
  rw [hJ0, hJtail] at hform
  rw [hform]
  ring



omit [BoundarylessManifold I M] in
omit [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
theorem chartPushedRaw_tensorChartComponentRaw_differentiableAt
    (g_bg : SmoothRiemannianMetric I M) (s : ℕ)
    (S : SmoothCcTensor g_bg 0 s) (α : M)
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y' : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy' : y' ∈ chartTargetEuclid (I := I) (M := M) α) :
    DifferentiableAt ℝ
      (chartPushedRaw I α
        (tensorChartComponentRaw (I := I) (M := M) g_bg 0 s S α
          (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) Jdx)) y' := by
  have hcd := chartPushedRaw_tensorChartComponentRaw_contDiffOn (I := I) (M := M) g_bg 0 s S α
    (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) Jdx
  have hopen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  exact (hcd.contDiffAt (hopen.mem_nhds hy')).differentiableAt (by simp)


omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem toEuclidean_mem_chartTargetEuclid_of_mem_interior
    (α : M) {y : E} (hy : y ∈ interior ((extChartAt I α).target : Set E)) :
    toEuclidean (E := E) y ∈ chartTargetEuclid (I := I) (M := M) α :=
  ⟨y, interior_subset hy, rfl⟩







omit [BoundarylessManifold I M] in
theorem partialDeriv_reprDiffChartCompOnE_eq_covGrad_sub_lowerOrder
    (g_bg : SmoothRiemannianMetric I M) {σ : ℝ}
    {u₁ u₂ : tensorHs (I := I) (M := M) g_bg 0 2 σ}
    (hu₁ : isRealizableMetricPerturbationAt (I := I) g_bg u₁) (hu₂ : isRealizableMetricPerturbationAt (I := I) g_bg u₂)
    (α : M) (a l b : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior ((extChartAt I α).target : Set E)) :
    partialDeriv (E := E) a (reprDiffChartCompOnE (I := I) g_bg hu₁ hu₂ α l b) y =
      (1 / 2 : ℝ) *
        ((tensorChartComponentRaw (I := I) (M := M) g_bg 0 (2 + 1)
              (covGrad (I := I) (M := M) g_bg 0 2
                (realizableRepr (I := I) g_bg hu₁ - realizableRepr (I := I) g_bg hu₂)) α
              (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) ![a, l, b]
              ((extChartAt I α).symm y)
            - covDerivLowerOrderTerm (I := I) (M := M) g_bg 0 2
                (realizableRepr (I := I) g_bg hu₁ - realizableRepr (I := I) g_bg hu₂) α a
                (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) ![l, b]
                (toEuclidean (E := E) y))
          + (tensorChartComponentRaw (I := I) (M := M) g_bg 0 (2 + 1)
              (covGrad (I := I) (M := M) g_bg 0 2
                (realizableRepr (I := I) g_bg hu₁ - realizableRepr (I := I) g_bg hu₂)) α
              (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) ![a, b, l]
              ((extChartAt I α).symm y)
            - covDerivLowerOrderTerm (I := I) (M := M) g_bg 0 2
                (realizableRepr (I := I) g_bg hu₁ - realizableRepr (I := I) g_bg hu₂) α a
                (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) ![b, l]
                (toEuclidean (E := E) y))) := by
  classical
  set S : SmoothCcTensor g_bg 0 2 :=
    realizableRepr (I := I) g_bg hu₁ - realizableRepr (I := I) g_bg hu₂ with hS_def
  set ys : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) := toEuclidean (E := E) y with hys_def
  have hys_mem : ys ∈ chartTargetEuclid (I := I) (M := M) α :=
    toEuclidean_mem_chartTargetEuclid_of_mem_interior (I := I) (M := M) α hy
  have hopen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  set Flb : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
    chartPushedRaw I α
      (tensorChartComponentRaw (I := I) (M := M) g_bg 0 2 S α
        (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) ![l, b]) with hFlb_def
  set Fbl : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
    chartPushedRaw I α
      (tensorChartComponentRaw (I := I) (M := M) g_bg 0 2 S α
        (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) ![b, l]) with hFbl_def
  rw [partialDeriv_eq_euclidPartial_comp_toEuclidean (E := E) a
    (reprDiffChartCompOnE (I := I) g_bg hu₁ hu₂ α l b) y]
  rw [← hys_def]
  have hevt : (reprDiffChartCompOnE (I := I) g_bg hu₁ hu₂ α l b ∘ (toEuclidean (E := E)).symm)
      =ᶠ[nhds ys] (fun y' => (1 / 2 : ℝ) * (Flb y' + Fbl y')) := by
    refine Filter.eventuallyEq_iff_exists_mem.mpr
      ⟨chartTargetEuclid (I := I) (M := M) α, hopen.mem_nhds hys_mem, ?_⟩
    intro z hz
    have h := reprDiffChartCompOnE_comp_toEuclidean_symm_eqOn (I := I) g_bg hu₁ hu₂ α l b hz
    rw [hFlb_def, hFbl_def]
    exact h
  rw [euclidPartial_def, hevt.fderiv_eq]
  have hdiff_lb : DifferentiableAt ℝ Flb ys :=
    chartPushedRaw_tensorChartComponentRaw_differentiableAt (I := I) g_bg 2 S α ![l, b] hys_mem
  have hdiff_bl : DifferentiableAt ℝ Fbl ys :=
    chartPushedRaw_tensorChartComponentRaw_differentiableAt (I := I) g_bg 2 S α ![b, l] hys_mem
  rw [show (fun y' => (1 / 2 : ℝ) * (Flb y' + Fbl y')) =
      (1 / 2 : ℝ) • (Flb + Fbl) from by
        funext y'; simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]]
  rw [fderiv_const_smul (hdiff_lb.add hdiff_bl),
    fderiv_add hdiff_lb hdiff_bl]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, smul_eq_mul]
  rw [show fderiv ℝ Flb ys (EuclideanSpace.single a 1) = euclidPartial (E := E) a Flb ys from rfl,
    show fderiv ℝ Fbl ys (EuclideanSpace.single a 1) = euclidPartial (E := E) a Fbl ys from rfl]
  rw [hFlb_def, hFbl_def, hys_def,
    euclidPartial_chartPushedRaw_eq_covGrad_sub_lowerOrder (I := I) g_bg S α a l b
      (by rw [← hys_def]; exact hys_mem),
    euclidPartial_chartPushedRaw_eq_covGrad_sub_lowerOrder (I := I) g_bg S α a b l
      (by rw [← hys_def]; exact hys_mem)]
  rw [show (toEuclidean (E := E)).symm ys = y from by rw [hys_def]; simp]



omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem chartPreimage_image_isCompact_subset_chartSource
    (α : M) {K_eucl : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))}
    (hK : IsCompact K_eucl) (hKsub : K_eucl ⊆ chartTargetEuclid (I := I) (M := M) α) :
    IsCompact ((fun y' => (extChartAt I α).symm ((toEuclidean (E := E)).symm y')) '' K_eucl) ∧
      (fun y' => (extChartAt I α).symm ((toEuclidean (E := E)).symm y')) '' K_eucl ⊆
        (chartAt H α).source := by
  classical
  constructor
  · have hcont_toE : Continuous (fun y' : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
        (toEuclidean (E := E)).symm y') := (toEuclidean (E := E)).symm.continuous
    have hcont_symm : ContinuousOn (extChartAt I α).symm (extChartAt I α).target :=
      continuousOn_extChartAt_symm α
    have hmaps : Set.MapsTo (fun y' : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
        (toEuclidean (E := E)).symm y') K_eucl (extChartAt I α).target := by
      intro y' hy'
      exact Analysis.Laplacian.MetricExtension.toEuclidean_symm_mem_target (I := I)
        (hKsub hy')
    have hcont : ContinuousOn
        (fun y' => (extChartAt I α).symm ((toEuclidean (E := E)).symm y')) K_eucl :=
      (hcont_symm.comp hcont_toE.continuousOn hmaps)
    exact hK.image_of_continuousOn hcont
  · intro x hx
    obtain ⟨y', hy'_mem, hy'_eq⟩ := hx
    rw [← hy'_eq]
    exact symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) α (hKsub hy'_mem)

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace
  Bundle.continuousMultilinearMap.mixed_instNormedAddCommGroup
  Bundle.continuousMultilinearMap.mixed_instNormedSpace in








omit [CompactSpace M] [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
theorem covDerivLowerOrderTerm_abs_le_riemannianFibreNorm
    (g_bg : SmoothRiemannianMetric I M) (s : ℕ) (α : M)
    {K_eucl : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))}
    (hK : IsCompact K_eucl) (hKsub : K_eucl ⊆ chartTargetEuclid (I := I) (M := M) α) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 s I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g_bg 0 s
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : SmoothCcTensor g_bg 0 s)
      (m : Fin (Module.finrank ℝ E)) (Jdx : Fin s → Fin (Module.finrank ℝ E))
      (y' : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))), y' ∈ K_eucl →
        |covDerivLowerOrderTerm (I := I) (M := M) g_bg 0 s T α m
            (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) Jdx y'| ≤
          C * ‖T.toSection ((extChartAt I α).symm ((toEuclidean (E := E)).symm y'))‖ := by
  classical
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g_bg 0 s
  obtain ⟨hImg_cpt, hImg_sub⟩ :=
    chartPreimage_image_isCompact_subset_chartSource (I := I) (M := M) α hK hKsub
  obtain ⟨Craw, hCraw_nn, hCraw_bd⟩ :=
    tensorChartComponentRaw_abs_le_riemannianFibreNorm (I := I) g_bg s α hImg_cpt hImg_sub
  have h_coeff_bound : ∀ (mIJ : (Fin (Module.finrank ℝ E)) ×
        ((Fin 0 → Fin (Module.finrank ℝ E)) × (Fin s → Fin (Module.finrank ℝ E)) ×
          (Fin s → Fin (Module.finrank ℝ E)))),
      ∃ Cc : ℝ, 0 ≤ Cc ∧ ∀ y' ∈ K_eucl,
        |covDerivLowerOrderCoeff (I := I) (M := M) g_bg 0 s α mIJ.1
            (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) mIJ.2.1 mIJ.2.2.1 mIJ.2.2.2 y'|
          ≤ Cc := by
    rintro ⟨m, Idx', Jdx, Jdx'⟩
    have hcd := covDerivLowerOrderCoeff_contDiffOn (I := I) (M := M) g_bg 0 s α m
      (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) Idx' Jdx Jdx'
    have hcont : ContinuousOn
        (covDerivLowerOrderCoeff (I := I) (M := M) g_bg 0 s α m
          (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) Idx' Jdx Jdx') K_eucl :=
      (hcd.continuousOn).mono hKsub
    obtain ⟨Cc, hCc⟩ := hK.exists_bound_of_continuousOn hcont
    refine ⟨max Cc 0, le_max_right _ _, fun y' hy' => ?_⟩
    have := hCc y' hy'
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  choose Cc hCc_nn hCc_bd using h_coeff_bound
  set Ccoeff : ℝ := (Finset.univ.sup' Finset.univ_nonempty Cc) with hCcoeff_def
  have hCcoeff_ge : ∀ q, Cc q ≤ Ccoeff := fun q => Finset.le_sup' Cc (Finset.mem_univ q)
  have hCcoeff_nn : 0 ≤ Ccoeff :=
    le_trans (hCc_nn (Classical.arbitrary _)) (hCcoeff_ge (Classical.arbitrary _))
  set Npairs : ℝ := (Fintype.card ((Fin 0 → Fin (Module.finrank ℝ E)) ×
      (Fin s → Fin (Module.finrank ℝ E))) : ℝ) with hNpairs_def
  have hNpairs_nn : 0 ≤ Npairs := by rw [hNpairs_def]; positivity
  refine ⟨Npairs * (Ccoeff * Craw), by positivity, ?_⟩
  intro T m Jdx y' hy'
  set b₀ : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y') with hb₀_def
  have hb₀_img : b₀ ∈ (fun y'' => (extChartAt I α).symm ((toEuclidean (E := E)).symm y'')) ''
      K_eucl := ⟨y', hy', rfl⟩
  set N : ℝ := ‖T.toSection b₀‖ with hN_def
  have hN_nn : 0 ≤ N := norm_nonneg _
  rw [covDerivLowerOrderTerm_def]
  have h_term : ∀ p : (Fin 0 → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)),
      |covDerivLowerOrderCoeff (I := I) (M := M) g_bg 0 s α m
            (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) p.1 Jdx p.2 y' *
          tensorChartComponentRaw (I := I) (M := M) g_bg 0 s T α p.1 p.2 b₀|
        ≤ Ccoeff * (Craw * N) := by
    intro p
    rw [abs_mul]
    have hp1 : p.1 = (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) :=
      Subsingleton.elim _ _
    have h_coeff : |covDerivLowerOrderCoeff (I := I) (M := M) g_bg 0 s α m
          (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) p.1 Jdx p.2 y'| ≤ Ccoeff :=
      (hCc_bd (m, p.1, Jdx, p.2) y' hy').trans (hCcoeff_ge _)
    have h_raw : |tensorChartComponentRaw (I := I) (M := M) g_bg 0 s T α p.1 p.2 b₀| ≤
        Craw * N := by
      rw [hp1]; exact hCraw_bd T b₀ hb₀_img p.2
    exact mul_le_mul h_coeff h_raw (abs_nonneg _) hCcoeff_nn
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum (fun p _ => h_term p)).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, ← hNpairs_def]
  ring_nf
  rfl



omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem extChartAt_symm_image_isCompact_subset_chartSource
    (α : M) {K : Set E} (hK : IsCompact K)
    (hKsub : K ⊆ interior ((extChartAt I α).target : Set E)) :
    IsCompact ((extChartAt I α).symm '' K) ∧
      (extChartAt I α).symm '' K ⊆ (chartAt H α).source := by
  classical
  have hKtgt : K ⊆ (extChartAt I α).target := fun x hx => interior_subset (hKsub hx)
  constructor
  · have hcont : ContinuousOn (extChartAt I α).symm (extChartAt I α).target :=
      continuousOn_extChartAt_symm α
    exact hK.image_of_continuousOn (hcont.mono hKtgt)
  · intro x hx
    obtain ⟨y, hy_mem, hy_eq⟩ := hx
    rw [← hy_eq]
    have hsrc : (extChartAt I α).symm y ∈ (extChartAt I α).source :=
      (extChartAt I α).map_target (hKtgt hy_mem)
    rwa [extChartAt_source] at hsrc


omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem euclidPartial_congr_of_eqOn_isOpen
    (a : Fin (Module.finrank ℝ E))
    {f h : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ}
    {U : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))}
    (hU : IsOpen U) (heq : Set.EqOn f h U) :
    Set.EqOn (euclidPartial (E := E) a f) (euclidPartial (E := E) a h) U := by
  intro z hz
  rw [euclidPartial_def, euclidPartial_def]
  rw [(heq.eventuallyEq_of_mem (hU.mem_nhds hz)).fderiv_eq]





omit [BoundarylessManifold I M] in
theorem euclidPartial_chartPushedRaw_general_eq_covGrad_sub_lowerOrder
    (g_bg : SmoothRiemannianMetric I M) (s : ℕ)
    (T : SmoothCcTensor g_bg 0 s) (α : M)
    (m : Fin (Module.finrank ℝ E)) (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y' : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy' : y' ∈ chartTargetEuclid (I := I) (M := M) α) :
    euclidPartial (E := E) m
        (chartPushedRaw I α
          (tensorChartComponentRaw (I := I) (M := M) g_bg 0 s T α
            (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) Jdx)) y' =
      tensorChartComponentRaw (I := I) (M := M) g_bg 0 (s + 1)
          (covGrad (I := I) (M := M) g_bg 0 s T) α
          (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) (Fin.cons m Jdx)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y'))
        - covDerivLowerOrderTerm (I := I) (M := M) g_bg 0 s T α m
            (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) Jdx y' := by
  classical
  have hJ0 : (Fin.cons m Jdx : Fin (s + 1) → Fin (Module.finrank ℝ E)) 0 = m := by
    rw [Fin.cons_zero]
  have hJtail : Matrix.vecTail (Fin.cons m Jdx : Fin (s + 1) → Fin (Module.finrank ℝ E)) = Jdx := by
    funext j
    rw [Matrix.vecTail, Function.comp_apply, Fin.cons_succ]
  have hform := tensorChartComponentRaw_covGrad (I := I) (M := M) g_bg 0 s T α
    (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) (Fin.cons m Jdx) hy'
  rw [hJ0, hJtail] at hform
  rw [hform]
  ring




omit [BoundarylessManifold I M] in
theorem covDerivComponentEuclid_eqOn_rawComponent_covGrad
    (g_bg : SmoothRiemannianMetric I M) (s : ℕ)
    (T : SmoothCcTensor g_bg 0 s) (α : M)
    (m : Fin (Module.finrank ℝ E)) (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    Set.EqOn
      (covDerivComponentEuclid (I := I) (M := M) g_bg 0 s α T m
        (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) Jdx)
      (fun y' => tensorChartComponentRaw (I := I) (M := M) g_bg 0 (s + 1)
        (covGrad (I := I) (M := M) g_bg 0 s T) α
        (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) (Fin.cons m Jdx)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y')))
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  intro y' hy'
  simp only []
  rw [covDerivComponentEuclid_eqOn (I := I) (M := M) g_bg 0 s α T m
    (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) Jdx hy']
  have hJ0 : (Fin.cons m Jdx : Fin (s + 1) → Fin (Module.finrank ℝ E)) 0 = m := by
    rw [Fin.cons_zero]
  have hJtail : Matrix.vecTail (Fin.cons m Jdx : Fin (s + 1) → Fin (Module.finrank ℝ E)) = Jdx := by
    funext j; rw [Matrix.vecTail, Function.comp_apply, Fin.cons_succ]
  have hform := tensorChartComponentRaw_covGrad (I := I) (M := M) g_bg 0 s T α
    (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) (Fin.cons m Jdx) hy'
  rw [hJ0, hJtail] at hform
  rw [hform]

set_option maxHeartbeats 3200000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace
  Bundle.continuousMultilinearMap.mixed_instNormedAddCommGroup
  Bundle.continuousMultilinearMap.mixed_instNormedSpace in



omit [BoundarylessManifold I M] in
theorem euclidPartial_covDerivComponentEuclid_abs_le
    (g_bg : SmoothRiemannianMetric I M) (α : M)
    {K_eucl : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))}
    (hKsub : K_eucl ⊆ chartTargetEuclid (I := I) (M := M) α)
    (Craw4 : ℝ)
    (hCraw4_bd : ∀ (T : SmoothCcTensor g_bg 0 4) (b : M),
      b ∈ (fun y'' => (extChartAt I α).symm ((toEuclidean (E := E)).symm y'')) '' K_eucl →
      ∀ (Jdx : Fin 4 → Fin (Module.finrank ℝ E)),
        letI : Bundle.RiemannianBundle (fun bb : M => TensorRSSpace 0 4 I bb) :=
          Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g_bg 0 4
        |tensorChartComponentRaw (I := I) (M := M) g_bg 0 4 T α
            (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) Jdx b| ≤ Craw4 * ‖T.toSection b‖)
    (CLO3 : ℝ)
    (hCLO3_bd : ∀ (T : SmoothCcTensor g_bg 0 3)
      (m : Fin (Module.finrank ℝ E)) (Jdx : Fin 3 → Fin (Module.finrank ℝ E))
      (z : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))), z ∈ K_eucl →
        letI : Bundle.RiemannianBundle (fun bb : M => TensorRSSpace 0 3 I bb) :=
          Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g_bg 0 3
        |covDerivLowerOrderTerm (I := I) (M := M) g_bg 0 3 T α m
            (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) Jdx z| ≤
          CLO3 * ‖T.toSection ((extChartAt I α).symm ((toEuclidean (E := E)).symm z))‖)
    (S : SmoothCcTensor g_bg 0 2) (c a : Fin (Module.finrank ℝ E))
    (Jdx : Fin 2 → Fin (Module.finrank ℝ E))
    {y' : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))} (hy' : y' ∈ K_eucl) :
    letI : Bundle.RiemannianBundle (fun bb : M => TensorRSSpace 0 4 I bb) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g_bg 0 4
    letI : Bundle.RiemannianBundle (fun bb : M => TensorRSSpace 0 3 I bb) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g_bg 0 3
    |euclidPartial (E := E) c
        (covDerivComponentEuclid (I := I) (M := M) g_bg 0 2 α S a
          (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) Jdx) y'| ≤
      Craw4 * ‖(covGrad (I := I) (M := M) g_bg 0 3
          (covGrad (I := I) (M := M) g_bg 0 2 S)).toSection
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y'))‖ +
        CLO3 * ‖(covGrad (I := I) (M := M) g_bg 0 2 S).toSection
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y'))‖ := by
  classical
  letI inst4 : Bundle.RiemannianBundle (fun bb : M => TensorRSSpace 0 4 I bb) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g_bg 0 4
  letI inst3 : Bundle.RiemannianBundle (fun bb : M => TensorRSSpace 0 3 I bb) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g_bg 0 3
  have hy'_tgt : y' ∈ chartTargetEuclid (I := I) (M := M) α := hKsub hy'
  set b₀ : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y') with hb₀_def
  have hb₀_img : b₀ ∈ (fun y'' => (extChartAt I α).symm ((toEuclidean (E := E)).symm y'')) ''
      K_eucl := ⟨y', hy', rfl⟩
  have hbridge : Set.EqOn
      (covDerivComponentEuclid (I := I) (M := M) g_bg 0 2 α S a
        (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) Jdx)
      (chartPushedRaw I α
        (tensorChartComponentRaw (I := I) (M := M) g_bg 0 (2 + 1)
          (covGrad (I := I) (M := M) g_bg 0 2 S) α
          (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) (Fin.cons a Jdx)))
      (chartTargetEuclid (I := I) (M := M) α) := by
    intro z hz
    rw [covDerivComponentEuclid_eqOn_rawComponent_covGrad (I := I) g_bg 2 S α a Jdx hz]
    rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hz]
  rw [(euclidPartial_congr_of_eqOn_isOpen (E := E) c (chartTargetEuclid_isOpen
    (I := I) (M := M) α) hbridge) hy'_tgt]
  rw [euclidPartial_chartPushedRaw_general_eq_covGrad_sub_lowerOrder (I := I) g_bg 3
    (covGrad (I := I) (M := M) g_bg 0 2 S) α c (Fin.cons a Jdx) hy'_tgt]
  have h_raw4 := hCraw4_bd (covGrad (I := I) (M := M) g_bg 0 3
    (covGrad (I := I) (M := M) g_bg 0 2 S)) b₀ hb₀_img (Fin.cons c (Fin.cons a Jdx))
  have h_lo3 := hCLO3_bd (covGrad (I := I) (M := M) g_bg 0 2 S) c (Fin.cons a Jdx) y' hy'
  refine (abs_sub _ _).trans ?_
  exact add_le_add h_raw4 h_lo3

set_option maxHeartbeats 3200000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace
  Bundle.continuousMultilinearMap.mixed_instNormedAddCommGroup
  Bundle.continuousMultilinearMap.mixed_instNormedSpace in




omit [BoundarylessManifold I M] in
theorem euclidPartial2_chartPushedRaw_abs_le_aux
    (g_bg : SmoothRiemannianMetric I M) (α : M)
    {K_eucl : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))}
    (hKsub : K_eucl ⊆ chartTargetEuclid (I := I) (M := M) α)
    (Craw4 : ℝ)
    (hCraw4_bd : ∀ (T : SmoothCcTensor g_bg 0 4) (b : M),
      b ∈ (fun y'' => (extChartAt I α).symm ((toEuclidean (E := E)).symm y'')) '' K_eucl →
      ∀ (Jdx : Fin 4 → Fin (Module.finrank ℝ E)),
        letI : Bundle.RiemannianBundle (fun bb : M => TensorRSSpace 0 4 I bb) :=
          Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g_bg 0 4
        |tensorChartComponentRaw (I := I) (M := M) g_bg 0 4 T α
            (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) Jdx b| ≤ Craw4 * ‖T.toSection b‖)
    (Craw3 : ℝ) (hCraw3_nn : 0 ≤ Craw3)
    (hCraw3_bd : ∀ (T : SmoothCcTensor g_bg 0 3) (b : M),
      b ∈ (fun y'' => (extChartAt I α).symm ((toEuclidean (E := E)).symm y'')) '' K_eucl →
      ∀ (Jdx : Fin 3 → Fin (Module.finrank ℝ E)),
        letI : Bundle.RiemannianBundle (fun bb : M => TensorRSSpace 0 3 I bb) :=
          Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g_bg 0 3
        |tensorChartComponentRaw (I := I) (M := M) g_bg 0 3 T α
            (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) Jdx b| ≤ Craw3 * ‖T.toSection b‖)
    (Craw2 : ℝ)
    (hCraw2_bd : ∀ (T : SmoothCcTensor g_bg 0 2) (b : M),
      b ∈ (fun y'' => (extChartAt I α).symm ((toEuclidean (E := E)).symm y'')) '' K_eucl →
      ∀ (Jdx : Fin 2 → Fin (Module.finrank ℝ E)),
        letI : Bundle.RiemannianBundle (fun bb : M => TensorRSSpace 0 2 I bb) :=
          Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g_bg 0 2
        |tensorChartComponentRaw (I := I) (M := M) g_bg 0 2 T α
            (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) Jdx b| ≤ Craw2 * ‖T.toSection b‖)
    (CLO3 : ℝ)
    (hCLO3_bd : ∀ (T : SmoothCcTensor g_bg 0 3)
      (m : Fin (Module.finrank ℝ E)) (Jdx : Fin 3 → Fin (Module.finrank ℝ E))
      (z : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))), z ∈ K_eucl →
        letI : Bundle.RiemannianBundle (fun bb : M => TensorRSSpace 0 3 I bb) :=
          Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g_bg 0 3
        |covDerivLowerOrderTerm (I := I) (M := M) g_bg 0 3 T α m
            (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) Jdx z| ≤
          CLO3 * ‖T.toSection ((extChartAt I α).symm ((toEuclidean (E := E)).symm z))‖)
    (CLO2 : ℝ) (hCLO2_nn : 0 ≤ CLO2)
    (hCLO2_bd : ∀ (T : SmoothCcTensor g_bg 0 2)
      (m : Fin (Module.finrank ℝ E)) (Jdx : Fin 2 → Fin (Module.finrank ℝ E))
      (z : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))), z ∈ K_eucl →
        letI : Bundle.RiemannianBundle (fun bb : M => TensorRSSpace 0 2 I bb) :=
          Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g_bg 0 2
        |covDerivLowerOrderTerm (I := I) (M := M) g_bg 0 2 T α m
            (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) Jdx z| ≤
          CLO2 * ‖T.toSection ((extChartAt I α).symm ((toEuclidean (E := E)).symm z))‖)
    (Cval : ℝ) (hCval_nn : 0 ≤ Cval)
    (hCval_bd : ∀ (a c : Fin (Module.finrank ℝ E))
      (p1 : Fin 0 → Fin (Module.finrank ℝ E)) (Jdx p2 : Fin 2 → Fin (Module.finrank ℝ E))
      (z : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))), z ∈ K_eucl →
        |secondCovDerivLO_valueCoeff (I := I) (M := M) g_bg 0 2 α a c
            (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) p1 Jdx p2 z| ≤ Cval)
    (Cgrd : ℝ) (hCgrd_nn : 0 ≤ Cgrd)
    (hCgrd_bd : ∀ (a : Fin (Module.finrank ℝ E))
      (p1 : Fin 0 → Fin (Module.finrank ℝ E)) (Jdx p2 : Fin 2 → Fin (Module.finrank ℝ E))
      (z : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))), z ∈ K_eucl →
        |secondCovDerivLO_gradCoeff (I := I) (M := M) g_bg 0 2 α a
            (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) p1 Jdx p2 z| ≤ Cgrd)
    (S : SmoothCcTensor g_bg 0 2) (c a : Fin (Module.finrank ℝ E))
    (Jdx : Fin 2 → Fin (Module.finrank ℝ E))
    {y' : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))} (hy' : y' ∈ K_eucl) :
    letI : Bundle.RiemannianBundle (fun bb : M => TensorRSSpace 0 4 I bb) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g_bg 0 4
    letI : Bundle.RiemannianBundle (fun bb : M => TensorRSSpace 0 3 I bb) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g_bg 0 3
    letI : Bundle.RiemannianBundle (fun bb : M => TensorRSSpace 0 2 I bb) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g_bg 0 2
    |euclidPartial (E := E) c
        (euclidPartial (E := E) a
          (chartPushedRaw I α
            (tensorChartComponentRaw (I := I) (M := M) g_bg 0 2 S α
              (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) Jdx))) y'| ≤
      (Craw4 * ‖(covGrad (I := I) (M := M) g_bg 0 3
            (covGrad (I := I) (M := M) g_bg 0 2 S)).toSection
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y'))‖
        + CLO3 * ‖(covGrad (I := I) (M := M) g_bg 0 2 S).toSection
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y'))‖)
      + ((Fintype.card ((Fin 0 → Fin (Module.finrank ℝ E)) ×
            (Fin 2 → Fin (Module.finrank ℝ E))) : ℝ) * (Cval * Craw2) *
          ‖S.toSection ((extChartAt I α).symm ((toEuclidean (E := E)).symm y'))‖
        + (Fintype.card ((Fin 0 → Fin (Module.finrank ℝ E)) ×
            (Fin 2 → Fin (Module.finrank ℝ E))) : ℝ) * (Cgrd * (Craw3 + CLO2)) *
          (‖(covGrad (I := I) (M := M) g_bg 0 2 S).toSection
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y'))‖
            + ‖S.toSection ((extChartAt I α).symm ((toEuclidean (E := E)).symm y'))‖)) := by
  classical
  letI inst4 : Bundle.RiemannianBundle (fun bb : M => TensorRSSpace 0 4 I bb) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g_bg 0 4
  letI inst3 : Bundle.RiemannianBundle (fun bb : M => TensorRSSpace 0 3 I bb) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g_bg 0 3
  letI inst2 : Bundle.RiemannianBundle (fun bb : M => TensorRSSpace 0 2 I bb) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g_bg 0 2
  have hy'_tgt : y' ∈ chartTargetEuclid (I := I) (M := M) α := hKsub hy'
  set b₀ : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y') with hb₀_def
  have hb₀_img : b₀ ∈ (fun y'' => (extChartAt I α).symm ((toEuclidean (E := E)).symm y'')) ''
      K_eucl := ⟨y', hy', rfl⟩
  set N0 : ℝ := ‖S.toSection b₀‖ with hN0_def
  set N1 : ℝ := ‖(covGrad (I := I) (M := M) g_bg 0 2 S).toSection b₀‖ with hN1_def
  set Npairs : ℝ := (Fintype.card ((Fin 0 → Fin (Module.finrank ℝ E)) ×
      (Fin 2 → Fin (Module.finrank ℝ E))) : ℝ) with hNpairs_def
  set A : ℝ := euclidPartial (E := E) c
      (covDerivComponentEuclid (I := I) (M := M) g_bg 0 2 α S a
        (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) Jdx) y' with hA_def
  set Bsum : ℝ := ∑ p : (Fin 0 → Fin (Module.finrank ℝ E)) × (Fin 2 → Fin (Module.finrank ℝ E)),
      secondCovDerivLO_valueCoeff (I := I) (M := M) g_bg 0 2 α a c
          (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) p.1 Jdx p.2 y' *
        rawComponentEuclid (I := I) (M := M) g_bg 0 2 α S p.1 p.2 y' with hBsum_def
  set Dsum : ℝ := ∑ p : (Fin 0 → Fin (Module.finrank ℝ E)) × (Fin 2 → Fin (Module.finrank ℝ E)),
      secondCovDerivLO_gradCoeff (I := I) (M := M) g_bg 0 2 α a
          (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) p.1 Jdx p.2 y' *
        euclidPartial (E := E) c
          (rawComponentEuclid (I := I) (M := M) g_bg 0 2 α S p.1 p.2) y' with hDsum_def
  have hform := covDerivComponent_second_eq_iteratedFDeriv_add_lowerOrder (I := I) (M := M)
    g_bg 0 2 α S a c (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) Jdx hy'_tgt
  rw [← hA_def, ← hBsum_def, ← hDsum_def] at hform
  have h_target : euclidPartial (E := E) c
        (euclidPartial (E := E) a
          (chartPushedRaw I α
            (tensorChartComponentRaw (I := I) (M := M) g_bg 0 2 S α
              (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) Jdx))) y' = A - (Bsum + Dsum) := by
    linarith [hform]
  rw [h_target]
  have h_dc : |A| ≤ Craw4 * ‖(covGrad (I := I) (M := M) g_bg 0 3
          (covGrad (I := I) (M := M) g_bg 0 2 S)).toSection b₀‖ + CLO3 * N1 := by
    rw [hA_def, hN1_def]
    exact euclidPartial_covDerivComponentEuclid_abs_le (I := I) g_bg α hKsub Craw4 hCraw4_bd CLO3
      hCLO3_bd S c a Jdx hy'
  have hN0_nn : 0 ≤ N0 := norm_nonneg _
  have hN1_nn : 0 ≤ N1 := norm_nonneg _
  have h_val_term : ∀ p : (Fin 0 → Fin (Module.finrank ℝ E)) ×
        (Fin 2 → Fin (Module.finrank ℝ E)),
      |secondCovDerivLO_valueCoeff (I := I) (M := M) g_bg 0 2 α a c
            (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) p.1 Jdx p.2 y' *
          rawComponentEuclid (I := I) (M := M) g_bg 0 2 α S p.1 p.2 y'| ≤
        Cval * (Craw2 * N0) := by
    intro p
    rw [abs_mul]
    have hp1 : p.1 = (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) := Subsingleton.elim _ _
    have h_raw : |rawComponentEuclid (I := I) (M := M) g_bg 0 2 α S p.1 p.2 y'| ≤ Craw2 * N0 := by
      rw [rawComponentEuclid_def, hp1, hN0_def]; exact hCraw2_bd S b₀ hb₀_img p.2
    exact mul_le_mul (hCval_bd a c p.1 Jdx p.2 y' hy') h_raw (abs_nonneg _) hCval_nn
  have h_val_sum : |Bsum| ≤ Npairs * (Cval * Craw2) * N0 := by
    rw [hBsum_def]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum (fun p _ => h_val_term p)).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, ← hNpairs_def]; ring_nf; rfl
  have h_grad_term : ∀ p : (Fin 0 → Fin (Module.finrank ℝ E)) ×
        (Fin 2 → Fin (Module.finrank ℝ E)),
      |secondCovDerivLO_gradCoeff (I := I) (M := M) g_bg 0 2 α a
            (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) p.1 Jdx p.2 y' *
          euclidPartial (E := E) c
            (rawComponentEuclid (I := I) (M := M) g_bg 0 2 α S p.1 p.2) y'| ≤
        Cgrd * ((Craw3 + CLO2) * (N1 + N0)) := by
    intro p
    rw [abs_mul]
    have hp1 : p.1 = (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) := Subsingleton.elim _ _
    have h_draw : |euclidPartial (E := E) c
        (rawComponentEuclid (I := I) (M := M) g_bg 0 2 α S p.1 p.2) y'| ≤
        (Craw3 + CLO2) * (N1 + N0) := by
      have hcongr : Set.EqOn
          (rawComponentEuclid (I := I) (M := M) g_bg 0 2 α S p.1 p.2)
          (chartPushedRaw I α
            (tensorChartComponentRaw (I := I) (M := M) g_bg 0 2 S α p.1 p.2))
          (chartTargetEuclid (I := I) (M := M) α) :=
        rawComponentEuclid_eqOn_chartPushed (I := I) (M := M) g_bg 0 2 α S p.1 p.2
      rw [(euclidPartial_congr_of_eqOn_isOpen (E := E) c (chartTargetEuclid_isOpen
        (I := I) (M := M) α) hcongr) hy'_tgt, hp1]
      rw [euclidPartial_chartPushedRaw_general_eq_covGrad_sub_lowerOrder (I := I) g_bg 2
        S α c p.2 hy'_tgt]
      have h_raw3 := hCraw3_bd (covGrad (I := I) (M := M) g_bg 0 2 S) b₀ hb₀_img (Fin.cons c p.2)
      have h_lo2 := hCLO2_bd S c p.2 y' hy'
      rw [← hN1_def] at h_raw3
      rw [← hN0_def] at h_lo2
      refine (abs_sub _ _).trans ?_
      nlinarith [h_raw3, h_lo2, hCLO2_nn, hCraw3_nn, hN1_nn, hN0_nn]
    exact mul_le_mul (hCgrd_bd a p.1 Jdx p.2 y' hy') h_draw (abs_nonneg _) hCgrd_nn
  have h_grad_sum : |Dsum| ≤ Npairs * (Cgrd * (Craw3 + CLO2)) * (N1 + N0) := by
    rw [hDsum_def]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum (fun p _ => h_grad_term p)).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, ← hNpairs_def]; ring_nf; rfl
  refine (abs_sub _ _).trans ?_
  exact add_le_add h_dc ((abs_add_le _ _).trans (add_le_add h_val_sum h_grad_sum))

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace
  Bundle.continuousMultilinearMap.mixed_instNormedAddCommGroup
  Bundle.continuousMultilinearMap.mixed_instNormedSpace in


omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem iteratedCovGrad_norm_le_jetSum
    (g_bg : SmoothRiemannianMetric I M) (S : SmoothCcTensor g_bg 0 2) (x : M)
    (j : ℕ) (hj : j < 3) :
    letI : Bundle.RiemannianBundle (fun bb : M => TensorRSSpace 0 (2 + j) I bb) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g_bg 0 (2 + j)
    ‖(iteratedCovGrad (I := I) (M := M) g_bg 0 2 j S).toSection x‖ ≤
      iteratedCovGradJetSum (I := I) g_bg S x := by
  rw [iteratedCovGradJetSum]
  have hsummand_nn : ∀ i ∈ Finset.range 3,
      0 ≤ (letI : Bundle.RiemannianBundle (fun bb : M => TensorRSSpace 0 (2 + i) I bb) :=
            Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g_bg 0 (2 + i)
          ‖(iteratedCovGrad (I := I) (M := M) g_bg 0 2 i S).toSection x‖) := by
    intro i _
    letI : Bundle.RiemannianBundle (fun bb : M => TensorRSSpace 0 (2 + i) I bb) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g_bg 0 (2 + i)
    exact norm_nonneg _
  exact Finset.single_le_sum hsummand_nn (Finset.mem_range.mpr hj)

set_option maxHeartbeats 3200000 in


omit [BoundarylessManifold I M] in
omit [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
theorem secondCovDerivLO_valueCoeff_uniform_bound
    (g_bg : SmoothRiemannianMetric I M) (α : M)
    {K_eucl : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))}
    (hK : IsCompact K_eucl) (hKsub : K_eucl ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ Cval : ℝ, 0 ≤ Cval ∧ ∀ (a c : Fin (Module.finrank ℝ E))
      (p1 : Fin 0 → Fin (Module.finrank ℝ E)) (Jdx p2 : Fin 2 → Fin (Module.finrank ℝ E))
      (z : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))), z ∈ K_eucl →
        |secondCovDerivLO_valueCoeff (I := I) (M := M) g_bg 0 2 α a c
            (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) p1 Jdx p2 z| ≤ Cval := by
  classical
  have h_bound : ∀ (acIJ : (Fin (Module.finrank ℝ E)) × (Fin (Module.finrank ℝ E)) ×
        ((Fin 0 → Fin (Module.finrank ℝ E)) × (Fin 2 → Fin (Module.finrank ℝ E)) ×
          (Fin 2 → Fin (Module.finrank ℝ E)))),
      ∃ Cv : ℝ, 0 ≤ Cv ∧ ∀ z ∈ K_eucl,
        |secondCovDerivLO_valueCoeff (I := I) (M := M) g_bg 0 2 α acIJ.1 acIJ.2.1
            (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) acIJ.2.2.1
            acIJ.2.2.2.1 acIJ.2.2.2.2 z| ≤ Cv := by
    rintro ⟨a, c, p1, Jdx, p2⟩
    obtain ⟨Cv, hCv⟩ := hK.exists_bound_of_continuousOn
      (((secondCovDerivLO_valueCoeff_contDiffOn (I := I) (M := M) g_bg 0 2 α a c
        (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) p1 Jdx p2).continuousOn).mono hKsub)
    refine ⟨max Cv 0, le_max_right _ _, fun z hz => ?_⟩
    have := hCv z hz; rw [Real.norm_eq_abs] at this; exact this.trans (le_max_left _ _)
  choose Cv hCv_nn hCv_bd using h_bound
  refine ⟨Finset.univ.sup' Finset.univ_nonempty Cv,
    le_trans (hCv_nn (Classical.arbitrary _)) (Finset.le_sup' Cv (Finset.mem_univ _)),
    fun a c p1 Jdx p2 z hz => ?_⟩
  have hp1 : p1 = (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) := Subsingleton.elim _ _
  subst hp1
  exact (hCv_bd (a, c, _, Jdx, p2) z hz).trans (Finset.le_sup' Cv (Finset.mem_univ _))

set_option maxHeartbeats 3200000 in


omit [BoundarylessManifold I M] in
omit [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
theorem secondCovDerivLO_gradCoeff_uniform_bound
    (g_bg : SmoothRiemannianMetric I M) (α : M)
    {K_eucl : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))}
    (hK : IsCompact K_eucl) (hKsub : K_eucl ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ Cgrd : ℝ, 0 ≤ Cgrd ∧ ∀ (a : Fin (Module.finrank ℝ E))
      (p1 : Fin 0 → Fin (Module.finrank ℝ E)) (Jdx p2 : Fin 2 → Fin (Module.finrank ℝ E))
      (z : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))), z ∈ K_eucl →
        |secondCovDerivLO_gradCoeff (I := I) (M := M) g_bg 0 2 α a
            (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) p1 Jdx p2 z| ≤ Cgrd := by
  classical
  have h_bound : ∀ (aIJ : (Fin (Module.finrank ℝ E)) ×
        ((Fin 0 → Fin (Module.finrank ℝ E)) × (Fin 2 → Fin (Module.finrank ℝ E)) ×
          (Fin 2 → Fin (Module.finrank ℝ E)))),
      ∃ Cg : ℝ, 0 ≤ Cg ∧ ∀ z ∈ K_eucl,
        |secondCovDerivLO_gradCoeff (I := I) (M := M) g_bg 0 2 α aIJ.1
            (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) aIJ.2.1
            aIJ.2.2.1 aIJ.2.2.2 z| ≤ Cg := by
    rintro ⟨a, p1, Jdx, p2⟩
    obtain ⟨Cg, hCg⟩ := hK.exists_bound_of_continuousOn
      (((secondCovDerivLO_gradCoeff_contDiffOn (I := I) (M := M) g_bg 0 2 α a
        (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) p1 Jdx p2).continuousOn).mono hKsub)
    refine ⟨max Cg 0, le_max_right _ _, fun z hz => ?_⟩
    have := hCg z hz; rw [Real.norm_eq_abs] at this; exact this.trans (le_max_left _ _)
  choose Cg hCg_nn hCg_bd using h_bound
  refine ⟨Finset.univ.sup' Finset.univ_nonempty Cg,
    le_trans (hCg_nn (Classical.arbitrary _)) (Finset.le_sup' Cg (Finset.mem_univ _)),
    fun a p1 Jdx p2 z hz => ?_⟩
  have hp1 : p1 = (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) := Subsingleton.elim _ _
  subst hp1
  exact (hCg_bd (a, _, Jdx, p2) z hz).trans (Finset.le_sup' Cg (Finset.mem_univ _))

set_option maxHeartbeats 4000000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace
  Bundle.continuousMultilinearMap.mixed_instNormedAddCommGroup
  Bundle.continuousMultilinearMap.mixed_instNormedSpace in




omit [BoundarylessManifold I M] in
theorem euclidPartial2_chartPushedRaw_abs_le_jetSum
    (g_bg : SmoothRiemannianMetric I M) (α : M)
    {K_eucl : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))}
    (hK : IsCompact K_eucl) (hKsub : K_eucl ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (S : SmoothCcTensor g_bg 0 2)
      (c a : Fin (Module.finrank ℝ E)) (Jdx : Fin 2 → Fin (Module.finrank ℝ E))
      (y' : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))), y' ∈ K_eucl →
        |euclidPartial (E := E) c
            (euclidPartial (E := E) a
              (chartPushedRaw I α
                (tensorChartComponentRaw (I := I) (M := M) g_bg 0 2 S α
                  (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) Jdx))) y'| ≤
          C * iteratedCovGradJetSum (I := I) g_bg S
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y')) := by
  classical
  obtain ⟨hImg_cpt, hImg_sub⟩ :=
    chartPreimage_image_isCompact_subset_chartSource (I := I) (M := M) α hK hKsub
  obtain ⟨Craw4, hCraw4_nn, hCraw4_bd⟩ :=
    tensorChartComponentRaw_abs_le_riemannianFibreNorm (I := I) g_bg 4 α hImg_cpt hImg_sub
  obtain ⟨Craw3, hCraw3_nn, hCraw3_bd⟩ :=
    tensorChartComponentRaw_abs_le_riemannianFibreNorm (I := I) g_bg 3 α hImg_cpt hImg_sub
  obtain ⟨Craw2, hCraw2_nn, hCraw2_bd⟩ :=
    tensorChartComponentRaw_abs_le_riemannianFibreNorm (I := I) g_bg 2 α hImg_cpt hImg_sub
  obtain ⟨CLO3, hCLO3_nn, hCLO3_bd⟩ :=
    covDerivLowerOrderTerm_abs_le_riemannianFibreNorm (I := I) g_bg 3 α hK hKsub
  obtain ⟨CLO2, hCLO2_nn, hCLO2_bd⟩ :=
    covDerivLowerOrderTerm_abs_le_riemannianFibreNorm (I := I) g_bg 2 α hK hKsub
  obtain ⟨Cval, hCval_nn, hCval_bd⟩ :=
    secondCovDerivLO_valueCoeff_uniform_bound (I := I) g_bg α hK hKsub
  obtain ⟨Cgrd, hCgrd_nn, hCgrd_bd⟩ :=
    secondCovDerivLO_gradCoeff_uniform_bound (I := I) g_bg α hK hKsub
  set Npairs : ℝ := (Fintype.card ((Fin 0 → Fin (Module.finrank ℝ E)) ×
      (Fin 2 → Fin (Module.finrank ℝ E))) : ℝ) with hNpairs_def
  have hNpairs_nn : 0 ≤ Npairs := by rw [hNpairs_def]; positivity
  refine ⟨Craw4 + CLO3 + Npairs * (Cval * Craw2) + 2 * (Npairs * (Cgrd * (Craw3 + CLO2))),
    by positivity, ?_⟩
  intro S c a Jdx y' hy'
  letI inst4 : Bundle.RiemannianBundle (fun bb : M => TensorRSSpace 0 4 I bb) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g_bg 0 4
  letI inst3 : Bundle.RiemannianBundle (fun bb : M => TensorRSSpace 0 3 I bb) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g_bg 0 3
  letI inst2 : Bundle.RiemannianBundle (fun bb : M => TensorRSSpace 0 2 I bb) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g_bg 0 2
  set b₀ : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y') with hb₀_def
  set R : ℝ := iteratedCovGradJetSum (I := I) g_bg S b₀ with hR_def
  set N0 : ℝ := ‖S.toSection b₀‖ with hN0_def
  set N1 : ℝ := ‖(covGrad (I := I) (M := M) g_bg 0 2 S).toSection b₀‖ with hN1_def
  set N2 : ℝ := ‖(covGrad (I := I) (M := M) g_bg 0 3
    (covGrad (I := I) (M := M) g_bg 0 2 S)).toSection b₀‖ with hN2_def
  have hN0_nn : 0 ≤ N0 := norm_nonneg _
  have hN1_nn : 0 ≤ N1 := norm_nonneg _
  have hN2_nn : 0 ≤ N2 := norm_nonneg _
  have hN0_le : N0 ≤ R := by
    rw [hN0_def, hR_def]
    exact iteratedCovGrad_norm_le_jetSum (I := I) g_bg S b₀ 0 (by norm_num)
  have hN1_le : N1 ≤ R := by
    rw [hN1_def, hR_def]
    exact iteratedCovGrad_norm_le_jetSum (I := I) g_bg S b₀ 1 (by norm_num)
  have hN2_le : N2 ≤ R := by
    rw [hN2_def, hR_def]
    exact iteratedCovGrad_norm_le_jetSum (I := I) g_bg S b₀ 2 (by norm_num)
  have hR_nn : 0 ≤ R := le_trans hN0_nn hN0_le
  have haux := euclidPartial2_chartPushedRaw_abs_le_aux (I := I) g_bg α hKsub
    Craw4 hCraw4_bd Craw3 hCraw3_nn hCraw3_bd Craw2 hCraw2_bd CLO3 hCLO3_bd CLO2 hCLO2_nn hCLO2_bd
    Cval hCval_nn hCval_bd Cgrd hCgrd_nn hCgrd_bd S c a Jdx hy'
  rw [← hN0_def, ← hN1_def, ← hN2_def] at haux
  refine haux.trans ?_
  have hb3 : Npairs * (Cval * Craw2) * N0 ≤ Npairs * (Cval * Craw2) * R :=
    mul_le_mul_of_nonneg_left hN0_le (by positivity)
  have hb4 : Npairs * (Cgrd * (Craw3 + CLO2)) * (N1 + N0) ≤
      Npairs * (Cgrd * (Craw3 + CLO2)) * (R + R) :=
    mul_le_mul_of_nonneg_left (add_le_add hN1_le hN0_le) (by positivity)
  have hb1 : Craw4 * N2 ≤ Craw4 * R := mul_le_mul_of_nonneg_left hN2_le hCraw4_nn
  have hb2 : CLO3 * N1 ≤ CLO3 * R := mul_le_mul_of_nonneg_left hN1_le hCLO3_nn
  calc (Craw4 * N2 + CLO3 * N1) + (Npairs * (Cval * Craw2) * N0
          + Npairs * (Cgrd * (Craw3 + CLO2)) * (N1 + N0))
      ≤ (Craw4 * R + CLO3 * R) + (Npairs * (Cval * Craw2) * R
          + Npairs * (Cgrd * (Craw3 + CLO2)) * (R + R)) :=
        add_le_add (add_le_add hb1 hb2) (add_le_add hb3 hb4)
    _ = (Craw4 + CLO3 + Npairs * (Cval * Craw2) + 2 * (Npairs * (Cgrd * (Craw3 + CLO2)))) * R := by
        ring

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace
  Bundle.continuousMultilinearMap.mixed_instNormedAddCommGroup
  Bundle.continuousMultilinearMap.mixed_instNormedSpace in



omit [BoundarylessManifold I M] in
theorem reprDiffChartCompOnE_abs_le_riemannianFibreNorm
    (g_bg : SmoothRiemannianMetric I M) {σ : ℝ}
    {u₁ u₂ : tensorHs (I := I) (M := M) g_bg 0 2 σ}
    (hu₁ : isRealizableMetricPerturbationAt (I := I) g_bg u₁) (hu₂ : isRealizableMetricPerturbationAt (I := I) g_bg u₂)
    (α : M) {K : Set E} (hK : IsCompact K)
    (hKsub : K ⊆ interior ((extChartAt I α).target : Set E)) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 2 I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g_bg 0 2
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ∀ l b : Fin (Module.finrank ℝ E),
      |reprDiffChartCompOnE (I := I) g_bg hu₁ hu₂ α l b y| ≤
        C * ‖(realizableRepr (I := I) g_bg hu₁ - realizableRepr (I := I) g_bg hu₂).toSection
          ((extChartAt I α).symm y)‖ := by
  classical
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 2 I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g_bg 0 2
  set S : SmoothCcTensor g_bg 0 2 :=
    realizableRepr (I := I) g_bg hu₁ - realizableRepr (I := I) g_bg hu₂ with hS_def
  obtain ⟨hImg_cpt, hImg_sub⟩ :=
    extChartAt_symm_image_isCompact_subset_chartSource (I := I) (M := M) α hK hKsub
  obtain ⟨Craw, hCraw_nn, hCraw_bd⟩ :=
    tensorChartComponentRaw_abs_le_riemannianFibreNorm (I := I) g_bg 2 α hImg_cpt hImg_sub
  refine ⟨Craw, hCraw_nn, ?_⟩
  intro y hy l b
  set b₀ : M := (extChartAt I α).symm y with hb₀_def
  have hb₀_src : b₀ ∈ (chartAt H α).source := hImg_sub ⟨y, hy, rfl⟩
  have hb₀_img : b₀ ∈ (extChartAt I α).symm '' K := ⟨y, hy, rfl⟩
  rw [reprDiffChartCompOnE_eq_symm_tensorChartComponentRaw (I := I) g_bg hu₁ hu₂ α l b hb₀_src]
  set N : ℝ := ‖S.toSection b₀‖ with hN_def
  have hN_nn : 0 ≤ N := norm_nonneg _
  have h_lb : |tensorChartComponentRaw (I := I) (M := M) g_bg 0 2 S α
      (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) ![l, b] b₀| ≤ Craw * N :=
    hCraw_bd S b₀ hb₀_img ![l, b]
  have h_bl : |tensorChartComponentRaw (I := I) (M := M) g_bg 0 2 S α
      (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) ![b, l] b₀| ≤ Craw * N :=
    hCraw_bd S b₀ hb₀_img ![b, l]
  calc |(1 / 2 : ℝ) *
          (tensorChartComponentRaw (I := I) (M := M) g_bg 0 2 S α
              (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) ![l, b] b₀ +
            tensorChartComponentRaw (I := I) (M := M) g_bg 0 2 S α
              (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) ![b, l] b₀)|
      = (1 / 2 : ℝ) *
          |tensorChartComponentRaw (I := I) (M := M) g_bg 0 2 S α
              (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) ![l, b] b₀ +
            tensorChartComponentRaw (I := I) (M := M) g_bg 0 2 S α
              (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) ![b, l] b₀| := by
        rw [abs_mul]; norm_num
    _ ≤ (1 / 2 : ℝ) * (Craw * N + Craw * N) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact (abs_add_le _ _).trans (add_le_add h_lb h_bl)
    _ = Craw * N := by ring

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 6400000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace
  Bundle.continuousMultilinearMap.mixed_instNormedAddCommGroup
  Bundle.continuousMultilinearMap.mixed_instNormedSpace in



omit [BoundarylessManifold I M] in
theorem partialDeriv_reprDiffChartCompOnE_abs_le
    (g_bg : SmoothRiemannianMetric I M) {σ : ℝ}
    {u₁ u₂ : tensorHs (I := I) (M := M) g_bg 0 2 σ}
    (hu₁ : isRealizableMetricPerturbationAt (I := I) g_bg u₁) (hu₂ : isRealizableMetricPerturbationAt (I := I) g_bg u₂)
    (α : M) {K : Set E} (hK : IsCompact K)
    (hKsub : K ⊆ interior ((extChartAt I α).target : Set E)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ∀ l b a : Fin (Module.finrank ℝ E),
      |partialDeriv (E := E) a (reprDiffChartCompOnE (I := I) g_bg hu₁ hu₂ α l b) y| ≤
        C * iteratedCovGradJetSum (I := I) g_bg
          (realizableRepr (I := I) g_bg hu₁ - realizableRepr (I := I) g_bg hu₂)
          ((extChartAt I α).symm y) := by
  classical
  set S : SmoothCcTensor g_bg 0 2 :=
    realizableRepr (I := I) g_bg hu₁ - realizableRepr (I := I) g_bg hu₂ with hS_def
  obtain ⟨hImg_cpt, hImg_sub⟩ :=
    extChartAt_symm_image_isCompact_subset_chartSource (I := I) (M := M) α hK hKsub
  obtain ⟨Craw1, hCraw1_nn, hCraw1_bd⟩ :=
    tensorChartComponentRaw_abs_le_riemannianFibreNorm (I := I) g_bg 3 α hImg_cpt hImg_sub
  have hKe_cpt : IsCompact (toEuclidean (E := E) '' K) := hK.image toEuclidean.continuous
  have hKe_sub : toEuclidean (E := E) '' K ⊆ chartTargetEuclid (I := I) (M := M) α := by
    intro z hz
    obtain ⟨y, hy_mem, hy_eq⟩ := hz
    rw [← hy_eq]
    exact toEuclidean_mem_chartTargetEuclid_of_mem_interior (I := I) (M := M) α (hKsub hy_mem)
  obtain ⟨CLO, hCLO_nn, hCLO_bd⟩ :=
    covDerivLowerOrderTerm_abs_le_riemannianFibreNorm (I := I) g_bg 2 α hKe_cpt hKe_sub
  refine ⟨Craw1 + CLO, by positivity, ?_⟩
  intro y hy l b a
  letI inst3 : Bundle.RiemannianBundle (fun bb : M => TensorRSSpace 0 (2 + 1) I bb) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g_bg 0 (2 + 1)
  letI inst2 : Bundle.RiemannianBundle (fun bb : M => TensorRSSpace 0 2 I bb) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g_bg 0 2
  set b₀ : M := (extChartAt I α).symm y with hb₀_def
  have hb₀_img : b₀ ∈ (extChartAt I α).symm '' K := ⟨y, hy, rfl⟩
  set N1 : ℝ := ‖(covGrad (I := I) (M := M) g_bg 0 2 S).toSection b₀‖ with hN1_def
  set N0 : ℝ := ‖S.toSection b₀‖ with hN0_def
  have hN1_nn : 0 ≤ N1 := norm_nonneg _
  have hN0_nn : 0 ≤ N0 := norm_nonneg _
  set R : ℝ := iteratedCovGradJetSum (I := I) g_bg S b₀ with hR_def
  have hR_nn : 0 ≤ R := iteratedCovGradJetSum_nonneg (I := I) g_bg S b₀
  have hsummand_nn : ∀ i ∈ Finset.range 3,
      0 ≤ (letI : Bundle.RiemannianBundle (fun bb : M => TensorRSSpace 0 (2 + i) I bb) :=
            Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g_bg 0 (2 + i)
          ‖(iteratedCovGrad (I := I) (M := M) g_bg 0 2 i S).toSection b₀‖) := by
    intro i _
    letI : Bundle.RiemannianBundle (fun bb : M => TensorRSSpace 0 (2 + i) I bb) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g_bg 0 (2 + i)
    exact norm_nonneg _
  have hN0_le : N0 ≤ R := by
    have h := Finset.single_le_sum hsummand_nn (Finset.mem_range.mpr (by norm_num : (0 : ℕ) < 3))
    rw [hR_def, iteratedCovGradJetSum]
    exact h
  have hN1_le : N1 ≤ R := by
    have h := Finset.single_le_sum hsummand_nn (Finset.mem_range.mpr (by norm_num : (1 : ℕ) < 3))
    rw [hR_def, iteratedCovGradJetSum]
    exact h
  rw [partialDeriv_reprDiffChartCompOnE_eq_covGrad_sub_lowerOrder (I := I) g_bg hu₁ hu₂ α a l b
    (hKsub hy)]
  have h_raw_alb : |tensorChartComponentRaw (I := I) (M := M) g_bg 0 (2 + 1)
      (covGrad (I := I) (M := M) g_bg 0 2 S) α
      (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) ![a, l, b] b₀| ≤ Craw1 * N1 :=
    hCraw1_bd (covGrad (I := I) (M := M) g_bg 0 2 S) b₀ hb₀_img ![a, l, b]
  have h_raw_abl : |tensorChartComponentRaw (I := I) (M := M) g_bg 0 (2 + 1)
      (covGrad (I := I) (M := M) g_bg 0 2 S) α
      (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) ![a, b, l] b₀| ≤ Craw1 * N1 :=
    hCraw1_bd (covGrad (I := I) (M := M) g_bg 0 2 S) b₀ hb₀_img ![a, b, l]
  have hbase_eq : (extChartAt I α).symm ((toEuclidean (E := E)).symm (toEuclidean (E := E) y)) =
      b₀ := by rw [hb₀_def]; simp
  have h_lo_lb : |covDerivLowerOrderTerm (I := I) (M := M) g_bg 0 2 S α a
      (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) ![l, b] (toEuclidean (E := E) y)| ≤
      CLO * N0 := by
    have := hCLO_bd S a ![l, b] (toEuclidean (E := E) y) ⟨y, hy, rfl⟩
    rwa [hbase_eq] at this
  have h_lo_bl : |covDerivLowerOrderTerm (I := I) (M := M) g_bg 0 2 S α a
      (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) ![b, l] (toEuclidean (E := E) y)| ≤
      CLO * N0 := by
    have := hCLO_bd S a ![b, l] (toEuclidean (E := E) y) ⟨y, hy, rfl⟩
    rwa [hbase_eq] at this
  rw [abs_mul]
  have h12 : |(1 / 2 : ℝ)| = (1 / 2 : ℝ) := by norm_num
  rw [h12]
  have h_sum : |(tensorChartComponentRaw (I := I) (M := M) g_bg 0 (2 + 1)
              (covGrad (I := I) (M := M) g_bg 0 2 S) α
              (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) ![a, l, b] b₀
            - covDerivLowerOrderTerm (I := I) (M := M) g_bg 0 2 S α a
                (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) ![l, b]
                (toEuclidean (E := E) y))
          + (tensorChartComponentRaw (I := I) (M := M) g_bg 0 (2 + 1)
              (covGrad (I := I) (M := M) g_bg 0 2 S) α
              (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) ![a, b, l] b₀
            - covDerivLowerOrderTerm (I := I) (M := M) g_bg 0 2 S α a
                (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) ![b, l]
                (toEuclidean (E := E) y))| ≤
        2 * (Craw1 * N1) + 2 * (CLO * N0) := by
    refine (abs_add_le _ _).trans ?_
    have hb1 := (abs_sub _ _).trans (add_le_add h_raw_alb h_lo_lb)
    have hb2 := (abs_sub _ _).trans (add_le_add h_raw_abl h_lo_bl)
    calc _ ≤ (Craw1 * N1 + CLO * N0) + (Craw1 * N1 + CLO * N0) := add_le_add hb1 hb2
      _ = 2 * (Craw1 * N1) + 2 * (CLO * N0) := by ring
  calc (1 / 2 : ℝ) * |_|
      ≤ (1 / 2 : ℝ) * (2 * (Craw1 * N1) + 2 * (CLO * N0)) :=
        mul_le_mul_of_nonneg_left h_sum (by norm_num)
    _ = Craw1 * N1 + CLO * N0 := by ring
    _ ≤ (Craw1 + CLO) * R := by nlinarith [hCraw1_nn, hCLO_nn, hN1_nn, hN0_nn, hN1_le, hN0_le, hR_nn]

set_option maxHeartbeats 1600000 in



omit [BoundarylessManifold I M] in
theorem partialDeriv2_reprDiffChartCompOnE_abs_le
    (g_bg : SmoothRiemannianMetric I M) {σ : ℝ}
    {u₁ u₂ : tensorHs (I := I) (M := M) g_bg 0 2 σ}
    (hu₁ : isRealizableMetricPerturbationAt (I := I) g_bg u₁) (hu₂ : isRealizableMetricPerturbationAt (I := I) g_bg u₂)
    (α : M) {K : Set E} (hK : IsCompact K)
    (hKsub : K ⊆ interior ((extChartAt I α).target : Set E)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ∀ l b c a : Fin (Module.finrank ℝ E),
      |partialDeriv (E := E) c
          (partialDeriv (E := E) a (reprDiffChartCompOnE (I := I) g_bg hu₁ hu₂ α l b)) y| ≤
        C * iteratedCovGradJetSum (I := I) g_bg
          (realizableRepr (I := I) g_bg hu₁ - realizableRepr (I := I) g_bg hu₂)
          ((extChartAt I α).symm y) := by
  classical
  set S : SmoothCcTensor g_bg 0 2 :=
    realizableRepr (I := I) g_bg hu₁ - realizableRepr (I := I) g_bg hu₂ with hS_def
  have hKe_cpt : IsCompact (toEuclidean (E := E) '' K) := hK.image toEuclidean.continuous
  have hKe_sub : toEuclidean (E := E) '' K ⊆ chartTargetEuclid (I := I) (M := M) α := by
    intro z hz
    obtain ⟨y, hy_mem, hy_eq⟩ := hz
    rw [← hy_eq]
    exact toEuclidean_mem_chartTargetEuclid_of_mem_interior (I := I) (M := M) α (hKsub hy_mem)
  obtain ⟨C2, hC2_nn, hC2_bd⟩ :=
    euclidPartial2_chartPushedRaw_abs_le_jetSum (I := I) g_bg α hKe_cpt hKe_sub
  have hopen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  refine ⟨C2, hC2_nn, ?_⟩
  intro y hy l b c a
  set ys : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) := toEuclidean (E := E) y with hys_def
  have hys_mem : ys ∈ chartTargetEuclid (I := I) (M := M) α :=
    toEuclidean_mem_chartTargetEuclid_of_mem_interior (I := I) (M := M) α (hKsub hy)
  have hys_imK : ys ∈ toEuclidean (E := E) '' K := ⟨y, hy, rfl⟩
  set Flb : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
    chartPushedRaw I α
      (tensorChartComponentRaw (I := I) (M := M) g_bg 0 2 S α
        (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) ![l, b]) with hFlb_def
  set Fbl : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
    chartPushedRaw I α
      (tensorChartComponentRaw (I := I) (M := M) g_bg 0 2 S α
        (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) ![b, l]) with hFbl_def
  rw [partialDeriv2_eq_euclidPartial2_comp_toEuclidean (E := E) c a
    (reprDiffChartCompOnE (I := I) g_bg hu₁ hu₂ α l b) y, ← hys_def]
  have heqOn : Set.EqOn
      (reprDiffChartCompOnE (I := I) g_bg hu₁ hu₂ α l b ∘ (toEuclidean (E := E)).symm)
      (fun z => (1 / 2 : ℝ) * (Flb z + Fbl z))
      (chartTargetEuclid (I := I) (M := M) α) := by
    rw [hFlb_def, hFbl_def]
    exact reprDiffChartCompOnE_comp_toEuclidean_symm_eqOn (I := I) g_bg hu₁ hu₂ α l b
  have hinner : Set.EqOn
      (euclidPartial (E := E) a
        (reprDiffChartCompOnE (I := I) g_bg hu₁ hu₂ α l b ∘ (toEuclidean (E := E)).symm))
      (euclidPartial (E := E) a (fun z => (1 / 2 : ℝ) * (Flb z + Fbl z)))
      (chartTargetEuclid (I := I) (M := M) α) :=
    euclidPartial_congr_of_eqOn_isOpen (E := E) a hopen heqOn
  rw [(euclidPartial_congr_of_eqOn_isOpen (E := E) c hopen hinner) hys_mem]
  have hdiff_lb : DifferentiableAt ℝ Flb ys :=
    chartPushedRaw_tensorChartComponentRaw_differentiableAt (I := I) g_bg 2 S α ![l, b] hys_mem
  have hdiff_bl : DifferentiableAt ℝ Fbl ys :=
    chartPushedRaw_tensorChartComponentRaw_differentiableAt (I := I) g_bg 2 S α ![b, l] hys_mem
  have hinner_eq : Set.EqOn
      (euclidPartial (E := E) a (fun z => (1 / 2 : ℝ) * (Flb z + Fbl z)))
      (fun z => (1 / 2 : ℝ) * (euclidPartial (E := E) a Flb z + euclidPartial (E := E) a Fbl z))
      (chartTargetEuclid (I := I) (M := M) α) := by
    intro z hz
    have hdz_lb : DifferentiableAt ℝ Flb z :=
      chartPushedRaw_tensorChartComponentRaw_differentiableAt (I := I) g_bg 2 S α ![l, b] hz
    have hdz_bl : DifferentiableAt ℝ Fbl z :=
      chartPushedRaw_tensorChartComponentRaw_differentiableAt (I := I) g_bg 2 S α ![b, l] hz
    rw [euclidPartial_def]
    rw [show (fun z => (1 / 2 : ℝ) * (Flb z + Fbl z)) = (1 / 2 : ℝ) • (Flb + Fbl) from by
      funext z; simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]]
    rw [fderiv_const_smul (hdz_lb.add hdz_bl), fderiv_add hdz_lb hdz_bl]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, smul_eq_mul]
    rw [show fderiv ℝ Flb z (EuclideanSpace.single a 1) = euclidPartial (E := E) a Flb z from rfl,
      show fderiv ℝ Fbl z (EuclideanSpace.single a 1) = euclidPartial (E := E) a Fbl z from rfl]
  rw [(euclidPartial_congr_of_eqOn_isOpen (E := E) c hopen hinner_eq) hys_mem]
  have hda_lb : DifferentiableAt ℝ (euclidPartial (E := E) a Flb) ys := by
    have hcd : ContDiffOn ℝ ∞ (euclidPartial (E := E) a Flb)
        (chartTargetEuclid (I := I) (M := M) α) := by
      rw [hFlb_def]
      exact euclidPartial_chartPushedRaw_contDiffOn (I := I) (M := M) g_bg 0 2 S α a
        (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) ![l, b]
    exact (hcd.contDiffAt (hopen.mem_nhds hys_mem)).differentiableAt (by simp)
  have hda_bl : DifferentiableAt ℝ (euclidPartial (E := E) a Fbl) ys := by
    have hcd : ContDiffOn ℝ ∞ (euclidPartial (E := E) a Fbl)
        (chartTargetEuclid (I := I) (M := M) α) := by
      rw [hFbl_def]
      exact euclidPartial_chartPushedRaw_contDiffOn (I := I) (M := M) g_bg 0 2 S α a
        (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) ![b, l]
    exact (hcd.contDiffAt (hopen.mem_nhds hys_mem)).differentiableAt (by simp)
  rw [euclidPartial_def]
  rw [show (fun z => (1 / 2 : ℝ) *
        (euclidPartial (E := E) a Flb z + euclidPartial (E := E) a Fbl z)) =
      (1 / 2 : ℝ) • (euclidPartial (E := E) a Flb + euclidPartial (E := E) a Fbl) from by
    funext z; simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]]
  rw [fderiv_const_smul (hda_lb.add hda_bl), fderiv_add hda_lb hda_bl]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, smul_eq_mul]
  rw [show fderiv ℝ (euclidPartial (E := E) a Flb) ys (EuclideanSpace.single c 1) =
      euclidPartial (E := E) c (euclidPartial (E := E) a Flb) ys from rfl,
    show fderiv ℝ (euclidPartial (E := E) a Fbl) ys (EuclideanSpace.single c 1) =
      euclidPartial (E := E) c (euclidPartial (E := E) a Fbl) ys from rfl]
  set R : ℝ := iteratedCovGradJetSum (I := I) g_bg S
    ((extChartAt I α).symm ((toEuclidean (E := E)).symm ys)) with hR_def
  have hR_nn : 0 ≤ R := iteratedCovGradJetSum_nonneg (I := I) g_bg S _
  have hbase : (extChartAt I α).symm ((toEuclidean (E := E)).symm ys) = (extChartAt I α).symm y := by
    rw [hys_def]; simp
  have h_lb : |euclidPartial (E := E) c (euclidPartial (E := E) a Flb) ys| ≤ C2 * R := by
    rw [hFlb_def]; exact hC2_bd S c a ![l, b] ys hys_imK
  have h_bl : |euclidPartial (E := E) c (euclidPartial (E := E) a Fbl) ys| ≤ C2 * R := by
    rw [hFbl_def]; exact hC2_bd S c a ![b, l] ys hys_imK
  rw [abs_mul, show |(1 / 2 : ℝ)| = (1 / 2 : ℝ) from by norm_num]
  rw [← hbase]
  calc (1 / 2 : ℝ) * |euclidPartial (E := E) c (euclidPartial (E := E) a Flb) ys +
          euclidPartial (E := E) c (euclidPartial (E := E) a Fbl) ys|
      ≤ (1 / 2 : ℝ) * (C2 * R + C2 * R) :=
        mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add h_lb h_bl)) (by norm_num)
    _ = C2 * R := by ring

set_option maxHeartbeats 1600000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace
  Bundle.continuousMultilinearMap.mixed_instNormedAddCommGroup
  Bundle.continuousMultilinearMap.mixed_instNormedSpace in








omit [BoundarylessManifold I M] in
theorem hcovgrad_jet_bound_holds
    (g_bg : SmoothRiemannianMetric I M) {σ : ℝ}
    {u₁ u₂ : tensorHs (I := I) (M := M) g_bg 0 2 σ}
    (hu₁ : isRealizableMetricPerturbationAt (I := I) g_bg u₁) (hu₂ : isRealizableMetricPerturbationAt (I := I) g_bg u₂)
    (α : M) {K : Set E} (hK : IsCompact K)
    (hKsub : K ⊆ interior ((extChartAt I α).target : Set E)) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ y ∈ K, ∀ l b : Fin (Module.finrank ℝ E),
      |reprDiffChartCompOnE (I := I) g_bg hu₁ hu₂ α l b y| ≤
          C₀ * iteratedCovGradJetSum (I := I) g_bg
            (realizableRepr (I := I) g_bg hu₁ - realizableRepr (I := I) g_bg hu₂)
            ((extChartAt I α).symm y) ∧
        (∀ a : Fin (Module.finrank ℝ E),
          |partialDeriv (E := E) a
              (reprDiffChartCompOnE (I := I) g_bg hu₁ hu₂ α l b) y| ≤
            C₀ * iteratedCovGradJetSum (I := I) g_bg
              (realizableRepr (I := I) g_bg hu₁ - realizableRepr (I := I) g_bg hu₂)
              ((extChartAt I α).symm y)) ∧
        (∀ c a : Fin (Module.finrank ℝ E),
          |partialDeriv (E := E) c
              (partialDeriv (E := E) a
                (reprDiffChartCompOnE (I := I) g_bg hu₁ hu₂ α l b)) y| ≤
            C₀ * iteratedCovGradJetSum (I := I) g_bg
              (realizableRepr (I := I) g_bg hu₁ - realizableRepr (I := I) g_bg hu₂)
              ((extChartAt I α).symm y)) := by
  classical
  letI : Bundle.RiemannianBundle (fun bb : M => TensorRSSpace 0 2 I bb) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g_bg 0 2
  set S : SmoothCcTensor g_bg 0 2 :=
    realizableRepr (I := I) g_bg hu₁ - realizableRepr (I := I) g_bg hu₂ with hS_def
  obtain ⟨C0, hC0_nn, hC0_bd⟩ :=
    reprDiffChartCompOnE_abs_le_riemannianFibreNorm (I := I) g_bg hu₁ hu₂ α hK hKsub
  obtain ⟨C1, hC1_nn, hC1_bd⟩ :=
    partialDeriv_reprDiffChartCompOnE_abs_le (I := I) g_bg hu₁ hu₂ α hK hKsub
  obtain ⟨C2, hC2_nn, hC2_bd⟩ :=
    partialDeriv2_reprDiffChartCompOnE_abs_le (I := I) g_bg hu₁ hu₂ α hK hKsub
  refine ⟨max C0 (max C1 C2), le_trans hC0_nn (le_max_left _ _), ?_⟩
  intro y hy l b
  set R : ℝ := iteratedCovGradJetSum (I := I) g_bg S ((extChartAt I α).symm y) with hR_def
  have hR_nn : 0 ≤ R := iteratedCovGradJetSum_nonneg (I := I) g_bg S _
  have h0_jet : ‖S.toSection ((extChartAt I α).symm y)‖ ≤ R := by
    rw [hR_def]
    exact iteratedCovGrad_norm_le_jetSum (I := I) g_bg S ((extChartAt I α).symm y) 0 (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · calc |reprDiffChartCompOnE (I := I) g_bg hu₁ hu₂ α l b y|
        ≤ C0 * ‖S.toSection ((extChartAt I α).symm y)‖ := hC0_bd y hy l b
      _ ≤ C0 * R := mul_le_mul_of_nonneg_left h0_jet hC0_nn
      _ ≤ max C0 (max C1 C2) * R :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hR_nn
  · intro a
    calc |partialDeriv (E := E) a (reprDiffChartCompOnE (I := I) g_bg hu₁ hu₂ α l b) y|
        ≤ C1 * R := hC1_bd y hy l b a
      _ ≤ max C0 (max C1 C2) * R :=
          mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _)) hR_nn
  · intro c a
    calc |partialDeriv (E := E) c
            (partialDeriv (E := E) a (reprDiffChartCompOnE (I := I) g_bg hu₁ hu₂ α l b)) y|
        ≤ C2 * R := hC2_bd y hy l b c a
      _ ≤ max C0 (max C1 C2) * R :=
          mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_right _ _)) hR_nn

set_option maxHeartbeats 1600000 in








omit [BoundarylessManifold I M] in
theorem chartMetricJet2DiffSup_realizeMetricAt_le_toHs_unconditional
    (g_bg : SmoothRiemannianMetric I M) {σ : ℝ}
    {u₁ u₂ : tensorHs (I := I) (M := M) g_bg 0 2 σ}
    (hu₁ : isRealizableMetricPerturbationAt (I := I) g_bg u₁) (hu₂ : isRealizableMetricPerturbationAt (I := I) g_bg u₂)
    (α : M) {K : Set E} (hK : IsCompact K)
    (hKsub : K ⊆ interior ((extChartAt I α).target : Set E))
    (k : ℕ) (h_super : 2 * k > Module.finrank ℝ E + 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K,
      chartMetricJet2DiffSup (I := I) (M := M)
          (realizeMetricAt (I := I) g_bg u₁) (realizeMetricAt (I := I) g_bg u₂) α y ≤
        C * ‖SmoothCcTensor.toHs (g := g_bg) (r := 0) (s := 2) (2 * k)
          (realizableRepr (I := I) g_bg hu₁ - realizableRepr (I := I) g_bg hu₂)‖ := by
  obtain ⟨C₀, hC₀_nn, hcovgrad_jet_bound⟩ :=
    hcovgrad_jet_bound_holds (I := I) g_bg hu₁ hu₂ α hK hKsub
  exact chartMetricJet2DiffSup_realizeMetricAt_le_toHs (I := I) g_bg hu₁ hu₂ α hKsub k h_super
    hC₀_nn hcovgrad_jet_bound

end MetricRealization
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
