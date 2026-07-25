import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Cross.EigenvectorChartCrossRightLimit
import DifferentialGeometry.Analysis.Elliptic.TensorRegularity.WeakSolution.WeakSolutionHeadline


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Tensor.TensorRSRiemannian
open TensorRSNabla
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Analysis.Laplacian.ChartLocalLaplacian

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma extDerivFun_apply_scalar (f : M → ℝ) (x : M) (v : TangentSpace I x) :
    extDerivFun (I := I) f x v = mfderiv I 𝓘(ℝ, ℝ) f x v := by
  simp only [extDerivFun, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe]
  simp only [NormedSpace.fromTangentSpace, ContinuousLinearEquiv.coe_mk,
    LinearEquiv.coe_mk]
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma covGradBundle_trivFibre_eq
    (r s : ℕ) (α : M) (b : M)
    (Φ : TangentSpace I b →L[ℝ] TensorRSSpace r s I b) :
    (trivializationAt (E →L[ℝ] TensorRSModel r s ℝ E)
        (fun y : M => TangentSpace I y →L[ℝ] TensorRSSpace r s I y) α
        ⟨b, Φ⟩).2 =
      ((trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b).comp
        (Φ.comp ((trivializationAt E (TangentSpace I) α).symmL ℝ b)) :=
  rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorChartComponentRaw_prependCovGradSlot
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin (s + 1) → Fin (Module.finrank ℝ E))
    {b : M} (hb : b ∈ (chartAt H α).source) :
    tensorChartComponentRaw (I := I) (M := M) g r (s + 1)
        (prependCovGradSlot (I := I) (M := M) g r s ζ S) α Idx Jdx b =
      extDerivFun (I := I) (ζ : M → ℝ) b
          (chartBasisVecFiber (I := I) α (Jdx 0) b) *
        tensorChartComponentRaw (I := I) (M := M) g r s S α Idx
          (Matrix.vecTail Jdx) b := by
  classical
  letI : TopologicalSpace (TotalSpace (Tensor0SModel r ℝ E)
      (fun y : M => Tensor0SSpace r I y)) := tensor0SBundle_topology r
  letI : TopologicalSpace (TotalSpace (Tensor0SModel (s + 1) ℝ E)
      (fun y : M => Tensor0SSpace (s + 1) I y)) := tensor0SBundle_topology (s + 1)
  letI : TopologicalSpace (TotalSpace (TensorRSModel r (s + 1) ℝ E)
      (fun y : M => TensorRSSpace r (s + 1) I y)) :=
    tensorRSBundle_topology r (s + 1)
  letI : FiberBundle (TensorRSModel r (s + 1) ℝ E)
      (fun y : M => TensorRSSpace r (s + 1) I y) :=
    tensorRSBundle_fiber r (s + 1)
  letI : VectorBundle ℝ (TensorRSModel r (s + 1) ℝ E)
      (fun y : M => TensorRSSpace r (s + 1) I y) :=
    tensorRSBundle_vector r (s + 1)
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact hb
  have hb_baseS1 : b ∈ (trivializationAt (TensorRSModel r (s + 1) ℝ E)
      (fun y : M => TensorRSSpace r (s + 1) I y) α).baseSet := by
    change b ∈ ((trivializationAt (Tensor0SModel r ℝ E)
        (fun y : M => Tensor0SSpace r I y) α).baseSet) ∩
      ((trivializationAt (Tensor0SModel (s + 1) ℝ E)
        (fun y : M => Tensor0SSpace (s + 1) I y) α).baseSet)
    exact ⟨hb_base, hb_base⟩
  set Φ : TangentSpace I b →L[ℝ] TensorRSSpace r s I b :=
    (extDerivFun (I := I) (ζ : M → ℝ) b).smulRight (S.toSection b) with hΦ_def
  rw [tensorChartComponentRaw_def]
  unfold tensorTrivProj
  rw [prependCovGradSlot_toSection_apply (I := I) (M := M) g r s ζ S b]
  rw [show ((extDerivFun (I := I) (ζ : M → ℝ) b).smulRight (S.toSection b)) = Φ
    from rfl]
  rw [Bundle.Trivialization.continuousLinearMapAt_apply,
    (trivializationAt (TensorRSModel r (s + 1) ℝ E)
        (fun y : M => TensorRSSpace r (s + 1) I y) α).coe_linearMapAt_of_mem
      (R := ℝ) hb_baseS1]
  beta_reduce
  rw [covGradBundleEquiv_trivializationAt_eq (I := I) (M := M) r s α hb_base Φ]
  rw [tensorChartComponentProjection_apply,
    covGradModelEquiv_apply (E := E) r s]
  rw [covGradBundle_trivFibre_eq (I := I) (M := M) r s α b Φ]
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  have hsymmL : (trivializationAt E (TangentSpace I) α).symmL ℝ b
      ((chartModelBasis E) (Jdx 0)) =
      chartBasisVecFiber (I := I) α (Jdx 0) b := rfl
  rw [hsymmL]
  rw [hΦ_def, ContinuousLinearMap.smulRight_apply]
  rw [map_smul, ContinuousLinearMap.smul_apply,
    ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  congr 1

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma partialDeriv_scalarOnE_eq_euclidPartial
    (f : M → ℝ) (α : M) (m : Fin (Module.finrank ℝ E))
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    partialDeriv (E := E) m (scalarOnE (I := I) α f)
        (extChartAt I α ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) =
      euclidPartial (E := E) m (chartPushedRaw I α f) y := by
  classical
  set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb_def
  have hy_pre : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
    rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
    exact hy
  have hphi_b : extChartAt I α b = (toEuclidean (E := E)).symm y := by
    rw [hb_def]; exact (extChartAt I α).right_inv hy_pre
  rw [euclidPartial_def]
  have hpushed_eq :
      chartPushedRaw I α f =ᶠ[𝓝 y]
        ((scalarOnE (I := I) α f) ∘ (toEuclidean (E := E)).symm) := by
    have hopen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
      chartTargetEuclid_isOpen (I := I) (M := M) α
    filter_upwards [hopen.mem_nhds hy] with z hz
    rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α f hz]
    rfl
  rw [Filter.EventuallyEq.fderiv_eq hpushed_eq]
  rw [(toEuclidean (E := E)).symm.comp_right_fderiv
    (f := scalarOnE (I := I) α f) (x := y)]
  rw [ContinuousLinearMap.comp_apply]
  rw [show (toEuclidean (E := E)).symm.toContinuousLinearMap
      (EuclideanSpace.single m (1 : ℝ)) = (chartModelBasis E) m from by
    rw [chartModelBasis_apply]; rfl]
  rw [partialDeriv]
  rw [show (toEuclidean (E := E)).symm y = extChartAt I α b from hphi_b.symm]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma extDerivFun_chartBasisVecFiber_eq_euclidPartial
    (ζ : C^∞⟮I, M; ℝ⟯) (α : M)
    (m : Fin (Module.finrank ℝ E))
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    extDerivFun (I := I) (ζ : M → ℝ)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
        (chartBasisVecFiber (I := I) α m
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) =
      euclidPartial (E := E) m (chartPushedRaw I α (ζ : M → ℝ)) y := by
  classical
  set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb_def
  have hy_pre : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
    rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
    exact hy
  have hb_chart : b ∈ (chartAt H α).source :=
    symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) α hy
  have hphi_b : extChartAt I α b = (toEuclidean (E := E)).symm y := by
    rw [hb_def]; exact (extChartAt I α).right_inv hy_pre
  have hb_int :
      extChartAt I α b ∈ interior ((extChartAt I α).target : Set E) := by
    rw [hphi_b, (isOpen_extChartAt_target (I := I) α).interior_eq]
    exact hy_pre
  rw [extDerivFun_apply_scalar (I := I) (ζ : M → ℝ) b
    (chartBasisVecFiber (I := I) α m b)]
  rw [mfderiv_chartBasisVecFiber_of_mdifferentiableAt (I := I) α
    (ζ.contMDiff.mdifferentiable (by norm_num)).mdifferentiableAt
    hb_chart hb_int m]
  exact partialDeriv_scalarOnE_eq_euclidPartial (I := I) (M := M)
    (ζ : M → ℝ) α m hy

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma tensorCovDerivAt_sum_smul_dir
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (b : M)
    (c : Fin (Module.finrank ℝ E) → ℝ) (v : Fin (Module.finrank ℝ E) → E) :
    tensorCovDerivAt (I := I) (M := M) g r s S b
        (∑ m : Fin (Module.finrank ℝ E), c m • v m) =
      ∑ m : Fin (Module.finrank ℝ E),
        c m • tensorCovDerivAt (I := I) (M := M) g r s S b (v m) := by
  classical
  rw [tensorCovDerivAt_def]
  rw [show (∑ m : Fin (Module.finrank ℝ E), c m • v m) =
      (∑ m : Fin (Module.finrank ℝ E), c m • v m :
        TangentSpace I b) from rfl]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [map_smul]
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma symm_mem_chartLeviCivitaGoodSet
    (α : M) {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∈
      chartLeviCivitaGoodSet (I := I) α := by
  set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb_def
  have hy_pre : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
    rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
    exact hy
  have hb_chart : b ∈ (chartAt H α).source :=
    symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) α hy
  have hphi_b : extChartAt I α b = (toEuclidean (E := E)).symm y := by
    rw [hb_def]; exact (extChartAt I α).right_inv hy_pre
  have hb_int :
      extChartAt I α b ∈ interior ((extChartAt I α).target : Set E) := by
    rw [hphi_b, (isOpen_extChartAt_target (I := I) α).interior_eq]
    exact hy_pre
  refine ⟨⟨?_, ?_⟩, hb_int⟩
  · rw [extChartAt_source]; exact hb_chart
  · rw [TangentBundle.trivializationAt_baseSet]; exact hb_chart

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorChartComponentRaw_covDerivAlongGrad
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    tensorChartComponentRaw (I := I) (M := M) g r s
        (covDerivAlongGrad (I := I) (M := M) g r s S ζ) α Idx Jdx
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) =
      ∑ m : Fin (Module.finrank ℝ E),
        gradChartCoeff (I := I) g α (ζ : M → ℝ) m
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
          (euclidPartial (E := E) m
              (chartPushedRaw I α
                (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx))
              y +
            covDerivLowerOrderTerm (I := I) (M := M) g r s S α m Idx Jdx y) := by
  classical
  set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb_def
  have hb_chart : b ∈ (chartAt H α).source :=
    symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) α hy
  have hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α :=
    symm_mem_chartLeviCivitaGoodSet (I := I) (M := M) α hy
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact hb_chart
  have hy_pre : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
    rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
    exact hy
  have hphi_b : extChartAt I α b = (toEuclidean (E := E)).symm y := by
    rw [hb_def]; exact (extChartAt I α).right_inv hy_pre
  have hb_int :
      extChartAt I α b ∈ interior ((extChartAt I α).target : Set E) := by
    rw [hphi_b, (isOpen_extChartAt_target (I := I) α).interior_eq]
    exact hy_pre
  rw [tensorChartComponentRaw_def]
  unfold tensorTrivProj
  rw [covDerivAlongGrad_toSection_apply (I := I) (M := M) g r s S ζ b]
  have hgrad : gradFun (I := I) g (ζ : M → ℝ) b =
      ∑ m : Fin (Module.finrank ℝ E),
        gradChartCoeff (I := I) g α (ζ : M → ℝ) m b •
          chartBasisVecFiber (I := I) α m b := by
    rw [← gradChartLocal_eq_gradFun (I := I) g α
      (ζ.contMDiff.mdifferentiable (by norm_num)).mdifferentiableAt
      hb_base hb_int]
    rfl
  rw [hgrad]
  rw [tensorCovDerivAt_sum_smul_dir (I := I) (M := M) g r s S b
    (fun m => gradChartCoeff (I := I) g α (ζ : M → ℝ) m b)
    (fun m => chartBasisVecFiber (I := I) α m b)]
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [map_smul, map_smul, smul_eq_mul]
  congr 1
  rw [tensorCovDerivAt_eq_chartTensorRSCovariantDerivative (I := I) (M := M)
    g r s S α m hb_good]
  exact covDerivComponent_eq_euclidPartial_add_lowerOrder (I := I) (M := M)
    g r s S α m Idx Jdx hy

noncomputable def crossLeftTestCoeff
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : CompIdx E r s) (Q : CompIdx E r (s + 1)) : EuclN → ℝ :=
  fun y =>
    euclidPartial (E := E) (Q.2 0)
        (chartPushedRaw I α ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) y *
      covChartMetricGramInv (I := I) (M := M) g r s α y
        (Q.1, Matrix.vecTail Q.2) P₀

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
lemma crossLeftTestCoeff_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : CompIdx E r s) (Q : CompIdx E r (s + 1)) (y : EuclN) :
    crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y =
      euclidPartial (E := E) (Q.2 0)
          (chartPushedRaw I α ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) y *
        covChartMetricGramInv (I := I) (M := M) g r s α y
          (Q.1, Matrix.vecTail Q.2) P₀ := rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem crossLeftTestCoeff_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : CompIdx E r s) (Q : CompIdx E r (s + 1)) :
    ContDiffOn ℝ ∞ (crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q)
      (chartTargetEuclid (I := I) (M := M) α) := by
  have hbump : ContDiffOn ℝ ∞
      (chartPushedRaw I α ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ))
      (chartTargetEuclid (I := I) (M := M) α) :=
    chartPushedRaw_bump_contDiffOn (I := I) (M := M) α
      (chartAtlasPOU I M α).contMDiff.contMDiffOn
  have hpartial : ContDiffOn ℝ ∞
      (euclidPartial (E := E) (Q.2 0)
        (chartPushedRaw I α ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)))
      (chartTargetEuclid (I := I) (M := M) α) :=
    euclidPartial_contDiffOn_target (I := I) (M := M) α (Q.2 0) hbump
  have hGinv : ContDiffOn ℝ ∞
      (fun y : EuclN => covChartMetricGramInv (I := I) (M := M) g r s α y
        (Q.1, Matrix.vecTail Q.2) P₀)
      (chartTargetEuclid (I := I) (M := M) α) :=
    covChartMetricGramInv_entry_contDiffOn (I := I) (M := M) g r s α
      (Q.1, Matrix.vecTail Q.2) P₀
  exact hpartial.mul hGinv

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorComponentEuclid_prependCovGradSlot_rotatedTestSection_eqOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : CompIdx E r s)
    {χ : M → ℝ} (hχs : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ χ (chartAt H α).source)
    (hχt : tsupport χ ⊆ (chartAt H α).source)
    (Q : CompIdx E r (s + 1)) :
    Set.EqOn
      (tensorComponentEuclid (I := I) (M := M) g r (s + 1)
        (prependCovGradSlot (I := I) (M := M) g r s (chartAtlasPOU I M α)
          (rotatedTestSection (I := I) (M := M) g r s α P₀ χ hχs hχt))
        α Q)
      (fun y => crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y *
        chartPushedRaw I α χ y)
      (chartTargetEuclid (I := I) (M := M) α) := by
  intro y hy
  rw [tensorComponentEuclid_apply_of_mem (I := I) (M := M) g r (s + 1)
    (prependCovGradSlot (I := I) (M := M) g r s (chartAtlasPOU I M α)
      (rotatedTestSection (I := I) (M := M) g r s α P₀ χ hχs hχt)) α Q hy]
  have hb_chart : (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∈
      (chartAt H α).source :=
    symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) α hy
  rw [tensorChartComponentRaw_prependCovGradSlot (I := I) (M := M) g r s
    (chartAtlasPOU I M α)
    (rotatedTestSection (I := I) (M := M) g r s α P₀ χ hχs hχt) α Q.1 Q.2
    hb_chart]
  rw [show tensorChartComponentRaw (I := I) (M := M) g r s
        (rotatedTestSection (I := I) (M := M) g r s α P₀ χ hχs hχt) α Q.1
        (Matrix.vecTail Q.2)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) =
      tensorChartComponentRaw (I := I) (M := M) g r s
        (rotatedTestSection (I := I) (M := M) g r s α P₀ χ hχs hχt) α
        (Q.1, Matrix.vecTail Q.2).1 (Q.1, Matrix.vecTail Q.2).2
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) from rfl]
  rw [rotatedTestSection_chartComp (I := I) (M := M) g r s α P₀ hχs hχt
    (Q.1, Matrix.vecTail Q.2) hy]
  rw [extDerivFun_chartBasisVecFiber_eq_euclidPartial (I := I) (M := M)
    (chartAtlasPOU I M α) α (Q.2 0) hy]
  simp only [crossLeftTestCoeff_def]
  ring

noncomputable def gradChartCoeffEuclid
    (g : SmoothRiemannianMetric I M) (α : M) (ζ : M → ℝ)
    (m : Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  fun y =>
    ∑ j : Fin (Module.finrank ℝ E),
      chartInvGramEuclid (I := I) g α m j y *
        euclidPartial (E := E) j (chartPushedRaw I α ζ) y

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
theorem gradChartCoeff_eq_gradChartCoeffEuclid
    (g : SmoothRiemannianMetric I M) (α : M) (ζ : M → ℝ)
    (m : Fin (Module.finrank ℝ E))
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    gradChartCoeff (I := I) g α ζ m
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) =
      gradChartCoeffEuclid (I := I) (M := M) g α ζ m y := by
  classical
  rw [gradChartCoeff_def, gradChartCoeffEuclid]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [show chartInvGramMatrix (I := I) g α
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) m j =
      chartInvGramEuclid (I := I) g α m j y from by
    rw [chartInvGramEuclid_def, chartInvGramOnE_def]]
  rw [partialDeriv_scalarOnE_eq_euclidPartial (I := I) (M := M) ζ α j hy]

omit [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem gradChartCoeffEuclid_contDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    {ζ : M → ℝ} (hζ : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ ζ (chartAt H α).source)
    (m : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (gradChartCoeffEuclid (I := I) (M := M) g α ζ m)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have hbump : ContDiffOn ℝ ∞ (chartPushedRaw I α ζ)
      (chartTargetEuclid (I := I) (M := M) α) :=
    chartPushedRaw_bump_contDiffOn (I := I) (M := M) α hζ
  refine ContDiffOn.sum (fun j _ => ?_)
  exact (chartInvGramEuclid_contDiffOn (I := I) (M := M) g α m j).mul
    (euclidPartial_contDiffOn_target (I := I) (M := M) α j hbump)

omit [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma covDerivLowerOrderTerm_rotatedTestSection_eqOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : CompIdx E r s)
    {χ : M → ℝ} (hχs : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ χ (chartAt H α).source)
    (hχt : tsupport χ ⊆ (chartAt H α).source)
    (m : Fin (Module.finrank ℝ E)) (Q : CompIdx E r s)
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    covDerivLowerOrderTerm (I := I) (M := M) g r s
        (rotatedTestSection (I := I) (M := M) g r s α P₀ χ hχs hχt)
        α m Q.1 Q.2 y =
      lowerOrderRotationLOCoeff (I := I) (M := M) g r s α P₀ m Q y *
        chartPushedRaw I α χ y := by
  classical
  rw [covDerivLowerOrderTerm_def, lowerOrderRotationLOCoeff, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [rotatedTestSection_chartComp (I := I) (M := M) g r s α P₀ hχs hχt p hy]
  ring

noncomputable def crossRightTestGradCoeff
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : CompIdx E r s) (Q : CompIdx E r s)
    (l : Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  fun y =>
    gradChartCoeffEuclid (I := I) (M := M) g α
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) l y *
      gramInvEntry (I := I) (M := M) g r s α Q P₀ y

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
lemma crossRightTestGradCoeff_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : CompIdx E r s) (Q : CompIdx E r s)
    (l : Fin (Module.finrank ℝ E)) (y : EuclN) :
    crossRightTestGradCoeff (I := I) (M := M) g r s α P₀ Q l y =
      gradChartCoeffEuclid (I := I) (M := M) g α
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) l y *
        gramInvEntry (I := I) (M := M) g r s α Q P₀ y := rfl

noncomputable def crossRightTestValueCoeff
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : CompIdx E r s) (Q : CompIdx E r s) : EuclN → ℝ :=
  fun y =>
    ∑ m : Fin (Module.finrank ℝ E),
      gradChartCoeffEuclid (I := I) (M := M) g α
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) m y *
        (euclidPartial (E := E) m
            (gramInvEntry (I := I) (M := M) g r s α Q P₀) y +
          lowerOrderRotationLOCoeff (I := I) (M := M) g r s α P₀ m Q y)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
lemma crossRightTestValueCoeff_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : CompIdx E r s) (Q : CompIdx E r s) (y : EuclN) :
    crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y =
      ∑ m : Fin (Module.finrank ℝ E),
        gradChartCoeffEuclid (I := I) (M := M) g α
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) m y *
          (euclidPartial (E := E) m
              (gramInvEntry (I := I) (M := M) g r s α Q P₀) y +
            lowerOrderRotationLOCoeff (I := I) (M := M) g r s α P₀ m Q y) := rfl

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem crossRightTestGradCoeff_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : CompIdx E r s) (Q : CompIdx E r s)
    (l : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (crossRightTestGradCoeff (I := I) (M := M) g r s α P₀ Q l)
      (chartTargetEuclid (I := I) (M := M) α) :=
  (gradChartCoeffEuclid_contDiffOn (I := I) (M := M) g α
      (chartAtlasPOU I M α).contMDiff.contMDiffOn l).mul
    (gramInvEntry_contDiffOn (I := I) (M := M) g r s α Q P₀)

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem crossRightTestValueCoeff_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : CompIdx E r s) (Q : CompIdx E r s) :
    ContDiffOn ℝ ∞ (crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  refine ContDiffOn.sum (fun m _ => ?_)
  have hgrad : ContDiffOn ℝ ∞
      (gradChartCoeffEuclid (I := I) (M := M) g α
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) m)
      (chartTargetEuclid (I := I) (M := M) α) :=
    gradChartCoeffEuclid_contDiffOn (I := I) (M := M) g α
      (chartAtlasPOU I M α).contMDiff.contMDiffOn m
  have hGinvPartial : ContDiffOn ℝ ∞
      (euclidPartial (E := E) m
        (gramInvEntry (I := I) (M := M) g r s α Q P₀))
      (chartTargetEuclid (I := I) (M := M) α) :=
    euclidPartial_contDiffOn_target (I := I) (M := M) α m
      (gramInvEntry_contDiffOn (I := I) (M := M) g r s α Q P₀)
  have hLO : ContDiffOn ℝ ∞
      (lowerOrderRotationLOCoeff (I := I) (M := M) g r s α P₀ m Q)
      (chartTargetEuclid (I := I) (M := M) α) :=
    lowerOrderRotationLOCoeff_contDiffOn (I := I) (M := M) g r s α P₀ m Q
  exact hgrad.mul (hGinvPartial.add hLO)

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorComponentEuclid_covDerivAlongGrad_rotatedTestSection_eqOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : CompIdx E r s)
    {χ : M → ℝ} (hχs : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ χ (chartAt H α).source)
    (hχt : tsupport χ ⊆ (chartAt H α).source)
    (Q : CompIdx E r s) :
    Set.EqOn
      (tensorComponentEuclid (I := I) (M := M) g r s
        (covDerivAlongGrad (I := I) (M := M) g r s
          (rotatedTestSection (I := I) (M := M) g r s α P₀ χ hχs hχt)
          (chartAtlasPOU I M α))
        α Q)
      (fun y => crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y *
          chartPushedRaw I α χ y +
        ∑ l : Fin (Module.finrank ℝ E),
          crossRightTestGradCoeff (I := I) (M := M) g r s α P₀ Q l y *
            euclidPartial (E := E) l (chartPushedRaw I α χ) y)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  intro y hy
  rw [tensorComponentEuclid_apply_of_mem (I := I) (M := M) g r s
    (covDerivAlongGrad (I := I) (M := M) g r s
      (rotatedTestSection (I := I) (M := M) g r s α P₀ χ hχs hχt)
      (chartAtlasPOU I M α)) α Q hy]
  rw [tensorChartComponentRaw_covDerivAlongGrad (I := I) (M := M) g r s
    (chartAtlasPOU I M α)
    (rotatedTestSection (I := I) (M := M) g r s α P₀ χ hχs hχt) α Q.1 Q.2 hy]
  have hterm : ∀ m : Fin (Module.finrank ℝ E),
      gradChartCoeff (I := I) g α
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) m
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
          (euclidPartial (E := E) m
              (chartPushedRaw I α
                (tensorChartComponentRaw (I := I) (M := M) g r s
                  (rotatedTestSection (I := I) (M := M) g r s α P₀ χ hχs hχt) α
                  Q.1 Q.2)) y +
            covDerivLowerOrderTerm (I := I) (M := M) g r s
              (rotatedTestSection (I := I) (M := M) g r s α P₀ χ hχs hχt)
              α m Q.1 Q.2 y) =
        gradChartCoeffEuclid (I := I) (M := M) g α
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) m y *
            (euclidPartial (E := E) m
                (gramInvEntry (I := I) (M := M) g r s α Q P₀) y +
              lowerOrderRotationLOCoeff (I := I) (M := M) g r s α P₀ m Q y) *
          chartPushedRaw I α χ y +
        gradChartCoeffEuclid (I := I) (M := M) g α
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) m y *
            gramInvEntry (I := I) (M := M) g r s α Q P₀ y *
          euclidPartial (E := E) m (chartPushedRaw I α χ) y := by
    intro m
    rw [gradChartCoeff_eq_gradChartCoeffEuclid (I := I) (M := M) g α
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) m hy]
    rw [show tensorChartComponentRaw (I := I) (M := M) g r s
          (rotatedTestSection (I := I) (M := M) g r s α P₀ χ hχs hχt) α Q.1 Q.2 =
        tensorChartComponentRaw (I := I) (M := M) g r s
          (rotatedTestSection (I := I) (M := M) g r s α P₀ χ hχs hχt) α
          Q.1 Q.2 from rfl]
    rw [euclidPartial_chartPushedRaw_rotatedTestSection_eqOn (I := I) (M := M)
      g r s α P₀ hχs hχt Q m hy]
    rw [covDerivLowerOrderTerm_rotatedTestSection_eqOn (I := I) (M := M)
      g r s α P₀ hχs hχt m Q hy]
    ring
  rw [Finset.sum_congr rfl (fun m _ => hterm m)]
  rw [Finset.sum_add_distrib]
  simp only [crossRightTestValueCoeff_def, crossRightTestGradCoeff_def,
    Finset.sum_mul]

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorComponentEuclid_prependCovGradSlot_rotatedTestSection_chartTestPullback_eqOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : CompIdx E r s)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α)
    (Q : CompIdx E r (s + 1)) :
    Set.EqOn
      (tensorComponentEuclid (I := I) (M := M) g r (s + 1)
        (prependCovGradSlot (I := I) (M := M) g r s (chartAtlasPOU I M α)
          (rotatedTestSection (I := I) (M := M) g r s α P₀
            (chartTestPullback (I := I) (M := M) α ψ)
            (chartTestPullback_contMDiffOn (I := I) (M := M) α hψ)
            (chartTestPullback_tsupport_subset_source (I := I) (M := M) α
              hψ_cs hψ_supp)))
        α Q)
      (fun y => crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y * ψ y)
      (chartTargetEuclid (I := I) (M := M) α) := by
  intro y hy
  rw [tensorComponentEuclid_prependCovGradSlot_rotatedTestSection_eqOn
    (I := I) (M := M) g r s α P₀
    (chartTestPullback_contMDiffOn (I := I) (M := M) α hψ)
    (chartTestPullback_tsupport_subset_source (I := I) (M := M) α hψ_cs hψ_supp)
    Q hy]
  beta_reduce
  rw [chartPushedRaw_chartTestPullback_eqOn (I := I) (M := M) α ψ hy]

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorComponentEuclid_covDerivAlongGrad_rotatedTestSection_chartTestPullback_eqOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : CompIdx E r s)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α)
    (Q : CompIdx E r s) :
    Set.EqOn
      (tensorComponentEuclid (I := I) (M := M) g r s
        (covDerivAlongGrad (I := I) (M := M) g r s
          (rotatedTestSection (I := I) (M := M) g r s α P₀
            (chartTestPullback (I := I) (M := M) α ψ)
            (chartTestPullback_contMDiffOn (I := I) (M := M) α hψ)
            (chartTestPullback_tsupport_subset_source (I := I) (M := M) α
              hψ_cs hψ_supp))
          (chartAtlasPOU I M α))
        α Q)
      (fun y => crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y *
          ψ y +
        ∑ l : Fin (Module.finrank ℝ E),
          crossRightTestGradCoeff (I := I) (M := M) g r s α P₀ Q l y *
            euclidPartial (E := E) l ψ y)
      (chartTargetEuclid (I := I) (M := M) α) := by
  intro y hy
  rw [tensorComponentEuclid_covDerivAlongGrad_rotatedTestSection_eqOn
    (I := I) (M := M) g r s α P₀
    (chartTestPullback_contMDiffOn (I := I) (M := M) α hψ)
    (chartTestPullback_tsupport_subset_source (I := I) (M := M) α hψ_cs hψ_supp)
    Q hy]
  beta_reduce
  rw [chartPushedRaw_chartTestPullback_eqOn (I := I) (M := M) α ψ hy]
  congr 1
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [euclidPartial_chartPushedRaw_chartTestPullback_eqOn (I := I) (M := M)
    α ψ l hy]

section ElaborationTests

variable (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
  (P₀ : CompIdx E r s)

example (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin (s + 1) → Fin (Module.finrank ℝ E))
    (ζ : C^∞⟮I, M; ℝ⟯) (S : SmoothCcTensor g r s)
    {b : M} (hb : b ∈ (chartAt H α).source) :
    tensorChartComponentRaw (I := I) (M := M) g r (s + 1)
        (prependCovGradSlot (I := I) (M := M) g r s ζ S) α Idx Jdx b =
      extDerivFun (I := I) (ζ : M → ℝ) b
          (chartBasisVecFiber (I := I) α (Jdx 0) b) *
        tensorChartComponentRaw (I := I) (M := M) g r s S α Idx
          (Matrix.vecTail Jdx) b :=
  tensorChartComponentRaw_prependCovGradSlot (I := I) (M := M) g r s ζ S α
    Idx Jdx hb

example {χ : M → ℝ} (hχs : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ χ (chartAt H α).source)
    (hχt : tsupport χ ⊆ (chartAt H α).source) (Q : CompIdx E r (s + 1)) :
    Set.EqOn
      (tensorComponentEuclid (I := I) (M := M) g r (s + 1)
        (prependCovGradSlot (I := I) (M := M) g r s (chartAtlasPOU I M α)
          (rotatedTestSection (I := I) (M := M) g r s α P₀ χ hχs hχt))
        α Q)
      (fun y => crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y *
        chartPushedRaw I α χ y)
      (chartTargetEuclid (I := I) (M := M) α) :=
  tensorComponentEuclid_prependCovGradSlot_rotatedTestSection_eqOn
    (I := I) (M := M) g r s α P₀ hχs hχt Q

example {χ : M → ℝ} (hχs : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ χ (chartAt H α).source)
    (hχt : tsupport χ ⊆ (chartAt H α).source) (Q : CompIdx E r s) :
    Set.EqOn
      (tensorComponentEuclid (I := I) (M := M) g r s
        (covDerivAlongGrad (I := I) (M := M) g r s
          (rotatedTestSection (I := I) (M := M) g r s α P₀ χ hχs hχt)
          (chartAtlasPOU I M α))
        α Q)
      (fun y => crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y *
          chartPushedRaw I α χ y +
        ∑ l : Fin (Module.finrank ℝ E),
          crossRightTestGradCoeff (I := I) (M := M) g r s α P₀ Q l y *
            euclidPartial (E := E) l (chartPushedRaw I α χ) y)
      (chartTargetEuclid (I := I) (M := M) α) :=
  tensorComponentEuclid_covDerivAlongGrad_rotatedTestSection_eqOn
    (I := I) (M := M) g r s α P₀ hχs hχt Q

end ElaborationTests

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
