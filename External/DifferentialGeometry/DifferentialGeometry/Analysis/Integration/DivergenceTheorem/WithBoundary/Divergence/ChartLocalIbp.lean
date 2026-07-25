import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.Divergence.LocalFormula
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.LocalFormula
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.TangentAction
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.ChartCoeffPullback
import DifferentialGeometry.Analysis.Integration.Measure.Family
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Topology.Algebra.Support


noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff Matrix

namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem
namespace WithBoundary

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private def chartImageOfTsupport (α : M) (φ : M → ℝ) : Set E :=
  (extChartAt I α) '' tsupport φ

omit [InnerProductSpace ℝ E] [Module.Finite ℝ E] [IsManifold I ∞ M] in
private lemma chartImageOfTsupport_isCompact
    (α : M) {φ : M → ℝ}
    (hφ_compactSupp : HasCompactSupport φ)
    (hφ_supp : tsupport φ ⊆ (chartAt H α).source) :
    IsCompact (chartImageOfTsupport (I := I) α φ) := by
  unfold chartImageOfTsupport
  have hcontOn : ContinuousOn (extChartAt I α) (tsupport φ) := by
    refine (continuousOn_extChartAt (I := I) α).mono ?_
    intro x hx
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    exact hφ_supp hx
  exact (hφ_compactSupp : IsCompact (tsupport φ)).image_of_continuousOn hcontOn

omit [InnerProductSpace ℝ E] [Module.Finite ℝ E] [IsManifold I ∞ M] in
private lemma chartImageOfTsupport_subset_target
    (α : M) {φ : M → ℝ}
    (hφ_supp : tsupport φ ⊆ (chartAt H α).source) :
    chartImageOfTsupport (I := I) α φ ⊆ (extChartAt I α).target := by
  intro y hy
  rcases hy with ⟨x, hxsupp, hxy⟩
  have hxsrc : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    exact hφ_supp hxsupp
  have : (extChartAt I α) x ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source hxsrc
  rwa [hxy] at this

omit [InnerProductSpace ℝ E] [Module.Finite ℝ E] [IsManifold I ∞ M] in
private lemma chartImageOfTsupport_isClosed
    (α : M) {φ : M → ℝ}
    (hφ_compactSupp : HasCompactSupport φ)
    (hφ_supp : tsupport φ ⊆ (chartAt H α).source) :
    IsClosed (chartImageOfTsupport (I := I) α φ) :=
  (chartImageOfTsupport_isCompact (I := I) α hφ_compactSupp hφ_supp).isClosed

omit [InnerProductSpace ℝ E] [Module.Finite ℝ E] in
private lemma chartImageOfTsupport_subset_interior_target
    (α : M) {φ : M → ℝ}
    (hφ_supp : tsupport φ ⊆ (chartAt H α).source)
    (hφ_int : tsupport φ ⊆ I.interior M) :
    chartImageOfTsupport (I := I) α φ ⊆ interior (extChartAt I α).target := by
  intro y hy
  rcases hy with ⟨x, hxsupp, hxy⟩
  have hx_src : x ∈ (chartAt H α).source := hφ_supp hxsupp
  have hx_int : x ∈ I.interior M := hφ_int hxsupp
  have h := extChartAt_mem_interior_target_of_isInteriorPoint
    (I := I) (M := M) α hx_src hx_int
  rwa [hxy] at h

private def vwIntegrandOnE
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (i : Fin (Module.finrank ℝ E)) : E → ℝ :=
  fun y => (extChartAt I α).target.indicator
    (fun z => chartCoeffOnE (I := I) α X i z * chartDensityOnE (I := I) g α z) y

omit [InnerProductSpace ℝ E] in
private lemma vwIntegrandOnE_apply_of_mem
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (i : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ (extChartAt I α).target) :
    vwIntegrandOnE (I := I) g α X i y =
      chartCoeffOnE (I := I) α X i y * chartDensityOnE (I := I) g α y :=
  Set.indicator_of_mem hy _

omit [InnerProductSpace ℝ E] in
private lemma vwIntegrandOnE_apply_of_notMem
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (i : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∉ (extChartAt I α).target) :
    vwIntegrandOnE (I := I) g α X i y = 0 :=
  Set.indicator_of_notMem hy _

omit [InnerProductSpace ℝ E] in
private lemma vwIntegrandOnE_contDiffOn_interior_target
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (i : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (vwIntegrandOnE (I := I) g α X i)
      (interior (extChartAt I α).target) := by
  have hsmooth : ContDiffOn ℝ ∞
      (fun y : E => chartCoeffOnE (I := I) α X i y * chartDensityOnE (I := I) g α y)
      (extChartAt I α).target :=
    chartCoeffOnE_mul_chartDensityOnE_contDiffOn (I := I) g α X i
  refine (hsmooth.mono interior_subset).congr ?_
  intro y hy
  rw [vwIntegrandOnE_apply_of_mem (I := I) g α X i (interior_subset hy)]

private def phiOnE (α : M) (φ : M → ℝ) : E → ℝ :=
  fun y => (extChartAt I α).target.indicator
    (fun z => φ ((extChartAt I α).symm z)) y

omit [InnerProductSpace ℝ E] [Module.Finite ℝ E] [IsManifold I ∞ M] in
private lemma phiOnE_apply_of_mem (α : M) (φ : M → ℝ) {y : E}
    (hy : y ∈ (extChartAt I α).target) :
    phiOnE (I := I) α φ y = φ ((extChartAt I α).symm y) :=
  Set.indicator_of_mem hy _

omit [InnerProductSpace ℝ E] [Module.Finite ℝ E] [IsManifold I ∞ M] in
private lemma phiOnE_apply_of_notMem (α : M) (φ : M → ℝ) {y : E}
    (hy : y ∉ (extChartAt I α).target) :
    phiOnE (I := I) α φ y = 0 :=
  Set.indicator_of_notMem hy _

omit [InnerProductSpace ℝ E] [Module.Finite ℝ E] [IsManifold I ∞ M] in
private lemma phiOnE_eq_scalarOnE_on_target
    (α : M) (φ : M → ℝ) {y : E}
    (hy : y ∈ (extChartAt I α).target) :
    phiOnE (I := I) α φ y = scalarOnE (I := I) α φ y := by
  rw [phiOnE_apply_of_mem (I := I) α φ hy]
  rfl

omit [InnerProductSpace ℝ E] [Module.Finite ℝ E] in
private lemma phiOnE_contDiffOn_interior_target
    (α : M) {φ : M → ℝ} (hφ : ContMDiff I 𝓘(ℝ) ∞ φ) :
    ContDiffOn ℝ ∞ (phiOnE (I := I) α φ)
      (interior (extChartAt I α).target) := by
  have hsmooth : ContDiffOn ℝ ∞
      (scalarOnE (I := I) α φ) (extChartAt I α).target :=
    scalarOnE_contDiffOn (I := I) α hφ
  refine (hsmooth.mono interior_subset).congr ?_
  intro y hy
  exact phiOnE_eq_scalarOnE_on_target (I := I) α φ (interior_subset hy)

omit [InnerProductSpace ℝ E] [Module.Finite ℝ E] in
private lemma contDiff_of_smooth_on_open_zero_outside
    {U : Set E} (hU : IsOpen U) {K : Set E} (hK : IsClosed K)
    (hKU : K ⊆ U) {f : E → ℝ}
    (hf_smooth : ContDiffOn ℝ ∞ f U)
    (hf_zero : ∀ y, y ∉ K → f y = 0) :
    ContDiff ℝ ∞ f := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y ∈ U
  · exact (hf_smooth.contDiffWithinAt hy).contDiffAt (hU.mem_nhds hy)
  · have hyK : y ∉ K := fun h => hy (hKU h)
    have hKc_open : IsOpen Kᶜ := hK.isOpen_compl
    have hf_zero_on : Kᶜ ∈ 𝓝 y := hKc_open.mem_nhds hyK
    have hzero_at : ContDiffAt ℝ ∞ (fun _ : E => (0 : ℝ)) y :=
      (contDiff_const).contDiffAt
    refine hzero_at.congr_of_eventuallyEq ?_
    filter_upwards [hf_zero_on] with z hz
    exact hf_zero z hz

omit [InnerProductSpace ℝ E] [Module.Finite ℝ E] [IsManifold I ∞ M] in
private lemma phiOnE_support_subset_chartImage
    (α : M) (φ : M → ℝ) :
    Function.support (phiOnE (I := I) α φ) ⊆ chartImageOfTsupport (I := I) α φ := by
  intro y hy
  rw [Function.mem_support] at hy
  by_cases hyT : y ∈ (extChartAt I α).target
  · rw [phiOnE_apply_of_mem (I := I) α φ hyT] at hy
    refine ⟨(extChartAt I α).symm y, ?_, ?_⟩
    · exact subset_tsupport _ hy
    · exact (extChartAt I α).right_inv hyT
  · rw [phiOnE_apply_of_notMem (I := I) α φ hyT] at hy
    exact (hy rfl).elim

omit [InnerProductSpace ℝ E] [Module.Finite ℝ E] [IsManifold I ∞ M] in
private lemma phiOnE_tsupport_subset_chartImage
    (α : M) {φ : M → ℝ}
    (hφ_compactSupp : HasCompactSupport φ)
    (hφ_supp : tsupport φ ⊆ (chartAt H α).source) :
    tsupport (phiOnE (I := I) α φ) ⊆ chartImageOfTsupport (I := I) α φ := by
  refine closure_minimal (phiOnE_support_subset_chartImage (I := I) α φ) ?_
  exact chartImageOfTsupport_isClosed (I := I) α hφ_compactSupp hφ_supp

omit [InnerProductSpace ℝ E] [Module.Finite ℝ E] [IsManifold I ∞ M] in
private lemma phiOnE_hasCompactSupport
    (α : M) {φ : M → ℝ}
    (hφ_compactSupp : HasCompactSupport φ)
    (hφ_supp : tsupport φ ⊆ (chartAt H α).source) :
    HasCompactSupport (phiOnE (I := I) α φ) := by
  refine HasCompactSupport.intro
    (chartImageOfTsupport_isCompact (I := I) α hφ_compactSupp hφ_supp) ?_
  intro y hy
  by_cases hyT : y ∈ (extChartAt I α).target
  · rw [phiOnE_apply_of_mem (I := I) α φ hyT]
    by_contra hne
    have : (extChartAt I α).symm y ∈ tsupport φ := subset_tsupport _ hne
    have : y ∈ chartImageOfTsupport (I := I) α φ :=
      ⟨(extChartAt I α).symm y, this, (extChartAt I α).right_inv hyT⟩
    exact hy this
  · exact phiOnE_apply_of_notMem (I := I) α φ hyT

omit [InnerProductSpace ℝ E] [Module.Finite ℝ E] in
private lemma phiOnE_contDiff
    (α : M) {φ : M → ℝ} (hφ : ContMDiff I 𝓘(ℝ) ∞ φ)
    (hφ_compactSupp : HasCompactSupport φ)
    (hφ_supp : tsupport φ ⊆ (chartAt H α).source)
    (hφ_int : tsupport φ ⊆ I.interior M) :
    ContDiff ℝ ∞ (phiOnE (I := I) α φ) := by
  refine contDiff_of_smooth_on_open_zero_outside
    (U := interior (extChartAt I α).target)
    isOpen_interior
    (K := chartImageOfTsupport (I := I) α φ)
    (chartImageOfTsupport_isClosed (I := I) α hφ_compactSupp hφ_supp)
    (chartImageOfTsupport_subset_interior_target (I := I) α hφ_supp hφ_int) ?_ ?_
  · exact phiOnE_contDiffOn_interior_target (I := I) α hφ
  · intro y hy
    by_cases hyT : y ∈ (extChartAt I α).target
    · rw [phiOnE_apply_of_mem (I := I) α φ hyT]
      by_contra hne
      have : (extChartAt I α).symm y ∈ tsupport φ := subset_tsupport _ hne
      have : y ∈ chartImageOfTsupport (I := I) α φ :=
        ⟨(extChartAt I α).symm y, this, (extChartAt I α).right_inv hyT⟩
      exact hy this
    · exact phiOnE_apply_of_notMem (I := I) α φ hyT

omit [InnerProductSpace ℝ E] in
private lemma vwIntegrandOnE_differentiableOn_interior_target
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (i : Fin (Module.finrank ℝ E)) :
    ∀ y ∈ interior (extChartAt I α).target,
      DifferentiableAt ℝ (vwIntegrandOnE (I := I) g α X i) y := by
  intro y hy
  have h_at : ContDiffWithinAt ℝ ∞
      (vwIntegrandOnE (I := I) g α X i)
      (interior (extChartAt I α).target) y :=
    vwIntegrandOnE_contDiffOn_interior_target (I := I) g α X i y hy
  exact ((h_at.contDiffAt (isOpen_interior.mem_nhds hy)).differentiableAt (by simp))

omit [InnerProductSpace ℝ E] [Module.Finite ℝ E] [IsManifold I ∞ M] in
private lemma fderiv_phiOnE_eq_fderiv_scalarOnE
    (α : M) (φ : M → ℝ)
    {y : E} (hy : y ∈ interior (extChartAt I α).target) :
    fderiv ℝ (phiOnE (I := I) α φ) y =
      fderiv ℝ (scalarOnE (I := I) α φ) y := by
  have h_eq : phiOnE (I := I) α φ =ᶠ[𝓝 y] scalarOnE (I := I) α φ := by
    filter_upwards [isOpen_interior.mem_nhds hy] with z hz
    exact phiOnE_eq_scalarOnE_on_target (I := I) α φ (interior_subset hz)
  exact Filter.EventuallyEq.fderiv_eq h_eq

omit [InnerProductSpace ℝ E] in
private theorem ibp_per_index
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {φ : M → ℝ} (hφ : ContMDiff I 𝓘(ℝ) ∞ φ)
    (hφ_compactSupp : HasCompactSupport φ)
    (hφ_supp : tsupport φ ⊆ (chartAt H α).source)
    (hφ_int : tsupport φ ⊆ I.interior M)
    (i : Fin (Module.finrank ℝ E)) :
    ∫ y, vwIntegrandOnE (I := I) g α X i y *
        fderiv ℝ (phiOnE (I := I) α φ) y ((chartModelBasis E) i)
        ∂(modelHaar (E := E)) =
      -∫ y, fderiv ℝ (vwIntegrandOnE (I := I) g α X i) y
            ((chartModelBasis E) i) *
          phiOnE (I := I) α φ y
        ∂(modelHaar (E := E)) := by
  have hphi_smooth : ContDiff ℝ ∞ (phiOnE (I := I) α φ) :=
    phiOnE_contDiff (I := I) α hφ hφ_compactSupp hφ_supp hφ_int
  have hphi_compactSupp : HasCompactSupport (phiOnE (I := I) α φ) :=
    phiOnE_hasCompactSupport (I := I) α hφ_compactSupp hφ_supp
  have hvw_diff_on_interior :=
    vwIntegrandOnE_differentiableOn_interior_target (I := I) g α X i
  have hphi_tsupp_in_interior_target : tsupport (phiOnE (I := I) α φ) ⊆
      interior (extChartAt I α).target := by
    refine (phiOnE_tsupport_subset_chartImage (I := I) α hφ_compactSupp hφ_supp).trans ?_
    exact chartImageOfTsupport_subset_interior_target (I := I) α hφ_supp hφ_int
  have hvw_diff_tsupp_phi : ∀ y ∈ tsupport (phiOnE (I := I) α φ),
      DifferentiableAt ℝ (vwIntegrandOnE (I := I) g α X i) y :=
    fun y hy => hvw_diff_on_interior y (hphi_tsupp_in_interior_target hy)
  have hphi_diff : ∀ y, DifferentiableAt ℝ (phiOnE (I := I) α φ) y :=
    fun y => hphi_smooth.differentiable (by simp) |>.differentiableAt
  have hphi_diff_tsupp_vw : ∀ y ∈ tsupport (vwIntegrandOnE (I := I) g α X i),
      DifferentiableAt ℝ (phiOnE (I := I) α φ) y :=
    fun y _ => hphi_diff y
  haveI : IsFiniteMeasureOnCompacts (modelHaar (E := E)) := by infer_instance
  have hI1_smooth : ContDiff ℝ ∞
      (fun y => vwIntegrandOnE (I := I) g α X i y * phiOnE (I := I) α φ y) := by
    refine contDiff_of_smooth_on_open_zero_outside
      (U := interior (extChartAt I α).target)
      isOpen_interior
      (K := chartImageOfTsupport (I := I) α φ)
      (chartImageOfTsupport_isClosed (I := I) α hφ_compactSupp hφ_supp)
      (chartImageOfTsupport_subset_interior_target (I := I) α hφ_supp hφ_int) ?_ ?_
    · exact (vwIntegrandOnE_contDiffOn_interior_target (I := I) g α X i).mul
        ((phiOnE_contDiff (I := I) α hφ hφ_compactSupp hφ_supp hφ_int).contDiffOn)
    · intro y hy
      have hphi_zero : phiOnE (I := I) α φ y = 0 := by
        by_cases hyT : y ∈ (extChartAt I α).target
        · rw [phiOnE_apply_of_mem (I := I) α φ hyT]
          by_contra hne
          have : (extChartAt I α).symm y ∈ tsupport φ := subset_tsupport _ hne
          exact hy ⟨(extChartAt I α).symm y, this, (extChartAt I α).right_inv hyT⟩
        · exact phiOnE_apply_of_notMem (I := I) α φ hyT
      rw [hphi_zero, mul_zero]
  have hI1_compactSupp : HasCompactSupport
      (fun y => vwIntegrandOnE (I := I) g α X i y * phiOnE (I := I) α φ y) :=
    hphi_compactSupp.mul_left
  have hfg_int : Integrable
      (fun y => vwIntegrandOnE (I := I) g α X i y * phiOnE (I := I) α φ y)
      (modelHaar (E := E)) :=
    hI1_smooth.continuous.integrable_of_hasCompactSupport hI1_compactSupp
  have hI2_smooth : ContDiff ℝ ∞
      (fun y => fderiv ℝ (vwIntegrandOnE (I := I) g α X i) y
            ((chartModelBasis E) i) * phiOnE (I := I) α φ y) := by
    refine contDiff_of_smooth_on_open_zero_outside
      (U := interior (extChartAt I α).target)
      isOpen_interior
      (K := chartImageOfTsupport (I := I) α φ)
      (chartImageOfTsupport_isClosed (I := I) α hφ_compactSupp hφ_supp)
      (chartImageOfTsupport_subset_interior_target (I := I) α hφ_supp hφ_int) ?_ ?_
    · have hvw_fderiv : ContDiffOn ℝ ∞
          (fderiv ℝ (vwIntegrandOnE (I := I) g α X i))
          (interior (extChartAt I α).target) :=
        (vwIntegrandOnE_contDiffOn_interior_target (I := I) g α X i).fderiv_of_isOpen
          isOpen_interior (by rw [ENat.coe_top_add_one])
      have hbasis_const : ContDiffOn ℝ ∞ (fun _ : E => (chartModelBasis E) i)
          (interior (extChartAt I α).target) := contDiffOn_const
      have hpartial : ContDiffOn ℝ ∞
          (fun y => fderiv ℝ (vwIntegrandOnE (I := I) g α X i) y
              ((chartModelBasis E) i)) (interior (extChartAt I α).target) :=
        hvw_fderiv.clm_apply hbasis_const
      exact hpartial.mul ((phiOnE_contDiff (I := I) α hφ hφ_compactSupp hφ_supp hφ_int).contDiffOn)
    · intro y hy
      have hphi_zero : phiOnE (I := I) α φ y = 0 := by
        by_cases hyT : y ∈ (extChartAt I α).target
        · rw [phiOnE_apply_of_mem (I := I) α φ hyT]
          by_contra hne
          have : (extChartAt I α).symm y ∈ tsupport φ := subset_tsupport _ hne
          exact hy ⟨(extChartAt I α).symm y, this, (extChartAt I α).right_inv hyT⟩
        · exact phiOnE_apply_of_notMem (I := I) α φ hyT
      rw [hphi_zero, mul_zero]
  have hI2_compactSupp : HasCompactSupport
      (fun y => fderiv ℝ (vwIntegrandOnE (I := I) g α X i) y
            ((chartModelBasis E) i) * phiOnE (I := I) α φ y) :=
    hphi_compactSupp.mul_left
  have hf'g_int : Integrable
      (fun y => fderiv ℝ (vwIntegrandOnE (I := I) g α X i) y
            ((chartModelBasis E) i) * phiOnE (I := I) α φ y)
      (modelHaar (E := E)) :=
    hI2_smooth.continuous.integrable_of_hasCompactSupport hI2_compactSupp
  have hI3_smooth : ContDiff ℝ ∞
      (fun y => vwIntegrandOnE (I := I) g α X i y *
          fderiv ℝ (phiOnE (I := I) α φ) y ((chartModelBasis E) i)) := by
    refine contDiff_of_smooth_on_open_zero_outside
      (U := interior (extChartAt I α).target)
      isOpen_interior
      (K := chartImageOfTsupport (I := I) α φ)
      (chartImageOfTsupport_isClosed (I := I) α hφ_compactSupp hφ_supp)
      (chartImageOfTsupport_subset_interior_target (I := I) α hφ_supp hφ_int) ?_ ?_
    · have hphi_smooth_total : ContDiff ℝ ∞ (phiOnE (I := I) α φ) := hphi_smooth
      have hphi_fderiv_total : ContDiff ℝ ∞ (fderiv ℝ (phiOnE (I := I) α φ)) := by
        have := hphi_smooth_total.fderiv_right (m := ∞) (by rw [ENat.coe_top_add_one])
        exact this
      have hphi_fderiv : ContDiffOn ℝ ∞ (fderiv ℝ (phiOnE (I := I) α φ))
          (interior (extChartAt I α).target) := hphi_fderiv_total.contDiffOn
      have hbasis_const : ContDiffOn ℝ ∞ (fun _ : E => (chartModelBasis E) i)
          (interior (extChartAt I α).target) := contDiffOn_const
      have hpartial : ContDiffOn ℝ ∞
          (fun y => fderiv ℝ (phiOnE (I := I) α φ) y ((chartModelBasis E) i))
          (interior (extChartAt I α).target) :=
        hphi_fderiv.clm_apply hbasis_const
      exact (vwIntegrandOnE_contDiffOn_interior_target (I := I) g α X i).mul hpartial
    · intro y hy
      have hKc_open : IsOpen (chartImageOfTsupport (I := I) α φ)ᶜ :=
        (chartImageOfTsupport_isClosed (I := I) α hφ_compactSupp hφ_supp).isOpen_compl
      have hphi_zero_on_nhd : phiOnE (I := I) α φ =ᶠ[𝓝 y] (fun _ => (0 : ℝ)) := by
        filter_upwards [hKc_open.mem_nhds hy] with z hz
        by_cases hzT : z ∈ (extChartAt I α).target
        · rw [phiOnE_apply_of_mem (I := I) α φ hzT]
          by_contra hne
          have : (extChartAt I α).symm z ∈ tsupport φ := subset_tsupport _ hne
          exact hz ⟨(extChartAt I α).symm z, this, (extChartAt I α).right_inv hzT⟩
        · exact phiOnE_apply_of_notMem (I := I) α φ hzT
      have hfderiv_zero : fderiv ℝ (phiOnE (I := I) α φ) y =
          fderiv ℝ (fun _ : E => (0 : ℝ)) y :=
        hphi_zero_on_nhd.fderiv_eq
      rw [hfderiv_zero]
      have hfderiv_const_zero : fderiv ℝ (fun _ : E => (0 : ℝ)) y = 0 := by
        rw [show (fun _ : E => (0 : ℝ)) = Function.const E (0 : ℝ) from rfl]
        rw [fderiv_const]
        rfl
      rw [hfderiv_const_zero]
      simp
  have hI3_compactSupp : HasCompactSupport
      (fun y => vwIntegrandOnE (I := I) g α X i y *
          fderiv ℝ (phiOnE (I := I) α φ) y ((chartModelBasis E) i)) := by
    refine HasCompactSupport.intro
      (chartImageOfTsupport_isCompact (I := I) α hφ_compactSupp hφ_supp) ?_
    intro y hy
    have hKc_open : IsOpen (chartImageOfTsupport (I := I) α φ)ᶜ :=
      (chartImageOfTsupport_isClosed (I := I) α hφ_compactSupp hφ_supp).isOpen_compl
    have hphi_zero_on_nhd : phiOnE (I := I) α φ =ᶠ[𝓝 y] (fun _ => (0 : ℝ)) := by
      filter_upwards [hKc_open.mem_nhds hy] with z hz
      by_cases hzT : z ∈ (extChartAt I α).target
      · rw [phiOnE_apply_of_mem (I := I) α φ hzT]
        by_contra hne
        have : (extChartAt I α).symm z ∈ tsupport φ := subset_tsupport _ hne
        exact hz ⟨(extChartAt I α).symm z, this, (extChartAt I α).right_inv hzT⟩
      · exact phiOnE_apply_of_notMem (I := I) α φ hzT
    have hfderiv_zero : fderiv ℝ (phiOnE (I := I) α φ) y =
        fderiv ℝ (fun _ : E => (0 : ℝ)) y :=
      hphi_zero_on_nhd.fderiv_eq
    rw [hfderiv_zero]
    have hfderiv_const_zero : fderiv ℝ (fun _ : E => (0 : ℝ)) y = 0 := by
      rw [show (fun _ : E => (0 : ℝ)) = Function.const E (0 : ℝ) from rfl]
      rw [fderiv_const]
      rfl
    rw [hfderiv_const_zero]
    simp
  have hfg'_int : Integrable
      (fun y => vwIntegrandOnE (I := I) g α X i y *
          fderiv ℝ (phiOnE (I := I) α φ) y ((chartModelBasis E) i))
      (modelHaar (E := E)) :=
    hI3_smooth.continuous.integrable_of_hasCompactSupport hI3_compactSupp
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hf'g_int hfg'_int hfg_int
    hvw_diff_tsupp_phi hphi_diff_tsupp_vw

omit [InnerProductSpace ℝ E] in
private lemma localDivergenceWithin_continuousOn_baseSet
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContinuousOn (localDivergenceWithin (I := I) g α X) (chartAt H α).source :=
  localDivergenceWithin_continuousOn (I := I) g α X

omit [InnerProductSpace ℝ E] in
private lemma localDivergenceWithin_mul_phi_measurable
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {φ : M → ℝ} (hφ_cont : Continuous φ)
    (hφ_supp : tsupport φ ⊆ (chartAt H α).source) :
    Measurable (fun x => localDivergenceWithin (I := I) g α X x * φ x) := by
  set s : Set M := (chartAt H α).source
  have hs_open : IsOpen s := (chartAt H α).open_source
  have hs_meas : MeasurableSet s := hs_open.measurableSet
  have hldiv_cont_s : ContinuousOn (localDivergenceWithin (I := I) g α X) s :=
    localDivergenceWithin_continuousOn_baseSet (I := I) g α X
  have hφ_cont_s : ContinuousOn φ s := hφ_cont.continuousOn
  have hprod_cont_s : ContinuousOn
      (fun x => localDivergenceWithin (I := I) g α X x * φ x) s :=
    hldiv_cont_s.mul hφ_cont_s
  have h_zero_off : ∀ x ∉ s, localDivergenceWithin (I := I) g α X x * φ x = 0 := by
    intro x hx
    have hxsupp : x ∉ tsupport φ := fun h => hx (hφ_supp h)
    have : φ x = 0 := by
      by_contra hne
      exact hxsupp (subset_tsupport _ hne)
    rw [this, mul_zero]
  classical
  have hzero_cont : ContinuousOn (fun _ : M => (0 : ℝ)) sᶜ := continuousOn_const
  have hpiecewise_meas : Measurable (s.piecewise
      (fun x => localDivergenceWithin (I := I) g α X x * φ x)
      (fun _ : M => (0 : ℝ))) :=
    hprod_cont_s.measurable_piecewise hzero_cont hs_meas
  have h_eq : (fun x => localDivergenceWithin (I := I) g α X x * φ x) =
      s.piecewise (fun x => localDivergenceWithin (I := I) g α X x * φ x)
        (fun _ : M => (0 : ℝ)) := by
    funext x
    by_cases hx : x ∈ s
    · rw [Set.piecewise_eq_of_mem _ _ _ hx]
    · rw [Set.piecewise_eq_of_notMem _ _ _ hx, h_zero_off x hx]
  rw [h_eq]
  exact hpiecewise_meas

omit [InnerProductSpace ℝ E] in
private lemma tangentSectionAction_measurable
    (α : M) (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {φ : M → ℝ} (hφ : ContMDiff I 𝓘(ℝ) ∞ φ)
    (hφ_supp : tsupport φ ⊆ (chartAt H α).source)
    (hφ_int : tsupport φ ⊆ I.interior M) :
    Measurable (tangentSectionAction (I := I) X φ) := by
  have h_zero_off : ∀ x, x ∉ tsupport φ →
      tangentSectionAction (I := I) X φ x = 0 := by
    intro x hx
    have hOpen_compl : IsOpen (tsupport φ)ᶜ := (isClosed_tsupport _).isOpen_compl
    have hphi_zero_on_nhd : φ =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
      filter_upwards [hOpen_compl.mem_nhds hx] with z hz
      by_contra hne
      exact hz (subset_tsupport _ hne)
    have hmfderiv_zero : mfderiv I 𝓘(ℝ) φ x = 0 := by
      have h_eq : mfderiv I 𝓘(ℝ) φ x = mfderiv I 𝓘(ℝ) (fun _ : M => (0 : ℝ)) x :=
        Filter.EventuallyEq.mfderiv_eq hphi_zero_on_nhd
      rw [h_eq, mfderiv_const]; rfl
    change mfderiv I 𝓘(ℝ) φ x (X x) = 0
    rw [hmfderiv_zero]; rfl
  have h_meas_support : ContinuousOn (tangentSectionAction (I := I) X φ)
      (tsupport φ) := by
    have h_in_smooth_domain : tsupport φ ⊆
        (extChartAt I α).source ∩
          (extChartAt I α) ⁻¹' interior (extChartAt I α).target := by
      intro x hx
      have hx_src : x ∈ (chartAt H α).source := hφ_supp hx
      have hx_intM : x ∈ I.interior M := hφ_int hx
      refine ⟨?_, ?_⟩
      · rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hx_src
      · exact extChartAt_mem_interior_target_of_isInteriorPoint
          (I := I) (M := M) α hx_src hx_intM
    have h_cmd := (tangentSectionAction_contMDiffOn (I := I) α X hφ).mono
      h_in_smooth_domain
    exact h_cmd.continuousOn
  set T : Set M := tsupport φ with hT_def
  have hT_closed : IsClosed T := isClosed_tsupport _
  have hT_meas : MeasurableSet T := hT_closed.measurableSet
  classical
  have hzero_cont : ContinuousOn (fun _ : M => (0 : ℝ)) Tᶜ := continuousOn_const
  have hpiecewise_meas : Measurable (T.piecewise
      (tangentSectionAction (I := I) X φ)
      (fun _ : M => (0 : ℝ))) :=
    h_meas_support.measurable_piecewise hzero_cont hT_meas
  have h_eq : tangentSectionAction (I := I) X φ =
      T.piecewise (tangentSectionAction (I := I) X φ) (fun _ : M => (0 : ℝ)) := by
    funext x
    by_cases hx : x ∈ T
    · rw [Set.piecewise_eq_of_mem _ _ _ hx]
    · rw [Set.piecewise_eq_of_notMem _ _ _ hx, h_zero_off x hx]
  rw [h_eq]
  exact hpiecewise_meas

omit [InnerProductSpace ℝ E] in
private lemma localDivergenceWithin_mul_phi_pullback_zero_off_chartImage
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {φ : M → ℝ}
    {y : E} (hyT : y ∈ (extChartAt I α).target)
    (hy : y ∉ chartImageOfTsupport (I := I) α φ) :
    chartDensity (I := I) g α ((extChartAt I α).symm y) *
      (localDivergenceWithin (I := I) g α X ((extChartAt I α).symm y) *
        φ ((extChartAt I α).symm y)) = 0 := by
  have hsymm_notin : (extChartAt I α).symm y ∉ tsupport φ := by
    intro hsymm_in
    apply hy
    refine ⟨(extChartAt I α).symm y, hsymm_in, ?_⟩
    exact (extChartAt I α).right_inv hyT
  have hφ_zero : φ ((extChartAt I α).symm y) = 0 := by
    by_contra hne
    exact hsymm_notin (subset_tsupport _ hne)
  rw [hφ_zero, mul_zero, mul_zero]

omit [InnerProductSpace ℝ E] in
private lemma localDivergenceWithin_mul_phi_pullback_eq_on_chartImage
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {φ : M → ℝ}
    (hφ_supp : tsupport φ ⊆ (chartAt H α).source)
    (hφ_int : tsupport φ ⊆ I.interior M)
    {y : E} (hy_img : y ∈ chartImageOfTsupport (I := I) α φ) :
    chartDensity (I := I) g α ((extChartAt I α).symm y) *
      (localDivergenceWithin (I := I) g α X ((extChartAt I α).symm y) *
        φ ((extChartAt I α).symm y)) =
      (∑ i : Fin (Module.finrank ℝ E),
          partialDeriv (E := E) i (vwIntegrandOnE (I := I) g α X i) y) *
        phiOnE (I := I) α φ y := by
  classical
  have hyT : y ∈ (extChartAt I α).target :=
    chartImageOfTsupport_subset_target (I := I) α hφ_supp hy_img
  have hy_int : y ∈ interior (extChartAt I α).target :=
    chartImageOfTsupport_subset_interior_target (I := I) α hφ_supp hφ_int hy_img
  have hsymm : (extChartAt I α) ((extChartAt I α).symm y) = y :=
    (extChartAt I α).right_inv hyT
  have hsymmsrc : (extChartAt I α).symm y ∈ (extChartAt I α).source :=
    (extChartAt I α).map_target hyT
  have hsymmbase : (extChartAt I α).symm y ∈
      (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]
    rw [extChartAt_source_eq_chartAt_source (I := I)] at hsymmsrc
    exact hsymmsrc
  have hρ_pos : 0 < chartDensity (I := I) g α ((extChartAt I α).symm y) :=
    chartDensity_pos (I := I) g α hsymmbase
  rw [localDivergenceWithin_def]
  rw [hsymm]
  rw [phiOnE_apply_of_mem (I := I) α φ hyT]
  have h_partial_eq : ∀ i : Fin (Module.finrank ℝ E),
      partialDerivWithin (E := E) (extChartAt I α).target i
        (fun z : E =>
          chartCoeffOnE (I := I) α X i z * chartDensityOnE (I := I) g α z) y =
      partialDeriv (E := E) i (vwIntegrandOnE (I := I) g α X i) y := by
    intro i
    rw [partialDerivWithin_extChartAt_target_eq_partialDeriv
          (I := I) (M := M) α i _ hy_int]
    unfold partialDeriv
    have htarget_nhd : (extChartAt I α).target ∈ 𝓝 y := by
      refine Filter.mem_of_superset (isOpen_interior.mem_nhds hy_int) ?_
      exact interior_subset
    have h_eq : (fun z : E =>
          chartCoeffOnE (I := I) α X i z * chartDensityOnE (I := I) g α z) =ᶠ[𝓝 y]
        vwIntegrandOnE (I := I) g α X i := by
      filter_upwards [htarget_nhd] with z hz
      exact (vwIntegrandOnE_apply_of_mem (I := I) g α X i hz).symm
    rw [h_eq.fderiv_eq]
  rw [Finset.sum_congr rfl (fun i _ => h_partial_eq i)]
  field_simp

omit [InnerProductSpace ℝ E] in
private lemma lhs_chart_target
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {φ : M → ℝ} (hφ : ContMDiff I 𝓘(ℝ) ∞ φ)
    (hφ_supp : tsupport φ ⊆ (chartAt H α).source)
    (hφ_int : tsupport φ ⊆ I.interior M) :
    ∫ x, localDivergenceWithin (I := I) g α X x * φ x
        ∂(chartLocalMeasure (I := I) g α) =
      ∫ y, (∑ i : Fin (Module.finrank ℝ E),
          fderiv ℝ (vwIntegrandOnE (I := I) g α X i) y ((chartModelBasis E) i)) *
            phiOnE (I := I) α φ y
        ∂(modelHaar (E := E)) := by
  classical
  set h : M → ℝ := fun x => localDivergenceWithin (I := I) g α X x * φ x with hh_def
  have hh_meas : Measurable h :=
    localDivergenceWithin_mul_phi_measurable (I := I) g α X hφ.continuous hφ_supp
  rw [integral_chartLocalMeasure (I := I) g α h hh_meas]
  have hT_meas := measurableSet_extChartAt_target (I := I) α
  rw [show ∫ y, (∑ i : Fin (Module.finrank ℝ E),
        fderiv ℝ (vwIntegrandOnE (I := I) g α X i) y ((chartModelBasis E) i)) *
          phiOnE (I := I) α φ y
        ∂(modelHaar (E := E)) =
      ∫ y in (extChartAt I α).target,
        (∑ i : Fin (Module.finrank ℝ E),
          fderiv ℝ (vwIntegrandOnE (I := I) g α X i) y ((chartModelBasis E) i)) *
            phiOnE (I := I) α φ y
        ∂(modelHaar (E := E)) from ?_]
  · refine setIntegral_congr_fun hT_meas ?_
    intro y hyT
    by_cases hy_img : y ∈ chartImageOfTsupport (I := I) α φ
    · have hy_int : y ∈ interior (extChartAt I α).target :=
        chartImageOfTsupport_subset_interior_target (I := I) α hφ_supp hφ_int hy_img
      have heq := localDivergenceWithin_mul_phi_pullback_eq_on_chartImage
        (I := I) g α X hφ_supp hφ_int hy_img
      change chartDensity (I := I) g α ((extChartAt I α).symm y) *
          h ((extChartAt I α).symm y) = _
      change chartDensity (I := I) g α ((extChartAt I α).symm y) *
          (localDivergenceWithin (I := I) g α X ((extChartAt I α).symm y) *
            φ ((extChartAt I α).symm y)) = _
      rw [heq]
      rfl
    · have hzero_lhs := localDivergenceWithin_mul_phi_pullback_zero_off_chartImage
        (I := I) g α X (φ := φ) hyT hy_img
      change chartDensity (I := I) g α ((extChartAt I α).symm y) *
          h ((extChartAt I α).symm y) = _
      change chartDensity (I := I) g α ((extChartAt I α).symm y) *
          (localDivergenceWithin (I := I) g α X ((extChartAt I α).symm y) *
            φ ((extChartAt I α).symm y)) = _
      rw [hzero_lhs]
      have hsymm_notin : (extChartAt I α).symm y ∉ tsupport φ := by
        intro hsymm_in
        apply hy_img
        refine ⟨(extChartAt I α).symm y, hsymm_in, ?_⟩
        exact (extChartAt I α).right_inv hyT
      have hφ_zero : φ ((extChartAt I α).symm y) = 0 := by
        by_contra hne
        exact hsymm_notin (subset_tsupport _ hne)
      have hphi_zero : phiOnE (I := I) α φ y = 0 := by
        rw [phiOnE_apply_of_mem (I := I) α φ hyT, hφ_zero]
      symm
      change (∑ i : Fin (Module.finrank ℝ E),
          fderiv ℝ (vwIntegrandOnE (I := I) g α X i) y ((chartModelBasis E) i)) *
            phiOnE (I := I) α φ y = 0
      rw [hphi_zero, mul_zero]
  · refine (setIntegral_eq_integral_of_forall_compl_eq_zero (μ := modelHaar (E := E))
      (s := (extChartAt I α).target) ?_).symm
    intro y hy
    rw [phiOnE_apply_of_notMem (I := I) α φ hy, mul_zero]

omit [InnerProductSpace ℝ E] in
private lemma rhs_chart_target
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {φ : M → ℝ} (hφ : ContMDiff I 𝓘(ℝ) ∞ φ)
    (hφ_compactSupp : HasCompactSupport φ)
    (hφ_supp : tsupport φ ⊆ (chartAt H α).source)
    (hφ_int : tsupport φ ⊆ I.interior M) :
    ∫ x, tangentSectionAction (I := I) X φ x ∂(chartLocalMeasure (I := I) g α) =
      ∫ y, (∑ i : Fin (Module.finrank ℝ E),
          vwIntegrandOnE (I := I) g α X i y *
            fderiv ℝ (phiOnE (I := I) α φ) y ((chartModelBasis E) i))
        ∂(modelHaar (E := E)) := by
  classical
  have htsa_meas : Measurable (tangentSectionAction (I := I) X φ) :=
    tangentSectionAction_measurable (I := I) α X hφ hφ_supp hφ_int
  rw [integral_chartLocalMeasure (I := I) g α (tangentSectionAction (I := I) X φ)
      htsa_meas]
  have hT_meas := measurableSet_extChartAt_target (I := I) α
  rw [show ∫ y, (∑ i : Fin (Module.finrank ℝ E),
        vwIntegrandOnE (I := I) g α X i y *
          fderiv ℝ (phiOnE (I := I) α φ) y ((chartModelBasis E) i))
        ∂(modelHaar (E := E)) =
      ∫ y in (extChartAt I α).target,
        (∑ i : Fin (Module.finrank ℝ E),
          vwIntegrandOnE (I := I) g α X i y *
            fderiv ℝ (phiOnE (I := I) α φ) y ((chartModelBasis E) i))
        ∂(modelHaar (E := E)) from ?_]
  · refine setIntegral_congr_fun hT_meas ?_
    intro y hyT
    by_cases hy_img : y ∈ chartImageOfTsupport (I := I) α φ
    · have hy_int : y ∈ interior (extChartAt I α).target :=
        chartImageOfTsupport_subset_interior_target (I := I) α hφ_supp hφ_int hy_img
      have hyT' := hyT
      have hsymm : (extChartAt I α) ((extChartAt I α).symm y) = y :=
        (extChartAt I α).right_inv hyT
      have hsymmsrc : (extChartAt I α).symm y ∈ (extChartAt I α).source :=
        (extChartAt I α).map_target hyT
      have hsymmchart : (extChartAt I α).symm y ∈ (chartAt H α).source := by
        rw [extChartAt_source_eq_chartAt_source (I := I)] at hsymmsrc
        exact hsymmsrc
      have h_int_at_symm : extChartAt I α ((extChartAt I α).symm y) ∈
          interior (extChartAt I α).target := by
        rw [hsymm]; exact hy_int
      have htsa_eq := tangentSectionAction_chartLocal (I := I) α X hφ hsymmchart
        h_int_at_symm
      change chartDensity (I := I) g α ((extChartAt I α).symm y) *
          tangentSectionAction (I := I) X φ ((extChartAt I α).symm y) = _
      rw [htsa_eq]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [vwIntegrandOnE_apply_of_mem (I := I) g α X i hyT']
      have h_fd : fderiv ℝ (phiOnE (I := I) α φ) y =
          fderiv ℝ (scalarOnE (I := I) α φ) y :=
        fderiv_phiOnE_eq_fderiv_scalarOnE (I := I) α φ hy_int
      rw [h_fd]
      rw [hsymm]
      change chartDensity (I := I) g α ((extChartAt I α).symm y) *
          (chartCoeff (I := I) α X i ((extChartAt I α).symm y) *
            fderiv ℝ (scalarOnE (I := I) α φ) y ((chartModelBasis E) i))
        = chartCoeffOnE (I := I) α X i y * chartDensityOnE (I := I) g α y *
            fderiv ℝ (scalarOnE (I := I) α φ) y ((chartModelBasis E) i)
      have h_coeff : chartCoeffOnE (I := I) α X i y =
          chartCoeff (I := I) α X i ((extChartAt I α).symm y) := rfl
      have h_density : chartDensityOnE (I := I) g α y =
          chartDensity (I := I) g α ((extChartAt I α).symm y) := rfl
      rw [h_coeff, h_density]
      ring
    · have hsymm_notin : (extChartAt I α).symm y ∉ tsupport φ := by
        intro hsymm_in
        apply hy_img
        refine ⟨(extChartAt I α).symm y, hsymm_in, ?_⟩
        exact (extChartAt I α).right_inv hyT
      have htsa_zero : tangentSectionAction (I := I) X φ ((extChartAt I α).symm y) = 0 := by
        have hOpen_compl : IsOpen (tsupport φ)ᶜ := (isClosed_tsupport _).isOpen_compl
        have hphi_zero_on_nhd : φ =ᶠ[𝓝 ((extChartAt I α).symm y)]
            (fun _ => (0 : ℝ)) := by
          filter_upwards [hOpen_compl.mem_nhds hsymm_notin] with z hz
          by_contra hne
          exact hz (subset_tsupport _ hne)
        have hmfderiv_zero : mfderiv I 𝓘(ℝ) φ ((extChartAt I α).symm y) = 0 := by
          have h_eq : mfderiv I 𝓘(ℝ) φ ((extChartAt I α).symm y) =
              mfderiv I 𝓘(ℝ) (fun _ : M => (0 : ℝ)) ((extChartAt I α).symm y) :=
            Filter.EventuallyEq.mfderiv_eq hphi_zero_on_nhd
          rw [h_eq, mfderiv_const]; rfl
        change mfderiv I 𝓘(ℝ) φ ((extChartAt I α).symm y) (X ((extChartAt I α).symm y)) = 0
        rw [hmfderiv_zero]; rfl
      change chartDensity (I := I) g α ((extChartAt I α).symm y) *
          tangentSectionAction (I := I) X φ ((extChartAt I α).symm y) = _
      rw [htsa_zero, mul_zero]
      have hKc_open : IsOpen (chartImageOfTsupport (I := I) α φ)ᶜ :=
        (chartImageOfTsupport_isClosed (I := I) α hφ_compactSupp hφ_supp).isOpen_compl
      have hphi_zero_on_nhd : phiOnE (I := I) α φ =ᶠ[𝓝 y] (fun _ => (0 : ℝ)) := by
        filter_upwards [hKc_open.mem_nhds hy_img] with z hz
        by_cases hzT : z ∈ (extChartAt I α).target
        · rw [phiOnE_apply_of_mem (I := I) α φ hzT]
          by_contra hne
          have : (extChartAt I α).symm z ∈ tsupport φ := subset_tsupport _ hne
          exact hz ⟨(extChartAt I α).symm z, this, (extChartAt I α).right_inv hzT⟩
        · exact phiOnE_apply_of_notMem (I := I) α φ hzT
      have h_fd_zero : fderiv ℝ (phiOnE (I := I) α φ) y = 0 := by
        have heq : fderiv ℝ (phiOnE (I := I) α φ) y =
            fderiv ℝ (fun _ : E => (0 : ℝ)) y :=
          hphi_zero_on_nhd.fderiv_eq
        rw [heq]
        rw [show (fun _ : E => (0 : ℝ)) = Function.const E (0 : ℝ) from rfl]
        rw [fderiv_const]; rfl
      symm
      refine Finset.sum_eq_zero ?_
      intro i _
      rw [h_fd_zero]
      simp
  · refine (setIntegral_eq_integral_of_forall_compl_eq_zero (μ := modelHaar (E := E))
      (s := (extChartAt I α).target) ?_).symm
    intro y hy
    refine Finset.sum_eq_zero ?_
    intro i _
    rw [vwIntegrandOnE_apply_of_notMem (I := I) g α X i hy, zero_mul]

omit [InnerProductSpace ℝ E] in
private lemma summand_int_lhs
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {φ : M → ℝ} (hφ : ContMDiff I 𝓘(ℝ) ∞ φ)
    (hφ_compactSupp : HasCompactSupport φ)
    (hφ_supp : tsupport φ ⊆ (chartAt H α).source)
    (hφ_int : tsupport φ ⊆ I.interior M)
    (i : Fin (Module.finrank ℝ E)) :
    Integrable (fun y =>
      fderiv ℝ (vwIntegrandOnE (I := I) g α X i) y ((chartModelBasis E) i) *
        phiOnE (I := I) α φ y) (modelHaar (E := E)) := by
  have hphi_smooth : ContDiff ℝ ∞ (phiOnE (I := I) α φ) :=
    phiOnE_contDiff (I := I) α hφ hφ_compactSupp hφ_supp hφ_int
  have hphi_compactSupp : HasCompactSupport (phiOnE (I := I) α φ) :=
    phiOnE_hasCompactSupport (I := I) α hφ_compactSupp hφ_supp
  have hI_smooth : ContDiff ℝ ∞
      (fun y => fderiv ℝ (vwIntegrandOnE (I := I) g α X i) y
          ((chartModelBasis E) i) * phiOnE (I := I) α φ y) := by
    refine contDiff_of_smooth_on_open_zero_outside
      (U := interior (extChartAt I α).target)
      isOpen_interior
      (K := chartImageOfTsupport (I := I) α φ)
      (chartImageOfTsupport_isClosed (I := I) α hφ_compactSupp hφ_supp)
      (chartImageOfTsupport_subset_interior_target (I := I) α hφ_supp hφ_int) ?_ ?_
    · have hvw_fderiv : ContDiffOn ℝ ∞
          (fderiv ℝ (vwIntegrandOnE (I := I) g α X i))
          (interior (extChartAt I α).target) :=
        (vwIntegrandOnE_contDiffOn_interior_target (I := I) g α X i).fderiv_of_isOpen
          isOpen_interior (by rw [ENat.coe_top_add_one])
      have hbasis_const : ContDiffOn ℝ ∞ (fun _ : E => (chartModelBasis E) i)
          (interior (extChartAt I α).target) := contDiffOn_const
      have hpartial : ContDiffOn ℝ ∞
          (fun y => fderiv ℝ (vwIntegrandOnE (I := I) g α X i) y
              ((chartModelBasis E) i)) (interior (extChartAt I α).target) :=
        hvw_fderiv.clm_apply hbasis_const
      exact hpartial.mul hphi_smooth.contDiffOn
    · intro y hy
      have hphi_zero : phiOnE (I := I) α φ y = 0 := by
        by_cases hyT : y ∈ (extChartAt I α).target
        · rw [phiOnE_apply_of_mem (I := I) α φ hyT]
          by_contra hne
          have : (extChartAt I α).symm y ∈ tsupport φ := subset_tsupport _ hne
          exact hy ⟨(extChartAt I α).symm y, this, (extChartAt I α).right_inv hyT⟩
        · exact phiOnE_apply_of_notMem (I := I) α φ hyT
      rw [hphi_zero, mul_zero]
  have hI_compactSupp : HasCompactSupport
      (fun y => fderiv ℝ (vwIntegrandOnE (I := I) g α X i) y
          ((chartModelBasis E) i) * phiOnE (I := I) α φ y) :=
    hphi_compactSupp.mul_left
  exact hI_smooth.continuous.integrable_of_hasCompactSupport hI_compactSupp

omit [InnerProductSpace ℝ E] in
private lemma summand_int_rhs
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {φ : M → ℝ} (hφ : ContMDiff I 𝓘(ℝ) ∞ φ)
    (hφ_compactSupp : HasCompactSupport φ)
    (hφ_supp : tsupport φ ⊆ (chartAt H α).source)
    (hφ_int : tsupport φ ⊆ I.interior M)
    (i : Fin (Module.finrank ℝ E)) :
    Integrable (fun y =>
      vwIntegrandOnE (I := I) g α X i y *
        fderiv ℝ (phiOnE (I := I) α φ) y ((chartModelBasis E) i))
      (modelHaar (E := E)) := by
  have hphi_smooth : ContDiff ℝ ∞ (phiOnE (I := I) α φ) :=
    phiOnE_contDiff (I := I) α hφ hφ_compactSupp hφ_supp hφ_int
  have hI_smooth : ContDiff ℝ ∞
      (fun y => vwIntegrandOnE (I := I) g α X i y *
          fderiv ℝ (phiOnE (I := I) α φ) y ((chartModelBasis E) i)) := by
    refine contDiff_of_smooth_on_open_zero_outside
      (U := interior (extChartAt I α).target)
      isOpen_interior
      (K := chartImageOfTsupport (I := I) α φ)
      (chartImageOfTsupport_isClosed (I := I) α hφ_compactSupp hφ_supp)
      (chartImageOfTsupport_subset_interior_target (I := I) α hφ_supp hφ_int) ?_ ?_
    · have hphi_fderiv : ContDiffOn ℝ ∞ (fderiv ℝ (phiOnE (I := I) α φ))
          (interior (extChartAt I α).target) :=
        (hphi_smooth.fderiv_right (m := ∞) (by rw [ENat.coe_top_add_one])).contDiffOn
      have hbasis_const : ContDiffOn ℝ ∞ (fun _ : E => (chartModelBasis E) i)
          (interior (extChartAt I α).target) := contDiffOn_const
      have hpartial : ContDiffOn ℝ ∞
          (fun y => fderiv ℝ (phiOnE (I := I) α φ) y ((chartModelBasis E) i))
          (interior (extChartAt I α).target) :=
        hphi_fderiv.clm_apply hbasis_const
      exact (vwIntegrandOnE_contDiffOn_interior_target (I := I) g α X i).mul hpartial
    · intro y hy
      have hKc_open : IsOpen (chartImageOfTsupport (I := I) α φ)ᶜ :=
        (chartImageOfTsupport_isClosed (I := I) α hφ_compactSupp hφ_supp).isOpen_compl
      have hphi_zero_on_nhd : phiOnE (I := I) α φ =ᶠ[𝓝 y] (fun _ => (0 : ℝ)) := by
        filter_upwards [hKc_open.mem_nhds hy] with z hz
        by_cases hzT : z ∈ (extChartAt I α).target
        · rw [phiOnE_apply_of_mem (I := I) α φ hzT]
          by_contra hne
          have : (extChartAt I α).symm z ∈ tsupport φ := subset_tsupport _ hne
          exact hz ⟨(extChartAt I α).symm z, this, (extChartAt I α).right_inv hzT⟩
        · exact phiOnE_apply_of_notMem (I := I) α φ hzT
      have hfderiv_zero : fderiv ℝ (phiOnE (I := I) α φ) y = 0 := by
        have heq : fderiv ℝ (phiOnE (I := I) α φ) y =
            fderiv ℝ (fun _ : E => (0 : ℝ)) y :=
          hphi_zero_on_nhd.fderiv_eq
        rw [heq]
        rw [show (fun _ : E => (0 : ℝ)) = Function.const E (0 : ℝ) from rfl]
        rw [fderiv_const]; rfl
      rw [hfderiv_zero]; simp
  have hI_compactSupp : HasCompactSupport
      (fun y => vwIntegrandOnE (I := I) g α X i y *
          fderiv ℝ (phiOnE (I := I) α φ) y ((chartModelBasis E) i)) := by
    refine HasCompactSupport.intro
      (chartImageOfTsupport_isCompact (I := I) α hφ_compactSupp hφ_supp) ?_
    intro y hy
    have hKc_open : IsOpen (chartImageOfTsupport (I := I) α φ)ᶜ :=
      (chartImageOfTsupport_isClosed (I := I) α hφ_compactSupp hφ_supp).isOpen_compl
    have hphi_zero_on_nhd : phiOnE (I := I) α φ =ᶠ[𝓝 y] (fun _ => (0 : ℝ)) := by
      filter_upwards [hKc_open.mem_nhds hy] with z hz
      by_cases hzT : z ∈ (extChartAt I α).target
      · rw [phiOnE_apply_of_mem (I := I) α φ hzT]
        by_contra hne
        have : (extChartAt I α).symm z ∈ tsupport φ := subset_tsupport _ hne
        exact hz ⟨(extChartAt I α).symm z, this, (extChartAt I α).right_inv hzT⟩
      · exact phiOnE_apply_of_notMem (I := I) α φ hzT
    have hfderiv_zero : fderiv ℝ (phiOnE (I := I) α φ) y = 0 := by
      have heq : fderiv ℝ (phiOnE (I := I) α φ) y =
          fderiv ℝ (fun _ : E => (0 : ℝ)) y :=
        hphi_zero_on_nhd.fderiv_eq
      rw [heq]
      rw [show (fun _ : E => (0 : ℝ)) = Function.const E (0 : ℝ) from rfl]
      rw [fderiv_const]; rfl
    rw [hfderiv_zero]; simp
  exact hI_smooth.continuous.integrable_of_hasCompactSupport hI_compactSupp

omit [InnerProductSpace ℝ E] in
theorem chart_local_ibp_within
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {φ : M → ℝ} (hφ : ContMDiff I 𝓘(ℝ) ∞ φ)
    (hφ_compactSupp : HasCompactSupport φ)
    (hφ_supp : tsupport φ ⊆ (chartAt H α).source)
    (hφ_int : tsupport φ ⊆ I.interior M) :
    ∫ x, localDivergenceWithin (I := I) g α X x * φ x ∂(chartLocalMeasure (I := I) g α) =
      -∫ x, tangentSectionAction (I := I) X φ x ∂(chartLocalMeasure (I := I) g α) := by
  classical
  rw [lhs_chart_target (I := I) g α X hφ hφ_supp hφ_int]
  rw [rhs_chart_target (I := I) g α X hφ hφ_compactSupp hφ_supp hφ_int]
  have h_lhs_distrib :
      (fun y : E => (∑ i : Fin (Module.finrank ℝ E),
            fderiv ℝ (vwIntegrandOnE (I := I) g α X i) y ((chartModelBasis E) i)) *
              phiOnE (I := I) α φ y) =
        (fun y : E => ∑ i : Fin (Module.finrank ℝ E),
          fderiv ℝ (vwIntegrandOnE (I := I) g α X i) y ((chartModelBasis E) i) *
            phiOnE (I := I) α φ y) := by
    funext y
    rw [Finset.sum_mul]
  rw [h_lhs_distrib]
  rw [integral_finset_sum (s := Finset.univ)
        (fun i _ => summand_int_lhs (I := I) g α X hφ hφ_compactSupp hφ_supp hφ_int i)]
  have h_each : ∀ i : Fin (Module.finrank ℝ E),
      ∫ y, fderiv ℝ (vwIntegrandOnE (I := I) g α X i) y ((chartModelBasis E) i) *
          phiOnE (I := I) α φ y
        ∂(modelHaar (E := E))
      = -∫ y, vwIntegrandOnE (I := I) g α X i y *
            fderiv ℝ (phiOnE (I := I) α φ) y ((chartModelBasis E) i)
          ∂(modelHaar (E := E)) := by
    intro i
    have h_ibp := ibp_per_index (I := I) g α X hφ hφ_compactSupp hφ_supp hφ_int i
    linarith [h_ibp]
  rw [Finset.sum_congr rfl (fun i _ => h_each i)]
  rw [Finset.sum_neg_distrib]
  congr 1
  rw [← integral_finset_sum (s := Finset.univ)
        (fun i _ => summand_int_rhs (I := I) g α X hφ hφ_compactSupp hφ_supp hφ_int i)]

end WithBoundary
end DivergenceTheorem
end Integral
end DifferentialGeometry
