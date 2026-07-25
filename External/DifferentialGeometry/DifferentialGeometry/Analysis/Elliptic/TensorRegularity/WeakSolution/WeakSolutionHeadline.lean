import DifferentialGeometry.Analysis.Elliptic.TensorRegularity.WeakSolution.WeakSolutionGlobal


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter MeasureTheory
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace TensorRegularity

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv
open DifferentialGeometry.Analysis.Laplacian.ChartLocalLaplacian
open DifferentialGeometry.Analysis.Laplacian.MetricExtension hiding chartTargetEuclid
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
local notation "chartHaar" =>
  MeasureTheory.Measure.map (toEuclidean : E → EuclN) (modelHaar (E := E))

def euclTestLift (α : M) (φ : EuclN → ℝ) : Set M :=
  (extChartAt I α).symm '' ((toEuclidean (E := E)).symm '' tsupport φ)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma euclTestLift_isCompact (α : M)
    {φ : EuclN → ℝ} (hφ_cs : HasCompactSupport φ)
    (hφ_supp : tsupport φ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    IsCompact (euclTestLift (I := I) (M := M) α φ) := by
  classical
  have h1 : IsCompact ((toEuclidean (E := E)).symm '' tsupport φ) :=
    (hφ_cs : IsCompact (tsupport φ)).image (toEuclidean (E := E)).symm.continuous
  have hmaps : ((toEuclidean (E := E)).symm '' tsupport φ) ⊆ (extChartAt I α).target := by
    intro z hz
    rcases hz with ⟨y, hy_supp, hy_eq⟩
    have hy_in : y ∈ chartTargetEuclid (I := I) (M := M) α := hφ_supp hy_supp
    rw [← hy_eq]
    have hy' : y ∈ (toEuclidean (E := E)).symm ⁻¹' (extChartAt I α).target := by
      rw [← chartTargetEuclid_eq_preimage_symm (I := I) (M := M)]; exact hy_in
    exact hy'
  have hcontOn : ContinuousOn (extChartAt I α).symm
      ((toEuclidean (E := E)).symm '' tsupport φ) :=
    (continuousOn_extChartAt_symm (I := I) α).mono hmaps
  exact h1.image_of_continuousOn hcontOn

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma euclTestLift_subset_source (α : M) (φ : EuclN → ℝ)
    (hφ_supp : tsupport φ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    euclTestLift (I := I) (M := M) α φ ⊆ (chartAt H α).source := by
  intro x hx
  rcases hx with ⟨z, hz_im, hz_eq⟩
  rcases hz_im with ⟨y, hy_supp, hy_eq⟩
  have hy_in : y ∈ chartTargetEuclid (I := I) (M := M) α := hφ_supp hy_supp
  have hz_target : z ∈ (extChartAt I α).target := by
    rw [← hy_eq]
    have hy' : y ∈ (toEuclidean (E := E)).symm ⁻¹' (extChartAt I α).target := by
      rw [← chartTargetEuclid_eq_preimage_symm (I := I) (M := M)]; exact hy_in
    exact hy'
  have hx_in_source : x ∈ (extChartAt I α).source := by
    rw [← hz_eq]; exact (extChartAt I α).map_target hz_target
  rwa [extChartAt_source_eq_chartAt_source (I := I)] at hx_in_source

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma chartTestPullback_support_subset (α : M) (φ : EuclN → ℝ) :
    Function.support (chartTestPullback (I := I) (M := M) α φ) ⊆
      euclTestLift (I := I) (M := M) α φ := by
  intro x hx
  rw [Function.mem_support] at hx
  by_cases hx_src : x ∈ (chartAt H α).source
  · rw [chartTestPullback_apply_of_mem (I := I) α φ hx_src] at hx
    have hφ_supp : (toEuclidean (E := E)) ((extChartAt I α) x) ∈ tsupport φ :=
      subset_tsupport _ hx
    refine ⟨(extChartAt I α) x, ⟨(toEuclidean (E := E)) ((extChartAt I α) x),
      hφ_supp, (toEuclidean (E := E)).symm_apply_apply _⟩, ?_⟩
    have hx_src' : x ∈ (extChartAt I α).source := by
      rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hx_src
    exact (extChartAt I α).left_inv hx_src'
  · rw [chartTestPullback_apply_of_notMem (I := I) α φ hx_src] at hx
    exact (hx rfl).elim

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
lemma chartTestPullback_tsupport_subset_source (α : M)
    {φ : EuclN → ℝ} (hφ_cs : HasCompactSupport φ)
    (hφ_supp : tsupport φ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    tsupport (chartTestPullback (I := I) (M := M) α φ) ⊆ (chartAt H α).source :=
  (closure_minimal (chartTestPullback_support_subset (I := I) (M := M) α φ)
    (euclTestLift_isCompact (I := I) (M := M) α hφ_cs hφ_supp).isClosed).trans
    (euclTestLift_subset_source (I := I) (M := M) α φ hφ_supp)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma chartTestPullback_contMDiffOn (α : M)
    {φ : EuclN → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (chartTestPullback (I := I) (M := M) α φ)
      (chartAt H α).source := by
  have h_ext : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α : M → E)
      (chartAt H α).source := contMDiffOn_extChartAt
  have h_toE_M : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, EuclN) ∞ (toEuclidean (E := E))
      Set.univ :=
    ((contMDiff_iff_contDiff (n := (⊤ : ℕ∞))).mpr
      (toEuclidean (E := E)).contDiff).contMDiffOn
  have h_psi_M : ContMDiffOn 𝓘(ℝ, EuclN) 𝓘(ℝ, ℝ) ∞ φ Set.univ :=
    ((contMDiff_iff_contDiff (n := (⊤ : ℕ∞))).mpr hφ).contMDiffOn
  have h1 : ContMDiffOn I 𝓘(ℝ, EuclN) ∞
      (fun x : M => (toEuclidean (E := E)) ((extChartAt I α) x))
      (chartAt H α).source :=
    h_toE_M.comp h_ext (Set.mapsTo_univ _ _)
  have hcompose : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun x : M => φ ((toEuclidean (E := E)) ((extChartAt I α) x)))
      (chartAt H α).source :=
    h_psi_M.comp h1 (Set.mapsTo_univ _ _)
  refine hcompose.congr (fun x hx => ?_)
  exact chartTestPullback_apply_of_mem (I := I) α φ hx

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
lemma contDiff_of_contDiffOn_chartTarget_zero_off
    (α : M) {P : EuclN → ℝ} {C : Set EuclN}
    (hC : IsClosed C) (hC_target : C ⊆ chartTargetEuclid (I := I) (M := M) α)
    (hP : ContDiffOn ℝ ∞ P (chartTargetEuclid (I := I) (M := M) α))
    (hzero : ∀ y, y ∉ C → P y = 0) :
    ContDiff ℝ ∞ P := by
  classical
  have hopen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
  · exact hP.contDiffAt (hopen.mem_nhds hy)
  · have hyC : y ∉ C := fun hyC => hy (hC_target hyC)
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [hC.isOpen_compl.mem_nhds hyC] with z hz using hzero z hz

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
lemma contDiff_mul_chartTest
    (α : M) {h φ : EuclN → ℝ}
    (hh : ContDiffOn ℝ ∞ h (chartTargetEuclid (I := I) (M := M) α))
    (hφ : ContDiff ℝ ∞ φ)
    (hφ_supp : tsupport φ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ContDiff ℝ ∞ (fun y => h y * φ y) := by
  refine contDiff_of_contDiffOn_chartTarget_zero_off (I := I) (M := M) α
    (isClosed_tsupport φ) hφ_supp (hh.mul hφ.contDiffOn) ?_
  intro y hy
  rw [image_eq_zero_of_notMem_tsupport hy, mul_zero]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
lemma hasCompactSupport_mul_chartTest
    {h φ : EuclN → ℝ} (hφ_cs : HasCompactSupport φ) :
    HasCompactSupport (fun y => h y * φ y) :=
  hφ_cs.mul_left

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
lemma euclidPartial_contDiffOn_chartTarget
    (α : M) (l : Fin (Module.finrank ℝ E))
    {u : EuclN → ℝ}
    (hu : ContDiffOn ℝ ∞ u (chartTargetEuclid (I := I) (M := M) α)) :
    ContDiffOn ℝ ∞ (euclidPartial (E := E) l u)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have hopen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α
  have hfderiv : ContDiffOn ℝ ∞ (fun z => fderiv ℝ u z)
      (chartTargetEuclid (I := I) (M := M) α) := by
    have hsucc : ContDiffOn ℝ ((∞ : WithTop ℕ∞) + 1) u
        (chartTargetEuclid (I := I) (M := M) α) := by
      rw [show (∞ : WithTop ℕ∞) + 1 = ∞ from rfl]; exact hu
    have hfw : ContDiffOn ℝ ∞ (fderivWithin ℝ u
        (chartTargetEuclid (I := I) (M := M) α))
        (chartTargetEuclid (I := I) (M := M) α) :=
      ((contDiffOn_succ_iff_fderivWithin hopen.uniqueDiffOn).mp hsucc).2.2
    refine hfw.congr (fun z hz => ?_)
    exact (fderivWithin_of_isOpen (f := u) (𝕜 := ℝ) hopen hz).symm
  have hcomp : ContDiffOn ℝ ∞
      ((fun L : EuclN →L[ℝ] ℝ => L (EuclideanSpace.single l 1)) ∘
        (fun z => fderiv ℝ u z))
      (chartTargetEuclid (I := I) (M := M) α) :=
    (ContinuousLinearMap.apply ℝ ℝ
      (EuclideanSpace.single l 1)).contDiff.comp_contDiffOn hfderiv
  refine hcomp.congr (fun z _ => ?_)
  rfl

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
lemma integrable_of_contDiff_hasCompactSupport
    {P : EuclN → ℝ} (hP : ContDiff ℝ ∞ P) (hP_cs : HasCompactSupport P) :
    Integrable P (volume : Measure EuclN) :=
  hP.continuous.integrable_of_hasCompactSupport hP_cs

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma chartPushedRaw_chartTestPullback_eqOn (α : M) (φ : EuclN → ℝ) :
    Set.EqOn (chartPushedRaw I α (chartTestPullback (I := I) (M := M) α φ)) φ
      (chartTargetEuclid (I := I) (M := M) α) := by
  intro y hy
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy]
  have hb_chart : (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∈
      (chartAt H α).source :=
    symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) α hy
  rw [chartTestPullback_apply_of_mem (I := I) α φ hb_chart]
  have hb_eq : (toEuclidean (E := E))
      ((extChartAt I α)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) = y := by
    have hy' : y ∈ (toEuclidean (E := E)).symm ⁻¹' (extChartAt I α).target := by
      rw [← chartTargetEuclid_eq_preimage_symm (I := I) (M := M)]; exact hy
    rw [(extChartAt I α).right_inv hy', ContinuousLinearEquiv.apply_symm_apply]
  rw [hb_eq]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
lemma euclidPartial_chartPushedRaw_chartTestPullback_eqOn
    (α : M) (φ : EuclN → ℝ) (l : Fin (Module.finrank ℝ E)) :
    Set.EqOn
      (euclidPartial (E := E) l
        (chartPushedRaw I α (chartTestPullback (I := I) (M := M) α φ)))
      (euclidPartial (E := E) l φ)
      (chartTargetEuclid (I := I) (M := M) α) := by
  intro y hy
  have hopen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α
  rw [euclidPartial_def, euclidPartial_def,
    Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) (x := y)
      (Filter.eventuallyEq_of_mem (hopen.mem_nhds hy)
        (chartPushedRaw_chartTestPullback_eqOn (I := I) (M := M) α φ))]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
private lemma euclidPartial_eq_zero_of_notMem_tsupport
    {u : EuclN → ℝ} (l : Fin (Module.finrank ℝ E))
    {y : EuclN} (hy : y ∉ tsupport u) :
    euclidPartial (E := E) l u y = 0 := by
  classical
  have hopen_c : IsOpen (tsupport u)ᶜ := (isClosed_tsupport u).isOpen_compl
  have hu_evt : u =ᶠ[𝓝 y] (fun _ => (0 : ℝ)) :=
    Filter.eventually_of_mem (hopen_c.mem_nhds hy)
      (fun z hz => image_eq_zero_of_notMem_tsupport hz)
  rw [euclidPartial_def, Filter.EventuallyEq.fderiv_eq hu_evt,
    fderiv_const_apply, ContinuousLinearMap.zero_apply]

omit [CompleteSpace E] [CompactSpace M] in
lemma density_scalarPrincipal_eq_principalIntegrand
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set EuclN} (hK : IsCompact K)
    (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    {u : EuclN → ℝ} (hu_K : tsupport u ⊆ K) (φ : EuclN → ℝ)
    {y : EuclN} (_hyK : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    densityOnEuclid (I := I) g α y *
        (∑ k : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramEuclid (I := I) g α k l y *
                euclidPartial (E := E) k u y *
              euclidPartial (E := E) l φ y) =
      (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).principalIntegrand
        u φ y := by
  classical
  by_cases hyu : y ∈ tsupport u
  · exact weightedInvGram_principalIntegrand_eq (I := I) (M := M) g α hK
      hK_target u φ (hu_K hyu)
  · have hLHS_zero :
        densityOnEuclid (I := I) g α y *
          (∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              chartInvGramEuclid (I := I) g α k l y *
                  euclidPartial (E := E) k u y *
                euclidPartial (E := E) l φ y) = 0 := by
      refine mul_eq_zero_of_right _ (Finset.sum_eq_zero (fun k _ => ?_))
      refine Finset.sum_eq_zero (fun l _ => ?_)
      rw [euclidPartial_eq_zero_of_notMem_tsupport (E := E) k hyu]; ring
    rw [hLHS_zero]
    rw [SmoothEllipticBilinearForm.principalIntegrand]
    refine (Finset.sum_eq_zero (fun i _ => Finset.sum_eq_zero (fun j _ => ?_))).symm
    have := euclidPartial_eq_zero_of_notMem_tsupport (E := E) i hyu
    rw [euclidPartial_def] at this
    rw [this]; ring

omit [CompleteSpace E] in
theorem tensorComponent_chartBilinIdentity
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T F : SmoothCcTensor g r s) (α : M)
    {K : Set EuclN} (hK : IsCompact K)
    (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    (P₀ : CompIdx E r s)
    (hT_supp : tsupport T.toFun ⊆ (chartAt H α).source)
    (hT_K : tsupport (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) ⊆ K)
    (hweak : ∀ v : SmoothCcTensor g r s,
      ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r s T v x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        tensorL2Inner (I := I) (M := M) g r s F.toFun v.toFun)
    {φ : EuclN → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφ_cs : HasCompactSupport φ)
    (hφ_supp : tsupport φ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).bilin
        (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) φ =
      ∫ y, tensorComponentWeakRHS (I := I) (M := M) g r s T F α hK hK_target P₀ y
        * φ y := by
  classical
  have hcTE_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α
  have hcTE_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    hcTE_open.measurableSet
  have hφ' : ContDiff ℝ ∞ φ := hφ
  have hχs : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (chartTestPullback (I := I) (M := M) α φ)
      (chartAt H α).source :=
    chartTestPullback_contMDiffOn (I := I) (M := M) α hφ
  have hχt : tsupport (chartTestPullback (I := I) (M := M) α φ) ⊆
      (chartAt H α).source :=
    chartTestPullback_tsupport_subset_source (I := I) (M := M) α hφ_cs hφ_supp
  have hdensity : ContDiffOn ℝ ∞ (densityOnEuclid (I := I) g α)
      (chartTargetEuclid (I := I) (M := M) α) :=
    densityOnEuclid_contDiffOn (I := I) g α
  have hbump_eqOn : Set.EqOn
      (chartPushedRaw I α (chartTestPullback (I := I) (M := M) α φ)) φ
      (chartTargetEuclid (I := I) (M := M) α) :=
    chartPushedRaw_chartTestPullback_eqOn (I := I) (M := M) α φ
  have hbump_partial_eqOn : ∀ l : Fin (Module.finrank ℝ E),
      Set.EqOn (euclidPartial (E := E) l
          (chartPushedRaw I α (chartTestPullback (I := I) (M := M) α φ)))
        (euclidPartial (E := E) l φ)
        (chartTargetEuclid (I := I) (M := M) α) := fun l =>
    euclidPartial_chartPushedRaw_chartTestPullback_eqOn (I := I) (M := M) α φ l
  have hdφ : ∀ l : Fin (Module.finrank ℝ E),
      ContDiff ℝ ∞ (euclidPartial (E := E) l φ) := by
    intro l
    rw [show euclidPartial (E := E) l φ =
        (fun L : EuclN →L[ℝ] ℝ => L (EuclideanSpace.single l 1)) ∘
          (fun z => fderiv ℝ φ z) from by funext z; rfl]
    exact (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single l 1)).contDiff.comp
      (hφ'.fderiv_right (m := ∞) (by rw [show (∞ : WithTop ℕ∞) + 1 = ∞ from rfl]))
  have hcs_dφ : ∀ l : Fin (Module.finrank ℝ E),
      HasCompactSupport (euclidPartial (E := E) l φ) := by
    intro l
    refine HasCompactSupport.of_support_subset_isCompact (K := tsupport φ)
      hφ_cs ?_
    intro y hy
    rw [Function.mem_support] at hy
    by_contra hyφ
    exact hy (euclidPartial_eq_zero_of_notMem_tsupport (E := E) l hyφ)
  have hdφ_supp : ∀ l : Fin (Module.finrank ℝ E),
      tsupport (euclidPartial (E := E) l φ) ⊆
        chartTargetEuclid (I := I) (M := M) α := by
    intro l
    refine (closure_minimal ?_ (isClosed_tsupport φ)).trans hφ_supp
    intro z hz
    rw [Function.mem_support] at hz
    by_contra hz'
    exact hz (euclidPartial_eq_zero_of_notMem_tsupport (E := E) l hz')
  have hφ_partial_zero : ∀ l : Fin (Module.finrank ℝ E), ∀ y, y ∉ tsupport φ →
      euclidPartial (E := E) l φ y = 0 := fun l y hy =>
    euclidPartial_eq_zero_of_notMem_tsupport (E := E) l hy
  have hu_partial_zero : ∀ k : Fin (Module.finrank ℝ E), ∀ y,
      y ∉ tsupport (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) →
      euclidPartial (E := E) k
        (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) y = 0 :=
    fun k y hy => euclidPartial_eq_zero_of_notMem_tsupport (E := E) k hy
  have hP_src : ContDiff ℝ ∞
      (fun y => densityOnEuclid (I := I) g α y *
        sourcePairingCoeff (I := I) (M := M) g r s F α P₀ y * φ y) :=
    contDiff_mul_chartTest (I := I) (M := M) α
      (hdensity.mul (sourcePairingCoeff_contDiffOn (I := I) (M := M)
        g r s F α P₀)) hφ' hφ_supp
  have hP_prc : ContDiff ℝ ∞
      (fun y => densityOnEuclid (I := I) g α y *
        covPrincipalRotationCoeff (I := I) (M := M) g r s T α P₀ y * φ y) :=
    contDiff_mul_chartTest (I := I) (M := M) α
      (hdensity.mul (covPrincipalRotationCoeff_contDiffOn (I := I) (M := M)
        g r s T α P₀)) hφ' hφ_supp
  have hP_lov : ContDiff ℝ ∞
      (fun y => densityOnEuclid (I := I) g α y *
        covLowerOrderRotationValueCoeff (I := I) (M := M) g r s T α P₀ y *
          φ y) :=
    contDiff_mul_chartTest (I := I) (M := M) α
      (hdensity.mul (covLowerOrderRotationValueCoeff_contDiffOn (I := I) (M := M)
        g r s T α P₀)) hφ' hφ_supp
  have hP_grad : ∀ l : Fin (Module.finrank ℝ E), ContDiff ℝ ∞
      (fun y => weightedGradCoeff (I := I) (M := M) g r s T α P₀ l y *
        euclidPartial (E := E) l φ y) := fun l =>
    contDiff_mul_chartTest (I := I) (M := M) α
      (weightedGradCoeff_contDiffOn (I := I) (M := M) g r s T α P₀ l) (hdφ l)
      (hdφ_supp l)
  have hP_ibp : ∀ l : Fin (Module.finrank ℝ E), ContDiff ℝ ∞
      (fun y => euclidPartial (E := E) l
          (weightedGradCoeff (I := I) (M := M) g r s T α P₀ l) y * φ y) :=
    fun l => contDiff_mul_chartTest (I := I) (M := M) α
      (euclidPartial_contDiffOn_chartTarget (I := I) (M := M) α l
        (weightedGradCoeff_contDiffOn (I := I) (M := M) g r s T α P₀ l)) hφ'
      hφ_supp
  have hP_principal : ContDiff ℝ ∞
      ((tensorPrincipalForm (I := I) (M := M) g α hK hK_target).principalIntegrand
        (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) φ) := by
    have hu_cd : ContDiff ℝ ∞
        (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) :=
      tensorComponentEuclid_contDiff (I := I) (M := M) g r s T α P₀ hT_supp
    have hbody : ContDiff ℝ ∞
        (fun x => ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).a x i j *
              ((fderiv ℝ (tensorComponentEuclid (I := I) (M := M)
                g r s T α P₀) x) (EuclideanSpace.single i 1)) *
              ((fderiv ℝ φ x) (EuclideanSpace.single j 1))) :=
      ContDiff.sum (fun i _ => ContDiff.sum (fun j _ =>
        (((tensorPrincipalForm (I := I) (M := M) g α hK hK_target).contDiff_a
          i j).mul ((hu_cd.fderiv_right (m := ∞)
          (by rw [show (∞ : WithTop ℕ∞) + 1 = ∞ from rfl])).clm_apply
          contDiff_const)).mul ((hφ'.fderiv_right (m := ∞)
          (by rw [show (∞ : WithTop ℕ∞) + 1 = ∞ from rfl])).clm_apply
          contDiff_const)))
    exact hbody
  have hcs_mul : ∀ h : EuclN → ℝ,
      HasCompactSupport (fun y => h y * φ y) := fun h =>
    hasCompactSupport_mul_chartTest (E := E) hφ_cs
  have hcs_principal : HasCompactSupport
      ((tensorPrincipalForm (I := I) (M := M) g α hK hK_target).principalIntegrand
        (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) φ) := by
    refine HasCompactSupport.of_support_subset_isCompact
      (K := tsupport (tensorComponentEuclid (I := I) (M := M) g r s T α P₀))
      (IsCompact.of_isClosed_subset hK (isClosed_tsupport _) hT_K) ?_
    intro y hy
    rw [Function.mem_support] at hy
    by_contra hyu
    apply hy
    rw [SmoothEllipticBilinearForm.principalIntegrand]
    refine Finset.sum_eq_zero (fun i _ => Finset.sum_eq_zero (fun j _ => ?_))
    have := hu_partial_zero i y hyu
    rw [euclidPartial_def] at this
    rw [this]; ring
  have hint_principal : Integrable
      ((tensorPrincipalForm (I := I) (M := M) g α hK hK_target).principalIntegrand
        (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) φ)
      (volume : Measure EuclN) :=
    integrable_of_contDiff_hasCompactSupport (E := E) hP_principal hcs_principal
  have hint_src : Integrable
      (fun y => densityOnEuclid (I := I) g α y *
        sourcePairingCoeff (I := I) (M := M) g r s F α P₀ y * φ y)
      (volume : Measure EuclN) := by
    have heq : (fun y => densityOnEuclid (I := I) g α y *
        sourcePairingCoeff (I := I) (M := M) g r s F α P₀ y * φ y) =
      (fun y => (densityOnEuclid (I := I) g α y *
        sourcePairingCoeff (I := I) (M := M) g r s F α P₀ y) * φ y) := by
      funext y; ring
    exact integrable_of_contDiff_hasCompactSupport (E := E) hP_src
      (heq ▸ hcs_mul _)
  have hint_prc : Integrable
      (fun y => densityOnEuclid (I := I) g α y *
        covPrincipalRotationCoeff (I := I) (M := M) g r s T α P₀ y * φ y)
      (volume : Measure EuclN) := by
    have heq : (fun y => densityOnEuclid (I := I) g α y *
        covPrincipalRotationCoeff (I := I) (M := M) g r s T α P₀ y * φ y) =
      (fun y => (densityOnEuclid (I := I) g α y *
        covPrincipalRotationCoeff (I := I) (M := M) g r s T α P₀ y) * φ y) := by
      funext y; ring
    exact integrable_of_contDiff_hasCompactSupport (E := E) hP_prc
      (heq ▸ hcs_mul _)
  have hint_lov : Integrable
      (fun y => densityOnEuclid (I := I) g α y *
        covLowerOrderRotationValueCoeff (I := I) (M := M) g r s T α P₀ y * φ y)
      (volume : Measure EuclN) := by
    have heq : (fun y => densityOnEuclid (I := I) g α y *
        covLowerOrderRotationValueCoeff (I := I) (M := M) g r s T α P₀ y * φ y) =
      (fun y => (densityOnEuclid (I := I) g α y *
        covLowerOrderRotationValueCoeff (I := I) (M := M) g r s T α P₀ y) *
          φ y) := by
      funext y; ring
    exact integrable_of_contDiff_hasCompactSupport (E := E) hP_lov
      (heq ▸ hcs_mul _)
  have hint_grad : ∀ l : Fin (Module.finrank ℝ E), Integrable
      (fun y => weightedGradCoeff (I := I) (M := M) g r s T α P₀ l y *
        euclidPartial (E := E) l φ y) (volume : Measure EuclN) := fun l =>
    integrable_of_contDiff_hasCompactSupport (E := E) (hP_grad l)
      (hasCompactSupport_mul_chartTest (E := E) (hcs_dφ l))
  have hint_ibp : ∀ l : Fin (Module.finrank ℝ E), Integrable
      (fun y => euclidPartial (E := E) l
          (weightedGradCoeff (I := I) (M := M) g r s T α P₀ l) y * φ y)
      (volume : Measure EuclN) := fun l =>
    integrable_of_contDiff_hasCompactSupport (E := E) (hP_ibp l) (hcs_mul _)
  have hsetInt_to_int : ∀ X : EuclN → ℝ,
      (∀ y, y ∉ chartTargetEuclid (I := I) (M := M) α → X y = 0) →
      ∫ y in chartTargetEuclid (I := I) (M := M) α, X y ∂chartHaar =
        ∫ y, X y ∂(volume : Measure EuclN) := by
    intro X hX_zero
    rw [DifferentialGeometry.Integral.Measure.map_toEuclidean_modelHaar_eq_volume
      (E := E)]
    exact MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hX_zero
  have hweak_v := hweak (rotatedTestSection (I := I) (M := M) g r s α P₀
    (chartTestPullback (I := I) (M := M) α φ) hχs hχt)
  rw [tensorCovDerivPointwiseInner_integral_chart_pull (I := I) (M := M)
      g r s T _ α hT_supp,
    tensorL2Inner_rotatedTestSection_chart_pull (I := I) (M := M) g r s F α P₀
      hχs hχt] at hweak_v
  have hLHS_integrand : ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y *
          (covPrincipalIntegrand (I := I) (M := M) g r s T
              (rotatedTestSection (I := I) (M := M) g r s α P₀
                (chartTestPullback (I := I) (M := M) α φ) hχs hχt) α y +
            covLowerOrderIntegrand (I := I) (M := M) g r s T
              (rotatedTestSection (I := I) (M := M) g r s α P₀
                (chartTestPullback (I := I) (M := M) α φ) hχs hχt) α y) =
        (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).principalIntegrand
            (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) φ y +
          (densityOnEuclid (I := I) g α y *
            covPrincipalRotationCoeff (I := I) (M := M) g r s T α P₀ y * φ y +
          (densityOnEuclid (I := I) g α y *
            covLowerOrderRotationValueCoeff (I := I) (M := M) g r s T α P₀ y *
              φ y +
          ∑ l : Fin (Module.finrank ℝ E),
            densityOnEuclid (I := I) g α y *
              covLowerOrderRotationGradCoeff (I := I) (M := M) g r s T α P₀ l y *
                euclidPartial (E := E) l φ y)) := by
    intro y hy
    have hPI : (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).principalIntegrand
          (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) φ y =
        densityOnEuclid (I := I) g α y *
          (∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              chartInvGramEuclid (I := I) g α k l y *
                  euclidPartial (E := E) k
                    (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) y *
                euclidPartial (E := E) l φ y) :=
      (density_scalarPrincipal_eq_principalIntegrand (I := I) (M := M) g α hK
        hK_target hT_K φ hy).symm
    have hscalar : ∑ k : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramEuclid (I := I) g α k l y *
                euclidPartial (E := E) k
                  (chartPushedRaw I α
                    (tensorChartComponentRaw (I := I) (M := M)
                      g r s T α P₀.1 P₀.2)) y *
              euclidPartial (E := E) l
                (chartPushedRaw I α (chartTestPullback (I := I) (M := M) α φ))
                y =
        ∑ k : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramEuclid (I := I) g α k l y *
                euclidPartial (E := E) k
                  (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) y *
              euclidPartial (E := E) l φ y := by
      refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
      rw [show chartPushedRaw I α
            (tensorChartComponentRaw (I := I) (M := M) g r s T α P₀.1 P₀.2) =
          tensorComponentEuclid (I := I) (M := M) g r s T α P₀ from
        (tensorComponentEuclid_def (I := I) (M := M) g r s T α P₀).symm,
        hbump_partial_eqOn l hy]
    have hgrad : ∑ l : Fin (Module.finrank ℝ E),
          covLowerOrderRotationGradCoeff (I := I) (M := M) g r s T α P₀ l y *
            euclidPartial (E := E) l
              (chartPushedRaw I α (chartTestPullback (I := I) (M := M) α φ)) y =
        ∑ l : Fin (Module.finrank ℝ E),
          covLowerOrderRotationGradCoeff (I := I) (M := M) g r s T α P₀ l y *
            euclidPartial (E := E) l φ y := by
      refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [hbump_partial_eqOn l hy]
    rw [covPrincipalIntegrand_rotated_collapse (I := I) (M := M) g r s T α P₀
        hχs hχt hy,
      covPrincipalRotationRemainder_eq_coeff_mul (I := I) (M := M) g r s T α P₀
        hχs hχt y,
      covLowerOrderIntegrand_rotated_collapse (I := I) (M := M) g r s T α P₀
        hχs hχt hy,
      hscalar, hgrad, hbump_eqOn hy, hPI]
    simp only [mul_add, Finset.mul_sum]
    ring
  have hLHS_setInt :
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          (covPrincipalIntegrand (I := I) (M := M) g r s T
              (rotatedTestSection (I := I) (M := M) g r s α P₀
                (chartTestPullback (I := I) (M := M) α φ) hχs hχt) α y +
            covLowerOrderIntegrand (I := I) (M := M) g r s T
              (rotatedTestSection (I := I) (M := M) g r s α P₀
                (chartTestPullback (I := I) (M := M) α φ) hχs hχt) α y)
        ∂chartHaar =
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        ((tensorPrincipalForm (I := I) (M := M) g α hK hK_target).principalIntegrand
            (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) φ y +
          (densityOnEuclid (I := I) g α y *
            covPrincipalRotationCoeff (I := I) (M := M) g r s T α P₀ y * φ y +
          (densityOnEuclid (I := I) g α y *
            covLowerOrderRotationValueCoeff (I := I) (M := M) g r s T α P₀ y *
              φ y +
          ∑ l : Fin (Module.finrank ℝ E),
            densityOnEuclid (I := I) g α y *
              covLowerOrderRotationGradCoeff (I := I) (M := M) g r s T α P₀ l y *
                euclidPartial (E := E) l φ y))) ∂chartHaar :=
    MeasureTheory.setIntegral_congr_fun hcTE_meas hLHS_integrand
  have hsum_zero : ∀ y, y ∉ chartTargetEuclid (I := I) (M := M) α →
      (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).principalIntegrand
          (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) φ y +
        (densityOnEuclid (I := I) g α y *
          covPrincipalRotationCoeff (I := I) (M := M) g r s T α P₀ y * φ y +
        (densityOnEuclid (I := I) g α y *
          covLowerOrderRotationValueCoeff (I := I) (M := M) g r s T α P₀ y *
            φ y +
        ∑ l : Fin (Module.finrank ℝ E),
          densityOnEuclid (I := I) g α y *
            covLowerOrderRotationGradCoeff (I := I) (M := M) g r s T α P₀ l y *
              euclidPartial (E := E) l φ y)) = 0 := by
    intro y hy
    have hyφ : y ∉ tsupport φ := fun h => hy (hφ_supp h)
    have hyu : y ∉ tsupport (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) :=
      fun h => hy ((hT_K.trans hK_target) h)
    have hφ0 : φ y = 0 := image_eq_zero_of_notMem_tsupport hyφ
    have hprinc0 :
        (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).principalIntegrand
          (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) φ y = 0 := by
      rw [SmoothEllipticBilinearForm.principalIntegrand]
      refine Finset.sum_eq_zero (fun i _ => Finset.sum_eq_zero (fun j _ => ?_))
      have := hu_partial_zero i y hyu
      rw [euclidPartial_def] at this
      rw [this]; ring
    rw [hprinc0, hφ0]
    simp only [mul_zero, zero_add]
    exact Finset.sum_eq_zero (fun l _ => by
      rw [hφ_partial_zero l y hyφ]; ring)
  have hLHS_volume :
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          (covPrincipalIntegrand (I := I) (M := M) g r s T
              (rotatedTestSection (I := I) (M := M) g r s α P₀
                (chartTestPullback (I := I) (M := M) α φ) hχs hχt) α y +
            covLowerOrderIntegrand (I := I) (M := M) g r s T
              (rotatedTestSection (I := I) (M := M) g r s α P₀
                (chartTestPullback (I := I) (M := M) α φ) hχs hχt) α y)
        ∂chartHaar =
      ∫ y, ((tensorPrincipalForm (I := I) (M := M) g α hK hK_target).principalIntegrand
          (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) φ y +
        (densityOnEuclid (I := I) g α y *
          covPrincipalRotationCoeff (I := I) (M := M) g r s T α P₀ y * φ y +
        (densityOnEuclid (I := I) g α y *
          covLowerOrderRotationValueCoeff (I := I) (M := M) g r s T α P₀ y *
            φ y +
        ∑ l : Fin (Module.finrank ℝ E),
          densityOnEuclid (I := I) g α y *
            covLowerOrderRotationGradCoeff (I := I) (M := M) g r s T α P₀ l y *
              euclidPartial (E := E) l φ y))) ∂(volume : Measure EuclN) := by
    rw [hLHS_setInt]
    exact hsetInt_to_int _ hsum_zero
  have hRHS_volume :
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          chartPushedRaw I α (chartTestPullback (I := I) (M := M) α φ) y *
          sourcePairingCoeff (I := I) (M := M) g r s F α P₀ y ∂chartHaar =
      ∫ y, densityOnEuclid (I := I) g α y *
        sourcePairingCoeff (I := I) (M := M) g r s F α P₀ y * φ y
        ∂(volume : Measure EuclN) := by
    rw [MeasureTheory.setIntegral_congr_fun hcTE_meas (fun y hy => by
      rw [hbump_eqOn hy]; ring :
      ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
            chartPushedRaw I α (chartTestPullback (I := I) (M := M) α φ) y *
            sourcePairingCoeff (I := I) (M := M) g r s F α P₀ y =
          densityOnEuclid (I := I) g α y *
            sourcePairingCoeff (I := I) (M := M) g r s F α P₀ y * φ y)]
    refine hsetInt_to_int _ (fun y hy => ?_)
    rw [image_eq_zero_of_notMem_tsupport (fun h => hy (hφ_supp h))]; ring
  rw [hLHS_volume, hRHS_volume] at hweak_v
  have hint_gradsum : Integrable
      (fun y => ∑ l : Fin (Module.finrank ℝ E),
        densityOnEuclid (I := I) g α y *
          covLowerOrderRotationGradCoeff (I := I) (M := M) g r s T α P₀ l y *
            euclidPartial (E := E) l φ y) (volume : Measure EuclN) := by
    refine MeasureTheory.integrable_finset_sum _ (fun l _ => ?_)
    have heq : (fun y => densityOnEuclid (I := I) g α y *
        covLowerOrderRotationGradCoeff (I := I) (M := M) g r s T α P₀ l y *
          euclidPartial (E := E) l φ y) =
      (fun y => weightedGradCoeff (I := I) (M := M) g r s T α P₀ l y *
        euclidPartial (E := E) l φ y) := by
      funext y; rw [weightedGradCoeff_eq]
    rw [heq]; exact hint_grad l
  have hLHS_split :
      ∫ y, ((tensorPrincipalForm (I := I) (M := M) g α hK hK_target).principalIntegrand
          (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) φ y +
        (densityOnEuclid (I := I) g α y *
          covPrincipalRotationCoeff (I := I) (M := M) g r s T α P₀ y * φ y +
        (densityOnEuclid (I := I) g α y *
          covLowerOrderRotationValueCoeff (I := I) (M := M) g r s T α P₀ y *
            φ y +
        ∑ l : Fin (Module.finrank ℝ E),
          densityOnEuclid (I := I) g α y *
            covLowerOrderRotationGradCoeff (I := I) (M := M) g r s T α P₀ l y *
              euclidPartial (E := E) l φ y))) ∂(volume : Measure EuclN) =
      (∫ y, (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).principalIntegrand
          (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) φ y
          ∂(volume : Measure EuclN)) +
      ((∫ y, densityOnEuclid (I := I) g α y *
          covPrincipalRotationCoeff (I := I) (M := M) g r s T α P₀ y * φ y
          ∂(volume : Measure EuclN)) +
      ((∫ y, densityOnEuclid (I := I) g α y *
          covLowerOrderRotationValueCoeff (I := I) (M := M) g r s T α P₀ y * φ y
          ∂(volume : Measure EuclN)) +
      ∫ y, (∑ l : Fin (Module.finrank ℝ E),
        densityOnEuclid (I := I) g α y *
          covLowerOrderRotationGradCoeff (I := I) (M := M) g r s T α P₀ l y *
            euclidPartial (E := E) l φ y) ∂(volume : Measure EuclN))) := by
    rw [MeasureTheory.integral_add
        (f := (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).principalIntegrand
          (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) φ)
        (g := fun y => densityOnEuclid (I := I) g α y *
            covPrincipalRotationCoeff (I := I) (M := M) g r s T α P₀ y * φ y +
          (densityOnEuclid (I := I) g α y *
            covLowerOrderRotationValueCoeff (I := I) (M := M) g r s T α P₀ y *
              φ y +
          ∑ l : Fin (Module.finrank ℝ E),
            densityOnEuclid (I := I) g α y *
              covLowerOrderRotationGradCoeff (I := I) (M := M) g r s T α P₀ l y *
                euclidPartial (E := E) l φ y))
        hint_principal (hint_prc.add (hint_lov.add hint_gradsum)),
      MeasureTheory.integral_add
        (f := fun y => densityOnEuclid (I := I) g α y *
          covPrincipalRotationCoeff (I := I) (M := M) g r s T α P₀ y * φ y)
        (g := fun y => densityOnEuclid (I := I) g α y *
            covLowerOrderRotationValueCoeff (I := I) (M := M) g r s T α P₀ y *
              φ y +
          ∑ l : Fin (Module.finrank ℝ E),
            densityOnEuclid (I := I) g α y *
              covLowerOrderRotationGradCoeff (I := I) (M := M) g r s T α P₀ l y *
                euclidPartial (E := E) l φ y)
        hint_prc (hint_lov.add hint_gradsum),
      MeasureTheory.integral_add
        (f := fun y => densityOnEuclid (I := I) g α y *
          covLowerOrderRotationValueCoeff (I := I) (M := M) g r s T α P₀ y * φ y)
        (g := fun y => ∑ l : Fin (Module.finrank ℝ E),
          densityOnEuclid (I := I) g α y *
            covLowerOrderRotationGradCoeff (I := I) (M := M) g r s T α P₀ l y *
              euclidPartial (E := E) l φ y)
        hint_lov hint_gradsum]
  rw [hLHS_split] at hweak_v
  have hgradsum_eq :
      ∫ y, (∑ l : Fin (Module.finrank ℝ E),
        densityOnEuclid (I := I) g α y *
          covLowerOrderRotationGradCoeff (I := I) (M := M) g r s T α P₀ l y *
            euclidPartial (E := E) l φ y) ∂(volume : Measure EuclN) =
      ∑ l : Fin (Module.finrank ℝ E),
        ∫ y, weightedGradCoeff (I := I) (M := M) g r s T α P₀ l y *
          euclidPartial (E := E) l φ y ∂(volume : Measure EuclN) := by
    rw [MeasureTheory.integral_finset_sum _ (fun l _ => by
      have heq : (fun y => densityOnEuclid (I := I) g α y *
          covLowerOrderRotationGradCoeff (I := I) (M := M) g r s T α P₀ l y *
            euclidPartial (E := E) l φ y) =
        (fun y => weightedGradCoeff (I := I) (M := M) g r s T α P₀ l y *
          euclidPartial (E := E) l φ y) := by funext y; rw [weightedGradCoeff_eq]
      rw [heq]; exact hint_grad l)]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro y; rw [weightedGradCoeff_eq]
  have hIBP : ∀ l : Fin (Module.finrank ℝ E),
      ∫ y, weightedGradCoeff (I := I) (M := M) g r s T α P₀ l y *
        euclidPartial (E := E) l φ y ∂(volume : Measure EuclN) =
      -∫ y, euclidPartial (E := E) l
          (weightedGradCoeff (I := I) (M := M) g r s T α P₀ l) y * φ y
        ∂(volume : Measure EuclN) := by
    intro l
    have hL : ∫ y, weightedGradCoeff (I := I) (M := M) g r s T α P₀ l y *
        euclidPartial (E := E) l φ y ∂(volume : Measure EuclN) =
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        weightedGradCoeff (I := I) (M := M) g r s T α P₀ l y *
          euclidPartial (E := E) l φ y ∂chartHaar :=
      (hsetInt_to_int _ (fun y hy => by
        rw [hφ_partial_zero l y (fun h => hy (hφ_supp h)), mul_zero])).symm
    have hR : ∫ y, euclidPartial (E := E) l
        (weightedGradCoeff (I := I) (M := M) g r s T α P₀ l) y * φ y
        ∂(volume : Measure EuclN) =
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        euclidPartial (E := E) l
          (weightedGradCoeff (I := I) (M := M) g r s T α P₀ l) y * φ y
        ∂chartHaar :=
      (hsetInt_to_int _ (fun y hy => by
        rw [image_eq_zero_of_notMem_tsupport (fun h => hy (hφ_supp h)),
          mul_zero])).symm
    rw [hL, hR]
    exact chartTarget_integral_byParts (I := I) (M := M) α l
      (weightedGradCoeff_contDiffOn (I := I) (M := M) g r s T α P₀ l)
      hφ'.contDiffOn hφ_cs hφ_supp
  rw [hgradsum_eq, Finset.sum_congr rfl (fun l (_ : l ∈ Finset.univ) => hIBP l),
    Finset.sum_neg_distrib] at hweak_v
  have hbilin_eq :
      (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).bilin
          (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) φ =
        ∫ y, (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).principalIntegrand
          (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) φ y
          ∂(volume : Measure EuclN) := by
    rw [SmoothEllipticBilinearForm.bilin, MeasureTheory.setIntegral_univ]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro y
    change (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).principalIntegrand
        (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) φ y +
        (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).c y *
          tensorComponentEuclid (I := I) (M := M) g r s T α P₀ y * φ y =
      (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).principalIntegrand
        (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) φ y
    rw [tensorPrincipalForm_c_apply (I := I) (M := M) g α hK hK_target y]
    ring
  have hint_ibpsum : Integrable
      (fun y => (∑ l : Fin (Module.finrank ℝ E),
        euclidPartial (E := E) l
          (weightedGradCoeff (I := I) (M := M) g r s T α P₀ l) y) * φ y)
      (volume : Measure EuclN) := by
    have hcd : ContDiff ℝ ∞
        (fun y => (∑ l : Fin (Module.finrank ℝ E),
          euclidPartial (E := E) l
            (weightedGradCoeff (I := I) (M := M) g r s T α P₀ l) y) * φ y) :=
      contDiff_mul_chartTest (I := I) (M := M) α
        (ContDiffOn.sum (fun l _ => euclidPartial_contDiffOn_chartTarget
          (I := I) (M := M) α l
          (weightedGradCoeff_contDiffOn (I := I) (M := M) g r s T α P₀ l)))
        hφ' hφ_supp
    exact integrable_of_contDiff_hasCompactSupport (E := E) hcd (hcs_mul _)
  have hWeakRHS_volume :
      ∫ y, tensorComponentWeakRHS (I := I) (M := M) g r s T F α hK hK_target P₀ y
        * φ y ∂(volume : Measure EuclN) =
      (∫ y, densityOnEuclid (I := I) g α y *
          sourcePairingCoeff (I := I) (M := M) g r s F α P₀ y * φ y
          ∂(volume : Measure EuclN)) -
        (∫ y, densityOnEuclid (I := I) g α y *
          covPrincipalRotationCoeff (I := I) (M := M) g r s T α P₀ y * φ y
          ∂(volume : Measure EuclN)) -
        (∫ y, densityOnEuclid (I := I) g α y *
          covLowerOrderRotationValueCoeff (I := I) (M := M) g r s T α P₀ y * φ y
          ∂(volume : Measure EuclN)) +
        ∑ l : Fin (Module.finrank ℝ E),
          ∫ y, euclidPartial (E := E) l
            (weightedGradCoeff (I := I) (M := M) g r s T α P₀ l) y * φ y
            ∂(volume : Measure EuclN) := by
    have hsetEq :
        ∫ y, tensorComponentWeakRHS (I := I) (M := M) g r s T F α hK hK_target P₀
            y * φ y ∂(volume : Measure EuclN) =
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          (densityOnEuclid (I := I) g α y *
              sourcePairingCoeff (I := I) (M := M) g r s F α P₀ y * φ y -
            densityOnEuclid (I := I) g α y *
              covPrincipalRotationCoeff (I := I) (M := M) g r s T α P₀ y * φ y -
            densityOnEuclid (I := I) g α y *
              covLowerOrderRotationValueCoeff (I := I) (M := M) g r s T α P₀ y *
                φ y +
            ∑ l : Fin (Module.finrank ℝ E),
              euclidPartial (E := E) l
                (weightedGradCoeff (I := I) (M := M) g r s T α P₀ l) y * φ y)
          ∂(volume : Measure EuclN) := by
      rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        (s := chartTargetEuclid (I := I) (M := M) α)
        (f := fun y => tensorComponentWeakRHS (I := I) (M := M)
          g r s T F α hK hK_target P₀ y * φ y)
        (fun y hy => by
          simp only []
          rw [image_eq_zero_of_notMem_tsupport (fun h => hy (hφ_supp h)),
            mul_zero])]
      refine MeasureTheory.setIntegral_congr_fun hcTE_meas (fun y hy => ?_)
      rw [tensorComponentWeakRHS_apply_of_mem (I := I) (M := M) g r s T F α hK
        hK_target P₀ hy]
      simp only [add_mul, sub_mul, Finset.sum_mul]
    rw [hsetEq,
      MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        (s := chartTargetEuclid (I := I) (M := M) α)
        (f := fun y => densityOnEuclid (I := I) g α y *
            sourcePairingCoeff (I := I) (M := M) g r s F α P₀ y * φ y -
          densityOnEuclid (I := I) g α y *
            covPrincipalRotationCoeff (I := I) (M := M) g r s T α P₀ y * φ y -
          densityOnEuclid (I := I) g α y *
            covLowerOrderRotationValueCoeff (I := I) (M := M) g r s T α P₀ y *
              φ y +
          ∑ l : Fin (Module.finrank ℝ E),
            euclidPartial (E := E) l
              (weightedGradCoeff (I := I) (M := M) g r s T α P₀ l) y * φ y)
        (fun y hy => by
          simp only []
          rw [image_eq_zero_of_notMem_tsupport (fun h => hy (hφ_supp h))]
          simp only [mul_zero, sub_zero, zero_add]
          exact Finset.sum_eq_zero (fun l _ => by ring))]
    have hint_ibpsum' : Integrable
        (fun y => ∑ l : Fin (Module.finrank ℝ E),
          euclidPartial (E := E) l
            (weightedGradCoeff (I := I) (M := M) g r s T α P₀ l) y * φ y)
        (volume : Measure EuclN) :=
      MeasureTheory.integrable_finset_sum _ (fun l _ => hint_ibp l)
    rw [MeasureTheory.integral_add
        (f := fun y => densityOnEuclid (I := I) g α y *
            sourcePairingCoeff (I := I) (M := M) g r s F α P₀ y * φ y -
          densityOnEuclid (I := I) g α y *
            covPrincipalRotationCoeff (I := I) (M := M) g r s T α P₀ y * φ y -
          densityOnEuclid (I := I) g α y *
            covLowerOrderRotationValueCoeff (I := I) (M := M) g r s T α P₀ y *
              φ y)
        (g := fun y => ∑ l : Fin (Module.finrank ℝ E),
          euclidPartial (E := E) l
            (weightedGradCoeff (I := I) (M := M) g r s T α P₀ l) y * φ y)
        ((hint_src.sub hint_prc).sub hint_lov) hint_ibpsum',
      MeasureTheory.integral_sub
        (f := fun y => densityOnEuclid (I := I) g α y *
            sourcePairingCoeff (I := I) (M := M) g r s F α P₀ y * φ y -
          densityOnEuclid (I := I) g α y *
            covPrincipalRotationCoeff (I := I) (M := M) g r s T α P₀ y * φ y)
        (g := fun y => densityOnEuclid (I := I) g α y *
          covLowerOrderRotationValueCoeff (I := I) (M := M) g r s T α P₀ y * φ y)
        (hint_src.sub hint_prc) hint_lov,
      MeasureTheory.integral_sub
        (f := fun y => densityOnEuclid (I := I) g α y *
          sourcePairingCoeff (I := I) (M := M) g r s F α P₀ y * φ y)
        (g := fun y => densityOnEuclid (I := I) g α y *
          covPrincipalRotationCoeff (I := I) (M := M) g r s T α P₀ y * φ y)
        hint_src hint_prc,
      MeasureTheory.integral_finset_sum _ (fun l _ => hint_ibp l)]
  rw [hbilin_eq, hWeakRHS_volume]
  linarith [hweak_v]

omit [CompleteSpace E] in
theorem tensorComponentWeakRHS_tsupport_subset
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T F : SmoothCcTensor g r s) (α : M)
    {K : Set EuclN} (hK : IsCompact K)
    (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    (P₀ : CompIdx E r s)
    (hT_supp : tsupport T.toFun ⊆ (chartAt H α).source)
    (hF_supp : tsupport F.toFun ⊆ (chartAt H α).source)
    (hT_K : tsupport (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) ⊆ K)
    (hweak : ∀ v : SmoothCcTensor g r s,
      ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r s T v x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        tensorL2Inner (I := I) (M := M) g r s F.toFun v.toFun) :
    tsupport (tensorComponentWeakRHS (I := I) (M := M) g r s T F α hK hK_target P₀)
      ⊆ tsupport (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) := by
  classical
  have hRHS_cont : Continuous
      (tensorComponentWeakRHS (I := I) (M := M) g r s T F α hK hK_target P₀) :=
    (tensorComponentWeakRHS_contDiff (I := I) (M := M) g r s T F α hK hK_target P₀
      hT_supp hF_supp).continuous
  set V : Set EuclN := chartTargetEuclid (I := I) (M := M) α \
    tsupport (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) with hV_def
  have hV_open : IsOpen V :=
    (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α).sdiff (isClosed_tsupport _)
  have hV_meas : MeasurableSet V := hV_open.measurableSet
  have hu_partial_zero : ∀ k : Fin (Module.finrank ℝ E), ∀ y,
      y ∉ tsupport (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) →
      euclidPartial (E := E) k
        (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) y = 0 :=
    fun k y hy => euclidPartial_eq_zero_of_notMem_tsupport (E := E) k hy
  have hzero_int : ∀ φ : EuclN → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ V →
      ∫ y, φ y • tensorComponentWeakRHS (I := I) (M := M)
        g r s T F α hK hK_target P₀ y ∂(volume : Measure EuclN) = 0 := by
    intro φ hφ hφ_cs hφ_supp_V
    have hφ_supp : tsupport φ ⊆ chartTargetEuclid (I := I) (M := M) α :=
      hφ_supp_V.trans (Set.diff_subset)
    have hbilin := tensorComponent_chartBilinIdentity (I := I) (M := M)
      g r s T F α hK hK_target P₀ hT_supp hT_K hweak hφ hφ_cs hφ_supp
    have hbilin_zero :
        (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).bilin
          (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) φ = 0 := by
      rw [SmoothEllipticBilinearForm.bilin]
      refine MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero (fun y _ => ?_)
      rw [tensorPrincipalForm_c_apply (I := I) (M := M) g α hK hK_target y]
      have hprinc0 :
          (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).principalIntegrand
            (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) φ y = 0 := by
        rw [SmoothEllipticBilinearForm.principalIntegrand]
        refine Finset.sum_eq_zero (fun i _ => Finset.sum_eq_zero (fun j _ => ?_))
        by_cases hyφ : y ∈ tsupport φ
        · have hyu : y ∉ tsupport
              (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) :=
            (hφ_supp_V hyφ).2
          have := hu_partial_zero i y hyu
          rw [euclidPartial_def] at this
          rw [this]; ring
        · have := euclidPartial_eq_zero_of_notMem_tsupport (E := E) j hyφ
          rw [euclidPartial_def] at this
          rw [this]; ring
      rw [hprinc0]; ring
    have hint0 : ∫ y, tensorComponentWeakRHS (I := I) (M := M)
        g r s T F α hK hK_target P₀ y * φ y ∂(volume : Measure EuclN) = 0 := by
      rw [← hbilin, hbilin_zero]
    rw [show (fun y => φ y • tensorComponentWeakRHS (I := I) (M := M)
          g r s T F α hK hK_target P₀ y) =
        (fun y => tensorComponentWeakRHS (I := I) (M := M)
          g r s T F α hK hK_target P₀ y * φ y) from by
      funext y; rw [smul_eq_mul, mul_comm]]
    exact hint0
  have hae : ∀ᵐ y ∂(volume : Measure EuclN), y ∈ V →
      tensorComponentWeakRHS (I := I) (M := M) g r s T F α hK hK_target P₀ y = 0 :=
    hV_open.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hRHS_cont.locallyIntegrable.locallyIntegrableOn V) hzero_int
  have hEqOn : Set.EqOn
      (tensorComponentWeakRHS (I := I) (M := M) g r s T F α hK hK_target P₀)
      (fun _ => (0 : ℝ)) V :=
    MeasureTheory.Measure.eqOn_open_of_ae_eq
      ((MeasureTheory.ae_restrict_iff' hV_meas).mpr hae) hV_open
      hRHS_cont.continuousOn continuousOn_const
  refine closure_minimal (fun y hy => ?_) (isClosed_tsupport _)
  rw [Function.mem_support] at hy
  by_contra hyu
  by_cases hyT : y ∈ chartTargetEuclid (I := I) (M := M) α
  · exact hy (hEqOn ⟨hyT, hyu⟩)
  · exact hy (tensorComponentWeakRHS_apply_of_notMem (I := I) (M := M)
      g r s T F α hK hK_target P₀ hyT)

omit [CompleteSpace E] in
theorem tensorComponentWeakRHS_hasCompactSupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T F : SmoothCcTensor g r s) (α : M)
    {K : Set EuclN} (hK : IsCompact K)
    (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    (P₀ : CompIdx E r s)
    (hT_supp : tsupport T.toFun ⊆ (chartAt H α).source)
    (hF_supp : tsupport F.toFun ⊆ (chartAt H α).source)
    (hT_K : tsupport (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) ⊆ K)
    (hweak : ∀ v : SmoothCcTensor g r s,
      ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r s T v x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        tensorL2Inner (I := I) (M := M) g r s F.toFun v.toFun) :
    HasCompactSupport
      (tensorComponentWeakRHS (I := I) (M := M) g r s T F α hK hK_target P₀) := by
  classical
  have hcomp_cs : HasCompactSupport
      (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) :=
    tensorComponentEuclid_hasCompactSupport (I := I) (M := M)
      g r s T α P₀ hT_supp
  have hRHS_supp : tsupport (tensorComponentWeakRHS (I := I) (M := M)
      g r s T F α hK hK_target P₀) ⊆
      tsupport (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) :=
    tensorComponentWeakRHS_tsupport_subset (I := I) (M := M) g r s T F α hK
      hK_target P₀ hT_supp hF_supp hT_K hweak
  exact HasCompactSupport.of_support_subset_isCompact hcomp_cs
    (subset_trans (subset_tsupport _) hRHS_supp)

omit [CompleteSpace E] in
theorem tensorComponent_isSmoothWeakSolution
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T F : SmoothCcTensor g r s) (α : M)
    {K : Set EuclN} (hK : IsCompact K)
    (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    (P₀ : CompIdx E r s)
    (hT_supp : tsupport T.toFun ⊆ (chartAt H α).source)
    (hF_supp : tsupport F.toFun ⊆ (chartAt H α).source)
    (hT_K : tsupport (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) ⊆ K)
    (hweak : ∀ v : SmoothCcTensor g r s,
      ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r s T v x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        tensorL2Inner (I := I) (M := M) g r s F.toFun v.toFun) :
    (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).IsSmoothWeakSolution
      (tensorComponentEuclid (I := I) (M := M) g r s T α P₀)
      (tensorComponentWeakRHS (I := I) (M := M) g r s T F α hK hK_target P₀) := by
  classical
  have hcTE_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α
  have hu_partial_zero : ∀ k : Fin (Module.finrank ℝ E), ∀ y,
      y ∉ tsupport (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) →
      euclidPartial (E := E) k
        (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) y = 0 :=
    fun k y hy => euclidPartial_eq_zero_of_notMem_tsupport (E := E) k hy
  have hRHS_supp : tsupport (tensorComponentWeakRHS (I := I) (M := M)
      g r s T F α hK hK_target P₀) ⊆
      tsupport (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) :=
    tensorComponentWeakRHS_tsupport_subset (I := I) (M := M) g r s T F α hK
      hK_target P₀ hT_supp hF_supp hT_K hweak
  obtain ⟨L, hL_compact, hKL, hL_target⟩ := exists_compact_between hK hcTE_open
    hK_target
  obtain ⟨ζ, hζ_one, hζ_zero, -⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior (𝓘(ℝ, EuclN))
      (n := (⊤ : ℕ∞)) hK.isClosed hKL
  have hζ_cd : ContDiff ℝ ∞ (fun y => ζ y) :=
    (contMDiff_iff_contDiff (n := (⊤ : ℕ∞))).mp ζ.contMDiff
  have hζ_supp : tsupport (fun y => ζ y) ⊆ L := by
    refine closure_minimal (fun y hy => ?_) hL_compact.isClosed
    rw [Function.mem_support] at hy
    by_contra hyL
    exact hy (hζ_zero y hyL)
  have hζ_cs : HasCompactSupport (fun y => ζ y) :=
    HasCompactSupport.of_support_subset_isCompact hL_compact
      (fun y hy => hζ_supp (subset_tsupport _ hy))
  have hζ_one_on : ∀ y ∈ tsupport (tensorComponentEuclid (I := I) (M := M)
      g r s T α P₀), ζ y = 1 := by
    intro y hy
    exact (hζ_one.filter_mono (nhds_le_nhdsSet (hT_K hy))).self_of_nhds
  refine tensorComponent_isSmoothWeakSolution_of_chartIdentity (I := I) (M := M)
    g r s T α hK hK_target P₀ hT_supp _ (fun φ hφ hφ_cs _ => ?_)
  have hφ' : ContDiff ℝ ∞ φ := hφ
  set ψ : EuclN → ℝ := fun y => ζ y * φ y with hψ_def
  have hψ_cd : ContDiff ℝ ∞ ψ := hζ_cd.mul hφ'
  have hψ_cs : HasCompactSupport ψ := hζ_cs.mul_right
  have hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α := by
    refine (closure_minimal ?_ hL_compact.isClosed).trans hL_target
    intro y hy
    rw [Function.mem_support] at hy
    by_contra hyL
    exact hy (show ζ y * φ y = 0 by rw [hζ_zero y hyL, zero_mul])
  have hbilin_eq :
      (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).bilin
          (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) φ =
        (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).bilin
          (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) ψ := by
    rw [SmoothEllipticBilinearForm.bilin, SmoothEllipticBilinearForm.bilin]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall
      (fun y => ?_))
    change (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).principalIntegrand
        (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) φ y +
        (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).c y *
          tensorComponentEuclid (I := I) (M := M) g r s T α P₀ y * φ y =
      (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).principalIntegrand
        (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) ψ y +
        (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).c y *
          tensorComponentEuclid (I := I) (M := M) g r s T α P₀ y * ψ y
    rw [tensorPrincipalForm_c_apply (I := I) (M := M) g α hK hK_target y]
    have hprinc :
        (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).principalIntegrand
            (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) φ y =
          (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).principalIntegrand
            (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) ψ y := by
      by_cases hyu : y ∈ tsupport
          (tensorComponentEuclid (I := I) (M := M) g r s T α P₀)
      · have hψφ : ψ =ᶠ[nhds y] φ := by
          have hone : ∀ᶠ z in nhds y, ζ z = 1 :=
            hζ_one.filter_mono (nhds_le_nhdsSet (hT_K hyu))
          filter_upwards [hone] with z hz
          change ζ z * φ z = φ z
          rw [hz, one_mul]
        rw [SmoothEllipticBilinearForm.principalIntegrand,
          SmoothEllipticBilinearForm.principalIntegrand]
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
        rw [Filter.EventuallyEq.fderiv_eq hψφ]
      · rw [SmoothEllipticBilinearForm.principalIntegrand,
          SmoothEllipticBilinearForm.principalIntegrand]
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
        have := hu_partial_zero i y hyu
        rw [euclidPartial_def] at this
        rw [this]; ring
    rw [hprinc]; ring
  have hRHS_eq :
      ∫ y, tensorComponentWeakRHS (I := I) (M := M) g r s T F α hK hK_target P₀ y
        * ψ y ∂(volume : Measure EuclN) =
      ∫ y, tensorComponentWeakRHS (I := I) (M := M) g r s T F α hK hK_target P₀ y
        * φ y ∂(volume : Measure EuclN) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall
      (fun y => ?_))
    change tensorComponentWeakRHS (I := I) (M := M) g r s T F α hK hK_target P₀ y *
        (ζ y * φ y) =
      tensorComponentWeakRHS (I := I) (M := M) g r s T F α hK hK_target P₀ y * φ y
    by_cases hyR : y ∈ tsupport (tensorComponentWeakRHS (I := I) (M := M)
        g r s T F α hK hK_target P₀)
    · rw [hζ_one_on y (hRHS_supp hyR)]; ring
    · rw [image_eq_zero_of_notMem_tsupport hyR]; ring
  rw [MeasureTheory.setIntegral_univ, hbilin_eq,
    tensorComponent_chartBilinIdentity (I := I) (M := M) g r s T F α hK hK_target
      P₀ hT_supp hT_K hweak hψ_cd hψ_cs hψ_supp, hRHS_eq]

end TensorRegularity
end Laplacian
end Analysis
end DifferentialGeometry
